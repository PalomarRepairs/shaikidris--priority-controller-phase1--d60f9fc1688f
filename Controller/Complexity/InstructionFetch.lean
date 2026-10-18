module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.FetchSetup
public import Controller.Complexity.InstructionSkip

public import Mathlib.Tactic.Ring

@[expose] public section

/-! A fixed finite driver fetches the instruction at a preserved binary index.
Original code/count are copied, the index is range-checked, exactly its prefix
is traversed, the selected instruction is parsed and source work is erased.
Successful actual fields observe the literal native indexed instruction. -/
namespace Controller.Complexity.InstructionFetch
open StackMachine WordReader
open scoped BigOperators

structure Ready (input : Port → List Bool) (bound : registers ≤ 2^width)
    (instructions : List (Controller.Cost.Instruction width registers)) (index : List Bool)
    extends FetchSetup.Ready input (InstructionCodec.encodeMany bound instructions) index instructions.length where
  stored : input (some 8)=List.replicate width true
  saved : input (some 9)=List.replicate registers true

theorem Ready.parser (input : Port → List Bool) (bound : registers ≤ 2^width)
    (instructions : List (Controller.Cost.Instruction width registers)) (index : List Bool) (ready : Ready input bound instructions index) :
    InstructionSkip.Ready input width registers where
  stored := ready.stored
  saved := ready.saved
  count := ready.clear _ (by simp [FetchSetup.work])
  payload := ready.clear _ (by simp [FetchSetup.work])
  arity := ready.clear _ (by simp [FetchSetup.work])
  tag := ready.clear _ (by simp [FetchSetup.work])
  bound := ready.clear _ (by simp [FetchSetup.work])
  scratch := ready.clear _ (by simp [FetchSetup.work])
  roles := ready.clear _ (by simp [FetchSetup.work])

def ReadLabel : Type := InstructionSkip.Label ⊕ InstructionSkip.ParseLabel
instance readFintype : Fintype ReadLabel := inferInstanceAs (Fintype (InstructionSkip.Label ⊕ InstructionSkip.ParseLabel))
def readProgram : Program (Fin 31) ReadLabel := link InstructionSkip.program InstructionSkip.parseProgram

def SetupLabel : Type := StateReader.LabelsOf FetchSetup.program
instance setupFintype : Fintype SetupLabel := inferInstanceAs (Fintype (StateReader.LabelsOf FetchSetup.program))
def setupProgram : Program (Fin 31) SetupLabel := FetchSetup.program

def GuardLabel : Type := SetupLabel ⊕ Option ReadLabel
instance guardFintype : Fintype GuardLabel := inferInstanceAs (Fintype (SetupLabel ⊕ Option ReadLabel))
def guarded : Program (Fin 31) GuardLabel := GuardedLink.program setupProgram readProgram none Option.isNone

def Label : Type := GuardLabel ⊕ Fin 2
instance labelFintype : Fintype Label := inferInstanceAs (Fintype (GuardLabel ⊕ Fin 2))
def program : Program (Fin 31) Label := link guarded (StackClear.program (some 0 : Port))

def chosen (input : Port → List Bool) (bound : registers ≤ 2^width) (instruction : Controller.Cost.Instruction width registers) : Port → List Bool :=
  InstructionShape.fieldsData (Function.update input (some 4) [])
    ⟨(InstructionCodec.fields bound instruction).1,InstructionCodec.fields_tag_lt bound instruction⟩ (InstructionCodec.fields bound instruction).2 []

def result (input : Port → List Bool) (bound : registers ≤ 2^width) (instructions : List (Controller.Cost.Instruction width registers)) (index : List Bool) : Port → List Bool :=
  if valid : Encoding.value index < instructions.length then chosen input bound instructions[Encoding.value index]
  else bank (Function.update input (some 4) []) [false] [] []

def perInstruction (width registers : Nat) := 12*width*registers+141*width+18*registers+301

theorem read_execution (input : Port → List Bool) (bound : registers ≤ 2^width)
    (left : List (Controller.Cost.Instruction width registers)) (instruction : Controller.Cost.Instruction width registers)
    (right : List (Controller.Cost.Instruction width registers)) (ready : InstructionSkip.Ready input width registers) :
    ∃ ticks peak, Execution readProgram
      ⟨some readProgram.main,InstructionSkip.data input left.length (InstructionCodec.encodeMany bound left++(InstructionCodec.encode bound instruction++InstructionCodec.encodeMany bound right))⟩
      ⟨none,InstructionShape.fieldsData (Function.update input (some 4) [])
        ⟨(InstructionCodec.fields bound instruction).1,InstructionCodec.fields_tag_lt bound instruction⟩ (InstructionCodec.fields bound instruction).2 (InstructionCodec.encodeMany bound right)⟩
      ticks peak ∧ ticks ≤ (left.length+1)*perInstruction width registers+2 := by
  obtain ⟨skipTicks,skipPeak,skipping,skipBound⟩ := InstructionSkip.execution input bound left
    (InstructionCodec.encode bound instruction++InstructionCodec.encodeMany bound right) ready
  obtain ⟨readTicks,readPeak,reading,readBound,_⟩ := InstructionEndpoint.execution (Function.update input (some 4) []) bound instruction
    (InstructionCodec.encodeMany bound right) (by simpa using ready.stored) (by simpa using ready.saved)
    (by simpa using ready.count) (by simpa using ready.payload) (by simpa using ready.arity) (by simpa using ready.tag)
    (by simpa using ready.bound) (by simpa using ready.scratch) (by simpa using ready.roles)
  have trace := skipping.link reading
  have finalBound : skipTicks+readTicks ≤ (left.length+1)*perInstruction width registers+2 := by
    simp only [perInstruction,Nat.add_mul,Nat.one_mul]
    omega
  exact ⟨_,_,by simpa only [readProgram,ReadLabel,InstructionSkip.parseProgram,InstructionSkip.ParseLabel,
    InstructionSkip.data,WordSkip.data,List.replicate_zero] using trace,finalBound⟩

theorem chosen_cleanup (input : Port → List Bool) (bound : registers ≤ 2^width) (instruction : Controller.Cost.Instruction width registers) (suffix : List Bool) :
    Function.update (InstructionShape.fieldsData (Function.update input (some 4) [])
      ⟨(InstructionCodec.fields bound instruction).1,InstructionCodec.fields_tag_lt bound instruction⟩ (InstructionCodec.fields bound instruction).2 suffix)
      (some 0) []=chosen input bound instruction := by
  funext address
  by_cases same : address=some 0 <;> simp_all [chosen,InstructionRange.fields_at]

theorem execution (input : Port → List Bool) (bound : registers ≤ 2^width)
    (instructions : List (Controller.Cost.Instruction width registers)) (index : List Bool) (ready : Ready input bound instructions index) :
    ∃ ticks peak, Execution program ⟨some program.main,input⟩ ⟨none,result input bound instructions index⟩ ticks peak ∧
      ticks ≤ 6*(InstructionCodec.encodeMany bound instructions).length+index.length*(11*instructions.length+33)+
        12*instructions.length+instructions.length*perInstruction width registers+44 := by
  obtain ⟨setupTicks,setupPeak,setting,setupBound⟩ := FetchSetup.execution input (InstructionCodec.encodeMany bound instructions) index instructions.length ready.toReady
  by_cases valid : Encoding.value index < instructions.length
  · let left := instructions.take (Encoding.value index)
    let instruction := instructions[Encoding.value index]
    let right := instructions.drop (Encoding.value index+1)
    have leftLength : left.length=Encoding.value index := by simp [left,Nat.min_eq_left (Nat.le_of_lt valid)]
    have split : instructions=left++instruction::right := by
      dsimp [left,instruction,right]
      rw [← List.drop_eq_getElem_cons valid,List.take_append_drop]
    have code : InstructionCodec.encodeMany bound instructions=
        InstructionCodec.encodeMany bound left++(InstructionCodec.encode bound instruction++InstructionCodec.encodeMany bound right) := by
      conv_lhs => rw [split,InstructionCodec.encodeMany,List.flatMap_append,List.flatMap_cons]
      rfl
    have planned : FetchSetup.output input (InstructionCodec.encodeMany bound instructions) index instructions.length=
        InstructionSkip.data input left.length (InstructionCodec.encodeMany bound left++(InstructionCodec.encode bound instruction++InstructionCodec.encodeMany bound right)) := by
      simp only [FetchSetup.output,ite_eq_left valid]
      simp only [← leftLength,InstructionSkip.data,WordSkip.data,code]
    rw [planned] at setting
    obtain ⟨readTicks,readPeak,reading,readBound⟩ := read_execution input bound left instruction right (ready.parser input bound instructions index)
    have fetched := GuardedLink.success none Option.isNone setting reading (by simp [InstructionSkip.data,WordSkip.data_at])
    obtain ⟨clearPeak,clearing⟩ := StackClear.ready_execution (InstructionShape.fieldsData (Function.update input (some 4) [])
      ⟨(InstructionCodec.fields bound instruction).1,InstructionCodec.fields_tag_lt bound instruction⟩ (InstructionCodec.fields bound instruction).2 (InstructionCodec.encodeMany bound right)) (some 0)
    rw [chosen_cleanup] at clearing
    have sourceLength : (InstructionShape.fieldsData (Function.update input (some 4) [])
        ⟨(InstructionCodec.fields bound instruction).1,InstructionCodec.fields_tag_lt bound instruction⟩ (InstructionCodec.fields bound instruction).2 (InstructionCodec.encodeMany bound right) (some 0)).length=
        (InstructionCodec.encodeMany bound right).length := by simp [InstructionRange.fields_at]
    rw [sourceLength] at clearing
    have trace := fetched.link clearing
    have final : result input bound instructions index=chosen input bound instruction := by simp only [result,dite_eq_left valid]; rfl
    rw [← final] at trace
    have suffixBound : (InstructionCodec.encodeMany bound right).length ≤ (InstructionCodec.encodeMany bound instructions).length := by
      have mass := congrArg List.length code
      simp only [List.length_append] at mass
      omega
    have countBound : left.length+1 ≤ instructions.length := by omega
    have product := Nat.mul_le_mul_right (perInstruction width registers) countBound
    refine ⟨setupTicks+readTicks+((InstructionCodec.encodeMany bound right).length+2),max (max setupPeak readPeak) clearPeak,?_,?_⟩
    · simpa only [program,guarded,setupProgram,Label,GuardLabel,SetupLabel] using trace
    · omega
  · have rejected : FetchSetup.output input (InstructionCodec.encodeMany bound instructions) index instructions.length=
        bank (Function.update input (some 4) []) [false] (InstructionCodec.encodeMany bound instructions) [] := by simp only [FetchSetup.output,ite_eq_right valid]
    rw [rejected] at setting
    have fetched := GuardedLink.failure readProgram none Option.isNone setting (by simp [bank_counter])
    obtain ⟨clearPeak,clearing⟩ := StackClear.ready_execution (bank (Function.update input (some 4) []) [false] (InstructionCodec.encodeMany bound instructions) []) (some 0)
    have endpoint : Function.update (bank (Function.update input (some 4) []) [false] (InstructionCodec.encodeMany bound instructions) []) (some 0) []=
        bank (Function.update input (some 4) []) [false] [] [] := by
      funext address
      by_cases same : address=some 0 <;> simp_all [WordSkip.reader_at]
    rw [endpoint] at clearing
    simp only [bank_source] at clearing
    have trace := fetched.link clearing
    have final : result input bound instructions index=bank (Function.update input (some 4) []) [false] [] [] := by simp only [result,dite_eq_right valid]
    rw [← final] at trace
    refine ⟨setupTicks+1+((InstructionCodec.encodeMany bound instructions).length+2),max setupPeak clearPeak,?_,?_⟩
    · simpa only [program,guarded,setupProgram,Label,GuardLabel,SetupLabel] using trace
    · omega

theorem total_polynomial (input : Port → List Bool) (bound : registers ≤ 2^width)
    (instructions : List (Controller.Cost.Instruction width registers)) (index : List Bool) (ready : Ready input bound instructions index) :
    ∃ ticks peak, Execution program ⟨some program.main,input⟩ ⟨none,result input bound instructions index⟩ ticks peak ∧
      ticks ≤ 12*(FetchSetup.size input)^3+170*(FetchSetup.size input)^2+352*FetchSetup.size input+44 ∧
      peak ≤ 12*(FetchSetup.size input)^3+170*(FetchSetup.size input)^2+353*FetchSetup.size input+44 := by
  obtain ⟨ticks,peak,trace,timeBound⟩ := execution input bound instructions index ready
  have cell (port : Port) : (input port).length ≤ FetchSetup.size input :=
    Finset.single_le_sum (f := fun address : Port => (input address).length) (fun _ _ => Nat.zero_le _) (Finset.mem_univ port)
  have codeBound : (InstructionCodec.encodeMany bound instructions).length ≤ FetchSetup.size input := by simpa only [ready.codeStored] using cell (some 19)
  have indexBound : index.length ≤ FetchSetup.size input := by simpa only [ready.indexStored] using cell (some 3)
  have nBound : instructions.length ≤ FetchSetup.size input := by simpa only [ready.countStored,List.length_replicate] using cell (some 15)
  have wBound : width ≤ FetchSetup.size input := by simpa only [ready.stored,List.length_replicate] using cell (some 8)
  have rBound : registers ≤ FetchSetup.size input := by simpa only [ready.saved,List.length_replicate] using cell (some 9)
  have pairs := Nat.mul_le_mul wBound rBound
  have product : 12*width*registers ≤ 12*(FetchSetup.size input)^2 := by
    calc
      _ = 12*(width*registers) := by ring
      _ ≤ 12*(FetchSetup.size input*FetchSetup.size input) := Nat.mul_le_mul_left 12 pairs
      _ = _ := by ring
  have oneBound : perInstruction width registers ≤ 12*(FetchSetup.size input)^2+159*FetchSetup.size input+301 := by dsimp only [perInstruction]; omega
  have repeated := Nat.mul_le_mul nBound oneBound
  have indices := Nat.mul_le_mul indexBound (Nat.add_le_add_right (Nat.mul_le_mul_left 11 nBound) 33)
  have identity : 6*FetchSetup.size input+FetchSetup.size input*(11*FetchSetup.size input+33)+12*FetchSetup.size input+
      FetchSetup.size input*(12*(FetchSetup.size input)^2+159*FetchSetup.size input+301)+44=
      12*(FetchSetup.size input)^3+170*(FetchSetup.size input)^2+352*FetchSetup.size input+44 := by ring
  have bounded : ticks ≤ 12*(FetchSetup.size input)^3+170*(FetchSetup.size input)^2+352*FetchSetup.size input+44 := by rw [← identity]; omega
  have space := trace.peak_le
  change peak ≤ FetchSetup.size input+ticks at space
  exact ⟨ticks,peak,trace,bounded,by omega⟩

theorem observation (input : Port → List Bool) (bound : registers ≤ 2^width)
    (instructions : List (Controller.Cost.Instruction width registers)) (index : List Bool) :
    Option.isNone ((result input bound instructions index none).head?)=(instructions[Encoding.value index]?).isSome ∧
    (∀ instruction, instructions[Encoding.value index]?=some instruction →
      InstructionFields.observe width registers (result input bound instructions index)=some instruction) := by
  by_cases valid : Encoding.value index < instructions.length
  · have final : result input bound instructions index=chosen input bound instructions[Encoding.value index] := by simp only [result,dite_eq_left valid]
    rw [final]
    constructor
    · simp [chosen,InstructionRange.fields_at,List.getElem?_eq_getElem valid]
    · intro instruction equal
      have same : instructions[Encoding.value index]=instruction := by simpa only [List.getElem?_eq_getElem valid,Option.some.injEq] using equal
      rw [← same]
      exact InstructionFields.endpoint_observation (Function.update input (some 4) []) bound instructions[Encoding.value index] []
  · simp [result,valid,bank_counter]

theorem setup_card : Fintype.card SetupLabel=107 := by
  have original : Fintype.card (StateReader.LabelsOf FetchSetup.program)=107 := by
    simp only [StateReader.LabelsOf,Fintype.card_sum,Fintype.card_option,Fintype.card_fin,Nat.reduceAdd]
  have same : Fintype.card SetupLabel=Fintype.card (StateReader.LabelsOf FetchSetup.program) :=
    @Fintype.card_congr SetupLabel (StateReader.LabelsOf FetchSetup.program) _ _ (Equiv.refl _)
  exact same.trans original

theorem read_card : Fintype.card ReadLabel=1605 := by
  have split : Fintype.card ReadLabel=Fintype.card InstructionSkip.Label+Fintype.card InstructionSkip.ParseLabel := Fintype.card_sum
  rw [InstructionSkip.canonical_card,InstructionSkip.parse_card] at split
  exact split

theorem guard_card : Fintype.card GuardLabel=1713 := by
  have split : Fintype.card GuardLabel=Fintype.card SetupLabel+Fintype.card (Option ReadLabel) := Fintype.card_sum
  have optional : Fintype.card (Option ReadLabel)=Fintype.card ReadLabel+1 := Fintype.card_option
  rw [setup_card,optional,read_card] at split
  exact split

theorem canonical_card : Fintype.card Label=1715 := by
  have split : Fintype.card Label=Fintype.card GuardLabel+Fintype.card (Fin 2) := Fintype.card_sum
  rw [guard_card] at split
  simpa only [Fintype.card_fin,Nat.reduceAdd] using split

theorem resident : (∑ label, statementSize (tmStatement (program.code label))) ≤ 15435 := by
  have bound := finiteTM_resident program
  rw [canonical_card] at bound
  exact bound

end Controller.Complexity.InstructionFetch
