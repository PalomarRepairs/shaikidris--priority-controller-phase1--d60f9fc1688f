module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.CountEquality
public import Controller.Complexity.StateShape
public import Controller.Complexity.WordFieldReader

public import Mathlib.Tactic.Ring

@[expose] public section

/-! State-field shape checks run between list parsing and persistent storage.
The concrete checks enforce the saved register count and a singleton PC.
Every successful field preserves total live storage after count framing. -/
namespace Controller.Complexity.CheckedWordField
open StackMachine WordReader
open scoped BigOperators

def parsedBank (frame : Port → List Bool) (words : List (Controller.Cost.Word width)) (suffix : List Bool) : Port → List Bool :=
  WordListReader.data (Function.update frame (some 12) (List.replicate words.length true)) 0 suffix (Encoding.wordList width words)

def mass (input : Port → List Bool) : Nat := ∑ port : Port,(input port).length

theorem parsed_mass (frame : Port → List Bool) (words : List (Controller.Cost.Word width)) (suffix : List Bool)
    (countEmpty : frame (some 10)=[]) (bufferEmpty : frame (some 11)=[]) (savedEmpty : frame (some 12)=[]) :
    mass (parsedBank frame words suffix)+1=(Encoding.encodeWords width words++suffix).length+ambientBits frame := by
  let saved := Function.update frame (some 12) (List.replicate words.length true)
  have savedBits : ambientBits saved=ambientBits frame+words.length := by
    simpa only [saved,List.length_replicate] using ColdInput.ambient_saved frame 12 (by decide) (by decide) (by decide) (List.replicate words.length true) savedEmpty
  have countClear : saved (some 10)=[] := by simp [saved,countEmpty]
  have bufferClear : saved (some 11)=[] := by simp [saved,bufferEmpty]
  have fields : WordListReader.fields saved 0 (Encoding.wordList width words)=Function.update saved (some 11) (Encoding.wordList width words) := by
    unfold WordListReader.fields
    rw [show List.replicate 0 true=[] from rfl,ColdInput.update_empty saved (some 10) countClear]
  have fieldBits : ambientBits (WordListReader.fields saved 0 (Encoding.wordList width words))=
      ambientBits frame+words.length+(Encoding.wordList width words).length := by
    rw [fields]
    rw [ColdInput.ambient_saved saved 11 (by decide) (by decide) (by decide) _ bufferClear,savedBits]
  have total := bank_live (WordListReader.fields saved 0 (Encoding.wordList width words)) (none : Option Unit) [] suffix []
  simp only [live,List.length_nil,Nat.zero_add,Nat.add_zero] at total
  change mass (parsedBank frame words suffix)=suffix.length+ambientBits (WordListReader.fields saved 0 (Encoding.wordList width words)) at total
  rw [total,fieldBits,List.length_append,Encoding.encodeWords_length,Encoding.wordList_length]
  ring

def program (checker : Program (Fin 31) Q) (slot : Fin 31) :=
  GuardedLink.program WordListReader.program
    (GuardedLink.program checker (WordFieldStore.program (some slot)) none Option.isNone) none Option.isNone

def readField (accepts : Nat → Bool) (width : Nat) (input : List Bool) : Option (List (Controller.Cost.Word width) × List Bool) := do
  let (words,suffix) ← Encoding.readFramedWords width input
  if accepts words.length then some (words,suffix) else none

/-- The checker runs on actual parsed banks, retaining them on acceptance. -/
def CheckSpec (checker : Program (Fin 31) Q) (accepts : Nat → Bool) (frame : Port → List Bool) (width : Nat) : Prop :=
  ∀ (words : List (Controller.Cost.Word width)) (suffix : List Bool),
    ∃ ticks peak output, Execution checker ⟨some checker.main,parsedBank frame words suffix⟩ ⟨none,output⟩ ticks peak ∧
      ticks ≤ 12*mass (parsedBank frame words suffix)+14 ∧
      Option.isNone ((output none).head?)=accepts words.length ∧
      (accepts words.length=true → output=parsedBank frame words suffix)

theorem register_spec (frame : Port → List Bool) (width registers : Nat)
    (stored : frame (some 9)=List.replicate registers true) (left : frame (some 16)=[]) (right : frame (some 17)=[])
    (scratch : frame (some 20)=[]) :
    CheckSpec CountEquality.program (fun count => decide (count=registers)) frame width := by
  intro words suffix
  let middle := parsedBank frame words suffix
  have status : middle none=[] := by simp [middle,parsedBank,WordListReader.data_at]
  have cleanLeft : middle (some 16)=[] := by simp [middle,parsedBank,WordListReader.data_at,left]
  have cleanRight : middle (some 17)=[] := by simp [middle,parsedBank,WordListReader.data_at,right]
  have entry := CountEquality.ready_bank middle status cleanLeft cleanRight
  obtain ⟨ticks,peak,trace,timeBound,spaceBound⟩ := CountEquality.total_polynomial middle registers words.length
    (by simp [middle,parsedBank,WordListReader.data_at,stored])
    (by simp [middle,parsedBank,WordListReader.data_at])
    (by simp [middle,parsedBank,WordListReader.data_at,scratch])
  rw [entry] at trace
  have size : CountEquality.size middle=mass middle := by simp only [CountEquality.size,entry,mass]
  rw [size] at timeBound
  refine ⟨ticks,peak,_,trace,timeBound,?_,?_⟩
  · by_cases same : words.length=registers <;> simp [CountEquality.bank_at,same]
  · intro accepted
    have same : words.length=registers := of_decide_eq_true accepted
    simpa only [ite_eq_left same] using entry

theorem singleton_spec (frame : Port → List Bool) (width : Nat) :
    CheckSpec StateShape.singletonProgram (fun count => decide (count=1)) frame width := by
  intro words suffix
  let middle := parsedBank frame words suffix
  obtain ⟨ticks,peak,trace,timeBound⟩ := StateShape.singleton_ready middle words.length
    (by simp [middle,parsedBank,WordListReader.data_at]) (by simp [middle,parsedBank,WordListReader.data_at])
  refine ⟨ticks,peak,_,trace,by omega,?_,?_⟩
  · by_cases same : words.length=1 <;> simp [StateShape.field_at,same]
  · intro accepted
    have same : words.length=1 := of_decide_eq_true accepted
    funext address
    by_cases hc : address=none <;> by_cases hn : address=some 12 <;>
      simp_all [StateShape.field_at,StateShape.retainedCount,middle,parsedBank,WordListReader.data_at]

theorem valid_cost (frame : Port → List Bool) (words : List (Controller.Cost.Word width)) (suffix : List Bool) (ticks : Nat)
    (countEmpty : frame (some 10)=[]) (bufferEmpty : frame (some 11)=[]) (savedEmpty : frame (some 12)=[])
    (checkTime : ticks ≤ 12*mass (parsedBank frame words suffix)+14) :
    words.length*(22*width+24)+16+ticks+(4*(width+1)*words.length+10) ≤
      40*((Encoding.encodeWords width words++suffix).length+ambientBits frame)+40 := by
  have total := parsed_mass frame words suffix countEmpty bufferEmpty savedEmpty
  have length : (Encoding.encodeWords width words++suffix).length=(width+1)*words.length+1+suffix.length := by
    rw [List.length_append,Encoding.encodeWords_length]
  have countBound : words.length ≤ (width+1)*words.length := by
    calc
      _ = 1*words.length := (Nat.one_mul _).symm
      _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
  have identity : words.length*(22*width+24)+16+ticks+(4*(width+1)*words.length+10)=
      26*((width+1)*words.length)+2*words.length+ticks+26 := by ring
  rw [identity]
  omega

theorem total_execution (checker : Program (Fin 31) Q) (accepts : Nat → Bool) (frame : Port → List Bool)
    (slot : Fin 31) (high : 21 ≤ slot.val) (width : Nat) (input : List Bool)
    (stored : frame (some 8)=List.replicate width true) (countEmpty : frame (some 10)=[])
    (bufferEmpty : frame (some 11)=[]) (savedEmpty : frame (some 12)=[])
    (temporaryEmpty : frame (some 20)=[]) (targetEmpty : frame (some slot)=[])
    (check : CheckSpec checker accepts frame width) :
    ∃ ticks peak output, Execution (program checker slot) ⟨some (program checker slot).main,bank frame [] input []⟩
      ⟨none,output⟩ ticks peak ∧
      ticks ≤ 16*(input.length+ambientBits frame)^2+40*(input.length+ambientBits frame)+40 ∧
      peak ≤ 16*(input.length+ambientBits frame)^2+41*(input.length+ambientBits frame)+40 ∧
      Option.isNone ((output none).head?)=(readField accepts width input).isSome ∧
      (∀ words suffix, readField accepts width input=some (words,suffix) → output=WordFieldReader.packet frame slot width words suffix) := by
  cases decoded : Encoding.readFramedWords width input with
  | none =>
    obtain ⟨ticks,peak,parsing,timeBound,spaceBound⟩ := WordListTotal.total_polynomial frame width input stored countEmpty bufferEmpty savedEmpty
    have rejected : Option.isNone ((WordListTotal.parseResult frame width input none).head?)=false := by
      have equivalence := WordListTotal.parse_accept frame width input
      cases flag : Option.isNone ((WordListTotal.parseResult frame width input none).head?) <;> simp_all
    have trace := GuardedLink.failure (GuardedLink.program checker (WordFieldStore.program (some slot)) none Option.isNone)
      none Option.isNone parsing rejected
    refine ⟨ticks+1,peak,WordListTotal.parseResult frame width input,?_,by omega,by omega,?_,?_⟩
    · simpa only [program] using trace
    · simpa [readField,decoded] using rejected
    · intro words suffix impossible
      simp [readField,decoded] at impossible
  | some pair =>
    rcases pair with ⟨words,suffix⟩
    have shape := InstructionFrontend.framed_sound width input words suffix decoded
    obtain ⟨parsePeak,parsing⟩ := WordListReader.execution frame words suffix stored countEmpty bufferEmpty savedEmpty
    rw [← shape] at parsing
    obtain ⟨checkTicks,checkPeak,checked,checking,checkTime,accepted,unchanged⟩ := check words suffix
    have charged := valid_cost frame words suffix checkTicks countEmpty bufferEmpty savedEmpty checkTime
    rw [← shape] at charged
    by_cases pass : accepts words.length=true
    · have same := unchanged pass
      rw [same] at checking
      obtain ⟨storePeak,storing⟩ := WordFieldStore.ready_execution (parsedBank frame words suffix) (some slot) words
        (by intro same; have := congrArg (fun port => port.map Fin.val) same; simp at this; omega)
        (by intro same; have := congrArg (fun port => port.map Fin.val) same; simp at this; omega)
        (by intro same; have := congrArg (fun port => port.map Fin.val) same; simp at this; omega)
        (by simp [parsedBank,WordListReader.data_at]) (by simp [parsedBank,WordListReader.data_at])
        (by simp [parsedBank,WordListReader.data_at,temporaryEmpty])
      have endpoint := WordFieldReader.stored_packet frame slot high words suffix countEmpty bufferEmpty savedEmpty temporaryEmpty targetEmpty
      change WordFieldStore.fields (parsedBank frame words suffix) (some slot) [] []
        (Encoding.encodeWords width words++parsedBank frame words suffix (some slot)) []=WordFieldReader.packet frame slot width words suffix at endpoint
      rw [endpoint] at storing
      have checkedStore := GuardedLink.success none Option.isNone checking storing (by simp [parsedBank,WordListReader.data_at])
      have trace := GuardedLink.success none Option.isNone parsing checkedStore (by simp [WordListReader.data_at])
      have space := trace.peak_le
      simp only [bank_live,List.length_nil,Nat.zero_add,Nat.add_zero] at space
      refine ⟨words.length*(22*width+24)+16+(checkTicks+(4*(width+1)*words.length+10)),
        max parsePeak (max checkPeak storePeak),WordFieldReader.packet frame slot width words suffix,?_,by omega,by omega,?_,?_⟩
      · simpa only [program] using trace
      · simp [readField,decoded,pass,WordFieldReader.packet_at frame slot high]
      · intro other rest observed
        simp [readField,decoded,pass] at observed
        rcases observed with ⟨rfl,rfl⟩
        rfl
    · have failed : accepts words.length=false := by cases value : accepts words.length <;> simp_all
      have checkedStore := GuardedLink.failure (WordFieldStore.program (some slot)) none Option.isNone checking (accepted.trans failed)
      have trace := GuardedLink.success none Option.isNone parsing checkedStore (by simp [WordListReader.data_at])
      have space := trace.peak_le
      simp only [bank_live,List.length_nil,Nat.zero_add,Nat.add_zero] at space
      refine ⟨words.length*(22*width+24)+16+(checkTicks+1),max parsePeak checkPeak,checked,?_,by omega,by omega,?_,?_⟩
      · simpa only [program] using trace
      · simpa [readField,decoded,failed] using accepted.trans failed
      · intro other rest impossible
        simp [readField,decoded,failed] at impossible

theorem packet_mass (frame : Port → List Bool) (slot : Fin 31) (high : 21 ≤ slot.val)
    (words : List (Controller.Cost.Word width)) (suffix : List Bool) (targetEmpty : frame (some slot)=[]) :
    mass (WordFieldReader.packet frame slot width words suffix)=(Encoding.encodeWords width words++suffix).length+ambientBits frame := by
  have h₀ : slot ≠ 0 := by intro same; simp [same] at high
  have h₁ : slot ≠ 1 := by intro same; simp [same] at high
  have h₂ : slot ≠ 2 := by intro same; simp [same] at high
  have total := bank_live (Function.update frame (some slot) (Encoding.encodeWords width words)) (none : Option Unit) [] suffix []
  simp only [live,List.length_nil,Nat.zero_add,Nat.add_zero] at total
  change mass (WordFieldReader.packet frame slot width words suffix)=
    suffix.length+ambientBits (Function.update frame (some slot) (Encoding.encodeWords width words)) at total
  rw [ColdInput.ambient_saved frame slot h₀ h₁ h₂ _ targetEmpty] at total
  simpa only [List.length_append,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using total

theorem ready_total_execution (checker : Program (Fin 31) Q) (accepts : Nat → Bool) (input : Port → List Bool)
    (slot : Fin 31) (high : 21 ≤ slot.val) (width : Nat)
    (status : input none=[]) (word : input (some 1)=[]) (scratch : input (some 2)=[])
    (stored : input (some 8)=List.replicate width true) (countEmpty : input (some 10)=[])
    (bufferEmpty : input (some 11)=[]) (savedEmpty : input (some 12)=[])
    (temporaryEmpty : input (some 20)=[]) (targetEmpty : input (some slot)=[])
    (check : CheckSpec checker accepts input width) :
    ∃ ticks peak output, Execution (program checker slot) ⟨some (program checker slot).main,input⟩
      ⟨none,output⟩ ticks peak ∧ ticks ≤ 16*(mass input)^2+40*mass input+40 ∧
      peak ≤ 16*(mass input)^2+41*mass input+40 ∧
      Option.isNone ((output none).head?)=(readField accepts width (input (some 0))).isSome ∧
      (∀ words suffix, readField accepts width (input (some 0))=some (words,suffix) →
        output=WordFieldReader.packet input slot width words suffix) := by
  have entry := WordFieldReader.ready_bank input status word scratch
  obtain ⟨ticks,peak,output,trace,timeBound,spaceBound,accepted,observation⟩ :=
    total_execution checker accepts input slot high width (input (some 0)) stored countEmpty bufferEmpty savedEmpty temporaryEmpty targetEmpty check
  rw [entry] at trace
  have total := bank_live input (none : Option Unit) [] (input (some 0)) []
  rw [entry] at total
  simp only [live,List.length_nil,Nat.zero_add,Nat.add_zero] at total
  change mass input=(input (some 0)).length+ambientBits input at total
  rw [← total] at timeBound spaceBound
  exact ⟨ticks,peak,output,trace,timeBound,spaceBound,accepted,observation⟩

def registerProgram := program CountEquality.program 21
def pcProgram := program StateShape.singletonProgram 25

theorem register_total (input : Port → List Bool) (width registers : Nat)
    (status : input none=[]) (word : input (some 1)=[]) (scratch : input (some 2)=[])
    (storedWidth : input (some 8)=List.replicate width true) (storedRegisters : input (some 9)=List.replicate registers true)
    (countEmpty : input (some 10)=[]) (bufferEmpty : input (some 11)=[]) (savedEmpty : input (some 12)=[])
    (left : input (some 16)=[]) (right : input (some 17)=[]) (temporaryEmpty : input (some 20)=[]) (targetEmpty : input (some 21)=[]) :
    ∃ ticks peak output, Execution registerProgram ⟨some registerProgram.main,input⟩ ⟨none,output⟩ ticks peak ∧
      ticks ≤ 16*(mass input)^2+40*mass input+40 ∧ peak ≤ 16*(mass input)^2+41*mass input+40 ∧
      Option.isNone ((output none).head?)=(readField (fun count => decide (count=registers)) width (input (some 0))).isSome ∧
      (∀ words suffix, readField (fun count => decide (count=registers)) width (input (some 0))=some (words,suffix) →
        output=WordFieldReader.packet input 21 width words suffix) :=
  ready_total_execution CountEquality.program (fun count => decide (count=registers)) input 21 (by decide) width
    status word scratch storedWidth countEmpty bufferEmpty savedEmpty temporaryEmpty targetEmpty
    (register_spec input width registers storedRegisters left right temporaryEmpty)

theorem pc_total (input : Port → List Bool) (width : Nat)
    (status : input none=[]) (word : input (some 1)=[]) (scratch : input (some 2)=[])
    (stored : input (some 8)=List.replicate width true) (countEmpty : input (some 10)=[])
    (bufferEmpty : input (some 11)=[]) (savedEmpty : input (some 12)=[])
    (temporaryEmpty : input (some 20)=[]) (targetEmpty : input (some 25)=[]) :
    ∃ ticks peak output, Execution pcProgram ⟨some pcProgram.main,input⟩ ⟨none,output⟩ ticks peak ∧
      ticks ≤ 16*(mass input)^2+40*mass input+40 ∧ peak ≤ 16*(mass input)^2+41*mass input+40 ∧
      Option.isNone ((output none).head?)=(readField (fun count => decide (count=1)) width (input (some 0))).isSome ∧
      (∀ words suffix, readField (fun count => decide (count=1)) width (input (some 0))=some (words,suffix) →
        output=WordFieldReader.packet input 25 width words suffix) :=
  ready_total_execution StateShape.singletonProgram (fun count => decide (count=1)) input 25 (by decide) width
    status word scratch stored countEmpty bufferEmpty savedEmpty temporaryEmpty targetEmpty (singleton_spec input width)

theorem register_resident : (∑ label, statementSize (tmStatement (registerProgram.code label))) ≤ 1017 := by
  simpa [registerProgram,program,WordListReader.program,WordListReader.payloadProgram,WordListReader.restorePayload,
    WordListReader.loop,WordListReader.body,WordListReader.moveWord,WordListReader.restoreMachine,WordListReader.countMachine,
    WordFieldStore.program,WordFieldStore.first,WordFieldStore.third,WordFieldStore.last,WordFieldStore.delimiter,
    CountEquality.program,CountEquality.leftMachine,CountEquality.rightMachine,CountEquality.compareMachine,
    ColdInput.readSave,ColdInput.headerMachine,CountLoop.program,GuardedLink.program,StackFrames.relocate,
    WidthReader.program,WidthReader.counterMachine,StackCopy.program,WordReader.program,
    WordReader.cursorMachine,WordReader.reverseMachine,StackBlocks.transfer,StackBlocks.reverseProgram,link] using finiteTM_resident registerProgram

theorem pc_resident : (∑ label, statementSize (tmStatement (pcProgram.code label))) ≤ 819 := by
  simpa [pcProgram,program,WordListReader.program,WordListReader.payloadProgram,WordListReader.restorePayload,
    WordListReader.loop,WordListReader.body,WordListReader.moveWord,WordListReader.restoreMachine,WordListReader.countMachine,
    WordFieldStore.program,WordFieldStore.first,WordFieldStore.third,WordFieldStore.last,WordFieldStore.delimiter,
    ColdInput.readSave,ColdInput.headerMachine,CountLoop.program,GuardedLink.program,StackFrames.relocate,
    WidthReader.program,WidthReader.counterMachine,StackCopy.program,WordReader.program,
    WordReader.cursorMachine,WordReader.reverseMachine,StackBlocks.transfer,StackBlocks.reverseProgram,link] using finiteTM_resident pcProgram

end Controller.Complexity.CheckedWordField
