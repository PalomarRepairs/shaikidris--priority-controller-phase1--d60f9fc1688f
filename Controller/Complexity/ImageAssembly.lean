module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.ImageHeaders
public import Controller.Complexity.ProgramTotal
public import Controller.Complexity.StateNative

@[expose] public section

/-! Program and state parsing share the actual bank produced by cold header
validation. Successful program parsing consumes its delimiter while retaining
code and count; state parsing uses the resulting conserved storage budget. -/
namespace Controller.Complexity.ImageAssembly
open StackMachine WordReader
open CheckedWordField (mass)
open scoped BigOperators

def CodeLabel : Type := StateReader.LabelsOf ProgramReader.program

instance codeFintype : Fintype CodeLabel := inferInstanceAs (Fintype (StateReader.LabelsOf ProgramReader.program))

def codeProgram : Program (Fin 31) CodeLabel := ProgramReader.program

def Label : Type := CodeLabel ⊕ Option (StateReader.Label StateReader.fields)

instance labelFintype : Fintype Label := inferInstanceAs (Fintype (CodeLabel ⊕ Option (StateReader.Label StateReader.fields)))

def program : Program (Fin 31) Label := GuardedLink.program codeProgram StateReader.stateProgram none Option.isNone

def read (width registers : Nat) (source : List Bool) :
    Option (List (Controller.Cost.Instruction width registers) × Controller.Cost.State width registers) := do
  let (instructions,suffix) ← ProgramSyntax.readPrefix width registers source
  let state ← MachineBridge.decodeState width registers suffix
  return (instructions,state)

def polynomial (size : Nat) := 32*size^4+256*size^3+480*size^2+615*size+227

def codeBank (width registers : Nat) (bound : registers ≤ 2^width) (source : List Bool)
    (instructions : List (Controller.Cost.Instruction width registers)) (suffix : List Bool) : Port → List Bool :=
  ProgramReader.data (Function.update (ImageHeaders.data width registers [] source) (some 15) (List.replicate instructions.length true))
    0 suffix (InstructionCodec.encodeMany bound instructions)

theorem code_at (width registers : Nat) (bound : registers ≤ 2^width) (source : List Bool)
    (instructions : List (Controller.Cost.Instruction width registers)) (suffix : List Bool) (address : Port) :
    codeBank width registers bound source instructions suffix address=
      if address=none then [] else if address=some 0 then suffix else if address=some 8 then List.replicate width true
      else if address=some 9 then List.replicate registers true else if address=some 15 then List.replicate instructions.length true
      else if address=some 19 then InstructionCodec.encodeMany bound instructions else [] := by
  by_cases hc : address=none <;> by_cases hs : address=some 0 <;> by_cases hw : address=some 1 <;>
    by_cases ht : address=some 2 <;> by_cases hn : address=some 14 <;> by_cases hp : address=some 15 <;>
    by_cases hb : address=some 19 <;> simp_all [codeBank,ProgramReader.data_at,ImageHeaders.data_at]

theorem header_workspace (width registers : Nat) (source : List Bool) :
    ProgramTotal.Workspace (ImageHeaders.data width registers [] source) width registers := by
  constructor <;> simp [ImageHeaders.data_at]

theorem header_entry (width registers : Nat) (source : List Bool) :
    bank (ImageHeaders.data width registers [] source) [] source []=ImageHeaders.data width registers [] source := by
  have entry := WordFieldReader.ready_bank (ImageHeaders.data width registers [] source)
    (by simp [ImageHeaders.data_at]) (by simp [ImageHeaders.data_at]) (by simp [ImageHeaders.data_at])
  have sourceEq : ImageHeaders.data width registers [] source (some 0)=source := by simp [ImageHeaders.data_at]
  simpa only [sourceEq] using entry

theorem header_size (width registers : Nat) (source : List Bool) :
    mass (ImageHeaders.data width registers [] source)=source.length+ambientBits (ImageHeaders.data width registers [] source) := by
  have total := bank_live (ImageHeaders.data width registers [] source) (none : Option Unit) [] source []
  rw [header_entry] at total
  simpa only [live,CheckedWordField.mass,List.length_nil,Nat.zero_add,Nat.add_zero] using total

theorem header_mass (width registers : Nat) (source : List Bool) :
    mass (ImageHeaders.data width registers [] source)=width+registers+source.length := by
  have widthBits := ColdInput.ambient_saved ColdInput.emptyFrame 8 (by decide) (by decide) (by decide) (List.replicate width true) rfl
  have registerBits := ColdInput.ambient_saved (Function.update ColdInput.emptyFrame (some 8) (List.replicate width true)) 9
    (by decide) (by decide) (by decide) (List.replicate registers true) (by simp [ColdInput.emptyFrame])
  have total := bank_live (ColdInput.savedFrame ColdInput.emptyFrame width registers) (none : Option Unit) [] source []
  simp only [live,List.length_nil,Nat.zero_add,Nat.add_zero] at total
  change mass (ImageHeaders.data width registers [] source)=source.length+ambientBits (ColdInput.savedFrame ColdInput.emptyFrame width registers) at total
  rw [ColdInput.savedFrame,registerBits,widthBits,ColdInput.empty_ambient] at total
  simp only [List.length_replicate] at total
  omega

theorem code_ready (width registers : Nat) (bound : registers ≤ 2^width) (source : List Bool)
    (instructions : List (Controller.Cost.Instruction width registers)) (suffix : List Bool) :
    StateReader.Ready (codeBank width registers bound source instructions suffix) width registers StateReader.fields := by
  refine ⟨by simp [code_at],by simp [code_at],by simp [code_at],?_,?_,by simp [code_at]⟩
  · intro index member
    simp [StateReader.work] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [code_at]
  · intro field _
    cases field <;> simp [code_at,StateReader.Field.slot]

theorem code_mass (width registers : Nat) (bound : registers ≤ 2^width) (source : List Bool)
    (instructions : List (Controller.Cost.Instruction width registers)) (suffix : List Bool)
    (parsed : ProgramSyntax.readPrefix width registers source=some (instructions,suffix)) :
    mass (codeBank width registers bound source instructions suffix)+1=mass (ImageHeaders.data width registers [] source) := by
  let frame := ImageHeaders.data width registers [] source
  let saved := Function.update frame (some 15) (List.replicate instructions.length true)
  have savedBits : ambientBits saved=ambientBits frame+instructions.length := by
    simpa only [saved,List.length_replicate] using ColdInput.ambient_saved frame 15 (by decide) (by decide) (by decide)
      (List.replicate instructions.length true) (by simp [frame,ImageHeaders.data_at])
  have fieldBits := ProgramTotal.ambient_fields saved 0 (InstructionCodec.encodeMany bound instructions)
    (by simp [saved,frame,ImageHeaders.data_at]) (by simp [saved,frame,ImageHeaders.data_at])
  have total := bank_live (ProgramReader.fields saved 0 (InstructionCodec.encodeMany bound instructions)) (none : Option Unit) [] suffix []
  simp only [live,List.length_nil,Nat.zero_add,Nat.add_zero] at total
  change mass (codeBank width registers bound source instructions suffix)=
    suffix.length+ambientBits (ProgramReader.fields saved 0 (InstructionCodec.encodeMany bound instructions)) at total
  rw [fieldBits,savedBits] at total
  have initial := bank_live frame (none : Option Unit) [] source []
  rw [header_entry] at initial
  simp only [live,List.length_nil,Nat.zero_add,Nat.add_zero] at initial
  change mass frame=source.length+ambientBits frame at initial
  have shape := ProgramSyntax.prefix_inverse bound source instructions suffix parsed
  have length : source.length=instructions.length+(InstructionCodec.encodeMany bound instructions).length+suffix.length+1 := by
    rw [shape]
    simp only [Encoding.frameCount,List.length_append,List.length_replicate,List.length_cons]
    omega
  change _=mass frame
  rw [initial]
  omega

def bodyBytes (input : Port → List Bool) := input (some 15)++false :: (input (some 19)++StateNative.storedBytes input)

theorem store_low (input : Port → List Bool) (width : Nat) (values : List (List (Controller.Cost.Word width))) (halt : Bool)
    (index : Fin 31) (low : index.val < 21) (notSource : index ≠ 0) :
    StateReader.store input width StateReader.fields values halt (some index)=input (some index) := by
  apply StateNative.store_other input width StateReader.fields values halt (some index) (by simp) (by simpa)
  · intro same
    have equal : index=26 := Option.some.inj same
    simp [equal] at low
  · intro field _ same
    have equal : index=field.slot := Option.some.inj same
    have high := field.slot_high
    rw [← equal] at high
    omega

theorem stored_body (width registers : Nat) (bound : registers ≤ 2^width) (source : List Bool)
    (instructions : List (Controller.Cost.Instruction width registers)) (suffix : List Bool)
    (values : List (List (Controller.Cost.Word width))) (halt : Bool)
    (parsed : ProgramSyntax.readPrefix width registers source=some (instructions,suffix))
    (stateRead : StateReader.read width registers StateReader.fields suffix=some (values,halt)) :
    bodyBytes (StateReader.store (codeBank width registers bound source instructions suffix) width StateReader.fields values halt)=source := by
  obtain ⟨shape,length⟩ := StateNative.read_inverse width registers StateReader.fields suffix values halt stateRead
  have five : values.length=5 := by simpa only [StateReader.fields,List.length_cons,List.length_nil] using length
  unfold bodyBytes
  rw [store_low _ width values halt 15 (by decide) (by decide),store_low _ width values halt 19 (by decide) (by decide),
    StateNative.stored_bytes _ values halt five,← shape]
  have original := ProgramSyntax.prefix_inverse bound source instructions suffix parsed
  simpa [code_at,Encoding.frameCount] using original.symm

theorem program_reject_time (size ticks : Nat) (bounded : ticks ≤ ProgramTotal.polynomial size) : ticks+1 ≤ polynomial size := by
  unfold polynomial ProgramTotal.polynomial at *
  omega

theorem join_time (size stored first second : Nat) (smaller : stored ≤ size)
    (firstBound : first ≤ ProgramTotal.polynomial size) (secondBound : second ≤ 80*stored^2+200*stored+210) :
    first+second ≤ polynomial size := by
  have square := Nat.pow_le_pow_left smaller 2
  unfold polynomial ProgramTotal.polynomial at *
  omega

theorem total_execution (width registers : Nat) (bound : registers ≤ 2^width) (source : List Bool) :
    ∃ ticks peak output, Execution program ⟨some program.main,ImageHeaders.data width registers [] source⟩ ⟨none,output⟩ ticks peak ∧
      ticks ≤ polynomial (mass (ImageHeaders.data width registers [] source)) ∧
      peak ≤ polynomial (mass (ImageHeaders.data width registers [] source))+mass (ImageHeaders.data width registers [] source) ∧
      Option.isNone ((output none).head?)=(read width registers source).isSome ∧
      (∀ instructions state, read width registers source=some (instructions,state) →
        bodyBytes output=source ∧ output (some 8)=List.replicate width true ∧ output (some 9)=List.replicate registers true ∧
        output none=[] ∧ output (some 0)=[]) := by
  obtain ⟨final,ticks,peak,first,halted,accepted,observed,timeBound,spaceBound⟩ :=
    ProgramTotal.total_decodes (ImageHeaders.data width registers [] source) bound source (header_workspace width registers source)
      (by simp [ImageHeaders.data_at]) (by simp [ImageHeaders.data_at]) (by simp [ImageHeaders.data_at])
  rw [header_entry] at first
  rw [← header_size] at timeBound spaceBound
  have terminal : final=⟨none,final.stk⟩ := congrArg₂ State.mk halted rfl
  rw [terminal] at first
  cases parsed : ProgramSyntax.readPrefix width registers source with
  | none =>
    have rejected : Option.isNone ((final.stk none).head?)=false := by simpa only [parsed,Option.isSome_none] using accepted
    have trace := GuardedLink.failure StateReader.stateProgram none Option.isNone first rejected
    have finalTime := program_reject_time (mass (ImageHeaders.data width registers [] source)) ticks timeBound
    have space := trace.peak_le
    change peak ≤ mass (ImageHeaders.data width registers [] source)+(ticks+1) at space
    refine ⟨ticks+1,peak,final.stk,trace,finalTime,by omega,?_,?_⟩
    · simpa [read,parsed] using rejected
    · intro instructions state impossible
      simp [read,parsed] at impossible
  | some pair =>
    rcases pair with ⟨instructions,suffix⟩
    obtain ⟨endpoint,programObserved,unread⟩ := observed instructions suffix parsed
    change final.stk=codeBank width registers bound source instructions suffix at endpoint
    rw [endpoint] at first
    have smaller := code_mass width registers bound source instructions suffix parsed
    obtain ⟨stateTicks,statePeak,output,second,stateTime,stateSpace,stateAccepted,stateObserved⟩ :=
      StateReader.state_total width registers (codeBank width registers bound source instructions suffix)
        (code_ready width registers bound source instructions suffix)
    have sourceEq : codeBank width registers bound source instructions suffix (some 0)=suffix := by simp [code_at]
    rw [sourceEq] at stateAccepted stateObserved
    rw [StateNative.accepts_native] at stateAccepted
    have trace := GuardedLink.success none Option.isNone first second (by simp [code_at])
    have finalTime := join_time (mass (ImageHeaders.data width registers [] source))
      (mass (codeBank width registers bound source instructions suffix)) ticks stateTicks (by omega) timeBound stateTime
    have space := trace.peak_le
    change max peak statePeak ≤ mass (ImageHeaders.data width registers [] source)+(ticks+stateTicks) at space
    refine ⟨ticks+stateTicks,max peak statePeak,output,trace,finalTime,by omega,?_,?_⟩
    · cases decoded : MachineBridge.decodeState width registers suffix <;> simpa [read,parsed,decoded] using stateAccepted
    · intro givenInstructions givenState bodyRead
      have hasState : (MachineBridge.decodeState width registers suffix).isSome=true := by
        cases decoded : MachineBridge.decodeState width registers suffix with
        | none => simp [read,parsed,decoded] at bodyRead
        | some state => rfl
      have hasParts : (StateReader.read width registers StateReader.fields suffix).isSome=true := by
        rw [StateNative.accepts_native]
        exact hasState
      obtain ⟨⟨values,halt⟩,partsRead⟩ := Option.isSome_iff_exists.mp hasParts
      rw [stateObserved values halt partsRead]
      refine ⟨stored_body width registers bound source instructions suffix values halt parsed partsRead,?_,?_,?_,?_⟩
      · rw [store_low _ width values halt 8 (by decide) (by decide)]
        simp [code_at]
      · rw [store_low _ width values halt 9 (by decide) (by decide)]
        simp [code_at]
      · exact StateNative.store_status _ width StateReader.fields values halt
      · exact StateNative.store_eof _ width StateReader.fields values halt

theorem program_card : Fintype.card CodeLabel=853 := by
  have original : Fintype.card (StateReader.LabelsOf ProgramReader.program)=853 := by
    simp only [StateReader.LabelsOf,Fintype.card_sum,Fintype.card_option,Fintype.card_fin,OpcodeArity.label_card,OpcodeRoles.label_card,
      OperandCheck.Label,RegisterRange.Label,WordBound.Label,WordBound.BodyLabel,Nat.reduceAdd]
  have same : Fintype.card CodeLabel=Fintype.card (StateReader.LabelsOf ProgramReader.program) :=
    @Fintype.card_congr CodeLabel (StateReader.LabelsOf ProgramReader.program) _ _ (Equiv.refl _)
  exact same.trans original


theorem canonical_card : Fintype.card (StateReader.LabelsOf program)=1325 := by
  have split : Fintype.card (StateReader.LabelsOf program)=
      Fintype.card CodeLabel+Fintype.card (Option (StateReader.Label StateReader.fields)) :=
    Fintype.card_sum
  have optional : Fintype.card (Option (StateReader.Label StateReader.fields))=Fintype.card (StateReader.Label StateReader.fields)+1 :=
    Fintype.card_option
  rw [program_card,optional,StateReader.canonical_card] at split
  exact split

theorem resident : (∑ label, statementSize (tmStatement (program.code label))) ≤ 11925 := by
  have bound := finiteTM_resident (K := Fin 31) (Q := StateReader.LabelsOf program) program
  rw [canonical_card] at bound
  exact bound

end Controller.Complexity.ImageAssembly


