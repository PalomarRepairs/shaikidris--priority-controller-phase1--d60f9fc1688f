module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.ShrinkFields
public import Controller.Complexity.InstructionEndpoint
public import Controller.Complexity.StateReader

public import Mathlib.Tactic.Ring

@[expose] public section

/-! A counted instruction-prefix traversal executes the native instruction
parser and erases only parsed operand/tag fields between iterations. Original
program/count and all unrelated banks are preserved; the exact suffix remains. -/
namespace Controller.Complexity.InstructionSkip
open StackMachine WordReader
open scoped BigOperators

structure Ready (frame : Port → List Bool) (width registers : Nat) : Prop where
  stored : frame (some 8)=List.replicate width true
  saved : frame (some 9)=List.replicate registers true
  count : frame (some 10)=[]
  payload : frame (some 11)=[]
  arity : frame (some 12)=[]
  tag : frame (some 13)=[]
  bound : frame (some 16)=[]
  scratch : frame (some 17)=[]
  roles : frame (some 18)=[]

def data (frame : Port → List Bool) (count : Nat) (source : List Bool) := WordSkip.data frame count source

def clearFields := link (link (StackClear.program (some 11 : Port)) (StackClear.program (some 12 : Port))) (StackClear.program (some 13 : Port))
def cleared (input : Port → List Bool) := Function.update (Function.update (Function.update input (some 11) []) (some 12) []) (some 13) []

def ParseLabel : Type := StateReader.LabelsOf InstructionEndpoint.program
instance parseFintype : Fintype ParseLabel := inferInstanceAs (Fintype (StateReader.LabelsOf InstructionEndpoint.program))
def parseProgram : Program (Fin 31) ParseLabel := InstructionEndpoint.program

def BodyLabel : Type := ParseLabel ⊕ ((Fin 2 ⊕ Fin 2) ⊕ Fin 2)
instance bodyFintype : Fintype BodyLabel := inferInstanceAs (Fintype (ParseLabel ⊕ ((Fin 2 ⊕ Fin 2) ⊕ Fin 2)))
def body : Program (Fin 31) BodyLabel := link parseProgram clearFields

def Label : Type := BodyLabel ⊕ Option (Fin 2)
instance labelFintype : Fintype Label := inferInstanceAs (Fintype (BodyLabel ⊕ Option (Fin 2)))
def program : Program (Fin 31) Label := CountLoop.program body (some 4) none Option.isNone

theorem clear_execution (input : Port → List Bool) :
    ∃ peak, Execution clearFields ⟨some clearFields.main,input⟩ ⟨none,cleared input⟩
      ((input (some 11)).length+(input (some 12)).length+(input (some 13)).length+6) peak := by
  obtain ⟨p₁,one⟩ := StackClear.ready_execution input (some 11)
  obtain ⟨p₂,two⟩ := StackClear.ready_execution (Function.update input (some 11) []) (some 12)
  obtain ⟨p₃,three⟩ := StackClear.ready_execution (Function.update (Function.update input (some 11) []) (some 12) []) (some 13)
  simp only [Function.update_of_ne (show (some 12 : Port) ≠ some 11 by decide)] at two
  simp only [Function.update_of_ne (show (some 13 : Port) ≠ some 12 by decide),Function.update_of_ne (show (some 13 : Port) ≠ some 11 by decide)] at three
  have ticks : ((input (some 11)).length+2)+((input (some 12)).length+2)+((input (some 13)).length+2)=
      (input (some 11)).length+(input (some 12)).length+(input (some 13)).length+6 := by omega
  exact ⟨_,by simpa only [clearFields,cleared,ticks] using (one.link two).link three⟩

theorem cleared_endpoint (frame : Port → List Bool) (opcode : Fin 16) (operands : List (Controller.Cost.Word width))
    (count : Nat) (suffix : List Bool) (countEmpty : frame (some 10)=[]) (payload : frame (some 11)=[]) (arity : frame (some 12)=[]) (tag : frame (some 13)=[]) :
    cleared (InstructionShape.fieldsData (Function.update frame (some 4) (List.replicate count true)) opcode operands suffix)=data frame count suffix := by
  funext address
  by_cases hp : address=some 11 <;> by_cases ha : address=some 12 <;> by_cases ht : address=some 13 <;>
    by_cases hc : address=some 10 <;> simp_all [cleared,InstructionRange.fields_at,data,WordSkip.data_at]
  all_goals split_ifs <;> simp_all

theorem body_execution (frame : Port → List Bool) (bound : registers ≤ 2^width) (instruction : Controller.Cost.Instruction width registers)
    (count : Nat) (suffix : List Bool) (ready : Ready frame width registers) :
    ∃ ticks peak, Execution body ⟨some body.main,data frame count (InstructionCodec.encode bound instruction++suffix)⟩
      ⟨none,data frame count suffix⟩ ticks peak ∧ ticks ≤ 12*width*registers+141*width+18*registers+300 := by
  let opcode : Fin 16 := ⟨(InstructionCodec.fields bound instruction).1,InstructionCodec.fields_tag_lt bound instruction⟩
  let operands := (InstructionCodec.fields bound instruction).2
  obtain ⟨readTicks,readPeak,reading,readBound,_⟩ := InstructionEndpoint.execution (Function.update frame (some 4) (List.replicate count true))
    bound instruction suffix (by simpa using ready.stored) (by simpa using ready.saved) (by simpa using ready.count)
    (by simpa using ready.payload) (by simpa using ready.arity) (by simpa using ready.tag)
    (by simpa using ready.bound) (by simpa using ready.scratch) (by simpa using ready.roles)
  obtain ⟨clearPeak,clearing⟩ := clear_execution (InstructionShape.fieldsData (Function.update frame (some 4) (List.replicate count true)) opcode operands suffix)
  rw [cleared_endpoint frame opcode operands count suffix ready.count ready.payload ready.arity ready.tag] at clearing
  have clearTicks : ((InstructionShape.fieldsData (Function.update frame (some 4) (List.replicate count true)) opcode operands suffix (some 11)).length+
      (InstructionShape.fieldsData (Function.update frame (some 4) (List.replicate count true)) opcode operands suffix (some 12)).length+
      (InstructionShape.fieldsData (Function.update frame (some 4) (List.replicate count true)) opcode operands suffix (some 13)).length+6)=
      (width+1)*operands.length+10 := by
    simp [InstructionRange.fields_at,Encoding.wordList_length]
    ring
  rw [clearTicks] at clearing
  have trace := reading.link clearing
  have arityBound := InstructionCodec.fields_length_le bound instruction
  change operands.length ≤ 3 at arityBound
  have product := Nat.mul_le_mul_left (width+1) arityBound
  have identity : (12*width*registers+138*width+18*registers+287)+((width+1)*3+10)=
      12*width*registers+141*width+18*registers+300 := by ring
  exact ⟨_,_,by simpa only [body,parseProgram,BodyLabel,ParseLabel,data,WordSkip.data] using trace,by omega⟩

theorem execution (frame : Port → List Bool) (bound : registers ≤ 2^width) (instructions : List (Controller.Cost.Instruction width registers))
    (suffix : List Bool) (ready : Ready frame width registers) :
    ∃ ticks peak, Execution program ⟨some program.main,data frame instructions.length (InstructionCodec.encodeMany bound instructions++suffix)⟩
      ⟨none,data frame 0 suffix⟩ ticks peak ∧ ticks ≤ instructions.length*(12*width*registers+141*width+18*registers+301)+2 := by
  induction instructions with
  | nil =>
    have trace := CountLoop.empty body (some 4) none Option.isNone (data frame 0 suffix) (by simp [data,WordSkip.data_at])
    exact ⟨2,_,by simpa only [program,Label,InstructionCodec.encodeMany,List.flatMap_nil,List.length_nil,List.nil_append] using trace,by simp⟩
  | cons instruction instructions ih =>
    obtain ⟨tailTicks,tailPeak,tail,tailBound⟩ := ih
    obtain ⟨bodyTicks,bodyPeak,working,bodyBound⟩ := body_execution frame bound instruction instructions.length (InstructionCodec.encodeMany bound instructions++suffix) ready
    have counted : data frame (instructions.length+1) (InstructionCodec.encode bound instruction++(InstructionCodec.encodeMany bound instructions++suffix)) (some 4)=
        true :: List.replicate instructions.length true := by simp [data,WordSkip.data_at,List.replicate_succ]
    have adjusted : Execution body
        ⟨some body.main,Function.update (data frame (instructions.length+1) (InstructionCodec.encode bound instruction++(InstructionCodec.encodeMany bound instructions++suffix)))
          (some 4) (List.replicate instructions.length true)⟩
        ⟨none,data frame instructions.length (InstructionCodec.encodeMany bound instructions++suffix)⟩ bodyTicks bodyPeak := by
      simpa only [data,WordSkip.decrement] using working
    obtain ⟨peak,trace⟩ := CountLoop.next (some 4) none Option.isNone counted adjusted (by simp [data,WordSkip.data_at]) tail
    refine ⟨bodyTicks+tailTicks+1,peak,?_,?_⟩
    · simpa only [program,Label,InstructionCodec.encodeMany,List.flatMap_cons,List.length_cons,List.append_assoc] using trace
    · simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      omega

theorem parse_card : Fintype.card ParseLabel=798 := by
  have original : Fintype.card (StateReader.LabelsOf InstructionEndpoint.program)=798 := by
    simp only [StateReader.LabelsOf,Fintype.card_sum,Fintype.card_option,Fintype.card_fin,OpcodeArity.label_card,OpcodeRoles.label_card,
      OperandCheck.Label,RegisterRange.Label,WordBound.Label,WordBound.BodyLabel,Nat.reduceAdd]
  have same : Fintype.card ParseLabel=Fintype.card (StateReader.LabelsOf InstructionEndpoint.program) :=
    @Fintype.card_congr ParseLabel (StateReader.LabelsOf InstructionEndpoint.program) _ _ (Equiv.refl _)
  exact same.trans original

theorem body_card : Fintype.card BodyLabel=804 := by
  have split : Fintype.card BodyLabel=Fintype.card ParseLabel+Fintype.card ((Fin 2 ⊕ Fin 2) ⊕ Fin 2) := Fintype.card_sum
  rw [parse_card] at split
  simpa only [Fintype.card_sum,Fintype.card_fin,Nat.reduceAdd] using split

theorem canonical_card : Fintype.card Label=807 := by
  have split : Fintype.card Label=Fintype.card BodyLabel+Fintype.card (Option (Fin 2)) := Fintype.card_sum
  rw [body_card] at split
  simpa only [Fintype.card_option,Fintype.card_fin,Nat.reduceAdd] using split

theorem resident : (∑ label, statementSize (tmStatement (program.code label))) ≤ 7263 := by
  have bound := finiteTM_resident program
  rw [canonical_card] at bound
  exact bound

end Controller.Complexity.InstructionSkip
