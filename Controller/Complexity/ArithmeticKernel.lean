module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.CopyBody

@[expose] public section

/-! Addition and XOR consume two native fixed-width buffer words, reverse the
actual computed bits and move the result into replacement27. Width zero and
modular overflow are included; every unselected physical bank is retained. -/
namespace Controller.Complexity.ArithmeticKernel
open StackMachine StackBlocks WordReader
open scoped BigOperators

def value (xorMode : Bool) (left right : Controller.Cost.Word width) : Controller.Cost.Word width :=
  Controller.Cost.word width (if xorMode then left.val ^^^ right.val else left.val+right.val)

def corePorts : Option Bool ↪ Port := StackFrames.threePorts (some 29) (some 28) (some 27) (by decide) (by decide) (by decide)
theorem corePorts_apply (port : Option Bool) : corePorts port=(match port with | none => some 29 | some false => some 28 | some true => some 27) := rfl

def CoreLabel : Bool → Type
  | false => WordArithmetic.Label
  | true => WordXor.Label
instance coreFintype (xorMode : Bool) : Fintype (CoreLabel xorMode) := by cases xorMode <;> dsimp [CoreLabel] <;> infer_instance

def core : (xorMode : Bool) → Program (Fin 31) (CoreLabel xorMode)
  | false => StackFrames.relocate corePorts WordArithmetic.program
  | true => StackFrames.relocate corePorts WordXor.program

def reversePorts : Option Bool ↪ Port := StackFrames.threePorts (some 29) (some 1) (some 2) (by decide) (by decide) (by decide)
theorem reversePorts_apply (port : Option Bool) : reversePorts port=(match port with | none => some 29 | some false => some 1 | some true => some 2) := rfl

def reversal := StackFrames.relocate reversePorts reverseProgram
def program (xorMode : Bool) := link (link (core xorMode) reversal) (WordMove.program (some 29) (some 27) (some 2))

def emptied (input : Port → List Bool) := Function.update (Function.update input (some 28) []) (some 27) []
def rawOutput (input : Port → List Bool) (word : List Bool) := Function.update (emptied input) (some 29) word
def output (input : Port → List Bool) (xorMode : Bool) (left right : Controller.Cost.Word width) :=
  Function.update (Function.update input (some 28) []) (some 27) (Encoding.bits width (value xorMode left right).val)

structure Ready (input : Port → List Bool) (left right : Controller.Cost.Word width) : Prop where
  leftStored : input (some 28)=Encoding.bits width left.val
  rightStored : input (some 27)=Encoding.bits width right.val
  resultEmpty : input (some 29)=[]
  wordEmpty : input (some 1)=[]
  scratchEmpty : input (some 2)=[]

theorem canonical_bits (width number : Nat) : Encoding.bits width (Controller.Cost.word width number).val=Encoding.bits width number := by
  have canonical := InstructionFrontend.bits_value (Encoding.bits width number)
  rw [Encoding.bits_length,WordArithmetic.value_bits_mod] at canonical
  exact canonical

theorem core_terminal (input : Port → List Bool) (word : List Bool) :
    StackFrames.embedStorage corePorts input (layout word [] [])=rawOutput input word := by
  funext address
  by_cases ho : address=some 29 <;> by_cases hl : address=some 28 <;> by_cases hr : address=some 27 <;>
    simp_all [StackFrames.embedStorage,corePorts_apply,layout,rawOutput,emptied]

theorem core_initial (input : Port → List Bool) (left right : Controller.Cost.Word width) (ready : Ready input left right) :
    StackFrames.embedStorage corePorts input (layout [] (Encoding.bits width left.val) (Encoding.bits width right.val))=input := by
  funext address
  by_cases ho : address=some 29 <;> by_cases hl : address=some 28 <;> by_cases hr : address=some 27 <;>
    simp_all [StackFrames.embedStorage,corePorts_apply,layout,ready.leftStored,ready.rightStored,ready.resultEmpty]

theorem core_execution (input : Port → List Bool) (xorMode : Bool) (left right : Controller.Cost.Word width) (ready : Ready input left right) :
    ∃ peak, Execution (core xorMode) ⟨some (core xorMode).main,input⟩
      ⟨none,rawOutput input (Encoding.bits width (value xorMode left right).val).reverse⟩ (3*width+2) peak := by
  cases xorMode with
  | false =>
    have trace := StackFrames.addition corePorts input width left.val right.val []
    have start : (WordArithmetic.state (some (WordArithmetic.entry false)) (Encoding.bits width left.val) (Encoding.bits width right.val) []).stk=
        layout [] (Encoding.bits width left.val) (Encoding.bits width right.val) := rfl
    have position : (WordArithmetic.state (some (WordArithmetic.entry false)) (Encoding.bits width left.val) (Encoding.bits width right.val) []).pc=
        some WordArithmetic.program.main := rfl
    exact ⟨2*width+0+StackFrames.frameBits corePorts input,by
      simpa only [core,CoreLabel,StackFrames.relocate,StackFrames.embedState,start,core_initial input left right ready,
        position,terminal_layout,core_terminal,List.append_nil,List.length_nil,value,canonical_bits,Bool.false_eq_true,ite_false] using trace⟩
  | true =>
    have trace := StackFrames.xor corePorts input width left.val right.val []
    have start : (WordXor.state (some WordXor.entry) (Encoding.bits width left.val) (Encoding.bits width right.val) []).stk=
        layout [] (Encoding.bits width left.val) (Encoding.bits width right.val) := rfl
    have position : (WordXor.state (some WordXor.entry) (Encoding.bits width left.val) (Encoding.bits width right.val) []).pc=
        some WordXor.program.main := rfl
    exact ⟨2*width+0+StackFrames.frameBits corePorts input,by
      simpa only [core,CoreLabel,StackFrames.relocate,StackFrames.embedState,start,core_initial input left right ready,
        position,terminal_layout,core_terminal,List.append_nil,List.length_nil,value,canonical_bits,ite_true] using trace⟩

theorem reverse_storage (input : Port → List Bool) (word : List Bool) (wordEmpty : input (some 1)=[]) (scratchEmpty : input (some 2)=[]) :
    StackFrames.embedStorage reversePorts (emptied input) (layout word [] [])=rawOutput input word := by
  funext address
  by_cases ho : address=some 29 <;> by_cases hw : address=some 1 <;> by_cases ht : address=some 2 <;>
    simp_all [StackFrames.embedStorage,reversePorts_apply,layout,rawOutput,emptied]

theorem execution (input : Port → List Bool) (xorMode : Bool) (left right : Controller.Cost.Word width) (ready : Ready input left right) :
    ∃ peak, Execution (program xorMode) ⟨some (program xorMode).main,input⟩
      ⟨none,output input xorMode left right⟩ (13*width+12) peak := by
  obtain ⟨corePeak,calculating⟩ := core_execution input xorMode left right ready
  let word := Encoding.bits width (value xorMode left right).val
  have reversing := StackFrames.reversal reversePorts (emptied input) word.reverse
  simp only [StackFrames.embedState,initial_layout,terminal_layout,reverse_storage input _ ready.wordEmpty ready.scratchEmpty,
    List.reverse_reverse,List.length_reverse,word,Encoding.bits_length] at reversing
  obtain ⟨movePeak,moving⟩ := WordMove.execution (rawOutput input word) (some 29) (some 27) (some 2)
    (by decide) (by decide) (by decide) (by simp [rawOutput,emptied,ready.scratchEmpty])
  simp only [rawOutput,Function.update_self,word,Encoding.bits_length,emptied,
    Function.update_of_ne (show (some 27 : Port) ≠ some 29 by decide),List.append_nil] at moving
  have final : Function.update (Function.update (rawOutput input word) (some 29) []) (some 27) word=output input xorMode left right := by
    funext address
    by_cases hl : address=some 28 <;> by_cases hr : address=some 27 <;> by_cases ho : address=some 29 <;>
      simp_all [rawOutput,emptied,output,word,ready.resultEmpty]
  rw [show Function.update (Function.update (Function.update (Function.update (Function.update input (some 28) []) (some 27) []) (some 29) word) (some 29) []) (some 27) word=output input xorMode left right from final] at moving
  have trace := (calculating.link reversing).link moving
  have ticks : ((3*width+2)+(6*width+6))+(4*width+4)=13*width+12 := by omega
  exact ⟨_,by simpa only [program,reversal,ticks] using trace⟩

theorem stored_output (input : Port → List Bool) (xorMode : Bool) (left right : Controller.Cost.Word width)
    (state : Controller.Cost.State width registers) (stored : NativeStore.Stored input state) :
    NativeStore.Stored (output input xorMode left right) state :=
  (stored.update_other input state (some 28) [] (by decide)).update_other (Function.update input (some 28) []) state
    (some 27) (Encoding.bits width (value xorMode left right).val) (by decide)

theorem clear_output (input : Port → List Bool) (xorMode : Bool) (left right : Controller.Cost.Word width)
    (clean : ∀ port ∈ FieldSet.work, input port=[]) : ∀ port ∈ FieldSet.work, output input xorMode left right port=[] := by
  intro port member
  have hl : port ≠ (some 28 : Port) := by intro equal; subst port; simp [FieldSet.work] at member
  have hr : port ≠ (some 27 : Port) := by intro equal; subst port; simp [FieldSet.work] at member
  simpa [output,hl,hr] using clean port member

theorem size_output (input : Port → List Bool) (xorMode : Bool) (left right : Controller.Cost.Word width) :
    FetchSetup.size (output input xorMode left right) ≤ FetchSetup.size input+width := by
  have first := OperandLoad.update_size_le input (some 28) []
  have second := OperandLoad.update_size_le (Function.update input (some 28) []) (some 27) (Encoding.bits width (value xorMode left right).val)
  simp only [List.length_nil,Nat.add_zero,Encoding.bits_length] at first second
  change FetchSetup.size (output input xorMode left right) ≤ FetchSetup.size (Function.update input (some 28) [])+width at second
  omega

theorem core_card (xorMode : Bool) : Fintype.card (CoreLabel xorMode)=(if xorMode then 7 else 13) := by
  cases xorMode with
  | false =>
    have same : Fintype.card (CoreLabel false)=Fintype.card WordArithmetic.Label :=
      @Fintype.card_congr (CoreLabel false) WordArithmetic.Label _ _ (Equiv.refl _)
    exact same.trans (by simp only [WordArithmetic.Label,Fintype.card_option,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,Nat.reduceMul,Nat.reduceAdd,Bool.false_eq_true,ite_false])
  | true =>
    have same : Fintype.card (CoreLabel true)=Fintype.card WordXor.Label :=
      @Fintype.card_congr (CoreLabel true) WordXor.Label _ _ (Equiv.refl _)
    exact same.trans (by simp only [WordXor.Label,Fintype.card_option,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,Nat.reduceMul,Nat.reduceAdd,ite_true])

theorem canonical_card (xorMode : Bool) : Fintype.card (StateReader.LabelsOf (program xorMode))=(if xorMode then 27 else 33) := by
  have split : Fintype.card (StateReader.LabelsOf (program xorMode))=(Fintype.card (CoreLabel xorMode)+12)+8 := by
    change Fintype.card ((CoreLabel xorMode ⊕ ((Fin 4 ⊕ Fin 4) ⊕ Fin 4)) ⊕ (Fin 4 ⊕ Fin 4))=_
    simp only [Fintype.card_sum,Fintype.card_fin,Nat.reduceAdd]
  rw [core_card] at split
  cases xorMode <;> simp only [Bool.false_eq_true,ite_false,ite_true,Nat.reduceAdd] at split ⊢ <;> exact split

theorem resident (xorMode : Bool) : (∑ label, statementSize (tmStatement ((program xorMode).code label))) ≤ 297 := by
  have bound := finiteTM_resident (program xorMode)
  rw [show Fintype.card (StateReader.LabelsOf (program xorMode))=(if xorMode then 27 else 33) from canonical_card xorMode] at bound
  cases xorMode <;> simp only [Bool.false_eq_true,ite_false,ite_true,Nat.reduceMul] at bound
  · exact bound
  · exact bound.trans (by decide)

end Controller.Complexity.ArithmeticKernel
