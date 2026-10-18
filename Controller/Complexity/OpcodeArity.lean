module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.StackEvaluation
public import Controller.Complexity.StackTail
public import Controller.Complexity.InstructionFields
public import Mathlib.Tactic.DeriveFintype

@[expose] public section

/-! A finite opcode/arity checker reads and restores the saved four-bit tag
and unary operand count. Reserved tags and mismatched arities set the error
flag. All decisions are finite control; operand register ranges are separate. -/
namespace Controller.Complexity.OpcodeArity
open StackMachine StackBlocks
open scoped BigOperators

def expectedArity (opcode : Fin 16) : Option (Fin 4) :=
  match opcode.val with
  | 0 | 1 | 4 | 5 | 11 => some 2
  | 2 | 3 => some 3
  | 6 | 8 | 9 | 10 => some 1
  | 7 | 12 => some 0
  | _ => none

def accepts (opcode : Fin 16) (count : Nat) : Bool :=
  match expectedArity opcode with | none => false | some arity => decide (count=arity.val)

inductive Label where
  | readTag (remaining : Fin 5) (value : Fin 16)
  | checkCount (value : Fin 16) (consumed : Fin 4)
  | restoreCount (value : Fin 16) (remaining : Fin 4) (reject : Bool)
  | flag (value : Fin 16)
  | restoreTag (value : Fin 16) (index : Fin 5)
  deriving DecidableEq, Fintype

def appendBit (value : Fin 16) (bit : Bool) : Fin 16 :=
  ⟨(2*value.val+(if bit then 1 else 0))%16,Nat.mod_lt _ (by decide)⟩

def program : Program Bool Label where
  main := .readTag 4 0
  code label := match label with
    | .readTag remaining value => if positive : 0 < remaining.val then
        .pop none (.flag value)
          (.readTag ⟨remaining.val-1,by omega⟩ (appendBit value false))
          (.readTag ⟨remaining.val-1,by omega⟩ (appendBit value true))
      else .jump (.checkCount value 0)
    | .checkCount value consumed => match expectedArity value with
      | none => .jump (.flag value)
      | some arity => if more : consumed.val < arity.val then
          .pop (some false) (.restoreCount value consumed true) (.restoreCount value consumed true)
            (.checkCount value ⟨consumed.val+1,by omega⟩)
        else .peek (some false) (.restoreCount value consumed false)
          (.restoreCount value consumed true) (.restoreCount value consumed true)
    | .restoreCount value remaining reject => if positive : 0 < remaining.val then
        .push (some false) true (.restoreCount value ⟨remaining.val-1,by omega⟩ reject)
      else .jump (if reject then .flag value else .restoreTag value 0)
    | .flag value => .push (some true) false (.restoreTag value 0)
    | .restoreTag value index => if more : index.val < 4 then
        .push none (value.val.testBit index.val) (.restoreTag value ⟨index.val+1,by omega⟩)
      else .halt

def start (opcode : Fin 16) (count : Nat) : State Bool Label :=
  ⟨some program.main,layout (Encoding.bits 4 opcode.val).reverse (List.replicate count true) []⟩

def checked (opcode : Fin 16) (count : Nat) := StackEvaluation.eval program 20 (start opcode count)

def Spec (opcode : Fin 16) (count : Nat) : Prop :=
  (checked opcode count).state.pc=none ∧
  (checked opcode count).state.stk none=(Encoding.bits 4 opcode.val).reverse ∧
  (checked opcode count).state.stk (some false)=List.replicate count true ∧
  (checked opcode count).state.stk (some true)=(if accepts opcode count then [] else [false])

theorem small_spec : ∀ opcode : Fin 16, ∀ count : Fin 4, Spec opcode count.val := by
  unfold Spec
  decide

theorem four_spec : ∀ opcode : Fin 16, Spec opcode 4 := by
  unfold Spec
  decide

theorem four_safe : ∀ opcode : Fin 16, StackTail.safe program (some false) 20 (start opcode 4)=true := by
  decide

theorem accepts_large (opcode : Fin 16) (excess : Nat) : accepts opcode (excess+4)=false := by
  unfold accepts
  cases expectedArity opcode with
  | none => rfl
  | some arity => simp only [decide_eq_false_iff_not]; omega

theorem extend_start (opcode : Fin 16) (excess : Nat) :
    StackTail.state (some false) (List.replicate excess true) (start opcode 4)=start opcode (excess+4) := by
  have count : List.replicate 4 true++List.replicate excess true=List.replicate (excess+4) true := by
    rw [← List.replicate_add, Nat.add_comm 4 excess]
  unfold StackTail.state start
  congr 1
  funext port
  cases port with
  | none => simp [StackTail.storage, layout]
  | some bit => cases bit with
    | false => simpa [StackTail.storage, layout] using count
    | true => simp [StackTail.storage, layout]

theorem large_spec (opcode : Fin 16) (excess : Nat) : Spec opcode (excess+4) := by
  have lifted := StackTail.eval_state program (some false) (List.replicate excess true) 20 (start opcode 4) (four_safe opcode)
  rw [extend_start] at lifted
  change (checked opcode (excess+4)).state=StackTail.state (some false) (List.replicate excess true) (checked opcode 4).state at lifted
  rcases four_spec opcode with ⟨pc,tag,count,error⟩
  have rejected : accepts opcode 4=false := accepts_large opcode 0
  rw [rejected] at error
  have sameCount : List.replicate 4 true++List.replicate excess true=List.replicate (excess+4) true := by
    rw [← List.replicate_add, Nat.add_comm 4 excess]
  unfold Spec
  rw [lifted]
  simp [StackTail.state, StackTail.storage, pc, tag, count, error, accepts_large]
  simpa using sameCount

theorem spec (opcode : Fin 16) (count : Nat) : Spec opcode count := by
  by_cases small : count < 4
  · exact small_spec opcode ⟨count,small⟩
  · have length : (count-4)+4=count := by omega
    simpa only [length] using large_spec opcode (count-4)

theorem execution (opcode : Fin 16) (count : Nat) :
    ∃ ticks peak, Execution program (start opcode count)
      ⟨none,layout (Encoding.bits 4 opcode.val).reverse (List.replicate count true)
        (if accepts opcode count then [] else [false])⟩ ticks peak ∧ ticks ≤ 20 := by
  rcases spec opcode count with ⟨pc,tag,operandCount,error⟩
  have bankEq : (checked opcode count).state.stk =
      layout (Encoding.bits 4 opcode.val).reverse (List.replicate count true) (if accepts opcode count then [] else [false]) := by
    funext port
    cases port with
    | none => exact tag
    | some bit => cases bit <;> assumption
  have endpoint : (checked opcode count).state =
      (⟨none,layout (Encoding.bits 4 opcode.val).reverse (List.replicate count true)
        (if accepts opcode count then [] else [false])⟩ : State Bool Label) :=
    congrArg₂ State.mk pc bankEq
  have trace := StackEvaluation.sound program 20 (start opcode count)
  change Execution program (start opcode count) (checked opcode count).state (checked opcode count).ticks (checked opcode count).peak at trace
  rw [endpoint] at trace
  exact ⟨_,_,trace,StackEvaluation.ticks_le program 20 (start opcode count)⟩

theorem accepts_fields (bound : registers ≤ 2^width) (instruction : Controller.Cost.Instruction width registers) :
    accepts ⟨(InstructionCodec.fields bound instruction).1,InstructionCodec.fields_tag_lt bound instruction⟩
      (InstructionCodec.fields bound instruction).2.length=true := by
  cases instruction <;> rfl

def ports : Option Bool ↪ WordReader.Port :=
  StackFrames.threePorts (some 13) (some 12) none (by decide) (by decide) (by decide)

theorem ports_apply (port : Option Bool) : ports port =
    (match port with | none => some 13 | some false => some 12 | some true => none) := rfl

theorem frame_storage (frame : WordReader.Port → List Bool) (opcode : Fin 16) (count : Nat) (flag : List Bool)
    (tagStored : frame (some 13)=(Encoding.bits 4 opcode.val).reverse)
    (countStored : frame (some 12)=List.replicate count true) :
    StackFrames.embedStorage ports frame (layout (Encoding.bits 4 opcode.val).reverse (List.replicate count true) flag) =
      Function.update frame none flag := by
  funext target
  by_cases ht : target=some 13 <;> by_cases hc : target=some 12 <;> by_cases hf : target=none <;>
    simp_all [StackFrames.embedStorage, ports_apply, layout]

def machine := StackFrames.relocate ports program

theorem framed_execution (frame : WordReader.Port → List Bool) (opcode : Fin 16) (count : Nat)
    (tagStored : frame (some 13)=(Encoding.bits 4 opcode.val).reverse)
    (countStored : frame (some 12)=List.replicate count true) (clean : frame none=[]) :
    ∃ ticks peak, Execution machine ⟨some machine.main,frame⟩
      ⟨none,Function.update frame none (if accepts opcode count then [] else [false])⟩ ticks peak ∧
      ticks ≤ 20 ∧ peak ≤ live (⟨some machine.main,frame⟩ : State (Fin 31) Label)+20 := by
  obtain ⟨ticks,peak,trace,bound⟩ := execution opcode count
  have lifted := StackFrames.execution ports frame trace
  simp only [StackFrames.embedState, start, frame_storage frame opcode count _ tagStored countStored,
    ColdInput.update_empty frame none clean] at lifted
  change Execution machine ⟨some machine.main,frame⟩ _ _ _ at lifted
  have space := lifted.peak_le
  exact ⟨ticks,_,lifted,bound,by omega⟩

def labelEquiv : Label ≃ (Fin 5 × Fin 16) ⊕ (Fin 16 × Fin 4) ⊕ (Fin 16 × Fin 4 × Bool) ⊕ Fin 16 ⊕ (Fin 16 × Fin 5) where
  toFun label := match label with
    | .readTag remaining value => .inl (remaining,value)
    | .checkCount value consumed => .inr (.inl (value,consumed))
    | .restoreCount value remaining reject => .inr (.inr (.inl (value,remaining,reject)))
    | .flag value => .inr (.inr (.inr (.inl value)))
    | .restoreTag value index => .inr (.inr (.inr (.inr (value,index))))
  invFun code := match code with
    | .inl (remaining,value) => .readTag remaining value
    | .inr (.inl (value,consumed)) => .checkCount value consumed
    | .inr (.inr (.inl (value,remaining,reject))) => .restoreCount value remaining reject
    | .inr (.inr (.inr (.inl value))) => .flag value
    | .inr (.inr (.inr (.inr (value,index)))) => .restoreTag value index
  left_inv label := by cases label <;> rfl
  right_inv code := by
    rcases code with ⟨remaining,value⟩ | ⟨value,consumed⟩ | ⟨value,remaining,reject⟩ | value | ⟨value,index⟩ <;> rfl

theorem label_card : Fintype.card Label=368 := by
  simpa using Fintype.card_congr labelEquiv

theorem resident : (∑ label, statementSize (tmStatement (machine.code label))) ≤ 3312 := by
  simpa only [label_card] using finiteTM_resident machine

theorem four_bit_canonical (tag : List Bool) (width : tag.length=4) :
    ∃ opcode : Fin 16, Encoding.bits 4 opcode.val=tag := by
  obtain ⟨a,b,c,d,rfl⟩ := List.length_eq_four.mp width
  exact (by decide : ∀ a b c d : Bool, ∃ opcode : Fin 16, Encoding.bits 4 opcode.val=[a,b,c,d]) a b c d

end Controller.Complexity.OpcodeArity
