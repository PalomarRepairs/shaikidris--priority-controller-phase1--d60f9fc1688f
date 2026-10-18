module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.OpcodeArity

@[expose] public section

/-! A finite decoder reads and restores a saved opcode and publishes its
operand roles. True denotes a register index and false an immediate word.
Reserved tags set the error stack. -/
namespace Controller.Complexity.OpcodeRoles
open StackMachine StackBlocks
open scoped BigOperators

def roles (opcode : Fin 16) : Option (List Bool) := match opcode.val with
  | 0 | 11 => some [true,false]
  | 1 | 4 | 5 => some [true,true]
  | 2 | 3 => some [true,true,true]
  | 6 | 8 | 9 | 10 => some [true]
  | 7 | 12 => some []
  | _ => none

inductive Label where
  | readTag (remaining : Fin 5) (value : Fin 16)
  | emit (value : Fin 16) (index : Fin 4)
  | flag (value : Fin 16)
  | restoreTag (value : Fin 16) (index : Fin 5)
  deriving DecidableEq, Fintype

def program : Program Bool Label where
  main := .readTag 4 0
  code label := match label with
    | .readTag remaining value => if positive : 0 < remaining.val then
        .pop none (.flag value)
          (.readTag ⟨remaining.val-1,by omega⟩ (OpcodeArity.appendBit value false))
          (.readTag ⟨remaining.val-1,by omega⟩ (OpcodeArity.appendBit value true))
      else .jump (.emit value 0)
    | .emit value index => match roles value with
      | none => .jump (.flag value)
      | some bits => if more : index.val < bits.length then
          .push (some false) (bits.reverse[index.val]'(by simpa only [List.length_reverse] using more))
            (.emit value ⟨(index.val+1)%4,Nat.mod_lt _ (by decide)⟩)
        else .jump (.restoreTag value 0)
    | .flag value => .push (some true) false (.restoreTag value 0)
    | .restoreTag value index => if more : index.val < 4 then
        .push none (value.val.testBit index.val) (.restoreTag value ⟨index.val+1,by omega⟩)
      else .halt

def start (opcode : Fin 16) : State Bool Label :=
  ⟨some program.main,layout (Encoding.bits 4 opcode.val).reverse [] []⟩

def checked (opcode : Fin 16) := StackEvaluation.eval program 14 (start opcode)

def Spec (opcode : Fin 16) : Prop :=
  (checked opcode).state.pc=none ∧
  (checked opcode).state.stk none=(Encoding.bits 4 opcode.val).reverse ∧
  (checked opcode).state.stk (some false)=(roles opcode).getD [] ∧
  (checked opcode).state.stk (some true)=(if (roles opcode).isSome then [] else [false])

theorem spec : ∀ opcode : Fin 16, Spec opcode := by
  unfold Spec
  decide

theorem execution (opcode : Fin 16) :
    ∃ ticks peak, Execution program (start opcode)
      ⟨none,layout (Encoding.bits 4 opcode.val).reverse (roles opcode |>.getD [])
        (if (roles opcode).isSome then [] else [false])⟩ ticks peak ∧ ticks ≤ 14 := by
  have trace := StackEvaluation.sound program 14 (start opcode)
  rcases spec opcode with ⟨pc,tag,role,error⟩
  have bankEq : (checked opcode).state.stk=
      layout (Encoding.bits 4 opcode.val).reverse (roles opcode |>.getD [])
        (if (roles opcode).isSome then [] else [false]) := by
    funext port
    cases port with
    | none => exact tag
    | some bit => cases bit <;> assumption
  have endpoint : (checked opcode).state=
      ⟨none,layout (Encoding.bits 4 opcode.val).reverse (roles opcode |>.getD [])
        (if (roles opcode).isSome then [] else [false])⟩ := congrArg₂ State.mk pc bankEq
  change Execution program (start opcode) (checked opcode).state _ _ at trace
  rw [endpoint] at trace
  exact ⟨_,_,trace,StackEvaluation.ticks_le program 14 (start opcode)⟩

def ports : Option Bool ↪ WordReader.Port :=
  StackFrames.threePorts (some 13) (some 18) none (by decide) (by decide) (by decide)

theorem ports_apply (port : Option Bool) : ports port =
    (match port with | none => some 13 | some false => some 18 | some true => none) := rfl

def machine := StackFrames.relocate ports program

theorem framed_execution (frame : WordReader.Port → List Bool) (opcode : Fin 16)
    (tag : frame (some 13)=(Encoding.bits 4 opcode.val).reverse)
    (emptyRoles : frame (some 18)=[]) (clean : frame none=[]) :
    ∃ ticks peak, Execution machine ⟨some machine.main,frame⟩
      ⟨none,Function.update (Function.update frame (some 18) (roles opcode |>.getD [])) none
        (if (roles opcode).isSome then [] else [false])⟩ ticks peak ∧ ticks ≤ 14 := by
  obtain ⟨ticks,peak,trace,bound⟩ := execution opcode
  have lifted := StackFrames.execution ports frame trace
  have input : StackFrames.embedStorage ports frame (layout (Encoding.bits 4 opcode.val).reverse [] [])=frame := by
    funext target
    by_cases ht : target=some 13 <;> by_cases hr : target=some 18 <;> by_cases hs : target=none <;>
      simp_all [StackFrames.embedStorage, ports_apply, layout]
  have output : StackFrames.embedStorage ports frame
      (layout (Encoding.bits 4 opcode.val).reverse (roles opcode |>.getD [])
        (if (roles opcode).isSome then [] else [false]))=
      Function.update (Function.update frame (some 18) (roles opcode |>.getD [])) none
        (if (roles opcode).isSome then [] else [false]) := by
    funext target
    by_cases ht : target=some 13 <;> by_cases hr : target=some 18 <;> by_cases hs : target=none <;>
      simp_all [StackFrames.embedStorage, ports_apply, layout]
  exact ⟨ticks,_,by simpa only [machine, StackFrames.relocate, StackFrames.embedState, start, input, output] using lifted,bound⟩

theorem roles_arity (opcode : Fin 16) : (roles opcode).map List.length=(OpcodeArity.expectedArity opcode).map Fin.val := by
  revert opcode
  decide

theorem label_card : Fintype.card Label=240 := by
  let equiv : Label ≃ (Fin 5 × Fin 16) ⊕ (Fin 16 × Fin 4) ⊕ Fin 16 ⊕ (Fin 16 × Fin 5) := {
    toFun := fun label => match label with
      | .readTag remaining value => .inl (remaining,value)
      | .emit value index => .inr (.inl (value,index))
      | .flag value => .inr (.inr (.inl value))
      | .restoreTag value index => .inr (.inr (.inr (value,index)))
    invFun := fun label => match label with
      | .inl (remaining,value) => .readTag remaining value
      | .inr (.inl (value,index)) => .emit value index
      | .inr (.inr (.inl value)) => .flag value
      | .inr (.inr (.inr (value,index))) => .restoreTag value index
    left_inv := by intro label; cases label <;> rfl
    right_inv := by intro label; rcases label with _ | (_ | (_ | _)) <;> rfl }
  rw [Fintype.card_congr equiv]
  simp

theorem resident : (∑ label, statementSize (tmStatement (machine.code label))) ≤ 2160 := by
  simpa only [label_card] using finiteTM_resident machine

end Controller.Complexity.OpcodeRoles
