module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.SpaceVirtualState

@[expose] public section

/-! Exact simulation of second-source work operations, emissions, start tests
and control instructions. Virtual reads and head movements have separate
executed request/counter proofs. No second input word is stored physically. -/
namespace Controller.Complexity.SpaceVirtualOrdinary
open SpaceMachine SpaceVirtual SpaceVirtualState

def ordinary : SpaceMachine.Instruction B Q → Prop
  | .readInput _ _ _ => False
  | .left _ => False
  | .right _ => False
  | _ => True

theorem step [DecidableEq A] [DecidableEq B]
    (first : SpaceMachine.Program A P) (second : SpaceMachine.Program B Q)
    (enumeration : Fin n ≃ SpaceLookup.Bank A) (left : SpaceLookup.Bank A → List Bool)
    (tape : ReadOnlyInput.Tape) (shadow : SpaceMachine.State B Q) (origin : Q)
    (position : shadow.pc=some origin) (direct : ordinary (second.code origin)) :
    SpaceMachine.step (program first second enumeration) (view left tape shadow)=
      some (view left tape (instructionStep (second.code origin) shadow)) := by
  cases code : second.code origin with
  | push port bit next =>
    simp only [SpaceMachine.step,view,position,Option.map_some,program,sourceLabel,code,
      instructionStep,advance,bank_second,bank_update]
  | pop port empty low high =>
    simp only [SpaceMachine.step,view,position,Option.map_some,program,sourceLabel,code,
      instructionStep,advance,bank_second,bank_update,SpaceControl.observed_map]
  | peek port empty low high =>
    simp only [SpaceMachine.step,view,position,Option.map_some,program,sourceLabel,code,
      instructionStep,advance,bank_second,SpaceControl.observed_map]
  | readInput eof low high => simp [code,ordinary] at direct
  | atStart yes no =>
    cases test : shadow.tape.left.isEmpty <;>
      simp [SpaceMachine.step,view,position,program,sourceLabel,code,instructionStep,advance,
        bank_head,head_test,test]
  | left next => simp [code,ordinary] at direct
  | right next => simp [code,ordinary] at direct
  | emit bit next =>
    simp only [SpaceMachine.step,view,position,Option.map_some,program,sourceLabel,code,instructionStep,advance]
  | jump next =>
    simp only [SpaceMachine.step,view,position,Option.map_some,program,sourceLabel,code,instructionStep,advance]
  | halt =>
    simp only [SpaceMachine.step,view,position,Option.map_some,Option.map_none,program,sourceLabel,code,instructionStep]

theorem simulation [Fintype A] [DecidableEq A] [DecidableEq B]
    (first : SpaceMachine.Program A P) (second : SpaceMachine.Program B Q)
    (enumeration : Fin n ≃ SpaceLookup.Bank A) (original : List Bool) (limit : Nat)
    (shadow : SpaceMachine.State B Q) (actual : SpaceMachine.State (Bank A B) (Label n P Q))
    (related : Represents original shadow actual limit) (origin : Q)
    (position : shadow.pc=some origin) (direct : ordinary (second.code origin)) :
    ∃ result, SpaceMachine.step (program first second enumeration) actual=some result ∧
      Represents original (instructionStep (second.code origin) shadow) result limit := by
  let left := fun port => actual.work (.inl port)
  have same := view_eq related
  have moved := step first second enumeration left actual.tape shadow origin position direct
  rw [← same] at moved
  refine ⟨_,moved,represents left actual.tape _ original limit related.input related.left⟩

end Controller.Complexity.SpaceVirtualOrdinary
