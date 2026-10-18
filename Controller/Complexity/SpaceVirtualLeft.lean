module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.SpaceVirtualCounter
public import Controller.Complexity.SpaceVirtualState

@[expose] public section

/-! A virtual left move executes canonical truncated binary decrement. The
physical original-input head does not move, including at the virtual start. -/
namespace Controller.Complexity.SpaceVirtualLeft
open SpaceMachine SpaceVirtual SpaceVirtualState

theorem execution [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (first : SpaceMachine.Program A P) (second : SpaceMachine.Program B Q)
    (enumeration : Fin n ≃ SpaceLookup.Bank A) (original : List Bool) (limit : Nat)
    (shadow : SpaceMachine.State B Q) (actual : SpaceMachine.State (Bank A B) (Label n P Q))
    (related : Represents original shadow actual limit) (origin next : Q)
    (position : shadow.pc=some origin) (code : second.code origin=.left next) :
    ∃ result ticks, SpaceMachine.Execution (program first second enumeration) actual result ticks (workspace actual) ∧
      Represents original (instructionStep (.left next) shadow) result limit := by
  have firstStep : SpaceMachine.step (program first second enumeration) actual=
      some ⟨some (decrementLabel next (SpaceDecrement.program (ports (A:=A) (B:=B))).main),
        actual.tape,actual.work,actual.output⟩ := by
    simp [SpaceMachine.step,related.pc,position,program,sourceLabel,code,instructionStep,advance]
  obtain ⟨ticks,subroutine⟩ := SpaceVirtualCounter.decrement first second enumeration actual next
    (ReadOnlyInput.position shadow.tape) related.head related.scratch
  have complete := Execution.cons firstStep subroutine
  let result : SpaceMachine.State (Bank A B) (Label n P Q) :=
    ⟨some (sourceLabel next),actual.tape,
      Function.update actual.work headPort (ReadOnlyInput.position shadow.tape-1).bits,actual.output⟩
  have data : DataRep original (instructionStep (.left next) shadow) result limit :=
    head_change (after:=instructionStep (.left next) shadow) related.toDataRep rfl (ReadOnlyInput.position_left shadow.tape) rfl _
  refine ⟨result,ticks+1,?_,⟨data,rfl⟩⟩
  simpa only [Nat.max_self] using complete

end Controller.Complexity.SpaceVirtualLeft
