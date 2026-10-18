module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.SpaceControl

@[expose] public section

/-! Sequential composition of two finite read-only transducer blocks sharing
the actual tape, work and output data. The first halt becomes the physical
continuation jump; ticks add and workspace peaks take their maximum. -/
namespace Controller.Complexity.SpaceLink
open SpaceMachine

def program (first : SpaceMachine.Program K Q) (second : SpaceMachine.Program K P) : SpaceMachine.Program K (Q ⊕ P) where
  main := .inl first.main
  code label := match label with
    | .inl label => SpaceControl.instruction Sum.inl (some (.inr second.main)) (first.code label)
    | .inr label => SpaceControl.instruction Sum.inr none (second.code label)

theorem execution [Fintype K] [DecidableEq K]
    {first : SpaceMachine.Program K Q} {second : SpaceMachine.Program K P}
    {inputTape middleTape finalTape : ReadOnlyInput.Tape} {inputWork middleWork finalWork : K → List Bool}
    {inputOutput middleOutput finalOutput : List Bool} {firstTicks firstPeak secondTicks secondPeak}
    (left : SpaceMachine.Execution first ⟨some first.main,inputTape,inputWork,inputOutput⟩
      ⟨none,middleTape,middleWork,middleOutput⟩ firstTicks firstPeak)
    (right : SpaceMachine.Execution second ⟨some second.main,middleTape,middleWork,middleOutput⟩
      ⟨none,finalTape,finalWork,finalOutput⟩ secondTicks secondPeak) :
    SpaceMachine.Execution (program first second) ⟨some (program first second).main,inputTape,inputWork,inputOutput⟩
      ⟨none,finalTape,finalWork,finalOutput⟩ (firstTicks+secondTicks) (max firstPeak secondPeak) := by
  have firstTrace := SpaceControl.execution first (program first second) Sum.inl (some (.inr second.main)) (fun _ => rfl) left
  have secondTrace := SpaceControl.execution second (program first second) Sum.inr none (fun _ => rfl) right
  exact firstTrace.append secondTrace

end Controller.Complexity.SpaceLink
