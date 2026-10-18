module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.SpaceTapeStack
public import Controller.Complexity.SpaceTapeInput
public import Controller.Complexity.SpaceConfigurations

@[expose] public section

/-! Every source instruction takes at most two ordinary multitape steps.
The resulting whole execution bounds every visited work cell, including
bottom markers and the blank cells beyond the current stack tops. -/
namespace Controller.Complexity.SpaceTapeSimulation
open SpaceMachine SpaceTapeMachine SpaceTapeRun

theorem instruction [DecidableEq K] (enumeration : Fin n ≃ K) (program : SpaceMachine.Program K Q)
    (source : SpaceMachine.State K Q) (label : Q) (position : source.pc=some label)
    (code : SpaceMachine.Instruction K Q) (selected : program.code label=code)
    (before : ∀ port, (source.work port).length+2 ≤ capacity)
    (after : ∀ port, ((instructionStep code source).work port).length+2 ≤ capacity) :
    ∃ ticks, Run enumeration program capacity (configuration source)
      (configuration (instructionStep code source)) ticks ∧ ticks ≤ 2 := by
  have initialWithin := configuration_within (n := n) source capacity before
  have finalWithin := configuration_within (n := n) (instructionStep code source) capacity after
  cases code with
  | push port bit next =>
    exact ⟨1,Run.cons (SpaceTapeOrdinary.push enumeration program source label port bit next position selected)
      initialWithin (Run.refl finalWithin),by omega⟩
  | readInput eof low high =>
    exact ⟨1,Run.cons (SpaceTapeOrdinary.readInput enumeration program source label eof low high position selected)
      initialWithin (Run.refl finalWithin),by omega⟩
  | right next =>
    exact ⟨1,Run.cons (SpaceTapeOrdinary.right enumeration program source label next position selected)
      initialWithin (Run.refl finalWithin),by omega⟩
  | emit bit next =>
    exact ⟨1,Run.cons (SpaceTapeOrdinary.emit enumeration program source label bit next position selected)
      initialWithin (Run.refl finalWithin),by omega⟩
  | jump next =>
    exact ⟨1,Run.cons (SpaceTapeOrdinary.jump enumeration program source label next position selected)
      initialWithin (Run.refl finalWithin),by omega⟩
  | halt =>
    exact ⟨1,Run.cons (SpaceTapeOrdinary.halt enumeration program source label position selected)
      initialWithin (Run.refl finalWithin),by omega⟩
  | pop port empty low high =>
    exact ⟨2,Run.cons (SpaceTapeStack.pop_first enumeration program source label port empty low high position selected)
      initialWithin (Run.cons (SpaceTapeStack.pop_return enumeration program source port empty low high)
        (SpaceTapeStack.lower_within source port _ before) (Run.refl finalWithin)),by omega⟩
  | peek port empty low high =>
    exact ⟨2,Run.cons (SpaceTapeStack.peek_first enumeration program source label port empty low high position selected)
      initialWithin (Run.cons (SpaceTapeStack.peek_return enumeration program source port empty low high)
        (SpaceTapeStack.lower_within source port _ before) (Run.refl finalWithin)),by omega⟩
  | left next =>
    exact ⟨2,Run.cons (SpaceTapeInput.left_first enumeration program source label next position selected)
      initialWithin (Run.cons (SpaceTapeInput.left_return enumeration program source next)
        (SpaceTapeInput.lower_within source _ before) (Run.refl finalWithin)),by omega⟩
  | atStart yes no =>
    exact ⟨2,Run.cons (SpaceTapeInput.start_first enumeration program source label yes no position selected)
      initialWithin (Run.cons (SpaceTapeInput.start_return enumeration program source yes no)
        (SpaceTapeInput.lower_within source _ before) (Run.refl finalWithin)),by omega⟩

theorem execution [Fintype K] [DecidableEq K] (enumeration : Fin n ≃ K)
    {program : SpaceMachine.Program K Q} {source final ticks peak}
    (actual : SpaceMachine.Execution program source final ticks peak) :
    ∃ tapeTicks, Run enumeration program (peak+2) (configuration source) (configuration final) tapeTicks ∧
      tapeTicks ≤ 2*ticks := by
  induction actual with
  | refl source =>
    refine ⟨0,Run.refl (configuration_within source _ ?_),by simp⟩
    intro port
    have bound := SpaceConfigurations.work_length_le source port
    omega
  | @cons source middle final ticks peak first rest ih =>
    obtain ⟨tailTicks,tailTrace,tailTime⟩ := ih
    cases position : source.pc with
    | none => simp [SpaceMachine.step,position] at first
    | some label =>
      have target : instructionStep (program.code label) source=middle := by
        simpa [SpaceMachine.step,position] using first
      have before : ∀ port, (source.work port).length+2 ≤ max (workspace source) peak+2 := by
        intro port
        have bound := SpaceConfigurations.work_length_le source port
        omega
      have after : ∀ port, ((instructionStep (program.code label) source).work port).length+2 ≤ max (workspace source) peak+2 := by
        rw [target]
        intro port
        have bound := (SpaceConfigurations.work_length_le middle port).trans rest.initial_workspace_le
        omega
      obtain ⟨firstTicks,firstTrace,firstTime⟩ := instruction enumeration program source label position
        (program.code label) rfl before after
      rw [target] at firstTrace
      have raised := tailTrace.mono (Nat.add_le_add_right (Nat.le_max_right (workspace source) peak) 2)
      exact ⟨_,firstTrace.append raised,by omega⟩

end Controller.Complexity.SpaceTapeSimulation
