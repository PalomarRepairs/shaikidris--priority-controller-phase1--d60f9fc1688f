module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.SpaceMachine

@[expose] public section

/-! A finite source execution with its chronological emission stream. The
stream is determined by actual executed instructions, and agrees with the
ordinary reverse-output-stack semantics. It introduces no new machine step. -/
namespace Controller.Complexity.SpaceEmissions
open SpaceMachine

def event (program : SpaceMachine.Program K Q) (state : SpaceMachine.State K Q) : Option Bool :=
  state.pc.bind fun label => emitted (program.code label)

inductive Trace [Fintype K] [DecidableEq K] (program : SpaceMachine.Program K Q) :
    SpaceMachine.State K Q → SpaceMachine.State K Q → Nat → Nat → List Bool → Prop
  | refl (state) : Trace program state state 0 (workspace state) []
  | cons {state next final ticks peak stream} : SpaceMachine.step program state=some next →
      Trace program next final ticks peak stream →
      Trace program state final (ticks+1) (max (workspace state) peak) ((event program state).toList++stream)

theorem execution [Fintype K] [DecidableEq K] {program : SpaceMachine.Program K Q}
    {state final ticks peak stream} (trace : Trace program state final ticks peak stream) :
    SpaceMachine.Execution program state final ticks peak := by
  induction trace with
  | refl state => exact Execution.refl _
  | cons actual rest ih => exact Execution.cons actual ih

theorem of_execution [Fintype K] [DecidableEq K] {program : SpaceMachine.Program K Q}
    {state final ticks peak} (trace : SpaceMachine.Execution program state final ticks peak) :
    ∃ stream, Trace program state final ticks peak stream := by
  induction trace with
  | refl state => exact ⟨[],Trace.refl _⟩
  | cons actual rest ih =>
    obtain ⟨stream,tail⟩ := ih
    exact ⟨_,Trace.cons actual tail⟩

theorem step_output [DecidableEq K] {program : SpaceMachine.Program K Q} {state next}
    (actual : SpaceMachine.step program state=some next) :
    next.output=(event program state).toList.reverse++state.output := by
  cases position : state.pc with
  | none => simp [SpaceMachine.step,position] at actual
  | some label =>
    have same : instructionStep (program.code label) state=next := by simpa [SpaceMachine.step,position] using actual
    rw [← same,instruction_output]
    cases emittedBit : emitted (program.code label) <;> simp [event,position,emittedBit]

theorem output [Fintype K] [DecidableEq K] {program : SpaceMachine.Program K Q}
    {state final ticks peak stream} (trace : Trace program state final ticks peak stream) :
    final.output=stream.reverse++state.output := by
  induction trace with
  | refl state => simp
  | cons actual rest ih =>
    rw [ih,step_output actual]
    simp only [List.reverse_append,List.append_assoc]

theorem stream_eq [Fintype K] [DecidableEq K] {program : SpaceMachine.Program K Q}
    {state final ticks peak stream} (trace : Trace program state final ticks peak stream) :
    stream=final.output.reverse.drop state.output.length := by
  rw [output trace,List.reverse_append,List.reverse_reverse]
  simp

end Controller.Complexity.SpaceEmissions
