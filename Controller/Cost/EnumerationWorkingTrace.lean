module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.EnumerationStreamEmit

@[expose] public section

/-! Pointwise streaming-space accounting for genuine machine traces. The output
history is excluded at every intermediate state, while the heap, stack, eight
registers and control word remain charged. -/
namespace Controller.Cost.EnumerationWorkingTrace
open Controller.Cost.GateProgram Controller.Cost.EnumerationStreamEmit

/-- Actual transitions whose peak charges heap, stack, registers and control. -/
inductive WorkingExecution (program : Program width 8) :
    State width 8 → State width 8 → Nat → Nat → Prop where
  | refl (state) : WorkingExecution program state state 0 (workingWords state)
  | cons {state middle final ticks peak}
      (transition : programStep program state = some middle)
      (rest : WorkingExecution program middle final ticks peak) :
      WorkingExecution program state final (ticks + 1) (max (workingWords state) peak)

/-- Working-space refinement retains all actual transitions and the exact tick
count; ordinary live-space execution is recovered by charging output as well. -/
theorem WorkingExecution.to_execution {program : Program width 8} {state final : State width 8} {ticks peak : Nat}
    (trace : WorkingExecution program state final ticks peak) :
    ∃ livePeak, Execution program state final ticks livePeak := by
  induction trace with
  | refl state => exact ⟨state.liveWords, Execution.refl state⟩
  | cons transition rest ih =>
    obtain ⟨livePeak, execution⟩ := ih
    exact ⟨max _ livePeak, Execution.cons transition execution⟩

theorem WorkingExecution.final_le_peak {program : Program width 8} {state final : State width 8} {ticks peak : Nat}
    (trace : WorkingExecution program state final ticks peak) : workingWords final ≤ peak := by
  induction trace with
  | refl => exact Nat.le_refl _
  | cons transition rest ih => exact ih.trans (Nat.le_max_right _ _)

theorem WorkingExecution.append {program : Program width 8} {state middle final : State width 8}
    {firstTicks firstPeak restTicks restPeak : Nat}
    (first : WorkingExecution program state middle firstTicks firstPeak)
    (rest : WorkingExecution program middle final restTicks restPeak) :
    WorkingExecution program state final (firstTicks + restTicks) (max firstPeak restPeak) := by
  induction first with
  | refl state =>
    have lower : workingWords state ≤ restPeak := by
      cases rest with
      | refl => exact Nat.le_refl _
      | cons transition tail => exact Nat.le_max_left _ _
    simpa only [Nat.zero_add, Nat.max_eq_right lower] using rest
  | cons transition tail ih =>
    simpa only [Nat.add_right_comm, Nat.max_assoc] using WorkingExecution.cons transition (ih rest)

private theorem step_output_mono (instruction : Instruction width 8) (state next : State width 8)
    (transition : step instruction state = some next) : state.output.length ≤ next.output.length := by
  unfold step at transition
  split at transition
  · simp_all
  · cases instruction <;> simp only [Option.some.injEq] at transition
    all_goals
      repeat' first | split at transition | cases transition
      all_goals simp [State.advance, State.put]

theorem transition_output_mono (program : Program width 8) (state next : State width 8)
    (transition : programStep program state = some next) : state.output.length ≤ next.output.length := by
  cases fetched : program[state.pc.val]? with
  | none => simp [programStep, fetched] at transition
  | some instruction =>
    have actual : step instruction state = some next := by simpa [programStep, fetched] using transition
    exact step_output_mono instruction state next actual

theorem execution_output_mono {program : Program width 8} {state final : State width 8} {ticks peak : Nat}
    (trace : Execution program state final ticks peak) : state.output.length ≤ final.output.length := by
  induction trace with
  | refl => exact Nat.le_refl _
  | cons transition rest ih => exact (transition_output_mono _ _ _ transition).trans ih

/-- A quiet execution has the same output length at every state. Its exact
ordinary peak splits into working peak plus the unchanged output length. -/
theorem quiet {program : Program width 8} {state final : State width 8} {ticks peak : Nat}
    (trace : Execution program state final ticks peak) :
    state.output.length = final.output.length →
    ∃ workingPeak, WorkingExecution program state final ticks workingPeak ∧
      peak = workingPeak + state.output.length := by
  induction trace with
  | refl state =>
    intro _
    exact ⟨workingWords state, WorkingExecution.refl state, live_eq_working_output state⟩
  | @cons state middle final ticks peak transition rest ih =>
    intro unchanged
    have firstMono := transition_output_mono _ _ _ transition
    have restMono := execution_output_mono rest
    have same : middle.output.length = state.output.length := by omega
    obtain ⟨workingPeak, workingTrace, relation⟩ := ih (by omega)
    refine ⟨max (workingWords state) workingPeak, WorkingExecution.cons transition workingTrace, ?_⟩
    rw [live_eq_working_output state, relation, same]
    omega

theorem quiet_bound {program : Program width 8} {state final : State width 8} {ticks peak extra : Nat}
    (trace : Execution program state final ticks peak) (unchanged : final.output = state.output)
    (bound : peak ≤ state.liveWords + extra) :
    ∃ workingPeak, WorkingExecution program state final ticks workingPeak ∧
      workingPeak ≤ workingWords state + extra := by
  obtain ⟨workingPeak, workingTrace, relation⟩ := quiet trace (by rw [unchanged])
  refine ⟨workingPeak, workingTrace, ?_⟩
  rw [relation, live_eq_working_output state] at bound
  omega

end Controller.Cost.EnumerationWorkingTrace
