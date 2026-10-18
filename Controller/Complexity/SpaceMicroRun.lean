module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.SpaceMicroBounds

@[expose] public section

/-! Whole executions expanded into literal TM2 primitive operations and one
finite-control dispatch per source instruction. Work-bank spans include every
internal state, with no additional work allocation between source boundaries. -/
namespace Controller.Complexity.SpaceMicroRun
open SpaceMachine SpaceMicro
open scoped BigOperators

def step [DecidableEq K] (program : SpaceMachine.Program K Q) : SpaceMicro.State K Q → Option (SpaceMicro.State K Q)
  | .pending code register bank => tick (.pending code register bank)
  | .done configuration => configuration.l.map fun label =>
      .pending (SpaceTM.statement (program.code label)) configuration.var configuration.stk

inductive Trace [DecidableEq K] (program : SpaceMachine.Program K Q) :
    SpaceMicro.State K Q → SpaceMicro.State K Q → Nat → (K → Nat) → Prop
  | refl (state) : Trace program state state 0 (fun port => (storage state (SpaceTM.workPort port)).length)
  | cons {state next final ticks spans} : step program state=some next →
      Trace program next final ticks spans →
      Trace program state final (ticks+1) (fun port => max (storage state (SpaceTM.workPort port)).length (spans port))

theorem Trace.initial_le [DecidableEq K] {program : SpaceMachine.Program K Q}
    {state final ticks spans} (trace : Trace program state final ticks spans) (port : K) :
    (storage state (SpaceTM.workPort port)).length ≤ spans port := by
  cases trace with
  | refl => rfl
  | cons => exact Nat.le_max_left _ _

theorem Trace.append [DecidableEq K] {program : SpaceMachine.Program K Q}
    {state middle final firstTicks secondTicks firstSpans secondSpans}
    (first : Trace program state middle firstTicks firstSpans)
    (second : Trace program middle final secondTicks secondSpans) :
    Trace program state final (firstTicks+secondTicks) (fun port => max (firstSpans port) (secondSpans port)) := by
  induction first with
  | refl middle =>
    have same : (fun port => max (storage middle (SpaceTM.workPort port)).length (secondSpans port))=secondSpans :=
      funext fun port => Nat.max_eq_right (second.initial_le port)
    simpa only [Nat.zero_add,same] using second
  | cons actual rest ih =>
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,Nat.max_assoc] using Trace.cons actual (ih second)

theorem of_local [DecidableEq K] (program : SpaceMachine.Program K Q)
    {state final ticks spans} (trace : SpaceMicro.Trace state final ticks spans) :
    Trace program state final ticks spans := by
  induction trace with
  | refl => exact Trace.refl _
  | @cons state next final ticks spans actual rest ih =>
    have expanded : step program state=some next := by
      cases state with
      | pending code register bank => exact actual
      | done configuration => simp [tick] at actual
    exact Trace.cons expanded ih

theorem expanded [Fintype K] [DecidableEq K] {program : SpaceMachine.Program K Q}
    {state final ticks peak} (execution : SpaceMachine.Execution program state final ticks peak) :
    ∃ microTicks spans, Trace program (.done (SpaceTM.configuration state))
      (.done (SpaceTM.configuration final)) microTicks spans ∧
      microTicks ≤ 6*ticks ∧ ∀ port, spans port ≤ peak := by
  induction execution with
  | refl state =>
    exact ⟨0,_,Trace.refl _,by simp,fun port => SpaceConfigurations.work_length_le state port⟩
  | @cons state middle final ticks peak actual rest ih =>
    obtain ⟨tailTicks,tailSpans,tailTrace,tailTime,tailBound⟩ := ih
    cases position : state.pc with
    | none => simp [SpaceMachine.step,position] at actual
    | some label =>
      have target : instructionStep (program.code label) state=middle := by
        simpa [SpaceMachine.step,position] using actual
      obtain ⟨firstTicks,firstSpans,firstTrace,firstTime,firstBound⟩ :=
        SpaceMicroBounds.instruction_execution (program.code label) state
      rw [target] at firstTrace firstBound
      have dispatch : step program (.done (SpaceTM.configuration state))=
          some (.pending (SpaceTM.statement (program.code label)) none (SpaceTM.storage state)) := by
        simp [step,SpaceTM.configuration,position]
      have combined := (Trace.cons dispatch (of_local program firstTrace)).append tailTrace
      refine ⟨_,_,combined,?_,?_⟩
      · omega
      · intro port
        have initialBound := SpaceConfigurations.work_length_le state port
        have middleBound := (SpaceConfigurations.work_length_le middle port).trans rest.initial_workspace_le
        have localBound := firstBound port
        have laterBound := tailBound port
        change max (max (state.work port).length (firstSpans port)) (tailSpans port) ≤ _
        omega

theorem allocated_cells [Fintype K] [DecidableEq K] {program : SpaceMachine.Program K Q}
    {state final ticks peak} (execution : SpaceMachine.Execution program state final ticks peak) :
    ∃ microTicks spans, Trace program (.done (SpaceTM.configuration state))
      (.done (SpaceTM.configuration final)) microTicks spans ∧ microTicks ≤ 6*ticks ∧
      (∑ port, spans port)+2*Fintype.card K ≤ Fintype.card K*(peak+2) := by
  obtain ⟨microTicks,spans,actual,time,bound⟩ := expanded execution
  have total : (∑ port, spans port) ≤ Fintype.card K*peak := by
    simpa using Finset.sum_le_sum (fun port (_ : port ∈ Finset.univ) => bound port)
  refine ⟨microTicks,spans,actual,time,?_⟩
  rw [Nat.mul_add,Nat.mul_comm (Fintype.card K) 2]
  omega

end Controller.Complexity.SpaceMicroRun
