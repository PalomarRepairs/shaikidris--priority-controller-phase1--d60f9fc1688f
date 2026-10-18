module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.SpaceTM
public import Controller.Complexity.SpaceConfigurations

@[expose] public section

/-! Maximum allocated span in each work bank along an actual finite trace.
Summing these individual maxima costs at most the fixed number of banks times
the simultaneous workspace peak. Bottom cells add one cell per work bank. -/
namespace Controller.Complexity.SpaceFootprint
open SpaceMachine
open scoped BigOperators

inductive Trace [DecidableEq K] (program : SpaceMachine.Program K Q) :
    SpaceMachine.State K Q → SpaceMachine.State K Q → Nat → (K → Nat) → Prop
  | refl (state) : Trace program state state 0 (fun port => (state.work port).length)
  | cons {state next final ticks spans} : SpaceMachine.step program state=some next →
      Trace program next final ticks spans →
      Trace program state final (ticks+1) (fun port => max (state.work port).length (spans port))

inductive PhysicalTrace [DecidableEq K] (program : SpaceMachine.Program K Q) :
    Turing.TM2.Cfg (fun _ : SpaceTM.Port K => Bool) Q (Option Bool) →
    Turing.TM2.Cfg (fun _ : SpaceTM.Port K => Bool) Q (Option Bool) → Nat → (K → Nat) → Prop
  | refl (state) : PhysicalTrace program state state 0 (fun port => (state.stk (SpaceTM.workPort port)).length)
  | cons {state next final ticks spans} : Turing.TM2.step (fun label => SpaceTM.statement (program.code label)) state=some next →
      PhysicalTrace program next final ticks spans →
      PhysicalTrace program state final (ticks+1) (fun port => max (state.stk (SpaceTM.workPort port)).length (spans port))

theorem physical [DecidableEq K] {program : SpaceMachine.Program K Q} {state final ticks spans}
    (trace : Trace program state final ticks spans) :
    PhysicalTrace program (SpaceTM.configuration state) (SpaceTM.configuration final) ticks spans := by
  induction trace with
  | refl state => exact PhysicalTrace.refl _
  | @cons state middle final ticks spans actual rest ih =>
    have compiled := SpaceTM.step program state
    rw [actual] at compiled
    exact PhysicalTrace.cons compiled ih

theorem bounded [Fintype K] [DecidableEq K] {program : SpaceMachine.Program K Q} {state final ticks peak}
    (trace : SpaceMachine.Execution program state final ticks peak) :
    ∃ spans, Trace program state final ticks spans ∧ ∀ port, spans port ≤ peak := by
  induction trace with
  | refl state => exact ⟨_,Trace.refl _,fun port => SpaceConfigurations.work_length_le state port⟩
  | @cons state middle final ticks peak actual rest ih =>
    obtain ⟨spans,tail,bound⟩ := ih
    refine ⟨_,Trace.cons actual tail,?_⟩
    intro port
    exact max_le_max (SpaceConfigurations.work_length_le state port) (bound port)

theorem allocated_cells [Fintype K] [DecidableEq K] {program : SpaceMachine.Program K Q} {state final ticks peak}
    (trace : SpaceMachine.Execution program state final ticks peak) :
    ∃ spans, Trace program state final ticks spans ∧
      PhysicalTrace program (SpaceTM.configuration state) (SpaceTM.configuration final) ticks spans ∧
      (∑ port, spans port)+Fintype.card K ≤ Fintype.card K*(peak+1) := by
  obtain ⟨spans,actual,bound⟩ := bounded trace
  have total : (∑ port, spans port) ≤ Fintype.card K*peak := by
    simpa using Finset.sum_le_sum (fun port (_ : port ∈ Finset.univ) => bound port)
  refine ⟨spans,actual,physical actual,?_⟩
  rw [Nat.mul_add,Nat.mul_one]
  omega

end Controller.Complexity.SpaceFootprint
