module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.SpaceTapeMachine

@[expose] public section

/-! Actual ordinary-tape executions with a bound on every visited work-head
position. The transition function cannot read these positions. -/
namespace Controller.Complexity.SpaceTapeRun
open SpaceTapeMachine SpaceMachine

def Within (capacity : Nat) (state : SpaceTapeMachine.State n K Q) : Prop :=
  ∀ port, 0 ≤ state.heads port ∧ state.heads port < (capacity : Int)

inductive Run [DecidableEq K] (enumeration : Fin n ≃ K) (program : SpaceMachine.Program K Q)
    (capacity : Nat) : SpaceTapeMachine.State n K Q → SpaceTapeMachine.State n K Q → Nat → Prop
  | refl {state} : Within capacity state → Run enumeration program capacity state state 0
  | cons {state next final ticks} : SpaceTapeMachine.step enumeration program state=some next →
      Within capacity state → Run enumeration program capacity next final ticks →
      Run enumeration program capacity state final (ticks+1)

theorem Run.mono [DecidableEq K] {enumeration : Fin n ≃ K} {program : SpaceMachine.Program K Q}
    {capacity larger state final ticks} (run : Run enumeration program capacity state final ticks)
    (bound : capacity ≤ larger) : Run enumeration program larger state final ticks := by
  have widen {state : SpaceTapeMachine.State n K Q} (within : Within capacity state) : Within larger state := by
    intro port
    have current := within port
    constructor <;> omega
  induction run with
  | refl within => exact Run.refl (widen within)
  | cons actual within rest ih => exact Run.cons actual (widen within) ih

theorem Run.append [DecidableEq K] {enumeration : Fin n ≃ K} {program : SpaceMachine.Program K Q}
    {capacity state middle final firstTicks secondTicks}
    (first : Run enumeration program capacity state middle firstTicks)
    (second : Run enumeration program capacity middle final secondTicks) :
    Run enumeration program capacity state final (firstTicks+secondTicks) := by
  induction first with
  | refl => simpa using second
  | cons actual within rest ih =>
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using Run.cons actual within (ih second)

theorem configuration_within (source : SpaceMachine.State K Q) (capacity : Nat)
    (bound : ∀ port, (source.work port).length+2 ≤ capacity) :
    Within capacity (configuration source : SpaceTapeMachine.State n K Q) := by
  intro port
  have current := bound port
  simp only [configuration]
  constructor <;> omega

end Controller.Complexity.SpaceTapeRun
