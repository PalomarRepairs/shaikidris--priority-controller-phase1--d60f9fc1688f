module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.SpaceTapeBridge
public import Mathlib.Data.Int.Interval

@[expose] public section

/-! Finite visited-cell certificates for the ordinary multitape simulation.
The bound counts the start cell, bottom marker and the blank cell beyond
each stack; immutable input and append-only output have separate tapes. -/
namespace Controller.Complexity.SpaceTapeAllocation
open SpaceTapeMachine SpaceTapeRun
open scoped BigOperators

inductive Covered [DecidableEq K] (enumeration : Fin n ≃ K) (program : SpaceMachine.Program K Q)
    (cells : K → Finset Int) : SpaceTapeMachine.State n K Q → SpaceTapeMachine.State n K Q → Nat → Prop
  | refl {state} : (∀ port, state.heads port ∈ cells port) → Covered enumeration program cells state state 0
  | cons {state next final ticks} : SpaceTapeMachine.step enumeration program state=some next →
      (∀ port, state.heads port ∈ cells port) → Covered enumeration program cells next final ticks →
      Covered enumeration program cells state final (ticks+1)

theorem covered [DecidableEq K] {enumeration : Fin n ≃ K} {program : SpaceMachine.Program K Q}
    {capacity state final ticks} (actual : Run enumeration program capacity state final ticks) :
    Covered enumeration program (fun _ => Finset.Ico 0 (capacity : Int)) state final ticks := by
  induction actual with
  | refl within => exact Covered.refl (fun port => Finset.mem_Ico.mpr (within port))
  | cons transition within rest ih => exact Covered.cons transition (fun port => Finset.mem_Ico.mpr (within port)) ih

theorem cells [Fintype K] [DecidableEq K] {enumeration : Fin n ≃ K} {program : SpaceMachine.Program K Q}
    {capacity state final ticks} (actual : Run enumeration program capacity state final ticks) :
    ∃ allocated : K → Finset Int, Covered enumeration program allocated state final ticks ∧
      (∑ port, (allocated port).card)=Fintype.card K*capacity := by
  refine ⟨_,covered actual,?_⟩
  simp [Int.card_Ico]

theorem logspace [Fintype K] [DecidableEq K] [Fintype Q]
    (enumeration : Fin n ≃ K) {program : SpaceMachine.Program K Q} {function constant}
    (computed : LogSpaceBounds.Computes program function constant) (input : List Bool) :
    ∃ final ticks allocated,
      Covered enumeration program allocated (SpaceTapeMachine.initial input) (configuration final) ticks ∧
      final.pc=none ∧ final.output.reverse=function input ∧
      (∑ port, (allocated port).card)=Fintype.card K*(constant+2)*LogSpaceBounds.bits input.length ∧
      ticks ≤ n+1+2*LogSpaceBounds.timeBound (Fintype.card Q) (Fintype.card K) constant input.length := by
  obtain ⟨final,ticks,actual,halted,output,time⟩ := SpaceTapeBridge.computes enumeration computed input
  obtain ⟨allocated,physical,space⟩ := cells actual
  exact ⟨final,ticks,allocated,physical,halted,output,by simpa only [Nat.mul_assoc] using space,time⟩

end Controller.Complexity.SpaceTapeAllocation
