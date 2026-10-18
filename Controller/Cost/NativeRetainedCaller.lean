module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.NativeRetainedExecution
public import Controller.Cost.ForestZeroCallerWiden

public import Mathlib.Tactic.FinCases

@[expose] public section

/-! The retained-heap native run executes directly inside an eight-register caller. -/
namespace Controller.Cost.NativeRetainedCaller
open Controller.Cost.GateProgram Controller.Native Controller.Native.SourceController
open Controller.Cost.NativeCircuitExecution Controller.Cost.NativeSourceExecution

set_option maxHeartbeats 2000000 in
theorem execution (parameters : Parameters) (K : Finset (Channel parameters.channels))
    (resident : Program width 8) (state : State width 8) (entry : Nat) (suffix : List (Word width))
    (position : state.pc = word width entry) (running : state.halted = false)
    (input : state.stack = NativeRootLoad.words width (assignmentOfSet K) ++ suffix)
    (room : entry + (NativeRetainedExecution.code parameters width state.heap.size entry).length < 2 ^ width)
    (boolFits : 1 < 2 ^ width)
    (tableRoom : state.heap.size + parameters.channels + (compile parameters).toState.count < 2 ^ width)
    (physical : ForestZeroCallerWiden.WidenedBlockAt resident entry
      (NativeRetainedExecution.code parameters width state.heap.size entry)) :
    ∃ final ticks, Execution resident state final ticks (state.liveWords + (compile parameters).toState.count) ∧
      ticks ≤ 2 * parameters.channels + 16 * SourceInitialIDs.rootCount parameters + 13 * (selectedSize parameters).total ∧
      TableStored final.heap (state.heap.size + parameters.channels)
        (SourceLift.finite parameters (Physical.realizeBridge parameters.bridge parameters.positiveBuses K)) ∧
      final.stack = suffix ∧ final.output = state.output ∧
      final.pc = word width (entry + (NativeRetainedExecution.code parameters width state.heap.size entry).length) ∧
      final.halted = false ∧ (∃ appended : Array (Word width), final.heap = state.heap ++ appended) ∧
      (∀ register : Fin 8, 4 ≤ register.val → final.reg register = state.reg register) := by
  let low : State width 4 := {
    reg := fun register => state.reg ⟨register.val, by omega⟩
    heap := state.heap, stack := state.stack, output := state.output, pc := state.pc, halted := state.halted }
  obtain ⟨final, ticks, trace, bound, table, stack, output, pc, active, appended⟩ :=
    NativeRetainedExecution.execution parameters K (ForestZeroCallerWiden.lowerProgram resident) low entry suffix
      position running input room boolFits tableRoom (ForestZeroCallerWiden.lower_block _ _ _ physical)
  have widened := ForestZeroCallerWiden.execution resident low final ticks
    (low.liveWords + (compile parameters).toState.count) trace active state.reg
  have startEq : RegisterWiden.widenState low state.reg = state := by
    cases state
    simp only [RegisterWiden.widenState, low, State.mk.injEq, and_true]
    funext register
    fin_cases register <;> rfl
  rw [startEq] at widened
  refine ⟨RegisterWiden.widenState final state.reg, ticks, ?_, bound, table, stack, output, pc, active, appended, ?_⟩
  · convert widened using 1
    simp only [low, State.liveWords]
    omega
  · intro register large
    exact RegisterWiden.widenState_high final state.reg register large

end Controller.Cost.NativeRetainedCaller
