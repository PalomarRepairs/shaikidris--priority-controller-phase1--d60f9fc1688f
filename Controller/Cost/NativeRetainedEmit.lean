module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.NativeRetainedCaller

public import Mathlib.Tactic.FinCases

@[expose] public section

/-! Stored native assignments are emitted by fetched loads in the eight-register caller. -/
namespace Controller.Cost.NativeRetainedEmit
open Controller.Cost.GateProgram Controller.Cost.NativeCircuitExecution

theorem execution (resident : Program width 8) (state : State width 8) (base entry : Nat)
    (values : Fin count → Bool) (stored : TableStored state.heap base values)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 3 * count < 2 ^ width) (heapFits : state.heap.size < 2 ^ width)
    (physical : ForestZeroCallerWiden.WidenedBlockAt resident entry
      (OutputProgram.emitCode width (NativeRealizedCore.addresses base count))) :
    ∃ final, Execution resident state final (3 * count) (state.liveWords + count) ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧
      final.output = (NativeRootLoad.words width values).reverse ++ state.output ∧
      final.pc = word width (entry + 3 * count) ∧ final.halted = false ∧
      (∀ register : Fin 8, 4 ≤ register.val → final.reg register = state.reg register) := by
  let low : State width 4 := {
    reg := fun register => state.reg ⟨register.val, by omega⟩
    heap := state.heap, stack := state.stack, output := state.output, pc := state.pc, halted := state.halted }
  have valid : ∀ address ∈ NativeRealizedCore.addresses base count, address < low.heap.size := by
    intro address member
    obtain ⟨index, present, rfl⟩ := List.mem_map.mp member
    exact (stored.2 index).choose
  obtain ⟨final, trace, heap, stack, output, pc, active⟩ :=
    OutputProgram.emitCode_execution (ForestZeroCallerWiden.lowerProgram resident) low entry
      (NativeRealizedCore.addresses base count) position running
      (by simpa only [NativeRealizedCore.addresses_length] using room) heapFits valid
      (ForestZeroCallerWiden.lower_block _ _ _ physical)
  have widened := ForestZeroCallerWiden.execution resident low final _ _ trace active state.reg
  have startEq : RegisterWiden.widenState low state.reg = state := by
    cases state
    simp only [RegisterWiden.widenState, low, State.mk.injEq, and_true]
    funext register
    fin_cases register <;> rfl
  rw [startEq] at widened
  refine ⟨RegisterWiden.widenState final state.reg, ?_, heap, stack, ?_, ?_, active, ?_⟩
  · convert widened using 1
    · simp only [NativeRealizedCore.addresses_length]
    · simp only [low, State.liveWords, NativeRealizedCore.addresses_length]; omega
  · simpa only [NativeRealizedCore.emitted_words low.heap base values stored, RegisterWiden.widenState_output, low] using output
  · simpa only [NativeRealizedCore.addresses_length, RegisterWiden.widenState_pc] using pc
  · intro register large
    exact RegisterWiden.widenState_high final state.reg register large

end Controller.Cost.NativeRetainedEmit
