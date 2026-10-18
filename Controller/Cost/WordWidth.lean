module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.OutputProgram
public import Mathlib.Data.Nat.Log

@[expose] public section

/-! A logarithmic word-width choice discharges concrete decoder program and
heap capacities. Input decoding, compilation and sparse workspace costs are
separate from this represented execution. -/
namespace Controller.Cost.WordWidth
open Controller.Decoder Controller.Cost.GateProgram Controller.Cost.OutputProgram

def width (graph : DAG n) : Nat := Nat.log 2 (graph.countedSize + 1) + 5

/-- Five extra bits cover constant-factor program addresses, including empty graphs. -/
theorem capacity (graph : DAG n) : 16 * (graph.countedSize + 1) < 2 ^ width graph := by
  have basic := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (graph.countedSize + 1)
  have scaled := Nat.mul_lt_mul_of_pos_left basic (by decide : 0 < 16)
  have identity : 16 * 2 ^ (Nat.log 2 (graph.countedSize + 1) + 1) = 2 ^ width graph := by
    simp only [width, Nat.pow_add, Nat.pow_one, Nat.reducePow]
    omega
  simpa only [Nat.succ_eq_add_one, identity] using scaled

theorem code_fits (graph : DAG n) : (completeCode graph (width graph)).length < 2 ^ width graph := by
  have bound := completeProgram_size_le graph (width graph)
  have size : (completeCode graph (width graph)).length + 1 ≤
      12 * graph.countedSize + 3 * graph.roots.length + 1 := by
    simpa [completeProgram] using bound
  have roots : graph.roots.length ≤ graph.countedSize := by rw [DAG.countedSize_eq]; omega
  have cap := capacity graph
  omega

theorem heap_fits (graph : DAG n) : n + graph.nodeCount < 2 ^ width graph := by
  have table : n + graph.nodeCount ≤ graph.countedSize := by rw [DAG.countedSize_eq]; omega
  have cap := capacity graph
  omega

theorem representable (graph : DAG n) (assignment : Assignment n) :
    Representable (completeProgram graph (width graph))
      (cellState (inputHeap (width graph) assignment) 0 (word (width graph) 0)
        (word (width graph) 0) false) := by
  have cap := capacity graph
  exact completeProgram_representable graph assignment (by omega) (code_fits graph) (heap_fits graph)

/-- Every guarded decoder has a represented execution at the stated logarithmic width. -/
theorem execution (graph : DAG n) (guarded : graph.Guarded) (assignment : Assignment n) :
    ∃ final ticks,
      Execution (completeProgram graph (width graph))
        (cellState (inputHeap (width graph) assignment) 0 (word (width graph) 0)
          (word (width graph) 0) false)
        final ticks (5 + n + graph.nodeCount + graph.roots.length) ∧
      final.halted = true ∧ final.heap.size = n + graph.nodeCount ∧
      Controller.Cost.DAGProgram.ChannelsStored assignment final.heap ∧
      final.output = ((graph.outputValues assignment).map (boolWord (width graph))).reverse ∧
      ticks ≤ 12 * graph.countedSize + 3 * graph.roots.length + 1 :=
  complete_execution_encoded graph guarded assignment (code_fits graph) (heap_fits graph)

theorem bits_bound (graph : DAG n) :
    width graph * (programWords (completeProgram graph (width graph)) +
      (5 + n + graph.nodeCount + graph.roots.length)) ≤
      (Nat.log 2 (graph.countedSize + 1) + 5) * (61 * graph.countedSize + 9) :=
  completeProgram_peak_bits_le graph (width graph)

end Controller.Cost.WordWidth
