module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.UniformDAGResources

@[expose] public section

/-! Shared evaluation from one retained source packet and channel table.
The fixed loop reads the loaded graph, appends only the node-value table and
preserves the caller's stack and observations for the next probe. -/
namespace Controller.Cost.SharedGraphEvaluation
open Controller.Decoder Controller.Decoder.DAG Controller.Cost.GateProgram
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestInputStored
open Controller.Cost.ForestInputPrefixStored Controller.Cost.UniformDAGRun
open Controller.Cost.UniformDAGSource

def code (width n entry : Nat) (rows : List Row) (roots : List Nat) : Code width :=
  UniformDAGLoop.code width entry 1
    (UniformDAGTypedNode.layout (packetHeaderHeap width n rows roots) rows roots (fun _ : Channel n => false))

@[simp] theorem code_length (width n entry : Nat) (rows : List Row) (roots : List Nat) :
    (code width n entry rows roots).length = 126 := by simp [code]

theorem layout_independent (width n : Nat) (rows : List Row) (roots : List Nat)
    (left right : Assignment n) :
    UniformDAGTypedNode.layout (packetHeaderHeap width n rows roots) rows roots left =
      UniformDAGTypedNode.layout (packetHeaderHeap width n rows roots) rows roots right := by
  simp [UniformDAGTypedNode.layout]

set_option maxHeartbeats 2000000 in
theorem execution (resident : Program width 4) (state : State width 4)
    (graph : DAG n) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (heads : HeadsMatch graph rows matched)
    (rootMatches : RootsMatch graph roots) (values : Assignment n) (entry : Nat)
    (physical : state.heap = channelHeap (packetHeaderHeap width n rows roots) rows roots values)
    (position : state.pc = word width entry) (running : state.halted = false)
    (fits : entry + 126 < 2 ^ width) (capacity : 256 * (graph.countedSize + 1) < 2 ^ width)
    (storedCode : BlockAt resident entry (code width n entry rows roots)) :
    ∃ final ticks peak, Execution resident state final ticks peak ∧
      ticks ≤ 43 * graph.countedSize + 6 ∧ peak ≤ state.liveWords + graph.nodeCount + 4 ∧
      final.heap = evaluationHeap (packetHeaderHeap width n rows roots) rows roots values (graph.evalTable values) ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry + 126) ∧ final.halted = false := by
  have size := graph.countedSize_eq
  obtain ⟨children, guards⟩ := matched_incidence_lengths graph rows matched
  have rootCount : roots.length = graph.roots.length := by rw [rootMatches]; simp
  have heapBound : (cacheHeap width (packetHeaderHeap width n rows roots) rows roots).size + n + graph.nodeCount < 2 ^ width := by
    simp only [cacheHeap_size, packetHeaderHeap_size]
    rw [matched.length_eq, children, guards, rootCount]
    omega
  have firstPrefix : 1 < (cacheHeap width (packetHeaderHeap width n rows roots) rows roots).size := by simp; omega
  have countBound : 1 < state.heap.size := by rw [physical, channelHeap_size]; omega
  have countCell : state.heap[1]'countBound = word width graph.nodeCount := by
    simpa only [physical, channelHeap] using (source_preserved (cacheHeap width (packetHeaderHeap width n rows roots) rows roots) values 1 firstPrefix).trans
      (packet_node_count graph rows roots matched)
  have start : state.heap = evaluationHeap (packetHeaderHeap width n rows roots) rows roots values
      (graph.evalPrefix values 0 (Nat.zero_le _)) := by
    rw [physical]
    simp [evaluationHeap, withValues]
  have actualCode : BlockAt resident entry
      (UniformDAGLoop.code width entry 1
        (UniformDAGTypedNode.layout (packetHeaderHeap width n rows roots) rows roots values)) := by
    rw [layout_independent width n rows roots values (fun _ => false)]
    exact storedCode
  obtain ⟨final, ticks, peak, trace, time, space, heap, stack, output, pc, halted⟩ :=
    UniformDAGRun.execution resident state (packetHeaderHeap width n rows roots) graph rows roots matched heads
      values entry 1 start (by omega) countBound countCell position running fits (by omega) actualCode
  refine ⟨final, ticks, peak, trace, ?_, space, heap, stack, output, pc, halted⟩
  rw [weights_sum] at time
  omega

end Controller.Cost.SharedGraphEvaluation
