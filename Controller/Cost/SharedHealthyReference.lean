module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedReusableProbe
public import Controller.Basic.Assignments

@[expose] public section

/-! The healthy reference is evaluated on the original singleton and retained as tagged root words. -/
namespace Controller.Cost.SharedHealthyReference
open Controller.Decoder Controller.Decoder.DAG Controller.Cost.GateProgram
open Controller.Cost.ForestIndexedOperands Controller.Cost.UniformDAGSource
open Controller.Cost.UniformDAGRun Controller.Cost.ForestInputPrefixStored
open Controller.Cost.RawTransferLoops

def reference (graph : DAG n) (target : Fin n) (width : Nat) : List (Word width) :=
  graph.roots.map (fun root => if graph.eval (assignmentOfSet {target}) root then
    word width target.val else word width (n + 1))

private theorem updated_replicate (roots : List (Nat × Bool)) (candidate sentinel : Word width) :
    SharedRootAggregate.updated candidate roots (List.replicate roots.length sentinel) =
      roots.map (fun root => if root.2 then candidate else sentinel) := by
  induction roots with
  | nil => rfl
  | cons root roots ih =>
    simpa [SharedRootAggregate.updated, List.replicate_succ] using congrArg (List.cons (if root.2 then candidate else sentinel)) ih

@[simp] theorem reference_length (graph : DAG n) (target : Fin n) (width : Nat) :
    (reference graph target width).length = graph.roots.length := by simp [reference]

theorem decode_reference (graph : DAG n) (target : Fin n) (width : Nat)
    (capacity : 256 * (graph.countedSize + 1) < 2 ^ width) :
    (reference graph target width).map (fun value => decide (value = word width target.val)) =
      graph.roots.map (fun root => graph.eval (assignmentOfSet {target}) root) := by
  have size := graph.countedSize_eq
  have sentinelFits : n + 1 < 2 ^ width := by omega
  have targetFits : target.val < 2 ^ width := by omega
  have distinct : word width (n + 1) ≠ word width target.val := by
    intro equal
    have numbers := congrArg Fin.val equal
    simp only [word, Nat.mod_eq_of_lt sentinelFits, Nat.mod_eq_of_lt targetFits] at numbers
    omega
  simp only [reference, List.map_map]
  apply List.map_congr_left
  intro root member
  cases value : graph.eval (assignmentOfSet {target}) root <;> simp [value, distinct]

set_option maxHeartbeats 2000000 in
theorem execution (resident : Program width 8) (state : State width 8)
    (graph : DAG n) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (heads : HeadsMatch graph rows matched)
    (rootMatches : RootsMatch graph roots) (target : Fin n)
    (suffix : List (Word width)) (entry done : Nat)
    (capacity : 256 * (graph.countedSize + 1) < 2 ^ width)
    (physical : CodeAt resident entry (SharedReusableProbe.code width n rows roots entry done))
    (room : entry + 167 < 2 ^ width)
    (position : state.pc = word width entry) (running : state.halted = false)
    (heapStored : state.heap = channelHeap (packetHeaderHeap width n rows roots) rows roots
      (assignmentOfSet {target}))
    (input : state.stack = List.replicate graph.roots.length (word width (n + 1)) ++ suffix)
    (held : state.reg 4 = word width target.val) :
    ∃ final ticks peak, Execution resident state final ticks peak ∧
      ticks ≤ 72 * graph.countedSize + 22 ∧
      peak ≤ 8 * graph.countedSize + 18 + state.stack.length + state.output.length ∧
      final.heap = state.heap ∧ final.stack = reference graph target width ++ suffix ∧
      final.output = state.output ∧ final.pc = word width done ∧ final.halted = false ∧
      final.reg 4 = word width target.val := by
  obtain ⟨final, ticks, peak, trace, time, space, heap, stack, output, pc, active, reg⟩ :=
    SharedReusableProbe.execution resident state graph rows roots matched heads rootMatches
      (assignmentOfSet {target}) (List.replicate graph.roots.length (word width (n + 1)))
      suffix (word width target.val) entry done capacity physical room position running heapStored input
      (by simp) held
  have tagged : SharedRootAggregate.updated (word width target.val)
      (graph.roots.map (fun root => (root.val, graph.eval (assignmentOfSet {target}) root)))
      (List.replicate graph.roots.length (word width (n + 1))) = reference graph target width := by
    rw [← List.length_map (f := fun root => (root.val, graph.eval (assignmentOfSet {target}) root)), updated_replicate]
    simp [reference, List.map_map]
  exact ⟨final, ticks, peak, trace, time, space, heap, by simpa only [tagged] using stack,
    output, pc, active, reg⟩

end Controller.Cost.SharedHealthyReference
