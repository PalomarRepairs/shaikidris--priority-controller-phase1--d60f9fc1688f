module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestWitnessWalk
public import Controller.Cost.ForestWeightedReconstruction

@[expose] public section

/-! The selected weighted incumbent determines its declared root and its exact
positional route through the once-materialized descriptor store. At the
positional-stack entry boundary, the source-derived walker emits precisely the
admissible maximum-weight assignment. Weight arithmetic and the preceding
root reload/reconstruction have separate execution contracts. The source
budget counts guard occurrences, including repeated channel labels. -/
namespace Controller.Cost.ForestWitnessAccept
open Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.GateProgram Controller.Cost.ForestCounter
open Controller.Cost.ForestWitnessWalk Controller.Cost.ForestCursorAllRoots
open Controller.Cost.ForestCursorAllRootsExecution
open Controller.Cost.ForestCursorDescriptors Controller.Cost.ForestWeightedGlobal
open Controller.Cost.ForestWeightedTagged Controller.Cost.ForestWeightedPhysicalOptimal
open Controller.Cost.ForestIndexedOperands
variable {width n : ℕ}

/-- A node contributes its fixed navigation allowance and every stored guard
incidence. This is a source bound, not a runtime route-list construction. -/
def nodeAllowance (graph : DAG n) (node : Fin graph.nodeCount) : ℕ :=
  36 + 11 * (graph.node node).guardLabels.length

def sourceBudget (graph : DAG n) (limit : ℕ) : ℕ :=
  ∑ node : Fin graph.nodeCount, if node.val < limit then nodeAllowance graph node else 0

theorem sourceBudget_mono (graph : DAG n) {left right : ℕ} (ordered : left ≤ right) :
    sourceBudget graph left ≤ sourceBudget graph right := by
  apply Finset.sum_le_sum
  intro node _
  by_cases lower : node.val < left
  · have upper : node.val < right := lt_of_lt_of_le lower ordered
    simp only [ite_eq_left lower, ite_eq_left upper]
    exact le_rfl
  · simp only [ite_eq_right lower]
    exact Nat.zero_le _

theorem sourceBudget_step (graph : DAG n) (node : Fin graph.nodeCount) :
    sourceBudget graph (node.val + 1) = sourceBudget graph node.val + nodeAllowance graph node := by
  have split (other : Fin graph.nodeCount) :
      (if other.val < node.val + 1 then nodeAllowance graph other else 0) =
        (if other.val < node.val then nodeAllowance graph other else 0) +
          (if other = node then nodeAllowance graph node else 0) := by
    by_cases same : other = node
    · subst other; simp
    · have different : other.val ≠ node.val := fun equal => same (Fin.ext equal)
      by_cases earlier : other.val < node.val
      · have next : other.val < node.val + 1 := by omega
        simp only [ite_eq_left earlier, ite_eq_left next, ite_eq_right same, Nat.add_zero]
      · have later : ¬other.val < node.val + 1 := by omega
        simp only [ite_eq_right earlier, ite_eq_right later, ite_eq_right same, Nat.add_zero]
  unfold sourceBudget
  simp_rw [split]
  rw [Finset.sum_add_distrib]
  simp

/-- Strictly decreasing source indices charge a complete selected route to
actual node/guard incidences without any forest assumption on terminals. -/
theorem routeCost_le_source (graph : DAG n) {node route head blocked ticks}
    (cost : RouteWalkCost graph node route head blocked ticks) :
    ticks ≤ sourceBudget graph (node.val + 1) := by
  induction cost with
  | input node head gate =>
      rw [sourceBudget_step]
      simp only [nodeAllowance, gate, Gate.guardLabels, List.length_nil, Nat.mul_zero, Nat.add_zero]
      omega
  | disj node refs position route head blocked ticks gate tail ih =>
      have earlier : (graph.childIndex node (refs.get position)).val + 1 ≤ node.val :=
        Nat.succ_le_of_lt (refs.get position).isLt
      have bound := ih.trans (sourceBudget_mono graph earlier)
      rw [sourceBudget_step]
      simp only [nodeAllowance, gate, Gate.guardLabels, List.length_nil, Nat.mul_zero, Nat.add_zero]
      omega
  | guard node child labels route head blocked ticks gate tail ih =>
      have earlier : (graph.childIndex node child).val + 1 ≤ node.val :=
        Nat.succ_le_of_lt child.isLt
      have bound := ih.trans (sourceBudget_mono graph earlier)
      rw [sourceBudget_step]
      simp only [nodeAllowance, gate, Gate.guardLabels]
      omega

variable {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]

/-- The endpoint uses the actual selected incumbent and the actual final
source-derived descriptor store. Entry-state register/stack conditions are
exactly the boundary produced by declared-root reload and once reconstruction;
they do not assert that the unweighted first-feasible caller selects a weighted
optimum. The output is checked against the complete weighted semantic domain. -/
theorem selected_stack_emission (program : Program width 4) (heap : Array (Word width))
    (graph : DAG n) (guarded : graph.Guarded) (weights : Channel n → W)
    (nonnegative : ∀ channel, 0 ≤ weights channel) (b : ℕ) (target : Channel n)
    (rows : List Row) (roots : List ℕ) (matched : RowsMatch graph rows)
    (countFits : (buildRoots graph).count < 2 ^ width)
    (positionFits : ∀ entry ∈ (buildRoots graph).entries, entry.position < 2 ^ width)
    (candidate : Candidate W)
    (selected : (runGlobal graph weights b target).2.1.selected = some candidate)
    (s : State width 4) (suffix : List (Word width)) (base countAddress : ℕ)
    (heapEq : s.heap = setupHeap width (cacheHeap width heap rows roots) graph)
    (countBefore : countAddress < setupOffset (cacheHeap width heap rows roots) graph)
    (countWord : s.heap[countAddress]'(by rw [heapEq, setupHeap_size]; unfold setupOffset at countBefore; omega) = word width n)
    (rootHeld : ∀ position : Fin graph.roots.length, candidate.root = position.val →
      s.reg 0 = word width (graph.roots.get position).val)
    (positions : s.stack = ((setupRoutes width (cacheHeap width heap rows roots) graph
      countFits positionFits).route candidate.pointer).reverse.map (word width) ++ suffix)
    (pc : s.pc = word width base) (running : s.halted = false)
    (programFits : base + 67 < 2 ^ width) (heapFits : s.heap.size ≤ 2 ^ width)
    (block : BlockAt program base (ForestWitnessWalk.code width base
      (ForestWitnessPath.packetLayout heap.size rows.length
        (setupOffset (cacheHeap width heap rows roots) graph)) countAddress)) :
    ∃ position : Fin graph.roots.length, candidate.root = position.val ∧
      ∃ blocked final ticks peak,
        Admissible b target (fullUnblocked blocked) ∧
        graph.eval (assignmentOfSet (fullUnblocked blocked)) (graph.roots.get position) = true ∧
        candidate.score = GenericWeight.total weights (fullUnblocked blocked) ∧
        (∀ other K, Admissible b target K →
          graph.eval (assignmentOfSet K) (graph.roots.get other) = true →
          GenericWeight.total weights K ≤ GenericWeight.total weights (fullUnblocked blocked)) ∧
        Execution program s final ticks peak ∧
        ticks ≤ sourceBudget graph graph.nodeCount + 10 * n + 4 ∧
        peak ≤ s.liveWords + n + 1 ∧ final.heap.size = s.heap.size ∧
        final.stack = suffix ∧
        final.output = List.ofFn (fun channel : Channel n =>
          boolWord width (decide (channel ∈ fullUnblocked blocked))) ++ s.output := by
  obtain ⟨position, rootEq, head, blocked, path, feasible, score, optimal⟩ :=
    global_physical_optimal width (cacheHeap width heap rows roots) graph guarded weights
      nonnegative b target countFits positionFits candidate selected
  obtain ⟨walkTicks, cost⟩ := route_cost path
  let layout := ForestWitnessPath.packetLayout heap.size rows.length
    (setupOffset (cacheHeap width heap rows roots) graph)
  have source : WalkSource width s.heap graph layout := by
    rw [heapEq]
    exact loadedSource heap graph rows roots matched (by simpa only [heapEq] using heapFits)
  have zero : MarkerCells source ∅ := by
    intro channel
    have valid : layout.markerBase + channel.val < s.heap.size := by
      have region := source.region; have bounded := channel.isLt; omega
    change s.heap[layout.markerBase + channel.val]'valid = boolWord width (decide (channel ∈ (∅ : Finset (Channel n))))
    simpa only [heapEq, layout, ForestWitnessPath.packetLayout, Finset.notMem_empty, decide_false, boolWord, Bool.false_eq_true, ite_false] using
      setup_zero width (cacheHeap width heap rows roots) graph channel.val (by have := channel.isLt; omega)
  obtain ⟨final, peak, trace, peakBound, size, stack, output, finalPC, finalRunning, nonempty, truth⟩ :=
    walk_and_emit cost feasible.1 program s layout source zero suffix base countAddress
      countBefore countWord (rootHeld position rootEq) positions pc running programFits heapFits block
  have costBound := (routeCost_le_source graph cost).trans
    (sourceBudget_mono graph (Nat.succ_le_of_lt (graph.roots.get position).isLt))
  refine ⟨position, rootEq, blocked, final, walkTicks + 10 * n + 4, peak,
    fullUnblocked_admissible b target head blocked feasible, truth, score, optimal,
    trace, by omega, peakBound, size, stack, ?_⟩
  simpa only [fullUnblocked, Finset.mem_sdiff, Finset.mem_univ, true_and,
    decide_not] using output

end Controller.Cost.ForestWitnessAccept
