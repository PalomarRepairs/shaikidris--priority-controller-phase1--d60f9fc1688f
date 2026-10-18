module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestWitnessMarshal
public import Controller.Cost.ForestWeightedDirect

@[expose] public section

/-! The direct source recursion computes one shared weight total and the actual
incumbent's declared-root and parent-pointer identifiers. This consumer transports
those identifiers to the fetched marshalling/reconstruction/emission suffix.
Generic ordered-weight arithmetic calls and encoded-word execution remain
separate costs; neither weight bit length nor prior source loading is hidden.
-/
namespace Controller.Cost.ForestWeightedCaller
open Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestCounter Controller.Cost.GateProgram
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestCursorDescriptors
open Controller.Cost.ForestCursorAllRoots Controller.Cost.ForestCursorAllRootsExecution
open Controller.Cost.ForestWeightedGlobal Controller.Cost.ForestWeightedTagged
open Controller.Cost.ForestWitnessWalk Controller.Cost.ForestWitnessMarshal
open Controller.Cost.ForestWeightedPhysicalOptimal
variable {width n : ℕ} {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]

/-- The physical witness budget is exactly a linear charge to stored nodes
and negative-guard incidences, including repeated labels. -/
theorem sourceBudget_exact (graph : DAG n) :
    ForestWitnessAccept.sourceBudget graph graph.nodeCount =
      36 * graph.nodeCount + 11 * graph.guardIncidences := by
  unfold ForestWitnessAccept.sourceBudget ForestWitnessAccept.nodeAllowance
  simp only [Fin.isLt, ite_true, Finset.sum_add_distrib]
  rw [← Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have incidence : (∑ node : Fin graph.nodeCount, (graph.node node).guardLabels.length) =
      graph.guardIncidences := by
    simp only [DAG.guardIncidences, List.sum_ofFn]
  rw [incidence]
  simp only [Nat.cast_id, Nat.mul_comm]

/-- The complete reconstruction/emission suffix has an explicit linear
source-incidence bound once its physical descriptor count is included. -/
theorem suffix_bound (graph : DAG n) :
    14 * (buildRoots graph).count +
      ForestWitnessAccept.sourceBudget graph graph.nodeCount + 10 * n + 16 =
    14 * (buildRoots graph).count + 36 * graph.nodeCount +
      11 * graph.guardIncidences + 10 * n + 16 := by
  rw [sourceBudget_exact]
  omega

theorem direct_selected_emission (program : Program width 4) (heap : Array (Word width))
    (graph : DAG n) (forest : graph.FormulaForest) (guarded : graph.Guarded) (rows : List Row) (roots : List ℕ)
    (matched : RowsMatch graph rows) (rootMatches : RootsMatch graph roots)
    (weights : Channel n → W) (nonnegative : ∀ channel, 0 ≤ weights channel)
    (b : ℕ) (target : Channel n) (candidate : Candidate W)
    (selected : (Controller.Cost.ForestWeightedDirect.runAll graph weights b target).2.data.selected = some candidate)
    (countFits : (buildRoots graph).count < 2 ^ width)
    (positionFits : ∀ entry ∈ (buildRoots graph).entries, entry.position < 2 ^ width)
    (base countAddress : ℕ) (address : Word width) (stack output : List (Word width))
    (countValid : countAddress < heap.size) (countWord : heap[countAddress] = word width n)
    (heapFits : (setupHeap width (cacheHeap width heap rows roots) graph).size ≤ 2 ^ width)
    (programFits : base + 92 < 2 ^ width)
    (block : BlockAt program base
      (preludeCode width base (provenanceCell (cacheHeap width heap rows roots) graph)
        (setupLayout (cacheHeap width heap rows roots) graph).best
        (setupRoutes width (cacheHeap width heap rows roots) graph countFits positionFits).base
        (heap.size + 6 * rows.length + (rowChildren rows).length + (rowGuards rows).length) ++
       ForestWitnessWalk.code width (base + 25)
        (ForestWitnessPath.packetLayout heap.size rows.length
          (setupOffset (cacheHeap width heap rows roots) graph)) countAddress)) :
    (Controller.Cost.ForestWeightedDirect.runAll graph weights b target).2.arithmetic ≤
      n + 8 * (graph.roots.length + graph.childIncidences) + 4 * graph.guardIncidences ∧
    ∃ position : Fin graph.roots.length, candidate.root = position.val ∧
      ∃ blocked final ticks peak,
        Admissible b target (fullUnblocked blocked) ∧
        graph.eval (assignmentOfSet (fullUnblocked blocked)) (graph.roots.get position) = true ∧
        candidate.score = GenericWeight.total weights (fullUnblocked blocked) ∧
        (∀ other K, Admissible b target K →
          graph.eval (assignmentOfSet K) (graph.roots.get other) = true →
          GenericWeight.total weights K ≤ GenericWeight.total weights (fullUnblocked blocked)) ∧
        Execution program
          ((counterState (setupHeap width (cacheHeap width heap rows roots) graph) base address
            (word width candidate.root) (word width candidate.pointer)).frame stack output)
          final ticks peak ∧
        ticks ≤ 14 * (buildRoots graph).count + ForestWitnessAccept.sourceBudget graph graph.nodeCount +
          10 * n + 16 ∧
        peak ≤ 5 + (setupHeap width (cacheHeap width heap rows roots) graph).size +
          (buildRoots graph).count + stack.length + output.length + n + 1 ∧
        final.stack = stack ∧
        final.output = List.ofFn (fun channel : Channel n =>
          boolWord width (decide (channel ∈ fullUnblocked blocked))) ++ output := by
  have projected := (Controller.Cost.ForestWeightedDirect.runAll_projection graph weights b target).1
  have selectedGlobal : (runGlobal graph weights b target).2.1.selected = some candidate := by
    rw [← projected]
    exact selected
  exact ⟨Controller.Cost.ForestWeightedDirect.runAll_arithmetic_bound graph forest weights b target,
    selected_emission program heap graph guarded rows roots matched rootMatches weights nonnegative
      b target candidate selectedGlobal countFits positionFits base countAddress address stack output
      countValid countWord heapFits programFits block⟩

end Controller.Cost.ForestWeightedCaller
