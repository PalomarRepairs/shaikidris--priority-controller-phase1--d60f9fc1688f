module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestWeightedPhysicalOptimal
public import Controller.Cost.ForestCursorReconstruct

@[expose] public section

/-! Selected descriptor capacity is derived from the actual root scans.
All declared roots share one final descriptor store; later source scans preserve
and bound every earlier selected pointer. The declared root identifier remains
separate from the zero sentinel used for empty routes. -/
namespace Controller.Cost.ForestWeightedReconstruction
open Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestWeightedTagged Controller.Cost.ForestWeightedGlobal
open Controller.Cost.ForestWeightedOptimal Controller.Cost.ForestWeightedSemantics
open Controller.Cost.ForestWeightedPhysicalOptimal Controller.Cost.ForestCursorDescriptors
open Controller.Cost.ForestCursorTraversal Controller.Cost.ForestCursorAllRoots
open Controller.Cost.ForestCursorAllRootsExecution
open Controller.Cost.ForestCursorReconstruct Controller.Cost.ForestCounter
open Controller.Cost.ForestCursorProgram Controller.Cost.GateProgram
variable {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]

/-- The globally selected pointer is an allocated identifier of the actual
final shared builder, including the empty-route sentinel zero. -/
theorem selected_pointer_bound (graph : DAG n) (weights : Channel n → W)
    (b : ℕ) (target : Channel n) (candidate : Candidate W)
    (selected : (runGlobal graph weights b target).2.1.selected = some candidate) :
    candidate.pointer ≤ (buildRoots graph).count := by
  have member := global_member graph weights b target candidate selected
  have actual : some candidate ∈ rootSummaries graph weights b target
      (GenericWeight.total weights Finset.univ) (List.finRange graph.roots.length)
      ⟨((fun _ => 0), 0), initial, none⟩ := by
    simpa only [sourceSummaries, (ForestWeightedTrace.cacheTotal_correct weights).1] using member
  obtain ⟨before, position, after, split, returned⟩ :=
    summary_origin graph weights b target _ ⟨((fun _ => 0), 0), initial, none⟩ rfl candidate actual
  let state := scanRoots graph initial before
  have valid : Valid (beginRoot state) :=
    beginRoot_valid state (scanRoots_valid graph initial initial_valid before)
  have sound := ForestWeightedProvenance.source_selected_sound graph weights
    (graph.roots.get position) position.val b target (beginRoot state) valid
    (fun _ => []) rfl candidate returned
  have localBound : candidate.pointer ≤ (scanRoot graph state position).count := sound.2.1
  have finalEq : buildRoots graph = scanRoots graph (scanRoot graph state position) after := by
    unfold buildRoots
    rw [split, source_scan_append]
    rfl
  rw [finalEq]
  exact localBound.trans (scanRoots_count_ge graph (scanRoot graph state position) after)

/-- Physical materialization and the appended zero region preserve the shared
builder's exact identifier capacity. -/
theorem setup_count (width : ℕ) (heap : Array (Word width)) (graph : DAG n)
    (countFits : (buildRoots graph).count < 2 ^ width)
    (positionFits : ∀ entry ∈ (buildRoots graph).entries, entry.position < 2 ^ width) :
    (setupRoutes width heap graph countFits positionFits).count = (buildRoots graph).count := rfl

/-- One fixed fetched reconstruction operates on the actual selected pointer
and the final shared store. Heap and output are read-only; the added stack is
exactly the forward positional route. Generic weights are not machine words. -/
theorem selected_execution (program : Program width 4) (heap : Array (Word width))
    (graph : DAG n) (weights : Channel n → W) (b : ℕ) (target : Channel n)
    (countFits : (buildRoots graph).count < 2 ^ width)
    (positionFits : ∀ entry ∈ (buildRoots graph).entries, entry.position < 2 ^ width)
    (candidate : Candidate W)
    (selected : (runGlobal graph weights b target).2.1.selected = some candidate)
    (base : ℕ) (heapFits : (setupHeap width heap graph).size ≤ 2 ^ width)
    (programFits : base + 14 < 2 ^ width)
    (block : BlockAt program base (reconstructCode width base
      (setupRoutes width heap graph countFits positionFits).base))
    (loaded temporary : Word width) (stack output : List (Word width)) :
    let routes := setupRoutes width heap graph countFits positionFits
    ∃ finalLoaded finalTemporary : Word width,
      Execution program
        ((counterState (setupHeap width heap graph) base
          (word width candidate.pointer) loaded temporary).frame stack output)
        ((counterState (setupHeap width heap graph) (base + 14) (word width 0)
          finalLoaded finalTemporary).frame
          ((routes.route candidate.pointer).reverse.map (word width) ++ stack) output)
        (14 * (routes.route candidate.pointer).length + 1)
        (5 + (setupHeap width heap graph).size +
          ((routes.route candidate.pointer).length + stack.length + output.length)) ∧
      14 * (routes.route candidate.pointer).length + 1 ≤ 14 * candidate.pointer + 1 ∧
      (routes.route candidate.pointer).length ≤ (buildRoots graph).count := by
  let routes := setupRoutes width heap graph countFits positionFits
  have bounded : candidate.pointer ≤ routes.count := selected_pointer_bound graph weights b target candidate selected
  obtain ⟨finalLoaded, finalTemporary, execution⟩ := route_execution program
    (setupHeap width heap graph) routes base candidate.pointer countFits heapFits
    programFits block bounded loaded temporary stack output
  have bounds := reconstruction_bounds routes candidate.pointer bounded
  exact ⟨finalLoaded, finalTemporary, execution, bounds.1, bounds.2⟩

/-- The reconstructed route belongs to the retained declared root and attains
the global optimum. Its exact execution is the single execution above; no
second route construction is required by the semantic optimum argument. -/
theorem optimal_reconstruction (program : Program width 4) (heap : Array (Word width))
    (graph : DAG n) (guarded : graph.Guarded) (weights : Channel n → W)
    (nonnegative : ∀ channel, 0 ≤ weights channel) (b : ℕ) (target : Channel n)
    (countFits : (buildRoots graph).count < 2 ^ width)
    (positionFits : ∀ entry ∈ (buildRoots graph).entries, entry.position < 2 ^ width)
    (candidate : Candidate W)
    (selected : (runGlobal graph weights b target).2.1.selected = some candidate)
    (base : ℕ) (heapFits : (setupHeap width heap graph).size ≤ 2 ^ width)
    (programFits : base + 14 < 2 ^ width)
    (block : BlockAt program base (reconstructCode width base
      (setupRoutes width heap graph countFits positionFits).base))
    (loaded temporary : Word width) (stack output : List (Word width)) :
    let routes := setupRoutes width heap graph countFits positionFits
    ∃ position : Fin graph.roots.length, candidate.root = position.val ∧
      ∃ head blocked finalLoaded finalTemporary,
        RoutePath graph (graph.roots.get position)
          (routes.route candidate.pointer).reverse head blocked ∧
        pathFeasible b target head blocked ∧
        candidate.score = GenericWeight.total weights (fullUnblocked blocked) ∧
        (∀ other K, Admissible b target K →
          graph.eval (assignmentOfSet K) (graph.roots.get other) = true →
          GenericWeight.total weights K ≤ GenericWeight.total weights (fullUnblocked blocked)) ∧
        Execution program
          ((counterState (setupHeap width heap graph) base
            (word width candidate.pointer) loaded temporary).frame stack output)
          ((counterState (setupHeap width heap graph) (base + 14) (word width 0)
            finalLoaded finalTemporary).frame
            ((routes.route candidate.pointer).reverse.map (word width) ++ stack) output)
          (14 * (routes.route candidate.pointer).length + 1)
          (5 + (setupHeap width heap graph).size +
            ((routes.route candidate.pointer).length + stack.length + output.length)) ∧
        14 * (routes.route candidate.pointer).length + 1 ≤ 14 * candidate.pointer + 1 ∧
        (routes.route candidate.pointer).length ≤ (buildRoots graph).count := by
  obtain ⟨position, rootEq, head, blocked, path, feasible, score, optimal⟩ :=
    global_physical_optimal width heap graph guarded weights nonnegative b target
      countFits positionFits candidate selected
  obtain ⟨finalLoaded, finalTemporary, execution, ticks, length⟩ :=
    selected_execution program heap graph weights b target countFits positionFits
      candidate selected base heapFits programFits block loaded temporary stack output
  exact ⟨position, rootEq, head, blocked, finalLoaded, finalTemporary,
    path, feasible, score, optimal, execution, ticks, length⟩

end Controller.Cost.ForestWeightedReconstruction
