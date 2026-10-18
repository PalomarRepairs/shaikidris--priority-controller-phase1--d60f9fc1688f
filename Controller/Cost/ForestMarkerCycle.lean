module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestMarkerCollect
public import Controller.Cost.ForestScopeCharging

@[expose] public section

/-!
# Scope-marker collection and restoration cycle

One program installs the touched-list sentinel, executes every supplied touch
block, and falls through to a reusable reset loop. The resulting execution
restores the entire heap and trailing stack/output frames. Address bounds,
word-width bounds and coverage of the actual emitted code are explicit.
Registers zero through two are outputs. This cycle accounts for marker work;
decoder traversal, selector work and code construction have separate costs.
-/
namespace Controller.Cost.ForestMarkerCycle

open Controller.Decoder Controller.Cost.GateProgram
open Controller.Cost.ForestCounter Controller.Cost.ForestScopeMarkers
open Controller.Cost.ForestMarkerResetLoop Controller.Cost.ForestMarkerCollect

/-- Every recorded fresh ID comes from a supplied incidence. -/
theorem touched_subset (labels : List (Channel n)) (coordinate : Channel n)
    (member : coordinate ∈ (touchAll ForestScopeMarkers.empty labels).touched) :
    coordinate ∈ labels := by
  have well := touchAll_wellFormed (ForestScopeMarkers.empty : MarkState n) labels empty_wellFormed
  have marked := (well.2 coordinate).mpr member
  have source := (touchAll_marked (ForestScopeMarkers.empty : MarkState n) labels coordinate).mp marked
  rcases source with impossible | present
  · simp only [ForestScopeMarkers.empty] at impossible
    contradiction
  · exact present

theorem collectedHeap_outside (width offset : ℕ) (heap : Array (Word width))
    (labels : List (Channel n)) (address : ℕ)
    (outside : ForestGuardRestore.Outside offset n address) :
    (collectedHeap width offset heap labels)[address]? = heap[address]? := by
  induction labels generalizing heap with
  | nil => rfl
  | cons coordinate rest ih =>
      change (collectedHeap width offset (touchHeap width offset heap coordinate) rest)[address]? = _
      exact (ih (touchHeap width offset heap coordinate)).trans
        (touchHeap_outside width offset heap coordinate address outside)

/-- The same fetched program performs collection and sparse restoration.
The restored heap includes every disjoint persistent caller region. -/
theorem cycle_execution (program : Program width 4) (heap : Array (Word width))
    (base offset : ℕ) (labels : List (Channel n))
    (address loaded temporary : Word width) (stack output : List (Word width))
    (stored : MarkersStored heap offset (ForestScopeMarkers.empty : MarkState n))
    (positiveOffset : 0 < offset)
    (fits : base + 2 + 9 * labels.length + 7 < 2 ^ width)
    (addressFits : ∀ coordinate ∈ labels, offset + coordinate.val < 2 ^ width)
    (oneFits : 1 < 2 ^ width)
    (sentinel : BlockAt program base (sentinelCode width))
    (touches : TouchBlocks program (base + 2) offset labels)
    (reset : BlockAt program (base + 2 + 9 * labels.length)
      (resetLoopCode width (base + 2 + 9 * labels.length) offset)) :
    ∃ finalLoaded finalTemporary : Word width, ∃ ticks : ℕ,
      Execution program ((counterState heap base address loaded temporary).frame stack output)
        ((counterState heap (base + 2 + 9 * labels.length + 7) (word width 0)
          finalLoaded finalTemporary).frame stack output)
        ticks (6 + heap.size + (touchAll ForestScopeMarkers.empty labels).touched.length +
          (stack.length + output.length)) ∧
      ticks = 4 + 5 * labels.length + 9 * (touchAll ForestScopeMarkers.empty labels).touched.length ∧
      ticks ≤ 14 * labels.length + 4 := by
  obtain ⟨a, l, t, collectTicks, collectPeak, collectTrace, collectCost, collectUpper, collectBound, well, markedStored⟩ :=
    collect_from_empty program heap base offset labels address loaded temporary stack output stored
      (by omega) addressFits oneFits sentinel touches
  obtain ⟨finalLoaded, finalTemporary, resetTrace⟩ :=
    list_execution_framed program (collectedHeap width offset heap labels)
      (base + 2 + 9 * labels.length) offset (touchAll ForestScopeMarkers.empty labels).touched
      a l t stack output positiveOffset fits (by
        intro coordinate present
        exact ⟨markedStored.valid coordinate, addressFits coordinate (touched_subset labels coordinate present)⟩) reset
  have restore : clearList width offset (collectedHeap width offset heap labels)
      (touchAll ForestScopeMarkers.empty labels).touched = heap :=
    clearList_heap_restore width offset heap (collectedHeap width offset heap labels)
      (touchAll ForestScopeMarkers.empty labels) well stored markedStored
      (fun address outside => collectedHeap_outside width offset heap labels address outside)
  rw [restore, collectedHeap_size] at resetTrace
  have joined := collectTrace.append resetTrace
  rw [max_eq_right collectBound] at joined
  have countBound := touchAll_length_le (ForestScopeMarkers.empty : MarkState n) labels
  simp only [show (ForestScopeMarkers.empty : MarkState n).touched.length = 0 from rfl,
    Nat.zero_add] at countBound
  refine ⟨finalLoaded, finalTemporary,
    collectTicks + (7 * (touchAll ForestScopeMarkers.empty labels).touched.length + 2),
    joined, ?_, ?_⟩ <;> omega

/-- The concrete cone-label collection/reset budget is linear in all stored
forest incidences. This is a marker-cycle budget, not a whole-decoder bound. -/
theorem root_marker_budget (graph : DAG n) (guarded : graph.Guarded)
    (forest : graph.FormulaForest) :
    (graph.roots.map fun node => 14 * (scopeLabels graph node).length + 4).sum ≤
      14 * (graph.roots.length + graph.childIncidences + graph.guardIncidences) +
        4 * graph.roots.length := by
  have bound := ForestScopeCharging.rootLabels_length_le graph guarded forest
  have identity : ∀ nodes : List (Fin graph.nodeCount),
      (nodes.map fun node => 14 * (scopeLabels graph node).length + 4).sum =
        14 * (nodes.flatMap (scopeLabels graph)).length + 4 * nodes.length := by
    intro nodes
    induction nodes with
    | nil => simp
    | cons node rest ih =>
        simp only [List.map_cons, List.sum_cons, List.flatMap_cons, List.length_append, List.length_cons]
        omega
  rw [identity graph.roots]
  change (ForestScopeCharging.rootLabels graph).length ≤ _ at bound
  change 14 * (ForestScopeCharging.rootLabels graph).length + 4 * graph.roots.length ≤ _
  omega

end Controller.Cost.ForestMarkerCycle
