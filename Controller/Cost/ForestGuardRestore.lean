module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestGuardRefinement

@[expose] public section

/-!
# Guard-counter heap restoration

Every guard store is confined to its indexed counter region. Balanced root
schedules restore initially zero counters and leave every outside cell intact,
so the complete heap can be reused. The theorem preserves the explicit initial
layout and word-width hypotheses of the guard-only refinement. Counter operations
overwrite address, counter and increment registers, while the boundary fixes
the fourth register to zero. The retained frame covers stack and output, not
arbitrary register values. Persistent selector metadata must occupy disjoint heap cells,
or its register restoration must be separately executed and charged. Heap
initialization, selector arithmetic and traversal costs are separate.
-/
namespace Controller.Cost.ForestGuardRestore

open Controller.Decoder Controller.Cost.GateProgram
open Controller.Cost.ForestCounter Controller.Cost.ForestGuardSchedule
open Controller.Cost.ForestGuardSafety Controller.Cost.ForestGuardRefinement

variable {n : ℕ}

def Outside (offset size address : ℕ) : Prop := address < offset ∨ offset + size ≤ address

theorem event_address_in_region (offset : ℕ) (event : GuardEvent n) :
    offset ≤ offset + event.channel.val ∧ offset + event.channel.val < offset + n := by
  have bounded := event.channel.isLt
  omega

/-- The total update also preserves outside cells when its store is invalid. -/
theorem update_outside (width offset : ℕ) (heap : Array (Word width))
    (event : GuardEvent n) (address : ℕ) (outside : Outside offset n address) :
    (update width offset heap event)[address]? = heap[address]? := by
  have region := event_address_in_region offset event
  have different : offset + event.channel.val ≠ address := by
    unfold Outside at outside
    omega
  by_cases valid : offset + event.channel.val < heap.size
  · simpa only [update, dite_eq_left valid] using
      (Array.getElem?_set_ne (xs := heap)
        (v := word width ((storedWord heap (offset + event.channel.val)).val +
          (word width (event.delta width)).val)) valid different)
  · simp only [update, dite_eq_right valid]

theorem finalHeap_size (width offset : ℕ) (heap : Array (Word width))
    (events : List (GuardEvent n)) : (finalHeap width offset heap events).size = heap.size := by
  induction events generalizing heap with
  | nil => rfl
  | cons event rest ih =>
      simpa only [finalHeap, List.foldl_cons, update_size] using
        ih (update width offset heap event)

theorem finalHeap_outside (width offset : ℕ) (heap : Array (Word width))
    (events : List (GuardEvent n)) (address : ℕ) (outside : Outside offset n address) :
    (finalHeap width offset heap events)[address]? = heap[address]? := by
  induction events generalizing heap with
  | nil => rfl
  | cons event rest ih =>
      change (finalHeap width offset (update width offset heap event) rest)[address]? = heap[address]?
      exact (ih (update width offset heap event)).trans
        (update_outside width offset heap event address outside)

/-- The represented counter invariant and outside preservation imply heap equality. -/
theorem zero_region_heap_eq (width offset : ℕ) (initial final : Array (Word width))
    (initialStored : CountersStored initial offset (fun _ : Channel n => 0))
    (finalStored : CountersStored final offset (fun _ : Channel n => 0))
    (outside : ∀ address, Outside offset n address → final[address]? = initial[address]?) :
    final = initial := by
  apply Array.ext_getElem?
  intro address
  by_cases external : Outside offset n address
  · exact outside address external
  · have lower : offset ≤ address := by unfold Outside at external; omega
    have upper : address < offset + n := by unfold Outside at external; omega
    let coordinate : Channel n := ⟨address - offset, by omega⟩
    have location : offset + coordinate.val = address := by
      dsimp only [coordinate]
      omega
    have initialLookup : initial[address]? = some (word width 0) := by
      rw [← location, Array.getElem?_eq_getElem (initialStored.valid coordinate), initialStored.held coordinate]
    have finalLookup : final[address]? = some (word width 0) := by
      rw [← location, Array.getElem?_eq_getElem (finalStored.valid coordinate), finalStored.held coordinate]
    exact finalLookup.trans initialLookup.symm

theorem root_heap_restore (width offset : ℕ) (graph : DAG n)
    (forest : graph.FormulaForest) (heap : Array (Word width))
    (stored : CountersStored heap offset (fun _ : Channel n => 0))
    (counterFits : 2 * graph.guardIncidences + 1 < 2 ^ width) :
    finalHeap width offset heap (rootEvents graph) = heap := by
  have refined := finalHeap_stored width offset heap (fun _ : Channel n => 0)
    (rootEvents graph) stored (root_safe width graph forest counterFits)
  have finalStored : CountersStored (finalHeap width offset heap (rootEvents graph))
      offset (fun _ : Channel n => 0) := by
    simpa only [root_counters_restore] using refined
  exact zero_region_heap_eq width offset heap _ stored finalStored
    (fun address external => finalHeap_outside width offset heap (rootEvents graph) address external)

/-- The genuine machine boundary has the complete initial heap, even with frames. -/
theorem finalState_root_heap (width offset base : ℕ) (graph : DAG n)
    (forest : graph.FormulaForest) (heap : Array (Word width))
    (stored : CountersStored heap offset (fun _ : Channel n => 0))
    (counterFits : 2 * graph.guardIncidences + 1 < 2 ^ width)
    (oldAddress oldCounter oldIncrement : Word width) (stack output : List (Word width)) :
    ((finalState width offset base heap oldAddress oldCounter oldIncrement
      (rootEvents graph)).frame stack output).heap = heap := by
  change (finalState width offset base heap oldAddress oldCounter oldIncrement (rootEvents graph)).heap = heap
  rw [finalState_heap]
  exact root_heap_restore width offset graph forest heap stored counterFits

/-- The checked guard-only execution restores the complete framed heap. -/
theorem root_execution_restore (program : Program width 4) (graph : DAG n)
    (forest : graph.FormulaForest) (offset base : ℕ) (heap : Array (Word width))
    (oldAddress oldCounter oldIncrement : Word width) (stack output : List (Word width))
    (stored : CountersStored heap offset (fun _ : Channel n => 0))
    (heapFits : heap.size ≤ 2 ^ width)
    (counterFits : 2 * graph.guardIncidences + 1 < 2 ^ width)
    (programFits : base + 5 * (rootEvents graph).length < 2 ^ width)
    (block : BlockAt program base (code width offset (rootEvents graph))) :
    Execution program ((counterState heap base oldAddress oldCounter oldIncrement).frame stack output)
      ((finalState width offset base heap oldAddress oldCounter oldIncrement (rootEvents graph)).frame stack output)
      (5 * (rootEvents graph).length) (5 + heap.size + stack.length + output.length) ∧
    ((finalState width offset base heap oldAddress oldCounter oldIncrement
      (rootEvents graph)).frame stack output).heap = heap ∧
    5 * (rootEvents graph).length ≤ 10 * graph.guardIncidences := by
  have checked := root_execution program graph forest offset base heap oldAddress oldCounter oldIncrement
    stack output stored heapFits counterFits programFits block
  exact ⟨checked.1, finalState_root_heap width offset base graph forest heap stored counterFits
    oldAddress oldCounter oldIncrement stack output, checked.2.1⟩

end Controller.Cost.ForestGuardRestore
