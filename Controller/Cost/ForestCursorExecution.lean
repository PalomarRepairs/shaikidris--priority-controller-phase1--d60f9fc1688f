module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestCursorTraversal

@[expose] public section

/-!
# Source-rooted cursor execution

The persistent-cell frame preserves the finite decoder records and shared
parent descriptors across physical counter and selector stores. The initial
heap layout is explicit. Traversal continuations use emitted source blocks;
route lists occur only in the refinement witness.
-/
namespace Controller.Cost.ForestCursorExecution

open Controller.Decoder Controller.Decoder.DAG Controller.Cost.GateProgram
open Controller.Cost.ForestCounter Controller.Cost.ForestCursorProgram
open Controller.Cost.ForestCursorTraversal Controller.Cost.ForestGuardSchedule

/-- Every persistent address is an actual finite source or route record cell. -/
def PersistentCell (graph : DAG n) (records : GraphRecords width initial graph)
    (routes : RouteDescriptors width initial) (address : ℕ) : Prop :=
  (∃ node : Fin graph.nodeCount,
    address = records.recordBase + 2 * node.val ∨
    address = records.recordBase + 2 * node.val + 1) ∨
  (∃ node : Fin graph.nodeCount, ∃ position : Fin (graph.node node).children.length,
    address = records.childBase node + position.val) ∨
  (∃ node : Fin graph.nodeCount, ∃ position : Fin (graph.node node).guardLabels.length,
    address = records.guardBase node + position.val) ∨
  (∃ pointer : ℕ, 0 < pointer ∧ pointer ≤ routes.count ∧
    (address = routes.base + 2 * (pointer - 1) ∨
      address = routes.base + 2 * (pointer - 1) + 1))

/-- The mutable regions are disjoint from all represented persistent cells. -/
structure ReadonlyLayout (graph : DAG n) (records : GraphRecords width initial graph)
    (routes : RouteDescriptors width initial) (layout : SelectorLayout n) : Prop where
  counters : ∀ address, PersistentCell graph records routes address →
    ForestGuardRestore.Outside layout.counterOffset n address
  found : ∀ address, PersistentCell graph records routes address → layout.found ≠ address
  best : ∀ address, PersistentCell graph records routes address → layout.best ≠ address

structure PersistentFrame (graph : DAG n) (records : GraphRecords width initial graph)
    (routes : RouteDescriptors width initial) (current : Array (Word width)) : Prop where
  size : current.size = initial.size
  cells : ∀ address, PersistentCell graph records routes address →
    current[address]? = initial[address]?

/-- A counter store keeps the entire persistent-cell frame, including cells
whose words encode the next navigation or reconstruction pointer. -/
theorem frame_counter (graph : DAG n) (records : GraphRecords width initial graph)
    (routes : RouteDescriptors width initial) (layout : SelectorLayout n)
    (readonly : ReadonlyLayout graph records routes layout)
    (current : Array (Word width)) (frame : PersistentFrame graph records routes current)
    (event : GuardEvent n) :
    PersistentFrame graph records routes (update width layout.counterOffset current event) := by
  refine ⟨(update_size width layout.counterOffset current event).trans frame.size, ?_⟩
  intro address persistent
  exact (ForestGuardRestore.update_outside width layout.counterOffset current event address
    (readonly.counters address persistent)).trans (frame.cells address persistent)

/-- Optional indexed agreement gives the represented word at every persistent
cell without requiring equality of the mutable heap regions. -/
theorem frame_word (graph : DAG n) (records : GraphRecords width initial graph)
    (routes : RouteDescriptors width initial) (current : Array (Word width))
    (frame : PersistentFrame graph records routes current) (address : ℕ)
    (persistent : PersistentCell graph records routes address) :
    storedWord current address = storedWord initial address := by
  unfold storedWord
  rw [frame.cells address persistent]

theorem frame_read (graph : DAG n) (records : GraphRecords width initial graph)
    (routes : RouteDescriptors width initial) (current : Array (Word width))
    (frame : PersistentFrame graph records routes current) (address : ℕ)
    (persistent : PersistentCell graph records routes address) (valid : address < initial.size) :
    current[address]'(by rw [frame.size]; exact valid) = initial[address] := by
  calc
    _ = storedWord current address := (storedWord_eq current address (by rw [frame.size]; exact valid)).symm
    _ = storedWord initial address := frame_word graph records routes current frame address persistent
    _ = _ := storedWord_eq initial address valid

/-- Rebase the actual finite source record representation after any sequence of
counter and selector operations that preserves its persistent cells. -/
def rebaseRecords (graph : DAG n) (records : GraphRecords width initial graph)
    (routes : RouteDescriptors width initial) (current : Array (Word width))
    (frame : PersistentFrame graph records routes current) : GraphRecords width current graph where
  recordBase := records.recordBase
  childBase := records.childBase
  guardBase := records.guardBase
  tagValid := fun node => by rw [frame.size]; exact records.tagValid node
  tagWord := fun node =>
    (frame_read graph records routes current frame _ (Or.inl ⟨node, Or.inl rfl⟩)
      (records.tagValid node)).trans (records.tagWord node)
  headValid := fun node => by rw [frame.size]; exact records.headValid node
  headWord := fun node head equal =>
    (frame_read graph records routes current frame _ (Or.inl ⟨node, Or.inr rfl⟩)
      (records.headValid node)).trans (records.headWord node head equal)
  childValid := fun node position => by rw [frame.size]; exact records.childValid node position
  childWord := fun node position =>
    (frame_read graph records routes current frame _ (Or.inr (Or.inl ⟨node, position, rfl⟩))
      (records.childValid node position)).trans (records.childWord node position)
  guardValid := fun node position => by rw [frame.size]; exact records.guardValid node position
  guardWord := fun node position =>
    (frame_read graph records routes current frame _ (Or.inr (Or.inr (Or.inl ⟨node, position, rfl⟩)))
      (records.guardValid node position)).trans (records.guardWord node position)

theorem persistent_valid (graph : DAG n) (records : GraphRecords width initial graph)
    (routes : RouteDescriptors width initial) (address : ℕ)
    (persistent : PersistentCell graph records routes address) : address < initial.size := by
  rcases persistent with source | child | guard | descriptor
  · obtain ⟨node, tag | head⟩ := source
    · subst address; exact records.tagValid node
    · subst address; exact records.headValid node
  · obtain ⟨node, position, equal⟩ := child
    subst address; exact records.childValid node position
  · obtain ⟨node, position, equal⟩ := guard
    subst address; exact records.guardValid node position
  · obtain ⟨pointer, positive, bounded, parent | position⟩ := descriptor
    · subst address; exact routes.parentValid pointer ⟨positive, bounded⟩
    · subst address; exact routes.positionValid pointer ⟨positive, bounded⟩

/-- Shared parent/position descriptors survive in the intermediate heap, so the
selected pointer always retains the same decoded route. -/
def rebaseRoutes (graph : DAG n) (records : GraphRecords width initial graph)
    (routes : RouteDescriptors width initial) (current : Array (Word width))
    (frame : PersistentFrame graph records routes current) : RouteDescriptors width current where
  base := routes.base
  count := routes.count
  route := routes.route
  sentinel := routes.sentinel
  parentValid := fun pointer valid => by rw [frame.size]; exact routes.parentValid pointer valid
  positionValid := fun pointer valid => by rw [frame.size]; exact routes.positionValid pointer valid
  parentEarlier := fun pointer valid => by
    rw [frame_read graph records routes current frame _
      (Or.inr (Or.inr (Or.inr ⟨pointer, valid.1, valid.2, Or.inl rfl⟩)))
      (routes.parentValid pointer valid)]
    exact routes.parentEarlier pointer valid
  cellRoute := fun pointer valid => by
    rw [frame_read graph records routes current frame _
      (Or.inr (Or.inr (Or.inr ⟨pointer, valid.1, valid.2, Or.inr rfl⟩)))
      (routes.positionValid pointer valid),
      frame_read graph records routes current frame _
      (Or.inr (Or.inr (Or.inr ⟨pointer, valid.1, valid.2, Or.inl rfl⟩)))
      (routes.parentValid pointer valid)]
    exact routes.cellRoute pointer valid

/-- Committing a selected route preserves the persistent source frame. The
selector metadata cells themselves may change and are intentionally excluded. -/
theorem frame_commit (graph : DAG n) (records : GraphRecords width initial graph)
    (routes : RouteDescriptors width initial) (layout : SelectorLayout n)
    (readonly : ReadonlyLayout graph records routes layout)
    (current : Array (Word width)) (frame : PersistentFrame graph records routes current)
    (pointer : ℕ) (foundValid : layout.found < current.size)
    (bestValid : layout.best < current.size) :
    PersistentFrame graph records routes
      (committedHeap width current layout.best layout.found pointer) := by
  have heapEq : committedHeap width current layout.best layout.found pointer =
      (current.set layout.best (word width pointer) bestValid).set layout.found (word width 1)
        (by simpa using foundValid) := by
    simp [committedHeap, Array.setIfInBounds_def, bestValid, foundValid]
  refine ⟨by simpa [heapEq] using frame.size, ?_⟩
  intro address persistent
  rw [heapEq, Array.getElem?_set_ne (by simpa using foundValid)
    (readonly.found address persistent),
    Array.getElem?_set_ne bestValid (readonly.best address persistent)]
  exact frame.cells address persistent

/-- The actual leaf callback keeps the persistent-cell frame on both branches. -/
theorem frame_leaf (graph : DAG n) (records : GraphRecords width initial graph)
    (routes : RouteDescriptors width initial) (layout : SelectorLayout n)
    (readonly : ReadonlyLayout graph records routes layout)
    (current : Array (Word width)) (frame : PersistentFrame graph records routes current)
    (b : ℕ) (target head : Channel n) (counters : GuardCounters n)
    (selected : Option ℕ) (pointer : ℕ) (metadata : SelectorStored current layout selected) :
    PersistentFrame graph records routes
      (leafHeap width current layout b target head counters selected pointer) := by
  unfold leafHeap
  split
  · exact frame_commit graph records routes layout readonly current frame pointer
      metadata.foundValid metadata.bestValid
  · exact frame

end Controller.Cost.ForestCursorExecution
