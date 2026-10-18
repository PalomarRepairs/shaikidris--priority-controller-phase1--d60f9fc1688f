module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestNodeVisits
public import Controller.Cost.ForestGuardRestore

@[expose] public section

/-!
# Cone scope markers

Scope markers include both input heads and negative guard labels. They are a
separate region from current-path guard counters. The positional label sequence
specifies exactly the semantic cone scope. Touched markers permit resets without
clearing every declared channel for each root. Indexed heap representation is
separate from instruction execution and its operation costs.
-/
namespace Controller.Cost.ForestScopeMarkers

open Controller.Decoder Controller.Cost.GateProgram
open Controller.Cost.ForestGuardSchedule

variable {n : ℕ}

/-- All direct labels encountered by the cone traversal, including repetitions. -/
def scopeLabels (graph : DAG n) (node : Fin graph.nodeCount) : List (Channel n) :=
  (graph.node node).directChannels ++ (graph.node node).children.flatMap
    (fun child => scopeLabels graph (graph.childIndex node child))
termination_by node.val
decreasing_by all_goals exact graph.childIndex_lt _ _

theorem scope_labels (graph : DAG n) : ∀ node : Fin graph.nodeCount,
    (scopeLabels graph node).toFinset = graph.scope node := by
  have claim : ∀ rank : ℕ, ∀ node : Fin graph.nodeCount, node.val = rank →
      (scopeLabels graph node).toFinset = graph.scope node := by
    intro rank
    induction rank using Nat.strong_induction_on with
    | h rank ih =>
      intro node value
      have childrenEq : ∀ child : Fin node.val,
          (scopeLabels graph (graph.childIndex node child)).toFinset =
            graph.scope (graph.childIndex node child) := by
        intro child
        exact ih child.val (by have earlier := graph.childIndex_lt node child; omega)
          (graph.childIndex node child) rfl
      apply Finset.ext
      intro coordinate
      rw [scopeLabels.eq_def, graph.scope_eq]
      simp only [List.mem_toFinset, List.mem_append, List.mem_flatMap,
        Finset.mem_union, Finset.mem_biUnion]
      constructor
      · rintro (direct | ⟨child, listed, member⟩)
        · exact Or.inl direct
        · exact Or.inr ⟨child, listed, by
            have marked : coordinate ∈ (scopeLabels graph (graph.childIndex node child)).toFinset :=
              List.mem_toFinset.mpr member
            simpa only [childrenEq child] using marked⟩
      · rintro (direct | ⟨child, listed, member⟩)
        · exact Or.inl direct
        · exact Or.inr ⟨child, listed, List.mem_toFinset.mp (by
            simpa only [childrenEq child] using member)⟩
  intro node
  exact claim node.val node rfl

@[ext] structure MarkState (n : ℕ) where
  marked : Channel n → Bool
  touched : List (Channel n)

def touch (state : MarkState n) (coordinate : Channel n) : MarkState n :=
  if state.marked coordinate then state else
    ⟨fun current => if current = coordinate then true else state.marked current,
      coordinate :: state.touched⟩

def WellFormed (state : MarkState n) : Prop :=
  state.touched.Nodup ∧ ∀ coordinate, state.marked coordinate = true ↔ coordinate ∈ state.touched

def empty : MarkState n := ⟨fun _ => false, []⟩

theorem empty_wellFormed : WellFormed (empty : MarkState n) := by
  simp [WellFormed, empty]

theorem touch_wellFormed (state : MarkState n) (coordinate : Channel n)
    (well : WellFormed state) : WellFormed (touch state coordinate) := by
  by_cases already : state.marked coordinate = true
  · simpa only [touch, already, ite_true] using well
  · have fresh : coordinate ∉ state.touched := by
      intro present
      exact already ((well.2 coordinate).mpr present)
    have off : state.marked coordinate = false := Bool.eq_false_iff.mpr already
    constructor
    · simpa only [touch, off, Bool.false_eq_true, ite_false] using List.nodup_cons.mpr ⟨fresh, well.1⟩
    · intro current
      by_cases same : current = coordinate
      · subst current
        simp [touch, off]
      · simp [touch, off, same, well.2 current, Ne.symm same]

theorem touch_length_le (state : MarkState n) (coordinate : Channel n) :
    (touch state coordinate).touched.length ≤ state.touched.length + 1 := by
  unfold touch
  split <;> simp <;> omega

def touchAll (state : MarkState n) (labels : List (Channel n)) : MarkState n := labels.foldl touch state

theorem touchAll_wellFormed (state : MarkState n) (labels : List (Channel n))
    (well : WellFormed state) : WellFormed (touchAll state labels) := by
  induction labels generalizing state with
  | nil => exact well
  | cons coordinate rest ih => exact ih (touch state coordinate) (touch_wellFormed state coordinate well)

theorem touchAll_length_le (state : MarkState n) (labels : List (Channel n)) :
    (touchAll state labels).touched.length ≤ state.touched.length + labels.length := by
  induction labels generalizing state with
  | nil => simp [touchAll]
  | cons coordinate rest ih =>
      have bound := ih (touch state coordinate)
      have stepBound := touch_length_le state coordinate
      change (touchAll (touch state coordinate) rest).touched.length ≤ _
      simp only [List.length_cons]
      omega

theorem touch_marked (state : MarkState n) (coordinate current : Channel n) :
    (touch state coordinate).marked current = true ↔
      state.marked current = true ∨ current = coordinate := by
  by_cases marked : state.marked coordinate = true
  · simp only [touch, marked, ite_true]
    constructor
    · exact Or.inl
    · rintro (held | same)
      · exact held
      · simpa only [same] using marked
  · have off : state.marked coordinate = false := Bool.eq_false_iff.mpr marked
    by_cases same : current = coordinate
    · simp [touch, off, same]
    · simp [touch, off, same]

theorem touchAll_marked (state : MarkState n) (labels : List (Channel n))
    (current : Channel n) :
    (touchAll state labels).marked current = true ↔
      state.marked current = true ∨ current ∈ labels := by
  induction labels generalizing state with
  | nil => simp [touchAll]
  | cons coordinate rest ih =>
      change (touchAll (touch state coordinate) rest).marked current = true ↔ _
      rw [ih, touch_marked]
      simp only [List.mem_cons]
      tauto

theorem scope_touch_exact (graph : DAG n) (node : Fin graph.nodeCount)
    (current : Channel n) :
    (touchAll empty (scopeLabels graph node)).marked current = true ↔
      current ∈ graph.scope node := by
  rw [touchAll_marked]
  simp only [empty, Bool.false_eq_true, false_or]
  rw [← scope_labels graph node]
  exact List.mem_toFinset.symm

theorem scope_touched (graph : DAG n) (node : Fin graph.nodeCount) :
    (touchAll empty (scopeLabels graph node)).touched.toFinset = graph.scope node := by
  have well := touchAll_wellFormed empty (scopeLabels graph node) empty_wellFormed
  apply Finset.ext
  intro current
  rw [List.mem_toFinset, ← well.2 current]
  exact scope_touch_exact graph node current

theorem scope_touched_length (graph : DAG n) (node : Fin graph.nodeCount) :
    (touchAll empty (scopeLabels graph node)).touched.length = (graph.scope node).card := by
  have well := touchAll_wellFormed empty (scopeLabels graph node) empty_wellFormed
  rw [← scope_touched graph node, List.toFinset_card_of_nodup well.1]

/-- The actual detector materializes at most one more candidate than the sparse
reset list; it does not scan all declared channels for each root. -/
theorem candidates_le_touched (graph : DAG n) (node : Fin graph.nodeCount) :
    (graph.unmarkedCandidates node).length ≤
      (touchAll empty (scopeLabels graph node)).touched.length + 1 := by
  rw [scope_touched_length]
  exact graph.unmarkedCandidates_length node

/-- The bounded candidate list from the production detector can use scope
marker reads instead of semantic finite-set membership. -/
theorem firstUnmarked_markers (graph : DAG n) (node : Fin graph.nodeCount) :
    (graph.unmarkedCandidates node).find?
      (fun current => !(touchAll empty (scopeLabels graph node)).marked current) =
      graph.firstUnmarked node := by
  have predicate :
      (fun current => !(touchAll empty (scopeLabels graph node)).marked current) =
        (fun current => decide (current ∉ graph.scope node)) := by
    funext current
    have exactScope := scope_touch_exact graph node current
    by_cases member : current ∈ graph.scope node
    · have marked := exactScope.mpr member
      simp [marked, member]
    · have off : (touchAll empty (scopeLabels graph node)).marked current = false :=
        Bool.eq_false_iff.mpr (by intro marked; exact member (exactScope.mp marked))
      simp [off, member]
  rw [predicate]
  rfl

/-- Sparse clearing uses exactly the recorded touched coordinates. -/
def clear (markers : Channel n → Bool) (coordinate : Channel n) : Channel n → Bool :=
  fun current => if current = coordinate then false else markers current

def reset (state : MarkState n) : MarkState n :=
  ⟨state.touched.foldl clear state.marked, []⟩

private theorem clear_fold (labels : List (Channel n)) (markers : Channel n → Bool)
    (current : Channel n) :
    labels.foldl clear markers current =
      if current ∈ labels then false else markers current := by
  induction labels generalizing markers with
  | nil => simp
  | cons coordinate rest ih =>
      rw [List.foldl_cons, ih]
      by_cases same : current = coordinate <;>
        by_cases member : current ∈ rest <;> simp [clear, same, member]

theorem reset_empty (state : MarkState n) (well : WellFormed state) : reset state = empty := by
  apply MarkState.ext
  · funext current
    change state.touched.foldl clear state.marked current = false
    rw [clear_fold]
    by_cases member : current ∈ state.touched
    · simp [member]
    · have off : state.marked current = false := Bool.eq_false_iff.mpr (by
        intro marked; exact member ((well.2 current).mp marked))
      simp [member, off]
  · rfl

/-- Physical scope-marker cells, distinct from the guard-counter region. -/
structure MarkersStored (heap : Array (Word width)) (offset : ℕ) (state : MarkState n) : Prop where
  valid : ∀ coordinate : Channel n, offset + coordinate.val < heap.size
  held : ∀ coordinate : Channel n, heap[offset + coordinate.val]'(valid coordinate) =
    word width (if state.marked coordinate then 1 else 0)

def readMark (heap : Array (Word width)) (address : ℕ) : Bool :=
  decide ((storedWord heap address).val ≠ 0)

theorem readMark_stored (width offset : ℕ) (heap : Array (Word width)) (state : MarkState n)
    (stored : MarkersStored heap offset state) (oneFits : 1 < 2 ^ width)
    (coordinate : Channel n) : readMark heap (offset + coordinate.val) = state.marked coordinate := by
  have lookup := (storedWord_eq heap _ (stored.valid coordinate)).trans (stored.held coordinate)
  unfold readMark
  rw [lookup]
  cases marked : state.marked coordinate <;>
    simp [word, marked, Nat.mod_eq_of_lt oneFits]

/-- Indexed touch operation: an already marked cell is left unchanged. -/
def touchHeap (width offset : ℕ) (heap : Array (Word width)) (coordinate : Channel n) :
    Array (Word width) :=
  if readMark heap (offset + coordinate.val) then heap else
    if valid : offset + coordinate.val < heap.size then
      heap.set (offset + coordinate.val) (word width 1) valid
    else heap

theorem touchHeap_stored (width offset : ℕ) (heap : Array (Word width))
    (state : MarkState n) (stored : MarkersStored heap offset state)
    (oneFits : 1 < 2 ^ width) (coordinate : Channel n) :
    MarkersStored (touchHeap width offset heap coordinate) offset (touch state coordinate) := by
  have read := readMark_stored width offset heap state stored oneFits coordinate
  by_cases marked : state.marked coordinate = true
  · simpa only [touchHeap, read, marked, ite_true, touch] using stored
  · have off : state.marked coordinate = false := Bool.eq_false_iff.mpr marked
    simp only [touchHeap, read, off, Bool.false_eq_true, ite_false,
      dite_eq_left (stored.valid coordinate), touch]
    refine ⟨fun other => by simpa using stored.valid other, ?_⟩
    intro other
    by_cases same : other = coordinate
    · subst other
      rw [Array.getElem_set_self (stored.valid coordinate)]
      simp
    · have different : offset + coordinate.val ≠ offset + other.val := by
        intro equal
        have values : coordinate.val = other.val := by omega
        exact same (Fin.ext values.symm)
      rw [Array.getElem_set_ne (stored.valid coordinate) (stored.valid other) different]
      rw [stored.held other]
      simp only [same, ite_false]

theorem touchHeap_outside (width offset : ℕ) (heap : Array (Word width))
    (coordinate : Channel n) (address : ℕ)
    (outside : ForestGuardRestore.Outside offset n address) :
    (touchHeap width offset heap coordinate)[address]? = heap[address]? := by
  have different : offset + coordinate.val ≠ address := by
    have bounded := coordinate.isLt
    unfold ForestGuardRestore.Outside at outside
    omega
  by_cases marked : readMark heap (offset + coordinate.val) = true
  · simp only [touchHeap, marked, ite_true]
  · have off : readMark heap (offset + coordinate.val) = false := Bool.eq_false_iff.mpr marked
    by_cases valid : offset + coordinate.val < heap.size
    · simpa only [touchHeap, off, Bool.false_eq_true, ite_false, dite_eq_left valid] using
        (Array.getElem?_set_ne (xs := heap) (v := word width 1) valid different)
    · simp only [touchHeap, off, Bool.false_eq_true, ite_false, dite_eq_right valid]

end Controller.Cost.ForestScopeMarkers
