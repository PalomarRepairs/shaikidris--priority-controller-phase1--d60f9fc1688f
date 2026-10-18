module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestCursorRoot

@[expose] public section

/-!
# Parent descriptors allocated by the source cursor scan

The builder maintains a constant-size allocation counter and a stack of parent
identifiers. Each child entry allocates one descriptor by consing its parent and
position onto a reverse accumulator. Leaf records retain the declared root
position. Routes are absent from the builder state; their decoding belongs to
the refinement relation. The scan specified here precedes physical heap and
code construction, whose allocation and store costs are separate.
-/
namespace Controller.Cost.ForestCursorDescriptors

open Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestCursorTraversal Controller.Cost.ForestCursorRoot

structure ParentEntry where
  identifier : ℕ
  parent : ℕ
  position : ℕ
  deriving DecidableEq, Repr

structure LeafEntry where
  root : ℕ
  owner : ℕ
  pointer : ℕ
  head : ℕ
  deriving DecidableEq, Repr

/-- The allocation counter avoids repeatedly computing accumulator lengths. -/
structure Builder where
  count : ℕ
  current : ℕ
  parents : List ℕ
  entries : List ParentEntry
  leaves : List LeafEntry
  deriving Repr

def initial : Builder := ⟨0, 0, [], [], []⟩

/-- A new root shares the descriptor store but starts from its own sentinel. -/
def beginRoot (state : Builder) : Builder :=
  { state with current := 0, parents := [] }

def step (root : ℕ) (state : Builder) (operation : CursorOp n) : Builder :=
  match operation with
  | .down _ position _ =>
      { state with
        count := state.count + 1
        current := state.count + 1
        parents := state.current :: state.parents
        entries := ⟨state.count + 1, state.current, position⟩ :: state.entries }
  | .up =>
      { state with current := state.parents.headD 0, parents := state.parents.tail }
  | .leaf owner _ head =>
      { state with leaves := ⟨root, owner, state.current, head.val⟩ :: state.leaves }
  | _ => state

def scan (root : ℕ) (state : Builder) (operations : List (CursorOp n)) : Builder :=
  operations.foldl (step root) state

theorem scan_append (root : ℕ) (state : Builder) (first second : List (CursorOp n)) :
    scan root state (first ++ second) = scan root (scan root state first) second := by
  simp only [scan, List.foldl_append]

/-- Source-balanced child pushes restore the previous pointer and parent stack.
The descriptor and leaf accumulators persist across the traversal. -/
theorem balanced_restore (root : ℕ) (operations : List (CursorOp n))
    (balanced : NavBalanced operations) (state : Builder) :
    (scan root state operations).current = state.current ∧
    (scan root state operations).parents = state.parents := by
  induction balanced generalizing state with
  | empty => exact ⟨rfl, rfl⟩
  | neutral operation neutral =>
      cases operation <;> simp_all [NavNeutral, scan, step]
  | @append first second firstBalanced secondBalanced firstIH secondIH =>
      rw [scan_append]
      obtain ⟨currentSecond, parentsSecond⟩ := secondIH (scan root state first)
      obtain ⟨currentFirst, parentsFirst⟩ := firstIH state
      exact ⟨currentSecond.trans currentFirst, parentsSecond.trans parentsFirst⟩
  | @child owner position child body balanced bodyIH =>
      change (scan root (step root state (.down owner position child)) (body ++ [.up])).current = _ ∧
        (scan root (step root state (.down owner position child)) (body ++ [.up])).parents = _
      rw [scan_append]
      obtain ⟨currentBody, parentsBody⟩ := bodyIH (step (n := n) root state (.down owner position child))
      simp only [scan, List.foldl_cons, List.foldl_nil, step]
      simp only [scan, step] at parentsBody
      rw [parentsBody]
      simp

theorem root_restore (graph : DAG n) (position : Fin graph.roots.length) (state : Builder) :
    (scan position.val (beginRoot state)
      (cursorOps graph (graph.roots.get position) [])).current = 0 ∧
    (scan position.val (beginRoot state)
      (cursorOps graph (graph.roots.get position) [])).parents = [] :=
  balanced_restore position.val _ (cursor_navigation_balanced graph _ []) (beginRoot state)

/-- Every stored parent precedes its child identifier; identifiers fit within
its single shared allocation counter, including inactive earlier root records. -/
structure Valid (state : Builder) : Prop where
  count : state.entries.length = state.count
  current : state.current ≤ state.count
  parents : ∀ parent ∈ state.parents, parent ≤ state.count
  entries : ∀ entry ∈ state.entries,
    0 < entry.identifier ∧ entry.parent < entry.identifier ∧ entry.identifier ≤ state.count
  leaves : ∀ leaf ∈ state.leaves, leaf.pointer ≤ state.count

theorem initial_valid : Valid initial := by
  refine ⟨rfl, by simp [initial], ?_, ?_, ?_⟩ <;> simp [initial]

theorem beginRoot_valid (state : Builder) (valid : Valid state) : Valid (beginRoot state) := by
  exact ⟨valid.count, Nat.zero_le _, by simp [beginRoot], valid.entries, valid.leaves⟩

/-- Allocation performs a single cons, and its parent is strictly earlier. -/
theorem step_valid (root : ℕ) (state : Builder) (valid : Valid state)
    (operation : CursorOp n) : Valid (step root state operation) := by
  cases operation with
  | down owner position child =>
      refine ⟨by simpa [step] using congrArg Nat.succ valid.count, by simp [step], ?_, ?_, ?_⟩
      · intro parent present
        rcases List.mem_cons.mp present with equal | earlier
        · subst parent; exact Nat.le_trans valid.current (Nat.le_succ _)
        · exact Nat.le_trans (valid.parents parent earlier) (Nat.le_succ _)
      · intro entry present
        rcases List.mem_cons.mp present with equal | earlier
        · subst entry; exact ⟨by simp, by simpa using Nat.lt_succ_of_le valid.current, by simp [step]⟩
        · obtain ⟨positive, parentEarlier, bounded⟩ := valid.entries entry earlier
          exact ⟨positive, parentEarlier, Nat.le_trans bounded (Nat.le_succ _)⟩
      · intro leaf present
        exact Nat.le_trans (valid.leaves leaf present) (Nat.le_succ _)
  | up =>
      refine ⟨valid.count, ?_, ?_, valid.entries, valid.leaves⟩
      · cases equal : state.parents with
        | nil => simp [step, equal]
        | cons parent rest =>
            simpa [step, equal] using valid.parents parent (by rw [equal]; exact List.mem_cons_self)
      · intro parent present
        exact valid.parents parent (List.mem_of_mem_tail present)
  | leaf owner route head =>
      refine ⟨valid.count, valid.current, valid.parents, valid.entries, ?_⟩
      intro leaf present
      rcases List.mem_cons.mp present with equal | earlier
      · subst leaf; exact valid.current
      · exact valid.leaves leaf earlier
  | node owner => exact valid
  | enter owner position channel => exact valid
  | leave owner position channel => exact valid

theorem scan_valid (root : ℕ) (state : Builder) (valid : Valid state)
    (operations : List (CursorOp n)) : Valid (scan root state operations) := by
  induction operations generalizing state with
  | nil => exact valid
  | cons operation rest ih => exact ih _ (step_valid root state valid operation)

/-- The allocation counter supplies fresh identifiers even when two source
child positions have the same terminal endpoint. -/
theorem step_identifiers (root : ℕ) (state : Builder) (valid : Valid state)
    (unique : (state.entries.map ParentEntry.identifier).Nodup)
    (operation : CursorOp n) :
    ((step root state operation).entries.map ParentEntry.identifier).Nodup := by
  cases operation with
  | down owner position child =>
      change ((state.count + 1) :: state.entries.map ParentEntry.identifier).Nodup
      apply List.nodup_cons.mpr
      refine ⟨?_, unique⟩
      intro present
      obtain ⟨entry, member, equal⟩ := List.mem_map.mp present
      have bound := (valid.entries entry member).2.2
      omega
  | node owner => exact unique
  | up => exact unique
  | enter owner position channel => exact unique
  | leave owner position channel => exact unique
  | leaf owner route head => exact unique

theorem scan_identifiers (root : ℕ) (state : Builder) (valid : Valid state)
    (unique : (state.entries.map ParentEntry.identifier).Nodup)
    (operations : List (CursorOp n)) :
    ((scan root state operations).entries.map ParentEntry.identifier).Nodup := by
  induction operations generalizing state with
  | nil => exact unique
  | cons operation rest ih =>
      exact ih _ (step_valid root state valid operation)
        (step_identifiers root state valid unique operation)

/-- A route decoder is a refinement witness. It is absent from the executable
builder state, which stores only natural parent and child-position words. -/
structure Decodes (state : Builder) (route : ℕ → LeafRoute) : Prop where
  sentinel : route 0 = []
  entries : ∀ entry ∈ state.entries,
    route entry.identifier = entry.position :: route entry.parent

def extendRoute (route : ℕ → LeafRoute) (identifier parent position : ℕ) : ℕ → LeafRoute :=
  fun pointer => if pointer = identifier then position :: route parent else route pointer

/-- Allocating a descriptor extends decoding while preserving every old
identifier, since both the old identifier and its parent precede the new one. -/
theorem down_decodes {n : ℕ} (root : ℕ) (state : Builder) (valid : Valid state)
    (route : ℕ → LeafRoute) (decoded : Decodes state route)
    (owner position child : ℕ) :
    Decodes (step (n := n) root state (.down owner position child))
      (extendRoute route (state.count + 1) state.current position) := by
  refine ⟨?_, ?_⟩
  · simp [extendRoute, decoded.sentinel]
  · intro entry present
    rcases List.mem_cons.mp present with equal | old
    · subst entry
      have earlier : state.current ≠ state.count + 1 := by have h := valid.current; omega
      simp [extendRoute, earlier]
    · obtain ⟨positive, parentEarlier, bounded⟩ := valid.entries entry old
      have different : entry.identifier ≠ state.count + 1 := by omega
      have parentDifferent : entry.parent ≠ state.count + 1 := by omega
      simpa [extendRoute, different, parentDifferent] using decoded.entries entry old

def routeStep (state : Builder) (route : ℕ → LeafRoute) (operation : CursorOp n) :
    ℕ → LeafRoute :=
  match operation with
  | .down _ position _ => extendRoute route (state.count + 1) state.current position
  | _ => route

/-- Ghost decoding follows the identical allocation order of the data scan. -/
def routeScan (root : ℕ) (state : Builder) (route : ℕ → LeafRoute) :
    List (CursorOp n) → ℕ → LeafRoute
  | [] => route
  | operation :: rest =>
      routeScan root (step root state operation) (routeStep state route operation) rest

theorem step_decodes (root : ℕ) (state : Builder) (valid : Valid state)
    (route : ℕ → LeafRoute) (decoded : Decodes state route) (operation : CursorOp n) :
    Decodes (step root state operation) (routeStep state route operation) := by
  cases operation with
  | down owner position child => exact down_decodes (n := n) root state valid route decoded owner position child
  | node owner => exact decoded
  | up => exact ⟨decoded.sentinel, decoded.entries⟩
  | enter owner position channel => exact decoded
  | leave owner position channel => exact decoded
  | leaf owner leafRoute head => exact ⟨decoded.sentinel, decoded.entries⟩

theorem scan_decodes (root : ℕ) (state : Builder) (valid : Valid state)
    (route : ℕ → LeafRoute) (decoded : Decodes state route) (operations : List (CursorOp n)) :
    Decodes (scan root state operations) (routeScan root state route operations) := by
  induction operations generalizing state route with
  | nil => exact decoded
  | cons operation rest ih =>
      exact ih _ (step_valid root state valid operation) _
        (step_decodes root state valid route decoded operation)

/-- New allocations never change decoding for an identifier already allocated
before the current operation. -/
theorem routeStep_preserves (state : Builder) (route : ℕ → LeafRoute)
    (operation : CursorOp n) (pointer : ℕ) (bounded : pointer ≤ state.count) :
    routeStep state route operation pointer = route pointer := by
  cases operation <;> simp only [routeStep]
  rename_i owner position child
  have different : pointer ≠ state.count + 1 := by omega
  simp [extendRoute, different]

def isDown : CursorOp n → ℕ
  | .down _ _ _ => 1
  | _ => 0

def isLeaf : CursorOp n → ℕ
  | .leaf _ _ _ => 1
  | _ => 0

/-- These are counts of the actual scanned source operations. -/
def allocations (operations : List (CursorOp n)) : ℕ := (operations.map isDown).sum
def callbacks (operations : List (CursorOp n)) : ℕ := (operations.map isLeaf).sum

theorem step_count (root : ℕ) (state : Builder) (operation : CursorOp n) :
    (step root state operation).count = state.count + isDown operation := by
  cases operation <;> simp [step, isDown]

theorem routeScan_preserves (root : ℕ) (state : Builder) (route : ℕ → LeafRoute)
    (operations : List (CursorOp n)) (pointer : ℕ) (bounded : pointer ≤ state.count) :
    routeScan root state route operations pointer = route pointer := by
  induction operations generalizing state route with
  | nil => rfl
  | cons operation rest ih =>
      change routeScan root (step root state operation) (routeStep state route operation) rest pointer = _
      have nextBound : pointer ≤ (step root state operation).count := by
        rw [step_count]
        omega
      rw [ih _ _ nextBound]
      exact routeStep_preserves state route operation pointer bounded

theorem step_leaves (root : ℕ) (state : Builder) (operation : CursorOp n) :
    (step root state operation).leaves.length = state.leaves.length + isLeaf operation := by
  cases operation <;> simp [step, isLeaf, Nat.add_comm]

theorem scan_count (root : ℕ) (state : Builder) (operations : List (CursorOp n)) :
    (scan root state operations).count = state.count + allocations operations := by
  induction operations generalizing state with
  | nil => simp [scan, allocations]
  | cons operation rest ih =>
      change (scan root (step root state operation) rest).count = _
      rw [ih, step_count]
      simp [allocations, Nat.add_assoc]

theorem scan_leaves (root : ℕ) (state : Builder) (operations : List (CursorOp n)) :
    (scan root state operations).leaves.length = state.leaves.length + callbacks operations := by
  induction operations generalizing state with
  | nil => simp [scan, callbacks]
  | cons operation rest ih =>
      change (scan root (step root state operation) rest).leaves.length = _
      rw [ih, step_leaves]
      simp [callbacks, Nat.add_assoc]

/-- The source scan allocates exactly one descriptor per child entry. It does
not construct or search the positional route carried by a refinement witness. -/
theorem source_root_count (graph : DAG n) (position : Fin graph.roots.length)
    (state : Builder) :
    (scan position.val (beginRoot state)
      (cursorOps graph (graph.roots.get position) [])).count =
      state.count + allocations (cursorOps graph (graph.roots.get position) []) :=
  scan_count position.val (beginRoot state) _

def scanRoot (graph : DAG n) (state : Builder) (position : Fin graph.roots.length) : Builder :=
  scan position.val (beginRoot state) (cursorOps graph (graph.roots.get position) [])

def scanRoots (graph : DAG n) (state : Builder) (positions : List (Fin graph.roots.length)) : Builder :=
  positions.foldl (scanRoot graph) state

/-- All roots share one descriptor allocation counter and accumulator; only
navigation is reset to the root sentinel. -/
def buildRoots (graph : DAG n) : Builder := scanRoots graph initial (List.finRange graph.roots.length)

theorem scanRoot_valid (graph : DAG n) (state : Builder) (valid : Valid state)
    (position : Fin graph.roots.length) : Valid (scanRoot graph state position) :=
  scan_valid position.val (beginRoot state) (beginRoot_valid state valid) _

theorem scanRoots_valid (graph : DAG n) (state : Builder) (valid : Valid state)
    (positions : List (Fin graph.roots.length)) : Valid (scanRoots graph state positions) := by
  induction positions generalizing state with
  | nil => exact valid
  | cons position rest ih => exact ih _ (scanRoot_valid graph state valid position)

theorem buildRoots_valid (graph : DAG n) : Valid (buildRoots graph) :=
  scanRoots_valid graph initial initial_valid _

theorem scanRoots_count (graph : DAG n) (state : Builder)
    (positions : List (Fin graph.roots.length)) :
    (scanRoots graph state positions).count = state.count +
      (positions.map fun position => allocations (cursorOps graph (graph.roots.get position) [])).sum := by
  induction positions generalizing state with
  | nil => simp [scanRoots]
  | cons position rest ih =>
      change (scanRoots graph (scanRoot graph state position) rest).count = _
      rw [ih]
      change (scan position.val (beginRoot state) _).count + _ = _
      rw [source_root_count]
      simp [Nat.add_assoc]

/-- This is an exact allocation count for the shared builder, before its
finite heap cells and code words are materialized. -/
theorem buildRoots_count (graph : DAG n) :
    (buildRoots graph).entries.length =
      ((List.finRange graph.roots.length).map fun position =>
        allocations (cursorOps graph (graph.roots.get position) [])).sum := by
  rw [(buildRoots_valid graph).count]
  simpa [buildRoots, initial] using scanRoots_count graph initial (List.finRange graph.roots.length)

end Controller.Cost.ForestCursorDescriptors
