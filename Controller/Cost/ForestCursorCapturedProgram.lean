module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestCursorDescriptorSource

@[expose] public section

/-!
# Leaf pointers emitted from the maintained allocation cursor

The compiler emits each leaf block with the builder's current descriptor
identifier. It does not search a route dictionary. A proof-only occurrence
index relates the resulting instruction list to the checked cursor program.
Physical descriptor materialization and construction-operation costs remain
separate contracts.
-/
namespace Controller.Cost.ForestCursorCapturedProgram

open Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestCursorProgram Controller.Cost.ForestCursorTraversal
open Controller.Cost.ForestCursorDescriptors Controller.Cost.ForestCursorDescriptorSource
open Controller.Cost.ForestCursorRoot Controller.Cost.ForestCounter Controller.Cost.ForestCursorExecution
open Controller.Cost.ForestGuardSchedule Controller.Cost.GateProgram

/-- This sentinel index is used only by non-leaf branches, which ignore it. -/
def zeroIndex (graph : DAG n) : OccurrenceIndex graph := ⟨fun _ => 0, rfl⟩

def capturedCode (graph : DAG n) (records : GraphRecords width heap graph)
    (layout : SelectorLayout n) (state : Builder)
    (base b : ℕ) (target : Channel n) (operation : CursorOp n) : ForestCounter.Code width :=
  match operation with
  | .leaf owner _ head =>
      recordReadCode width (records.recordBase + 2 * owner + 1) ++
        leafCode width (base + 2) layout b target head state.current
  | _ => operationCode graph records layout (zeroIndex graph) base b target operation

/-- The leaf's compiled immediate is exactly the maintained current ID. -/
theorem captured_leaf (graph : DAG n) (records : GraphRecords width heap graph)
    (layout : SelectorLayout n) (state : Builder) (base b owner : ℕ)
    (target head : Channel n) (route : LeafRoute) :
    capturedCode graph records layout state base b target (.leaf owner route head) =
      recordReadCode width (records.recordBase + 2 * owner + 1) ++
        leafCode width (base + 2) layout b target head state.current := rfl

/-- Only leaf immediates can depend on an occurrence-index function. -/
theorem capturedCode_eq (graph : DAG n) (records : GraphRecords width heap graph)
    (layout : SelectorLayout n) (state : Builder) (index : OccurrenceIndex graph)
    (base b : ℕ) (target : Channel n) (operation : CursorOp n)
    (captured : ∀ owner route head, operation = .leaf owner route head →
      index.pointer route = state.current) :
    capturedCode graph records layout state base b target operation =
      operationCode graph records layout index base b target operation := by
  cases operation with
  | leaf owner route head => simp only [capturedCode, operationCode, captured owner route head rfl]
  | node owner => rfl
  | enter owner position channel => rfl
  | leave owner position channel => rfl
  | down owner position child => rfl
  | up => rfl

/-- The compiler traverses operations once while carrying its shared builder. -/
def emitCaptured (graph : DAG n) (records : GraphRecords width heap graph)
    (layout : SelectorLayout n) (root b : ℕ) (target : Channel n) :
    Builder → ℕ → List (CursorOp n) → ForestCounter.Code width
  | _, _, [] => []
  | state, base, operation :: rest =>
      let block := capturedCode graph records layout state base b target operation
      block ++ emitCaptured graph records layout root b target
        (ForestCursorDescriptors.step (n := n) root state operation) (base + block.length) rest

/-- The proof relation mentions routes; the compiler never reads this relation. -/
def Captured (root : ℕ) (index : OccurrenceIndex graph) :
    Builder → List (CursorOp n) → Prop
  | _, [] => True
  | state, operation :: rest =>
      (∀ owner route head, operation = .leaf owner route head →
        index.pointer route = state.current) ∧
      Captured root index (ForestCursorDescriptors.step (n := n) root state operation) rest

/-- Every emitted block is the checked source operation block with its captured
pointer immediate. This transfers complete program coverage, not a timing claim. -/
theorem emitCaptured_eq (graph : DAG n) (records : GraphRecords width heap graph)
    (layout : SelectorLayout n) (root b : ℕ) (target : Channel n)
    (state : Builder) (index : OccurrenceIndex graph) (base : ℕ)
    (operations : List (CursorOp n)) (captured : Captured root index state operations) :
    emitCaptured graph records layout root b target state base operations =
      emitOperations graph records layout index b target base operations := by
  induction operations generalizing state base with
  | nil => rfl
  | cons operation rest ih =>
      change capturedCode graph records layout state base b target operation ++
        emitCaptured graph records layout root b target (ForestCursorDescriptors.step (n := n) root state operation)
          (base + (capturedCode graph records layout state base b target operation).length) rest = _
      have blockEq := capturedCode_eq graph records layout state index base b target operation captured.1
      rw [blockEq]
      rw [ih _ _ captured.2]
      rfl

/-- Every callback record is either retained or belongs to this root scan. -/
theorem step_leaf_root (root : ℕ) (state : Builder) (operation : CursorOp n)
    (leaf : LeafEntry) (present : leaf ∈ (ForestCursorDescriptors.step (n := n) root state operation).leaves) :
    leaf ∈ state.leaves ∨ leaf.root = root := by
  cases operation with
  | leaf owner route head =>
      change leaf ∈ (⟨root, owner, state.current, head.val⟩ : LeafEntry) :: state.leaves at present
      rcases List.mem_cons.mp present with same | old
      · subst leaf; exact Or.inr rfl
      · exact Or.inl old
  | node owner => exact Or.inl present
  | down owner position child => exact Or.inl present
  | up => exact Or.inl present
  | enter owner position channel => exact Or.inl present
  | leave owner position channel => exact Or.inl present

theorem scan_leaf_root (root : ℕ) (state : Builder) (operations : List (CursorOp n))
    (leaf : LeafEntry) (present : leaf ∈ (scan root state operations).leaves) :
    leaf ∈ state.leaves ∨ leaf.root = root := by
  induction operations generalizing state with
  | nil => exact Or.inl present
  | cons operation rest ih =>
      change leaf ∈ (scan root (ForestCursorDescriptors.step (n := n) root state operation) rest).leaves at present
      rcases ih _ present with old | same
      · exact step_leaf_root root state operation leaf old
      · exact Or.inr same

/-- The actual all-root prefix confines every accumulated record's root ID to
that prefix. This excludes arbitrary previously populated builder states. -/
theorem scanRoots_leaf_root (graph : DAG n) (state : Builder)
    (positions : List (Fin graph.roots.length)) (leaf : LeafEntry)
    (present : leaf ∈ (scanRoots graph state positions).leaves) :
    leaf ∈ state.leaves ∨ leaf.root ∈ positions.map Fin.val := by
  induction positions generalizing state with
  | nil => exact Or.inl present
  | cons position rest ih =>
      change leaf ∈ (scanRoots graph (scanRoot graph state position) rest).leaves at present
      rcases ih _ present with old | previous
      · rcases scan_leaf_root position.val (beginRoot state) _ leaf old with original | same
        · exact Or.inl original
        · exact Or.inr (by simp [same])
      · exact Or.inr (List.mem_cons_of_mem _ previous)

/-- For a declared root not yet scanned, no record accumulated from the actual
prefix can masquerade as a record from the new root. -/
theorem fresh_root_records (graph : DAG n) (positions : List (Fin graph.roots.length))
    (position : Fin graph.roots.length) (fresh : position ∉ positions)
    (leaf : LeafEntry) (present : leaf ∈ (scanRoots graph initial positions).leaves) :
    leaf.root ≠ position.val := by
  intro same
  rcases scanRoots_leaf_root graph initial positions leaf present with empty | previous
  · simpa [initial] using empty
  · rw [same] at previous
    obtain ⟨old, oldPresent, equal⟩ := List.mem_map.mp previous
    exact fresh (by have samePosition : old = position := Fin.ext equal; simpa [samePosition] using oldPresent)

/-- Positional leaf paths are ghost witnesses for source callback uniqueness. -/
def leafPaths (graph : DAG n) (node : Fin graph.nodeCount) (routePrefix : LeafRoute) : List LeafRoute :=
  match graph.node node with
  | .input _ => [routePrefix]
  | .disj refs => (List.ofFn fun position : Fin refs.length =>
      leafPaths graph (graph.childIndex node (refs.get position)) (position.val :: routePrefix)).flatten
  | .guard child _ => leafPaths graph (graph.childIndex node child) (0 :: routePrefix)
  | _ => []
termination_by node.val
decreasing_by all_goals exact graph.childIndex_lt _ _

theorem leafPaths_suffix (graph : DAG n) :
    ∀ (node : Fin graph.nodeCount) (routePrefix route : LeafRoute),
      route ∈ leafPaths graph node routePrefix → routePrefix <:+ route := by
  have claim : ∀ rank : ℕ, ∀ node : Fin graph.nodeCount, node.val = rank →
      ∀ routePrefix route, route ∈ leafPaths graph node routePrefix → routePrefix <:+ route := by
    intro rank
    induction rank using Nat.strong_induction_on with
    | h rank ih =>
      intro node equal routePrefix route present
      rw [leafPaths.eq_def] at present
      cases kind : graph.node node with
      | zero => simp [kind] at present
      | liveAnd left right => simp [kind] at present
      | input head =>
          simp only [kind, List.mem_singleton] at present
          subst route
          exact List.suffix_refl routePrefix
      | disj refs =>
          simp only [kind] at present
          obtain ⟨block, member, contained⟩ := List.mem_flatten.mp present
          obtain ⟨position, same⟩ := List.mem_ofFn.mp member
          subst block
          have held := ih (refs.get position).val
            (by have earlier := graph.childIndex_lt node (refs.get position); omega)
            (graph.childIndex node (refs.get position)) rfl _ route contained
          exact (List.suffix_cons _ routePrefix).trans held
      | guard child labels =>
          simp only [kind] at present
          have held := ih child.val (by have earlier := graph.childIndex_lt node child; omega)
            (graph.childIndex node child) rfl _ route present
          exact (List.suffix_cons _ routePrefix).trans held
  intro node routePrefix route present
  exact claim node.val node rfl routePrefix route present

/-- Different child positions produce disjoint path sets, including repeated
references to the same terminal node. -/
theorem leafPaths_children_disjoint (graph : DAG n) (node : Fin graph.nodeCount)
    (refs : List (Fin node.val)) (routePrefix : LeafRoute)
    (first second : Fin refs.length) (different : first ≠ second) :
    List.Disjoint (leafPaths graph (graph.childIndex node (refs.get first)) (first.val :: routePrefix))
      (leafPaths graph (graph.childIndex node (refs.get second)) (second.val :: routePrefix)) := by
  apply List.disjoint_left.mpr
  intro route firstPresent secondPresent
  have firstSuffix := leafPaths_suffix graph _ _ route firstPresent
  have secondSuffix := leafPaths_suffix graph _ _ route secondPresent
  have equal : first.val :: routePrefix = second.val :: routePrefix :=
    (List.suffix_of_suffix_length_le firstSuffix secondSuffix (by simp)).eq_of_length (by simp)
  exact different (Fin.ext (List.cons.inj equal).1)

/-- The source has at most one callback for each positional route. This statement
concerns paths, not internal-node uniqueness or a runtime path dictionary. -/
theorem leafPaths_nodup (graph : DAG n) :
    ∀ (node : Fin graph.nodeCount) (routePrefix : LeafRoute), (leafPaths graph node routePrefix).Nodup := by
  have claim : ∀ rank : ℕ, ∀ node : Fin graph.nodeCount, node.val = rank →
      ∀ routePrefix, (leafPaths graph node routePrefix).Nodup := by
    intro rank
    induction rank using Nat.strong_induction_on with
    | h rank ih =>
      intro node equal routePrefix
      rw [leafPaths.eq_def]
      cases kind : graph.node node with
      | zero => simp [kind]
      | liveAnd left right => simp [kind]
      | input head => simp [kind]
      | guard child labels =>
          simp only [kind]
          exact ih child.val (by have earlier := graph.childIndex_lt node child; omega)
            (graph.childIndex node child) rfl _
      | disj refs =>
          simp only [kind]
          apply List.nodup_flatten.mpr
          constructor
          · intro block member
            obtain ⟨position, same⟩ := List.mem_ofFn.mp member
            subst block
            exact ih (refs.get position).val
              (by have earlier := graph.childIndex_lt node (refs.get position); omega)
              (graph.childIndex node (refs.get position)) rfl _
          · apply List.pairwise_ofFn.mpr
            intro first second before
            exact leafPaths_children_disjoint graph node refs routePrefix first second (ne_of_lt before)
  intro node routePrefix
  exact claim node.val node rfl routePrefix

def operationRoute : CursorOp n → Option LeafRoute
  | .leaf _ route _ => some route
  | _ => none

def callbackRoutes (operations : List (CursorOp n)) : List LeafRoute :=
  operations.filterMap operationRoute

/-- The source callback projection is exactly the ghost positional path list. -/
theorem cursor_callbackRoutes (graph : DAG n) :
    ∀ (node : Fin graph.nodeCount) (routePrefix : LeafRoute),
      callbackRoutes (cursorOps graph node routePrefix) = leafPaths graph node routePrefix := by
  have claim : ∀ rank : ℕ, ∀ node : Fin graph.nodeCount, node.val = rank →
      ∀ routePrefix, callbackRoutes (cursorOps graph node routePrefix) = leafPaths graph node routePrefix := by
    intro rank
    induction rank using Nat.strong_induction_on with
    | h rank ih =>
      intro node equal routePrefix
      rw [cursorOps.eq_def, leafPaths.eq_def]
      cases kind : graph.node node with
      | zero => simp [kind, callbackRoutes, operationRoute]
      | liveAnd left right => simp [kind, callbackRoutes, operationRoute]
      | input head => simp only [kind, callbackRoutes, List.filterMap_cons, operationRoute, List.filterMap_nil]
      | guard child labels =>
          simp only [kind, callbackRoutes, List.filterMap_cons, operationRoute,
            List.filterMap_append, List.filterMap_map, Function.comp_def,
            List.filterMap_none, List.filterMap_nil, List.nil_append, List.append_nil]
          exact ih child.val (by have earlier := graph.childIndex_lt node child; omega)
            (graph.childIndex node child) rfl _
      | disj refs =>
          simp only [kind, callbackRoutes, List.filterMap_cons, operationRoute,
            List.filterMap_flatMap, List.ofFn_eq_map, ← List.flatMap_def]
          apply congrArg (fun body => (List.finRange refs.length).flatMap body)
          funext position
          simp only [List.filterMap_append, List.filterMap_cons, operationRoute,
            List.filterMap_nil, List.nil_append, List.append_nil]
          exact ih (refs.get position).val
            (by have earlier := graph.childIndex_lt node (refs.get position); omega)
            (graph.childIndex node (refs.get position)) rfl _
  intro node routePrefix
  exact claim node.val node rfl routePrefix

theorem cursor_callbackRoutes_nodup (graph : DAG n) (node : Fin graph.nodeCount)
    (routePrefix : LeafRoute) : (callbackRoutes (cursorOps graph node routePrefix)).Nodup := by
  rw [cursor_callbackRoutes]
  exact leafPaths_nodup graph node routePrefix

/-- This chronological capture list is ghost refinement data. The executable
compiler stores only current IDs as instruction immediates. -/
def capturePairs (root : ℕ) (state : Builder) : List (CursorOp n) → List (LeafRoute × ℕ)
  | [] => []
  | operation :: rest =>
      let tail := capturePairs root (ForestCursorDescriptors.step (n := n) root state operation) rest
      match operation with
      | .leaf _ route _ => (route, state.current) :: tail
      | _ => tail

theorem capturePairs_routes (root : ℕ) (state : Builder) (operations : List (CursorOp n)) :
    (capturePairs root state operations).map Prod.fst = callbackRoutes operations := by
  induction operations generalizing state with
  | nil => rfl
  | cons operation rest ih =>
      cases operation <;> simp only [capturePairs, callbackRoutes, List.filterMap_cons,
        operationRoute, List.map_cons, Prod.fst, ih]

/-- The source capture relation is functional on routes even if multiple
occurrences refer to the same input node. -/
theorem source_capturePairs_unique (graph : DAG n) (position : Fin graph.roots.length)
    (state : Builder) :
    ((capturePairs position.val (beginRoot state)
      (cursorOps graph (graph.roots.get position) [])).map Prod.fst).Nodup := by
  rw [capturePairs_routes]
  exact cursor_callbackRoutes_nodup graph _ []

/-- A proof-only index chooses IDs from the chronological new-record capture. -/
noncomputable def pairIndex (graph : DAG n) (pairs : List (LeafRoute × ℕ)) :
    OccurrenceIndex graph := by
  classical
  exact {
    pointer := fun route => if route = [] then 0 else
      if supported : ∃ pointer, (route, pointer) ∈ pairs then Classical.choose supported else 0
    empty := by simp }

theorem pairIndex_matches (graph : DAG n) (pairs : List (LeafRoute × ℕ))
    (unique : (pairs.map Prod.fst).Nodup)
    (empty : ∀ pointer, ([], pointer) ∈ pairs → pointer = 0)
    (route : LeafRoute) (pointer : ℕ) (present : (route, pointer) ∈ pairs) :
    (pairIndex graph pairs).pointer route = pointer := by
  classical
  by_cases zero : route = []
  · subst route
    simp only [pairIndex, ite_eq_left rfl]
    exact (empty pointer present).symm
  · have supported : ∃ other, (route, other) ∈ pairs := ⟨pointer, present⟩
    have chosen := Classical.choose_spec supported
    have equal : (route, Classical.choose supported) = (route, pointer) :=
      List.inj_on_of_nodup_map unique chosen present rfl
    simpa only [pairIndex, ite_eq_right zero, dite_eq_left supported] using congrArg Prod.snd equal

/-- The code witness is derived from the actual captured immediates. No route
lookup takes place in emitted instructions or in the running cursor. -/
theorem captured_of_pairs (root : ℕ) (state : Builder) (index : OccurrenceIndex graph)
    (operations : List (CursorOp n))
    (agrees : ∀ route pointer, (route, pointer) ∈ capturePairs root state operations →
      index.pointer route = pointer) : Captured root index state operations := by
  induction operations generalizing state with
  | nil => trivial
  | cons operation rest ih =>
      constructor
      · intro owner route head equal
        subst operation
        exact agrees route state.current (by simp [capturePairs])
      · apply ih
        intro route pointer present
        apply agrees route pointer
        cases operation with
        | leaf owner leafRoute head => exact List.mem_cons_of_mem _ present
        | node owner => exact present
        | down owner position child => exact present
        | up => exact present
        | enter owner position channel => exact present
        | leave owner position channel => exact present

theorem leafPaths_empty_root (graph : DAG n) (node : Fin graph.nodeCount)
    (present : [] ∈ leafPaths graph node []) : ∃ head, graph.node node = .input head := by
  rw [leafPaths.eq_def] at present
  cases kind : graph.node node with
  | zero => simp [kind] at present
  | liveAnd left right => simp [kind] at present
  | input head => exact ⟨head, rfl⟩
  | guard child labels =>
      simp only [kind] at present
      have impossible := (leafPaths_suffix graph (graph.childIndex node child) [0] [] present).length_le
      simp at impossible
  | disj refs =>
      simp only [kind] at present
      obtain ⟨block, member, contains⟩ := List.mem_flatten.mp present
      obtain ⟨position, same⟩ := List.mem_ofFn.mp member
      subst block
      have impossible := (leafPaths_suffix graph (graph.childIndex node (refs.get position))
        [position.val] [] contains).length_le
      simp at impossible

/-- Empty routes arise only at an input root, before any child descriptor has
been allocated; the actual maintained pointer is therefore sentinel zero. -/
theorem source_capturePairs_empty (graph : DAG n) (position : Fin graph.roots.length)
    (state : Builder) (pointer : ℕ)
    (present : ([], pointer) ∈ capturePairs position.val (beginRoot state)
      (cursorOps graph (graph.roots.get position) [])) : pointer = 0 := by
  have routePresent : [] ∈ callbackRoutes (cursorOps graph (graph.roots.get position) []) := by
    rw [← capturePairs_routes position.val (beginRoot state)]
    exact List.mem_map.mpr ⟨([], pointer), present, rfl⟩
  rw [cursor_callbackRoutes] at routePresent
  obtain ⟨head, kind⟩ := leafPaths_empty_root graph _ routePresent
  rw [cursorOps.eq_def, kind] at present
  have equal : (([] : LeafRoute), pointer) = ([], 0) := by simpa [capturePairs, ForestCursorDescriptors.step, beginRoot] using present
  exact congrArg Prod.snd equal

/-- The generic compiler relation follows from new-record uniqueness and the
root sentinel invariant, rather than arbitrary retained leaf records. -/
theorem source_captured (graph : DAG n) (position : Fin graph.roots.length)
    (state : Builder) :
    Captured position.val
      (pairIndex graph (capturePairs position.val (beginRoot state)
        (cursorOps graph (graph.roots.get position) [])))
      (beginRoot state) (cursorOps graph (graph.roots.get position) []) := by
  apply captured_of_pairs
  exact pairIndex_matches graph _ (source_capturePairs_unique graph position state)
    (source_capturePairs_empty graph position state)

theorem capturePairs_callback (root : ℕ) (state : Builder) (operations : List (CursorOp n))
    (owner : ℕ) (route : LeafRoute) (head : Channel n)
    (present : CursorOp.leaf owner route head ∈ operations) :
    ∃ pointer, (route, pointer) ∈ capturePairs root state operations := by
  induction operations generalizing state with
  | nil => simp at present
  | cons operation rest ih =>
      rcases List.mem_cons.mp present with equal | later
      · subst operation
        exact ⟨state.current, List.mem_cons_self⟩
      · obtain ⟨pointer, member⟩ := ih (ForestCursorDescriptors.step (n := n) root state operation) later
        refine ⟨pointer, ?_⟩
        cases operation with
        | leaf oldOwner oldRoute oldHead => exact List.mem_cons_of_mem _ member
        | node owner => exact member
        | down owner position child => exact member
        | up => exact member
        | enter owner position channel => exact member
        | leave owner position channel => exact member

theorem capturePairs_decoded (root : ℕ) (state : Builder) (valid : Valid state)
    (decode : ℕ → LeafRoute) (operations : List (CursorOp n))
    (safe : RouteSafe root state decode operations) (route : LeafRoute) (pointer : ℕ)
    (present : (route, pointer) ∈ capturePairs root state operations) :
    routeScan root state decode operations pointer = route ∧
      pointer ≤ (scan root state operations).count := by
  induction operations generalizing state decode with
  | nil => simp [capturePairs] at present
  | cons operation rest ih =>
      have recurse := ih (ForestCursorDescriptors.step (n := n) root state operation) (step_valid root state valid operation)
        (routeStep state decode operation) safe.2
      cases operation with
      | node owner => exact recurse present
      | down owner position child => exact recurse present
      | up => exact recurse present
      | enter owner position channel => exact recurse present
      | leave owner position channel => exact recurse present
      | leaf owner leafRoute head =>
          rcases List.mem_cons.mp present with equal | later
          · have routeEq := (Prod.mk.inj equal).1
            have pointerEq := (Prod.mk.inj equal).2
            subst route
            subst pointer
            constructor
            · change routeScan root (ForestCursorDescriptors.step (n := n) root state (.leaf owner leafRoute head)) decode rest state.current = _
              have held : state.current ≤ (ForestCursorDescriptors.step (n := n) root state (.leaf owner leafRoute head)).count := valid.current
              rw [routeScan_preserves root _ _ rest state.current held]
              exact safe.1
            · change state.current ≤ (scan root (ForestCursorDescriptors.step (n := n) root state (.leaf owner leafRoute head)) rest).count
              rw [scan_count]
              change state.current ≤ state.count + allocations rest
              exact Nat.le_trans valid.current (Nat.le_add_right _ _)
          · exact recurse later

/-- The direct captured compiler obtains a represented RootIndex from actual
source callbacks and descriptor decoding, with no route dictionary premise. -/
theorem pair_root_index (graph : DAG n) (position : Fin graph.roots.length)
    (state : Builder) (valid : Valid state) (decode : ℕ → LeafRoute) (sentinel : decode 0 = [])
    (routes : RouteDescriptors width heap)
    (count : routes.count = (scanRoot graph state position).count)
    (represented : ∀ pointer ≤ (scanRoot graph state position).count,
      routes.route pointer = routeScan position.val (beginRoot state) decode
        (cursorOps graph (graph.roots.get position) []) pointer)
    (fits : (scanRoot graph state position).count < 2 ^ width) :
    RootIndex graph (graph.roots.get position) routes
      (pairIndex graph (capturePairs position.val (beginRoot state)
        (cursorOps graph (graph.roots.get position) []))) := by
  intro owner route head present
  obtain ⟨pointer, member⟩ := capturePairs_callback position.val (beginRoot state) _ owner route head present
  have safe := source_route_safe graph position.val (graph.roots.get position) []
    (beginRoot state) (beginRoot_valid state valid) decode sentinel
  obtain ⟨decoded, bounded⟩ := capturePairs_decoded position.val (beginRoot state)
    (beginRoot_valid state valid) decode _ safe route pointer member
  have pointerEq := pairIndex_matches graph _ (source_capturePairs_unique graph position state)
    (source_capturePairs_empty graph position state) route pointer member
  rw [pointerEq]
  exact ⟨(represented pointer bounded).trans decoded, by simpa only [count, scanRoot] using bounded,
    Nat.lt_of_le_of_lt bounded fits⟩

/-- A zero route decodes only to sentinel zero in a represented parent store. -/
theorem empty_pointer (routes : RouteDescriptors width heap) (pointer : ℕ)
    (bounded : pointer ≤ routes.count) (empty : routes.route pointer = []) : pointer = 0 := by
  by_contra nonzero
  have valid : 0 < pointer ∧ pointer ≤ routes.count := ⟨Nat.pos_of_ne_zero nonzero, bounded⟩
  rw [routes.cellRoute pointer valid] at empty
  have impossible := congrArg List.length empty
  simp only [List.length_cons, List.length_nil] at impossible
  omega

noncomputable def sourceIndex (graph : DAG n) (position : Fin graph.roots.length) (state : Builder) :
    OccurrenceIndex graph := pairIndex graph (capturePairs position.val (beginRoot state)
      (cursorOps graph (graph.roots.get position) []))

/-- The full physical source-root cursor uses immediate pointers from the
actual builder scan. Its proof index is derived, never supplied by a caller.
Finite graph/descriptor representation, code coverage and initial counters
remain explicit; their construction costs are separate. -/
theorem captured_root_execution (program : Program width 4) (graph : DAG n)
    (position : Fin graph.roots.length) (builder : Builder) (valid : Valid builder)
    (initial : Array (Word width))
    (decode : ℕ → LeafRoute) (sentinel : decode 0 = [])
    (records : GraphRecords width initial graph) (routes : RouteDescriptors width initial)
    (count : routes.count = (scanRoot graph builder position).count)
    (represented : ∀ pointer ≤ (scanRoot graph builder position).count,
      routes.route pointer = routeScan position.val (beginRoot builder) decode
        (cursorOps graph (graph.roots.get position) []) pointer)
    (descriptorFits : (scanRoot graph builder position).count < 2 ^ width)
    (layout : SelectorLayout n) (readonly : ReadonlyLayout graph records routes layout)
    (b : ℕ) (target : Channel n) (state : RuntimeModel width n)
    (held : RuntimeStored graph records routes layout state)
    (capacity : ∀ channel, state.counters channel + (walkEvents graph (graph.roots.get position)).length + 1 < 2 ^ width)
    (heapFits : initial.size ≤ 2 ^ width) (oneFits : 1 < 2 ^ width)
    (base : ℕ) (address loaded temporary : Word width) (output : List (Word width))
    (fits : base + (emitCaptured graph records layout position.val b target (beginRoot builder) base
      (cursorOps graph (graph.roots.get position) [])).length < 2 ^ width)
    (block : BlockAt program base (emitCaptured graph records layout position.val b target
      (beginRoot builder) base (cursorOps graph (graph.roots.get position) []))) :
    ∃ finalAddress finalLoaded finalTemporary : Word width, ∃ ticks peak : ℕ,
      Execution program
        ((counterState state.heap base address loaded temporary).frame state.navigation output)
        ((counterState (runModel layout (sourceIndex graph position builder) b target state
            (cursorOps graph (graph.roots.get position) [])).heap
          (base + (emitCaptured graph records layout position.val b target (beginRoot builder) base
            (cursorOps graph (graph.roots.get position) [])).length)
          finalAddress finalLoaded finalTemporary).frame state.navigation output)
        ticks peak ∧ ticks ≤ 20 * (cursorOps graph (graph.roots.get position) []).length ∧
        peak ≤ 6 + state.heap.size + state.navigation.length +
          (cursorOps graph (graph.roots.get position) []).length + output.length ∧
        RuntimeStored graph records routes layout (runModel layout (sourceIndex graph position builder)
          b target state (cursorOps graph (graph.roots.get position) [])) ∧
        (runModel layout (sourceIndex graph position builder) b target state
          (cursorOps graph (graph.roots.get position) [])).counters = state.counters ∧
        modelProjection routes (runModel layout (sourceIndex graph position builder) b target state
          (cursorOps graph (graph.roots.get position) [])) =
          graph.foldLeafCursor (fun _ => 0) (graph.roots.get position) [] (state.counters, 0)
            ((state.selected.map routes.route).map fun route => (route, 0)) (keepBestRoute b target 0) := by
  have emitted := emitCaptured_eq graph records layout position.val b target (beginRoot builder)
    (sourceIndex graph position builder) base (cursorOps graph (graph.roots.get position) [])
    (source_captured graph position builder)
  have indexed := pair_root_index graph position builder valid decode sentinel routes count represented descriptorFits
  have coverage : BlockAt program base (rootCode graph records layout (sourceIndex graph position builder)
      b target base (graph.roots.get position)) := by
    simpa only [rootCode, ← emitted] using block
  have codeFits : base + (rootCode graph records layout (sourceIndex graph position builder)
      b target base (graph.roots.get position)).length < 2 ^ width := by
    simpa only [rootCode, ← emitted] using fits
  have execution := ForestCursorRoot.root_execution program graph (graph.roots.get position)
    records routes layout readonly (sourceIndex graph position builder) b target state held capacity
    heapFits oneFits indexed base address loaded temporary output codeFits coverage
  simpa only [rootCode, ← emitted] using execution

end Controller.Cost.ForestCursorCapturedProgram
