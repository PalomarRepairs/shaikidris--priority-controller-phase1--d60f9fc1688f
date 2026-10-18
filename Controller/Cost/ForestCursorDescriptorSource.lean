module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestCursorDescriptors

@[expose] public section

/-!
# Source leaf decoding for allocated cursor descriptors

The route-safety relation compares the builder's current identifier with the
positional route of each actual source leaf. It is a proof relation; the builder
stores neither complete routes nor a route dictionary. Source traversal and
parent allocation determine the relation, while physical descriptor cells are
a separate representation contract.
-/
namespace Controller.Cost.ForestCursorDescriptorSource

open Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestCursorTraversal Controller.Cost.ForestCursorRoot
open Controller.Cost.ForestCursorDescriptors

/-- The leaf route must decode from the identifier held at that scan operation. -/
def RouteSafe (root : ℕ) (state : Builder) (decode : ℕ → LeafRoute) : List (CursorOp n) → Prop
  | [] => True
  | operation :: rest =>
      (match operation with | .leaf _ route _ => decode state.current = route | _ => True) ∧
        RouteSafe root (ForestCursorDescriptors.step (n := n) root state operation) (routeStep state decode operation) rest

theorem routeScan_append (root : ℕ) (state : Builder) (decode : ℕ → LeafRoute)
    (first second : List (CursorOp n)) :
    routeScan root state decode (first ++ second) =
      routeScan root (scan root state first) (routeScan root state decode first) second := by
  induction first generalizing state decode with
  | nil => rfl
  | cons operation rest ih =>
      simpa only [List.cons_append, routeScan, scan, List.foldl_cons] using
        ih (ForestCursorDescriptors.step (n := n) root state operation) (routeStep state decode operation)

theorem routeSafe_append (root : ℕ) (state : Builder) (decode : ℕ → LeafRoute)
    (first second : List (CursorOp n)) :
    RouteSafe root state decode (first ++ second) ↔
      RouteSafe root state decode first ∧
        RouteSafe root (scan root state first) (routeScan root state decode first) second := by
  induction first generalizing state decode with
  | nil => simp [RouteSafe, scan, routeScan]
  | cons operation rest ih =>
      simp only [List.cons_append, RouteSafe, scan, List.foldl_cons, routeScan]
      rw [ih]
      exact and_assoc.symm

/-- Every source-balanced block retains the decoding of its initial current
identifier; all later allocations have strictly larger identifiers. -/
theorem balanced_current (root : ℕ) (state : Builder) (valid : Valid state)
    (decode : ℕ → LeafRoute) (operations : List (CursorOp n)) (balanced : NavBalanced operations) :
    routeScan root state decode operations (scan root state operations).current = decode state.current := by
  rw [(balanced_restore root operations balanced state).1]
  exact routeScan_preserves root state decode operations state.current valid.current

/-- Earlier leaf records remain in the accumulator as the source scan proceeds. -/
theorem step_old_leaves (root : ℕ) (state : Builder) (operation : CursorOp n)
    (leaf : LeafEntry) (present : leaf ∈ state.leaves) : leaf ∈ (ForestCursorDescriptors.step (n := n) root state operation).leaves := by
  cases operation with
  | leaf owner route head => exact List.mem_cons_of_mem _ present
  | node owner => exact present
  | down owner position child => exact present
  | up => exact present
  | enter owner position channel => exact present
  | leave owner position channel => exact present

theorem scan_old_leaves (root : ℕ) (state : Builder) (operations : List (CursorOp n))
    (leaf : LeafEntry) (present : leaf ∈ state.leaves) : leaf ∈ (scan root state operations).leaves := by
  induction operations generalizing state with
  | nil => exact present
  | cons operation rest ih => exact ih _ (step_old_leaves root state operation leaf present)

/-- A captured pointer belongs to the actual source leaf at its declared root
and continues to decode to that leaf's route after all subsequent allocations. -/
theorem safe_leaf_capture (root : ℕ) (state : Builder) (valid : Valid state)
    (decode : ℕ → LeafRoute) (operations : List (CursorOp n))
    (safe : RouteSafe root state decode operations)
    (owner : ℕ) (route : LeafRoute) (head : Channel n)
    (present : CursorOp.leaf owner route head ∈ operations) :
    ∃ leaf ∈ (scan root state operations).leaves,
      leaf.root = root ∧ leaf.owner = owner ∧ leaf.head = head.val ∧
      routeScan root state decode operations leaf.pointer = route := by
  induction operations generalizing state decode with
  | nil => simp at present
  | cons operation rest ih =>
      rcases List.mem_cons.mp present with equal | later
      · subst operation
        let leaf : LeafEntry := ⟨root, owner, state.current, head.val⟩
        refine ⟨leaf, ?_, rfl, rfl, rfl, ?_⟩
        · exact scan_old_leaves root (ForestCursorDescriptors.step (n := n) root state (.leaf owner route head)) rest leaf List.mem_cons_self
        · change routeScan root (ForestCursorDescriptors.step (n := n) root state (.leaf owner route head))
            (routeStep state decode (.leaf owner route head)) rest state.current = route
          rw [routeScan_preserves root _ _ rest state.current (by exact valid.current)]
          exact safe.1
      · exact ih (ForestCursorDescriptors.step (n := n) root state operation) (step_valid root state valid operation)
          (routeStep state decode operation) safe.2 later

/-- Composition over sibling blocks retains the same prefix decoder, even
though each sibling allocates new descriptors in the shared store. -/
theorem routeSafe_flatMap (root : ℕ) (items : List α) (body : α → List (CursorOp n))
    (balanced : ∀ item ∈ items, NavBalanced (body item))
    (routePrefix : LeafRoute)
    (correct : ∀ item ∈ items, ∀ (state : Builder), Valid state →
      ∀ decode : ℕ → LeafRoute, decode state.current = routePrefix → RouteSafe root state decode (body item))
    (state : Builder) (valid : Valid state) (decode : ℕ → LeafRoute) (current : decode state.current = routePrefix) :
    RouteSafe root state decode (items.flatMap body) := by
  induction items generalizing state decode with
  | nil => trivial
  | cons item rest ih =>
      rw [List.flatMap_cons, routeSafe_append]
      refine ⟨correct item List.mem_cons_self state valid decode current, ?_⟩
      apply ih
        (fun later present => balanced later (List.mem_cons_of_mem item present))
        (fun later present => correct later (List.mem_cons_of_mem item present))
        (scan root state (body item)) (scan_valid root state valid (body item))
        (routeScan root state decode (body item))
      exact (balanced_current root state valid decode (body item)
        (balanced item List.mem_cons_self)).trans current

def Skipped : CursorOp n → Prop
  | .node _ | .enter _ _ _ | .leave _ _ _ => True
  | _ => False

theorem skipped_scan (root : ℕ) (state : Builder) (decode : ℕ → LeafRoute)
    (operations : List (CursorOp n)) (skipped : ∀ operation ∈ operations, Skipped operation) :
    scan root state operations = state ∧ routeScan root state decode operations = decode ∧
      RouteSafe root state decode operations := by
  induction operations generalizing state decode with
  | nil => exact ⟨rfl, rfl, trivial⟩
  | cons operation rest ih =>
      have skip := skipped operation List.mem_cons_self
      have tail := ih state decode (fun later present => skipped later (List.mem_cons_of_mem operation present))
      cases operation <;> simp_all [Skipped, scan, routeScan, RouteSafe, ForestCursorDescriptors.step, routeStep]

theorem child_route_safe (root owner position child : ℕ) (body : List (CursorOp n))
    (routePrefix : LeafRoute)
    (correct : ∀ (state : Builder), Valid state → ∀ decode : ℕ → LeafRoute,
      decode state.current = position :: routePrefix → RouteSafe root state decode body)
    (state : Builder) (valid : Valid state) (decode : ℕ → LeafRoute)
    (current : decode state.current = routePrefix) :
    RouteSafe root state decode (CursorOp.down owner position child :: body ++ [CursorOp.up]) := by
  change True ∧ RouteSafe root (ForestCursorDescriptors.step (n := n) root state (.down owner position child))
    (routeStep state decode (.down owner position child)) (body ++ [.up])
  refine ⟨trivial, ?_⟩
  rw [routeSafe_append]
  refine ⟨correct _ (step_valid root state valid _) _ ?_, ?_⟩
  · simp [ForestCursorDescriptors.step, routeStep, extendRoute, current]
  · simp [RouteSafe]

/-- The route predicate is derived from the actual decoder source and the
allocation scan, rather than supplied for an arbitrary operation list. -/
theorem source_route_safe (graph : DAG n) (root : ℕ) (node : Fin graph.nodeCount)
    (routePrefix : LeafRoute) (state : Builder) (valid : Valid state)
    (decode : ℕ → LeafRoute) (current : decode state.current = routePrefix) :
    RouteSafe root state decode (cursorOps graph node routePrefix) := by
  have claim : ∀ rank : ℕ, ∀ node : Fin graph.nodeCount, node.val = rank →
      ∀ routePrefix : LeafRoute, ∀ state : Builder, Valid state →
      ∀ decode : ℕ → LeafRoute, decode state.current = routePrefix →
        RouteSafe root state decode (cursorOps graph node routePrefix) := by
    intro rank
    induction rank using Nat.strong_induction_on with
    | h rank ih =>
      intro node equal routePrefix state valid decode current
      rw [cursorOps]
      cases equation : graph.node node with
      | zero => simp [RouteSafe, ForestCursorDescriptors.step, routeStep]
      | input head => simpa [RouteSafe, ForestCursorDescriptors.step, routeStep] using current
      | liveAnd first second => simp [RouteSafe, ForestCursorDescriptors.step, routeStep]
      | disj refs =>
          simp only [RouteSafe, ForestCursorDescriptors.step, routeStep, true_and,
            List.singleton_append, List.cons_append, List.nil_append, DAG.childIndex_val]
          apply routeSafe_flatMap root (List.finRange refs.length)
            (fun position => CursorOp.down node.val position.val (refs.get position).val ::
              cursorOps graph (graph.childIndex node (refs.get position)) (position.val :: routePrefix) ++ [CursorOp.up])
            (fun position present => NavBalanced.child node.val position.val (refs.get position).val
              (cursor_navigation_balanced graph _ _)) routePrefix
          · intro position present previous held routes located
            apply child_route_safe root node.val position.val (refs.get position).val _ routePrefix
            · intro childState childValid childRoutes childCurrent
              exact ih (refs.get position).val
                (by have earlier := graph.childIndex_lt node (refs.get position); omega)
                (graph.childIndex node (refs.get position)) rfl _ childState childValid childRoutes childCurrent
            · exact held
            · exact located
          · exact valid
          · exact current
      | guard child labels =>
          let entered := (List.finRange labels.length).map (fun position =>
            CursorOp.enter node.val position.val (labels.get position))
          let exited := (List.finRange labels.length).reverse.map (fun position =>
            CursorOp.leave node.val position.val (labels.get position))
          let middle := CursorOp.down node.val 0 child.val ::
            cursorOps graph (graph.childIndex node child) (0 :: routePrefix) ++ [CursorOp.up]
          have enteredSkip : ∀ operation ∈ entered, Skipped operation := by
            intro operation present
            obtain ⟨position, member, same⟩ := List.mem_map.mp present
            subst operation
            trivial
          have exitedSkip : ∀ operation ∈ exited, Skipped operation := by
            intro operation present
            obtain ⟨position, member, same⟩ := List.mem_map.mp present
            subst operation
            trivial
          have entry := skipped_scan root state decode entered enteredSkip
          have whole : RouteSafe root state decode (entered ++ (middle ++ exited)) := by
            rw [routeSafe_append, entry.1, entry.2.1, routeSafe_append]
            refine ⟨entry.2.2, ?_, ?_⟩
            · apply child_route_safe root node.val 0 child.val _ routePrefix
              · intro childState childValid childRoutes childCurrent
                exact ih child.val (by have earlier := graph.childIndex_lt node child; omega)
                  (graph.childIndex node child) rfl _ childState childValid childRoutes childCurrent
              · exact valid
              · exact current
            · exact (skipped_scan root _ _ exited exitedSkip).2.2
          simpa only [RouteSafe, ForestCursorDescriptors.step, routeStep, true_and, entered, middle, exited,
            List.append_assoc, List.singleton_append, DAG.childIndex_val] using whole
  exact claim node.val node rfl routePrefix state valid decode current

/-- Every actual root leaf obtains an allocated pointer that decodes to its
source route and fits the final allocation counter. -/
theorem source_leaf_capture (graph : DAG n) (position : Fin graph.roots.length)
    (state : Builder) (valid : Valid state) (decode : ℕ → LeafRoute) (sentinel : decode 0 = [])
    (owner : ℕ) (route : LeafRoute) (head : Channel n)
    (present : CursorOp.leaf owner route head ∈ cursorOps graph (graph.roots.get position) []) :
    ∃ leaf ∈ (scanRoot graph state position).leaves,
      leaf.root = position.val ∧ leaf.owner = owner ∧ leaf.head = head.val ∧
      routeScan position.val (beginRoot state) decode
        (cursorOps graph (graph.roots.get position) []) leaf.pointer = route ∧
      leaf.pointer ≤ (scanRoot graph state position).count := by
  have held := beginRoot_valid state valid
  have safe := source_route_safe graph position.val (graph.roots.get position) [] (beginRoot state) held
    decode sentinel
  obtain ⟨leaf, member, rootEq, ownerEq, headEq, decoded⟩ :=
    safe_leaf_capture position.val (beginRoot state) held decode _ safe owner route head present
  exact ⟨leaf, member, rootEq, ownerEq, headEq, decoded,
    (scanRoot_valid graph state valid position).leaves leaf member⟩

/-- A ghost index chooses only IDs present in this root's captured leaf records.
Its empty route is the root sentinel. This proof-only choice function has no
runtime evaluation bound; direct captured-ID code emission is a distinct refinement. -/
noncomputable def capturedIndex (graph : DAG n) (position : Fin graph.roots.length)
    (state : Builder) (decode : ℕ → LeafRoute) : OccurrenceIndex graph := by
  classical
  exact {
    pointer := fun route =>
      if route = [] then 0 else
        if supported : ∃ leaf ∈ state.leaves, leaf.root = position.val ∧ decode leaf.pointer = route then
          (Classical.choose supported).pointer
        else 0
    empty := by simp }

/-- Finite represented descriptor decoding and the actual source capture
construct a RootIndex. Physical cell construction and direct captured-ID code
emission require their own operational refinement, not a route dictionary. -/
theorem captured_root_index (graph : DAG n) (position : Fin graph.roots.length)
    (state : Builder) (valid : Valid state) (decode : ℕ → LeafRoute) (sentinel : decode 0 = [])
    (routes : Controller.Cost.ForestCursorProgram.RouteDescriptors width heap)
    (count : routes.count = (scanRoot graph state position).count)
    (represented : ∀ pointer ≤ (scanRoot graph state position).count,
      routes.route pointer = routeScan position.val (beginRoot state) decode
        (cursorOps graph (graph.roots.get position) []) pointer)
    (fits : (scanRoot graph state position).count < 2 ^ width) :
    RootIndex graph (graph.roots.get position) routes
      (capturedIndex graph position (scanRoot graph state position)
        (routeScan position.val (beginRoot state) decode (cursorOps graph (graph.roots.get position) []))) := by
  classical
  intro owner route head present
  let final := scanRoot graph state position
  let finalDecode := routeScan position.val (beginRoot state) decode
    (cursorOps graph (graph.roots.get position) [])
  by_cases empty : route = []
  · subst route
    have result : routes.route 0 = [] ∧ 0 ≤ routes.count ∧ 0 < 2 ^ width :=
      ⟨routes.sentinel, Nat.zero_le _, by omega⟩
    simpa [capturedIndex] using result
  · obtain ⟨leaf, member, rootEq, ownerEq, headEq, decoded, bounded⟩ :=
      source_leaf_capture graph position state valid decode sentinel owner route head present
    have supported : ∃ leaf ∈ final.leaves, leaf.root = position.val ∧ finalDecode leaf.pointer = route :=
      ⟨leaf, member, rootEq, decoded⟩
    have chosen := Classical.choose_spec supported
    have bound := (scanRoot_valid graph state valid position).leaves (Classical.choose supported) chosen.1
    have pointerEq : (capturedIndex graph position final finalDecode).pointer route =
        (Classical.choose supported).pointer := by simp [capturedIndex, empty, supported]
    change routes.route ((capturedIndex graph position final finalDecode).pointer route) = route ∧
      (capturedIndex graph position final finalDecode).pointer route ≤ routes.count ∧
      (capturedIndex graph position final finalDecode).pointer route < 2 ^ width
    rw [pointerEq]
    exact ⟨(represented _ bound).trans chosen.2.2, by simpa only [count] using bound,
      Nat.lt_of_le_of_lt bound fits⟩

end Controller.Cost.ForestCursorDescriptorSource
