module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestCursorTraversal

@[expose] public section

/-!
# Exact callback semantics of the source-rooted forest cursor

The source-derived operation fold agrees with the production positional cursor.
Navigation and source-record reads preserve the callback state; repeated guard
incidences retain their multiplicity. This semantic projection does not assert
an instruction or construction cost.
-/
namespace Controller.Cost.ForestCursorSemantics

open Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestCursorTraversal

/-- Folding one component preserves the other component exactly. -/
theorem fold_pair (items : List α) (step : β → α → β) (state : β) (saved : γ) :
    items.foldl (fun previous item => (step previous.1 item, previous.2)) (state, saved) =
      (items.foldl step state, saved) := by
  induction items generalizing state with
  | nil => rfl
  | cons item rest ih => simpa only [List.foldl_cons] using ih (step state item)

theorem enter_zero_labels (state : WeightedCounters n) (labels : List (Channel n)) :
    enterWeightedGuards (fun _ => 0) state labels = (enterGuards state.1 labels, state.2) := by
  induction labels generalizing state with
  | nil => rfl
  | cons label rest ih =>
      rw [enterWeightedGuards, List.foldl_cons]
      change enterWeightedGuards (fun _ => 0)
        (enterWeightedLabel (fun _ => 0) state label) rest = _
      rw [ih, enter_zero state.1 state.2 label]
      rfl

theorem leave_zero_labels (state : WeightedCounters n) (labels : List (Channel n)) :
    leaveWeightedGuards (fun _ => 0) state labels = (leaveGuards state.1 labels, state.2) := by
  induction labels generalizing state with
  | nil => rfl
  | cons label rest ih =>
      rw [leaveWeightedGuards, List.foldl_cons]
      change leaveWeightedGuards (fun _ => 0)
        (leaveWeightedLabel (fun _ => 0) state label) rest = _
      rw [ih, leave_zero state.1 state.2 label]
      rfl

theorem leave_reverse_zero (state : WeightedCounters n) (labels : List (Channel n)) :
    leaveWeightedGuards (fun _ => 0) state labels.reverse =
      leaveWeightedGuards (fun _ => 0) state labels := by
  rw [leave_zero_labels, leave_zero_labels, leave_reverse]

/-- The stored label positions fold to the production guard-entry operation. -/
theorem indexed_enter_fold (b : ℕ) (target : Channel n) (owner : ℕ)
    (labels : List (Channel n)) (state : CursorState n) :
    ((List.finRange labels.length).map (fun position =>
      CursorOp.enter owner position.val (labels.get position))).foldl (cursorStep b target) state =
      (enterWeightedGuards (fun _ => 0) state.1 labels, state.2) := by
  rw [List.foldl_map]
  calc
    _ = ((List.finRange labels.length).map labels.get).foldl
        (fun previous label => (enterWeightedLabel (fun _ => 0) previous.1 label, previous.2)) state := by
      rw [List.foldl_map]
      rfl
    _ = labels.foldl
        (fun previous label => (enterWeightedLabel (fun _ => 0) previous.1 label, previous.2)) state := by
      rw [List.map_get_finRange]
    _ = _ := fold_pair labels _ state.1 state.2

/-- Reversed exit positions are extensionally the production exit fold, with
no distinctness assumption on the stored labels. -/
theorem indexed_leave_fold (b : ℕ) (target : Channel n) (owner : ℕ)
    (labels : List (Channel n)) (state : CursorState n) :
    ((List.finRange labels.length).reverse.map (fun position =>
      CursorOp.leave owner position.val (labels.get position))).foldl (cursorStep b target) state =
      (leaveWeightedGuards (fun _ => 0) state.1 labels, state.2) := by
  rw [List.foldl_map]
  calc
    _ = ((List.finRange labels.length).reverse.map labels.get).foldl
        (fun previous label => (leaveWeightedLabel (fun _ => 0) previous.1 label, previous.2)) state := by
      rw [List.foldl_map]
      rfl
    _ = labels.reverse.foldl
        (fun previous label => (leaveWeightedLabel (fun _ => 0) previous.1 label, previous.2)) state := by
      rw [List.map_reverse, List.map_get_finRange]
    _ = (leaveWeightedGuards (fun _ => 0) state.1 labels.reverse, state.2) :=
      fold_pair labels.reverse _ state.1 state.2
    _ = _ := by rw [leave_reverse_zero]

/-- The full source-rooted callback fold is exactly the production cursor.
This identity holds for every initial counter and accumulator state. -/
theorem cursor_fold_correct (graph : DAG n) (node : Fin graph.nodeCount)
    (routePrefix : LeafRoute) (b : ℕ) (target : Channel n) (state : CursorState n) :
    (cursorOps graph node routePrefix).foldl (cursorStep b target) state =
      graph.foldLeafCursor (fun _ => 0) node routePrefix state.1 state.2
        (keepBestRoute b target 0) := by
  have claim : ∀ rank : ℕ, ∀ current : Fin graph.nodeCount, current.val = rank →
      ∀ routePrefix : LeafRoute, ∀ state : CursorState n,
        (cursorOps graph current routePrefix).foldl (cursorStep b target) state =
          graph.foldLeafCursor (fun _ => 0) current routePrefix state.1 state.2
            (keepBestRoute b target 0) := by
    intro rank
    induction rank using Nat.strong_induction_on with
    | h rank ih =>
      intro current equal route currentState
      rw [cursorOps, foldLeafCursor]
      cases equation : graph.node current with
      | zero => rfl
      | input head => rfl
      | liveAnd left right => rfl
      | disj refs =>
          simp only [List.foldl_cons, cursorStep, List.foldl_flatMap]
          congr 1
          funext previous position
          simpa only [List.foldl_append, List.foldl_cons, List.foldl_nil, cursorStep] using
            ih _ (by have earlier := graph.childIndex_lt current (refs.get position); omega)
              _ rfl (position.val :: route) previous
      | guard child labels =>
          simp only [List.foldl_cons, cursorStep, List.foldl_append, List.foldl_nil]
          rw [indexed_enter_fold]
          rw [ih _ (by have earlier := graph.childIndex_lt current child; omega) _ rfl]
          rw [indexed_leave_fold]
  exact claim node.val node rfl routePrefix state

/-- The zero-initialized source root has exactly the production callback result.
A forest instruction and construction bound is an additional theorem. -/
theorem root_cursor_identity (graph : DAG n) (root : Fin graph.nodeCount)
    (b : ℕ) (target : Channel n) :
    (cursorOps graph root []).foldl (cursorStep b target) ((fun _ => 0, 0), none) =
      graph.foldLeafCursor (fun _ => 0) root [] (fun _ => 0, 0) none
        (keepBestRoute b target 0) :=
  cursor_fold_correct graph root [] b target ((fun _ => 0, 0), none)

end Controller.Cost.ForestCursorSemantics
