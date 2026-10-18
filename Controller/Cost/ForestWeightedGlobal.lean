module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestWeightedProvenance

@[expose] public section

/-!
# Shared-incumbent composition of weighted root scans

Strict-better selection is an associative, left-biased maximum. A root scan
with a supplied incumbent therefore merges that incumbent with its fresh
source-derived summary. Feasible proposals are independent of the incumbent;
only blocked counters and descriptor navigation determine their contents.
These summaries are proof instrumentation, not extra runtime root scans.
-/
namespace Controller.Cost.ForestWeightedGlobal
open Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestCursorTraversal Controller.Cost.ForestWeightedTrace
open Controller.Cost.ForestWeightedTagged Controller.Cost.ForestWeightedSemantics
variable {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]

def merge (previous fresh : Option (Candidate W)) : Option (Candidate W) :=
  match fresh with
  | none => previous
  | some candidate => choose previous candidate

theorem choose_associative (previous : Option (Candidate W)) (first second : Candidate W) :
    choose (choose previous first) second = merge previous (choose (some first) second) := by
  cases previous with
  | none => simp only [choose_none]; cases choice : choose (some first) second <;> simp [merge, choice]
  | some old =>
      by_cases earlier : old.score < first.score
      · by_cases later : first.score < second.score
        · have whole : old.score < second.score := lt_trans earlier later
          simp [choose, merge, earlier, later, whole]
        · simp [choose, merge, earlier, later]
      · by_cases later : first.score < second.score
        · simp [choose, merge, earlier, later]
        · have whole : ¬ old.score < second.score :=
            not_lt_of_ge ((le_of_not_gt later).trans (le_of_not_gt earlier))
          simp [choose, merge, earlier, later, whole]

theorem merge_associative (previous first second : Option (Candidate W)) :
    merge (merge previous first) second = merge previous (merge first second) := by
  cases first with
  | none => cases second <;> rfl
  | some first =>
      cases second with
      | none => rfl
      | some second => exact choose_associative previous first second

/-- A supplied incumbent can be merged after the complete fresh summary;
strict ties retain the earlier complete root/pointer provenance. -/
theorem select_summary (items : List (Candidate W)) (previous : Option (Candidate W)) :
    selectCandidates items previous = merge previous (selectCandidates items none) := by
  induction items generalizing previous with
  | nil => rfl
  | cons first rest ih =>
      change selectCandidates rest (choose previous first) =
        merge previous (selectCandidates rest (some first))
      rw [ih, ih (some first)]
      exact merge_associative previous (some first) (selectCandidates rest none)

/-- Equality of source fields is enough: selection metadata cannot change a
feasible proposal or descriptor allocation. -/
theorem proposals_same_source (weights : Channel n → W) (root b : ℕ) (target : Channel n)
    (total : W) (operations : List (CursorOp n)) (first second : TaggedState n W)
    (blocked : first.blocked = second.blocked) (descriptors : first.descriptors = second.descriptors) :
    proposals weights root b target total operations first = proposals weights root b target total operations second := by
  induction operations generalizing first second with
  | nil => rfl
  | cons operation rest ih =>
      have nextBlocked : (taggedStep weights root b target total first operation).blocked =
          (taggedStep weights root b target total second operation).blocked := by
        rw [taggedStep_blocked, taggedStep_blocked, blocked]
      have nextDescriptors : (taggedStep weights root b target total first operation).descriptors =
          (taggedStep weights root b target total second operation).descriptors := by
        rw [taggedStep_descriptors, taggedStep_descriptors, descriptors]
      have next := ih _ _ nextBlocked nextDescriptors
      have current : proposal root b target total first operation = proposal root b target total second operation := by
        cases operation <;> simp only [proposal, blocked, descriptors]
      simp only [proposals, current, next]

/-- This equality is for the actual source operation fold. The fresh scan is
a semantic summary and is not evaluated again by the runtime caller. -/
theorem root_summary (weights : Channel n → W) (root b : ℕ) (target : Channel n)
    (total : W) (operations : List (CursorOp n)) (state : TaggedState n W) :
    (runTaggedTrace weights root b target total operations state).1.selected =
      merge state.selected
        (runTaggedTrace weights root b target total operations { state with selected := none }).1.selected := by
  have same := proposals_same_source weights root b target total operations state
    { state with selected := none } rfl rfl
  rw [tagged_trace_selected, same, select_summary]
  rw [tagged_trace_selected]

theorem merge_member (previous fresh : Option (Candidate W)) (candidate : Candidate W)
    (selected : merge previous fresh = some candidate) :
    previous = some candidate ∨ fresh = some candidate := by
  cases fresh with
  | none => exact Or.inl selected
  | some proposed =>
      rcases choose_member previous proposed candidate selected with new | old
      · right; simpa only [new] using (rfl : some proposed = some proposed)
      · exact Or.inl old

theorem merge_previous_bound (previous fresh candidate : Candidate W)
    (selected : merge (some previous) (some fresh) = some candidate) : previous.score ≤ candidate.score :=
  choose_dominates_previous previous fresh candidate selected

theorem merge_fresh_bound (previous : Option (Candidate W)) (fresh candidate : Candidate W)
    (selected : merge previous (some fresh) = some candidate) : fresh.score ≤ candidate.score :=
  choose_dominates_proposal previous fresh candidate selected

private theorem without_selection_eq (first second : TaggedState n W)
    (blocked : first.blocked = second.blocked) (descriptors : first.descriptors = second.descriptors) :
    { first with selected := none } = { second with selected := none } := by
  cases first with
  | mk firstBlocked firstDescriptors firstSelected =>
      cases second with
      | mk secondBlocked secondDescriptors secondSelected =>
          simp only at blocked descriptors
          cases blocked
          cases descriptors
          rfl

/-- One proof-only fresh summary per declared root. Its state carries source
counter and descriptor fields forward; the runtime evaluates only runRootsTrace. -/
def rootSummaries (graph : DAG n) (weights : Channel n → W) (b : ℕ) (target : Channel n) (total : W) :
    List (Fin graph.roots.length) → TaggedState n W → List (Option (Candidate W))
  | [], _ => []
  | position :: rest, state =>
      let started := { state with descriptors := ForestCursorDescriptors.beginRoot state.descriptors, selected := none }
      let fresh := (runTaggedTrace weights position.val b target total
        (cursorOps graph (graph.roots.get position) []) started).1
      fresh.selected :: rootSummaries graph weights b target total rest { fresh with selected := none }

theorem summaries_same_source (graph : DAG n) (weights : Channel n → W) (b : ℕ) (target : Channel n)
    (total : W) (positions : List (Fin graph.roots.length)) (first second : TaggedState n W)
    (blocked : first.blocked = second.blocked) (descriptors : first.descriptors = second.descriptors) :
    rootSummaries graph weights b target total positions first =
      rootSummaries graph weights b target total positions second := by
  cases positions with
  | nil => rfl
  | cons position rest =>
      have same := without_selection_eq
        { first with descriptors := ForestCursorDescriptors.beginRoot first.descriptors }
        { second with descriptors := ForestCursorDescriptors.beginRoot second.descriptors }
        blocked (by simp only; rw [descriptors])
      simpa only [rootSummaries] using congrArg
        (fun started : TaggedState n W =>
          let fresh := (runTaggedTrace weights position.val b target total
            (cursorOps graph (graph.roots.get position) []) started).1
          fresh.selected :: rootSummaries graph weights b target total rest { fresh with selected := none }) same

/-- The actual all-root caller equals a fold of source-derived fresh summaries,
with exactly one shared incumbent and the same caller-cached total operand. -/
theorem roots_selected_summary (graph : DAG n) (weights : Channel n → W) (b : ℕ) (target : Channel n)
    (total : W) (positions : List (Fin graph.roots.length)) (state : TaggedState n W) :
    (runRootsTrace graph weights b target total positions state).1.selected =
      (rootSummaries graph weights b target total positions state).foldl merge state.selected := by
  induction positions generalizing state with
  | nil => rfl
  | cons position rest ih =>
      let started := { state with descriptors := ForestCursorDescriptors.beginRoot state.descriptors }
      let current := (runTaggedTrace weights position.val b target total
        (cursorOps graph (graph.roots.get position) []) started).1
      let fresh := (runTaggedTrace weights position.val b target total
        (cursorOps graph (graph.roots.get position) []) { started with selected := none }).1
      have equalBlocked : current.blocked = fresh.blocked := by
        simp only [current, fresh, tagged_trace_blocked]
      have equalDescriptors : current.descriptors = fresh.descriptors := by
        simp only [current, fresh, tagged_trace_descriptors]
      have same := summaries_same_source graph weights b target total rest current
        { fresh with selected := none } equalBlocked equalDescriptors
      have choice : current.selected = merge state.selected fresh.selected :=
        root_summary weights position.val b target total (cursorOps graph (graph.roots.get position) []) started
      change (runRootsTrace graph weights b target total rest current).1.selected = _
      rw [ih, same, choice]
      rfl

/-- No initial incumbent is supplied to the global caller. The total weight
is computed once by cacheTotal and reused by every actual root scan. -/
theorem global_selected_summary (graph : DAG n) (weights : Channel n → W) (b : ℕ) (target : Channel n) :
    (runGlobal graph weights b target).2.1.selected =
      (rootSummaries graph weights b target (cacheTotal weights).1 (List.finRange graph.roots.length)
        ⟨((fun _ => 0), 0), ForestCursorDescriptors.initial, none⟩).foldl merge none := by
  exact roots_selected_summary graph weights b target (cacheTotal weights).1
    (List.finRange graph.roots.length) ⟨((fun _ => 0), 0), ForestCursorDescriptors.initial, none⟩

end Controller.Cost.ForestWeightedGlobal
