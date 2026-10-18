module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestWeightedTagged

@[expose] public section

/-!
# Score projection of the root-tagged selector

Erasing provenance identifies the actual tagged selector with the production
ordered-weight cursor. This transfers the semantic optimum score while leaving
selected-pointer provenance and physical witness reconstruction as separate
contracts. Arithmetic in the ordered group is not a fixed-width instruction.
-/
namespace Controller.Cost.ForestWeightedScore
open Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestCursorTraversal Controller.Cost.ForestWeightedTrace
open Controller.Cost.ForestWeightedTagged
variable {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]

def pickScore (previous : Option W) (score : W) : Option W :=
  match previous with
  | none => some score
  | some old => if old < score then some score else previous

theorem choose_score (previous : Option (Candidate W)) (proposed : Candidate W) :
    (choose previous proposed).map Candidate.score = pickScore (previous.map Candidate.score) proposed.score := by
  cases previous with
  | none => rfl
  | some old =>
      by_cases better : old.score < proposed.score <;> simp [choose, pickScore, better]

theorem keepBest_score (b : ℕ) (target head : Channel n) (total : W) (route : LeafRoute)
    (state : GuardCounters n × W) (best : Option (LeafRoute × W)) :
    (keepBestGenericRoute b target total route head state best).map Prod.snd =
      if state.1 head = 0 ∧ (b ≠ 1 ∨ state.1 target = 0) then
        pickScore (best.map Prod.snd) (total - state.2) else best.map Prod.snd := by
  by_cases feasible : state.1 head = 0 ∧ (b ≠ 1 ∨ state.1 target = 0)
  · cases best with
    | none => simp [keepBestGenericRoute, pickScore, feasible]
    | some old =>
        by_cases better : old.2 < total - state.2 <;>
          simp [keepBestGenericRoute, pickScore, feasible, better]
  · simp [keepBestGenericRoute, feasible]

def taggedView (state : TaggedState n W) : (GuardCounters n × W) × Option W :=
  (state.blocked, state.selected.map Candidate.score)

def weightedView (state : WeightedState n W) : (GuardCounters n × W) × Option W :=
  (state.1, state.2.map Prod.snd)

def scoreStep (weights : Channel n → W) (b : ℕ) (target : Channel n) (total : W)
    (state : (GuardCounters n × W) × Option W) : CursorOp n → (GuardCounters n × W) × Option W
  | .enter _ _ channel => (GenericWeight.enter weights state.1 channel, state.2)
  | .leave _ _ channel => (GenericWeight.leave weights state.1 channel, state.2)
  | .leaf _ _ head =>
      (state.1, if state.1.1 head = 0 ∧ (b ≠ 1 ∨ state.1.1 target = 0) then
        pickScore state.2 (total - state.1.2) else state.2)
  | _ => state

theorem tagged_step_score (weights : Channel n → W) (root b : ℕ) (target : Channel n)
    (total : W) (state : TaggedState n W) (operation : CursorOp n) :
    taggedView (taggedStep weights root b target total state operation) =
      scoreStep weights b target total (taggedView state) operation := by
  cases operation with
  | node owner => rfl
  | down owner position child => rfl
  | up => rfl
  | enter owner position channel => rfl
  | leave owner position channel => rfl
  | leaf owner route head =>
      by_cases feasible : state.blocked.1 head = 0 ∧ (b ≠ 1 ∨ state.blocked.1 target = 0)
      · have chosen : taggedStep weights root b target total state (.leaf owner route head) =
            ⟨state.blocked, ForestCursorDescriptors.step root state.descriptors (.leaf owner route head),
              choose state.selected ⟨root, state.descriptors.current, total - state.blocked.2⟩⟩ := by
          simp only [taggedStep, ite_eq_left feasible]
        rw [chosen]
        simp only [taggedView, scoreStep, choose_score]
        apply Prod.ext
        · rfl
        · exact (ite_eq_left feasible).symm
      · have retained : taggedStep weights root b target total state (.leaf owner route head) =
            ⟨state.blocked, ForestCursorDescriptors.step root state.descriptors (.leaf owner route head), state.selected⟩ := by
          simp only [taggedStep, ite_eq_right feasible]
        rw [retained]
        simp only [taggedView, scoreStep]
        apply Prod.ext
        · rfl
        · exact (ite_eq_right feasible).symm

theorem weighted_step_score (weights : Channel n → W) (b : ℕ) (target : Channel n)
    (total : W) (state : WeightedState n W) (operation : CursorOp n) :
    weightedView (weightedStep weights b target total state operation) =
      scoreStep weights b target total (weightedView state) operation := by
  cases operation with
  | node owner => rfl
  | down owner position child => rfl
  | up => rfl
  | enter owner position channel => rfl
  | leave owner position channel => rfl
  | leaf owner route head =>
      simp only [weightedView, weightedStep, scoreStep, keepBest_score]
      rfl

theorem tagged_fold_score (weights : Channel n → W) (root b : ℕ) (target : Channel n)
    (total : W) (operations : List (CursorOp n)) (state : TaggedState n W) :
    taggedView (runTaggedTrace weights root b target total operations state).1 =
      operations.foldl (scoreStep weights b target total) (taggedView state) := by
  induction operations generalizing state with
  | nil => rfl
  | cons operation rest ih =>
      simp only [runTaggedTrace, List.foldl_cons]
      rw [ih, tagged_step_score]

theorem weighted_fold_score (weights : Channel n → W) (b : ℕ) (target : Channel n)
    (total : W) (operations : List (CursorOp n)) (state : WeightedState n W) :
    weightedView (operations.foldl (weightedStep weights b target total) state) =
      operations.foldl (scoreStep weights b target total) (weightedView state) := by
  induction operations generalizing state with
  | nil => rfl
  | cons operation rest ih =>
      rw [List.foldl_cons, ih, weighted_step_score]
      rfl

/-- With zero counters and no incumbent, the root-tagged fold returns exactly
 the production cursor's optimum score. The descriptor builder is arbitrary
 because navigation cannot influence feasibility or weight comparisons. -/
theorem root_score (graph : DAG n) (weights : Channel n → W) (root b : ℕ)
    (target : Channel n) (node : Fin graph.nodeCount) (builder : ForestCursorDescriptors.Builder) :
    ((runTaggedTrace weights root b target (GenericWeight.total weights Finset.univ)
      (cursorOps graph node []) ⟨((fun _ => 0), 0), builder, none⟩).1.selected).map Candidate.score =
      (graph.bestGenericLeafRoute weights b target node).map Prod.snd := by
  let initial : TaggedState n W := ⟨((fun _ => 0), 0), builder, none⟩
  let production : WeightedState n W := (((fun _ => 0), 0), none)
  have same : taggedView initial = weightedView production := rfl
  have projected := tagged_fold_score weights root b target (GenericWeight.total weights Finset.univ)
    (cursorOps graph node []) initial
  rw [same, ← weighted_fold_score, weighted_cursor_correct] at projected
  have scores := congrArg Prod.snd projected
  simpa [taggedView, weightedView, initial, production, bestGenericLeafRoute,
    Option.map_map, Function.comp_def] using scores

/-- The selected numeric score is attained by a semantic forward route.
This assertion does not identify that route with the returned descriptor. -/
theorem root_score_witness (graph : DAG n) (weights : Channel n → W) (root b : ℕ)
    (target : Channel n) (node : Fin graph.nodeCount) (builder : ForestCursorDescriptors.Builder)
    (candidate : Candidate W)
    (returned : (runTaggedTrace weights root b target (GenericWeight.total weights Finset.univ)
      (cursorOps graph node []) ⟨((fun _ => 0), 0), builder, none⟩).1.selected = some candidate) :
    ∃ route, graph.bestGenericForwardLeafRoute weights b target node = some (route, candidate.score) := by
  have score := root_score graph weights root b target node builder
  rw [returned, Option.map_some, graph.bestGenericLeafRoute_eq] at score
  cases selected : graph.bestGenericForwardLeafRoute weights b target node with
  | none => simp [selected] at score
  | some pair =>
      rw [selected, Option.map_some] at score
      have equal : candidate.score = pair.2 := Option.some.inj score
      exact ⟨pair.1, by simpa only [equal] using selected⟩

/-- Every admissible true set is bounded by the actual tagged selected score,
for arbitrary nonnegative weights in the supported ordered group. -/
theorem root_score_optimal (graph : DAG n) (guarded : graph.Guarded) (weights : Channel n → W)
    (nonnegative : ∀ channel, 0 ≤ weights channel) (root b : ℕ) (target : Channel n)
    (node : Fin graph.nodeCount) (builder : ForestCursorDescriptors.Builder) (candidate : Candidate W)
    (returned : (runTaggedTrace weights root b target (GenericWeight.total weights Finset.univ)
      (cursorOps graph node []) ⟨((fun _ => 0), 0), builder, none⟩).1.selected = some candidate)
    (K : Finset (Channel n)) (eligible : Admissible b target K)
    (value : graph.eval (assignmentOfSet K) node = true) :
    GenericWeight.total weights K ≤ candidate.score := by
  obtain ⟨route, selected⟩ := root_score_witness graph weights root b target node builder candidate returned
  exact graph.bestGenericForwardLeafRoute_optimal guarded weights nonnegative b target node route
    candidate.score selected K eligible value

theorem root_score_feasible (graph : DAG n) (weights : Channel n → W) (root b : ℕ)
    (target : Channel n) (node : Fin graph.nodeCount) (builder : ForestCursorDescriptors.Builder)
    (candidate : Candidate W)
    (returned : (runTaggedTrace weights root b target (GenericWeight.total weights Finset.univ)
      (cursorOps graph node []) ⟨((fun _ => 0), 0), builder, none⟩).1.selected = some candidate) :
    ∃ route head blocked, RoutePath graph node route head blocked ∧ pathFeasible b target head blocked ∧
      candidate.score = GenericWeight.total weights (fullUnblocked blocked) := by
  obtain ⟨route, selected⟩ := root_score_witness graph weights root b target node builder candidate returned
  obtain ⟨head, blocked, path, feasible, score⟩ :=
    graph.bestGenericForwardLeafRoute_sound weights b target node route candidate.score selected
  exact ⟨route, head, blocked, path, feasible, score⟩

end Controller.Cost.ForestWeightedScore
