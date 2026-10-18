module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestWeightedTrace
public import Controller.Cost.ForestCursorWholeProgram

@[expose] public section

/-!
# Root-tagged ordered-weight selector

A feasible leaf proposes its current descriptor pointer, declared root and
unblocked weight. Strictly greater scores replace the selected triple; ties
retain its complete provenance. The total weight is a caller-cached operand.
The arithmetic trace counts generic ordered-group operations and makes no
fixed-width machine claim.
-/
namespace Controller.Cost.ForestWeightedTagged

open Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestCursorTraversal Controller.Cost.ForestWeightedTrace

variable {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]

structure Candidate (W : Type) where
  root : ℕ
  pointer : ℕ
  score : W
  deriving Repr

def choose (previous : Option (Candidate W)) (proposed : Candidate W) : Option (Candidate W) :=
  match previous with
  | none => some proposed
  | some old => if old.score < proposed.score then some proposed else previous

@[simp] theorem choose_none (proposed : Candidate W) : choose none proposed = some proposed := rfl

theorem choose_better (old proposed : Candidate W) (better : old.score < proposed.score) :
    choose (some old) proposed = some proposed := by
  simp only [choose, ite_eq_left better]

theorem choose_retains (old proposed : Candidate W) (notBetter : ¬ old.score < proposed.score) :
    choose (some old) proposed = some old := by
  simp only [choose, ite_eq_right notBetter]

/-- Pointer and root are replaced together, including when the pointer is zero. -/
theorem choose_origin (old proposed : Candidate W) (better : old.score < proposed.score) :
    (choose (some old) proposed).map (fun result => (result.root, result.pointer)) =
      some (proposed.root, proposed.pointer) := by
  rw [choose_better old proposed better]
  rfl

theorem choose_dominates_proposal (previous : Option (Candidate W)) (proposed result : Candidate W)
    (selected : choose previous proposed = some result) : proposed.score ≤ result.score := by
  cases previous with
  | none => simp only [choose, Option.some.injEq] at selected; subst result; exact le_refl _
  | some old =>
      by_cases better : old.score < proposed.score
      · rw [choose_better old proposed better] at selected
        injection selected with same
        subst result
        exact le_refl _
      · rw [choose_retains old proposed better] at selected
        injection selected with same
        subst result
        exact le_of_not_gt better

theorem choose_dominates_previous (old proposed result : Candidate W)
    (selected : choose (some old) proposed = some result) : old.score ≤ result.score := by
  by_cases better : old.score < proposed.score
  · rw [choose_better old proposed better] at selected
    injection selected with same
    subst result
    exact le_of_lt better
  · rw [choose_retains old proposed better] at selected
    injection selected with same
    subst result
    exact le_refl _

def selectCandidates (items : List (Candidate W)) (previous : Option (Candidate W)) :
    Option (Candidate W) := items.foldl choose previous

theorem select_nonempty (items : List (Candidate W)) (previous : Candidate W) :
    ∃ result, selectCandidates items (some previous) = some result := by
  induction items generalizing previous with
  | nil => exact ⟨previous, rfl⟩
  | cons proposed rest ih =>
      by_cases better : previous.score < proposed.score
      · simpa only [selectCandidates, List.foldl_cons, choose_better previous proposed better] using ih proposed
      · simpa only [selectCandidates, List.foldl_cons, choose_retains previous proposed better] using ih previous

theorem select_previous_bound (items : List (Candidate W)) (previous result : Candidate W)
    (selected : selectCandidates items (some previous) = some result) : previous.score ≤ result.score := by
  induction items generalizing previous with
  | nil => injection selected with same; subst result; exact le_refl _
  | cons proposed rest ih =>
      by_cases better : previous.score < proposed.score
      · have next : selectCandidates rest (some proposed) = some result := by
          simpa only [selectCandidates, List.foldl_cons, choose_better previous proposed better] using selected
        exact (le_of_lt better).trans (ih proposed next)
      · have next : selectCandidates rest (some previous) = some result := by
          simpa only [selectCandidates, List.foldl_cons, choose_retains previous proposed better] using selected
        exact ih previous next

theorem select_dominates (items : List (Candidate W)) (previous : Option (Candidate W))
    (result item : Candidate W) (selected : selectCandidates items previous = some result)
    (present : item ∈ items) : item.score ≤ result.score := by
  induction items generalizing previous with
  | nil => simp only [List.not_mem_nil] at present
  | cons proposed rest ih =>
      obtain ⟨current, chosen⟩ : ∃ current, choose previous proposed = some current := by
        cases previous with
        | none => exact ⟨proposed, rfl⟩
        | some old =>
            by_cases better : old.score < proposed.score
            · exact ⟨proposed, choose_better old proposed better⟩
            · exact ⟨old, choose_retains old proposed better⟩
      have next : selectCandidates rest (some current) = some result := by
        simpa only [selectCandidates, List.foldl_cons, chosen] using selected
      rcases List.mem_cons.mp present with equal | tail
      · subst item
        exact (choose_dominates_proposal previous proposed current chosen).trans
          (select_previous_bound rest current result next)
      · exact ih (some current) next tail

structure TaggedState (n : ℕ) (W : Type) where
  blocked : GuardCounters n × W
  descriptors : ForestCursorDescriptors.Builder
  selected : Option (Candidate W)

/-- Leaf routes are ignored by the runtime transition; only the current ID is
read. Guard weights change at zero/one counter transitions. -/
def taggedStep (weights : Channel n → W) (root b : ℕ) (target : Channel n) (total : W)
    (state : TaggedState n W) (operation : CursorOp n) : TaggedState n W :=
  let descriptors := ForestCursorDescriptors.step root state.descriptors operation
  match operation with
  | .enter _ _ channel => ⟨GenericWeight.enter weights state.blocked channel, descriptors, state.selected⟩
  | .leave _ _ channel => ⟨GenericWeight.leave weights state.blocked channel, descriptors, state.selected⟩
  | .leaf _ _ head =>
      if state.blocked.1 head = 0 ∧ (b ≠ 1 ∨ state.blocked.1 target = 0) then
        ⟨state.blocked, descriptors,
          choose state.selected ⟨root, state.descriptors.current, total - state.blocked.2⟩⟩
      else ⟨state.blocked, descriptors, state.selected⟩
  | _ => ⟨state.blocked, descriptors, state.selected⟩

theorem taggedStep_leaf_erased (weights : Channel n → W) (root b : ℕ) (target : Channel n)
    (total : W) (state : TaggedState n W) (owner : ℕ) (head : Channel n) (route : LeafRoute) :
    taggedStep weights root b target total state (.leaf owner route head) =
      taggedStep weights root b target total state (.leaf owner [] head) := rfl

def stepArithmetic (weights : Channel n → W) (b : ℕ) (target : Channel n) (total : W)
    (state : TaggedState n W) : CursorOp n → List (Arithmetic W)
  | .enter _ _ channel =>
      if state.blocked.1 channel = 0 then [.add state.blocked.2 (weights channel)] else []
  | .leave _ _ channel =>
      if state.blocked.1 channel = 1 then [.subtract state.blocked.2 (weights channel)] else []
  | .leaf _ _ head =>
      if state.blocked.1 head = 0 ∧ (b ≠ 1 ∨ state.blocked.1 target = 0) then
        match state.selected with
        | none => [.subtract total state.blocked.2]
        | some old => [.subtract total state.blocked.2, .compare old.score (total - state.blocked.2)]
      else []
  | _ => []

theorem stepArithmetic_bound (weights : Channel n → W) (b : ℕ) (target : Channel n)
    (total : W) (state : TaggedState n W) (operation : CursorOp n) :
    (stepArithmetic weights b target total state operation).length ≤ 2 := by
  cases operation with
  | node owner => simp [stepArithmetic]
  | down owner position child => simp [stepArithmetic]
  | up => simp [stepArithmetic]
  | enter owner position channel =>
      by_cases zero : state.blocked.1 channel = 0 <;> simp [stepArithmetic, zero]
  | leave owner position channel =>
      by_cases one : state.blocked.1 channel = 1 <;> simp [stepArithmetic, one]
  | leaf owner route head =>
      by_cases feasible : state.blocked.1 head = 0 ∧ (b ≠ 1 ∨ state.blocked.1 target = 0)
      · cases selected : state.selected <;> simp [stepArithmetic, feasible, selected]
      · simp [stepArithmetic, feasible]

/-- A feasible improved leaf updates root, pointer and score atomically at the
mathematical ordered-arithmetic interface. -/
theorem tagged_leaf_replaces (weights : Channel n → W) (root b : ℕ) (target : Channel n)
    (total : W) (state : TaggedState n W) (owner : ℕ) (route : LeafRoute) (head : Channel n)
    (old : Candidate W) (selected : state.selected = some old)
    (feasible : state.blocked.1 head = 0 ∧ (b ≠ 1 ∨ state.blocked.1 target = 0))
    (better : old.score < total - state.blocked.2) :
    (taggedStep weights root b target total state (.leaf owner route head)).selected =
      some ⟨root, state.descriptors.current, total - state.blocked.2⟩ := by
  simp only [taggedStep, feasible, ite_eq_left, selected]
  exact choose_better old _ better


/-- Instrumented execution of the tagged transitions. The arithmetic trace is
proof instrumentation; operand lists are not part of the selector's state. -/
def runTaggedTrace (weights : Channel n → W) (root b : ℕ) (target : Channel n) (total : W) :
    List (CursorOp n) → TaggedState n W → TaggedState n W × List (Arithmetic W)
  | [], state => (state, [])
  | operation :: rest, state =>
      let current := stepArithmetic weights b target total state operation
      let later := runTaggedTrace weights root b target total rest
        (taggedStep weights root b target total state operation)
      (later.1, current ++ later.2)

theorem runTaggedTrace_length (weights : Channel n → W) (root b : ℕ) (target : Channel n)
    (total : W) (operations : List (CursorOp n)) (state : TaggedState n W) :
    (runTaggedTrace weights root b target total operations state).2.length ≤ 2 * operations.length := by
  induction operations generalizing state with
  | nil => simp [runTaggedTrace]
  | cons operation rest ih =>
      have current := stepArithmetic_bound weights b target total state operation
      have tail := ih (taggedStep weights root b target total state operation)
      simp only [runTaggedTrace, List.length_append, List.length_cons]
      omega

/-- All root scans share the incumbent triple; only the navigation origin is
reset. The total weight remains the same cached parameter throughout. -/
def runRootsTrace (graph : DAG n) (weights : Channel n → W) (b : ℕ) (target : Channel n) (total : W) :
    List (Fin graph.roots.length) → TaggedState n W → TaggedState n W × List (Arithmetic W)
  | [], state => (state, [])
  | position :: rest, state =>
      let started := { state with descriptors := ForestCursorDescriptors.beginRoot state.descriptors }
      let current := runTaggedTrace weights position.val b target total
        (cursorOps graph (graph.roots.get position) []) started
      let later := runRootsTrace graph weights b target total rest current.1
      (later.1, current.2 ++ later.2)

theorem runRootsTrace_length (graph : DAG n) (weights : Channel n → W) (b : ℕ) (target : Channel n)
    (total : W) (positions : List (Fin graph.roots.length)) (state : TaggedState n W) :
    (runRootsTrace graph weights b target total positions state).2.length ≤
      2 * Controller.Cost.ForestCursorAllRootsExecution.rootOperations graph positions := by
  induction positions generalizing state with
  | nil => simp [runRootsTrace, Controller.Cost.ForestCursorAllRootsExecution.rootOperations]
  | cons position rest ih =>
      let started := { state with descriptors := ForestCursorDescriptors.beginRoot state.descriptors }
      have current := runTaggedTrace_length weights position.val b target total
        (cursorOps graph (graph.roots.get position) []) started
      have tail := ih (runTaggedTrace weights position.val b target total
        (cursorOps graph (graph.roots.get position) []) started).1
      simp only [runRootsTrace, started, List.length_append,
        Controller.Cost.ForestCursorAllRootsExecution.rootOperations, List.map_cons, List.sum_cons] at *
      omega

def runGlobal (graph : DAG n) (weights : Channel n → W) (b : ℕ) (target : Channel n) :
    (W × List (Arithmetic W)) × (TaggedState n W × List (Arithmetic W)) :=
  let cached := cacheTotal weights
  (cached, runRootsTrace graph weights b target cached.1 (List.finRange graph.roots.length)
    ⟨(fun _ => 0, 0), ForestCursorDescriptors.initial, none⟩)

/-- The global incumbent comparisons, guard updates and one total computation
are all included. Generic arithmetic remains separate from operand encoding. -/
theorem global_arithmetic_bound (graph : DAG n) (forest : graph.FormulaForest)
    (weights : Channel n → W) (b : ℕ) (target : Channel n) :
    (runGlobal graph weights b target).1.2.length + (runGlobal graph weights b target).2.2.length ≤
      n + 8 * (graph.roots.length + graph.childIncidences) + 4 * graph.guardIncidences := by
  have current := runRootsTrace_length graph weights b target (cacheTotal weights).1
    (List.finRange graph.roots.length)
    (⟨(fun _ => 0, 0), ForestCursorDescriptors.initial, none⟩ : TaggedState n W)
  have source := Controller.Cost.ForestCursorCharging.all_root_budget_bound graph forest
  rw [← Controller.Cost.ForestCursorWholeProgram.rootOperations_total] at source
  have cached := (cacheTotal_correct weights).2
  simp only [runGlobal] at *
  rw [cached]
  omega

end Controller.Cost.ForestWeightedTagged
