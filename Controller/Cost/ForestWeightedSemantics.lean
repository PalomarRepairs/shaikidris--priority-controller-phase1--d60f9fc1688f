module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestWeightedTagged

@[expose] public section

/-!
# Restoration of the root-tagged weighted cursor

The actual tagged transition's counter component is independent of provenance
and selection. Its source-root fold therefore has the same guard counters and
blocked-union weight as the production generic cursor. A correct initial
blocked-union weight is restored across every root while the incumbent remains
shared. These identities are semantic; ordered-weight operation counts and
fixed-width operand encodings have distinct contracts.
-/
namespace Controller.Cost.ForestWeightedSemantics
open Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestCursorTraversal Controller.Cost.ForestWeightedTrace
open Controller.Cost.ForestWeightedTagged
variable {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]

def blockedStep (weights : Channel n → W) (state : GuardCounters n × W) : CursorOp n → GuardCounters n × W
  | .enter _ _ channel => GenericWeight.enter weights state channel
  | .leave _ _ channel => GenericWeight.leave weights state channel
  | _ => state

theorem taggedStep_blocked (weights : Channel n → W) (root b : ℕ) (target : Channel n)
    (total : W) (state : TaggedState n W) (operation : CursorOp n) :
    (taggedStep weights root b target total state operation).blocked = blockedStep weights state.blocked operation := by
  cases operation with
  | node owner => rfl
  | down owner position child => rfl
  | up => rfl
  | enter owner position channel => rfl
  | leave owner position channel => rfl
  | leaf owner route head => simp only [taggedStep]; split <;> rfl

theorem weightedStep_blocked (weights : Channel n → W) (b : ℕ) (target : Channel n)
    (total : W) (state : WeightedState n W) (operation : CursorOp n) :
    (weightedStep weights b target total state operation).1 = blockedStep weights state.1 operation := by
  cases operation <;> rfl

theorem tagged_trace_blocked (weights : Channel n → W) (root b : ℕ) (target : Channel n)
    (total : W) (operations : List (CursorOp n)) (state : TaggedState n W) :
    (runTaggedTrace weights root b target total operations state).1.blocked =
      operations.foldl (blockedStep weights) state.blocked := by
  induction operations generalizing state with
  | nil => rfl
  | cons operation rest ih =>
      simp only [runTaggedTrace, List.foldl_cons]
      rw [ih, taggedStep_blocked]

theorem weighted_fold_blocked (weights : Channel n → W) (b : ℕ) (target : Channel n)
    (total : W) (operations : List (CursorOp n)) (state : WeightedState n W) :
    (operations.foldl (weightedStep weights b target total) state).1 =
      operations.foldl (blockedStep weights) state.1 := by
  induction operations generalizing state with
  | nil => rfl
  | cons operation rest ih =>
      rw [List.foldl_cons, ih, weightedStep_blocked]
      rfl

theorem root_restores (graph : DAG n) (weights : Channel n → W)
    (node : Fin graph.nodeCount) (root b : ℕ) (target : Channel n) (total : W)
    (state : TaggedState n W)
    (correct : state.blocked.2 = GenericWeight.total weights (blockedChannels state.blocked.1)) :
    (runTaggedTrace weights root b target total (cursorOps graph node []) state).1.blocked = state.blocked := by
  rw [tagged_trace_blocked]
  rw [← weighted_fold_blocked weights b target total _
    (state.blocked, (none : Option (LeafRoute × W)))]
  rw [weighted_cursor_correct, foldGenericLeafCursor_eq_fold]
  exact graph.foldGenericLeafRoutes_restores weights node state.blocked none _ correct

theorem roots_restore (graph : DAG n) (weights : Channel n → W) (b : ℕ)
    (target : Channel n) (total : W) (positions : List (Fin graph.roots.length))
    (state : TaggedState n W)
    (correct : state.blocked.2 = GenericWeight.total weights (blockedChannels state.blocked.1)) :
    (runRootsTrace graph weights b target total positions state).1.blocked = state.blocked := by
  induction positions generalizing state with
  | nil => rfl
  | cons position rest ih =>
      let started := { state with descriptors := ForestCursorDescriptors.beginRoot state.descriptors }
      have restored := root_restores graph weights (graph.roots.get position) position.val b target total started correct
      have tail := ih (runTaggedTrace weights position.val b target total
        (cursorOps graph (graph.roots.get position) []) started).1 (by rw [restored]; exact correct)
      simpa only [runRootsTrace] using tail.trans restored

theorem global_restores (graph : DAG n) (weights : Channel n → W) (b : ℕ) (target : Channel n) :
    (runGlobal graph weights b target).2.1.blocked = ((fun _ => 0), (0 : W)) := by
  exact roots_restore graph weights b target (cacheTotal weights).1 (List.finRange graph.roots.length)
    ⟨((fun _ => 0), 0), ForestCursorDescriptors.initial, none⟩
    (by simp [blockedChannels, GenericWeight.total])

/-- Strict comparison never invents provenance: it keeps the old triple or
accepts precisely the proposed triple. -/
theorem choose_member (previous : Option (Candidate W)) (proposed result : Candidate W)
    (selected : choose previous proposed = some result) :
    result = proposed ∨ previous = some result := by
  cases previous with
  | none =>
      left
      simpa only [choose, Option.some.injEq] using selected.symm
  | some old =>
      by_cases better : old.score < proposed.score
      · left
        rw [choose_better old proposed better] at selected
        exact (Option.some.inj selected).symm
      · right
        rw [choose_retains old proposed better] at selected
        exact selected

/-- The complete selected root/pointer/score comes from one actual proposal or
from the supplied incumbent; equal scores preserve the earlier provenance. -/
theorem select_member (items : List (Candidate W)) (previous : Option (Candidate W))
    (result : Candidate W) (selected : selectCandidates items previous = some result) :
    result ∈ items ∨ previous = some result := by
  induction items generalizing previous with
  | nil => right; exact selected
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
      rcases ih (some current) next with tail | retained
      · left; exact List.mem_cons_of_mem proposed tail
      · have equal : current = result := Option.some.inj retained
        subst current
        rcases choose_member previous proposed result chosen with accepted | old
        · left; exact List.mem_cons.mpr (Or.inl accepted)
        · right; exact old

/-- Weight and comparison decisions leave descriptor navigation unchanged. -/
theorem taggedStep_descriptors (weights : Channel n → W) (root b : ℕ) (target : Channel n)
    (total : W) (state : TaggedState n W) (operation : CursorOp n) :
    (taggedStep weights root b target total state operation).descriptors =
      ForestCursorDescriptors.step root state.descriptors operation := by
  cases operation with
  | node owner => rfl
  | down owner position child => rfl
  | up => rfl
  | enter owner position channel => rfl
  | leave owner position channel => rfl
  | leaf owner route head => simp only [taggedStep]; split <;> rfl

theorem tagged_trace_descriptors (weights : Channel n → W) (root b : ℕ) (target : Channel n)
    (total : W) (operations : List (CursorOp n)) (state : TaggedState n W) :
    (runTaggedTrace weights root b target total operations state).1.descriptors =
      ForestCursorDescriptors.scan root state.descriptors operations := by
  induction operations generalizing state with
  | nil => rfl
  | cons operation rest ih =>
      simp only [runTaggedTrace]
      rw [ih, taggedStep_descriptors]
      rfl

theorem roots_descriptors (graph : DAG n) (weights : Channel n → W) (b : ℕ)
    (target : Channel n) (total : W) (positions : List (Fin graph.roots.length))
    (state : TaggedState n W) :
    (runRootsTrace graph weights b target total positions state).1.descriptors =
      ForestCursorDescriptors.scanRoots graph state.descriptors positions := by
  induction positions generalizing state with
  | nil => rfl
  | cons position rest ih =>
      simp only [runRootsTrace]
      rw [ih, tagged_trace_descriptors]
      rfl

/-- Ghost proposals record precisely the feasible leaf candidates presented to
selection. They are not constructed by the runtime selector. -/
def proposal (root b : ℕ) (target : Channel n) (total : W)
    (state : TaggedState n W) : CursorOp n → Option (Candidate W)
  | .leaf _ _ head =>
      if state.blocked.1 head = 0 ∧ (b ≠ 1 ∨ state.blocked.1 target = 0) then
        some ⟨root, state.descriptors.current, total - state.blocked.2⟩ else none
  | _ => none

theorem taggedStep_selected (weights : Channel n → W) (root b : ℕ) (target : Channel n)
    (total : W) (state : TaggedState n W) (operation : CursorOp n) :
    (taggedStep weights root b target total state operation).selected =
      match proposal root b target total state operation with
      | none => state.selected
      | some candidate => choose state.selected candidate := by
  cases operation with
  | node owner => rfl
  | down owner position child => rfl
  | up => rfl
  | enter owner position channel => rfl
  | leave owner position channel => rfl
  | leaf owner route head => simp only [taggedStep, proposal]; split <;> rfl

def proposals (weights : Channel n → W) (root b : ℕ) (target : Channel n) (total : W) :
    List (CursorOp n) → TaggedState n W → List (Candidate W)
  | [], _ => []
  | operation :: rest, state =>
      let tail := proposals weights root b target total rest
        (taggedStep weights root b target total state operation)
      match proposal root b target total state operation with
      | none => tail
      | some candidate => candidate :: tail

/-- The actual tagged source fold is exactly strict-better selection of its
source-generated feasible proposals, with one shared incumbent. -/
theorem tagged_trace_selected (weights : Channel n → W) (root b : ℕ) (target : Channel n)
    (total : W) (operations : List (CursorOp n)) (state : TaggedState n W) :
    (runTaggedTrace weights root b target total operations state).1.selected =
      selectCandidates (proposals weights root b target total operations state) state.selected := by
  induction operations generalizing state with
  | nil => rfl
  | cons operation rest ih =>
      simp only [runTaggedTrace]
      rw [ih, taggedStep_selected]
      cases proposed : proposal root b target total state operation <;>
        simp only [proposals, proposed, selectCandidates, List.foldl_cons]

theorem selected_source_member (weights : Channel n → W) (root b : ℕ) (target : Channel n)
    (total : W) (operations : List (CursorOp n)) (state : TaggedState n W) (result : Candidate W)
    (selected : (runTaggedTrace weights root b target total operations state).1.selected = some result) :
    result ∈ proposals weights root b target total operations state ∨ state.selected = some result := by
  rw [tagged_trace_selected] at selected
  exact select_member _ _ _ selected

/-- A proposal is made only at the current feasible input occurrence. Its
pointer is the actual current descriptor, with the root stored atomically. -/
theorem proposal_leaf (root b : ℕ) (target : Channel n) (total : W)
    (state : TaggedState n W) (operation : CursorOp n) (candidate : Candidate W)
    (proposed : proposal root b target total state operation = some candidate) :
    ∃ owner route head, operation = .leaf owner route head ∧ candidate.root = root ∧
      candidate.pointer = state.descriptors.current ∧ candidate.score = total - state.blocked.2 ∧
      state.blocked.1 head = 0 ∧ (b ≠ 1 ∨ state.blocked.1 target = 0) := by
  cases operation with
  | node owner => simp [proposal] at proposed
  | down owner position child => simp [proposal] at proposed
  | up => simp [proposal] at proposed
  | enter owner position channel => simp [proposal] at proposed
  | leave owner position channel => simp [proposal] at proposed
  | leaf owner route head =>
      by_cases feasible : state.blocked.1 head = 0 ∧ (b ≠ 1 ∨ state.blocked.1 target = 0)
      · simp only [proposal, ite_eq_left feasible, Option.some.injEq] at proposed
        cases proposed
        exact ⟨owner, route, head, rfl, rfl, rfl, rfl, feasible.1, feasible.2⟩
      · simp [proposal, feasible] at proposed

private theorem capture_tail (root : ℕ) (state : ForestCursorDescriptors.Builder)
    (operation : CursorOp n) (rest : List (CursorOp n)) (pair : LeafRoute × ℕ)
    (present : pair ∈ ForestCursorCapturedProgram.capturePairs root
      (ForestCursorDescriptors.step root state operation) rest) :
    pair ∈ ForestCursorCapturedProgram.capturePairs root state (operation :: rest) := by
  cases operation with
  | node owner => exact present
  | down owner position child => exact present
  | up => exact present
  | enter owner position channel => exact present
  | leave owner position channel => exact present
  | leaf owner route head => exact List.mem_cons_of_mem _ present

/-- Every actual feasible proposal carries one of the source scan's captured
route/current-pointer pairs. This statement includes empty routes and repeated
input-node references without imposing global pointer injectivity. -/
theorem proposals_captured (weights : Channel n → W) (root b : ℕ) (target : Channel n)
    (total : W) (operations : List (CursorOp n)) (state : TaggedState n W) (candidate : Candidate W)
    (present : candidate ∈ proposals weights root b target total operations state) :
    candidate.root = root ∧ ∃ route,
      (route, candidate.pointer) ∈ ForestCursorCapturedProgram.capturePairs root state.descriptors operations := by
  induction operations generalizing state with
  | nil => simp only [proposals, List.not_mem_nil] at present
  | cons operation rest ih =>
      cases proposed : proposal root b target total state operation with
      | none =>
          have tail : candidate ∈ proposals weights root b target total rest
              (taggedStep weights root b target total state operation) := by
            simpa only [proposals, proposed] using present
          obtain ⟨rootEq, route, captured⟩ := ih _ tail
          refine ⟨rootEq, route, capture_tail root state.descriptors operation rest _ ?_⟩
          simpa only [taggedStep_descriptors] using captured
      | some current =>
          have membership : candidate = current ∨ candidate ∈ proposals weights root b target total rest
              (taggedStep weights root b target total state operation) := by
            simpa only [proposals, proposed, List.mem_cons] using present
          rcases membership with accepted | tail
          · subst current
            obtain ⟨owner, route, head, operationEq, rootEq, pointerEq, scoreEq, feasible⟩ :=
              proposal_leaf root b target total state operation candidate proposed
            subst operation
            refine ⟨rootEq, route, ?_⟩
            rw [pointerEq]
            exact List.mem_cons_self
          · obtain ⟨rootEq, route, captured⟩ := ih _ tail
            refine ⟨rootEq, route, capture_tail root state.descriptors operation rest _ ?_⟩
            simpa only [taggedStep_descriptors] using captured

end Controller.Cost.ForestWeightedSemantics
