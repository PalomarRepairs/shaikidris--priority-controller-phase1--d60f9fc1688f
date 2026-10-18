module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestWeightedSemantics

@[expose] public section

/-!
# Route-erased direct weighted forest recursion

The executable recurrence carries current descriptor IDs, blocked counters,
the shared incumbent and arithmetic-call counters. It does not construct
cursorOps or route-prefix lists. The operation-list relation is proof-only.
Indexed source-record lookup and operand formation have their own physical
input contract; an arbitrary DAG.node function is not assumed constant-time.
-/
namespace Controller.Cost.ForestWeightedDirect
open Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestCursorTraversal Controller.Cost.ForestWeightedTrace
open Controller.Cost.ForestWeightedTagged
variable {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]

structure State (n : ℕ) (W : Type) where
  data : TaggedState n W
  operations : ℕ
  arithmetic : ℕ

/-- This counter examines feasibility and incumbent presence without executing
weight addition, subtraction or comparison a second time. -/
def arithmeticCount (b : ℕ) (target : Channel n) (state : TaggedState n W) : CursorOp n → ℕ
  | .enter _ _ channel => if state.blocked.1 channel = 0 then 1 else 0
  | .leave _ _ channel => if state.blocked.1 channel = 1 then 1 else 0
  | .leaf _ _ head =>
      if state.blocked.1 head = 0 ∧ (b ≠ 1 ∨ state.blocked.1 target = 0) then
        match state.selected with | none => 1 | some _ => 2
      else 0
  | _ => 0

theorem arithmeticCount_eq (weights : Channel n → W) (b : ℕ) (target : Channel n) (total : W)
    (state : TaggedState n W) (operation : CursorOp n) :
    arithmeticCount b target state operation = (stepArithmetic weights b target total state operation).length := by
  cases operation with
  | node owner => rfl
  | down owner position child => rfl
  | up => rfl
  | enter owner position channel => by_cases zero : state.blocked.1 channel = 0 <;> simp [arithmeticCount, stepArithmetic, zero]
  | leave owner position channel => by_cases one : state.blocked.1 channel = 1 <;> simp [arithmeticCount, stepArithmetic, one]
  | leaf owner route head =>
      by_cases feasible : state.blocked.1 head = 0 ∧ (b ≠ 1 ∨ state.blocked.1 target = 0)
      · cases selected : state.selected <;> simp [arithmeticCount, stepArithmetic, feasible, selected]
      · simp [arithmeticCount, stepArithmetic, feasible]

def emit (weights : Channel n → W) (total : W) (root b : ℕ) (target : Channel n)
    (state : State n W) (operation : CursorOp n) : State n W :=
  ⟨taggedStep weights root b target total state.data operation, state.operations + 1,
    state.arithmetic + arithmeticCount b target state.data operation⟩

/-- Specification only: the direct runtime recursion does not call this fold. -/
def runOps (weights : Channel n → W) (total : W) (root b : ℕ) (target : Channel n)
    (state : State n W) (operations : List (CursorOp n)) : State n W :=
  operations.foldl (emit weights total root b target) state

theorem emit_leaf_erased (weights : Channel n → W) (total : W) (root b : ℕ) (target : Channel n)
    (state : State n W) (owner : ℕ) (head : Channel n) (route : LeafRoute) :
    emit weights total root b target state (.leaf owner [] head) =
      emit weights total root b target state (.leaf owner route head) := rfl

def runNode (graph : DAG n) (weights : Channel n → W) (total : W) (root b : ℕ) (target : Channel n)
    (node : Fin graph.nodeCount) (state : State n W) : State n W :=
  let entered := emit weights total root b target state (.node node.val)
  match graph.node node with
  | .zero => entered
  | .liveAnd _ _ => entered
  | .input head => emit weights total root b target entered (.leaf node.val [] head)
  | .disj refs =>
      refs.zipIdx.foldl (fun current item =>
        let child := graph.childIndex node item.1
        let down := emit weights total root b target current (.down node.val item.2 child.val)
        let visited := runNode graph weights total root b target child down
        emit weights total root b target visited .up) entered
  | .guard child labels =>
      let indexed := labels.zipIdx
      let guarded := indexed.foldl (fun current item => emit weights total root b target current (.enter node.val item.2 item.1)) entered
      let down := emit weights total root b target guarded (.down node.val 0 (graph.childIndex node child).val)
      let visited := runNode graph weights total root b target (graph.childIndex node child) down
      let up := emit weights total root b target visited .up
      indexed.reverse.foldl (fun current item => emit weights total root b target current (.leave node.val item.2 item.1)) up
termination_by node.val
decreasing_by all_goals exact graph.childIndex_lt _ _

private theorem zipIdx_finRange (items : List α) :
    items.zipIdx = (List.finRange items.length).map (fun position => (items.get position, position.val)) := by
  apply List.ext_getElem
  · simp
  · intro index leftBound rightBound
    simp

private theorem foldl_agrees (items : List α) (left right : β → α → β)
    (same : ∀ state item, left state item = right state item) (state : β) :
    items.foldl left state = items.foldl right state := by
  induction items generalizing state with
  | nil => rfl
  | cons item rest ih => simp only [List.foldl_cons, same]; exact ih _

private theorem foldl_flatBlocks (items : List α) (body : α → List β)
    (step : γ → β → γ) (state : γ) :
    (items.flatMap body).foldl step state =
      items.foldl (fun current item => (body item).foldl step current) state := by
  induction items generalizing state with
  | nil => rfl
  | cons item rest ih => simp only [List.flatMap_cons, List.foldl_append, List.foldl_cons]; exact ih _

/-- Whole-node refinement for arbitrary ghost prefix routes and accumulators. -/
theorem runNode_eq (graph : DAG n) (weights : Channel n → W) (total : W) (root b : ℕ) (target : Channel n) :
    ∀ (node : Fin graph.nodeCount) (route : LeafRoute) (state : State n W),
      runNode graph weights total root b target node state =
        runOps weights total root b target state (cursorOps graph node route) := by
  have claim : ∀ rank : ℕ, ∀ node : Fin graph.nodeCount, node.val = rank →
      ∀ route state, runNode graph weights total root b target node state =
        runOps weights total root b target state (cursorOps graph node route) := by
    intro rank
    induction rank using Nat.strong_induction_on with
    | h rank ih =>
      intro node equal route state
      rw [runNode.eq_def, cursorOps.eq_def]
      cases kind : graph.node node with
      | zero => rfl
      | liveAnd left right => rfl
      | input head => exact emit_leaf_erased weights total root b target _ node.val head route
      | disj refs =>
          simp only [zipIdx_finRange, List.foldl_map, runOps, List.foldl_cons, List.foldl_nil, foldl_flatBlocks]
          apply foldl_agrees
          intro current position
          let child := graph.childIndex node (refs.get position)
          have earlier : child.val < rank := by
            have bound := graph.childIndex_lt node (refs.get position)
            dsimp [child]
            omega
          rw [ih child.val earlier child rfl (position.val :: route)]
          simp only [runOps, List.foldl_append, List.foldl_cons, List.foldl_nil]
          rfl
      | guard child labels =>
          simp only [zipIdx_finRange, ← List.map_reverse, List.foldl_map]
          have earlier : (graph.childIndex node child).val < rank := by
            have bound := graph.childIndex_lt node child
            omega
          rw [ih (graph.childIndex node child).val earlier (graph.childIndex node child) rfl (0 :: route)]
          simp only [runOps, List.foldl_cons, List.foldl_append, List.foldl_map, List.foldl_nil]
  intro node route state
  exact claim node.val node rfl route state


theorem runOps_data (weights : Channel n → W) (total : W) (root b : ℕ) (target : Channel n)
    (state : State n W) (operations : List (CursorOp n)) :
    (runOps weights total root b target state operations).data =
      (runTaggedTrace weights root b target total operations state.data).1 := by
  induction operations generalizing state with
  | nil => rfl
  | cons operation rest ih =>
      change (runOps weights total root b target (emit weights total root b target state operation) rest).data = _
      rw [ih]
      rfl

theorem runOps_counts (weights : Channel n → W) (total : W) (root b : ℕ) (target : Channel n)
    (state : State n W) (operations : List (CursorOp n)) :
    (runOps weights total root b target state operations).operations = state.operations + operations.length ∧
    (runOps weights total root b target state operations).arithmetic = state.arithmetic +
      (runTaggedTrace weights root b target total operations state.data).2.length := by
  induction operations generalizing state with
  | nil => simp [runOps, runTaggedTrace]
  | cons operation rest ih =>
      obtain ⟨visits, arithmetic⟩ := ih (emit weights total root b target state operation)
      constructor
      · simpa only [runOps, List.foldl_cons, emit, List.length_cons, Nat.add_assoc, Nat.add_comm] using visits
      · simpa only [runOps, List.foldl_cons, emit, arithmeticCount_eq weights b target total, runTaggedTrace,
          List.length_append, Nat.add_assoc] using arithmetic

theorem runNode_projection (graph : DAG n) (weights : Channel n → W) (total : W)
    (root b : ℕ) (target : Channel n) (node : Fin graph.nodeCount) (state : State n W) :
    (runNode graph weights total root b target node state).data =
      (runTaggedTrace weights root b target total (cursorOps graph node []) state.data).1 ∧
    (runNode graph weights total root b target node state).arithmetic = state.arithmetic +
      (runTaggedTrace weights root b target total (cursorOps graph node []) state.data).2.length := by
  rw [runNode_eq graph weights total root b target node [] state]
  exact ⟨runOps_data weights total root b target state _, (runOps_counts weights total root b target state _).2⟩

theorem runNode_arithmetic_bound (graph : DAG n) (weights : Channel n → W) (total : W)
    (root b : ℕ) (target : Channel n) (node : Fin graph.nodeCount) (state : State n W) :
    (runNode graph weights total root b target node state).arithmetic ≤
      state.arithmetic + 2 * (cursorOps graph node []).length := by
  obtain ⟨data, calls⟩ := runNode_projection graph weights total root b target node state
  rw [calls]
  exact Nat.add_le_add_left (runTaggedTrace_length weights root b target total _ state.data) _

def runRoots (graph : DAG n) (weights : Channel n → W) (total : W) (b : ℕ) (target : Channel n) :
    List (Fin graph.roots.length) → State n W → State n W
  | [], state => state
  | position :: rest, state =>
      let started := { state with data := { state.data with descriptors := ForestCursorDescriptors.beginRoot state.data.descriptors } }
      let current := runNode graph weights total position.val b target (graph.roots.get position) started
      runRoots graph weights total b target rest current

/-- This is an actual direct all-root recurrence. It carries the same incumbent
and current-ID builder, without generating operation lists between roots. -/
theorem runRoots_projection (graph : DAG n) (weights : Channel n → W) (total : W)
    (b : ℕ) (target : Channel n) (positions : List (Fin graph.roots.length)) (state : State n W) :
    (runRoots graph weights total b target positions state).data =
      (runRootsTrace graph weights b target total positions state.data).1 ∧
    (runRoots graph weights total b target positions state).arithmetic = state.arithmetic +
      (runRootsTrace graph weights b target total positions state.data).2.length := by
  induction positions generalizing state with
  | nil => simp [runRoots, runRootsTrace]
  | cons position rest ih =>
      let started := { state with data := { state.data with descriptors := ForestCursorDescriptors.beginRoot state.data.descriptors } }
      let current := runNode graph weights total position.val b target (graph.roots.get position) started
      obtain ⟨oneData, oneCalls⟩ := runNode_projection graph weights total position.val b target (graph.roots.get position) started
      simp only [List.get_eq_getElem] at oneData oneCalls
      obtain ⟨laterData, laterCalls⟩ := ih current
      constructor
      · change (runRoots graph weights total b target rest current).data = _
        rw [laterData]
        dsimp [current]
        rw [oneData]
        rfl
      · change (runRoots graph weights total b target rest current).arithmetic = _
        rw [laterCalls]
        dsimp [current]
        rw [oneCalls, oneData]
        simp only [runRootsTrace, List.length_append, Nat.add_assoc]
        rfl

/-- The total is evaluated once. The second component records actual generic
arithmetic calls, including these initial n additions. -/
def runAll (graph : DAG n) (weights : Channel n → W) (b : ℕ) (target : Channel n) : W × State n W :=
  let cached := cacheTotal weights
  (cached.1, runRoots graph weights cached.1 b target (List.finRange graph.roots.length)
    ⟨⟨((fun _ => 0), 0), ForestCursorDescriptors.initial, none⟩, 0, cached.2.length⟩)

theorem runAll_projection (graph : DAG n) (weights : Channel n → W) (b : ℕ) (target : Channel n) :
    (runAll graph weights b target).2.data = (runGlobal graph weights b target).2.1 ∧
    (runAll graph weights b target).2.arithmetic =
      (runGlobal graph weights b target).1.2.length + (runGlobal graph weights b target).2.2.length := by
  exact runRoots_projection graph weights (cacheTotal weights).1 b target (List.finRange graph.roots.length)
    ⟨⟨((fun _ => 0), 0), ForestCursorDescriptors.initial, none⟩, 0, (cacheTotal weights).2.length⟩

/-- All direct-root guard arithmetic, feasible comparisons and the once-only
total computation fit the source-incidence bound. Indexed Boolean input access
and the output witness have their independent operation contracts. -/
theorem runAll_arithmetic_bound (graph : DAG n) (forest : graph.FormulaForest)
    (weights : Channel n → W) (b : ℕ) (target : Channel n) :
    (runAll graph weights b target).2.arithmetic ≤
      n + 8 * (graph.roots.length + graph.childIncidences) + 4 * graph.guardIncidences := by
  rw [(runAll_projection graph weights b target).2]
  exact global_arithmetic_bound graph forest weights b target

end Controller.Cost.ForestWeightedDirect
