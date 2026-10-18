module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestNodeVisits
public import Controller.Decoder.ForestGeneric

@[expose] public section

/-!
# Production leaf-cursor callback counts

The counting accumulator is passed to the actual cursor fold. Counts include
infeasible input leaves, which still invoke the selector callback. Positional
multiplicity is preserved. Callback counts are distinct from instruction costs,
weight representation, and reconstruction costs.
-/
namespace Controller.Cost.ForestCursorCalls

open Controller.Decoder Controller.Decoder.DAG
variable {n : ℕ}

/-- The number of callback invocations in an unfolded cursor query. -/
def leafCalls (graph : DAG n) (node : Fin graph.nodeCount) : ℕ :=
  match graph.node node with
  | .zero => 0
  | .input _ => 1
  | .disj refs => (refs.map fun child => leafCalls graph (graph.childIndex node child)).sum
  | .guard child _ => leafCalls graph (graph.childIndex node child)
  | .liveAnd _ _ => 0
termination_by node.val
decreasing_by all_goals exact graph.childIndex_lt _ _

private theorem foldl_count {S B : Type*} (items : List B)
    (step : S × ℕ → B → S × ℕ) (count : B → ℕ)
    (adds : ∀ state item, (step state item).2 = state.2 + count item)
    (initial : S × ℕ) :
    (items.foldl step initial).2 = initial.2 + (items.map count).sum := by
  induction items generalizing initial with
  | nil => simp
  | cons item rest ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [ih, adds]
      omega

private theorem map_sum_le {B : Type*} (items : List B) (first second : B → ℕ)
    (bound : ∀ item ∈ items, first item ≤ second item) :
    (items.map first).sum ≤ (items.map second).sum := by
  induction items with
  | nil => simp
  | cons item rest ih =>
      have head := bound item (by simp)
      have tail := ih (by intro current present; exact bound current (by simp [present]))
      simp only [List.map_cons, List.sum_cons]
      omega

/-- Every invoked leaf is charged to a generated node visit. This also holds for
DAGs with live AND gates: the production cursor skips their children. -/
theorem leafCalls_le_nodes (graph : DAG n) : ∀ node : Fin graph.nodeCount,
    leafCalls graph node ≤ (ForestNodeVisits.walkNodes graph node).length := by
  have claim : ∀ rank : ℕ, ∀ node : Fin graph.nodeCount, node.val = rank →
      leafCalls graph node ≤ (ForestNodeVisits.walkNodes graph node).length := by
    intro rank
    induction rank using Nat.strong_induction_on with
    | h rank ih =>
      intro node value
      have childBound : ∀ child : Fin node.val,
          leafCalls graph (graph.childIndex node child) ≤
            (ForestNodeVisits.walkNodes graph (graph.childIndex node child)).length := by
        intro child
        exact ih child.val (by have earlier := graph.childIndex_lt node child; omega)
          (graph.childIndex node child) rfl
      rw [leafCalls.eq_def, ForestNodeVisits.walkNodes.eq_def]
      cases equation : graph.node node with
      | zero => simp [Gate.children]
      | input head => simp [Gate.children]
      | liveAnd left right => exact Nat.zero_le _
      | guard child labels =>
          simpa only [Gate.children, List.flatMap_cons, List.flatMap_nil,
            List.append_nil, List.length_cons] using Nat.le_succ_of_le (childBound child)
      | disj refs =>
          have bound := map_sum_le refs
            (fun child => leafCalls graph (graph.childIndex node child))
            (fun child => (ForestNodeVisits.walkNodes graph (graph.childIndex node child)).length)
            (by intro child present; exact childBound child)
          simpa only [Gate.children, List.length_cons, List.length_flatMap] using
            Nat.le_succ_of_le bound
  intro node
  exact claim node.val node rfl

/-- All-root callback count, including repeated terminal root positions. -/
def rootCalls (graph : DAG n) : ℕ := (graph.roots.map (leafCalls graph)).sum

theorem rootCalls_le_occurrences (graph : DAG n) (forest : graph.FormulaForest) :
    rootCalls graph ≤ graph.roots.length + graph.childIncidences := by
  have bound := map_sum_le graph.roots (leafCalls graph)
    (fun node => (ForestNodeVisits.walkNodes graph node).length)
    (by intro node present; exact leafCalls_le_nodes graph node)
  have nodes := ForestNodeVisits.root_node_count_le graph forest
  have total : (graph.roots.map (fun node => (ForestNodeVisits.walkNodes graph node).length)).sum =
      (ForestNodeVisits.rootNodes graph).length := by
    simp only [ForestNodeVisits.rootNodes, List.length_flatMap]
  exact le_trans (by simpa only [rootCalls, total] using bound) nodes

/-- Exact callback count for the executable natural-weight cursor, for every initial
counter state. No feasibility or nonnegative-weight premise is required. -/
theorem natural_cursor_count (graph : DAG n) (weights : Channel n → ℕ) :
    ∀ (node : Fin graph.nodeCount) (route : LeafRoute)
      (counters : WeightedCounters n) (initial : ℕ),
    (graph.foldLeafCursor weights node route counters initial
      (fun _ _ _ count => count + 1)).2 = initial + leafCalls graph node := by
  have claim : ∀ rank : ℕ, ∀ node : Fin graph.nodeCount, node.val = rank →
      ∀ (route : LeafRoute) (counters : WeightedCounters n) (initial : ℕ),
      (graph.foldLeafCursor weights node route counters initial
        (fun _ _ _ count => count + 1)).2 = initial + leafCalls graph node := by
    intro rank
    induction rank using Nat.strong_induction_on with
    | h rank ih =>
      intro node value route counters initial
      have childCount : ∀ (child : Fin node.val) route counters initial,
          (graph.foldLeafCursor weights (graph.childIndex node child) route counters initial
            (fun _ _ _ count => count + 1)).2 =
          initial + leafCalls graph (graph.childIndex node child) := by
        intro child route counters initial
        exact ih child.val (by have earlier := graph.childIndex_lt node child; omega)
          (graph.childIndex node child) rfl route counters initial
      rw [foldLeafCursor.eq_def, leafCalls.eq_def]
      cases equation : graph.node node with
      | zero => simp
      | input head => simp
      | liveAnd left right => simp
      | guard child labels => exact childCount child _ _ initial
      | disj refs =>
          simp only []
          rw [foldl_count _ _
            (fun position : Fin refs.length => leafCalls graph (graph.childIndex node (refs.get position)))
            (by intro state position; exact childCount (refs.get position) _ state.1 state.2)]
          congr 1
          rw [← List.ofFn_eq_map]
          exact congrArg List.sum (List.ofFn_getElem_eq_map refs
            (fun child => leafCalls graph (graph.childIndex node child)))
  intro node route counters initial
  exact claim node.val node rfl route counters initial


/-- Instrumenting an arbitrary callback preserves its accumulator result. -/
theorem natural_cursor_instrument {A : Type*} (graph : DAG n) (weights : Channel n → ℕ)
    (node : Fin graph.nodeCount) (route : LeafRoute) (counters : WeightedCounters n)
    (initial : A) (calls : ℕ)
    (visit : LeafRoute → Channel n → (WeightedCounters n) → A → A) :
    graph.foldLeafCursor weights node route counters initial visit =
      let result := graph.foldLeafCursor weights node route counters (initial, calls)
        (fun path head state previous => (visit path head state previous.1, previous.2 + 1))
      (result.1, result.2.1) := by
  rw [foldLeafCursor_eq_fold, foldLeafCursor_eq_fold]
  exact foldLeafRoutes_map graph weights node counters (initial, calls)
    (fun path head state previous =>
      (visit (path.reverse ++ route) head state previous.1, previous.2 + 1))
    (fun path head state previous => visit (path.reverse ++ route) head state previous)
    Prod.fst (by intros; rfl)

/-- The second coordinate of an instrumented production cursor counts all actual
callback invocations, independently of the callback's accumulator result. -/
theorem natural_cursor_instrument_count {A : Type*} (graph : DAG n)
    (weights : Channel n → ℕ) (node : Fin graph.nodeCount) (route : LeafRoute)
    (counters : WeightedCounters n) (initial : A) (calls : ℕ)
    (visit : LeafRoute → Channel n → (WeightedCounters n) → A → A) :
    (graph.foldLeafCursor weights node route counters (initial, calls)
      (fun path head state previous => (visit path head state previous.1, previous.2 + 1))).2.2 =
      calls + leafCalls graph node := by
  have projected :
      graph.foldLeafCursor weights node route counters calls (fun _ _ _ previous => previous + 1) =
        let result := graph.foldLeafCursor weights node route counters (initial, calls)
          (fun path head state previous => (visit path head state previous.1, previous.2 + 1))
        (result.1, result.2.2) := by
    rw [foldLeafCursor_eq_fold, foldLeafCursor_eq_fold]
    exact foldLeafRoutes_map graph weights node counters (initial, calls)
      (fun path head state previous =>
        (visit (path.reverse ++ route) head state previous.1, previous.2 + 1))
      (fun _ _ _ previous => previous + 1) Prod.snd (by intros; rfl)
  have same := congrArg (fun result => result.2) projected
  rw [← same]
  exact natural_cursor_count graph weights node route counters calls

variable {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]

/-- Exact callback count for the executable generic cursor, for every initial
counter state. No feasibility or nonnegative-weight premise is required. -/
theorem generic_cursor_count (graph : DAG n) (weights : Channel n → W) :
    ∀ (node : Fin graph.nodeCount) (route : LeafRoute)
      (counters : GuardCounters n × W) (initial : ℕ),
    (graph.foldGenericLeafCursor weights node route counters initial
      (fun _ _ _ count => count + 1)).2 = initial + leafCalls graph node := by
  have claim : ∀ rank : ℕ, ∀ node : Fin graph.nodeCount, node.val = rank →
      ∀ (route : LeafRoute) (counters : GuardCounters n × W) (initial : ℕ),
      (graph.foldGenericLeafCursor weights node route counters initial
        (fun _ _ _ count => count + 1)).2 = initial + leafCalls graph node := by
    intro rank
    induction rank using Nat.strong_induction_on with
    | h rank ih =>
      intro node value route counters initial
      have childCount : ∀ (child : Fin node.val) route counters initial,
          (graph.foldGenericLeafCursor weights (graph.childIndex node child) route counters initial
            (fun _ _ _ count => count + 1)).2 =
          initial + leafCalls graph (graph.childIndex node child) := by
        intro child route counters initial
        exact ih child.val (by have earlier := graph.childIndex_lt node child; omega)
          (graph.childIndex node child) rfl route counters initial
      rw [foldGenericLeafCursor.eq_def, leafCalls.eq_def]
      cases equation : graph.node node with
      | zero => simp
      | input head => simp
      | liveAnd left right => simp
      | guard child labels => exact childCount child _ _ initial
      | disj refs =>
          simp only []
          rw [foldl_count _ _
            (fun position : Fin refs.length => leafCalls graph (graph.childIndex node (refs.get position)))
            (by intro state position; exact childCount (refs.get position) _ state.1 state.2)]
          congr 1
          rw [← List.ofFn_eq_map]
          exact congrArg List.sum (List.ofFn_getElem_eq_map refs
            (fun child => leafCalls graph (graph.childIndex node child)))
  intro node route counters initial
  exact claim node.val node rfl route counters initial

/-- Instrumenting an arbitrary callback preserves its accumulator result. -/
theorem generic_cursor_instrument {A : Type*} (graph : DAG n) (weights : Channel n → W)
    (node : Fin graph.nodeCount) (route : LeafRoute) (counters : GuardCounters n × W)
    (initial : A) (calls : ℕ)
    (visit : LeafRoute → Channel n → (GuardCounters n × W) → A → A) :
    graph.foldGenericLeafCursor weights node route counters initial visit =
      let result := graph.foldGenericLeafCursor weights node route counters (initial, calls)
        (fun path head state previous => (visit path head state previous.1, previous.2 + 1))
      (result.1, result.2.1) := by
  rw [foldGenericLeafCursor_eq_fold, foldGenericLeafCursor_eq_fold]
  exact foldGenericLeafRoutes_map graph weights node counters (initial, calls)
    (fun path head state previous =>
      (visit (path.reverse ++ route) head state previous.1, previous.2 + 1))
    (fun path head state previous => visit (path.reverse ++ route) head state previous)
    Prod.fst (by intros; rfl)

/-- The second coordinate of an instrumented production cursor counts all actual
callback invocations, independently of the callback's accumulator result. -/
theorem generic_cursor_instrument_count {A : Type*} (graph : DAG n)
    (weights : Channel n → W) (node : Fin graph.nodeCount) (route : LeafRoute)
    (counters : GuardCounters n × W) (initial : A) (calls : ℕ)
    (visit : LeafRoute → Channel n → (GuardCounters n × W) → A → A) :
    (graph.foldGenericLeafCursor weights node route counters (initial, calls)
      (fun path head state previous => (visit path head state previous.1, previous.2 + 1))).2.2 =
      calls + leafCalls graph node := by
  have projected :
      graph.foldGenericLeafCursor weights node route counters calls (fun _ _ _ previous => previous + 1) =
        let result := graph.foldGenericLeafCursor weights node route counters (initial, calls)
          (fun path head state previous => (visit path head state previous.1, previous.2 + 1))
        (result.1, result.2.2) := by
    rw [foldGenericLeafCursor_eq_fold, foldGenericLeafCursor_eq_fold]
    exact foldGenericLeafRoutes_map graph weights node counters (initial, calls)
      (fun path head state previous =>
        (visit (path.reverse ++ route) head state previous.1, previous.2 + 1))
      (fun _ _ _ previous => previous + 1) Prod.snd (by intros; rfl)
  have same := congrArg (fun result => result.2) projected
  rw [← same]
  exact generic_cursor_count graph weights node route counters calls

end Controller.Cost.ForestCursorCalls
