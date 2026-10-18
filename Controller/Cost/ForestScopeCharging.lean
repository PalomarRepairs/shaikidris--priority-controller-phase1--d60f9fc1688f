module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestScopeMarkers
public import Controller.Cost.ForestCursorCalls
public import Controller.Cost.ForestGuardVisits

@[expose] public section

/-!
# All-root sparse scope counts

The exact unfolded label count is derived from production leaf-cursor callback
counts and generated guard events. It charges repeated terminal/root positions
and repeated guard labels. Touched-list clearing and bounded candidate search
are counted by their actual lists; these counts require separate instruction
execution and construction refinements before becoming RAM resource bounds.
-/
namespace Controller.Cost.ForestScopeCharging

open Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestScopeMarkers Controller.Cost.ForestCursorCalls
open Controller.Cost.ForestGuardSchedule
variable {n : ℕ}

private theorem sum_balance {A : Type*} (items : List A) (labels calls events : A → ℕ)
    (balance : ∀ item ∈ items, 2 * labels item = 2 * calls item + events item) :
    2 * (items.map labels).sum = 2 * (items.map calls).sum + (items.map events).sum := by
  induction items with
  | nil => simp
  | cons item rest ih =>
      have head := balance item (by simp)
      have tail := ih (by intro current present; exact balance current (by simp [present]))
      simp only [List.map_cons, List.sum_cons]
      omega

/-- Each input contributes one scope label and each guarded label contributes
one entry and one exit event. -/
theorem labels_balance (graph : DAG n) (guarded : graph.Guarded) :
    ∀ node : Fin graph.nodeCount,
    2 * (scopeLabels graph node).length = 2 * leafCalls graph node + (walkEvents graph node).length := by
  have claim : ∀ rank : ℕ, ∀ node : Fin graph.nodeCount, node.val = rank →
      2 * (scopeLabels graph node).length = 2 * leafCalls graph node + (walkEvents graph node).length := by
    intro rank
    induction rank using Nat.strong_induction_on with
    | h rank ih =>
      intro node value
      have childBalance : ∀ child : Fin node.val,
          2 * (scopeLabels graph (graph.childIndex node child)).length =
            2 * leafCalls graph (graph.childIndex node child) +
              (walkEvents graph (graph.childIndex node child)).length := by
        intro child
        exact ih child.val (by have earlier := graph.childIndex_lt node child; omega)
          (graph.childIndex node child) rfl
      rw [scopeLabels.eq_def, leafCalls.eq_def, walkEvents.eq_def]
      cases equation : graph.node node with
      | zero => simp [Gate.directChannels, Gate.children]
      | input head => simp [Gate.directChannels, Gate.children]
      | liveAnd left right =>
          have impossible := guarded node
          simp [Gate.IsGuarded, Gate.isLiveAnd, equation] at impossible
      | disj refs =>
          simp only [Gate.directChannels, Gate.children, List.nil_append, List.length_flatMap]
          exact sum_balance refs
            (fun child => (scopeLabels graph (graph.childIndex node child)).length)
            (fun child => leafCalls graph (graph.childIndex node child))
            (fun child => (walkEvents graph (graph.childIndex node child)).length)
            (by intro child present; exact childBalance child)
      | guard child labels =>
          have balance := childBalance child
          simp only [Gate.directChannels, Gate.children, List.flatMap_cons, List.flatMap_nil,
            List.append_nil, List.length_append, List.length_map, List.length_reverse]
          omega
  intro node
  exact claim node.val node rfl

def rootLabels (graph : DAG n) : List (Channel n) := graph.roots.flatMap (scopeLabels graph)

theorem roots_balance (graph : DAG n) (guarded : graph.Guarded) :
    2 * (rootLabels graph).length = 2 * rootCalls graph + (rootEvents graph).length := by
  simp only [rootLabels, rootCalls, rootEvents, List.length_flatMap]
  exact sum_balance graph.roots
    (fun node => (scopeLabels graph node).length) (leafCalls graph)
    (fun node => (walkEvents graph node).length)
    (by intro node present; exact labels_balance graph guarded node)

/-- Forest internal-use uniqueness and positional terminal charging yield a
linear all-root label count; no declared-channel factor occurs. -/
theorem rootLabels_length_le (graph : DAG n) (guarded : graph.Guarded)
    (forest : graph.FormulaForest) :
    (rootLabels graph).length ≤ graph.roots.length + graph.childIncidences + graph.guardIncidences := by
  have balance := roots_balance graph guarded
  have calls := rootCalls_le_occurrences graph forest
  have guards := ForestGuardVisits.root_event_count_le graph forest
  omega

private theorem sum_le {A : Type*} (items : List A) (first second : A → ℕ)
    (bound : ∀ item ∈ items, first item ≤ second item) :
    (items.map first).sum ≤ (items.map second).sum := by
  induction items with
  | nil => simp
  | cons item rest ih =>
      have head := bound item (by simp)
      have tail := ih (by intro current present; exact bound current (by simp [present]))
      simp only [List.map_cons, List.sum_cons]
      omega

/-- Total touched IDs across independently restored root queries. -/
def touchedCount (graph : DAG n) : ℕ :=
  (graph.roots.map fun node => (touchAll empty (scopeLabels graph node)).touched.length).sum

theorem touchedCount_le_labels (graph : DAG n) : touchedCount graph ≤ (rootLabels graph).length := by
  have bound := sum_le graph.roots
    (fun node => (touchAll empty (scopeLabels graph node)).touched.length)
    (fun node => (scopeLabels graph node).length) (by
      intro node present
      simpa only [ForestScopeMarkers.empty, List.length_nil, Nat.zero_add] using
        touchAll_length_le empty (scopeLabels graph node))
  simpa only [touchedCount, rootLabels, List.length_flatMap] using bound

def candidateCount (graph : DAG n) : ℕ :=
  (graph.roots.map fun node => (graph.unmarkedCandidates node).length).sum

private theorem sum_add_one {A : Type*} (items : List A) (count : A → ℕ) :
    (items.map fun item => count item + 1).sum = (items.map count).sum + items.length := by
  induction items with
  | nil => simp
  | cons item rest ih => simp only [List.map_cons, List.sum_cons, List.length_cons]; omega

theorem candidateCount_le_touched (graph : DAG n) :
    candidateCount graph ≤ touchedCount graph + graph.roots.length := by
  have bound := sum_le graph.roots
    (fun node => (graph.unmarkedCandidates node).length)
    (fun node => (touchAll empty (scopeLabels graph node)).touched.length + 1)
    (by intro node present; exact candidates_le_touched graph node)
  rw [sum_add_one] at bound
  exact bound

theorem candidateCount_linear (graph : DAG n) (guarded : graph.Guarded)
    (forest : graph.FormulaForest) :
    candidateCount graph ≤ 2 * graph.roots.length + graph.childIncidences + graph.guardIncidences := by
  have candidates := candidateCount_le_touched graph
  have touched := touchedCount_le_labels graph
  have labels := rootLabels_length_le graph guarded forest
  omega

/-- The shared all-root budget is the sum of counts from the natural-weight
production API, for arbitrary per-root initial counter states. -/
theorem natural_root_callback_count (graph : DAG n) (weights : Channel n → ℕ)
    (states : Fin graph.nodeCount → WeightedCounters n) :
    (graph.roots.map fun node =>
      (graph.foldLeafCursor weights node [] (states node) 0 (fun _ _ _ count => count + 1)).2).sum =
      rootCalls graph := by
  unfold rootCalls
  apply congrArg List.sum
  apply List.map_congr_left
  intro node present
  simpa only [Nat.zero_add] using natural_cursor_count graph weights node [] (states node) 0

/-- The same count holds for the generic ordered additive-group production API;
no encoded-weight arithmetic cost is inferred from this equality. -/
theorem generic_root_callback_count {W : Type} [AddCommGroup W] [LinearOrder W]
    [IsOrderedAddMonoid W] (graph : DAG n) (weights : Channel n → W)
    (states : Fin graph.nodeCount → GuardCounters n × W) :
    (graph.roots.map fun node =>
      (graph.foldGenericLeafCursor weights node [] (states node) 0
        (fun _ _ _ count => count + 1)).2).sum = rootCalls graph := by
  unfold rootCalls
  apply congrArg List.sum
  apply List.map_congr_left
  intro node present
  simpa only [Nat.zero_add] using generic_cursor_count graph weights node [] (states node) 0

end Controller.Cost.ForestScopeCharging
