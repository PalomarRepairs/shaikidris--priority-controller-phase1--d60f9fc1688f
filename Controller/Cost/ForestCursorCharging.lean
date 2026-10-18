module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestCursorRoot
public import Controller.Cost.ForestNodeVisits

@[expose] public section

/-!
# Source cursor execution charged to forest incidences

The operation count follows the actual emitted source traversal. Its bounds
are transferred to the ticks of the physical root execution. Persistent record
construction, shared caller initialization and weighted arithmetic are separate
contracts.
-/
namespace Controller.Cost.ForestCursorCharging

open Controller.Decoder Controller.Decoder.DAG Controller.Cost.ForestCursorTraversal
open Controller.Cost.ForestCursorRoot Controller.Cost.ForestGuardSchedule
open Controller.Cost.GateProgram Controller.Cost.ForestCounter Controller.Cost.ForestCursorProgram
open Controller.Cost.ForestCursorExecution

/-- Exact source operation count, without constructing a runtime route list. -/
def operationBudget (graph : DAG n) (node : Fin graph.nodeCount) : ℕ :=
  match graph.node node with
  | .zero | .liveAnd _ _ => 1
  | .input _ => 2
  | .disj refs => 1 + (refs.map fun child => 2 + operationBudget graph (graph.childIndex node child)).sum
  | .guard child labels => 3 + 2 * labels.length + operationBudget graph (graph.childIndex node child)
termination_by node.val
decreasing_by all_goals exact graph.childIndex_lt _ _

theorem cursor_length (graph : DAG n) (node : Fin graph.nodeCount) (route : LeafRoute) :
    (cursorOps graph node route).length = operationBudget graph node := by
  have claim : ∀ rank : ℕ, ∀ current : Fin graph.nodeCount, current.val = rank →
      ∀ route, (cursorOps graph current route).length = operationBudget graph current := by
    intro rank
    induction rank using Nat.strong_induction_on with
    | h rank ih =>
      intro current equal route
      rw [cursorOps, operationBudget]
      cases equation : graph.node current with
      | zero => simp
      | input head => simp
      | liveAnd left right => simp
      | guard child labels =>
          have below := ih (graph.childIndex current child).val
            (by have earlier := graph.childIndex_lt current child; omega)
            (graph.childIndex current child) rfl (0 :: route)
          simp only [List.length_cons, List.length_append, List.length_map, List.length_reverse,
            List.length_finRange, List.length_nil, below]
          omega
      | disj refs =>
          have counts : ((List.finRange refs.length).map fun position =>
              2 + (cursorOps graph (graph.childIndex current (refs.get position)) (position.val :: route)).length) =
              refs.map (fun child => 2 + operationBudget graph (graph.childIndex current child)) := by
            calc
              _ = (List.finRange refs.length).map (fun position =>
                  2 + operationBudget graph (graph.childIndex current (refs.get position))) := by
                apply List.map_congr_left
                intro position present
                rw [ih (graph.childIndex current (refs.get position)).val
                  (by have earlier := graph.childIndex_lt current (refs.get position); omega)
                  (graph.childIndex current (refs.get position)) rfl]
              _ = _ := by
                simpa only [List.map_map, Function.comp_def] using
                  congrArg (List.map (fun child => 2 + operationBudget graph (graph.childIndex current child)))
                    (List.map_get_finRange refs)
          simp only [List.length_cons, List.length_flatMap, List.length_append,
            List.length_singleton, List.length_nil, Nat.zero_add] 
          have same : ((List.finRange refs.length).map fun position =>
              (1 + (cursorOps graph (graph.childIndex current (refs.get position)) (position.val :: route)).length) + 1) =
              (List.finRange refs.length).map (fun position =>
                2 + (cursorOps graph (graph.childIndex current (refs.get position)) (position.val :: route)).length) := by
            apply List.map_congr_left
            intro position present
            omega
          simp only [Nat.add_assoc] at same ⊢
          rw [same, counts]
          omega
  exact claim node.val node rfl route

private theorem map_sum_bound (items : List α) (first second : α → ℕ)
    (bound : ∀ item ∈ items, first item ≤ second item) :
    (items.map first).sum ≤ (items.map second).sum := by
  induction items with
  | nil => simp
  | cons item rest ih =>
      have head := bound item List.mem_cons_self
      have tail := ih (fun current present => bound current (List.mem_cons_of_mem item present))
      simp only [List.map_cons, List.sum_cons]
      omega

private theorem sum_budget (items : List α) (nodes guards : α → ℕ) :
    (items.map fun item => 4 * nodes item + guards item).sum =
      4 * (items.map nodes).sum + (items.map guards).sum := by
  induction items with
  | nil => simp
  | cons item rest ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      omega

/-- Two navigation operations are charged to the incoming position of each
child. The spare two units make the bound compositional across source branches. -/
theorem operationBudget_bound (graph : DAG n) (node : Fin graph.nodeCount) :
    operationBudget graph node + 2 ≤
      4 * (ForestNodeVisits.walkNodes graph node).length + (walkEvents graph node).length := by
  have claim : ∀ rank : ℕ, ∀ current : Fin graph.nodeCount, current.val = rank →
      operationBudget graph current + 2 ≤
        4 * (ForestNodeVisits.walkNodes graph current).length + (walkEvents graph current).length := by
    intro rank
    induction rank using Nat.strong_induction_on with
    | h rank ih =>
      intro current equal
      have below : ∀ child : Fin current.val,
          operationBudget graph (graph.childIndex current child) + 2 ≤
            4 * (ForestNodeVisits.walkNodes graph (graph.childIndex current child)).length +
              (walkEvents graph (graph.childIndex current child)).length := by
        intro child
        exact ih child.val (by have earlier := graph.childIndex_lt current child; omega)
          (graph.childIndex current child) rfl
      rw [operationBudget, ForestNodeVisits.walkNodes, walkEvents]
      cases equation : graph.node current with
      | zero => simp [Gate.children]
      | input head => simp [Gate.children]
      | liveAnd left right =>
          simp only [Gate.children, List.length_cons]
          omega
      | guard child labels =>
          have bounded := below child
          simp only [Gate.children, List.flatMap_cons, List.flatMap_nil, List.append_nil,
            List.length_cons, List.length_append, List.length_map, List.length_reverse]
          omega
      | disj refs =>
          have bounded := map_sum_bound refs
            (fun child => 2 + operationBudget graph (graph.childIndex current child))
            (fun child => 4 * (ForestNodeVisits.walkNodes graph (graph.childIndex current child)).length +
              (walkEvents graph (graph.childIndex current child)).length)
            (fun child present => by have currentBound := below child; omega)
          rw [sum_budget] at bounded
          simp only [Gate.children, List.length_cons, List.length_flatMap]
          omega
  exact claim node.val node rfl

/-- All declared roots, counted by position, share a linear operation budget. -/
def allRootBudget (graph : DAG n) : ℕ := (graph.roots.map (operationBudget graph)).sum

theorem all_root_budget_bound (graph : DAG n) (forest : graph.FormulaForest) :
    allRootBudget graph ≤ 4 * (graph.roots.length + graph.childIncidences) + 2 * graph.guardIncidences := by
  have bounded := map_sum_bound graph.roots (operationBudget graph)
    (fun root => 4 * (ForestNodeVisits.walkNodes graph root).length + (walkEvents graph root).length)
    (fun root present => by have currentBound := operationBudget_bound graph root; omega)
  rw [sum_budget] at bounded
  have nodes := ForestNodeVisits.root_node_count_le graph forest
  have guards := ForestGuardVisits.root_event_count_le graph forest
  simp only [ForestNodeVisits.rootNodes, rootEvents, List.length_flatMap] at nodes guards
  unfold allRootBudget
  omega

/-- This transfer consumes a bound on actual physical execution ticks. It does
not assert that the budget alone is a machine execution. -/
theorem executed_root_ticks (graph : DAG n) (root : Fin graph.nodeCount) (ticks : ℕ)
    (executionBound : ticks ≤ 20 * (cursorOps graph root []).length) :
    ticks ≤ 80 * (ForestNodeVisits.walkNodes graph root).length + 20 * (walkEvents graph root).length := by
  rw [cursor_length] at executionBound
  have budget := operationBudget_bound graph root
  omega

/-- For actual per-root executions with the proven root bound, repeated
terminal roots and child positions are included in the total tick charge. -/
theorem executed_all_root_ticks (graph : DAG n) (forest : graph.FormulaForest)
    (ticks : Fin graph.roots.length → ℕ)
    (executionBound : ∀ position, ticks position ≤
      20 * (cursorOps graph (graph.roots.get position) []).length) :
    ((List.finRange graph.roots.length).map ticks).sum ≤
      80 * (graph.roots.length + graph.childIncidences) + 40 * graph.guardIncidences := by
  have bounded := map_sum_bound (List.finRange graph.roots.length) ticks
    (fun position => 20 * operationBudget graph (graph.roots.get position))
    (fun position present => by simpa only [cursor_length] using executionBound position)
  have total : ((List.finRange graph.roots.length).map
      (fun position => 20 * operationBudget graph (graph.roots.get position))).sum =
      20 * allRootBudget graph := by
    have mapped : ((List.finRange graph.roots.length).map
        (fun position => operationBudget graph (graph.roots.get position))) = graph.roots.map (operationBudget graph) := by
      simpa only [List.map_map, Function.comp_def] using
        congrArg (List.map (operationBudget graph)) (List.map_get_finRange graph.roots)
    have scaled : ∀ items : List (Fin graph.roots.length),
        (items.map (fun position => 20 * operationBudget graph (graph.roots.get position))).sum =
          20 * (items.map (fun position => operationBudget graph (graph.roots.get position))).sum := by
      intro items
      induction items with
      | nil => simp
      | cons position rest ih => simp only [List.map_cons, List.sum_cons, ih]; omega
    rw [scaled, mapped]
    rfl
  rw [total] at bounded
  have budget := all_root_budget_bound graph forest
  omega

/-- The actual source-root machine execution has the incidence-charged tick
bound, while retaining its physical invariant and production cursor result. -/
theorem root_execution_charged (program : Program width 4) (graph : DAG n)
    (root : Fin graph.nodeCount) (records : GraphRecords width initial graph)
    (routes : RouteDescriptors width initial) (layout : SelectorLayout n)
    (readonly : ReadonlyLayout graph records routes layout)
    (index : OccurrenceIndex graph) (b : ℕ) (target : Channel n)
    (state : RuntimeModel width n) (held : RuntimeStored graph records routes layout state)
    (capacity : ∀ channel, state.counters channel + (walkEvents graph root).length + 1 < 2 ^ width)
    (heapFits : initial.size ≤ 2 ^ width) (oneFits : 1 < 2 ^ width)
    (indexed : RootIndex graph root routes index)
    (base : ℕ) (address loaded temporary : Word width) (output : List (Word width))
    (fits : base + (rootCode graph records layout index b target base root).length < 2 ^ width)
    (block : BlockAt program base (rootCode graph records layout index b target base root)) :
    ∃ finalAddress finalLoaded finalTemporary : Word width, ∃ ticks peak : ℕ,
      Execution program
        ((counterState state.heap base address loaded temporary).frame state.navigation output)
        ((counterState (runModel layout index b target state (cursorOps graph root [])).heap
          (base + (rootCode graph records layout index b target base root).length)
          finalAddress finalLoaded finalTemporary).frame state.navigation output)
        ticks peak ∧ ticks ≤ 80 * (ForestNodeVisits.walkNodes graph root).length + 20 * (walkEvents graph root).length ∧
        peak ≤ 6 + state.heap.size + state.navigation.length + (cursorOps graph root []).length + output.length ∧
        RuntimeStored graph records routes layout (runModel layout index b target state (cursorOps graph root [])) ∧
        (runModel layout index b target state (cursorOps graph root [])).counters = state.counters ∧
        modelProjection routes (runModel layout index b target state (cursorOps graph root [])) =
          graph.foldLeafCursor (fun _ => 0) root [] (state.counters, 0)
            ((state.selected.map routes.route).map fun route => (route, 0)) (keepBestRoute b target 0) := by
  obtain ⟨fa, fl, ft, ticks, peak, execution, tickBound, spaceBound, finalHeld, countersRestored, result⟩ :=
    ForestCursorRoot.root_execution program graph root records routes layout readonly index b target state held
      capacity heapFits oneFits indexed base address loaded temporary output fits block
  exact ⟨fa, fl, ft, ticks, peak, execution, executed_root_ticks graph root ticks tickBound,
    spaceBound, finalHeld, countersRestored, result⟩

end Controller.Cost.ForestCursorCharging
