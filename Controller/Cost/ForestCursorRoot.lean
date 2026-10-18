module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestCursorRun

@[expose] public section

/-!
# Composition of the source-rooted physical cursor

The source operation model retains the actual heap, path counters, selected
route pointer and live navigation stack. Emitted block offsets follow the same
source-derived list. Counter projections connect the physical refinement to the
checked balanced source guard trace; semantic projections remain separate from
instruction-resource claims.
-/
namespace Controller.Cost.ForestCursorRoot

open Controller.Decoder Controller.Decoder.DAG Controller.Cost.GateProgram
open Controller.Cost.ForestCounter Controller.Cost.ForestCursorProgram
open Controller.Cost.ForestCursorTraversal Controller.Cost.ForestCursorExecution
open Controller.Cost.ForestCursorSemantics Controller.Cost.ForestCursorRun
open Controller.Cost.ForestGuardSchedule Controller.Cost.ForestGuardSafety

/-- A concrete emitted prefix fixes the continuation's actual code address. -/
theorem emission_append (graph : DAG n) (records : GraphRecords width heap graph)
    (layout : SelectorLayout n) (index : OccurrenceIndex graph) (b : ℕ) (target : Channel n)
    (first rest : List (CursorOp n)) (base : ℕ) :
    emitOperations graph records layout index b target base (first ++ rest) =
      emitOperations graph records layout index b target base first ++
        emitOperations graph records layout index b target
          (base + (emitOperations graph records layout index b target base first).length) rest := by
  induction first generalizing base with
  | nil => simp [emitOperations]
  | cons operation tail ih =>
      simp only [List.cons_append, emitOperations, ih, List.length_append, List.append_assoc,
        Nat.add_assoc]

/-- Whole source coverage supplies both the actual prefix and its continuation. -/
theorem emission_coverage (program : Program width 4) (graph : DAG n)
    (records : GraphRecords width heap graph) (layout : SelectorLayout n)
    (index : OccurrenceIndex graph) (b : ℕ) (target : Channel n)
    (first rest : List (CursorOp n)) (base : ℕ)
    (block : BlockAt program base
      (emitOperations graph records layout index b target base (first ++ rest))) :
    BlockAt program base (emitOperations graph records layout index b target base first) ∧
    BlockAt program (base + (emitOperations graph records layout index b target base first).length)
      (emitOperations graph records layout index b target
        (base + (emitOperations graph records layout index b target base first).length) rest) := by
  rw [emission_append] at block
  exact ⟨BlockAt.prefix program base _ _ block, BlockAt.suffix program base _ _ block⟩

structure RuntimeModel (width n : ℕ) where
  heap : Array (Word width)
  counters : GuardCounters n
  selected : Option ℕ
  navigation : List (Word width)

/-- Deterministic data effects of the same actual operation blocks. Register
outputs are existential at physical block boundaries. -/
def modelStep (layout : SelectorLayout n) (index : OccurrenceIndex graph)
    (b : ℕ) (target : Channel n) (state : RuntimeModel width n) : CursorOp n → RuntimeModel width n
  | .node _ => state
  | .down _ position _ => { state with navigation := word width position :: state.navigation }
  | .up => { state with navigation := state.navigation.tail }
  | .enter _ _ channel => { state with
      heap := update width layout.counterOffset state.heap (.enter channel)
      counters := enterGuards state.counters [channel] }
  | .leave _ _ channel => { state with
      heap := update width layout.counterOffset state.heap (.leave channel)
      counters := leaveGuards state.counters [channel] }
  | .leaf _ route head => { state with
      heap := leafHeap width state.heap layout b target head state.counters state.selected (index.pointer route)
      selected := leafChoice b target head state.counters state.selected (index.pointer route) }

def runModel (layout : SelectorLayout n) (index : OccurrenceIndex graph)
    (b : ℕ) (target : Channel n) (state : RuntimeModel width n) (operations : List (CursorOp n)) :
    RuntimeModel width n := operations.foldl (modelStep layout index b target) state

/-- Source reads, navigation and leaf selection do not change path counters. -/
theorem model_counters (layout : SelectorLayout n) (index : OccurrenceIndex graph)
    (b : ℕ) (target : Channel n) (state : RuntimeModel width n) (operations : List (CursorOp n)) :
    (runModel layout index b target state operations).counters =
      runNatural state.counters (operations.flatMap guardProjection) := by
  induction operations generalizing state with
  | nil => rfl
  | cons operation rest ih =>
      rw [runModel, List.foldl_cons]
      change (runModel layout index b target (modelStep layout index b target state operation) rest).counters = _
      rw [ih]
      cases operation <;> simp only [guardProjection, List.flatMap_cons, List.nil_append,
        List.singleton_append, runNatural_cons, modelStep, naturalStep]

/-- The actual generated root model restores every initial path counter. This
uses source balancing, rather than assuming an arbitrary trace is safe. -/
theorem root_model_counters (graph : DAG n) (node : Fin graph.nodeCount)
    (layout : SelectorLayout n) (index : OccurrenceIndex graph)
    (b : ℕ) (target : Channel n) (state : RuntimeModel width n) :
    (runModel layout index b target state (cursorOps graph node [])).counters = state.counters := by
  rw [model_counters, cursor_guard_projection]
  exact (balanced_restore_positive (walk_balanced graph node) state.counters).1

/-- Only source-generated leaf routes require descriptor indices. This finite
contract does not quantify over all possible route lists. -/
def RootIndex (graph : DAG n) (root : Fin graph.nodeCount)
    (routes : RouteDescriptors width initial) (index : OccurrenceIndex graph) : Prop :=
  ∀ owner route head, CursorOp.leaf owner route head ∈ cursorOps graph root [] →
    routes.route (index.pointer route) = route ∧ index.pointer route ≤ routes.count ∧
      index.pointer route < 2 ^ width

def modelProjection (routes : RouteDescriptors width initial) (state : RuntimeModel width n) :
    CursorState n := ((state.counters, 0), (state.selected.map routes.route).map fun route => (route, 0))

/-- The data-effect model projects to the exact callback operation. -/
theorem model_step_projection (layout : SelectorLayout n) (index : OccurrenceIndex graph)
    (routes : RouteDescriptors width initial) (b : ℕ) (target : Channel n)
    (state : RuntimeModel width n) (operation : CursorOp n)
    (indexed : ∀ owner route head, operation = .leaf owner route head →
      routes.route (index.pointer route) = route) :
    modelProjection routes (modelStep layout index b target state operation) =
      cursorStep b target (modelProjection routes state) operation := by
  cases operation with
  | node owner => rfl
  | down owner position child => rfl
  | up => rfl
  | enter owner position channel =>
      simp only [modelProjection, modelStep, cursorStep, enter_zero]
  | leave owner position channel =>
      simp only [modelProjection, modelStep, cursorStep, leave_zero]
  | leaf owner route head =>
      have routeEq := indexed owner route head rfl
      simp only [modelProjection, modelStep, cursorStep]
      rw [keepBest_zero]
      by_cases feasible : state.counters head = 0 ∧ (b ≠ 1 ∨ state.counters target = 0)
      · cases selectedEq : state.selected <;> simp [leafChoice, feasible, selectedEq, routeEq]
      · have impossible : ¬(state.counters head = 0 ∧
          (b ≠ 1 ∨ state.counters target = 0) ∧ state.selected = none) := by tauto
        simp [leafChoice, feasible, impossible]

theorem model_projection_fold (layout : SelectorLayout n) (index : OccurrenceIndex graph)
    (routes : RouteDescriptors width initial) (b : ℕ) (target : Channel n)
    (state : RuntimeModel width n) (operations : List (CursorOp n))
    (indexed : ∀ owner route head, CursorOp.leaf owner route head ∈ operations →
      routes.route (index.pointer route) = route) :
    modelProjection routes (runModel layout index b target state operations) =
      operations.foldl (cursorStep b target) (modelProjection routes state) := by
  induction operations generalizing state with
  | nil => rfl
  | cons operation rest ih =>
      rw [runModel, List.foldl_cons]
      change modelProjection routes (runModel layout index b target
        (modelStep layout index b target state operation) rest) = _
      rw [ih (modelStep layout index b target state operation)
        (fun owner route head present => indexed owner route head (List.mem_cons_of_mem operation present))]
      rw [List.foldl_cons, model_step_projection layout index routes b target state operation
        (fun owner route head equal => indexed owner route head (by rw [equal]; exact List.mem_cons_self))]

/-- The actual source-root data model has the production cursor result. This
projection accompanies, rather than replaces, the physical execution theorem. -/
theorem root_model_result (graph : DAG n) (root : Fin graph.nodeCount)
    (layout : SelectorLayout n) (index : OccurrenceIndex graph)
    (routes : RouteDescriptors width initial) (b : ℕ) (target : Channel n)
    (state : RuntimeModel width n) (indexed : RootIndex graph root routes index) :
    modelProjection routes (runModel layout index b target state (cursorOps graph root [])) =
      graph.foldLeafCursor (fun _ => 0) root [] (state.counters, 0)
        ((state.selected.map routes.route).map fun route => (route, 0)) (keepBestRoute b target 0) := by
  rw [model_projection_fold layout index routes b target state _
    (fun owner route head present => (indexed owner route head present).1)]
  exact cursor_fold_correct graph root [] b target (modelProjection routes state)

def navigationStep (stack : List (Word width)) : CursorOp n → List (Word width)
  | .down _ position _ => word width position :: stack
  | .up => stack.tail
  | _ => stack

def runNavigation (stack : List (Word width)) (operations : List (CursorOp n)) : List (Word width) :=
  operations.foldl navigationStep stack

def NavigationSafe (stack : List (Word width)) : List (CursorOp n) → Prop
  | [] => True
  | operation :: rest =>
      (match operation with | .up => stack ≠ [] | _ => True) ∧
        NavigationSafe (navigationStep stack operation) rest

def NavNeutral : CursorOp n → Prop
  | .down _ _ _ | .up => False
  | _ => True

/-- A source navigation derivation keeps each actual pop under its matching
child-position push. Reads, guard operations and callbacks are neutral. -/
inductive NavBalanced : List (CursorOp n) → Prop
  | empty : NavBalanced []
  | neutral (operation : CursorOp n) (neutral : NavNeutral operation) : NavBalanced [operation]
  | append {first second} : NavBalanced first → NavBalanced second → NavBalanced (first ++ second)
  | child (owner position child : ℕ) {body} : NavBalanced body →
      NavBalanced (CursorOp.down owner position child :: body ++ [CursorOp.up])

theorem navigation_append (stack : List (Word width)) (first second : List (CursorOp n)) :
    runNavigation stack (first ++ second) = runNavigation (runNavigation stack first) second := by
  simp only [runNavigation, List.foldl_append]

theorem navigation_safe_append (stack : List (Word width)) (first second : List (CursorOp n)) :
    NavigationSafe stack (first ++ second) ↔
      NavigationSafe stack first ∧ NavigationSafe (runNavigation stack first) second := by
  induction first generalizing stack with
  | nil => simp [NavigationSafe, runNavigation]
  | cons operation rest ih =>
      simp only [List.cons_append, NavigationSafe, runNavigation, List.foldl_cons, ih, and_assoc]

/-- Every balanced source navigation trace restores the live stack and every
actual up operation sees a nonempty stack. -/
theorem navigation_balanced_safe {operations : List (CursorOp n)} (balanced : NavBalanced operations) :
    ∀ stack : List (Word width), runNavigation stack operations = stack ∧ NavigationSafe stack operations := by
  induction balanced with
  | empty => intro stack; exact ⟨rfl, trivial⟩
  | neutral operation neutral =>
      intro stack
      cases operation <;> simp_all [NavNeutral, runNavigation, navigationStep, NavigationSafe]
  | append first second firstIH secondIH =>
      intro stack
      obtain ⟨firstRestore, firstSafe⟩ := firstIH stack
      obtain ⟨secondRestore, secondSafe⟩ := secondIH stack
      refine ⟨by rw [navigation_append, firstRestore, secondRestore], ?_⟩
      rw [navigation_safe_append, firstRestore]
      exact ⟨firstSafe, secondSafe⟩
  | @child owner position child body balanced bodyIH =>
      intro stack
      obtain ⟨restores, safe⟩ := bodyIH (word width position :: stack)
      refine ⟨?_, ?_⟩
      · simp only [runNavigation, List.foldl_cons, navigationStep]
        change runNavigation (word width position :: stack) (_ ++ [CursorOp.up]) = stack
        rw [navigation_append, restores]
        rfl
      · change True ∧ NavigationSafe (word width position :: stack) (body ++ [CursorOp.up])
        refine ⟨trivial, ?_⟩
        rw [navigation_safe_append, restores]
        exact ⟨safe, by simp [NavigationSafe, navigationStep]⟩

theorem navbalanced_map (items : List α) (operation : α → CursorOp n)
    (neutral : ∀ item ∈ items, NavNeutral (operation item)) :
    NavBalanced (items.map operation) := by
  induction items with
  | nil => exact .empty
  | cons item rest ih =>
      exact .append (.neutral (operation item) (neutral item List.mem_cons_self))
        (ih (fun current present => neutral current (List.mem_cons_of_mem item present)))

theorem navbalanced_flatMap (items : List α) (body : α → List (CursorOp n))
    (balanced : ∀ item ∈ items, NavBalanced (body item)) : NavBalanced (items.flatMap body) := by
  induction items with
  | nil => exact .empty
  | cons item rest ih =>
      exact .append (balanced item List.mem_cons_self)
        (ih (fun current present => balanced current (List.mem_cons_of_mem item present)))

/-- Navigation validity is derived from actual decoder recursion, including
repeated child occurrences and shared terminals. -/
theorem cursor_navigation_balanced (graph : DAG n) (node : Fin graph.nodeCount)
    (routePrefix : LeafRoute) : NavBalanced (cursorOps graph node routePrefix) := by
  have claim : ∀ rank : ℕ, ∀ current : Fin graph.nodeCount, current.val = rank →
      ∀ routePrefix : LeafRoute, NavBalanced (cursorOps graph current routePrefix) := by
    intro rank
    induction rank using Nat.strong_induction_on with
    | h rank ih =>
      intro current equal route
      rw [cursorOps]
      refine .append (.neutral (.node current.val) (by trivial)) ?_
      cases equation : graph.node current with
      | zero => exact .empty
      | input head => exact .neutral (.leaf current.val route head) (by trivial)
      | liveAnd left right => exact .empty
      | disj refs =>
          apply navbalanced_flatMap
          intro position present
          exact .child current.val position.val (graph.childIndex current (refs.get position)).val
            (ih _ (by have earlier := graph.childIndex_lt current (refs.get position); omega) _ rfl _)
      | guard child labels =>
          have entered := navbalanced_map (List.finRange labels.length)
            (fun position => CursorOp.enter current.val position.val (labels.get position)) (by
              intro position present; trivial)
          have exited := navbalanced_map (List.finRange labels.length).reverse
            (fun position => CursorOp.leave current.val position.val (labels.get position)) (by
              intro position present; trivial)
          have descended := NavBalanced.child current.val 0 (graph.childIndex current child).val
            (ih (graph.childIndex current child).val
              (by have earlier := graph.childIndex_lt current child; omega) (graph.childIndex current child) rfl (0 :: route))
          simpa only [List.append_assoc, List.singleton_append] using
            NavBalanced.append (NavBalanced.append entered descended) exited
  exact claim node.val node rfl routePrefix

theorem source_navigation_safe (graph : DAG n) (node : Fin graph.nodeCount)
    (routePrefix : LeafRoute) (stack : List (Word width)) :
    runNavigation stack (cursorOps graph node routePrefix) = stack ∧
      NavigationSafe stack (cursorOps graph node routePrefix) :=
  navigation_balanced_safe (cursor_navigation_balanced graph node routePrefix) stack

/-- The guard representability condition is derived for the actual source
trace. Its natural counter bound includes the initial state and every incidence. -/
theorem source_guard_safe (graph : DAG n) (node : Fin graph.nodeCount)
    (counters : GuardCounters n)
    (capacity : ∀ channel, counters channel + (walkEvents graph node).length + 1 < 2 ^ width) :
    ForestGuardRefinement.Safe width counters (walkEvents graph node) := by
  apply ForestGuardRefinement.safe_of_positive_bound width counters _
    (balanced_restore_positive (walk_balanced graph node) counters).2 capacity

/-- Positional source witnesses exclude fallback addresses: every emitted read
belongs to a real node and a real incidence in its represented source record. -/
inductive SourceOperation (graph : DAG n) : CursorOp n → Prop
  | node (owner : Fin graph.nodeCount) : SourceOperation graph (.node owner.val)
  | down (owner : Fin graph.nodeCount) (position : Fin (graph.node owner).children.length) :
      SourceOperation graph (.down owner.val position.val ((graph.node owner).children.get position).val)
  | up : SourceOperation graph .up
  | enter (owner : Fin graph.nodeCount) (position : Fin (graph.node owner).guardLabels.length) :
      SourceOperation graph (.enter owner.val position.val ((graph.node owner).guardLabels.get position))
  | leave (owner : Fin graph.nodeCount) (position : Fin (graph.node owner).guardLabels.length) :
      SourceOperation graph (.leave owner.val position.val ((graph.node owner).guardLabels.get position))
  | leaf (owner : Fin graph.nodeCount) (route : LeafRoute) (head : Channel n)
      (equation : graph.node owner = .input head) :
      SourceOperation graph (.leaf owner.val route head)

/-- Actual recursion supplies all record-position witnesses, even when terminal
nodes are shared or a guard label is repeated at several positions. -/
theorem cursor_source_operations (graph : DAG n) (node : Fin graph.nodeCount)
    (routePrefix : LeafRoute) :
    ∀ operation ∈ cursorOps graph node routePrefix, SourceOperation graph operation := by
  have claim : ∀ rank : ℕ, ∀ current : Fin graph.nodeCount, current.val = rank →
      ∀ route : LeafRoute, ∀ operation ∈ cursorOps graph current route,
        SourceOperation graph operation := by
    intro rank
    induction rank using Nat.strong_induction_on with
    | h rank ih =>
      intro current equal route operation present
      rw [cursorOps] at present
      rcases List.mem_cons.mp present with same | present
      · subst operation; exact .node current
      · cases equation : graph.node current with
        | zero => simpa [equation] using present
        | liveAnd left right => simpa [equation] using present
        | input head =>
            simp only [equation, List.mem_singleton] at present
            subst operation
            exact .leaf current route head equation
        | disj refs =>
            simp only [equation, List.mem_flatMap] at present
            obtain ⟨position, _, present⟩ := present
            simp only [List.mem_append, List.mem_singleton] at present
            rcases present with (same | recursive) | same
            · subst operation
              let storedPosition : Fin (graph.node current).children.length :=
                ⟨position.val, by simpa [equation, Gate.children] using position.isLt⟩
              simpa [equation, Gate.children, storedPosition] using
                SourceOperation.down current storedPosition
            · exact ih _ (by have earlier := graph.childIndex_lt current (refs.get position); omega)
                _ rfl _ operation recursive
            · subst operation; exact .up
        | guard child labels =>
            simp only [equation, List.mem_append, List.mem_singleton, List.mem_map] at present
            rcases present with (((entered | descended) | recursive) | ascended) | exited
            · obtain ⟨position, _, same⟩ := entered
              subst operation
              let storedPosition : Fin (graph.node current).guardLabels.length :=
                ⟨position.val, by simpa [equation, Gate.guardLabels] using position.isLt⟩
              simpa [equation, Gate.guardLabels, storedPosition] using
                SourceOperation.enter current storedPosition
            · subst operation
              let storedPosition : Fin (graph.node current).children.length :=
                ⟨0, by simp [equation, Gate.children]⟩
              simpa [equation, Gate.children, storedPosition] using
                SourceOperation.down current storedPosition
            · exact ih _ (by have earlier := graph.childIndex_lt current child; omega)
                _ rfl _ operation recursive
            · subst operation; exact .up
            · obtain ⟨position, _, same⟩ := exited
              subst operation
              let storedPosition : Fin (graph.node current).guardLabels.length :=
                ⟨position.val, by simpa [equation, Gate.guardLabels] using position.isLt⟩
              simpa [equation, Gate.guardLabels, storedPosition] using
                SourceOperation.leave current storedPosition
  exact claim node.val node rfl routePrefix

/-- The operational data model carries exactly the actual pushed words, not a
separately postulated navigation trace. -/
theorem model_navigation (layout : SelectorLayout n) (index : OccurrenceIndex graph)
    (b : ℕ) (target : Channel n) (state : RuntimeModel width n)
    (operations : List (CursorOp n)) :
    (runModel layout index b target state operations).navigation =
      runNavigation state.navigation operations := by
  induction operations generalizing state with
  | nil => rfl
  | cons operation rest ih =>
      rw [runModel, List.foldl_cons]
      change (runModel layout index b target (modelStep layout index b target state operation) rest).navigation = _
      rw [ih]
      cases operation <;> rfl

/-- Generated traversal restores the physical navigation stack in the data
model, using the source matching proof rather than assuming its endpoint. -/
theorem root_model_navigation (graph : DAG n) (node : Fin graph.nodeCount)
    (layout : SelectorLayout n) (index : OccurrenceIndex graph)
    (b : ℕ) (target : Channel n) (state : RuntimeModel width n) :
    (runModel layout index b target state (cursorOps graph node [])).navigation = state.navigation := by
  rw [model_navigation]
  exact (source_navigation_safe graph node [] state.navigation).1

/-- The physical caller invariant is maintained at every operation boundary.
It rebases the same persistent record cells on the current heap. -/
structure RuntimeStored (graph : DAG n) (records : GraphRecords width initial graph)
    (routes : RouteDescriptors width initial) (layout : SelectorLayout n)
    (state : RuntimeModel width n) : Prop where
  counters : CountersStored state.heap layout.counterOffset state.counters
  selector : SelectorStored state.heap layout state.selected
  persistent : PersistentFrame graph records routes state.heap

/-- Positive exits and guard-word representability are attached to actual
source events. Navigation pops use the independent matching invariant. -/
def OperationSafe (width : ℕ) (state : RuntimeModel width n) : CursorOp n → Prop
  | .enter _ _ channel => state.counters channel + 1 < 2 ^ width
  | .leave _ _ channel => 0 < state.counters channel ∧ state.counters channel < 2 ^ width
  | .up => state.navigation ≠ []
  | _ => True

private theorem model_enter_heap (heap : Array (Word width)) (offset : ℕ)
    (counters : GuardCounters n) (channel : Channel n)
    (stored : CountersStored heap offset counters)
    (room : counters channel + 1 < 2 ^ width) :
    update width offset heap (.enter channel) =
      heap.set (offset + channel.val) (word width (counters channel + 1)) (stored.valid channel) := by
  change (if valid : offset + channel.val < heap.size then
    heap.set (offset + channel.val)
      (word width ((storedWord heap (offset + channel.val)).val + (word width 1).val)) valid
    else heap) = _
  rw [dite_eq_left (stored.valid channel),
    (storedWord_eq heap _ (stored.valid channel)).trans (stored.held channel)]
  have countValue : (word width (counters channel)).val = counters channel :=
    Nat.mod_eq_of_lt (by omega)
  have oneValue : (word width 1).val = 1 := Nat.mod_eq_of_lt (by omega)
  rw [countValue, oneValue]

private theorem model_leave_heap (heap : Array (Word width)) (offset : ℕ)
    (counters : GuardCounters n) (channel : Channel n)
    (stored : CountersStored heap offset counters)
    (positive : 0 < counters channel) (room : counters channel < 2 ^ width) :
    update width offset heap (.leave channel) =
      heap.set (offset + channel.val) (word width (counters channel - 1)) (stored.valid channel) := by
  change (if valid : offset + channel.val < heap.size then
    heap.set (offset + channel.val)
      (word width ((storedWord heap (offset + channel.val)).val + (word width (2 ^ width - 1)).val)) valid
    else heap) = _
  rw [dite_eq_left (stored.valid channel),
    (storedWord_eq heap _ (stored.valid channel)).trans (stored.held channel),
    exit_word width (counters channel) positive room]

/-- Every typed source operation executes its emitted block on the represented
heap. The theorem includes the physical state transition, all three invariant
fields, and actual ticks and stack words; it is a per-block composition lemma. -/
theorem operation_execution (program : Program width 4) (graph : DAG n)
    (records : GraphRecords width initial graph) (routes : RouteDescriptors width initial)
    (layout : SelectorLayout n) (readonly : ReadonlyLayout graph records routes layout)
    (index : OccurrenceIndex graph) (b : ℕ) (target : Channel n)
    (state : RuntimeModel width n) (held : RuntimeStored graph records routes layout state)
    (operation : CursorOp n) (source : SourceOperation graph operation)
    (safe : OperationSafe width state operation)
    (bounded : ∀ channel, state.counters channel < 2 ^ width)
    (heapFits : initial.size ≤ 2 ^ width) (oneFits : 1 < 2 ^ width)
    (indexed : ∀ owner route head, operation = .leaf owner route head →
      routes.route (index.pointer route) = route)
    (base : ℕ) (address loaded temporary : Word width) (output : List (Word width))
    (fits : base + (operationCode graph records layout index base b target operation).length < 2 ^ width)
    (block : BlockAt program base (operationCode graph records layout index base b target operation)) :
    ∃ finalAddress finalLoaded finalTemporary : Word width, ∃ ticks peak : ℕ,
      Execution program
        ((counterState state.heap base address loaded temporary).frame state.navigation output)
        ((counterState (modelStep layout index b target state operation).heap
          (base + (operationCode graph records layout index base b target operation).length)
          finalAddress finalLoaded finalTemporary).frame
          (modelStep layout index b target state operation).navigation output)
        ticks peak ∧ ticks ≤ 20 ∧
        peak ≤ 6 + state.heap.size + state.navigation.length + output.length ∧
        RuntimeStored graph records routes layout (modelStep layout index b target state operation) := by
  let currentRecords := rebaseRecords graph records routes state.heap held.persistent
  let currentRoutes := rebaseRoutes graph records routes state.heap held.persistent
  have sizeFits : state.heap.size ≤ 2 ^ width := by rw [held.persistent.size]; exact heapFits
  have counterFits : ∀ channel : Channel n, layout.counterOffset + channel.val < 2 ^ width := by
    intro channel
    have valid := held.counters.valid channel
    omega
  have foundFits : layout.found < 2 ^ width := by have valid := held.selector.foundValid; omega
  have bestFits : layout.best < 2 ^ width := by have valid := held.selector.bestValid; omega
  cases source with
  | node owner =>
      have actual := source_tag_execution program state.heap graph currentRecords owner base
        address loaded temporary (by simpa [operationCode, recordReadCode] using fits)
        (by have valid := currentRecords.tagValid owner; omega)
        (by simpa [operationCode, currentRecords, rebaseRecords] using block)
      refine ⟨word width (currentRecords.recordBase + 2 * owner.val),
        word width (match graph.node owner with
          | .zero => 0 | .input _ => 1 | .disj _ => 2 | .guard _ _ => 3 | .liveAnd _ _ => 4),
        temporary, 2, 5 + state.heap.size + (state.navigation.length + output.length),
        ?_, by omega, by omega, held⟩
      convert actual.frame state.navigation output using 1 <;>
        simp [operationCode, recordReadCode, modelStep, currentRecords, rebaseRecords]
      rfl
  | down owner position =>
      have actual := source_down_execution program graph state.heap currentRecords layout index owner position
        base b target address loaded temporary state.navigation output
        (by simpa [operationCode, recordReadCode, downCode] using fits)
        (by have valid := currentRecords.childValid owner position; omega)
        (by simpa [operationCode, currentRecords, rebaseRecords, childRecordAddress] using block)
      refine ⟨word width position.val, word width ((graph.node owner).children.get position).val,
        temporary, 4, 6 + state.heap.size + (state.navigation.length + output.length),
        ?_, by omega, by omega, ?_⟩
      · simpa [operationCode, recordReadCode, downCode, modelStep, State.frame, counterState] using actual
      · exact ⟨held.counters, held.selector, held.persistent⟩
  | up =>
      cases navigationEq : state.navigation with
      | nil => exact False.elim (safe navigationEq)
      | cons position rest =>
          have actual := source_up_execution program state.heap base address loaded temporary position rest output
            (by simpa [operationCode, upCode] using fits) (by simpa [operationCode] using block)
          refine ⟨position, loaded, temporary, 1, 6 + state.heap.size + (rest.length + output.length),
            ?_, by omega, ?_, ?_⟩
          · simpa [operationCode, upCode, modelStep, navigationEq, State.frame, counterState] using actual
          · simp only [navigationEq, List.length_cons]; omega
          · exact ⟨held.counters, held.selector, held.persistent⟩
  | enter owner position =>
      have actual := source_enter_execution program graph initial state.heap records routes layout readonly
        held.persistent currentRecords index owner position _ target rfl base b state.counters state.selected
        address loaded temporary state.navigation output held.counters held.selector (counterFits _)
        (by have valid := currentRecords.guardValid owner position; omega) safe
        (by simpa [operationCode, recordReadCode, changeCode] using fits)
        (by simpa [operationCode, currentRecords, rebaseRecords, guardRecordAddress] using block)
      have heapEq := model_enter_heap state.heap layout.counterOffset state.counters _ held.counters safe
      refine ⟨word width (layout.counterOffset + ((graph.node owner).guardLabels.get position).val),
        word width (state.counters ((graph.node owner).guardLabels.get position) + 1), word width 1,
        7, 5 + state.heap.size + (state.navigation.length + output.length),
        ?_, by omega, by omega, ?_⟩
      · simpa only [operationCode, recordReadCode, changeCode, modelStep, heapEq,
          List.length_append, List.length_cons, List.length_nil, Nat.add_zero] using actual.1
      · change RuntimeStored graph records routes layout
          { state with
            heap := (update width layout.counterOffset state.heap
              (.enter ((graph.node owner).guardLabels.get position)))
            counters := enterGuards state.counters [(graph.node owner).guardLabels.get position] }
        rw [heapEq]
        exact ⟨actual.2.1, actual.2.2.1, actual.2.2.2⟩
  | leave owner position =>
      have actual := source_leave_execution program graph initial state.heap records routes layout readonly
        held.persistent currentRecords index owner position _ target rfl base b state.counters state.selected
        address loaded temporary state.navigation output held.counters held.selector (counterFits _)
        (by have valid := currentRecords.guardValid owner position; omega) safe.1 safe.2
        (by simpa [operationCode, recordReadCode, changeCode] using fits)
        (by simpa [operationCode, currentRecords, rebaseRecords, guardRecordAddress] using block)
      have heapEq := model_leave_heap state.heap layout.counterOffset state.counters _ held.counters safe.1 safe.2
      refine ⟨word width (layout.counterOffset + ((graph.node owner).guardLabels.get position).val),
        word width (state.counters ((graph.node owner).guardLabels.get position) - 1), word width (2 ^ width - 1),
        7, 5 + state.heap.size + (state.navigation.length + output.length),
        ?_, by omega, by omega, ?_⟩
      · simpa only [operationCode, recordReadCode, changeCode, modelStep, heapEq,
          List.length_append, List.length_cons, List.length_nil, Nat.add_zero] using actual.1
      · change RuntimeStored graph records routes layout
          { state with
            heap := (update width layout.counterOffset state.heap
              (.leave ((graph.node owner).guardLabels.get position)))
            counters := leaveGuards state.counters [(graph.node owner).guardLabels.get position] }
        rw [heapEq]
        exact ⟨actual.2.1, actual.2.2.1, actual.2.2.2⟩
  | leaf owner route head equation =>
      obtain ⟨fa, fl, ft, ticks, actual, bound, countersHeld, selectorHeld, frameHeld, callback⟩ :=
        source_leaf_execution program graph initial state.heap records routes layout readonly held.persistent
          currentRecords currentRoutes index owner head target equation route base b state.counters state.selected
          address loaded temporary state.navigation output held.counters held.selector bounded oneFits counterFits
          bestFits foundFits (by have valid := currentRecords.headValid owner; omega)
          (indexed owner.val route head rfl) (by simpa [operationCode, currentRecords, rebaseRecords] using fits)
          (by simpa [operationCode, currentRecords, rebaseRecords] using block)
      refine ⟨fa, fl, ft, ticks, 5 + state.heap.size + (state.navigation.length + output.length),
        ?_, bound, by omega, ⟨countersHeld, selectorHeld, frameHeld⟩⟩
      simpa [modelStep, operationCode, currentRecords, rebaseRecords] using actual

private theorem model_navigation_step (layout : SelectorLayout n) (index : OccurrenceIndex graph)
    (b : ℕ) (target : Channel n) (state : RuntimeModel width n) (operation : CursorOp n) :
    (modelStep layout index b target state operation).navigation = navigationStep state.navigation operation := by
  cases operation <;> rfl

private theorem navigation_step_length (stack : List (Word width)) (operation : CursorOp n) :
    (navigationStep stack operation).length ≤ stack.length + 1 := by
  cases operation <;> simp [navigationStep] <;> omega

private theorem model_counter_step_le (layout : SelectorLayout n) (index : OccurrenceIndex graph)
    (b : ℕ) (target : Channel n) (state : RuntimeModel width n) (operation : CursorOp n)
    (channel : Channel n) :
    (modelStep layout index b target state operation).counters channel ≤
      state.counters channel + (guardProjection operation).length := by
  have projection := model_counters layout index b target state [operation]
  have bound := runNatural_le state.counters (guardProjection operation) channel
  simp only [runModel, List.foldl_cons, List.foldl_nil, List.flatMap_cons, List.flatMap_nil,
    List.append_nil] at projection
  rw [projection]
  exact bound

/-- Composition of emitted operations executes actual code on the represented
heap. This internal lemma exposes its safety hypotheses; the public root theorem
below obtains them from source recursion rather than accepting a supplied trace. -/
theorem emitted_execution (program : Program width 4) (graph : DAG n)
    (records : GraphRecords width initial graph) (routes : RouteDescriptors width initial)
    (layout : SelectorLayout n) (readonly : ReadonlyLayout graph records routes layout)
    (index : OccurrenceIndex graph) (b : ℕ) (target : Channel n)
    (state : RuntimeModel width n) (held : RuntimeStored graph records routes layout state)
    (operations : List (CursorOp n))
    (source : ∀ operation ∈ operations, SourceOperation graph operation)
    (navigation : NavigationSafe state.navigation operations)
    (guardSafe : ForestGuardRefinement.Safe width state.counters (operations.flatMap guardProjection))
    (room : ∀ channel, state.counters channel + (operations.flatMap guardProjection).length + 1 < 2 ^ width)
    (heapFits : initial.size ≤ 2 ^ width) (oneFits : 1 < 2 ^ width)
    (indexed : ∀ owner route head, CursorOp.leaf owner route head ∈ operations →
      routes.route (index.pointer route) = route)
    (base : ℕ) (address loaded temporary : Word width) (output : List (Word width))
    (fits : base + (emitOperations graph records layout index b target base operations).length < 2 ^ width)
    (block : BlockAt program base (emitOperations graph records layout index b target base operations)) :
    ∃ finalAddress finalLoaded finalTemporary : Word width, ∃ ticks peak : ℕ,
      Execution program
        ((counterState state.heap base address loaded temporary).frame state.navigation output)
        ((counterState (runModel layout index b target state operations).heap
          (base + (emitOperations graph records layout index b target base operations).length)
          finalAddress finalLoaded finalTemporary).frame
          (runModel layout index b target state operations).navigation output)
        ticks peak ∧ ticks ≤ 20 * operations.length ∧
        peak ≤ 6 + state.heap.size + state.navigation.length + operations.length + output.length ∧
        RuntimeStored graph records routes layout (runModel layout index b target state operations) := by
  induction operations generalizing state base address loaded temporary with
  | nil =>
      refine ⟨address, loaded, temporary, 0,
        5 + state.heap.size + (state.navigation.length + output.length), ?_, by simp, ?_, held⟩
      · simpa [runModel, emitOperations] using
          (Execution.refl ((counterState state.heap base address loaded temporary).frame state.navigation output))
      · simp [State.frame_liveWords, counterState_liveWords]; omega
  | cons operation rest ih =>
      have stepSafe : OperationSafe width state operation := by
        cases operation <;> simp only [OperationSafe]
        case enter owner position channel =>
          simpa [guardProjection, ForestGuardRefinement.Safe] using guardSafe.1
        case leave owner position channel =>
          simpa [guardProjection, ForestGuardRefinement.Safe] using guardSafe.1
        case up => exact navigation.1
      have bounded : ∀ channel, state.counters channel < 2 ^ width := by
        intro channel; have available := room channel; omega
      have coverage := emitOperations_coverage program graph records layout index b target base operation rest block
      obtain ⟨fa, fl, ft, firstTicks, firstPeak, firstExecution, firstBound, firstSpace, nextHeld⟩ :=
        operation_execution program graph records routes layout readonly index b target state held operation
          (source operation List.mem_cons_self) stepSafe bounded heapFits oneFits
          (fun owner route head equal => indexed owner route head (by rw [equal]; exact List.mem_cons_self))
          base address loaded temporary output
          (by simp only [emitOperations, List.length_append] at fits; omega) coverage.1
      have nextNavigation : NavigationSafe
          (modelStep layout index b target state operation).navigation rest := by
        rw [model_navigation_step]
        exact navigation.2
      have nextGuard : ForestGuardRefinement.Safe width
          (modelStep layout index b target state operation).counters (rest.flatMap guardProjection) := by
        cases operation <;> simp only [List.flatMap_cons, guardProjection, List.nil_append,
          List.singleton_append, ForestGuardRefinement.Safe, modelStep, naturalStep] at guardSafe ⊢
        case node => exact guardSafe
        case down => exact guardSafe
        case up => exact guardSafe
        case leaf => exact guardSafe
        case enter => exact guardSafe.2
        case leave => exact guardSafe.2
      have nextRoom : ∀ channel,
          (modelStep layout index b target state operation).counters channel +
            (rest.flatMap guardProjection).length + 1 < 2 ^ width := by
        intro channel
        have countBound := model_counter_step_le layout index b target state operation channel
        have available := room channel
        simp only [List.flatMap_cons, List.length_append] at available
        omega
      obtain ⟨lastAddress, lastLoaded, lastTemporary, restTicks, restPeak, restExecution,
          restBound, restSpace, finalHeld⟩ :=
        ih (modelStep layout index b target state operation) nextHeld
          (fun current present => source current (List.mem_cons_of_mem operation present))
          nextNavigation nextGuard nextRoom
          (fun owner route head present => indexed owner route head (List.mem_cons_of_mem operation present))
          (base + (operationCode graph records layout index base b target operation).length) fa fl ft
          (by simp only [emitOperations, List.length_append] at fits; omega) coverage.2
      have nextSize : (modelStep layout index b target state operation).heap.size = state.heap.size :=
        nextHeld.persistent.size.trans held.persistent.size.symm
      have nextLength := navigation_step_length state.navigation operation
      rw [← model_navigation_step layout index b target state operation] at nextLength
      refine ⟨lastAddress, lastLoaded, lastTemporary, firstTicks + restTicks, max firstPeak restPeak,
        ?_, ?_, ?_, finalHeld⟩
      · simpa only [runModel, List.foldl_cons, emitOperations, List.length_append, Nat.add_assoc] using
          firstExecution.append restExecution
      · simp only [List.length_cons]; omega
      · rw [nextSize] at restSpace
        apply max_le <;> simp only [List.length_cons] <;> omega

/-- A full source-root physical traversal, with code coverage and finite heap
representation explicit. Guard capacity and stack validity are obtained from the
actual decoder. This theorem does not charge construction of those representations. -/
theorem root_execution (program : Program width 4) (graph : DAG n)
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
        ticks peak ∧ ticks ≤ 20 * (cursorOps graph root []).length ∧
        peak ≤ 6 + state.heap.size + state.navigation.length + (cursorOps graph root []).length + output.length ∧
        RuntimeStored graph records routes layout (runModel layout index b target state (cursorOps graph root [])) ∧
        (runModel layout index b target state (cursorOps graph root [])).counters = state.counters ∧
        modelProjection routes (runModel layout index b target state (cursorOps graph root [])) =
          graph.foldLeafCursor (fun _ => 0) root [] (state.counters, 0)
            ((state.selected.map routes.route).map fun route => (route, 0)) (keepBestRoute b target 0) := by
  obtain ⟨fa, fl, ft, ticks, peak, execution, tickBound, spaceBound, finalHeld⟩ :=
    emitted_execution program graph records routes layout readonly index b target state held
      (cursorOps graph root []) (cursor_source_operations graph root [])
      (source_navigation_safe graph root [] state.navigation).2
      (by rw [cursor_guard_projection]; exact source_guard_safe graph root state.counters capacity)
      (by rw [cursor_guard_projection]; exact capacity) heapFits oneFits
      (fun owner route head present => (indexed owner route head present).1)
      base address loaded temporary output fits block
  refine ⟨fa, fl, ft, ticks, peak, ?_, tickBound, spaceBound, finalHeld,
    root_model_counters graph root layout index b target state,
    root_model_result graph root layout index routes b target state indexed⟩
  simpa only [root_model_navigation, rootCode] using execution

end Controller.Cost.ForestCursorRoot
