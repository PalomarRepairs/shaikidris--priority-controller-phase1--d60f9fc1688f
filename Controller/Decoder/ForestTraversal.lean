module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Decoder.ForestWeight

@[expose] public section

/-!
# Positional forest traversal

A route lists child positions in order from the queried root to its positive
leaf. Distinct positions remain distinct when two children refer to the same
stored node. The traversal folds a callback over leaves and retains only its
accumulator; channel sets are reconstructed from the selected route.
-/

namespace Controller.Decoder

variable {n : ℕ}

abbrev LeafRoute := List ℕ

/-- A route certificate retains child positions as well as stored endpoints. -/
inductive RoutePath (graph : DAG n) :
    Fin graph.nodeCount → LeafRoute → Channel n → Finset (Channel n) → Prop where
  | input (index : Fin graph.nodeCount) (head : Channel n)
      (gateEquation : graph.node index = .input head) :
      RoutePath graph index [] head ∅
  | disj (index : Fin graph.nodeCount) (refs : List (Fin index.val))
      (position : Fin refs.length) (route : LeafRoute) (head : Channel n)
      (blocked : Finset (Channel n)) (gateEquation : graph.node index = .disj refs)
      (tail : RoutePath graph (graph.childIndex index (refs.get position)) route head blocked) :
      RoutePath graph index (position.val :: route) head blocked
  | guard (index : Fin graph.nodeCount) (child : Fin index.val)
      (labels : List (Channel n)) (route : LeafRoute) (head : Channel n)
      (blocked : Finset (Channel n)) (gateEquation : graph.node index = .guard child labels)
      (tail : RoutePath graph (graph.childIndex index child) route head blocked) :
      RoutePath graph index (0 :: route) head (labels.toFinset ∪ blocked)

namespace RoutePath

theorem livePath {graph : DAG n} {index : Fin graph.nodeCount} {route : LeafRoute}
    {head : Channel n} {blocked : Finset (Channel n)}
    (path : RoutePath graph index route head blocked) : LivePath graph index head blocked := by
  induction path with
  | input index head equation => exact .input index head equation
  | disj index refs position route head blocked equation tail ih =>
      exact .disj index refs (refs.get position) head blocked equation (List.get_mem _ _) ih
  | guard index child labels route head blocked equation tail ih =>
      exact .guard index child labels head blocked equation ih

end RoutePath

namespace LivePath

theorem exists_route {graph : DAG n} {index : Fin graph.nodeCount}
    {head : Channel n} {blocked : Finset (Channel n)}
    (path : LivePath graph index head blocked) :
    ∃ route, RoutePath graph index route head blocked := by
  induction path with
  | input index head equation => exact ⟨[], .input index head equation⟩
  | disj index refs child head blocked equation present tail ih =>
      obtain ⟨position, equal⟩ := List.mem_iff_get.mp present
      obtain ⟨route, routePath⟩ := ih
      refine ⟨position.val :: route, .disj index refs position route head blocked equation ?_⟩
      simpa only [equal] using routePath
  | guard index child labels head blocked equation tail ih =>
      obtain ⟨route, routePath⟩ := ih
      exact ⟨0 :: route, .guard index child labels route head blocked equation routePath⟩

end LivePath

abbrev WeightedCounters (n : ℕ) := GuardCounters n × ℕ

def enterWeightedGuards (weights : Channel n → ℕ) (state : WeightedCounters n)
    (labels : List (Channel n)) : WeightedCounters n :=
  labels.foldl (enterWeightedLabel weights) state

def leaveWeightedGuards (weights : Channel n → ℕ) (state : WeightedCounters n)
    (labels : List (Channel n)) : WeightedCounters n :=
  labels.foldl (leaveWeightedLabel weights) state

@[simp] theorem enterWeightedGuards_counters (weights : Channel n → ℕ)
    (state : WeightedCounters n) (labels : List (Channel n)) :
    (enterWeightedGuards weights state labels).1 = enterGuards state.1 labels := by
  induction labels generalizing state with
  | nil => rfl
  | cons label rest ih =>
      simpa only [enterWeightedGuards, List.foldl_cons, enterGuards,
        enterWeightedLabel, enterGuards] using ih (enterWeightedLabel weights state label)

@[simp] theorem leaveWeightedGuards_counters (weights : Channel n → ℕ)
    (state : WeightedCounters n) (labels : List (Channel n)) :
    (leaveWeightedGuards weights state labels).1 = leaveGuards state.1 labels := by
  induction labels generalizing state with
  | nil => rfl
  | cons label rest ih =>
      simpa only [leaveWeightedGuards, List.foldl_cons, leaveGuards,
        leaveWeightedLabel, leaveGuards] using ih (leaveWeightedLabel weights state label)

theorem enterWeightedGuards_correct (weights : Channel n → ℕ)
    (state : WeightedCounters n) (labels : List (Channel n))
    (invariant : state.2 = channelWeight weights (blockedChannels state.1)) :
    (enterWeightedGuards weights state labels).2 =
      channelWeight weights (blockedChannels (enterWeightedGuards weights state labels).1) := by
  induction labels generalizing state with
  | nil => exact invariant
  | cons label rest ih =>
      exact ih _ (enterWeightedLabel_correct weights state label invariant)

theorem leaveWeightedGuards_correct (weights : Channel n → ℕ)
    (state : WeightedCounters n) (labels : List (Channel n))
    (invariant : state.2 = channelWeight weights (blockedChannels state.1)) :
    (leaveWeightedGuards weights state labels).2 =
      channelWeight weights (blockedChannels (leaveWeightedGuards weights state labels).1) := by
  induction labels generalizing state with
  | nil => exact invariant
  | cons label rest ih =>
      exact ih _ (leaveWeightedLabel_correct weights state label invariant)

theorem leave_enterWeightedGuards (weights : Channel n → ℕ)
    (state : WeightedCounters n) (labels : List (Channel n))
    (invariant : state.2 = channelWeight weights (blockedChannels state.1)) :
    leaveWeightedGuards weights (enterWeightedGuards weights state labels) labels = state := by
  apply Prod.ext
  · simp only [leaveWeightedGuards_counters, enterWeightedGuards_counters, leave_enterGuards]
  · rw [leaveWeightedGuards_correct weights _ _
      (enterWeightedGuards_correct weights state labels invariant)]
    simp only [leaveWeightedGuards_counters, enterWeightedGuards_counters, leave_enterGuards]
    exact invariant.symm

namespace SparseFormula

variable {α : Type*} [LinearOrder α]

/-- Every actual literal coordinate, preserving rows separately in the formula. -/
def support (formula : CNF.Formula α) : Finset α :=
  (formula.clauses.toList.flatMap (fun clause => clause.map Prod.fst)).toFinset

theorem variable_mem_support (formula : CNF.Formula α) (clause : CNF.Clause α)
    (row : clause ∈ formula.clauses) (literal : CNF.Literal α) (present : literal ∈ clause) :
    literal.1 ∈ support formula := by
  apply List.mem_toFinset.mpr
  exact List.mem_flatMap.mpr ⟨clause, by simpa using row,
    List.mem_map.mpr ⟨literal, present, rfl⟩⟩

/-- A dummy last slot makes the renaming total even for an empty formula.
Unused source coordinates share that slot and occur in no clause. -/
def index (formula : CNF.Formula α) (coordinate : α) : Fin ((support formula).card + 1) :=
  if member : coordinate ∈ support formula then
    Fin.castSucc (((support formula).orderIsoOfFin rfl).symm ⟨coordinate, member⟩)
  else Fin.last (support formula).card

def compact (formula : CNF.Formula α) : CNF.FiniteFormula ((support formula).card + 1) :=
  CNF.relabel (index formula) formula

/-- The canonical compact extension evaluates each retained index at its old ID. -/
def compactAssignment (formula : CNF.Formula α) (values : α → Bool)
    (slot : Fin ((support formula).card + 1)) : Bool :=
  if retained : slot.val < (support formula).card then
    values (((support formula).orderIsoOfFin rfl) ⟨slot.val, retained⟩).val
  else false

theorem compactAssignment_index (formula : CNF.Formula α) (values : α → Bool)
    (coordinate : α) (present : coordinate ∈ support formula) :
    compactAssignment formula values (index formula coordinate) = values coordinate := by
  simp only [index, dite_eq_left present, compactAssignment, Fin.coe_castSucc,
    Fin.isLt, dite_eq_left]
  change values (((support formula).orderIsoOfFin rfl)
    (((support formula).orderIsoOfFin rfl).symm ⟨coordinate, present⟩)).val = values coordinate
  rw [OrderIso.apply_symm_apply]

/-- Assignments agreeing on actual literal coordinates satisfy the same rows. -/
theorem satisfies_agree (formula : CNF.Formula α) (first second : α → Bool)
    (agree : ∀ coordinate ∈ support formula, first coordinate = second coordinate) :
    CNF.Satisfies first formula ↔ CNF.Satisfies second formula := by
  constructor
  · intro model clause row
    obtain ⟨literal, present, trueLiteral⟩ := model clause row
    refine ⟨literal, present, ?_⟩
    unfold CNF.LiteralHolds at *
    rw [← agree literal.1 (variable_mem_support formula clause row literal present)]
    exact trueLiteral
  · intro model clause row
    obtain ⟨literal, present, trueLiteral⟩ := model clause row
    refine ⟨literal, present, ?_⟩
    unfold CNF.LiteralHolds at *
    rw [agree literal.1 (variable_mem_support formula clause row literal present)]
    exact trueLiteral

theorem compact_satisfiable_iff (formula : CNF.Formula α) :
    CNF.Satisfiable (compact formula) ↔ CNF.Satisfiable formula := by
  constructor
  · rintro ⟨values, model⟩
    exact ⟨values ∘ index formula, (CNF.satisfies_relabel _ _ _).mp model⟩
  · rintro ⟨values, model⟩
    refine ⟨compactAssignment formula values, (CNF.satisfies_relabel _ _ _).mpr ?_⟩
    apply (satisfies_agree formula values (compactAssignment formula values ∘ index formula) ?_).mp model
    intro coordinate present
    exact (compactAssignment_index formula values coordinate present).symm

/-- Channel decoding fixes every omitted coordinate false. -/
def liftAssignment (formula : CNF.Formula α) (values : Fin ((support formula).card + 1) → Bool)
    (coordinate : α) : Bool :=
  if coordinate ∈ support formula then values (index formula coordinate) else false

theorem liftAssignment_model (formula : CNF.Formula α)
    (values : Fin ((support formula).card + 1) → Bool)
    (model : CNF.Satisfies values (compact formula)) :
    CNF.Satisfies (liftAssignment formula values) formula := by
  apply (satisfies_agree formula (values ∘ index formula) (liftAssignment formula values) ?_).mp
    ((CNF.satisfies_relabel _ _ _).mp model)
  intro coordinate present
  simp only [Function.comp_apply, liftAssignment, ite_eq_left present]

omit [LinearOrder α] in
/-- Literal renaming preserves dual-Horn clauses even when unused IDs collapse. -/
theorem clause_relabel_dualHorn (rename : α → β) (clause : CNF.Clause α)
    (restricted : Horn.DualHornClause clause) :
    Horn.DualHornClause (Controller.CNF.OrderedFormula.Clause.relabel rename clause) := by
  rcases restricted with tautology | unique
  · obtain ⟨literal, present, opposite⟩ := tautology
    left
    refine ⟨(rename literal.1, literal.2), ?_, ?_⟩
    · exact List.mem_map.mpr ⟨literal, present, rfl⟩
    · exact List.mem_map.mpr ⟨CNF.negate literal, opposite, rfl⟩
  · right
    intro left leftMember right rightMember leftNegative rightNegative
    obtain ⟨oldLeft, oldLeftMember, leftEquation⟩ := List.mem_map.mp leftMember
    obtain ⟨oldRight, oldRightMember, rightEquation⟩ := List.mem_map.mp rightMember
    subst left
    subst right
    exact congrArg rename (unique oldLeft oldLeftMember oldRight oldRightMember
      leftNegative rightNegative)

omit [LinearOrder α] in
theorem relabel_dualHorn (rename : α → β) (formula : CNF.Formula α)
    (restricted : Horn.DualHorn formula) : Horn.DualHorn (CNF.relabel rename formula) := by
  intro clause present
  obtain ⟨old, membership, equation⟩ := Array.mem_map.mp present
  subst clause
  exact clause_relabel_dualHorn rename old (restricted old membership)

theorem compact_dualHorn (formula : CNF.Formula α) (restricted : Horn.DualHorn formula) :
    Horn.DualHorn (compact formula) := relabel_dualHorn _ _ restricted

end SparseFormula

namespace DAG

/-- Read one selected route and its guard incidences, without evaluating other branches. -/
def reconstructRoute (graph : DAG n) (index : Fin graph.nodeCount) (route : LeafRoute) :
    Option (Channel n × List (Channel n)) :=
  match graph.node index, route with
  | .input head, [] => some (head, [])
  | .disj refs, position :: rest =>
      if bound : position < refs.length then
        graph.reconstructRoute (graph.childIndex index (refs.get ⟨position, bound⟩)) rest
      else none
  | .guard child labels, 0 :: rest =>
      (graph.reconstructRoute (graph.childIndex index child) rest).map
        fun result => (result.1, labels ++ result.2)
  | _, _ => none
termination_by index.val
decreasing_by all_goals exact graph.childIndex_lt _ _

/-- Every certified positional route is read back with precisely its guard union. -/
theorem reconstructRoute_of_path (graph : DAG n) {index : Fin graph.nodeCount}
    {route : LeafRoute} {head : Channel n} {blocked : Finset (Channel n)}
    (path : RoutePath graph index route head blocked) :
    ∃ labels, graph.reconstructRoute index route = some (head, labels) ∧
      labels.toFinset = blocked := by
  induction path with
  | input index head equation =>
      refine ⟨[], ?_, rfl⟩
      rw [reconstructRoute.eq_def, equation]
  | disj index refs position route head blocked equation tail ih =>
      obtain ⟨labels, result, union⟩ := ih
      refine ⟨labels, ?_, union⟩
      rw [reconstructRoute.eq_def, equation]
      simpa only [dite_eq_left position.isLt] using result
  | guard index child labels route head blocked equation tail ih =>
      obtain ⟨tailLabels, result, union⟩ := ih
      refine ⟨labels ++ tailLabels, ?_, ?_⟩
      · rw [reconstructRoute.eq_def, equation]
        simp only []
        rw [result]
        rfl
      · simp only [List.toFinset_append, union]

/-- A callback fold over actual child positions. Guards are entered before descent
and left on return. The callback cannot change the path counter state. -/
def foldLeafRoutes {α : Type*} (graph : DAG n) (weights : Channel n → ℕ)
    (index : Fin graph.nodeCount) (counters : WeightedCounters n) (initial : α)
    (visit : LeafRoute → Channel n → WeightedCounters n → α → α) :
    WeightedCounters n × α :=
  match graph.node index with
  | .zero => (counters, initial)
  | .input head => (counters, visit [] head counters initial)
  | .disj refs =>
      (List.finRange refs.length).foldl (fun state position =>
        graph.foldLeafRoutes weights (graph.childIndex index (refs.get position))
          state.1 state.2 (fun route head current accumulator =>
            visit (position.val :: route) head current accumulator)) (counters, initial)
  | .guard child labels =>
      let result := graph.foldLeafRoutes weights (graph.childIndex index child)
        (enterWeightedGuards weights counters labels) initial
        (fun route head current accumulator => visit (0 :: route) head current accumulator)
      (leaveWeightedGuards weights result.1 labels, result.2)
  | .liveAnd _ _ => (counters, initial)
termination_by index.val
decreasing_by all_goals exact graph.childIndex_lt _ _

private theorem foldl_counters_unchanged {α β S : Type*} (items : List β)
    (step : S × α → β → S × α)
    (base : S) (initial : S × α)
    (initialEqual : initial.1 = base)
    (preserved : ∀ state item, state.1 = base → (step state item).1 = base) :
    (items.foldl step initial).1 = base := by
  induction items generalizing initial with
  | nil => exact initialEqual
  | cons item rest ih => exact ih _ (preserved initial item initialEqual)

/-- A complete subtree visit restores both guard counts and blocked union weight. -/
theorem foldLeafRoutes_restores {α : Type*} (graph : DAG n)
    (weights : Channel n → ℕ) (index : Fin graph.nodeCount)
    (counters : WeightedCounters n) (initial : α)
    (visit : LeafRoute → Channel n → WeightedCounters n → α → α)
    (invariant : counters.2 = channelWeight weights (blockedChannels counters.1)) :
    (graph.foldLeafRoutes weights index counters initial visit).1 = counters := by
  have claim : ∀ bound : ℕ, ∀ current : Fin graph.nodeCount, current.val = bound →
      ∀ (state : WeightedCounters n) (accumulator : α)
        (callback : LeafRoute → Channel n → WeightedCounters n → α → α),
      state.2 = channelWeight weights (blockedChannels state.1) →
      (graph.foldLeafRoutes weights current state accumulator callback).1 = state := by
    intro bound
    induction bound using Nat.strong_induction_on with
    | h bound ih =>
      intro current currentBound state accumulator callback correct
      rw [foldLeafRoutes]
      cases equation : graph.node current with
      | zero => rfl
      | input head => rfl
      | liveAnd left right => rfl
      | disj refs =>
          apply foldl_counters_unchanged _ _ state (state, accumulator) rfl
          intro previous position equal
          have earlier : (graph.childIndex current (refs.get position)).val < bound := by
            simpa only [DAG.childIndex, currentBound] using (refs.get position).isLt
          rw [ih _ earlier _ rfl previous.1 previous.2 _ (by simpa only [equal] using correct)]
          exact equal
      | guard child labels =>
          have earlier : (graph.childIndex current child).val < bound := by
            simpa only [DAG.childIndex, currentBound] using child.isLt
          have restore := ih _ earlier _ rfl (enterWeightedGuards weights state labels)
            accumulator (fun route head current accumulator => callback (0 :: route) head current accumulator)
            (enterWeightedGuards_correct weights state labels correct)
          change leaveWeightedGuards weights
            (graph.foldLeafRoutes weights (graph.childIndex current child)
              (enterWeightedGuards weights state labels) accumulator
              (fun route head current accumulator => callback (0 :: route) head current accumulator)).1
            labels = state
          rw [restore]
          exact leave_enterWeightedGuards weights state labels correct
  exact claim index.val index rfl counters initial visit invariant

private theorem foldl_state_invariant {α β : Type*} (items : List β)
    (step : WeightedCounters n × α → β → WeightedCounters n × α)
    (base : WeightedCounters n) (P : α → Prop) (initial : WeightedCounters n × α)
    (initialEqual : initial.1 = base) (initialValid : P initial.2)
    (preserved : ∀ state item, state.1 = base → P state.2 →
      (step state item).1 = base ∧ P (step state item).2) :
    (items.foldl step initial).1 = base ∧ P (items.foldl step initial).2 := by
  induction items generalizing initial with
  | nil => exact ⟨initialEqual, initialValid⟩
  | cons item rest ih =>
      obtain ⟨equal, valid⟩ := preserved initial item initialEqual initialValid
      exact ih _ equal valid

/-- Callback invariants need only be proved at genuine positive-leaf routes with
exact blocked unions. This transfers them to the executable fold. -/
theorem foldLeafRoutes_preserves {α : Type*} (graph : DAG n)
    (weights : Channel n → ℕ) (index : Fin graph.nodeCount)
    (counters : WeightedCounters n) (initial : α)
    (visit : LeafRoute → Channel n → WeightedCounters n → α → α)
    (P : α → Prop) (initialValid : P initial)
    (correct : counters.2 = channelWeight weights (blockedChannels counters.1))
    (leafValid : ∀ route head blocked current,
      RoutePath graph index route head blocked →
      blockedChannels current.1 = blockedChannels counters.1 ∪ blocked →
      current.2 = channelWeight weights (blockedChannels current.1) →
      ∀ accumulator, P accumulator → P (visit route head current accumulator)) :
    P (graph.foldLeafRoutes weights index counters initial visit).2 := by
  have claim : ∀ bound : ℕ, ∀ current : Fin graph.nodeCount, current.val = bound →
      ∀ (state : WeightedCounters n) (accumulator : α)
        (callback : LeafRoute → Channel n → WeightedCounters n → α → α)
        (Q : α → Prop), Q accumulator →
      state.2 = channelWeight weights (blockedChannels state.1) →
      (∀ route head blocked leafState, RoutePath graph current route head blocked →
        blockedChannels leafState.1 = blockedChannels state.1 ∪ blocked →
        leafState.2 = channelWeight weights (blockedChannels leafState.1) →
        ∀ previous, Q previous → Q (callback route head leafState previous)) →
      Q (graph.foldLeafRoutes weights current state accumulator callback).2 := by
    intro bound
    induction bound using Nat.strong_induction_on with
    | h bound ih =>
      intro current currentBound state accumulator callback Q valid invariant leaves
      rw [foldLeafRoutes]
      cases equation : graph.node current with
      | zero => exact valid
      | liveAnd left right => exact valid
      | input head =>
          exact leaves [] head ∅ state (.input current head equation)
            (by simp) invariant accumulator valid
      | disj refs =>
          apply (foldl_state_invariant (List.finRange refs.length) _ state Q
            (state, accumulator) rfl valid ?_).2
          intro previous position equal previousValid
          have earlier : (graph.childIndex current (refs.get position)).val < bound := by
            simpa only [DAG.childIndex, currentBound] using (refs.get position).isLt
          refine ⟨?_, ?_⟩
          · exact (graph.foldLeafRoutes_restores weights _ previous.1 previous.2 _
              (by simpa only [equal] using invariant)).trans equal
          · apply ih _ earlier _ rfl previous.1 previous.2 _ Q previousValid
              (by simpa only [equal] using invariant)
            intro route head blocked leafState path union weight previousAccumulator previousAccumulatorValid
            apply leaves (position.val :: route) head blocked leafState
              (.disj current refs position route head blocked equation path)
              (by simpa only [equal] using union) weight previousAccumulator previousAccumulatorValid
      | guard child labels =>
          have earlier : (graph.childIndex current child).val < bound := by
            simpa only [DAG.childIndex, currentBound] using child.isLt
          apply ih _ earlier _ rfl (enterWeightedGuards weights state labels) accumulator _ Q valid
            (enterWeightedGuards_correct weights state labels invariant)
          intro route head blocked leafState path union weight previous previousValid
          apply leaves (0 :: route) head (labels.toFinset ∪ blocked) leafState
            (.guard current child labels route head blocked equation path) ?_ weight previous previousValid
          rw [enterWeightedGuards_counters, blocked_enterGuards] at union
          simpa only [Finset.union_assoc] using union
  exact claim index.val index rfl counters initial visit P initialValid correct leafValid

private theorem foldl_hits {α β : Type*} [DecidableEq β] (items : List β)
    (step : WeightedCounters n × α → β → WeightedCounters n × α)
    (base : WeightedCounters n) (P : α → Prop) (chosen : β) (present : chosen ∈ items)
    (initial : WeightedCounters n × α) (initialEqual : initial.1 = base)
    (restores : ∀ state item, state.1 = base → (step state item).1 = base)
    (preserves : ∀ state item, state.1 = base → P state.2 → P (step state item).2)
    (hits : ∀ state, state.1 = base → P (step state chosen).2) :
    P (items.foldl step initial).2 := by
  induction items generalizing initial with
  | nil => simp at present
  | cons item rest ih =>
      by_cases equal : item = chosen
      · subst item
        exact (foldl_state_invariant rest step base P (step initial chosen)
          (restores initial chosen initialEqual) (hits initial initialEqual)
          (fun state item equal valid => ⟨restores state item equal,
            preserves state item equal valid⟩)).2
      · have tailPresent : chosen ∈ rest := by simpa [Ne.symm equal] using present
        exact ih tailPresent (step initial item) (restores initial item initialEqual)

/-- Every certified leaf occurrence is visited. An invariant established at that
occurrence and preserved by callbacks therefore holds after the entire fold. -/
theorem foldLeafRoutes_hits {α : Type*} (graph : DAG n) (weights : Channel n → ℕ)
    {index : Fin graph.nodeCount} {route : LeafRoute} {head : Channel n}
    {blocked : Finset (Channel n)} (path : RoutePath graph index route head blocked)
    (counters : WeightedCounters n) (initial : α)
    (visit : LeafRoute → Channel n → WeightedCounters n → α → α)
    (P : α → Prop)
    (correct : counters.2 = channelWeight weights (blockedChannels counters.1))
    (preserved : ∀ route head current accumulator,
      P accumulator → P (visit route head current accumulator))
    (hit : ∀ current,
      blockedChannels current.1 = blockedChannels counters.1 ∪ blocked →
      current.2 = channelWeight weights (blockedChannels current.1) →
      ∀ accumulator, P (visit route head current accumulator)) :
    P (graph.foldLeafRoutes weights index counters initial visit).2 := by
  induction path generalizing counters initial visit with
  | input index head equation =>
      rw [foldLeafRoutes, equation]
      exact hit counters (by simp) correct initial
  | disj index refs position route head blocked equation tail ih =>
      rw [foldLeafRoutes, equation]
      apply foldl_hits (List.finRange refs.length) _ counters P position
        (by simp) (counters, initial) rfl
      · intro previous child equal
        exact (graph.foldLeafRoutes_restores weights _ previous.1 previous.2 _
          (by simpa only [equal] using correct)).trans equal
      · intro previous child equal previousValid
        apply graph.foldLeafRoutes_preserves weights _ previous.1 previous.2 _ P previousValid
          (by simpa only [equal] using correct)
        intro childRoute childHead childBlocked current childPath union weight accumulator valid
        exact preserved (child.val :: childRoute) childHead current accumulator valid
      · intro previous equal
        apply ih previous.1 previous.2
          (fun childRoute childHead current accumulator =>
            visit (position.val :: childRoute) childHead current accumulator)
          (by simpa only [equal] using correct)
        · intro childRoute childHead current accumulator valid
          exact preserved (position.val :: childRoute) childHead current accumulator valid
        · intro current union weight accumulator
          exact hit current (by simpa only [equal] using union) weight accumulator
  | guard index child labels route head blocked equation tail ih =>
      rw [foldLeafRoutes, equation]
      apply ih (enterWeightedGuards weights counters labels) initial
        (fun childRoute childHead current accumulator =>
          visit (0 :: childRoute) childHead current accumulator)
        (enterWeightedGuards_correct weights counters labels correct)
      · intro childRoute childHead current accumulator valid
        exact preserved (0 :: childRoute) childHead current accumulator valid
      · intro current union weight accumulator
        apply hit current ?_ weight accumulator
        rw [enterWeightedGuards_counters, blocked_enterGuards] at union
        simpa only [Finset.union_assoc] using union

/-- The accumulator stores a route and scalar score, never a channel set. -/
def keepBestRoute (b : ℕ) (target : Channel n) (total : ℕ)
    (route : LeafRoute) (head : Channel n) (state : WeightedCounters n)
    (best : Option (LeafRoute × ℕ)) : Option (LeafRoute × ℕ) :=
  if state.1 head = 0 ∧ (b ≠ 1 ∨ state.1 target = 0) then
    let score := total - state.2
    match best with
    | none => some (route, score)
    | some previous => if previous.2 < score then some (route, score) else best
  else best

private theorem keepBestRoute_preserves (b : ℕ) (target : Channel n) (total : ℕ)
    (route : LeafRoute) (head : Channel n) (state : WeightedCounters n)
    (best : Option (LeafRoute × ℕ)) (P : Option (LeafRoute × ℕ) → Prop)
    (previousValid : P best)
    (newValid : state.1 head = 0 ∧ (b ≠ 1 ∨ state.1 target = 0) →
      P (some (route, total - state.2))) :
    P (keepBestRoute b target total route head state best) := by
  unfold keepBestRoute
  by_cases feasible : state.1 head = 0 ∧ (b ≠ 1 ∨ state.1 target = 0)
  · simp only [ite_eq_left feasible]
    cases best with
    | none => exact newValid feasible
    | some previous =>
        simp only
        by_cases improves : previous.2 < total - state.2
        · simpa only [ite_eq_left improves] using newValid feasible
        · simpa only [ite_eq_right improves] using previousValid
  · simpa only [ite_eq_right feasible] using previousValid

def RouteScoreAtLeast (threshold : ℕ) (best : Option (LeafRoute × ℕ)) : Prop :=
  ∃ route score, best = some (route, score) ∧ threshold ≤ score

private theorem keepBestRoute_monotone (b : ℕ) (target : Channel n) (total : ℕ)
    (route : LeafRoute) (head : Channel n) (state : WeightedCounters n)
    (best : Option (LeafRoute × ℕ)) (threshold : ℕ)
    (good : RouteScoreAtLeast threshold best) :
    RouteScoreAtLeast threshold (keepBestRoute b target total route head state best) := by
  obtain ⟨oldRoute, oldScore, equal, bound⟩ := good
  unfold keepBestRoute
  by_cases feasible : state.1 head = 0 ∧ (b ≠ 1 ∨ state.1 target = 0)
  · simp only [ite_eq_left feasible, equal]
    by_cases improves : oldScore < total - state.2
    · exact ⟨route, total - state.2, by simp only [ite_eq_left improves], bound.trans (Nat.le_of_lt improves)⟩
    · exact ⟨oldRoute, oldScore, by simp only [ite_eq_right improves], bound⟩
  · exact ⟨oldRoute, oldScore, by simp only [ite_eq_right feasible, equal], bound⟩

private theorem keepBestRoute_hits (b : ℕ) (target : Channel n) (total : ℕ)
    (route : LeafRoute) (head : Channel n) (state : WeightedCounters n)
    (best : Option (LeafRoute × ℕ))
    (feasible : state.1 head = 0 ∧ (b ≠ 1 ∨ state.1 target = 0)) :
    RouteScoreAtLeast (total - state.2) (keepBestRoute b target total route head state best) := by
  unfold keepBestRoute
  rw [ite_eq_left feasible]
  cases best with
  | none => exact ⟨route, total - state.2, rfl, le_rfl⟩
  | some previous =>
      simp only
      by_cases improves : previous.2 < total - state.2
      · exact ⟨route, total - state.2, by simp only [ite_eq_left improves], le_rfl⟩
      · exact ⟨previous.1, previous.2, by simp only [ite_eq_right improves], Nat.le_of_not_lt improves⟩

/-- A shared reversed routePrefix grows by one constructor per descent. Leaf callbacks
receive that cursor directly; no forward route is rebuilt at each leaf. -/
def foldLeafCursor {α : Type*} (graph : DAG n) (weights : Channel n → ℕ)
    (index : Fin graph.nodeCount) (routePrefix : LeafRoute)
    (counters : WeightedCounters n) (initial : α)
    (visit : LeafRoute → Channel n → WeightedCounters n → α → α) :
    WeightedCounters n × α :=
  match graph.node index with
  | .zero => (counters, initial)
  | .input head => (counters, visit routePrefix head counters initial)
  | .disj refs =>
      (List.finRange refs.length).foldl (fun state position =>
        graph.foldLeafCursor weights (graph.childIndex index (refs.get position))
          (position.val :: routePrefix) state.1 state.2 visit) (counters, initial)
  | .guard child labels =>
      let result := graph.foldLeafCursor weights (graph.childIndex index child) (0 :: routePrefix)
        (enterWeightedGuards weights counters labels) initial visit
      (leaveWeightedGuards weights result.1 labels, result.2)
  | .liveAnd _ _ => (counters, initial)
termination_by index.val
decreasing_by all_goals exact graph.childIndex_lt _ _

/-- Cursor execution agrees with the positional callback fold under routePrefix reversal. -/
theorem foldLeafCursor_eq_fold {α : Type*} (graph : DAG n) (weights : Channel n → ℕ)
    (index : Fin graph.nodeCount) (routePrefix : LeafRoute)
    (counters : WeightedCounters n) (initial : α)
    (visit : LeafRoute → Channel n → WeightedCounters n → α → α) :
    graph.foldLeafCursor weights index routePrefix counters initial visit =
      graph.foldLeafRoutes weights index counters initial
        (fun route head current accumulator => visit (route.reverse ++ routePrefix) head current accumulator) := by
  have claim : ∀ bound : ℕ, ∀ current : Fin graph.nodeCount, current.val = bound →
      ∀ (routePrefix : LeafRoute) (state : WeightedCounters n) (accumulator : α)
        (callback : LeafRoute → Channel n → WeightedCounters n → α → α),
      graph.foldLeafCursor weights current routePrefix state accumulator callback =
        graph.foldLeafRoutes weights current state accumulator
          (fun route head current accumulator =>
            callback (route.reverse ++ routePrefix) head current accumulator) := by
    intro bound
    induction bound using Nat.strong_induction_on with
    | h bound ih =>
      intro current currentBound routePrefix state accumulator callback
      rw [foldLeafCursor, foldLeafRoutes]
      cases equation : graph.node current with
      | zero => rfl
      | input head => simp
      | liveAnd left right => rfl
      | disj refs =>
          simp only []
          congr 1
          funext previous position
          have earlier : (graph.childIndex current (refs.get position)).val < bound := by
            simpa only [DAG.childIndex, currentBound] using (refs.get position).isLt
          rw [ih _ earlier _ rfl]
          congr 1
          funext route head current accumulator
          simp [List.reverse_cons, List.append_assoc]
      | guard child labels =>
          simp only []
          have earlier : (graph.childIndex current child).val < bound := by
            simpa only [DAG.childIndex, currentBound] using child.isLt
          rw [ih _ earlier _ rfl]
          simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
  exact claim index.val index rfl routePrefix counters initial visit

/-- Changing only the callback accumulator commutes with the traversal. -/
theorem foldLeafRoutes_map {α β : Type*} (graph : DAG n) (weights : Channel n → ℕ)
    (index : Fin graph.nodeCount) (counters : WeightedCounters n) (initial : α)
    (first : LeafRoute → Channel n → WeightedCounters n → α → α)
    (second : LeafRoute → Channel n → WeightedCounters n → β → β)
    (f : α → β)
    (commutes : ∀ route head current accumulator,
      second route head current (f accumulator) = f (first route head current accumulator)) :
    graph.foldLeafRoutes weights index counters (f initial) second =
      let result := graph.foldLeafRoutes weights index counters initial first
      (result.1, f result.2) := by
  have claim : ∀ bound : ℕ, ∀ current : Fin graph.nodeCount, current.val = bound →
      ∀ state accumulator first second,
      (∀ route head leafState previous,
        second route head leafState (f previous) = f (first route head leafState previous)) →
      graph.foldLeafRoutes weights current state (f accumulator) second =
        let result := graph.foldLeafRoutes weights current state accumulator first
        (result.1, f result.2) := by
    intro bound
    induction bound using Nat.strong_induction_on with
    | h bound ih =>
      intro current currentBound state accumulator first second relation
      cases equation : graph.node current with
      | zero => simp only [foldLeafRoutes, equation]
      | liveAnd left right => simp only [foldLeafRoutes, equation]
      | input head => simp only [foldLeafRoutes, equation, relation]
      | disj refs =>
          rw [foldLeafRoutes.eq_def (graph := graph) (weights := weights)
            (index := current) (counters := state) (initial := f accumulator) (visit := second),
            foldLeafRoutes.eq_def (graph := graph) (weights := weights)
            (index := current) (counters := state) (initial := accumulator) (visit := first)]
          simp only [equation]
          apply List.foldl_hom (fun previous : WeightedCounters n × α => (previous.1, f previous.2))
            (init := (state, accumulator))
          intro previous position
          have earlier : (graph.childIndex current (refs.get position)).val < bound := by
            simpa only [DAG.childIndex, currentBound] using (refs.get position).isLt
          exact ih _ earlier _ rfl previous.1 previous.2 _ _
            (fun route head leafState previous => relation (position.val :: route) head leafState previous)
      | guard child labels =>
          have earlier : (graph.childIndex current child).val < bound := by
            simpa only [DAG.childIndex, currentBound] using child.isLt
          rw [foldLeafRoutes.eq_def (graph := graph) (weights := weights)
            (index := current) (counters := state) (initial := f accumulator) (visit := second),
            foldLeafRoutes.eq_def (graph := graph) (weights := weights)
            (index := current) (counters := state) (initial := accumulator) (visit := first)]
          simp only [equation]
          rw [ih _ earlier _ rfl _ accumulator _ _
            (fun route head leafState previous => relation (0 :: route) head leafState previous)]
  exact claim index.val index rfl counters initial first second commutes

private def reverseBest (best : Option (LeafRoute × ℕ)) : Option (LeafRoute × ℕ) :=
  best.map fun result => (result.1.reverse, result.2)

@[simp] private theorem reverseBest_reverseBest (best : Option (LeafRoute × ℕ)) :
    reverseBest (reverseBest best) = best := by
  cases best <;> simp [reverseBest]

private theorem keepBestRoute_reverse (b : ℕ) (target : Channel n) (total : ℕ)
    (route : LeafRoute) (head : Channel n) (state : WeightedCounters n)
    (best : Option (LeafRoute × ℕ)) :
    keepBestRoute b target total route.reverse head state (reverseBest best) =
      reverseBest (keepBestRoute b target total route head state best) := by
  by_cases feasible : state.1 head = 0 ∧ (b ≠ 1 ∨ state.1 target = 0)
  · cases best with
    | none => simp [keepBestRoute, feasible, reverseBest]
    | some previous =>
        simp only [reverseBest, Option.map_some, keepBestRoute, ite_eq_left feasible]
        split <;> rfl
  · simp [keepBestRoute, feasible]

/-- Select one reversed cursor and reverse only the winning route. -/
def bestLeafRouteCursor (graph : DAG n) (weights : Channel n → ℕ) (b : ℕ)
    (target : Channel n) (root : Fin graph.nodeCount) : Option (LeafRoute × ℕ) :=
  ((graph.foldLeafCursor weights root [] (fun _ => 0, 0) none
    (keepBestRoute b target (channelWeight weights Finset.univ))).2).map
      (fun best => (best.1.reverse, best.2))

/-- Channel-set reconstruction is performed once, after cursor selection. -/
def bestLeafSetCursor (graph : DAG n) (weights : Channel n → ℕ) (b : ℕ)
    (target : Channel n) (root : Fin graph.nodeCount) : Option (Finset (Channel n)) := do
  let best ← graph.bestLeafRouteCursor weights b target root
  let leaf ← graph.reconstructRoute root best.1
  pure (fullUnblocked leaf.2.toFinset)

/-- Select a best leaf route using one path counter state and one best accumulator. -/
def bestLeafRoute (graph : DAG n) (weights : Channel n → ℕ) (b : ℕ)
    (target : Channel n) (root : Fin graph.nodeCount) : Option (LeafRoute × ℕ) :=
  (graph.foldLeafRoutes weights root (fun _ => 0, 0) none
    (keepBestRoute b target (channelWeight weights Finset.univ))).2

/-- Reversed-routePrefix selection has exactly the semantic forward-route fold result. -/
theorem bestLeafRouteCursor_eq (graph : DAG n) (weights : Channel n → ℕ) (b : ℕ)
    (target : Channel n) (root : Fin graph.nodeCount) :
    graph.bestLeafRouteCursor weights b target root = graph.bestLeafRoute weights b target root := by
  unfold bestLeafRouteCursor bestLeafRoute
  rw [foldLeafCursor_eq_fold]
  simp only [List.append_nil]
  have transport := graph.foldLeafRoutes_map weights root (fun _ => 0, 0) none
    (keepBestRoute b target (channelWeight weights Finset.univ))
    (fun route head current previous =>
      keepBestRoute b target (channelWeight weights Finset.univ) route.reverse head current previous)
    reverseBest (keepBestRoute_reverse b target (channelWeight weights Finset.univ))
  have accumulator := congrArg Prod.snd transport
  simp only [reverseBest, Option.map_none] at accumulator
  change reverseBest _ = _
  rw [accumulator]
  exact reverseBest_reverseBest _

/-- A selected route certifies an admissible full-unblocked set and its exact score. -/
theorem bestLeafRoute_sound (graph : DAG n) (weights : Channel n → ℕ) (b : ℕ)
    (target : Channel n) (root : Fin graph.nodeCount) (route : LeafRoute) (score : ℕ)
    (selected : graph.bestLeafRoute weights b target root = some (route, score)) :
    ∃ head blocked, RoutePath graph root route head blocked ∧
      pathFeasible b target head blocked ∧
      score = channelWeight weights (fullUnblocked blocked) := by
  let P : Option (LeafRoute × ℕ) → Prop := fun best =>
    ∀ chosen value, best = some (chosen, value) →
      ∃ head blocked, RoutePath graph root chosen head blocked ∧
        pathFeasible b target head blocked ∧
        value = channelWeight weights (fullUnblocked blocked)
  have initialValid : P none := by
    intro chosen value impossible
    cases impossible
  have valid : P (graph.bestLeafRoute weights b target root) := by
    apply graph.foldLeafRoutes_preserves weights root (fun _ => 0, 0) none
      (keepBestRoute b target (channelWeight weights Finset.univ)) P initialValid
      (by simp [blockedChannels, channelWeight])
    intro chosen head blocked state path union weight previous previousValid
    apply keepBestRoute_preserves b target _ chosen head state previous P previousValid
    intro eligible
    have initialEmpty : blockedChannels (fun _ : Channel n => 0) = ∅ := by
      simp [blockedChannels]
    have exactBlocked : blockedChannels state.1 = blocked := by
      simpa only [initialEmpty, Finset.empty_union] using union
    have feasible : pathFeasible b target head blocked := by
      rw [← exactBlocked, pathFeasible_counter_iff]
      refine ⟨eligible.1, ?_⟩
      intro one
      rcases eligible.2 with many | targetZero
      · exact False.elim (many one)
      · exact targetZero
    intro resultRoute resultScore resultEqual
    have equal := Option.some.inj resultEqual
    have routeEqual : chosen = resultRoute := congrArg Prod.fst equal
    have scoreEqual : channelWeight weights Finset.univ - state.2 = resultScore :=
      congrArg Prod.snd equal
    refine ⟨head, blocked, ?_, feasible, ?_⟩
    · simpa only [routeEqual] using path
    · rw [← scoreEqual, weight, exactBlocked, fullUnblocked_weight]
  exact valid route score selected

/-- Each feasible route supplies a lower bound on the final selected score. -/
theorem bestLeafRoute_dominates_path (graph : DAG n) (weights : Channel n → ℕ) (b : ℕ)
    (target : Channel n) {root : Fin graph.nodeCount} {route : LeafRoute}
    {head : Channel n} {blocked : Finset (Channel n)}
    (path : RoutePath graph root route head blocked)
    (feasible : pathFeasible b target head blocked) :
    RouteScoreAtLeast (channelWeight weights (fullUnblocked blocked))
      (graph.bestLeafRoute weights b target root) := by
  apply graph.foldLeafRoutes_hits weights path (fun _ => 0, 0) none
    (keepBestRoute b target (channelWeight weights Finset.univ))
    (RouteScoreAtLeast (channelWeight weights (fullUnblocked blocked)))
    (by simp [blockedChannels, channelWeight])
  · intro chosen leaf current previous good
    exact keepBestRoute_monotone b target _ chosen leaf current previous _ good
  · intro current union weight previous
    have exactBlocked : blockedChannels current.1 = blocked := by
      simpa [blockedChannels] using union
    have counterFeasible : current.1 head = 0 ∧ (b ≠ 1 ∨ current.1 target = 0) := by
      have translated := (pathFeasible_counter_iff b target head current.1).mp
        (by simpa only [exactBlocked] using feasible)
      refine ⟨translated.1, ?_⟩
      by_cases one : b = 1
      · exact Or.inr (translated.2 one)
      · exact Or.inl one
    have hit := keepBestRoute_hits b target (channelWeight weights Finset.univ)
      route head current previous counterFeasible
    rw [weight, exactBlocked, ← fullUnblocked_weight] at hit
    exact hit

/-- No admissible true set exceeds the score of a returned route. -/
theorem bestLeafRoute_optimal (graph : DAG n) (guarded : graph.Guarded)
    (weights : Channel n → ℕ) (b : ℕ) (target : Channel n)
    (root : Fin graph.nodeCount) (route : LeafRoute) (score : ℕ)
    (selected : graph.bestLeafRoute weights b target root = some (route, score))
    (K : Finset (Channel n)) (eligible : Admissible b target K)
    (value : graph.eval (assignmentOfSet K) root = true) :
    channelWeight weights K ≤ score := by
  obtain ⟨head, blocked, path, feasible, fullEligible, fullTrue, dominates⟩ :=
    graph.exists_dominating_path guarded b target root weights K eligible value
  obtain ⟨witness, routePath⟩ := path.exists_route
  obtain ⟨bestRoute, bestScore, actual, bound⟩ :=
    graph.bestLeafRoute_dominates_path weights b target routePath feasible
  have equal := Option.some.inj (selected.symm.trans actual)
  have scores : score = bestScore := congrArg Prod.snd equal
  exact dominates.trans (by simpa only [scores] using bound)

/-- Every admissible true valuation forces the fold to select a leaf. -/
theorem bestLeafRoute_exists (graph : DAG n) (guarded : graph.Guarded)
    (weights : Channel n → ℕ) (b : ℕ) (target : Channel n)
    (root : Fin graph.nodeCount) (K : Finset (Channel n))
    (eligible : Admissible b target K)
    (value : graph.eval (assignmentOfSet K) root = true) :
    ∃ route score, graph.bestLeafRoute weights b target root = some (route, score) := by
  obtain ⟨head, blocked, path, feasible, fullEligible, fullTrue, dominates⟩ :=
    graph.exists_dominating_path guarded b target root weights K eligible value
  obtain ⟨route, routePath⟩ := path.exists_route
  obtain ⟨bestRoute, bestScore, selected, bound⟩ :=
    graph.bestLeafRoute_dominates_path weights b target routePath feasible
  exact ⟨bestRoute, bestScore, selected⟩

/-- Reconstruct the guard union only for the selected route. -/
def bestLeafSet (graph : DAG n) (weights : Channel n → ℕ) (b : ℕ)
    (target : Channel n) (root : Fin graph.nodeCount) : Option (Finset (Channel n)) := do
  let best ← graph.bestLeafRoute weights b target root
  let leaf ← graph.reconstructRoute root best.1
  pure (fullUnblocked leaf.2.toFinset)

/-- Every returned reconstructed set is a reachable true valuation at the root. -/
theorem bestLeafSet_sound (graph : DAG n) (weights : Channel n → ℕ) (b : ℕ)
    (target : Channel n) (root : Fin graph.nodeCount) (K : Finset (Channel n))
    (returned : graph.bestLeafSet weights b target root = some K) :
    Admissible b target K ∧ graph.eval (assignmentOfSet K) root = true := by
  unfold bestLeafSet at returned
  cases selected : graph.bestLeafRoute weights b target root with
  | none => simp only [selected, Option.bind_none] at returned; cases returned
  | some best =>
      obtain ⟨head, blocked, path, feasible, score⟩ :=
        graph.bestLeafRoute_sound weights b target root best.1 best.2 selected
      obtain ⟨labels, readback, union⟩ := graph.reconstructRoute_of_path path
      simp [selected, readback] at returned
      have equal : fullUnblocked blocked = K := by
        simpa only [union] using returned
      rw [← equal]
      exact ⟨fullUnblocked_admissible b target head blocked feasible,
        path.livePath.fullUnblocked_true b target feasible⟩

/-- A detecting healthy-zero query obtains a reconstructed witness. -/
theorem bestLeafSet_exists (graph : DAG n) (guarded : graph.Guarded)
    (weights : Channel n → ℕ) (b : ℕ) (target : Channel n)
    (root : Fin graph.nodeCount) (K : Finset (Channel n))
    (eligible : Admissible b target K)
    (value : graph.eval (assignmentOfSet K) root = true) :
    ∃ result, graph.bestLeafSet weights b target root = some result := by
  obtain ⟨route, score, selected⟩ := graph.bestLeafRoute_exists guarded weights b target root K eligible value
  obtain ⟨head, blocked, path, feasible, exactScore⟩ :=
    graph.bestLeafRoute_sound weights b target root route score selected
  obtain ⟨labels, readback, union⟩ := graph.reconstructRoute_of_path path
  refine ⟨fullUnblocked labels.toFinset, ?_⟩
  simp [bestLeafSet, selected, readback]

/-- The returned full set maximizes nonnegative weights over all admissible true sets. -/
theorem bestLeafSet_optimal (graph : DAG n) (guarded : graph.Guarded)
    (weights : Channel n → ℕ) (b : ℕ) (target : Channel n)
    (root : Fin graph.nodeCount) (result : Finset (Channel n))
    (returned : graph.bestLeafSet weights b target root = some result)
    (K : Finset (Channel n)) (eligible : Admissible b target K)
    (value : graph.eval (assignmentOfSet K) root = true) :
    channelWeight weights K ≤ channelWeight weights result := by
  unfold bestLeafSet at returned
  cases selected : graph.bestLeafRoute weights b target root with
  | none => simp only [selected, Option.bind_none] at returned; cases returned
  | some best =>
      obtain ⟨head, blocked, path, feasible, score⟩ :=
        graph.bestLeafRoute_sound weights b target root best.1 best.2 selected
      obtain ⟨labels, readback, union⟩ := graph.reconstructRoute_of_path path
      simp [selected, readback] at returned
      have equal : fullUnblocked blocked = result := by
        simpa only [union] using returned
      rw [← equal, ← score]
      exact graph.bestLeafRoute_optimal guarded weights b target root best.1 best.2 selected K eligible value

/-- Exact failure characterization for a positive-root query. -/
theorem bestLeafSet_none_iff (graph : DAG n) (guarded : graph.Guarded)
    (weights : Channel n → ℕ) (b : ℕ) (target : Channel n)
    (root : Fin graph.nodeCount) :
    graph.bestLeafSet weights b target root = none ↔
      ¬ ∃ K, Admissible b target K ∧ graph.eval (assignmentOfSet K) root = true := by
  constructor
  · intro absent ⟨K, eligible, value⟩
    obtain ⟨result, returned⟩ := graph.bestLeafSet_exists guarded weights b target root K eligible value
    rw [absent] at returned
    cases returned
  · intro impossible
    cases returned : graph.bestLeafSet weights b target root with
    | none => rfl
    | some result =>
        obtain ⟨eligible, value⟩ := graph.bestLeafSet_sound weights b target root result returned
        exact False.elim (impossible ⟨result, eligible, value⟩)

/-- Healthy-zero outputs reduce detection and weight optimization to this traversal. -/
theorem bestLeafSet_healthyZero (graph : DAG n) (guarded : graph.Guarded)
    (weights : Channel n → ℕ) (b : ℕ) (target : Channel n)
    (root : Fin graph.nodeCount)
    (healthy : graph.eval (assignmentOfSet {target}) root = false)
    (result : Finset (Channel n))
    (returned : graph.bestLeafSet weights b target root = some result) :
    Admissible b target result ∧
      graph.eval (assignmentOfSet result) root ≠ graph.eval (assignmentOfSet {target}) root ∧
      ∀ K, Admissible b target K →
        graph.eval (assignmentOfSet K) root ≠ graph.eval (assignmentOfSet {target}) root →
        channelWeight weights K ≤ channelWeight weights result := by
  obtain ⟨eligible, value⟩ := graph.bestLeafSet_sound weights b target root result returned
  refine ⟨eligible, by rw [value, healthy]; decide, ?_⟩
  intro K admissible differs
  have trueValue : graph.eval (assignmentOfSet K) root = true := by
    cases actual : graph.eval (assignmentOfSet K) root <;> simp_all
  exact graph.bestLeafSet_optimal guarded weights b target root result returned K admissible trueValue

/-- The production cursor selector reconstructs precisely the certified optimal set. -/
theorem bestLeafSetCursor_eq (graph : DAG n) (weights : Channel n → ℕ) (b : ℕ)
    (target : Channel n) (root : Fin graph.nodeCount) :
    graph.bestLeafSetCursor weights b target root = graph.bestLeafSet weights b target root := by
  unfold bestLeafSetCursor bestLeafSet
  rw [bestLeafRouteCursor_eq]


open CNF ZeroSystem

/-- Root-local reachability row. In the one-bus branch the target unit alone
implies nonemptiness, so no ambient n-literal row is emitted. -/
def forestZeroSystem (graph : DAG n) (b : ℕ) (target : Channel n)
    (root : Fin graph.nodeCount) : CNF.Formula graph.ZeroVar :=
  ofClauses (graph.forwardClauses ++
    [positiveClause (if b = 1 then [.inl target] else (List.finRange n).map Sum.inl),
      implicationClause (.inr root) []])

theorem forestZeroSystem_satisfies_iff (graph : DAG n) (b : ℕ) (target : Channel n)
    (root : Fin graph.nodeCount) (K : Finset (Channel n))
    (activities : Fin graph.nodeCount → Bool) :
    CNF.Satisfies (graph.zeroAssignment (assignmentOfSet K) activities)
      (graph.forestZeroSystem b target root) ↔
    graph.ForwardModel (assignmentOfSet K) activities ∧
      Admissible b target K ∧ activities root = false := by
  simp only [forestZeroSystem, satisfies_ofClauses, List.forall_mem_append,
    List.forall_mem_cons, List.forall_mem_nil, and_true,
    forwardClauses_holds_iff, positiveClause_holds, implicationClause_holds]
  by_cases one : b = 1
  · simp only [ite_eq_left one, List.mem_singleton, exists_eq_left, zeroAssignment]
    constructor
    · rintro ⟨forward, targetTrue, rootFalse⟩
      have present : target ∈ K := by simpa [assignmentOfSet] using targetTrue
      exact ⟨forward, ⟨⟨target, present⟩, fun _ => present⟩, by simpa using rootFalse⟩
    · rintro ⟨forward, eligible, rootFalse⟩
      exact ⟨forward, by simpa [assignmentOfSet] using eligible.2 one, by simpa using rootFalse⟩
  · simp [one, zeroAssignment, Admissible, Finset.Nonempty, assignmentOfSet,
      Bool.not_eq_true, and_assoc]

theorem forestZeroSystem_equivalent (graph : DAG n) (b : ℕ) (target : Channel n)
    (root : Fin graph.nodeCount) (values : graph.ZeroVar → Bool) :
    CNF.Satisfies values (graph.forestZeroSystem b target root) ↔
      CNF.Satisfies values (graph.zeroSystem b target root ∅ ∅) := by
  rw [← graph.zeroAssignment_channelSet values, graph.forestZeroSystem_satisfies_iff,
    graph.zeroSystem_satisfies_iff]
  simp [ExtendsFixed]

def finiteForestZeroSystem (graph : DAG n) (b : ℕ) (target : Channel n)
    (root : Fin graph.nodeCount) : CNF.FiniteFormula (n + graph.nodeCount) :=
  CNF.relabel graph.zeroIndex (graph.forestZeroSystem b target root)

/-- Allocate only coordinates that actually occur in the cone's emitted rows. -/
def compactForestZeroSystem (graph : DAG n) (b : ℕ) (target : Channel n)
    (root : Fin graph.nodeCount) :=
  SparseFormula.compact (graph.finiteForestZeroSystem b target root)

theorem compactForestZeroSystem_satisfiable_iff (graph : DAG n) (guarded : graph.Guarded)
    (b : ℕ) (target : Channel n) (root : Fin graph.nodeCount) :
    CNF.Satisfiable (graph.compactForestZeroSystem b target root) ↔
      ∃ K, Admissible b target K ∧ graph.eval (assignmentOfSet K) root = false := by
  rw [compactForestZeroSystem, SparseFormula.compact_satisfiable_iff]
  have relabel : CNF.Satisfiable (graph.finiteForestZeroSystem b target root) ↔
      CNF.Satisfiable (graph.forestZeroSystem b target root) := by
    exact CNF.satisfiable_relabel_equiv graph.zeroIndex _
  rw [relabel]
  have equivalent : CNF.Satisfiable (graph.forestZeroSystem b target root) ↔
      CNF.Satisfiable (graph.zeroSystem b target root ∅ ∅) := by
    apply exists_congr
    intro values
    exact graph.forestZeroSystem_equivalent b target root values
  rw [equivalent, graph.zeroSystem_satisfiable_iff guarded]
  simp [ExtendsFixed]

theorem forestZeroSystem_dualHorn (graph : DAG n) (guarded : graph.Guarded)
    (b : ℕ) (target : Channel n) (root : Fin graph.nodeCount) :
    Horn.DualHorn (graph.forestZeroSystem b target root) := by
  intro clause present
  have row : clause ∈ graph.forwardClauses ++
      [positiveClause (if b = 1 then [.inl target] else (List.finRange n).map Sum.inl),
        implicationClause (.inr root) []] := by
    simpa only [forestZeroSystem, ofClauses, List.mem_toArray] using present
  rcases List.mem_append.mp row with forward | reach
  · obtain ⟨node, _, localMember⟩ := List.mem_flatMap.mp forward
    exact graph.nodeClauses_dualHorn guarded node clause localMember
  · rcases List.mem_cons.mp reach with rfl | final
    · exact positiveClause_dualHorn _
    · have same := List.mem_singleton.mp final
      subst clause
      exact implicationClause_dualHorn _ _

theorem compactForestZeroSystem_dualHorn (graph : DAG n) (guarded : graph.Guarded)
    (b : ℕ) (target : Channel n) (root : Fin graph.nodeCount) :
    Horn.DualHorn (graph.compactForestZeroSystem b target root) :=
  SparseFormula.compact_dualHorn (graph.finiteForestZeroSystem b target root)
    (SparseFormula.relabel_dualHorn graph.zeroIndex (graph.forestZeroSystem b target root)
    (graph.forestZeroSystem_dualHorn guarded b target root))

/-- Execute the worklist only over literal-support coordinates, then project the
actual channel values; omitted coordinates are fixed false. -/
def solveForestZero (graph : DAG n) (b : ℕ) (target : Channel n)
    (root : Fin graph.nodeCount) : Option (Finset (Channel n)) :=
  (Horn.Worklist.solveFormula (graph.compactForestZeroSystem b target root)).map fun values =>
    graph.zeroChannelSet (SparseFormula.liftAssignment
      (graph.finiteForestZeroSystem b target root) (fun slot => values[slot.val]) ∘ graph.zeroIndex)

theorem solveForestZero_none_iff (graph : DAG n) (guarded : graph.Guarded)
    (b : ℕ) (target : Channel n) (root : Fin graph.nodeCount) :
    graph.solveForestZero b target root = none ↔
      ¬ ∃ K, Admissible b target K ∧ graph.eval (assignmentOfSet K) root = false := by
  rw [solveForestZero, Option.map_eq_none_iff,
    Horn.Worklist.solveFormula_none_iff _ (graph.compactForestZeroSystem_dualHorn guarded b target root),
    CNF.Unsatisfiable]
  rw [graph.compactForestZeroSystem_satisfiable_iff guarded]

theorem solveForestZero_some (graph : DAG n) (guarded : graph.Guarded)
    (b : ℕ) (target : Channel n) (root : Fin graph.nodeCount) (K : Finset (Channel n))
    (returned : graph.solveForestZero b target root = some K) :
    Admissible b target K ∧ graph.eval (assignmentOfSet K) root = false := by
  unfold solveForestZero at returned
  obtain ⟨values, selected, rfl⟩ := Option.map_eq_some_iff.mp returned
  have compactModel := (Horn.Worklist.solveFormula_some_model _
    (graph.compactForestZeroSystem_dualHorn guarded b target root) values selected).1
  have finiteModel := SparseFormula.liftAssignment_model _ _ compactModel
  have localModel := (CNF.satisfies_relabel graph.zeroIndex _ _).mp finiteModel
  have originalModel := (graph.forestZeroSystem_equivalent b target root _).mp localModel
  have combined := originalModel
  rw [← graph.zeroAssignment_channelSet
    (SparseFormula.liftAssignment (graph.finiteForestZeroSystem b target root)
      (fun slot => values[slot.val]) ∘ graph.zeroIndex)] at combined
  obtain ⟨forward, ⟨eligible, _⟩, falseRoot⟩ :=
    (graph.zeroSystem_satisfies_iff b target root ∅ ∅ _ _).mp combined
  refine ⟨eligible, ?_⟩
  cases value : graph.eval (assignmentOfSet _) root with
  | false => rfl
  | true =>
    have actual := graph.eval_true_implies_activity guarded _ _ forward root value
    rw [falseRoot] at actual
    cases actual

/-- Solve on the root's actual sharing-preserving cone. -/
def solveForestConeZero (graph : DAG n) (b : ℕ) (target : Channel n)
    (root : Fin graph.nodeCount) : Option (Finset (Channel n)) :=
  (graph.singleCone root).solveForestZero b target (graph.singleConeRoot root)

theorem solveForestConeZero_some (graph : DAG n) (guarded : graph.Guarded)
    (b : ℕ) (target : Channel n) (root : Fin graph.nodeCount) (K : Finset (Channel n))
    (returned : graph.solveForestConeZero b target root = some K) :
    Admissible b target K ∧ graph.eval (assignmentOfSet K) root = false := by
  obtain ⟨eligible, value⟩ := (graph.singleCone root).solveForestZero_some
    (graph.singleCone_guarded guarded root) b target (graph.singleConeRoot root) K returned
  exact ⟨eligible, by simpa only [singleCone_eval] using value⟩

theorem solveForestConeZero_none_iff (graph : DAG n) (guarded : graph.Guarded)
    (b : ℕ) (target : Channel n) (root : Fin graph.nodeCount) :
    graph.solveForestConeZero b target root = none ↔
      ¬ ∃ K, Admissible b target K ∧ graph.eval (assignmentOfSet K) root = false := by
  simpa only [solveForestConeZero, singleCone_eval] using
    (graph.singleCone root).solveForestZero_none_iff
      (graph.singleCone_guarded guarded root) b target (graph.singleConeRoot root)

/-- A bounded omitted-channel scan bypasses the many-bus solver; otherwise the
actual cone-local sparse system is solved. -/
def sparseForestZero (graph : DAG n) (b : ℕ) (target : Channel n)
    (root : Fin graph.nodeCount) : Option (Finset (Channel n)) :=
  if b = 1 then graph.solveForestConeZero b target root
  else match graph.firstUnmarked root with
    | some channel => some {channel}
    | none => graph.solveForestConeZero b target root

theorem sparseForestZero_some (graph : DAG n) (guarded : graph.Guarded)
    (b : ℕ) (target : Channel n) (root : Fin graph.nodeCount) (K : Finset (Channel n))
    (returned : graph.sparseForestZero b target root = some K) :
    Admissible b target K ∧ graph.eval (assignmentOfSet K) root = false := by
  unfold sparseForestZero at returned
  split at returned
  · exact graph.solveForestConeZero_some guarded b target root K returned
  · rename_i notOne
    cases found : graph.firstUnmarked root with
    | none =>
      rw [found] at returned
      exact graph.solveForestConeZero_some guarded b target root K returned
    | some channel =>
      rw [found] at returned
      have equal := Option.some.inj returned
      subst K
      exact ⟨⟨by simp, fun one => False.elim (notOne one)⟩,
        unmarked_singleton_zero graph root channel (graph.firstUnmarked_some root channel found)⟩

theorem sparseForestZero_none_iff (graph : DAG n) (guarded : graph.Guarded)
    (b : ℕ) (target : Channel n) (root : Fin graph.nodeCount) :
    graph.sparseForestZero b target root = none ↔
      ¬ ∃ K, Admissible b target K ∧ graph.eval (assignmentOfSet K) root = false := by
  unfold sparseForestZero
  split
  · exact graph.solveForestConeZero_none_iff guarded b target root
  · rename_i notOne
    cases found : graph.firstUnmarked root with
    | none => exact graph.solveForestConeZero_none_iff guarded b target root
    | some channel =>
      simp only [Option.some_ne_none, false_iff, not_not]
      exact ⟨{channel}, ⟨by simp, fun one => False.elim (notOne one)⟩,
        unmarked_singleton_zero graph root channel (graph.firstUnmarked_some root channel found)⟩

/-- A shared-table root query uses a counter leaf traversal on healthy-zero
outputs and a cone-local sparse zero solver on healthy-one outputs. Resource refinement of the
zero branch is separate from this semantic assembly. -/
def forestRootQuery (graph : DAG n) (b : ℕ) (target : Channel n)
    (healthy : Fin graph.nodeCount → Bool) (root : Fin graph.nodeCount) :
    Option (Finset (Channel n)) :=
  if healthy root then graph.sparseForestZero b target root
  else graph.bestLeafSetCursor (fun _ => 0) b target root

theorem forestRootQuery_some (graph : DAG n) (guarded : graph.Guarded)
    (b : ℕ) (target : Channel n) (root : Fin graph.nodeCount)
    (K : Finset (Channel n))
    (returned : graph.forestRootQuery b target
      (graph.eval (assignmentOfSet {target})) root = some K) :
    Admissible b target K ∧
      graph.eval (assignmentOfSet K) root ≠ graph.eval (assignmentOfSet {target}) root := by
  cases healthy : graph.eval (assignmentOfSet {target}) root with
  | false =>
    simp only [forestRootQuery, healthy, Bool.false_eq_true, ite_false,
      bestLeafSetCursor_eq] at returned
    obtain ⟨eligible, value⟩ := graph.bestLeafSet_sound (fun _ => 0) b target root K returned
    exact ⟨eligible, by rw [value]; decide⟩
  | true =>
    simp only [forestRootQuery, healthy, ite_true] at returned
    obtain ⟨eligible, value⟩ := graph.sparseForestZero_some guarded b target root K returned
    exact ⟨eligible, by rw [value]; decide⟩

theorem forestRootQuery_none_iff (graph : DAG n) (guarded : graph.Guarded)
    (b : ℕ) (target : Channel n) (root : Fin graph.nodeCount) :
    graph.forestRootQuery b target (graph.eval (assignmentOfSet {target})) root = none ↔
      ¬ ∃ K, Admissible b target K ∧
        graph.eval (assignmentOfSet K) root ≠ graph.eval (assignmentOfSet {target}) root := by
  cases healthy : graph.eval (assignmentOfSet {target}) root with
  | false =>
    simp only [forestRootQuery, healthy, Bool.false_eq_true, ite_false,
      bestLeafSetCursor_eq, bestLeafSet_none_iff graph guarded]
    simp only [Bool.not_eq_false]
  | true =>
    simp only [forestRootQuery, healthy, ite_true, sparseForestZero_none_iff graph guarded]
    simp only [Bool.not_eq_true]

/-- Compute healthy values once, then fold root queries. Duplicate root positions
remain in the supplied root list; no family of channel sets is retained. -/
def detectForestSet (graph : DAG n) (b : ℕ) (target : Channel n) (drive : Bool) :
    Option (Finset (Channel n)) :=
  if drive then
    let healthy := graph.evalTable (assignmentOfSet {target})
    firstSuccess (graph.forestRootQuery b target healthy) graph.roots
  else none

theorem detectForestSet_some (graph : DAG n) (guarded : graph.Guarded)
    (b : ℕ) (target : Channel n) (drive : Bool) (K : Finset (Channel n))
    (returned : graph.detectForestSet b target drive = some K) :
    drive = true ∧ Admissible b target K ∧ ∃ root ∈ graph.roots,
      graph.eval (assignmentOfSet K) root ≠ graph.eval (assignmentOfSet {target}) root := by
  cases drive with
  | false => simp [detectForestSet] at returned
  | true =>
    simp only [detectForestSet, ite_true, evalTable_eq_eval] at returned
    obtain ⟨root, present, query⟩ := firstSuccess_some _ _ K returned
    obtain ⟨eligible, differs⟩ := graph.forestRootQuery_some guarded b target root K query
    exact ⟨rfl, eligible, root, present, differs⟩

theorem detectForestSet_none_iff (graph : DAG n) (guarded : graph.Guarded)
    (b : ℕ) (target : Channel n) (drive : Bool) :
    graph.detectForestSet b target drive = none ↔
      ¬ (drive = true ∧ ∃ root ∈ graph.roots, ∃ K, Admissible b target K ∧
        graph.eval (assignmentOfSet K) root ≠ graph.eval (assignmentOfSet {target}) root) := by
  cases drive with
  | false => simp [detectForestSet]
  | true =>
    simp only [detectForestSet, ite_true, evalTable_eq_eval, firstSuccess_none_iff, true_and]
    constructor
    · intro absent ⟨root, present, K, eligible, differs⟩
      exact (graph.forestRootQuery_none_iff guarded b target root).mp
        (absent root present) ⟨K, eligible, differs⟩
    · intro absent root present
      apply (graph.forestRootQuery_none_iff guarded b target root).mpr
      rintro ⟨K, eligible, differs⟩
      exact absent ⟨root, present, K, eligible, differs⟩

/-! Generic arithmetic production kernel. The cached weight lives in an ordered
additive group, so rational and real mathematical weights share the same
operations. Optimality requires explicit nonnegativity; encoded-word costs are
not assertions of these executable definitions. -/
section GenericArithmetic

variable {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]

def enterGenericGuards (weights : Channel n → W) (state : GuardCounters n × W)
    (labels : List (Channel n)) : GuardCounters n × W :=
  labels.foldl (GenericWeight.enter weights) state

def leaveGenericGuards (weights : Channel n → W) (state : GuardCounters n × W)
    (labels : List (Channel n)) : GuardCounters n × W :=
  labels.foldl (GenericWeight.leave weights) state

theorem enterGenericGuards_counters (weights : Channel n → W)
    (state : GuardCounters n × W) (labels : List (Channel n)) :
    (enterGenericGuards weights state labels).1 = enterGuards state.1 labels := by
  induction labels generalizing state with
  | nil => rfl
  | cons label rest ih =>
      simpa only [enterGenericGuards, List.foldl_cons, enterGuards,
        GenericWeight.enter] using ih (GenericWeight.enter weights state label)

theorem leaveGenericGuards_counters (weights : Channel n → W)
    (state : GuardCounters n × W) (labels : List (Channel n)) :
    (leaveGenericGuards weights state labels).1 = leaveGuards state.1 labels := by
  induction labels generalizing state with
  | nil => rfl
  | cons label rest ih =>
      simpa only [leaveGenericGuards, List.foldl_cons, leaveGuards,
        GenericWeight.leave] using ih (GenericWeight.leave weights state label)

theorem enterGenericGuards_correct (weights : Channel n → W)
    (state : GuardCounters n × W) (labels : List (Channel n))
    (invariant : state.2 = GenericWeight.total weights (blockedChannels state.1)) :
    (enterGenericGuards weights state labels).2 =
      GenericWeight.total weights (blockedChannels (enterGenericGuards weights state labels).1) := by
  induction labels generalizing state with
  | nil => exact invariant
  | cons label rest ih => exact ih _ (GenericWeight.enter_correct weights state label invariant)

theorem leaveGenericGuards_correct (weights : Channel n → W)
    (state : GuardCounters n × W) (labels : List (Channel n))
    (invariant : state.2 = GenericWeight.total weights (blockedChannels state.1)) :
    (leaveGenericGuards weights state labels).2 =
      GenericWeight.total weights (blockedChannels (leaveGenericGuards weights state labels).1) := by
  induction labels generalizing state with
  | nil => exact invariant
  | cons label rest ih => exact ih _ (GenericWeight.leave_correct weights state label invariant)

theorem leave_enterGenericGuards (weights : Channel n → W)
    (state : GuardCounters n × W) (labels : List (Channel n))
    (invariant : state.2 = GenericWeight.total weights (blockedChannels state.1)) :
    leaveGenericGuards weights (enterGenericGuards weights state labels) labels = state := by
  apply Prod.ext
  · rw [leaveGenericGuards_counters, enterGenericGuards_counters, leave_enterGuards]
  · rw [leaveGenericGuards_correct weights _ _
      (enterGenericGuards_correct weights state labels invariant)]
    rw [leaveGenericGuards_counters, enterGenericGuards_counters, leave_enterGuards]
    exact invariant.symm

/-- Reversed route cursors and cached union weights are updated only along
actual guard incidences. No blocked-set sum is recomputed at a leaf. -/
def foldGenericLeafCursor {α : Type*} (graph : DAG n) (weights : Channel n → W)
    (index : Fin graph.nodeCount) (routePrefix : LeafRoute) (counters : GuardCounters n × W)
    (initial : α) (visit : LeafRoute → Channel n → (GuardCounters n × W) → α → α) :
    (GuardCounters n × W) × α :=
  match graph.node index with
  | .zero => (counters, initial)
  | .input head => (counters, visit routePrefix head counters initial)
  | .disj refs =>
      (List.finRange refs.length).foldl (fun state position =>
        graph.foldGenericLeafCursor weights (graph.childIndex index (refs.get position))
          (position.val :: routePrefix) state.1 state.2 visit) (counters, initial)
  | .guard child labels =>
      let result := graph.foldGenericLeafCursor weights (graph.childIndex index child)
        (0 :: routePrefix) (enterGenericGuards weights counters labels) initial visit
      (leaveGenericGuards weights result.1 labels, result.2)
  | .liveAnd _ _ => (counters, initial)
termination_by index.val
decreasing_by all_goals exact graph.childIndex_lt _ _

/-- Cached generic weights and counters are restored after every complete subtree,
including nested repeated guards and duplicated child positions. -/
theorem foldGenericLeafCursor_restores {α : Type*} (graph : DAG n)
    (weights : Channel n → W) (index : Fin graph.nodeCount) (routePrefix : LeafRoute)
    (counters : GuardCounters n × W) (initial : α)
    (visit : LeafRoute → Channel n → (GuardCounters n × W) → α → α)
    (invariant : counters.2 = GenericWeight.total weights (blockedChannels counters.1)) :
    (graph.foldGenericLeafCursor weights index routePrefix counters initial visit).1 = counters := by
  have claim : ∀ bound : ℕ, ∀ current : Fin graph.nodeCount, current.val = bound →
      ∀ (cursor : LeafRoute) (state : GuardCounters n × W) (accumulator : α)
        (callback : LeafRoute → Channel n → (GuardCounters n × W) → α → α),
      state.2 = GenericWeight.total weights (blockedChannels state.1) →
      (graph.foldGenericLeafCursor weights current cursor state accumulator callback).1 = state := by
    intro bound
    induction bound using Nat.strong_induction_on with
    | h bound ih =>
      intro current currentBound cursor state accumulator callback correct
      rw [foldGenericLeafCursor]
      cases equation : graph.node current with
      | zero => rfl
      | input head => rfl
      | liveAnd left right => rfl
      | disj refs =>
          apply foldl_counters_unchanged _ _ state (state, accumulator) rfl
          intro previous position equal
          have earlier : (graph.childIndex current (refs.get position)).val < bound := by
            simpa only [DAG.childIndex, currentBound] using (refs.get position).isLt
          rw [ih _ earlier _ rfl (position.val :: cursor) previous.1 previous.2 _
            (by simpa only [equal] using correct)]
          exact equal
      | guard child labels =>
          have earlier : (graph.childIndex current child).val < bound := by
            simpa only [DAG.childIndex, currentBound] using child.isLt
          have restore := ih _ earlier _ rfl (0 :: cursor)
            (enterGenericGuards weights state labels) accumulator callback
            (enterGenericGuards_correct weights state labels correct)
          change leaveGenericGuards weights
            (graph.foldGenericLeafCursor weights (graph.childIndex current child) (0 :: cursor)
              (enterGenericGuards weights state labels) accumulator callback).1 labels = state
          rw [restore]
          exact leave_enterGenericGuards weights state labels correct
  exact claim index.val index rfl routePrefix counters initial visit invariant

def keepBestGenericRoute (b : ℕ) (target : Channel n) (total : W)
    (route : LeafRoute) (head : Channel n) (state : GuardCounters n × W)
    (best : Option (LeafRoute × W)) : Option (LeafRoute × W) :=
  if state.1 head = 0 ∧ (b ≠ 1 ∨ state.1 target = 0) then
    let score := total - state.2
    match best with
    | none => some (route, score)
    | some previous => if previous.2 < score then some (route, score) else best
  else best

def bestGenericLeafRoute (graph : DAG n) (weights : Channel n → W) (b : ℕ)
    (target : Channel n) (root : Fin graph.nodeCount) : Option (LeafRoute × W) :=
  ((graph.foldGenericLeafCursor weights root [] (fun _ => 0, 0) (none : Option (LeafRoute × W))
    (keepBestGenericRoute b target (GenericWeight.total weights Finset.univ))).2).map
      fun best => (best.1.reverse, best.2)

def bestGenericLeafSet (graph : DAG n) (weights : Channel n → W) (b : ℕ)
    (target : Channel n) (root : Fin graph.nodeCount) : Option (Finset (Channel n)) := do
  let best ← graph.bestGenericLeafRoute weights b target root
  let leaf ← graph.reconstructRoute root best.1
  pure (fullUnblocked leaf.2.toFinset)

end GenericArithmetic

end DAG
end Controller.Decoder
