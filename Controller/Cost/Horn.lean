module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Horn.IndexedNormalize
public import Controller.Cost.Refinement
public import Mathlib.Data.List.Perm.Subperm
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.Group.Nat

@[expose] public section

/-!
# Exact worklist traces and amortized propagation bounds

The trace constructors include the executable loop's failure, queue and branch
tests. The bounds below concern those exact traces: every pop consumes a row
credit, and a variable can generate an occurrence traversal only once. These
combinatorial bounds are inputs to an indexed-word-machine simulation; they do
not assign primitive instruction counts to a high-level transition.
-/

namespace Controller.Cost.Horn

open Controller.Horn.Worklist

/-- The input size includes rows even when their literal lists are empty. -/
def inputSize (formula : CNF.Formula (Fin n)) : Nat :=
  1 + n + formula.clauses.size + (formula.clauses.toList.map List.length).sum

/-- A not-yet-fired row still owns one scheduling credit. -/
def unfired (fired : Vector Bool m) : Nat :=
  (List.finRange m).countP (fun row => !fired[row.val])

/-- Moving a fresh row onto the agenda transfers its credit to the queue. -/
def agendaPotential (agenda : Agenda m) : Nat :=
  unfired agenda.fired + agenda.pending.length

theorem unfired_set_true (fired : Vector Bool m) (row : Fin m)
    (fresh : fired[row.val] = false) :
    unfired (fired.set row.val true row.isLt) = unfired fired - 1 := by
  have pointwise : (fun other : Fin m => !(fired.set row.val true row.isLt)[other.val]) =
      Controller.Horn.forceFalse (fun other => !fired[other.val]) row := by
    funext other
    by_cases equal : row = other
    · subst other
      simp [Controller.Horn.forceFalse]
    · have unequal : row.val ≠ other.val := fun same => equal (Fin.ext same)
      simp [Controller.Horn.forceFalse, Ne.symm equal, unequal]
  unfold unfired
  rw [pointwise, countP_forceFalse _ (List.nodup_finRange m)]
  simp [List.mem_finRange, fresh]

theorem unfired_pos (fired : Vector Bool m) (row : Fin m)
    (fresh : fired[row.val] = false) : 0 < unfired fired := by
  exact List.countP_pos_iff.mpr ⟨row, List.mem_finRange row, by simp [fresh]⟩

/-- Scheduling cannot increase the row-credit potential, including a conflict. -/
theorem schedule_potential_le (rules : RuleTable n m) (counted : CountedState n m)
    (row : Fin m) (agenda : Agenda m) :
    agendaPotential (Agenda.schedule rules counted row agenda) ≤ agendaPotential agenda := by
  unfold Agenda.schedule
  split
  · rename_i ready
    have fresh := ready.2
    have positive := unfired_pos agenda.fired row fresh
    cases equation : rules[row.val] with
    | skip => exact Nat.le_refl _
    | positive labels =>
      change unfired (agenda.fired.set row.val true row.isLt) + agenda.pending.length ≤ _
      rw [unfired_set_true _ _ fresh]
      unfold agendaPotential
      omega
    | negative head labels =>
      change unfired (agenda.fired.set row.val true row.isLt) + (row :: agenda.pending).length ≤ _
      rw [unfired_set_true _ _ fresh]
      simp only [List.length_cons]
      unfold agendaPotential
      omega
  · exact Nat.le_refl _

theorem scheduleRows_potential_le (rules : RuleTable n m) (counted : CountedState n m)
    (rows : List (Fin m)) (agenda : Agenda m) :
    agendaPotential (Agenda.scheduleRows rules counted rows agenda) ≤ agendaPotential agenda := by
  induction rows generalizing agenda with
  | nil => exact Nat.le_refl _
  | cons row rest ih =>
    exact (ih (Agenda.schedule rules counted row agenda)).trans
      (schedule_potential_le rules counted row agenda)

theorem initial_potential_le (rules : RuleTable n m) :
    agendaPotential (State.initial rules).agenda ≤ m := by
  have bound := scheduleRows_potential_le rules (CountedState.initial rules)
    (List.finRange m) (Agenda.empty m)
  simpa [State.initial, agendaPotential, unfired, Agenda.empty] using bound

theorem propagate_potential_lt (rules : RuleTable n m) (index : Vector (List (Fin m)) n)
    (state : Controller.Horn.Worklist.State n m) (row : Fin m) (head : Fin n)
    (rest : List (Fin m)) (pending : state.agenda.pending = row :: rest) :
    agendaPotential (state.propagate rules index head rest).agenda <
      agendaPotential state.agenda := by
  have bound := scheduleRows_potential_le rules (state.counted.turnOff index head)
    index[head.val] { state.agenda with pending := rest }
  change agendaPotential (Agenda.scheduleRows rules (state.counted.turnOff index head)
    index[head.val] { state.agenda with pending := rest }) < _
  have before : agendaPotential { state.agenda with pending := rest } + 1 =
      agendaPotential state.agenda := by
    simp [agendaPotential, pending, Nat.add_assoc]
  omega

theorem discard_potential_lt (state : Controller.Horn.Worklist.State n m)
    (row : Fin m) (rest : List (Fin m)) (pending : state.agenda.pending = row :: rest) :
    agendaPotential (state.discard rest).agenda < agendaPotential state.agenda := by
  simp [State.discard, agendaPotential, pending]

/-- A pop names its original row and, only on a first-false step, its variable. -/
abbrev Event (n m : Nat) := Fin m × Option (Fin n)

/-- These constructors impose the actual queue-front and branch tests. -/
inductive Step (rules : RuleTable n m) (index : Vector (List (Fin m)) n) :
    Controller.Horn.Worklist.State n m → Event n m →
      Controller.Horn.Worklist.State n m → Prop
  | force (state : Controller.Horn.Worklist.State n m) (row : Fin m)
      (head : Fin n) (labels : List (Fin n)) (rest : List (Fin m))
      (noFailure : state.agenda.failed = false)
      (pending : state.agenda.pending = row :: rest)
      (rule : rules[row.val] = .negative head labels)
      (wasTrue : state.counted.assignment head = true) :
      Step rules index state (row, some head) (state.propagate rules index head rest)
  | discard (state : Controller.Horn.Worklist.State n m) (row : Fin m) (rest : List (Fin m))
      (noFailure : state.agenda.failed = false)
      (pending : state.agenda.pending = row :: rest)
      (idle : ∀ head labels, rules[row.val] = .negative head labels →
        state.counted.assignment head = false) :
      Step rules index state (row, none) (state.discard rest)

theorem Step.potential_lt {rules : RuleTable n m} {index : Vector (List (Fin m)) n}
    {first last : Controller.Horn.Worklist.State n m} {event : Event n m}
    (step : Step rules index first event last) :
    agendaPotential last.agenda < agendaPotential first.agenda := by
  cases step with
  | force row head labels rest _ pending _ _ =>
      exact propagate_potential_lt rules index first row head rest pending
  | discard row rest _ pending _ => exact discard_potential_lt first row rest pending

theorem Step.below {rules : RuleTable n m} {index : Vector (List (Fin m)) n}
    {first last : Controller.Horn.Worklist.State n m} {event : Event n m}
    (step : Step rules index first event last) :
    Controller.Horn.Below last.counted.assignment first.counted.assignment := by
  cases step with
  | force row head labels rest _ _ _ _ =>
      exact State.propagate_below rules index first head rest
  | discard => exact Controller.Horn.below_refl _

/-- An exact execution prefix can end between any two worklist iterations. -/
inductive Prefix (rules : RuleTable n m) (index : Vector (List (Fin m)) n) :
    Controller.Horn.Worklist.State n m → Controller.Horn.Worklist.State n m → Prop
  | refl (state : Controller.Horn.Worklist.State n m) : Prefix rules index state state
  | next {first middle last : Controller.Horn.Worklist.State n m} {event : Event n m}
      (transition : Step rules index first event middle)
      (tail : Prefix rules index middle last) : Prefix rules index first last

theorem Prefix.potential_le {rules : RuleTable n m} {index : Vector (List (Fin m)) n}
    {first last : Controller.Horn.Worklist.State n m} (path : Prefix rules index first last) :
    agendaPotential last.agenda ≤ agendaPotential first.agenda := by
  induction path with
  | refl => exact Nat.le_refl _
  | next transition tail ih => exact ih.trans (Nat.le_of_lt transition.potential_lt)

/-- A queue of `m` row slots suffices at every reachable loop boundary. -/
theorem Prefix.queue_length_le_rows (rules : RuleTable n m) (index : Vector (List (Fin m)) n)
    (state : Controller.Horn.Worklist.State n m)
    (path : Prefix rules index (State.initial rules) state) : state.agenda.pending.length ≤ m := by
  have withinPotential : state.agenda.pending.length ≤ agendaPotential state.agenda := by
    unfold agendaPotential
    omega
  exact withinPotential.trans (path.potential_le.trans (initial_potential_le rules))

/-- The same credit bound holds inside a scheduling pass, not only at its end. -/
theorem scheduleRows_queue_length_le (rules : RuleTable n m) (counted : CountedState n m)
    (rows : List (Fin m)) (agenda : Agenda m) (bound : agendaPotential agenda ≤ m) :
    (Agenda.scheduleRows rules counted rows agenda).pending.length ≤ m := by
  have potentialBound := (scheduleRows_potential_le rules counted rows agenda).trans bound
  unfold agendaPotential at potentialBound
  omega

/-- A finite exact trace ends at the failure test or the empty queue test. -/
inductive LoopTrace (rules : RuleTable n m) (index : Vector (List (Fin m)) n) :
    Controller.Horn.Worklist.State n m → Option (Vector Bool n) → List (Event n m) → Prop
  | failed (state : Controller.Horn.Worklist.State n m) (failure : state.agenda.failed = true) :
      LoopTrace rules index state none []
  | done (state : Controller.Horn.Worklist.State n m) (noFailure : state.agenda.failed = false)
      (pending : state.agenda.pending = []) :
      LoopTrace rules index state (some state.counted.values) []
  | step {first middle : Controller.Horn.Worklist.State n m} {event result events}
      (transition : Step rules index first event middle)
      (tail : LoopTrace rules index middle result events) :
      LoopTrace rules index first result (event :: events)

/-- Erasing a trace yields precisely the accepted D04 executable result. -/
theorem LoopTrace.erasure {rules : RuleTable n m} {index : Vector (List (Fin m)) n}
    {state : Controller.Horn.Worklist.State n m} {result events}
    (trace : LoopTrace rules index state result events) : State.run rules index state = result := by
  induction trace with
  | failed state failure => rw [State.run]; simp [failure]
  | done state noFailure pending =>
    rw [State.run]
    simp only [noFailure, Bool.false_eq_true, ite_false]
    split
    · rfl
    · rename_i front rest currentPending
      simp [pending] at currentPending
  | @step first middle event result events transition tail ih =>
    cases transition with
    | force row head labels rest noFailure pending rule wasTrue =>
      rw [State.run]
      simp only [noFailure, Bool.false_eq_true, ite_false]
      split
      · rename_i currentPending
        simp only [pending, List.cons_ne_nil] at currentPending
      · rename_i front remainder currentPending
        obtain ⟨rfl, rfl⟩ := List.cons.inj (pending.symm.trans currentPending)
        simpa only [rule, wasTrue, dite_true] using ih
    | discard row rest noFailure pending idle =>
      rw [State.run]
      simp only [noFailure, Bool.false_eq_true, ite_false]
      split
      · rename_i currentPending
        simp only [pending, List.cons_ne_nil] at currentPending
      · rename_i front remainder currentPending
        obtain ⟨rfl, rfl⟩ := List.cons.inj (pending.symm.trans currentPending)
        cases equation : rules[row.val] with
        | skip => exact ih
        | positive labels => exact ih
        | negative head labels => simpa [idle head labels equation] using ih

theorem loopTrace_exists (rules : RuleTable n m) (index : Vector (List (Fin m)) n)
    (state : Controller.Horn.Worklist.State n m) :
    ∃ result events, LoopTrace rules index state result events := by
  by_cases failure : state.agenda.failed = true
  · exact ⟨none, [], .failed state failure⟩
  · have noFailure : state.agenda.failed = false := Bool.eq_false_iff.mpr failure
    cases pending : state.agenda.pending with
    | nil => exact ⟨some state.counted.values, [], .done state noFailure pending⟩
    | cons row rest =>
      cases equation : rules[row.val] with
      | skip =>
        obtain ⟨result, events, tail⟩ := loopTrace_exists rules index (state.discard rest)
        refine ⟨result, (row, none) :: events, .step
          (.discard state row rest noFailure pending ?_) tail⟩
        intro head labels impossible
        simp [equation] at impossible
      | positive labels =>
        obtain ⟨result, events, tail⟩ := loopTrace_exists rules index (state.discard rest)
        refine ⟨result, (row, none) :: events, .step
          (.discard state row rest noFailure pending ?_) tail⟩
        intro head otherLabels impossible
        simp [equation] at impossible
      | negative head labels =>
        by_cases wasTrue : state.counted.assignment head = true
        · obtain ⟨result, events, tail⟩ :=
            loopTrace_exists rules index (state.propagate rules index head rest)
          exact ⟨result, (row, some head) :: events,
            .step (.force state row head labels rest noFailure pending equation wasTrue) tail⟩
        · obtain ⟨result, events, tail⟩ := loopTrace_exists rules index (state.discard rest)
          refine ⟨result, (row, none) :: events, .step
            (.discard state row rest noFailure pending ?_) tail⟩
          intro other otherLabels otherEquation
          have same := (Rule.negative.inj (equation.symm.trans otherEquation)).1
          simpa only [← same] using Bool.eq_false_iff.mpr wasTrue
termination_by agendaPotential state.agenda
decreasing_by
  all_goals first
    | exact propagate_potential_lt rules index state row head rest pending
    | exact discard_potential_lt state row rest pending

theorem run_has_trace (rules : RuleTable n m) (index : Vector (List (Fin m)) n)
    (state : Controller.Horn.Worklist.State n m) :
    ∃ events, LoopTrace rules index state (State.run rules index state) events := by
  obtain ⟨result, events, trace⟩ := loopTrace_exists rules index state
  exact ⟨events, trace.erasure.symm ▸ trace⟩

theorem LoopTrace.pops_le_potential {rules : RuleTable n m}
    {index : Vector (List (Fin m)) n} {state : Controller.Horn.Worklist.State n m}
    {result events} (trace : LoopTrace rules index state result events) :
    events.length ≤ agendaPotential state.agenda := by
  induction trace with
  | failed => exact Nat.zero_le _
  | done => exact Nat.zero_le _
  | step transition tail ih =>
    have decreases := transition.potential_lt
    simp only [List.length_cons]
    omega

/-- First-false variables, in their execution order. -/
def forcedHeads (events : List (Event n m)) : List (Fin n) := events.filterMap Prod.snd

theorem LoopTrace.forced_true_at_start {rules : RuleTable n m}
    {index : Vector (List (Fin m)) n} {state : Controller.Horn.Worklist.State n m}
    {result events} (trace : LoopTrace rules index state result events)
    (label : Fin n) (member : label ∈ forcedHeads events) :
    state.counted.assignment label = true := by
  induction trace with
  | failed => simp [forcedHeads] at member
  | done => simp [forcedHeads] at member
  | @step first middle event result events transition tail ih =>
    cases transition with
    | force row head labels rest noFailure pending rule wasTrue =>
      simp only [forcedHeads, List.filterMap_cons, List.mem_cons] at member
      rcases member with equal | later
      · simpa only [equal] using wasTrue
      · exact State.propagate_below rules index first head rest label (ih later)
    | discard row rest noFailure pending idle =>
      exact ih (by simpa [forcedHeads] using member)

theorem LoopTrace.forcedHeads_nodup {rules : RuleTable n m}
    {index : Vector (List (Fin m)) n} {state : Controller.Horn.Worklist.State n m}
    {result events} (trace : LoopTrace rules index state result events) :
    (forcedHeads events).Nodup := by
  induction trace with
  | failed => exact List.nodup_nil
  | done => exact List.nodup_nil
  | @step first middle event result events transition tail ih =>
    cases transition with
    | force row head labels rest noFailure pending rule wasTrue =>
      change (head :: forcedHeads events).Nodup
      refine List.nodup_cons.mpr ⟨?_, ih⟩
      intro member
      have laterTrue := tail.forced_true_at_start head member
      have nowFalse := State.propagate_head_false rules index first head rest
      exact Bool.false_ne_true (nowFalse.symm.trans laterTrue)
    | discard => exact ih

private theorem nodup_weight_sum_le (labels : List (Fin n)) (distinct : labels.Nodup)
    (weight : Fin n → Nat) :
    (labels.map weight).sum ≤ ((List.finRange n).map weight).sum := by
  have subperm := distinct.subperm (fun label _ => List.mem_finRange label)
  obtain ⟨middle, permutation, sublist⟩ := subperm
  calc
    (labels.map weight).sum = (middle.map weight).sum := (permutation.map weight).sum_eq.symm
    _ ≤ ((List.finRange n).map weight).sum :=
      (sublist.map weight).sum_le_sum (fun value _ => Nat.zero_le value)

/-- Bucket incidences visited by first-false steps, before the two local passes
for decrements and scheduling. Each pass has this same incidence bound. -/
def visitedIncidences (index : Vector (List (Fin m)) n) (events : List (Event n m)) : Nat :=
  ((forcedHeads events).map fun head => index[head.val].length).sum

private theorem bucket_push_sum (index : Vector (List (Fin m)) n)
    (label : Fin n) (row : Fin m) :
    ((List.finRange n).map fun other =>
      (index.set label.val (row :: index[label.val]) label.isLt)[other.val].length).sum =
        ((List.finRange n).map fun other => index[other.val].length).sum + 1 := by
  rw [← Fin.sum_univ_def, ← Fin.sum_univ_def]
  calc
    (∑ other : Fin n,
      (index.set label.val (row :: index[label.val]) label.isLt)[other.val].length) =
        ∑ other : Fin n, (index[other.val].length + if label = other then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro other _
      by_cases equal : label = other
      · subst other
        simp
      · have unequal : label.val ≠ other.val := fun same => equal (Fin.ext same)
        simp [equal, unequal]
    _ = (∑ other : Fin n, index[other.val].length) + 1 := by
      rw [Finset.sum_add_distrib]
      simp

/-- Every stored occurrence comes from exactly one original positive incidence. -/
theorem bucketIncidences_total (edges : List (Fin n × Fin m)) :
    ((List.finRange n).map fun label => (bucketIncidences edges)[label.val].length).sum =
      edges.length := by
  induction edges with
  | nil => simp [bucketIncidences]
  | cons edge edges ih =>
    rcases edge with ⟨label, row⟩
    change ((List.finRange n).map fun other =>
      ((bucketIncidences edges).set label.val
        (row :: (bucketIncidences edges)[label.val]) label.isLt)[other.val].length).sum = _
    rw [bucket_push_sum, ih]
    rfl

theorem occurrences_total (rules : RuleTable n m) :
    ((List.finRange n).map fun label => (occurrences rules)[label.val].length).sum =
      (positiveIncidences rules).length :=
  bucketIncidences_total _

private theorem compiled_positives_length_le (clause : CNF.Clause (Fin n)) :
    (compileClause clause).positives.length ≤ clause.length := by
  have bound : (signedLabels clause true).length ≤ clause.length := by
    unfold signedLabels
    have dedup := (List.dedup_sublist
      ((clause.filter fun literal => decide (literal.2 = true)).map Prod.fst)).length_le
    simp only [List.length_map] at dedup
    exact dedup.trans (List.length_filter_le _ _)
  unfold compileClause
  split
  · exact Nat.zero_le _
  · cases signedLabels clause false <;> exact bound

theorem normalized_positiveIncidences_le_literals (formula : CNF.Formula (Fin n)) :
    (positiveIncidences (normalizedTable formula)).length ≤
      (formula.clauses.toList.map List.length).sum := by
  have getRows : (List.finRange formula.clauses.size).map
      (fun row => formula.clauses[row.val]) = formula.clauses.toList := by
    rw [← List.ofFn_eq_map, ← Array.toList_ofFn, Array.ofFn_getElem]
  have sumRows := congrArg (fun rows => (rows.map List.length).sum) getRows
  simp only [List.map_map, Function.comp_def] at sumRows
  have bound := List.sum_le_sum (l := List.finRange formula.clauses.size)
    (f := fun row => (compileClause formula.clauses[row.val]).positives.length)
    (g := fun row => formula.clauses[row.val].length)
    (fun row _ => compiled_positives_length_le formula.clauses[row.val])
  apply (show (positiveIncidences (normalizedTable formula)).length =
    ((List.finRange formula.clauses.size).map fun row =>
      (compileClause formula.clauses[row.val]).positives.length).sum by
      simp [positiveIncidences, List.length_flatMap, normalizedTable, compileFormula]).le.trans
  exact bound.trans_eq sumRows

theorem LoopTrace.visits_le_all_buckets {rules : RuleTable n m}
    {index : Vector (List (Fin m)) n} {state : Controller.Horn.Worklist.State n m}
    {result events} (trace : LoopTrace rules index state result events) :
    visitedIncidences index events ≤
      ((List.finRange n).map fun head => index[head.val].length).sum :=
  nodup_weight_sum_le _ trace.forcedHeads_nodup _

/-- The accepted rule solver has an exact trace with at most one pop per input
row and at most one traversal of each variable's stored occurrence bucket. -/
theorem solveRules_trace_bounds (rules : RuleTable n m) :
    ∃ events, LoopTrace rules (occurrences rules) (State.initial rules) (solveRules rules) events ∧
      events.length ≤ m ∧ (forcedHeads events).Nodup ∧
      visitedIncidences (occurrences rules) events ≤
        ((List.finRange n).map fun head => (occurrences rules)[head.val].length).sum := by
  obtain ⟨events, trace⟩ := run_has_trace rules (occurrences rules) (State.initial rules)
  exact ⟨events, trace, trace.pops_le_potential.trans (initial_potential_le rules),
    trace.forcedHeads_nodup, trace.visits_le_all_buckets⟩

/-- The exact formula-solver trace pops at most the declared number of clauses;
each of its two incidence passes visits at most the input's literal count. -/
theorem solveFormula_trace_bounds (formula : CNF.Formula (Fin n)) :
    ∃ events, LoopTrace (normalizedTable formula) (occurrences (normalizedTable formula))
      (State.initial (normalizedTable formula)) (solveFormula formula) events ∧
      events.length ≤ formula.clauses.size ∧ (forcedHeads events).Nodup ∧
      visitedIncidences (occurrences (normalizedTable formula)) events ≤
        (formula.clauses.toList.map List.length).sum := by
  obtain ⟨events, trace, pops, distinct, visits⟩ :=
    solveRules_trace_bounds (normalizedTable formula)
  refine ⟨events, trace, pops, distinct, visits.trans ?_⟩
  rw [occurrences_total]
  exact normalized_positiveIncidences_le_literals formula

end Controller.Cost.Horn
