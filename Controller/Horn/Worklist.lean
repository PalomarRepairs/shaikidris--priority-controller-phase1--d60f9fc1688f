module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Horn.IndexedState

@[expose] public section

/-!
# Counted downward propagation

The agenda stores original row identifiers. Each row is scheduled once; a
negative row requests its head to become false, and an empty positive row
records a contradiction. Popping an already false head performs no updates.
-/

namespace Controller.Horn.Worklist

/-- Models of the normalized row array. -/
def Models (rules : RuleTable n m) (assignment : Fin n → Bool) : Prop :=
  ∀ row : Fin m, (rules[row.val]).Holds assignment

/-- No assignment satisfies every normalized rule. -/
def NoModel (rules : RuleTable n m) : Prop :=
  ¬∃ assignment, Models rules assignment

/-- A row-index agenda with persistent scheduling marks and a conflict flag. -/
structure Agenda (m : Nat) where
  fired : Vector Bool m
  pending : List (Fin m)
  failed : Bool

namespace Agenda

/-- The empty agenda before the initial scan. -/
def empty (m : Nat) : Agenda m where
  fired := Vector.replicate m false
  pending := []
  failed := false

/-- Register a zero-count row, unless it has already been registered. -/
def schedule (rules : RuleTable n m) (counted : CountedState n m)
    (row : Fin m) (agenda : Agenda m) : Agenda m :=
  if counted.counts[row.val] = 0 ∧ agenda.fired[row.val] = false then
    match rules[row.val] with
    | .skip => agenda
    | .positive _ =>
        { agenda with fired := agenda.fired.set row.val true row.isLt, failed := true }
    | .negative _ _ =>
        { agenda with
          fired := agenda.fired.set row.val true row.isLt
          pending := row :: agenda.pending }
  else agenda

/-- Schedule a supplied list, which is the full row list only at initialization. -/
def scheduleRows (rules : RuleTable n m) (counted : CountedState n m) :
    List (Fin m) → Agenda m → Agenda m
  | [], agenda => agenda
  | row :: rest, agenda => scheduleRows rules counted rest (schedule rules counted row agenda)

/-- A scheduled row has either recorded a conflict or has its head false or pending. -/
def Settled (rules : RuleTable n m) (counted : CountedState n m)
    (agenda : Agenda m) (row : Fin m) : Prop :=
  match rules[row.val] with
  | .skip => True
  | .positive _ => agenda.failed = true
  | .negative head _ => counted.assignment head = false ∨ row ∈ agenda.pending

/-- Agenda invariants which hold even partway through scheduling an incidence list. -/
structure Sound (rules : RuleTable n m) (counted : CountedState n m)
    (agenda : Agenda m) : Prop where
  pending_ready : ∀ row ∈ agenda.pending,
    ∃ head labels, rules[row.val] = .negative head labels ∧ counted.counts[row.val] = 0
  fired_settled : ∀ row : Fin m, agenda.fired[row.val] = true →
    counted.counts[row.val] = 0 ∧ Settled rules counted agenda row
  failed_sound : agenda.failed = true → NoModel rules
  pending_fired : ∀ row ∈ agenda.pending, agenda.fired[row.val] = true
  pending_nodup : agenda.pending.Nodup

/-- Every enabled zero-count row has been placed on the agenda. -/
def Complete (rules : RuleTable n m) (counted : CountedState n m)
    (agenda : Agenda m) : Prop :=
  ∀ row : Fin m, (rules[row.val]).enabled = true →
    counted.counts[row.val] = 0 → agenda.fired[row.val] = true

theorem empty_sound (rules : RuleTable n m) (counted : CountedState n m) :
    Sound rules counted (empty m) := by
  constructor
  · simp [empty]
  · simp [empty]
  · simp [empty]
  · simp [empty]
  · simp [empty]

/-- A scheduling mark prevents a row from generating another request. -/
theorem schedule_of_fired (rules : RuleTable n m) (counted : CountedState n m)
    (row : Fin m) (agenda : Agenda m) (fired : agenda.fired[row.val] = true) :
    schedule rules counted row agenda = agenda := by
  simp [schedule, fired]

theorem schedule_fired_mono (rules : RuleTable n m) (counted : CountedState n m)
    (row : Fin m) (agenda : Agenda m) (other : Fin m)
    (already : agenda.fired[other.val] = true) :
    (schedule rules counted row agenda).fired[other.val] = true := by
  unfold schedule
  split
  · cases rules[row.val] <;> simp_all [Vector.getElem_set]
  · exact already

theorem schedule_pending_mono (rules : RuleTable n m) (counted : CountedState n m)
    (row : Fin m) (agenda : Agenda m) :
    agenda.pending ⊆ (schedule rules counted row agenda).pending := by
  unfold schedule
  split
  · cases rules[row.val] <;> simp
  · exact List.Subset.refl _

theorem schedule_failed_mono (rules : RuleTable n m) (counted : CountedState n m)
    (row : Fin m) (agenda : Agenda m) (failed : agenda.failed = true) :
    (schedule rules counted row agenda).failed = true := by
  unfold schedule
  split
  · cases rules[row.val] <;> simp_all
  · exact failed

theorem settled_mono (rules : RuleTable n m) (counted : CountedState n m)
    (first second : Agenda m) (pending : first.pending ⊆ second.pending)
    (failed : first.failed = true → second.failed = true) (row : Fin m)
    (settled : Settled rules counted first row) : Settled rules counted second row := by
  unfold Settled at *
  cases ruleEquation : rules[row.val] with
  | skip => trivial
  | positive _ =>
      rw [ruleEquation] at settled
      exact failed settled
  | negative head _ =>
      rw [ruleEquation] at settled
      exact settled.imp_right (fun member => pending member)

theorem schedule_complete_row (rules : RuleTable n m) (counted : CountedState n m)
    (row : Fin m) (agenda : Agenda m) (enabled : (rules[row.val]).enabled = true)
    (zero : counted.counts[row.val] = 0) :
    (schedule rules counted row agenda).fired[row.val] = true := by
  unfold schedule
  by_cases fired : agenda.fired[row.val] = false
  · simp only [zero, fired, and_self, ite_true]
    cases ruleEquation : rules[row.val] <;> simp_all [Rule.enabled]
  · simp [fired]

theorem schedule_sound (rules : RuleTable n m) (counted : CountedState n m)
    (correct : counted.Correct rules)
    (upper : ∀ assignment, Models rules assignment → Below assignment counted.assignment)
    (row : Fin m) (agenda : Agenda m) (sound : Sound rules counted agenda) :
    Sound rules counted (schedule rules counted row agenda) := by
  by_cases ready : counted.counts[row.val] = 0 ∧ agenda.fired[row.val] = false
  · cases ruleEquation : rules[row.val] with
    | skip => simpa [schedule, ready, ruleEquation] using sound
    | positive labels =>
        have impossible : NoModel rules := by
          rintro ⟨assignment, model⟩
          have rowHolds := model row
          rw [ruleEquation] at rowHolds
          obtain ⟨label, member, value⟩ := rowHolds
          have countZero : positiveCount rules[row.val] counted.assignment = 0 :=
            (correct row).symm.trans ready.1
          have allFalse := (positiveCount_eq_zero _ _).mp countZero
          have falseValue : counted.assignment label = false :=
            allFalse label (by simpa [ruleEquation, Rule.positives] using member)
          exact Bool.false_ne_true (falseValue.symm.trans (upper assignment model label value))
        rw [schedule, ite_eq_left ready, ruleEquation]
        constructor
        · exact sound.pending_ready
        · intro other fired
          by_cases equal : row = other
          · subst other
            exact ⟨ready.1, by simp [Settled, ruleEquation]⟩
          · have unequalValues : row.val ≠ other.val := fun same => equal (Fin.ext same)
            have oldFired : agenda.fired[other.val] = true := by
              simpa [Vector.getElem_set, unequalValues] using fired
            obtain ⟨zero, settled⟩ := sound.fired_settled other oldFired
            exact ⟨zero, settled_mono rules counted agenda
              { agenda with fired := agenda.fired.set row.val true row.isLt, failed := true }
              (List.Subset.refl _) (fun _ => rfl) other settled⟩
        · intro _
          exact impossible
        · intro other member
          have already := sound.pending_fired other member
          simp [Vector.getElem_set, already]
        · exact sound.pending_nodup
    | negative head labels =>
        rw [schedule, ite_eq_left ready, ruleEquation]
        constructor
        · intro other member
          rcases List.mem_cons.mp member with equal | oldMember
          · subst other
            exact ⟨head, labels, ruleEquation, ready.1⟩
          · exact sound.pending_ready other oldMember
        · intro other fired
          by_cases equal : row = other
          · subst other
            exact ⟨ready.1, by simp [Settled, ruleEquation]⟩
          · have unequalValues : row.val ≠ other.val := fun same => equal (Fin.ext same)
            have oldFired : agenda.fired[other.val] = true := by
              simpa [Vector.getElem_set, unequalValues] using fired
            obtain ⟨zero, settled⟩ := sound.fired_settled other oldFired
            exact ⟨zero, settled_mono rules counted agenda
              { agenda with
                fired := agenda.fired.set row.val true row.isLt
                pending := row :: agenda.pending }
              (List.subset_cons_self _ _) (fun value => value) other settled⟩
        · exact sound.failed_sound
        · intro other member
          rcases List.mem_cons.mp member with equal | oldMember
          · subst other
            simp
          · have already := sound.pending_fired other oldMember
            simp [Vector.getElem_set, already]
        · apply List.nodup_cons.mpr
          constructor
          · intro member
            exact Bool.false_ne_true (ready.2.symm.trans (sound.pending_fired row member))
          · exact sound.pending_nodup
  · simpa [schedule, ready] using sound

theorem scheduleRows_fired_mono (rules : RuleTable n m) (counted : CountedState n m)
    (rows : List (Fin m)) (agenda : Agenda m) (row : Fin m)
    (already : agenda.fired[row.val] = true) :
    (scheduleRows rules counted rows agenda).fired[row.val] = true := by
  induction rows generalizing agenda with
  | nil => exact already
  | cons first rest inductionHypothesis =>
      exact inductionHypothesis _ (schedule_fired_mono rules counted first agenda row already)

theorem scheduleRows_complete_mem (rules : RuleTable n m) (counted : CountedState n m)
    (rows : List (Fin m)) (agenda : Agenda m) (row : Fin m) (member : row ∈ rows)
    (enabled : (rules[row.val]).enabled = true) (zero : counted.counts[row.val] = 0) :
    (scheduleRows rules counted rows agenda).fired[row.val] = true := by
  induction rows generalizing agenda with
  | nil => simp at member
  | cons first rest inductionHypothesis =>
      rcases List.mem_cons.mp member with equal | restMember
      · subst first
        exact scheduleRows_fired_mono rules counted rest _ row
          (schedule_complete_row rules counted row agenda enabled zero)
      · exact inductionHypothesis _ restMember

theorem scheduleRows_sound (rules : RuleTable n m) (counted : CountedState n m)
    (correct : counted.Correct rules)
    (upper : ∀ assignment, Models rules assignment → Below assignment counted.assignment)
    (rows : List (Fin m)) (agenda : Agenda m) (sound : Sound rules counted agenda) :
    Sound rules counted (scheduleRows rules counted rows agenda) := by
  induction rows generalizing agenda with
  | nil => exact sound
  | cons first rest inductionHypothesis =>
      exact inductionHypothesis _ (schedule_sound rules counted correct upper first agenda sound)

/-- Popping a request is sound once its head is false and every old zero count stays zero. -/
theorem sound_pop (rules : RuleTable n m) (before after : CountedState n m)
    (agenda : Agenda m) (sound : Sound rules before agenda)
    (row : Fin m) (head : Fin n) (labels : List (Fin n)) (rest : List (Fin m))
    (pending : agenda.pending = row :: rest) (ruleEquation : rules[row.val] = .negative head labels)
    (below : Below after.assignment before.assignment) (headFalse : after.assignment head = false)
    (zeroPreserved : ∀ other : Fin m, before.counts[other.val] = 0 → after.counts[other.val] = 0) :
    Sound rules after { agenda with pending := rest } := by
  have falsePreserved : ∀ label, before.assignment label = false → after.assignment label = false := by
    intro label wasFalse
    apply Bool.eq_false_iff.mpr
    intro isTrue
    exact Bool.false_ne_true (wasFalse.symm.trans (below label isTrue))
  constructor
  · intro other member
    obtain ⟨otherHead, otherLabels, equation, zero⟩ := sound.pending_ready other
      (by rw [pending]; exact List.mem_cons_of_mem _ member)
    exact ⟨otherHead, otherLabels, equation, zeroPreserved other zero⟩
  · intro other fired
    obtain ⟨zero, settled⟩ := sound.fired_settled other fired
    refine ⟨zeroPreserved other zero, ?_⟩
    cases otherEquation : rules[other.val] with
    | skip => simp [Settled, otherEquation]
    | positive _ => simpa [Settled, otherEquation] using settled
    | negative otherHead otherLabels =>
        simp only [Settled, otherEquation] at settled ⊢
        rcases settled with wasFalse | member
        · exact Or.inl (falsePreserved otherHead wasFalse)
        · rw [pending] at member
          rcases List.mem_cons.mp member with equal | restMember
          · subst other
            have headsEqual := (Rule.negative.inj (otherEquation.symm.trans ruleEquation)).1
            exact Or.inl (by simpa [headsEqual] using headFalse)
          · exact Or.inr restMember
  · exact sound.failed_sound
  · intro other member
    exact sound.pending_fired other (by rw [pending]; exact List.mem_cons_of_mem _ member)
  · have noDuplicates := sound.pending_nodup
    rw [pending] at noDuplicates
    exact (List.nodup_cons.mp noDuplicates).2

end Agenda

/-- The counted assignment and the row agenda form the executable propagation state. -/
structure State (n m : Nat) where
  counted : CountedState n m
  agenda : Agenda m

namespace State

/-- The invariants used at the boundary of each worklist iteration. -/
structure Valid (rules : RuleTable n m) (state : State n m) : Prop where
  correct : state.counted.Correct rules
  upper : ∀ assignment, Models rules assignment → Below assignment state.counted.assignment
  sound : state.agenda.Sound rules state.counted
  complete : state.agenda.Complete rules state.counted

/-- Initialize counts and schedule the initially empty rules. -/
def initial (rules : RuleTable n m) : State n m where
  counted := CountedState.initial rules
  agenda := Agenda.scheduleRows rules (CountedState.initial rules) (List.finRange m)
    (Agenda.empty m)

theorem initial_valid (rules : RuleTable n m) : Valid rules (initial rules) := by
  have correct := CountedState.initial_correct rules
  have upper : ∀ assignment, Models rules assignment →
      Below assignment (CountedState.initial rules).assignment := by
    intro assignment _
    rw [CountedState.initial_assignment]
    exact below_allTrue assignment
  constructor
  · exact correct
  · exact upper
  · exact Agenda.scheduleRows_sound rules _ correct upper _ _ (Agenda.empty_sound rules _)
  · intro row enabled zero
    exact Agenda.scheduleRows_complete_mem rules _ _ _ row (List.mem_finRange row) enabled zero

/-- Remove the current request and force its head false, updating only that head's occurrences. -/
def propagate (rules : RuleTable n m) (index : Vector (List (Fin m)) n)
    (state : State n m) (head : Fin n) (rest : List (Fin m)) : State n m :=
  let counted := state.counted.turnOff index head
  let agenda := { state.agenda with pending := rest }
  { counted := counted,
    agenda := Agenda.scheduleRows rules counted index[head.val] agenda }

/-- Removing a request whose head is already false does not change the count state. -/
def discard (state : State n m) (rest : List (Fin m)) : State n m :=
  { state with agenda := { state.agenda with pending := rest } }

/-- A fired row remains marked throughout an incidence update and its scheduling pass. -/
theorem propagate_fired_mono (rules : RuleTable n m) (index : Vector (List (Fin m)) n)
    (state : State n m) (head : Fin n) (rest : List (Fin m)) (row : Fin m)
    (fired : state.agenda.fired[row.val] = true) :
    (propagate rules index state head rest).agenda.fired[row.val] = true :=
  Agenda.scheduleRows_fired_mono rules _ _ _ row fired

/-- Propagation only changes true values to false. -/
theorem propagate_below (rules : RuleTable n m) (index : Vector (List (Fin m)) n)
    (state : State n m) (head : Fin n) (rest : List (Fin m)) :
    Below (propagate rules index state head rest).counted.assignment state.counted.assignment := by
  change Below (state.counted.turnOff index head).assignment state.counted.assignment
  rw [CountedState.turnOff_assignment]
  exact forceFalse_below _ _

/-- A variable already false cannot be restored by any propagation step. -/
theorem propagate_preserves_false (rules : RuleTable n m) (index : Vector (List (Fin m)) n)
    (state : State n m) (head label : Fin n) (rest : List (Fin m))
    (wasFalse : state.counted.assignment label = false) :
    (propagate rules index state head rest).counted.assignment label = false := by
  apply Bool.eq_false_iff.mpr
  intro isTrue
  exact Bool.false_ne_true (wasFalse.symm.trans (propagate_below rules index state head rest label isTrue))

/-- The variable processed in a propagation step is false afterwards. -/
theorem propagate_head_false (rules : RuleTable n m) (index : Vector (List (Fin m)) n)
    (state : State n m) (head : Fin n) (rest : List (Fin m)) :
    (propagate rules index state head rest).counted.assignment head = false := by
  change (state.counted.turnOff index head).assignment head = false
  rw [CountedState.turnOff_assignment]
  simp [forceFalse]

/-- The two state changes made by the loop; a propagation requires a previously true head. -/
inductive Transition (rules : RuleTable n m) (index : Vector (List (Fin m)) n) :
    State n m → State n m → Prop
  | propagate (state : State n m) (head : Fin n) (rest : List (Fin m))
      (wasTrue : state.counted.assignment head = true) :
      Transition rules index state (state.propagate rules index head rest)
  | discard (state : State n m) (rest : List (Fin m)) :
      Transition rules index state (state.discard rest)

/-- A finite sequence of the loop's state changes. -/
inductive Trace (rules : RuleTable n m) (index : Vector (List (Fin m)) n) :
    State n m → State n m → Prop
  | refl (state : State n m) : Trace rules index state state
  | next {first middle last : State n m} :
      Transition rules index first middle → Trace rules index middle last →
      Trace rules index first last

theorem Transition.preserves_false {rules : RuleTable n m} {index : Vector (List (Fin m)) n}
    {first last : State n m} (transition : Transition rules index first last) (label : Fin n)
    (wasFalse : first.counted.assignment label = false) : last.counted.assignment label = false := by
  cases transition with
  | propagate head rest _ => exact propagate_preserves_false rules index first head label rest wasFalse
  | discard rest => exact wasFalse

theorem Trace.preserves_false {rules : RuleTable n m} {index : Vector (List (Fin m)) n}
    {first last : State n m} (trace : Trace rules index first last) (label : Fin n)
    (wasFalse : first.counted.assignment label = false) : last.counted.assignment label = false := by
  induction trace with
  | refl _ => exact wasFalse
  | next transition _ inductionHypothesis =>
      exact inductionHypothesis (transition.preserves_false label wasFalse)

/-- After a variable is switched off, no later iteration can meet its first-false guard again. -/
theorem cannot_repeat_turnOff (rules : RuleTable n m) (index : Vector (List (Fin m)) n)
    (state : State n m) (head : Fin n) (rest : List (Fin m)) (later : State n m)
    (trace : Trace rules index (propagate rules index state head rest) later) :
    later.counted.assignment head ≠ true := by
  have isFalse := trace.preserves_false head (propagate_head_false rules index state head rest)
  exact fun isTrue => Bool.false_ne_true (isFalse.symm.trans isTrue)

theorem Transition.fired_mono {rules : RuleTable n m} {index : Vector (List (Fin m)) n}
    {first last : State n m} (transition : Transition rules index first last) (row : Fin m)
    (fired : first.agenda.fired[row.val] = true) : last.agenda.fired[row.val] = true := by
  cases transition with
  | propagate head rest _ => exact propagate_fired_mono rules index first head rest row fired
  | discard rest => exact fired

theorem Trace.fired_mono {rules : RuleTable n m} {index : Vector (List (Fin m)) n}
    {first last : State n m} (trace : Trace rules index first last) (row : Fin m)
    (fired : first.agenda.fired[row.val] = true) : last.agenda.fired[row.val] = true := by
  induction trace with
  | refl _ => exact fired
  | next transition _ inductionHypothesis =>
      exact inductionHypothesis (transition.fired_mono row fired)

theorem discard_valid (rules : RuleTable n m) (state : State n m) (valid : Valid rules state)
    (row : Fin m) (head : Fin n) (labels : List (Fin n)) (rest : List (Fin m))
    (pending : state.agenda.pending = row :: rest)
    (ruleEquation : rules[row.val] = .negative head labels)
    (headFalse : state.counted.assignment head = false) : Valid rules (discard state rest) := by
  constructor
  · exact valid.correct
  · exact valid.upper
  · exact Agenda.sound_pop rules _ _ state.agenda valid.sound row head labels rest pending
      ruleEquation (below_refl _) headFalse (fun _ zero => zero)
  · exact valid.complete

/-- A ready negative row forces its head false in every model below the current state. -/
theorem forced_head_false (rules : RuleTable n m) (state : State n m) (valid : Valid rules state)
    (row : Fin m) (head : Fin n) (labels : List (Fin n))
    (ruleEquation : rules[row.val] = .negative head labels)
    (zero : state.counted.counts[row.val] = 0)
    (assignment : Fin n → Bool) (model : Models rules assignment) : assignment head = false := by
  have holds := model row
  simp only [ruleEquation, Rule.Holds] at holds
  rcases holds with headFalse | ⟨label, member, trueValue⟩
  · exact headFalse
  · have countZero : positiveCount rules[row.val] state.counted.assignment = 0 :=
      (valid.correct row).symm.trans zero
    have allFalse := (positiveCount_eq_zero _ _).mp countZero
    have falseValue : state.counted.assignment label = false :=
      allFalse label (by simpa [ruleEquation, Rule.positives] using member)
    exact False.elim (Bool.false_ne_true
      (falseValue.symm.trans (valid.upper assignment model label trueValue)))

theorem propagate_valid (rules : RuleTable n m) (normalized : Normalized rules)
    (state : State n m) (valid : Valid rules state)
    (row : Fin m) (head : Fin n) (labels : List (Fin n)) (rest : List (Fin m))
    (pending : state.agenda.pending = row :: rest)
    (ruleEquation : rules[row.val] = .negative head labels)
    (zero : state.counted.counts[row.val] = 0) (wasTrue : state.counted.assignment head = true) :
    Valid rules (propagate rules (occurrences rules) state head rest) := by
  let updated := state.counted.turnOff (occurrences rules) head
  have correct : updated.Correct rules :=
    CountedState.turnOff_correct rules normalized state.counted valid.correct head wasTrue
  have updatedAssignment : updated.assignment = forceFalse state.counted.assignment head :=
    CountedState.turnOff_assignment _ _ _
  have upper : ∀ assignment, Models rules assignment → Below assignment updated.assignment := by
    intro assignment model label trueValue
    rw [updatedAssignment]
    by_cases equal : label = head
    · subst label
      have falseValue := forced_head_false rules state valid row head labels ruleEquation zero
        assignment model
      exact False.elim (Bool.false_ne_true (falseValue.symm.trans trueValue))
    · simpa [forceFalse, equal] using valid.upper assignment model label trueValue
  have zeroPreserved : ∀ other : Fin m, state.counted.counts[other.val] = 0 →
      updated.counts[other.val] = 0 := by
    intro other oldZero
    change (decrementRows (occurrences rules)[head.val] state.counted.counts)[other.val] = 0
    rw [decrementRows_get _ (occurrences_nodup rules normalized head), oldZero]
    exact Nat.zero_sub _
  have sound : Agenda.Sound rules updated { state.agenda with pending := rest } := by
    apply Agenda.sound_pop rules state.counted updated state.agenda valid.sound row head labels
      rest pending ruleEquation
    · rw [updatedAssignment]
      exact forceFalse_below _ _
    · rw [updatedAssignment]
      simp [forceFalse]
    · exact zeroPreserved
  constructor
  · exact correct
  · exact upper
  · exact Agenda.scheduleRows_sound rules updated correct upper _ _ sound
  · intro other enabled newZero
    by_cases member : other ∈ (occurrences rules)[head.val]
    · exact Agenda.scheduleRows_complete_mem rules updated _ _ other member enabled newZero
    · have oldZero : state.counted.counts[other.val] = 0 := by
        change (decrementRows (occurrences rules)[head.val] state.counted.counts)[other.val] = 0
          at newZero
        simpa [decrementRows_get _ (occurrences_nodup rules normalized head), member] using newZero
      exact Agenda.scheduleRows_fired_mono rules updated _ _ other
        (valid.complete other enabled oldZero)

/-- At a successful empty agenda every rule holds in the current assignment. -/
theorem terminal_models (rules : RuleTable n m) (state : State n m) (valid : Valid rules state)
    (noFailure : state.agenda.failed = false) (noPending : state.agenda.pending = []) :
    Models rules state.counted.assignment := by
  intro row
  cases ruleEquation : rules[row.val] with
  | skip => trivial
  | positive labels =>
      by_cases zero : state.counted.counts[row.val] = 0
      · have fired := valid.complete row (by simp [ruleEquation, Rule.enabled]) zero
        have settled := (valid.sound.fired_settled row fired).2
        simp [Agenda.Settled, ruleEquation, noFailure] at settled
      · have countPositive : 0 < positiveCount rules[row.val] state.counted.assignment := by
          rw [← valid.correct row]
          exact Nat.pos_of_ne_zero zero
        simpa [ruleEquation, Rule.positives, Rule.Holds] using
          (positiveCount_pos _ _).mp countPositive
  | negative head labels =>
      by_cases zero : state.counted.counts[row.val] = 0
      · have fired := valid.complete row (by simp [ruleEquation, Rule.enabled]) zero
        have settled := (valid.sound.fired_settled row fired).2
        have headFalse : state.counted.assignment head = false := by
          simpa [Agenda.Settled, ruleEquation, noPending] using settled
        exact Or.inl headFalse
      · have countPositive : 0 < positiveCount rules[row.val] state.counted.assignment := by
          rw [← valid.correct row]
          exact Nat.pos_of_ne_zero zero
        exact Or.inr (by simpa [ruleEquation, Rule.positives] using
          (positiveCount_pos _ _).mp countPositive)

/-- A semantic termination measure: the number of variables still true. -/
def remaining (state : State n m) : Nat :=
  (List.finRange n).countP state.counted.assignment

theorem propagate_remaining_lt (rules : RuleTable n m) (index : Vector (List (Fin m)) n)
    (state : State n m) (head : Fin n) (rest : List (Fin m))
    (wasTrue : state.counted.assignment head = true) :
    remaining (propagate rules index state head rest) < remaining state := by
  have positive : 0 < remaining state :=
    List.countP_pos_iff.mpr ⟨head, List.mem_finRange head, wasTrue⟩
  change (List.finRange n).countP (state.counted.turnOff index head).assignment < remaining state
  rw [CountedState.turnOff_assignment, countP_forceFalse _ (List.nodup_finRange n)]
  simp only [List.mem_finRange, wasTrue, and_self, ite_true]
  exact Nat.sub_lt positive (by decide)

/-- Execute propagation using the single precomputed occurrence table. -/
def run (rules : RuleTable n m) (index : Vector (List (Fin m)) n) (state : State n m) :
    Option (Vector Bool n) :=
  if state.agenda.failed then none
  else match pendingEquation : state.agenda.pending with
    | [] => some state.counted.values
    | row :: rest =>
      match rules[row.val] with
      | .negative head _ =>
        if wasTrue : state.counted.assignment head = true then
          run rules index (propagate rules index state head rest)
        else run rules index (discard state rest)
      | _ => run rules index (discard state rest)
termination_by (remaining state, state.agenda.pending.length)
decreasing_by
  all_goals first
    | exact Prod.Lex.left _ _ (propagate_remaining_lt rules index state head rest wasTrue)
    | apply Prod.Lex.right
      simp [discard, pendingEquation]

/-- The executable result is a contradiction or a greatest normalized model. -/
def OutcomeCorrect (rules : RuleTable n m) : Option (Vector Bool n) → Prop
  | none => NoModel rules
  | some values =>
      Models rules (fun label => values[label.val]) ∧
        ∀ assignment, Models rules assignment → Below assignment (fun label => values[label.val])

theorem run_correct (rules : RuleTable n m) (normalized : Normalized rules)
    (state : State n m) (valid : Valid rules state) :
    OutcomeCorrect rules (run rules (occurrences rules) state) := by
  rw [run]
  split
  · rename_i failed
    exact valid.sound.failed_sound failed
  · rename_i notFailed
    have noFailure : state.agenda.failed = false := Bool.eq_false_iff.mpr notFailed
    cases pendingEquation : state.agenda.pending with
    | nil =>
        exact ⟨terminal_models rules state valid noFailure pendingEquation, valid.upper⟩
    | cons row rest =>
        obtain ⟨head, labels, ruleEquation, zero⟩ := valid.sound.pending_ready row
          (by rw [pendingEquation]; exact List.mem_cons_self)
        simp only [ruleEquation]
        split
        · rename_i wasTrue
          exact run_correct rules normalized _ (propagate_valid rules normalized state valid
            row head labels rest pendingEquation ruleEquation zero wasTrue)
        · rename_i wasNotTrue
          have headFalse : state.counted.assignment head = false := Bool.eq_false_iff.mpr wasNotTrue
          exact run_correct rules normalized _ (discard_valid rules state valid row head labels
            rest pendingEquation ruleEquation headFalse)
termination_by (remaining state, state.agenda.pending.length)
decreasing_by
  all_goals first
    | exact Prod.Lex.left _ _
        (propagate_remaining_lt rules (occurrences rules) state head rest (by assumption))
    | apply Prod.Lex.right
      simp [discard, pendingEquation]

end State

/-- Solve a normalized rule array using one occurrence table throughout the worklist. -/
def solveRules (rules : RuleTable n m) : Option (Vector Bool n) :=
  let index := occurrences rules
  State.run rules index (State.initial rules)

theorem solveRules_correct (rules : RuleTable n m) (normalized : Normalized rules) :
    State.OutcomeCorrect rules (solveRules rules) :=
  State.run_correct rules normalized (State.initial rules) (State.initial_valid rules)

theorem solveRules_none_iff (rules : RuleTable n m) (normalized : Normalized rules) :
    solveRules rules = none ↔ NoModel rules := by
  have correct := solveRules_correct rules normalized
  cases result : solveRules rules with
  | none =>
      simp only [result, State.OutcomeCorrect] at correct
      exact ⟨fun _ => correct, fun _ => rfl⟩
  | some values =>
      simp only [result, State.OutcomeCorrect] at correct
      constructor
      · intro impossible
        contradiction
      · intro noModel
        exact False.elim (noModel ⟨fun label => values[label.val], correct.1⟩)

end Controller.Horn.Worklist
