module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Resolution.Soundness

@[expose] public section

/-! Backward conflict analysis uses ordinary resolution only when the current
clause contains the propagated literal's negation. An absent pivot is skipped;
no target clause is inserted by weakening. The producer emits a checked
ordinary-resolution trace with at most one inference per trail entry. -/
namespace Controller.Resolution.RUP
open Controller.CNF

/-- The reason is unit after the earlier trail: every non-pivot literal is
already among the negations of the earlier assignments. -/
def ReasonEarlier (pivot : Literal (Fin v)) (reason earlier : Clause (Fin v)) : Prop :=
  pivot ∈ reason ∧ ∀ literal ∈ reason, literal ≠ pivot → literal ∈ earlier

def reverseClause (pivot : Literal (Fin v)) (current reason : Clause (Fin v)) : Clause (Fin v) :=
  if negate pivot ∈ current then resolvent pivot current reason else current

@[simp] theorem reverseClause_skip (pivot : Literal (Fin v)) (current reason : Clause (Fin v))
    (absent : negate pivot ∉ current) : reverseClause pivot current reason = current := by
  simp [reverseClause, absent]

/-- Removing the latest assignment leaves only earlier falsified literals. -/
theorem reverseClause_subset (pivot : Literal (Fin v)) (current reason earlier : Clause (Fin v))
    (currentSubset : ClauseSubset current (negate pivot :: earlier))
    (reasonEarlier : ReasonEarlier pivot reason earlier) :
    ClauseSubset (reverseClause pivot current reason) earlier := by
  intro literal member
  by_cases present : negate pivot ∈ current
  · rw [reverseClause, ite_eq_left present] at member
    rcases (mem_resolvent pivot literal current reason).mp member with left | right
    · rcases List.mem_cons.mp (currentSubset literal left.1) with same | old
      · exact False.elim (left.2 same)
      · exact old
    · exact reasonEarlier.2 literal right.1 right.2
  · rw [reverseClause, ite_eq_right present] at member
    rcases List.mem_cons.mp (currentSubset literal member) with same | old
    · exact False.elim (present (same ▸ member))
    · exact old

/-- The core first-occurrence deduplicator has a duplicate-free result. -/
theorem eraseDups_nodup (clause : Clause (Fin v)) : clause.eraseDups.Nodup := by
  suffices universal : ∀ size, ∀ input : Clause (Fin v), input.length = size → input.eraseDups.Nodup by
    exact universal clause.length clause rfl
  intro size
  induction size using Nat.strong_induction_on with
  | h size ih =>
      intro input lengthEq
      cases input with
      | nil => simp
      | cons literal rest =>
          rw [List.eraseDups_cons]
          apply List.nodup_cons.mpr
          constructor
          · simp [List.mem_eraseDups]
          · apply ih (rest.filter (fun item => !item == literal)).length ?_
              (rest.filter (fun item => !item == literal)) rfl
            have filtered := List.length_filter_le (fun item => !item == literal) rest
            simp only [List.length_cons] at lengthEq
            omega

/-- Present pivots use the exact ordinary resolution rule; absent ones require
no inference. This statement neither adds a target axiom nor weakens a clause. -/
theorem reverseClause_rule (pivot : Literal (Fin v)) (current reason : Clause (Fin v))
    (reasonContains : pivot ∈ reason) :
    reverseClause pivot current reason = current ∨
      ExactRule pivot current reason (reverseClause pivot current reason) := by
  by_cases present : negate pivot ∈ current
  · right
    rw [reverseClause, ite_eq_left present]
    refine ⟨present, reasonContains, ?_, rfl⟩
    exact eraseDups_nodup _
  · left
    exact reverseClause_skip pivot current reason present

/-- Each reverse operation emits either zero or one resolution inference. -/
def inferenceCount (pivot : Literal (Fin v)) (current : Clause (Fin v)) : Nat :=
  if negate pivot ∈ current then 1 else 0

theorem inferenceCount_le_one (pivot : Literal (Fin v)) (current : Clause (Fin v)) :
    inferenceCount pivot current ≤ 1 := by
  unfold inferenceCount
  split <;> omega

/-- Reasons are ordered latest propagation first for backward analysis. -/
structure ReverseReason (v : Nat) where
  pivot : Literal (Fin v)
  clause : Clause (Fin v)

def negations (reasons : List (ReverseReason v)) : Clause (Fin v) :=
  reasons.map (fun reason => negate reason.pivot)

/-- Each reason is justified by the strictly earlier trail and the negated
requested-target assumptions. Original row availability is checked separately. -/
def ValidReasons (target : Clause (Fin v)) : List (ReverseReason v) → Prop
  | [] => True
  | reason :: earlier =>
      ReasonEarlier reason.pivot reason.clause (negations earlier ++ target) ∧
        ValidReasons target earlier

def reverseTrail : List (ReverseReason v) → Clause (Fin v) → Clause (Fin v)
  | [], current => current
  | reason :: earlier, current =>
      reverseTrail earlier (reverseClause reason.pivot current reason.clause)

/-- The final clause contains only requested-target literals, including when
conflict occurs before every planned propagation has been used. -/
theorem reverseTrail_subset (target : Clause (Fin v)) (reasons : List (ReverseReason v))
    (valid : ValidReasons target reasons) (current : Clause (Fin v))
    (currentSubset : ClauseSubset current (negations reasons ++ target)) :
    ClauseSubset (reverseTrail reasons current) target := by
  induction reasons generalizing current with
  | nil => simpa [reverseTrail, negations] using currentSubset
  | cons reason earlier ih =>
      apply ih valid.2
      exact reverseClause_subset reason.pivot current reason.clause
        (negations earlier ++ target) (by simpa [negations] using currentSubset) valid.1

def trailInferenceCount : List (ReverseReason v) → Clause (Fin v) → Nat
  | [], _ => 0
  | reason :: earlier, current =>
      inferenceCount reason.pivot current +
        trailInferenceCount earlier (reverseClause reason.pivot current reason.clause)

/-- At most one inference per successful propagation; absent pivots cost none. -/
theorem trailInferenceCount_le_length (reasons : List (ReverseReason v))
    (current : Clause (Fin v)) : trailInferenceCount reasons current ≤ reasons.length := by
  induction reasons generalizing current with
  | nil => simp [trailInferenceCount]
  | cons reason earlier ih =>
      have one := inferenceCount_le_one reason.pivot current
      have tail := ih (reverseClause reason.pivot current reason.clause)
      simp only [trailInferenceCount, List.length_cons]
      omega

@[simp] theorem reverseTrail_empty (reasons : List (ReverseReason v)) :
    reverseTrail reasons [] = [] := by
  induction reasons with
  | nil => rfl
  | cons reason earlier ih => simpa [reverseTrail, reverseClause] using ih

@[simp] theorem trailInferenceCount_empty (reasons : List (ReverseReason v)) :
    trailInferenceCount reasons [] = 0 := by
  induction reasons with
  | nil => rfl
  | cons reason earlier ih =>
      simpa [trailInferenceCount, inferenceCount, reverseClause] using ih

/-- Fresh IDs preserve every earlier reason row. -/
def resolutionStep (state : State v) (leftId rightId : Nat)
    (pivot : Literal (Fin v)) (left right : Clause (Fin v)) : Step v :=
  ⟨state.lastId + 1, leftId, rightId, pivot, resolvent pivot left right⟩

/-- A present backward pivot constructs a step accepted by the ordinary
resolution checker, using actual available parent rows. -/
theorem resolutionStep_apply (state : State v) (leftId rightId : Nat)
    (pivot : Literal (Fin v)) (left right : Clause (Fin v))
    (leftRow : state.rows leftId = some left) (rightRow : state.rows rightId = some right)
    (leftBound : leftId ≤ state.lastId) (rightBound : rightId ≤ state.lastId)
    (leftPivot : negate pivot ∈ left) (rightPivot : pivot ∈ right) :
    applyStep state (resolutionStep state leftId rightId pivot left right) =
      some (insertRow state (state.lastId + 1) (resolvent pivot left right)) := by
  have rule : ExactRule pivot left right (resolvent pivot left right) := by
    refine ⟨leftPivot, rightPivot, ?_, rfl⟩
    exact eraseDups_nodup _
  have valid : StepOK state (resolutionStep state leftId rightId pivot left right) left right := by
    refine ⟨by simp [resolutionStep], by simpa [resolutionStep] using (show leftId < state.lastId + 1 by omega),
      by simpa [resolutionStep] using (show rightId < state.lastId + 1 by omega), rule⟩
  simp only [applyStep, resolutionStep, leftRow, rightRow]
  exact ite_eq_left valid

/-- The constructed inference is executable as a singleton checked trace. -/
theorem resolutionStep_run (state : State v) (leftId rightId : Nat)
    (pivot : Literal (Fin v)) (left right : Clause (Fin v))
    (leftRow : state.rows leftId = some left) (rightRow : state.rows rightId = some right)
    (leftBound : leftId ≤ state.lastId) (rightBound : rightId ≤ state.lastId)
    (leftPivot : negate pivot ∈ left) (rightPivot : pivot ∈ right) :
    runSteps state [resolutionStep state leftId rightId pivot left right] =
      some (insertRow state (state.lastId + 1) (resolvent pivot left right)) := by
  simp only [runSteps, resolutionStep_apply state leftId rightId pivot left right
    leftRow rightRow leftBound rightBound leftPivot rightPivot]

/-- A propagation reason references a real pre-existing resolution row. -/
structure RowReason (v : Nat) where
  rowId : Nat
  entry : ReverseReason v

structure CompiledTrail (v : Nat) where
  state : State v
  rowId : Nat
  clause : Clause (Fin v)
  steps : List (Step v)

/-- The functional producer emits exact resolutions, reuses the current row
when a pivot is absent, and never inserts the requested target clause. -/
def compileReasons (state : State v) (rowId : Nat) (current : Clause (Fin v)) :
    List (RowReason v) → CompiledTrail v
  | [] => ⟨state, rowId, current, []⟩
  | reason :: earlier =>
      if negate reason.entry.pivot ∈ current then
        let step := resolutionStep state rowId reason.rowId reason.entry.pivot current reason.entry.clause
        let next := insertRow state (state.lastId + 1)
          (resolvent reason.entry.pivot current reason.entry.clause)
        let tail := compileReasons next (state.lastId + 1)
          (resolvent reason.entry.pivot current reason.entry.clause) earlier
        { tail with steps := step :: tail.steps }
      else compileReasons state rowId current earlier

/-- Producer metadata must bind every reason to an available earlier row.
These checks will justify complete ordinary-checker acceptance. -/
def KnownReasons (state : State v) (reasons : List (RowReason v)) : Prop :=
  ∀ reason ∈ reasons, state.rows reason.rowId = some reason.entry.clause ∧
    reason.rowId ≤ state.lastId ∧ reason.entry.pivot ∈ reason.entry.clause

theorem compileReasons_clause (state : State v) (rowId : Nat) (current : Clause (Fin v))
    (reasons : List (RowReason v)) :
    (compileReasons state rowId current reasons).clause =
      reverseTrail (reasons.map RowReason.entry) current := by
  induction reasons generalizing state rowId current with
  | nil => rfl
  | cons reason earlier ih =>
      by_cases present : negate reason.entry.pivot ∈ current
      · simpa [compileReasons, present, reverseTrail, reverseClause] using
          ih (insertRow state (state.lastId + 1)
            (resolvent reason.entry.pivot current reason.entry.clause)) (state.lastId + 1)
            (resolvent reason.entry.pivot current reason.entry.clause)
      · simpa [compileReasons, present, reverseTrail, reverseClause] using ih state rowId current

theorem compileReasons_count (state : State v) (rowId : Nat) (current : Clause (Fin v))
    (reasons : List (RowReason v)) :
    (compileReasons state rowId current reasons).steps.length =
      trailInferenceCount (reasons.map RowReason.entry) current := by
  induction reasons generalizing state rowId current with
  | nil => rfl
  | cons reason earlier ih =>
      by_cases present : negate reason.entry.pivot ∈ current
      · simp only [compileReasons, ite_eq_left present, List.length_cons, List.map_cons,
          trailInferenceCount, inferenceCount, ite_eq_left present, reverseClause, ite_eq_left present]
        rw [ih]
        omega
      · simpa [compileReasons, present, trailInferenceCount, inferenceCount, reverseClause] using
          ih state rowId current

/-- The actual emitted step list has at most one inference per trail entry. -/
theorem compileReasons_count_le (state : State v) (rowId : Nat) (current : Clause (Fin v))
    (reasons : List (RowReason v)) :
    (compileReasons state rowId current reasons).steps.length ≤ reasons.length := by
  rw [compileReasons_count]
  simpa using trailInferenceCount_le_length (reasons.map RowReason.entry) current

/-- Every emitted inference checks, and the final stronger clause is an actual
available row. Earlier reason rows survive all fresh insertions. -/
theorem compileReasons_run (reasons : List (RowReason v)) (state : State v)
    (rowId : Nat) (current : Clause (Fin v))
    (known : KnownReasons state reasons) (currentRow : state.rows rowId = some current)
    (currentBound : rowId ≤ state.lastId) :
    runSteps state (compileReasons state rowId current reasons).steps =
      some (compileReasons state rowId current reasons).state ∧
    (compileReasons state rowId current reasons).state.rows
      (compileReasons state rowId current reasons).rowId =
        some (compileReasons state rowId current reasons).clause ∧
    (compileReasons state rowId current reasons).rowId ≤
      (compileReasons state rowId current reasons).state.lastId := by
  induction reasons generalizing state rowId current with
  | nil => exact ⟨rfl, currentRow, currentBound⟩
  | cons reason earlier ih =>
      have reasonKnown := known reason (by simp)
      by_cases present : negate reason.entry.pivot ∈ current
      · let next := insertRow state (state.lastId + 1)
          (resolvent reason.entry.pivot current reason.entry.clause)
        have checked := resolutionStep_apply state rowId reason.rowId reason.entry.pivot
          current reason.entry.clause currentRow reasonKnown.1 currentBound reasonKnown.2.1
          present reasonKnown.2.2
        have earlierKnown : KnownReasons next earlier := by
          intro other member
          have old := known other (by simp [member])
          refine ⟨?_, ?_, old.2.2⟩
          · exact (applyStep_preserves_old_rows checked other.rowId old.2.1).trans old.1
          · change other.rowId ≤ state.lastId + 1
            omega
        have tail := ih next (state.lastId + 1)
          (resolvent reason.entry.pivot current reason.entry.clause) earlierKnown
          (insertRow_self state _ _) (by simp [next, insertRow])
        refine ⟨?_, ?_, ?_⟩
        · simpa only [compileReasons, ite_eq_left present, runSteps, checked] using tail.1
        · simpa only [compileReasons, ite_eq_left present] using tail.2.1
        · simpa only [compileReasons, ite_eq_left present] using tail.2.2
      · have earlierKnown : KnownReasons state earlier := by
          intro other member
          exact known other (by simp [member])
        simpa only [compileReasons, ite_eq_right present] using
          ih state rowId current earlierKnown currentRow currentBound

/-- A completed RUP analysis yields a real derived subclause of the target;
its checked prefix concatenates the original proof with only emitted steps. -/
def compileReasons_derived (formula : FiniteFormula v) (state : State v)
    (prefixSteps : List (Step v))
    (prefixRun : runSteps (initialState formula) prefixSteps = some state)
    (rowId : Nat) (current target : Clause (Fin v)) (reasons : List (RowReason v))
    (known : KnownReasons state reasons) (currentRow : state.rows rowId = some current)
    (currentBound : rowId ≤ state.lastId)
    (valid : ValidReasons target (reasons.map RowReason.entry))
    (conflict : ClauseSubset current (negations (reasons.map RowReason.entry) ++ target)) :
    DerivedSubclause formula (compileReasons state rowId current reasons).state target where
  rowId := (compileReasons state rowId current reasons).rowId
  clause := (compileReasons state rowId current reasons).clause
  present := (compileReasons_run reasons state rowId current known currentRow currentBound).2.1
  subset := by
    rw [compileReasons_clause]
    exact reverseTrail_subset target _ valid current conflict
  checkedPrefix := by
    refine ⟨prefixSteps ++ (compileReasons state rowId current reasons).steps, ?_⟩
    rw [runSteps_append, prefixRun]
    exact compileReasons_run reasons state rowId current known currentRow currentBound |>.1

/-- A tautological requested macro is skipped rather than inserted as a row. -/
def tautologyCheck (target : Clause (Fin v)) : Bool :=
  target.any (fun literal => decide (negate literal ∈ target))

theorem tautologyCheck_iff (target : Clause (Fin v)) :
    tautologyCheck target = true ↔ ∃ literal ∈ target, negate literal ∈ target := by
  simp [tautologyCheck, List.any_eq_true]

def compileMacro (state : State v) (rowId : Nat) (current target : Clause (Fin v))
    (reasons : List (RowReason v)) : Option (CompiledTrail v) :=
  if tautologyCheck target = true then none else some (compileReasons state rowId current reasons)

@[simp] theorem compileMacro_skip (state : State v) (rowId : Nat)
    (current target : Clause (Fin v)) (reasons : List (RowReason v))
    (tautological : ∃ literal ∈ target, negate literal ∈ target) :
    compileMacro state rowId current target reasons = none := by
  simp [compileMacro, (tautologyCheck_iff target).mpr tautological]

theorem compileMacro_nonTautological (state : State v) (rowId : Nat)
    (current target : Clause (Fin v)) (reasons : List (RowReason v))
    (nonTautological : ¬ ∃ literal ∈ target, negate literal ∈ target) :
    compileMacro state rowId current target reasons = some (compileReasons state rowId current reasons) := by
  have check : tautologyCheck target ≠ true := by
    intro accepted
    exact nonTautological ((tautologyCheck_iff target).mp accepted)
  simp [compileMacro, check]

end Controller.Resolution.RUP
