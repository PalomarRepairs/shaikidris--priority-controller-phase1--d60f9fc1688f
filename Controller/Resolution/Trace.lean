module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.CNF.Relabel

@[expose] public section

/-! Ordinary-resolution traces with external, one-based clause IDs.

Input clause occurrences retain separate IDs. Derived IDs increase strictly but
may have gaps. A signed pivot removes its negation from the left parent and
itself from the right parent. Clause order is irrelevant to the exact resolvent;
derived clauses must contain no repeated literal. All literals inhabit `Fin v`.
-/

namespace Controller.Resolution

open CNF

abbrev Rows (v : Nat) := Nat → Option (Clause (Fin v))

structure State (v : Nat) where
  rows : Rows v
  lastId : Nat

structure Step (v : Nat) where
  id : Nat
  left : Nat
  right : Nat
  pivot : Literal (Fin v)
  clause : Clause (Fin v)
  deriving DecidableEq, Repr

structure Trace (v : Nat) where
  originalClauseCount : Nat
  steps : List (Step v)
  finalClauseId : Nat
  deriving DecidableEq, Repr

def initialState (f : FiniteFormula v) : State v :=
  ⟨fun id => if id = 0 then none else f.clauses[id - 1]?, f.clauses.size⟩

def insertRow (state : State v) (id : Nat) (c : Clause (Fin v)) : State v :=
  ⟨fun j => if j = id then some c else state.rows j, id⟩

def resolvent (pivot : Literal (Fin v)) (left right : Clause (Fin v)) : Clause (Fin v) :=
  normalizeClause ((left.filter (fun l => decide (l ≠ negate pivot))) ++
    (right.filter (fun l => decide (l ≠ pivot))))

def ExactRule (pivot : Literal (Fin v)) (left right out : Clause (Fin v)) : Prop :=
  negate pivot ∈ left ∧ pivot ∈ right ∧ out.Nodup ∧
    out.toFinset = (resolvent pivot left right).toFinset

instance (pivot : Literal (Fin v)) (left right out : Clause (Fin v)) :
    Decidable (ExactRule pivot left right out) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

def StepOK (state : State v) (step : Step v) (left right : Clause (Fin v)) : Prop :=
  state.lastId < step.id ∧ step.left < step.id ∧ step.right < step.id ∧
    ExactRule step.pivot left right step.clause

instance (state : State v) (step : Step v) (left right : Clause (Fin v)) :
    Decidable (StepOK state step left right) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

def applyStep (state : State v) (step : Step v) : Option (State v) :=
  match state.rows step.left, state.rows step.right with
  | some left, some right =>
    if StepOK state step left right then some (insertRow state step.id step.clause) else none
  | _, _ => none

def runSteps : State v → List (Step v) → Option (State v)
  | state, [] => some state
  | state, step :: steps =>
    match applyStep state step with
    | none => none
    | some next => runSteps next steps

def check (f : FiniteFormula v) (trace : Trace v) : Bool :=
  if trace.originalClauseCount = f.clauses.size then
    match runSteps (initialState f) trace.steps with
    | none => false
    | some state =>
      match state.rows trace.finalClauseId with
      | none => false
      | some c => c.isEmpty
  else false

@[simp] theorem initialState_zero (f : FiniteFormula v) :
    (initialState f).rows 0 = none := by simp [initialState]

theorem initialState_row (f : FiniteFormula v) (i : Nat) (hi : i < f.clauses.size) :
    (initialState f).rows (i + 1) = some f.clauses[i] := by
  simp [initialState, Array.getElem?_eq_getElem hi]

@[simp] theorem insertRow_self (state : State v) (id : Nat) (c : Clause (Fin v)) :
    (insertRow state id c).rows id = some c := by simp [insertRow]

theorem insertRow_other (state : State v) (id j : Nat) (c : Clause (Fin v)) (h : j ≠ id) :
    (insertRow state id c).rows j = state.rows j := by simp [insertRow, h]

@[simp] theorem mem_resolvent (pivot l : Literal (Fin v)) (left right : Clause (Fin v)) :
    l ∈ resolvent pivot left right ↔
      (l ∈ left ∧ l ≠ negate pivot) ∨ (l ∈ right ∧ l ≠ pivot) := by
  simp [resolvent]

theorem exactRule_sameLiterals {pivot : Literal (Fin v)} {left right out : Clause (Fin v)}
    (h : ExactRule pivot left right out) : SameLiterals out (resolvent pivot left right) := by
  intro l
  have hm := Finset.ext_iff.mp h.2.2.2 l
  simpa only [List.mem_toFinset] using hm

theorem applyStep_success {state next : State v} {step : Step v}
    (h : applyStep state step = some next) :
    ∃ left right, state.rows step.left = some left ∧ state.rows step.right = some right ∧
      StepOK state step left right ∧ next = insertRow state step.id step.clause := by
  unfold applyStep at h
  cases hl : state.rows step.left with
  | none => simp [hl] at h
  | some left =>
    cases hr : state.rows step.right with
    | none => simp [hl, hr] at h
    | some right =>
      simp only [hl, hr] at h
      split at h
      · rename_i hok
        cases h
        exact ⟨left, right, rfl, rfl, hok, rfl⟩
      · simp at h

theorem applyStep_lastId_gt {state next : State v} {step : Step v}
    (h : applyStep state step = some next) : state.lastId < next.lastId := by
  obtain ⟨left, right, hl, hr, hok, rfl⟩ := applyStep_success h
  exact hok.1

theorem applyStep_preserves_old_rows {state next : State v} {step : Step v}
    (h : applyStep state step = some next) (id : Nat) (hid : id ≤ state.lastId) :
    next.rows id = state.rows id := by
  obtain ⟨left, right, hl, hr, hok, rfl⟩ := applyStep_success h
  apply insertRow_other
  exact Nat.ne_of_lt (Nat.lt_of_le_of_lt hid hok.1)

theorem runSteps_lastId_le {state next : State v} {steps : List (Step v)}
    (h : runSteps state steps = some next) : state.lastId ≤ next.lastId := by
  induction steps generalizing state with
  | nil => cases h; exact Nat.le_refl _
  | cons step steps ih =>
    simp only [runSteps] at h
    cases hs : applyStep state step with
    | none => simp [hs] at h
    | some middle =>
      simp only [hs] at h
      exact Nat.le_trans (Nat.le_of_lt (applyStep_lastId_gt hs)) (ih h)

theorem runSteps_preserves_old_rows {state next : State v} {steps : List (Step v)}
    (h : runSteps state steps = some next) (id : Nat) (hid : id ≤ state.lastId) :
    next.rows id = state.rows id := by
  induction steps generalizing state with
  | nil => cases h; rfl
  | cons step steps ih =>
    simp only [runSteps] at h
    cases hs : applyStep state step with
    | none => simp [hs] at h
    | some middle =>
      simp only [hs] at h
      have hm : id ≤ middle.lastId := Nat.le_trans hid (Nat.le_of_lt (applyStep_lastId_gt hs))
      exact (ih h hm).trans (applyStep_preserves_old_rows hs id hid)

theorem runSteps_append (state : State v) (xs ys : List (Step v)) :
    runSteps state (xs ++ ys) = (runSteps state xs).bind (fun middle => runSteps middle ys) := by
  induction xs generalizing state with
  | nil => rfl
  | cons step steps ih =>
    simp only [List.cons_append, runSteps]
    cases applyStep state step <;> simp [ih]

theorem runSteps_original_row {f : FiniteFormula v} {state : State v} {steps : List (Step v)}
    (h : runSteps (initialState f) steps = some state) (i : Fin f.clauses.size) :
    state.rows (i.val + 1) = some f.clauses[i] := by
  rw [runSteps_preserves_old_rows h (i.val + 1) (Nat.succ_le_of_lt i.isLt)]
  exact initialState_row f i.val i.isLt

/-- Acceptance retains every original input occurrence, including duplicates. -/
theorem original_rows_distinct_ids (f : FiniteFormula v) (i j : Fin f.clauses.size)
    (h : i ≠ j) :
    i.val + 1 ≠ j.val + 1 ∧
      (initialState f).rows (i.val + 1) = some f.clauses[i] ∧
      (initialState f).rows (j.val + 1) = some f.clauses[j] := by
  refine ⟨?_, initialState_row f _ i.isLt, initialState_row f _ j.isLt⟩
  intro heq
  apply h
  exact Fin.ext (Nat.add_right_cancel heq)

/- The following kernel-reduced examples exercise acceptance boundaries. -/
private def testFormula : FiniteFormula 1 := ofClauses [[(0, false)], [(0, true)]]
private def testStep : Step 1 := ⟨7, 1, 2, (0, true), []⟩

example : check testFormula ⟨2, [testStep], 7⟩ = true := by decide
example : check testFormula ⟨2, [{ testStep with left := 3 }], 7⟩ = false := by decide
example : check testFormula ⟨2, [{ testStep with left := 7 }], 7⟩ = false := by decide
example : check testFormula ⟨2, [{ testStep with pivot := (0, false) }], 7⟩ = false := by decide
example : check testFormula ⟨2, [{ testStep with clause := [(0, true)] }], 7⟩ = false := by decide
example : check testFormula ⟨2, [testStep], 1⟩ = false := by decide
example : check testFormula ⟨3, [testStep], 7⟩ = false := by decide
example : check (ofClauses [[]] : FiniteFormula 0) ⟨1, [], 1⟩ = true := by decide

private def duplicateTestFormula : FiniteFormula 2 :=
  ofClauses [[(0, false), (1, true)], [(0, true)]]

example : (applyStep (initialState duplicateTestFormula)
    ⟨3, 1, 2, (0, true), [(1, true), (1, true)]⟩).isNone = true := by decide

example : (applyStep (initialState duplicateTestFormula)
    ⟨3, 1, 2, (0, true), [(1, true)]⟩).isSome = true := by decide

end Controller.Resolution
