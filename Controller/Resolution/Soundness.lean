module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Resolution.Trace

@[expose] public section

/-! Soundness for arbitrary typed CNFs and traces. No controller-family or
recognition hypothesis is used. The only inference is exact ordinary resolution.
-/

namespace Controller.Resolution

open CNF

def RowsEntailed (f : FiniteFormula v) (rows : Rows v) : Prop :=
  ∀ id c, rows id = some c → Entails f c

theorem resolvent_holds (a : Fin v → Bool) (pivot : Literal (Fin v))
    {left right : Clause (Fin v)} (hl : ClauseHolds a left) (hr : ClauseHolds a right) :
    ClauseHolds a (resolvent pivot left right) := by
  by_cases hp : LiteralHolds a pivot
  · rcases hl with ⟨l, hl, ha⟩
    have hn : l ≠ negate pivot := by
      intro h
      subst l
      exact (literalHolds_negate a pivot).mp ha hp
    exact ⟨l, (mem_resolvent pivot l left right).mpr (Or.inl ⟨hl, hn⟩), ha⟩
  · rcases hr with ⟨l, hr, ha⟩
    have hn : l ≠ pivot := by
      intro h
      subst l
      exact hp ha
    exact ⟨l, (mem_resolvent pivot l left right).mpr (Or.inr ⟨hr, hn⟩), ha⟩

theorem exactRule_entails {f : FiniteFormula v} {pivot : Literal (Fin v)}
    {left right out : Clause (Fin v)} (h : ExactRule pivot left right out)
    (hl : Entails f left) (hr : Entails f right) : Entails f out := by
  intro a ha
  apply (clauseHolds_congr (exactRule_sameLiterals h)).mpr
  exact resolvent_holds a pivot (hl a ha) (hr a ha)

theorem initialState_sound (f : FiniteFormula v) : RowsEntailed f (initialState f).rows := by
  intro id c h a ha
  by_cases hid : id = 0
  · simp [initialState, hid] at h
  · have hc : f.clauses[id - 1]? = some c := by simpa [initialState, hid] using h
    exact ha c (Array.mem_iff_getElem?.mpr ⟨id - 1, hc⟩)

theorem insertRow_sound {f : FiniteFormula v} {state : State v} {id : Nat}
    {c : Clause (Fin v)} (hrows : RowsEntailed f state.rows) (hc : Entails f c) :
    RowsEntailed f (insertRow state id c).rows := by
  intro j d hd
  by_cases hj : j = id
  · simp [insertRow, hj] at hd
    subst d
    exact hc
  · exact hrows j d (by simpa [insertRow, hj] using hd)

theorem applyStep_sound {f : FiniteFormula v} {state next : State v} {step : Step v}
    (hrows : RowsEntailed f state.rows) (h : applyStep state step = some next) :
    RowsEntailed f next.rows := by
  obtain ⟨left, right, hl, hr, hok, rfl⟩ := applyStep_success h
  apply insertRow_sound hrows
  exact exactRule_entails hok.2.2.2 (hrows _ _ hl) (hrows _ _ hr)

theorem runSteps_sound {f : FiniteFormula v} {state next : State v} {steps : List (Step v)}
    (hrows : RowsEntailed f state.rows) (h : runSteps state steps = some next) :
    RowsEntailed f next.rows := by
  induction steps generalizing state with
  | nil =>
    cases h
    exact hrows
  | cons step steps ih =>
    simp only [runSteps] at h
    cases hs : applyStep state step with
    | none => simp [hs] at h
    | some middle =>
      simp only [hs] at h
      exact ih (applyStep_sound hrows hs) h

theorem check_sound {f : FiniteFormula v} {trace : Trace v} (h : check f trace = true) :
    Unsatisfiable f := by
  unfold check at h
  split at h
  · cases hs : runSteps (initialState f) trace.steps with
    | none => simp [hs] at h
    | some state =>
      cases hc : state.rows trace.finalClauseId with
      | none => simp [hs, hc] at h
      | some c =>
        have hempty : c = [] := by simpa [hs, hc] using h
        subst c
        have he := runSteps_sound (initialState_sound f) hs _ _ hc
        rintro ⟨a, ha⟩
        exact clauseHolds_nil a (he a ha)
  · simp at h

theorem check_stdUnsat {f : FiniteFormula v} {trace : Trace v} (h : check f trace = true) :
    Controller.CNF.OrderedFormula.Unsat f :=
  (unsatisfiable_iff_stdUnsat f).mp (check_sound h)

/-- A requested macro clause may be represented by a stronger existing row.
The target is not inserted into the trace by a weakening rule. -/
structure DerivedSubclause (f : FiniteFormula v) (state : State v) (target : Clause (Fin v)) where
  rowId : Nat
  clause : Clause (Fin v)
  present : state.rows rowId = some clause
  subset : ClauseSubset clause target
  checkedPrefix : ∃ steps, runSteps (initialState f) steps = some state

theorem DerivedSubclause.row_entails {f : FiniteFormula v} {state : State v}
    {target : Clause (Fin v)} (d : DerivedSubclause f state target) : Entails f d.clause := by
  obtain ⟨steps, h⟩ := d.checkedPrefix
  exact runSteps_sound (initialState_sound f) h d.rowId d.clause d.present

theorem DerivedSubclause.target_entails {f : FiniteFormula v} {state : State v}
    {target : Clause (Fin v)} (d : DerivedSubclause f state target) : Entails f target := by
  intro a ha
  exact clauseHolds_mono d.subset (d.row_entails a ha)

def derivedSubclauseOfRun {f : FiniteFormula v} {state : State v} {steps : List (Step v)}
    (h : runSteps (initialState f) steps = some state) (id : Nat) (c target : Clause (Fin v))
    (hc : state.rows id = some c) (hsub : ClauseSubset c target) :
    DerivedSubclause f state target :=
  ⟨id, c, hc, hsub, ⟨steps, h⟩⟩

end Controller.Resolution
