module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.HornReplay
public import Controller.Horn.DualHorn
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Fin

@[expose] public section

/-! A finite dual-Horn clause scan retains original row IDs and reverse unit
reasons. Each propagation removes one live variable; the scan has no branch
tree and keeps at most one reason per declared variable. -/
namespace Controller.NativeProof.HornTrail
open Controller.CNF Controller.Resolution Controller.Resolution.RUP

def valuation (live : Finset (Fin v)) : Fin v → Bool := fun label => decide (label ∈ live)

def badRow (formula : FiniteFormula v) (live : Finset (Fin v)) :
    Option (Fin formula.clauses.size) :=
  (List.finRange formula.clauses.size).find? fun row =>
    !(Controller.CNF.OrderedFormula.Clause.eval (valuation live) formula.clauses[row.val])

def negative (clause : Clause (Fin v)) : Option (Literal (Fin v)) :=
  clause.find? fun literal => !literal.2

structure Conflict (v : Nat) where
  rowId : Nat
  clause : Clause (Fin v)
  reasons : List (RowReason v)

/-- The extra final scan allows a conflict after every variable became false. -/
def scan (formula : FiniteFormula v) : Nat → Finset (Fin v) →
    List (RowReason v) → Option (Conflict v)
  | 0, _, _ => none
  | fuel + 1, live, reasons =>
      match badRow formula live with
      | none => none
      | some row =>
          let clause := formula.clauses[row.val]
          match negative clause with
          | none => some ⟨row.val + 1, clause, reasons⟩
          | some pivot => scan formula fuel (live.erase pivot.1)
              (⟨row.val + 1, ⟨pivot, clause⟩⟩ :: reasons)

def produce (formula : FiniteFormula v) : Option (Conflict v) :=
  scan formula (v + 1) Finset.univ []

theorem scan_conflict_positive (formula : FiniteFormula v) (fuel : Nat)
    (live : Finset (Fin v)) (reasons : List (RowReason v)) (result : Conflict v)
    (returned : scan formula fuel live reasons = some result) :
    negative result.clause = none := by
  induction fuel generalizing live reasons with
  | zero => simp [scan] at returned
  | succ fuel ih =>
    cases selected : badRow formula live with
    | none => simp [scan, selected] at returned
    | some row =>
      cases head : negative formula.clauses[row.val] with
      | none =>
        simp only [scan, selected] at returned
        rw [head] at returned
        have same := Option.some.inj returned
        rw [← same]
        exact head
      | some pivot =>
        apply ih (live.erase pivot.1)
          (⟨row.val + 1, ⟨pivot, formula.clauses[row.val]⟩⟩ :: reasons)
        simp only [scan, selected] at returned
        rw [head] at returned
        exact returned

theorem badRow_false (formula : FiniteFormula v) (live : Finset (Fin v))
    (row : Fin formula.clauses.size) (found : badRow formula live = some row) :
    ¬ClauseHolds (valuation live) formula.clauses[row.val] := by
  have failed := List.find?_some found
  intro satisfied
  have evaluated := (clauseHolds_iff_eval _ _).mp satisfied
  simp [evaluated] at failed

theorem badRow_none_model (formula : FiniteFormula v) (live : Finset (Fin v))
    (absent : badRow formula live = none) : Satisfies (valuation live) formula := by
  have none := List.find?_eq_none.mp absent
  intro clause member
  obtain ⟨row, bound, same⟩ := Array.getElem_of_mem member
  apply (clauseHolds_iff_eval _ _).mpr
  have entry := none ⟨row, bound⟩ (List.mem_finRange _)
  simpa [same] using entry

theorem negative_some (clause : Clause (Fin v)) (pivot : Literal (Fin v))
    (found : negative clause = some pivot) : pivot ∈ clause ∧ pivot.2 = false := by
  have result := List.find?_some found
  exact ⟨List.mem_of_find?_eq_some found, by simpa using result⟩

theorem negative_none (clause : Clause (Fin v)) (absent : negative clause = none) :
    ∀ literal ∈ clause, literal.2 = true := by
  have none := List.find?_eq_none.mp absent
  intro literal member
  have result := none literal member
  simpa using result

theorem negative_live (live : Finset (Fin v)) (clause : Clause (Fin v))
    (failed : ¬ClauseHolds (valuation live) clause) (pivot : Literal (Fin v))
    (found : negative clause = some pivot) : pivot.1 ∈ live := by
  obtain ⟨member, negative⟩ := negative_some clause pivot found
  by_contra absent
  apply failed
  exact ⟨pivot, member, by simp [LiteralHolds, valuation, absent, negative]⟩

/-- Reverse reasons contain exactly the positive literals of removed labels. -/
def Covers (live : Finset (Fin v)) (reasons : List (RowReason v)) : Prop :=
  ∀ label, label ∉ live → (label, true) ∈ negations (reasons.map RowReason.entry)

theorem negative_reason (live : Finset (Fin v)) (reasons : List (RowReason v))
    (covers : Covers live reasons) (clause : Clause (Fin v))
    (restricted : Controller.Horn.DualHornClause clause)
    (failed : ¬ClauseHolds (valuation live) clause) (pivot : Literal (Fin v))
    (found : negative clause = some pivot) :
    ReasonEarlier pivot clause (negations (reasons.map RowReason.entry) ++ []) := by
  obtain ⟨member, negative⟩ := negative_some clause pivot found
  refine ⟨member, ?_⟩
  intro literal present different
  have positive : literal.2 = true := by
    rcases restricted with tautology | unique
    · obtain ⟨opposite, pos, neg⟩ := tautology
      exact False.elim (failed (tautology_holds _ pos neg))
    · cases polarity : literal.2 with
      | true => rfl
      | false =>
          have same := unique literal present pivot member polarity negative
          exact False.elim (different (Prod.ext same (polarity.trans negative.symm)))
  have absent : literal.1 ∉ live := by
    intro alive
    exact failed ⟨literal, present, by simp [LiteralHolds, valuation, alive, positive]⟩
  have literalEq : literal = (literal.1, true) := Prod.ext rfl positive
  rw [List.append_nil]
  exact literalEq.symm ▸ covers literal.1 absent

theorem covers_erase (live : Finset (Fin v)) (reasons : List (RowReason v))
    (covers : Covers live reasons) (row : Nat) (pivot : Literal (Fin v))
    (clause : Clause (Fin v)) (negative : pivot.2 = false) :
    Covers (live.erase pivot.1) (⟨row, ⟨pivot, clause⟩⟩ :: reasons) := by
  intro label absent
  simp only [List.map_cons, negations, List.mem_cons]
  by_cases same : label = pivot.1
  · left
    simp [same, negate, Std.Sat.Literal.negate, negative]
  · right
    apply covers label
    simpa [Finset.mem_erase, same] using absent

theorem positive_conflict (live : Finset (Fin v)) (reasons : List (RowReason v))
    (covers : Covers live reasons) (clause : Clause (Fin v))
    (failed : ¬ClauseHolds (valuation live) clause) (absent : negative clause = none) :
    ClauseSubset clause (negations (reasons.map RowReason.entry)) := by
  intro literal member
  have positive := negative_none clause absent literal member
  have removed : literal.1 ∉ live := by
    intro alive
    exact failed ⟨literal, member, by simp [LiteralHolds, valuation, alive, positive]⟩
  have same : literal = (literal.1, true) := Prod.ext rfl positive
  exact same.symm ▸ covers literal.1 removed

structure Certified (formula : FiniteFormula v) (result : Conflict v) : Prop where
  present : (initialState formula).rows result.rowId = some result.clause
  bound : result.rowId ≤ (initialState formula).lastId
  known : KnownReasons (initialState formula) result.reasons
  valid : ValidReasons [] (result.reasons.map RowReason.entry)
  conflict : ClauseSubset result.clause (negations (result.reasons.map RowReason.entry))

/-- Every UNSAT dual-Horn input returns a causal conflict trail within the
declared variable budget. No model search or splitting is used. -/
theorem scan_complete (formula : FiniteFormula v) (restricted : Controller.Horn.DualHorn formula)
    (unsat : Unsatisfiable formula) (fuel : Nat) (live : Finset (Fin v))
    (reasons : List (RowReason v)) (capacity : live.card < fuel)
    (covers : Covers live reasons) (known : KnownReasons (initialState formula) reasons)
    (valid : ValidReasons [] (reasons.map RowReason.entry)) :
    ∃ result, scan formula fuel live reasons = some result ∧ Certified formula result ∧
      result.reasons.length ≤ reasons.length + live.card := by
  induction fuel generalizing live reasons with
  | zero => omega
  | succ fuel ih =>
    cases selected : badRow formula live with
    | none => exact False.elim (unsat ⟨valuation live, badRow_none_model formula live selected⟩)
    | some row =>
      have failed := badRow_false formula live row selected
      have present := initialState_row formula row.val row.isLt
      have bound : row.val + 1 ≤ (initialState formula).lastId := by
        change row.val + 1 ≤ formula.clauses.size
        omega
      cases found : negative (formula.clauses[row.val]'row.isLt) with
      | none =>
        refine ⟨⟨row.val + 1, formula.clauses[row.val]'row.isLt, reasons⟩, ?_,
          ⟨present, bound, known, valid, positive_conflict live reasons covers _ failed found⟩, ?_⟩
        · simp only [scan, selected]
          rw [found]
        · simp
      | some pivot =>
        have alive := negative_live live _ failed pivot found
        have size : (live.erase pivot.1).card + 1 = live.card := Finset.card_erase_add_one alive
        have newKnown : KnownReasons (initialState formula)
            (⟨row.val + 1, ⟨pivot, formula.clauses[row.val]'row.isLt⟩⟩ :: reasons) := by
          intro reason member
          rcases List.mem_cons.mp member with same | old
          · subst reason
            exact ⟨present, bound, (negative_some _ _ found).1⟩
          · exact known reason old
        have newValid : ValidReasons []
            ((⟨row.val + 1, ⟨pivot, formula.clauses[row.val]'row.isLt⟩⟩ :: reasons).map RowReason.entry) :=
          ⟨negative_reason live reasons covers _
            (restricted _ (Array.getElem_mem row.isLt)) failed pivot found, valid⟩
        obtain ⟨result, returned, certified, count⟩ := ih (live.erase pivot.1)
          (⟨row.val + 1, ⟨pivot, formula.clauses[row.val]'row.isLt⟩⟩ :: reasons) (by omega)
          (covers_erase live reasons covers _ _ _ (negative_some _ _ found).2) newKnown newValid
        refine ⟨result, ?_, certified, ?_⟩
        · simp only [scan, selected]
          rw [found]
          exact returned
        · simp only [List.length_cons] at count
          omega

theorem produce_complete (formula : FiniteFormula v)
    (restricted : Controller.Horn.DualHorn formula) (unsat : Unsatisfiable formula) :
    ∃ result, produce formula = some result ∧ Certified formula result ∧
      result.reasons.length ≤ v := by
  simpa [produce] using scan_complete formula restricted unsat (v + 1) Finset.univ []
    (by simp) (by simp [Covers]) (by simp [KnownReasons]) (by trivial)

/-- Ordinary resolution expansion of the actual generated reason trail. -/
def refute (formula : FiniteFormula v) : Option (CompiledTrail v) :=
  (produce formula).map fun result =>
    compileReasons (initialState formula) result.rowId result.clause result.reasons

/-- Every UNSAT finite dual-Horn formula has an emitted checked empty subclause
with at most one ordinary resolution inference per declared variable. -/
theorem refute_complete (formula : FiniteFormula v)
    (restricted : Controller.Horn.DualHorn formula) (unsat : Unsatisfiable formula) :
    ∃ trace, refute formula = some trace ∧
      Nonempty (DerivedSubclause formula trace.state []) ∧ trace.steps.length ≤ v := by
  obtain ⟨result, returned, certified, count⟩ := produce_complete formula restricted unsat
  refine ⟨compileReasons (initialState formula) result.rowId result.clause result.reasons,
    by simp [refute, returned], ?_, ?_⟩
  · exact ⟨compileReasons_derived formula (initialState formula) [] rfl result.rowId
      result.clause [] result.reasons certified.known certified.present certified.bound
      certified.valid (by simpa only [List.append_nil] using certified.conflict)⟩
  · exact (compileReasons_count_le _ _ _ _).trans count

/-- The public certificate contains the original ordered row count and the
actual emitted steps; it can be replayed by the ordinary resolution checker. -/
def certificate (formula : FiniteFormula v) : Option (Trace v) :=
  (refute formula).map fun result => ⟨formula.clauses.size, result.steps, result.rowId⟩

theorem certificate_complete (formula : FiniteFormula v)
    (restricted : Controller.Horn.DualHorn formula) (unsat : Unsatisfiable formula) :
    ∃ trace, certificate formula = some trace ∧ check formula trace = true ∧
      trace.steps.length ≤ v := by
  obtain ⟨result, returned, certified, count⟩ := produce_complete formula restricted unsat
  let actual := compileReasons (initialState formula) result.rowId result.clause result.reasons
  have run := compileReasons_run result.reasons (initialState formula) result.rowId
    result.clause certified.known certified.present certified.bound
  have empty : actual.clause = [] := by
    have subset := reverseTrail_subset [] (result.reasons.map RowReason.entry)
      certified.valid result.clause (by simpa only [List.append_nil] using certified.conflict)
    have contained : ClauseSubset actual.clause [] := by
      simpa only [actual, compileReasons_clause] using subset
    cases shape : actual.clause with
    | nil => rfl
    | cons first rest => exact False.elim (List.not_mem_nil (contained first (by simp [shape])))
  refine ⟨⟨formula.clauses.size, actual.steps, actual.rowId⟩,
    by simp [certificate, refute, returned, actual], ?_, ?_⟩
  · have actualRun : runSteps (initialState formula) actual.steps = some actual.state := run.1
    have actualRow : actual.state.rows actual.rowId = some actual.clause := run.2.1
    simp only [check, ↓reduceIte, actualRun, actualRow, empty]
    rfl
  · exact (compileReasons_count_le _ _ _ _).trans count

end Controller.NativeProof.HornTrail
