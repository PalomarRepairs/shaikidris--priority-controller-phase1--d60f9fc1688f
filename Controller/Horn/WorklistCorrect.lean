module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Horn.Worklist

@[expose] public section

/-!
# Greatest-model solver for finite dual-Horn formulas

Rule normalization, stored positive counts, and the terminating row agenda
implement the greatest-model semantics. All declared variables remain in the
returned vector, including variables absent from every input row.
-/

namespace Controller.Horn.Worklist

open CNF

theorem normalizedTable_models_iff (formula : Formula (Fin n)) (dualHorn : DualHorn formula)
    (assignment : Fin n → Bool) :
    Models (normalizedTable formula) assignment ↔ Satisfies assignment formula := by
  simp only [Models, normalizedTable, Vector.getElem_mk]
  exact compileFormula_holds_iff formula dualHorn assignment

/-- Compute a greatest model, or report contradiction, for a finite dual-Horn formula. -/
def solveFormula (formula : Formula (Fin n)) : Option (Vector Bool n) :=
  solveRules (normalizedTable formula)

/-- Contradiction is returned exactly for unsatisfiable dual-Horn formulas. -/
theorem solveFormula_none_iff (formula : Formula (Fin n)) (dualHorn : DualHorn formula) :
    solveFormula formula = none ↔ Unsatisfiable formula := by
  rw [solveFormula, solveRules_none_iff _ (normalizedTable_normalized formula)]
  exact not_congr (exists_congr fun assignment => normalizedTable_models_iff formula dualHorn assignment)

/-- Every returned vector is a model and bounds every other model from above. -/
theorem solveFormula_some_model (formula : Formula (Fin n)) (dualHorn : DualHorn formula)
    (values : Vector Bool n) (returned : solveFormula formula = some values) :
    Satisfies (fun label => values[label.val]) formula ∧
      ∀ assignment, Satisfies assignment formula → Below assignment (fun label => values[label.val]) := by
  have correct := solveRules_correct (normalizedTable formula) (normalizedTable_normalized formula)
  change solveRules (normalizedTable formula) = some values at returned
  rw [returned] at correct
  obtain ⟨model, upper⟩ := correct
  exact ⟨(normalizedTable_models_iff formula dualHorn _).mp model,
    fun assignment satisfied => upper assignment
      ((normalizedTable_models_iff formula dualHorn assignment).mpr satisfied)⟩

/-- The returned assignment equals the independently defined greatest-model semantics. -/
theorem solveFormula_some_greatest (formula : Formula (Fin n)) (dualHorn : DualHorn formula)
    (values : Vector Bool n) (returned : solveFormula formula = some values) :
    (fun label => values[label.val]) = greatestCandidate formula := by
  obtain ⟨model, upper⟩ := solveFormula_some_model formula dualHorn values returned
  exact terminal_state_eq_greatest (satisfies_rulesClosed dualHorn model) upper

/-- A successful terminal assignment also meets D02's explicit propagation closure condition. -/
theorem solveFormula_some_rulesClosed (formula : Formula (Fin n)) (dualHorn : DualHorn formula)
    (values : Vector Bool n) (returned : solveFormula formula = some values) :
    RulesClosed formula (fun label => values[label.val]) :=
  satisfies_rulesClosed dualHorn (solveFormula_some_model formula dualHorn values returned).1

/-- A model is returned exactly when the finite dual-Horn input has a model. -/
theorem solveFormula_some_iff_satisfiable (formula : Formula (Fin n)) (dualHorn : DualHorn formula) :
    (∃ values, solveFormula formula = some values) ↔ Satisfiable formula := by
  constructor
  · rintro ⟨values, returned⟩
    exact ⟨fun label => values[label.val], (solveFormula_some_model formula dualHorn values returned).1⟩
  · intro satisfiable
    cases result : solveFormula formula with
    | none => exact False.elim ((solveFormula_none_iff formula dualHorn).mp result satisfiable)
    | some values => exact ⟨values, rfl⟩

end Controller.Horn.Worklist
