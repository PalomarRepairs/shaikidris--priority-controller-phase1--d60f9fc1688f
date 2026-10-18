module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.CNF.Basic

@[expose] public section

/-! Exact typed-CNF model checking. Evaluation visits the original ordered rows;
no recognition or family-membership hypothesis is used. -/
namespace Controller.Certificate.ModelCheck
open Controller

def check (formula : CNF.Formula α) (assignment : α → Bool) : Bool :=
  Controller.CNF.OrderedFormula.eval assignment formula

theorem check_iff (formula : CNF.Formula α) (assignment : α → Bool) :
    check formula assignment = true ↔ CNF.Satisfies assignment formula := by
  exact (CNF.satisfies_iff_stdSat assignment formula).symm

theorem accepted_satisfiable (formula : CNF.Formula α) (assignment : α → Bool)
    (accepted : check formula assignment = true) : CNF.Satisfiable formula :=
  ⟨assignment, (check_iff formula assignment).mp accepted⟩

theorem accepted_original_row (formula : CNF.Formula α) (assignment : α → Bool)
    (accepted : check formula assignment = true) (row : CNF.Clause α)
    (original : row ∈ formula.clauses) : CNF.ClauseHolds assignment row :=
  (check_iff formula assignment).mp accepted row original

end Controller.Certificate.ModelCheck
