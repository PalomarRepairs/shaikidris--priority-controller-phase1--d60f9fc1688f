module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Horn.Rules
public import Controller.Basic.Admissible

@[expose] public section

/-!
# Dual-Horn violation terms

Normalized rows retain the original clause identifiers, including inert
 tautologies and empty positive clauses. The Boolean term representation is
 the semantic layer of the one-bus decoder transfer. Stored topological
 decoder construction and its size bound are separate declarations.
-/
namespace Controller.Reductions.DualHorn

open Controller.CNF Controller.Horn Controller.Horn.Worklist

/-- Violation of one normalized row, with the positive-clause head supplied
by the forced target channel. -/
def violation (target : Bool) (values : α → Bool) : Rule α → Bool
  | .skip => false
  | .positive labels => target && !(labels.any values)
  | .negative head labels => values head && !(labels.any values)

/-- The exact row complement under the target cofactor. -/
theorem violation_false_iff (rule : Rule α) (values : α → Bool) :
    violation true values rule = false ↔ rule.Holds values := by
  cases rule with
  | skip => simp [violation, Rule.Holds]
  | positive labels => simp [violation, Rule.Holds, List.any_eq_true]
  | negative head labels =>
    cases h : values head <;> simp [violation, Rule.Holds, h, List.any_eq_true]

/-- The helper term forces the helper channel into every zero witness. -/
def outputValue [DecidableEq α] (formula : Formula α) (target helper : Bool)
    (values : α → Bool) : Bool :=
  (target && !helper) ||
    ((compileFormula formula).toList.any (violation target values))

/-- Every zero at the forced target is exactly a helper-true source model. -/
theorem output_zero_iff [DecidableEq α] (formula : Formula α)
    (dualHorn : DualHorn formula) (helper : Bool) (values : α → Bool) :
    outputValue formula true helper values = false ↔
      helper = true ∧ Satisfies values formula := by
  have helperEq : (!helper) = false ↔ helper = true := by cases helper <;> decide
  have falseEq : ∀ value : Bool, (¬value = true) ↔ value = false := by
    intro value; cases value <;> decide
  simp only [outputValue, Bool.true_and, Bool.or_eq_false_iff, helperEq,
    List.any_eq_false, falseEq, compileFormula, Array.toList_map, List.mem_map]
  constructor
  · rintro ⟨helperTrue, rows⟩
    refine ⟨helperTrue, ?_⟩
    intro clause membership
    have compiled := rows (compileClause clause) ⟨clause, by simpa using membership, rfl⟩
    exact (compileClause_holds_iff clause (dualHorn clause membership) values).mp
      ((violation_false_iff _ values).mp compiled)
  · rintro ⟨helperTrue, model⟩
    refine ⟨helperTrue, ?_⟩
    rintro rule ⟨clause, membership, rfl⟩
    have member : clause ∈ formula.clauses := by simpa using membership
    exact (violation_false_iff _ values).mpr
      ((compileClause_holds_iff clause (dualHorn clause member) values).mpr (model clause member))

/-- A healthy target-only assignment always makes the helper term true,
independently of all source clauses. -/
theorem output_healthy [DecidableEq α] (formula : Formula α) :
    outputValue formula true false (fun _ => false) = true := by
  simp [outputValue]

/-- Inert tautologies contribute no violation term. -/
@[simp] theorem violation_skip (target : Bool) (values : α → Bool) :
    violation target values .skip = false := rfl

/-- The empty positive row is the target itself, ruling out detecting zeros. -/
@[simp] theorem violation_empty (target : Bool) (values : α → Bool) :
    violation target values (.positive []) = target := by simp [violation]

end Controller.Reductions.DualHorn
