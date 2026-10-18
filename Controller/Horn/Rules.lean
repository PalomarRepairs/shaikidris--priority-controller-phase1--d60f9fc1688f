module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Horn.GreatestModel
public import Mathlib.Data.List.Dedup

@[expose] public section

/-!
# Normalized rules for dual-Horn propagation

Tautological rows become inert rules. Every other row records its distinct
positive variables and at most one negative head. Input row positions are
retained, including repeated rows and empty clauses.
-/

namespace Controller.Horn.Worklist

open CNF

/-- An inert row, a positive clause, or a rule with one negative head. -/
inductive Rule (α : Type*) where
  | skip
  | positive (positive : List α)
  | negative (head : α) (positive : List α)
  deriving DecidableEq, Repr

namespace Rule

/-- The distinct positive labels retained for counting. -/
def positives : Rule α → List α
  | .skip => []
  | .positive labels => labels
  | .negative _ labels => labels

/-- The variable forced false when all positive alternatives are false. -/
def head? : Rule α → Option α
  | .negative head _ => some head
  | _ => none

/-- An inert tautology requires no work when its positive count is zero. -/
def enabled : Rule α → Bool
  | .skip => false
  | _ => true

/-- Propositional semantics of a compiled propagation rule. -/
def Holds (assignment : α → Bool) : Rule α → Prop
  | .skip => True
  | .positive labels => ∃ label ∈ labels, assignment label = true
  | .negative head labels => assignment head = false ∨
      ∃ label ∈ labels, assignment label = true

end Rule

variable [DecidableEq α]

/-- Distinct variables of one polarity, retaining one list occurrence of each. -/
def signedLabels (clause : Clause α) (polarity : Bool) : List α :=
  ((clause.filter fun literal => decide (literal.2 = polarity)).map Prod.fst).dedup

/-- Normalization preserves literal membership of the selected polarity. -/
@[simp] theorem mem_signedLabels (clause : Clause α) (polarity : Bool) (label : α) :
    label ∈ signedLabels clause polarity ↔ (label, polarity) ∈ clause := by
  simp only [signedLabels, List.mem_dedup, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨source, sign⟩, ⟨membership, signEquation⟩, labelEquation⟩
    dsimp at signEquation labelEquation
    subst source
    subst sign
    exact membership
  · intro membership
    exact ⟨(label, polarity), ⟨membership, rfl⟩, rfl⟩

/-- Duplicate positive occurrences cannot inflate the propagation count. -/
theorem signedLabels_nodup (clause : Clause α) (polarity : Bool) :
    (signedLabels clause polarity).Nodup := by
  exact List.nodup_dedup _

/-- A finite executable test for a literal together with its negation. -/
def tautologyCheck (clause : Clause α) : Bool :=
  clause.any fun literal => clause.contains (negate literal)

@[simp] theorem tautologyCheck_eq_true (clause : Clause α) :
    tautologyCheck clause = true ↔ Tautological clause := by
  simp [tautologyCheck, Tautological]

/-- Normalize one row; correctness for non-tautologies uses the dual-Horn restriction. -/
def compileClause (clause : Clause α) : Rule α :=
  if tautologyCheck clause then .skip
  else match signedLabels clause false with
    | [] => .positive (signedLabels clause true)
    | head :: _ => .negative head (signedLabels clause true)

/-- Every compiled positive list contains each variable at most once. -/
theorem compileClause_positives_nodup (clause : Clause α) :
    (compileClause clause).positives.Nodup := by
  unfold compileClause
  split
  · exact List.nodup_nil
  · cases signedLabels clause false <;> exact signedLabels_nodup clause true

/-- Compilation preserves the exact clause meaning, including units and the empty clause. -/
theorem compileClause_holds_iff (clause : Clause α) (dualHorn : DualHornClause clause)
    (assignment : α → Bool) :
    (compileClause clause).Holds assignment ↔ ClauseHolds assignment clause := by
  by_cases tautology : tautologyCheck clause = true
  · have semanticTautology := (tautologyCheck_eq_true clause).mp tautology
    obtain ⟨literal, member, negativeMember⟩ := semanticTautology
    have satisfied := tautology_holds assignment member negativeMember
    simp only [compileClause, tautology, ite_true, Rule.Holds]
    exact ⟨fun _ => satisfied, fun _ => trivial⟩
  · have uniqueNegative : NegativeUnique clause :=
      dualHorn.resolve_left (fun semanticTautology =>
        tautology ((tautologyCheck_eq_true clause).mpr semanticTautology))
    cases negatives : signedLabels clause false with
    | nil =>
        have noNegative : ∀ label, (label, false) ∉ clause := by
          intro label membership
          have labelMember := (mem_signedLabels clause false label).mpr membership
          simp only [negatives, List.not_mem_nil] at labelMember
        simp only [compileClause, tautology, negatives, Rule.Holds]
        constructor
        · rintro ⟨label, member, trueValue⟩
          exact ⟨(label, true), (mem_signedLabels clause true label).mp member, trueValue⟩
        · rintro ⟨⟨label, sign⟩, member, literalValue⟩
          cases sign with
          | false => exact False.elim (noNegative label member)
          | true => exact ⟨label, (mem_signedLabels clause true label).mpr member, literalValue⟩
    | cons head rest =>
        have headMember : (head, false) ∈ clause := by
          apply (mem_signedLabels clause false head).mp
          simp [negatives]
        have everyNegative : ∀ label, (label, false) ∈ clause → label = head := by
          intro label member
          exact uniqueNegative (label, false) member (head, false) headMember rfl rfl
        simp only [compileClause, tautology, negatives, Rule.Holds]
        constructor
        · rintro (headFalse | ⟨label, member, trueValue⟩)
          · exact ⟨(head, false), headMember, headFalse⟩
          · exact ⟨(label, true), (mem_signedLabels clause true label).mp member, trueValue⟩
        · rintro ⟨⟨label, sign⟩, member, literalValue⟩
          cases sign with
          | false =>
              have labelEquation := everyNegative label member
              exact Or.inl (labelEquation ▸ literalValue)
          | true =>
              exact Or.inr ⟨label, (mem_signedLabels clause true label).mpr member, literalValue⟩

/-- Compile all rows without deleting or merging their identifiers. -/
def compileFormula (formula : Formula α) : Array (Rule α) :=
  formula.clauses.map compileClause

@[simp] theorem compileFormula_size (formula : Formula α) :
    (compileFormula formula).size = formula.clauses.size := by simp [compileFormula]

/-- The compiled row at each original identifier has exactly the original meaning. -/
theorem compileFormula_row_holds_iff (formula : Formula α) (dualHorn : DualHorn formula)
    (assignment : α → Bool) (index : Fin formula.clauses.size) :
    ((compileFormula formula)[index.val]'(by simp)).Holds assignment ↔
      ClauseHolds assignment formula.clauses[index.val] := by
  simp only [compileFormula, Array.getElem_map]
  exact compileClause_holds_iff _ (dualHorn _ (Array.getElem_mem ..)) assignment

/-- The complete normalized rule array has exactly the original models. -/
theorem compileFormula_holds_iff (formula : Formula α) (dualHorn : DualHorn formula)
    (assignment : α → Bool) :
    (∀ index : Fin formula.clauses.size,
      ((compileFormula formula)[index.val]'(by simp)).Holds assignment) ↔
      Satisfies assignment formula := by
  rw [satisfies_iff_rows]
  exact forall_congr' fun index => compileFormula_row_holds_iff formula dualHorn assignment index

omit [DecidableEq α] in
/-- Satisfaction already supplies the terminal propagation conditions of a dual-Horn formula. -/
theorem satisfies_rulesClosed {formula : Formula α} (dualHorn : DualHorn formula)
    {assignment : α → Bool} (satisfied : Satisfies assignment formula) :
    RulesClosed formula assignment := by
  intro clause member notTautology
  have uniqueNegative := (dualHorn clause member).resolve_left notTautology
  constructor
  · intro allPositive
    obtain ⟨literal, literalMember, value⟩ := satisfied clause member
    exact ⟨literal, literalMember, value.trans (allPositive literal literalMember)⟩
  · intro label negativeMember allFalse
    exact downward_forcing_safe member uniqueNegative negativeMember allFalse
      satisfied (below_refl assignment)

end Controller.Horn.Worklist
