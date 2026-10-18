module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Reductions.DualHornDecoder
public import Mathlib.Data.List.Dedup
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

/-! # Literal-incidence accounting for the stored dual-Horn decoder -/
open scoped BigOperators
namespace Controller.Reductions.DualHorn
open Controller.CNF Controller.Decoder Controller.Horn.Worklist

/-- Raw literal incidences retain duplicates and the entire declared row table. -/
def sourceLiteralIncidences (formula : FiniteFormula n) : ℕ :=
  (List.ofFn fun row : Fin formula.clauses.size => formula.clauses[row].length).sum

/-- Normalization cannot add positive occurrences. -/
theorem signedLabels_length_le (clause : Clause (Fin n)) (polarity : Bool) :
    (signedLabels clause polarity).length ≤ clause.length := by
  unfold signedLabels
  exact (List.dedup_sublist _).length_le.trans (by simp only [List.length_map]; exact List.length_filter_le _ _)

theorem compileClause_positive_length_le (clause : Clause (Fin n)) :
    (compileClause clause).positives.length ≤ clause.length := by
  unfold compileClause
  split
  · simp [Rule.positives]
  · cases signedLabels clause false <;>
      exact signedLabels_length_le clause true

@[simp] theorem channelRule_positive_length (rule : Rule (Fin n)) :
    (channelRule rule).positives.length = rule.positives.length := by
  cases rule <;> simp [channelRule, Rule.positives]

/-- Each normalized row has at most its raw literal-incidence budget. -/
theorem storedRule_next_positive_length_le (formula : FiniteFormula n)
    (row : Fin formula.clauses.size) :
    (storedRule formula row.succ).positives.length ≤ formula.clauses[row].length := by
  rw [storedRule_next, channelRule_positive_length]
  exact compileClause_positive_length_le _

/-- Every row/helper violation node has at most one live input reference. -/
theorem decoder_term_children_le (formula : FiniteFormula n)
    (term : Fin (formula.clauses.size + 1)) :
    ((decoder formula).node ⟨n + 2 + term.val, by change n + 2 + term.val < n + formula.clauses.size + 4; omega⟩).children.length ≤ 1 := by
  have notInput : ¬n + 2 + term.val < n + 2 := by omega
  have isTerm : n + 2 + term.val < n + formula.clauses.size + 3 := by omega
  simp only [decoder, notInput, dite_false, isTerm, dite_true]
  unfold violationGate
  split <;> simp [Gate.children]

/-- The guard incidences at a term are exactly its normalized positive alternatives. -/
theorem decoder_term_guard_length (formula : FiniteFormula n)
    (term : Fin (formula.clauses.size + 1)) :
    ((decoder formula).node ⟨n + 2 + term.val, by change n + 2 + term.val < n + formula.clauses.size + 4; omega⟩).guardLabels.length =
      (storedRule formula term).positives.length := by
  have notInput : ¬n + 2 + term.val < n + 2 := by omega
  have isTerm : n + 2 + term.val < n + formula.clauses.size + 3 := by omega
  simp only [decoder, notInput, dite_false, isTerm, dite_true]
  have same : (⟨n + 2 + term.val - (n + 2), by omega⟩ : Fin (formula.clauses.size + 1)) = term := by
    apply Fin.ext; simp
  rw [same]
  cases storedRule formula term <;> rfl

/-- Helper plus all source rows retain a linear raw-literal guard budget. -/
theorem storedRule_guard_sum_le (formula : FiniteFormula n) :
    (∑ term : Fin (formula.clauses.size + 1), (storedRule formula term).positives.length) ≤
      sourceLiteralIncidences formula + 1 := by
  rw [Fin.sum_univ_succ]
  have first : (storedRule formula (0 : Fin (formula.clauses.size + 1))).positives.length = 1 := by
    rw [storedRule_first]
    rfl
  rw [first]
  have rows : (∑ row : Fin formula.clauses.size,
      (storedRule formula row.succ).positives.length) ≤ sourceLiteralIncidences formula := by
    unfold sourceLiteralIncidences
    rw [Fin.sum_ofFn]
    apply Finset.sum_le_sum
    intro row _
    exact storedRule_next_positive_length_le formula row
  omega

/-- Split the actual table into declared inputs, source/helper terms and its output. -/
private theorem decoder_sum_blocks (formula : FiniteFormula n)
    (cost : Fin (n + formula.clauses.size + 4) → ℕ) :
    (∑ index, cost index) =
      (∑ input : Fin (n + 2), cost ⟨input.val, by omega⟩) +
      (∑ term : Fin (formula.clauses.size + 1), cost ⟨n + 2 + term.val, by omega⟩) +
      cost ⟨n + formula.clauses.size + 3, by omega⟩ := by
  let shifted : Fin ((n + 2) + ((formula.clauses.size + 1) + 1)) → ℕ :=
    fun i => cost ⟨i.val, by omega⟩
  have reindex : (∑ index, cost index) = ∑ index, shifted index := by
    apply Finset.sum_bij (fun index _ => (⟨index.val, by omega⟩ :
      Fin ((n + 2) + ((formula.clauses.size + 1) + 1))))
    · simp
    · intro a _ b _ same
      apply Fin.ext
      exact congrArg (fun i : Fin ((n + 2) + ((formula.clauses.size + 1) + 1)) => i.val) same
    · intro index _
      exact ⟨⟨index.val, by omega⟩, by simp, rfl⟩
    · intro index _
      rfl
  rw [reindex, Fin.sum_univ_add]
  rw [Fin.sum_univ_castSucc (fun i : Fin ((formula.clauses.size + 1) + 1) => shifted (i.natAdd (n + 2)))]
  simp only [shifted, Fin.val_castAdd, Fin.val_natAdd, Fin.val_castSucc,
    Fin.val_last]
  simp only [Nat.add_assoc]
  have lastEq : (⟨n + (2 + (formula.clauses.size + 1)), by omega⟩ : Fin (n + formula.clauses.size + 4)) =
      ⟨n + (formula.clauses.size + 3), by omega⟩ := by
    apply Fin.ext
    change n + (2 + (formula.clauses.size + 1)) = n + (formula.clauses.size + 3)
    omega
  exact congrArg (fun result =>
    (∑ input : Fin (n + 2), cost ⟨input.val, by omega⟩) +
      ((∑ term : Fin (formula.clauses.size + 1), cost ⟨n + (2 + term.val), by omega⟩) + result))
    (congrArg cost lastEq)

/-- All live references are the term-to-input edges and the final term list. -/
theorem decoder_children_le (formula : FiniteFormula n) :
    (decoder formula).childIncidences ≤ 2 * (formula.clauses.size + 1) := by
  unfold DAG.childIncidences
  rw [Fin.sum_ofFn]
  change (∑ index : Fin (n + formula.clauses.size + 4),
    ((decoder formula).node index).children.length) ≤ _
  rw [decoder_sum_blocks]
  change (∑ input : Fin (n + 2),
      ((decoder formula).node ⟨input.val, by change input.val < n + formula.clauses.size + 4; omega⟩).children.length) +
    (∑ term : Fin (formula.clauses.size + 1),
      ((decoder formula).node ⟨n + 2 + term.val, by change n + 2 + term.val < n + formula.clauses.size + 4; omega⟩).children.length) +
    ((decoder formula).node ⟨n + formula.clauses.size + 3, by change n + formula.clauses.size + 3 < n + formula.clauses.size + 4; omega⟩).children.length ≤ 2 * (formula.clauses.size + 1)
  have inputs : (∑ input : Fin (n + 2),
      ((decoder formula).node ⟨input.val, by change input.val < n + formula.clauses.size + 4; omega⟩).children.length) = 0 := by
    apply Finset.sum_eq_zero
    intro input _
    simp [decoder, input.isLt, Gate.children]
  have terms : (∑ term : Fin (formula.clauses.size + 1),
      ((decoder formula).node ⟨n + 2 + term.val, by change n + 2 + term.val < n + formula.clauses.size + 4; omega⟩).children.length) ≤ formula.clauses.size + 1 := by
    calc
      _ ≤ ∑ _term : Fin (formula.clauses.size + 1), 1 := by
        apply Finset.sum_le_sum
        intro term _
        exact decoder_term_children_le formula term
      _ = _ := by simp
  have last : ((decoder formula).node
      ⟨n + formula.clauses.size + 3, by change n + formula.clauses.size + 3 < n + formula.clauses.size + 4; omega⟩).children.length = formula.clauses.size + 1 := by
    have notInput : ¬n + formula.clauses.size + 3 < n + 2 := by omega
    simp [decoder, notInput, Gate.children]
  have inputZero : (∑ input : Fin (n + 2),
      ((decoder formula).node ⟨input.val, by change input.val < n + formula.clauses.size + 4; omega⟩).children.length) = 0 := inputs
  omega

/-- Channel guard incidences charge at most one helper plus the raw source literals. -/
theorem decoder_guards_le (formula : FiniteFormula n) :
    (decoder formula).guardIncidences ≤ sourceLiteralIncidences formula + 1 := by
  unfold DAG.guardIncidences
  rw [Fin.sum_ofFn]
  change (∑ index : Fin (n + formula.clauses.size + 4),
    ((decoder formula).node index).guardLabels.length) ≤ _
  rw [decoder_sum_blocks]
  change (∑ input : Fin (n + 2),
      ((decoder formula).node ⟨input.val, by change input.val < n + formula.clauses.size + 4; omega⟩).guardLabels.length) +
    (∑ term : Fin (formula.clauses.size + 1),
      ((decoder formula).node ⟨n + 2 + term.val, by change n + 2 + term.val < n + formula.clauses.size + 4; omega⟩).guardLabels.length) +
    ((decoder formula).node ⟨n + formula.clauses.size + 3, by change n + formula.clauses.size + 3 < n + formula.clauses.size + 4; omega⟩).guardLabels.length ≤ sourceLiteralIncidences formula + 1
  have inputs : (∑ input : Fin (n + 2),
      ((decoder formula).node ⟨input.val, by change input.val < n + formula.clauses.size + 4; omega⟩).guardLabels.length) = 0 := by
    apply Finset.sum_eq_zero
    intro input _
    simp [decoder, input.isLt, Gate.guardLabels]
  have last : ((decoder formula).node
      ⟨n + formula.clauses.size + 3, by change n + formula.clauses.size + 3 < n + formula.clauses.size + 4; omega⟩).guardLabels.length = 0 := by
    have notInput : ¬n + formula.clauses.size + 3 < n + 2 := by omega
    simp [decoder, notInput, Gate.guardLabels]
  have terms : (∑ term : Fin (formula.clauses.size + 1),
      ((decoder formula).node ⟨n + 2 + term.val, by change n + 2 + term.val < n + formula.clauses.size + 4; omega⟩).guardLabels.length) ≤ sourceLiteralIncidences formula + 1 := by
    simpa only [decoder_term_guard_length] using storedRule_guard_sum_le formula
  omega

/-- Linear storage counts declared unused variables, raw incidences and the empty source. -/
theorem decoder_countedSize_le (formula : FiniteFormula n) :
    (decoder formula).countedSize ≤
      2 * n + 3 * formula.clauses.size + sourceLiteralIncidences formula + 10 := by
  have children := decoder_children_le formula
  have guards := decoder_guards_le formula
  have roots : (decoder formula).roots.length = 1 := rfl
  rw [DAG.countedSize_eq]
  have nodes := decoder_node_count formula
  omega

theorem decoder_size_linear (formula : FiniteFormula n) :
    (decoder formula).countedSize ≤
      10 * (1 + n + formula.clauses.size + sourceLiteralIncidences formula) := by
  have bound := decoder_countedSize_le formula
  omega

end Controller.Reductions.DualHorn
