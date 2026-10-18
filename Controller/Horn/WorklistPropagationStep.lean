module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Horn.WorklistPropagation

@[expose] public section

/-! Original predecessor pointers strictly descend, and a fresh physical row
visit removes exactly one distinct positive label from its remaining count. -/
namespace Controller.Horn.WorklistPropagationStep
open Controller.Horn.Worklist Controller.Horn.WorklistPropagation
variable {width n : Nat}

/-- Every visited original node is at or below the starting physical pointer. -/
theorem prefix_address_le (edges : List (Nat × Fin n)) (recordEnd : Nat)
    (positive : 0 < recordEnd) (active : Fin n) (start finish : Nat)
    (indices : List (Fin edges.length))
    (path : LinkPrefix edges recordEnd active start indices finish) :
    ∀ index ∈ indices, recordEnd + 2 * index.val ≤ start := by
  induction path with
  | nil => simp
  | cons index rest finish label tail ih =>
      intro query member
      rcases List.mem_cons.mp member with equal | member
      · subst query; omega
      · have bound := ih query member
        have previous := IndexScan.heads_bound recordEnd positive (edges.take index.val) active
        rw [List.length_take_of_le (by have := index.isLt; omega)] at previous
        omega

/-- The physical successor of a node can only visit smaller original indices. -/
theorem prefix_strict_tail (edges : List (Nat × Fin n)) (recordEnd : Nat)
    (positive : 0 < recordEnd) (active : Fin n) (index : Fin edges.length)
    (rest : List (Fin edges.length)) (finish : Nat)
    (path : LinkPrefix edges recordEnd active
      (IndexScan.heads recordEnd (edges.take index.val) active) rest finish) :
    ∀ query ∈ rest, query.val < index.val := by
  intro query member
  have bound := prefix_address_le edges recordEnd positive active _ finish rest path query member
  have previous := IndexScan.heads_bound recordEnd positive (edges.take index.val) active
  rw [List.length_take_of_le (by have := index.isLt; omega)] at previous
  omega

/-- A stored occurrence is visited at most once in one physical bucket traversal. -/
theorem prefix_nodup (edges : List (Nat × Fin n)) (recordEnd : Nat)
    (positive : 0 < recordEnd) (active : Fin n) (start finish : Nat)
    (indices : List (Fin edges.length))
    (path : LinkPrefix edges recordEnd active start indices finish) : indices.Nodup := by
  induction path with
  | nil => exact List.nodup_nil
  | cons index rest finish label tail ih =>
      refine List.nodup_cons.mpr ⟨?_, ih⟩
      intro member
      have impossible := prefix_strict_tail edges recordEnd positive active index rest finish tail index member
      omega

/-- Original normalized support has distinct labels, so one physical incident
visit decrements once, with no contribution from other pending queued labels. -/
theorem remaining_append (rule : Rule (Fin n)) (unique : rule.positives.Nodup)
    (processed : List (Fin n)) (active : Fin n)
    (incident : active ∈ rule.positives) (fresh : active ∉ processed) :
    remaining rule (processed ++ [active]) = remaining rule processed - 1 := by
  simp only [remaining, ← List.countP_eq_length_filter]
  calc
    rule.positives.countP (fun label => decide (label ∉ processed ++ [active])) =
        rule.positives.countP (forceFalse (fun label => decide (label ∉ processed)) active) := by
      apply List.countP_congr
      intro label _
      by_cases equal : label = active <;> simp [forceFalse, equal]
    _ = _ := by
      rw [countP_forceFalse rule.positives unique (fun label => decide (label ∉ processed)) active]
      simp [incident, fresh]

theorem fresh_visit_count (rule : Rule (Fin n)) (unique : rule.positives.Nodup)
    (queue : List (Fin n)) (head : Nat) (active : Fin n) (visitedRows : List Nat) (row : Nat)
    (unvisited : row ∉ visitedRows) (incident : active ∈ rule.positives)
    (fresh : active ∉ queue.take head) :
    remaining rule (processedForRow queue head (some active) (row :: visitedRows) row) =
      remaining rule (processedForRow queue head (some active) visitedRows row) - 1 := by
  simpa [processedForRow, unvisited] using remaining_append rule unique (queue.take head) active incident fresh

/-- A fresh unvisited incidence cannot have a zero predecessor count. -/
theorem fresh_visit_positive (rule : Rule (Fin n))
    (queue : List (Fin n)) (head : Nat) (active : Fin n) (visitedRows : List Nat) (row : Nat)
    (unvisited : row ∉ visitedRows) (incident : active ∈ rule.positives)
    (fresh : active ∉ queue.take head) :
    0 < remaining rule (processedForRow queue head (some active) visitedRows row) := by
  by_contra nonpositive
  have zero : remaining rule (processedForRow queue head (some active) visitedRows row) = 0 := by omega
  have processed := remaining_zero rule _ zero active incident
  simp only [processedForRow, ite_eq_right unvisited, List.append_nil] at processed
  exact fresh processed

/-- Fired rows explicitly retain zero counts as more physical labels are processed. -/
def FiredZero (clauses : List (Controller.CNF.Clause (Fin n))) (recordStart : Nat)
    (queue : List (Fin n)) (head : Nat) (active : Option (Fin n)) (visitedRows : List Nat)
    (fired : Fin clauses.length → Bool) : Prop :=
  ∀ index : Fin clauses.length, fired index = true →
    remaining (compileClause clauses[index.val])
      (processedForRow queue head active visitedRows
        (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val)) = 0

/-- An unvisited original incidence is never already fired: its active positive
label still contributes one to the physical predecessor count. -/
theorem fresh_row_not_fired (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart : Nat) (queue : List (Fin n)) (head : Nat) (active : Fin n)
    (visitedRows : List Nat) (fired : Fin clauses.length → Bool)
    (zero : FiredZero clauses recordStart queue head (some active) visitedRows fired)
    (index : Fin clauses.length)
    (unvisited : Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val ∉ visitedRows)
    (incident : active ∈ (compileClause clauses[index.val]).positives)
    (fresh : active ∉ queue.take head) : fired index = false := by
  have positive := fresh_visit_positive (compileClause clauses[index.val]) queue head active visitedRows
    (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val) unvisited incident fresh
  cases value : fired index with
  | false => rfl
  | true => have empty := zero index value; omega

theorem remaining_zero_of_support (rule : Rule (Fin n)) (processed : List (Fin n))
    (support : ∀ label ∈ rule.positives, label ∈ processed) : remaining rule processed = 0 := by
  simp only [remaining, List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro label member
  simp [support label member]

/-- Processing further labels preserves the zero count of an already fired row. -/
theorem zero_monotone (rule : Rule (Fin n)) (before after : List (Fin n))
    (included : ∀ label ∈ before, label ∈ after) (zero : remaining rule before = 0) :
    remaining rule after = 0 := by
  apply remaining_zero_of_support
  intro label member
  exact included label (remaining_zero rule before zero label member)

end Controller.Horn.WorklistPropagationStep
