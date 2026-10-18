module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Resolution.RUP

@[expose] public section

/-! Premise-only replay of reverse Horn reasons. Synthetic assumption reasons
are discharged into the requested clause before ordinary resolution is emitted.
The conflict row and every retained reason must already be in the checked prefix. -/
namespace Controller.NativeProof.HornReplay
open Controller.CNF Controller.Resolution Controller.Resolution.RUP

/-- Retain only reasons admitted by the premise-row classifier. -/
def premiseReasons (keep : RowReason v → Bool) : List (RowReason v) → List (RowReason v)
  | [] => []
  | reason :: earlier =>
      if keep reason then reason :: premiseReasons keep earlier else premiseReasons keep earlier

theorem premiseReasons_member (keep : RowReason v → Bool) (reasons : List (RowReason v))
    (reason : RowReason v) (member : reason ∈ premiseReasons keep reasons) :
    reason ∈ reasons ∧ keep reason = true := by
  induction reasons with
  | nil => simp [premiseReasons] at member
  | cons first earlier ih =>
    by_cases retained : keep first = true
    · simp only [premiseReasons, retained, ↓reduceIte, List.mem_cons] at member
      rcases member with same | tail
      · subst reason; exact ⟨List.mem_cons_self, retained⟩
      · exact ⟨List.mem_cons_of_mem _ (ih tail).1, (ih tail).2⟩
    · simp only [premiseReasons, retained, ↓reduceIte] at member
      exact ⟨List.mem_cons_of_mem _ (ih member).1, (ih member).2⟩

/-- A removed assumption contributes only a literal already in the target. -/
theorem discharged_negations (keep : RowReason v → Bool) (reasons : List (RowReason v))
    (target : Clause (Fin v))
    (discharged : ∀ reason ∈ reasons, keep reason ≠ true → negate reason.entry.pivot ∈ target) :
    ClauseSubset (negations (reasons.map RowReason.entry))
      (negations ((premiseReasons keep reasons).map RowReason.entry) ++ target) := by
  induction reasons with
  | nil => simp [ClauseSubset, negations]
  | cons reason earlier ih =>
    have tail := ih (fun r hr => discharged r (List.mem_cons_of_mem _ hr))
    intro literal member
    simp only [List.map_cons, negations, List.mem_cons] at member
    by_cases retained : keep reason = true
    · simp only [premiseReasons, retained, ↓reduceIte, List.map_cons, negations,
        List.cons_append, List.mem_cons]
      rcases member with same | old
      · exact Or.inl same
      · exact Or.inr (tail literal old)
    · simp only [premiseReasons, retained, ↓reduceIte]
      rcases member with same | old
      · subst literal
        exact List.mem_append.mpr (Or.inr (discharged reason List.mem_cons_self retained))
      · exact tail literal old

/-- Reverse causality survives removing synthetic unit assumptions. -/
theorem premiseReasons_valid (keep : RowReason v → Bool) (reasons : List (RowReason v))
    (target : Clause (Fin v))
    (discharged : ∀ reason ∈ reasons, keep reason ≠ true → negate reason.entry.pivot ∈ target)
    (valid : ValidReasons [] (reasons.map RowReason.entry)) :
    ValidReasons target ((premiseReasons keep reasons).map RowReason.entry) := by
  induction reasons with
  | nil => trivial
  | cons reason earlier ih =>
    have tailDischarged : ∀ r ∈ earlier, keep r ≠ true → negate r.entry.pivot ∈ target :=
      fun r hr => discharged r (List.mem_cons_of_mem _ hr)
    have original : ReasonEarlier reason.entry.pivot reason.entry.clause
        (negations (earlier.map RowReason.entry) ++ []) ∧
        ValidReasons [] (earlier.map RowReason.entry) := valid
    by_cases retained : keep reason = true
    · simp only [premiseReasons, retained, ↓reduceIte, List.map_cons, ValidReasons]
      refine ⟨⟨original.1.1, ?_⟩, ih tailDischarged original.2⟩
      intro literal member different
      apply discharged_negations keep earlier target tailDischarged literal
      simpa using original.1.2 literal member different
    · simp only [premiseReasons, retained, ↓reduceIte]
      exact ih tailDischarged original.2

/-- The emitted trace has at most one inference per original propagation reason. -/
theorem premiseReasons_count (keep : RowReason v → Bool) (reasons : List (RowReason v))
    (state : State v) (rowId : Nat) (current : Clause (Fin v)) :
    (compileReasons state rowId current (premiseReasons keep reasons)).steps.length ≤ reasons.length := by
  apply Nat.le_trans (compileReasons_count_le _ _ _ _)
  induction reasons with
  | nil => simp [premiseReasons]
  | cons reason earlier ih =>
    by_cases retained : keep reason = true
    · simpa [premiseReasons, retained] using Nat.succ_le_succ ih
    · simpa [premiseReasons, retained] using Nat.le_trans ih (Nat.le_succ earlier.length)

/-- A premise conflict and a full reverse certificate produce a checked target
subclause without using any discarded synthetic row as a resolution parent. -/
def dischargeAssumptions (formula : FiniteFormula v) (state : State v)
    (prefixSteps : List (Step v))
    (prefixRun : runSteps (initialState formula) prefixSteps = some state)
    (rowId : Nat) (current target : Clause (Fin v)) (reasons : List (RowReason v))
    (keep : RowReason v → Bool)
    (known : KnownReasons state (premiseReasons keep reasons))
    (currentRow : state.rows rowId = some current) (currentBound : rowId ≤ state.lastId)
    (valid : ValidReasons [] (reasons.map RowReason.entry))
    (conflict : ClauseSubset current (negations (reasons.map RowReason.entry)))
    (discharged : ∀ reason ∈ reasons, keep reason ≠ true → negate reason.entry.pivot ∈ target) :
    DerivedSubclause formula (compileReasons state rowId current (premiseReasons keep reasons)).state target :=
  compileReasons_derived formula state prefixSteps prefixRun rowId current target
    (premiseReasons keep reasons) known currentRow currentBound
    (premiseReasons_valid keep reasons target discharged valid)
    (fun literal member => discharged_negations keep reasons target discharged literal (conflict literal member))

end Controller.NativeProof.HornReplay
