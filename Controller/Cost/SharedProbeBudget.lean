module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedBaselineProbe
public import Controller.Cost.SharedHeadLoop

@[expose] public section

/-! Healthy, nonempty-baseline and allowed-head probes obey the shared evaluation budget. -/
namespace Controller.Cost.SharedProbeBudget

def allowed (T F : Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun channel => channel ∉ T ∧ channel ∉ F)

def evaluations (T F : Finset (Fin n)) : Nat :=
  1 + (if T.Nonempty then 1 else 0) + (allowed T F).card

theorem allowed_bound (T F : Finset (Fin n)) : (allowed T F).card ≤ n - T.card := by
  have included : allowed T F ⊆ Finset.univ \ T := by
    intro channel member
    simp only [allowed, Finset.mem_filter, Finset.mem_univ, true_and] at member
    simp [member.1]
  have bound := Finset.card_le_card included
  simpa [Finset.card_sdiff] using bound

theorem evaluations_bound (T F : Finset (Fin n)) : evaluations T F ≤ n + 1 := by
  have bound := allowed_bound T F
  have channelCount : T.card ≤ n := by
    have count := Finset.card_le_card (Finset.subset_univ T)
    simpa using count
  unfold evaluations
  split
  · have positive := Finset.card_pos.mpr ‹T.Nonempty›
    omega
  · omega

theorem baseline_guard (T : Finset (Fin n)) :
    (List.finRange n).any (assignmentOfSet T) = decide T.Nonempty :=
  SharedBaselineNonempty.any_set T

theorem candidate_guard (T F : Finset (Fin n)) (channel : Fin n) :
    (assignmentOfSet T channel || assignmentOfSet F channel) = false ↔ channel ∈ allowed T F := by
  rw [SharedCandidateFilter.allowed_iff]
  simp [allowed]

end Controller.Cost.SharedProbeBudget
