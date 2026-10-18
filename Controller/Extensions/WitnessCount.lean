module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

/-! Finite shared-witness counting. Each nonroot vertex needs one incoming
selected edge. Counting distinct outgoing targets is sufficient even when
children repeat; no tree unfolding or disjoint-branch premise is used. -/
namespace Controller.Extensions.WitnessCount
open scoped BigOperators
variable [DecidableEq α]

theorem leaf_bound (vertices leaves binary : Finset α) (root : α)
    (children : α → Finset α) (rootMem : root ∈ vertices)
    (leafSubset : leaves ⊆ vertices)
    (parent : ∀ v ∈ vertices, v ≠ root → ∃ p ∈ vertices, v ∈ children p)
    (degree : ∀ v ∈ vertices, (children v).card ≤
      (if v ∈ leaves then 0 else 1) + (if v ∈ binary then 1 else 0)) :
    leaves.card ≤ (vertices ∩ binary).card + 1 := by
  have cover : vertices.erase root ⊆ vertices.biUnion children := by
    intro v member
    obtain ⟨different, inside⟩ := Finset.mem_erase.mp member
    obtain ⟨p, stored, edge⟩ := parent v inside different
    exact Finset.mem_biUnion.mpr ⟨p, stored, edge⟩
  have edges : (vertices.erase root).card ≤ ∑ v ∈ vertices, (children v).card :=
    (Finset.card_le_card cover).trans Finset.card_biUnion_le
  have unary : (∑ v ∈ vertices, if v ∈ leaves then 0 else 1 : Nat) =
      (vertices \ leaves).card := by
    calc
      _ = ∑ v ∈ vertices, if v ∉ leaves then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro v _
        by_cases h : v ∈ leaves <;> simp [h]
      _ = (vertices.filter (fun v => v ∉ leaves)).card := Finset.sum_boole _ _
      _ = _ := by congr 1; ext v; simp
  have branching : (∑ v ∈ vertices, if v ∈ binary then 1 else 0 : Nat) =
      (vertices ∩ binary).card := by
    rw [Finset.sum_boole]
    congr 1
  have capacity := Finset.sum_le_sum degree
  rw [Finset.sum_add_distrib, unary, branching] at capacity
  have vertexCount := Finset.card_erase_of_mem rootMem
  have partition := Finset.card_sdiff_add_card_eq_card leafSubset
  omega

theorem leaf_bound_all (vertices leaves binary : Finset α) (root : α)
    (children : α → Finset α) (rootMem : root ∈ vertices)
    (leafSubset : leaves ⊆ vertices)
    (parent : ∀ v ∈ vertices, v ≠ root → ∃ p ∈ vertices, v ∈ children p)
    (degree : ∀ v ∈ vertices, (children v).card ≤
      (if v ∈ leaves then 0 else 1) + (if v ∈ binary then 1 else 0)) :
    leaves.card ≤ binary.card + 1 := by
  have within := leaf_bound vertices leaves binary root children rootMem leafSubset parent degree
  have smaller := Finset.card_le_card (Finset.inter_subset_right : vertices ∩ binary ⊆ binary)
  omega

end Controller.Extensions.WitnessCount
