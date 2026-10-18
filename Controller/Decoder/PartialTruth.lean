module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Decoder.Paths

@[expose] public section

/-!
# True extensions of partial channel assignments

Both fixed-true and fixed-false channels are retained in the contract. A true
extension of a guarded node can be replaced by the fixed-true set together
with at most one unfixed positive head. Any forced controller target is part
of the caller's fixed-true set.
-/

namespace Controller.Decoder.DAG

variable {n : ℕ}

/-- A true decoder value requires at least one true channel. -/
theorem nonempty_of_eval_true (graph : DAG n) (K : Finset (Channel n))
    (index : Fin graph.nodeCount) (trueValue : graph.eval (assignmentOfSet K) index = true) :
    K.Nonempty := by
  apply Finset.nonempty_iff_ne_empty.mpr
  intro emptySet
  subst K
  exact Bool.false_ne_true ((graph.eval_empty index).symm.trans trueValue)

/-- The finite candidate family for a true partial extension is complete. -/
theorem exists_true_extension_iff (graph : DAG n) (guarded : graph.Guarded)
    (index : Fin graph.nodeCount) (T F : Finset (Channel n)) :
    (∃ K, ExtendsFixed T F K ∧ graph.eval (assignmentOfSet K) index = true) ↔
      FixedConsistent T F ∧
        (graph.eval (assignmentOfSet T) index = true ∨
          ∃ head, head ∉ T ∧ head ∉ F ∧ graph.IsPositiveHead index head ∧
            graph.eval (assignmentOfSet (insert head T)) index = true) := by
  constructor
  · rintro ⟨K, extension, trueValue⟩
    refine ⟨extendsFixed_consistent extension, ?_⟩
    obtain ⟨head, headTrue, positiveHead, preserves⟩ :=
      graph.exists_head_preserving_subsets guarded K index trueValue
    by_cases fixedTrue : head ∈ T
    · exact Or.inl (preserves T fixedTrue extension.1)
    · refine Or.inr ⟨head, fixedTrue, ?_, positiveHead, ?_⟩
      · intro fixedFalse
        exact Finset.disjoint_left.mp extension.2 headTrue fixedFalse
      · exact preserves (insert head T) (Finset.mem_insert_self head T)
          (Finset.insert_subset_iff.mpr ⟨headTrue, extension.1⟩)
  · rintro ⟨consistent, trueFixed | ⟨head, _, headFree, _, trueWithHead⟩⟩
    · exact ⟨T, extendsFixed_self consistent, trueFixed⟩
    · exact ⟨insert head T,
        ⟨Finset.subset_insert head T, Finset.disjoint_insert_left.mpr ⟨headFree, consistent⟩⟩,
        trueWithHead⟩

/-- A successful partial extension can keep all fixed true channels and at most one new head. -/
theorem exists_small_true_extension (graph : DAG n) (guarded : graph.Guarded)
    (index : Fin graph.nodeCount) (T F : Finset (Channel n))
    (extension : ∃ K, ExtendsFixed T F K ∧ graph.eval (assignmentOfSet K) index = true) :
    ∃ K, ExtendsFixed T F K ∧ graph.eval (assignmentOfSet K) index = true ∧
      (K = T ∨ ∃ head, head ∉ T ∧ head ∉ F ∧ graph.IsPositiveHead index head ∧
        K = insert head T) := by
  obtain ⟨consistent, trueFixed | ⟨head, notTrue, notFalse, positiveHead, trueWithHead⟩⟩ :=
    (graph.exists_true_extension_iff guarded index T F).mp extension
  · exact ⟨T, extendsFixed_self consistent, trueFixed, Or.inl rfl⟩
  · exact ⟨insert head T,
      ⟨Finset.subset_insert head T, Finset.disjoint_insert_left.mpr ⟨notFalse, consistent⟩⟩,
      trueWithHead, Or.inr ⟨head, notTrue, notFalse, positiveHead, rfl⟩⟩

end Controller.Decoder.DAG
