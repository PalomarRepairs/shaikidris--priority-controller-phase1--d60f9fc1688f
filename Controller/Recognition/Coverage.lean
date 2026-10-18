module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.CNF.Basic
public import Mathlib.Data.List.FinRange

@[expose] public section

/-! Exact ordered source-clause coverage. Blocks refer to original row IDs;
duplicate clauses therefore retain distinct obligations. Overlapping blocks
are permitted and do not weaken the coverage test. -/

namespace Controller.Recognition.Coverage
open Controller.CNF

abbrev Origins (source : Formula α) := List (Fin source.clauses.size)

def block (source : Formula α) (origins : Origins source) : Formula α :=
  ofClauses (origins.map fun i => source.clauses[i])

def Complete (source : Formula α) (blocks : List (Origins source)) : Prop :=
  ∀ i : Fin source.clauses.size, ∃ origins ∈ blocks, i ∈ origins

instance (source : Formula α) (blocks : List (Origins source)) :
    Decidable (Complete source blocks) := by
  unfold Complete
  infer_instance

def check (source : Formula α) (blocks : List (Origins source)) : Bool :=
  decide (Complete source blocks)

@[simp] theorem check_iff (source : Formula α) (blocks : List (Origins source)) :
    check source blocks = true ↔ Complete source blocks := by
  simp [check]

theorem block_iff (source : Formula α) (origins : Origins source) (a : α → Bool) :
    Satisfies a (block source origins) ↔
      ∀ i ∈ origins, ClauseHolds a source.clauses[i] := by
  simp [block, satisfies_ofClauses]

theorem source_implies_block (source : Formula α) (origins : Origins source)
    (a : α → Bool) (model : Satisfies a source) : Satisfies a (block source origins) := by
  rw [block_iff]
  intro i _
  exact (satisfies_iff_rows a source).mp model i

theorem covered_models_iff (source : Formula α) (blocks : List (Origins source))
    (covered : Complete source blocks) (a : α → Bool) :
    Satisfies a source ↔ ∀ origins ∈ blocks, Satisfies a (block source origins) := by
  constructor
  · intro model origins _
    exact source_implies_block source origins a model
  · intro models
    rw [satisfies_iff_rows]
    intro i
    obtain ⟨origins, member, occurrence⟩ := covered i
    exact (block_iff source origins a).mp (models origins member) i occurrence

theorem rejected_missing_id (source : Formula α) (blocks : List (Origins source))
    (i : Fin source.clauses.size) (missing : ∀ origins ∈ blocks, i ∉ origins) :
    check source blocks = false := by
  apply Bool.eq_false_iff.mpr
  intro accepted
  obtain ⟨origins, membership, occurrence⟩ := (check_iff source blocks).mp accepted i
  exact missing origins membership occurrence

end Controller.Recognition.Coverage
