module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.WrapperCanonical

@[expose] public section

/-! Selected inputs retain the optional clauses in order and append the activity disjunction. -/
namespace Controller.NativeProof.Wrapper
open Controller.CNF Controller.Resolution Controller.Native Controller.Native.SourceController
open Controller.Native.ObservationProjection Controller.NativeProof.FoldProjection
open Controller.NativeProof.SourceStageCongruence Controller.NativeProof.SourceBusSchedule
variable {internalCount v : Nat}

def selectedInputRows (parameters : Parameters)
    (wrapper : OptionalWrapper Nat (Fin internalCount) (Fin parameters.decoder.roots.length))
    (selected : List (Fin parameters.decoder.roots.length)) :=
  optionalInputRows parameters wrapper ++ [selected.map (fun output => (Sum.inr (.observed output), true))]

def selectedFiniteInput (parameters : Parameters)
    (wrapper : OptionalWrapper Nat (Fin internalCount) (Fin parameters.decoder.roots.length))
    (selected : List (Fin parameters.decoder.roots.length)) (rename : WrapperLabel parameters internalCount → Fin v) : FiniteFormula v :=
  ofClauses ((selectedInputRows parameters wrapper selected).map (Rows.mapClause rename))

def guardsFromRows {σ ρ : Type} [DecidableEq σ] [DecidableEq ρ]
    (rename : Sum σ (PrivateActivity (Fin internalCount) ρ) → Fin v)
    (clauses : List (Clause (Sum σ (PrivateActivity (Fin internalCount) ρ))))
    (wrapper : OptionalWrapper σ (Fin internalCount) ρ) (output : ρ)
    (contained : ∀ clause ∈ guardRows (.observed output) (wrapper.observedPairs output), clause ∈ clauses) :
    Guards (initialState (relabel rename (ofClauses clauses)))
      (rename (.inr (.observed output)), true)
      (rename (.inl (wrapper.observedPairs output).1.1), (wrapper.observedPairs output).1.2)
      (rename (.inl (wrapper.observedPairs output).2.1), (wrapper.observedPairs output).2.2) := by
  let first : Clause (Sum σ (PrivateActivity (Fin internalCount) ρ)) := (guardRows (.observed output) (wrapper.observedPairs output))[0]'(by simp [guardRows])
  let second : Clause (Sum σ (PrivateActivity (Fin internalCount) ρ)) := (guardRows (.observed output) (wrapper.observedPairs output))[1]'(by simp [guardRows])
  constructor
  · simpa [first, guardRows, Rows.mapClause, negate, Std.Sat.Literal.negate] using
      ofRow (memberRow rename clauses first (contained first (by simp [first, guardRows])))
  · simpa [second, guardRows, Rows.mapClause, negate, Std.Sat.Literal.negate] using
      ofRow (memberRow rename clauses second (contained second (by simp [second, guardRows])))

def selectedAfterPrefix (parameters : Parameters)
    (wrapper : OptionalWrapper Nat (Fin internalCount) (Fin parameters.decoder.roots.length))
    (selected : List (Fin parameters.decoder.roots.length)) (nonempty : selected ≠ [])
    (leaves : ∀ output ∈ selected, output ∈ wrapper.tree.leaves)
    (rename : WrapperLabel parameters internalCount → Fin v) (state : State v) (steps : List (Step v))
    (checked : runSteps (initialState (selectedFiniteInput parameters wrapper selected rename)) steps = some state)
    (equal : ∀ output ∈ selected, DirectionPair state []
      (rename (.inl (wrapper.observedPairs output).1.1), (wrapper.observedPairs output).1.2)
      (rename (.inl (wrapper.observedPairs output).2.1), (wrapper.observedPairs output).2.2)) :
    SubclauseProjection state [] (5 * selected.length - 1) := by
  let clauses := selectedInputRows parameters wrapper selected
  have run : runSteps (initialState (relabel rename (ofClauses clauses))) steps = some state := by
    rw [mapped_formula]
    exact checked
  let guards := fun output member => guardsFromRows rename clauses wrapper output (by
    intro clause present
    exact List.mem_append_left _ (List.mem_append_right _ (optionalRows_guard wrapper output (leaves output member) clause present)))
  let requirement : AvailableSubclause (initialState (relabel rename (ofClauses clauses)))
      (selected.map (fun output => (rename (.inr (.observed output)), true))) := by
    simpa [Rows.mapClause, List.map_map, Function.comp_def] using ofRow (memberRow rename clauses
      (selected.map (fun output => (Sum.inr (.observed output), true))) (by simp [clauses, selectedInputRows]))
  exact selectedSuffix state [] (fun output => (rename (.inr (.observed output)), true))
    (fun output => (rename (.inl (wrapper.observedPairs output).1.1), (wrapper.observedPairs output).1.2))
    (fun output => (rename (.inl (wrapper.observedPairs output).2.1), (wrapper.observedPairs output).2.2)) selected nonempty
    (fun output member => (guards output member).afterTrace state steps run) equal (afterTrace requirement state steps run)


def canonicalSelectedInput (parameters : Parameters)
    (wrapper : OptionalWrapper Nat (Fin internalCount) (Fin parameters.decoder.roots.length))
    (selected : List (Fin parameters.decoder.roots.length)) : FiniteFormula (canonicalWrapperCount parameters wrapper) :=
  let labels := canonicalWrapperLabels parameters wrapper
  selectedFiniteInput parameters wrapper selected (fun label => canonicalLabelIndex parameters labels label)

theorem canonicalObservedLabel_present (parameters : Parameters)
    (wrapper : OptionalWrapper Nat (Fin internalCount) (Fin parameters.decoder.roots.length))
    (output : Fin parameters.decoder.roots.length) (leaf : output ∈ wrapper.tree.leaves) :
    Sum.inr (PrivateActivity.observed output) ∈ canonicalWrapperLabels parameters wrapper := by
  let first : Clause (WrapperLabel parameters internalCount) := (guardRows (.observed output) (wrapper.observedPairs output))[0]'(by simp [guardRows])
  have present : first ∈ optionalInputRows parameters wrapper :=
    List.mem_append_right _ (optionalRows_guard wrapper output leaf first (by simp [first, guardRows]))
  exact canonicalWrapperLabels_contains parameters wrapper first present (Sum.inr (.observed output), false)
    (by simp [first, guardRows])

theorem canonicalSelectedInput_roundtrip (parameters : Parameters)
    (wrapper : OptionalWrapper Nat (Fin internalCount) (Fin parameters.decoder.roots.length))
    (selected : List (Fin parameters.decoder.roots.length))
    (leaves : ∀ output ∈ selected, output ∈ wrapper.tree.leaves) :
    relabel (canonicalWrapperDecode parameters wrapper) (canonicalSelectedInput parameters wrapper selected) =
      ofClauses (selectedInputRows parameters wrapper selected) := by
  apply relabel_rows_roundtrip
  intro clause present literal member
  apply canonicalWrapperRename_roundtrip
  rcases List.mem_append.mp present with old | added
  · exact canonicalWrapperLabels_contains parameters wrapper clause old literal member
  · simp only [List.mem_singleton] at added
    subst clause
    obtain ⟨output, accepted, same⟩ := List.mem_map.mp member
    subst literal
    exact canonicalObservedLabel_present parameters wrapper output (leaves output accepted)

end Controller.NativeProof.Wrapper
