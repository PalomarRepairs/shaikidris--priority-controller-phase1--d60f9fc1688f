module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.WrapperAssembly

@[expose] public section

/-! Complete native refutation constructors for the optional and selected wrappers. -/
namespace Controller.NativeProof.Wrapper
open Controller.CNF Controller.Resolution Controller.Native Controller.Native.SourceController
open Controller.Native.ObservationProjection Controller.NativeProof.FoldProjection
open Controller.NativeProof.SourceBusSchedule
variable {internalCount v : Nat}

theorem optionalInputRows_formula (parameters : Parameters)
    (wrapper : OptionalWrapper Nat (Fin internalCount) (Fin parameters.decoder.roots.length)) :
    ofClauses (optionalInputRows parameters wrapper) = optionalNativeInput parameters wrapper := by
  apply Controller.CNF.OrderedFormula.Internal.ext_iff.mpr
  simp [Controller.CNF.OrderedFormula.Internal.clauses_append, optionalInputRows, optionalNativeInput, optionalFormula, taggedCoreRows, nativeCore,
    ofClauses, relabel, Controller.CNF.OrderedFormula.relabel, Controller.CNF.OrderedFormula.Clause.relabel, Controller.CNF.OrderedFormula.append]

theorem selectedInputRows_formula (parameters : Parameters)
    (wrapper : OptionalWrapper Nat (Fin internalCount) (Fin parameters.decoder.roots.length))
    (selected : List (Fin parameters.decoder.roots.length)) :
    ofClauses (selectedInputRows parameters wrapper selected) = selectedNativeInput parameters wrapper selected := by
  have appendRows {α : Type} (first second : List (Clause α)) :
      ofClauses (first ++ second) = ofClauses first ++ ofClauses second := by
    apply Controller.CNF.OrderedFormula.Internal.ext_iff.mpr
    simp [ofClauses, Controller.CNF.OrderedFormula.Internal.clauses_append]
  rw [selectedInputRows, appendRows, optionalInputRows_formula]
  change (relabel Sum.inl (nativeCore parameters) ++ optionalFormula wrapper) ++ _ =
    relabel Sum.inl (nativeCore parameters) ++ (optionalFormula wrapper ++ _)
  apply Controller.CNF.OrderedFormula.Internal.ext_iff.mpr
  simp only [Controller.CNF.OrderedFormula.Internal.clauses_append, Array.append_assoc]


theorem unsatisfiable_of_decode {α : Type} {size : Nat} (original : Formula α) (finite : FiniteFormula size)
    (decode : Fin size → α) (roundtrip : relabel decode finite = original) (unsat : Unsatisfiable finite) :
    Unsatisfiable original := by
  rintro ⟨values, model⟩
  apply unsat
  refine ⟨values ∘ decode, (satisfies_relabel decode values finite).mp ?_⟩
  rw [roundtrip]
  exact model

structure SelectedRefutation (parameters : Parameters)
    (wrapper : OptionalWrapper Nat (Fin internalCount) (Fin parameters.decoder.roots.length))
    (selected : List (Fin parameters.decoder.roots.length)) (rename : WrapperLabel parameters internalCount → Fin v) where
  trace : Trace v
  accepted : Controller.Resolution.check (selectedFiniteInput parameters wrapper selected rename) trace = true

def selectedRefutationOfAbsence (parameters : Parameters)
    (guarded : parameters.decoder.Guarded)
    (wrapper : OptionalWrapper Nat (Fin internalCount) (Fin parameters.decoder.roots.length))
    (pairs : ∀ output ∈ wrapper.tree.leaves, wrapper.observedPairs output = nativePair parameters output)
    (selected : List (Fin parameters.decoder.roots.length)) (nonempty : selected ≠ [])
    (leaves : ∀ output ∈ selected, output ∈ wrapper.tree.leaves)
    (absent : parameters.drive = true → Decoder.NoDiscrepancy parameters selected.toFinset)
    (rename : WrapperLabel parameters internalCount → Fin v) : SelectedRefutation parameters wrapper selected rename := by
  let prefixState := nativeSelectedPrefix parameters (selectedInputRows parameters wrapper selected)
    (fun clause member => List.mem_append_left _ (List.mem_append_left _ member)) rename selected guarded
    absent
  have equal : ∀ output ∈ selected, DirectionPair prefixState.state []
      (rename (.inl (wrapper.observedPairs output).1.1), (wrapper.observedPairs output).1.2)
      (rename (.inl (wrapper.observedPairs output).2.1), (wrapper.observedPairs output).2.2) := by
    intro output member
    rw [pairs output (leaves output member)]
    exact prefixState.pairs output member
  let suffix := selectedAfterPrefix parameters wrapper selected nonempty leaves rename prefixState.state
    prefixState.steps prefixState.checked equal
  have empty : suffix.result.clause = [] := by
    cases shape : suffix.result.clause with
    | nil => rfl
    | cons head tail =>
      exact False.elim (by have bad := suffix.result.subset head (by rw [shape]; simp); simpa using bad)
  let trace : Trace v := ⟨(selectedFiniteInput parameters wrapper selected rename).clauses.size,
    prefixState.steps ++ suffix.steps, suffix.result.row.id⟩
  refine ⟨trace, ?_⟩
  have combined : runSteps (initialState (selectedFiniteInput parameters wrapper selected rename)) trace.steps = some suffix.state := by
    rw [runSteps_append]
    change (runSteps (initialState (ofClauses ((selectedInputRows parameters wrapper selected).map (Rows.mapClause rename)) )) prefixState.steps).bind _ = _
    rw [prefixState.checked]
    exact suffix.checked
  have final : suffix.state.rows trace.finalClauseId = some [] :=
    suffix.result.row.present.trans (congrArg some empty)
  unfold Controller.Resolution.check
  rw [ite_eq_left (show trace.originalClauseCount = (selectedFiniteInput parameters wrapper selected rename).clauses.size from rfl), combined]
  simp only [final]
  rfl

def compileOptional (parameters : Parameters) (raw : parameters.layout = .raw)
    (guarded : parameters.decoder.Guarded)
    (wrapper : OptionalWrapper Nat (Fin internalCount) (Fin parameters.decoder.roots.length))
    (pairs : ∀ output ∈ wrapper.tree.leaves, wrapper.observedPairs output = nativePair parameters output)
    (unsat : Unsatisfiable (canonicalOptionalInput parameters wrapper)) :
    OptionalRefutation parameters wrapper (canonicalWrapperRename parameters wrapper) := by
  have sourceUnsat : Unsatisfiable (optionalNativeInput parameters wrapper) := by
    apply unsatisfiable_of_decode _ _ (canonicalWrapperDecode parameters wrapper) _ unsat
    rw [canonicalOptionalInput_roundtrip, optionalInputRows_formula]
  exact optionalRefutationFromPrefix parameters wrapper (canonicalWrapperRename parameters wrapper)
    (optionalDrivenPrefix parameters raw guarded wrapper pairs sourceUnsat _)

def compileSelected (parameters : Parameters) (raw : parameters.layout = .raw)
    (guarded : parameters.decoder.Guarded)
    (wrapper : OptionalWrapper Nat (Fin internalCount) (Fin parameters.decoder.roots.length))
    (pairs : ∀ output ∈ wrapper.tree.leaves, wrapper.observedPairs output = nativePair parameters output)
    (selected : List (Fin parameters.decoder.roots.length)) (nonempty : selected ≠ [])
    (leaves : ∀ output ∈ selected, output ∈ wrapper.tree.leaves)
    (unsat : Unsatisfiable (canonicalSelectedInput parameters wrapper selected)) :
    SelectedRefutation parameters wrapper selected (canonicalWrapperRename parameters wrapper) := by
  have sourceUnsat : Unsatisfiable (selectedNativeInput parameters wrapper selected) := by
    apply unsatisfiable_of_decode _ _ (canonicalWrapperDecode parameters wrapper) _ unsat
    rw [canonicalSelectedInput_roundtrip parameters wrapper selected leaves, selectedInputRows_formula]
  exact selectedRefutationOfAbsence parameters guarded wrapper pairs selected nonempty leaves
    (fun drive => selected_native_absence parameters raw drive wrapper pairs selected leaves sourceUnsat) _

end Controller.NativeProof.Wrapper
