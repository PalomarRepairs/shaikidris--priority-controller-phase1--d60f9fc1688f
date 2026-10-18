module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.WrapperCompiler
public import Controller.NativeProof.WrapperDetection

@[expose] public section

/-! Executable wrapper compilers use the selected guarded-DAG detector and canonical emission. -/
namespace Controller.NativeProof.Wrapper
open Controller.CNF Controller.Resolution Controller.Native Controller.Native.SourceController
open Controller.Native.ObservationProjection Controller.NativeProof.FoldProjection
variable {internalCount : Nat}

def declaredActivity {ρ : Type} [BEq ρ] (wrapper : OptionalWrapper Nat (Fin internalCount) ρ) : PrivateActivity (Fin internalCount) ρ → Bool
  | .internal _ => true
  | .observed output => wrapper.tree.leaves.contains output
  | .tree path => match wrapper.tree.atPath path with
    | some (.branch _ _) => true
    | _ => false

def wrapperSupported (parameters : Parameters)
    (wrapper : OptionalWrapper Nat (Fin internalCount) (Fin parameters.decoder.roots.length)) : Bool :=
  Compiler.supported parameters &&
    ((wrapper.tree.leaves.all (fun output => decide (wrapper.observedPairs output = nativePair parameters output))) &&
      wrapper.clauses.all (fun clause => clause.alternatives.all (declaredActivity wrapper)))

theorem wrapperSupported_native (parameters : Parameters)
    (wrapper : OptionalWrapper Nat (Fin internalCount) (Fin parameters.decoder.roots.length))
    (accepted : wrapperSupported parameters wrapper = true) : parameters.layout = .raw ∧ parameters.decoder.Guarded :=
  Compiler.supported_iff.mp (Bool.and_eq_true_iff.mp accepted).1

theorem wrapperSupported_pairs (parameters : Parameters)
    (wrapper : OptionalWrapper Nat (Fin internalCount) (Fin parameters.decoder.roots.length))
    (accepted : wrapperSupported parameters wrapper = true) :
    ∀ output ∈ wrapper.tree.leaves, wrapper.observedPairs output = nativePair parameters output := by
  have pairs := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp accepted).2).1
  simpa only [List.all_eq_true, decide_eq_true_eq] using pairs

def optionalRefutationOfAbsence (parameters : Parameters) (guarded : parameters.decoder.Guarded)
    (wrapper : OptionalWrapper Nat (Fin internalCount) (Fin parameters.decoder.roots.length))
    (pairs : ∀ output ∈ wrapper.tree.leaves, wrapper.observedPairs output = nativePair parameters output)
    (absent : parameters.drive = true → Decoder.NoDiscrepancy parameters wrapper.tree.leaves.toFinset) :
    OptionalRefutation parameters wrapper (canonicalWrapperRename parameters wrapper) := by
  let labels := canonicalWrapperLabels parameters wrapper
  let rename := fun label => canonicalLabelIndex parameters labels label
  let native := nativeSelectedPrefix parameters (optionalInputRows parameters wrapper)
    (fun clause member => List.mem_append_left _ member) rename wrapper.tree.leaves guarded absent
  let prefixState : OptionalEqualityPrefix parameters wrapper rename :=
    ⟨native.state, native.steps, native.checked, fun output member => by
      rw [pairs output member]
      exact native.pairs output member⟩
  exact optionalRefutationFromPrefix parameters wrapper rename prefixState

def runOptional (parameters : Parameters)
    (wrapper : OptionalWrapper Nat (Fin internalCount) (Fin parameters.decoder.roots.length)) :
    Option (Trace (canonicalWrapperCount parameters wrapper)) :=
  if accepted : wrapperSupported parameters wrapper = true then
    if absent : wrapperDetect parameters wrapper.tree.leaves = none then
      some (optionalRefutationOfAbsence parameters (wrapperSupported_native parameters wrapper accepted).2 wrapper
        (wrapperSupported_pairs parameters wrapper accepted)
        ((wrapperDetect_none_iff parameters (wrapperSupported_native parameters wrapper accepted).2 _).mp absent)).trace
    else none
  else none

def runSelected (parameters : Parameters)
    (wrapper : OptionalWrapper Nat (Fin internalCount) (Fin parameters.decoder.roots.length))
    (selected : List (Fin parameters.decoder.roots.length)) : Option (Trace (canonicalWrapperCount parameters wrapper)) :=
  if accepted : wrapperSupported parameters wrapper = true then
    let labels := canonicalWrapperLabels parameters wrapper
    let rename := fun label => canonicalLabelIndex parameters labels label
    if nonempty : selected ≠ [] then
      if leaves : ∀ output ∈ selected, output ∈ wrapper.tree.leaves then
        if absent : wrapperDetect parameters selected = none then
          some (selectedRefutationOfAbsence parameters (wrapperSupported_native parameters wrapper accepted).2 wrapper (wrapperSupported_pairs parameters wrapper accepted)
            selected nonempty leaves
            ((wrapperDetect_none_iff parameters (wrapperSupported_native parameters wrapper accepted).2 _).mp absent)
            rename).trace
        else none
      else none
    else none
  else none

theorem runOptional_checked (parameters : Parameters)
    (wrapper : OptionalWrapper Nat (Fin internalCount) (Fin parameters.decoder.roots.length))
    (trace : Trace (canonicalWrapperCount parameters wrapper)) (returned : runOptional parameters wrapper = some trace) :
    check (canonicalOptionalInput parameters wrapper) trace = true := by
  unfold runOptional at returned
  split at returned
  · split at returned
    · cases Option.some.inj returned
      exact (optionalRefutationOfAbsence parameters _ wrapper _ _).accepted
    · simp at returned
  · simp at returned

theorem runSelected_checked (parameters : Parameters)
    (wrapper : OptionalWrapper Nat (Fin internalCount) (Fin parameters.decoder.roots.length))
    (selected : List (Fin parameters.decoder.roots.length)) (trace : Trace (canonicalWrapperCount parameters wrapper))
    (returned : runSelected parameters wrapper selected = some trace) :
    check (canonicalSelectedInput parameters wrapper selected) trace = true := by
  unfold runSelected at returned
  split at returned
  · dsimp only at returned
    split at returned
    · split at returned
      · split at returned
        · cases Option.some.inj returned
          exact (selectedRefutationOfAbsence parameters _ wrapper _ selected _ _ _ _).accepted
        · simp at returned
      · simp at returned
    · simp at returned
  · simp at returned

theorem runOptional_complete (parameters : Parameters)
    (wrapper : OptionalWrapper Nat (Fin internalCount) (Fin parameters.decoder.roots.length))
    (accepted : wrapperSupported parameters wrapper = true)
    (unsat : Unsatisfiable (canonicalOptionalInput parameters wrapper)) :
    ∃ trace, runOptional parameters wrapper = some trace ∧ check (canonicalOptionalInput parameters wrapper) trace = true := by
  have native := wrapperSupported_native parameters wrapper accepted
  have pairs := wrapperSupported_pairs parameters wrapper accepted
  have original : Unsatisfiable (optionalNativeInput parameters wrapper) := by
    apply unsatisfiable_of_decode _ _ (canonicalWrapperDecode parameters wrapper) _ unsat
    rw [canonicalOptionalInput_roundtrip, optionalInputRows_formula]
  have absent : wrapperDetect parameters wrapper.tree.leaves = none :=
    (wrapperDetect_none_iff parameters native.2 _).mpr
      (fun drive => optional_native_absence parameters native.1 drive wrapper pairs original)
  unfold runOptional
  simp only [accepted, absent, ↓reduceDIte]
  exact ⟨_, rfl, (optionalRefutationOfAbsence parameters _ wrapper _ _).accepted⟩

theorem runSelected_complete (parameters : Parameters)
    (wrapper : OptionalWrapper Nat (Fin internalCount) (Fin parameters.decoder.roots.length))
    (accepted : wrapperSupported parameters wrapper = true)
    (selected : List (Fin parameters.decoder.roots.length)) (nonempty : selected ≠ [])
    (leaves : ∀ output ∈ selected, output ∈ wrapper.tree.leaves)
    (unsat : Unsatisfiable (canonicalSelectedInput parameters wrapper selected)) :
    ∃ trace, runSelected parameters wrapper selected = some trace ∧
      check (canonicalSelectedInput parameters wrapper selected) trace = true := by
  have native := wrapperSupported_native parameters wrapper accepted
  have pairs := wrapperSupported_pairs parameters wrapper accepted
  have original : Unsatisfiable (selectedNativeInput parameters wrapper selected) := by
    apply unsatisfiable_of_decode _ _ (canonicalWrapperDecode parameters wrapper) _ unsat
    rw [canonicalSelectedInput_roundtrip parameters wrapper selected leaves, selectedInputRows_formula]
  have absent : wrapperDetect parameters selected = none :=
    (wrapperDetect_none_iff parameters native.2 _).mpr
      (fun drive => selected_native_absence parameters native.1 drive wrapper pairs selected leaves original)
  unfold runSelected
  rw [dite_eq_left accepted, dite_eq_left nonempty, dite_eq_left leaves, dite_eq_left absent]
  exact ⟨_, rfl, (selectedRefutationOfAbsence parameters _ wrapper _ selected _ _ _ _).accepted⟩

end Controller.NativeProof.Wrapper
