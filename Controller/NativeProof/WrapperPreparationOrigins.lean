module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.WrapperTargetPreparation

@[expose] public section

/-! Shared healthy-one preparation carries retained origins for its exported rows. -/
namespace Controller.NativeProof.Wrapper
open Controller.CNF Controller.Resolution Controller.Native Controller.Native.SourceController
open Controller.NativeProof.FoldProjection Controller.NativeProof.SourceFoldProjection
open Controller.NativeProof.SourceStageCongruence Controller.NativeProof.SourceStagePolarity
open Controller.NativeProof.SourceStageXor Controller.NativeProof.SourceBusSchedule
open Controller.NativeProof.SourceBusAdvance Controller.NativeProof.SourceFoldProvenance
open Controller.NativeProof.SourceMismatchHandles Controller.NativeProof.SourceDecoderTraversal
open Controller.NativeProof.SourceHealthyOne
variable {parameters : Parameters} {v : Nat}

structure TargetPrefixOrigins (rename : Nat → Fin v) (start : SourcePrefix (parameters := parameters) rename)
    (target : SourceHealthyOne.TargetPrefix rename start) : Prop where
  supported : SourceDecoderSchedule.PrefixOriginalSupport rename (start.extend target.state target.steps target.checked)
  targetUnit : ∀ one, DecoderRowOrigin rename (start.extend target.state target.steps target.checked) (target.targetUnit one)

theorem targetPrefix_dite_origins (rename : Nat → Fin v) (start : SourcePrefix (parameters := parameters) rename)
    (condition : Prop) [Decidable condition]
    (yes : condition → SourceHealthyOne.TargetPrefix rename start)
    (no : ¬condition → SourceHealthyOne.TargetPrefix rename start)
    (yesOrigins : ∀ proof, TargetPrefixOrigins rename start (yes proof))
    (noOrigins : ∀ proof, TargetPrefixOrigins rename start (no proof)) :
    TargetPrefixOrigins rename start (dite condition yes no) := by
  by_cases proof : condition
  · rw [dite_eq_left proof]; exact yesOrigins proof
  · rw [dite_eq_right proof]; exact noOrigins proof

theorem optionalTarget_origins (rename : Nat → Fin v) (start : SourcePrefix (parameters := parameters) rename)
    (drive : parameters.drive = true) (supported : SourceDecoderSchedule.PrefixOriginalSupport rename start) :
    TargetPrefixOrigins rename start (SourceHealthyOne.optionalTarget rename start drive) := by
  unfold SourceHealthyOne.optionalTarget
  apply targetPrefix_dite_origins
  · intro one
    have actual := oneBusTarget_origins rename start drive one supported
    exact ⟨actual.1, fun _ => actual.2⟩
  · intro different
    refine ⟨?_, ?_⟩
    · simpa only [SourceDecoderSchedule.PrefixOriginalSupport, SourcePrefix.extend, List.append_nil] using supported
    · intro one; exact False.elim (different one)

structure PreparationOrigins (rename : Nat → Fin v)
    (prepared : SourceHealthyOne.Preparation (parameters := parameters) rename) : Prop where
  supported : SourceDecoderSchedule.PrefixOriginalSupport rename prepared.proofPrefix
  healthy : ∀ node, DecoderRowOrigin rename prepared.proofPrefix (prepared.healthy node)
  forward : ∀ row member, ForwardOriginProvenance rename prepared.proofPrefix (prepared.forward row member)
  nonempty : DecoderRowOrigin rename prepared.proofPrefix prepared.nonempty
  targetUnit : ∀ one, DecoderRowOrigin rename prepared.proofPrefix (prepared.targetUnit one)

theorem PreparationOrigins.afterTrace (rename : Nat → Fin v)
    (prepared : SourceHealthyOne.Preparation (parameters := parameters) rename) (origins : PreparationOrigins rename prepared)
    (next : State v) (steps : List (Step v)) (checked : runSteps prepared.proofPrefix.state steps = some next)
    (supported : SourceDecoderSchedule.PrefixOriginalSupport rename (prepared.proofPrefix.extend next steps checked)) :
    PreparationOrigins rename (prepared.afterTrace next steps checked) := by
  refine ⟨supported, ?_, ?_, ?_, ?_⟩
  · intro node; exact resultOrigin_append_right _ _ prepared.proofPrefix.steps steps _ (origins.healthy node)
  · intro row member
    exact ForwardOriginProvenance.afterTrace rename prepared.proofPrefix (prepared.forward row member)
      (origins.forward row member) next steps checked
  · exact resultOrigin_append_right _ _ prepared.proofPrefix.steps steps _ origins.nonempty
  · intro one; exact resultOrigin_append_right _ _ prepared.proofPrefix.steps steps _ (origins.targetUnit one)

theorem forwardRow_origins (rename : Nat → Fin v) (side : Side) (cofactor : Clause (Fin v))
    (table : SourceForwardRows.Table (parameters := parameters) rename side cofactor parameters.decoder.nodeCount)
    (origins : ForwardTableOrigins rename side table) (row : Clause parameters.decoder.ZeroVar)
    (member : row ∈ parameters.decoder.forwardClauses) :
    ForwardOriginProvenance rename table.proofPrefix (SourceForwardRows.forwardRow rename side cofactor table row member) := by
  unfold SourceForwardRows.forwardRow
  dsimp only [id]
  exact origins.rows _ _ _ _

theorem nativeReplay_available_origin (rename : Nat → Fin v)
    (before source : SourcePrefix (parameters := parameters) rename)
    (replay : NativeReplay (parameters := parameters) rename before source.state source.steps)
    (row : Rows.Available source.state clause)
    (origin : ResultOrigin (formula parameters).clauses.size
      (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) source.steps row.id) :
    ResultOrigin (formula parameters).clauses.size
      (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) replay.prefix.steps (replay.available row).id := by
  have mapped := rebase_native_result_origin rename (before.state.lastId - (formula parameters).clauses.size) source.steps row.id origin
  exact resultOrigin_append_left _ _ before.steps replay.added _ mapped

end Controller.NativeProof.Wrapper
