module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.WrapperPreparationOrigins

@[expose] public section

/-! The concrete healthy-one preparation exports only retained native origins. -/
namespace Controller.NativeProof.Wrapper
open Controller.CNF Controller.Resolution Controller.Native Controller.Native.SourceController
open Controller.NativeProof.FoldProjection Controller.NativeProof.SourceFoldProjection
open Controller.NativeProof.SourceStageCongruence Controller.NativeProof.SourceStagePolarity
open Controller.NativeProof.SourceStageXor Controller.NativeProof.SourceBusSchedule
open Controller.NativeProof.SourceBusAdvance Controller.NativeProof.SourceFoldProvenance
open Controller.NativeProof.SourceMismatchHandles Controller.NativeProof.SourceDecoderTraversal
open Controller.NativeProof.SourceHealthyOne
variable {parameters : Parameters} {v : Nat}

theorem healthyOnePreparation_origins (rename : Nat → Fin v) (drive : parameters.drive = true)
    (guarded : parameters.decoder.Guarded) :
    PreparationOrigins rename (SourceHealthyOne.prepare (parameters := parameters) rename drive guarded) := by
  let healthy := SourceDecoderEvaluation.healthy rename drive guarded
  let forwards := SourceForwardRows.allRows rename .faulty (cofactor (parameters := parameters) rename) guarded healthy.proofPrefix
  have forwardRun : runSteps healthy.proofPrefix.state
      (forwards.proofPrefix.steps.drop healthy.proofPrefix.steps.length) = some forwards.proofPrefix.state :=
    SourceForwardRows.build_relative rename .faulty (cofactor (parameters := parameters) rename) guarded healthy.proofPrefix
      parameters.decoder.nodeCount (Nat.le_refl _)
  let healthyNow := healthy.afterTrace forwards.proofPrefix.state
    (forwards.proofPrefix.steps.drop healthy.proofPrefix.steps.length) forwardRun
  let activation := compiledMixedActivation rename drive
  let replay := replayNativeProgram rename forwards.proofPrefix activation.state activation.steps activation.checked
  let forwardNow := forwards.afterTrace replay.next replay.added replay.checked
  let healthyActivated := healthyNow.afterTrace replay.next replay.added replay.checked
  let target := SourceHealthyOne.optionalTarget rename replay.prefix drive
  let prefixState := replay.prefix.extend target.state target.steps target.checked
  have healthyOrigins := healthyDecoder_origins rename drive guarded
  have forwardOrigins := forwardAllRows_origins rename .faulty (cofactor (parameters := parameters) rename) guarded
    healthy.proofPrefix healthyOrigins.supported
  have relativeSteps : healthy.proofPrefix.steps ++ forwards.proofPrefix.steps.drop healthy.proofPrefix.steps.length =
      forwards.proofPrefix.steps := by
    obtain ⟨suffix, same⟩ := SourceForwardRows.build_extends rename .faulty (cofactor (parameters := parameters) rename)
      guarded healthy.proofPrefix parameters.decoder.nodeCount (Nat.le_refl _)
    change healthy.proofPrefix.steps ++ forwards.proofPrefix.steps.drop healthy.proofPrefix.steps.length = _
    change forwards.proofPrefix.steps = healthy.proofPrefix.steps ++ suffix at same
    rw [same, List.drop_left]
  have healthyNowSupport : SourceDecoderSchedule.PrefixOriginalSupport rename healthyNow.proofPrefix := by
    change TraceOriginalSupport (formula parameters).clauses.size
      (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
      (healthy.proofPrefix.steps ++ forwards.proofPrefix.steps.drop healthy.proofPrefix.steps.length)
    rw [relativeSteps]
    exact forwardOrigins.supported
  have healthyNowOrigins := DecoderTableOrigins.afterTrace rename .healthy healthy healthyOrigins
    forwards.proofPrefix.state (forwards.proofPrefix.steps.drop healthy.proofPrefix.steps.length) forwardRun healthyNowSupport
  let activationPrefix : SourcePrefix (parameters := parameters) rename :=
    ⟨activation.state, activation.steps, activation.checked⟩
  have activationOrigins := compiledMixedActivation_supported rename drive
  have activationSupport : SourceDecoderSchedule.PrefixOriginalSupport rename activationPrefix := by
    simpa only [SourcePrefix.initial, List.nil_append, SourceDecoderSchedule.PrefixOriginalSupport,
      activationPrefix, activation] using activationOrigins.1
  have replaySupport := NativeReplay.prefix_supported rename forwards.proofPrefix activationPrefix replay
    forwardOrigins.supported activationSupport
  have forwardNowOrigins := ForwardTableOrigins.afterTrace rename .faulty forwards forwardOrigins
    replay.next replay.added replay.checked replaySupport
  have activatedSupport : SourceDecoderSchedule.PrefixOriginalSupport rename healthyActivated.proofPrefix := by
    change TraceOriginalSupport (formula parameters).clauses.size
      (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
      ((healthy.proofPrefix.steps ++ forwards.proofPrefix.steps.drop healthy.proofPrefix.steps.length) ++ replay.added)
    rw [relativeSteps]
    exact replaySupport
  have activatedOrigins := DecoderTableOrigins.afterTrace rename .healthy healthyNow healthyNowOrigins
    replay.next replay.added replay.checked activatedSupport
  have targetOrigins := optionalTarget_origins rename replay.prefix drive replaySupport
  let emitted := SourceHealthyOne.prepare rename drive guarded
  have activatedSteps : healthyActivated.proofPrefix.steps = replay.prefix.steps := by
    change (healthy.proofPrefix.steps ++ forwards.proofPrefix.steps.drop healthy.proofPrefix.steps.length) ++ replay.added = _
    rw [relativeSteps]
    rfl
  refine ⟨targetOrigins.supported, ?_, ?_, ?_, targetOrigins.targetUnit⟩
  · intro node
    have indexEqual : (emitted.healthy node).row.id = (healthyActivated.nodes node node.isLt).row.id := by
      unfold emitted SourceHealthyOne.prepare
      dsimp only [id]
      with_unfolding_all
        apply SourceMixedSchedule.subclause_indices_cast_id rfl
        simp only [cofactor, SourceHealthyMasks.context, SourceDecoderEvaluation.nodeBit,
          SourceDecoderEvaluation.stored_eq_output rename .healthy parameters.decoder.nodeCount (Nat.le_refl _) node node.isLt]
    unfold DecoderRowOrigin
    change ResultOrigin (formula parameters).clauses.size
      (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) prefixState.steps (emitted.healthy node).row.id
    rw [indexEqual]
    have origin := resultOrigin_append_right _ _ healthyActivated.proofPrefix.steps target.steps _
      (activatedOrigins.nodes node node.isLt)
    rw [activatedSteps] at origin
    exact origin
  · intro row member
    exact ForwardOriginProvenance.afterTrace rename forwardNow.proofPrefix
      (SourceForwardRows.forwardRow rename .faulty (cofactor (parameters := parameters) rename) forwardNow row member)
      (forwardRow_origins rename .faulty (cofactor (parameters := parameters) rename) forwardNow forwardNowOrigins row member)
      target.state target.steps target.checked
  · have mapped := nativeReplay_available_origin rename forwards.proofPrefix activationPrefix replay activation.result.row
      (by simpa only [SourcePrefix.initial, List.nil_append] using activationOrigins.2)
    have origin := resultOrigin_append_right _ _ replay.prefix.steps target.steps _ mapped
    have indexEqual : emitted.nonempty.row.id = (replay.available activation.result.row).id := by
      unfold emitted SourceHealthyOne.prepare
      dsimp only [id]
      with_unfolding_all
        apply SourceMixedSchedule.subclause_indices_cast_id rfl
        congr 1
        unfold compiledQualifierOutputs
        apply List.map_congr_left
        intro channel member
        exact congrArg (mapLiteral rename) (compiled_faulty_qualifier_slot channel)
    unfold DecoderRowOrigin
    change ResultOrigin (formula parameters).clauses.size
      (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) prefixState.steps emitted.nonempty.row.id
    rw [indexEqual]
    exact origin

end Controller.NativeProof.Wrapper
