module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.WrapperCofactorOrigins

@[expose] public section

/-! The driven seed prepares native rows independently of the wrapper observations. -/
namespace Controller.NativeProof.Wrapper
open Controller.CNF Controller.Resolution Controller.Native Controller.Native.SourceController
open Controller.NativeProof.FoldProjection Controller.NativeProof.SourceFoldProjection
open Controller.NativeProof.SourceStageCongruence Controller.NativeProof.SourceStagePolarity
open Controller.NativeProof.SourceBusSchedule Controller.NativeProof.SourceBusAdvance
open Controller.NativeProof.SourceMismatchHandles Controller.NativeProof.SourceDecoderTraversal
open Controller.NativeProof.SourceHealthyOne Controller.NativeProof.SourceFoldProvenance
variable {parameters : Parameters} {v : Nat}

structure DrivenSeedOrigins (rename : Nat → Fin v)
    (table : Compiler.DrivenTable (parameters := parameters) rename 0) : Prop where
  summaries : SupportTableOrigins rename table.summaries
  equalOne : ∀ output, SourceDecoderSchedule.DirectionPairOrigin rename table.summaries.prepared.proofPrefix (table.equalOne output)
  healthyFlag : DecoderRowOrigin rename table.summaries.prepared.proofPrefix table.healthyFlag

theorem DrivenSeedOrigins.afterTrace (rename : Nat → Fin v)
    (table : Compiler.DrivenTable (parameters := parameters) rename 0) (origins : DrivenSeedOrigins rename table)
    (next : State v) (steps : List (Step v)) (checked : runSteps table.summaries.prepared.proofPrefix.state steps = some next)
    (supported : SourceDecoderSchedule.PrefixOriginalSupport rename (table.summaries.prepared.proofPrefix.extend next steps checked)) :
    DrivenSeedOrigins rename (table.afterTrace next steps checked) := by
  refine ⟨SupportTableOrigins.afterTrace rename table.summaries origins.summaries next steps checked supported, ?_, ?_⟩
  · intro output
    exact ⟨SourceDecoderSchedule.GuardedTransferOrigin.afterTrace rename _ _ (origins.equalOne output).1 next steps checked,
      SourceDecoderSchedule.GuardedTransferOrigin.afterTrace rename _ _ (origins.equalOne output).2 next steps checked⟩
  · exact resultOrigin_append_right _ _ _ steps _ origins.healthyFlag

theorem initialDriven_origins (rename : Nat → Fin v) (drive : parameters.drive = true)
    (guarded : parameters.decoder.Guarded) : DrivenSeedOrigins rename (Compiler.initialDriven rename drive guarded) := by
  let summaries := SourceSupportSummaries.allSummaries rename guarded (prepare rename drive guarded)
  let equal := equalDecoderProgram (parameters := parameters) rename true
  let replay := replayNativeProgram rename summaries.prepared.proofPrefix equal.table.prefixState.state
    equal.table.prefixState.steps equal.table.prefixState.checked
  let extended := summaries.afterTrace replay.next replay.added replay.checked
  let physical := SourceMismatchHandles.healthyFlagUnit rename drive
  let final := replayNativeProgram rename extended.prepared.proofPrefix physical.state physical.steps physical.checked
  have summariesOrigins := supportClosedSummaries_origins rename drive guarded
  have replaySupport := NativeReplay.prefix_supported rename summaries.prepared.proofPrefix equal.table.prefixState replay
    summariesOrigins.prepared.supported (equalDecoderProgram_supported rename true).1.1
  have extendedOrigins := SupportTableOrigins.afterTrace rename summaries summariesOrigins replay.next replay.added replay.checked replaySupport
  have physicalSupport := healthyPhysicalSource_supported rename drive
  have finalSupport := NativeReplay.prefix_supported rename extended.prepared.proofPrefix (healthyPhysicalSource rename drive) final
    extendedOrigins.prepared.supported physicalSupport
  refine ⟨SupportTableOrigins.afterTrace rename extended extendedOrigins final.next final.added final.checked finalSupport, ?_, ?_⟩
  · intro output
    have origin := NativeReplay.pair_supported rename summaries.prepared.proofPrefix equal.table.prefixState replay
      (compiledEqualDecoderRoot rename true output) (compiledEqualDecoderRoot_supported rename true output)
    exact ⟨SourceDecoderSchedule.GuardedTransferOrigin.afterTrace rename replay.prefix _ origin.1 final.next final.added final.checked,
      SourceDecoderSchedule.GuardedTransferOrigin.afterTrace rename replay.prefix _ origin.2 final.next final.added final.checked⟩
  · exact nativeReplay_available_origin rename extended.prepared.proofPrefix (healthyPhysicalSource rename drive) final
      physical.result.row (healthyPhysicalSource_unit_origin rename drive)

end Controller.NativeProof.Wrapper
