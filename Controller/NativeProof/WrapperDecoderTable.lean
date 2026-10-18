module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.WrapperDecoderGuard

@[expose] public section

/-! Retained provenance is preserved through the shared native decoder table. -/
namespace Controller.NativeProof.Wrapper
open Controller.CNF Controller.Resolution Controller.Native Controller.Native.SourceController
open Controller.NativeProof.FoldProjection Controller.NativeProof.SourceFoldProjection
open Controller.NativeProof.SourceStageCongruence Controller.NativeProof.SourceStagePolarity
open Controller.NativeProof.SourceStageXor Controller.NativeProof.SourceBusSchedule
open Controller.NativeProof.SourceFoldProvenance Controller.NativeProof.SourceMismatchHandles
open Controller.NativeProof.SourceDecoderEvaluation Controller.NativeProof.SourceDecoderTraversal
open Controller.NativeProof.SourceDecoderClauses Controller.NativeProof.SourceDecoderSchedule
variable {parameters : Parameters} {v : Nat}

theorem decoderStep_origins (rename : Nat → Fin v) (side : Side) (guarded : parameters.decoder.Guarded)
    (node : Fin parameters.decoder.nodeCount)
    (table : SourceDecoderEvaluation.Table (parameters := parameters) rename side cofactor assignment node.val)
    (origins : DecoderTableOrigins rename side table) :
    DecoderNodeStepOrigins rename side node table (SourceDecoderEvaluation.step rename side guarded node table) := by
  unfold SourceDecoderEvaluation.step
  split
  · rename_i shape
    exact decoderZero_origins rename side node table shape origins
  · rename_i channel shape
    exact decoderInput_origins rename side node table channel shape origins
  · rename_i children shape
    exact decoderDisjunction_origins rename side node table children shape origins
  · rename_i child labels shape
    exact decoderGuard_origins rename side node table child labels shape origins
  · rename_i left right shape
    exact False.elim (by simpa [Controller.Decoder.Gate.IsGuarded, shape, Controller.Decoder.Gate.isLiveAnd] using guarded node)

theorem decoderAppend_origins (rename : Nat → Fin v) (side : Side) (node : Fin parameters.decoder.nodeCount)
    (table : SourceDecoderEvaluation.Table (parameters := parameters) rename side cofactor assignment node.val)
    (added : NodeStep rename side cofactor assignment node table)
    (origins : DecoderTableOrigins rename side table) (addedOrigins : DecoderNodeStepOrigins rename side node table added) :
    DecoderTableOrigins rename side (SourceDecoderEvaluation.append rename side node table added) := by
  let next := table.afterTrace added.state added.steps added.checked
  have nextOrigins := DecoderTableOrigins.afterTrace rename side table origins added.state added.steps added.checked addedOrigins.supported
  refine ⟨addedOrigins.supported, nextOrigins.qualifiers, ?_⟩
  intro query before
  by_cases same : query = node
  · subst query
    have indexEqual : ((SourceDecoderEvaluation.append rename side node table added).nodes node before).row.id =
        added.result.row.id := by
      unfold SourceDecoderEvaluation.append
      dsimp only [id]
      simp only [SourceMixedSchedule.subclause_dite_id, dite_eq_left rfl, dite_true]
      with_unfolding_all
        apply SourceMixedSchedule.subclause_indices_mpr_id rfl
        simp only [decoderStoredLiteral_self, outputLiteral, SourceDecoderEvaluation.Table.afterTrace, SourcePrefix.extend]
    unfold DecoderRowOrigin
    rw [indexEqual]
    exact addedOrigins.result
  · have earlier : query.val < node.val := by
      have different : query.val ≠ node.val := fun equal => same (Fin.ext equal)
      omega
    have indexEqual : ((SourceDecoderEvaluation.append rename side node table added).nodes query before).row.id =
        (next.nodes query earlier).row.id := by
      unfold SourceDecoderEvaluation.append
      dsimp only [id]
      simp only [SourceMixedSchedule.subclause_dite_id, dite_eq_right same]
      with_unfolding_all
        apply SourceMixedSchedule.subclause_indices_mpr_id rfl
        simp only [decoderStoredLiteral_old rename side node query earlier]
    unfold DecoderRowOrigin
    rw [indexEqual]
    exact nextOrigins.nodes query earlier

theorem decoderBuild_origins (rename : Nat → Fin v) (side : Side) (guarded : parameters.decoder.Guarded)
    (seed : SourceDecoderEvaluation.Table (parameters := parameters) rename side cofactor assignment 0)
    (origins : DecoderTableOrigins rename side seed) (count : Nat) (bound : count ≤ parameters.decoder.nodeCount) :
    DecoderTableOrigins rename side (SourceDecoderEvaluation.build rename side guarded seed count bound) := by
  induction count with
  | zero => exact origins
  | succ count ih =>
    let node : Fin parameters.decoder.nodeCount := ⟨count, by omega⟩
    let table := SourceDecoderEvaluation.build rename side guarded seed count (by omega)
    have tableOrigins := ih (by omega)
    exact decoderAppend_origins rename side node table (SourceDecoderEvaluation.step rename side guarded node table)
      tableOrigins (decoderStep_origins rename side guarded node table tableOrigins)

theorem healthyDecoder_origins (rename : Nat → Fin v) (drive : parameters.drive = true)
    (guarded : parameters.decoder.Guarded) :
    DecoderTableOrigins rename .healthy (SourceDecoderEvaluation.healthy (parameters := parameters) rename drive guarded) :=
  decoderBuild_origins rename .healthy guarded (SourceDecoderEvaluation.healthySeed rename drive)
    (healthyDecoderSeed_origins rename drive) _ (Nat.le_refl _)

end Controller.NativeProof.Wrapper
