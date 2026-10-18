module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.WrapperDecoderOrigins

@[expose] public section

/-! Provenance follows the actual native decoder evaluation constructors. -/
namespace Controller.NativeProof.Wrapper
open Controller.CNF Controller.Resolution Controller.Native Controller.Native.SourceController
open Controller.NativeProof.FoldProjection Controller.NativeProof.SourceFoldProjection
open Controller.NativeProof.SourceStageCongruence Controller.NativeProof.SourceStagePolarity
open Controller.NativeProof.SourceStageXor Controller.NativeProof.SourceBusSchedule
open Controller.NativeProof.SourceFoldProvenance Controller.NativeProof.SourceMismatchHandles
open Controller.NativeProof.SourceDecoderEvaluation Controller.NativeProof.SourceDecoderTraversal
open Controller.NativeProof.SourceDecoderClauses
open Controller.NativeProof.SourceDecoderSchedule
variable {parameters : Parameters} {v : Nat}

theorem decoderZero_origins (rename : Nat → Fin v) (side : Side) (node : Fin parameters.decoder.nodeCount)
    (table : SourceDecoderEvaluation.Table (parameters := parameters) rename side cofactor assignment node.val)
    (shape : parameters.decoder.node node = .zero) (origins : DecoderTableOrigins rename side table) :
    DecoderNodeStepOrigins rename side node table (SourceDecoderEvaluation.zero rename side node table shape) := by
  let added := SourceDecoderEvaluation.zero rename side node table shape
  have bit : nodeBit assignment node = false := parameters.decoder.eval_zero assignment node shape
  have output : outputLiteral rename side node = mapLiteral rename (decoderLiveAndOutput side node) := by
    simp only [outputLiteral, decoderZero_output side node _ shape]
    rfl
  have stepsEqual : added.steps = [] := rfl
  have indexEqual : added.result.row.id = (decoderZeroUnit rename side node shape table.proofPrefix).row.id := by
    unfold added SourceDecoderEvaluation.zero
    dsimp only [id]
    with_unfolding_all
      apply SourceMixedSchedule.subclause_indices_mpr_id rfl
      simp only [bit, valueLiteral, Bool.false_eq_true, ite_false, output]
  refine ⟨?_, ?_⟩
  · change TraceOriginalSupport (formula parameters).clauses.size
      (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) (table.proofPrefix.steps ++ added.steps)
    rw [stepsEqual, List.append_nil]
    exact origins.supported
  · change ResultOrigin (formula parameters).clauses.size
      (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
      (table.proofPrefix.steps ++ added.steps) added.result.row.id
    rw [stepsEqual, List.append_nil, indexEqual]
    exact Or.inl (decoderZeroUnit_allowed rename side node shape table.proofPrefix)

theorem decoderInput_origins (rename : Nat → Fin v) (side : Side) (node : Fin parameters.decoder.nodeCount)
    (table : SourceDecoderEvaluation.Table (parameters := parameters) rename side cofactor assignment node.val)
    (channel : Fin parameters.channels) (shape : parameters.decoder.node node = .input channel)
    (origins : DecoderTableOrigins rename side table) :
    DecoderNodeStepOrigins rename side node table (SourceDecoderEvaluation.input rename side node table channel shape) := by
  let added := SourceDecoderEvaluation.input rename side node table channel shape
  have bit : nodeBit assignment node = assignment channel := parameters.decoder.eval_input assignment node channel shape
  have output : outputLiteral rename side node = qualifierLiteral rename side channel := by
    simp only [outputLiteral, decoderInput_output side node channel _ shape,
      ← decoderCursorAt_before, decoderCursorAt_qualifier, qualifierLiteral]
  have stepsEqual : added.steps = [] := rfl
  have indexEqual : added.result.row.id = (table.qualifiers channel).row.id := by
    unfold added SourceDecoderEvaluation.input
    dsimp only [id]
    with_unfolding_all
      apply SourceMixedSchedule.subclause_indices_mpr_id rfl
      simp only [bit, output]
  refine ⟨?_, ?_⟩
  · change TraceOriginalSupport (formula parameters).clauses.size
      (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) (table.proofPrefix.steps ++ added.steps)
    rw [stepsEqual, List.append_nil]
    exact origins.supported
  · change ResultOrigin (formula parameters).clauses.size
      (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
      (table.proofPrefix.steps ++ added.steps) added.result.row.id
    rw [stepsEqual, List.append_nil, indexEqual]
    exact origins.qualifiers channel

end Controller.NativeProof.Wrapper
