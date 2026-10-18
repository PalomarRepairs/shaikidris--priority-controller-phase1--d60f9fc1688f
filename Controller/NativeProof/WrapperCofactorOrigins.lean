module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.WrapperHealthyZeroQuery

@[expose] public section

/-! Complementary native cofactors are discharged by ordinary resolution. -/
namespace Controller.NativeProof.Wrapper
open Controller.CNF Controller.Resolution Controller.Native Controller.Native.SourceController
open Controller.NativeProof.FoldProjection Controller.NativeProof.SourceFoldProjection
open Controller.NativeProof.SourceStageCongruence Controller.NativeProof.SourceStagePolarity
open Controller.NativeProof.SourceStageXor Controller.NativeProof.SourceBusSchedule
open Controller.NativeProof.SourceBusAdvance Controller.NativeProof.SourceFoldProvenance
open Controller.NativeProof.SourceMismatchHandles Controller.NativeProof.SourceDecoderTraversal
variable {parameters : Parameters} {v : Nat}

theorem guardedOrigin_steps (rename : Nat → Fin v) (state : State v)
    (firstSteps secondSteps : List (Step v))
    (firstRun : runSteps (initialState (relabel rename (formula parameters))) firstSteps = some state)
    (secondRun : runSteps (initialState (relabel rename (formula parameters))) secondSteps = some state)
    (same : firstSteps = secondSteps) {context : Clause (Fin v)} {input output : Literal (Fin v)}
    (transfer : GuardedTransfer state context input output)
    (origin : SourceDecoderSchedule.GuardedTransferOrigin rename ⟨state, firstSteps, firstRun⟩ transfer) :
    SourceDecoderSchedule.GuardedTransferOrigin rename ⟨state, secondSteps, secondRun⟩ transfer := by
  cases same
  exact origin

theorem dischargeTransfer_origins (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename) (healthy faulty input output : Literal (Fin v))
    (one : GuardedTransfer prefixState.state [negate healthy, negate faulty] input output)
    (zero : GuardedTransfer prefixState.state [negate healthy, faulty] input output)
    (unit : AvailableSubclause prefixState.state [healthy])
    (supported : SourceDecoderSchedule.PrefixOriginalSupport rename prefixState)
    (oneOrigin : SourceDecoderSchedule.GuardedTransferOrigin rename prefixState one)
    (zeroOrigin : SourceDecoderSchedule.GuardedTransferOrigin rename prefixState zero)
    (unitOrigin : DecoderRowOrigin rename prefixState unit) :
    SourceDecoderSchedule.GuardedProjectionOriginalSupport rename prefixState
      (Compiler.dischargeTransfer prefixState.state healthy faulty input output one zero unit) := by
  cases one with
  | identity same =>
    simpa only [Compiler.dischargeTransfer, SourceDecoderSchedule.GuardedProjectionOriginalSupport,
      SourceDecoderSchedule.GuardedTransferOrigin, SourcePrefix.extend, SourceDecoderSchedule.PrefixOriginalSupport,
      List.append_nil, and_true] using supported
  | derived first =>
    cases zero with
    | identity same =>
      simpa only [Compiler.dischargeTransfer, SourceDecoderSchedule.GuardedProjectionOriginalSupport,
        SourceDecoderSchedule.GuardedTransferOrigin, SourcePrefix.extend, SourceDecoderSchedule.PrefixOriginalSupport,
        List.append_nil, and_true] using supported
    | derived second =>
      let target := [negate input, output]
      let a : AvailableSubclause prefixState.state ([negate faulty] ++ [negate healthy] ++ target) :=
        retarget first (by intro l h; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h ⊢; aesop)
      let b : AvailableSubclause prefixState.state ([faulty] ++ target ++ [negate healthy]) :=
        retarget second (by intro l h; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h ⊢; aesop)
      let joined := longMerge prefixState.state faulty ([negate healthy] ++ target) (target ++ [negate healthy]) a b
      let row : AvailableSubclause joined.state ([negate healthy] ++ target) :=
        retarget (longMerge_result _ _ _ _ _ _) (by
          intro l h
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h ⊢
          aesop)
      let held := afterTrace unit joined.state joined.steps (longMerge_run _ _ _ _ _ _)
      let final := longMerge joined.state healthy target [] row held
      have firstOrigins := SourceMixedSchedule.longMerge_supported (formula parameters).clauses.size
        (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) prefixState.steps prefixState.state
        faulty ([negate healthy] ++ target) (target ++ [negate healthy]) a b supported
        (SourceDecoderSchedule.allowed_native_count_le rename) (SourceMixedSchedule.prefix_native_count_le rename prefixState)
        oneOrigin zeroOrigin
      have heldOrigin := resultOrigin_append_right _ _ prefixState.steps joined.steps unit.row.id unitOrigin
      have finalOrigins := SourceMixedSchedule.longMerge_supported (formula parameters).clauses.size
        (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) (prefixState.steps ++ joined.steps) joined.state
        healthy target [] row held firstOrigins.1 (SourceDecoderSchedule.allowed_native_count_le rename)
        (Nat.le_trans (SourceMixedSchedule.prefix_native_count_le rename prefixState) (runSteps_lastId_le (longMerge_run _ _ _ _ _ _)))
        firstOrigins.2 heldOrigin
      simpa only [SourceDecoderSchedule.GuardedProjectionOriginalSupport, SourceDecoderSchedule.PrefixOriginalSupport,
        SourceDecoderSchedule.GuardedTransferOrigin, Compiler.dischargeTransfer, id, target, a, b, joined, row, held, final,
        retarget, SourcePrefix.extend, List.append_assoc] using finalOrigins

theorem dischargePair_origins (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename) (healthy faulty left right : Literal (Fin v))
    (one : DirectionPair prefixState.state [negate healthy, negate faulty] left right)
    (zero : DirectionPair prefixState.state [negate healthy, faulty] left right)
    (unit : AvailableSubclause prefixState.state [healthy])
    (supported : SourceDecoderSchedule.PrefixOriginalSupport rename prefixState)
    (oneOrigins : SourceDecoderSchedule.DirectionPairOrigin rename prefixState one)
    (zeroOrigins : SourceDecoderSchedule.DirectionPairOrigin rename prefixState zero)
    (unitOrigin : DecoderRowOrigin rename prefixState unit) :
    SourceDecoderSchedule.PairedProjectionOriginalSupport rename prefixState
      (Compiler.dischargePair prefixState.state healthy faulty left right one zero unit) := by
  let first := Compiler.dischargeTransfer prefixState.state healthy faulty left right one.forward zero.forward unit
  let current := prefixState.extend first.state first.steps first.checked
  have firstOrigins := dischargeTransfer_origins rename prefixState healthy faulty left right one.forward zero.forward unit
    supported oneOrigins.1 zeroOrigins.1 unitOrigin
  have oneBack := SourceDecoderSchedule.GuardedTransferOrigin.afterTrace rename prefixState one.backward oneOrigins.2 first.state first.steps first.checked
  have zeroBack := SourceDecoderSchedule.GuardedTransferOrigin.afterTrace rename prefixState zero.backward zeroOrigins.2 first.state first.steps first.checked
  have unitBack := resultOrigin_append_right _ _ prefixState.steps first.steps unit.row.id unitOrigin
  let second := Compiler.dischargeTransfer first.state healthy faulty right left
    (one.backward.afterTrace first.state first.steps first.checked)
    (zero.backward.afterTrace first.state first.steps first.checked) (afterTrace unit first.state first.steps first.checked)
  have secondOrigins := dischargeTransfer_origins rename current healthy faulty right left
    (one.backward.afterTrace first.state first.steps first.checked)
    (zero.backward.afterTrace first.state first.steps first.checked) (afterTrace unit first.state first.steps first.checked)
    firstOrigins.1 oneBack zeroBack unitBack
  have forwardOrigin := SourceDecoderSchedule.GuardedTransferOrigin.afterTrace rename current first.result firstOrigins.2 second.state second.steps second.checked
  unfold SourceDecoderSchedule.PairedProjectionOriginalSupport Compiler.dischargePair
  dsimp only [id]
  refine ⟨?_, ?_, ?_⟩
  · simpa only [current, first, second, SourceDecoderSchedule.PrefixOriginalSupport,
      SourcePrefix.extend, List.append_assoc] using secondOrigins.1
  · change SourceDecoderSchedule.GuardedTransferOrigin rename
      (prefixState.extend second.state (first.steps ++ second.steps) _) (first.result.afterTrace second.state second.steps second.checked)
    exact guardedOrigin_steps rename second.state _ _ _ _ (List.append_assoc _ _ _) _ forwardOrigin
  · change SourceDecoderSchedule.GuardedTransferOrigin rename
      (prefixState.extend second.state (first.steps ++ second.steps) _) second.result
    exact guardedOrigin_steps rename second.state _ _ _ _ (List.append_assoc _ _ _) _ secondOrigins.2

end Controller.NativeProof.Wrapper
