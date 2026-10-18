module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.WrapperHealthyPreparation
public import Controller.NativeProof.WrapperCaseProvenance

@[expose] public section

/-! Retained controller provenance through healthy mask advancement. -/
namespace Controller.NativeProof.Wrapper
open Controller.CNF Controller.Resolution Controller.Native Controller.Native.SourceController
open Controller.NativeProof.FoldProjection Controller.NativeProof.SourceFoldProjection
open Controller.NativeProof.SourceStageCongruence Controller.NativeProof.SourceStagePolarity
open Controller.NativeProof.SourceStageXor Controller.NativeProof.SourceBusSchedule
open Controller.NativeProof.SourceBusAdvance Controller.NativeProof.SourceFoldProvenance
open Controller.NativeProof.SourceHealthyMasks Controller.NativeProof.SourceMixedSchedule
open Controller.NativeProof.SourceMismatchHandles
variable {parameters : Parameters} {v : Nat}

theorem laterMaskNativeRows_origins (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename) (side : Side)
    (position : Fin (SourceFoldOccurrences.laterBuses (parameters := parameters)).length)
    (channel : Fin parameters.channels) :
    ControllerOrigins.XorRowsOrigins rename prefixState
      (laterMaskNativeRows rename side position channel prefixState) := by
  exact ⟨Or.inl (laterMaskRows_allowed rename side position channel ⟨0, by change 0 < 4; decide⟩),
    Or.inl (laterMaskRows_allowed rename side position channel ⟨1, by change 1 < 4; decide⟩),
    Or.inl (laterMaskRows_allowed rename side position channel ⟨2, by change 2 < 4; decide⟩),
    Or.inl (laterMaskRows_allowed rename side position channel ⟨3, by change 3 < 4; decide⟩)⟩

theorem laterAbsentNativeRows_origins (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename) (side : Side)
    (position : Fin (SourceFoldOccurrences.laterBuses (parameters := parameters)).length)
    (channel : Fin parameters.channels) :
    ControllerOrigins.NotRowsOrigins rename prefixState
      (laterAbsentNativeRows rename side position channel prefixState) := by
  exact ⟨Or.inl (laterAbsentRows_allowed rename side position channel ⟨0, by change 0 < 2; decide⟩),
    Or.inl (laterAbsentRows_allowed rename side position channel ⟨1, by change 1 < 2; decide⟩)⟩

theorem directionPair_same_steps_origins (rename : Nat → Fin v)
    (before after : SourcePrefix (parameters := parameters) rename)
    (stateEqual : before.state = after.state) (stepsEqual : before.steps = after.steps)
    (pair : DirectionPair before.state cofactor input output)
    (origins : ControllerOrigins.DirectionPairOrigin rename before pair) :
    ControllerOrigins.DirectionPairOrigin rename after (stateEqual ▸ pair) := by
  cases before with
  | mk firstState firstSteps firstChecked =>
    cases after with
    | mk secondState secondSteps secondChecked =>
      cases stateEqual
      cases stepsEqual
      exact origins

structure HealthyMaskStepOrigins (rename : Nat → Fin v)
    (position : Fin (SourceFoldOccurrences.laterBuses (parameters := parameters)).length)
    (start : SourceHealthyMasks.Table (parameters := parameters) rename position.val)
    (mask : SourceHealthyMasks.MaskStep rename position start) : Prop where
  supported : SourceMixedSchedule.PrefixOriginalSupport rename
    (start.proofPrefix.extend mask.state mask.steps mask.checked)
  result : ControllerRowOrigin rename (start.proofPrefix.extend mask.state mask.steps mask.checked) mask.result
  pair : ControllerOrigins.DirectionPairOrigin rename
    (start.proofPrefix.extend mask.state mask.steps mask.checked) mask.pair

theorem notRows_indices_mp_origins (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    {beforeInput afterInput beforeOutput afterOutput : Literal (Fin v)}
    (inputEqual : beforeInput = afterInput) (outputEqual : beforeOutput = afterOutput)
    (typeEqual : NotRows prefixState.state beforeInput beforeOutput =
      NotRows prefixState.state afterInput afterOutput)
    (value : NotRows prefixState.state beforeInput beforeOutput)
    (origins : ControllerOrigins.NotRowsOrigins rename prefixState value) :
    ControllerOrigins.NotRowsOrigins rename prefixState (Eq.mp typeEqual value) := by
  subst afterInput
  subst afterOutput
  have same : typeEqual = rfl := Subsingleton.elim _ _
  rw [same]
  exact origins

theorem healthyCurrentTargetMask_origins (rename : Nat → Fin v)
    (position : Fin (SourceFoldOccurrences.laterBuses (parameters := parameters)).length)
    (table : SourceHealthyMasks.Table (parameters := parameters) rename position.val)
    (drive : parameters.drive = true) (origins : HealthyMaskOrigins rename table) :
    HealthyMaskStepOrigins rename position table
      (SourceHealthyMasks.currentTargetMask rename position table drive) := by
  let term := SourceHealthyMasks.targetTerm rename position table drive
  let next := table.afterTrace term.state term.steps term.checked
  let zeros := SourceHealthyMasks.collectOtherTerms rename position next (List.finRange parameters.channels)
  let flag := SourceHealthyMasks.targetFlag rename position zeros
  have termOrigins := healthyTargetTerm_origins rename position table drive origins
  have nextOrigins := HealthyMaskOrigins.afterTrace rename table origins term.state term.steps term.checked termOrigins.1
  have zerosOrigins := collectOtherTerms_origins rename position next (List.finRange parameters.channels) nextOrigins
  have flagOrigins := healthyTargetFlag_origins rename position zeros zerosOrigins
  have zerosRun : runSteps term.state zeros.steps = some zeros.table.proofPrefix.state := zeros.checked
  have termRun : runSteps term.state (zeros.steps ++ flag.steps) = some flag.state := by
    rw [runSteps_append, zerosRun]
    exact flag.checked
  let termNow := term.pair.afterTrace flag.state (zeros.steps ++ flag.steps) termRun
  let termPrefix := table.proofPrefix.extend term.state term.steps term.checked
  let flagPrefix := zeros.table.proofPrefix.extend flag.state flag.steps flag.checked
  let carriedPrefix := termPrefix.extend flag.state (zeros.steps ++ flag.steps) termRun
  have nextSteps : next.proofPrefix.steps = table.proofPrefix.steps ++ term.steps := rfl
  have termCarried := ControllerOrigins.DirectionPairOrigin.afterTrace rename termPrefix
    term.pair termOrigins.2 flag.state (zeros.steps ++ flag.steps) termRun
  have carriedSteps : carriedPrefix.steps = flagPrefix.steps := by
    dsimp only [carriedPrefix, flagPrefix, termPrefix, SourcePrefix.extend]
    rw [zerosOrigins.sameSteps, nextSteps]
    simp only [List.append_assoc]
    rfl
  have termNowOrigins := directionPair_same_steps_origins rename carriedPrefix flagPrefix rfl
    carriedSteps termNow termCarried
  let paired := TreeUnits.composePairs flag.state (context (parameters := parameters) rename) flag.pair termNow
  have pairedOrigins := ControllerOrigins.composePairs_supported rename flagPrefix
    (context (parameters := parameters) rename) (laterFlagOutput rename .healthy position)
    (laterTermOutput rename .healthy position parameters.bridge.target) (targetRequest rename position)
    flag.pair termNow flagOrigins.1 flagOrigins.2 termNowOrigins
  have pairedRun : runSteps zeros.table.proofPrefix.state (flag.steps ++ paired.steps) = some paired.state := by
    rw [runSteps_append, flag.checked]
    exact paired.checked
  let prefixState := zeros.table.proofPrefix.extend paired.state (flag.steps ++ paired.steps) pairedRun
  let composePrefix := flagPrefix.extend paired.state paired.steps paired.checked
  have composeSteps : composePrefix.steps = prefixState.steps := List.append_assoc ..
  have composeSupported : SourceMixedSchedule.PrefixOriginalSupport rename prefixState := by
    change TraceOriginalSupport (formula parameters).clauses.size
      (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename) prefixState.steps
    rw [← composeSteps]
    exact pairedOrigins.1
  have composePairOrigins := directionPair_same_steps_origins rename composePrefix prefixState rfl
    composeSteps paired.pair pairedOrigins.2
  have flagCarried := ControllerOrigins.DirectionPairOrigin.afterTrace rename flagPrefix flag.pair flagOrigins.2
    paired.state paired.steps paired.checked
  have flagNowOrigins := directionPair_same_steps_origins rename composePrefix prefixState rfl
    composeSteps (flag.pair.afterTrace paired.state paired.steps paired.checked) flagCarried
  let equal : DirectionPair paired.state (context (parameters := parameters) rename)
      (laterMaskFlag rename .healthy position parameters.bridge.target)
      (laterAbsentInput rename .healthy position parameters.bridge.target) := by
    simpa only [laterMaskFlag_eq_flagOutput, laterAbsentInput_eq_termOutput] using
      flag.pair.afterTrace paired.state paired.steps paired.checked
  have equalOrigins : ControllerOrigins.DirectionPairOrigin rename prefixState equal := by
    dsimp only [equal]
    apply directionPair_indices_mp_origins rename prefixState rfl
      (laterMaskFlag_eq_flagOutput rename .healthy position parameters.bridge.target).symm
      (laterAbsentInput_eq_termOutput rename .healthy position parameters.bridge.target).symm _ _
    exact flagNowOrigins
  let xorRows := laterMaskNativeRows rename .healthy position parameters.bridge.target prefixState
  let notRows := laterAbsentNativeRows rename .healthy position parameters.bridge.target prefixState
  let negRows : NotRows paired.state
      (laterAbsentInput rename .healthy position parameters.bridge.target)
      (laterMaskAbsent rename .healthy position parameters.bridge.target) := by
    simpa only [laterMaskAbsent_eq_absentOutput, prefixState, SourcePrefix.extend] using notRows
  have negOrigins : ControllerOrigins.NotRowsOrigins rename prefixState negRows := by
    dsimp only [negRows]
    apply notRows_indices_mp_origins rename prefixState rfl
      (laterMaskAbsent_eq_absentOutput rename .healthy position parameters.bridge.target).symm _ _
    exact laterAbsentNativeRows_origins rename prefixState .healthy position parameters.bridge.target
  let mask := XorUnits.complementary paired.state (context (parameters := parameters) rename)
    _ _ _ _ xorRows negRows equal
  have maskOrigins := ControllerOrigins.xorComplementary_supported rename prefixState
    (context (parameters := parameters) rename) _ _ _ _ xorRows negRows equal composeSupported
    (laterMaskNativeRows_origins rename prefixState .healthy position parameters.bridge.target) negOrigins equalOrigins
  let maskPrefix := prefixState.extend mask.state mask.steps mask.checked
  let actual := SourceHealthyMasks.currentTargetMask rename position table drive
  let final := table.proofPrefix.extend actual.state actual.steps actual.checked
  have actualSteps : actual.steps = (((term.steps ++ zeros.steps) ++ flag.steps) ++ paired.steps) ++ mask.steps := rfl
  have same : maskPrefix.steps = final.steps := by
    dsimp only [maskPrefix, prefixState, final, SourcePrefix.extend]
    rw [zerosOrigins.sameSteps, nextSteps, actualSteps]
    simp only [List.append_assoc]
    rfl
  have pairCarried := ControllerOrigins.DirectionPairOrigin.afterTrace rename prefixState paired.pair
    composePairOrigins mask.state mask.steps mask.checked
  refine ⟨?_, ?_, ?_⟩
  · change TraceOriginalSupport (formula parameters).clauses.size
      (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename) final.steps
    rw [← same]
    exact maskOrigins.1
  · have indexEqual : actual.result.row.id = mask.result.row.id := by rfl
    unfold ControllerRowOrigin
    change ResultOrigin (formula parameters).clauses.size
      (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename) final.steps actual.result.row.id
    rw [indexEqual, ← same]
    exact maskOrigins.2
  · have result := directionPair_same_steps_origins rename maskPrefix final rfl same
      (paired.pair.afterTrace mask.state mask.steps mask.checked) pairCarried
    exact result

theorem healthyAdvance_origins (rename : Nat → Fin v)
    (position : Fin (SourceFoldOccurrences.laterBuses (parameters := parameters)).length)
    (table : SourceHealthyMasks.Table (parameters := parameters) rename position.val)
    (drive : parameters.drive = true) (origins : HealthyMaskOrigins rename table) :
    HealthyMaskOrigins rename (SourceHealthyMasks.advance rename position table drive) := by
  let mask := SourceHealthyMasks.currentTargetMask rename position table drive
  let next := table.afterTrace mask.state mask.steps mask.checked
  have maskOrigins := healthyCurrentTargetMask_origins rename position table drive origins
  have nextOrigins := HealthyMaskOrigins.afterTrace rename table origins mask.state mask.steps mask.checked maskOrigins.supported
  refine ⟨maskOrigins.supported, nextOrigins.firstZero, nextOrigins.firstAbsent, ?_, ?_⟩
  · intro bus member
    by_cases same : bus = (SourceFoldOccurrences.laterBuses (parameters := parameters))[position.val]
    · subst bus
      have indexEqual :
          ((SourceHealthyMasks.advance rename position table drive).targetMasks
            (SourceFoldOccurrences.laterBuses (parameters := parameters))[position.val] member).row.id = mask.result.row.id := by
        unfold SourceHealthyMasks.advance
        dsimp only [id]
        simp only [SourceMixedSchedule.subclause_dite_id, dite_true]
        with_unfolding_all
          apply SourceMixedSchedule.subclause_indices_mpr_id rfl
          simp only [stagesBefore_current_mask]
      unfold ControllerRowOrigin
      rw [indexEqual]
      exact maskOrigins.result
    · have old : bus ∈ parameters.firstBus :: (SourceFoldOccurrences.laterBuses (parameters := parameters)).take position.val := by
        rw [List.take_succ_eq_append_getElem position.isLt] at member
        simp only [List.mem_cons, List.mem_append, List.mem_singleton] at member ⊢
        aesop
      have indexEqual :
          ((SourceHealthyMasks.advance rename position table drive).targetMasks bus member).row.id =
          (next.targetMasks bus old).row.id := by
        unfold SourceHealthyMasks.advance
        dsimp only [id]
        simp only [SourceMixedSchedule.subclause_dite_id, dite_eq_right same]
        with_unfolding_all
          apply Eq.trans (SourceMixedSchedule.subclause_indices_mpr_id rfl
            (by simp only [stagesBefore_succ]) _ _)
          apply SourceMixedSchedule.subclause_indices_mpr_id rfl
          simp only [laterBus_mask_other .healthy .healthy _ bus parameters.bridge.target same]
      unfold ControllerRowOrigin
      rw [indexEqual]
      exact nextOrigins.targetMasks bus old
  · intro query before
    by_cases same : query = position
    · subst query
      have pairEqual : (SourceHealthyMasks.advance rename position table drive).flagRequests position before =
          mask.pair := by
        unfold SourceHealthyMasks.advance
        dsimp only [id]
        exact dite_eq_left rfl
      rw [pairEqual]
      exact maskOrigins.pair
    · have earlier : query.val < position.val := by
        have ne : query.val ≠ position.val := fun equal => same (Fin.ext equal)
        omega
      have pairEqual : (SourceHealthyMasks.advance rename position table drive).flagRequests query before =
          next.flagRequests query earlier := by
        unfold SourceHealthyMasks.advance
        dsimp only [id]
        rw [dite_eq_right same]
      rw [pairEqual]
      exact nextOrigins.flagRequests query earlier

theorem healthyBuildPrefix_origins (rename : Nat → Fin v) (drive : parameters.drive = true)
    (count : Nat) (bound : count ≤ (SourceFoldOccurrences.laterBuses (parameters := parameters)).length) :
    HealthyMaskOrigins rename (SourceHealthyMasks.buildPrefix rename drive count bound) := by
  induction count with
  | zero => exact healthyMaskInitial_origins rename drive
  | succ count ih =>
    exact healthyAdvance_origins rename ⟨count, by omega⟩
      (SourceHealthyMasks.buildPrefix rename drive count (by omega)) drive (ih (by omega))

theorem healthyAllMasks_origins (rename : Nat → Fin v) (drive : parameters.drive = true) :
    HealthyMaskOrigins rename (SourceHealthyMasks.allMasks (parameters := parameters) rename drive) :=
  healthyBuildPrefix_origins rename drive _ (Nat.le_refl _)

end Controller.NativeProof.Wrapper
