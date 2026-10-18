module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.WrapperDecoderBranches

@[expose] public section

/-! Guard-chain evaluation retains each live-child and blocking-label origin. -/
namespace Controller.NativeProof.Wrapper
open Controller.CNF Controller.Resolution Controller.Native Controller.Native.SourceController
open Controller.NativeProof.FoldProjection Controller.NativeProof.SourceFoldProjection
open Controller.NativeProof.SourceStageCongruence Controller.NativeProof.SourceStagePolarity
open Controller.NativeProof.SourceStageXor Controller.NativeProof.SourceBusSchedule
open Controller.NativeProof.SourceFoldProvenance Controller.NativeProof.SourceMismatchHandles
open Controller.NativeProof.SourceDecoderEvaluation Controller.NativeProof.SourceDecoderTraversal
open Controller.NativeProof.SourceDecoderClauses Controller.NativeProof.SourceDecoderSchedule
variable {parameters : Parameters} {v : Nat}

theorem decoderGuard_origins (rename : Nat → Fin v) (side : Side) (node : Fin parameters.decoder.nodeCount)
    (table : SourceDecoderEvaluation.Table (parameters := parameters) rename side cofactor assignment node.val)
    (child : Fin node.val) (labels : List (Fin parameters.channels))
    (shape : parameters.decoder.node node = .guard child labels) (origins : DecoderTableOrigins rename side table) :
    DecoderNodeStepOrigins rename side node table (SourceDecoderEvaluation.guard rename side node table child labels shape) := by
  let tree := (nativeGuardTree rename side node child labels shape).afterTrace
    table.proofPrefix.state table.proofPrefix.steps table.proofPrefix.checked
  let live := childLiteral rename side node child
  let blocked := fun channel => negate (mapLiteral rename
    ((SourceFoldOccurrences.decoderPositionBefore side node).slots (.internal (.qualifier side channel))))
  have inputs : guardInputs rename side node child labels labels.length = [live] ++ labels.map blocked := by
    simp only [guardInputs, List.take_length, live, blocked, childLiteral]
  have output : outputLiteral rename side node = mapLiteral rename (guardCursorAt side node child labels labels.length).1 := by
    simp only [outputLiteral, guardNode_output side node child labels shape]
  have bits : nodeBit assignment node =
      (nodeBit assignment (parameters.decoder.childIndex node child) && !(labels.any assignment)) :=
    parameters.decoder.eval_guard assignment node child labels shape
  have originals := treeOriginals_afterTrace
    (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
    (nativeGuardTree rename side node child labels shape)
    (nativeGuardTree_originals rename side node child labels shape)
    table.proofPrefix.state table.proofPrefix.steps table.proofPrefix.checked
  unfold SourceDecoderEvaluation.guard
  dsimp only [id]
  apply nodeStep_dite_origins
  · intro active
    have conditions : nodeBit assignment (parameters.decoder.childIndex node child) = true ∧ labels.any assignment = false := by
      rw [bits] at active
      simpa only [Bool.and_eq_true, Bool.not_eq_true'] using active
    let liveUnit : AvailableSubclause table.proofPrefix.state (cofactor ++ [live]) := by
      simpa only [conditions.1, valueLiteral, ite_true] using childUnit rename side node table child
    have liveId : liveUnit.row.id = (childUnit rename side node table child).row.id := by
      dsimp only [liveUnit]
      apply SourceMixedSchedule.subclause_cast_id
      simp only [conditions.1, valueLiteral, ite_true, live]
    have liveOrigin : ResultOrigin (formula parameters).clauses.size
        (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) table.proofPrefix.steps liveUnit.row.id := by
      rw [liveId]
      exact decoderChildUnit_origins rename side node table origins child
    let rows : ∀ channel ∈ labels, AvailableSubclause table.proofPrefix.state (cofactor ++ [blocked channel]) :=
      fun channel present => by
        have falseBit : assignment channel = false :=
          Bool.eq_false_of_not_eq_true (List.any_eq_false.mp conditions.2 channel present)
        simpa only [falseBit, valueLiteral, Bool.false_eq_true, ite_false, blocked] using
          SourceDecoderEvaluation.qualifierAt rename side node table channel
    have rowOrigins : ∀ channel present, ResultOrigin (formula parameters).clauses.size
        (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) table.proofPrefix.steps (rows channel present).row.id := by
      intro channel present
      have falseBit : assignment channel = false :=
        Bool.eq_false_of_not_eq_true (List.any_eq_false.mp conditions.2 channel present)
      have indexEqual : (rows channel present).row.id = (SourceDecoderEvaluation.qualifierAt rename side node table channel).row.id := by
        dsimp only [rows]
        apply SourceMixedSchedule.subclause_cast_id
        simp only [falseBit, valueLiteral, Bool.false_eq_true, ite_false, blocked]
      rw [indexEqual]
      exact decoderQualifierAt_origins rename side node table origins channel
    let units : ∀ leaf ∈ guardInputs rename side node child labels labels.length,
        AvailableSubclause table.proofPrefix.state (cofactor ++ [leaf]) := by
      intro leaf member
      rw [inputs] at member
      by_cases same : leaf = live
      · subst leaf; exact liveUnit
      · exact TreeUnits.mappedUnit labels blocked cofactor rows leaf ((List.mem_cons.mp member).resolve_left same)
    have unitOrigins : ∀ leaf member, ResultOrigin (formula parameters).clauses.size
        (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) table.proofPrefix.steps (units leaf member).row.id := by
      intro leaf member
      by_cases same : leaf = live
      · subst leaf
        simpa only [units, SourceMixedSchedule.subclause_dite_id, dite_eq_left rfl, dite_true] using liveOrigin
      · have listed : leaf ∈ labels.map blocked := by rw [inputs] at member; exact (List.mem_cons.mp member).resolve_left same
        have mapped := mappedUnit_resultOrigin table.proofPrefix.state labels blocked cofactor rows _ _ table.proofPrefix.steps
          rowOrigins leaf listed
        simpa only [units, SourceMixedSchedule.subclause_dite_id, dite_eq_right same] using mapped
    let forced := TreeUnits.force tree cofactor units
    have actual := Wrapper.tree_force_supported rename table.proofPrefix tree cofactor units origins.supported originals unitOrigins
    refine ⟨actual.1, ?_⟩
    change ResultOrigin (formula parameters).clauses.size
      (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) (table.proofPrefix.steps ++ forced.steps) _
    apply available_indices_mpr_resultOrigin _ _ (table.proofPrefix.steps ++ forced.steps)
      (by simp only [active, valueLiteral, ite_true, output]) _
    exact actual.2
  · intro active
    have inactive : nodeBit assignment node = false := Bool.eq_false_of_not_eq_true active
    apply nodeStep_dite_origins
    · intro childFalse
      have member : live ∈ guardInputs rename side node child labels labels.length := by rw [inputs]; simp
      let unit : AvailableSubclause table.proofPrefix.state (cofactor ++ [negate live]) := by
        simpa only [childFalse, valueLiteral, Bool.false_eq_true, ite_false] using childUnit rename side node table child
      have unitId : unit.row.id = (childUnit rename side node table child).row.id := by
        dsimp only [unit]
        apply SourceMixedSchedule.subclause_cast_id
        simp only [childFalse, valueLiteral, Bool.false_eq_true, ite_false, live]
      have unitOrigin : ResultOrigin (formula parameters).clauses.size
          (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) table.proofPrefix.steps unit.row.id := by
        rw [unitId]
        exact decoderChildUnit_origins rename side node table origins child
      let denied := TreeUnits.deny tree cofactor live member unit
      have actual := Wrapper.tree_deny_supported rename table.proofPrefix tree cofactor live member unit origins.supported originals unitOrigin
      refine ⟨actual.1, ?_⟩
      change ResultOrigin (formula parameters).clauses.size
        (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) (table.proofPrefix.steps ++ denied.steps) _
      apply available_indices_mpr_resultOrigin _ _ (table.proofPrefix.steps ++ denied.steps)
        (by simp only [inactive, valueLiteral, Bool.false_eq_true, ite_false, output]) _
      exact actual.2
    · intro childFalse
      have labelTrue : labels.any assignment = true := by
        have childTrue := Bool.eq_true_of_not_eq_false childFalse
        rw [bits, childTrue] at inactive
        simpa using inactive
      let selected := pick labels (fun channel => assignment channel = true) (List.any_eq_true.mp labelTrue)
      let leaf := blocked selected.val
      have member : leaf ∈ guardInputs rename side node child labels labels.length := by
        rw [inputs]
        exact List.mem_append_right _ (List.mem_map.mpr ⟨selected.val, selected.property.1, rfl⟩)
      let unit : AvailableSubclause table.proofPrefix.state (cofactor ++ [negate leaf]) := by
        simpa only [selected.property.2, valueLiteral, ite_true, leaf, blocked, negate_negate] using
          SourceDecoderEvaluation.qualifierAt rename side node table selected.val
      have unitId : unit.row.id = (SourceDecoderEvaluation.qualifierAt rename side node table selected.val).row.id := by
        dsimp only [unit]
        with_unfolding_all
          apply Eq.trans (SourceMixedSchedule.subclause_indices_mpr_id rfl
            (by simp only [leaf, blocked, negate_negate]) _ _)
          apply SourceMixedSchedule.subclause_indices_cast_id rfl
          simp only [selected.property.2, valueLiteral, ite_true]
      have unitOrigin : ResultOrigin (formula parameters).clauses.size
          (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) table.proofPrefix.steps unit.row.id := by
        rw [unitId]
        exact decoderQualifierAt_origins rename side node table origins selected.val
      let denied := TreeUnits.deny tree cofactor leaf member unit
      have actual := Wrapper.tree_deny_supported rename table.proofPrefix tree cofactor leaf member unit origins.supported originals unitOrigin
      refine ⟨actual.1, ?_⟩
      change ResultOrigin (formula parameters).clauses.size
        (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) (table.proofPrefix.steps ++ denied.steps) _
      apply available_indices_mpr_resultOrigin _ _ (table.proofPrefix.steps ++ denied.steps)
        (by simp only [inactive, valueLiteral, Bool.false_eq_true, ite_false, output]) _
      exact actual.2

end Controller.NativeProof.Wrapper
