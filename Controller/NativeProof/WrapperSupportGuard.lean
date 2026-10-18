module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.WrapperSupportDisjunction

@[expose] public section

/-! Native guard summaries retain origins through killing and support erasure. -/
namespace Controller.NativeProof.Wrapper
open Controller.CNF Controller.Resolution Controller.Native Controller.Native.SourceController
open Controller.NativeProof.FoldProjection Controller.NativeProof.SourceFoldProjection
open Controller.NativeProof.SourceStageCongruence Controller.NativeProof.SourceStagePolarity
open Controller.NativeProof.SourceStageXor Controller.NativeProof.SourceFoldOccurrences
open Controller.NativeProof.SourceFoldProvenance Controller.NativeProof.SourceMismatchHandles
open Controller.NativeProof.SourceDecoderEvaluation Controller.NativeProof.SourceDecoderTraversal
open Controller.NativeProof.SourceDecoderClauses Controller.NativeProof.SourceDecoderSchedule
open Controller.NativeProof.SourceHealthyOne Controller.NativeProof.SupportRows
variable {parameters : Parameters} {v : Nat}

theorem supportNode_dite_origins (rename : Nat → Fin v) (node : Fin parameters.decoder.nodeCount)
    (table : SourceSupportSummaries.Table (parameters := parameters) rename node.val)
    (condition : Prop) [Decidable condition]
    (yes : condition → SourceSupportSummaries.NodeStep rename node table)
    (no : ¬condition → SourceSupportSummaries.NodeStep rename node table)
    (yesOrigins : ∀ proof, SupportNodeStepOrigins rename node table (yes proof))
    (noOrigins : ∀ proof, SupportNodeStepOrigins rename node table (no proof)) :
    SupportNodeStepOrigins rename node table (dite condition yes no) := by
  by_cases proof : condition
  · rw [dite_eq_left proof]; exact yesOrigins proof
  · rw [dite_eq_right proof]; exact noOrigins proof

theorem supportGuard_origins (rename : Nat → Fin v) (node : Fin parameters.decoder.nodeCount)
    (table : SourceSupportSummaries.Table (parameters := parameters) rename node.val) (child : Fin node.val)
    (labels : List (Fin parameters.channels)) (shape : parameters.decoder.node node = .guard child labels)
    (origins : SupportTableOrigins rename table) :
    SupportNodeStepOrigins rename node table (SourceSupportSummaries.guard rename node table child labels shape) := by
  let previous := SourceSupportSummaries.childEntry table child
  unfold SourceSupportSummaries.guard
  dsimp only [id]
  apply supportNode_dite_origins
  · intro empty
    subst labels
    have same : SourceSupportSummaries.output rename node = SourceSupportSummaries.output rename (parameters.decoder.childIndex node child) := by
      simpa [SourceSupportSummaries.output, outputLiteral, guardNode_output .faulty node child [] shape, guardCursorAt, childLiteral] using
        child_eq_output rename .faulty node child
    dsimp only [id]
    refine ⟨?_, ?_⟩
    · simpa only [SourceDecoderSchedule.PrefixOriginalSupport, SourcePrefix.extend, List.append_nil] using origins.prepared.supported
    · apply summary_indices_mpr_origin _ _ _ same rfl _
      simpa only [List.append_nil, SourceSupportSummaries.childEntry] using
        origins.entries (parameters.decoder.childIndex node child) child.isLt
  · intro empty
    let start := table.prepared.proofPrefix
    let tree := (nativeGuardTree rename .faulty node child labels shape).afterTrace start.state start.steps start.checked
    have two : 2 ≤ (guardInputs rename .faulty node child labels labels.length).length := by
      simp only [guardInputs, List.take_length, List.length_append, List.length_cons, List.length_nil, List.length_map]
      have positive := List.length_pos_iff.mpr empty
      omega
    let projected := nonunaryTreeInputs tree two
    let live := childLiteral rename .faulty node child
    have inputs : guardInputs rename .faulty node child labels labels.length =
        [live] ++ labels.map (fun channel => negate (SourceSupportSummaries.qualifier rename channel)) := by
      simp only [guardInputs, List.take_length, live, childLiteral]
      congr 1
      apply List.map_congr_left
      intro channel member
      exact congrArg negate (qualifierAt_eq rename .faulty node channel)
    have rootEq : mapLiteral rename (guardCursorAt .faulty node child labels labels.length).1 = SourceSupportSummaries.output rename node :=
      (congrArg (mapLiteral rename) (guardNode_output .faulty node child labels shape)).symm
    let childRow : AvailableSubclause projected.state [negate (SourceSupportSummaries.output rename node), SourceSupportSummaries.output rename (parameters.decoder.childIndex node child)] := by
      have member : live ∈ guardInputs rename .faulty node child labels labels.length := by rw [inputs]; simp
      simpa only [rootEq, live, child_eq_output, SourceSupportSummaries.output] using projected.results live member
    let blocked : ∀ channel ∈ labels, AvailableSubclause projected.state
        [negate (SourceSupportSummaries.output rename node), negate (SourceSupportSummaries.qualifier rename channel)] := by
      intro channel present
      have member : negate (SourceSupportSummaries.qualifier rename channel) ∈ guardInputs rename .faulty node child labels labels.length := by
        rw [inputs]
        exact List.mem_append_right _ (List.mem_map.mpr ⟨channel, present, rfl⟩)
      simpa only [rootEq] using projected.results _ member
    have treeOrigins := treeOriginals_afterTrace
      (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
      (nativeGuardTree rename .faulty node child labels shape) (nativeGuardTree_originals rename .faulty node child labels shape)
      start.state start.steps start.checked
    have projectedOrigins := SourceDecoderSchedule.nonunaryTreeInputs_prefixed_supported rename start tree two treeOrigins origins.prepared.supported
    have childOrigin : ResultOrigin (SourceController.formula parameters).clauses.size
        (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) (start.steps ++ projected.steps) childRow.row.id := by
      dsimp only [childRow]
      apply available_indices_mp_resultOrigin _ _ (start.steps ++ projected.steps)
        (by simp only [rootEq, live, child_eq_output, SourceSupportSummaries.output]) _
      exact projectedOrigins.2 _ _
    have blockedOrigins : ∀ channel member, ResultOrigin (SourceController.formula parameters).clauses.size
        (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) (start.steps ++ projected.steps) (blocked channel member).row.id := by
      intro channel member
      dsimp only [blocked]
      apply available_indices_mp_resultOrigin _ _ (start.steps ++ projected.steps) (by simp only [rootEq]) _
      exact projectedOrigins.2 _ _
    with_unfolding_all apply supportNode_dite_origins
    · intro killed
      let unit := FoldProjection.afterTrace (table.prepared.targetUnit killed.1) projected.state projected.steps projected.checked
      let killedRow := SupportRows.kill projected.state (cofactor (parameters := parameters) rename) (SourceSupportSummaries.output rename node)
        (SourceSupportSummaries.qualifier rename parameters.bridge.target) (blocked _ killed.2) unit
      have unitOrigin := resultOrigin_append_right _ _ start.steps projected.steps _ (origins.prepared.targetUnit killed.1)
      have actual := summaryKill_supported projected.state (cofactor (parameters := parameters) rename) (SourceSupportSummaries.output rename node)
        (SourceSupportSummaries.qualifier rename parameters.bridge.target) (blocked _ killed.2) unit
        (SourceController.formula parameters).clauses.size (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
        (start.steps ++ projected.steps) projectedOrigins.1 (SourceDecoderSchedule.allowed_native_count_le rename)
        (Nat.le_trans (SourceMixedSchedule.prefix_native_count_le rename start) (runSteps_lastId_le projected.checked))
        (blockedOrigins _ killed.2) unitOrigin
      refine ⟨?_, ?_⟩
      · simpa only [SourceDecoderSchedule.PrefixOriginalSupport, SourcePrefix.extend, start, tree, projected, blocked,
          unit, killedRow, List.append_assoc] using actual.1
      · unfold SummaryResultOrigin
        dsimp only [id]
        apply available_indices_mp_resultOrigin _ _ _ (by simp only [heads_empty]) _
        simpa only [start, tree, projected, blocked, unit, killedRow, List.append_assoc] using actual.2
    · intro killed
      let target := cofactor (parameters := parameters) rename ++ negate (SourceSupportSummaries.output rename node) :: heads previous.stored (SourceSupportSummaries.qualifier rename)
      let parent : AvailableSubclause projected.state (SourceSupportSummaries.output rename (parameters.decoder.childIndex node child) :: target) :=
        retarget childRow (by
          intro literal member
          simp only [target, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at member ⊢
          aesop)
      let expanded := SupportRows.expand projected.state (cofactor (parameters := parameters) rename) target
        (SourceSupportSummaries.output rename (parameters.decoder.childIndex node child)) (heads previous.stored (SourceSupportSummaries.qualifier rename))
        (previous.summary.afterTrace projected.state projected.steps projected.checked) parent
        (fun _ member => List.mem_append_left _ member) (fun _ member => List.mem_append_right _ (List.mem_cons_of_mem _ member))
      have previousOrigin := SummaryResultOrigin.afterTrace _ _ start.steps previous.summary
        (origins.entries (parameters.decoder.childIndex node child) child.isLt) projected.state projected.steps projected.checked
      have expandedOrigins := summaryExpand_supported projected.state (cofactor (parameters := parameters) rename) target
        (SourceSupportSummaries.output rename (parameters.decoder.childIndex node child)) (heads previous.stored (SourceSupportSummaries.qualifier rename))
        (previous.summary.afterTrace projected.state projected.steps projected.checked) parent
        (fun _ member => List.mem_append_left _ member) (fun _ member => List.mem_append_right _ (List.mem_cons_of_mem _ member))
        (SourceController.formula parameters).clauses.size (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
        (start.steps ++ projected.steps) projectedOrigins.1 (SourceDecoderSchedule.allowed_native_count_le rename)
        (Nat.le_trans (SourceMixedSchedule.prefix_native_count_le rename start) (runSteps_lastId_le projected.checked)) previousOrigin childOrigin
      let erased := SupportRows.eraseLabels expanded.state (cofactor (parameters := parameters) rename) (SourceSupportSummaries.output rename node)
        previous.stored (SourceSupportSummaries.qualifier rename) labels expanded.result
        (fun channel present => FoldProjection.afterTrace (blocked channel present) expanded.state expanded.steps expanded.checked)
      have erasedOrigins := summaryEraseLabels_supported expanded.state (cofactor (parameters := parameters) rename)
        (SourceSupportSummaries.output rename node) previous.stored (SourceSupportSummaries.qualifier rename) labels expanded.result
        (fun channel present => FoldProjection.afterTrace (blocked channel present) expanded.state expanded.steps expanded.checked)
        (SourceController.formula parameters).clauses.size (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
        ((start.steps ++ projected.steps) ++ expanded.steps) expandedOrigins.1 (SourceDecoderSchedule.allowed_native_count_le rename)
        (Nat.le_trans (Nat.le_trans (SourceMixedSchedule.prefix_native_count_le rename start) (runSteps_lastId_le projected.checked))
          (runSteps_lastId_le expanded.checked)) expandedOrigins.2
        (fun channel member => resultOrigin_append_right _ _ (start.steps ++ projected.steps) expanded.steps _ (blockedOrigins channel member))
      refine ⟨?_, ?_⟩
      · with_unfolding_all
          simpa only [SourceDecoderSchedule.PrefixOriginalSupport, SourcePrefix.extend, start, tree, projected, childRow, target, parent,
            previous, blocked, expanded, erased, live, id, List.append_assoc] using erasedOrigins.1
      · with_unfolding_all
          simpa only [SummaryResultOrigin, start, tree, projected, childRow, target, parent, previous, blocked, expanded, erased,
            live, id, List.append_assoc] using erasedOrigins.2

end Controller.NativeProof.Wrapper
