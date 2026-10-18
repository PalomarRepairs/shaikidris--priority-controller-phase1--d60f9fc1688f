module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.WrapperSupportOrigins

@[expose] public section

/-! Empty, aliased, and shared disjunction summaries retain native origins. -/
namespace Controller.NativeProof.Wrapper
open Controller.CNF Controller.Resolution Controller.Native Controller.Native.SourceController
open Controller.NativeProof.FoldProjection Controller.NativeProof.SourceFoldProjection
open Controller.NativeProof.SourceStageCongruence Controller.NativeProof.SourceStagePolarity
open Controller.NativeProof.SourceStageXor Controller.NativeProof.SourceFoldOccurrences
open Controller.NativeProof.SourceFoldProvenance Controller.NativeProof.SourceMismatchHandles
open Controller.NativeProof.SourceDecoderEvaluation Controller.NativeProof.SourceDecoderTraversal
open Controller.NativeProof.SourceDecoderSchedule Controller.NativeProof.SourceHealthyOne Controller.NativeProof.SupportRows
variable {parameters : Parameters} {v : Nat}

theorem supportDisjunction_origins (rename : Nat → Fin v) (node : Fin parameters.decoder.nodeCount)
    (table : SourceSupportSummaries.Table (parameters := parameters) rename node.val)
    (children : List (Fin node.val)) (shape : parameters.decoder.node node = .disj children)
    (origins : SupportTableOrigins rename table) :
    SupportNodeStepOrigins rename node table (SourceSupportSummaries.disjunction rename node table children shape) := by
  cases children with
  | nil =>
    have same : SourceSupportSummaries.output rename node = mapLiteral rename (decoderLiveAndOutput .faulty node) := by
      rw [SourceSupportSummaries.output, outputLiteral, decoderDisjunction_output .faulty node [] shape]
      simp only [decoderDisjunctionOutput, SourceSerialFold.allocate, List.map_nil, decoderLiveAndOutput]
    unfold SourceSupportSummaries.disjunction
    dsimp only [id]
    refine ⟨?_, ?_⟩
    · simpa only [SourceDecoderSchedule.PrefixOriginalSupport, SourcePrefix.extend, List.append_nil] using origins.prepared.supported
    · unfold SummaryResultOrigin
      dsimp only [id]
      rw [List.append_nil]
      apply available_indices_mpr_resultOrigin _ _ table.prepared.proofPrefix.steps (by simp only [heads_empty, same]) _
      exact Or.inl (decoderEmptyDisjunctionUnit_allowed rename .faulty node shape table.prepared.proofPrefix)
  | cons first rest =>
    cases rest with
    | nil =>
      let previous := SourceSupportSummaries.childEntry table first
      have same : SourceSupportSummaries.output rename node = SourceSupportSummaries.output rename (parameters.decoder.childIndex node first) := by
        rw [SourceSupportSummaries.output, outputLiteral, decoderDisjunction_output .faulty node [first] shape]
        simpa only [decoderDisjunctionOutput, List.map_cons, List.map_nil, SourceSerialFold.allocate,
          childLiteral] using child_eq_output rename .faulty node first
      unfold SourceSupportSummaries.disjunction
      dsimp only [id]
      refine ⟨?_, ?_⟩
      · simpa only [SourceDecoderSchedule.PrefixOriginalSupport, SourcePrefix.extend, List.append_nil] using origins.prepared.supported
      · apply summary_indices_mpr_origin _ _ _ same rfl _
        simpa only [List.append_nil, previous, SourceSupportSummaries.childEntry] using
          origins.entries (parameters.decoder.childIndex node first) first.isLt
    | cons second rest =>
      let children := first :: second :: rest
      let stored := children.toFinset.biUnion (fun child => (SourceSupportSummaries.childEntry table child).stored)
      let start := table.prepared.proofPrefix
      let tree := (decoderDisjunctionTree rename .faulty node children shape (by simp [children])).afterTrace
        start.state start.steps start.checked
      let projected := TreeUnits.nonunaryLong tree (by simp [children])
      let target := cofactor (parameters := parameters) rename ++ negate (SourceSupportSummaries.output rename node) :: heads stored (SourceSupportSummaries.qualifier rename)
      let labels := fun child => SourceSupportSummaries.output rename (parameters.decoder.childIndex node child)
      let supportHeads := fun child => heads (SourceSupportSummaries.childEntry table child).stored (SourceSupportSummaries.qualifier rename)
      let parent : AvailableSubclause projected.state (children.map labels ++ target) := by
        apply retarget projected.result
        intro literal member
        have rootEq : dualLiteral rename (SourceSerialFold.allocate .disjunction (decoderPositionBefore .faulty node).lastID
            (children.map (fun child => (decoderPositionBefore .faulty node).slots
              (.internal (.decoder .faulty (parameters.decoder.childIndex node child)))))).output = negate (SourceSupportSummaries.output rename node) := by
          rw [SourceSupportSummaries.output, outputLiteral, decoderDisjunction_output .faulty node children shape]
          rfl
        have inputEq : ((children.map (fun child => (decoderPositionBefore .faulty node).slots
            (.internal (.decoder .faulty (parameters.decoder.childIndex node child))))).map (dualLiteral rename)).map negate = children.map labels := by
          rw [List.map_map, List.map_map]
          apply List.map_congr_left
          intro child member
          simpa only [Function.comp_apply, dualLiteral, negate_negate, labels, SourceSupportSummaries.output, childLiteral] using child_eq_output rename .faulty node child
        simp only [rootEq, inputEq, List.mem_cons] at member
        exact member.elim (fun same => List.mem_append_right _ (List.mem_append_right _ (List.mem_cons.mpr (Or.inl same))))
          (List.mem_append_left _)
      have included : ∀ child ∈ children, ClauseSubset (supportHeads child) target := by
        intro child listed literal member
        obtain ⟨channel, present, equal⟩ := (heads_member _ _ _).mp member
        apply List.mem_append_right
        apply List.mem_cons_of_mem
        apply (heads_member stored (SourceSupportSummaries.qualifier rename) literal).mpr
        exact ⟨channel, Finset.mem_biUnion.mpr ⟨child, List.mem_toFinset.mpr listed, present⟩, equal⟩
      let summaries := fun child (_ : child ∈ children) =>
        (SourceSupportSummaries.childEntry table child).summary.afterTrace projected.state projected.steps projected.checked
      let eliminated := SupportRows.eliminate projected.state (cofactor (parameters := parameters) rename) target children labels supportHeads
        summaries (fun _ member => List.mem_append_left _ member) included parent
      have treeOrigins := treeOriginals_afterTrace
        (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
        (decoderDisjunctionTree rename .faulty node children shape (by simp [children]))
        (decoderDisjunctionTree_originals rename .faulty node children shape (by simp [children])) start.state start.steps start.checked
      have projectedOrigins := nonunaryLong_supported rename start tree (by simp [children]) origins.prepared.supported treeOrigins
      have summaryOrigins : ∀ child member, SummaryResultOrigin (SourceController.formula parameters).clauses.size
          (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) (start.steps ++ projected.steps) (summaries child member) := by
        intro child member
        exact SummaryResultOrigin.afterTrace _ _ start.steps (SourceSupportSummaries.childEntry table child).summary
          (origins.entries (parameters.decoder.childIndex node child) child.isLt) projected.state projected.steps projected.checked
      have actual := summaryEliminate_supported projected.state (cofactor (parameters := parameters) rename) target children labels supportHeads summaries
        (fun _ member => List.mem_append_left _ member) included parent (SourceController.formula parameters).clauses.size
        (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) (start.steps ++ projected.steps)
        projectedOrigins.1 (SourceDecoderSchedule.allowed_native_count_le rename)
        (Nat.le_trans (SourceMixedSchedule.prefix_native_count_le rename start) (runSteps_lastId_le projected.checked)) summaryOrigins projectedOrigins.2
      unfold SourceSupportSummaries.disjunction
      dsimp only [id]
      refine ⟨?_, ?_⟩
      · simpa only [SourceDecoderSchedule.PrefixOriginalSupport, SourcePrefix.extend, children, stored, start, tree, projected,
          target, labels, supportHeads, summaries, parent, eliminated, List.append_assoc] using actual.1
      · simpa only [SummaryResultOrigin, children, stored, start, tree, projected, target, labels, supportHeads, summaries,
          parent, eliminated, List.append_assoc] using actual.2

end Controller.NativeProof.Wrapper
