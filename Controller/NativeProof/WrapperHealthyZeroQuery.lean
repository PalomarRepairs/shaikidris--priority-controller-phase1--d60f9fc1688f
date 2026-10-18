module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.WrapperSupportTable

@[expose] public section

/-! Selected healthy-zero equalities consume the checked empty support summary. -/
namespace Controller.NativeProof.Wrapper
open Controller.CNF Controller.Resolution Controller.Native Controller.Native.SourceController
open Controller.NativeProof.FoldProjection Controller.NativeProof.SourceFoldProjection
open Controller.NativeProof.SourceStageCongruence Controller.NativeProof.SourceStagePolarity
open Controller.NativeProof.SourceStageXor Controller.NativeProof.SourceBusSchedule
open Controller.NativeProof.SourceBusAdvance Controller.NativeProof.SourceFoldProvenance
open Controller.NativeProof.SourceMismatchHandles Controller.NativeProof.SourceDecoderTraversal
open Controller.NativeProof.SourceHealthyOne Controller.NativeProof.SupportRows
variable {parameters : Parameters} {v : Nat}

theorem summaryEmptyRow_origin (originalCount : Nat) (allowed : Nat → Prop) (prior : List (Step v))
    {state : State v} {cofactor : Clause (Fin v)} {output : Literal (Fin v)}
    (summary : SupportRows.Summary state cofactor output []) (origin : SummaryResultOrigin originalCount allowed prior summary) :
    ResultOrigin originalCount allowed prior summary.emptyRow.row.id := by
  cases summary with
  | identity same => have length := congrArg List.length same; simp at length
  | derived row => exact origin

theorem healthyZeroEquality_origins (rename : Nat → Fin v)
    (table : SourceSupportSummaries.Table (parameters := parameters) rename parameters.decoder.nodeCount)
    (origins : SupportTableOrigins rename table) (guarded : parameters.decoder.Guarded)
    (selected : Finset (Fin parameters.decoder.roots.length)) (absent : Decoder.NoDiscrepancy parameters selected)
    (index : Fin parameters.decoder.roots.length) (accepted : index ∈ selected)
    (healthy : parameters.observations index (Controller.assignmentOfSet {parameters.bridge.target}) = false) :
    SourceDecoderSchedule.PairedProjectionOriginalSupport rename table.prepared.proofPrefix
      (SourceSupportSummaries.equality rename table guarded selected absent index accepted healthy) := by
  let root := parameters.decoder.roots.get index
  let entry := table.entries root root.isLt
  have semanticEmpty := DecoderSupport.root_support_empty parameters guarded selected absent index accepted healthy
  have storedEmpty : entry.stored = ∅ := entry.exactSupport.trans semanticEmpty
  let summary : SupportRows.Summary table.prepared.proofPrefix.state (cofactor (parameters := parameters) rename)
      (SourceSupportSummaries.output rename root) [] := by
    simpa only [storedEmpty, heads_empty] using entry.summary
  have summaryOrigin : SummaryResultOrigin (SourceController.formula parameters).clauses.size
      (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) table.prepared.proofPrefix.steps summary := by
    dsimp only [summary]
    apply summary_indices_mpr_origin _ _ _ rfl (by simp only [storedEmpty, heads_empty]) _
    exact origins.entries root root.isLt
  let faulty : AvailableSubclause table.prepared.proofPrefix.state
      (cofactor (parameters := parameters) rename ++ [negate (nativeRootLiteral rename .faulty index)]) := by
    simpa only [SourceHealthyOneQuery.rootHandle, SourceSupportSummaries.output] using summary.emptyRow
  let healthyRow : AvailableSubclause table.prepared.proofPrefix.state
      (cofactor (parameters := parameters) rename ++ [negate (nativeRootLiteral rename .healthy index)]) := by
    have bit : parameters.decoder.eval (Controller.assignmentOfSet {parameters.bridge.target}) root = false := healthy
    simpa only [bit, valueLiteral, Bool.false_eq_true, ite_false, SourceHealthyOneQuery.rootHandle] using table.prepared.healthy root
  have faultyId : faulty.row.id = summary.emptyRow.row.id := by
    dsimp only [faulty]
    with_unfolding_all
      apply SourceMixedSchedule.subclause_indices_mpr_id rfl
      simp only [SourceHealthyOneQuery.rootHandle, SourceSupportSummaries.output]
  have healthyId : healthyRow.row.id = (table.prepared.healthy root).row.id := by
    have bit : parameters.decoder.eval (Controller.assignmentOfSet {parameters.bridge.target}) root = false := healthy
    dsimp only [healthyRow]
    with_unfolding_all
      apply Eq.trans (SourceMixedSchedule.subclause_indices_mpr_id rfl
        (by simp only [SourceHealthyOneQuery.rootHandle, root]) _ _)
      apply SourceMixedSchedule.subclause_indices_cast_id rfl
      simp only [bit, valueLiteral, Bool.false_eq_true, ite_false]
      rfl
  unfold SourceDecoderSchedule.PairedProjectionOriginalSupport SourceSupportSummaries.equality
  dsimp only [id]
  refine ⟨?_, ?_, ?_⟩
  · simpa only [SourceDecoderSchedule.PrefixOriginalSupport, SourcePrefix.extend, List.append_nil] using origins.prepared.supported
  · change ResultOrigin (SourceController.formula parameters).clauses.size
      (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) (table.prepared.proofPrefix.steps ++ []) healthyRow.row.id
    rw [List.append_nil, healthyId]
    exact origins.prepared.healthy root
  · change ResultOrigin (SourceController.formula parameters).clauses.size
      (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) (table.prepared.proofPrefix.steps ++ []) faulty.row.id
    rw [List.append_nil, faultyId]
    exact summaryEmptyRow_origin _ _ _ summary summaryOrigin

end Controller.NativeProof.Wrapper
