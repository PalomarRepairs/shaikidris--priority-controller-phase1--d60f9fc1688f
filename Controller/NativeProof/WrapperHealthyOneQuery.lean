module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.WrapperQueryRows

@[expose] public section

/-! Selected healthy-one equalities retain native query and preparation origins. -/
namespace Controller.NativeProof.Wrapper
open Controller.CNF Controller.Resolution Controller.Native Controller.Native.SourceController
open Controller.NativeProof.FoldProjection Controller.NativeProof.SourceFoldProjection
open Controller.NativeProof.SourceStageCongruence Controller.NativeProof.SourceStagePolarity
open Controller.NativeProof.SourceStageXor Controller.NativeProof.SourceBusSchedule
open Controller.NativeProof.SourceBusAdvance Controller.NativeProof.SourceFoldProvenance
open Controller.NativeProof.SourceMismatchHandles Controller.NativeProof.SourceDecoderTraversal
open Controller.NativeProof.SourceHealthyOne Controller.NativeProof.HornNativeReplay
variable {parameters : Parameters} {v : Nat}

theorem healthyOneQuery_origins (rename : Nat → Fin v)
    (prepared : SourceHealthyOne.Preparation (parameters := parameters) rename) (origins : PreparationOrigins rename prepared)
    (guarded : parameters.decoder.Guarded) (selected : Finset (Fin parameters.decoder.roots.length))
    (absent : Decoder.NoDiscrepancy parameters selected) (output : Fin parameters.decoder.roots.length)
    (accepted : output ∈ selected)
    (healthy : parameters.observations output (Controller.assignmentOfSet {parameters.bridge.target}) = true) :
    SourceDecoderSchedule.ProjectionOriginalSupport rename prepared.proofPrefix
      (SourceHealthyOneQuery.query rename prepared guarded selected absent output accepted healthy) := by
  let root := parameters.decoder.roots.get output
  let formula := parameters.decoder.finiteZeroSystem parameters.buses parameters.bridge.target root ∅ ∅
  have unsat : Unsatisfiable formula := by
    apply (unsatisfiable_relabel_iff parameters.decoder.zeroIndex.injective _).mpr
    exact Decoder.healthyOne_zeroSystem_unsatisfiable parameters guarded selected absent output accepted healthy
  have complete := HornTrail.produce_complete formula (parameters.decoder.finiteZeroSystem_dualHorn guarded _ _ _ _ _) unsat
  unfold SourceHealthyOneQuery.query
  dsimp only [id]
  split
  · rename_i returned
    change HornTrail.produce formula = none at returned
    obtain ⟨conflict, run, _, _⟩ := complete
    simp [returned] at run
  · rename_i conflict returned
    change HornTrail.produce formula = some conflict at returned
    have certified : HornTrail.Certified formula conflict := by
      obtain ⟨result, run, proof, bound⟩ := complete
      have same : result = conflict := Option.some.inj (run.symm.trans returned)
      exact same ▸ proof
    have positive := HornTrail.scan_conflict_positive formula _ _ _ conflict returned
    have actual := hornRowReplay_supported formula conflict certified positive
      (SourceHealthyOneQuery.handles (parameters := parameters) rename) prepared.proofPrefix.state
      (cofactor (parameters := parameters) rename ++ [SourceForwardRows.handle rename .faulty (.inr root)])
      (SourceHealthyOneQuery.finiteRows rename prepared root) (SourceController.formula parameters).clauses.size
      (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) prepared.proofPrefix.steps
      origins.supported (SourceDecoderSchedule.allowed_native_count_le rename)
      (SourceMixedSchedule.prefix_native_count_le rename prepared.proofPrefix)
      (queryFiniteRows_origins rename prepared origins root)
    exact actual

theorem healthyOneEquality_origins (rename : Nat → Fin v)
    (prepared : SourceHealthyOne.Preparation (parameters := parameters) rename) (origins : PreparationOrigins rename prepared)
    (guarded : parameters.decoder.Guarded) (selected : Finset (Fin parameters.decoder.roots.length))
    (absent : Decoder.NoDiscrepancy parameters selected) (output : Fin parameters.decoder.roots.length)
    (accepted : output ∈ selected)
    (healthy : parameters.observations output (Controller.assignmentOfSet {parameters.bridge.target}) = true) :
    SourceDecoderSchedule.PairedProjectionOriginalSupport rename prepared.proofPrefix
      (SourceHealthyOneQuery.equality rename prepared guarded selected absent output accepted healthy) := by
  let actual := SourceHealthyOneQuery.query rename prepared guarded selected absent output accepted healthy
  let faulty : AvailableSubclause actual.state (cofactor (parameters := parameters) rename ++ [nativeRootLiteral rename .faulty output]) := by
    simpa only [SourceHealthyOneQuery.rootHandle, SourceForwardRows.handle, Sum.elim_inr] using actual.result
  let healthyRow : AvailableSubclause actual.state (cofactor (parameters := parameters) rename ++ [nativeRootLiteral rename .healthy output]) := by
    have bit : parameters.decoder.eval (Controller.assignmentOfSet {parameters.bridge.target}) (parameters.decoder.roots.get output) = true := healthy
    simpa only [bit, valueLiteral, ite_true, SourceHealthyOneQuery.rootHandle] using
      FoldProjection.afterTrace (prepared.healthy (parameters.decoder.roots.get output)) actual.state actual.steps actual.checked
  have actualOrigins := healthyOneQuery_origins rename prepared origins guarded selected absent output accepted healthy
  have faultyId : faulty.row.id = actual.result.row.id := by
    dsimp only [faulty]
    with_unfolding_all
      apply SourceMixedSchedule.subclause_indices_mpr_id rfl
      simp only [SourceHealthyOneQuery.rootHandle, SourceForwardRows.handle, Sum.elim_inr]
  have healthyId : healthyRow.row.id = (prepared.healthy (parameters.decoder.roots.get output)).row.id := by
    have bit : parameters.decoder.eval (Controller.assignmentOfSet {parameters.bridge.target})
        (parameters.decoder.roots.get output) = true := healthy
    dsimp only [healthyRow]
    with_unfolding_all
      apply Eq.trans (SourceMixedSchedule.subclause_indices_mpr_id rfl
        (by simp only [SourceHealthyOneQuery.rootHandle]) _ _)
      apply SourceMixedSchedule.subclause_indices_cast_id rfl
      simp only [bit, valueLiteral, ite_true]
  unfold SourceDecoderSchedule.PairedProjectionOriginalSupport SourceHealthyOneQuery.equality
  dsimp only [id]
  refine ⟨actualOrigins.1, ?_, ?_⟩
  · change ResultOrigin (SourceController.formula parameters).clauses.size
      (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
      (prepared.proofPrefix.steps ++ actual.steps) faulty.row.id
    rw [faultyId]
    exact actualOrigins.2
  · change ResultOrigin (SourceController.formula parameters).clauses.size
      (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
      (prepared.proofPrefix.steps ++ actual.steps) healthyRow.row.id
    rw [healthyId]
    exact resultOrigin_append_right _ _ prepared.proofPrefix.steps actual.steps _ (origins.healthy _)

end Controller.NativeProof.Wrapper
