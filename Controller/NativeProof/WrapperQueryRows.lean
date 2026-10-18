module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.WrapperHornRowOrigins

@[expose] public section

/-! Selected-query rows come from preparation or discharged synthetic assumptions. -/
namespace Controller.NativeProof.Wrapper
open Controller.CNF Controller.Resolution Controller.Native Controller.Native.SourceController
open Controller.Decoder.ZeroSystem
open Controller.NativeProof.FoldProjection Controller.NativeProof.SourceFoldProjection
open Controller.NativeProof.SourceStageCongruence Controller.NativeProof.SourceStagePolarity
open Controller.NativeProof.SourceFoldProvenance Controller.NativeProof.SourceMismatchHandles
open Controller.NativeProof.SourceHealthyOne Controller.NativeProof.HornNativeReplay
variable {parameters : Parameters} {u v : Nat}

def QueryOriginProvenance (rename : Nat → Fin v) (prefixState : SourcePrefix (parameters := parameters) rename)
    {handles : Fin u → Literal (Fin v)} {target : Clause (Fin v)} {clause : Clause (Fin u)}
    (origin : HornRowTransport.Origin handles prefixState.state target clause) : Prop :=
  HornOriginResultOrigin (formula parameters).clauses.size
    (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) prefixState.steps origin

theorem queryOrigin_dite_provenance (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    {handles : Fin u → Literal (Fin v)} {target : Clause (Fin v)} {clause : Clause (Fin u)}
    (condition : Prop) [Decidable condition]
    (yes : condition → HornRowTransport.Origin handles prefixState.state target clause)
    (no : ¬condition → HornRowTransport.Origin handles prefixState.state target clause)
    (yesOrigins : ∀ proof, QueryOriginProvenance rename prefixState (yes proof))
    (noOrigins : ∀ proof, QueryOriginProvenance rename prefixState (no proof)) :
    QueryOriginProvenance rename prefixState (dite condition yes no) := by
  by_cases proof : condition
  · rw [dite_eq_left proof]; exact yesOrigins proof
  · rw [dite_eq_right proof]; exact noOrigins proof

theorem queryOrigin_indices_mpr_provenance (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    {handles : Fin u → Literal (Fin v)} {target : Clause (Fin v)} {before after : Clause (Fin u)}
    (clauseEqual : before = after)
    (typeEqual : HornRowTransport.Origin handles prefixState.state target before =
      HornRowTransport.Origin handles prefixState.state target after)
    (value : HornRowTransport.Origin handles prefixState.state target after)
    (origin : QueryOriginProvenance rename prefixState value) :
    QueryOriginProvenance rename prefixState (Eq.mpr typeEqual value) := by
  subst after
  have same : typeEqual = rfl := Subsingleton.elim _ _
  rw [same]
  exact origin

theorem queryFromNative_origins (rename : Nat → Fin v)
    (prepared : SourceHealthyOne.Preparation (parameters := parameters) rename) (root : Fin parameters.decoder.nodeCount)
    (row : Clause parameters.decoder.ZeroVar)
    (origin : SourceForwardRows.Origin (parameters := parameters) rename .faulty prepared.proofPrefix.state
      (cofactor (parameters := parameters) rename) row)
    (supported : ForwardOriginProvenance rename prepared.proofPrefix origin) :
    QueryOriginProvenance rename prepared.proofPrefix (SourceHealthyOneQuery.fromNative rename prepared root row origin) := by
  cases origin with
  | native available =>
    unfold SourceHealthyOneQuery.fromNative QueryOriginProvenance HornOriginResultOrigin
    dsimp only [id]
    apply available_indices_mpr_resultOrigin _ _ prepared.proofPrefix.steps
      (by rw [SourceHealthyOneQuery.lifted]) _
    exact supported
  | identity premise conclusion shape same => trivial

theorem queryRowOrigin_origins (rename : Nat → Fin v)
    (prepared : SourceHealthyOne.Preparation (parameters := parameters) rename) (origins : PreparationOrigins rename prepared)
    (root : Fin parameters.decoder.nodeCount) (row : Clause parameters.decoder.ZeroVar)
    (member : row ∈ SourceHealthyOneQuery.originalRows (parameters := parameters) root) :
    QueryOriginProvenance rename prepared.proofPrefix (SourceHealthyOneQuery.rowOrigin rename prepared root row member) := by
  letI : DecidablePred (fun row : Clause parameters.decoder.ZeroVar => row ∈ parameters.decoder.forwardClauses) :=
    fun row => SourceForwardRows.memDecidable row parameters.decoder.forwardClauses
  unfold SourceHealthyOneQuery.rowOrigin
  apply queryOrigin_dite_provenance
  · intro assumption; trivial
  · intro assumption
    apply queryOrigin_dite_provenance
    · intro forward
      exact queryFromNative_origins rename prepared root row (prepared.forward row forward) (origins.forward row forward)
    · intro forward
      let allChannels := positiveClause ((List.finRange parameters.channels).map
        (Sum.inl : Fin parameters.channels → parameters.decoder.ZeroVar))
      let target := positiveClause [(Sum.inl parameters.bridge.target : parameters.decoder.ZeroVar)]
      have classified : row = allChannels ∨ (parameters.buses = 1 ∧ row = target) := by
        have emptyTrue : parameters.decoder.trueUnitClauses ∅ = [] := by simp [Controller.Decoder.DAG.trueUnitClauses]
        have emptyFalse : parameters.decoder.falseUnitClauses ∅ = [] := by simp [Controller.Decoder.DAG.falseUnitClauses]
        by_cases one : parameters.buses = 1 <;>
          simpa [SourceHealthyOneQuery.originalRows, Controller.Decoder.DAG.channelClauses,
            emptyTrue, emptyFalse, forward, assumption, one, allChannels, target] using member
      apply queryOrigin_dite_provenance
      · intro nonempty
        unfold QueryOriginProvenance HornOriginResultOrigin
        dsimp only [id]
        apply available_indices_mpr_resultOrigin _ _ prepared.proofPrefix.steps
          (by rw [SourceHealthyOneQuery.lifted]) _
        apply available_indices_mpr_resultOrigin _ _ prepared.proofPrefix.steps
          (by simp [nonempty, SourceForwardRows.clause, SourceForwardRows.literal, SourceForwardRows.handle,
            positiveClause, List.map_map, Function.comp_def]) _
        exact origins.nonempty
      · intro nonempty
        have targetRow := classified.resolve_left nonempty
        unfold QueryOriginProvenance HornOriginResultOrigin
        dsimp only [id]
        apply available_indices_mpr_resultOrigin _ _ prepared.proofPrefix.steps
          (by rw [SourceHealthyOneQuery.lifted]) _
        apply available_indices_mpr_resultOrigin _ _ prepared.proofPrefix.steps
          (by simp [targetRow.2, target, SourceForwardRows.clause, SourceForwardRows.literal,
            SourceForwardRows.handle, positiveClause]) _
        exact origins.targetUnit targetRow.1

theorem queryFiniteRows_origins (rename : Nat → Fin v)
    (prepared : SourceHealthyOne.Preparation (parameters := parameters) rename) (origins : PreparationOrigins rename prepared)
    (root : Fin parameters.decoder.nodeCount)
    (index : Fin (parameters.decoder.finiteZeroSystem parameters.buses parameters.bridge.target root ∅ ∅).clauses.size) :
    QueryOriginProvenance rename prepared.proofPrefix (SourceHealthyOneQuery.finiteRows rename prepared root index) := by
  unfold SourceHealthyOneQuery.finiteRows
  dsimp only [id]
  apply queryOrigin_indices_mpr_provenance
  · simp only [Controller.Decoder.DAG.finiteZeroSystem, relabel, Controller.CNF.OrderedFormula.relabel, Array.getElem_map,
      Controller.CNF.OrderedFormula.Clause.relabel, Rows.mapClause]
  · exact queryRowOrigin_origins rename prepared origins root _ _

end Controller.NativeProof.Wrapper
