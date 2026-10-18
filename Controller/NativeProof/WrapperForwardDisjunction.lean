module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.WrapperForwardBranches

@[expose] public section

/-! Forward disjunction rows retain the selected native directional certificate. -/
namespace Controller.NativeProof.Wrapper
open Controller.CNF Controller.Resolution Controller.Native Controller.Native.SourceController
open Controller.Decoder.ZeroSystem
open Controller.NativeProof.FoldProjection Controller.NativeProof.SourceFoldProjection
open Controller.NativeProof.SourceStageCongruence Controller.NativeProof.SourceStagePolarity
open Controller.NativeProof.SourceStageXor Controller.NativeProof.SourceBusSchedule
open Controller.NativeProof.SourceFoldProvenance Controller.NativeProof.SourceMismatchHandles
open Controller.NativeProof.SourceDecoderEvaluation Controller.NativeProof.SourceDecoderTraversal
open Controller.NativeProof.SourceDecoderClauses Controller.NativeProof.SourceDecoderSchedule
variable {parameters : Parameters} {v : Nat}

theorem mapDirectionalCertificate_provenance (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    {root input : Literal (Fin v)}
    (certificate : DirectionalCertificate prefixState.state root input)
    (identity : root = input → SourceForwardRows.Origin (parameters := parameters) rename side prefixState.state cofactor row)
    (derived : AvailableSubclause prefixState.state [negate root, input] →
      SourceForwardRows.Origin (parameters := parameters) rename side prefixState.state cofactor row)
    (certificateOrigin : CertificateOrigin (formula parameters).clauses.size
      (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) prefixState.steps certificate)
    (identityOrigins : ∀ same, ForwardOriginProvenance rename prefixState (identity same))
    (derivedOrigins : ∀ available, DecoderRowOrigin rename prefixState available →
      ForwardOriginProvenance rename prefixState (derived available)) :
    ForwardOriginProvenance rename prefixState (SourceForwardRows.mapDirectionalCertificate certificate identity derived) := by
  cases certificate with
  | identity same => exact identityOrigins same
  | derived available => exact derivedOrigins available certificateOrigin

theorem forwardDisjunction_origins (rename : Nat → Fin v) (side : Side) (cofactor : Clause (Fin v))
    (node : Fin parameters.decoder.nodeCount) (start : SourcePrefix (parameters := parameters) rename)
    (children : List (Fin node.val)) (shape : parameters.decoder.node node = .disj children)
    (supported : SourceDecoderSchedule.PrefixOriginalSupport rename start) :
    ForwardNodeRowsOrigins rename side cofactor node start (SourceForwardRows.disjunction rename side cofactor node start children shape) := by
  unfold SourceForwardRows.disjunction
  apply forwardRows_dite_origins
  · intro empty
    subst children
    dsimp only [id]
    refine ⟨?_, ?_⟩
    · simpa only [SourceDecoderSchedule.PrefixOriginalSupport, SourcePrefix.extend, List.append_nil] using supported
    · intro row member
      exact False.elim (by simpa [Controller.Decoder.DAG.nodeClauses, shape] using member)
  · intro empty
    let tree := (decoderDisjunctionTree rename side node children shape empty).afterTrace start.state start.steps start.checked
    let projected := projectTreeInputs tree
    have originals := treeOriginals_afterTrace
      (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
      (decoderDisjunctionTree rename side node children shape empty)
      (decoderDisjunctionTree_originals rename side node children shape empty)
      start.state start.steps start.checked
    have actual := projectTreeInputs_supported tree (formula parameters).clauses.size
      (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) originals
      (SourceDecoderSchedule.allowed_native_count_le rename) (SourceMixedSchedule.prefix_native_count_le rename start)
    dsimp only [id]
    refine ⟨?_, ?_⟩
    · exact SourceMixedSchedule.traceOriginalSupport_append _ _ start.steps projected.steps supported actual.1
    · intro row member
      dsimp only [id]
      let selected := SourceForwardRows.disjunctionSelection node children shape row member
      let leaf := negate (childLiteral rename side node selected.val)
      have listed : leaf ∈ (children.map (fun child => (SourceFoldOccurrences.decoderPositionBefore side node).slots
          (.internal (.decoder side (parameters.decoder.childIndex node child))))).map (dualLiteral rename) :=
        List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨selected.val, selected.property.1, rfl⟩, rfl⟩
      apply mapDirectionalCertificate_provenance
      · have certificateOrigin := actual.2 leaf listed
        cases certificate : projected.results leaf listed with
        | identity same => trivial
        | derived available =>
          have original : ResultOrigin (formula parameters).clauses.size
              (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) projected.steps available.row.id := by
            change CertificateOrigin (formula parameters).clauses.size
              (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
              projected.steps (projected.results leaf listed) at certificateOrigin
            rw [certificate] at certificateOrigin
            exact certificateOrigin
          exact resultOrigin_append_left _ _ start.steps projected.steps _ original
      · intro same; trivial
      · intro available original; exact original

end Controller.NativeProof.Wrapper
