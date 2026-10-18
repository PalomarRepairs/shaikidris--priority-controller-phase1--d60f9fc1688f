module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.WrapperForwardOrigins

@[expose] public section

/-! Native forward rows preserve source origins through aliases and folds. -/
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

theorem forwardOrigin_dite_provenance (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (condition : Prop) [Decidable condition]
    (yes : condition → SourceForwardRows.Origin (parameters := parameters) rename side prefixState.state cofactor row)
    (no : ¬condition → SourceForwardRows.Origin (parameters := parameters) rename side prefixState.state cofactor row)
    (yesOrigins : ∀ proof, ForwardOriginProvenance rename prefixState (yes proof))
    (noOrigins : ∀ proof, ForwardOriginProvenance rename prefixState (no proof)) :
    ForwardOriginProvenance rename prefixState (dite condition yes no) := by
  by_cases proof : condition
  · rw [dite_eq_left proof]; exact yesOrigins proof
  · rw [dite_eq_right proof]; exact noOrigins proof

theorem forwardRows_dite_origins (rename : Nat → Fin v) (side : Side) (cofactor : Clause (Fin v))
    (node : Fin parameters.decoder.nodeCount) (start : SourcePrefix (parameters := parameters) rename)
    (condition : Prop) [Decidable condition]
    (yes : condition → SourceForwardRows.NodeRows rename side cofactor node start)
    (no : ¬condition → SourceForwardRows.NodeRows rename side cofactor node start)
    (yesOrigins : ∀ proof, ForwardNodeRowsOrigins rename side cofactor node start (yes proof))
    (noOrigins : ∀ proof, ForwardNodeRowsOrigins rename side cofactor node start (no proof)) :
    ForwardNodeRowsOrigins rename side cofactor node start (dite condition yes no) := by
  by_cases proof : condition
  · rw [dite_eq_left proof]; exact yesOrigins proof
  · rw [dite_eq_right proof]; exact noOrigins proof

theorem forwardInput_origins (rename : Nat → Fin v) (side : Side) (cofactor : Clause (Fin v))
    (node : Fin parameters.decoder.nodeCount) (start : SourcePrefix (parameters := parameters) rename)
    (channel : Fin parameters.channels) (shape : parameters.decoder.node node = .input channel)
    (supported : SourceDecoderSchedule.PrefixOriginalSupport rename start) :
    ForwardNodeRowsOrigins rename side cofactor node start (SourceForwardRows.input rename side cofactor node start channel shape) := by
  unfold SourceForwardRows.input
  dsimp only [id]
  refine ⟨?_, ?_⟩
  · simpa only [SourceDecoderSchedule.PrefixOriginalSupport, SourcePrefix.extend, List.append_nil] using supported
  · intro row member
    apply forwardOrigin_dite_provenance
    · intro first; trivial
    · intro first; trivial

theorem nonunaryLong_supported (rename : Nat → Fin v)
    (start : SourcePrefix (parameters := parameters) rename) (tree : AndTree start.state root inputs)
    (two : 2 ≤ inputs.length) (supported : SourceDecoderSchedule.PrefixOriginalSupport rename start)
    (originals : TreeOriginals (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) tree) :
    SourceDecoderSchedule.ProjectionOriginalSupport rename start (TreeUnits.nonunaryLong tree two) := by
  have actual := Wrapper.aggregate_long_supported rename start tree two supported originals
  simpa only [SourceDecoderSchedule.ProjectionOriginalSupport, TreeUnits.nonunaryLong,
    SourcePrefix.extend] using actual

theorem forwardGuard_origins (rename : Nat → Fin v) (side : Side) (cofactor : Clause (Fin v))
    (node : Fin parameters.decoder.nodeCount) (start : SourcePrefix (parameters := parameters) rename)
    (child : Fin node.val) (labels : List (Fin parameters.channels))
    (shape : parameters.decoder.node node = .guard child labels)
    (supported : SourceDecoderSchedule.PrefixOriginalSupport rename start) :
    ForwardNodeRowsOrigins rename side cofactor node start (SourceForwardRows.guard rename side cofactor node start child labels shape) := by
  unfold SourceForwardRows.guard
  apply forwardRows_dite_origins
  · intro empty
    subst labels
    dsimp only [id]
    refine ⟨?_, ?_⟩
    · simpa only [SourceDecoderSchedule.PrefixOriginalSupport, SourcePrefix.extend, List.append_nil] using supported
    · intro row member
      trivial
  · intro empty
    let tree := (nativeGuardTree rename side node child labels shape).afterTrace start.state start.steps start.checked
    have two : 2 ≤ (guardInputs rename side node child labels labels.length).length := by
      simp only [guardInputs, List.take_length, List.length_append, List.length_cons, List.length_nil, List.length_map]
      have positive := List.length_pos_iff.mpr empty
      omega
    have originals := treeOriginals_afterTrace
      (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
      (nativeGuardTree rename side node child labels shape) (nativeGuardTree_originals rename side node child labels shape)
      start.state start.steps start.checked
    have actual := nonunaryLong_supported rename start tree two supported originals
    dsimp only [id]
    refine ⟨actual.1, ?_⟩
    intro row member
    exact actual.2

end Controller.NativeProof.Wrapper
