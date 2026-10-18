module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.WrapperForwardDisjunction

@[expose] public section

/-! The shared forward-row bank contains retained native or identity origins. -/
namespace Controller.NativeProof.Wrapper
open Controller.CNF Controller.Resolution Controller.Native Controller.Native.SourceController
open Controller.NativeProof.FoldProjection Controller.NativeProof.SourceFoldProjection
open Controller.NativeProof.SourceStageCongruence Controller.NativeProof.SourceStagePolarity
open Controller.NativeProof.SourceStageXor Controller.NativeProof.SourceBusSchedule
open Controller.NativeProof.SourceFoldProvenance Controller.NativeProof.SourceMismatchHandles
open Controller.NativeProof.SourceDecoderEvaluation Controller.NativeProof.SourceDecoderTraversal
open Controller.NativeProof.SourceDecoderClauses Controller.NativeProof.SourceDecoderSchedule
variable {parameters : Parameters} {v : Nat}

theorem forwardNodeRows_origins (rename : Nat → Fin v) (side : Side) (cofactor : Clause (Fin v))
    (guarded : parameters.decoder.Guarded) (node : Fin parameters.decoder.nodeCount)
    (start : SourcePrefix (parameters := parameters) rename) (supported : SourceDecoderSchedule.PrefixOriginalSupport rename start) :
    ForwardNodeRowsOrigins rename side cofactor node start (SourceForwardRows.nodeRows rename side cofactor guarded node start) := by
  unfold SourceForwardRows.nodeRows
  split
  · rename_i shape; exact forwardZero_origins rename side cofactor node start shape supported
  · rename_i channel shape; exact forwardInput_origins rename side cofactor node start channel shape supported
  · rename_i children shape; exact forwardDisjunction_origins rename side cofactor node start children shape supported
  · rename_i child labels shape; exact forwardGuard_origins rename side cofactor node start child labels shape supported
  · rename_i left right shape
    exact False.elim (by simpa [Controller.Decoder.Gate.IsGuarded, shape, Controller.Decoder.Gate.isLiveAnd] using guarded node)

theorem forwardAppend_origins (rename : Nat → Fin v) (side : Side) (cofactor : Clause (Fin v))
    (node : Fin parameters.decoder.nodeCount) (table : SourceForwardRows.Table (parameters := parameters) rename side cofactor node.val)
    (added : SourceForwardRows.NodeRows rename side cofactor node table.proofPrefix)
    (origins : ForwardTableOrigins rename side table) (addedOrigins : ForwardNodeRowsOrigins rename side cofactor node table.proofPrefix added) :
    ForwardTableOrigins rename side (SourceForwardRows.append rename side cofactor node table added) := by
  refine ⟨addedOrigins.supported, ?_⟩
  intro query before row member
  by_cases same : query = node
  · subst query
    have originEqual : (SourceForwardRows.append rename side cofactor node table added).rows node before row member =
        added.rows row member := by
      unfold SourceForwardRows.append
      dsimp only [id]
      exact dite_eq_left rfl
    rw [originEqual]
    exact addedOrigins.rows row member
  · have earlier : query.val < node.val := by
      have different : query.val ≠ node.val := fun equal => same (Fin.ext equal)
      omega
    have originEqual : (SourceForwardRows.append rename side cofactor node table added).rows query before row member =
        (table.rows query earlier row member).afterTrace added.state added.steps added.checked := by
      unfold SourceForwardRows.append
      dsimp only [id]
      exact dite_eq_right same
    rw [originEqual]
    exact ForwardOriginProvenance.afterTrace rename table.proofPrefix (table.rows query earlier row member)
      (origins.rows query earlier row member) added.state added.steps added.checked

theorem forwardBuild_origins (rename : Nat → Fin v) (side : Side) (cofactor : Clause (Fin v))
    (guarded : parameters.decoder.Guarded) (seed : SourcePrefix (parameters := parameters) rename)
    (supported : SourceDecoderSchedule.PrefixOriginalSupport rename seed) (count : Nat) (bound : count ≤ parameters.decoder.nodeCount) :
    ForwardTableOrigins rename side (SourceForwardRows.build rename side cofactor guarded seed count bound) := by
  induction count with
  | zero =>
    refine ⟨supported, ?_⟩
    intro node before row member
    exact False.elim (Nat.not_lt_zero _ before)
  | succ count ih =>
    let node : Fin parameters.decoder.nodeCount := ⟨count, by omega⟩
    let table := SourceForwardRows.build rename side cofactor guarded seed count (by omega)
    have tableOrigins := ih (by omega)
    exact forwardAppend_origins rename side cofactor node table
      (SourceForwardRows.nodeRows rename side cofactor guarded node table.proofPrefix) tableOrigins
      (forwardNodeRows_origins rename side cofactor guarded node table.proofPrefix tableOrigins.supported)

theorem forwardAllRows_origins (rename : Nat → Fin v) (side : Side) (cofactor : Clause (Fin v))
    (guarded : parameters.decoder.Guarded) (seed : SourcePrefix (parameters := parameters) rename)
    (supported : SourceDecoderSchedule.PrefixOriginalSupport rename seed) :
    ForwardTableOrigins rename side (SourceForwardRows.allRows rename side cofactor guarded seed) :=
  forwardBuild_origins rename side cofactor guarded seed supported _ (Nat.le_refl _)

end Controller.NativeProof.Wrapper
