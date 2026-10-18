module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.WrapperSupportGuard

@[expose] public section

/-! The concrete shared support bank retains every preparation and summary origin. -/
namespace Controller.NativeProof.Wrapper
open Controller.CNF Controller.Resolution Controller.Native Controller.Native.SourceController
open Controller.NativeProof.FoldProjection Controller.NativeProof.SourceFoldProjection
open Controller.NativeProof.SourceStageCongruence Controller.NativeProof.SourceStagePolarity
open Controller.NativeProof.SourceStageXor Controller.NativeProof.SourceBusSchedule
open Controller.NativeProof.SourceFoldProvenance Controller.NativeProof.SourceMismatchHandles
open Controller.NativeProof.SourceDecoderEvaluation Controller.NativeProof.SourceDecoderTraversal
open Controller.NativeProof.SourceDecoderSchedule Controller.NativeProof.SourceHealthyOne Controller.NativeProof.SupportRows
variable {parameters : Parameters} {v : Nat}

theorem supportStep_origins (rename : Nat → Fin v) (guarded : parameters.decoder.Guarded)
    (node : Fin parameters.decoder.nodeCount) (table : SourceSupportSummaries.Table (parameters := parameters) rename node.val)
    (origins : SupportTableOrigins rename table) :
    SupportNodeStepOrigins rename node table (SourceSupportSummaries.step rename guarded node table) := by
  unfold SourceSupportSummaries.step
  split
  · rename_i shape; exact supportZero_origins rename node table shape origins
  · rename_i channel shape; exact supportInput_origins rename node table channel shape origins
  · rename_i children shape; exact supportDisjunction_origins rename node table children shape origins
  · rename_i child labels shape; exact supportGuard_origins rename node table child labels shape origins
  · rename_i left right shape
    exact False.elim (by simpa [Controller.Decoder.Gate.IsGuarded, shape, Controller.Decoder.Gate.isLiveAnd] using guarded node)

theorem supportAppend_origins (rename : Nat → Fin v) (node : Fin parameters.decoder.nodeCount)
    (table : SourceSupportSummaries.Table (parameters := parameters) rename node.val)
    (added : SourceSupportSummaries.NodeStep rename node table) (origins : SupportTableOrigins rename table)
    (addedOrigins : SupportNodeStepOrigins rename node table added) :
    SupportTableOrigins rename (SourceSupportSummaries.append rename node table added) := by
  let next := table.afterTrace added.state added.steps added.checked
  have nextOrigins := SupportTableOrigins.afterTrace rename table origins added.state added.steps added.checked addedOrigins.supported
  refine ⟨nextOrigins.prepared, ?_⟩
  intro query before
  by_cases same : query = node
  · subst query
    have entryEqual : (SourceSupportSummaries.append rename node table added).entries node before = added.entry := by
      unfold SourceSupportSummaries.append
      dsimp only [id]
      exact dite_eq_left rfl
    rw [entryEqual]
    exact addedOrigins.summary
  · have earlier : query.val < node.val := by
      have different : query.val ≠ node.val := fun equal => same (Fin.ext equal)
      omega
    have entryEqual : (SourceSupportSummaries.append rename node table added).entries query before = next.entries query earlier := by
      unfold SourceSupportSummaries.append
      dsimp only [id]
      exact dite_eq_right same
    rw [entryEqual]
    exact nextOrigins.entries query earlier

theorem supportBuild_origins (rename : Nat → Fin v) (guarded : parameters.decoder.Guarded)
    (prepared : SourceHealthyOne.Preparation (parameters := parameters) rename) (origins : PreparationOrigins rename prepared)
    (count : Nat) (bound : count ≤ parameters.decoder.nodeCount) :
    SupportTableOrigins rename (SourceSupportSummaries.build rename guarded prepared count bound) := by
  induction count with
  | zero =>
    refine ⟨origins, ?_⟩
    intro node before
    exact False.elim (Nat.not_lt_zero _ before)
  | succ count ih =>
    let node : Fin parameters.decoder.nodeCount := ⟨count, by omega⟩
    let table := SourceSupportSummaries.build rename guarded prepared count (by omega)
    have tableOrigins := ih (by omega)
    exact supportAppend_origins rename node table (SourceSupportSummaries.step rename guarded node table) tableOrigins
      (supportStep_origins rename guarded node table tableOrigins)

theorem supportAllSummaries_origins (rename : Nat → Fin v) (guarded : parameters.decoder.Guarded)
    (prepared : SourceHealthyOne.Preparation (parameters := parameters) rename) (origins : PreparationOrigins rename prepared) :
    SupportTableOrigins rename (SourceSupportSummaries.allSummaries rename guarded prepared) :=
  supportBuild_origins rename guarded prepared origins _ (Nat.le_refl _)

theorem supportClosedSummaries_origins (rename : Nat → Fin v) (drive : parameters.drive = true)
    (guarded : parameters.decoder.Guarded) :
    SupportTableOrigins rename (SourceSupportSummaries.allSummaries rename guarded (SourceHealthyOne.prepare rename drive guarded)) :=
  supportAllSummaries_origins rename guarded _ (healthyOnePreparation_origins rename drive guarded)

end Controller.NativeProof.Wrapper
