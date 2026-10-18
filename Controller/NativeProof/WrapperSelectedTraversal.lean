module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.WrapperDrivenSeed

@[expose] public section

/-! Driven equality traversal requests only the observed outputs in the supplied list. -/
namespace Controller.NativeProof.Wrapper
open Controller.CNF Controller.Resolution Controller.Native Controller.Native.SourceController
open Controller.NativeProof.FoldProjection Controller.NativeProof.SourceFoldProjection
open Controller.NativeProof.SourceStageCongruence Controller.NativeProof.SourceStagePolarity
open Controller.NativeProof.SourceBusSchedule Controller.NativeProof.SourceBusAdvance
open Controller.NativeProof.SourceMismatchHandles Controller.NativeProof.SourceDecoderTraversal
open Controller.NativeProof.SourceHealthyOne
variable {parameters : Parameters} {v : Nat}

def selectedMixed (rename : Nat → Fin v) (guarded : parameters.decoder.Guarded)
    (selected : Finset (Fin parameters.decoder.roots.length)) (absent : Decoder.NoDiscrepancy parameters selected)
    (table : Compiler.DrivenTable (parameters := parameters) rename 0)
    (output : Fin parameters.decoder.roots.length) (accepted : output ∈ selected) :
    PairedProjection table.summaries.prepared.proofPrefix.state (cofactor (parameters := parameters) rename)
      (nativeRootLiteral rename .healthy output) (nativeRootLiteral rename .faulty output)
      (parameters.channels + parameters.decoder.nodeCount) :=
  if healthy : parameters.observations output (Controller.assignmentOfSet {parameters.bridge.target}) = true then
    SourceHealthyOneQuery.equality rename table.summaries.prepared guarded selected absent output accepted healthy
  else
    let actual := SourceSupportSummaries.equality rename table.summaries guarded selected absent output accepted
      (Bool.eq_false_of_not_eq_true healthy)
    ⟨actual.state, actual.steps, actual.checked, actual.pair, actual.count.trans (Nat.zero_le _)⟩

theorem selectedMixed_origins (rename : Nat → Fin v) (guarded : parameters.decoder.Guarded)
    (selected : Finset (Fin parameters.decoder.roots.length)) (absent : Decoder.NoDiscrepancy parameters selected)
    (table : Compiler.DrivenTable (parameters := parameters) rename 0) (origins : DrivenSeedOrigins rename table)
    (output : Fin parameters.decoder.roots.length) (accepted : output ∈ selected) :
    SourceDecoderSchedule.PairedProjectionOriginalSupport rename table.summaries.prepared.proofPrefix
      (selectedMixed rename guarded selected absent table output accepted) := by
  unfold selectedMixed
  split
  · rename_i healthy
    exact healthyOneEquality_origins rename table.summaries.prepared origins.summaries.prepared guarded selected absent output accepted healthy
  · rename_i healthy
    exact healthyZeroEquality_origins rename table.summaries origins.summaries guarded selected absent output accepted
      (Bool.eq_false_of_not_eq_true healthy)

structure SelectedDriven (rename : Nat → Fin v) (outputs : List (Fin parameters.decoder.roots.length)) where
  seed : Compiler.DrivenTable (parameters := parameters) rename 0
  origins : DrivenSeedOrigins rename seed
  pairs : ∀ output, output ∈ outputs → DirectionPair seed.summaries.prepared.proofPrefix.state []
    (nativeRootLiteral rename .healthy output) (nativeRootLiteral rename .faulty output)
  pairOrigins : ∀ output member, SourceDecoderSchedule.DirectionPairOrigin rename seed.summaries.prepared.proofPrefix (pairs output member)

def SelectedDriven.afterTrace (table : SelectedDriven (parameters := parameters) rename outputs)
    (next : State v) (steps : List (Step v)) (checked : runSteps table.seed.summaries.prepared.proofPrefix.state steps = some next)
    (supported : SourceDecoderSchedule.PrefixOriginalSupport rename (table.seed.summaries.prepared.proofPrefix.extend next steps checked)) :
    SelectedDriven (parameters := parameters) rename outputs where
  seed := table.seed.afterTrace next steps checked
  origins := table.origins.afterTrace rename table.seed next steps checked supported
  pairs output member := (table.pairs output member).afterTrace next steps checked
  pairOrigins output member :=
    ⟨SourceDecoderSchedule.GuardedTransferOrigin.afterTrace rename _ _ (table.pairOrigins output member).1 next steps checked,
     SourceDecoderSchedule.GuardedTransferOrigin.afterTrace rename _ _ (table.pairOrigins output member).2 next steps checked⟩

def selectedAdvance (rename : Nat → Fin v) (guarded : parameters.decoder.Guarded)
    (selected : Finset (Fin parameters.decoder.roots.length)) (absent : Decoder.NoDiscrepancy parameters selected)
    (output : Fin parameters.decoder.roots.length) (accepted : output ∈ selected)
    (table : SelectedDriven (parameters := parameters) rename outputs) :
    SelectedDriven (parameters := parameters) rename (output :: outputs) := by
  let mixed := selectedMixed rename guarded selected absent table.seed output accepted
  have mixedOrigins := selectedMixed_origins rename guarded selected absent table.seed table.origins output accepted
  let current := table.afterTrace mixed.state mixed.steps mixed.checked mixedOrigins.1
  let final := Compiler.dischargePair mixed.state
    (nativeHealthyFirstFlag (parameters := parameters) rename) (nativeFaultyFirstFlag (parameters := parameters) rename)
    (nativeRootLiteral rename .healthy output) (nativeRootLiteral rename .faulty output)
    (current.seed.equalOne output) mixed.pair current.seed.healthyFlag
  have finalOrigins := dischargePair_origins rename current.seed.summaries.prepared.proofPrefix _ _ _ _
    (current.seed.equalOne output) mixed.pair current.seed.healthyFlag current.origins.summaries.prepared.supported
    (current.origins.equalOne output) mixedOrigins.2 current.origins.healthyFlag
  let extended := current.afterTrace final.state final.steps final.checked finalOrigins.1
  refine ⟨extended.seed, extended.origins,
    (fun query member => if same : query = output then same ▸ final.pair else
      extended.pairs query (by simpa only [List.mem_cons, same, false_or] using member)), ?_⟩
  intro query member
  split
  · rename_i same
    subst query
    exact finalOrigins.2
  · exact extended.pairOrigins _ _

def selectedBuild (rename : Nat → Fin v) (drive : parameters.drive = true) (guarded : parameters.decoder.Guarded)
    (selected : Finset (Fin parameters.decoder.roots.length)) (absent : Decoder.NoDiscrepancy parameters selected) :
    (outputs : List (Fin parameters.decoder.roots.length)) → (∀ output ∈ outputs, output ∈ selected) →
      SelectedDriven (parameters := parameters) rename outputs
  | [], _ => ⟨Compiler.initialDriven rename drive guarded, initialDriven_origins rename drive guarded,
      fun _ member => False.elim (List.not_mem_nil member), fun _ member => False.elim (List.not_mem_nil member)⟩
  | output :: rest, accepted => selectedAdvance rename guarded selected absent output (accepted output (by simp))
      (selectedBuild rename drive guarded selected absent rest (fun query member => accepted query (List.mem_cons_of_mem _ member)))

end Controller.NativeProof.Wrapper
