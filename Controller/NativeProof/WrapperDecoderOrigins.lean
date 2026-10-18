module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.WrapperQualifierBank

@[expose] public section

/-! The healthy decoder table uses retained controller and decoder occurrences. -/
namespace Controller.NativeProof.Wrapper
open Controller.CNF Controller.Resolution Controller.Native Controller.Native.SourceController
open Controller.NativeProof.FoldProjection Controller.NativeProof.SourceFoldProjection
open Controller.NativeProof.SourceStageCongruence Controller.NativeProof.SourceStagePolarity
open Controller.NativeProof.SourceStageXor Controller.NativeProof.SourceBusSchedule
open Controller.NativeProof.SourceFoldProvenance Controller.NativeProof.SourceMismatchHandles
open Controller.NativeProof.SourceDecoderEvaluation
variable {parameters : Parameters} {v : Nat}

theorem traceOriginalSupport_mono (originalCount : Nat) (before after : Nat → Prop)
    (steps : List (Step v)) (included : ∀ row, before row → after row)
    (supported : TraceOriginalSupport originalCount before steps) :
    TraceOriginalSupport originalCount after steps := by
  intro step member parent present
  have old := supported step member parent present
  exact ⟨fun bounded => included parent (old.1 bounded), old.2⟩

theorem resultOrigin_mono (originalCount : Nat) (before after : Nat → Prop)
    (steps : List (Step v)) (row : Nat) (included : ∀ row, before row → after row)
    (origin : ResultOrigin originalCount before steps row) :
    ResultOrigin originalCount after steps row := by
  rcases origin with original | derived
  · exact Or.inl (included row original)
  · exact Or.inr derived

def DecoderRowOrigin (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename) {clause : Clause (Fin v)}
    (row : AvailableSubclause prefixState.state clause) : Prop :=
  ResultOrigin (formula parameters).clauses.size
    (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) prefixState.steps row.row.id

structure DecoderTableOrigins (rename : Nat → Fin v) (side : Side)
    (table : SourceDecoderEvaluation.Table (parameters := parameters) rename side cofactor assignment count) : Prop where
  supported : SourceDecoderSchedule.PrefixOriginalSupport rename table.proofPrefix
  qualifiers : ∀ channel, DecoderRowOrigin rename table.proofPrefix (table.qualifiers channel)
  nodes : ∀ node before, DecoderRowOrigin rename table.proofPrefix (table.nodes node before)

theorem DecoderTableOrigins.afterTrace (rename : Nat → Fin v) (side : Side)
    (table : SourceDecoderEvaluation.Table (parameters := parameters) rename side cofactor assignment count)
    (origins : DecoderTableOrigins rename side table)
    (next : State v) (steps : List (Step v)) (checked : runSteps table.proofPrefix.state steps = some next)
    (supported : SourceDecoderSchedule.PrefixOriginalSupport rename (table.proofPrefix.extend next steps checked)) :
    DecoderTableOrigins rename side (table.afterTrace next steps checked) := by
  refine ⟨supported, ?_, ?_⟩
  · intro channel
    exact resultOrigin_append_right _ _ table.proofPrefix.steps steps _ (origins.qualifiers channel)
  · intro node before
    exact resultOrigin_append_right _ _ table.proofPrefix.steps steps _ (origins.nodes node before)

structure DecoderNodeStepOrigins (rename : Nat → Fin v) (side : Side)
    (node : Fin parameters.decoder.nodeCount)
    (start : SourceDecoderEvaluation.Table (parameters := parameters) rename side cofactor assignment node.val)
    (added : SourceDecoderEvaluation.NodeStep rename side cofactor assignment node start) : Prop where
  supported : SourceDecoderSchedule.PrefixOriginalSupport rename
    (start.proofPrefix.extend added.state added.steps added.checked)
  result : DecoderRowOrigin rename (start.proofPrefix.extend added.state added.steps added.checked) added.result

theorem healthyDecoderSeed_origins (rename : Nat → Fin v) (drive : parameters.drive = true) :
    DecoderTableOrigins rename .healthy (SourceDecoderEvaluation.healthySeed (parameters := parameters) rename drive) := by
  let bank := SourceHealthyQualifiers.allQualifiers (parameters := parameters) rename drive
  have bankOrigins := healthyAllQualifiers_origins (parameters := parameters) rename drive
  refine ⟨?_, ?_, ?_⟩
  · exact traceOriginalSupport_mono _ _ _ bank.table.proofPrefix.steps
      (SourceDecoderSchedule.controller_original_allowed rename) bankOrigins.table.supported
  · intro channel
    have indexEqual : ((SourceDecoderEvaluation.healthySeed (parameters := parameters) rename drive).qualifiers channel).row.id =
        (bank.rows channel (List.mem_finRange _)).row.id := by
      unfold SourceDecoderEvaluation.healthySeed
      dsimp only [id]
      apply SourceMixedSchedule.subclause_cast_id
      simp only [SourceDecoderEvaluation.qualifierLiteral, ← SourceQualifierSchedule.qualifierOutput_decoderStart]
      simp [Controller.assignmentOfSet]
    unfold DecoderRowOrigin
    rw [indexEqual]
    exact resultOrigin_mono _ _ _ bank.table.proofPrefix.steps _
      (SourceDecoderSchedule.controller_original_allowed rename) (bankOrigins.rows channel (List.mem_finRange _))
  · intro node before
    exact False.elim (Nat.not_lt_zero _ before)

theorem mappedUnit_resultOrigin {α : Type} (state : State v)
    (items : List α) (handle : α → Literal (Fin v)) (cofactor : Clause (Fin v))
    (rows : ∀ item ∈ items, AvailableSubclause state (cofactor ++ [handle item]))
    (originalCount : Nat) (allowed : Nat → Prop) (steps : List (Step v))
    (origins : ∀ item member, ResultOrigin originalCount allowed steps (rows item member).row.id)
    (input : Literal (Fin v)) (present : input ∈ items.map handle) :
    ResultOrigin originalCount allowed steps (TreeUnits.mappedUnit items handle cofactor rows input present).row.id := by
  induction items with
  | nil => simp at present
  | cons item rest ih =>
    by_cases equal : input = handle item
    · subst input
      simpa only [TreeUnits.mappedUnit, SourceMixedSchedule.subclause_dite_id,
        dite_eq_left rfl, dite_true] using origins item (List.mem_cons_self ..)
    · have member := (List.mem_cons.mp present).resolve_left equal
      simpa only [TreeUnits.mappedUnit, SourceMixedSchedule.subclause_dite_id, dite_eq_right equal] using
        ih (fun old listed => rows old (List.mem_cons_of_mem _ listed))
          (fun old listed => origins old (List.mem_cons_of_mem _ listed)) member

theorem decoderChildUnit_origins (rename : Nat → Fin v) (side : Side) (node : Fin parameters.decoder.nodeCount)
    (table : SourceDecoderEvaluation.Table (parameters := parameters) rename side cofactor assignment node.val)
    (origins : DecoderTableOrigins rename side table) (child : Fin node.val) :
    DecoderRowOrigin rename table.proofPrefix (SourceDecoderEvaluation.childUnit rename side node table child) := by
  have indexEqual : (SourceDecoderEvaluation.childUnit rename side node table child).row.id =
      (table.nodes (parameters.decoder.childIndex node child) (parameters.decoder.childIndex_lt node child)).row.id := by
    unfold SourceDecoderEvaluation.childUnit
    dsimp only [id]
  unfold DecoderRowOrigin
  rw [indexEqual]
  exact origins.nodes (parameters.decoder.childIndex node child) (parameters.decoder.childIndex_lt node child)

theorem decoderQualifierAt_origins (rename : Nat → Fin v) (side : Side) (node : Fin parameters.decoder.nodeCount)
    (table : SourceDecoderEvaluation.Table (parameters := parameters) rename side cofactor assignment node.val)
    (origins : DecoderTableOrigins rename side table) (channel : Fin parameters.channels) :
    DecoderRowOrigin rename table.proofPrefix (SourceDecoderEvaluation.qualifierAt rename side node table channel) := by
  have indexEqual : (SourceDecoderEvaluation.qualifierAt rename side node table channel).row.id =
      (table.qualifiers channel).row.id := by
    unfold SourceDecoderEvaluation.qualifierAt
    with_unfolding_all
      apply SourceMixedSchedule.subclause_indices_mpr_id rfl
      simp only [← SourceDecoderTraversal.decoderCursorAt_before,
        SourceDecoderTraversal.decoderCursorAt_qualifier, qualifierLiteral]
  unfold DecoderRowOrigin
  rw [indexEqual]
  exact origins.qualifiers channel

theorem decoderRootUnit_origins (rename : Nat → Fin v) (side : Side)
    (table : SourceDecoderEvaluation.Table (parameters := parameters) rename side cofactor assignment parameters.decoder.nodeCount)
    (origins : DecoderTableOrigins rename side table) (output : Fin parameters.decoder.roots.length) :
    DecoderRowOrigin rename table.proofPrefix (SourceDecoderEvaluation.rootUnit rename side table output) := by
  let root := parameters.decoder.roots[output.val]
  have indexEqual : (SourceDecoderEvaluation.rootUnit rename side table output).row.id =
      (table.nodes root root.isLt).row.id := by
    unfold SourceDecoderEvaluation.rootUnit
    dsimp only [id]
    apply SourceMixedSchedule.subclause_cast_id
    simp only [SourceDecoderTraversal.nativeRootLiteral, SourceDecoderTraversal.compiled_decoder_slot,
      SourceDecoderTraversal.decoderComplete_slot, SourceDecoderTraversal.decoderStoredLiteral,
      nodeBit, Parameters.observations, root, List.get_eq_getElem]
  unfold DecoderRowOrigin
  rw [indexEqual]
  exact origins.nodes root root.isLt

end Controller.NativeProof.Wrapper
