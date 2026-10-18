module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.WrapperOtherQualifiers

@[expose] public section

/-! Healthy qualifier tables retain the origins of every emitted unit. -/
namespace Controller.NativeProof.Wrapper
open Controller.CNF Controller.Resolution Controller.Native Controller.Native.SourceController
open Controller.NativeProof.FoldProjection Controller.NativeProof.SourceFoldProjection
open Controller.NativeProof.SourceStageCongruence Controller.NativeProof.SourceStagePolarity
open Controller.NativeProof.SourceStageXor Controller.NativeProof.SourceFoldOccurrences
open Controller.NativeProof.SourceBusAdvance Controller.NativeProof.SourceBusSchedule
open Controller.NativeProof.SourceMixedSchedule Controller.NativeProof.SourceHealthyMasks
open Controller.NativeProof.SourceFoldProvenance Controller.NativeProof.SourceMismatchHandles
open Controller.NativeProof.SourceQualifierSchedule
variable {parameters : Parameters} {v : Nat}

theorem projection_dite_supported (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    {clause : Clause (Fin v)} {budget : Nat}
    (condition : Prop) [Decidable condition]
    (yes : condition → SubclauseProjection prefixState.state clause budget)
    (no : ¬condition → SubclauseProjection prefixState.state clause budget)
    (yesSupported : ∀ proof, ProjectionOriginalSupport rename prefixState (yes proof))
    (noSupported : ∀ proof, ProjectionOriginalSupport rename prefixState (no proof)) :
    ProjectionOriginalSupport rename prefixState (dite condition yes no) := by
  by_cases proof : condition
  · rw [dite_eq_left proof]; exact yesSupported proof
  · rw [dite_eq_right proof]; exact noSupported proof

theorem healthyQualifierAt_origins (rename : Nat → Fin v)
    (table : SourceHealthyMasks.Table (parameters := parameters) rename (laterBuses (parameters := parameters)).length)
    (drive : parameters.drive = true) (channel : Fin parameters.channels) (origins : HealthyMaskOrigins rename table) :
    ProjectionOriginalSupport rename table.proofPrefix (SourceHealthyQualifiers.qualifierAt rename table drive channel) := by
  unfold SourceHealthyQualifiers.qualifierAt
  dsimp only [id]
  apply projection_dite_supported
  · intro same
    subst channel
    apply ControllerOrigins.projection_indices_mpr_supported rename table.proofPrefix
      (by simp only [decide_true, valueLiteral, ite_true])
      (by simp only [SourceHealthyQualifiers.qualifierBudgetAt, ite_eq_left rfl, ite_true]) _ _
    exact healthyTargetQualifier_origins rename table drive origins
  · intro different
    apply ControllerOrigins.projection_indices_mpr_supported rename table.proofPrefix
      (by simp only [decide_eq_false different, valueLiteral, Bool.false_eq_true, ite_false])
      (by simp only [SourceHealthyQualifiers.qualifierBudgetAt, ite_eq_right different]) _ _
    exact healthyOtherQualifier_origins rename table channel different origins

structure QualifierBankOrigins (rename : Nat → Fin v)
    (start : SourceHealthyMasks.Table (parameters := parameters) rename (laterBuses (parameters := parameters)).length)
    {channels : List (Fin parameters.channels)}
    (bank : SourceHealthyQualifiers.QualifierBank rename start channels) : Prop where
  table : HealthyMaskOrigins rename bank.table
  sameSteps : bank.table.proofPrefix.steps = start.proofPrefix.steps ++ bank.steps
  rows : ∀ channel member, ControllerRowOrigin rename bank.table.proofPrefix (bank.rows channel member)

theorem healthyBuildQualifiers_origins (rename : Nat → Fin v)
    (table : SourceHealthyMasks.Table (parameters := parameters) rename (laterBuses (parameters := parameters)).length)
    (drive : parameters.drive = true) (channels : List (Fin parameters.channels)) (origins : HealthyMaskOrigins rename table) :
    QualifierBankOrigins rename table (SourceHealthyQualifiers.buildQualifiers rename table drive channels) := by
  induction channels generalizing table with
  | nil =>
    refine ⟨origins, ?_, ?_⟩
    · simp only [SourceHealthyQualifiers.buildQualifiers, List.append_nil]
    · intro channel member; simp at member
  | cons channel rest ih =>
    let one := SourceHealthyQualifiers.qualifierAt rename table drive channel
    let next := table.afterTrace one.state one.steps one.checked
    let tailBank := SourceHealthyQualifiers.buildQualifiers rename next drive rest
    have oneOrigins := healthyQualifierAt_origins rename table drive channel origins
    have nextOrigins := HealthyMaskOrigins.afterTrace rename table origins one.state one.steps one.checked oneOrigins.1
    have tail := ih next nextOrigins
    refine ⟨tail.table, ?_, ?_⟩
    · change tailBank.table.proofPrefix.steps = table.proofPrefix.steps ++ (one.steps ++ tailBank.steps)
      rw [tail.sameSteps]
      simp only [next, SourceHealthyMasks.Table.afterTrace, SourcePrefix.extend, List.append_assoc]
      rfl
    · intro query member
      by_cases equal : query = channel
      · subst query
        have indexEqual : ((SourceHealthyQualifiers.buildQualifiers rename table drive (channel :: rest)).rows channel member).row.id =
            one.result.row.id := by
          simp only [SourceHealthyQualifiers.buildQualifiers, id, SourceMixedSchedule.subclause_dite_id,
            dite_true, dite_eq_left rfl, afterTrace]
          rfl
        unfold ControllerRowOrigin
        rw [indexEqual]
        change ResultOrigin (formula parameters).clauses.size
          (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename) tailBank.table.proofPrefix.steps _
        rw [tail.sameSteps]
        exact resultOrigin_append_right _ _ (table.proofPrefix.steps ++ one.steps) tailBank.steps _ oneOrigins.2
      · have indexEqual : ((SourceHealthyQualifiers.buildQualifiers rename table drive (channel :: rest)).rows query member).row.id =
            (tailBank.rows query ((List.mem_cons.mp member).resolve_left equal)).row.id := by
          simp only [SourceHealthyQualifiers.buildQualifiers, id, SourceMixedSchedule.subclause_dite_id,
            dite_eq_right equal, tailBank, next, one]
        unfold ControllerRowOrigin
        rw [indexEqual]
        exact tail.rows query ((List.mem_cons.mp member).resolve_left equal)

theorem healthyAllQualifiers_origins (rename : Nat → Fin v) (drive : parameters.drive = true) :
    QualifierBankOrigins rename (SourceHealthyMasks.allMasks (parameters := parameters) rename drive)
      (SourceHealthyQualifiers.allQualifiers rename drive) :=
  healthyBuildQualifiers_origins rename _ drive _ (healthyAllMasks_origins rename drive)

end Controller.NativeProof.Wrapper
