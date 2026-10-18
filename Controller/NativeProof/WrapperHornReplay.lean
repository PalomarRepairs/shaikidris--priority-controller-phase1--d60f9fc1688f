module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.WrapperHealthyOnePreparation

@[expose] public section

/-! Causal Horn replay retains each native premise's original provenance. -/
namespace Controller.NativeProof.Wrapper
open Controller.CNF Controller.Resolution Controller.Resolution.RUP
open Controller.NativeProof.FoldProjection Controller.NativeProof.SourceStageCongruence
open Controller.NativeProof.SourceBusSchedule Controller.NativeProof.SourceFoldProvenance
open Controller.NativeProof.SourceMismatchHandles Controller.NativeProof.HornNativeReplay
variable {u v : Nat}

theorem hornNativeReplay_supported (handles : Fin u → Literal (Fin v)) (state : State v)
    (target : Clause (Fin v)) (keep : RowReason u → Bool) (reasons : List (RowReason u))
    (rows : ReplayRows handles state target keep reasons)
    (valid : ValidReasons [] (reasons.map RowReason.entry))
    (discharged : Skippable handles target keep reasons)
    (current : AvailableSubclause state (remaining handles reasons target))
    (originalCount : Nat) (allowed : Nat → Prop) (prior : List (Step v))
    (supported : TraceOriginalSupport originalCount allowed prior)
    (originalBound : ∀ row, allowed row → row ≤ originalCount) (bound : originalCount ≤ state.lastId)
    (rowOrigins : ∀ reason member retained, ResultOrigin originalCount allowed prior (rows reason member retained).row.id)
    (currentOrigin : ResultOrigin originalCount allowed prior current.row.id) :
    let actual := HornNativeReplay.replay handles state target keep reasons rows valid discharged current
    TraceOriginalSupport originalCount allowed (prior ++ actual.steps) ∧
      ResultOrigin originalCount allowed (prior ++ actual.steps) actual.result.row.id := by
  induction reasons generalizing state prior with
  | nil =>
    simpa only [HornNativeReplay.replay, List.append_nil] using And.intro supported currentOrigin
  | cons reason earlier ih =>
    have tailValid : ValidReasons [] (earlier.map RowReason.entry) := valid.2
    have tailDischarge : Skippable handles target keep earlier := discharged.2
    by_cases retained : keep reason = true
    · let row := rows reason List.mem_cons_self retained
      let rest := remaining handles earlier target
      let pivot := liftLiteral handles reason.entry.pivot
      let left : AvailableSubclause state (negate pivot :: rest) := current
      let right : AvailableSubclause state (pivot :: rest) := retarget row (by
        intro literal member
        rcases List.mem_append.mp member with premise | carried
        · have included := reason_subset handles reason earlier valid.1 literal premise
          rcases List.mem_cons.mp included with same | old
          · exact List.mem_cons.mpr (Or.inl same)
          · exact List.mem_cons.mpr (Or.inr (List.mem_append_left target
              (by simpa only [remaining, List.append_nil] using old)))
        · exact List.mem_cons.mpr (Or.inr (List.mem_append_right _ carried)))
      let joined := longMerge state pivot rest rest left right
      let next : AvailableSubclause joined.state (remaining handles earlier target) :=
        retarget (longMerge_result state pivot rest rest left right) (by
          intro literal member
          exact (List.mem_append.mp member).elim id id)
      let tailRows : ReplayRows handles joined.state target keep earlier := fun r member used =>
        afterTrace (rows r (List.mem_cons_of_mem _ member) used) joined.state joined.steps
          (longMerge_run state pivot rest rest left right)
      have joinedOrigins := SourceMixedSchedule.longMerge_supported originalCount allowed prior state pivot rest rest left right
        supported originalBound bound currentOrigin (rowOrigins reason List.mem_cons_self retained)
      have tailRowOrigins : ∀ r member used, ResultOrigin originalCount allowed (prior ++ joined.steps)
          (tailRows r member used).row.id := fun r member used =>
        resultOrigin_append_right _ _ prior joined.steps _ (rowOrigins r (List.mem_cons_of_mem _ member) used)
      have nextBound : originalCount ≤ joined.state.lastId :=
        Nat.le_trans bound (runSteps_lastId_le (longMerge_run state pivot rest rest left right))
      have tail := ih joined.state tailRows tailValid tailDischarge next (prior ++ joined.steps)
        joinedOrigins.1 nextBound tailRowOrigins joinedOrigins.2
      simpa only [HornNativeReplay.replay, HornNativeReplay.replayStep, projection_dite_result_id, dite_eq_left retained, row, rest, pivot, left, right,
        joined, next, tailRows, List.append_assoc] using tail
    · let next : AvailableSubclause state (remaining handles earlier target) := retarget current (by
        intro literal member
        rcases List.mem_cons.mp member with same | old
        · rw [same]
          exact discharged.1 retained
        · exact old)
      let tailRows : ReplayRows handles state target keep earlier := fun r member => rows r (List.mem_cons_of_mem _ member)
      have tail := ih state tailRows tailValid tailDischarge next prior supported bound
        (fun r member used => rowOrigins r (List.mem_cons_of_mem _ member) used) currentOrigin
      simpa only [HornNativeReplay.replay, HornNativeReplay.replayStep, projection_dite_result_id, dite_eq_right retained, next, tailRows] using tail

end Controller.NativeProof.Wrapper
