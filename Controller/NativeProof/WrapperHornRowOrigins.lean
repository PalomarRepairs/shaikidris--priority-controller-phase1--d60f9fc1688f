module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.WrapperHornReplay

@[expose] public section

/-! Synthetic Horn rows are discharged; native rows retain their source origins. -/
namespace Controller.NativeProof.Wrapper
open Controller.CNF Controller.Resolution Controller.Resolution.RUP
open Controller.NativeProof.FoldProjection Controller.NativeProof.SourceStageCongruence
open Controller.NativeProof.SourceBusSchedule Controller.NativeProof.SourceFoldProvenance
open Controller.NativeProof.SourceMismatchHandles Controller.NativeProof.HornNativeReplay
variable {u v : Nat}

def HornOriginResultOrigin (originalCount : Nat) (allowed : Nat → Prop) (prior : List (Step v))
    {handles : Fin u → Literal (Fin v)} {state : State v} {target : Clause (Fin v)} {clause : Clause (Fin u)}
    (origin : HornRowTransport.Origin handles state target clause) : Prop :=
  match (generalizing := false) origin with
  | .native row => ResultOrigin originalCount allowed prior row.row.id
  | .identity _ _ _ _ => True
  | .assumption _ _ _ _ => True

theorem hornNativeRow_origin (originalCount : Nat) (allowed : Nat → Prop) (prior : List (Step v))
    {handles : Fin u → Literal (Fin v)} {state : State v} {target : Clause (Fin v)} {clause : Clause (Fin u)}
    (origin : HornRowTransport.Origin handles state target clause)
    (supported : HornOriginResultOrigin originalCount allowed prior origin) (retained : origin.keep = true) :
    ResultOrigin originalCount allowed prior (origin.nativeRow retained).row.id := by
  cases origin with
  | native row => exact supported
  | identity first second shape same => simp only [HornRowTransport.Origin.keep, Bool.false_eq_true] at retained
  | assumption literal shape negative discharged => simp only [HornRowTransport.Origin.keep, Bool.false_eq_true] at retained

theorem hornReasonRows_origins (formula : FiniteFormula u) (handles : Fin u → Literal (Fin v))
    (state : State v) (target : Clause (Fin v))
    (rows : ∀ index : Fin formula.clauses.size, HornRowTransport.Origin handles state target formula.clauses[index.val])
    (reasons : List (RowReason u)) (known : KnownReasons (initialState formula) reasons)
    (originalCount : Nat) (allowed : Nat → Prop) (prior : List (Step v))
    (origins : ∀ index, HornOriginResultOrigin originalCount allowed prior (rows index))
    (reason : RowReason u) (member : reason ∈ reasons)
    (retained : HornRowTransport.keep formula handles state target rows reason = true) :
    ResultOrigin originalCount allowed prior
      (HornRowTransport.reasonRows formula handles state target rows reasons known reason member retained).row.id := by
  unfold HornRowTransport.reasonRows
  dsimp only [id]
  apply available_indices_mp_resultOrigin originalCount allowed prior
    (congrArg (fun clause => liftClause handles clause ++ target)
      (HornRowTransport.index_clause formula reason.rowId reason.entry.clause
        (HornRowTransport.validId formula reason.rowId reason.entry.clause (known reason member).1 (known reason member).2.1)
        (known reason member).1)) _
  apply hornNativeRow_origin
  exact origins _

theorem hornConflictRow_origins (formula : FiniteFormula u) (conflict : HornTrail.Conflict u)
    (certified : HornTrail.Certified formula conflict) (positive : HornTrail.negative conflict.clause = none)
    (handles : Fin u → Literal (Fin v)) (state : State v) (target : Clause (Fin v))
    (rows : ∀ index : Fin formula.clauses.size, HornRowTransport.Origin handles state target formula.clauses[index.val])
    (originalCount : Nat) (allowed : Nat → Prop) (prior : List (Step v))
    (origins : ∀ index, HornOriginResultOrigin originalCount allowed prior (rows index)) :
    ResultOrigin originalCount allowed prior
      (HornRowTransport.conflictRow formula conflict certified positive handles state target rows).row.id := by
  unfold HornRowTransport.conflictRow
  dsimp only [id]
  apply available_indices_mp_resultOrigin originalCount allowed prior
    (congrArg (fun clause => liftClause handles clause ++ target)
      (HornRowTransport.index_clause formula conflict.rowId conflict.clause
        (HornRowTransport.validId formula conflict.rowId conflict.clause certified.present certified.bound) certified.present)) _
  apply hornNativeRow_origin
  exact origins _

theorem hornRowReplay_supported (formula : FiniteFormula u) (conflict : HornTrail.Conflict u)
    (certified : HornTrail.Certified formula conflict) (positive : HornTrail.negative conflict.clause = none)
    (handles : Fin u → Literal (Fin v)) (state : State v) (target : Clause (Fin v))
    (rows : ∀ index : Fin formula.clauses.size, HornRowTransport.Origin handles state target formula.clauses[index.val])
    (originalCount : Nat) (allowed : Nat → Prop) (prior : List (Step v))
    (supported : TraceOriginalSupport originalCount allowed prior)
    (originalBound : ∀ row, allowed row → row ≤ originalCount) (bound : originalCount ≤ state.lastId)
    (origins : ∀ index, HornOriginResultOrigin originalCount allowed prior (rows index)) :
    let actual := HornRowTransport.replay formula conflict certified positive handles state target rows
    TraceOriginalSupport originalCount allowed (prior ++ actual.steps) ∧
      ResultOrigin originalCount allowed (prior ++ actual.steps) actual.result.row.id := by
  unfold HornRowTransport.replay HornNativeReplay.replayConflict
  apply hornNativeReplay_supported
  · exact supported
  · exact originalBound
  · exact bound
  · exact hornReasonRows_origins formula handles state target rows conflict.reasons certified.known
      originalCount allowed prior origins
  · exact hornConflictRow_origins formula conflict certified positive handles state target rows
      originalCount allowed prior origins

end Controller.NativeProof.Wrapper
