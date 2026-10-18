module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.HornTrail
public import Controller.NativeProof.FoldProjection

@[expose] public section

/-! Native replay of an abstract causal Horn trail. Each retained abstract
row is represented by an available native subclause. Literal maps may contain
signed aliases; missing pivots retain stronger clauses. Synthetic assumptions
contribute target literals and never become resolution parents. -/
namespace Controller.NativeProof.HornNativeReplay
open Controller.CNF Controller.Resolution Controller.Resolution.RUP
open Controller.NativeProof.FoldProjection

def liftLiteral (handles : Fin u → Literal (Fin v)) (literal : Literal (Fin u)) :
    Literal (Fin v) := if literal.2 then handles literal.1 else negate (handles literal.1)

def liftClause (handles : Fin u → Literal (Fin v)) (clause : Clause (Fin u)) :=
  clause.map (liftLiteral handles)

@[simp] theorem liftLiteral_negate (handles : Fin u → Literal (Fin v))
    (literal : Literal (Fin u)) :
    liftLiteral handles (negate literal) = negate (liftLiteral handles literal) := by
  rcases literal with ⟨label, polarity⟩
  cases polarity <;> simp [liftLiteral, negate, Std.Sat.Literal.negate]

theorem liftClause_subset (handles : Fin u → Literal (Fin v))
    (first second : Clause (Fin u)) (subset : ClauseSubset first second) :
    ClauseSubset (liftClause handles first) (liftClause handles second) := by
  intro literal member
  obtain ⟨source, present, same⟩ := List.mem_map.mp member
  exact List.mem_map.mpr ⟨source, subset source present, same⟩

theorem lift_negations (handles : Fin u → Literal (Fin v))
    (reasons : List (RowReason u)) :
    liftClause handles (negations (reasons.map RowReason.entry)) =
      reasons.map (fun reason => negate (liftLiteral handles reason.entry.pivot)) := by
  simp [liftClause, negations, List.map_map, Function.comp_def]

def remaining (handles : Fin u → Literal (Fin v)) (reasons : List (RowReason u))
    (target : Clause (Fin v)) : Clause (Fin v) :=
  reasons.map (fun reason => negate (liftLiteral handles reason.entry.pivot)) ++ target

theorem reason_subset (handles : Fin u → Literal (Fin v))
    (reason : RowReason u) (earlier : List (RowReason u))
    (valid : ReasonEarlier reason.entry.pivot reason.entry.clause
      (negations (earlier.map RowReason.entry) ++ [])) :
    ClauseSubset (liftClause handles reason.entry.clause)
      (liftLiteral handles reason.entry.pivot :: remaining handles earlier []) := by
  intro literal member
  obtain ⟨source, present, same⟩ := List.mem_map.mp member
  by_cases pivot : source = reason.entry.pivot
  · exact List.mem_cons.mpr (Or.inl (same.symm.trans (congrArg (liftLiteral handles) pivot)))
  · apply List.mem_cons.mpr
    right
    have old := valid.2 source present pivot
    have mapped := liftClause_subset handles _ _ (fun x hx => hx) (liftLiteral handles source)
      (List.mem_map.mpr ⟨source, old, rfl⟩)
    simpa only [remaining, ← lift_negations, List.append_nil, liftClause, List.map_append,
      List.map_nil, List.append_nil, same] using mapped

/-- A table stores real native rows for retained reasons, while discarded
assumptions are discharged into the target. -/
def ReplayRows (handles : Fin u → Literal (Fin v)) (state : State v)
    (target : Clause (Fin v)) (keep : RowReason u → Bool)
    (reasons : List (RowReason u)) : Type :=
  ∀ reason ∈ reasons, keep reason = true →
    AvailableSubclause state (liftClause handles reason.entry.clause ++ target)

/-- Discarded assumptions occur in the target. Literal-identity aliases may
instead occur among earlier falsified literals; neither requires a row. -/
def Skippable (handles : Fin u → Literal (Fin v)) (target : Clause (Fin v))
    (keep : RowReason u → Bool) : List (RowReason u) → Prop
  | [] => True
  | reason :: earlier =>
      (keep reason ≠ true → negate (liftLiteral handles reason.entry.pivot) ∈
        remaining handles earlier target) ∧ Skippable handles target keep earlier

theorem assumptions_skippable (handles : Fin u → Literal (Fin v))
    (target : Clause (Fin v)) (keep : RowReason u → Bool) (reasons : List (RowReason u))
    (discharged : ∀ reason ∈ reasons, keep reason ≠ true →
      negate (liftLiteral handles reason.entry.pivot) ∈ target) :
    Skippable handles target keep reasons := by
  induction reasons with
  | nil => trivial
  | cons reason earlier ih =>
    refine ⟨?_, ih (fun r member => discharged r (List.mem_cons_of_mem _ member))⟩
    intro omitted
    exact List.mem_append.mpr (Or.inr (discharged reason List.mem_cons_self omitted))

/-- Replay one reason while keeping recursive proof assembly behind an explicit
continuation with the original causal-row and discharge premises. -/
def replayStep (handles : Fin u → Literal (Fin v)) (state : State v)
    (target : Clause (Fin v)) (keep : RowReason u → Bool)
    (reason : RowReason u) (earlier : List (RowReason u))
    (rows : ReplayRows handles state target keep (reason :: earlier))
    (valid : ValidReasons [] ((reason :: earlier).map RowReason.entry))
    (discharged : Skippable handles target keep (reason :: earlier))
    (current : AvailableSubclause state (remaining handles (reason :: earlier) target))
    (recurse : ∀ (next : State v),
      ReplayRows handles next target keep earlier →
      ValidReasons [] (earlier.map RowReason.entry) →
      Skippable handles target keep earlier →
      AvailableSubclause next (remaining handles earlier target) →
      SubclauseProjection next target earlier.length) :
    SubclauseProjection state target (reason :: earlier).length := by
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
    let tail := recurse joined.state tailRows tailValid tailDischarge next
    refine ⟨tail.state, joined.steps ++ tail.steps, ?_, tail.result, ?_⟩
    · rw [runSteps_append, longMerge_run state pivot rest rest left right]
      exact tail.checked
    · have bound := tail.count
      have one : joined.steps.length ≤ 1 := longMerge_count state pivot rest rest left right
      simp only [List.length_append, List.length_cons]
      omega
  · let next : AvailableSubclause state (remaining handles earlier target) := retarget current (by
      intro literal member
      rcases List.mem_cons.mp member with same | old
      · rw [same]
        exact discharged.1 retained
      · exact old)
    let tailRows : ReplayRows handles state target keep earlier :=
      fun r member => rows r (List.mem_cons_of_mem _ member)
    let tail := recurse state tailRows tailValid tailDischarge next
    exact ⟨tail.state, tail.steps, tail.checked, tail.result,
      Nat.le_trans tail.count (by simp)⟩


def replay (handles : Fin u → Literal (Fin v)) (state : State v)
    (target : Clause (Fin v)) (keep : RowReason u → Bool)
    (reasons : List (RowReason u))
    (rows : ReplayRows handles state target keep reasons)
    (valid : ValidReasons [] (reasons.map RowReason.entry))
    (discharged : Skippable handles target keep reasons)
    (current : AvailableSubclause state (remaining handles reasons target)) :
    SubclauseProjection state target reasons.length := by
  match reasons with
  | [] => exact ⟨state, [], rfl, current, by simp⟩
  | reason :: earlier =>
    exact replayStep handles state target keep reason earlier rows valid discharged current
      (fun next tailRows tailValid tailDischarge nextClause =>
        replay handles next target keep earlier tailRows tailValid tailDischarge nextClause)

/-- A certified abstract conflict supplies the checked ordinary-resolution
native replay. The generated steps retain the available stronger native rows. -/
def replayConflict (abstract : FiniteFormula u) (conflict : HornTrail.Conflict u)
    (certified : HornTrail.Certified abstract conflict)
    (handles : Fin u → Literal (Fin v)) (state : State v)
    (target : Clause (Fin v)) (keep : RowReason u → Bool)
    (rows : ReplayRows handles state target keep conflict.reasons)
    (discharged : Skippable handles target keep conflict.reasons)
    (current : AvailableSubclause state (liftClause handles conflict.clause ++ target)) :
    SubclauseProjection state target conflict.reasons.length :=
  replay handles state target keep conflict.reasons rows certified.valid discharged
    (retarget current (by
      intro literal member
      rcases List.mem_append.mp member with premise | carried
      · have inclusion := liftClause_subset handles _ _ certified.conflict literal premise
        rw [lift_negations] at inclusion
        exact List.mem_append.mpr (Or.inl inclusion)
      · exact List.mem_append.mpr (Or.inr carried)))

end Controller.NativeProof.HornNativeReplay
