module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.HornNativeReplay

@[expose] public section

/-! Concrete row-table transport discharges synthetic negative assumptions
and skips certified literal identities in an actual causal Horn reason list. -/
namespace Controller.NativeProof.HornRowTransport
open Controller.CNF Controller.Resolution Controller.Resolution.RUP
open Controller.NativeProof.FoldProjection Controller.NativeProof.HornNativeReplay

inductive Origin (handles : Fin u → Literal (Fin v)) (state : State v)
    (target : Clause (Fin v)) (clause : Clause (Fin u)) : Type
  | native (row : AvailableSubclause state (liftClause handles clause ++ target))
  | identity (first second : Fin u) (shape : clause = [(first, false), (second, true)])
      (same : handles first = handles second)
  | assumption (literal : Literal (Fin u)) (shape : clause = [literal])
      (negative : literal.2 = false) (discharged : negate (liftLiteral handles literal) ∈ target)

def Origin.keep (origin : Origin handles state target clause) : Bool :=
  match origin with
  | .native _ => true
  | .identity _ _ _ _ => false
  | .assumption _ _ _ _ => false

def Origin.nativeRow {handles : Fin u → Literal (Fin v)} {state : State v}
    {target : Clause (Fin v)} {clause : Clause (Fin u)}
    (origin : Origin handles state target clause) (retained : origin.keep = true) :
    AvailableSubclause state (liftClause handles clause ++ target) :=
  match actual : origin with
  | .native row => row
  | .identity _ _ _ _ => False.elim (by simpa only [actual, Origin.keep, Bool.false_eq_true] using retained)
  | .assumption _ _ _ _ => False.elim (by simpa only [actual, Origin.keep, Bool.false_eq_true] using retained)

abbrev ValidId (formula : FiniteFormula u) (id : Nat) := 0 < id ∧ id ≤ formula.clauses.size

def index (formula : FiniteFormula u) (id : Nat) (valid : ValidId formula id) : Fin formula.clauses.size :=
  ⟨id - 1, by have := valid.1; have := valid.2; omega⟩

theorem validId (formula : FiniteFormula u) (id : Nat) (clause : Clause (Fin u))
    (present : (initialState formula).rows id = some clause)
    (bound : id ≤ (initialState formula).lastId) : ValidId formula id := by
  refine ⟨?_, bound⟩
  by_contra absent
  have zero : id = 0 := by omega
  simp [zero] at present

theorem index_clause (formula : FiniteFormula u) (id : Nat) (clause : Clause (Fin u))
    (valid : ValidId formula id) (present : (initialState formula).rows id = some clause) :
    formula.clauses[(index formula id valid).val] = clause := by
  have same : (index formula id valid).val + 1 = id := by have := valid.1; simp only [index]; omega
  have original := initialState_row formula (index formula id valid).val (index formula id valid).isLt
  rw [same, present] at original
  exact (Option.some.inj original).symm

def keep (formula : FiniteFormula u) (handles : Fin u → Literal (Fin v))
    (state : State v) (target : Clause (Fin v))
    (rows : ∀ row : Fin formula.clauses.size, Origin handles state target formula.clauses[row.val])
    (reason : RowReason u) : Bool :=
  if valid : ValidId formula reason.rowId then (rows (index formula reason.rowId valid)).keep else false

theorem identity_skippable (handles : Fin u → Literal (Fin v))
    (reason : RowReason u) (earlier : List (RowReason u)) (target : Clause (Fin v))
    (valid : ReasonEarlier reason.entry.pivot reason.entry.clause (negations (earlier.map RowReason.entry) ++ []))
    (first second : Fin u) (shape : reason.entry.clause = [(first, false), (second, true)])
    (same : handles first = handles second) :
    negate (liftLiteral handles reason.entry.pivot) ∈ remaining handles earlier target := by
  have pivot := valid.1
  rw [shape] at pivot
  simp only [List.mem_cons, List.not_mem_nil, or_false] at pivot
  rcases pivot with one | two
  · have other := valid.2 (second, true) (by simp [shape]) (by rw [one]; simp)
    have mapped : liftLiteral handles (second, true) ∈ liftClause handles
        (negations (earlier.map RowReason.entry) ++ []) := List.mem_map.mpr ⟨(second, true), other, rfl⟩
    rw [List.append_nil] at mapped
    have converted : liftLiteral handles (second, true) ∈
        earlier.map (fun reason => negate (liftLiteral handles reason.entry.pivot)) := by
      simpa only [← lift_negations, liftClause] using mapped
    apply List.mem_append_left
    simpa only [one, liftLiteral, ite_true, Bool.false_eq_true, ite_false, negate_negate, same] using converted
  · have other := valid.2 (first, false) (by simp [shape]) (by rw [two]; simp)
    have mapped : liftLiteral handles (first, false) ∈ liftClause handles
        (negations (earlier.map RowReason.entry) ++ []) := List.mem_map.mpr ⟨(first, false), other, rfl⟩
    rw [List.append_nil] at mapped
    have converted : liftLiteral handles (first, false) ∈
        earlier.map (fun reason => negate (liftLiteral handles reason.entry.pivot)) := by
      simpa only [← lift_negations, liftClause] using mapped
    apply List.mem_append_left
    simpa only [two, liftLiteral, ite_true, Bool.false_eq_true, ite_false, same] using converted

def reasonRows (formula : FiniteFormula u) (handles : Fin u → Literal (Fin v))
    (state : State v) (target : Clause (Fin v))
    (rows : ∀ row : Fin formula.clauses.size, Origin handles state target formula.clauses[row.val])
    (reasons : List (RowReason u)) (known : KnownReasons (initialState formula) reasons) :
    ReplayRows handles state target (keep formula handles state target rows) reasons := by
  intro reason member retained
  have available := known reason member
  have valid := validId formula reason.rowId reason.entry.clause available.1 available.2.1
  have same := index_clause formula reason.rowId reason.entry.clause valid available.1
  have retainedRow : (rows (index formula reason.rowId valid)).keep = true := by
    simpa only [keep, dite_eq_left valid] using retained
  exact Eq.mp (congrArg (fun clause => AvailableSubclause state (liftClause handles clause ++ target)) same)
    ((rows (index formula reason.rowId valid)).nativeRow retainedRow)

theorem skippable (formula : FiniteFormula u) (handles : Fin u → Literal (Fin v))
    (state : State v) (target : Clause (Fin v))
    (rows : ∀ row : Fin formula.clauses.size, Origin handles state target formula.clauses[row.val])
    (reasons : List (RowReason u)) (known : KnownReasons (initialState formula) reasons)
    (valid : ValidReasons [] (reasons.map RowReason.entry)) :
    Skippable handles target (keep formula handles state target rows) reasons := by
  induction reasons with
  | nil => trivial
  | cons reason earlier ih =>
    refine ⟨?_, ih (fun old member => known old (List.mem_cons_of_mem _ member)) valid.2⟩
    intro omitted
    have original := known reason List.mem_cons_self
    have validId := validId formula reason.rowId reason.entry.clause original.1 original.2.1
    have same := index_clause formula reason.rowId reason.entry.clause validId original.1
    have dropped : (rows (index formula reason.rowId validId)).keep ≠ true := by
      simpa only [keep, dite_eq_left validId] using omitted
    cases origin : rows (index formula reason.rowId validId) with
    | native row => simp [origin, Origin.keep] at dropped
    | identity first second shape equal =>
      exact identity_skippable handles reason earlier target valid.1 first second (same.symm.trans shape) equal
    | assumption literal shape negative discharged =>
      have clauseEq := same.symm.trans shape
      have pivotEq : reason.entry.pivot = literal := by simpa only [clauseEq, List.mem_singleton] using valid.1.1
      exact List.mem_append_right _ (by simpa only [pivotEq] using discharged)

def conflictRow (formula : FiniteFormula u) (conflict : HornTrail.Conflict u)
    (certified : HornTrail.Certified formula conflict) (positive : HornTrail.negative conflict.clause = none)
    (handles : Fin u → Literal (Fin v)) (state : State v) (target : Clause (Fin v))
    (rows : ∀ row : Fin formula.clauses.size, Origin handles state target formula.clauses[row.val]) :
    AvailableSubclause state (liftClause handles conflict.clause ++ target) := by
  have valid := validId formula conflict.rowId conflict.clause certified.present certified.bound
  have same := index_clause formula conflict.rowId conflict.clause valid certified.present
  have retained : (rows (index formula conflict.rowId valid)).keep = true := by
    cases origin : rows (index formula conflict.rowId valid) with
    | native row => rfl
    | identity first second shape equal =>
      have clauseEq := same.symm.trans shape
      have impossible := HornTrail.negative_none conflict.clause positive (first, false) (by simp [clauseEq])
      exact False.elim (Bool.false_ne_true impossible)
    | assumption literal shape negative discharged =>
      have clauseEq := same.symm.trans shape
      have impossible := HornTrail.negative_none conflict.clause positive literal (by simp [clauseEq])
      exact False.elim (Bool.false_ne_true (negative.symm.trans impossible))
  exact Eq.mp (congrArg (fun clause => AvailableSubclause state (liftClause handles clause ++ target)) same)
    ((rows (index formula conflict.rowId valid)).nativeRow retained)

def replay (formula : FiniteFormula u) (conflict : HornTrail.Conflict u)
    (certified : HornTrail.Certified formula conflict) (positive : HornTrail.negative conflict.clause = none)
    (handles : Fin u → Literal (Fin v)) (state : State v) (target : Clause (Fin v))
    (rows : ∀ row : Fin formula.clauses.size, Origin handles state target formula.clauses[row.val]) :
    SubclauseProjection state target conflict.reasons.length :=
  replayConflict formula conflict certified handles state target (keep formula handles state target rows)
    (reasonRows formula handles state target rows conflict.reasons certified.known)
    (skippable formula handles state target rows conflict.reasons certified.known certified.valid)
    (conflictRow formula conflict certified positive handles state target rows)

end Controller.NativeProof.HornRowTransport
