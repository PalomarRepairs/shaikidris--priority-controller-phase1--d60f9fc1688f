module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.FoldProjection

@[expose] public section

/-! Bounded local truth cases produce ordinary-resolution subclauses from
available native rows. Only listed local variables are split; cofactor context
is retained in every target. Rows and literal aliases keep their actual IDs. -/
namespace Controller.NativeProof.LocalUnitCases
open Controller.CNF Controller.Resolution Controller.Resolution.Cases
open Controller.NativeProof.FoldProjection
variable {v : Nat} {state : State v} {context : Clause (Fin v)}

structure Premise (state : State v) (context : Clause (Fin v)) where
  clause : Clause (Fin v)
  row : AvailableSubclause state (context ++ clause)

def labelsOf (clause : Clause (Fin v)) : List (Fin v) := clause.map Prod.fst

def Covers (rows : List (Premise state context)) (guards : Clause (Fin v))
    (pending : List (Fin v)) : Prop :=
  ∀ premise ∈ rows, ∀ literal ∈ premise.clause,
    literal.1 ∈ labelsOf guards ∨ literal.1 ∈ pending

def Falsifies (values : Fin v → Bool) (guards : Clause (Fin v)) : Prop :=
  ∀ literal ∈ guards, ¬LiteralHolds values literal

def EntailsUnit (rows : List (Premise state context)) (goal : Literal (Fin v)) : Prop :=
  ∀ values, (∀ premise ∈ rows, ClauseHolds values premise.clause) → LiteralHolds values goal

structure Built (state : State v) (target : Clause (Fin v)) (budget : Nat) where
  tree : CaseTree v
  valid : ValidTree state target tree
  bound : inferenceBudget tree ≤ budget

theorem false_same (values : Fin v → Bool) (first second : Literal (Fin v))
    (same : first.1 = second.1) (one : ¬LiteralHolds values first)
    (two : ¬LiteralHolds values second) : first = second := by
  rcases first with ⟨x, p⟩
  rcases second with ⟨y, q⟩
  dsimp at same
  subst y
  cases p <;> cases q <;> cases values x <;> simp_all [LiteralHolds]

theorem update_falsifies (values : Fin v → Bool) (guards : Clause (Fin v))
    (old : Falsifies values guards) (label : Fin v) (fresh : label ∉ labelsOf guards)
    (value : Bool) : Falsifies (Function.update values label value)
      (guards ++ [(label, !value)]) := by
  intro literal member
  rcases List.mem_append.mp member with previous | added
  · have different : literal.1 ≠ label := by
      intro same
      exact fresh (same ▸ List.mem_map.mpr ⟨literal, previous, rfl⟩)
    simpa only [LiteralHolds, Function.update_of_ne different] using old literal previous
  · have same : literal = (label, !value) := by simpa using added
    subst literal
    cases value <;> simp [LiteralHolds]

theorem covers_tail (rows : List (Premise state context)) (guards : Clause (Fin v))
    (label : Fin v) (rest : List (Fin v)) (covers : Covers rows guards (label :: rest))
    (known : label ∈ labelsOf guards) : Covers rows guards rest := by
  intro premise member literal present
  rcases covers premise member literal present with old | pending
  · exact Or.inl old
  · rcases List.mem_cons.mp pending with same | later
    · exact Or.inl (same ▸ known)
    · exact Or.inr later

theorem covers_extend (rows : List (Premise state context)) (guards : Clause (Fin v))
    (label : Fin v) (rest : List (Fin v)) (covers : Covers rows guards (label :: rest))
    (value : Bool) : Covers rows (guards ++ [(label, value)]) rest := by
  intro premise member literal present
  rcases covers premise member literal present with old | pending
  · left
    simp only [labelsOf, List.map_append]
    exact List.mem_append_left _ old
  · rcases List.mem_cons.mp pending with same | later
    · left
      simp only [labelsOf, List.map_append, List.map_cons, List.map_nil, List.mem_append,
        List.mem_cons, List.not_mem_nil, or_false]
      exact Or.inr same
    · exact Or.inr later

def build (state : State v) (context : Clause (Fin v))
    (rows : List (Premise state context)) (goal : Literal (Fin v))
    (entails : EntailsUnit rows goal) (guards : Clause (Fin v))
    (goalPresent : goal ∈ guards) (values : Fin v → Bool) (falseGuards : Falsifies values guards)
    (pending : List (Fin v)) (covers : Covers rows guards pending) :
    Built state (context ++ guards) (2 ^ pending.length - 1) := by
  match pending with
  | [] =>
    let selected := rows.attach.find? fun premise =>
      !(Controller.CNF.OrderedFormula.Clause.eval values premise.val.clause)
    match found : selected with
    | none =>
      have allTrue : ∀ premise ∈ rows, ClauseHolds values premise.clause := by
        intro premise member
        have none := List.find?_eq_none.mp found
        have yes := none ⟨premise, member⟩ (List.mem_attach _ _)
        apply (clauseHolds_iff_eval _ _).mpr
        simpa using yes
      exact False.elim (falseGuards goal goalPresent (entails values allTrue))
    | some premise =>
      have failed : ¬ClauseHolds values premise.val.clause := by
        have no := List.find?_some found
        intro satisfied
        have yes := (clauseHolds_iff_eval _ _).mp satisfied
        simp [yes] at no
      let row := premise.val.row
      have subset : ClauseSubset row.clause (context ++ guards) := by
        intro literal member
        rcases List.mem_append.mp (row.subset literal member) with carried | localMember
        · exact List.mem_append.mpr (Or.inl carried)
        · have label := covers premise.val premise.property literal localMember
          have covered : literal.1 ∈ labelsOf guards := label.resolve_right (by simp)
          obtain ⟨guard, present, same⟩ := List.mem_map.mp covered
          have equal := false_same values literal guard same.symm
            (fun holds => failed ⟨literal, localMember, holds⟩) (falseGuards guard present)
          exact List.mem_append.mpr (Or.inr (equal.symm ▸ present))
      refine ⟨.leaf ⟨row.row.id, row.clause, []⟩, ?_, by simp [inferenceBudget]⟩
      exact ⟨row.row.present, row.row.bound, by simp [RUP.KnownReasons], by trivial,
        by simpa [RUP.negations] using subset⟩
  | label :: rest =>
    if known : label ∈ labelsOf guards then
      let tail := build state context rows goal entails guards goalPresent values falseGuards rest
        (covers_tail rows guards label rest covers known)
      refine ⟨tail.tree, tail.valid, ?_⟩
      have bound := tail.bound
      simp only [List.length_cons, Nat.pow_succ]
      omega
    else
      let left := build state context rows goal entails (guards ++ [(label, false)])
        (List.mem_append_left _ goalPresent) (Function.update values label true)
        (update_falsifies values guards falseGuards label known true) rest
        (covers_extend rows guards label rest covers false)
      let right := build state context rows goal entails (guards ++ [(label, true)])
        (List.mem_append_left _ goalPresent) (Function.update values label false)
        (update_falsifies values guards falseGuards label known false) rest
        (covers_extend rows guards label rest covers true)
      refine ⟨.fork (label, true) left.tree right.tree, ?_, ?_⟩
      · exact ⟨by simpa only [List.append_assoc, negate, Std.Sat.Literal.negate, Bool.not_true] using left.valid,
          by simpa only [List.append_assoc] using right.valid⟩
      · have one := left.bound
        have two := right.bound
        have positive : 0 < 2 ^ rest.length := Nat.pow_pos (by decide)
        simp only [inferenceBudget, List.length_cons, Nat.pow_succ]
        omega

def allVariables (rows : List (Premise state context)) (goal : Literal (Fin v)) : List (Fin v) :=
  ((rows.flatMap fun row => labelsOf row.clause).eraseDups).filter (fun label => label ≠ goal.1)

def unitUsing (state : State v) (context : Clause (Fin v)) (rows : List (Premise state context))
    (goal : Literal (Fin v)) (entails : EntailsUnit rows goal) (pending : List (Fin v))
    (covers : Covers rows [goal] pending) :
    SubclauseProjection state (context ++ [goal]) (2 ^ pending.length - 1) := by
  let values : Fin v → Bool := fun label => if label = goal.1 then !goal.2 else false
  have falsifies : Falsifies values [goal] := by
    intro literal member
    have same : literal = goal := by simpa using member
    subst literal
    cases polarity : goal.2 <;> simp [LiteralHolds, values, polarity]
  let cases := build state context rows goal entails [goal] (by simp) values falsifies
    pending covers
  let actual := compileTree state cases.tree
  have run := compileTree_run cases.tree state state (Nat.le_refl _) (fun _ _ => rfl)
    (context ++ [goal]) cases.valid
  exact ⟨actual.state, actual.steps, run.1,
    ⟨actual.clause, ⟨actual.rowId, run.2.1, run.2.2.1⟩, run.2.2.2⟩,
    (compileTree_count_le _ _).trans cases.bound⟩

def unit (state : State v) (context : Clause (Fin v)) (rows : List (Premise state context))
    (goal : Literal (Fin v)) (entails : EntailsUnit rows goal) :
    SubclauseProjection state (context ++ [goal]) (2 ^ (allVariables rows goal).length - 1) :=
  unitUsing state context rows goal entails (allVariables rows goal) (by
    intro row member literal present
    by_cases same : literal.1 = goal.1
    · exact Or.inl (by simp [labelsOf, same])
    · right
      simp only [allVariables, List.mem_filter, List.mem_eraseDups]
      exact ⟨List.mem_flatMap.mpr ⟨row, member, List.mem_map.mpr ⟨literal, present, rfl⟩⟩,
        by simpa using same⟩)

end Controller.NativeProof.LocalUnitCases
