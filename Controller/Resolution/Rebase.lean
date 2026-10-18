module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Resolution.Trace

@[expose] public section

/-! Replay resolution derivations after an already accepted prefix. Original
clause IDs are fixed; every derived ID is shifted by the prefix's extra span.
The correspondence covers every source row, including absent rows. -/
namespace Controller.Resolution.Rebase
open CNF

def rebaseId (originalCount offset id : Nat) : Nat :=
  if id ≤ originalCount then id else id + offset

def rebaseStep (originalCount offset : Nat) (s : Step v) : Step v :=
  ⟨rebaseId originalCount offset s.id, rebaseId originalCount offset s.left,
    rebaseId originalCount offset s.right, s.pivot, s.clause⟩

theorem rebaseId_original {id n d : Nat} (h : id ≤ n) : rebaseId n d id = id := by
  simp [rebaseId, h]

theorem rebaseId_derived {id n d : Nat} (h : n < id) : rebaseId n d id = id + d := by
  simp [rebaseId, Nat.not_le.mpr h]

theorem rebaseId_strictMono (n d : Nat) : StrictMono (rebaseId n d) := by
  intro a b hab
  unfold rebaseId
  split_ifs <;> omega

theorem rebaseId_injective (n d : Nat) : Function.Injective (rebaseId n d) :=
  (rebaseId_strictMono n d).injective

structure Matches (n d : Nat) (source target : State v) : Prop where
  originalBound : n ≤ source.lastId
  last : target.lastId = source.lastId + d
  rows : ∀ id, target.rows (rebaseId n d id) = source.rows id

theorem matches_insert {id : Nat} {source target : State v} (h : Matches n d source target)
    (hid : source.lastId < id) (c : Clause (Fin v)) :
    Matches n d (insertRow source id c) (insertRow target (rebaseId n d id) c) := by
  have hn : n < id := lt_of_le_of_lt h.originalBound hid
  refine ⟨by simp only [insertRow]; omega, ?_, ?_⟩
  · simp only [insertRow, rebaseId_derived hn]
  · intro j
    by_cases hj : j = id
    · subst j; simp
    · have hj' : rebaseId n d j ≠ rebaseId n d id :=
        fun he => hj (rebaseId_injective n d he)
      simp only [insertRow, ite_eq_right hj', ite_eq_right hj]
      exact h.rows j

theorem applyStep_rebase {source next target : State v} {s : Step v}
    (hm : Matches n d source target) (hs : applyStep source s = some next) :
    ∃ nextTarget, applyStep target (rebaseStep n d s) = some nextTarget ∧
      Matches n d next nextTarget := by
  obtain ⟨l, r, hl, hr, hok, rfl⟩ := applyStep_success hs
  have hn : n < s.id := lt_of_le_of_lt hm.originalBound hok.1
  have hlast : target.lastId < rebaseId n d s.id := by
    rw [hm.last, rebaseId_derived hn]; exact Nat.add_lt_add_right hok.1 d
  have ht : StepOK target (rebaseStep n d s) l r :=
    ⟨hlast, rebaseId_strictMono n d hok.2.1,
      rebaseId_strictMono n d hok.2.2.1, hok.2.2.2⟩
  refine ⟨insertRow target (rebaseId n d s.id) s.clause, ?_, matches_insert hm hok.1 _⟩
  have hl' : target.rows (rebaseStep n d s).left = some l := (hm.rows s.left).trans hl
  have hr' : target.rows (rebaseStep n d s).right = some r := (hm.rows s.right).trans hr
  unfold applyStep
  rw [hl', hr']
  exact ite_eq_left ht

theorem runSteps_rebase {source next target : State v} {steps : List (Step v)}
    (hm : Matches n d source target) (hs : runSteps source steps = some next) :
    ∃ nextTarget, runSteps target (steps.map (rebaseStep n d)) = some nextTarget ∧
      Matches n d next nextTarget := by
  induction steps generalizing source target with
  | nil => cases hs; exact ⟨target, rfl, hm⟩
  | cons s ss ih =>
    simp only [runSteps] at hs
    cases he : applyStep source s with
    | none => simp [he] at hs
    | some middle =>
      simp only [he] at hs
      obtain ⟨middleTarget, hmt, hmatch⟩ := applyStep_rebase hm he
      obtain ⟨nextTarget, hnt, hn⟩ := ih hmatch hs
      exact ⟨nextTarget, by simp only [List.map_cons, runSteps, hmt]; exact hnt, hn⟩

def RowsBounded (state : State v) : Prop :=
  ∀ id, state.lastId < id → state.rows id = none

theorem initialState_bounded (f : FiniteFormula v) : RowsBounded (initialState f) := by
  intro id hid
  have hz : id ≠ 0 := by change f.clauses.size < id at hid; omega
  have hb : f.clauses.size ≤ id - 1 := by change f.clauses.size < id at hid; omega
  simp only [initialState, ite_eq_right hz]
  exact Array.getElem?_eq_none hb

theorem applyStep_bounded {source next : State v} {s : Step v}
    (hb : RowsBounded source) (hs : applyStep source s = some next) : RowsBounded next := by
  obtain ⟨l, r, hl, hr, hok, rfl⟩ := applyStep_success hs
  intro id hid
  change s.id < id at hid
  rw [insertRow_other _ _ _ _ (by omega)]
  exact hb id (lt_trans hok.1 hid)

theorem runSteps_bounded {source next : State v} {steps : List (Step v)}
    (hb : RowsBounded source) (hs : runSteps source steps = some next) : RowsBounded next := by
  induction steps generalizing source with
  | nil => cases hs; exact hb
  | cons s ss ih =>
    simp only [runSteps] at hs
    cases he : applyStep source s with
    | none => simp [he] at hs
    | some middle =>
      simp only [he] at hs
      exact ih (applyStep_bounded hb he) hs

theorem initial_matches_prefix {f : FiniteFormula v} {target : State v}
    {accepted : List (Step v)} (ha : runSteps (initialState f) accepted = some target) :
    Matches f.clauses.size (target.lastId - f.clauses.size) (initialState f) target := by
  have hl := runSteps_lastId_le ha
  change f.clauses.size ≤ target.lastId at hl
  have hb := runSteps_bounded (initialState_bounded f) ha
  refine ⟨le_rfl, by change target.lastId = f.clauses.size + (target.lastId - f.clauses.size); omega, ?_⟩
  intro id
  by_cases hi : id ≤ f.clauses.size
  · rw [rebaseId_original hi]
    exact runSteps_preserves_old_rows ha id hi
  · have hn : f.clauses.size < id := by omega
    rw [rebaseId_derived hn, hb _ (by omega), initialState_bounded f id hn]

theorem replay_initial_into_prefix {f : FiniteFormula v} {target next : State v}
    {accepted steps : List (Step v)}
    (ha : runSteps (initialState f) accepted = some target)
    (hs : runSteps (initialState f) steps = some next) :
    ∃ nextTarget,
      runSteps target (steps.map (rebaseStep f.clauses.size
        (target.lastId - f.clauses.size))) = some nextTarget ∧
      Matches f.clauses.size (target.lastId - f.clauses.size) next nextTarget :=
  runSteps_rebase (initial_matches_prefix ha) hs

theorem Matches.row_available {id : Nat} {c : Clause (Fin v)} {source target : State v} (h : Matches n d source target)
    (hr : source.rows id = some c) (hi : id ≤ source.lastId) :
    target.rows (rebaseId n d id) = some c ∧ rebaseId n d id ≤ target.lastId := by
  refine ⟨(h.rows id).trans hr, ?_⟩
  rw [h.last]
  unfold rebaseId
  split_ifs <;> omega

@[simp] theorem rebaseSteps_length (steps : List (Step v)) (n d : Nat) :
    (steps.map (rebaseStep n d)).length = steps.length := by simp

/-- One accepted trace, with every previously available row retained. -/
theorem replay_append {f : FiniteFormula v} {target next : State v}
    {accepted steps : List (Step v)}
    (ha : runSteps (initialState f) accepted = some target)
    (hs : runSteps (initialState f) steps = some next) :
    ∃ nextTarget,
      runSteps (initialState f) (accepted ++ steps.map (rebaseStep f.clauses.size
        (target.lastId - f.clauses.size))) = some nextTarget ∧
      Matches f.clauses.size (target.lastId - f.clauses.size) next nextTarget ∧
      (∀ id, id ≤ target.lastId → nextTarget.rows id = target.rows id) := by
  obtain ⟨nextTarget, hr, hm⟩ := replay_initial_into_prefix ha hs
  refine ⟨nextTarget, ?_, hm, ?_⟩
  · rw [runSteps_append, ha]
    exact hr
  · intro id hi
    exact runSteps_preserves_old_rows hr id hi

/-- Original parents keep their external ID; earlier derived parents retain
an earlier step witness in the mapped list. -/
theorem parent_supported_rebase {parent n d : Nat} {allowed : Nat → Prop}
    {earlier : List (Step v)}
    (h : (parent ≤ n ∧ allowed parent) ∨
      ∃ s ∈ earlier, s.id = parent) :
    (rebaseId n d parent ≤ n ∧ allowed (rebaseId n d parent)) ∨
      ∃ s ∈ earlier.map (rebaseStep n d), s.id = rebaseId n d parent := by
  rcases h with ho | ⟨s, hmem, hid⟩
  · left
    rw [rebaseId_original ho.1]
    exact ho
  · right
    refine ⟨rebaseStep n d s, List.mem_map.mpr ⟨s, hmem, rfl⟩, ?_⟩
    change rebaseId n d s.id = rebaseId n d parent
    rw [hid]

@[simp] theorem replay_append_length (accepted steps : List (Step v)) (n d : Nat) :
    (accepted ++ steps.map (rebaseStep n d)).length = accepted.length + steps.length := by
  simp

end Controller.Resolution.Rebase
