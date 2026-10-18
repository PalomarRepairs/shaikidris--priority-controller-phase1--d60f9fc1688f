module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.Compiler
public import Controller.Native.ObservationProjection
public import Mathlib.Tactic.FinCases

@[expose] public section

/-! Ordinary-resolution suffixes for the optional-activity grammar. Equality
rows precede discrepancy guards, and requirement nodes retain actual IDs. -/
namespace Controller.NativeProof.Wrapper
open Controller.CNF Controller.Resolution
open Controller.Native.ObservationProjection
open Controller.NativeProof.FoldProjection Controller.NativeProof.SourceStageCongruence
open Controller.NativeProof.SourceBusSchedule
variable {v : Nat}

@[irreducible] def mergeContext (state : State v) (context : Clause (Fin v)) (pivot : Literal (Fin v))
    (left right : Clause (Fin v))
    (one : AvailableSubclause state (context ++ [negate pivot] ++ left))
    (two : AvailableSubclause state (context ++ [pivot] ++ right)) :
    SubclauseProjection state (context ++ left ++ right) 1 := by
  let a : AvailableSubclause state (negate pivot :: (context ++ left)) :=
    retarget one (by intro l h; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h ⊢; aesop)
  let b : AvailableSubclause state (pivot :: (context ++ right)) :=
    retarget two (by intro l h; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h ⊢; aesop)
  let actual := longMerge state pivot (context ++ left) (context ++ right) a b
  refine ⟨actual.state, actual.steps, longMerge_run _ _ _ _ _ _,
    retarget (longMerge_result _ _ _ _ _ _) ?_, longMerge_count _ _ _ _ _ _⟩
  intro l h
  simp only [List.mem_append] at h ⊢
  aesop

structure Guards (state : State v) (activity left right : Literal (Fin v)) where
  positive : AvailableSubclause state [negate activity, left, right]
  negative : AvailableSubclause state [negate activity, negate left, negate right]

def Guards.afterTrace (rows : Guards state activity left right) (next : State v)
    (steps : List (Step v)) (checked : runSteps state steps = some next) : Guards next activity left right :=
  ⟨FoldProjection.afterTrace rows.positive next steps checked, FoldProjection.afterTrace rows.negative next steps checked⟩

def identicalActivity (state : State v) (context : Clause (Fin v)) (activity signal : Literal (Fin v))
    (rows : Guards state activity signal signal) : SubclauseProjection state (context ++ [negate activity]) 1 := by
  let negative : AvailableSubclause state (context ++ [negate signal] ++ [negate activity]) :=
    retarget rows.negative (by intro l h; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h ⊢; aesop)
  let positive : AvailableSubclause state (context ++ [signal] ++ [negate activity]) :=
    retarget rows.positive (by intro l h; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h ⊢; aesop)
  let actual := mergeContext state context signal [negate activity] [negate activity] negative positive
  exact ⟨actual.state, actual.steps, actual.checked, retarget actual.result (by
    intro l h; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h ⊢; aesop), actual.count⟩

/-- Two guard/equality resolutions and their complementary merge suffice.
Identity pairs and disappeared pivots emit fewer ordinary inferences. -/
def inactiveActivity (state : State v) (context : Clause (Fin v))
    (activity left right : Literal (Fin v)) (rows : Guards state activity left right)
    (equal : DirectionPair state context left right) :
    SubclauseProjection state (context ++ [negate activity]) 3 := by
  let positive : LocalUnitCases.Premise state context := XorUnits.contextual rows.positive
  let negative : LocalUnitCases.Premise state context := XorUnits.contextual rows.negative
  let premises := [positive, negative] ++ XorUnits.pairPremises equal
  have entails : LocalUnitCases.EntailsUnit premises (negate activity) := by
    intro values all
    have same := XorUnits.pair_value equal values (fun p h => all p (List.mem_append_right _ h))
    have pos := all positive (by simp [premises])
    have neg := all negative (by simp [premises])
    have positiveClause : ¬LiteralHolds values activity ∨ LiteralHolds values left ∨ LiteralHolds values right := by
      simpa only [positive, XorUnits.contextual, clauseHolds_cons, clauseHolds_nil, literalHolds_negate, or_false] using pos
    have negativeClause : ¬LiteralHolds values activity ∨ ¬LiteralHolds values left ∨ ¬LiteralHolds values right := by
      simpa only [negative, XorUnits.contextual, clauseHolds_cons, clauseHolds_nil, literalHolds_negate, or_false] using neg
    have agrees : LiteralHolds values left ↔ LiteralHolds values right := by
      rw [← literalValue_eq_true, ← literalValue_eq_true, same]
    rw [literalHolds_negate]
    aesop
  have covers : LocalUnitCases.Covers premises [negate activity] [left.1, right.1] := by
    intro premise member literal present
    rcases List.mem_append.mp member with guard | equality
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at guard
      rcases guard with rfl | rfl <;>
        simp only [positive, negative, XorUnits.contextual, List.mem_cons, List.not_mem_nil, or_false] at present <;>
        rcases present with rfl | rfl | rfl <;>
        simp [LocalUnitCases.labelsOf, negate, Std.Sat.Literal.negate]
    · rcases List.mem_append.mp equality with forward | backward
      · have labels := XorUnits.transfer_labels equal.forward premise forward literal present
        exact Or.inr labels
      · have labels := XorUnits.transfer_labels equal.backward premise backward literal present
        right
        simp only [List.mem_cons, List.not_mem_nil, or_false] at labels ⊢
        exact labels.symm
  exact LocalUnitCases.unitUsing state context premises (negate activity) entails [left.1, right.1] covers

def nodes : RequirementTree ρ → Nat
  | .leaf _ => 0
  | .branch left right => 1 + nodes left + nodes right

theorem nodes_leaves (tree : RequirementTree ρ) : nodes tree + 1 = tree.leaves.length := by
  induction tree with
  | leaf => rfl
  | branch left right a b => simp only [nodes, RequirementTree.leaves, List.length_append]; omega

inductive TreeRows {ρ ι : Type} (state : State v) (handle : PrivateActivity ι ρ → Literal (Fin v)) :
    RequirementTree ρ → List Bool → Type
  | leaf (output : ρ) (path : List Bool) : TreeRows state handle (.leaf output) path
  | branch (left right : RequirementTree ρ) (path : List Bool)
      (row : AvailableSubclause state [negate (handle (.tree path)),
        handle (left.root (path ++ [false])), handle (right.root (path ++ [true]))])
      (one : TreeRows state handle left (path ++ [false]))
      (two : TreeRows state handle right (path ++ [true])) : TreeRows state handle (.branch left right) path

def TreeRows.afterTrace (rows : TreeRows state handle tree path) (next : State v)
    (steps : List (Step v)) (checked : runSteps state steps = some next) : TreeRows next handle tree path :=
  match rows with
  | .leaf output path => .leaf output path
  | .branch left right path row one two => .branch left right path
      (FoldProjection.afterTrace row next steps checked) (one.afterTrace next steps checked) (two.afterTrace next steps checked)

/-- Assemble two checked child refutations and their original requirement row. -/
def treeInactiveStep {ρ ι : Type} (state : State v) (context : Clause (Fin v))
    (handle : PrivateActivity ι ρ → Literal (Fin v))
    (left right : RequirementTree ρ) (path : List Bool)
    (row : AvailableSubclause state [negate (handle (.tree path)),
      handle (left.root (path ++ [false])), handle (right.root (path ++ [true]))])
    (first : SubclauseProjection state
      (context ++ [negate (handle (left.root (path ++ [false])))]) (2 * nodes left))
    (second : SubclauseProjection first.state
      (context ++ [negate (handle (right.root (path ++ [true])))]) (2 * nodes right)) :
    SubclauseProjection state (context ++ [negate (handle (.tree path))])
      (2 * nodes (.branch left right)) := by
  let parentNow := afterTrace (afterTrace row first.state first.steps first.checked) second.state second.steps second.checked
  let negativeLeft := afterTrace first.result second.state second.steps second.checked
  let negativeRight := second.result
  let one := mergeContext second.state context (handle (left.root (path ++ [false]))) []
    [negate (handle (.tree path)), handle (right.root (path ++ [true]))]
    (retarget negativeLeft (by intro l h; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h ⊢; aesop))
    (retarget parentNow (by
      intro l h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
      aesop))
  let two := mergeContext one.state context (handle (right.root (path ++ [true]))) [] [negate (handle (.tree path))]
    (retarget (afterTrace negativeRight one.state one.steps one.checked) (by
      intro l h; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h ⊢; aesop))
    (retarget one.result (by intro l h; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h ⊢; aesop))
  refine ⟨two.state, first.steps ++ second.steps ++ one.steps ++ two.steps, ?_, ?_, ?_⟩
  · rw [runSteps_append, runSteps_append, runSteps_append, first.checked, Option.bind_some, second.checked,
      Option.bind_some, one.checked]
    exact two.checked
  · simpa only [List.append_nil, RequirementTree.root] using two.result
  · have a := first.count; have b := second.count; have c := one.count; have d := two.count
    simp only [List.length_append, nodes]; omega


/-- Each actual requirement implication consumes its two negative children. -/
def treeInactive {ρ : Type} {ι : Type} (state : State v) (context : Clause (Fin v))
    (handle : PrivateActivity ι ρ → Literal (Fin v)) (tree : RequirementTree ρ) (path : List Bool)
    (units : ∀ output ∈ tree.leaves, AvailableSubclause state (context ++ [negate (handle (.observed output))]))
    (rows : TreeRows state handle tree path) :
    SubclauseProjection state (context ++ [negate (handle (tree.root path))]) (2 * nodes tree) := by
  match rows with
  | .leaf output path => exact ⟨state, [], rfl, units output (by simp [RequirementTree.leaves]), by simp [nodes]⟩
  | .branch left right path row oneRows twoRows =>
    let first := treeInactive state context handle left (path ++ [false])
      (fun output h => units output (List.mem_append_left _ h)) oneRows
    let second := treeInactive first.state context handle right (path ++ [true])
      (fun output h => afterTrace (units output (List.mem_append_right _ h)) first.state first.steps first.checked)
      (twoRows.afterTrace first.state first.steps first.checked)
    exact treeInactiveStep state context handle left right path row first second

structure ActivityResult {ρ : Type} (state : State v) (context : Clause (Fin v))
    (activity : ρ → Literal (Fin v)) (outputs : List ρ) where
  next : State v
  steps : List (Step v)
  checked : runSteps state steps = some next
  units : ∀ output ∈ outputs, AvailableSubclause next (context ++ [negate (activity output)])
  count : steps.length ≤ 3 * outputs.length

/-- Assemble one checked activity unit outside the recursive output traversal. -/
def inactiveActivitiesStep {ρ : Type} [DecidableEq ρ] (state : State v)
    (context : Clause (Fin v)) (activity left right : ρ → Literal (Fin v))
    (output : ρ) (rest : List ρ)
    (guards : ∀ query ∈ output :: rest, Guards state (activity query) (left query) (right query))
    (equal : ∀ query ∈ output :: rest, DirectionPair state context (left query) (right query))
    (recurse : ∀ (next : State v),
      (∀ query ∈ rest, Guards next (activity query) (left query) (right query)) →
      (∀ query ∈ rest, DirectionPair next context (left query) (right query)) →
      ActivityResult next context activity rest) :
    ActivityResult state context activity (output :: rest) := by
  let first := inactiveActivity state context (activity output) (left output) (right output)
    (guards output (by simp)) (equal output (by simp))
  let tail := recurse first.state
    (fun query h => (guards query (List.mem_cons_of_mem _ h)).afterTrace first.state first.steps first.checked)
    (fun query h => (equal query (List.mem_cons_of_mem _ h)).afterTrace first.state first.steps first.checked)
  refine ⟨tail.next, first.steps ++ tail.steps, ?_, ?_, ?_⟩
  · rw [runSteps_append, first.checked]; exact tail.checked
  · intro query h
    if same : query = output then
      subst query
      exact afterTrace first.result tail.next tail.steps tail.checked
    else exact tail.units query ((List.mem_cons.mp h).resolve_left same)
  · have one := first.count; have more := tail.count
    simp only [List.length_append, List.length_cons]; omega


def inactiveActivities {ρ : Type} [DecidableEq ρ] (state : State v) (context : Clause (Fin v))
    (activity left right : ρ → Literal (Fin v)) (outputs : List ρ)
    (guards : ∀ output ∈ outputs, Guards state (activity output) (left output) (right output))
    (equal : ∀ output ∈ outputs, DirectionPair state context (left output) (right output)) :
    ActivityResult state context activity outputs := by
  match outputs with
  | [] => exact ⟨state, [], rfl, fun output impossible => False.elim (List.not_mem_nil impossible), by simp⟩
  | output :: rest =>
    exact inactiveActivitiesStep state context activity left right output rest guards equal
      (fun next nextGuards nextEqual =>
        inactiveActivities next context activity left right rest nextGuards nextEqual)

/-- The exact optional requirement tree contributes at most `5q-1` steps,
including all observed-activity units and the root contradiction. -/
def optionalSuffix {ρ ι : Type} [DecidableEq ρ] (state : State v) (context : Clause (Fin v))
    (handle : PrivateActivity ι ρ → Literal (Fin v)) (left right : ρ → Literal (Fin v))
    (tree : RequirementTree ρ)
    (guards : ∀ output ∈ tree.leaves, Guards state (handle (.observed output)) (left output) (right output))
    (equal : ∀ output ∈ tree.leaves, DirectionPair state context (left output) (right output))
    (rows : TreeRows state handle tree [])
    (root : AvailableSubclause state [handle (tree.root [])]) :
    SubclauseProjection state context (5 * tree.leaves.length - 1) := by
  let units := inactiveActivities state context (fun output => handle (.observed output)) left right tree.leaves guards equal
  let negative := treeInactive units.next context handle tree [] units.units
    (rows.afterTrace units.next units.steps units.checked)
  let rootNow := afterTrace (afterTrace root units.next units.steps units.checked) negative.state negative.steps negative.checked
  let final := mergeContext negative.state context (handle (tree.root [])) [] []
    (by simpa only [List.append_nil] using negative.result)
    (retarget rootNow (fun _ h => List.mem_append_left _ (List.mem_append_right _ h)))
  refine ⟨final.state, units.steps ++ negative.steps ++ final.steps, ?_, ?_, ?_⟩
  · rw [runSteps_append, runSteps_append, units.checked, Option.bind_some, negative.checked]
    exact final.checked
  · simpa only [List.append_nil] using final.result
  · have a := units.count; have b := negative.count; have c := final.count
    have size := nodes_leaves tree
    simp only [List.length_append]; omega

/-- Only selected guards and equality pairs are consumed. The optional tree
and every unselected guard remain in the input without being proof parents. -/
def selectedSuffix {ρ : Type} [DecidableEq ρ] (state : State v) (context : Clause (Fin v))
    (activity left right : ρ → Literal (Fin v)) (selected : List ρ) (nonempty : selected ≠ [])
    (guards : ∀ output ∈ selected, Guards state (activity output) (left output) (right output))
    (equal : ∀ output ∈ selected, DirectionPair state context (left output) (right output))
    (requirement : AvailableSubclause state (selected.map activity)) :
    SubclauseProjection state context (5 * selected.length - 1) := by
  let units := inactiveActivities state context activity left right selected guards equal
  let remaining := selected.map (fun output => negate (activity output))
  let parent : AvailableSubclause units.next (remaining.map negate ++ context) := by
    have dual : remaining.map negate = selected.map activity := by
      simp only [remaining, List.map_map, Function.comp_def, negate_negate]
    rw [dual]
    exact retarget (afterTrace requirement units.next units.steps units.checked)
      (fun _ h => List.mem_append_left _ h)
  let propagation : ∀ input ∈ remaining, AvailableSubclause units.next (context ++ [input]) :=
    TreeUnits.mappedUnit selected (fun output => negate (activity output)) context units.units
  let final := dischargeInputs units.next remaining context parent propagation
  refine ⟨final.state, units.steps ++ final.steps, ?_, final.result, ?_⟩
  · rw [runSteps_append, units.checked]; exact final.checked
  · have a := units.count; have b := final.count
    have positive : 0 < selected.length := List.length_pos_iff.mpr nonempty
    simp only [remaining, List.length_map] at b
    simp only [List.length_append]; omega

/-- The replaced observation assertion is deliberately absent from the row
correspondence. All retained originals and derived IDs are translated. -/
structure MatchesExcept (originalCount offset missing : Nat) (source target : State v) : Prop where
  originalBound : originalCount ≤ source.lastId
  missingBound : missing ≤ originalCount
  last : target.lastId = source.lastId + offset
  rows : ∀ id, id ≠ missing →
    target.rows (Rebase.rebaseId originalCount offset id) = source.rows id

theorem matchesExcept_insert {source target : State v} {freshId : Nat}
    (matched : MatchesExcept originalCount offset missing source target)
    (fresh : source.lastId < freshId) (clause : Clause (Fin v)) :
    MatchesExcept originalCount offset missing (insertRow source freshId clause)
      (insertRow target (Rebase.rebaseId originalCount offset freshId) clause) := by
  have derived : originalCount < freshId := lt_of_le_of_lt matched.originalBound fresh
  refine ⟨by simp only [insertRow]; omega, matched.missingBound, ?_, ?_⟩
  · simp only [insertRow, Rebase.rebaseId_derived derived]
  · intro query notMissing
    if same : query = freshId then subst query; simp
    else
      have different : Rebase.rebaseId originalCount offset query ≠ Rebase.rebaseId originalCount offset freshId :=
        fun equal => same (Rebase.rebaseId_injective originalCount offset equal)
      simp only [insertRow, ite_eq_right same, ite_eq_right different]
      exact matched.rows query notMissing

theorem applyStep_except {source next target : State v} {step : Step v}
    (matched : MatchesExcept originalCount offset missing source target)
    (checked : applyStep source step = some next)
    (left : step.left ≠ missing) (right : step.right ≠ missing) :
    ∃ nextTarget, applyStep target (Rebase.rebaseStep originalCount offset step) = some nextTarget ∧
      MatchesExcept originalCount offset missing next nextTarget := by
  obtain ⟨one, two, first, second, valid, rfl⟩ := applyStep_success checked
  have derived : originalCount < step.id := lt_of_le_of_lt matched.originalBound valid.1
  have fresh : target.lastId < Rebase.rebaseId originalCount offset step.id := by
    rw [matched.last, Rebase.rebaseId_derived derived]
    exact Nat.add_lt_add_right valid.1 offset
  have ok : StepOK target (Rebase.rebaseStep originalCount offset step) one two :=
    ⟨fresh, Rebase.rebaseId_strictMono originalCount offset valid.2.1,
      Rebase.rebaseId_strictMono originalCount offset valid.2.2.1, valid.2.2.2⟩
  refine ⟨insertRow target (Rebase.rebaseId originalCount offset step.id) step.clause, ?_,
    matchesExcept_insert matched valid.1 _⟩
  have firstTarget : target.rows (Rebase.rebaseStep originalCount offset step).left = some one :=
    (matched.rows step.left left).trans first
  have secondTarget : target.rows (Rebase.rebaseStep originalCount offset step).right = some two :=
    (matched.rows step.right right).trans second
  unfold applyStep
  rw [firstTarget, secondTarget]
  exact ite_eq_left ok

def Avoids (missing : Nat) (steps : List (Step v)) : Prop :=
  ∀ step ∈ steps, step.left ≠ missing ∧ step.right ≠ missing

theorem runSteps_except {source next target : State v} {steps : List (Step v)}
    (matched : MatchesExcept originalCount offset missing source target)
    (checked : runSteps source steps = some next) (avoids : Avoids missing steps) :
    ∃ nextTarget, runSteps target (steps.map (Rebase.rebaseStep originalCount offset)) = some nextTarget ∧
      MatchesExcept originalCount offset missing next nextTarget := by
  induction steps generalizing source target with
  | nil => cases checked; exact ⟨target, rfl, matched⟩
  | cons step rest ih =>
    simp only [runSteps] at checked
    cases first : applyStep source step with
    | none => simp [first] at checked
    | some middle =>
      simp only [first] at checked
      have noMissing := avoids step (by simp)
      obtain ⟨middleTarget, firstTarget, matchMiddle⟩ := applyStep_except matched first noMissing.1 noMissing.2
      obtain ⟨final, restTarget, finalMatch⟩ := ih matchMiddle checked
        (fun query h => avoids query (List.mem_cons_of_mem _ h))
      exact ⟨final, by simp only [List.map_cons, runSteps, firstTarget]; exact restTarget, finalMatch⟩

def MatchesExcept.available {source target : State v}
    (matched : MatchesExcept originalCount offset missing source target)
    (row : Rows.Available source clause) (notMissing : row.id ≠ missing) :
    Rows.Available target clause := by
  refine ⟨Rebase.rebaseId originalCount offset row.id, (matched.rows row.id notMissing).trans row.present, ?_⟩
  unfold Rebase.rebaseId
  split
  · have bound := row.bound
    rw [matched.last]
    omega
  · rw [matched.last]
    exact Nat.add_le_add_right row.bound offset

theorem retained_initial_match (retained extra : List (Clause (Fin v))) (positive : 0 < extra.length)
    (nativeAssertion : Clause (Fin v)) :
    MatchesExcept (retained.length + 1) (extra.length - 1) (retained.length + 1)
      (initialState (ofClauses (retained ++ [nativeAssertion])))
      (initialState (ofClauses (retained ++ extra))) := by
  refine ⟨by simp [initialState, ofClauses], le_rfl, by simp [initialState, ofClauses]; omega, ?_⟩
  intro id notMissing
  if zero : id = 0 then subst id; simp [Rebase.rebaseId, initialState]
  else
    if old : id ≤ retained.length + 1 then
      have before : id - 1 < retained.length := by omega
      rw [Rebase.rebaseId_original old]
      simp only [initialState, ite_eq_right zero, ofClauses, List.getElem?_toArray]
      rw [List.getElem?_append_left before, List.getElem?_append_left before]
    else
      have derived : retained.length + 1 < id := by omega
      rw [Rebase.rebaseId_derived derived]
      have beyondSource : (retained ++ [nativeAssertion]).length ≤ id - 1 := by simp; omega
      have beyondTarget : (retained ++ extra).length ≤ id + (extra.length - 1) - 1 := by simp; omega
      have translatedNonzero : id + (extra.length - 1) ≠ 0 := by omega
      simp only [initialState, ite_eq_right zero, ite_eq_right translatedNonzero, ofClauses]
      rw [Array.getElem?_eq_none (by simpa only [List.size_toArray] using beyondTarget),
        Array.getElem?_eq_none (by simpa only [List.size_toArray] using beyondSource)]

theorem step_avoids_of_pivot {state next : State v} {step : Step v}
    (checked : applyStep state step = some next) (unit : state.rows missing = some [forbidden])
    (different : step.pivot.1 ≠ forbidden.1) : step.left ≠ missing ∧ step.right ≠ missing := by
  obtain ⟨left, right, first, second, valid, _⟩ := applyStep_success checked
  constructor
  · intro same
    rw [same, unit] at first
    have clause : left = [forbidden] := (Option.some.inj first).symm
    have pivot : negate step.pivot = forbidden := by simpa only [clause, List.mem_singleton] using valid.2.2.2.1
    have labels := congrArg Prod.fst pivot
    exact different labels
  · intro same
    rw [same, unit] at second
    have clause : right = [forbidden] := (Option.some.inj second).symm
    have pivot : step.pivot = forbidden := by simpa only [clause, List.mem_singleton] using valid.2.2.2.2.1
    exact different (congrArg Prod.fst pivot)

theorem run_avoids_of_pivots {state next : State v} {steps : List (Step v)}
    (checked : runSteps state steps = some next) (unit : state.rows missing = some [forbidden])
    (old : missing ≤ state.lastId)
    (different : ∀ step ∈ steps, step.pivot.1 ≠ forbidden.1) : Avoids missing steps := by
  induction steps generalizing state with
  | nil => intro step impossible; exact False.elim (List.not_mem_nil impossible)
  | cons step rest ih =>
    simp only [runSteps] at checked
    cases first : applyStep state step with
    | none => simp [first] at checked
    | some middle =>
      simp only [first] at checked
      have head := step_avoids_of_pivot first unit (different step (by simp))
      obtain ⟨left, right, hl, hr, valid, shape⟩ := applyStep_success first
      have retained : middle.rows missing = some [forbidden] := by
        rw [shape, insertRow_other _ _ _ _ (by have := valid.1; omega)]
        exact unit
      have below : missing ≤ middle.lastId := by rw [shape]; change missing ≤ step.id; have := valid.1; omega
      have tail := ih checked retained below (fun query h => different query (List.mem_cons_of_mem _ h))
      intro query member
      rcases List.mem_cons.mp member with same | later
      · exact same ▸ head
      · exact tail query later

theorem merge_pivots (state : State v) (one two : Nat) (pivot : Literal (Fin v))
    (left right : Clause (Fin v)) :
    ∀ step ∈ (Cases.merge state one two pivot left right).steps, step.pivot = pivot := by
  unfold Cases.merge
  split
  · simp
  · split
    · simp
    · simp only [List.mem_singleton]
      intro step same
      subst step
      rfl

def TreePivots (allowed : Fin v → Prop) : Cases.CaseTree v → Prop
  | .leaf certificate => ∀ reason ∈ certificate.reasons, allowed reason.entry.pivot.1
  | .fork pivot left right => allowed pivot.1 ∧ TreePivots allowed left ∧ TreePivots allowed right

def TracePivots (allowed : Fin v → Prop) (steps : List (Step v)) : Prop :=
  ∀ step ∈ steps, allowed step.pivot.1

theorem reason_pivots (allowed : Fin v → Prop) (state : State v) (rowId : Nat) (current : Clause (Fin v))
    (reasons : List (RUP.RowReason v)) (permitted : ∀ reason ∈ reasons, allowed reason.entry.pivot.1) :
    TracePivots allowed (RUP.compileReasons state rowId current reasons).steps := by
  induction reasons generalizing state rowId current with
  | nil => intro step impossible; exact False.elim (List.not_mem_nil impossible)
  | cons reason rest ih =>
    have tail := fun state rowId current => ih state rowId current
      (fun query h => permitted query (List.mem_cons_of_mem _ h))
    unfold RUP.compileReasons
    split
    · intro step member
      rcases List.mem_cons.mp member with same | later
      · subst step; exact permitted reason (by simp)
      · exact tail _ _ _ step later
    · exact tail _ _ _

theorem tree_pivots (allowed : Fin v → Prop) (tree : Cases.CaseTree v) (state : State v)
    (permitted : TreePivots allowed tree) : TracePivots allowed (Cases.compileTree state tree).steps := by
  induction tree generalizing state with
  | leaf certificate => exact reason_pivots allowed state _ _ _ permitted
  | fork pivot left right one two =>
    have first := one state permitted.2.1
    have second := two (Cases.compileTree state left).state permitted.2.2
    intro step member
    change step ∈ (Cases.compileTree state left).steps ++
      (Cases.compileTree (Cases.compileTree state left).state right).steps ++
      (Cases.merge (Cases.compileTree (Cases.compileTree state left).state right).state
        (Cases.compileTree state left).rowId (Cases.compileTree (Cases.compileTree state left).state right).rowId
        pivot (Cases.compileTree state left).clause (Cases.compileTree (Cases.compileTree state left).state right).clause).steps at member
    rcases List.mem_append.mp member with earlier | joined
    · rcases List.mem_append.mp earlier with before | after
      · exact first step before
      · exact second step after
    · have same := merge_pivots _ _ _ _ _ _ step joined
      exact same.symm ▸ permitted.1

/-- Local truth cases split only the explicitly supplied pending labels. -/
theorem local_build_pivots (allowed : Fin v → Prop) (state : State v)
    (context : Clause (Fin v)) (rows : List (LocalUnitCases.Premise state context))
    (goal : Literal (Fin v)) (entails : LocalUnitCases.EntailsUnit rows goal)
    (guards : Clause (Fin v)) (goalPresent : goal ∈ guards) (values : Fin v → Bool)
    (falseGuards : LocalUnitCases.Falsifies values guards) (pending : List (Fin v))
    (covers : LocalUnitCases.Covers rows guards pending)
    (permitted : ∀ label ∈ pending, allowed label) :
    TreePivots allowed (LocalUnitCases.build state context rows goal entails guards
      goalPresent values falseGuards pending covers).tree := by
  induction pending generalizing guards values with
  | nil =>
    let built := LocalUnitCases.build state context rows goal entails guards
      goalPresent values falseGuards [] covers
    have bound : Cases.inferenceBudget built.tree ≤ 0 := by simpa using built.bound
    cases shape : built.tree with
    | leaf certificate =>
      have empty : certificate.reasons = [] := by
        have length : certificate.reasons.length = 0 := by
          simpa [shape, Cases.inferenceBudget] using bound
        exact List.eq_nil_of_length_eq_zero length
      simp [TreePivots, empty]
    | fork pivot left right =>
      simp [shape, Cases.inferenceBudget] at bound
  | cons label rest ih =>
    have tail : ∀ query ∈ rest, allowed query := fun query member =>
      permitted query (List.mem_cons_of_mem _ member)
    unfold LocalUnitCases.build
    split
    · exact ih _ _ _ _ _ tail
    · exact ⟨permitted label (by simp), ih _ _ _ _ _ tail, ih _ _ _ _ _ tail⟩

/-- Ordinary resolution compiled from local truth cases retains their pivot support. -/
theorem local_unit_pivots (allowed : Fin v → Prop) (state : State v)
    (context : Clause (Fin v)) (rows : List (LocalUnitCases.Premise state context))
    (goal : Literal (Fin v)) (entails : LocalUnitCases.EntailsUnit rows goal)
    (pending : List (Fin v)) (covers : LocalUnitCases.Covers rows [goal] pending)
    (permitted : ∀ label ∈ pending, allowed label) :
    TracePivots allowed (LocalUnitCases.unitUsing state context rows goal entails pending covers).steps := by
  unfold LocalUnitCases.unitUsing
  apply tree_pivots
  exact local_build_pivots allowed state context rows goal entails _ _ _ _ pending covers permitted

/-- A computable enumeration fixes the original occurrence order of the exact
optional grammar. Internal indices are emitted in increasing order. -/
def optionalRows (wrapper : OptionalWrapper σ (Fin internalCount) ρ) :
    List (Clause (Sum σ (PrivateActivity (Fin internalCount) ρ))) :=
  ((List.finRange internalCount).flatMap fun i => guardRows (.internal i) (wrapper.internalPairs i)) ++
    (wrapper.tree.leaves.flatMap fun i => guardRows (.observed i) (wrapper.observedPairs i)) ++
    wrapper.clauses.map OptionalClause.clause ++ wrapper.tree.rows [] ++
    [[(Sum.inr (wrapper.tree.root []), true)]]

def optionalFormula (wrapper : OptionalWrapper σ (Fin internalCount) ρ) :
    Formula (Sum σ (PrivateActivity (Fin internalCount) ρ)) := ofClauses (optionalRows wrapper)

/-- Emission implements A.2 with existential optional activities. -/
theorem optionalFormula_iff (wrapper : OptionalWrapper σ (Fin internalCount) ρ)
    (signals : σ → Bool) (values : PrivateActivity (Fin internalCount) ρ → Bool) :
    Satisfies (joint signals values) (optionalFormula wrapper) ↔ wrapper.Holds signals values := by
  simp only [optionalFormula, optionalRows, satisfies_ofClauses, List.forall_mem_append,
    List.forall_mem_flatMap, List.forall_mem_map]
  have guards : ∀ activity pair,
      (∀ row ∈ guardRows activity pair, ClauseHolds (joint signals values) row) ↔
      (values activity = true → Discrepant signals pair) := by
    intro activity pair
    simpa only [satisfies_ofClauses] using guardRows_iff activity pair signals values
  have treeRows : (∀ row ∈ wrapper.tree.rows [], ClauseHolds (joint signals values) row) ↔
      wrapper.tree.Holds [] values := by
    simpa only [satisfies_ofClauses] using requirementTree_rows_iff wrapper.tree [] signals values
  simp only [guards, optionalClause_clause_iff, treeRows, OptionalWrapper.Holds,
    List.mem_finRange, forall_true_left, List.forall_mem_cons,
    clauseHolds_cons, clauseHolds_nil, or_false, and_assoc]
  simp [LiteralHolds, joint]

theorem optionalFormula_projection (wrapper : OptionalWrapper σ (Fin internalCount) ρ)
    (signals : σ → Bool) :
    (∃ values, Satisfies (joint signals values) (optionalFormula wrapper)) ↔
      ∃ output ∈ wrapper.tree.leaves, Discrepant signals (wrapper.observedPairs output) := by
  simp only [optionalFormula_iff]
  exact optional_activity_projection wrapper signals

/-- A.3 retains the whole optional wrapper and appends exactly the selected
positive activity disjunction. -/
def selectedOptionalFormula (wrapper : OptionalWrapper σ (Fin internalCount) ρ)
    (selected : List ρ) : Formula (Sum σ (PrivateActivity (Fin internalCount) ρ)) :=
  optionalFormula wrapper ++ ofClauses [selected.map (fun output => (Sum.inr (.observed output), true))]

theorem selectedOptionalFormula_equiv (wrapper : OptionalWrapper σ (Fin internalCount) ρ)
    (selected : List ρ) (signals : σ → Bool) (values : PrivateActivity (Fin internalCount) ρ → Bool) :
    Satisfies (joint signals values) (selectedOptionalFormula wrapper selected) ↔
      Satisfies (joint signals values) (selectedFormula wrapper selected) := by
  rw [selectedOptionalFormula, selectedFormula, satisfies_append, satisfies_append,
    optionalFormula_iff, optionalWrapper_formula_iff]

theorem selectedOptionalFormula_projection (wrapper : OptionalWrapper σ (Fin internalCount) ρ)
    (selected : List ρ) (allLeaves : ∀ output ∈ selected, output ∈ wrapper.tree.leaves)
    (signals : σ → Bool) :
    (∃ values, Satisfies (joint signals values) (selectedOptionalFormula wrapper selected)) ↔
      ∃ output ∈ selected, Discrepant signals (wrapper.observedPairs output) := by
  simp only [selectedOptionalFormula_equiv]
  exact selected_activity_cnf_projection wrapper selected allLeaves signals

/-- Unsatisfiability of the emitted wrapper over every model of a retained core
forces absence of the selected discrepancies in each such model. -/
theorem selected_absence_of_unsatisfiable (core : Formula σ)
    (wrapper : OptionalWrapper σ (Fin internalCount) ρ) (selected : List ρ)
    (allLeaves : ∀ output ∈ selected, output ∈ wrapper.tree.leaves)
    (unsatisfiable : ¬∃ signals values, Satisfies signals core ∧
      Satisfies (joint signals values) (selectedOptionalFormula wrapper selected))
    (signals : σ → Bool) (model : Satisfies signals core) :
    ∀ output ∈ selected, ¬Discrepant signals (wrapper.observedPairs output) := by
  intro output member difference
  obtain ⟨values, extension⟩ := (selectedOptionalFormula_projection wrapper selected allLeaves signals).mpr
    ⟨output, member, difference⟩
  exact unsatisfiable ⟨signals, values, model, extension⟩

/-- A concrete clause lookup selects a real original occurrence, including
when several original rows have equal contents. -/
def memberRow [DecidableEq α] (rename : α → Fin v) (clauses : List (Clause α))
    (clause : Clause α) (member : clause ∈ clauses) :
    Rows.Available (initialState (relabel rename (ofClauses clauses))) (Rows.mapClause rename clause) := by
  let position : Fin (ofClauses clauses).clauses.size :=
    ⟨clauses.idxOf clause, by simpa [ofClauses] using List.idxOf_lt_length_of_mem member⟩
  have content : (ofClauses clauses).clauses[position.val] = clause := by
    change clauses[clauses.idxOf clause]'(List.idxOf_lt_length_of_mem member) = clause
    exact List.getElem_idxOf _
  rw [← content]
  exact Rows.originalRow rename (ofClauses clauses) position

/-- The emitter always contains the requirement-root unit. -/
theorem optionalRows_root (wrapper : OptionalWrapper σ (Fin internalCount) ρ) :
    [(Sum.inr (wrapper.tree.root []), true)] ∈ optionalRows wrapper := by
  simp [optionalRows]

/-- Each observed guard is an actual clause of the emitted grammar. -/
theorem optionalRows_guard (wrapper : OptionalWrapper σ (Fin internalCount) ρ)
    (output : ρ) (leaf : output ∈ wrapper.tree.leaves)
    (clause : Clause (Sum σ (PrivateActivity (Fin internalCount) ρ)))
    (guard : clause ∈ guardRows (.observed output) (wrapper.observedPairs output)) :
    clause ∈ optionalRows wrapper := by
  unfold optionalRows
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _ (List.mem_flatMap.mpr ⟨output, leaf, guard⟩))))

/-- Every tree implication keeps its emitted original occurrence. -/
theorem optionalRows_tree (wrapper : OptionalWrapper σ (Fin internalCount) ρ)
    (clause : Clause (Sum σ (PrivateActivity (Fin internalCount) ρ)))
    (row : clause ∈ wrapper.tree.rows []) : clause ∈ optionalRows wrapper := by
  unfold optionalRows
  exact List.mem_append_left _ (List.mem_append_right _ row)

deriving instance DecidableEq for PrivateActivity

/-- Actual original guard IDs are obtained from the emitted clauses after the
retained core; no asserted availability map is supplied by the caller. -/
def emittedGuards [DecidableEq σ] [DecidableEq ρ]
    (rename : Sum σ (PrivateActivity (Fin internalCount) ρ) → Fin v)
    (core : List (Clause (Sum σ (PrivateActivity (Fin internalCount) ρ))))
    (wrapper : OptionalWrapper σ (Fin internalCount) ρ) (output : ρ)
    (leaf : output ∈ wrapper.tree.leaves) :
    Guards (initialState (relabel rename (ofClauses (core ++ optionalRows wrapper))))
      (rename (.inr (.observed output)), true)
      (rename (.inl (wrapper.observedPairs output).1.1), (wrapper.observedPairs output).1.2)
      (rename (.inl (wrapper.observedPairs output).2.1), (wrapper.observedPairs output).2.2) := by
  let first : Clause (Sum σ (PrivateActivity (Fin internalCount) ρ)) := (guardRows (.observed output) (wrapper.observedPairs output))[0]'(by simp [guardRows])
  let second : Clause (Sum σ (PrivateActivity (Fin internalCount) ρ)) := (guardRows (.observed output) (wrapper.observedPairs output))[1]'(by simp [guardRows])
  have firstMember : first ∈ core ++ optionalRows wrapper :=
    List.mem_append_right _ (optionalRows_guard wrapper output leaf first (by simp [first, guardRows]))
  have secondMember : second ∈ core ++ optionalRows wrapper :=
    List.mem_append_right _ (optionalRows_guard wrapper output leaf second (by simp [second, guardRows]))
  constructor
  · simpa [first, guardRows, Rows.mapClause, negate, Std.Sat.Literal.negate] using
      ofRow (memberRow rename (core ++ optionalRows wrapper) first firstMember)
  · simpa [second, guardRows, Rows.mapClause, negate, Std.Sat.Literal.negate] using
      ofRow (memberRow rename (core ++ optionalRows wrapper) second secondMember)

/-- Requirement implications are read from the concrete original row list. -/
def emittedTree [DecidableEq σ] [DecidableEq ι] [DecidableEq ρ]
    (rename : Sum σ (PrivateActivity ι ρ) → Fin v)
    (clauses : List (Clause (Sum σ (PrivateActivity ι ρ))))
    (tree : RequirementTree ρ) (path : List Bool)
    (contained : ∀ clause ∈ tree.rows path, clause ∈ clauses) :
    TreeRows (initialState (relabel rename (ofClauses clauses)))
      (fun activity => (rename (.inr activity), true)) tree path := by
  match tree with
  | .leaf output => exact .leaf output path
  | .branch left right =>
    let parent : Clause (Sum σ (PrivateActivity ι ρ)) :=
      requirementRow (.tree path) (left.root (path ++ [false])) (right.root (path ++ [true]))
    have parentMember : parent ∈ clauses := contained parent (by simp [parent, RequirementTree.rows])
    have leftContained : ∀ clause ∈ left.rows (path ++ [false]), clause ∈ clauses := by
      intro clause member
      apply contained clause
      simp only [RequirementTree.rows, List.mem_cons, List.mem_append]
      exact Or.inl (Or.inr member)
    have rightContained : ∀ clause ∈ right.rows (path ++ [true]), clause ∈ clauses := by
      intro clause member
      apply contained clause
      simp only [RequirementTree.rows, List.mem_cons, List.mem_append]
      exact Or.inr member
    refine .branch left right path ?_
      (emittedTree rename clauses left (path ++ [false]) leftContained)
      (emittedTree rename clauses right (path ++ [true]) rightContained)
    simpa [parent, requirementRow, Rows.mapClause, negate, Std.Sat.Literal.negate] using
      ofRow (memberRow rename clauses parent parentMember)

def emittedOptionalTree [DecidableEq σ] [DecidableEq ρ]
    (rename : Sum σ (PrivateActivity (Fin internalCount) ρ) → Fin v)
    (core : List (Clause (Sum σ (PrivateActivity (Fin internalCount) ρ))))
    (wrapper : OptionalWrapper σ (Fin internalCount) ρ) :
    TreeRows (initialState (relabel rename (ofClauses (core ++ optionalRows wrapper))))
      (fun activity => (rename (.inr activity), true)) wrapper.tree [] :=
  emittedTree rename (core ++ optionalRows wrapper) wrapper.tree [] (fun clause member =>
    List.mem_append_right _ (optionalRows_tree wrapper clause member))

def emittedRoot [DecidableEq σ] [DecidableEq ρ]
    (rename : Sum σ (PrivateActivity (Fin internalCount) ρ) → Fin v)
    (core : List (Clause (Sum σ (PrivateActivity (Fin internalCount) ρ))))
    (wrapper : OptionalWrapper σ (Fin internalCount) ρ) :
    AvailableSubclause (initialState (relabel rename (ofClauses (core ++ optionalRows wrapper))))
      [(rename (.inr (wrapper.tree.root [])), true)] := by
  simpa [Rows.mapClause] using ofRow (memberRow rename (core ++ optionalRows wrapper)
    [(Sum.inr (wrapper.tree.root []), true)] (List.mem_append_right _ (optionalRows_root wrapper)))

/-- The optional suffix obtains all guard/tree/root parents from its emitted
formula and retains them through an actual checked equality prefix. -/
def optionalAfterPrefix [DecidableEq σ] [DecidableEq ρ]
    (rename : Sum σ (PrivateActivity (Fin internalCount) ρ) → Fin v)
    (core : List (Clause (Sum σ (PrivateActivity (Fin internalCount) ρ))))
    (wrapper : OptionalWrapper σ (Fin internalCount) ρ)
    (state : State v) (steps : List (Step v))
    (checked : runSteps (initialState (relabel rename (ofClauses (core ++ optionalRows wrapper)))) steps = some state)
    (context : Clause (Fin v))
    (equal : ∀ output ∈ wrapper.tree.leaves, DirectionPair state context
      (rename (.inl (wrapper.observedPairs output).1.1), (wrapper.observedPairs output).1.2)
      (rename (.inl (wrapper.observedPairs output).2.1), (wrapper.observedPairs output).2.2)) :
    SubclauseProjection state context (5 * wrapper.tree.leaves.length - 1) :=
  optionalSuffix state context (fun activity => (rename (.inr activity), true))
    (fun output => (rename (.inl (wrapper.observedPairs output).1.1), (wrapper.observedPairs output).1.2))
    (fun output => (rename (.inl (wrapper.observedPairs output).2.1), (wrapper.observedPairs output).2.2))
    wrapper.tree (fun output member => (emittedGuards rename core wrapper output member).afterTrace state steps checked)
    equal ((emittedOptionalTree rename core wrapper).afterTrace state steps checked)
    (FoldProjection.afterTrace (emittedRoot rename core wrapper) state steps checked)

open Controller.NativeProof.SourceMismatchHandles
open Controller.NativeProof.SourceFoldAggregateProvenance
open Controller.NativeProof.SourceFoldProvenance

/-- Local case leaves reuse real rows and contain no reason trail. -/
def CaseOrigins (originalCount : Nat) (allowed : Nat → Prop) (prior : List (Step v)) :
    Cases.CaseTree v → Prop
  | .leaf certificate => certificate.reasons = [] ∧
      ResultOrigin originalCount allowed prior certificate.rowId
  | .fork _ left right => CaseOrigins originalCount allowed prior left ∧
      CaseOrigins originalCount allowed prior right

theorem caseOrigins_extend (extra : List (Step v))
    (origin : CaseOrigins originalCount allowed prior tree) :
    CaseOrigins originalCount allowed (prior ++ extra) tree := by
  induction tree with
  | leaf certificate => exact ⟨origin.1,
      resultOrigin_append_right originalCount allowed prior extra certificate.rowId origin.2⟩
  | fork pivot left right one two => exact ⟨one origin.1, two origin.2⟩

theorem validTree_after {state next : State v} {steps : List (Step v)}
    (checked : runSteps state steps = some next) (tree : Cases.CaseTree v)
    (target : Clause (Fin v)) (valid : Cases.ValidTree state target tree) :
    Cases.ValidTree next target tree := by
  induction tree generalizing target with
  | leaf certificate =>
    refine ⟨(runSteps_preserves_old_rows checked _ valid.2.1).trans valid.1,
      valid.2.1.trans (runSteps_lastId_le checked), ?_, valid.2.2.2⟩
    intro reason member
    have known := valid.2.2.1 reason member
    exact ⟨(runSteps_preserves_old_rows checked _ known.2.1).trans known.1,
      known.2.1.trans (runSteps_lastId_le checked), known.2.2⟩
  | fork pivot left right one two => exact ⟨one _ valid.1, two _ valid.2⟩

/-- Original-row support composes through the actual case-tree compiler. -/
theorem case_compile_supported (state : State v) (tree : Cases.CaseTree v)
    (target : Clause (Fin v)) (valid : Cases.ValidTree state target tree)
    (originalCount : Nat) (allowed : Nat → Prop) (prior : List (Step v))
    (supported : TraceOriginalSupport originalCount allowed prior)
    (originalBound : ∀ rowId, allowed rowId → rowId ≤ originalCount)
    (bound : originalCount ≤ state.lastId)
    (origin : CaseOrigins originalCount allowed prior tree) :
    TraceOriginalSupport originalCount allowed (prior ++ (Cases.compileTree state tree).steps) ∧
      ResultOrigin originalCount allowed (prior ++ (Cases.compileTree state tree).steps)
        (Cases.compileTree state tree).rowId := by
  induction tree generalizing state target prior with
  | leaf certificate =>
    simp only [Cases.compileTree, origin.1, RUP.compileReasons, List.append_nil]
    exact ⟨supported, origin.2⟩
  | fork pivot left right one two =>
    let first := Cases.compileTree state left
    let second := Cases.compileTree first.state right
    have firstRun := Cases.compileTree_run left state state le_rfl (fun _ _ => rfl)
      (target ++ [negate pivot]) valid.1
    have firstSupport := one state _ valid.1 prior supported bound origin.1
    have rightValid := validTree_after firstRun.1 right _ valid.2
    have secondRun := Cases.compileTree_run right first.state first.state le_rfl (fun _ _ => rfl)
      (target ++ [pivot]) rightValid
    have secondSupport := two first.state _ rightValid (prior ++ first.steps)
      firstSupport.1 (bound.trans (runSteps_lastId_le firstRun.1))
      (caseOrigins_extend first.steps origin.2)
    have firstOrigin := resultOrigin_append_right originalCount allowed
      (prior ++ first.steps) second.steps first.rowId firstSupport.2
    have firstBound : first.rowId ≤ second.state.lastId :=
      firstRun.2.2.1.trans (runSteps_lastId_le secondRun.1)
    have finalSupport := appendMerge_origins_supported originalCount allowed
      ((prior ++ first.steps) ++ second.steps) second.state first.rowId second.rowId
      pivot first.clause second.clause secondSupport.1 originalBound firstOrigin secondSupport.2
      firstBound secondRun.2.2.1
    have finalOrigin := merge_origins originalCount allowed
      ((prior ++ first.steps) ++ second.steps) second.state first.rowId second.rowId
      pivot first.clause second.clause firstOrigin secondSupport.2
      ((bound.trans (runSteps_lastId_le firstRun.1)).trans (runSteps_lastId_le secondRun.1))
    exact ⟨by simpa only [Cases.compileTree, first, second, List.append_assoc] using finalSupport,
      by simpa only [Cases.compileTree, first, second, List.append_assoc] using finalOrigin⟩

theorem local_build_origins (state : State v) (context : Clause (Fin v))
    (rows : List (LocalUnitCases.Premise state context)) (goal : Literal (Fin v))
    (entails : LocalUnitCases.EntailsUnit rows goal) (guards : Clause (Fin v))
    (goalPresent : goal ∈ guards) (values : Fin v → Bool)
    (falseGuards : LocalUnitCases.Falsifies values guards) (pending : List (Fin v))
    (covers : LocalUnitCases.Covers rows guards pending)
    (originalCount : Nat) (allowed : Nat → Prop) (prior : List (Step v))
    (origins : ∀ row ∈ rows, ResultOrigin originalCount allowed prior row.row.row.id) :
    CaseOrigins originalCount allowed prior (LocalUnitCases.build state context rows goal entails
      guards goalPresent values falseGuards pending covers).tree := by
  induction pending generalizing guards values with
  | nil =>
    unfold LocalUnitCases.build
    dsimp only
    split
    · rename_i found
      have allTrue : ∀ premise ∈ rows, ClauseHolds values premise.clause := by
        intro premise member
        have yes := List.find?_eq_none.mp found ⟨premise, member⟩ (List.mem_attach _ _)
        apply (clauseHolds_iff_eval _ _).mpr
        simpa using yes
      exact False.elim (falseGuards goal goalPresent (entails values allTrue))
    · rename_i premise found
      exact ⟨rfl, origins premise.val premise.property⟩
  | cons label rest ih =>
    unfold LocalUnitCases.build
    split
    · exact ih _ _ _ _ _
    · exact ⟨ih _ _ _ _ _, ih _ _ _ _ _⟩

theorem local_unit_supported (state : State v) (context : Clause (Fin v))
    (rows : List (LocalUnitCases.Premise state context)) (goal : Literal (Fin v))
    (entails : LocalUnitCases.EntailsUnit rows goal) (pending : List (Fin v))
    (covers : LocalUnitCases.Covers rows [goal] pending)
    (originalCount : Nat) (allowed : Nat → Prop) (prior : List (Step v))
    (supported : TraceOriginalSupport originalCount allowed prior)
    (originalBound : ∀ rowId, allowed rowId → rowId ≤ originalCount)
    (bound : originalCount ≤ state.lastId)
    (origins : ∀ row ∈ rows, ResultOrigin originalCount allowed prior row.row.row.id) :
    TraceOriginalSupport originalCount allowed
      (prior ++ (LocalUnitCases.unitUsing state context rows goal entails pending covers).steps) ∧
      ResultOrigin originalCount allowed
        (prior ++ (LocalUnitCases.unitUsing state context rows goal entails pending covers).steps)
        (LocalUnitCases.unitUsing state context rows goal entails pending covers).result.row.id := by
  unfold LocalUnitCases.unitUsing
  apply case_compile_supported
  · exact (LocalUnitCases.build _ _ _ _ _ _ _ _ _ _ _).valid
  · exact supported
  · exact originalBound
  · exact bound
  · exact local_build_origins _ _ _ _ _ _ _ _ _ _ _ _ _ _ origins

open Controller.NativeProof.SourceDecoderSchedule
open Controller.NativeProof.SourceMixedSchedule

open Controller.Native Controller.Native.SourceController

/-- Only native controller and decoder emissions are retained. Both source
observation layers and their private OR folds are excluded. -/
def retainedOwner : Owner parameters → Bool
  | .oldDifference _ | .oldDetected _ => false
  | .native (.internal (.difference _)) | .native (.internal .detected) => false
  | .fold (.internal (.difference _)) _ | .fold (.internal .detected) _ => false
  | _ => true

def retainedIndex (parameters : Parameters) (index : Nat) : Prop :=
  index < (controller parameters).entries.length ∨
    ((SourceFoldOccurrences.decoderStart (parameters := parameters) .healthy).entries.length ≤ index ∧
      index < (attachDecoder parameters .healthy (SourceFoldOccurrences.decoderStart .healthy)).entries.length) ∨
    ((SourceFoldOccurrences.decoderStart (parameters := parameters) .faulty).entries.length ≤ index ∧
      index < (attachDecoder parameters .faulty (SourceFoldOccurrences.decoderStart .faulty)).entries.length)

instance (parameters : Parameters) (index : Nat) : Decidable (retainedIndex parameters index) :=
  inferInstanceAs (Decidable (_ ∨ (_ ∧ _) ∨ (_ ∧ _)))

def nativeCoreEntries (parameters : Parameters) : List (Entry parameters) :=
  ((List.finRange (compile parameters).entries.length).filter
    (fun owner => decide (retainedIndex parameters owner.val))).map
    (fun owner => (compile parameters).entries[owner.val])

def nativeCoreRows (parameters : Parameters) : List (Clause Nat) :=
  ((nativeCoreEntries parameters).flatMap (fun entry => entry.producer.rows)) ++
    ((assertions parameters).take 3).map (fun literal => [literal])

def nativeCore (parameters : Parameters) : Formula Nat := ofClauses (nativeCoreRows parameters)

theorem native_model_core (parameters : Parameters) (signals : Nat → Bool)
    (model : Satisfies signals (formula parameters)) : Satisfies signals (nativeCore parameters) := by
  obtain ⟨equations, assertionsModel⟩ := (satisfies_append _ _ _).mp model
  have equationRows := (satisfies_ofClauses _ _).mp equations
  have assertionRows := (satisfies_ofClauses _ _).mp assertionsModel
  rw [nativeCore, nativeCoreRows, satisfies_ofClauses]
  intro clause member
  rcases List.mem_append.mp member with equation | assertion
  · obtain ⟨entry, present, row⟩ := List.mem_flatMap.mp equation
    obtain ⟨owner, _, same⟩ := List.mem_map.mp present
    subst entry
    exact equationRows clause (List.mem_flatMap.mpr ⟨_, List.getElem_mem owner.isLt, row⟩)
  · obtain ⟨literal, present, rfl⟩ := List.mem_map.mp assertion
    exact assertionRows [literal] (List.mem_map.mpr ⟨literal, List.mem_of_mem_take present, rfl⟩)

theorem core_producer_member (parameters : Parameters)
    (owner : Fin (compile parameters).entries.length) (kept : retainedIndex parameters owner.val)
    (index : Fin (compile parameters).entries[owner.val].producer.rows.length) :
    (compile parameters).entries[owner.val].producer.rows[index.val] ∈ nativeCoreRows parameters := by
  apply List.mem_append_left
  apply List.mem_flatMap.mpr
  refine ⟨(compile parameters).entries[owner.val], ?_, List.getElem_mem index.isLt⟩
  exact List.mem_map.mpr ⟨owner, List.mem_filter.mpr ⟨List.mem_finRange _, decide_eq_true kept⟩, rfl⟩

theorem core_physical_member (parameters : Parameters) (index : Fin 3) :
    [SourceMismatchBranch.physicalUnit (parameters := parameters) index] ∈ nativeCoreRows parameters := by
  apply List.mem_append_right
  apply List.mem_map.mpr
  refine ⟨SourceMismatchBranch.physicalUnit (parameters := parameters) index, ?_, rfl⟩
  have size : index.val < ((assertions parameters).take 3).length := by
    simpa [assertions] using index.isLt
  have entry := List.getElem_mem size
  simpa [SourceMismatchBranch.physicalUnit, List.getElem_take] using entry

/-- Every allowed original source row has an actual retained core clause. -/
theorem allowed_core_row (parameters : Parameters) (rename : Nat → Fin v) (rowId : Nat)
    (allowed : SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename rowId) :
    ∃ clause ∈ nativeCoreRows parameters,
      (initialState (relabel rename (formula parameters))).rows rowId = some (Rows.mapClause rename clause) := by
  rcases allowed with controllerRow | ⟨side, owner, lower, upper, _, index, rfl⟩
  · rcases controllerRow with ⟨owner, before, index, rfl⟩ | ⟨index, rfl⟩
    · exact ⟨_, core_producer_member parameters owner (Or.inl before) index,
        (SourceMismatchBranch.ownedRow rename owner index).present⟩
    · exact ⟨_, core_physical_member parameters index, (SourceMismatchBranch.physicalUnitRow rename index).present⟩
  · have kept : retainedIndex parameters owner.val := by
      cases side
      · exact Or.inr (Or.inl ⟨lower, upper⟩)
      · exact Or.inr (Or.inr ⟨lower, upper⟩)
    exact ⟨_, core_producer_member parameters owner kept index,
      (SourceMismatchBranch.ownedRow rename owner index).present⟩

def nativePair (parameters : Parameters) (output : Fin parameters.decoder.roots.length) :
    Literal Nat × Literal Nat :=
  (sourceRoleMap parameters (.internal (.decoder .healthy (parameters.decoder.roots.get output))),
    sourceRoleMap parameters (.internal (.decoder .faulty (parameters.decoder.roots.get output))))

def optionalNativeInput (parameters : Parameters)
    (wrapper : OptionalWrapper Nat (Fin internalCount) (Fin parameters.decoder.roots.length)) :
    Formula (Sum Nat (PrivateActivity (Fin internalCount) (Fin parameters.decoder.roots.length))) :=
  relabel Sum.inl (nativeCore parameters) ++ optionalFormula wrapper

def selectedNativeInput (parameters : Parameters)
    (wrapper : OptionalWrapper Nat (Fin internalCount) (Fin parameters.decoder.roots.length))
    (selected : List (Fin parameters.decoder.roots.length)) :
    Formula (Sum Nat (PrivateActivity (Fin internalCount) (Fin parameters.decoder.roots.length))) :=
  relabel Sum.inl (nativeCore parameters) ++ selectedOptionalFormula wrapper selected

/-- The independent source lift interprets a native observed pair as the
healthy singleton and the realized eligible faulty set. -/
theorem nativePair_lift (parameters : Parameters) (raw : parameters.layout = .raw)
    (K : Finset (Controller.Channel parameters.channels))
    (eligible : Controller.Admissible parameters.buses parameters.bridge.target K)
    (output : Fin parameters.decoder.roots.length) :
    Discrepant (SourceLift.assignment parameters
      (Controller.Physical.realizeBridge parameters.bridge parameters.positiveBuses K))
      (nativePair parameters output) ↔
    parameters.observations output (Controller.assignmentOfSet {parameters.bridge.target}) ≠
      parameters.observations output (Controller.assignmentOfSet K) := by
  let input := Controller.Physical.realizeBridge parameters.bridge parameters.positiveBuses K
  let signals := SourceLift.assignment parameters input
  have equations := SourceLift.equations parameters input
  have loaded := SourceLift.loaded parameters input
  have specification := Controller.Physical.realizeBridge_spec parameters.bridge parameters.positiveBuses K eligible
  have wire := (Controller.Physical.realizeBridge_cofactors parameters.bridge parameters.positiveBuses K).2.1
  simp only [nativePair, Discrepant]
  rw [sourceRoleMap_physical_of_equation_model parameters signals raw equations,
    sourceRoleMap_physical_of_equation_model parameters signals raw equations, loaded]
  change parameters.decoder.eval (parameters.qualifiers input (Controller.Physical.bridgeD parameters.bridge input) .healthy)
      (parameters.decoder.roots.get output) ≠
    parameters.decoder.eval (parameters.qualifiers input (Controller.Physical.bridgeD parameters.bridge input) .faulty)
      (parameters.decoder.roots.get output) ↔ _
  rw [wire]
  change parameters.decoder.eval (Controller.Physical.healthyQualifiers input) _ ≠
    parameters.decoder.eval (Controller.Physical.bridgeQualifiers parameters.bridge input true) _ ↔ _
  rw [specification.2.2.2.1, specification.2.2.2.2]
  rfl

theorem selected_native_absence (parameters : Parameters) (raw : parameters.layout = .raw)
    (drive : parameters.drive = true)
    (wrapper : OptionalWrapper Nat (Fin internalCount) (Fin parameters.decoder.roots.length))
    (pairs : ∀ output ∈ wrapper.tree.leaves, wrapper.observedPairs output = nativePair parameters output)
    (selected : List (Fin parameters.decoder.roots.length))
    (leaves : ∀ output ∈ selected, output ∈ wrapper.tree.leaves)
    (unsat : Unsatisfiable (selectedNativeInput parameters wrapper selected)) :
    Controller.NativeProof.Decoder.NoDiscrepancy parameters selected.toFinset := by
  intro output member K eligible
  have chosen : output ∈ selected := List.mem_toFinset.mp member
  by_contra different
  let input := Controller.Physical.realizeBridge parameters.bridge parameters.positiveBuses K
  let signals := SourceLift.assignment parameters input
  have checked := SourceLift.eligible_checked parameters raw K eligible drive ⟨output, Ne.symm different⟩
  have model := (Controller.Certificate.ModelCheck.check_iff _ _).mp checked
  have discrepant : Discrepant signals (wrapper.observedPairs output) := by
    rw [pairs output (leaves output chosen)]
    exact (nativePair_lift parameters raw K eligible output).mpr (Ne.symm different)
  obtain ⟨values, extension⟩ := (selectedOptionalFormula_projection wrapper selected leaves signals).mpr
    ⟨output, chosen, discrepant⟩
  apply unsat
  refine ⟨joint signals values, (satisfies_append _ _ _).mpr ⟨?_, extension⟩⟩
  exact (satisfies_relabel Sum.inl (joint signals values) (nativeCore parameters)).mpr
    (native_model_core parameters signals model)

/-- Original IDs are looked up in the retained input; derived IDs preserve
their offset from the original source count, even when the input shrinks. -/
def translatedId (sourceCount targetCount : Nat) (original : Nat → Nat) (rowId : Nat) : Nat :=
  if rowId ≤ sourceCount then original rowId else targetCount + (rowId - sourceCount)

def translatedStep (sourceCount targetCount : Nat) (original : Nat → Nat) (step : Step v) : Step v :=
  { id := translatedId sourceCount targetCount original step.id
    left := translatedId sourceCount targetCount original step.left
    right := translatedId sourceCount targetCount original step.right
    pivot := step.pivot
    clause := step.clause }

structure RetainedMatch (sourceCount targetCount : Nat) (original : Nat → Nat)
    (allowed : Nat → Prop) (source target : State v) : Prop where
  sourceBound : sourceCount ≤ source.lastId
  targetLast : target.lastId = targetCount + (source.lastId - sourceCount)
  originalBound : ∀ rowId, rowId ≤ sourceCount → allowed rowId → original rowId ≤ targetCount
  rows : ∀ rowId, sourceCount < rowId ∨ allowed rowId →
    target.rows (translatedId sourceCount targetCount original rowId) = source.rows rowId

theorem translated_parent_lt (matched : RetainedMatch sourceCount targetCount original allowed source target)
    (fresh : source.lastId < newId) (before : rowId < newId)
    (permitted : rowId ≤ sourceCount → allowed rowId) :
    translatedId sourceCount targetCount original rowId <
      translatedId sourceCount targetCount original newId := by
  have derived : sourceCount < newId := lt_of_le_of_lt matched.sourceBound fresh
  rw [show translatedId sourceCount targetCount original newId = targetCount + (newId - sourceCount)
    from ite_eq_right (Nat.not_le.mpr derived)]
  unfold translatedId
  split
  · have bound := matched.originalBound rowId (by assumption) (permitted (by assumption))
    omega
  · omega

theorem retainedMatch_insert (matched : RetainedMatch sourceCount targetCount original allowed source target)
    (fresh : source.lastId < newId) (clause : Clause (Fin v)) :
    RetainedMatch sourceCount targetCount original allowed (insertRow source newId clause)
      (insertRow target (translatedId sourceCount targetCount original newId) clause) := by
  have derived : sourceCount < newId := lt_of_le_of_lt matched.sourceBound fresh
  have translated : translatedId sourceCount targetCount original newId = targetCount + (newId - sourceCount) :=
    ite_eq_right (Nat.not_le.mpr derived)
  refine ⟨by change sourceCount ≤ newId; omega, by change _ = _; exact translated,
    matched.originalBound, ?_⟩
  intro rowId permitted
  by_cases same : rowId = newId
  · subst rowId
    simp only [insertRow_self]
  · have distinct : translatedId sourceCount targetCount original rowId ≠
        translatedId sourceCount targetCount original newId := by
      rw [translated]
      unfold translatedId
      split
      · have allowedRow := permitted.resolve_left (by omega)
        have oldBound := matched.originalBound rowId (by assumption) allowedRow
        omega
      · omega
    rw [insertRow_other _ _ _ _ distinct, insertRow_other _ _ _ _ same]
    exact matched.rows rowId permitted

theorem applyStep_retained {source next target : State v} {step : Step v}
    (matched : RetainedMatch sourceCount targetCount original allowed source target)
    (checked : applyStep source step = some next)
    (left : step.left ≤ sourceCount → allowed step.left)
    (right : step.right ≤ sourceCount → allowed step.right) :
    ∃ nextTarget, applyStep target (translatedStep sourceCount targetCount original step) = some nextTarget ∧
      RetainedMatch sourceCount targetCount original allowed next nextTarget := by
  obtain ⟨one, two, first, second, valid, rfl⟩ := applyStep_success checked
  have derived : sourceCount < step.id := lt_of_le_of_lt matched.sourceBound valid.1
  have fresh : target.lastId < translatedId sourceCount targetCount original step.id := by
    have sourceBound := matched.sourceBound
    have newBound := valid.1
    rw [matched.targetLast, translatedId, ite_eq_right (Nat.not_le.mpr derived)]
    omega
  have firstTarget := (matched.rows step.left (by
    by_cases old : step.left ≤ sourceCount
    · exact Or.inr (left old)
    · exact Or.inl (Nat.lt_of_not_ge old))).trans first
  have secondTarget := (matched.rows step.right (by
    by_cases old : step.right ≤ sourceCount
    · exact Or.inr (right old)
    · exact Or.inl (Nat.lt_of_not_ge old))).trans second
  have ok : StepOK target (translatedStep sourceCount targetCount original step) one two :=
    ⟨fresh, translated_parent_lt matched valid.1 valid.2.1 left,
      translated_parent_lt matched valid.1 valid.2.2.1 right, valid.2.2.2⟩
  refine ⟨insertRow target (translatedId sourceCount targetCount original step.id) step.clause,
    ?_, retainedMatch_insert matched valid.1 step.clause⟩
  unfold applyStep translatedStep
  dsimp only
  rw [firstTarget, secondTarget]
  exact ite_eq_left ok

theorem runSteps_retained {source next target : State v} {steps : List (Step v)}
    (matched : RetainedMatch sourceCount targetCount original allowed source target)
    (checked : runSteps source steps = some next)
    (supported : ∀ step ∈ steps, ∀ parent ∈ [step.left, step.right],
      parent ≤ sourceCount → allowed parent) :
    ∃ nextTarget, runSteps target (steps.map (translatedStep sourceCount targetCount original)) = some nextTarget ∧
      RetainedMatch sourceCount targetCount original allowed next nextTarget := by
  induction steps generalizing source target with
  | nil => cases checked; exact ⟨target, rfl, matched⟩
  | cons step rest ih =>
    simp only [runSteps] at checked
    cases first : applyStep source step with
    | none => simp [first] at checked
    | some middle =>
      simp only [first] at checked
      obtain ⟨middleTarget, firstTarget, matchMiddle⟩ := applyStep_retained matched first
        (supported step (by simp) step.left (by simp))
        (supported step (by simp) step.right (by simp))
      obtain ⟨final, restTarget, finalMatch⟩ := ih matchMiddle checked
        (fun query member => supported query (List.mem_cons_of_mem _ member))
      exact ⟨final, by simp only [List.map_cons, runSteps, firstTarget]; exact restTarget, finalMatch⟩

def RetainedMatch.available {source target : State v}
    (matched : RetainedMatch sourceCount targetCount original allowed source target)
    (row : Rows.Available source clause) (permitted : sourceCount < row.id ∨ allowed row.id) :
    Rows.Available target clause := by
  refine ⟨translatedId sourceCount targetCount original row.id,
    (matched.rows row.id permitted).trans row.present, ?_⟩
  rw [matched.targetLast]
  unfold translatedId
  split
  · have permittedOld := permitted.resolve_left (by omega)
    have originalBound := matched.originalBound row.id (by assumption) permittedOld
    omega
  · have rowBound := row.bound
    omega

def originalLookup (source : FiniteFormula v) (targetRows : List (Clause (Fin v))) (rowId : Nat) : Nat :=
  match (initialState source).rows rowId with
  | none => 0
  | some clause => targetRows.idxOf clause + 1

theorem originalLookup_row (source : FiniteFormula v) (targetRows : List (Clause (Fin v)))
    (present : (initialState source).rows rowId = some clause) (member : clause ∈ targetRows) :
    (initialState (ofClauses targetRows)).rows (originalLookup source targetRows rowId) = some clause ∧
      originalLookup source targetRows rowId ≤ targetRows.length := by
  have bound := List.idxOf_lt_length_of_mem member
  have content : (ofClauses targetRows).clauses[targetRows.idxOf clause] = clause :=
    List.getElem_idxOf bound
  have row := initialState_row (ofClauses targetRows) (targetRows.idxOf clause) (by simpa [ofClauses] using bound)
  have actualRow := row.trans (congrArg some content)
  simp only [originalLookup, present]
  exact ⟨actualRow, by omega⟩

theorem initial_retained_match (source : FiniteFormula v) (targetRows : List (Clause (Fin v)))
    (allowed : Nat → Prop)
    (covered : ∀ rowId, allowed rowId → ∃ clause ∈ targetRows,
      (initialState source).rows rowId = some clause) :
    RetainedMatch source.clauses.size targetRows.length (originalLookup source targetRows) allowed
      (initialState source) (initialState (ofClauses targetRows)) := by
  refine ⟨le_rfl, by simp [initialState, ofClauses], ?_, ?_⟩
  · intro rowId _ permitted
    obtain ⟨clause, member, present⟩ := covered rowId permitted
    exact (originalLookup_row source targetRows present member).2
  · intro rowId relevant
    by_cases old : rowId ≤ source.clauses.size
    · have permitted := relevant.resolve_left (by omega)
      obtain ⟨clause, member, present⟩ := covered rowId permitted
      rw [translatedId, ite_eq_left old, present]
      exact (originalLookup_row source targetRows present member).1
    · have above : source.clauses.size < rowId := Nat.lt_of_not_ge old
      have nonzero : rowId ≠ 0 := by omega
      have translatedNonzero : targetRows.length + (rowId - source.clauses.size) ≠ 0 := by omega
      have sourceOutside : source.clauses.size ≤ rowId - 1 := by omega
      have targetOutside : (ofClauses targetRows).clauses.size ≤
          targetRows.length + (rowId - source.clauses.size) - 1 := by simp [ofClauses]; omega
      simp only [translatedId, ite_eq_right old, initialState, ite_eq_right nonzero, ite_eq_right translatedNonzero]
      rw [Array.getElem?_eq_none sourceOutside, Array.getElem?_eq_none targetOutside]

structure RetainedReplay (sourceCount targetCount : Nat) (original : Nat → Nat)
    (allowed : Nat → Prop) (source next target : State v) (program : List (Step v)) where
  state : State v
  steps : List (Step v)
  emitted : steps = program.map (translatedStep sourceCount targetCount original)
  checked : runSteps target steps = some state
  matched : RetainedMatch sourceCount targetCount original allowed next state

/-- Execution is total on a checked, supported source prefix and a computed
retained-row correspondence. No successful checker result is assumed. -/
def replayRetained (matched : RetainedMatch sourceCount targetCount original allowed source target)
    (program : List (Step v)) (next : State v) (checked : runSteps source program = some next)
    (supported : TraceOriginalSupport sourceCount allowed program) :
    RetainedReplay sourceCount targetCount original allowed source next target program := by
  let steps := program.map (translatedStep sourceCount targetCount original)
  have succeeds := runSteps_retained matched checked
    (fun step member parent present => (supported step member parent present).1)
  match result : runSteps target steps with
  | none =>
    have impossible : False := by
      obtain ⟨final, finalRun, _⟩ := succeeds
      rw [result] at finalRun
      contradiction
    exact False.elim impossible
  | some final =>
    refine ⟨final, steps, rfl, result, ?_⟩
    obtain ⟨other, finalRun, finalMatch⟩ := succeeds
    have same : other = final := Option.some.inj (finalRun.symm.trans result)
    exact same ▸ finalMatch

def taggedCoreRows (parameters : Parameters) {α : Type} : List (Clause (Sum Nat α)) :=
  (nativeCoreRows parameters).map (fun clause => clause.map (fun literal => (Sum.inl literal.1, literal.2)))

def optionalInputRows (parameters : Parameters)
    (wrapper : OptionalWrapper Nat (Fin internalCount) (Fin parameters.decoder.roots.length)) :=
  taggedCoreRows parameters ++ optionalRows wrapper

theorem native_initial_match (parameters : Parameters)
    (wrapper : OptionalWrapper Nat (Fin internalCount) (Fin parameters.decoder.roots.length))
    (rename : Sum Nat (PrivateActivity (Fin internalCount) (Fin parameters.decoder.roots.length)) → Fin v) :
    let signalRename := fun signal => rename (Sum.inl signal)
    let source := relabel signalRename (formula parameters)
    let targetRows := (optionalInputRows parameters wrapper).map (Rows.mapClause rename)
    RetainedMatch source.clauses.size targetRows.length (originalLookup source targetRows)
      (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) signalRename)
      (initialState source) (initialState (ofClauses targetRows)) := by
  dsimp only
  apply initial_retained_match
  intro rowId allowed
  obtain ⟨clause, member, present⟩ := allowed_core_row parameters (fun signal => rename (Sum.inl signal)) rowId allowed
  refine ⟨Rows.mapClause (fun signal => rename (Sum.inl signal)) clause, ?_, present⟩
  unfold optionalInputRows
  apply List.mem_map.mpr
  refine ⟨clause.map (fun literal => (Sum.inl literal.1, literal.2)), ?_, ?_⟩
  · exact List.mem_append_left _ (List.mem_map.mpr ⟨clause, member, rfl⟩)
  · simp [Rows.mapClause, List.map_map, Function.comp_def]

theorem origin_relevant (origin : ResultOrigin originalCount allowed prior rowId) :
    originalCount < rowId ∨ allowed rowId := by
  rcases origin with original | ⟨step, _, same, derived⟩
  · exact Or.inr original
  · exact Or.inl (same ▸ derived)

def retainedTransfer {parameters : Parameters}
    (rename : Nat → Fin v) (proofPrefix : SourcePrefix (parameters := parameters) rename)
    (matched : RetainedMatch (formula parameters).clauses.size targetCount original
      (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) proofPrefix.state target)
    (transfer : SourceStageCongruence.GuardedTransfer proofPrefix.state context input output)
    (origin : SourceDecoderSchedule.GuardedTransferOrigin rename proofPrefix transfer) :
    SourceStageCongruence.GuardedTransfer target context input output := by
  match transfer with
  | .identity same => exact .identity same
  | .derived row => exact .derived ⟨row.clause, matched.available row.row (origin_relevant origin), row.subset⟩

def retainedPair {parameters : Parameters}
    (rename : Nat → Fin v) (proofPrefix : SourcePrefix (parameters := parameters) rename)
    (matched : RetainedMatch (formula parameters).clauses.size targetCount original
      (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) proofPrefix.state target)
    (pair : DirectionPair proofPrefix.state context input output)
    (origin : SourceDecoderSchedule.DirectionPairOrigin rename proofPrefix pair) :
    DirectionPair target context input output :=
  ⟨retainedTransfer rename proofPrefix matched pair.forward origin.1,
    retainedTransfer rename proofPrefix matched pair.backward origin.2⟩

theorem mapped_formula (rename : α → Fin v) (clauses : List (Clause α)) :
    relabel rename (ofClauses clauses) = ofClauses (clauses.map (Rows.mapClause rename)) := by
  simp [relabel, Controller.CNF.OrderedFormula.relabel, Controller.CNF.OrderedFormula.Clause.relabel, ofClauses, Rows.mapClause]

def optionalFiniteInput (parameters : Parameters)
    (wrapper : OptionalWrapper Nat (Fin internalCount) (Fin parameters.decoder.roots.length))
    (rename : Sum Nat (PrivateActivity (Fin internalCount) (Fin parameters.decoder.roots.length)) → Fin v) :
    FiniteFormula v := ofClauses ((optionalInputRows parameters wrapper).map (Rows.mapClause rename))

structure OptionalEqualityPrefix (parameters : Parameters)
    (wrapper : OptionalWrapper Nat (Fin internalCount) (Fin parameters.decoder.roots.length))
    (rename : Sum Nat (PrivateActivity (Fin internalCount) (Fin parameters.decoder.roots.length)) → Fin v) where
  state : State v
  steps : List (Step v)
  checked : runSteps (initialState (optionalFiniteInput parameters wrapper rename)) steps = some state
  pairs : ∀ output ∈ wrapper.tree.leaves, DirectionPair state []
    (rename (.inl (wrapper.observedPairs output).1.1), (wrapper.observedPairs output).1.2)
    (rename (.inl (wrapper.observedPairs output).2.1), (wrapper.observedPairs output).2.2)

open Controller.NativeProof.SourceDecoderTraversal

/-- The zero-drive native prefix is replayed using only the retained original
core, with no source observation definition or assertion in the new input. -/
def optionalZeroPrefix (parameters : Parameters) (drive : parameters.drive = false)
    (wrapper : OptionalWrapper Nat (Fin internalCount) (Fin parameters.decoder.roots.length))
    (pairs : ∀ output ∈ wrapper.tree.leaves, wrapper.observedPairs output = nativePair parameters output)
    (rename : Sum Nat (PrivateActivity (Fin internalCount) (Fin parameters.decoder.roots.length)) → Fin v) :
    OptionalEqualityPrefix parameters wrapper rename := by
  let signalRename := fun signal => rename (Sum.inl signal)
  let source := relabel signalRename (formula parameters)
  let targetRows := (optionalInputRows parameters wrapper).map (Rows.mapClause rename)
  let old := driveZeroOutputPrefix (parameters := parameters) signalRename drive
  have matched : RetainedMatch (formula parameters).clauses.size targetRows.length
      (originalLookup source targetRows)
      (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) signalRename)
      (initialState source) (initialState (ofClauses targetRows)) := by
    simpa only [source, targetRows, signalRename, relabel, Controller.CNF.OrderedFormula.relabel, Array.size_map] using
      native_initial_match parameters wrapper rename
  let replay := replayRetained matched old.steps old.state old.checked
    (driveZeroOutputPrefix_supported signalRename drive)
  refine ⟨replay.state, replay.steps, replay.checked, ?_⟩
  intro output member
  rw [pairs output member]
  exact retainedPair signalRename old replay.matched (driveZeroOutputRoot signalRename drive output)
    (driveZeroOutputRoot_supported signalRename drive output)

structure OptionalRefutation (parameters : Parameters)
    (wrapper : OptionalWrapper Nat (Fin internalCount) (Fin parameters.decoder.roots.length))
    (rename : Sum Nat (PrivateActivity (Fin internalCount) (Fin parameters.decoder.roots.length)) → Fin v) where
  trace : Trace v
  accepted : Controller.Resolution.check (optionalFiniteInput parameters wrapper rename) trace = true

def optionalRefutationFromPrefix (parameters : Parameters)
    (wrapper : OptionalWrapper Nat (Fin internalCount) (Fin parameters.decoder.roots.length))
    (rename : Sum Nat (PrivateActivity (Fin internalCount) (Fin parameters.decoder.roots.length)) → Fin v)
    (proofPrefix : OptionalEqualityPrefix parameters wrapper rename) :
    OptionalRefutation parameters wrapper rename := by
  have checked : runSteps (initialState (relabel rename (ofClauses (optionalInputRows parameters wrapper))))
      proofPrefix.steps = some proofPrefix.state := by
    rw [mapped_formula]
    exact proofPrefix.checked
  let suffix := optionalAfterPrefix rename (taggedCoreRows parameters) wrapper proofPrefix.state
    proofPrefix.steps checked [] proofPrefix.pairs
  have empty : suffix.result.clause = [] := by
    cases shape : suffix.result.clause with
    | nil => rfl
    | cons head tail =>
      exact False.elim (by have bad := suffix.result.subset head (by rw [shape]; simp); simpa using bad)
  let trace : Trace v := ⟨(optionalFiniteInput parameters wrapper rename).clauses.size,
    proofPrefix.steps ++ suffix.steps, suffix.result.row.id⟩
  refine ⟨trace, ?_⟩
  have combined : runSteps (initialState (optionalFiniteInput parameters wrapper rename)) trace.steps =
      some suffix.state := by
    rw [runSteps_append, proofPrefix.checked]
    exact suffix.checked
  have final : suffix.state.rows trace.finalClauseId = some [] := by
    exact suffix.result.row.present.trans (congrArg some empty)
  unfold Controller.Resolution.check
  rw [ite_eq_left (show trace.originalClauseCount = (optionalFiniteInput parameters wrapper rename).clauses.size from rfl),
    combined]
  simp only [final]
  rfl

def optionalZeroRefutation (parameters : Parameters) (drive : parameters.drive = false)
    (wrapper : OptionalWrapper Nat (Fin internalCount) (Fin parameters.decoder.roots.length))
    (pairs : ∀ output ∈ wrapper.tree.leaves, wrapper.observedPairs output = nativePair parameters output)
    (rename : Sum Nat (PrivateActivity (Fin internalCount) (Fin parameters.decoder.roots.length)) → Fin v) :
    OptionalRefutation parameters wrapper rename :=
  optionalRefutationFromPrefix parameters wrapper rename (optionalZeroPrefix parameters drive wrapper pairs rename)

theorem aggregate_long_supported {parameters : Parameters}
    (rename : Nat → Fin v) (proofPrefix : SourcePrefix (parameters := parameters) rename)
    (tree : AndTree proofPrefix.state root inputs) (two : 2 ≤ inputs.length)
    (supported : SourceDecoderSchedule.PrefixOriginalSupport rename proofPrefix)
    (original : TreeOriginals (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) tree) :
    TraceOriginalSupport (formula parameters).clauses.size
      (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
      (proofPrefix.steps ++ (projectTreeLong tree).steps) ∧
      ResultOrigin (formula parameters).clauses.size
        (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
        (proofPrefix.steps ++ (projectTreeLong tree).steps)
        (nonunaryAggregate (projectTreeLong tree).result two).row.id := by
  have actual := projectTreeLong_supported proofPrefix.state tree (formula parameters).clauses.size
    (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) proofPrefix.steps
    original supported (SourceDecoderSchedule.allowed_native_count_le rename)
    (SourceMixedSchedule.prefix_native_count_le rename proofPrefix)
  exact ⟨actual.1, SourceDecoderSchedule.nonunaryAggregate_origin _ _ _ _ two actual.2⟩

theorem force_node_fields (left : AndTree state leftRoot leftInputs)
    (right : AndTree state rightRoot rightInputs) (root : Literal (Fin v))
    (rows : BinaryAndRows state leftRoot rightRoot root) (context : Clause (Fin v))
    (units : ∀ input ∈ leftInputs ++ rightInputs, AvailableSubclause state (context ++ [input])) :
    let tree := AndTree.node left right root rows
    let two : 2 ≤ (leftInputs ++ rightInputs).length := by
      have one := left.nodes_leaves; have other := right.nodes_leaves
      simp only [List.length_append]; omega
    let projected := projectTreeLong tree
    let row := nonunaryAggregate projected.result two
    let known := fun input member => afterTrace (units input member) projected.state projected.steps projected.checked
    let parent : AvailableSubclause projected.state ((leftInputs ++ rightInputs).map negate ++ (context ++ [root])) :=
      retarget row (by
        intro literal member
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member ⊢
        aesop)
    let eliminated := dischargeInputs projected.state (leftInputs ++ rightInputs) (context ++ [root]) parent
      (fun input member => retarget (known input member) (by
        intro literal present
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at present ⊢
        aesop))
    (TreeUnits.force tree context units).steps = projected.steps ++ eliminated.steps ∧
      (TreeUnits.force tree context units).result.row.id = eliminated.result.row.id := by
  constructor <;> rfl

theorem tree_force_supported {parameters : Parameters}
    (rename : Nat → Fin v) (proofPrefix : SourcePrefix (parameters := parameters) rename)
    (tree : AndTree proofPrefix.state root inputs) (context : Clause (Fin v))
    (units : ∀ input ∈ inputs, AvailableSubclause proofPrefix.state (context ++ [input]))
    (supported : SourceDecoderSchedule.PrefixOriginalSupport rename proofPrefix)
    (original : TreeOriginals (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) tree)
    (unitOrigins : ∀ input member, ResultOrigin (formula parameters).clauses.size
      (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) proofPrefix.steps
      (units input member).row.id) :
    SourceDecoderSchedule.ProjectionOriginalSupport rename proofPrefix (TreeUnits.force tree context units) := by
  cases tree with
  | leaf =>
    unfold SourceDecoderSchedule.ProjectionOriginalSupport
    simp only [TreeUnits.force, List.append_nil]
    exact ⟨supported, unitOrigins root (by simp)⟩
  | @node leftRoot rightRoot leftInputs rightInputs left right root rows =>
    let tree := AndTree.node left right root rows
    have two : 2 ≤ (leftInputs ++ rightInputs).length := by
      have one := left.nodes_leaves; have other := right.nodes_leaves
      simp only [List.length_append]; omega
    let projected := projectTreeLong tree
    let row := nonunaryAggregate projected.result two
    have projectionSupport := aggregate_long_supported rename proofPrefix tree two supported original
    let current := proofPrefix.extend projected.state projected.steps projected.checked
    let known := fun input member => afterTrace (units input member) projected.state projected.steps projected.checked
    let parent : AvailableSubclause projected.state ((leftInputs ++ rightInputs).map negate ++ (context ++ [root])) :=
      retarget row (by
        intro literal member
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member ⊢
        aesop)
    let propagation : ∀ input ∈ leftInputs ++ rightInputs,
        AvailableSubclause projected.state ((context ++ [root]) ++ [input]) := fun input member => retarget (known input member) (by
      intro literal present
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at present ⊢
      aesop)
    have final := SourceDecoderSchedule.dischargeInputs_supported rename current (leftInputs ++ rightInputs)
      (context ++ [root]) parent propagation projectionSupport.1 projectionSupport.2
      (fun input member => resultOrigin_append_right _ _ proofPrefix.steps projected.steps _ (unitOrigins input member))
    have fields := force_node_fields left right root rows context units
    unfold SourceDecoderSchedule.ProjectionOriginalSupport
    rw [fields.1, fields.2]
    simpa only [SourceDecoderSchedule.ProjectionOriginalSupport, current, SourcePrefix.extend,
      projected, parent, propagation, known, row, tree, List.append_assoc] using final

theorem treeOriginals_mono (included : ∀ rowId, one rowId → two rowId)
    (tree : AndTree state root inputs) (original : TreeOriginals one tree) : TreeOriginals two tree := by
  induction tree with
  | leaf => trivial
  | node left right root rows first second =>
    exact ⟨first original.1, second original.2.1,
      included _ original.2.2.1, included _ original.2.2.2.1, included _ original.2.2.2.2⟩

theorem firstMaskRows_allowed {parameters : Parameters} (rename : Nat → Fin v)
    (side : Side) (channel : Fin parameters.channels)
    (index : Fin 4) :
    SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename
      ((SourceMismatchAdvance.initialMaskRowsExact rename side channel).row
        ⟨index.val, by change index.val < 4; exact index.isLt⟩).id := by
  apply Or.inl
  simpa only [SourceMismatchAdvance.initialMaskRowsExact, SourceMismatchBranch.emitRowsExact,
    SourceMismatchBranch.ownedRow, SourceCongruence.emitOwner, SourceRows.before, id] using
    SourceMismatchBranch.emitRow_allowed rename (SourceCongruence.initialMaskBefore side channel)
      (.internal (.mask side parameters.firstBus channel))
      (.xor ((SourceCongruence.initialMaskBefore side channel).slots (.internal (.flag side parameters.firstBus)))
        ((SourceCongruence.initialMaskBefore side channel).slots (.internal (.absent side parameters.firstBus channel))))
      (SourceEqualSchedule.initial_mask_before_controller side channel)
      ⟨index.val, by change index.val < 4; exact index.isLt⟩

theorem groupTree_originals {parameters : Parameters} (rename : Nat → Fin v)
    (group : SourceMismatchSeed.Group)
    (nonempty : SourceMismatchSeed.groupInputs (parameters := parameters) group ≠ []) :
    TreeOriginals (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
      (SourceMismatchSeed.groupTree rename group nonempty) := by
  apply treeOriginals_mono (fun _ origin => Or.inl origin)
  cases group with
  | drivers =>
    unfold SourceMismatchSeed.groupTree
    apply allocateForest_originals
    · exact initialForest_originals _ _ _
    · simpa only [SourceFoldOwners.driverRows] using
        actualFoldRows_allowed rename (firstArrays parameters) (.internal .driver) .conjunction
          (SourceFoldOwners.driverInputs parameters)
          (SourceFoldOwners.driver_before_interface.trans SourceFoldOwners.interface_before_controller)
  | remaining =>
    unfold SourceMismatchSeed.groupTree
    apply allocateForest_originals
    · exact initialForest_originals _ _ _
    · simpa only [SourceFoldOwners.remainingRows] using
        actualFoldRows_allowed rename (SourceFoldOwners.driverCursor parameters) (.internal .remaining) .conjunction
          (SourceFoldOwners.remainingInputs parameters)
          (SourceFoldOwners.remaining_before_interface.trans SourceFoldOwners.interface_before_controller)

theorem firstMaskForward_allowed {parameters : Parameters} (rename : Nat → Fin v)
    (side : Side) (channel : Fin parameters.channels) :
    SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename
      (SourceMismatchAdvance.initialMaskForward rename side channel).row.id := by
  cases side
  all_goals
    unfold SourceMismatchAdvance.initialMaskForward
    simp only [retarget, ofRow, id]
    repeat' rw [SourceMixedSchedule.subclause_indices_cast_id rfl (by
      simp [Bounded.Producer.rows, Gate.clauses, Rows.mapClause, SourceCongruence.maskFlag,
        SourceCongruence.maskAbsent, SourceCongruence.maskOutput, SourceFoldProjection.mapLiteral,
        negate, Std.Sat.Literal.negate])]
  · exact firstMaskRows_allowed (parameters := parameters) rename .healthy channel ⟨3, by decide⟩
  · exact firstMaskRows_allowed (parameters := parameters) rename .faulty channel ⟨2, by decide⟩

theorem firstMaskBackward_allowed {parameters : Parameters} (rename : Nat → Fin v)
    (side : Side) (channel : Fin parameters.channels) :
    SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename
      (SourceMismatchAdvance.initialMaskBackward rename side channel).row.id := by
  cases side
  all_goals
    unfold SourceMismatchAdvance.initialMaskBackward
    simp only [retarget, ofRow, id]
    repeat' rw [SourceMixedSchedule.subclause_indices_cast_id rfl (by
      simp [Bounded.Producer.rows, Gate.clauses, Rows.mapClause, SourceCongruence.maskFlag,
        SourceCongruence.maskAbsent, SourceCongruence.maskOutput, SourceFoldProjection.mapLiteral,
        negate, Std.Sat.Literal.negate])]
  · exact firstMaskRows_allowed (parameters := parameters) rename .healthy channel ⟨1, by decide⟩
  · exact firstMaskRows_allowed (parameters := parameters) rename .faulty channel ⟨0, by decide⟩

theorem maskValueOriginal_allowed {parameters : Parameters} (rename : Nat → Fin v)
    (side : Side) (channel : Fin parameters.channels) (absence : Bool) :
    SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename
      (SourceMismatchAdvance.maskValueOriginal rename side channel absence).row.id := by
  cases side <;> cases absence
  · exact firstMaskForward_allowed rename .healthy channel
  · exact firstMaskBackward_allowed rename .healthy channel
  · exact firstMaskBackward_allowed rename .faulty channel
  · exact firstMaskForward_allowed rename .faulty channel

theorem faultyProductRows_allowed {parameters : Parameters} (rename : Nat → Fin v) (index : Fin 4) :
    SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename
      ((SourceMismatchBranch.faultyProductRows (parameters := parameters) rename).row
        ⟨index.val, by change index.val < 4; exact index.isLt⟩).id := by
  apply Or.inl
  have retained : SourceFoldOwners.EntriesBefore
      (SourceMismatchBranch.faultyProductCursor (parameters := parameters)) (controller parameters) :=
    (SourceFoldOwners.emitNative_before _ _ _).trans SourceFoldOwners.interface_before_controller
  simpa only [SourceMismatchBranch.faultyProductRows, SourceMismatchBranch.emitRowsExact,
    SourceMismatchBranch.ownedRow, SourceCongruence.emitOwner, SourceRows.before] using
    SourceMismatchBranch.emitRow_allowed rename (SourceMismatchBranch.healthyFlagCursor (parameters := parameters))
      (.internal (.firstProduct .faulty)) (.and (SourceMismatchBranch.faultyProductInputs (parameters := parameters)))
      retained ⟨index.val, by change index.val < 4; exact index.isLt⟩

theorem faultyFlagRows_allowed {parameters : Parameters} (rename : Nat → Fin v) (index : Fin 2) :
    SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename
      ((SourceMismatchBranch.faultyFlagRows (parameters := parameters) rename).row
        ⟨index.val, by change index.val < 2; exact index.isLt⟩).id := by
  apply Or.inl
  simpa only [SourceMismatchBranch.faultyFlagRows, SourceMismatchBranch.emitRowsExact,
    SourceMismatchBranch.ownedRow, SourceCongruence.emitOwner, SourceRows.before] using
    SourceMismatchBranch.emitRow_allowed rename (SourceMismatchBranch.faultyProductCursor (parameters := parameters))
      (.internal (.flag .faulty parameters.firstBus))
      (.not ((SourceMismatchBranch.faultyProductCursor (parameters := parameters)).slots (.internal (.firstProduct .faulty))))
      SourceFoldOwners.interface_before_controller ⟨index.val, by change index.val < 2; exact index.isLt⟩

theorem maskValueAt_supported {parameters : Parameters} (rename : Nat → Fin v)
    (proofPrefix : SourcePrefix (parameters := parameters) rename) (side : Side)
    (channel : Fin parameters.channels) (absence : Bool)
    (seed : AvailableSubclause proofPrefix.state
      (SourceMismatchAdvance.mixedContext (parameters := parameters) rename ++
        [SourceMismatchAdvance.absenceValue rename channel absence]))
    (supported : SourceDecoderSchedule.PrefixOriginalSupport rename proofPrefix)
    (seedOrigin : ResultOrigin (formula parameters).clauses.size
      (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) proofPrefix.steps seed.row.id) :
    SourceDecoderSchedule.ProjectionOriginalSupport rename proofPrefix
      (SourceMismatchAdvance.maskValueAt rename proofPrefix side channel absence seed) := by
  let input := SourceMismatchAdvance.absenceValue rename channel absence
  let output := SourceMismatchAdvance.firstMaskValue rename side channel absence
  let context := SourceMismatchAdvance.mixedContext (parameters := parameters) rename
  let original := SourceMismatchAdvance.maskValueOriginal rename side channel absence
  let row := FoldProjection.afterTrace original proofPrefix.state proofPrefix.steps proofPrefix.checked
  let left : AvailableSubclause proofPrefix.state (negate input :: (context ++ [output])) := retarget row (by
    intro literal member
    simp only [input, output, context, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member ⊢
    rcases member with old | pivot | final
    · exact Or.inr (Or.inl old)
    · exact Or.inl pivot
    · exact Or.inr (Or.inr final))
  let right : AvailableSubclause proofPrefix.state (input :: context) := retarget seed (by
    intro literal member
    simp only [input, context, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member ⊢
    exact member.elim Or.inr Or.inl)
  have leftOrigin : ResultOrigin (formula parameters).clauses.size
      (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) proofPrefix.steps left.row.id :=
    Or.inl (maskValueOriginal_allowed rename side channel absence)
  have actual := SourceMixedSchedule.longMerge_supported (formula parameters).clauses.size
    (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) proofPrefix.steps proofPrefix.state
    input (context ++ [output]) context left right supported
    (SourceDecoderSchedule.allowed_native_count_le rename)
    (SourceMixedSchedule.prefix_native_count_le rename proofPrefix) leftOrigin seedOrigin
  simpa only [SourceMismatchAdvance.maskValueAt, SourceDecoderSchedule.ProjectionOriginalSupport,
    input, output, context, original, row, left, right, retarget] using actual

/-- Complementary cofactor subclauses merge before the physical healthy unit
is discharged. Both operations are ordinary resolution with stronger-row reuse. -/
def cofactorFinish (state : State v) (healthy faulty : Literal (Fin v))
    (zero : AvailableSubclause state [negate healthy, faulty])
    (one : AvailableSubclause state [negate healthy, negate faulty])
    (physical : AvailableSubclause state [healthy]) : SubclauseProjection state [] 2 := by
  let joined := mergeContext state [negate healthy] faulty [] []
    (by simpa using one) (by simpa using zero)
  let unitNow := FoldProjection.afterTrace physical joined.state joined.steps joined.checked
  let final := mergeContext joined.state [] healthy [] []
    (by simpa using joined.result) (by simpa using unitNow)
  refine ⟨final.state, joined.steps ++ final.steps, ?_, ?_, ?_⟩
  · rw [runSteps_append, joined.checked]
    exact final.checked
  · simpa using final.result
  · have first := joined.count
    have second := final.count
    simp only [List.length_append]
    omega

theorem faultyZeroInputAt_supported {parameters : Parameters} (rename : Nat → Fin v)
    (proofPrefix : SourcePrefix (parameters := parameters) rename) (index : Fin 3)
    (supported : SourceDecoderSchedule.PrefixOriginalSupport rename proofPrefix) :
    SourceDecoderSchedule.ProjectionOriginalSupport rename proofPrefix
      (SourceMismatchAdvance.faultyZeroInputAt rename proofPrefix index) := by
  let base := initialState (relabel rename (formula parameters))
  let product := SourceFoldProjection.mapLiteral rename ((SourceMismatchBranch.healthyFlagCursor (parameters := parameters)).lastID + 1, true)
  let flag := SourceFoldProjection.mapLiteral rename ((SourceMismatchBranch.faultyProductCursor (parameters := parameters)).lastID + 1, true)
  let input := SourceFoldProjection.mapLiteral rename
    ((SourceMismatchBranch.faultyProductInputs (parameters := parameters))[index.val]'(by
      simpa [SourceMismatchBranch.faultyProductInputs] using index.isLt))
  let originalLeft : AvailableSubclause base [negate product, input] := by
    have row := ofRow ((SourceMismatchBranch.faultyProductRows (parameters := parameters) rename).row
      ⟨index.val, by change index.val < 4; omega⟩)
    have bound : index.val < (SourceMismatchBranch.faultyProductInputs (parameters := parameters)).length := by
      simpa [SourceMismatchBranch.faultyProductInputs] using index.isLt
    simpa [Bounded.Producer.rows, Gate.clauses, List.getElem_append, bound,
      Rows.mapClause, SourceFoldProjection.mapLiteral, product, input, base, negate, Std.Sat.Literal.negate] using row
  let originalRight : AvailableSubclause base [product, flag] :=
    retarget (ofRow ((SourceMismatchBranch.faultyFlagRows (parameters := parameters) rename).row
      ⟨0, by change 0 < 2; decide⟩)) (by
        intro literal member
        simp [SourceMismatchBranch.faultyProductCursor, Cursor.emitNative, Cursor.emit, Cursor.assign,
          Bounded.Producer.rows, Gate.clauses, Rows.mapClause, SourceFoldProjection.mapLiteral, product, flag,
          List.mem_cons, List.not_mem_nil] at member ⊢ <;> aesop)
  let left := FoldProjection.afterTrace originalLeft proofPrefix.state proofPrefix.steps proofPrefix.checked
  let right := FoldProjection.afterTrace originalRight proofPrefix.state proofPrefix.steps proofPrefix.checked
  have leftAllowed : SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename originalLeft.row.id := by
    dsimp only [originalLeft]
    with_unfolding_all
      repeat' rw [SourceMixedSchedule.subclause_indices_mpr_id rfl (by
        fin_cases index <;> simp [Bounded.Producer.rows, Gate.clauses, Rows.mapClause, SourceFoldProjection.mapLiteral,
          SourceMismatchBranch.faultyProductInputs, product, input, base, negate, Std.Sat.Literal.negate]),
        SourceMixedSchedule.subclause_indices_cast_id rfl (by
        fin_cases index <;> simp [Bounded.Producer.rows, Gate.clauses, Rows.mapClause, SourceFoldProjection.mapLiteral,
          SourceMismatchBranch.faultyProductInputs, product, input, base, negate, Std.Sat.Literal.negate])]
    exact faultyProductRows_allowed rename ⟨index.val, by omega⟩
  have actual := SourceMixedSchedule.longMerge_supported (formula parameters).clauses.size
    (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) proofPrefix.steps proofPrefix.state
    product [input] [flag] left right supported (SourceDecoderSchedule.allowed_native_count_le rename)
    (SourceMixedSchedule.prefix_native_count_le rename proofPrefix) (Or.inl leftAllowed)
    (Or.inl (faultyFlagRows_allowed rename ⟨0, by decide⟩))
  simpa only [SourceMismatchAdvance.faultyZeroInputAt, SourceDecoderSchedule.ProjectionOriginalSupport,
    base, product, flag, input, originalLeft, originalRight, left, right, retarget] using actual

/-- Optional requirements may choose any observed leaf as their discrepancy
witness. Their unsatisfiability therefore excludes every observed discrepancy. -/
theorem optional_native_absence (parameters : Parameters) (raw : parameters.layout = .raw)
    (drive : parameters.drive = true)
    (wrapper : OptionalWrapper Nat (Fin internalCount) (Fin parameters.decoder.roots.length))
    (pairs : ∀ output ∈ wrapper.tree.leaves, wrapper.observedPairs output = nativePair parameters output)
    (unsat : Unsatisfiable (optionalNativeInput parameters wrapper)) :
    Controller.NativeProof.Decoder.NoDiscrepancy parameters wrapper.tree.leaves.toFinset := by
  apply selected_native_absence parameters raw drive wrapper pairs wrapper.tree.leaves
    (by intro output member; exact member)
  intro model
  apply unsat
  rcases model with ⟨values, satisfied⟩
  refine ⟨values, (satisfies_append _ _ _).mpr ⟨?_, ?_⟩⟩
  · exact ((satisfies_append _ _ _).mp satisfied).1
  · exact ((satisfies_append _ _ _).mp
      ((satisfies_append _ _ _).mp satisfied).2).1

/-- Retargeting the physical product input to its native group output preserves
both the actual resolution trace and its retained-clause provenance. -/
theorem groupCofactorAt_supported {parameters : Parameters} (rename : Nat → Fin v)
    (proofPrefix : SourcePrefix (parameters := parameters) rename)
    (group : SourceMismatchSeed.Group)
    (supported : SourceDecoderSchedule.PrefixOriginalSupport rename proofPrefix) :
    SourceDecoderSchedule.ProjectionOriginalSupport rename proofPrefix
      (SourceMismatchAdvance.groupCofactorAt rename proofPrefix group) := by
  have actual := faultyZeroInputAt_supported rename proofPrefix
    (SourceMismatchSeed.groupIndex group) supported
  simpa only [SourceMismatchAdvance.groupCofactorAt,
    SourceDecoderSchedule.ProjectionOriginalSupport, retarget] using actual

/-- A negative input kills its native AND tree using only that input unit and
the tree's retained original rows, including unary identity trees. -/
theorem tree_deny_supported {parameters : Parameters}
    (rename : Nat → Fin v) (proofPrefix : SourcePrefix (parameters := parameters) rename)
    (tree : AndTree proofPrefix.state root inputs) (context : Clause (Fin v))
    (input : Literal (Fin v)) (member : input ∈ inputs)
    (unit : AvailableSubclause proofPrefix.state (context ++ [negate input]))
    (supported : SourceDecoderSchedule.PrefixOriginalSupport rename proofPrefix)
    (original : TreeOriginals (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) tree)
    (unitOrigin : ResultOrigin (formula parameters).clauses.size
      (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
      proofPrefix.steps unit.row.id) :
    SourceDecoderSchedule.ProjectionOriginalSupport rename proofPrefix
      (TreeUnits.deny tree context input member unit) := by
  let projected := projectTreeInputs tree
  let unitNow := afterTrace unit projected.state projected.steps projected.checked
  have actual := projectTreeInputs_supported tree (formula parameters).clauses.size
    (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) original
    (SourceDecoderSchedule.allowed_native_count_le rename)
    (SourceMixedSchedule.prefix_native_count_le rename proofPrefix)
  have complete := traceOriginalSupport_append _ _ proofPrefix.steps projected.steps supported actual.1
  have carried := resultOrigin_append_right _ _ proofPrefix.steps projected.steps unit.row.id unitOrigin
  have directionOrigin := actual.2 input member
  unfold TreeUnits.deny
  dsimp only
  split
  · rename_i same direction
    unfold SourceDecoderSchedule.ProjectionOriginalSupport
    constructor
    · exact complete
    · subst input
      with_unfolding_all
        simpa only [SourceMixedSchedule.subclause_indices_mpr_id
          (show projected.state = projected.state from rfl)
          (show context ++ [negate root] = context ++ [negate root] from rfl),
          unitNow, afterTrace] using carried
  · rename_i row direction
    let left : AvailableSubclause projected.state (negate input :: context) :=
      retarget unitNow (by
        intro literal present
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at present ⊢
        aesop)
    let right : AvailableSubclause projected.state (input :: [negate root]) :=
      retarget row (by
        intro literal present
        simp only [List.mem_cons, List.not_mem_nil, or_false] at present ⊢
        aesop)
    have rowOrigin : ResultOrigin (formula parameters).clauses.size
        (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
        (proofPrefix.steps ++ projected.steps) row.row.id := by
      apply resultOrigin_append_left
      simpa only [direction, CertificateOrigin] using directionOrigin
    have joined := SourceMixedSchedule.longMerge_supported (formula parameters).clauses.size
      (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
      (proofPrefix.steps ++ projected.steps) projected.state input context [negate root] left right
      complete (SourceDecoderSchedule.allowed_native_count_le rename)
      (Nat.le_trans (SourceMixedSchedule.prefix_native_count_le rename proofPrefix)
        (runSteps_lastId_le projected.checked)) carried rowOrigin
    simpa only [SourceDecoderSchedule.ProjectionOriginalSupport, projected, unitNow,
      left, right, List.append_assoc] using joined

open Controller.NativeProof.SourceMismatchSeed Controller.NativeProof.SourceMismatchAdvance
open Controller.NativeProof.SourceFoldProjection

theorem otherAbsenceAt_supported {parameters : Parameters} (rename : Nat → Fin v)
    (proofPrefix : SourcePrefix (parameters := parameters) rename)
    (channel : Fin parameters.channels) (different : channel ≠ parameters.bridge.target)
    (supported : SourceDecoderSchedule.PrefixOriginalSupport rename proofPrefix) :
    SourceDecoderSchedule.ProjectionOriginalSupport rename proofPrefix
      (otherAbsenceAt rename proofPrefix channel different) := by
  let group := otherGroup (parameters := parameters) channel
  let first := groupCofactorAt rename proofPrefix group
  let root := SourceFoldProjection.mapLiteral rename (groupOutput (parameters := parameters) group)
  let flag := SourceFoldProjection.mapLiteral rename ((SourceMismatchBranch.faultyProductCursor (parameters := parameters)).lastID + 1, true)
  let input := SourceFoldProjection.mapLiteral rename ((firstArrays parameters).slots
    (.internal (.absent .healthy parameters.firstBus channel)))
  let originalTree := groupTree rename group (otherGroup_nonempty channel different)
  have combinedPrefix : runSteps (initialState (relabel rename (formula parameters)))
      (proofPrefix.steps ++ first.steps) = some first.state := by
    rw [runSteps_append, proofPrefix.checked]
    exact first.checked
  let tree := originalTree.afterTrace first.state (proofPrefix.steps ++ first.steps) combinedPrefix
  let projected := projectTreeInputs tree
  have inputMember : input ∈ (groupInputs (parameters := parameters) group).map (SourceFoldProjection.mapLiteral rename) :=
    List.mem_map.mpr ⟨_, otherGroup_member channel different, rfl⟩
  let rootClause : AvailableSubclause projected.state [flag, root] :=
    afterTrace first.result projected.state projected.steps projected.checked
  have firstSupport := groupCofactorAt_supported rename proofPrefix group supported
  have originals := treeOriginals_afterTrace
    (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) originalTree
    (groupTree_originals rename group (otherGroup_nonempty channel different))
    first.state (proofPrefix.steps ++ first.steps) combinedPrefix
  have projectionSupport := projectTreeInputs_supported tree (formula parameters).clauses.size
    (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) originals
    (SourceDecoderSchedule.allowed_native_count_le rename)
    (Nat.le_trans (SourceMixedSchedule.prefix_native_count_le rename proofPrefix)
      (runSteps_lastId_le first.checked))
  have complete := traceOriginalSupport_append _ _ (proofPrefix.steps ++ first.steps)
    projected.steps firstSupport.1 projectionSupport.1
  have rootOrigin := resultOrigin_append_right _ _ (proofPrefix.steps ++ first.steps)
    projected.steps first.result.row.id firstSupport.2
  have directionOrigin : CertificateOrigin (formula parameters).clauses.size
      (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
      projected.steps (projected.results input inputMember) := projectionSupport.2 input inputMember
  unfold otherAbsenceAt
  dsimp only [id]
  split
  · rename_i same direction
    unfold SourceDecoderSchedule.ProjectionOriginalSupport
    constructor
    · simpa only [id, projected, tree, originalTree, group, first, List.append_assoc] using complete
    · simpa only [projected, tree, originalTree, group, first, rootClause, afterTrace,
        retarget, id, List.append_assoc] using rootOrigin
  · rename_i implication direction
    let right : AvailableSubclause projected.state [root, flag] := retarget rootClause (by
      intro literal member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢
      exact member.elim (fun equal => Or.inr equal) (fun equal => Or.inl equal))
    have implicationOrigin : ResultOrigin (formula parameters).clauses.size
        (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
        ((proofPrefix.steps ++ first.steps) ++ projected.steps) implication.row.id := by
      apply resultOrigin_append_left
      with_unfolding_all
        rw [direction] at directionOrigin
      exact directionOrigin
    have joined := SourceMixedSchedule.longMerge_supported (formula parameters).clauses.size
      (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
      ((proofPrefix.steps ++ first.steps) ++ projected.steps) projected.state root [input] [flag]
      implication right complete (SourceDecoderSchedule.allowed_native_count_le rename)
      (Nat.le_trans (SourceMixedSchedule.prefix_native_count_le rename proofPrefix)
        (Nat.le_trans (runSteps_lastId_le first.checked) (runSteps_lastId_le projected.checked)))
      implicationOrigin rootOrigin
    simpa only [SourceDecoderSchedule.ProjectionOriginalSupport, projected, tree,
      originalTree, group, first, root, input, flag, right, rootClause, retarget,
      id, List.append_assoc] using joined

end Controller.NativeProof.Wrapper
