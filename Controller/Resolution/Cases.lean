module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Resolution.RUP

@[expose] public section

/-! Binary local cases combine derived subclauses by exact ordinary resolution.
If one child no longer contains its branch literal, reuse that stronger row.
No weakening or requested-target row is introduced. -/
namespace Controller.Resolution.Cases
open Controller.CNF Controller.Resolution.RUP

theorem subset_drop_last (current target : Clause (Fin v)) (extra : Literal (Fin v))
    (subset : ClauseSubset current (target ++ [extra])) (absent : extra ∉ current) :
    ClauseSubset current target := by
  intro literal member
  rcases List.mem_append.mp (subset literal member) with old | last
  · exact old
  · have same : literal = extra := by simpa using last
    exact False.elim (absent (same ▸ member))

/-- Resolving the two branch literals retains only target literals. -/
theorem resolvent_subset (pivot : Literal (Fin v)) (left right target : Clause (Fin v))
    (leftSubset : ClauseSubset left (target ++ [negate pivot]))
    (rightSubset : ClauseSubset right (target ++ [pivot])) :
    ClauseSubset (resolvent pivot left right) target := by
  intro literal member
  rcases (mem_resolvent pivot literal left right).mp member with first | second
  · rcases List.mem_append.mp (leftSubset literal first.1) with old | last
    · exact old
    · exact False.elim (first.2 (by simpa using last))
  · rcases List.mem_append.mp (rightSubset literal second.1) with old | last
    · exact old
    · exact False.elim (second.2 (by simpa using last))

/-- Both case results already reside in the current checked prefix. -/
def merge (state : State v) (leftId rightId : Nat) (pivot : Literal (Fin v))
    (left right : Clause (Fin v)) : CompiledTrail v :=
  if negate pivot ∉ left then ⟨state, leftId, left, []⟩
  else if pivot ∉ right then ⟨state, rightId, right, []⟩
  else
    let output := resolvent pivot left right
    ⟨insertRow state (state.lastId + 1) output, state.lastId + 1, output,
      [resolutionStep state leftId rightId pivot left right]⟩

theorem merge_subset (state : State v) (leftId rightId : Nat)
    (pivot : Literal (Fin v)) (left right target : Clause (Fin v))
    (leftSubset : ClauseSubset left (target ++ [negate pivot]))
    (rightSubset : ClauseSubset right (target ++ [pivot])) :
    ClauseSubset (merge state leftId rightId pivot left right).clause target := by
  by_cases leftAbsent : negate pivot ∉ left
  · simpa [merge, leftAbsent] using subset_drop_last left target (negate pivot) leftSubset leftAbsent
  · by_cases rightAbsent : pivot ∉ right
    · simpa [merge, leftAbsent, rightAbsent] using subset_drop_last right target pivot rightSubset rightAbsent
    · simpa [merge, leftAbsent, rightAbsent] using resolvent_subset pivot left right target leftSubset rightSubset

theorem merge_count_le_one (state : State v) (leftId rightId : Nat)
    (pivot : Literal (Fin v)) (left right : Clause (Fin v)) :
    (merge state leftId rightId pivot left right).steps.length ≤ 1 := by
  unfold merge
  split
  · simp
  · split <;> simp

/-- The actual merger either uses an existing row or emits one checked exact
resolution step with a fresh ID, preserving the ordinary trace language. -/
theorem merge_run (state : State v) (leftId rightId : Nat)
    (pivot : Literal (Fin v)) (left right : Clause (Fin v))
    (leftRow : state.rows leftId = some left) (rightRow : state.rows rightId = some right)
    (leftBound : leftId ≤ state.lastId) (rightBound : rightId ≤ state.lastId) :
    runSteps state (merge state leftId rightId pivot left right).steps =
      some (merge state leftId rightId pivot left right).state ∧
    (merge state leftId rightId pivot left right).state.rows
      (merge state leftId rightId pivot left right).rowId =
        some (merge state leftId rightId pivot left right).clause ∧
    (merge state leftId rightId pivot left right).rowId ≤
      (merge state leftId rightId pivot left right).state.lastId := by
  by_cases leftAbsent : negate pivot ∉ left
  · simpa [merge, leftAbsent, runSteps] using (show True ∧ state.rows leftId = some left ∧
        leftId ≤ state.lastId from ⟨True.intro, leftRow, leftBound⟩)
  · by_cases rightAbsent : pivot ∉ right
    · simpa [merge, leftAbsent, rightAbsent, runSteps] using
        (show True ∧ state.rows rightId = some right ∧ rightId ≤ state.lastId from
          ⟨True.intro, rightRow, rightBound⟩)
    · have leftPresent : negate pivot ∈ left := by simpa using leftAbsent
      have rightPresent : pivot ∈ right := by simpa using rightAbsent
      refine ⟨?_, ?_, ?_⟩
      · simpa [merge, leftAbsent, rightAbsent] using resolutionStep_run state leftId rightId pivot
          left right leftRow rightRow leftBound rightBound leftPresent rightPresent
      · simp [merge, leftAbsent, rightAbsent, insertRow]
      · simp [merge, leftAbsent, rightAbsent, insertRow]

/-- A merger continues an actual checked prefix, with no target axiom. -/
def merge_derived (formula : FiniteFormula v) (state : State v)
    (prefixSteps : List (Step v))
    (prefixRun : runSteps (initialState formula) prefixSteps = some state)
    (leftId rightId : Nat) (pivot : Literal (Fin v)) (left right target : Clause (Fin v))
    (leftRow : state.rows leftId = some left) (rightRow : state.rows rightId = some right)
    (leftBound : leftId ≤ state.lastId) (rightBound : rightId ≤ state.lastId)
    (leftSubset : ClauseSubset left (target ++ [negate pivot]))
    (rightSubset : ClauseSubset right (target ++ [pivot])) :
    DerivedSubclause formula (merge state leftId rightId pivot left right).state target where
  rowId := (merge state leftId rightId pivot left right).rowId
  clause := (merge state leftId rightId pivot left right).clause
  present := (merge_run state leftId rightId pivot left right leftRow rightRow leftBound rightBound).2.1
  subset := merge_subset state leftId rightId pivot left right target leftSubset rightSubset
  checkedPrefix := by
    refine ⟨prefixSteps ++ (merge state leftId rightId pivot left right).steps, ?_⟩
    rw [runSteps_append, prefixRun]
    exact (merge_run state leftId rightId pivot left right leftRow rightRow leftBound rightBound).1

/-- Leaf data names actual rows and reasons; validity is a separate contract. -/
structure LeafCertificate (v : Nat) where
  rowId : Nat
  clause : Clause (Fin v)
  reasons : List (RowReason v)

inductive CaseTree (v : Nat) where
  | leaf (certificate : LeafCertificate v)
  | fork (pivot : Literal (Fin v)) (left right : CaseTree v)

/-- Every leaf must independently provide a valid conflict trail under its branch
assumptions. A failed or unverified branch is not a certificate. -/
def ValidTree (base : State v) (target : Clause (Fin v)) : CaseTree v → Prop
  | .leaf certificate =>
      base.rows certificate.rowId = some certificate.clause ∧
      certificate.rowId ≤ base.lastId ∧ KnownReasons base certificate.reasons ∧
      ValidReasons target (certificate.reasons.map RowReason.entry) ∧
      ClauseSubset certificate.clause (negations (certificate.reasons.map RowReason.entry) ++ target)
  | .fork pivot left right =>
      ValidTree base (target ++ [negate pivot]) left ∧
      ValidTree base (target ++ [pivot]) right

/-- Sequential producer: both child traces are retained before their merger. -/
def compileTree (state : State v) : CaseTree v → CompiledTrail v
  | .leaf certificate => compileReasons state certificate.rowId certificate.clause certificate.reasons
  | .fork pivot left right =>
      let first := compileTree state left
      let second := compileTree first.state right
      let joined := merge second.state first.rowId second.rowId pivot first.clause second.clause
      { joined with steps := first.steps ++ second.steps ++ joined.steps }

/-- Counts only reason resolutions and successful binary merges, not explored
or failed search attempts. -/
def inferenceBudget : CaseTree v → Nat
  | .leaf certificate => certificate.reasons.length
  | .fork _ left right => inferenceBudget left + inferenceBudget right + 1

theorem compileTree_count_le (tree : CaseTree v) (state : State v) :
    (compileTree state tree).steps.length ≤ inferenceBudget tree := by
  induction tree generalizing state with
  | leaf certificate => exact compileReasons_count_le state certificate.rowId certificate.clause certificate.reasons
  | fork pivot left right leftIH rightIH =>
      have first := leftIH state
      have second := rightIH (compileTree state left).state
      have joined := merge_count_le_one (compileTree (compileTree state left).state right).state
        (compileTree state left).rowId (compileTree (compileTree state left).state right).rowId
        pivot (compileTree state left).clause (compileTree (compileTree state left).state right).clause
      simp only [compileTree, List.length_append, inferenceBudget]
      omega

/-- An accepted prefix preserves every base row needed by later leaves. -/
theorem compileTree_run (tree : CaseTree v) (base state : State v)
    (baseBound : base.lastId ≤ state.lastId)
    (baseRows : ∀ id, id ≤ base.lastId → state.rows id = base.rows id)
    (target : Clause (Fin v)) (valid : ValidTree base target tree) :
    runSteps state (compileTree state tree).steps = some (compileTree state tree).state ∧
    (compileTree state tree).state.rows (compileTree state tree).rowId =
      some (compileTree state tree).clause ∧
    (compileTree state tree).rowId ≤ (compileTree state tree).state.lastId ∧
    ClauseSubset (compileTree state tree).clause target := by
  induction tree generalizing state target with
  | leaf certificate =>
      rcases valid with ⟨row, bound, known, reasonsValid, conflict⟩
      have actualRow := (baseRows certificate.rowId bound).trans row
      have actualKnown : KnownReasons state certificate.reasons := by
        intro reason member
        have old := known reason member
        exact ⟨(baseRows reason.rowId old.2.1).trans old.1,
          Nat.le_trans old.2.1 baseBound, old.2.2⟩
      have checked := compileReasons_run certificate.reasons state certificate.rowId
        certificate.clause actualKnown actualRow (Nat.le_trans bound baseBound)
      refine ⟨checked.1, checked.2.1, checked.2.2, ?_⟩
      change ClauseSubset (compileReasons state certificate.rowId certificate.clause certificate.reasons).clause target
      rw [compileReasons_clause]
      exact reverseTrail_subset target _ reasonsValid certificate.clause conflict
  | fork pivot left right leftIH rightIH =>
      have first := leftIH state baseBound baseRows (target ++ [negate pivot]) valid.1
      have firstBound := runSteps_lastId_le first.1
      have firstBaseRows : ∀ id, id ≤ base.lastId →
          (compileTree state left).state.rows id = base.rows id := by
        intro id bound
        exact (runSteps_preserves_old_rows first.1 id (Nat.le_trans bound baseBound)).trans
          (baseRows id bound)
      have second := rightIH (compileTree state left).state
        (Nat.le_trans baseBound firstBound) firstBaseRows (target ++ [pivot]) valid.2
      have leftStill := (runSteps_preserves_old_rows second.1 (compileTree state left).rowId first.2.2.1).trans first.2.1
      have leftBound := Nat.le_trans first.2.2.1 (runSteps_lastId_le second.1)
      have joined := merge_run (compileTree (compileTree state left).state right).state
        (compileTree state left).rowId (compileTree (compileTree state left).state right).rowId
        pivot (compileTree state left).clause (compileTree (compileTree state left).state right).clause
        leftStill second.2.1 leftBound second.2.2.1
      refine ⟨?_, joined.2.1, joined.2.2, ?_⟩
      · simp only [compileTree, runSteps_append, first.1, second.1, Option.bind_some]
        exact joined.1
      · exact merge_subset _ _ _ _ _ _ target first.2.2.2 second.2.2.2

/-- The whole tree produces a checked stronger row after the original prefix. -/
def compileTree_derived (formula : FiniteFormula v) (base : State v)
    (prefixSteps : List (Step v))
    (prefixRun : runSteps (initialState formula) prefixSteps = some base)
    (target : Clause (Fin v)) (tree : CaseTree v) (valid : ValidTree base target tree) :
    DerivedSubclause formula (compileTree base tree).state target where
  rowId := (compileTree base tree).rowId
  clause := (compileTree base tree).clause
  present := (compileTree_run tree base base (Nat.le_refl _) (fun _ _ => rfl) target valid).2.1
  subset := (compileTree_run tree base base (Nat.le_refl _) (fun _ _ => rfl) target valid).2.2.2
  checkedPrefix := by
    refine ⟨prefixSteps ++ (compileTree base tree).steps, ?_⟩
    rw [runSteps_append, prefixRun]
    exact (compileTree_run tree base base (Nat.le_refl _) (fun _ _ => rfl) target valid).1

def leafCount : CaseTree v → Nat
  | .leaf _ => 1
  | .fork _ left right => leafCount left + leafCount right

def mergeCount : CaseTree v → Nat
  | .leaf _ => 0
  | .fork _ left right => mergeCount left + mergeCount right + 1

def DepthBound : Nat → CaseTree v → Prop
  | 0, .leaf _ => True
  | 0, .fork _ _ _ => False
  | _ + 1, .leaf _ => True
  | r + 1, .fork _ left right => DepthBound r left ∧ DepthBound r right

theorem leaf_merge_identity (tree : CaseTree v) : mergeCount tree + 1 = leafCount tree := by
  induction tree with
  | leaf _ => rfl
  | fork _ left right ihLeft ihRight => simp only [mergeCount, leafCount]; omega

theorem depth_leaf_bound (r : Nat) (tree : CaseTree v) (bound : DepthBound r tree) :
    leafCount tree ≤ 2 ^ r := by
  induction r generalizing tree with
  | zero => cases tree with
    | leaf _ => simp [leafCount]
    | fork _ _ _ => exact False.elim bound
  | succ r ih => cases tree with
    | leaf _ => simp only [leafCount]; exact Nat.one_le_two_pow
    | fork _ left right =>
      have first := ih left bound.1
      have second := ih right bound.2
      simp only [leafCount, Nat.pow_succ]
      omega

def ReasonsBound (limit : Nat) : CaseTree v → Prop
  | .leaf certificate => certificate.reasons.length ≤ limit
  | .fork _ left right => ReasonsBound limit left ∧ ReasonsBound limit right

theorem budget_by_leaves (tree : CaseTree v) (limit : Nat) (bound : ReasonsBound limit tree) :
    inferenceBudget tree ≤ leafCount tree * limit + mergeCount tree := by
  induction tree with
  | leaf certificate => simpa [inferenceBudget, leafCount, mergeCount, ReasonsBound] using bound
  | fork pivot left right ihLeft ihRight =>
      have first := ihLeft bound.1
      have second := ihRight bound.2
      simp only [inferenceBudget, leafCount, mergeCount, Nat.add_mul]
      omega

/-- Depth five gives at most 32 successful leaves and 31 mergers. These counts
are distinct from the 63 nodes of a fully explored search tree. -/
theorem depth_five_counts (tree : CaseTree v) (bound : DepthBound 5 tree) :
    leafCount tree ≤ 32 ∧ mergeCount tree ≤ 31 ∧ leafCount tree + mergeCount tree ≤ 63 := by
  have leaves := depth_leaf_bound 5 tree bound
  have identity := leaf_merge_identity tree
  change leafCount tree ≤ 32 at leaves
  omega

theorem depth_counts (r : Nat) (tree : CaseTree v) (bound : DepthBound r tree) :
    leafCount tree ≤ 2 ^ r ∧ mergeCount tree + 1 ≤ 2 ^ r ∧
    leafCount tree + mergeCount tree + 1 ≤ 2 ^ (r + 1) := by
  have leaves := depth_leaf_bound r tree bound
  have identity := leaf_merge_identity tree
  rw [Nat.pow_succ]
  omega

def compileTreeMacro (state : State v) (target : Clause (Fin v)) (tree : CaseTree v) :
    Option (CompiledTrail v) :=
  if tautologyCheck target = true then none else some (compileTree state tree)

@[simp] theorem compileTreeMacro_skip (state : State v) (target : Clause (Fin v))
    (tree : CaseTree v) (tautological : ∃ literal ∈ target, negate literal ∈ target) :
    compileTreeMacro state target tree = none := by
  simp [compileTreeMacro, (tautologyCheck_iff target).mpr tautological]

theorem compileTreeMacro_nonTautological (state : State v) (target : Clause (Fin v))
    (tree : CaseTree v) (nonTautological : ¬ ∃ literal ∈ target, negate literal ∈ target) :
    compileTreeMacro state target tree = some (compileTree state tree) := by
  have check : tautologyCheck target ≠ true := by
    intro accepted
    exact nonTautological ((tautologyCheck_iff target).mp accepted)
  simp [compileTreeMacro, check]

/-- Uniform leaf-trail limit gives the symbolic depth-r emitted-proof bound. -/
theorem compileTree_depth_budget (r limit : Nat) (tree : CaseTree v) (state : State v)
    (depth : DepthBound r tree) (reasons : ReasonsBound limit tree) :
    (compileTree state tree).steps.length ≤ 2 ^ r * limit + (2 ^ r - 1) := by
  have emitted := compileTree_count_le tree state
  have budget := budget_by_leaves tree limit reasons
  have leaves := depth_leaf_bound r tree depth
  have product := Nat.mul_le_mul_right limit leaves
  have identity := leaf_merge_identity tree
  omega

end Controller.Resolution.Cases
