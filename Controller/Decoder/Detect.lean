module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Decoder.ZeroSystem
public import Controller.Horn.WorklistCorrect
public import Controller.CNF.Relabel
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

/-! A supplied-structure guarded detector. Healthy-zero observations share
candidate value tables; healthy-one observations use the indexed dual-Horn
worklist. Every successful result is an eligible detecting set, and absence
of a result is complete. Resource bounds belong to operational refinements. -/
namespace Controller.Decoder

private theorem dualHornClause_relabel (rename : α → β) (clause : CNF.Clause α)
    (restricted : Horn.DualHornClause clause) :
    Horn.DualHornClause (Controller.CNF.OrderedFormula.Clause.relabel rename clause) := by
  rcases restricted with tautology | unique
  · obtain ⟨literal, present, opposite⟩ := tautology
    left
    refine ⟨(rename literal.1, literal.2), ?_, ?_⟩
    · exact List.mem_map.mpr ⟨literal, present, rfl⟩
    · exact List.mem_map.mpr ⟨CNF.negate literal, opposite, rfl⟩
  · right
    intro left leftMember right rightMember leftNegative rightNegative
    obtain ⟨oldLeft, oldLeftMember, leftEquation⟩ := List.mem_map.mp leftMember
    obtain ⟨oldRight, oldRightMember, rightEquation⟩ := List.mem_map.mp rightMember
    subst left
    subst right
    exact congrArg rename (unique oldLeft oldLeftMember oldRight oldRightMember
      leftNegative rightNegative)

private theorem dualHorn_relabel (rename : α → β) (formula : CNF.Formula α)
    (restricted : Horn.DualHorn formula) : Horn.DualHorn (CNF.relabel rename formula) := by
  intro clause present
  obtain ⟨old, membership, equation⟩ := Array.mem_map.mp present
  subst clause
  exact dualHornClause_relabel rename old (restricted old membership)

def trueCandidate (b : Nat) (target head : Channel n) : Finset (Channel n) :=
  if b = 1 then {head, target} else {head}

theorem trueCandidate_admissible (b : Nat) (target head : Channel n) :
    Admissible b target (trueCandidate b target head) := by
  by_cases one : b = 1
  · subst b
    simp [trueCandidate, Admissible]
  · simp [trueCandidate, one, Admissible]

theorem head_mem_trueCandidate (b : Nat) (target head : Channel n) :
    head ∈ trueCandidate b target head := by
  by_cases one : b = 1 <;> simp [trueCandidate, one]

theorem trueCandidate_subset {b : Nat} {target head : Channel n}
    {K : Finset (Channel n)} (admissible : Admissible b target K) (present : head ∈ K) :
    trueCandidate b target head ⊆ K := by
  by_cases one : b = 1
  · rw [trueCandidate, ite_eq_left one]
    exact Finset.insert_subset_iff.mpr
      ⟨present, Finset.singleton_subset_iff.mpr (admissible.2 one)⟩
  · simpa [trueCandidate, one] using present

namespace DAG

/-- Computable disjoint allocation: channel indices first, node activities next. -/
def zeroIndex (graph : DAG n) : graph.ZeroVar ≃ Fin (n + graph.nodeCount) :=
  finSumFinEquiv

def finiteZeroSystem (graph : DAG n) (b : Nat) (target : Channel n)
    (root : Fin graph.nodeCount) (T F : Finset (Channel n)) :
    CNF.FiniteFormula (n + graph.nodeCount) :=
  CNF.relabel graph.zeroIndex (graph.zeroSystem b target root T F)

theorem finiteZeroSystem_dualHorn (graph : DAG n) (guarded : graph.Guarded)
    (b : Nat) (target : Channel n) (root : Fin graph.nodeCount) (T F : Finset (Channel n)) :
    Horn.DualHorn (graph.finiteZeroSystem b target root T F) :=
  dualHorn_relabel graph.zeroIndex _ (graph.zeroSystem_dualHorn guarded b target root T F)

/-- Run the finite-vector worklist and project its channel coordinates. -/
def solveZero (graph : DAG n) (b : Nat) (target : Channel n)
    (root : Fin graph.nodeCount) (T F : Finset (Channel n)) :
    Option (Finset (Channel n)) :=
  (Horn.Worklist.solveFormula (graph.finiteZeroSystem b target root T F)).map
    (fun values => graph.zeroChannelSet (fun coordinate => values[(graph.zeroIndex coordinate).val]))

theorem solveZero_none_iff (graph : DAG n) (guarded : graph.Guarded)
    (b : Nat) (target : Channel n) (root : Fin graph.nodeCount) (T F : Finset (Channel n)) :
    graph.solveZero b target root T F = none ↔
      ¬ ∃ K, Admissible b target K ∧ ExtendsFixed T F K ∧
        graph.eval (assignmentOfSet K) root = false := by
  rw [solveZero, Option.map_eq_none_iff,
    Horn.Worklist.solveFormula_none_iff _ (graph.finiteZeroSystem_dualHorn guarded b target root T F)]
  rw [finiteZeroSystem, CNF.unsatisfiable_relabel_iff graph.zeroIndex.injective]
  exact not_congr (graph.zeroSystem_satisfiable_iff guarded b target root T F)

theorem solveZero_some (graph : DAG n) (guarded : graph.Guarded)
    (b : Nat) (target : Channel n) (root : Fin graph.nodeCount) (T F : Finset (Channel n))
    (K : Finset (Channel n)) (result : graph.solveZero b target root T F = some K) :
    Admissible b target K ∧ ExtendsFixed T F K ∧
      graph.eval (assignmentOfSet K) root = false := by
  unfold solveZero at result
  obtain ⟨values, returned, rfl⟩ := Option.map_eq_some_iff.mp result
  have model := (Horn.Worklist.solveFormula_some_model _
    (graph.finiteZeroSystem_dualHorn guarded b target root T F) values returned).1
  have rawModel := (CNF.satisfies_relabel graph.zeroIndex _
    (graph.zeroSystem b target root T F)).mp model
  apply (graph.zeroSystem_projection guarded b target root T F _).mp
  refine ⟨fun index => values[(graph.zeroIndex (.inr index)).val], ?_⟩
  simpa only [graph.zeroAssignment_channelSet, Function.comp_def] using rawModel

/-- A true admissible value has a true member of the explicitly scanned family. -/
theorem admissible_true_iff_candidate (graph : DAG n) (guarded : graph.Guarded)
    (b : Nat) (target : Channel n) (root : Fin graph.nodeCount) :
    (∃ K, Admissible b target K ∧ graph.eval (assignmentOfSet K) root = true) ↔
      ∃ head, graph.eval (assignmentOfSet (trueCandidate b target head)) root = true := by
  constructor
  · rintro ⟨K, admissible, value⟩
    obtain ⟨head, present, _, preserves⟩ :=
      graph.exists_head_preserving_subsets guarded K root value
    exact ⟨head, preserves _ (head_mem_trueCandidate b target head)
      (trueCandidate_subset admissible present)⟩
  · rintro ⟨head, value⟩
    exact ⟨trueCandidate b target head, trueCandidate_admissible b target head, value⟩

/-- Executable enumeration of all declared channel heads, including unused ones. -/
def scanTrue (graph : DAG n) (b : Nat) (target : Channel n)
    (root : Fin graph.nodeCount) : Option (Finset (Channel n)) :=
  ((List.finRange n).find? fun head =>
    graph.eval (assignmentOfSet (trueCandidate b target head)) root).map
      (trueCandidate b target)

theorem scanTrue_some (graph : DAG n) (b : Nat) (target : Channel n)
    (root : Fin graph.nodeCount) (K : Finset (Channel n))
    (result : graph.scanTrue b target root = some K) :
    Admissible b target K ∧ graph.eval (assignmentOfSet K) root = true := by
  unfold scanTrue at result
  obtain ⟨head, found, rfl⟩ := Option.map_eq_some_iff.mp result
  have value := List.find?_some found
  exact ⟨trueCandidate_admissible b target head, value⟩

theorem scanTrue_none_iff (graph : DAG n) (guarded : graph.Guarded) (b : Nat)
    (target : Channel n) (root : Fin graph.nodeCount) :
    graph.scanTrue b target root = none ↔
      ¬ ∃ K, Admissible b target K ∧ graph.eval (assignmentOfSet K) root = true := by
  rw [graph.admissible_true_iff_candidate guarded b target root]
  simp [scanTrue, Option.map_eq_none_iff, List.find?_eq_none]

/-- The two exact semantic branches of a single observed output. Activity
models remain existential witnesses; this does not assert a worklist runtime. -/
theorem discrepancy_iff_branches (graph : DAG n) (guarded : graph.Guarded)
    (b : Nat) (target : Channel n) (root : Fin graph.nodeCount) :
    (∃ K, Admissible b target K ∧ graph.eval (assignmentOfSet K) root ≠
      graph.eval (assignmentOfSet {target}) root) ↔
    (if graph.eval (assignmentOfSet {target}) root then
      CNF.Satisfiable (graph.zeroSystem b target root ∅ ∅)
    else ∃ head, graph.eval (assignmentOfSet (trueCandidate b target head)) root = true) := by
  cases healthy : graph.eval (assignmentOfSet {target}) root with
  | false =>
      simpa [healthy] using graph.admissible_true_iff_candidate guarded b target root
  | true =>
      have projected := graph.zeroSystem_satisfiable_iff guarded b target root ∅ ∅
      simpa [healthy, ExtendsFixed] using projected.symm

/-- Ordered short-circuit search, retaining the first successful witness. -/
def firstSuccess (query : α → Option β) : List α → Option β
  | [] => none
  | head :: tail => match query head with
    | some value => some value
    | none => firstSuccess query tail

theorem firstSuccess_none_iff (query : α → Option β) (items : List α) :
    firstSuccess query items = none ↔ ∀ item ∈ items, query item = none := by
  induction items with
  | nil => simp [firstSuccess]
  | cons head tail ih =>
    cases result : query head <;> simp [firstSuccess, result, ih]

theorem firstSuccess_some (query : α → Option β) (items : List α) (value : β)
    (returned : firstSuccess query items = some value) :
    ∃ item ∈ items, query item = some value := by
  induction items with
  | nil => simp [firstSuccess] at returned
  | cons head tail ih =>
    cases result : query head with
    | none =>
      obtain ⟨item, member, found⟩ := ih (by simpa [firstSuccess, result] using returned)
      exact ⟨item, List.mem_cons_of_mem head member, found⟩
    | some found =>
      have equal : found = value := by simpa [firstSuccess, result] using returned
      subst found
      exact ⟨head, List.mem_cons_self, result⟩

/-- Each head is evaluated once over the full shared DAG. All healthy-zero
observations use that one table; roots are not given separate head scans. -/
def trueQuery (graph : DAG n) (b : Nat) (target : Channel n)
    (healthy : Fin graph.nodeCount → Bool) (head : Channel n) :
    Option (Finset (Channel n)) :=
  let candidate := trueCandidate b target head
  let values := graph.evalTable (assignmentOfSet candidate)
  if graph.roots.any (fun root => !healthy root && values root) then some candidate else none

/-- Healthy-one observations ask the finite indexed worklist for a zero. -/
def zeroQuery (graph : DAG n) (b : Nat) (target : Channel n)
    (healthy : Fin graph.nodeCount → Bool) (root : Fin graph.nodeCount) :
    Option (Finset (Channel n)) :=
  if healthy root then graph.solveZero b target root ∅ ∅ else none

theorem trueQuery_none_iff (graph : DAG n) (b : Nat) (target head : Channel n)
    (healthy : Fin graph.nodeCount → Bool) :
    graph.trueQuery b target healthy head = none ↔
      ¬ ∃ root ∈ graph.roots, healthy root = false ∧
        graph.eval (assignmentOfSet (trueCandidate b target head)) root = true := by
  simp [trueQuery, evalTable_eq_eval, List.any_eq_true]

theorem trueQuery_some (graph : DAG n) (b : Nat) (target head : Channel n)
    (healthy : Fin graph.nodeCount → Bool) (K : Finset (Channel n))
    (returned : graph.trueQuery b target healthy head = some K) :
    K = trueCandidate b target head ∧
      ∃ root ∈ graph.roots, healthy root = false ∧ graph.eval (assignmentOfSet K) root = true := by
  unfold trueQuery at returned
  dsimp only at returned
  split at returned
  next yes =>
    have equal : trueCandidate b target head = K := Option.some.inj returned
    subst K
    refine ⟨rfl, ?_⟩
    simpa [evalTable_eq_eval, List.any_eq_true] using yes
  next no => simp at returned

theorem zeroQuery_none_iff (graph : DAG n) (guarded : graph.Guarded) (b : Nat)
    (target : Channel n) (healthy : Fin graph.nodeCount → Bool) (root : Fin graph.nodeCount) :
    graph.zeroQuery b target healthy root = none ↔
      ¬ (healthy root = true ∧ ∃ K, Admissible b target K ∧
        graph.eval (assignmentOfSet K) root = false) := by
  cases value : healthy root <;>
    simp [zeroQuery, value, graph.solveZero_none_iff guarded, ExtendsFixed]

/-- Avoid enumerating heads when no healthy-zero observation exists. -/
def scanCandidates (graph : DAG n) (b : Nat) (target : Channel n)
    (healthy : Fin graph.nodeCount → Bool) : Option (Finset (Channel n)) :=
  if graph.roots.all healthy then none
  else firstSuccess (graph.trueQuery b target healthy) (List.finRange n)

theorem scanCandidates_eq_firstSuccess (graph : DAG n) (b : Nat) (target : Channel n)
    (healthy : Fin graph.nodeCount → Bool) :
    graph.scanCandidates b target healthy =
      firstSuccess (graph.trueQuery b target healthy) (List.finRange n) := by
  unfold scanCandidates
  split
  next all =>
    symm
    apply (firstSuccess_none_iff _ _).mpr
    intro head _
    apply (graph.trueQuery_none_iff b target head healthy).mpr
    rintro ⟨root, member, falseValue, _⟩
    have trueValue := List.all_eq_true.mp all root member
    exact Bool.false_ne_true (falseValue.symm.trans trueValue)
  next notAll => rfl

/-- Compute the healthy graph once, scan candidate tables, then solve zero
queries. The drive flag supplies the physical undetectability early exit. -/
def detectSet (graph : DAG n) (b : Nat) (target : Channel n) (drive : Bool) :
    Option (Finset (Channel n)) :=
  if drive then
    let healthy := graph.evalTable (assignmentOfSet {target})
    match graph.scanCandidates b target healthy with
    | some K => some K
    | none => firstSuccess (graph.zeroQuery b target healthy) graph.roots
  else none

@[simp] theorem detectSet_drive_false (graph : DAG n) (b : Nat) (target : Channel n) :
    graph.detectSet b target false = none := by simp [detectSet]

@[simp] theorem detectSet_no_roots (graph : DAG n) (b : Nat) (target : Channel n)
    (drive : Bool) (empty : graph.roots = []) : graph.detectSet b target drive = none := by
  have scan : firstSuccess
      (graph.trueQuery b target (graph.evalTable (assignmentOfSet {target}))) (List.finRange n) = none := by
    apply (firstSuccess_none_iff _ _).mpr
    intro head _
    simp [trueQuery, empty]
  cases drive <;> simp [detectSet, scanCandidates_eq_firstSuccess, scan, empty, firstSuccess]

/-- Exact absence criterion for the assembled executable. -/
theorem detectSet_none_iff (graph : DAG n) (guarded : graph.Guarded) (b : Nat)
    (target : Channel n) (drive : Bool) :
    graph.detectSet b target drive = none ↔
      ¬ (drive = true ∧ ∃ root ∈ graph.roots, ∃ K, Admissible b target K ∧
        graph.eval (assignmentOfSet K) root ≠ graph.eval (assignmentOfSet {target}) root) := by
  cases drive with
  | false => simp [detectSet]
  | true =>
    simp only [detectSet, ite_true, scanCandidates_eq_firstSuccess, evalTable_eq_eval, true_and]
    cases scan : firstSuccess
        (graph.trueQuery b target (graph.eval (assignmentOfSet {target}))) (List.finRange n) with
    | some K =>
      simp only [Option.some_ne_none, false_iff, not_not]
      obtain ⟨head, _, found⟩ := firstSuccess_some _ _ K scan
      obtain ⟨rfl, root, present, healthy, faulty⟩ := graph.trueQuery_some b target head _ K found
      exact ⟨root, present, trueCandidate b target head, trueCandidate_admissible b target head,
        by rw [healthy, faulty]; decide⟩
    | none =>
      rw [firstSuccess_none_iff]
      have absent := (firstSuccess_none_iff _ _).mp scan
      constructor
      · intro zeros
        rintro ⟨root, present, K, eligible, differs⟩
        cases healthy : graph.eval (assignmentOfSet {target}) root with
        | false =>
          have faulty : graph.eval (assignmentOfSet K) root = true := by
            cases value : graph.eval (assignmentOfSet K) root <;> simp_all
          obtain ⟨head, found⟩ :=
            (graph.admissible_true_iff_candidate guarded b target root).mp ⟨K, eligible, faulty⟩
          have no := (graph.trueQuery_none_iff b target head _).mp
            (absent head (List.mem_finRange head))
          exact no ⟨root, present, healthy, found⟩
        | true =>
          have faulty : graph.eval (assignmentOfSet K) root = false := by
            cases value : graph.eval (assignmentOfSet K) root <;> simp_all
          exact (graph.zeroQuery_none_iff guarded b target _ root).mp (zeros root present)
            ⟨healthy, K, eligible, faulty⟩
      · intro no root present
        apply (graph.zeroQuery_none_iff guarded b target _ root).mpr
        rintro ⟨healthy, K, eligible, faulty⟩
        exact no ⟨root, present, K, eligible, by rw [healthy, faulty]; decide⟩

/-- Every returned set is physically eligible and changes an observed root. -/
theorem detectSet_some (graph : DAG n) (guarded : graph.Guarded) (b : Nat)
    (target : Channel n) (drive : Bool) (K : Finset (Channel n))
    (returned : graph.detectSet b target drive = some K) :
    drive = true ∧ Admissible b target K ∧ ∃ root ∈ graph.roots,
      graph.eval (assignmentOfSet K) root ≠ graph.eval (assignmentOfSet {target}) root := by
  cases drive with
  | false => simp [detectSet] at returned
  | true =>
    simp only [detectSet, ite_true, scanCandidates_eq_firstSuccess, evalTable_eq_eval] at returned
    cases scan : firstSuccess
        (graph.trueQuery b target (graph.eval (assignmentOfSet {target}))) (List.finRange n) with
    | some found =>
      rw [scan] at returned
      have equal := Option.some.inj returned
      subst found
      obtain ⟨head, _, value⟩ := firstSuccess_some _ _ K scan
      obtain ⟨rfl, root, present, healthy, faulty⟩ := graph.trueQuery_some b target head _ K value
      exact ⟨rfl, trueCandidate_admissible b target head, root, present,
        by rw [healthy, faulty]; decide⟩
    | none =>
      rw [scan] at returned
      obtain ⟨root, present, value⟩ := firstSuccess_some _ _ K returned
      unfold zeroQuery at value
      split at value
      next healthy =>
        obtain ⟨eligible, _, faulty⟩ := graph.solveZero_some guarded b target root ∅ ∅ K value
        exact ⟨rfl, eligible, root, present, by rw [healthy, faulty]; decide⟩
      next impossible => simp at value

end DAG
end Controller.Decoder
