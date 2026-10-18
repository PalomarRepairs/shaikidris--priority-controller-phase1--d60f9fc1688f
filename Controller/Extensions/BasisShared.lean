module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Extensions.GateBasis

@[expose] public section

/-! Proper-basis detection with shared tables across all observations. The
monotone branch evaluates each candidate once; the no-OR branch constructs
its summary table outside the root loop. -/
namespace Controller.Extensions.BasisShared
open Controller.Decoder Controller.Decoder.DAG Controller.Extensions.GateBasis

instance admissibleDecidable (b : ℕ) (target : Channel n) (K : Finset (Channel n)) :
    Decidable (Admissible b target K) :=
  inferInstanceAs (Decidable (K.Nonempty ∧ (b=1 → target ∈ K)))

/-- One faulty evaluation is shared by all output comparisons. -/
def testCandidate (graph : DAG n) (b : ℕ) (target : Channel n)
    (healthy : Fin graph.nodeCount → Bool) (K : Finset (Channel n)) : Option (Finset (Channel n)) :=
  let values := graph.evalTable (assignmentOfSet K)
  if Admissible b target K ∧ graph.roots.any (fun root => values root != healthy root)
  then some K else none

theorem testCandidate_some (graph : DAG n) (b : ℕ) (target : Channel n)
    (healthy : Fin graph.nodeCount → Bool) (K L : Finset (Channel n))
    (returned : testCandidate graph b target healthy K = some L) :
    Admissible b target L ∧ ∃ root ∈ graph.roots, graph.eval (assignmentOfSet L) root ≠ healthy root := by
  unfold testCandidate at returned
  dsimp only at returned
  split at returned
  next yes =>
    have eq := Option.some.inj returned
    subst L
    simpa [DAG.evalTable_eq_eval, List.any_eq_true] using yes
  next no => simp at returned

theorem testCandidate_none_iff (graph : DAG n) (b : ℕ) (target : Channel n)
    (healthy : Fin graph.nodeCount → Bool) (K : Finset (Channel n)) :
    testCandidate graph b target healthy K = none ↔
      ¬ (Admissible b target K ∧ ∃ root ∈ graph.roots, graph.eval (assignmentOfSet K) root ≠ healthy root) := by
  simp [testCandidate,DAG.evalTable_eq_eval,List.any_eq_true]

def monotoneCandidates (b : ℕ) (target : Channel n) : List (Finset (Channel n)) :=
  Finset.univ :: (List.finRange n).map (trueCandidate b target)

@[simp] theorem monotoneCandidates_length (b : ℕ) (target : Channel n) :
    (monotoneCandidates b target).length = n+1 := by simp [monotoneCandidates]

/-- Extremal sets are shared across observations, including repeated roots. -/
def monotoneSearch (graph : DAG n) (b : ℕ) (target : Channel n)
    (healthy : Fin graph.nodeCount → Bool) : Option (Finset (Channel n)) :=
  firstSuccess (testCandidate graph b target healthy) (monotoneCandidates b target)

theorem monotoneSearch_some (graph : DAG n) (b : ℕ) (target : Channel n)
    (healthy : Fin graph.nodeCount → Bool) (K : Finset (Channel n))
    (returned : monotoneSearch graph b target healthy = some K) :
    Admissible b target K ∧ ∃ root ∈ graph.roots, graph.eval (assignmentOfSet K) root ≠ healthy root := by
  obtain ⟨L,_,found⟩ := firstSuccess_some _ _ K returned
  exact testCandidate_some graph b target healthy L K found

theorem monotoneSearch_none_iff (graph : DAG n) (noGuards : NoNegativeGuards graph)
    (b : ℕ) (target : Channel n) (healthy : Fin graph.nodeCount → Bool) :
    monotoneSearch graph b target healthy = none ↔
      ¬ ∃ root ∈ graph.roots, ∃ K, Admissible b target K ∧
        graph.eval (assignmentOfSet K) root ≠ healthy root := by
  rw [monotoneSearch, firstSuccess_none_iff]
  constructor
  · intro absent ⟨root,member,K,eligible,differs⟩
    cases h : healthy root with
    | false =>
      have truth : graph.eval (assignmentOfSet K) root = true := by
        cases f : graph.eval (assignmentOfSet K) root <;> simp_all
      have fullTruth := (monotone_true_full graph noGuards b target root).mp ⟨K,eligible,truth⟩
      apply (testCandidate_none_iff graph b target healthy Finset.univ).mp
        (absent _ (by simp [monotoneCandidates]))
      exact ⟨⟨⟨target,Finset.mem_univ _⟩,fun _ => Finset.mem_univ _⟩,
        root,member,by rw [fullTruth,h]; decide⟩
    | true =>
      have zero : graph.eval (assignmentOfSet K) root = false := by
        cases f : graph.eval (assignmentOfSet K) root <;> simp_all
      obtain ⟨head,zero⟩ := (monotone_false_minimal graph noGuards b target root).mp ⟨K,eligible,zero⟩
      apply (testCandidate_none_iff graph b target healthy (trueCandidate b target head)).mp
        (absent _ (by simp [monotoneCandidates]))
      exact ⟨trueCandidate_admissible b target head,root,member,by rw [zero,h]; decide⟩
  · intro absent K _
    apply (testCandidate_none_iff graph b target healthy K).mpr
    rintro ⟨eligible,root,member,differs⟩
    exact absent ⟨root,member,K,eligible,differs⟩

/-- The summary table is allocated once and shared by the root callbacks. -/
def literalSearch (graph : DAG n) (b : ℕ) (target : Channel n)
    (healthy : Fin graph.nodeCount → Bool) : Option (Finset (Channel n)) :=
  let summaries := summaryTable graph
  firstSuccess (fun root => literalQuery graph summaries b target root (!healthy root)) graph.roots

theorem literalSearch_some (graph : DAG n) (noOr : NoDisjunction graph)
    (b : ℕ) (target : Channel n) (healthy : Fin graph.nodeCount → Bool) (K : Finset (Channel n))
    (returned : literalSearch graph b target healthy = some K) :
    Admissible b target K ∧ ∃ root ∈ graph.roots, graph.eval (assignmentOfSet K) root ≠ healthy root := by
  obtain ⟨root,member,found⟩ := firstSuccess_some _ _ K returned
  obtain ⟨eligible,value⟩ := literalQuery_some graph noOr b target root _ K found
  refine ⟨eligible,root,member,?_⟩
  rw [value]
  cases healthy root <;> decide

theorem literalSearch_none_iff (graph : DAG n) (noOr : NoDisjunction graph)
    (b : ℕ) (target : Channel n) (healthy : Fin graph.nodeCount → Bool) :
    literalSearch graph b target healthy = none ↔
      ¬ ∃ root ∈ graph.roots, ∃ K, Admissible b target K ∧
        graph.eval (assignmentOfSet K) root ≠ healthy root := by
  rw [literalSearch,firstSuccess_none_iff]
  constructor
  · intro absent ⟨root,member,K,eligible,differs⟩
    apply (literalQuery_none_iff graph noOr b target root _).mp (absent root member)
    refine ⟨K,eligible,?_⟩
    cases f : graph.eval (assignmentOfSet K) root <;> cases h : healthy root <;> simp_all
  · intro absent root member
    apply (literalQuery_none_iff graph noOr b target root _).mpr
    rintro ⟨K,eligible,value⟩
    apply absent ⟨root,member,K,eligible,?_⟩
    rw [value]
    cases healthy root <;> decide

/-- Dispatch by a missing operation, hoisting reusable tables outside scans. -/
def detectSet (graph : DAG n) (B : Basis) (b : ℕ) (target : Channel n) (drive : Bool) :
    Option (Finset (Channel n)) :=
  if drive then
    if B.conjunction = false then GateBasis.detectSet graph B b target drive
    else
      let healthy := graph.evalTable (assignmentOfSet {target})
      if B.negativeGuard = false then monotoneSearch graph b target healthy
      else literalSearch graph b target healthy
  else none

theorem detectSet_some (graph : DAG n) (B : Basis) (uses : Uses graph B) (proper : B ≠ full)
    (b : ℕ) (target : Channel n) (drive : Bool) (K : Finset (Channel n))
    (returned : detectSet graph B b target drive = some K) :
    drive = true ∧ Admissible b target K ∧ ∃ root ∈ graph.roots,
      graph.eval (assignmentOfSet K) root ≠ graph.eval (assignmentOfSet {target}) root := by
  cases drive with
  | false => simp [detectSet] at returned
  | true =>
    by_cases noAnd : B.conjunction = false
    · exact GateBasis.detectSet_some graph B uses proper b target true K
        (by simpa [detectSet,noAnd] using returned)
    · by_cases noGuard : B.negativeGuard = false
      · obtain ⟨eligible,meaning⟩ := monotoneSearch_some graph b target _ K
          (by simpa [detectSet,noAnd,noGuard] using returned)
        exact ⟨rfl,eligible,by simpa [DAG.evalTable_eq_eval] using meaning⟩
      · have noOr : B.disjunction = false := by
          rcases (proper_iff_missing B).mp proper with h | h | h
          · exact h
          · exact (noAnd h).elim
          · exact (noGuard h).elim
        obtain ⟨eligible,meaning⟩ := literalSearch_some graph (no_disjunction graph B uses noOr) b target _ K
          (by simpa [detectSet,noAnd,noGuard] using returned)
        exact ⟨rfl,eligible,by simpa [DAG.evalTable_eq_eval] using meaning⟩

theorem detectSet_none_iff (graph : DAG n) (B : Basis) (uses : Uses graph B) (proper : B ≠ full)
    (b : ℕ) (target : Channel n) (drive : Bool) :
    detectSet graph B b target drive = none ↔
      ¬ (drive = true ∧ ∃ root ∈ graph.roots, ∃ K, Admissible b target K ∧
        graph.eval (assignmentOfSet K) root ≠ graph.eval (assignmentOfSet {target}) root) := by
  cases drive with
  | false => simp [detectSet]
  | true =>
    by_cases noAnd : B.conjunction = false
    · simpa [detectSet,noAnd] using GateBasis.detectSet_none_iff graph B uses proper b target true
    · by_cases noGuard : B.negativeGuard = false
      · simpa [detectSet,noAnd,noGuard,DAG.evalTable_eq_eval] using
          monotoneSearch_none_iff graph (no_guard graph B uses noGuard) b target (graph.evalTable (assignmentOfSet {target}))
      · have noOr : B.disjunction = false := by
          rcases (proper_iff_missing B).mp proper with h | h | h
          · exact h
          · exact (noAnd h).elim
          · exact (noGuard h).elim
        simpa [detectSet,noAnd,noGuard,DAG.evalTable_eq_eval] using
          literalSearch_none_iff graph (no_disjunction graph B uses noOr) b target (graph.evalTable (assignmentOfSet {target}))

end Controller.Extensions.BasisShared
