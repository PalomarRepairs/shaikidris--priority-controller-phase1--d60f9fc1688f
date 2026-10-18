module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Decoder.Detect
public import Mathlib.Data.Finset.Union

@[expose] public section

/-! Typed operation bases and monotone decoder extrema. Negative guards read
primary channels; they do not accept negative subdecoder references. -/
namespace Controller.Extensions.GateBasis
open Controller.Decoder Controller.Decoder.DAG

structure Basis where
  disjunction : Bool
  conjunction : Bool
  negativeGuard : Bool
  deriving DecidableEq, Repr

def full : Basis := ⟨true, true, true⟩

def allBases : List Basis :=
  [⟨false, false, false⟩, ⟨false, false, true⟩,
   ⟨false, true, false⟩, ⟨false, true, true⟩,
   ⟨true, false, false⟩, ⟨true, false, true⟩,
   ⟨true, true, false⟩, ⟨true, true, true⟩]

theorem allBases_complete (B : Basis) : B ∈ allBases := by
  obtain ⟨d, c, g⟩ := B
  cases d <;> cases c <;> cases g <;> decide

theorem allBases_distinct : allBases.Nodup := by decide

theorem proper_iff_missing (B : Basis) :
    B ≠ full ↔ B.disjunction = false ∨ B.conjunction = false ∨ B.negativeGuard = false := by
  obtain ⟨d, c, g⟩ := B
  cases d <;> cases c <;> cases g <;> decide

/-- Nullary and unary disjunctions are constants and aliases; an empty guard
is also an alias. Neither needs a nontrivial operation from the basis. -/
def Allows (B : Basis) : Gate n available → Prop
  | .zero | .input _ => True
  | .disj refs => refs.length ≤ 1 ∨ B.disjunction = true
  | .guard _ labels => labels = [] ∨ B.negativeGuard = true
  | .liveAnd _ _ => B.conjunction = true

def Uses (graph : DAG n) (B : Basis) : Prop := ∀ i, Allows B (graph.node i)
def NoNegativeGuards (graph : DAG n) : Prop := ∀ i, (graph.node i).guardLabels = []
def NoDisjunction (graph : DAG n) : Prop :=
  ∀ i, match graph.node i with | .disj refs => refs.length ≤ 1 | _ => True

theorem no_conjunction_guarded (graph : DAG n) (B : Basis) (uses : Uses graph B)
    (missing : B.conjunction = false) : graph.Guarded := by
  intro i
  have allows := uses i
  cases gate : graph.node i <;> simp_all [Allows, Gate.IsGuarded, Gate.isLiveAnd]

theorem no_guard (graph : DAG n) (B : Basis) (uses : Uses graph B)
    (missing : B.negativeGuard = false) : NoNegativeGuards graph := by
  intro i
  have allows := uses i
  cases gate : graph.node i <;> simp_all [Allows, Gate.guardLabels]

theorem no_disjunction (graph : DAG n) (B : Basis) (uses : Uses graph B)
    (missing : B.disjunction = false) : NoDisjunction graph := by
  intro i
  have allows := uses i
  cases gate : graph.node i <;> simp_all [Allows]

private theorem gate_monotone (gate : Gate n available) (noGuards : gate.guardLabels = [])
    (a a' : Assignment n) (earlier later : Fin available → Bool)
    (inputs : ∀ c, a c = true → a' c = true)
    (children : ∀ c, earlier c = true → later c = true)
    (truth : gate.eval a earlier = true) : gate.eval a' later = true := by
  cases gate with
  | zero => simp [Gate.eval] at truth
  | input c => exact inputs c truth
  | disj refs =>
    obtain ⟨c, hc, value⟩ := List.any_eq_true.mp truth
    exact List.any_eq_true.mpr ⟨c, hc, children c value⟩
  | guard c labels =>
    have empty : labels = [] := noGuards
    subst labels
    simpa [Gate.eval] using children c (by simpa [Gate.eval] using truth)
  | liveAnd l r =>
    have parts := Bool.and_eq_true_iff.mp truth
    exact Bool.and_eq_true_iff.mpr ⟨children l parts.1, children r parts.2⟩

theorem eval_monotone (graph : DAG n) (noGuards : NoNegativeGuards graph)
    (K L : Finset (Channel n)) (subset : K ⊆ L) (root : Fin graph.nodeCount)
    (truth : graph.eval (assignmentOfSet K) root = true) :
    graph.eval (assignmentOfSet L) root = true := by
  have claim : ∀ bound : ℕ, ∀ i : Fin graph.nodeCount, i.val = bound →
      graph.eval (assignmentOfSet K) i = true → graph.eval (assignmentOfSet L) i = true := by
    intro bound
    induction bound using Nat.strong_induction_on with
    | h bound ih =>
      intro i hi truth
      rw [graph.eval_eq] at truth ⊢
      apply gate_monotone _ (noGuards i) _ _ _ _ ?_ ?_ truth
      · intro c hc
        simpa [assignmentOfSet] using subset (by simpa [assignmentOfSet] using hc)
      · intro c hc
        exact ih c.val (by simpa [hi] using c.isLt) _ rfl hc
  exact claim root.val root rfl truth

theorem monotone_true_full (graph : DAG n) (noGuards : NoNegativeGuards graph)
    (b : ℕ) (target : Channel n) (root : Fin graph.nodeCount) :
    (∃ K, Admissible b target K ∧ graph.eval (assignmentOfSet K) root = true) ↔
      graph.eval (assignmentOfSet Finset.univ) root = true := by
  constructor
  · rintro ⟨K, _, truth⟩
    exact eval_monotone graph noGuards K Finset.univ (Finset.subset_univ _) root truth
  · intro truth
    exact ⟨Finset.univ, ⟨⟨target, Finset.mem_univ _⟩, fun _ => Finset.mem_univ _⟩, truth⟩

theorem monotone_false_minimal (graph : DAG n) (noGuards : NoNegativeGuards graph)
    (b : ℕ) (target : Channel n) (root : Fin graph.nodeCount) :
    (∃ K, Admissible b target K ∧ graph.eval (assignmentOfSet K) root = false) ↔
      ∃ head : Channel n, graph.eval (assignmentOfSet (trueCandidate b target head)) root = false := by
  constructor
  · rintro ⟨K, admissible, zero⟩
    obtain ⟨head, member⟩ := admissible.1
    refine ⟨head, ?_⟩
    cases value : graph.eval (assignmentOfSet (trueCandidate b target head)) root with
    | false => rfl
    | true =>
      have := eval_monotone graph noGuards _ K (trueCandidate_subset admissible member) root value
      simp [zero] at this
  · rintro ⟨head, zero⟩
    exact ⟨trueCandidate b target head, trueCandidate_admissible b target head, zero⟩

structure Cube (n : ℕ) where
  positive : Finset (Channel n)
  negative : Finset (Channel n)
  deriving DecidableEq

def Holds (summary : Option (Cube n)) (K : Finset (Channel n)) : Prop :=
  match summary with
  | none => False
  | some c => c.positive ⊆ K ∧ Disjoint c.negative K

def normalize (P N : Finset (Channel n)) : Option (Cube n) :=
  if Disjoint P N then some ⟨P, N⟩ else none

theorem normalize_holds (P N K : Finset (Channel n)) :
    Holds (normalize P N) K ↔ P ⊆ K ∧ Disjoint N K := by
  by_cases consistent : Disjoint P N
  · simp [normalize, consistent, Holds]
  · simp only [normalize, ite_eq_right consistent, Holds, false_iff]
    rintro ⟨subset, disjoint⟩
    apply consistent
    apply Finset.disjoint_left.mpr
    intro c hp hn
    exact Finset.disjoint_left.mp disjoint hn (subset hp)

def merge (a b : Option (Cube n)) : Option (Cube n) := do
  let a ← a
  let b ← b
  normalize (a.positive ∪ b.positive) (a.negative ∪ b.negative)

def addGuards (a : Option (Cube n)) (labels : List (Channel n)) : Option (Cube n) := do
  let a ← a
  normalize a.positive (a.negative ∪ labels.toFinset)

theorem merge_holds (a b : Option (Cube n)) (K : Finset (Channel n)) :
    Holds (merge a b) K ↔ Holds a K ∧ Holds b K := by
  cases a with
  | none => simp [merge, Holds]
  | some a =>
    cases b with
    | none => simp [merge, Holds]
    | some b =>
      change Holds (normalize (a.positive ∪ b.positive) (a.negative ∪ b.negative)) K ↔ _
      rw [normalize_holds]
      simp [Holds, Finset.union_subset_iff, Finset.disjoint_union_left,
        and_assoc, and_left_comm, and_comm]

theorem addGuards_holds (a : Option (Cube n)) (labels : List (Channel n))
    (K : Finset (Channel n)) :
    Holds (addGuards a labels) K ↔ Holds a K ∧ ∀ c ∈ labels, c ∉ K := by
  cases a with
  | none => simp [addGuards, Holds]
  | some a =>
    change Holds (normalize a.positive (a.negative ∪ labels.toFinset)) K ↔ _
    rw [normalize_holds, Finset.disjoint_union_left]
    constructor
    · rintro ⟨hp, hn, hl⟩
      exact ⟨⟨hp, hn⟩, fun c hc => Finset.disjoint_left.mp hl (by simpa using hc)⟩
    · rintro ⟨⟨hp, hn⟩, hl⟩
      exact ⟨hp, hn, Finset.disjoint_left.mpr (fun c hc => hl c (by simpa using hc))⟩

def literalGate (gate : Gate n available) (earlier : Fin available → Option (Cube n)) :
    Option (Cube n) := match gate with
  | .zero => none
  | .input c => some ⟨{c}, ∅⟩
  | .disj [c] => earlier c
  | .disj _ => none
  | .guard c labels => addGuards (earlier c) labels
  | .liveAnd l r => merge (earlier l) (earlier r)

theorem literalGate_correct (gate : Gate n available)
    (noOr : match gate with | .disj refs => refs.length ≤ 1 | _ => True)
    (summaries : Fin available → Option (Cube n)) (values : Fin available → Bool)
    (K : Finset (Channel n))
    (correct : ∀ c, Holds (summaries c) K ↔ values c = true) :
    Holds (literalGate gate summaries) K ↔ gate.eval (assignmentOfSet K) values = true := by
  cases gate with
  | zero => simp [literalGate, Holds, Gate.eval]
  | input c => simp [literalGate, Holds, Gate.eval, assignmentOfSet]
  | liveAnd l r => simpa [literalGate, merge_holds, Gate.eval] using and_congr (correct l) (correct r)
  | guard c labels =>
    rw [literalGate, addGuards_holds, correct]
    simp [Gate.eval, List.any_eq_false, assignmentOfSet]
  | disj refs =>
    cases refs with
    | nil => simp [literalGate, Holds, Gate.eval]
    | cons c rest =>
      cases rest with
      | nil => simpa [literalGate, Gate.eval] using correct c
      | cons d rest => simp at noOr

/-- Literal summaries use represented node identities and preserve sharing. -/
def literalSummary (graph : DAG n) (index : Fin graph.nodeCount) : Option (Cube n) :=
  literalGate (graph.node index) (fun child => literalSummary graph (graph.childIndex index child))
termination_by index.val
decreasing_by exact graph.childIndex_lt index child

theorem literalSummary_correct (graph : DAG n) (noOr : NoDisjunction graph)
    (K : Finset (Channel n)) (root : Fin graph.nodeCount) :
    Holds (literalSummary graph root) K ↔ graph.eval (assignmentOfSet K) root = true := by
  have claim : ∀ bound : ℕ, ∀ i : Fin graph.nodeCount, i.val = bound →
      (Holds (literalSummary graph i) K ↔ graph.eval (assignmentOfSet K) i = true) := by
    intro bound
    induction bound using Nat.strong_induction_on with
    | h bound ih =>
      intro i hi
      rw [literalSummary, graph.eval_eq]
      refine literalGate_correct (n := n) (available := i.val) (graph.node i) ?_ _ _ K ?_
      · cases h : graph.node i with
        | zero => trivial
        | input _ => trivial
        | guard _ _ => trivial
        | liveAnd _ _ => trivial
        | disj refs => simpa only [h] using noOr i
      · intro c
        exact ih c.val (by simpa [hi] using c.isLt) _ rfl
  exact claim root.val root rfl

end Controller.Extensions.GateBasis

namespace Controller.Extensions.GateBasis
open Controller.Decoder Controller.Decoder.DAG

/-- Prefix tables compute each stored summary once and retain earlier values. -/
def summaryPrefix (graph : DAG n) :
    (length : ℕ) → length ≤ graph.nodeCount → Fin length → Option (Cube n)
  | 0, _ => Fin.elim0
  | length + 1, bound =>
    let earlier := summaryPrefix graph length (Nat.le_trans (Nat.le_succ _) bound)
    let gate := graph.node ⟨length, Nat.lt_of_lt_of_le (Nat.lt_succ_self _) bound⟩
    Fin.lastCases (literalGate gate earlier) earlier

theorem summaryPrefix_eq (graph : DAG n) : ∀ length bound (index : Fin length),
    summaryPrefix graph length bound index = literalSummary graph (index.castLE bound) := by
  intro length
  induction length with
  | zero => intro bound index; exact Fin.elim0 index
  | succ length ih =>
    intro bound index
    refine Fin.lastCases ?_ (fun child => ?_) index
    · simp only [summaryPrefix, Fin.lastCases_last]
      rw [literalSummary]
      congr 1
      funext child
      exact ih _ child
    · simp only [summaryPrefix, Fin.lastCases_castSucc]
      simpa only [Fin.castLE, Fin.castSucc, Fin.castAdd] using
        ih (Nat.le_trans (Nat.le_succ length) bound) child

def summaryTable (graph : DAG n) : Fin graph.nodeCount → Option (Cube n) :=
  summaryPrefix graph graph.nodeCount le_rfl

theorem summaryTable_correct (graph : DAG n) (noOr : NoDisjunction graph)
    (K : Finset (Channel n)) (root : Fin graph.nodeCount) :
    Holds (summaryTable graph root) K ↔ graph.eval (assignmentOfSet K) root = true := by
  rw [summaryTable, summaryPrefix_eq]
  exact literalSummary_correct graph noOr K root

private theorem admissible_mono {b : ℕ} {target : Channel n} {K L : Finset (Channel n)}
    (h : Admissible b target K) (sub : K ⊆ L) : Admissible b target L :=
  ⟨h.1.mono sub, fun one => sub (h.2 one)⟩

def forcedPositive (b : ℕ) (target : Channel n) (P : Finset (Channel n)) : Finset (Channel n) :=
  if b = 1 then insert target P else P

/-- Linear many possible witnesses for either truth value of one literal cube. -/
def cubeCandidates (b : ℕ) (target : Channel n) (summary : Option (Cube n)) :
    List (Finset (Channel n)) :=
  let positive := match summary with | none => ∅ | some c => c.positive
  {target} :: forcedPositive b target positive ::
    ((List.finRange n).map (trueCandidate b target) ++
      (List.finRange n).map (fun c => Finset.univ.erase c))

theorem cubeCandidates_length (b : ℕ) (target : Channel n) (summary : Option (Cube n)) :
    (cubeCandidates b target summary).length = 2 * n + 2 := by
  simp [cubeCandidates]
  omega

theorem cube_true_complete (b : ℕ) (target : Channel n) (summary : Option (Cube n))
    (K : Finset (Channel n)) (eligible : Admissible b target K) (truth : Holds summary K) :
    ∃ L ∈ cubeCandidates b target summary, Admissible b target L ∧ Holds summary L := by
  classical
  cases summary with
  | none => exact truth.elim
  | some c =>
    let P := forcedPositive b target c.positive
    have contains : c.positive ⊆ P := by
      by_cases one : b = 1 <;> simp [P, forcedPositive, one]
    have sub : P ⊆ K := by
      by_cases one : b = 1
      · simpa [P, forcedPositive, one] using Finset.insert_subset (eligible.2 one) truth.1
      · simpa [P, forcedPositive, one] using truth.1
    by_cases nonempty : P.Nonempty
    · refine ⟨P, by simp [cubeCandidates, P], ⟨nonempty, ?_⟩, contains, ?_⟩
      · intro one
        simp [P, forcedPositive, one]
      · exact Finset.disjoint_left.mpr (fun v hv hP => Finset.disjoint_left.mp truth.2 hv (sub hP))
    · have empty : P = ∅ := Finset.not_nonempty_iff_eq_empty.mp nonempty
      have emptyPos : c.positive = ∅ := by simpa only [empty, Finset.subset_empty] using contains
      obtain ⟨head, hh⟩ := eligible.1
      let L := trueCandidate b target head
      refine ⟨L, ?_, trueCandidate_admissible b target head, ?_, ?_⟩
      · simp only [cubeCandidates, List.mem_cons, List.mem_append, List.mem_map]
        exact Or.inr (Or.inr (Or.inl ⟨head, by simp, rfl⟩))
      · simp [emptyPos]
      · exact Finset.disjoint_left.mpr (fun v hv hL =>
          Finset.disjoint_left.mp truth.2 hv (trueCandidate_subset eligible hh hL))

theorem cube_false_complete (b : ℕ) (target : Channel n) (summary : Option (Cube n))
    (K : Finset (Channel n)) (eligible : Admissible b target K) (zero : ¬ Holds summary K) :
    ∃ L ∈ cubeCandidates b target summary, Admissible b target L ∧ ¬ Holds summary L := by
  classical
  cases summary with
  | none => exact ⟨{target}, by simp [cubeCandidates], admissible_singleton target, by simp [Holds]⟩
  | some c =>
    by_cases positives : c.positive ⊆ K
    · have bad : ¬ Disjoint c.negative K := fun h => zero ⟨positives, h⟩
      obtain ⟨head, hn, hk⟩ := Finset.not_disjoint_iff.mp bad
      refine ⟨trueCandidate b target head, ?_, trueCandidate_admissible b target head, ?_⟩
      · simp only [cubeCandidates, List.mem_cons, List.mem_append, List.mem_map]
        exact Or.inr (Or.inr (Or.inl ⟨head, by simp, rfl⟩))
      · intro h
        exact Finset.disjoint_left.mp h.2 hn (head_mem_trueCandidate b target head)
    · obtain ⟨head, hp, hk⟩ := Finset.not_subset.mp positives
      have sub : K ⊆ Finset.univ.erase head := by
        intro v hv
        exact Finset.mem_erase.mpr ⟨by intro eq; subst v; exact hk hv, Finset.mem_univ _⟩
      refine ⟨Finset.univ.erase head, ?_, admissible_mono eligible sub, ?_⟩
      · simp only [cubeCandidates, List.mem_cons, List.mem_append, List.mem_map]
        exact Or.inr (Or.inr (Or.inr ⟨head, by simp, rfl⟩))
      · intro h
        have := h.1 hp
        simp at this

instance holdsDecidable (summary : Option (Cube n)) (K : Finset (Channel n)) :
    Decidable (Holds summary K) := by
  cases summary <;> dsimp [Holds] <;> infer_instance

instance admissibleDecidable (b : ℕ) (target : Channel n) (K : Finset (Channel n)) :
    Decidable (Admissible b target K) :=
  inferInstanceAs (Decidable (K.Nonempty ∧ (b = 1 → target ∈ K)))

theorem cube_any_complete (b : ℕ) (target : Channel n) (summary : Option (Cube n))
    (K : Finset (Channel n)) (eligible : Admissible b target K) (wanted : Bool)
    (value : Holds summary K ↔ wanted = true) :
    ∃ L ∈ cubeCandidates b target summary, Admissible b target L ∧
      (Holds summary L ↔ wanted = true) := by
  cases wanted with
  | false =>
    obtain ⟨L, member, admissible, zero⟩ := cube_false_complete b target summary K eligible
      (by simpa using value)
    exact ⟨L, member, admissible, by simpa using zero⟩
  | true =>
    obtain ⟨L, member, admissible, truth⟩ := cube_true_complete b target summary K eligible
      (value.mpr rfl)
    exact ⟨L, member, admissible, by simpa using truth⟩

def cubeSearch (b : ℕ) (target : Channel n) (summary : Option (Cube n)) (wanted : Bool) :
    Option (Finset (Channel n)) :=
  (cubeCandidates b target summary).find? fun K =>
    decide (Admissible b target K ∧ (Holds summary K ↔ wanted = true))

theorem cubeSearch_some (b : ℕ) (target : Channel n) (summary : Option (Cube n))
    (wanted : Bool) (K : Finset (Channel n)) (returned : cubeSearch b target summary wanted = some K) :
    Admissible b target K ∧ (Holds summary K ↔ wanted = true) := by
  have test := List.find?_some
    (p := fun L => decide (Admissible b target L ∧ (Holds summary L ↔ wanted = true))) returned
  exact of_decide_eq_true test

theorem cubeSearch_none_iff (b : ℕ) (target : Channel n) (summary : Option (Cube n)) (wanted : Bool) :
    cubeSearch b target summary wanted = none ↔
      ¬ ∃ K, Admissible b target K ∧ (Holds summary K ↔ wanted = true) := by
  constructor
  · intro none ⟨K, eligible, value⟩
    obtain ⟨L, member, admissible, value⟩ := cube_any_complete b target summary K eligible wanted value
    have rejects := List.find?_eq_none.mp none L member
    exact rejects (by simp only [decide_eq_true_eq]; exact ⟨admissible, value⟩)
  · intro no
    apply List.find?_eq_none.mpr
    intro K _ test
    exact no ⟨K, of_decide_eq_true test⟩

/-- A no-OR root query uses the memoized literal summary and linear many
candidate sets. The target/nonemptiness restriction is checked on every result. -/
def literalQuery (graph : DAG n) (summaries : Fin graph.nodeCount → Option (Cube n))
    (b : ℕ) (target : Channel n) (root : Fin graph.nodeCount) (wanted : Bool) :
    Option (Finset (Channel n)) := cubeSearch b target (summaries root) wanted

theorem literalQuery_none_iff (graph : DAG n) (noOr : NoDisjunction graph)
    (b : ℕ) (target : Channel n) (root : Fin graph.nodeCount) (wanted : Bool) :
    literalQuery graph (summaryTable graph) b target root wanted = none ↔
      ¬ ∃ K, Admissible b target K ∧ graph.eval (assignmentOfSet K) root = wanted := by
  rw [literalQuery, cubeSearch_none_iff]
  apply not_congr
  apply exists_congr
  intro K
  apply and_congr_right
  intro _
  rw [summaryTable_correct graph noOr]
  cases graph.eval (assignmentOfSet K) root <;> cases wanted <;> decide

theorem literalQuery_some (graph : DAG n) (noOr : NoDisjunction graph)
    (b : ℕ) (target : Channel n) (root : Fin graph.nodeCount) (wanted : Bool)
    (K : Finset (Channel n))
    (returned : literalQuery graph (summaryTable graph) b target root wanted = some K) :
    Admissible b target K ∧ graph.eval (assignmentOfSet K) root = wanted := by
  have sound := cubeSearch_some b target (summaryTable graph root) wanted K returned
  refine ⟨sound.1, ?_⟩
  have value := (summaryTable_correct graph noOr K root).symm.trans sound.2
  cases faulty : graph.eval (assignmentOfSet K) root <;> cases wanted <;> simp_all

def monotoneQuery (graph : DAG n) (b : ℕ) (target : Channel n)
    (root : Fin graph.nodeCount) (wanted : Bool) : Option (Finset (Channel n)) :=
  (Finset.univ :: (List.finRange n).map (trueCandidate b target)).find? fun K =>
    decide (Admissible b target K ∧ graph.evalTable (assignmentOfSet K) root = wanted)

theorem monotoneQuery_some (graph : DAG n) (b : ℕ) (target : Channel n)
    (root : Fin graph.nodeCount) (wanted : Bool) (K : Finset (Channel n))
    (returned : monotoneQuery graph b target root wanted = some K) :
    Admissible b target K ∧ graph.eval (assignmentOfSet K) root = wanted := by
  have test := List.find?_some
    (p := fun L => decide (Admissible b target L ∧ graph.evalTable (assignmentOfSet L) root = wanted)) returned
  simpa only [DAG.evalTable_eq_eval] using (of_decide_eq_true test)

theorem monotoneQuery_none_iff (graph : DAG n) (noGuards : NoNegativeGuards graph)
    (b : ℕ) (target : Channel n) (root : Fin graph.nodeCount) (wanted : Bool) :
    monotoneQuery graph b target root wanted = none ↔
      ¬ ∃ K, Admissible b target K ∧ graph.eval (assignmentOfSet K) root = wanted := by
  unfold monotoneQuery
  simp only [DAG.evalTable_eq_eval]
  constructor
  · intro none ⟨K, admissible, value⟩
    have reject := List.find?_eq_none.mp none
    cases wanted with
    | true =>
      have truth := (monotone_true_full graph noGuards b target root).mp ⟨K, admissible, value⟩
      exact reject Finset.univ (List.mem_cons_self) (by
        simp only [decide_eq_true_eq]
        exact ⟨⟨⟨target, Finset.mem_univ _⟩, fun _ => Finset.mem_univ _⟩, truth⟩)
    | false =>
      obtain ⟨head, zero⟩ := (monotone_false_minimal graph noGuards b target root).mp
        ⟨K, admissible, value⟩
      exact reject (trueCandidate b target head)
        (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨head, by simp, rfl⟩))
        (by simp only [decide_eq_true_eq]; exact ⟨trueCandidate_admissible b target head, zero⟩)
  · intro no
    apply List.find?_eq_none.mpr
    intro K _ test
    exact no ⟨K, of_decide_eq_true test⟩

def cachedScanTrue (graph : DAG n) (b : ℕ) (target : Channel n)
    (root : Fin graph.nodeCount) : Option (Finset (Channel n)) :=
  ((List.finRange n).find? fun head =>
    graph.evalTable (assignmentOfSet (trueCandidate b target head)) root).map
      (trueCandidate b target)

theorem cachedScanTrue_eq (graph : DAG n) (b : ℕ) (target : Channel n)
    (root : Fin graph.nodeCount) : cachedScanTrue graph b target root = graph.scanTrue b target root := by
  simp only [cachedScanTrue, DAG.evalTable_eq_eval, DAG.scanTrue]

/-- Proper bases dispatch by a missing operation; the syntax need not contain
every allowed operation. The full basis has no correctness claim here. -/
def rootQuery (graph : DAG n) (B : Basis) (b : ℕ) (target : Channel n)
    (root : Fin graph.nodeCount) (wanted : Bool) : Option (Finset (Channel n)) :=
  if B.conjunction = false then
    match wanted with
    | true => cachedScanTrue graph b target root
    | false => graph.solveZero b target root ∅ ∅
  else if B.negativeGuard = false then monotoneQuery graph b target root wanted
  else literalQuery graph (summaryTable graph) b target root wanted

theorem rootQuery_none_iff (graph : DAG n) (B : Basis) (uses : Uses graph B) (proper : B ≠ full)
    (b : ℕ) (target : Channel n) (root : Fin graph.nodeCount) (wanted : Bool) :
    rootQuery graph B b target root wanted = none ↔
      ¬ ∃ K, Admissible b target K ∧ graph.eval (assignmentOfSet K) root = wanted := by
  by_cases noAnd : B.conjunction = false
  · have guarded := no_conjunction_guarded graph B uses noAnd
    cases wanted with
    | true => simpa [rootQuery, noAnd, cachedScanTrue_eq] using graph.scanTrue_none_iff guarded b target root
    | false => simpa [rootQuery, noAnd, ExtendsFixed] using
        graph.solveZero_none_iff guarded b target root ∅ ∅
  · by_cases noGuard : B.negativeGuard = false
    · simpa [rootQuery, noAnd, noGuard] using
        monotoneQuery_none_iff graph (no_guard graph B uses noGuard) b target root wanted
    · have noOr : B.disjunction = false := by
        rcases (proper_iff_missing B).mp proper with h | h | h
        · exact h
        · exact (noAnd h).elim
        · exact (noGuard h).elim
      simpa [rootQuery, noAnd, noGuard] using
        literalQuery_none_iff graph (no_disjunction graph B uses noOr) b target root wanted

theorem rootQuery_some (graph : DAG n) (B : Basis) (uses : Uses graph B) (proper : B ≠ full)
    (b : ℕ) (target : Channel n) (root : Fin graph.nodeCount) (wanted : Bool)
    (K : Finset (Channel n)) (returned : rootQuery graph B b target root wanted = some K) :
    Admissible b target K ∧ graph.eval (assignmentOfSet K) root = wanted := by
  by_cases noAnd : B.conjunction = false
  · have guarded := no_conjunction_guarded graph B uses noAnd
    cases wanted with
    | true =>
      exact graph.scanTrue_some b target root K
        (by simpa [rootQuery, noAnd, cachedScanTrue_eq] using returned)
    | false =>
      have sound := graph.solveZero_some guarded b target root ∅ ∅ K
        (by simpa [rootQuery, noAnd] using returned)
      exact ⟨sound.1, sound.2.2⟩
  · by_cases noGuard : B.negativeGuard = false
    · exact monotoneQuery_some graph b target root wanted K
        (by simpa [rootQuery, noAnd, noGuard] using returned)
    · have noOr : B.disjunction = false := by
        rcases (proper_iff_missing B).mp proper with h | h | h
        · exact h
        · exact (noAnd h).elim
        · exact (noGuard h).elim
      exact literalQuery_some graph (no_disjunction graph B uses noOr) b target root wanted K
        (by simpa [rootQuery, noAnd, noGuard] using returned)

/-- Evaluate the healthy table once and ask each observation for its opposite.
The drive flag is the physical early exit. -/
def detectSet (graph : DAG n) (B : Basis) (b : ℕ) (target : Channel n) (drive : Bool) :
    Option (Finset (Channel n)) :=
  if drive then
    let healthy := graph.evalTable (assignmentOfSet {target})
    firstSuccess (fun root => rootQuery graph B b target root (!healthy root)) graph.roots
  else none

@[simp] theorem detectSet_drive_false (graph : DAG n) (B : Basis) (b : ℕ)
    (target : Channel n) : detectSet graph B b target false = none := by
  simp [detectSet]

theorem detectSet_some (graph : DAG n) (B : Basis) (uses : Uses graph B) (proper : B ≠ full)
    (b : ℕ) (target : Channel n) (drive : Bool) (K : Finset (Channel n))
    (returned : detectSet graph B b target drive = some K) :
    drive = true ∧ Admissible b target K ∧ ∃ root ∈ graph.roots,
      graph.eval (assignmentOfSet K) root ≠ graph.eval (assignmentOfSet {target}) root := by
  cases drive with
  | false => simp [detectSet] at returned
  | true =>
    simp only [detectSet, ite_true, DAG.evalTable_eq_eval] at returned
    obtain ⟨root, member, result⟩ := firstSuccess_some _ _ K returned
    obtain ⟨eligible, opposite⟩ := rootQuery_some graph B uses proper b target root _ K result
    refine ⟨rfl, eligible, root, member, ?_⟩
    rw [opposite]
    cases graph.eval (assignmentOfSet {target}) root <;> decide

theorem detectSet_none_iff (graph : DAG n) (B : Basis) (uses : Uses graph B) (proper : B ≠ full)
    (b : ℕ) (target : Channel n) (drive : Bool) :
    detectSet graph B b target drive = none ↔
      ¬ (drive = true ∧ ∃ root ∈ graph.roots, ∃ K, Admissible b target K ∧
        graph.eval (assignmentOfSet K) root ≠ graph.eval (assignmentOfSet {target}) root) := by
  cases drive with
  | false => simp [detectSet]
  | true =>
    simp only [detectSet, ite_true, DAG.evalTable_eq_eval, firstSuccess_none_iff, true_and]
    constructor
    · intro absent ⟨root, member, K, eligible, differs⟩
      have opposite : graph.eval (assignmentOfSet K) root =
          !graph.eval (assignmentOfSet {target}) root := by
        cases h : graph.eval (assignmentOfSet {target}) root <;>
          cases f : graph.eval (assignmentOfSet K) root <;> simp_all
      exact (rootQuery_none_iff graph B uses proper b target root _).mp
        (absent root member) ⟨K, eligible, opposite⟩
    · intro absent root member
      apply (rootQuery_none_iff graph B uses proper b target root _).mpr
      rintro ⟨K, eligible, opposite⟩
      apply absent ⟨root, member, K, eligible, ?_⟩
      rw [opposite]
      cases graph.eval (assignmentOfSet {target}) root <;> decide

end Controller.Extensions.GateBasis
