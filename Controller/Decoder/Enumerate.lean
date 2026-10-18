module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Decoder.Extend
public import Controller.Physical.DetectionBridge
public import Mathlib.Data.Fintype.Powerset

@[expose] public section

/-! Streaming partialSet search. The runtime retains one eligible set and a cursor.
Right siblings are reconstructed from its false coordinates in decreasing
coordinate order. Emitted results are passed to a callback; no output list is
part of the runtime state. Prefix-copy costs are separate from oracle counts. -/
namespace Controller.Decoder
namespace Enumeration

/-- False precedes true, and channel zero is the first lexicographic coordinate. -/
def Before (first second : Finset (Channel n)) : Prop :=
  ∃ channel : Channel n, channel ∉ first ∧ channel ∈ second ∧
    ∀ earlier : Channel n, earlier.val < channel.val →
      (earlier ∈ first ↔ earlier ∈ second)

def Agrees (depth : ℕ) (partialSet K : Finset (Channel n)) : Prop :=
  ∀ channel : Channel n, channel.val < depth → (channel ∈ K ↔ channel ∈ partialSet)

def fixedTrue (depth : ℕ) (partialSet : Finset (Channel n)) : Finset (Channel n) :=
  partialSet.filter (fun channel => channel.val < depth)

def fixedFalse (depth : ℕ) (partialSet : Finset (Channel n)) : Finset (Channel n) :=
  Finset.univ.filter (fun channel => channel.val < depth ∧ channel ∉ partialSet)

theorem extendsFixed_iff_agrees (depth : ℕ) (partialSet K : Finset (Channel n)) :
    ExtendsFixed (fixedTrue depth partialSet) (fixedFalse depth partialSet) K ↔
      Agrees depth partialSet K := by
  constructor
  · rintro ⟨positive, negative⟩ channel lower
    constructor
    · intro member
      by_contra missing
      exact Finset.disjoint_left.mp negative member (by simp [fixedFalse, lower, missing])
    · intro member
      exact positive (by simp [fixedTrue, member, lower])
  · intro agreement
    constructor
    · intro channel member
      obtain ⟨present, lower⟩ := Finset.mem_filter.mp member
      exact (agreement channel lower).mpr present
    · apply Finset.disjoint_left.mpr
      intro channel member forbidden
      have denied := (Finset.mem_filter.mp forbidden).2
      exact denied.2 ((agreement channel denied.1).mp member)

theorem agrees_full (partialSet K : Finset (Channel n)) : Agrees n partialSet K ↔ K = partialSet := by
  constructor
  · intro agreement
    ext channel
    exact agreement channel channel.isLt
  · rintro rfl
    exact fun _ _ => Iff.rfl

def Detecting (graph : DAG n) (busCount : ℕ) (target : Channel n) (drive : Bool)
    (K : Finset (Channel n)) : Prop :=
  drive = true ∧ Admissible busCount target K ∧
    ∃ root ∈ graph.roots,
      graph.eval (assignmentOfSet K) root ≠ graph.eval (assignmentOfSet {target}) root

/-- The existing exact extension solver is the sole prefix-pruning oracle. -/
def query (graph : DAG n) (busCount : ℕ) (target : Channel n) (drive : Bool)
    (depth : ℕ) (partialSet : Finset (Channel n)) : Bool :=
  (graph.extendSet busCount target drive (fixedTrue depth partialSet)
    (fixedFalse depth partialSet)).isSome

theorem query_true_iff (graph : DAG n) (guarded : graph.Guarded) (busCount : ℕ)
    (target : Channel n) (drive : Bool) (depth : ℕ) (partialSet : Finset (Channel n)) :
    query graph busCount target drive depth partialSet = true ↔
      ∃ K, Detecting graph busCount target drive K ∧ Agrees depth partialSet K := by
  have exactOracle := graph.extendSet_exists_iff guarded busCount target drive
    (fixedTrue depth partialSet) (fixedFalse depth partialSet)
  have optionIff : query graph busCount target drive depth partialSet = true ↔
      ∃ K, graph.extendSet busCount target drive (fixedTrue depth partialSet)
        (fixedFalse depth partialSet) = some K := by
    unfold query
    cases result : graph.extendSet busCount target drive (fixedTrue depth partialSet)
        (fixedFalse depth partialSet) <;> simp
  rw [optionIff, exactOracle]
  constructor
  · rintro ⟨driveTrue, root, present, K, eligible, fixed, differs⟩
    exact ⟨K, ⟨driveTrue, eligible, root, present, differs⟩,
      (extendsFixed_iff_agrees depth partialSet K).mp fixed⟩
  · rintro ⟨K, ⟨driveTrue, eligible, root, present, differs⟩, agreement⟩
    exact ⟨driveTrue, root, present, K, eligible,
      (extendsFixed_iff_agrees depth partialSet K).mpr agreement, differs⟩

theorem query_false_iff (graph : DAG n) (guarded : graph.Guarded) (busCount : ℕ)
    (target : Channel n) (drive : Bool) (depth : ℕ) (partialSet : Finset (Channel n)) :
    query graph busCount target drive depth partialSet = false ↔
      ¬∃ K, Detecting graph busCount target drive K ∧ Agrees depth partialSet K := by
  rw [← query_true_iff graph guarded busCount target drive depth partialSet]
  exact Bool.eq_false_iff

def Bounded (depth : ℕ) (partialSet : Finset (Channel n)) : Prop :=
  ∀ channel ∈ partialSet, channel.val < depth

theorem agrees_mono {first second : ℕ} {partialSet K : Finset (Channel n)}
    (agreement : Agrees second partialSet K) (smaller : first ≤ second) :
    Agrees first partialSet K := fun channel lower => agreement channel (lower.trans_le smaller)

theorem agrees_false_child (depth : ℕ) (partialSet K : Finset (Channel n))
    (lower : depth < n) (bounded : Bounded depth partialSet) :
    Agrees (depth + 1) partialSet K ↔ Agrees depth partialSet K ∧ (⟨depth, lower⟩ : Channel n) ∉ K := by
  let channel : Channel n := ⟨depth, lower⟩
  have missing : channel ∉ partialSet := fun h => Nat.lt_irrefl depth (bounded channel h)
  constructor
  · intro agreement
    refine ⟨agrees_mono agreement (by omega), ?_⟩
    exact fun h => missing ((agreement channel (by dsimp [channel]; omega)).mp h)
  · rintro ⟨agreement, absent⟩ current earlier
    by_cases prior : current.val < depth
    · exact agreement current prior
    · have eq : current = channel := Fin.ext (by dsimp [channel]; omega)
      subst current
      exact ⟨fun h => False.elim (absent h), fun h => False.elim (missing h)⟩

theorem agrees_true_child (depth : ℕ) (partialSet K : Finset (Channel n))
    (lower : depth < n) (bounded : Bounded depth partialSet) :
    Agrees (depth + 1) (insert (⟨depth, lower⟩ : Channel n) partialSet) K ↔
      Agrees depth partialSet K ∧ (⟨depth, lower⟩ : Channel n) ∈ K := by
  let channel : Channel n := ⟨depth, lower⟩
  constructor
  · intro agreement
    refine ⟨?_, ?_⟩
    · intro current earlier
      have different : current ≠ channel := by intro eq; subst current; dsimp [channel] at earlier; omega
      have differentFin : current ≠ (⟨depth, lower⟩ : Channel n) := different
      simpa only [Finset.mem_insert, differentFin, false_or] using agreement current (by omega)
    · exact (agreement channel (by dsimp [channel]; omega)).mpr (Finset.mem_insert_self _ _)
  · rintro ⟨agreement, present⟩ current earlier
    by_cases prior : current.val < depth
    · have different : current ≠ channel := by intro eq; subst current; dsimp [channel] at prior; omega
      have differentFin : current ≠ (⟨depth, lower⟩ : Channel n) := different
      simpa only [Finset.mem_insert, differentFin, false_or] using agreement current prior
    · have eq : current = channel := Fin.ext (by dsimp [channel]; omega)
      subst current
      exact ⟨fun _ => Finset.mem_insert_self _ _, fun _ => present⟩

theorem bounded_insert (depth : ℕ) (partialSet : Finset (Channel n)) (lower : depth < n)
    (bounded : Bounded depth partialSet) : Bounded (depth + 1) (insert ⟨depth, lower⟩ partialSet) := by
  intro channel member
  rcases Finset.mem_insert.mp member with rfl | member
  · simp
  · exact (bounded channel member).trans (Nat.lt_succ_self depth)

theorem true_child_feasible (graph : DAG n) (guarded : graph.Guarded) (busCount : ℕ)
    (target : Channel n) (drive : Bool) (depth : ℕ) (partialSet : Finset (Channel n))
    (lower : depth < n) (bounded : Bounded depth partialSet)
    (feasible : query graph busCount target drive depth partialSet = true)
    (leftFalse : query graph busCount target drive (depth + 1) partialSet = false) :
    query graph busCount target drive (depth + 1) (insert ⟨depth, lower⟩ partialSet) = true := by
  obtain ⟨K, detects, agreement⟩ := (query_true_iff graph guarded busCount target drive depth partialSet).mp feasible
  have present : (⟨depth, lower⟩ : Channel n) ∈ K := by
    by_contra absent
    exact (query_false_iff graph guarded busCount target drive (depth + 1) partialSet).mp leftFalse
      ⟨K, detects, (agrees_false_child depth partialSet K lower bounded).mpr ⟨agreement, absent⟩⟩
  exact (query_true_iff graph guarded busCount target drive (depth + 1) _).mpr
    ⟨K, detects, (agrees_true_child depth partialSet K lower bounded).mpr ⟨agreement, present⟩⟩

/-- Oracle charges belong to one call; the eligible set is the current path. -/
structure Completed (n : ℕ) where
  eligible : Finset (Channel n)
  tests : ℕ

/-- Given a feasible prefix, query only the false child. If it is infeasible,
the true child is feasible by the exact oracle and is selected without a test. -/
def complete (graph : DAG n) (busCount : ℕ) (target : Channel n) (drive : Bool)
    (depth : ℕ) (partialSet : Finset (Channel n)) : ℕ → Completed n
  | 0 => ⟨partialSet, 0⟩
  | fuel + 1 =>
    if lower : depth < n then
      let child : Channel n := ⟨depth, lower⟩
      let nextPrefix := if query graph busCount target drive (depth + 1) partialSet then
        partialSet else insert child partialSet
      let result := complete graph busCount target drive (depth + 1) nextPrefix fuel
      ⟨result.eligible, result.tests + 1⟩
    else ⟨partialSet, 0⟩

theorem complete_tests_le (graph : DAG n) (busCount : ℕ) (target : Channel n)
    (drive : Bool) (fuel : ℕ) : ∀ depth partialSet,
    (complete graph busCount target drive depth partialSet fuel).tests ≤ fuel := by
  induction fuel with
  | zero => intro depth partialSet; simp [complete]
  | succ fuel ih =>
    intro depth partialSet
    unfold complete
    split
    · exact Nat.add_le_add_right (ih _ _) 1
    · exact Nat.zero_le _

/-- A greedy descent returns a detecting completion of the original prefix. -/
theorem complete_spec (graph : DAG n) (guarded : graph.Guarded) (busCount : ℕ)
    (target : Channel n) (drive : Bool) (fuel : ℕ) : ∀ depth partialSet,
    depth + fuel = n → Bounded depth partialSet →
    query graph busCount target drive depth partialSet = true →
    Detecting graph busCount target drive (complete graph busCount target drive depth partialSet fuel).eligible ∧
    Agrees depth partialSet (complete graph busCount target drive depth partialSet fuel).eligible := by
  induction fuel with
  | zero =>
    intro depth partialSet total bounded feasible
    have eq : depth = n := by omega
    subst depth
    obtain ⟨K, detects, agrees⟩ := (query_true_iff graph guarded busCount target drive n partialSet).mp feasible
    have eq := (agrees_full partialSet K).mp agrees
    subst K
    exact ⟨detects, fun _ _ => Iff.rfl⟩
  | succ fuel ih =>
    intro depth partialSet total bounded feasible
    have lower : depth < n := by omega
    have nextTotal : depth + 1 + fuel = n := by omega
    cases left : query graph busCount target drive (depth + 1) partialSet with
    | true =>
      have boundNext : Bounded (depth + 1) partialSet := fun channel member => (bounded channel member).trans (by omega)
      have result := ih (depth + 1) partialSet nextTotal boundNext left
      simpa [complete, lower, left] using
        (show Detecting graph busCount target drive (complete graph busCount target drive (depth + 1) partialSet fuel).eligible ∧
          Agrees depth partialSet (complete graph busCount target drive (depth + 1) partialSet fuel).eligible from
          ⟨result.1, agrees_mono result.2 (by omega)⟩)
    | false =>
      let child : Channel n := ⟨depth, lower⟩
      have right := true_child_feasible graph guarded busCount target drive depth partialSet lower bounded feasible left
      have result := ih (depth + 1) (insert child partialSet) nextTotal (bounded_insert depth partialSet lower bounded) right
      have prior := ((agrees_true_child depth partialSet _ lower bounded).mp result.2).1
      simpa [complete, lower, left, child] using
        (show Detecting graph busCount target drive
          (complete graph busCount target drive (depth + 1) (insert child partialSet) fuel).eligible ∧
          Agrees depth partialSet (complete graph busCount target drive (depth + 1) (insert child partialSet) fuel).eligible from
          ⟨result.1, prior⟩)

/-- The greedy completion is lexicographically first among detecting
completions of its partialSet. -/
theorem complete_min (graph : DAG n) (guarded : graph.Guarded) (busCount : ℕ)
    (target : Channel n) (drive : Bool) (fuel : ℕ) : ∀ depth partialSet,
    depth + fuel = n → Bounded depth partialSet →
    query graph busCount target drive depth partialSet = true →
    ∀ K, Detecting graph busCount target drive K → Agrees depth partialSet K →
      (complete graph busCount target drive depth partialSet fuel).eligible = K ∨
      Before (complete graph busCount target drive depth partialSet fuel).eligible K := by
  induction fuel with
  | zero =>
    intro depth partialSet total bounded feasible K detects agreement
    have eq : depth = n := by omega
    subst depth
    exact Or.inl ((agrees_full partialSet K).mp agreement).symm
  | succ fuel ih =>
    intro depth partialSet total bounded feasible K detects agreement
    have lower : depth < n := by omega
    let channel : Channel n := ⟨depth, lower⟩
    have nextTotal : depth + 1 + fuel = n := by omega
    cases left : query graph busCount target drive (depth + 1) partialSet with
    | true =>
      have boundNext : Bounded (depth + 1) partialSet := fun current member => (bounded current member).trans (by omega)
      by_cases inK : channel ∈ K
      · have outputAgreement :=
          (complete_spec graph guarded busCount target drive fuel (depth + 1) partialSet nextTotal boundNext left).2
        have outputFalse := ((agrees_false_child depth partialSet _ lower bounded).mp outputAgreement).2
        have smaller : Before
            (complete graph busCount target drive (depth + 1) partialSet fuel).eligible K := by
          refine ⟨channel, outputFalse, inK, ?_⟩
          intro prior earlier
          exact (outputAgreement prior (by dsimp [channel] at earlier; omega)).trans (agreement prior earlier).symm
        simpa [complete, lower, left] using Or.inr smaller
      · have comparison := ih (depth + 1) partialSet nextTotal boundNext left K detects
          ((agrees_false_child depth partialSet K lower bounded).mpr ⟨agreement, inK⟩)
        simpa [complete, lower, left] using comparison
    | false =>
      have right := true_child_feasible graph guarded busCount target drive depth partialSet lower bounded feasible left
      have inK : channel ∈ K := by
        by_contra absent
        exact (query_false_iff graph guarded busCount target drive (depth + 1) partialSet).mp left
          ⟨K, detects, (agrees_false_child depth partialSet K lower bounded).mpr ⟨agreement, absent⟩⟩
      have comparison := ih (depth + 1) (insert channel partialSet) nextTotal
        (bounded_insert depth partialSet lower bounded) right K detects
        ((agrees_true_child depth partialSet K lower bounded).mpr ⟨agreement, inK⟩)
      simpa [complete, lower, left, channel] using comparison

def AfterWithin (cursor : ℕ) (previous K : Finset (Channel n)) : Prop :=
  ∃ channel : Channel n, channel.val < cursor ∧ channel ∉ previous ∧ channel ∈ K ∧
    Agrees channel.val previous K

theorem afterWithin_full (previous K : Finset (Channel n)) :
    AfterWithin n previous K ↔ Before previous K := by
  constructor
  · rintro ⟨channel, _, absent, present, agreement⟩
    exact ⟨channel, absent, present, fun prior lower => (agreement prior lower).symm⟩
  · rintro ⟨channel, absent, present, agreement⟩
    exact ⟨channel, channel.isLt, absent, present, fun prior lower => (agreement prior lower).symm⟩

theorem afterWithin_zero (previous K : Finset (Channel n)) : ¬AfterWithin 0 previous K := by
  rintro ⟨channel, lower, _⟩
  omega

theorem afterWithin_succ (cursor : ℕ) (previous K : Finset (Channel n)) (lower : cursor < n) :
    AfterWithin (cursor + 1) previous K ↔ AfterWithin cursor previous K ∨
      ((⟨cursor, lower⟩ : Channel n) ∉ previous ∧
        (⟨cursor, lower⟩ : Channel n) ∈ K ∧ Agrees cursor previous K) := by
  constructor
  · rintro ⟨channel, before, absent, present, agreement⟩
    by_cases earlier : channel.val < cursor
    · exact Or.inl ⟨channel, earlier, absent, present, agreement⟩
    · have eq : channel = ⟨cursor, lower⟩ := Fin.ext (by change channel.val = cursor; omega)
      subst channel
      exact Or.inr ⟨absent, present, agreement⟩
  · rintro (⟨channel, before, absent, present, agreement⟩ | ⟨absent, present, agreement⟩)
    · exact ⟨channel, by omega, absent, present, agreement⟩
    · exact ⟨⟨cursor, lower⟩, by simp, absent, present, agreement⟩

theorem agrees_fixedTrue (depth : ℕ) (previous K : Finset (Channel n)) :
    Agrees depth (fixedTrue depth previous) K ↔ Agrees depth previous K := by
  constructor <;> intro agreement channel lower <;>
    simpa [fixedTrue, lower] using agreement channel lower

theorem sibling_agrees (depth : ℕ) (previous K : Finset (Channel n)) (lower : depth < n) :
    Agrees (depth + 1) (insert (⟨depth, lower⟩ : Channel n) (fixedTrue depth previous)) K ↔
      Agrees depth previous K ∧ (⟨depth, lower⟩ : Channel n) ∈ K := by
  rw [agrees_true_child depth (fixedTrue depth previous) K lower]
  · rw [agrees_fixedTrue]
  · intro channel member
    exact (Finset.mem_filter.mp member).2

theorem sibling_bounded (depth : ℕ) (previous : Finset (Channel n)) (lower : depth < n) :
    Bounded (depth + 1) (insert (⟨depth, lower⟩ : Channel n) (fixedTrue depth previous)) :=
  bounded_insert depth (fixedTrue depth previous) lower
    (fun channel member => (Finset.mem_filter.mp member).2)

theorem earlier_sibling_before (cursor : ℕ) (previous result K : Finset (Channel n))
    (lower : cursor < n)
    (resultAgrees : Agrees cursor previous result)
    (within : AfterWithin cursor previous K) : Before result K := by
  obtain ⟨channel, earlier, absent, present, agreement⟩ := within
  refine ⟨channel, ?_, present, ?_⟩
  · exact fun member => absent ((resultAgrees channel earlier).mp member)
  · intro prior before
    exact (resultAgrees prior (before.trans earlier)).trans (agreement prior before).symm

/-- A sibling search scans implicit pending depths from high to low. -/
structure SearchResult (n : ℕ) where
  output : Option (Finset (Channel n))
  tests : ℕ

def seek (graph : DAG n) (busCount : ℕ) (target : Channel n) (drive : Bool)
    (previous : Finset (Channel n)) : ℕ → SearchResult n
  | 0 => ⟨none, 0⟩
  | cursor + 1 =>
    if lower : cursor < n then
      let channel : Channel n := ⟨cursor, lower⟩
      if channel ∈ previous then seek graph busCount target drive previous cursor
      else
        let partialSet := insert channel (fixedTrue cursor previous)
        if query graph busCount target drive (cursor + 1) partialSet then
          let result := complete graph busCount target drive (cursor + 1) partialSet
            (n - (cursor + 1))
          ⟨some result.eligible, result.tests + 1⟩
        else
          let result := seek graph busCount target drive previous cursor
          ⟨result.output, result.tests + 1⟩
    else seek graph busCount target drive previous cursor

theorem seek_tests_le (graph : DAG n) (busCount : ℕ) (target : Channel n)
    (drive : Bool) (previous : Finset (Channel n)) : ∀ cursor,
    (seek graph busCount target drive previous cursor).tests ≤ cursor + n := by
  intro cursor
  induction cursor with
  | zero => simp [seek]
  | succ cursor ih =>
    unfold seek
    split
    · dsimp only
      split
      · exact ih.trans (by omega)
      · split
        · have cost := complete_tests_le graph busCount target drive (n - (cursor + 1))
            (cursor + 1) (insert ⟨cursor, by assumption⟩ (fixedTrue cursor previous))
          dsimp only
          omega
        · dsimp only
          omega
    · exact ih.trans (by omega)

/-- Ghost specification of a single streamed result; this is not runtime state. -/
def Least (predicate : Finset (Channel n) → Prop) : Option (Finset (Channel n)) → Prop
  | none => ¬∃ K, predicate K
  | some result => predicate result ∧ ∀ K, predicate K → result = K ∨ Before result K

theorem least_congr {first second : Finset (Channel n) → Prop}
    (agreement : ∀ K, first K ↔ second K) (output : Option (Finset (Channel n))) :
    Least first output ↔ Least second output := by
  cases output with
  | none => simp only [Least]; exact not_congr (exists_congr agreement)
  | some result =>
    constructor
    · rintro ⟨member, minimal⟩
      exact ⟨(agreement result).mp member, fun K h => minimal K ((agreement K).mpr h)⟩
    · rintro ⟨member, minimal⟩
      exact ⟨(agreement result).mpr member, fun K h => minimal K ((agreement K).mp h)⟩

theorem seek_spec (graph : DAG n) (guarded : graph.Guarded) (busCount : ℕ)
    (target : Channel n) (drive : Bool) (previous : Finset (Channel n)) : ∀ cursor,
    cursor ≤ n → Least (fun K => Detecting graph busCount target drive K ∧
      AfterWithin cursor previous K) (seek graph busCount target drive previous cursor).output := by
  intro cursor
  induction cursor with
  | zero =>
    intro bounded
    simp only [seek, Least]
    rintro ⟨K, _, within⟩
    exact afterWithin_zero previous K within
  | succ cursor ih =>
    intro bounded
    have lower : cursor < n := by omega
    let channel : Channel n := ⟨cursor, lower⟩
    have smaller := ih (by omega)
    by_cases present : channel ∈ previous
    · have predicates : ∀ K,
          (Detecting graph busCount target drive K ∧ AfterWithin cursor previous K) ↔
          (Detecting graph busCount target drive K ∧ AfterWithin (cursor + 1) previous K) := by
        intro K
        rw [afterWithin_succ cursor previous K lower]
        simp [channel, present]
      have transported := (least_congr predicates _).mp smaller
      simpa [seek, lower, present, channel] using transported
    · let partialSet := insert channel (fixedTrue cursor previous)
      cases feasible : query graph busCount target drive (cursor + 1) partialSet with
      | false =>
        have predicates : ∀ K,
            (Detecting graph busCount target drive K ∧ AfterWithin cursor previous K) ↔
            (Detecting graph busCount target drive K ∧ AfterWithin (cursor + 1) previous K) := by
          intro K
          constructor
          · rintro ⟨detects, within⟩
            exact ⟨detects, (afterWithin_succ cursor previous K lower).mpr (Or.inl within)⟩
          · rintro ⟨detects, within⟩
            rcases (afterWithin_succ cursor previous K lower).mp within with old | ⟨_, inK, agreement⟩
            · exact ⟨detects, old⟩
            · exact False.elim ((query_false_iff graph guarded busCount target drive (cursor + 1) partialSet).mp feasible
                ⟨K, detects, (sibling_agrees cursor previous K lower).mpr ⟨agreement, inK⟩⟩)
        have transported := (least_congr predicates _).mp smaller
        simpa [seek, lower, present, feasible, partialSet, channel] using transported
      | true =>
        let result := complete graph busCount target drive (cursor + 1) partialSet (n - (cursor + 1))
        have total : cursor + 1 + (n - (cursor + 1)) = n := by omega
        have completion := complete_spec graph guarded busCount target drive (n - (cursor + 1))
          (cursor + 1) partialSet total (sibling_bounded cursor previous lower) feasible
        have resultAgreement := (sibling_agrees cursor previous result.eligible lower).mp completion.2
        have minimal : Least (fun K => Detecting graph busCount target drive K ∧
            AfterWithin (cursor + 1) previous K) (some result.eligible) := by
          refine ⟨⟨completion.1, ⟨channel, by dsimp [channel]; omega, present,
            resultAgreement.2, resultAgreement.1⟩⟩, ?_⟩
          rintro K ⟨detects, within⟩
          rcases (afterWithin_succ cursor previous K lower).mp within with old | ⟨_, inK, agreement⟩
          · exact Or.inr (earlier_sibling_before cursor previous result.eligible K lower resultAgreement.1 old)
          · exact complete_min graph guarded busCount target drive (n - (cursor + 1))
              (cursor + 1) partialSet total (sibling_bounded cursor previous lower) feasible K detects
              ((sibling_agrees cursor previous K lower).mpr ⟨agreement, inK⟩)
        simpa [seek, lower, present, feasible, result, partialSet, channel] using minimal

/-- No emitted-history list is present: only the current eligible set is retained. -/
inductive State (n : ℕ) where
  | initial
  | after (previous : Finset (Channel n))
  | exhausted

structure NextResult (n : ℕ) where
  output : Option (Finset (Channel n))
  continuation : State n
  tests : ℕ

def next (graph : DAG n) (busCount : ℕ) (target : Channel n) (drive : Bool)
    (state : State n) : NextResult n :=
  let result : SearchResult n := match state with
    | .initial => if query graph busCount target drive 0 ∅ then
        let completed := complete graph busCount target drive 0 ∅ n
        ⟨some completed.eligible, completed.tests + 1⟩ else ⟨none, 1⟩
    | .after previous => seek graph busCount target drive previous n
    | .exhausted => ⟨none, 0⟩
  ⟨result.output, match result.output with | none => .exhausted | some K => .after K,
    result.tests⟩

theorem next_tests_le (graph : DAG n) (busCount : ℕ) (target : Channel n)
    (drive : Bool) (state : State n) :
    (next graph busCount target drive state).tests ≤ 2 * n + 1 := by
  cases state with
  | initial =>
    by_cases feasible : query graph busCount target drive 0 ∅ = true
    · have cost := complete_tests_le graph busCount target drive n 0 ∅
      simp only [next, feasible, ite_true]
      omega
    · simp [next, feasible]
  | after previous =>
    change (seek graph busCount target drive previous n).tests ≤ 2 * n + 1
    exact (seek_tests_le graph busCount target drive previous n).trans (by omega)
  | exhausted => simp [next]

@[reducible] def Remaining (graph : DAG n) (busCount : ℕ) (target : Channel n) (drive : Bool) :
    State n → Finset (Channel n) → Prop
  | .initial, K => Detecting graph busCount target drive K
  | .after previous, K => Detecting graph busCount target drive K ∧ Before previous K
  | .exhausted, _ => False

theorem next_spec (graph : DAG n) (guarded : graph.Guarded) (busCount : ℕ)
    (target : Channel n) (drive : Bool) (state : State n) :
    Least (Remaining graph busCount target drive state)
      (next graph busCount target drive state).output := by
  cases state with
  | exhausted => simp [next, Least, Remaining]
  | after previous =>
    have result := seek_spec graph guarded busCount target drive previous n (by omega)
    simpa only [next, Remaining, afterWithin_full] using result
  | initial =>
    cases feasible : query graph busCount target drive 0 ∅ with
    | false =>
      have none := (query_false_iff graph guarded busCount target drive 0 ∅).mp feasible
      have absent : ¬∃ K, Detecting graph busCount target drive K := by
        rintro ⟨K, detects⟩
        exact none ⟨K, detects, by intro channel lower; omega⟩
      simpa [next, feasible, Least, Remaining] using absent
    | true =>
      have bounded : Bounded 0 (∅ : Finset (Channel n)) := by simp [Bounded]
      have result := complete_spec graph guarded busCount target drive n 0 ∅ (by omega) bounded feasible
      have minimal := complete_min graph guarded busCount target drive n 0 ∅ (by omega) bounded feasible
      have least : Least (Detecting graph busCount target drive)
          (some (complete graph busCount target drive 0 ∅ n).eligible) :=
        ⟨result.1, fun K detects => minimal K detects (by intro channel lower; omega)⟩
      simpa [next, feasible, Remaining] using least

theorem before_irrefl (K : Finset (Channel n)) : ¬Before K K := by
  rintro ⟨channel, absent, present, _⟩
  exact absent present

theorem before_trans {first second third : Finset (Channel n)}
    (left : Before first second) (right : Before second third) : Before first third := by
  obtain ⟨a, firstFalse, secondTrue, leftAgree⟩ := left
  obtain ⟨b, secondFalse, thirdTrue, rightAgree⟩ := right
  rcases lt_trichotomy a.val b.val with earlier | same | later
  · refine ⟨a, firstFalse, (rightAgree a earlier).mp secondTrue, ?_⟩
    intro channel lower
    exact (leftAgree channel lower).trans (rightAgree channel (lower.trans earlier))
  · have eq : a = b := Fin.ext same
    subst b
    exact False.elim (secondFalse secondTrue)
  · refine ⟨b, ?_, thirdTrue, ?_⟩
    · exact fun member => secondFalse ((leftAgree b later).mp member)
    · intro channel lower
      exact (leftAgree channel (lower.trans later)).trans (rightAgree channel lower)

theorem next_continuation_some (graph : DAG n) (busCount : ℕ) (target : Channel n)
    (drive : Bool) (state : State n) (K : Finset (Channel n))
    (returned : (next graph busCount target drive state).output = some K) :
    (next graph busCount target drive state).continuation = .after K := by
  unfold next at returned ⊢
  dsimp only at returned ⊢
  rw [returned]

theorem next_continuation_none (graph : DAG n) (busCount : ℕ) (target : Channel n)
    (drive : Bool) (state : State n)
    (returned : (next graph busCount target drive state).output = none) :
    (next graph busCount target drive state).continuation = .exhausted := by
  unfold next at returned ⊢
  dsimp only at returned ⊢
  rw [returned]

theorem remaining_after_subset (graph : DAG n) (busCount : ℕ) (target : Channel n)
    (drive : Bool) (state : State n) (J : Finset (Channel n))
    (member : Remaining graph busCount target drive state J) :
    ∀ K, Remaining graph busCount target drive (.after J) K →
      Remaining graph busCount target drive state K := by
  cases state with
  | initial => exact fun K h => h.1
  | exhausted => exact False.elim member
  | after previous => exact fun K h => ⟨h.1, before_trans member.2 h.2⟩

theorem next_partition (graph : DAG n) (guarded : graph.Guarded) (busCount : ℕ)
    (target : Channel n) (drive : Bool) (state : State n) (J : Finset (Channel n))
    (returned : (next graph busCount target drive state).output = some J) :
    ∀ K, Remaining graph busCount target drive state K ↔
      K = J ∨ Remaining graph busCount target drive (.after J) K := by
  have spec := next_spec graph guarded busCount target drive state
  rw [returned] at spec
  obtain ⟨member, minimal⟩ := spec
  intro K
  constructor
  · intro present
    rcases minimal K present with eq | earlier
    · exact Or.inl eq.symm
    · have detecting : Detecting graph busCount target drive K := by
        cases state <;> simp_all [Remaining]
      exact Or.inr ⟨detecting, earlier⟩
  · rintro (rfl | later)
    · exact member
    · exact remaining_after_subset graph busCount target drive state J member K later

/-- Ghost finite trace for proving enumeration properties. The executable
streaming driver below does not compute or retain this list. -/
def trace (graph : DAG n) (busCount : ℕ) (target : Channel n) (drive : Bool) :
    ℕ → State n → List (Finset (Channel n))
  | 0, _ => []
  | fuel + 1, state =>
    let result := next graph busCount target drive state
    match result.output with
    | none => []
    | some K => K :: trace graph busCount target drive fuel result.continuation

noncomputable def remainingSets (graph : DAG n) (busCount : ℕ) (target : Channel n)
    (drive : Bool) (state : State n) : Finset (Finset (Channel n)) := by
  classical
  exact Finset.univ.filter (Remaining graph busCount target drive state)

@[simp] theorem mem_remainingSets (graph : DAG n) (busCount : ℕ) (target : Channel n)
    (drive : Bool) (state : State n) (K : Finset (Channel n)) :
    K ∈ remainingSets graph busCount target drive state ↔ Remaining graph busCount target drive state K := by
  classical
  simp [remainingSets]

theorem remainingSets_card_le (graph : DAG n) (busCount : ℕ) (target : Channel n)
    (drive : Bool) (state : State n) :
    (remainingSets graph busCount target drive state).card ≤ 2 ^ n := by
  classical
  have smaller := Finset.card_le_card (Finset.filter_subset
    (Remaining graph busCount target drive state) (Finset.univ : Finset (Finset (Channel n))))
  simpa [remainingSets, Fintype.card_finset] using smaller

theorem remaining_card_decreases (graph : DAG n) (guarded : graph.Guarded) (busCount : ℕ)
    (target : Channel n) (drive : Bool) (state : State n) (J : Finset (Channel n))
    (returned : (next graph busCount target drive state).output = some J) :
    (remainingSets graph busCount target drive (.after J)).card <
      (remainingSets graph busCount target drive state).card := by
  classical
  have spec := next_spec graph guarded busCount target drive state
  rw [returned] at spec
  have rootMem : J ∈ remainingSets graph busCount target drive state :=
    (mem_remainingSets _ _ _ _ _ _).mpr spec.1
  have subset : remainingSets graph busCount target drive (.after J) ⊆
      (remainingSets graph busCount target drive state).erase J := by
    intro K member
    have later := (mem_remainingSets _ _ _ _ _ _).mp member
    apply Finset.mem_erase.mpr
    refine ⟨?_, ?_⟩
    · intro eq
      subst K
      exact before_irrefl J later.2
    · exact (mem_remainingSets _ _ _ _ _ _).mpr
        (remaining_after_subset graph busCount target drive state J spec.1 K later)
  exact (Finset.card_le_card subset).trans_lt
    (Finset.card_erase_lt_of_mem rootMem)

theorem trace_remaining (graph : DAG n) (guarded : graph.Guarded) (busCount : ℕ)
    (target : Channel n) (drive : Bool) (fuel : ℕ) : ∀ state K,
    K ∈ trace graph busCount target drive fuel state →
      Remaining graph busCount target drive state K := by
  induction fuel with
  | zero => intro state K member; simp [trace] at member
  | succ fuel ih =>
    intro state K member
    cases returned : (next graph busCount target drive state).output with
    | none => simp [trace, returned] at member
    | some J =>
      have continuation := next_continuation_some graph busCount target drive state J returned
      have partition := next_partition graph guarded busCount target drive state J returned K
      simp only [trace, returned, continuation, List.mem_cons] at member
      rcases member with rfl | tail
      · exact partition.mpr (Or.inl rfl)
      · exact partition.mpr (Or.inr (ih (.after J) K tail))

theorem trace_complete (graph : DAG n) (guarded : graph.Guarded) (busCount : ℕ)
    (target : Channel n) (drive : Bool) (fuel : ℕ) : ∀ state,
    (remainingSets graph busCount target drive state).card ≤ fuel → ∀ K,
      K ∈ trace graph busCount target drive fuel state ↔
        Remaining graph busCount target drive state K := by
  induction fuel with
  | zero =>
    intro state bounded K
    have empty : remainingSets graph busCount target drive state = ∅ :=
      Finset.card_eq_zero.mp (by omega)
    simp only [trace, List.not_mem_nil, false_iff]
    intro member
    have inside := (mem_remainingSets graph busCount target drive state K).mpr member
    rw [empty] at inside
    simpa using inside
  | succ fuel ih =>
    intro state bounded K
    cases returned : (next graph busCount target drive state).output with
    | none =>
      have spec := next_spec graph guarded busCount target drive state
      rw [returned] at spec
      simp only [trace, returned, List.not_mem_nil, false_iff]
      exact fun member => spec ⟨K, member⟩
    | some J =>
      have continuation := next_continuation_some graph busCount target drive state J returned
      have decrease := remaining_card_decreases graph guarded busCount target drive state J returned
      have smaller : (remainingSets graph busCount target drive (.after J)).card ≤ fuel := by omega
      simp only [trace, returned, continuation, List.mem_cons, ih (.after J) smaller K]
      exact (next_partition graph guarded busCount target drive state J returned K).symm

theorem trace_lexicographic (graph : DAG n) (guarded : graph.Guarded) (busCount : ℕ)
    (target : Channel n) (drive : Bool) (fuel : ℕ) : ∀ state,
    (trace graph busCount target drive fuel state).Pairwise Before := by
  induction fuel with
  | zero => intro state; simp [trace]
  | succ fuel ih =>
    intro state
    cases returned : (next graph busCount target drive state).output with
    | none => simp [trace, returned]
    | some J =>
      have continuation := next_continuation_some graph busCount target drive state J returned
      simp only [trace, returned, continuation, List.pairwise_cons]
      exact ⟨fun K member => (trace_remaining graph guarded busCount target drive fuel (.after J) K member).2,
        ih (.after J)⟩

theorem trace_nodup (graph : DAG n) (guarded : graph.Guarded) (busCount : ℕ)
    (target : Channel n) (drive : Bool) (fuel : ℕ) (state : State n) :
    (trace graph busCount target drive fuel state).Nodup := by
  apply List.Pairwise.imp _ (trace_lexicographic graph guarded busCount target drive fuel state)
  intro first second before eq
  subst second
  exact before_irrefl first before

/-- Exact finite enumeration: the list is a ghost trace of streamed callback
invocations, not the driver's retained working state. -/
theorem enumeration_exact (graph : DAG n) (guarded : graph.Guarded) (busCount : ℕ)
    (target : Channel n) (drive : Bool) :
    (trace graph busCount target drive (2 ^ n) .initial).Nodup ∧
    (trace graph busCount target drive (2 ^ n) .initial).Pairwise Before ∧
    ∀ K, K ∈ trace graph busCount target drive (2 ^ n) .initial ↔
      Detecting graph busCount target drive K :=
  ⟨trace_nodup graph guarded busCount target drive _ _,
    trace_lexicographic graph guarded busCount target drive _ _,
    trace_complete graph guarded busCount target drive _ _
      (remainingSets_card_le graph busCount target drive _)⟩

/-- A bounded driver streams each result into the caller's callback. Its return
value is the continuation state, never a retained list of outputs. -/
def stream [Monad m] (graph : DAG n) (busCount : ℕ) (target : Channel n) (drive : Bool)
    (emit : Finset (Channel n) → m Unit) : ℕ → State n → m (State n)
  | 0, state => pure state
  | fuel + 1, state => do
    let result := next graph busCount target drive state
    match result.output with
    | none => pure .exhausted
    | some K =>
      emit K
      stream graph busCount target drive emit fuel result.continuation

/-- Ghost final state of the same iterator calls. -/
def finish (graph : DAG n) (busCount : ℕ) (target : Channel n) (drive : Bool) :
    ℕ → State n → State n
  | 0, state => state
  | fuel + 1, state =>
    let result := next graph busCount target drive state
    match result.output with
    | none => .exhausted
    | some _ => finish graph busCount target drive fuel result.continuation

theorem finish_exhausted (graph : DAG n) (guarded : graph.Guarded) (busCount : ℕ)
    (target : Channel n) (drive : Bool) (fuel : ℕ) : ∀ state,
    (remainingSets graph busCount target drive state).card < fuel →
      finish graph busCount target drive fuel state = .exhausted := by
  induction fuel with
  | zero => intro state impossible; omega
  | succ fuel ih =>
    intro state bounded
    cases returned : (next graph busCount target drive state).output with
    | none => simp [finish, returned]
    | some J =>
      have continuation := next_continuation_some graph busCount target drive state J returned
      have decrease := remaining_card_decreases graph guarded busCount target drive state J returned
      have smaller : (remainingSets graph busCount target drive (.after J)).card < fuel := by omega
      simpa [finish, returned, continuation] using ih (.after J) smaller

/-- This ghost fold specifies callback order; it is not computed by stream. -/
def emitTrace [Monad m] (emit : Finset (Channel n) → m Unit) :
    List (Finset (Channel n)) → m Unit
  | [] => pure ()
  | K :: rest => do emit K; emitTrace emit rest

theorem stream_callback_order [Monad m] [LawfulMonad m] (graph : DAG n) (busCount : ℕ)
    (target : Channel n) (drive : Bool) (emit : Finset (Channel n) → m Unit) (fuel : ℕ) :
    ∀ state, stream graph busCount target drive emit fuel state = (do
      emitTrace emit (trace graph busCount target drive fuel state)
      pure (finish graph busCount target drive fuel state)) := by
  induction fuel with
  | zero => intro state; simp [stream, trace, finish, emitTrace]
  | succ fuel ih =>
    intro state
    cases returned : (next graph busCount target drive state).output with
    | none => simp [stream, trace, finish, returned, emitTrace]
    | some J => simp [stream, trace, finish, returned, emitTrace, ih, bind_assoc]

/-- Canonical physical realization is applied to one emitted eligible set. -/
def observations (graph : DAG n) : Fin graph.roots.length → Assignment n → Bool :=
  fun output a => graph.eval a (graph.roots.get output)

theorem canonical_realization_detects (graph : DAG n) (bridge : Controller.Physical.Bridge n)
    (busCount : ℕ) (positive : 0 < busCount) (drive : Bool) (K : Finset (Channel n))
    (detects : Detecting graph busCount bridge.target drive K) :
    Controller.Physical.BridgeInputDetects bridge true (observations graph)
      (Controller.Physical.realizeBridge bridge positive K) true := by
  obtain ⟨driveTrue, eligible, root, present, differs⟩ := detects
  apply (Controller.Physical.realizeBridge_detects_iff bridge positive K eligible (observations graph)).mpr
  obtain ⟨output, rootEq⟩ := List.mem_iff_get.mp present
  refine ⟨output, ?_⟩
  change graph.eval (assignmentOfSet {bridge.target}) (graph.roots.get output) ≠
    graph.eval (assignmentOfSet K) (graph.roots.get output)
  rw [rootEq]
  exact differs.symm

/-- One additional iterator call accounts for the final exhaustion event. -/
theorem enumeration_terminates (graph : DAG n) (guarded : graph.Guarded) (busCount : ℕ)
    (target : Channel n) (drive : Bool) :
    finish graph busCount target drive (2 ^ n + 1) .initial = .exhausted :=
  finish_exhausted graph guarded busCount target drive _ _
    ((remainingSets_card_le graph busCount target drive _).trans_lt (Nat.lt_succ_self _))

end Enumeration
end Controller.Decoder
