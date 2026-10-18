module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Extensions.LiteralMachine

@[expose] public section

/-! Direct witnesses for one no-OR literal summary. A reachable one keeps all
positive literals and the forced target, rejects a negative conflict and
enforces nonemptiness. A reachable zero falsifies one conjunct while obeying
the target and nonemptiness conditions. Each test reads the summary once. -/
namespace Controller.Extensions.LiteralWitness
open Controller.Decoder Controller.Decoder.DAG Controller.Extensions.GateBasis
open Controller.Extensions.LiteralMachine

variable {n : ℕ}

/-- The forced part of every admissible set. -/
def forced (b : ℕ) (target : Channel n) : Finset (Channel n) := if b = 1 then {target} else ∅

theorem mem_forced (b : ℕ) (target c : Channel n) : c ∈ forced b target ↔ b = 1 ∧ c = target := by
  by_cases one : b = 1 <;> simp [forced, one]

theorem forced_subset (b : ℕ) (target : Channel n) (K : Finset (Channel n))
    (eligible : Admissible b target K) : forced b target ⊆ K := by
  intro c member
  obtain ⟨one, rfl⟩ := (mem_forced b target c).mp member
  exact eligible.2 one

theorem admissible_union (b : ℕ) (target : Channel n) (S : Finset (Channel n)) (nonempty : S.Nonempty) :
    Admissible b target (S ∪ forced b target) := by
  refine ⟨nonempty.mono Finset.subset_union_left, fun one => ?_⟩
  exact Finset.mem_union_right _ ((mem_forced b target target).mpr ⟨one, rfl⟩)

theorem admissible_target (b : ℕ) (target : Channel n) : Admissible b target {target} :=
  ⟨Finset.singleton_nonempty _, fun _ => Finset.mem_singleton_self _⟩

/-- Semantic value of a raw summary on an eligible set. -/
theorem holds_iff (a : Raw n) (K : Finset (Channel n)) :
    Holds a.decode K ↔ a.zero = false ∧ a.positive ⊆ K ∧ Disjoint a.negative K := by
  cases zero : a.zero
  · simp only [Raw.decode, zero, Bool.false_eq_true, ite_false, normalize_holds, true_and]
  · simp [Raw.decode, zero, Holds]

/-- A reachable one. -/
def oneWitness (b : ℕ) (target : Channel n) (a : Raw n) : Option (Finset (Channel n)) :=
  if a.zero then none
  else if Disjoint a.negative (a.positive ∪ forced b target) then
    if (a.positive ∪ forced b target).Nonempty then some (a.positive ∪ forced b target)
    else ((List.finRange n).find? fun c => decide (c ∉ a.negative)).map fun c => {c}
  else none

theorem oneWitness_some (b : ℕ) (target : Channel n) (a : Raw n) (K : Finset (Channel n))
    (returned : oneWitness b target a = some K) : Admissible b target K ∧ Holds a.decode K := by
  rw [holds_iff]
  unfold oneWitness at returned
  split at returned
  · simp at returned
  next zero =>
    split at returned
    next disjoint =>
      split at returned
      next nonempty =>
        cases returned
        exact ⟨⟨nonempty, fun one => Finset.mem_union_right _ ((mem_forced b target target).mpr ⟨one, rfl⟩)⟩,
          by simpa using zero, Finset.subset_union_left, disjoint⟩
      next empty =>
        obtain ⟨c, found, rfl⟩ := Option.map_eq_some_iff.mp returned
        have free : c ∉ a.negative := by simpa using List.find?_some found
        have emptyUnion : a.positive ∪ forced b target = ∅ := Finset.not_nonempty_iff_eq_empty.mp empty
        have positiveEmpty : a.positive = ∅ := Finset.union_eq_empty.mp emptyUnion |>.1
        have forcedEmpty : forced b target = ∅ := Finset.union_eq_empty.mp emptyUnion |>.2
        refine ⟨⟨Finset.singleton_nonempty c, fun one => ?_⟩, by simpa using zero, by simp [positiveEmpty], ?_⟩
        · have : target ∈ forced b target := (mem_forced b target target).mpr ⟨one, rfl⟩
          rw [forcedEmpty] at this
          exact absurd this (Finset.notMem_empty _)
        · exact Finset.disjoint_singleton_right.mpr free
    next => simp at returned

theorem oneWitness_none_iff (b : ℕ) (target : Channel n) (a : Raw n) :
    oneWitness b target a = none ↔ ¬∃ K, Admissible b target K ∧ Holds a.decode K := by
  constructor
  · intro absent ⟨K, eligible, truth⟩
    rw [holds_iff] at truth
    obtain ⟨zero, positive, disjoint⟩ := truth
    have base : a.positive ∪ forced b target ⊆ K :=
      Finset.union_subset positive (forced_subset b target K eligible)
    have disjointBase : Disjoint a.negative (a.positive ∪ forced b target) := disjoint.mono_right base
    unfold oneWitness at absent
    simp only [zero, Bool.false_eq_true, ite_false, disjointBase, ite_true] at absent
    split at absent
    · simp at absent
    · obtain ⟨c, member⟩ := eligible.1
      have free : c ∉ a.negative := fun h => Finset.disjoint_left.mp disjoint h member
      rw [Option.map_eq_none_iff, List.find?_eq_none] at absent
      exact absurd (by simpa using free) (absent c (List.mem_finRange c))
  · intro absent
    cases result : oneWitness b target a with
    | none => rfl
    | some K => exact absurd ⟨K, oneWitness_some b target a K result⟩ absent

/-- A reachable zero. -/
def zeroWitness (b : ℕ) (target : Channel n) (a : Raw n) : Option (Finset (Channel n)) :=
  if a.zero then some {target}
  else match (List.finRange n).find? (fun c => decide (c ∈ a.negative)) with
    | some m => some ({m} ∪ forced b target)
    | none =>
      if b = 1 then
        if ((List.finRange n).find? fun p => decide (p ∈ a.positive ∧ p ≠ target)).isSome then some {target}
        else none
      else match (List.finRange n).find? (fun p => decide (p ∈ a.positive)) with
        | none => none
        | some p => ((List.finRange n).find? fun c => decide (c ≠ p)).map fun c => {c}

theorem zeroWitness_some (b : ℕ) (target : Channel n) (a : Raw n) (K : Finset (Channel n))
    (returned : zeroWitness b target a = some K) : Admissible b target K ∧ ¬Holds a.decode K := by
  rw [holds_iff]
  unfold zeroWitness at returned
  split at returned
  next zero =>
    cases returned
    exact ⟨admissible_target b target, by simp [zero]⟩
  next =>
    split at returned
    next m found =>
      cases returned
      have member : m ∈ a.negative := by simpa using List.find?_some found
      refine ⟨admissible_union b target {m} (Finset.singleton_nonempty m), ?_⟩
      rintro ⟨_, _, disjoint⟩
      exact Finset.disjoint_left.mp disjoint member (by simp)
    next =>
      split at returned
      next one =>
        split at returned
        next some =>
          cases returned
          obtain ⟨p, found⟩ := Option.isSome_iff_exists.mp some
          have chosen := List.find?_some found
          simp only [decide_eq_true_eq] at chosen
          refine ⟨admissible_target b target, ?_⟩
          rintro ⟨_, positive, _⟩
          exact chosen.2 (Finset.mem_singleton.mp (positive chosen.1))
        next => simp at returned
      next notOne =>
        split at returned
        next => simp at returned
        next p found =>
          obtain ⟨c, other, rfl⟩ := Option.map_eq_some_iff.mp returned
          have present : p ∈ a.positive := by simpa using List.find?_some found
          have different : c ≠ p := by simpa using List.find?_some other
          refine ⟨⟨Finset.singleton_nonempty c, fun one => absurd one notOne⟩, ?_⟩
          rintro ⟨_, positive, _⟩
          exact different (Finset.mem_singleton.mp (positive present)).symm

theorem zeroWitness_none_iff (b : ℕ) (target : Channel n) (a : Raw n) :
    zeroWitness b target a = none ↔ ¬∃ K, Admissible b target K ∧ ¬Holds a.decode K := by
  constructor
  · intro absent ⟨K, eligible, falsity⟩
    rw [holds_iff] at falsity
    unfold zeroWitness at absent
    split at absent
    · simp at absent
    next zero =>
      have zeroFalse : a.zero = false := by simpa using zero
      split at absent
      · simp at absent
      next noNegative =>
        have negativeEmpty : ∀ c, c ∉ a.negative := by
          intro c member
          have := List.find?_eq_none.mp noNegative c (List.mem_finRange c)
          simp [member] at this
        have disjoint : Disjoint a.negative K := Finset.disjoint_left.mpr fun c h => absurd h (negativeEmpty c)
        have missing : ¬a.positive ⊆ K := fun positive => falsity ⟨zeroFalse, positive, disjoint⟩
        obtain ⟨p, present, outside⟩ := Finset.not_subset.mp missing
        split at absent
        next one =>
          have different : p ≠ target := fun h => outside (h ▸ eligible.2 one)
          split at absent
          · simp at absent
          next none =>
            have := List.find?_eq_none.mp (Option.not_isSome_iff_eq_none.mp none) p (List.mem_finRange p)
            simp [present, different] at this
        next notOne =>
          split at absent
          next none =>
            have := List.find?_eq_none.mp none p (List.mem_finRange p)
            simp [present] at this
          next q found =>
            obtain ⟨c, member⟩ := eligible.1
            have chosen : q ∈ a.positive := by simpa using List.find?_some found
            rw [Option.map_eq_none_iff, List.find?_eq_none] at absent
            by_cases same : c = q
            · -- every element differs from `q` fails, so the only channel is `q`;
              -- but `p ∉ K` and `c ∈ K`, so `p ≠ c = q`.
              have pDiff : p ≠ q := fun h => outside (h ▸ same ▸ member)
              have := absent p (List.mem_finRange p)
              simp [pDiff] at this
            · have := absent c (List.mem_finRange c)
              simp [same] at this
  · intro absent
    cases result : zeroWitness b target a with
    | none => rfl
    | some K => exact absurd ⟨K, zeroWitness_some b target a K result⟩ absent

/-- One root: change a healthy one to zero or a healthy zero to one. -/
def rootWitness (b : ℕ) (target : Channel n) (a : Raw n) : Option (Finset (Channel n)) :=
  if decide (Holds a.decode {target}) then zeroWitness b target a else oneWitness b target a

theorem rootWitness_some (b : ℕ) (target : Channel n) (a : Raw n) (K : Finset (Channel n))
    (returned : rootWitness b target a = some K) :
    Admissible b target K ∧ (Holds a.decode K ↔ ¬Holds a.decode {target}) := by
  unfold rootWitness at returned
  by_cases healthy : Holds a.decode {target}
  · simp only [healthy, decide_true, ite_true] at returned
    obtain ⟨eligible, falsity⟩ := zeroWitness_some b target a K returned
    exact ⟨eligible, by simp [falsity, healthy]⟩
  · simp only [healthy, decide_false, Bool.false_eq_true, ite_false] at returned
    obtain ⟨eligible, truth⟩ := oneWitness_some b target a K returned
    exact ⟨eligible, by simp [truth, healthy]⟩

theorem rootWitness_none_iff (b : ℕ) (target : Channel n) (a : Raw n) :
    rootWitness b target a = none ↔
      ¬∃ K, Admissible b target K ∧ (Holds a.decode K ↔ ¬Holds a.decode {target}) := by
  unfold rootWitness
  by_cases healthy : Holds a.decode {target}
  · simp only [healthy, decide_true, ite_true, zeroWitness_none_iff, not_true_eq_false, iff_false]
  · simp only [healthy, decide_false, Bool.false_eq_true, ite_false, oneWitness_none_iff,
      not_false_eq_true, iff_true]

/-- All outputs, read from the physical summaries. -/
def search (graph : DAG n) (b : ℕ) (target : Channel n) : Option (Finset (Channel n)) :=
  firstSuccess (fun root => rootWitness b target (summary graph root)) graph.roots

theorem summary_holds (graph : DAG n) (noOr : NoDisjunction graph) (root : Fin graph.nodeCount)
    (K : Finset (Channel n)) :
    Holds (summary graph root).decode K ↔ graph.eval (assignmentOfSet K) root = true := by
  rw [summary_decode]
  exact literalSummary_correct graph noOr K root

theorem search_some (graph : DAG n) (noOr : NoDisjunction graph) (b : ℕ) (target : Channel n)
    (K : Finset (Channel n)) (returned : search graph b target = some K) :
    Admissible b target K ∧ ∃ root ∈ graph.roots,
      graph.eval (assignmentOfSet K) root ≠ graph.eval (assignmentOfSet {target}) root := by
  obtain ⟨root, member, found⟩ := firstSuccess_some _ _ K returned
  obtain ⟨eligible, flips⟩ := rootWitness_some b target _ K found
  rw [summary_holds graph noOr, summary_holds graph noOr] at flips
  refine ⟨eligible, root, member, ?_⟩
  cases h : graph.eval (assignmentOfSet K) root <;>
    cases g : graph.eval (assignmentOfSet {target}) root <;> simp_all

theorem search_none_iff (graph : DAG n) (noOr : NoDisjunction graph) (b : ℕ) (target : Channel n) :
    search graph b target = none ↔
      ¬∃ root ∈ graph.roots, ∃ K, Admissible b target K ∧
        graph.eval (assignmentOfSet K) root ≠ graph.eval (assignmentOfSet {target}) root := by
  rw [search, firstSuccess_none_iff]
  constructor
  · rintro absent ⟨root, member, K, eligible, differs⟩
    apply (rootWitness_none_iff b target _).mp (absent root member)
    refine ⟨K, eligible, ?_⟩
    rw [summary_holds graph noOr, summary_holds graph noOr]
    cases h : graph.eval (assignmentOfSet K) root <;>
      cases g : graph.eval (assignmentOfSet {target}) root <;> simp_all
  · intro absent root member
    apply (rootWitness_none_iff b target _).mpr
    rintro ⟨K, eligible, flips⟩
    rw [summary_holds graph noOr, summary_holds graph noOr] at flips
    apply absent ⟨root, member, K, eligible, ?_⟩
    cases h : graph.eval (assignmentOfSet K) root <;>
      cases g : graph.eval (assignmentOfSet {target}) root <;> simp_all

end Controller.Extensions.LiteralWitness
