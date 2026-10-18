module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Extensions.Support
public import Controller.Extensions.Expansion
public import Controller.Decoder.Detect
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Data.List.Sublists

@[expose] public section

/-! Bounded-conjunction candidate families and exact guarded-expansion queries. -/
namespace Controller.Extensions.BoundedAnd
open Controller.Decoder Controller.Decoder.DAG
open scoped BigOperators

def supportCount (n k : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (min (k + 1) n + 1), n.choose j

def supports (n k : ℕ) : Finset (Finset (Channel n)) :=
  (Finset.range (min (k + 1) n + 1)).biUnion fun j => Finset.univ.powersetCard j

theorem mem_supports (S : Finset (Channel n)) : S ∈ supports n k ↔ S.card ≤ k + 1 := by
  simp only [supports, Finset.mem_biUnion, Finset.mem_range, Finset.mem_powersetCard]
  constructor
  · rintro ⟨j, hj, _, eq⟩
    omega
  · intro bound
    exact ⟨S.card, by have := Finset.card_le_univ S; simp only [Fintype.card_fin] at this; omega,
      Finset.subset_univ _, rfl⟩

theorem supports_card (n k : ℕ) : (supports n k).card = supportCount n k := by
  unfold supports supportCount
  rw [Finset.card_biUnion]
  · simp only [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  · intro i _ j _ ne
    apply Finset.disjoint_left.mpr
    intro S hi hj
    exact ne ((Finset.mem_powersetCard.mp hi).2.symm.trans (Finset.mem_powersetCard.mp hj).2)

/-- For fixed k, the support count is bounded by a polynomial of degree k+1. -/
theorem supportCount_polynomial (n k : ℕ) :
    supportCount n k ≤ (k + 2) * (n + 1) ^ (k + 1) := by
  unfold supportCount
  calc
    _ ≤ ∑ _j ∈ Finset.range (min (k + 1) n + 1), (n + 1) ^ (k + 1) := by
      apply Finset.sum_le_sum
      intro j hj
      have bound : j ≤ k + 1 := by have := Finset.mem_range.mp hj; omega
      exact (Nat.choose_le_pow n j).trans
        ((Nat.pow_le_pow_left (by omega) j).trans (Nat.pow_le_pow_right (by omega) bound))
    _ = (min (k + 1) n + 1) * (n + 1) ^ (k + 1) := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (by omega)

def candidate (b : ℕ) (target : Channel n) (S : Finset (Channel n)) : Finset (Channel n) :=
  if b = 1 then insert target S else S

def candidates (n k b : ℕ) (target : Channel n) : Finset (Finset (Channel n)) :=
  (supports n k).image (candidate b target)

theorem candidates_card (n k b : ℕ) (target : Channel n) :
    (candidates n k b target).card ≤ supportCount n k :=
  Finset.card_image_le.trans (supports_card n k).le

/-- Bounded supports are complete for the healthy-zero branch, including the
forced-target enlargement for one bus. -/
theorem true_iff_candidate (graph : DAG n) (k : ℕ) (bound : graph.liveAndCount ≤ k)
    (b : ℕ) (target : Channel n) (root : Fin graph.nodeCount) :
    (∃ K, Admissible b target K ∧ graph.eval (assignmentOfSet K) root = true) ↔
      ∃ K ∈ candidates n k b target,
        Admissible b target K ∧ graph.eval (assignmentOfSet K) root = true := by
  constructor
  · rintro ⟨K, admissible, truth⟩
    let S := graph.positiveSupport K root
    have count : S.card ≤ k + 1 :=
      (graph.positiveSupport_card_le K root).trans (Nat.add_le_add_right bound 1)
    refine ⟨candidate b target S, Finset.mem_image.mpr
      ⟨S, (mem_supports S).mpr count, rfl⟩, ?_, ?_⟩
    · by_cases one : b = 1
      · simp [candidate, one, Admissible]
      · exact ⟨by simpa [candidate, one] using graph.positiveSupport_nonempty K root truth,
          fun h => (one h).elim⟩
    · by_cases one : b = 1
      · simpa [candidate, one, S] using
          graph.positiveSupport_insert_target_true K root truth target (admissible.2 one)
      · simpa [candidate, one, S] using graph.positiveSupport_true K root truth
  · rintro ⟨K, _, admissible, truth⟩
    exact ⟨K, admissible, truth⟩

theorem false_iff_expansion (graph : DAG n) (a : Assignment n) (root : Fin graph.nodeCount) :
    graph.eval a root = false ↔
      ∃ selector : graph.Selector (graph.cone root),
        (graph.expansion (graph.cone root) selector).eval a root = false := by
  have identity := graph.cone_expansion_identity a root
  constructor
  · intro zero
    by_contra no
    have allTrue : ∀ selector : graph.Selector (graph.cone root),
        (graph.expansion (graph.cone root) selector).eval a root = true := by
      intro selector
      cases eq : (graph.expansion (graph.cone root) selector).eval a root with
      | false => exact (no ⟨selector, eq⟩).elim
      | true => rfl
    have := identity.mpr allTrue
    simp [zero] at this
  · rintro ⟨selector, zero⟩
    cases eq : graph.eval a root with
    | false => rfl
    | true => have := identity.mp eq selector; simp [zero] at this

noncomputable def expansionZero (graph : DAG n) (b : ℕ) (target : Channel n)
    (root : Fin graph.nodeCount) : Option (Finset (Channel n)) :=
  firstSuccess (fun selector : graph.Selector (graph.cone root) =>
    (graph.expansion (graph.cone root) selector).solveZero b target root ∅ ∅)
      Finset.univ.toList

theorem expansionZero_none_iff (graph : DAG n) (b : ℕ) (target : Channel n)
    (root : Fin graph.nodeCount) :
    expansionZero graph b target root = none ↔
      ¬ ∃ K, Admissible b target K ∧ graph.eval (assignmentOfSet K) root = false := by
  classical
  simp only [expansionZero, firstSuccess_none_iff, Finset.mem_toList, Finset.mem_univ,
    forall_true_left]
  constructor
  · intro none ⟨K, admissible, zero⟩
    obtain ⟨selector, value⟩ := (false_iff_expansion graph _ root).mp zero
    have h := ((graph.expansion (graph.cone root) selector).solveZero_none_iff
      (graph.expansion_guarded _ _) b target root ∅ ∅).mp (none selector)
    exact h ⟨K, admissible, by simp [ExtendsFixed], value⟩
  · intro none selector
    apply ((graph.expansion (graph.cone root) selector).solveZero_none_iff
      (graph.expansion_guarded _ _) b target root ∅ ∅).mpr
    rintro ⟨K, admissible, _, value⟩
    exact none ⟨K, admissible, (false_iff_expansion graph _ root).mpr ⟨selector, value⟩⟩

theorem expansionZero_some (graph : DAG n) (b : ℕ) (target : Channel n)
    (root : Fin graph.nodeCount) (K : Finset (Channel n))
    (returned : expansionZero graph b target root = some K) :
    Admissible b target K ∧ graph.eval (assignmentOfSet K) root = false := by
  classical
  obtain ⟨selector, _, result⟩ := firstSuccess_some _ _ K returned
  have sound := (graph.expansion (graph.cone root) selector).solveZero_some
    (graph.expansion_guarded _ _) b target root ∅ ∅ K result
  exact ⟨sound.1, (false_iff_expansion graph _ root).mpr ⟨selector, sound.2.2⟩⟩

theorem expansion_queries_le (graph : DAG n) (root : Fin graph.nodeCount)
    (k : ℕ) (bound : graph.liveAndCount ≤ k) :
    Fintype.card (graph.Selector (graph.cone root)) ≤ 2 ^ k := by
  apply graph.selector_count_le
  exact (Finset.card_le_card Finset.inter_subset_right).trans bound

/-- Depth-first support traversal. A saturated chosen is tested immediately;
no list of candidate supports is constructed. -/
def searchSmall {α β : Type*} [DecidableEq α] (query : Finset α → Option β) :
    ℕ → List α → Finset α → Option β
  | 0, _, chosen => query chosen
  | _ + 1, [], chosen => query chosen
  | r + 1, head :: tail, chosen =>
    match searchSmall query r tail (insert head chosen) with
    | some value => some value
    | none => searchSmall query (r + 1) tail chosen

theorem searchSmall_none_iff {α β : Type*} [DecidableEq α]
    (query : Finset α → Option β) (items : List α) (r : ℕ) (chosen : Finset α) :
    searchSmall query r items chosen = none ↔
      ∀ S ∈ items.sublists', S.length ≤ r → query (chosen ∪ S.toFinset) = none := by
  induction items generalizing r chosen with
  | nil => cases r <;> simp [searchSmall]
  | cons head tail ih =>
    cases r with
    | zero =>
      simp only [searchSmall]
      constructor
      · intro no S _ bound
        have empty : S = [] := List.length_eq_zero_iff.mp (by omega)
        simpa [empty] using no
      · intro no
        simpa using no [] (List.mem_sublists'.mpr (List.nil_sublist _)) (by simp)
    | succ r =>
      have union (S : List α) : insert head chosen ∪ S.toFinset =
          chosen ∪ (head :: S).toFinset := by ext; simp
      have combined : searchSmall query (r + 1) (head :: tail) chosen = none ↔
          searchSmall query r tail (insert head chosen) = none ∧
          searchSmall query (r + 1) tail chosen = none := by
        cases found : searchSmall query r tail (insert head chosen) <;> simp [searchSmall, found]
      rw [combined, ih, ih]
      simp only [List.sublists'_cons, List.mem_append, List.mem_map]
      constructor
      · rintro ⟨withHead, withoutHead⟩ S (member | ⟨T, member, rfl⟩) bound
        · exact withoutHead S member bound
        · simpa only [union] using withHead T member (by simpa using bound)
      · intro allSubsets
        constructor
        · intro S member bound
          rw [union]
          exact allSubsets (head :: S) (Or.inr ⟨S, member, rfl⟩) (by simpa using bound)
        · intro S member bound
          exact allSubsets S (Or.inl member) bound

theorem searchSmall_none_iff_finset {α β : Type*} [DecidableEq α]
    (query : Finset α → Option β) (items : List α) (unique : items.Nodup)
    (r : ℕ) (chosen : Finset α) :
    searchSmall query r items chosen = none ↔
      ∀ S ⊆ items.toFinset, S.card ≤ r → query (chosen ∪ S) = none := by
  rw [searchSmall_none_iff]
  constructor
  · intro absent S subset bound
    let selected := items.filter (fun x => decide (x ∈ S))
    have sets : selected.toFinset = S := by
      ext x
      simp only [selected, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
      exact ⟨fun h => h.2, fun h => ⟨List.mem_toFinset.mp (subset h), h⟩⟩
    have length : selected.length = S.card := by
      rw [← sets, List.toFinset_card_of_nodup (unique.filter _)]
    simpa only [sets] using absent selected
      (List.mem_sublists'.mpr (List.filter_sublist)) (length ▸ bound)
  · intro absent S member bound
    have sub := List.mem_sublists'.mp member
    exact absent S.toFinset
      (by intro x hx; exact List.mem_toFinset.mpr (sub.subset (List.mem_toFinset.mp hx)))
      ((List.toFinset_card_le S).trans bound)

theorem searchSmall_some {α β : Type*} [DecidableEq α]
    (query : Finset α → Option β) (items : List α) (r : ℕ) (chosen : Finset α) (value : β)
    (returned : searchSmall query r items chosen = some value) :
    ∃ S ∈ items.sublists', S.length ≤ r ∧ query (chosen ∪ S.toFinset) = some value := by
  induction items generalizing r chosen with
  | nil =>
    cases r <;> exact ⟨[], by simp, by simp, by simpa [searchSmall] using returned⟩
  | cons head tail ih =>
    cases r with
    | zero =>
      exact ⟨[], List.mem_sublists'.mpr (List.nil_sublist _), by simp,
        by simpa [searchSmall] using returned⟩
    | succ r =>
      cases found : searchSmall query r tail (insert head chosen) with
      | none =>
        obtain ⟨S, member, bound, result⟩ := ih (r + 1) chosen
          (by simpa [searchSmall, found] using returned)
        exact ⟨S, List.mem_sublists'.mpr ((List.mem_sublists'.mp member).cons head), bound, result⟩
      | some output =>
        have same : output = value := by simpa [searchSmall, found] using returned
        subst output
        obtain ⟨S, member, bound, result⟩ := ih r (insert head chosen) found
        refine ⟨head :: S, List.mem_sublists'.mpr ((List.mem_sublists'.mp member).cons_cons head),
          by simpa using bound, ?_⟩
        have sets : chosen ∪ (head :: S).toFinset = insert head chosen ∪ S.toFinset := by
          ext; simp
        simpa only [sets] using result

instance admissibleDecidable (b : ℕ) (target : Channel n) (K : Finset (Channel n)) :
    Decidable (Admissible b target K) := inferInstanceAs (Decidable (K.Nonempty ∧ (b = 1 → target ∈ K)))

/-- A support is evaluated once for all healthy-zero observations. -/
def supportQuery (graph : DAG n) (b : ℕ) (target : Channel n)
    (healthy : Fin graph.nodeCount → Bool) (S : Finset (Channel n)) :
    Option (Finset (Channel n)) :=
  let K := candidate b target S
  let values := graph.evalTable (assignmentOfSet K)
  if Admissible b target K ∧ graph.roots.any (fun root => !healthy root && values root) then
    some K else none

theorem supportQuery_none_iff (graph : DAG n) (b : ℕ) (target : Channel n)
    (healthy : Fin graph.nodeCount → Bool) (S : Finset (Channel n)) :
    supportQuery graph b target healthy S = none ↔
      ¬ (Admissible b target (candidate b target S) ∧ ∃ root ∈ graph.roots,
        healthy root = false ∧ graph.eval (assignmentOfSet (candidate b target S)) root = true) := by
  simp [supportQuery, DAG.evalTable_eq_eval, List.any_eq_true]

theorem supportQuery_some (graph : DAG n) (b : ℕ) (target : Channel n)
    (healthy : Fin graph.nodeCount → Bool) (S K : Finset (Channel n))
    (returned : supportQuery graph b target healthy S = some K) :
    Admissible b target K ∧ ∃ root ∈ graph.roots,
      healthy root = false ∧ graph.eval (assignmentOfSet K) root = true := by
  unfold supportQuery at returned
  dsimp only at returned
  split at returned
  next yes =>
    have eq := Option.some.inj returned
    subst K
    simpa [DAG.evalTable_eq_eval, List.any_eq_true] using yes
  next no => simp at returned

def scanSupports (graph : DAG n) (k b : ℕ) (target : Channel n)
    (healthy : Fin graph.nodeCount → Bool) : Option (Finset (Channel n)) :=
  searchSmall (supportQuery graph b target healthy) (k + 1) (List.finRange n) ∅

theorem scanSupports_none_iff (graph : DAG n) (k : ℕ) (bound : graph.liveAndCount ≤ k)
    (b : ℕ) (target : Channel n) (healthy : Fin graph.nodeCount → Bool) :
    scanSupports graph k b target healthy = none ↔
      ¬ ∃ root ∈ graph.roots, healthy root = false ∧ ∃ K, Admissible b target K ∧
        graph.eval (assignmentOfSet K) root = true := by
  unfold scanSupports
  rw [searchSmall_none_iff_finset _ _ (List.nodup_finRange n)]
  simp only [Finset.empty_union]
  constructor
  · intro absent ⟨root, member, zero, K, eligible, value⟩
    obtain ⟨L, inCandidates, admissible, truth⟩ :=
      (true_iff_candidate graph k bound b target root).mp ⟨K, eligible, value⟩
    obtain ⟨S, inSupports, rfl⟩ := Finset.mem_image.mp inCandidates
    exact (supportQuery_none_iff graph b target healthy S).mp
      (absent S (by simp) ((mem_supports S).mp inSupports))
      ⟨admissible, root, member, zero, truth⟩
  · intro absent S _ _
    apply (supportQuery_none_iff graph b target healthy S).mpr
    rintro ⟨admissible, root, member, zero, truth⟩
    exact absent ⟨root, member, zero, candidate b target S, admissible, truth⟩

theorem scanSupports_some (graph : DAG n) (k b : ℕ) (target : Channel n)
    (healthy : Fin graph.nodeCount → Bool) (K : Finset (Channel n))
    (returned : scanSupports graph k b target healthy = some K) :
    Admissible b target K ∧ ∃ root ∈ graph.roots,
      healthy root = false ∧ graph.eval (assignmentOfSet K) root = true := by
  obtain ⟨S, _, _, found⟩ := searchSmall_some _ _ _ _ K returned
  exact supportQuery_some graph b target healthy S.toFinset K (by simpa using found)

private def evalAt (graph : DAG n) (a : Assignment n) (index : ℕ) : Bool :=
  if h : index < graph.nodeCount then graph.eval a ⟨index, h⟩ else false

/-- A Boolean set of stored AND identities chooses right operands. -/
@[reducible] def resolved (graph : DAG n) (right : Finset (Fin graph.nodeCount)) : DAG n where
  nodeCount := graph.nodeCount
  node i := (graph.node i).resolve (decide (i ∈ right))
  roots := graph.roots

theorem resolved_guarded (graph : DAG n) (right : Finset (Fin graph.nodeCount)) :
    (resolved graph right).Guarded := fun _ => Gate.resolve_guarded _ _

theorem resolved_eq_expansion (graph : DAG n) (right : Finset (Fin graph.nodeCount)) :
    resolved graph right = graph.expansion Finset.univ (fun i => decide (i.val ∈ right)) := by
  have nodes : (fun i : Fin graph.nodeCount => (graph.node i).resolve (decide (i ∈ right))) =
      (fun i => (graph.node i).resolve
        (graph.selectedChoice Finset.univ (fun i => decide (i.val ∈ right)) i)) := by
    funext i
    by_cases isAnd : i ∈ graph.liveAndNodes
    · simp [DAG.selectedChoice, isAnd]
    · have notAnd : (graph.node i).isLiveAnd ≠ true := by simpa [DAG.liveAndNodes] using isAnd
      cases gate : graph.node i <;> simp_all [Gate.resolve, Gate.isLiveAnd]
  exact congrArg (fun node => DAG.mk graph.nodeCount node graph.roots) nodes

theorem expansion_as_resolved (graph : DAG n) (selector : graph.Selector Finset.univ) :
    ∃ right ⊆ graph.liveAndNodes, resolved graph right = graph.expansion Finset.univ selector := by
  classical
  let right := graph.liveAndNodes.filter fun i => graph.selectedChoice Finset.univ selector i = true
  refine ⟨right, Finset.filter_subset _ _, ?_⟩
  have nodes : (fun i : Fin graph.nodeCount => (graph.node i).resolve (decide (i ∈ right))) =
      (fun i => (graph.node i).resolve (graph.selectedChoice Finset.univ selector i)) := by
    funext i
    by_cases isAnd : i ∈ graph.liveAndNodes
    · have choices : decide (i ∈ right) = graph.selectedChoice Finset.univ selector i := by
        simp only [right, Finset.mem_filter, isAnd, true_and]
        cases graph.selectedChoice Finset.univ selector i <;> decide
      rw [choices]
    · have notAnd : (graph.node i).isLiveAnd ≠ true := by simpa [DAG.liveAndNodes] using isAnd
      cases gate : graph.node i <;> simp_all [Gate.resolve, Gate.isLiveAnd]
  exact congrArg (fun node => DAG.mk graph.nodeCount node graph.roots) nodes

def andIdentities (graph : DAG n) : List (Fin graph.nodeCount) :=
  (List.finRange graph.nodeCount).filter fun i => (graph.node i).isLiveAnd

theorem andIdentities_toFinset (graph : DAG n) :
    (andIdentities graph).toFinset = graph.liveAndNodes := by
  ext i
  simp [andIdentities, DAG.liveAndNodes]

theorem andIdentities_length (graph : DAG n) :
    (andIdentities graph).length = graph.liveAndCount := by
  rw [DAG.liveAndCount, ← andIdentities_toFinset]
  exact (List.toFinset_card_of_nodup ((List.nodup_finRange _).filter _)).symm

def resolvedZeroQuery (graph : DAG n) (b : ℕ) (target : Channel n)
    (root : Fin graph.nodeCount) (right : Finset (Fin graph.nodeCount)) :
    Option (Finset (Channel n)) :=
  (resolved graph right).solveZero b target root ∅ ∅

/-- Depth-first selector generation retains one chosen identity set at a time. -/
def scanExpansions (graph : DAG n) (b : ℕ) (target : Channel n)
    (root : Fin graph.nodeCount) : Option (Finset (Channel n)) :=
  searchSmall (resolvedZeroQuery graph b target root)
    graph.liveAndCount (andIdentities graph) ∅

theorem scanExpansions_some (graph : DAG n) (b : ℕ) (target : Channel n)
    (root : Fin graph.nodeCount) (K : Finset (Channel n))
    (returned : scanExpansions graph b target root = some K) :
    Admissible b target K ∧ graph.eval (assignmentOfSet K) root = false := by
  obtain ⟨S, _, _, found⟩ := searchSmall_some _ _ _ _ K returned
  have found' : resolvedZeroQuery graph b target root S.toFinset = some K := by
    simpa only [Finset.empty_union] using found
  have sound := (resolved graph S.toFinset).solveZero_some (resolved_guarded graph _)
    b target root ∅ ∅ K found'
  refine ⟨sound.1, ?_⟩
  have zero := sound.2.2
  have transported := congrArg (fun g => evalAt g (assignmentOfSet K) root.val)
    (resolved_eq_expansion graph S.toFinset)
  have evaluation : (resolved graph S.toFinset).eval (assignmentOfSet K) root =
      (graph.expansion Finset.univ (fun i => decide (i.val ∈ S.toFinset))).eval
        (assignmentOfSet K) root := by
    dsimp only [evalAt, resolved, DAG.expansion] at transported
    simpa only [dite_eq_left root.isLt] using transported
  rw [evaluation] at zero
  cases value : graph.eval (assignmentOfSet K) root with
  | false => rfl
  | true =>
    have truth := graph.true_implies_expansion_true Finset.univ
      (fun i => decide (i.val ∈ S.toFinset)) _ root value
    simp [zero] at truth

theorem scanExpansions_none_iff (graph : DAG n) (b : ℕ) (target : Channel n)
    (root : Fin graph.nodeCount) :
    scanExpansions graph b target root = none ↔
      ¬ ∃ K, Admissible b target K ∧ graph.eval (assignmentOfSet K) root = false := by
  classical
  unfold scanExpansions
  rw [searchSmall_none_iff_finset _ (andIdentities graph)
    (by exact (List.nodup_finRange _).filter _)]
  simp only [andIdentities_toFinset, Finset.empty_union]
  constructor
  · intro absent ⟨K, eligible, zero⟩
    obtain ⟨selector, preserves⟩ := graph.exists_global_preserving_selector (assignmentOfSet K)
    obtain ⟨right, subset, eq⟩ := expansion_as_resolved graph selector
    have none := absent right subset (Finset.card_le_card subset)
    apply ((resolved graph right).solveZero_none_iff (resolved_guarded graph right)
      b target root ∅ ∅).mp none
    have transported := congrArg (fun g => evalAt g (assignmentOfSet K) root.val) eq
    have evaluation : (resolved graph right).eval (assignmentOfSet K) root =
        (graph.expansion Finset.univ selector).eval (assignmentOfSet K) root := by
      dsimp only [evalAt, resolved, DAG.expansion] at transported
      simpa only [dite_eq_left root.isLt] using transported
    exact ⟨K, eligible, by simp [ExtendsFixed], by rw [evaluation, preserves, zero]⟩
  · intro absent right _ _
    apply ((resolved graph right).solveZero_none_iff (resolved_guarded graph right)
      b target root ∅ ∅).mpr
    rintro ⟨K, eligible, _, zero⟩
    have transported := congrArg (fun g => evalAt g (assignmentOfSet K) root.val)
      (resolved_eq_expansion graph right)
    have evaluation : (resolved graph right).eval (assignmentOfSet K) root =
        (graph.expansion Finset.univ (fun i => decide (i.val ∈ right))).eval
          (assignmentOfSet K) root := by
      dsimp only [evalAt, resolved, DAG.expansion] at transported
      simpa only [dite_eq_left root.isLt] using transported
    rw [evaluation] at zero
    cases value : graph.eval (assignmentOfSet K) root with
    | false => exact absent ⟨K, eligible, value⟩
    | true =>
      have truth := graph.true_implies_expansion_true Finset.univ
        (fun i => decide (i.val ∈ right)) _ root value
      simp [zero] at truth

def zeroQuery (graph : DAG n) (b : ℕ) (target : Channel n)
    (healthy : Fin graph.nodeCount → Bool) (root : Fin graph.nodeCount) :
    Option (Finset (Channel n)) :=
  if healthy root then scanExpansions graph b target root else none

theorem zeroQuery_none_iff (graph : DAG n) (b : ℕ) (target : Channel n)
    (healthy : Fin graph.nodeCount → Bool) (root : Fin graph.nodeCount) :
    zeroQuery graph b target healthy root = none ↔
      ¬ (healthy root = true ∧ ∃ K, Admissible b target K ∧
        graph.eval (assignmentOfSet K) root = false) := by
  cases value : healthy root <;> simp [zeroQuery, value, scanExpansions_none_iff]

def scanCandidates (graph : DAG n) (k b : ℕ) (target : Channel n)
    (healthy : Fin graph.nodeCount → Bool) : Option (Finset (Channel n)) :=
  if graph.roots.all healthy then none else scanSupports graph k b target healthy

theorem scanCandidates_some (graph : DAG n) (k b : ℕ) (target : Channel n)
    (healthy : Fin graph.nodeCount → Bool) (K : Finset (Channel n))
    (returned : scanCandidates graph k b target healthy = some K) :
    Admissible b target K ∧ ∃ root ∈ graph.roots,
      healthy root = false ∧ graph.eval (assignmentOfSet K) root = true := by
  unfold scanCandidates at returned
  split at returned
  · simp at returned
  · exact scanSupports_some graph k b target healthy K returned

theorem scanCandidates_none_iff (graph : DAG n) (k : ℕ) (bound : graph.liveAndCount ≤ k)
    (b : ℕ) (target : Channel n) (healthy : Fin graph.nodeCount → Bool) :
    scanCandidates graph k b target healthy = none ↔
      ¬ ∃ root ∈ graph.roots, healthy root = false ∧ ∃ K, Admissible b target K ∧
        graph.eval (assignmentOfSet K) root = true := by
  unfold scanCandidates
  split
  next allHealthy =>
    simp only [true_iff]
    rintro ⟨root, member, zero, _⟩
    have one := List.all_eq_true.mp allHealthy root member
    simp [zero] at one
  next notAll => exact scanSupports_none_iff graph k bound b target healthy

/-- The healthy-zero traversal shares each value table across all observations.
Healthy-one observations search consistently resolved guarded DAGs. -/
def detectSet (graph : DAG n) (k b : ℕ) (target : Channel n) (drive : Bool) :
    Option (Finset (Channel n)) :=
  if drive then
    let healthy := graph.evalTable (assignmentOfSet {target})
    match scanCandidates graph k b target healthy with
    | some K => some K
    | none => firstSuccess (zeroQuery graph b target healthy) graph.roots
  else none

@[simp] theorem detectSet_drive_false (graph : DAG n) (k b : ℕ) (target : Channel n) :
    detectSet graph k b target false = none := by simp [detectSet]

theorem detectSet_some (graph : DAG n) (k b : ℕ) (target : Channel n)
    (drive : Bool) (K : Finset (Channel n))
    (returned : detectSet graph k b target drive = some K) :
    drive = true ∧ Admissible b target K ∧ ∃ root ∈ graph.roots,
      graph.eval (assignmentOfSet K) root ≠ graph.eval (assignmentOfSet {target}) root := by
  cases drive with
  | false => simp [detectSet] at returned
  | true =>
    simp only [detectSet, ite_true, DAG.evalTable_eq_eval] at returned
    cases scan : scanCandidates graph k b target (graph.eval (assignmentOfSet {target})) with
    | some found =>
      rw [scan] at returned
      have eq := Option.some.inj returned
      subst found
      obtain ⟨eligible, root, member, healthy, faulty⟩ := scanCandidates_some graph k b target _ K scan
      exact ⟨rfl, eligible, root, member, by rw [healthy, faulty]; decide⟩
    | none =>
      rw [scan] at returned
      obtain ⟨root, member, value⟩ := firstSuccess_some _ _ K returned
      unfold zeroQuery at value
      split at value
      next healthy =>
        obtain ⟨eligible, faulty⟩ := scanExpansions_some graph b target root K value
        exact ⟨rfl, eligible, root, member, by rw [healthy, faulty]; decide⟩
      next no => simp at value

theorem detectSet_none_iff (graph : DAG n) (k : ℕ) (bound : graph.liveAndCount ≤ k)
    (b : ℕ) (target : Channel n) (drive : Bool) :
    detectSet graph k b target drive = none ↔
      ¬ (drive = true ∧ ∃ root ∈ graph.roots, ∃ K, Admissible b target K ∧
        graph.eval (assignmentOfSet K) root ≠ graph.eval (assignmentOfSet {target}) root) := by
  cases drive with
  | false => simp [detectSet]
  | true =>
    simp only [detectSet, ite_true, DAG.evalTable_eq_eval, true_and]
    cases scan : scanCandidates graph k b target (graph.eval (assignmentOfSet {target})) with
    | some K =>
      simp only [Option.some_ne_none, false_iff, not_not]
      obtain ⟨eligible, root, member, healthy, faulty⟩ := scanCandidates_some graph k b target _ K scan
      exact ⟨root, member, K, eligible, by rw [healthy, faulty]; decide⟩
    | none =>
      rw [firstSuccess_none_iff]
      have absent := (scanCandidates_none_iff graph k bound b target _).mp scan
      constructor
      · intro zeros ⟨root, member, K, eligible, differs⟩
        cases healthy : graph.eval (assignmentOfSet {target}) root with
        | false =>
          have faulty : graph.eval (assignmentOfSet K) root = true := by
            cases value : graph.eval (assignmentOfSet K) root <;> simp_all
          exact absent ⟨root, member, healthy, K, eligible, faulty⟩
        | true =>
          have faulty : graph.eval (assignmentOfSet K) root = false := by
            cases value : graph.eval (assignmentOfSet K) root <;> simp_all
          exact (zeroQuery_none_iff graph b target _ root).mp (zeros root member)
            ⟨healthy, K, eligible, faulty⟩
      · intro absent root member
        apply (zeroQuery_none_iff graph b target _ root).mpr
        rintro ⟨healthy, K, eligible, faulty⟩
        exact absent ⟨root, member, K, eligible, by rw [healthy, faulty]; decide⟩

end Controller.Extensions.BoundedAnd
