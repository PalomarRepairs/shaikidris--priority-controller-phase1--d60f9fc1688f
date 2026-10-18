module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Boundaries.CriticalSets
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Adaptive value-query detection

A decision tree receives only Boolean values at supplied eligible sets.
Its query list depends on preceding answers. The lower bound concerns this
access model: syntax inspection is not an operation of these trees.
-/

namespace Controller.Boundaries

variable {n : ℕ}

/-- The undetectable all-positive OR. Empty inputs receive false. -/
def bottomValue (L : Finset (Channel n)) : Bool := decide L.Nonempty

/-- The all-positive OR supplied as a qualifier observation. -/
def bottomObservation : Fin 1 → Assignment n → Bool := fun _ assignment =>
  bottomValue (setOfAssignment assignment)

/-- The baseline decoder is undetectable on the actual physical bridge image. -/
theorem bottom_physical_undetectable {b : ℕ} (bridge : Physical.Bridge n)
    (hb : 0 < b) :
    ¬ Physical.BridgeDetectable (b := b) bridge true (bottomObservation (n := n)) := by
  rw [Physical.bridge_detectable_iff bridge hb]
  rintro ⟨_, L, admissible, index, changed⟩
  simp [bottomObservation, bottomValue, admissible.1] at changed

/-- A finite deterministic adaptive value-query decision tree. -/
inductive QueryTree (Query : Type*) where
  | answer (detectable : Bool)
  | ask (query : Query) (onFalse onTrue : QueryTree Query)

namespace QueryTree

variable {Query : Type*}

/-- Decision reached by following the supplied oracle's answers. -/
def run (oracle : Query → Bool) : QueryTree Query → Bool
  | .answer result => result
  | .ask query onFalse onTrue =>
    if oracle query then onTrue.run oracle else onFalse.run oracle

/-- The actual ordered query transcript, retaining repeated queries. -/
def queries (oracle : Query → Bool) : QueryTree Query → List Query
  | .answer _ => []
  | .ask query onFalse onTrue =>
    query :: (if oracle query then onTrue.queries oracle else onFalse.queries oracle)

/-- Maximum number of value queries on a root-to-answer path. -/
def budget : QueryTree Query → ℕ
  | .answer _ => 0
  | .ask _ onFalse onTrue => 1 + max onFalse.budget onTrue.budget

theorem queries_length_le (tree : QueryTree Query) (oracle : Query → Bool) :
    (tree.queries oracle).length ≤ tree.budget := by
  induction tree with
  | answer result => simp [queries, budget]
  | ask query onFalse onTrue ihFalse ihTrue =>
    cases h : oracle query <;> simp [queries, budget, h]
    · omega
    · omega

/-- Agreement at queries on the first transcript fixes the entire adaptive run. -/
theorem run_eq_of_transcript_agreement (tree : QueryTree Query)
    (first second : Query → Bool)
    (agreement : ∀ query ∈ tree.queries first, first query = second query) :
    tree.run first = tree.run second := by
  induction tree with
  | answer result => rfl
  | ask query onFalse onTrue ihFalse ihTrue =>
    have head := agreement query (by simp [queries])
    cases h : first query
    · have tail : ∀ q ∈ onFalse.queries first, first q = second q := by
        intro q hq
        exact agreement q (by simp [queries, h, hq])
      simpa [run, h, ← head] using ihFalse tail
    · have tail : ∀ q ∈ onTrue.queries first, first q = second q := by
        intro q hq
        exact agreement q (by simp [queries, h, hq])
      simpa [run, h, ← head] using ihTrue tail

end QueryTree

/-- The image-query promise can be imposed on every branch, independently of
which branch a particular oracle takes. -/
def QueriesAdmissible (b : ℕ) (t : Channel n) :
    QueryTree (Finset (Channel n)) → Prop
  | .answer _ => True
  | .ask K onFalse onTrue =>
    Admissible b t K ∧ QueriesAdmissible b t onFalse ∧ QueriesAdmissible b t onTrue

/-- All behavior trees with at most the given number of queries. Finite
query domains give a finite space of behaviors, even for adaptive algorithms. -/
def BoundedStrategy (Query : Type) : ℕ → Type
  | 0 => Bool
  | r + 1 => Bool ⊕ (Query × BoundedStrategy Query r × BoundedStrategy Query r)

instance boundedStrategyFintype (Query : Type) [Fintype Query] :
    (r : ℕ) → Fintype (BoundedStrategy Query r)
  | 0 => inferInstanceAs (Fintype Bool)
  | r + 1 =>
    letI := boundedStrategyFintype Query r
    inferInstanceAs
      (Fintype (Bool ⊕ (Query × BoundedStrategy Query r × BoundedStrategy Query r)))

namespace BoundedStrategy

variable {Query : Type}

/-- Forget only the depth bound; preserve all queries and branches. -/
def toTree : {r : ℕ} → BoundedStrategy Query r → QueryTree Query
  | 0, result => .answer result
  | _ + 1, .inl result => .answer result
  | _ + 1, .inr (query, onFalse, onTrue) => .ask query onFalse.toTree onTrue.toTree

theorem toTree_budget_le : ∀ {r : ℕ} (strategy : BoundedStrategy Query r),
    strategy.toTree.budget ≤ r := by
  intro r
  induction r with
  | zero => intro strategy; simp [toTree, QueryTree.budget]
  | succ r ih =>
    intro strategy
    rcases strategy with result | ⟨query, onFalse, onTrue⟩
    · simp [toTree, QueryTree.budget]
    · have hf := ih onFalse
      have ht := ih onTrue
      simp only [toTree, QueryTree.budget]
      omega

/-- Every deterministic behavior with the stated worst-case budget has an
exact bounded representation. Fixing random coins therefore selects an
element of this finite behavior space. -/
theorem represents (r : ℕ) (tree : QueryTree Query) (bound : tree.budget ≤ r) :
    ∃ strategy : BoundedStrategy Query r, strategy.toTree = tree := by
  induction r generalizing tree with
  | zero =>
    cases tree with
    | answer result => exact ⟨result, rfl⟩
    | ask query onFalse onTrue => simp [QueryTree.budget] at bound
  | succ r ih =>
    cases tree with
    | answer result => exact ⟨.inl result, rfl⟩
    | ask query onFalse onTrue =>
      have hf : onFalse.budget ≤ r := by simp only [QueryTree.budget] at bound; omega
      have ht : onTrue.budget ≤ r := by simp only [QueryTree.budget] at bound; omega
      obtain ⟨sf, hsf⟩ := ih onFalse hf
      obtain ⟨st, hst⟩ := ih onTrue ht
      exact ⟨.inr (query, sf, st), by simp [toTree, hsf, hst]⟩

end BoundedStrategy

/-- A hidden decoder differs from the all-positive OR only at its nonempty set. -/
theorem criticalValue_eq_bottom_of_ne (K L : Finset (Channel n))
    (hne : L ≠ K) : criticalValue K L = bottomValue L := by
  classical
  by_cases hL : L.Nonempty
  · have hz : criticalValue K L ≠ false := by
      intro hz
      exact hne ((criticalValue_nonempty K L hL).mp hz)
    cases he : criticalValue K L <;> simp_all [bottomValue]
  · have he : L = ∅ := Finset.not_nonempty_iff_eq_empty.mp hL
    subst L
    simp [bottomValue]

/-- If the hidden set is absent from the baseline transcript, adaptation cannot
distinguish its decoder from the undetectable baseline. -/
theorem hidden_indistinguishable (tree : QueryTree (Finset (Channel n)))
    (K : Finset (Channel n)) (unqueried : K ∉ tree.queries bottomValue) :
    tree.run (criticalValue K) = tree.run bottomValue := by
  apply Eq.symm
  apply tree.run_eq_of_transcript_agreement
  intro L hL
  exact (criticalValue_eq_bottom_of_ne K L (fun equation =>
    unqueried (equation ▸ hL))).symm

/-- Correct deterministic detection on the precise hidden-set promise family. -/
def CorrectOnCriticalFamily (tree : QueryTree (Finset (Channel n)))
    (b : ℕ) (t : Channel n) : Prop :=
  tree.run bottomValue = false ∧
    ∀ K ∈ criticalSets b t, tree.run (criticalValue K) = true

/-- Every hidden critical set must occur on the baseline transcript. -/
theorem criticalSets_subset_queries (tree : QueryTree (Finset (Channel n)))
    (b : ℕ) (t : Channel n) (correct : CorrectOnCriticalFamily tree b t) :
    criticalSets b t ⊆ (tree.queries bottomValue).toFinset := by
  classical
  intro K hK
  simp only [List.mem_toFinset]
  by_contra unqueried
  have indistinguishable := hidden_indistinguishable tree K unqueried
  rw [correct.1, correct.2 K hK] at indistinguishable
  contradiction

/-- Exact worst-case bound, witnessed by the undetectable decoder transcript. -/
theorem deterministic_queries_lower_bound (tree : QueryTree (Finset (Channel n)))
    (b : ℕ) (t : Channel n) (correct : CorrectOnCriticalFamily tree b t) :
    (criticalSets b t).card ≤ (tree.queries bottomValue).length := by
  classical
  exact (Finset.card_le_card (criticalSets_subset_queries tree b t correct)).trans
    (List.toFinset_card_le _)

theorem deterministic_budget_lower_bound (tree : QueryTree (Finset (Channel n)))
    (b : ℕ) (t : Channel n) (correct : CorrectOnCriticalFamily tree b t) :
    (criticalSets b t).card ≤ tree.budget :=
  (deterministic_queries_lower_bound tree b t correct).trans (tree.queries_length_le _)

theorem deterministic_one_bus (tree : QueryTree (Finset (Channel n)))
    (t : Channel n) (correct : CorrectOnCriticalFamily tree 1 t) :
    2 ^ (n - 1) - 1 ≤ tree.budget := by
  simpa only [criticalSets_card_one] using deterministic_budget_lower_bound tree 1 t correct

theorem deterministic_many_buses (tree : QueryTree (Finset (Channel n)))
    (b : ℕ) (hb : 2 ≤ b) (t : Channel n) (correct : CorrectOnCriticalFamily tree b t) :
    2 ^ n - 2 ≤ tree.budget := by
  simpa only [criticalSets_card_many b hb] using
    deterministic_budget_lower_bound tree b t correct

/-- Probability-free score for the source's balanced hard distribution,
scaled by twice the number of hidden decoders. -/
noncomputable def hardScore (tree : QueryTree (Finset (Channel n)))
    (b : ℕ) (t : Channel n) : ℝ :=
  (criticalSets b t).card * (if tree.run bottomValue = false then 1 else 0) +
    ∑ K ∈ criticalSets b t, if tree.run (criticalValue K) = true then (1 : ℝ) else 0

/-- A baseline-rejecting tree succeeds only at hidden sets it actually queries. -/
theorem successes_subset_queries (tree : QueryTree (Finset (Channel n)))
    (b : ℕ) (t : Channel n) (rejects : tree.run bottomValue = false) :
    (criticalSets b t).filter (fun K => tree.run (criticalValue K) = true) ⊆
      (tree.queries bottomValue).toFinset := by
  classical
  intro K hK
  have success := (Finset.mem_filter.mp hK).2
  simp only [List.mem_toFinset]
  by_contra unqueried
  have same := hidden_indistinguishable tree K unqueried
  rw [rejects, success] at same
  contradiction

/-- Exact deterministic success bound before averaging over random coins. -/
theorem hardScore_le (tree : QueryTree (Finset (Channel n)))
    (b : ℕ) (t : Channel n) (r : ℕ) (budget : tree.budget ≤ r) :
    hardScore tree b t ≤ (criticalSets b t).card + r := by
  classical
  unfold hardScore
  rw [Finset.sum_boole]
  by_cases rejects : tree.run bottomValue = false
  · rw [ite_eq_left rejects, mul_one]
    have count := (Finset.card_le_card (successes_subset_queries tree b t rejects)).trans
      ((List.toFinset_card_le _).trans ((tree.queries_length_le _).trans budget))
    have realCount :
        (((criticalSets b t).filter (fun K => tree.run (criticalValue K) = true)).card : ℝ)
          ≤ r := by exact_mod_cast count
    linarith
  · rw [ite_eq_right rejects, mul_zero, zero_add]
    have count := Finset.card_le_card
      (Finset.filter_subset (fun K => tree.run (criticalValue K) = true) (criticalSets b t))
    have realCount :
        (((criticalSets b t).filter (fun K => tree.run (criticalValue K) = true)).card : ℝ)
          ≤ (criticalSets b t).card := by exact_mod_cast count
    have hr : (0 : ℝ) ≤ r := by positivity
    linarith

/-- A finite probability mixture of arbitrary adaptive trees. The individual
trees may have different shapes; the bound is a worst-case query budget. -/
theorem randomized_mixture_lower_bound {Coins : Type*} [Fintype Coins]
    (trees : Coins → QueryTree (Finset (Channel n))) (weight : Coins → ℝ)
    (nonnegative : ∀ coin, 0 ≤ weight coin) (normalized : ∑ coin, weight coin = 1)
    (b : ℕ) (t : Channel n) (r : ℕ) (budget : ∀ coin, (trees coin).budget ≤ r)
    (bottomCorrect : (2 / 3 : ℝ) ≤
      ∑ coin, weight coin * (if (trees coin).run bottomValue = false then 1 else 0))
    (hiddenCorrect : ∀ K ∈ criticalSets b t, (2 / 3 : ℝ) ≤
      ∑ coin, weight coin * (if (trees coin).run (criticalValue K) = true then 1 else 0)) :
    (criticalSets b t).card ≤ 3 * r := by
  classical
  have upper : (∑ coin, weight coin * hardScore (trees coin) b t) ≤
      (criticalSets b t).card + r := by
    calc
      _ ≤ ∑ coin, weight coin * ((criticalSets b t).card + r) :=
        Finset.sum_le_sum (fun coin _ => mul_le_mul_of_nonneg_left
          (hardScore_le (trees coin) b t r (budget coin)) (nonnegative coin))
      _ = _ := by rw [← Finset.sum_mul, normalized, one_mul]
  have hiddenLower : (criticalSets b t).card * (2 / 3 : ℝ) ≤
      ∑ K ∈ criticalSets b t, ∑ coin, weight coin *
        (if (trees coin).run (criticalValue K) = true then 1 else 0) := by
    simpa using Finset.sum_le_sum hiddenCorrect
  have bottomLower := mul_le_mul_of_nonneg_left bottomCorrect
    (by positivity : (0 : ℝ) ≤ (criticalSets b t).card)
  have rearrange : (∑ coin, weight coin * hardScore (trees coin) b t) =
      (criticalSets b t).card *
        (∑ coin, weight coin * (if (trees coin).run bottomValue = false then 1 else 0)) +
      ∑ K ∈ criticalSets b t, ∑ coin, weight coin *
        (if (trees coin).run (criticalValue K) = true then 1 else 0) := by
    simp only [hardScore, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    · apply Finset.sum_congr rfl
      intro coin _
      ring
    · exact Finset.sum_comm
  rw [rearrange] at upper
  have realBound : ((criticalSets b t).card : ℝ) ≤ 3 * (r : ℝ) := by linarith
  exact_mod_cast realBound

/-- A randomized algorithm in the bounded value-query model is an arbitrary
probability law on the complete finite space of adaptive behaviors. Weights
are real probabilities, not frequencies of a finite experiment. -/
structure RandomizedQueryAlgorithm (Query : Type) [Fintype Query] (r : ℕ) where
  probability : BoundedStrategy Query r → ℝ
  nonnegative : ∀ strategy, 0 ≤ probability strategy
  normalized : ∑ strategy, probability strategy = 1

namespace RandomizedQueryAlgorithm

variable {r : ℕ}

/-- Correct-answer probability for a particular value oracle. -/
noncomputable def successProbability
    (algorithm : RandomizedQueryAlgorithm (Finset (Channel n)) r)
    (oracle : Finset (Channel n) → Bool) (correct : Bool) : ℝ :=
  ∑ strategy, algorithm.probability strategy *
    (if strategy.toTree.run oracle = correct then 1 else 0)

/-- The source's randomized lower bound, with its exact constant: worst-case
error at most one third implies at least one third of the hidden-family size
in the worst-case query budget. -/
theorem lower_bound (algorithm : RandomizedQueryAlgorithm (Finset (Channel n)) r)
    (b : ℕ) (t : Channel n)
    (bottomCorrect : (2 / 3 : ℝ) ≤ algorithm.successProbability bottomValue false)
    (hiddenCorrect : ∀ K ∈ criticalSets b t, (2 / 3 : ℝ) ≤
      algorithm.successProbability (criticalValue K) true) :
    (criticalSets b t).card ≤ 3 * r :=
  randomized_mixture_lower_bound BoundedStrategy.toTree algorithm.probability
    algorithm.nonnegative algorithm.normalized b t r
    (fun strategy => strategy.toTree_budget_le) bottomCorrect hiddenCorrect

end RandomizedQueryAlgorithm

end Controller.Boundaries
