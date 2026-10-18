module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Extensions.BoundedAnd
public import Mathlib.Data.Nat.Choose.Sum

@[expose] public section

/-! A depth-first subset iterator keeps a chosen list and a stack of pending
branches. Its instrumented recursion counts actual calls and callbacks; it
never constructs the family of subsets. -/
namespace Controller.Extensions.SupportStream
open Controller.Extensions.BoundedAnd
open scoped BigOperators

/-- The number of subsets of size at most `r`, without a truncated sum index. -/
def leaves (n r : ℕ) : ℕ := ∑ j ∈ Finset.range (r+1), n.choose j

@[simp] theorem leaves_zero (r : ℕ) : leaves 0 r = 1 := by
  unfold leaves
  rw [Finset.sum_range_succ']
  simp

@[simp] theorem leaves_capacity_zero (n : ℕ) : leaves n 0 = 1 := by simp [leaves]

theorem leaves_step (n r : ℕ) : leaves (n+1) (r+1) = leaves n r + leaves n (r+1) := by
  unfold leaves
  conv_lhs => rw [Finset.sum_range_succ']
  simp only [Nat.choose_zero_right, Nat.choose_succ_succ]
  rw [Finset.sum_add_distrib]
  conv_rhs => rhs; rw [Finset.sum_range_succ']
  simp only [Nat.choose_zero_right]
  simp only [Nat.succ_eq_add_one]
  omega

theorem leaves_eq_supportCount (n k : ℕ) : leaves n (k+1) = supportCount n k := by
  unfold leaves supportCount
  apply Finset.sum_congr_of_eq_on_inter
  · intro j hj hnot
    have high : n < j := by
      have a := Finset.mem_range.mp hj
      have b : min (k+1) n + 1 ≤ j := Nat.le_of_not_gt (fun h => hnot (Finset.mem_range.mpr h))
      omega
    exact Nat.choose_eq_zero_of_lt high
  · intro j hj hnot
    have a := Finset.mem_range.mp hj
    have b : k+1+1 ≤ j := Nat.le_of_not_gt (fun h => hnot (Finset.mem_range.mpr h))
    omega
  · intro j _ _; rfl

/-- Number of callbacks in a traversal which does not stop early. -/
def fullCalls : ℕ → ℕ → ℕ
  | _, 0 => 1
  | 0, _+1 => 1
  | n+1, r+1 => fullCalls n r + fullCalls n (r+1)

theorem fullCalls_eq (n r : ℕ) : fullCalls n r = leaves n r := by
  induction n generalizing r with
  | zero => cases r <;> simp [fullCalls]
  | succ n ih => cases r <;> simp [fullCalls, ih, leaves_step]

/-- Result, number of traversal nodes visited, and callbacks executed. -/
structure Run (β : Type*) where
  result : Option β
  nodes : ℕ
  queries : ℕ
  deriving Repr

/-- Chosen elements are consed in constant time; tail lists are shared by the
recursive calls. Conversion to an indexed support occurs only in the callback. -/
def search (query : List α → Option β) : ℕ → List α → List α → Run β
  | 0, _, chosen => ⟨query chosen,1,1⟩
  | _+1, [], chosen => ⟨query chosen,1,1⟩
  | r+1, head::tail, chosen =>
    let first := search query r tail (head::chosen)
    match first.result with
    | some value => ⟨some value, first.nodes+1,first.queries⟩
    | none =>
      let second := search query (r+1) tail chosen
      ⟨second.result,first.nodes+second.nodes+1,first.queries+second.queries⟩

theorem search_eq {α β : Type*} [DecidableEq α] (query : Finset α → Option β)
    (r : ℕ) (items chosen : List α) :
    (search (fun xs => query xs.toFinset) r items chosen).result =
      searchSmall query r items chosen.toFinset := by
  induction items generalizing r chosen with
  | nil => cases r <;> rfl
  | cons head tail ih =>
    cases r with
    | zero => rfl
    | succ r =>
      simp only [search, searchSmall]
      have first := ih r (head::chosen)
      simp only [List.toFinset_cons] at first
      rw [first]
      cases result : searchSmall query r tail (insert head chosen.toFinset)
      · exact ih (r+1) chosen
      · rfl

theorem search_queries_le (query : List α → Option β) (r : ℕ) (items chosen : List α) :
    (search query r items chosen).queries ≤ fullCalls items.length r := by
  induction items generalizing r chosen with
  | nil => cases r <;> exact le_rfl
  | cons head tail ih =>
    cases r with
    | zero => exact le_rfl
    | succ r =>
      simp only [search, List.length_cons, fullCalls]
      have first := ih r (head::chosen)
      have second := ih (r+1) chosen
      split
      · exact first.trans (Nat.le_add_right _ _)
      · exact Nat.add_le_add first second

theorem search_nodes_le (query : List α → Option β) (r : ℕ) (items chosen : List α) :
    (search query r items chosen).nodes + 1 ≤ 2 * fullCalls items.length r := by
  induction items generalizing r chosen with
  | nil => cases r <;> exact le_rfl
  | cons head tail ih =>
    cases r with
    | zero => exact le_rfl
    | succ r =>
      simp only [search, List.length_cons, fullCalls]
      have first := ih r (head::chosen)
      have second := ih (r+1) chosen
      have positive : 1 ≤ fullCalls tail.length (r+1) := by
        rw [fullCalls_eq]
        exact Finset.single_le_sum (fun _ _ => Nat.zero_le _)
          (show 0 ∈ Finset.range (r+1+1) by simp) |>.trans' (by simp)
      split <;> dsimp only <;> omega

/-- The iterator's simultaneous pending frames and chosen values grow only
along the current recursion depth; neither subtree remains live afterwards. -/
def frontier : ℕ → ℕ → ℕ
  | _, 0 => 0
  | 0, _+1 => 0
  | n+1,r+1 => 1 + max (frontier n r) (frontier n (r+1))

theorem frontier_le (n r : ℕ) : frontier n r ≤ n := by
  induction n generalizing r with
  | zero => cases r <;> simp [frontier]
  | succ n ih =>
    cases r with
    | zero => simp [frontier]
    | succ r =>
      have a := ih r
      have b := ih (r+1)
      simp only [frontier]
      omega

/-- At most B_k(n) callbacks and fewer than 2 B_k(n) traversal nodes. This is
an iterator bound; callback execution and its storage must be composed separately. -/
theorem support_search_bounds (query : List (Fin n) → Option β) (k : ℕ) :
    (search query (k+1) (List.finRange n) []).queries ≤ supportCount n k ∧
    (search query (k+1) (List.finRange n) []).nodes + 1 ≤ 2*supportCount n k ∧
    frontier n (k+1) ≤ n := by
  have queries := search_queries_le query (k+1) (List.finRange n) []
  have nodes := search_nodes_le query (k+1) (List.finRange n) []
  rw [List.length_finRange,fullCalls_eq,leaves_eq_supportCount] at queries nodes
  exact ⟨queries,nodes,frontier_le n (k+1)⟩

theorem leaves_positive (n r : ℕ) : 0 < leaves n r := by
  have one := Finset.single_le_sum (f := fun j => n.choose j) (fun _ _ => Nat.zero_le _)
    (show 0 ∈ Finset.range (r+1) by simp)
  simp only [Nat.choose_zero_right] at one
  exact Nat.lt_of_lt_of_le (by decide : 0 < 1) one

/-- Saturating the capacity visits each subset once. -/
theorem leaves_saturated (n r : ℕ) (enough : n ≤ r) : leaves n r = 2^n := by
  have same : leaves n r = leaves n n := by
    unfold leaves
    apply Finset.sum_congr_of_eq_on_inter
    · intro j hj hn
      have high : n < j := by
        have := Nat.le_of_not_gt (fun h => hn (Finset.mem_range.mpr h))
        omega
      exact Nat.choose_eq_zero_of_lt high
    · intro j hj hn
      have low := Finset.mem_range.mp hj
      have high := Nat.le_of_not_gt (fun h => hn (Finset.mem_range.mpr h))
      omega
    · intro j _ _; rfl
  rw [same]
  exact Nat.sum_range_choose n

/-- The selector traversal uses distinct stored AND identities and has at most
2^k callbacks, even when a node is shared or used outside an observed cone. -/
theorem selector_search_bounds (graph : Controller.Decoder.DAG n)
    (query : List (Fin graph.nodeCount) → Option β) (k : ℕ) (bound : graph.liveAndCount ≤ k) :
    (search query graph.liveAndCount (andIdentities graph) []).queries ≤ 2^k ∧
    (search query graph.liveAndCount (andIdentities graph) []).nodes + 1 ≤ 2*(2^k) ∧
    frontier (andIdentities graph).length graph.liveAndCount ≤ graph.nodeCount := by
  have queries := search_queries_le query graph.liveAndCount (andIdentities graph) []
  have nodes := search_nodes_le query graph.liveAndCount (andIdentities graph) []
  rw [andIdentities_length,fullCalls_eq,leaves_saturated _ _ le_rfl] at queries nodes
  have powers : 2^graph.liveAndCount ≤ 2^k := Nat.pow_le_pow_right (by decide) bound
  refine ⟨queries.trans powers,nodes.trans (Nat.mul_le_mul_left _ powers),?_⟩
  exact (frontier_le _ _).trans ((andIdentities_length graph).le.trans graph.liveAndCount_le_nodeCount)

/-- A callback reports the work and temporary words of its own execution.
The iterator accounts for those resources and releases callback scratch before
visiting a sibling. Closing a machine theorem requires a callback refinement. -/
structure Callback (β : Type*) where
  result : Option β
  steps : ℕ
  scratch : ℕ
  deriving Repr

structure Measured (β : Type*) where
  result : Option β
  steps : ℕ
  peak : ℕ
  deriving Repr

def measured (query : List α → Callback β) : ℕ → List α → List α → Measured β
  | 0, _, chosen =>
    let call := query chosen
    ⟨call.result,call.steps+1,chosen.length+call.scratch⟩
  | _+1, [], chosen =>
    let call := query chosen
    ⟨call.result,call.steps+1,chosen.length+call.scratch⟩
  | r+1,head::tail,chosen =>
    let first := measured query r tail (head::chosen)
    match first.result with
    | some value => ⟨some value,first.steps+1,first.peak+1⟩
    | none =>
      let second := measured query (r+1) tail chosen
      ⟨second.result,first.steps+second.steps+1,max (first.peak+1) (second.peak+1)⟩

theorem measured_result (query : List α → Callback β) (r : ℕ) (items chosen : List α) :
    (measured query r items chosen).result = (search (fun xs => (query xs).result) r items chosen).result := by
  induction items generalizing r chosen with
  | nil => cases r <;> rfl
  | cons head tail ih =>
    cases r with
    | zero => rfl
    | succ r =>
      simp only [measured,search]
      rw [ih r (head::chosen)]
      cases (search (fun xs => (query xs).result) r tail (head::chosen)).result
      · exact ih (r+1) chosen
      · rfl

theorem measured_steps (query : List α → Callback β) (Q : ℕ)
    (callback : ∀ chosen, (query chosen).steps ≤ Q)
    (r : ℕ) (items chosen : List α) :
    (measured query r items chosen).steps + 1 ≤ (Q+2)*fullCalls items.length r := by
  induction items generalizing r chosen with
  | nil => cases r <;> simpa [measured,fullCalls] using Nat.add_le_add_right (callback chosen) 2
  | cons head tail ih =>
    cases r with
    | zero => simpa [measured,fullCalls] using Nat.add_le_add_right (callback chosen) 2
    | succ r =>
      have first := ih r (head::chosen)
      have second := ih (r+1) chosen
      have positive : 0 < fullCalls tail.length (r+1) := by rw [fullCalls_eq]; exact leaves_positive _ _
      simp only [measured, List.length_cons,fullCalls]
      split <;> dsimp only <;> nlinarith

theorem measured_peak (query : List α → Callback β) (S : ℕ)
    (callback : ∀ chosen, (query chosen).scratch ≤ S)
    (r : ℕ) (items chosen : List α) :
    (measured query r items chosen).peak ≤ chosen.length + 2*items.length + S := by
  induction items generalizing r chosen with
  | nil => cases r <;> simpa [measured] using Nat.add_le_add_left (callback chosen) chosen.length
  | cons head tail ih =>
    cases r with
    | zero => simp only [measured]; have h := callback chosen; omega
    | succ r =>
      have first := ih r (head::chosen)
      have second := ih (r+1) chosen
      simp only [List.length_cons] at first
      simp only [measured,List.length_cons]
      split <;> dsimp only <;> omega

/-- Query budgets need hold only for reachable chosen lists, whose lengths
cannot exceed the original input length. -/
theorem measured_steps_bounded (query : List α → Callback β) (N Q : ℕ)
    (callback : ∀ chosen, chosen.length ≤ N → (query chosen).steps ≤ Q)
    (r : ℕ) (items chosen : List α) (room : chosen.length+items.length ≤ N) :
    (measured query r items chosen).steps+1 ≤ (Q+2)*fullCalls items.length r := by
  induction items generalizing r chosen with
  | nil => cases r <;> simpa [measured,fullCalls] using Nat.add_le_add_right (callback chosen (by simpa using room)) 2
  | cons head tail ih =>
    cases r with
    | zero => simpa [measured,fullCalls] using Nat.add_le_add_right (callback chosen (by simp only [List.length_cons] at room; omega)) 2
    | succ r =>
      have first := ih r (head::chosen) (by simp only [List.length_cons] at room ⊢; omega)
      have second := ih (r+1) chosen (by simp only [List.length_cons] at room; omega)
      have positive : 0 < fullCalls tail.length (r+1) := by rw [fullCalls_eq]; exact leaves_positive _ _
      simp only [measured,List.length_cons,fullCalls]
      split <;> dsimp only <;> nlinarith

theorem measured_peak_bounded (query : List α → Callback β) (N S : ℕ)
    (callback : ∀ chosen, chosen.length ≤ N → (query chosen).scratch ≤ S)
    (r : ℕ) (items chosen : List α) (room : chosen.length+items.length ≤ N) :
    (measured query r items chosen).peak ≤ chosen.length+2*items.length+S := by
  induction items generalizing r chosen with
  | nil => cases r <;> simpa [measured] using Nat.add_le_add_left (callback chosen (by simpa using room)) chosen.length
  | cons head tail ih =>
    cases r with
    | zero =>
      have bound := callback chosen (by simp only [List.length_cons] at room; omega)
      simp only [measured,List.length_cons]; omega
    | succ r =>
      have first := ih r (head::chosen) (by simp only [List.length_cons] at room ⊢; omega)
      have second := ih (r+1) chosen (by simp only [List.length_cons] at room; omega)
      simp only [List.length_cons] at first
      simp only [measured,List.length_cons]
      split <;> dsimp only <;> omega

/-- Structured iterator composition with explicit callback obligations. The
machine integration must supply these bounds and simulate the iterator. -/
theorem support_measured_bounds (query : List (Fin n) → Callback β) (k Q S : ℕ)
    (time : ∀ chosen, chosen.length ≤ n → (query chosen).steps ≤ Q)
    (space : ∀ chosen, chosen.length ≤ n → (query chosen).scratch ≤ S) :
    (measured query (k+1) (List.finRange n) []).steps+1 ≤ (Q+2)*supportCount n k ∧
    (measured query (k+1) (List.finRange n) []).peak ≤ 2*n+S := by
  have bound := measured_steps_bounded query n Q time (k+1) (List.finRange n) [] (by simp)
  rw [List.length_finRange,fullCalls_eq,leaves_eq_supportCount] at bound
  exact ⟨bound,by simpa using measured_peak_bounded query n S space (k+1) (List.finRange n) [] (by simp)⟩

/-- The chosen-list iterator is an exact refinement of the checked support
search, with the same callback order and early exit. -/
def scanSupports (graph : Controller.Decoder.DAG n) (k b : ℕ) (target : Controller.Channel n)
    (healthy : Fin graph.nodeCount → Bool) : Option (Finset (Controller.Channel n)) :=
  (search (fun chosen => supportQuery graph b target healthy chosen.toFinset)
    (k+1) (List.finRange n) []).result

theorem scanSupports_eq (graph : Controller.Decoder.DAG n) (k b : ℕ) (target : Controller.Channel n)
    (healthy : Fin graph.nodeCount → Bool) :
    scanSupports graph k b target healthy = BoundedAnd.scanSupports graph k b target healthy := by
  simpa only [scanSupports,BoundedAnd.scanSupports,List.toFinset_nil] using
    search_eq (supportQuery graph b target healthy) (k+1) (List.finRange n) []

def scanExpansions (graph : Controller.Decoder.DAG n) (b : ℕ) (target : Controller.Channel n)
    (root : Fin graph.nodeCount) : Option (Finset (Controller.Channel n)) :=
  (search (fun chosen => resolvedZeroQuery graph b target root chosen.toFinset)
    graph.liveAndCount (andIdentities graph) []).result

theorem scanExpansions_eq (graph : Controller.Decoder.DAG n) (b : ℕ) (target : Controller.Channel n)
    (root : Fin graph.nodeCount) :
    scanExpansions graph b target root = BoundedAnd.scanExpansions graph b target root := by
  simpa only [scanExpansions,BoundedAnd.scanExpansions,List.toFinset_nil] using
    search_eq (resolvedZeroQuery graph b target root) graph.liveAndCount (andIdentities graph) []

/-- One consistent selector bit is stored for each distinct represented AND,
with all roots retaining their original multiplicities. -/
def detectSet (graph : Controller.Decoder.DAG n) (k b : ℕ) (target : Controller.Channel n) (drive : Bool) :
    Option (Finset (Controller.Channel n)) :=
  if drive then
    let healthy := graph.evalTable (Controller.assignmentOfSet {target})
    let candidates := if graph.roots.all healthy then none else scanSupports graph k b target healthy
    match candidates with
    | some K => some K
    | none => Controller.Decoder.DAG.firstSuccess
        (fun root => if healthy root then scanExpansions graph b target root else none) graph.roots
  else none

theorem detectSet_eq (graph : Controller.Decoder.DAG n) (k b : ℕ) (target : Controller.Channel n) (drive : Bool) :
    detectSet graph k b target drive = BoundedAnd.detectSet graph k b target drive := by
  simp only [detectSet,BoundedAnd.detectSet,BoundedAnd.scanCandidates,scanSupports_eq,
    scanExpansions_eq]
  rfl

theorem detectSet_none_iff (graph : Controller.Decoder.DAG n) (k : ℕ) (bound : graph.liveAndCount ≤ k)
    (b : ℕ) (target : Controller.Channel n) (drive : Bool) :
    detectSet graph k b target drive = none ↔
      ¬ (drive = true ∧ ∃ root ∈ graph.roots, ∃ K, Controller.Admissible b target K ∧
        graph.eval (Controller.assignmentOfSet K) root ≠ graph.eval (Controller.assignmentOfSet {target}) root) := by
  rw [detectSet_eq]
  exact BoundedAnd.detectSet_none_iff graph k bound b target drive

/-- Capacities at least the number of remaining IDs have exactly the same
execution tree, including early returns and the traversal counters. -/
theorem search_capacity_congr (query : List α → Option β) (items chosen : List α)
    (r s : ℕ) (left : items.length ≤ r) (right : items.length ≤ s) :
    search query r items chosen = search query s items chosen := by
  induction items generalizing r s chosen with
  | nil => cases r <;> cases s <;> rfl
  | cons head tail ih =>
    cases r with
    | zero => simp only [List.length_cons] at left; omega
    | succ r =>
      cases s with
      | zero => simp only [List.length_cons] at right; omega
      | succ s =>
        have lr : tail.length ≤ r := by simp only [List.length_cons] at left; omega
        have ls : tail.length ≤ s := by simp only [List.length_cons] at right; omega
        simp only [search, ih (head::chosen) r s lr ls,
          ih chosen (r+1) (s+1) (by omega) (by omega)]

/-- The runtime capacity can be clamped before word encoding, regardless of
how large the supplied natural-number bound is. This preserves the full run. -/
theorem search_clamp (query : List α → Option β) (r : ℕ) (items chosen : List α) :
    search query (min r items.length) items chosen = search query r items chosen := by
  by_cases lower : r ≤ items.length
  · rw [Nat.min_eq_left lower]
  · rw [Nat.min_eq_right (by omega)]
    exact search_capacity_congr query items chosen items.length r (by omega) (by omega)

end Controller.Extensions.SupportStream
