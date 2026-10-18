module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Decoder.Forest
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

/-!
# Guard counters and path weight optima

Counters retain repeated guard occurrences. A feasible positive-leaf path admits
all channels outside its guard union; nonnegative channel weights are maximized
by that full set. Arithmetic and encoded-weight costs are separate contracts.
-/

namespace Controller.Decoder

variable {n : ℕ}

abbrev GuardCounters (n : ℕ) := Channel n → ℕ

def enterGuards (counters : GuardCounters n) : List (Channel n) → GuardCounters n
  | [] => counters
  | label :: rest => enterGuards (Function.update counters label (counters label + 1)) rest

def leaveGuards (counters : GuardCounters n) : List (Channel n) → GuardCounters n
  | [] => counters
  | label :: rest => leaveGuards (Function.update counters label (counters label - 1)) rest

theorem enterGuards_count (counters : GuardCounters n) (labels : List (Channel n))
    (channel : Channel n) :
    enterGuards counters labels channel = counters channel + labels.count channel := by
  induction labels generalizing counters with
  | nil => simp [enterGuards]
  | cons label rest ih =>
    rw [enterGuards, ih]
    by_cases same : channel = label
    · subst channel
      simp [Function.update, List.count_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    · simp [Function.update, same, Ne.symm same, List.count_cons]

theorem leaveGuards_count (counters : GuardCounters n) (labels : List (Channel n))
    (channel : Channel n) :
    leaveGuards counters labels channel = counters channel - labels.count channel := by
  induction labels generalizing counters with
  | nil => simp [leaveGuards]
  | cons label rest ih =>
    rw [leaveGuards, ih]
    by_cases same : channel = label
    · subst channel
      simp [Function.update, List.count_cons]
      omega
    · simp [Function.update, same, Ne.symm same, List.count_cons]

/-- Entering and leaving the same incidences restores the preceding path state. -/
theorem leave_enterGuards (counters : GuardCounters n) (labels : List (Channel n)) :
    leaveGuards (enterGuards counters labels) labels = counters := by
  funext channel
  rw [leaveGuards_count, enterGuards_count]
  omega

def blockedChannels (counters : GuardCounters n) : Finset (Channel n) :=
  Finset.univ.filter fun channel => counters channel ≠ 0

@[simp] theorem mem_blockedChannels (counters : GuardCounters n) (channel : Channel n) :
    channel ∈ blockedChannels counters ↔ counters channel ≠ 0 := by
  simp [blockedChannels]

theorem blocked_enterGuards (counters : GuardCounters n) (labels : List (Channel n)) :
    blockedChannels (enterGuards counters labels) = blockedChannels counters ∪ labels.toFinset := by
  ext channel
  simp only [mem_blockedChannels, enterGuards_count, Finset.mem_union, List.mem_toFinset]
  rw [← List.count_pos_iff]
  omega

def pathFeasible (b : ℕ) (target head : Channel n) (blocked : Finset (Channel n)) : Prop :=
  head ∉ blocked ∧ (b = 1 → target ∉ blocked)

theorem pathFeasible_counter_iff (b : ℕ) (target head : Channel n)
    (counters : GuardCounters n) :
    pathFeasible b target head (blockedChannels counters) ↔
      counters head = 0 ∧ (b = 1 → counters target = 0) := by
  simp [pathFeasible]

theorem pathFeasible_iff_smallSet (b : ℕ) (target head : Channel n)
    (blocked : Finset (Channel n)) :
    pathFeasible b target head blocked ↔ Disjoint blocked (trueCandidate b target head) := by
  by_cases one : b = 1
  · simp [pathFeasible, trueCandidate, one, Finset.disjoint_insert_right,
      Finset.disjoint_singleton_right]
  · simp [pathFeasible, trueCandidate, one, Finset.disjoint_singleton_right]

def fullUnblocked (blocked : Finset (Channel n)) : Finset (Channel n) :=
  Finset.univ \ blocked

@[simp] theorem mem_fullUnblocked (blocked : Finset (Channel n)) (channel : Channel n) :
    channel ∈ fullUnblocked blocked ↔ channel ∉ blocked := by simp [fullUnblocked]

theorem fullUnblocked_admissible (b : ℕ) (target head : Channel n)
    (blocked : Finset (Channel n)) (feasible : pathFeasible b target head blocked) :
    Admissible b target (fullUnblocked blocked) :=
  ⟨⟨head, (mem_fullUnblocked _ _).mpr feasible.1⟩,
    fun one => (mem_fullUnblocked _ _).mpr (feasible.2 one)⟩

theorem avoiding_subset_fullUnblocked (blocked K : Finset (Channel n))
    (avoids : Disjoint blocked K) : K ⊆ fullUnblocked blocked := by
  intro channel present
  apply (mem_fullUnblocked _ _).mpr
  intro forbidden
  exact Finset.disjoint_left.mp avoids forbidden present

def channelWeight (weights : Channel n → ℕ) (K : Finset (Channel n)) : ℕ :=
  ∑ channel ∈ K, weights channel

theorem channelWeight_mono (weights : Channel n → ℕ) (K L : Finset (Channel n))
    (subset : K ⊆ L) : channelWeight weights K ≤ channelWeight weights L :=
  Finset.sum_le_sum_of_subset subset

theorem blocked_enter_singleton (counters : GuardCounters n) (label : Channel n) :
    blockedChannels (enterGuards counters [label]) =
      if counters label = 0 then insert label (blockedChannels counters) else blockedChannels counters := by
  rw [blocked_enterGuards]
  by_cases zero : counters label = 0
  · simp [zero]
  · simp [zero, (mem_blockedChannels counters label).mpr zero]

theorem blocked_leave_singleton (counters : GuardCounters n) (label : Channel n) :
    blockedChannels (leaveGuards counters [label]) =
      if counters label = 1 then (blockedChannels counters).erase label else blockedChannels counters := by
  ext channel
  by_cases last : counters label = 1 <;> by_cases same : channel = label
  · subst channel
    simp [last, leaveGuards_count]
  · simp [last, same, Ne.symm same, leaveGuards_count, List.count_cons]
  · subst channel
    simp only [ite_eq_right last, mem_blockedChannels, leaveGuards_count, List.count_cons_self,
      List.count_nil]
    omega
  · simp [last, same, Ne.symm same, leaveGuards_count, List.count_cons]

theorem blockedWeight_enter (weights : Channel n → ℕ) (counters : GuardCounters n)
    (label : Channel n) :
    channelWeight weights (blockedChannels (enterGuards counters [label])) =
      if counters label = 0 then channelWeight weights (blockedChannels counters) + weights label
      else channelWeight weights (blockedChannels counters) := by
  rw [blocked_enter_singleton]
  by_cases zero : counters label = 0
  · simp [zero, channelWeight, Finset.sum_insert, Nat.add_comm]
  · simp [zero]

theorem blockedWeight_leave (weights : Channel n → ℕ) (counters : GuardCounters n)
    (label : Channel n) :
    channelWeight weights (blockedChannels (leaveGuards counters [label])) =
      if counters label = 1 then channelWeight weights (blockedChannels counters) - weights label
      else channelWeight weights (blockedChannels counters) := by
  rw [blocked_leave_singleton]
  by_cases last : counters label = 1
  · simp only [ite_eq_left last]
    have present : label ∈ blockedChannels counters := by simp [last]
    have partition := Finset.sum_erase_add (s := blockedChannels counters) weights present
    change channelWeight weights ((blockedChannels counters).erase label) + weights label =
      channelWeight weights (blockedChannels counters) at partition
    omega
  · simp [last]

/-- Union weight changes only at a zero-to-positive guard-count transition. -/
def enterWeightedLabel (weights : Channel n → ℕ) (state : GuardCounters n × ℕ)
    (label : Channel n) : GuardCounters n × ℕ :=
  (enterGuards state.1 [label],
    if state.1 label = 0 then state.2 + weights label else state.2)

/-- The last occurrence removes its channel weight; overlapping guards retain it. -/
def leaveWeightedLabel (weights : Channel n → ℕ) (state : GuardCounters n × ℕ)
    (label : Channel n) : GuardCounters n × ℕ :=
  (leaveGuards state.1 [label],
    if state.1 label = 1 then state.2 - weights label else state.2)

theorem enterWeightedLabel_correct (weights : Channel n → ℕ) (state : GuardCounters n × ℕ)
    (label : Channel n) (invariant : state.2 = channelWeight weights (blockedChannels state.1)) :
    (enterWeightedLabel weights state label).2 =
      channelWeight weights (blockedChannels (enterWeightedLabel weights state label).1) := by
  simp only [enterWeightedLabel, invariant, blockedWeight_enter]

theorem leaveWeightedLabel_correct (weights : Channel n → ℕ) (state : GuardCounters n × ℕ)
    (label : Channel n) (invariant : state.2 = channelWeight weights (blockedChannels state.1)) :
    (leaveWeightedLabel weights state label).2 =
      channelWeight weights (blockedChannels (leaveWeightedLabel weights state label).1) := by
  simp only [leaveWeightedLabel, invariant, blockedWeight_leave]

theorem fullUnblocked_weight (weights : Channel n → ℕ) (blocked : Finset (Channel n)) :
    channelWeight weights (fullUnblocked blocked) =
      channelWeight weights Finset.univ - channelWeight weights blocked := by
  have partition := Finset.sum_sdiff (f := weights) (Finset.subset_univ blocked)
  change channelWeight weights (fullUnblocked blocked) + channelWeight weights blocked =
    channelWeight weights Finset.univ at partition
  omega

namespace LivePath

theorem smallSet_true {graph : DAG n} {root : Fin graph.nodeCount}
    {head : Channel n} {blocked : Finset (Channel n)}
    (path : LivePath graph root head blocked) (b : ℕ) (target : Channel n)
    (feasible : pathFeasible b target head blocked) :
    graph.eval (assignmentOfSet (trueCandidate b target head)) root = true :=
  path.eval_true _ (head_mem_trueCandidate b target head)
    ((pathFeasible_iff_smallSet b target head blocked).mp feasible)

theorem fullUnblocked_true {graph : DAG n} {root : Fin graph.nodeCount}
    {head : Channel n} {blocked : Finset (Channel n)}
    (path : LivePath graph root head blocked) (b : ℕ) (target : Channel n)
    (feasible : pathFeasible b target head blocked) :
    graph.eval (assignmentOfSet (fullUnblocked blocked)) root = true := by
  apply path.eval_true
  · exact (mem_fullUnblocked _ _).mpr feasible.1
  · exact Finset.disjoint_sdiff

/-- The full unblocked set dominates every set that succeeds on this path. -/
theorem fullUnblocked_optimal {graph : DAG n} {root : Fin graph.nodeCount}
    {head : Channel n} {blocked : Finset (Channel n)}
    (path : LivePath graph root head blocked) (weights : Channel n → ℕ)
    (K : Finset (Channel n)) (headTrue : head ∈ K) (avoids : Disjoint blocked K) :
    graph.eval (assignmentOfSet (fullUnblocked blocked)) root = true ∧
      channelWeight weights K ≤ channelWeight weights (fullUnblocked blocked) := by
  refine ⟨path.eval_true _ ?_ Finset.disjoint_sdiff,
    channelWeight_mono weights K _ (avoiding_subset_fullUnblocked blocked K avoids)⟩
  exact avoiding_subset_fullUnblocked blocked K avoids headTrue

end LivePath

namespace DAG

/-- Every true reachable set is dominated by a feasible leaf-path complement. -/
theorem exists_dominating_path (graph : DAG n) (guarded : graph.Guarded)
    (b : ℕ) (target : Channel n) (root : Fin graph.nodeCount) (weights : Channel n → ℕ)
    (K : Finset (Channel n)) (eligible : Admissible b target K)
    (value : graph.eval (assignmentOfSet K) root = true) :
    ∃ head blocked, LivePath graph root head blocked ∧ pathFeasible b target head blocked ∧
      Admissible b target (fullUnblocked blocked) ∧
      graph.eval (assignmentOfSet (fullUnblocked blocked)) root = true ∧
      channelWeight weights K ≤ channelWeight weights (fullUnblocked blocked) := by
  obtain ⟨head, blocked, path, headTrue, avoids⟩ := graph.exists_livePath_of_eval_true guarded K root value
  have feasible : pathFeasible b target head blocked := by
    refine ⟨?_, ?_⟩
    · intro forbidden
      exact Finset.disjoint_left.mp avoids forbidden headTrue
    · intro one forbidden
      exact Finset.disjoint_left.mp avoids forbidden (eligible.2 one)
  obtain ⟨fullTrue, dominates⟩ := path.fullUnblocked_optimal weights K headTrue avoids
  exact ⟨head, blocked, path, feasible, fullUnblocked_admissible b target head blocked feasible,
    fullTrue, dominates⟩

/-- On a healthy-zero root, the dominating path complement remains a detector. -/
theorem healthyZero_dominating_path (graph : DAG n) (guarded : graph.Guarded)
    (b : ℕ) (target : Channel n) (root : Fin graph.nodeCount) (weights : Channel n → ℕ)
    (healthy : graph.eval (assignmentOfSet {target}) root = false)
    (K : Finset (Channel n)) (eligible : Admissible b target K)
    (differs : graph.eval (assignmentOfSet K) root ≠ graph.eval (assignmentOfSet {target}) root) :
    ∃ head blocked, LivePath graph root head blocked ∧ pathFeasible b target head blocked ∧
      Admissible b target (fullUnblocked blocked) ∧
      graph.eval (assignmentOfSet (fullUnblocked blocked)) root ≠
        graph.eval (assignmentOfSet {target}) root ∧
      channelWeight weights K ≤ channelWeight weights (fullUnblocked blocked) := by
  have value : graph.eval (assignmentOfSet K) root = true := by
    cases actual : graph.eval (assignmentOfSet K) root <;> simp_all
  obtain ⟨head, blocked, path, feasible, fullEligible, fullTrue, dominates⟩ :=
    graph.exists_dominating_path guarded b target root weights K eligible value
  exact ⟨head, blocked, path, feasible, fullEligible, by rw [fullTrue, healthy]; decide, dominates⟩

end DAG
/-! The ordered-group layer keeps nonnegativity explicit and does not restrict
mathematical weights to integers. Its operations are abstract arithmetic;
representations and bit costs remain separate. -/
namespace GenericWeight

variable {W : Type*} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]

def total (weights : Channel n → W) (K : Finset (Channel n)) : W :=
  ∑ channel ∈ K, weights channel

theorem mono (weights : Channel n → W) (nonnegative : ∀ channel, 0 ≤ weights channel)
    (K L : Finset (Channel n)) (subset : K ⊆ L) : total weights K ≤ total weights L := by
  apply Finset.sum_le_sum_of_subset_of_nonneg subset
  intro channel _ _
  exact nonnegative channel

theorem fullUnblocked_total (weights : Channel n → W) (blocked : Finset (Channel n)) :
    total weights (fullUnblocked blocked) = total weights Finset.univ - total weights blocked := by
  apply eq_sub_iff_add_eq.mpr
  exact Finset.sum_sdiff (f := weights) (Finset.subset_univ blocked)

/-- The cached union sum changes only when a label first becomes blocked. -/
def enter (weights : Channel n → W) (state : GuardCounters n × W)
    (label : Channel n) : GuardCounters n × W :=
  (enterGuards state.1 [label], if state.1 label = 0 then state.2 + weights label else state.2)

/-- Ordered-group subtraction removes a weight exactly on the last exit. -/
def leave (weights : Channel n → W) (state : GuardCounters n × W)
    (label : Channel n) : GuardCounters n × W :=
  (leaveGuards state.1 [label], if state.1 label = 1 then state.2 - weights label else state.2)

theorem enter_correct (weights : Channel n → W) (state : GuardCounters n × W)
    (label : Channel n) (invariant : state.2 = total weights (blockedChannels state.1)) :
    (enter weights state label).2 = total weights (blockedChannels (enter weights state label).1) := by
  simp only [enter, blocked_enter_singleton]
  by_cases zero : state.1 label = 0
  · simp [zero, invariant, total, Finset.sum_insert, add_comm]
  · simp [zero, invariant]

theorem leave_correct (weights : Channel n → W) (state : GuardCounters n × W)
    (label : Channel n) (invariant : state.2 = total weights (blockedChannels state.1)) :
    (leave weights state label).2 = total weights (blockedChannels (leave weights state label).1) := by
  simp only [leave, blocked_leave_singleton]
  by_cases last : state.1 label = 1
  · simp only [ite_eq_left last, invariant]
    symm
    apply eq_sub_iff_add_eq.mpr
    exact Finset.sum_erase_add _ weights (by simp [last])
  · simp [last, invariant]

theorem path_optimal {graph : DAG n} {root : Fin graph.nodeCount}
    {head : Channel n} {blocked : Finset (Channel n)}
    (path : LivePath graph root head blocked) (weights : Channel n → W)
    (nonnegative : ∀ channel, 0 ≤ weights channel)
    (K : Finset (Channel n)) (headTrue : head ∈ K) (avoids : Disjoint blocked K) :
    graph.eval (assignmentOfSet (fullUnblocked blocked)) root = true ∧
      total weights K ≤ total weights (fullUnblocked blocked) := by
  refine ⟨path.eval_true _ ?_ Finset.disjoint_sdiff,
    mono weights nonnegative K _ (avoiding_subset_fullUnblocked blocked K avoids)⟩
  exact avoiding_subset_fullUnblocked blocked K avoids headTrue

theorem exists_dominating_path (graph : DAG n) (guarded : graph.Guarded)
    (b : ℕ) (target : Channel n) (root : Fin graph.nodeCount) (weights : Channel n → W)
    (nonnegative : ∀ channel, 0 ≤ weights channel)
    (K : Finset (Channel n)) (eligible : Admissible b target K)
    (value : graph.eval (assignmentOfSet K) root = true) :
    ∃ head blocked, LivePath graph root head blocked ∧ pathFeasible b target head blocked ∧
      Admissible b target (fullUnblocked blocked) ∧
      graph.eval (assignmentOfSet (fullUnblocked blocked)) root = true ∧
      total weights K ≤ total weights (fullUnblocked blocked) := by
  obtain ⟨head, blocked, path, headTrue, avoids⟩ := graph.exists_livePath_of_eval_true guarded K root value
  have feasible : pathFeasible b target head blocked := by
    refine ⟨?_, ?_⟩
    · intro forbidden
      exact Finset.disjoint_left.mp avoids forbidden headTrue
    · intro one forbidden
      exact Finset.disjoint_left.mp avoids forbidden (eligible.2 one)
  obtain ⟨fullTrue, dominates⟩ := path_optimal path weights nonnegative K headTrue avoids
  exact ⟨head, blocked, path, feasible, fullUnblocked_admissible b target head blocked feasible,
    fullTrue, dominates⟩

end GenericWeight

end Controller.Decoder
