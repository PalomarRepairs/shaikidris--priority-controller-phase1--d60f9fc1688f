module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Decoder.Eval

@[expose] public section

/-!
# Successful paths in a guarded decoder

A live path chooses one listed child of each OR, traverses the unique child
of each guard, and ends at a positive channel. It records the union of guard
labels on that path. Shared nodes retain their original indices.
-/

namespace Controller.Decoder

variable {n : ℕ}

/-- A positive-leaf path with the channel labels forbidden along that path. -/
inductive LivePath (graph : DAG n) :
    Fin graph.nodeCount → Channel n → Finset (Channel n) → Prop where
  | input (index : Fin graph.nodeCount) (head : Channel n)
      (gateEquation : graph.node index = .input head) :
      LivePath graph index head ∅
  | disj (index : Fin graph.nodeCount) (refs : List (Fin index.val))
      (child : Fin index.val) (head : Channel n) (blocked : Finset (Channel n))
      (gateEquation : graph.node index = .disj refs) (membership : child ∈ refs)
      (tail : LivePath graph (graph.childIndex index child) head blocked) :
      LivePath graph index head blocked
  | guard (index : Fin graph.nodeCount) (child : Fin index.val)
      (labels : List (Channel n)) (head : Channel n) (blocked : Finset (Channel n))
      (gateEquation : graph.node index = .guard child labels)
      (tail : LivePath graph (graph.childIndex index child) head blocked) :
      LivePath graph index head (labels.toFinset ∪ blocked)

namespace LivePath

variable {graph : DAG n} {index : Fin graph.nodeCount}
variable {head : Channel n} {blocked : Finset (Channel n)}

/-- A path succeeds when its head is true and all of its guards are false. -/
theorem eval_true (path : LivePath graph index head blocked) (K : Finset (Channel n)) :
    head ∈ K → Disjoint blocked K → graph.eval (assignmentOfSet K) index = true := by
  induction path with
  | input index head gateEquation =>
      intro headTrue _
      rw [graph.eval_input _ index head gateEquation]
      exact (assignmentOfSet_eq_true K head).mpr headTrue
  | disj index refs child head blocked gateEquation membership tail inductionHypothesis =>
      intro headTrue guardsFalse
      rw [graph.eval_disj _ index refs gateEquation]
      exact List.any_eq_true.mpr
        ⟨child, membership, inductionHypothesis headTrue guardsFalse⟩
  | guard index child labels head blocked gateEquation tail inductionHypothesis =>
      intro headTrue guardsFalse
      rw [graph.eval_guard _ index child labels gateEquation]
      simp only [Bool.and_eq_true, Bool.not_eq_true', List.any_eq_false,
        assignmentOfSet_eq_true]
      refine ⟨inductionHypothesis headTrue
        (guardsFalse.mono_left Finset.subset_union_right), ?_⟩
      intro channel membership channelTrue
      exact Finset.disjoint_left.mp guardsFalse
        (Finset.mem_union_left _ (by simpa using membership)) channelTrue

/-- Removing true channels preserves a path when its positive head is retained. -/
theorem eval_true_of_subset (path : LivePath graph index head blocked)
    {K L : Finset (Channel n)} (headTrue : head ∈ L) (guardsFalse : Disjoint blocked K)
    (subset : L ⊆ K) : graph.eval (assignmentOfSet L) index = true :=
  path.eval_true L headTrue (guardsFalse.mono_right subset)

/-- Adding channels preserves a path when the added channels avoid its guards. -/
theorem eval_true_union (path : LivePath graph index head blocked)
    {K added : Finset (Channel n)} (headTrue : head ∈ K)
    (guardsFalse : Disjoint blocked K) (addedAvoids : Disjoint blocked added) :
    graph.eval (assignmentOfSet (K ∪ added)) index = true :=
  path.eval_true _ (Finset.mem_union_left _ headTrue)
    (Finset.disjoint_union_right.mpr ⟨guardsFalse, addedAvoids⟩)

/-- A path's positive head occurs in the root's syntactic channel scope. -/
theorem head_mem_scope (path : LivePath graph index head blocked) :
    head ∈ graph.scope index := by
  induction path with
  | input index head gateEquation =>
      apply graph.mem_scope_of_mem_directChannels index
      simp [gateEquation, Gate.directChannels]
  | disj index refs child head blocked gateEquation membership tail inductionHypothesis =>
      exact graph.scope_child_subset index child
        (by simpa only [gateEquation, Gate.children] using membership) inductionHypothesis
  | guard index child labels head blocked gateEquation tail inductionHypothesis =>
      exact graph.scope_child_subset index child
        (by simp [gateEquation, Gate.children]) inductionHypothesis

/-- Every guard recorded along a path belongs to the root's syntactic scope. -/
theorem blocked_subset_scope (path : LivePath graph index head blocked) :
    blocked ⊆ graph.scope index := by
  induction path with
  | input index head gateEquation => exact Finset.empty_subset _
  | disj index refs child head blocked gateEquation membership tail inductionHypothesis =>
      exact inductionHypothesis.trans (graph.scope_child_subset index child
        (by simpa only [gateEquation, Gate.children] using membership))
  | guard index child labels head blocked gateEquation tail inductionHypothesis =>
      intro channel membership
      rcases Finset.mem_union.mp membership with directMembership | tailMembership
      · apply graph.mem_scope_of_mem_directChannels index
        simpa only [gateEquation, Gate.directChannels, List.mem_toFinset] using directMembership
      · exact graph.scope_child_subset index child
          (by simp [gateEquation, Gate.children]) (inductionHypothesis tailMembership)

end LivePath

namespace DAG

/-- A positive head is witnessed by an actual live path in the stored DAG. -/
def IsPositiveHead (graph : DAG n) (index : Fin graph.nodeCount) (head : Channel n) : Prop :=
  ∃ blocked, LivePath graph index head blocked

/-- A true guarded node has a path with a true positive head and false guards. -/
theorem exists_livePath_of_eval_true (graph : DAG n) (guarded : graph.Guarded)
    (K : Finset (Channel n)) (index : Fin graph.nodeCount)
    (trueValue : graph.eval (assignmentOfSet K) index = true) :
    ∃ head blocked, LivePath graph index head blocked ∧ head ∈ K ∧ Disjoint blocked K := by
  have inductionClaim : ∀ bound : ℕ, ∀ current : Fin graph.nodeCount,
      current.val = bound → graph.eval (assignmentOfSet K) current = true →
      ∃ head blocked, LivePath graph current head blocked ∧ head ∈ K ∧ Disjoint blocked K := by
    intro bound
    induction bound using Nat.strong_induction_on with
    | h bound inductionHypothesis =>
        intro current currentBound currentTrue
        cases gateEquation : graph.node current with
        | zero =>
            have zeroValue := graph.eval_zero (assignmentOfSet K) current gateEquation
            simp [zeroValue] at currentTrue
        | input head =>
            refine ⟨head, ∅, .input current head gateEquation, ?_, Finset.disjoint_empty_left K⟩
            apply (assignmentOfSet_eq_true K head).mp
            exact (graph.eval_input _ current head gateEquation).symm.trans currentTrue
        | disj refs =>
            have childrenTrue :=
              (graph.eval_disj (assignmentOfSet K) current refs gateEquation).symm.trans currentTrue
            obtain ⟨child, membership, childTrue⟩ := List.any_eq_true.mp childrenTrue
            have earlier : child.val < bound := by simpa only [currentBound] using child.isLt
            obtain ⟨head, blocked, path, headTrue, guardsFalse⟩ :=
              inductionHypothesis child.val earlier (graph.childIndex current child) rfl childTrue
            exact ⟨head, blocked, .disj current refs child head blocked gateEquation membership path,
              headTrue, guardsFalse⟩
        | guard child labels =>
            have gateTrue :=
              (graph.eval_guard (assignmentOfSet K) current child labels gateEquation).symm.trans
                currentTrue
            obtain ⟨childTrue, labelsFalse⟩ := Bool.and_eq_true_iff.mp gateTrue
            have earlier : child.val < bound := by simpa only [currentBound] using child.isLt
            obtain ⟨head, blocked, path, headTrue, guardsFalse⟩ :=
              inductionHypothesis child.val earlier (graph.childIndex current child) rfl childTrue
            refine ⟨head, labels.toFinset ∪ blocked,
              .guard current child labels head blocked gateEquation path, headTrue, ?_⟩
            apply Finset.disjoint_union_left.mpr
            refine ⟨?_, guardsFalse⟩
            apply Finset.disjoint_left.mpr
            intro channel membership channelTrue
            have labelsAnyFalse : labels.any (assignmentOfSet K) = false := by
              simpa only [Bool.not_eq_true'] using labelsFalse
            exact List.any_eq_false.mp labelsAnyFalse channel (by simpa using membership)
              ((assignmentOfSet_eq_true K channel).mpr channelTrue)
        | liveAnd left right =>
            have guardCondition := guarded current
            simp [Gate.IsGuarded, gateEquation, Gate.isLiveAnd] at guardCondition
  exact inductionClaim index.val index rfl trueValue

/-- Truth in the guarded language is exactly existence of a successful live path. -/
theorem eval_true_iff_livePath (graph : DAG n) (guarded : graph.Guarded)
    (K : Finset (Channel n)) (index : Fin graph.nodeCount) :
    graph.eval (assignmentOfSet K) index = true ↔
      ∃ head blocked, LivePath graph index head blocked ∧ head ∈ K ∧ Disjoint blocked K := by
  constructor
  · exact graph.exists_livePath_of_eval_true guarded K index
  · rintro ⟨head, blocked, path, headTrue, guardsFalse⟩
    exact path.eval_true K headTrue guardsFalse

/-- A true guarded value has a head whose retention suffices in every smaller set. -/
theorem exists_head_preserving_subsets (graph : DAG n) (guarded : graph.Guarded)
    (K : Finset (Channel n)) (index : Fin graph.nodeCount)
    (trueValue : graph.eval (assignmentOfSet K) index = true) :
    ∃ head, head ∈ K ∧ graph.IsPositiveHead index head ∧
      ∀ L : Finset (Channel n), head ∈ L → L ⊆ K →
        graph.eval (assignmentOfSet L) index = true := by
  obtain ⟨head, blocked, path, headTrue, guardsFalse⟩ :=
    graph.exists_livePath_of_eval_true guarded K index trueValue
  exact ⟨head, headTrue, ⟨blocked, path⟩,
    fun _ retained subset => path.eval_true_of_subset retained guardsFalse subset⟩

end DAG
end Controller.Decoder
