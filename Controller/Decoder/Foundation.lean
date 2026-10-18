module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Decoder.Raw

@[expose] public section

/-! Public decoder foundation: intrinsically topological evaluation,
sharing-preserving cone extraction, and validated unordered-table numbering.
Representation-preserving operational costs are separate resource theorems. -/
namespace Controller.Decoder

theorem empty_or_value (assignment : Assignment n) (earlier : Fin available → Bool) :
    (Gate.disj [] : Gate n available).eval assignment earlier = false := rfl

theorem empty_guard_value (assignment : Assignment n) (earlier : Fin available → Bool)
    (child : Fin available) :
    (Gate.guard child []).eval assignment earlier = earlier child := by
  simp [Gate.eval]

theorem repeated_guard_value (assignment : Assignment n) (earlier : Fin available → Bool)
    (child : Fin available) (channel : Channel n) :
    (Gate.guard child [channel, channel]).eval assignment earlier =
      (Gate.guard child [channel]).eval assignment earlier := by
  simp [Gate.eval]

theorem guarded_own_head_false (assignment : Assignment n) (earlier : Fin available → Bool)
    (child : Fin available) (channel : Channel n) (head : earlier child = assignment channel) :
    (Gate.guard child [channel]).eval assignment earlier = false := by
  simp [Gate.eval, head]

/-- Every represented output incidence remains present, including repetitions. -/
theorem outputValues_length (graph : DAG n) (assignment : Assignment n) :
    (graph.outputValues assignment).length = graph.roots.length := by
  simp [DAG.outputValues]

/-- The decoder grammar has no standalone negated leaf or true constant.
A singleton channel outside the entire syntactic scope therefore evaluates
like the empty assignment, and its value is zero. -/
theorem unmarked_singleton_zero (graph : DAG n) (root : Fin graph.nodeCount)
    (head : Channel n) (unused : head ∉ graph.scope root) :
    graph.eval (assignmentOfSet {head}) root = false := by
  have agrees : ∀ i ∈ graph.scope root,
      assignmentOfSet {head} i = assignmentOfSet ∅ i := by
    intro i hi
    have different : i ≠ head := by
      intro equal
      subst i
      exact unused hi
    simp [assignmentOfSet, different]
  calc
    graph.eval (assignmentOfSet {head}) root = graph.eval (assignmentOfSet ∅) root :=
      graph.eval_eq_of_agree_scope _ _ root agrees
    _ = false := graph.eval_empty root

end Controller.Decoder
