module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestZeroGrammar
public import Controller.Decoder.Cone

@[expose] public section

/-! Root-local zero queries retain original node identities and only rows
owned by a child-closed source cone. Their semantic correctness does not
require processing rows of unrelated nodes. Operational cone extraction and
source-row emission have separate fetched execution contracts.
-/
namespace Controller.Cost.ForestZeroCone
open Controller.Decoder Controller.Decoder.DAG Controller.CNF Controller.Decoder.ZeroSystem
variable {n : ℕ}

def LocalForward (graph : DAG n) (nodes : Finset (Fin graph.nodeCount))
    (channels : Assignment n) (activities : Fin graph.nodeCount → Bool) : Prop :=
  ∀ index ∈ nodes, ∀ clause ∈ graph.nodeClauses index,
    ClauseHolds (graph.zeroAssignment channels activities) clause

/-- Every live path in a closed source cone forces its root activity using
only original rows owned by retained nodes. -/
theorem path_activity (graph : DAG n) (nodes : Finset (Fin graph.nodeCount))
    (closed : graph.ChildClosed nodes) (K : Finset (Channel n))
    (activities : Fin graph.nodeCount → Bool)
    (forward : LocalForward graph nodes (assignmentOfSet K) activities)
    {index : Fin graph.nodeCount} {head : Channel n} {blocked : Finset (Channel n)}
    (path : LivePath graph index head blocked) :
    index ∈ nodes → head ∈ K → Disjoint blocked K → activities index = true := by
  induction path with
  | input index head gateEquation =>
      intro present headTrue _
      have row := forward index present (implicationClause (.inl head) [.inr index])
        (by simp [nodeClauses, gateEquation])
      have alternatives := (implicationClause_holds _ _ _).mp row
        ((assignmentOfSet_eq_true K head).mpr headTrue)
      simpa [zeroAssignment] using alternatives
  | disj index refs child head blocked gateEquation membership tail ih =>
      intro present headTrue guardsFalse
      have childPresent := closed index present child (by simpa [Gate.children, gateEquation] using membership)
      have childTrue := ih childPresent headTrue guardsFalse
      have row := forward index present
        (implicationClause (.inr (graph.childIndex index child)) [.inr index])
        (by simpa only [nodeClauses, gateEquation] using List.mem_map.mpr ⟨child, membership, rfl⟩)
      simpa [zeroAssignment] using (implicationClause_holds _ _ _).mp row childTrue
  | guard index child labels head blocked gateEquation tail ih =>
      intro present headTrue guardsFalse
      have childPresent := closed index present child (by simp [Gate.children, gateEquation])
      have childTrue := ih childPresent headTrue (guardsFalse.mono_left Finset.subset_union_right)
      have row := forward index present (implicationClause (.inr (graph.childIndex index child))
        (labels.map Sum.inl ++ [.inr index])) (by simp [nodeClauses, gateEquation])
      obtain ⟨literalVar, membership, trueValue⟩ := (implicationClause_holds _ _ _).mp row childTrue
      rcases List.mem_append.mp membership with guardMember | rootMember
      · obtain ⟨channel, channelMember, rfl⟩ := List.mem_map.mp guardMember
        have channelTrue : channel ∈ K := (assignmentOfSet_eq_true K channel).mp trueValue
        exact False.elim (Finset.disjoint_left.mp guardsFalse
          (Finset.mem_union_left _ (by simpa using channelMember)) channelTrue)
      · have equality : literalVar = .inr index := List.mem_singleton.mp rootMember
        subst literalVar
        exact trueValue

theorem local_eval_activity (graph : DAG n) (guarded : graph.Guarded)
    (nodes : Finset (Fin graph.nodeCount)) (closed : graph.ChildClosed nodes)
    (K : Finset (Channel n)) (activities : Fin graph.nodeCount → Bool)
    (forward : LocalForward graph nodes (assignmentOfSet K) activities)
    (root : Fin graph.nodeCount) (present : root ∈ nodes)
    (truth : graph.eval (assignmentOfSet K) root = true) : activities root = true := by
  obtain ⟨head, blocked, path, headTrue, guardsFalse⟩ :=
    graph.exists_livePath_of_eval_true guarded K root truth
  exact path_activity graph nodes closed K activities forward path present headTrue guardsFalse

/-- The complete root-local forward query is exact; omitted node rows are
unnecessary for both constructing a zero model and refuting a false zero. -/
theorem local_zero_iff (graph : DAG n) (guarded : graph.Guarded)
    (nodes : Finset (Fin graph.nodeCount)) (closed : graph.ChildClosed nodes)
    (K : Finset (Channel n)) (root : Fin graph.nodeCount) (present : root ∈ nodes) :
    (∃ activities, LocalForward graph nodes (assignmentOfSet K) activities ∧ activities root = false) ↔
      graph.eval (assignmentOfSet K) root = false := by
  constructor
  · rintro ⟨activities, forward, zero⟩
    apply Bool.eq_false_of_not_eq_true
    intro truth
    have positive := local_eval_activity graph guarded nodes closed K activities forward root present truth
    exact Bool.false_ne_true (zero.symm.trans positive)
  · intro zero
    exact ⟨graph.eval (assignmentOfSet K),
      fun index _ clause member => graph.exact_forwardModel guarded (assignmentOfSet K) index clause member, zero⟩

theorem cone_zero_iff (graph : DAG n) (guarded : graph.Guarded)
    (K : Finset (Channel n)) (root : Fin graph.nodeCount) :
    (∃ activities, LocalForward graph (graph.cone root) (assignmentOfSet K) activities ∧
      activities root = false) ↔ graph.eval (assignmentOfSet K) root = false :=
  local_zero_iff graph guarded (graph.cone root) (graph.cone_childClosed root) K root (graph.self_mem_cone root)

end Controller.Cost.ForestZeroCone
