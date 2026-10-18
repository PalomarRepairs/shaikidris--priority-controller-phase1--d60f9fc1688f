module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Decoder.Eval
public import Controller.Extensions.WitnessCount
public import Controller.Basic.Admissible
public import Mathlib.Logic.Relation
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

@[expose] public section

/-! Fixed per-node true choices and shared positive-support witnesses. -/
namespace Controller.Decoder

namespace Gate
/-- One true OR child is chosen per represented node; binary conjunction keeps
both references. Repeated references are identified in this finite set. -/
noncomputable def trueChildren (gate : Gate n available)
    (earlier : Fin available → Bool) : Finset (Fin available) := by
  classical
  exact match gate with
  | .zero => ∅
  | .input _ => ∅
  | .disj refs => if h : ∃ child ∈ refs, earlier child = true then
      {Classical.choose h} else ∅
  | .guard child _ => {child}
  | .liveAnd left right => {left, right}

theorem trueChildren_true (gate : Gate n available) (a : Assignment n)
    (earlier : Fin available → Bool) (active : gate.eval a earlier = true)
    {child : Fin available} (member : child ∈ gate.trueChildren earlier) :
    earlier child = true := by
  classical
  cases gate with
  | zero => simp [trueChildren] at member
  | input channel => simp [trueChildren] at member
  | disj refs =>
    have existsChild : ∃ child ∈ refs, earlier child = true := by
      simpa only [eval, List.any_eq_true] using active
    have childEq : child = Classical.choose existsChild := by
      simpa only [trueChildren, dite_eq_left existsChild, Finset.mem_singleton] using member
    subst child
    exact (Classical.choose_spec existsChild).2
  | guard chosen labels =>
    have childEq : child = chosen := by simpa [trueChildren] using member
    subst child
    exact (Bool.and_eq_true_iff.mp active).1
  | liveAnd left right =>
    rcases (by simpa [trueChildren] using member : child = left ∨ child = right) with rfl | rfl
    · exact (Bool.and_eq_true_iff.mp active).1
    · exact (Bool.and_eq_true_iff.mp active).2

/-- Positive channel labels are attached only to represented input nodes. -/
def positiveHead : Gate n available → Finset (Channel n)
  | .input channel => {channel}
  | _ => ∅
/-- Shrinking preserves a true gate when its selected positive dependencies
remain true. Negative guard labels can only turn off. -/
theorem eval_true_of_selected (gate : Gate n available)
    (a a' : Assignment n) (earlier earlier' : Fin available → Bool)
    (active : gate.eval a earlier = true)
    (heads : ∀ channel ∈ gate.positiveHead, a' channel = true)
    (shrinks : ∀ channel, a' channel = true → a channel = true)
    (children : ∀ child ∈ gate.trueChildren earlier, earlier' child = true) :
    gate.eval a' earlier' = true := by
  classical
  cases gate with
  | zero => exact False.elim (by simpa [eval] using active)
  | input channel => exact heads channel (by simp [positiveHead])
  | disj refs =>
    have existsChild : ∃ child ∈ refs, earlier child = true := by
      simpa only [eval, List.any_eq_true] using active
    apply List.any_eq_true.mpr
    refine ⟨Classical.choose existsChild, (Classical.choose_spec existsChild).1, ?_⟩
    apply children
    simp only [trueChildren, dite_eq_left existsChild, Finset.mem_singleton]
  | guard child labels =>
    have childTrue := children child (by simp [trueChildren])
    have originalFalse : labels.any a = false := by
      have negTrue := (Bool.and_eq_true_iff.mp active).2
      cases h : labels.any a <;> simp_all [eval]
    have newFalse : labels.any a' = false := by
      cases h : labels.any a' with
      | false => rfl
      | true =>
        obtain ⟨label, member, truth⟩ := List.any_eq_true.mp h
        have originalTrue : labels.any a = true :=
          List.any_eq_true.mpr ⟨label, member, shrinks label truth⟩
        rw [originalFalse] at originalTrue
        contradiction
    simp [eval, childTrue, newFalse]
  | liveAnd left right =>
    have leftTrue := children left (by simp [trueChildren])
    have rightTrue := children right (by simp [trueChildren])
    simp [eval, leftTrue, rightTrue]

theorem positiveHead_card (gate : Gate n available) :
    gate.positiveHead.card = if gate.positiveHead.Nonempty then 1 else 0 := by
  cases gate <;> simp [positiveHead]

theorem trueChildren_card_le (gate : Gate n available) (earlier : Fin available → Bool) :
    (gate.trueChildren earlier).card ≤
      (if gate.positiveHead.Nonempty then 0 else 1) +
      (if gate.isLiveAnd = true then 1 else 0) := by
  classical
  cases gate with
  | zero => simp [trueChildren, positiveHead, isLiveAnd]
  | input channel => simp [trueChildren, positiveHead, isLiveAnd]
  | disj refs =>
    by_cases h : ∃ child ∈ refs, earlier child = true
    · simp [trueChildren, h, positiveHead, isLiveAnd]
    · simp [trueChildren, h, positiveHead, isLiveAnd]
  | guard child labels => simp [trueChildren, positiveHead, isLiveAnd]
  | liveAnd left right =>
    by_cases same : left = right
    · simp [trueChildren, positiveHead, isLiveAnd, same]
    · simp [trueChildren, positiveHead, isLiveAnd, same]

end Gate

namespace DAG

noncomputable def trueChildren (graph : DAG n) (K : Finset (Channel n))
    (index : Fin graph.nodeCount) : Finset (Fin graph.nodeCount) := by
  classical
  exact ((graph.node index).trueChildren
    (fun child => graph.eval (assignmentOfSet K) (graph.childIndex index child))).image
      (graph.childIndex index)

/-- A single, consistent child selection is shared by every use of a node. -/
def TrueEdge (graph : DAG n) (K : Finset (Channel n))
    (parent child : Fin graph.nodeCount) : Prop := child ∈ graph.trueChildren K parent

noncomputable def witnessNodes (graph : DAG n) (K : Finset (Channel n))
    (root : Fin graph.nodeCount) : Finset (Fin graph.nodeCount) := by
  classical
  exact Finset.univ.filter (Relation.ReflTransGen (graph.TrueEdge K) root)

@[simp] theorem mem_witnessNodes (graph : DAG n) (K : Finset (Channel n))
    (root index : Fin graph.nodeCount) : index ∈ graph.witnessNodes K root ↔
    Relation.ReflTransGen (graph.TrueEdge K) root index := by
  classical
  simp [witnessNodes]

theorem root_mem_witnessNodes (graph : DAG n) (K : Finset (Channel n))
    (root : Fin graph.nodeCount) : root ∈ graph.witnessNodes K root := by
  exact (graph.mem_witnessNodes K root root).mpr Relation.ReflTransGen.refl

theorem witnessNodes_closed (graph : DAG n) (K : Finset (Channel n))
    (root : Fin graph.nodeCount) {parent child : Fin graph.nodeCount}
    (member : parent ∈ graph.witnessNodes K root)
    (edge : child ∈ graph.trueChildren K parent) : child ∈ graph.witnessNodes K root := by
  exact (graph.mem_witnessNodes K root child).mpr
    (((graph.mem_witnessNodes K root parent).mp member).tail edge)

theorem witnessNodes_parent (graph : DAG n) (K : Finset (Channel n))
    (root : Fin graph.nodeCount) {child : Fin graph.nodeCount}
    (member : child ∈ graph.witnessNodes K root) (different : child ≠ root) :
    ∃ parent ∈ graph.witnessNodes K root, child ∈ graph.trueChildren K parent := by
  rcases Relation.ReflTransGen.cases_tail
    ((graph.mem_witnessNodes K root child).mp member) with same | ⟨parent, path, edge⟩
  · exact False.elim (different same)
  · exact ⟨parent, (graph.mem_witnessNodes K root parent).mpr path, edge⟩

theorem trueChildren_true (graph : DAG n) (K : Finset (Channel n))
    (parent : Fin graph.nodeCount)
    (active : graph.eval (assignmentOfSet K) parent = true)
    {child : Fin graph.nodeCount} (member : child ∈ graph.trueChildren K parent) :
    graph.eval (assignmentOfSet K) child = true := by
  classical
  obtain ⟨ref, selected, rfl⟩ := Finset.mem_image.mp member
  exact Gate.trueChildren_true (graph.node parent) (assignmentOfSet K) _
    ((graph.eval_eq _ parent) ▸ active) selected

theorem witnessNodes_true (graph : DAG n) (K : Finset (Channel n))
    (root : Fin graph.nodeCount) (active : graph.eval (assignmentOfSet K) root = true)
    {index : Fin graph.nodeCount} (member : index ∈ graph.witnessNodes K root) :
    graph.eval (assignmentOfSet K) index = true := by
  have path := (graph.mem_witnessNodes K root index).mp member
  clear member
  induction path with
  | refl => exact active
  | tail path edge ih => exact graph.trueChildren_true K _ ih edge

noncomputable def positiveSupport (graph : DAG n) (K : Finset (Channel n))
    (root : Fin graph.nodeCount) : Finset (Channel n) := by
  classical
  exact (graph.witnessNodes K root).biUnion (fun index => (graph.node index).positiveHead)

theorem positiveSupport_subset (graph : DAG n) (K : Finset (Channel n))
    (root : Fin graph.nodeCount) (active : graph.eval (assignmentOfSet K) root = true) :
    graph.positiveSupport K root ⊆ K := by
  classical
  intro channel member
  obtain ⟨index, represented, head⟩ := Finset.mem_biUnion.mp member
  have truth := graph.witnessNodes_true K root active represented
  cases gateEq : graph.node index with
  | input label =>
    have eq : channel = label := by simpa [Gate.positiveHead, gateEq] using head
    subst channel
    rw [graph.eval_input (assignmentOfSet K) index label gateEq] at truth
    exact (assignmentOfSet_eq_true K label).mp truth
  | zero => simp [Gate.positiveHead, gateEq] at head
  | disj refs => simp [Gate.positiveHead, gateEq] at head
  | guard child labels => simp [Gate.positiveHead, gateEq] at head
  | liveAnd left right => simp [Gate.positiveHead, gateEq] at head

theorem trueChildren_lt (graph : DAG n) (K : Finset (Channel n))
    (parent : Fin graph.nodeCount) {child : Fin graph.nodeCount}
    (member : child ∈ graph.trueChildren K parent) : child.val < parent.val := by
  classical
  obtain ⟨ref, selected, rfl⟩ := Finset.mem_image.mp member
  exact graph.childIndex_lt parent ref

/-- Every intermediate set between the positive support and the original true
set preserves the complete selected witness, including all negative guards. -/
theorem positiveSupport_preserves (graph : DAG n) (K J : Finset (Channel n))
    (root : Fin graph.nodeCount) (active : graph.eval (assignmentOfSet K) root = true)
    (contains : graph.positiveSupport K root ⊆ J) (shrinks : J ⊆ K) :
    graph.eval (assignmentOfSet J) root = true := by
  classical
  have claim : ∀ bound : ℕ, ∀ index : Fin graph.nodeCount, index.val = bound →
      index ∈ graph.witnessNodes K root → graph.eval (assignmentOfSet J) index = true := by
    intro bound
    induction bound using Nat.strong_induction_on with
    | h bound ih =>
      intro index rankEq member
      rw [graph.eval_eq]
      apply Gate.eval_true_of_selected (graph.node index) (assignmentOfSet K)
        (assignmentOfSet J) (fun ref => graph.eval (assignmentOfSet K) (graph.childIndex index ref))
        (fun ref => graph.eval (assignmentOfSet J) (graph.childIndex index ref))
      · rw [← graph.eval_eq]
        exact graph.witnessNodes_true K root active member
      · intro channel head
        apply (assignmentOfSet_eq_true J channel).mpr
        exact contains (Finset.mem_biUnion.mpr ⟨index, member, head⟩)
      · intro channel truth
        exact (assignmentOfSet_eq_true K channel).mpr
          (shrinks ((assignmentOfSet_eq_true J channel).mp truth))
      · intro ref chosen
        have edge : graph.childIndex index ref ∈ graph.trueChildren K index :=
          Finset.mem_image.mpr ⟨ref, chosen, rfl⟩
        exact ih ref.val (by simpa only [rankEq] using ref.isLt)
          (graph.childIndex index ref) rfl (graph.witnessNodes_closed K root member edge)
  exact claim root.val root rfl (graph.root_mem_witnessNodes K root)

theorem positiveSupport_true (graph : DAG n) (K : Finset (Channel n))
    (root : Fin graph.nodeCount) (active : graph.eval (assignmentOfSet K) root = true) :
    graph.eval (assignmentOfSet (graph.positiveSupport K root)) root = true :=
  graph.positiveSupport_preserves K _ root active (Finset.Subset.refl _)
    (graph.positiveSupport_subset K root active)

theorem positiveSupport_nonempty (graph : DAG n) (K : Finset (Channel n))
    (root : Fin graph.nodeCount) (active : graph.eval (assignmentOfSet K) root = true) :
    (graph.positiveSupport K root).Nonempty := by
  have truth := graph.positiveSupport_true K root active
  by_contra empty
  have eq : graph.positiveSupport K root = ∅ := Finset.not_nonempty_iff_eq_empty.mp empty
  rw [eq, graph.eval_empty] at truth
  contradiction

/-- Adjoining the target is valid precisely here because the target belongs to
original K; every negative label continues to avoid the resulting subset. -/
theorem positiveSupport_insert_target_true (graph : DAG n) (K : Finset (Channel n))
    (root : Fin graph.nodeCount) (active : graph.eval (assignmentOfSet K) root = true)
    (target : Channel n) (targetIn : target ∈ K) :
    graph.eval (assignmentOfSet (insert target (graph.positiveSupport K root))) root = true := by
  apply graph.positiveSupport_preserves K _ root active
  · exact Finset.subset_insert _ _
  · exact Finset.insert_subset targetIn (graph.positiveSupport_subset K root active)

theorem positiveSupport_admissible (graph : DAG n) (K : Finset (Channel n))
    (root : Fin graph.nodeCount) (active : graph.eval (assignmentOfSet K) root = true)
    (target : Channel n) (busCount : ℕ) (many : 2 ≤ busCount) :
    Admissible busCount target (graph.positiveSupport K root) :=
  (admissible_many many target _).mpr (graph.positiveSupport_nonempty K root active)

/-- Distinct represented input nodes of the selected witness. -/
noncomputable def witnessInputs (graph : DAG n) (K : Finset (Channel n))
    (root : Fin graph.nodeCount) : Finset (Fin graph.nodeCount) := by
  classical
  exact (graph.witnessNodes K root).filter (fun index => (graph.node index).positiveHead.Nonempty)

/-- Channel sharing and repeated positive heads cannot increase this count. -/
theorem positiveSupport_card_le_inputs (graph : DAG n) (K : Finset (Channel n))
    (root : Fin graph.nodeCount) :
    (graph.positiveSupport K root).card ≤ (graph.witnessInputs K root).card := by
  classical
  calc
    (graph.positiveSupport K root).card ≤
        ∑ index ∈ graph.witnessNodes K root, (graph.node index).positiveHead.card :=
      Finset.card_biUnion_le
    _ = (graph.witnessInputs K root).card := by
      simp only [Gate.positiveHead_card, witnessInputs, Finset.card_filter]

theorem witnessInputs_subset (graph : DAG n) (K : Finset (Channel n))
    (root : Fin graph.nodeCount) : graph.witnessInputs K root ⊆ graph.witnessNodes K root := by
  classical
  exact Finset.filter_subset _ _

/-- The positive support counts distinct channel heads and is bounded by the
number of distinct represented binary conjunctions, even with DAG sharing. -/
theorem positiveSupport_card_le (graph : DAG n) (K : Finset (Channel n))
    (root : Fin graph.nodeCount) :
    (graph.positiveSupport K root).card ≤ graph.liveAndCount + 1 := by
  classical
  apply (graph.positiveSupport_card_le_inputs K root).trans
  apply Controller.Extensions.WitnessCount.leaf_bound_all
    (graph.witnessNodes K root) (graph.witnessInputs K root) graph.liveAndNodes root
    (graph.trueChildren K) (graph.root_mem_witnessNodes K root)
    (graph.witnessInputs_subset K root)
  · intro index member different
    exact graph.witnessNodes_parent K root member different
  · intro index member
    have smaller : (graph.trueChildren K index).card ≤
        ((graph.node index).trueChildren
          (fun ref => graph.eval (assignmentOfSet K) (graph.childIndex index ref))).card :=
      Finset.card_image_le
    have localBound := (graph.node index).trueChildren_card_le
      (fun ref => graph.eval (assignmentOfSet K) (graph.childIndex index ref))
    simpa [witnessInputs, member, liveAndNodes] using smaller.trans localBound

/-- The complete bounded positive-support conclusion for an arbitrary true set. -/
theorem exists_small_true_support (graph : DAG n) (K : Finset (Channel n))
    (root : Fin graph.nodeCount) (active : graph.eval (assignmentOfSet K) root = true)
    (k : ℕ) (bound : graph.liveAndCount ≤ k) :
    ∃ support : Finset (Channel n), support ⊆ K ∧ support.Nonempty ∧
      support.card ≤ k + 1 ∧ graph.eval (assignmentOfSet support) root = true := by
  refine ⟨graph.positiveSupport K root, graph.positiveSupport_subset K root active,
    graph.positiveSupport_nonempty K root active, ?_, graph.positiveSupport_true K root active⟩
  exact (graph.positiveSupport_card_le K root).trans (Nat.add_le_add_right bound 1)

/-- A target already in K can be retained with a size increase of at most one;
the resulting true set is admissible for any bus count. -/
theorem exists_small_target_support (graph : DAG n) (K : Finset (Channel n))
    (root : Fin graph.nodeCount) (active : graph.eval (assignmentOfSet K) root = true)
    (target : Channel n) (targetIn : target ∈ K)
    (k : ℕ) (bound : graph.liveAndCount ≤ k) (busCount : ℕ) :
    ∃ support : Finset (Channel n), support ⊆ K ∧ target ∈ support ∧
      support.card ≤ k + 2 ∧ Admissible busCount target support ∧
      graph.eval (assignmentOfSet support) root = true := by
  let support := insert target (graph.positiveSupport K root)
  have targetMember : target ∈ support := Finset.mem_insert_self _ _
  have count := graph.positiveSupport_card_le K root
  have inserted := Finset.card_insert_le target (graph.positiveSupport K root)
  refine ⟨support, Finset.insert_subset targetIn (graph.positiveSupport_subset K root active),
    targetMember, ?_, ⟨⟨target, targetMember⟩, fun _ => targetMember⟩,
    graph.positiveSupport_insert_target_true K root active target targetIn⟩
  dsimp [support]
  omega

end DAG
end Controller.Decoder
