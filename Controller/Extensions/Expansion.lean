module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Decoder.Cone
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.BigOperators

@[expose] public section

/-! Guarded expansions use one Boolean choice per represented binary AND.
Closed node sets give cone-local identities; the universal set gives a single
selector preserving every stored node and therefore every observed root. -/
namespace Controller.Decoder
namespace Gate

/-- An empty negative guard is an alias of the selected live child. -/
def resolve (gate : Gate n available) (choice : Bool) : Gate n available :=
  match gate with
  | .liveAnd left right => .guard (if choice then right else left) []
  | other => other

def preservingChoice (gate : Gate n available) (earlier : Fin available → Bool) : Bool :=
  match gate with
  | .liveAnd left _ => earlier left
  | _ => false

@[simp] theorem resolve_guarded (gate : Gate n available) (choice : Bool) :
    (gate.resolve choice).IsGuarded := by
  cases gate <;> simp [resolve, IsGuarded, isLiveAnd]

theorem resolve_children_subset (gate : Gate n available) (choice : Bool) :
    ∀ child ∈ (gate.resolve choice).children, child ∈ gate.children := by
  cases gate <;> cases choice <;> simp [resolve, children]

theorem preservingChoice_false (gate : Gate n available) (earlier : Fin available → Bool)
    (notAnd : gate.isLiveAnd ≠ true) : gate.preservingChoice earlier = false := by
  cases gate <;> simp_all [preservingChoice, isLiveAnd]

theorem resolve_preserves (gate : Gate n available) (a : Assignment n)
    (earlier : Fin available → Bool) :
    (gate.resolve (gate.preservingChoice earlier)).eval a earlier = gate.eval a earlier := by
  cases gate with
  | liveAnd left right =>
    cases hl : earlier left <;> cases hr : earlier right <;> simp [resolve, preservingChoice, eval, hl, hr]
  | zero => rfl
  | input channel => rfl
  | disj refs => rfl
  | guard child labels => rfl

/-- Every operation is monotone in live children, with channel guards fixed. -/
theorem resolve_true_of_true (gate : Gate n available) (choice : Bool)
    (a : Assignment n) (earlier later : Fin available → Bool)
    (children : ∀ child ∈ gate.children, earlier child = true → later child = true)
    (active : gate.eval a earlier = true) : (gate.resolve choice).eval a later = true := by
  cases gate with
  | zero => simp [eval] at active
  | input channel => exact active
  | disj refs =>
    obtain ⟨child, member, truth⟩ := List.any_eq_true.mp active
    exact List.any_eq_true.mpr ⟨child, member, children child member truth⟩
  | guard child labels =>
    have parts := Bool.and_eq_true_iff.mp active
    have truth := children child (by simp [Gate.children]) parts.1
    simp [resolve, eval, truth, parts.2]
  | liveAnd left right =>
    have parts := Bool.and_eq_true_iff.mp active
    have leftTrue := children left (by simp [Gate.children]) parts.1
    have rightTrue := children right (by simp [Gate.children]) parts.2
    cases choice <;> simp [resolve, eval, leftTrue, rightTrue]
end Gate

namespace DAG

/-- Choices are indexed by stored AND identities in the supplied node set. -/
abbrev Selector (graph : DAG n) (nodes : Finset (Fin graph.nodeCount)) :=
  {index // index ∈ nodes ∩ graph.liveAndNodes} → Bool

noncomputable def selectedChoice (graph : DAG n) (nodes : Finset (Fin graph.nodeCount))
    (selector : graph.Selector nodes) (index : Fin graph.nodeCount) : Bool := by
  classical
  exact if h : index ∈ nodes ∩ graph.liveAndNodes then selector ⟨index, h⟩ else false

/-- Every stored AND is replaced once. Outside the selected node set the left
child is used; cone conclusions make no assertion about these outside values. -/
@[reducible] noncomputable def expansion (graph : DAG n) (nodes : Finset (Fin graph.nodeCount))
    (selector : graph.Selector nodes) : DAG n where
  nodeCount := graph.nodeCount
  node index := (graph.node index).resolve (graph.selectedChoice nodes selector index)
  roots := graph.roots

theorem expansion_guarded (graph : DAG n) (nodes : Finset (Fin graph.nodeCount))
    (selector : graph.Selector nodes) : (graph.expansion nodes selector).Guarded := by
  intro index
  exact Gate.resolve_guarded _ _

theorem selector_count (graph : DAG n) (nodes : Finset (Fin graph.nodeCount)) :
    Fintype.card (graph.Selector nodes) = 2 ^ (nodes ∩ graph.liveAndNodes).card := by
  classical
  change Fintype.card ((↥(nodes ∩ graph.liveAndNodes)) → Bool) = _
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]

theorem selector_count_le (graph : DAG n) (nodes : Finset (Fin graph.nodeCount))
    (k : ℕ) (bound : (nodes ∩ graph.liveAndNodes).card ≤ k) :
    Fintype.card (graph.Selector nodes) ≤ 2 ^ k := by
  rw [graph.selector_count]
  exact Nat.pow_le_pow_right (by decide) bound

/-- Dropping a conjunction operand can only increase every stored node value. -/
theorem true_implies_expansion_true (graph : DAG n) (nodes : Finset (Fin graph.nodeCount))
    (selector : graph.Selector nodes) (a : Assignment n) (index : Fin graph.nodeCount)
    (active : graph.eval a index = true) : (graph.expansion nodes selector).eval a index = true := by
  have claim : ∀ bound : ℕ, ∀ current : Fin graph.nodeCount, current.val = bound →
      graph.eval a current = true → (graph.expansion nodes selector).eval a current = true := by
    intro bound
    induction bound using Nat.strong_induction_on with
    | h bound ih =>
      intro current rankEq truth
      rw [DAG.eval_eq]
      change ((graph.node current).resolve (graph.selectedChoice nodes selector current)).eval a
        (fun ref => (graph.expansion nodes selector).eval a (graph.childIndex current ref)) = true
      apply Gate.resolve_true_of_true
      · intro ref member childTrue
        exact ih ref.val (by simpa only [rankEq] using ref.isLt) _ rfl childTrue
      · exact (graph.eval_eq a current) ▸ truth
  exact claim index.val index rfl active

noncomputable def preservingSelector (graph : DAG n) (nodes : Finset (Fin graph.nodeCount))
    (a : Assignment n) : graph.Selector nodes :=
  fun index => (graph.node index.val).preservingChoice
    (fun ref => graph.eval a (graph.childIndex index.val ref))

theorem selectedChoice_preserving (graph : DAG n) (nodes : Finset (Fin graph.nodeCount))
    (a : Assignment n) (index : Fin graph.nodeCount) (member : index ∈ nodes) :
    graph.selectedChoice nodes (graph.preservingSelector nodes a) index =
      (graph.node index).preservingChoice (fun ref => graph.eval a (graph.childIndex index ref)) := by
  classical
  by_cases h : index ∈ nodes ∩ graph.liveAndNodes
  · simp [selectedChoice, h, preservingSelector]
  · have notAnd : (graph.node index).isLiveAnd ≠ true := by
      intro yes
      exact h (Finset.mem_inter.mpr ⟨member, by simp [liveAndNodes, yes]⟩)
    simp [selectedChoice, h, Gate.preservingChoice_false _ _ notAnd]

/-- One input-dependent selector preserves every value in a child-closed set.
This is simultaneous induction on stored node identities, with no unfolding. -/
theorem preserving_expansion_eq (graph : DAG n) (nodes : Finset (Fin graph.nodeCount))
    (closed : graph.ChildClosed nodes) (a : Assignment n)
    (index : Fin graph.nodeCount) (member : index ∈ nodes) :
    (graph.expansion nodes (graph.preservingSelector nodes a)).eval a index = graph.eval a index := by
  have claim : ∀ bound : ℕ, ∀ current : Fin graph.nodeCount, current.val = bound →
      current ∈ nodes →
      (graph.expansion nodes (graph.preservingSelector nodes a)).eval a current = graph.eval a current := by
    intro bound
    induction bound using Nat.strong_induction_on with
    | h bound ih =>
      intro current rankEq inside
      rw [DAG.eval_eq, graph.eval_eq]
      change ((graph.node current).resolve
        (graph.selectedChoice nodes (graph.preservingSelector nodes a) current)).eval a
        (fun ref => (graph.expansion nodes (graph.preservingSelector nodes a)).eval a
          (graph.childIndex current ref)) = (graph.node current).eval a
            (fun ref => graph.eval a (graph.childIndex current ref))
      rw [graph.selectedChoice_preserving nodes a current inside]
      calc
        _ = ((graph.node current).resolve ((graph.node current).preservingChoice
            (fun ref => graph.eval a (graph.childIndex current ref)))).eval a
              (fun ref => graph.eval a (graph.childIndex current ref)) := by
          apply Gate.eval_congr
          · intro channel _
            rfl
          · intro ref selected
            exact ih ref.val (by simpa only [rankEq] using ref.isLt) _ rfl
              (closed current inside ref (Gate.resolve_children_subset _ _ ref selected))
        _ = _ := Gate.resolve_preserves _ _ _
  exact claim index.val index rfl member

/-- The original is the conjunction of every consistently selected expansion. -/
theorem expansion_identity (graph : DAG n) (nodes : Finset (Fin graph.nodeCount))
    (closed : graph.ChildClosed nodes) (a : Assignment n)
    (index : Fin graph.nodeCount) (member : index ∈ nodes) :
    graph.eval a index = true ↔
      ∀ selector : graph.Selector nodes, (graph.expansion nodes selector).eval a index = true := by
  constructor
  · exact fun truth selector => graph.true_implies_expansion_true nodes selector a index truth
  · intro allTrue
    rw [← graph.preserving_expansion_eq nodes closed a index member]
    exact allTrue (graph.preservingSelector nodes a)

/-- The universal selector domain preserves all stored nodes with one selector,
so every output shares the same consistent choices. -/
theorem exists_global_preserving_selector (graph : DAG n) (a : Assignment n) :
    ∃ selector : graph.Selector Finset.univ,
      ∀ index : Fin graph.nodeCount, (graph.expansion Finset.univ selector).eval a index = graph.eval a index := by
  refine ⟨graph.preservingSelector Finset.univ a, ?_⟩
  intro index
  exact graph.preserving_expansion_eq Finset.univ (by intro _ _ _ _; simp)
    a index (by simp)

/-- Root-cone choices charge only represented ANDs reachable from that root. -/
theorem cone_expansion_identity (graph : DAG n) (a : Assignment n)
    (root : Fin graph.nodeCount) :
    graph.eval a root = true ↔ ∀ selector : graph.Selector (graph.cone root),
      (graph.expansion (graph.cone root) selector).eval a root = true :=
  graph.expansion_identity (graph.cone root) (graph.cone_childClosed root) a root
    (graph.self_mem_cone root)

noncomputable def expansionConjunction (graph : DAG n)
    (nodes : Finset (Fin graph.nodeCount)) (a : Assignment n)
    (index : Fin graph.nodeCount) : Bool := by
  classical
  exact (Finset.univ.toList.map (fun selector : graph.Selector nodes =>
    (graph.expansion nodes selector).eval a index)).all id

theorem eval_eq_expansionConjunction (graph : DAG n)
    (nodes : Finset (Fin graph.nodeCount)) (closed : graph.ChildClosed nodes)
    (a : Assignment n) (index : Fin graph.nodeCount) (member : index ∈ nodes) :
    graph.eval a index = graph.expansionConjunction nodes a index := by
  classical
  apply Bool.eq_iff_iff.mpr
  rw [graph.expansion_identity nodes closed a index member]
  simp [expansionConjunction, List.all_eq_true]

theorem global_selector_count (graph : DAG n) :
    Fintype.card (graph.Selector Finset.univ) = 2 ^ graph.liveAndCount := by
  rw [graph.selector_count Finset.univ]
  simp [liveAndCount]

theorem cone_selector_count (graph : DAG n) (root : Fin graph.nodeCount) :
    Fintype.card (graph.Selector (graph.cone root)) =
      2 ^ ((graph.cone root) ∩ graph.liveAndNodes).card := graph.selector_count _

end DAG
end Controller.Decoder
