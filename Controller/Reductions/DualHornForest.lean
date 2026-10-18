module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Reductions.DualHornDecoder
public import Controller.Decoder.Forest
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.List.FinRange

@[expose] public section

/-! # Private internal gates in the dual-Horn reduction -/
namespace Controller.Reductions.DualHorn
open Controller.CNF Controller.Decoder Controller.Horn.Worklist

/-- A final OR over distinct terms whose live children are terminals is a stored forest. -/
private theorem oneLayer_storedForest (graph : DAG n) (top : Fin graph.nodeCount)
    (guarded : graph.Guarded) (roots : graph.roots = [top])
    (maximum : ∀ index : Fin graph.nodeCount, index.val ≤ top.val)
    (terminal : ∀ parent : Fin graph.nodeCount, parent ≠ top →
      ∀ child ∈ (graph.node parent).children,
        (graph.node (graph.childIndex parent child)).isInternal = false)
    (distinct : (graph.node top).children.Nodup) : graph.StoredForest := by
  refine ⟨guarded, ?_⟩
  intro node internal
  rw [Nat.card_eq_fintype_card]
  apply Fintype.card_le_one_iff_subsingleton.mpr
  refine ⟨?_⟩
  intro first second
  apply Subtype.ext
  rcases first with ⟨first, firstRef⟩
  rcases second with ⟨second, secondRef⟩
  have parentTop : ∀ use : graph.ParentOccurrence,
      graph.refers (.inr use) = node → use.1 = top := by
    intro use reference
    by_contra different
    have zero := terminal use.1 different ((graph.node use.1).children.get use.2)
      (List.get_mem _ _)
    have same : graph.childIndex use.1 ((graph.node use.1).children.get use.2) = node := reference
    rw [same] at zero
    rw [internal] at zero
    contradiction
  have rootTop : ∀ position : Fin graph.roots.length, graph.refers (.inl position) = top := by
    intro position
    simp [DAG.refers, roots]
  cases first with
  | inl a =>
    cases second with
    | inl b =>
      have equal : a = b := by
        apply Fin.ext
        have length : graph.roots.length = 1 := by simp [roots]
        have aa := a.isLt
        have bb := b.isLt
        omega
      subst b
      rfl
    | inr b =>
      have root := rootTop a
      have ref := firstRef
      have last : node = top := root.symm.trans ref |>.symm
      have before := graph.childIndex_lt b.1 ((graph.node b.1).children.get b.2)
      have val := congrArg Fin.val secondRef
      simp only [DAG.refers, DAG.childIndex_val] at val
      have max := maximum b.1
      have nodeval := congrArg Fin.val last
      omega
  | inr a =>
    cases second with
    | inl b =>
      have root := rootTop b
      have ref := secondRef
      have last : node = top := root.symm.trans ref |>.symm
      have before := graph.childIndex_lt a.1 ((graph.node a.1).children.get a.2)
      have val := congrArg Fin.val firstRef
      simp only [DAG.refers, DAG.childIndex_val] at val
      have max := maximum a.1
      have nodeval := congrArg Fin.val last
      omega
    | inr b =>
      have ap := parentTop a firstRef
      have bp := parentTop b secondRef
      rcases a with ⟨aprent, apos⟩
      rcases b with ⟨bprent, bpos⟩
      dsimp at ap bp
      subst aprent
      subst bprent
      have equality : (graph.node top).children.get apos = (graph.node top).children.get bpos := by
        apply Fin.ext
        have same := congrArg Fin.val (firstRef.trans secondRef.symm)
        exact same
      have positions := distinct.injective_get equality
      subst bpos
      rfl

private theorem violationGate_children_input (rule : Rule (Channel (n + 2)))
    (available : ℕ) (bound : n + 2 ≤ available) (child : Fin available)
    (present : child ∈ (violationGate rule available bound).children) : child.val < n + 2 := by
  cases rule with
  | skip => simp [violationGate, Gate.children] at present
  | positive labels =>
    simp only [violationGate, Gate.children, List.mem_singleton] at present
    subst child
    change n < n + 2
    omega
  | negative head labels =>
    simp only [violationGate, Gate.children, List.mem_singleton] at present
    subst child
    exact head.isLt

/-- Every internal term is used once by the final OR; shared inputs stay terminals. -/
theorem decoder_storedForest (formula : FiniteFormula n) : (decoder formula).StoredForest := by
  let top : Fin (decoder formula).nodeCount :=
    ⟨n + formula.clauses.size + 3, by change n + formula.clauses.size + 3 < n + formula.clauses.size + 4; omega⟩
  apply oneLayer_storedForest (decoder formula) top (decoder_guarded formula) rfl
  · intro index
    have limit := index.isLt
    change index.val < n + formula.clauses.size + 4 at limit
    change index.val ≤ n + formula.clauses.size + 3
    omega
  · intro parent different child present
    by_cases input : parent.val < n + 2
    · simp only [decoder, dite_eq_left input, Gate.children] at present
      simp at present
    · by_cases term : parent.val < n + formula.clauses.size + 3
      · have inputBound : n + 2 ≤ parent.val := by omega
        have seen : child ∈ (violationGate
            (storedRule formula ⟨parent.val - (n + 2), by omega⟩) parent.val inputBound).children := by
          simpa only [decoder, dite_eq_right input, dite_eq_left term] using present
        have small := violationGate_children_input _ _ _ child seen
        have smallIndex : ((decoder formula).childIndex parent child).val < n + 2 := small
        change ((decoder formula).node ⟨child.val, by change child.val < n + formula.clauses.size + 4; omega⟩).isInternal = false
        simp only [decoder, small, dite_true, Gate.isInternal]
      · have last : parent = top := by
          apply Fin.ext
          have limit := parent.isLt
          change parent.val < n + formula.clauses.size + 4 at limit
          change parent.val = n + formula.clauses.size + 3
          omega
        exact False.elim (different last)
  · have notInput : ¬n + formula.clauses.size + 3 < n + 2 := by omega
    change ((decoder formula).node
      ⟨n + formula.clauses.size + 3, by change n + formula.clauses.size + 3 < n + formula.clauses.size + 4; omega⟩).children.Nodup
    simp only [decoder, notInput, dite_false, lt_self_iff_false, Gate.children]
    apply List.nodup_ofFn_ofInjective
    intro a b same
    apply Fin.ext
    have values := congrArg Fin.val same
    dsimp only at values
    omega

theorem decoder_formulaForest (formula : FiniteFormula n) : (decoder formula).FormulaForest :=
  (decoder formula).storedForest_formulaForest (decoder_storedForest formula)

end Controller.Reductions.DualHorn
