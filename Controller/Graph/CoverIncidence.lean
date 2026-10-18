module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Graph.CoverCircuit

public import Mathlib.Tactic.Ring

@[expose] public section

/-! Clause occurrences are indexed by their positions in the complete formula.
Binary output-to-input clauses give a minor without identifying repeated rows. -/
namespace Controller.Graph
namespace ClauseOccurrence
variable {V : Type} [DecidableEq V] (clauses : List (CNF.Clause V))

abbrev Vertex := V ⊕ Fin clauses.length

def incidence : SimpleGraph (Vertex clauses) where
  Adj x y := match x, y with
    | .inl v, .inr i | .inr i, .inl v => v ∈ (clauses.get i).map Prod.fst
    | _, _ => False
  symm := ⟨by intro x y h; cases x <;> cases y <;> exact h⟩
  loopless := ⟨by intro x; cases x <;> simp⟩

/-- Only length-two rows contribute edges to this graph. -/
def binaryGraph : SimpleGraph V where
  Adj u v := u ≠ v ∧ ∃ p q : Bool,
    [(u,p),(v,q)] ∈ clauses ∨ [(v,q),(u,p)] ∈ clauses
  symm := ⟨by
    rintro u v ⟨ne, p, q, edge⟩
    exact ⟨ne.symm, q, p, edge.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- A binary row belongs to the branch of its first variable. -/
def ownsRow (v : V) (i : Fin clauses.length) : Prop :=
  ∃ p : Bool, ∃ lit : V × Bool, clauses.get i = [(v,p),lit]

noncomputable def branch [Fintype V] (v : V) : Finset (Vertex clauses) := by
  classical
  exact Finset.univ.filter fun x => match x with
    | .inl u => u = v
    | .inr i => ownsRow clauses v i

omit [DecidableEq V] in
@[simp] theorem variable_mem [Fintype V] (u v : V) :
    Sum.inl u ∈ branch clauses v ↔ u = v := by simp [branch]

omit [DecidableEq V] in
@[simp] theorem row_mem [Fintype V] (i : Fin clauses.length) (v : V) :
    Sum.inr i ∈ branch clauses v ↔ ownsRow clauses v i := by simp [branch]

omit [DecidableEq V] in
theorem owned_incident (v : V) (i : Fin clauses.length) (h : ownsRow clauses v i) :
    (incidence clauses).Adj (.inl v) (.inr i) := by
  obtain ⟨p, lit, eq⟩ := h
  change v ∈ (clauses.get i).map Prod.fst
  rw [eq]; simp

noncomputable def binaryMinor [Fintype V] : MinorModel (binaryGraph clauses) (incidence clauses) where
  branch := branch clauses
  connected v := by
    have hub : Sum.inl v ∈ branch clauses v := by simp
    refine ⟨⟨.inl v, hub⟩, ?_⟩
    have paths (x : Vertex clauses) (hx : x ∈ branch clauses v) :
        Relation.ReflTransGen (fun a b => a ∈ branch clauses v ∧ b ∈ branch clauses v ∧
          (incidence clauses).Adj a b) (.inl v) x ∧
        Relation.ReflTransGen (fun a b => a ∈ branch clauses v ∧ b ∈ branch clauses v ∧
          (incidence clauses).Adj a b) x (.inl v) := by
      cases x with
      | inl u => have eq := (variable_mem clauses u v).mp hx; subst u; exact ⟨.refl,.refl⟩
      | inr i =>
        have edge := owned_incident clauses v i ((row_mem clauses i v).mp hx)
        exact ⟨.single ⟨hub,hx,edge⟩, .single ⟨hx,hub,edge.symm⟩⟩
    intro x hx y hy
    exact (paths x hx).2.trans (paths y hy).1
  disjoint := by
    intro u v ne
    apply Finset.disjoint_left.mpr
    intro x hu hv
    cases x with
    | inl a => exact ne (((variable_mem clauses a u).mp hu).symm.trans ((variable_mem clauses a v).mp hv))
    | inr i =>
      obtain ⟨p, a, ha⟩ := (row_mem clauses i u).mp hu
      obtain ⟨q, b, hb⟩ := (row_mem clauses i v).mp hv
      have eq := ha.symm.trans hb
      exact ne (congrArg Prod.fst (List.cons.inj eq).1)
  edge := by
    rintro u v ⟨ne, p, q, forward | backward⟩
    · obtain ⟨i, hi⟩ := List.mem_iff_get.mp forward
      refine ⟨.inr i, (row_mem clauses i u).mpr ⟨p,(v,q),hi⟩,
        .inl v, (variable_mem clauses v v).mpr rfl, ?_⟩
      change v ∈ (clauses.get i).map Prod.fst
      rw [hi]; simp
    · obtain ⟨i, hi⟩ := List.mem_iff_get.mp backward
      refine ⟨.inl u, (variable_mem clauses u u).mpr rfl,
        .inr i, (row_mem clauses i v).mpr ⟨q,(u,p),hi⟩, ?_⟩
      change u ∈ (clauses.get i).map Prod.fst
      rw [hi]; simp

end ClauseOccurrence

namespace CoverCircuit
open Controller.Reductions Controller.Counting Controller.Native Controller.Native.Parameters
open Controller.Native.Bounded Controller.Graph.BoundedCircuit
variable {n m : ℕ} (J : EnumeratedGraph n m) (driver : Fin n) (layout : PrefixLayout)

def incidenceGraph := ClauseOccurrence.incidence (globalFormula (parameters J driver layout)).clauses.toList

def binaryNodeGraph : SimpleGraph (BoundedCover.Node n m) where
  Adj x y := (ClauseOccurrence.binaryGraph (globalFormula (parameters J driver layout)).clauses.toList).Adj
    (BoundedCover.embedding J driver layout x) (BoundedCover.embedding J driver layout y)
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem binary_core_edges (e : Fin m) :
    (binaryNodeGraph J driver layout).Adj (.inl (J.left e)) (.inr (.inl e)) ∧
    (binaryNodeGraph J driver layout).Adj (.inr (.inl e)) (.inr (.inr e)) ∧
    (binaryNodeGraph J driver layout).Adj (.inr (.inr e)) (.inl (J.right e)) := by
  have ne {x y : BoundedCover.Node n m} (h : x ≠ y) :
      BoundedCover.embedding J driver layout x ≠ BoundedCover.embedding J driver layout y :=
    fun eq => h (BoundedCover.embedding_injective J driver layout eq)
  obtain ⟨a,b,c⟩ := BoundedCover.edge_rows J driver layout e
  exact ⟨⟨ne (by simp), false, false, Or.inr a⟩,
    ⟨ne (by simp), true, false, Or.inr b⟩,
    ⟨ne (by simp), false, false, Or.inl c⟩⟩

/-- The complete occurrence-indexed incidence graph has at least the width of J. -/
theorem incidence_width_lower (c w : ℕ) (expansion : VertexExpansion J.graph c)
    (width : TreewidthLE (incidenceGraph J driver layout) w) : n ≤ 4*c*(w+1) := by
  let inclusion := MinorModel.ofInjective (BoundedCover.embedding J driver layout)
    (BoundedCover.embedding_injective J driver layout)
    (H := binaryNodeGraph J driver layout)
    (G := ClauseOccurrence.binaryGraph (globalFormula (parameters J driver layout)).clauses.toList)
    (by intro u v h; exact h)
  have binary := (ClauseOccurrence.binaryMinor (globalFormula (parameters J driver layout)).clauses.toList).treewidth_mono width
  have node := inclusion.treewidth_mono binary
  have source := (BoundedCover.patternMinor J _ (binary_core_edges J driver layout)).treewidth_mono node
  simpa only [Fintype.card_fin] using expansion_treewidth_lower c w expansion source

theorem incidence_width_size_lower (c D w : ℕ) (expansion : VertexExpansion J.graph c)
    (degree : ∀ v, (BoundedCover.neighbors J v).card ≤ D)
    (width : TreewidthLE (incidenceGraph J driver layout) w) :
    (BoundedCover.size J driver layout).total ≤ 12000*c*(D+1)*(w+1) := by
  calc
    _ ≤ 3000*(D+1)*n := BoundedCover.size_degree_linear J driver layout D degree
    _ ≤ 3000*(D+1)*(4*c*(w+1)) := Nat.mul_le_mul_left _ (incidence_width_lower J driver layout c w expansion width)
    _ = _ := by ring

theorem incidence_width_variableLiteralSize_lower (c D w : ℕ)
    (expansion : VertexExpansion J.graph c) (degree : ∀ v, (BoundedCover.neighbors J v).card ≤ D)
    (width : TreewidthLE (incidenceGraph J driver layout) w) :
    BoundedCover.variableLiteralSize J driver layout ≤ 12000*c*(D+1)*(w+1) :=
  (BoundedCover.variableLiteralSize_le J driver layout).trans
    (incidence_width_size_lower J driver layout c D w expansion degree width)
end CoverCircuit
end Controller.Graph
