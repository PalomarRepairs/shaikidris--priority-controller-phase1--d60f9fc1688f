module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Graph.TreeDecomposition
public import Mathlib.Logic.Relation

@[expose] public section

/-! Finite branch-set minors and transport of actual tree decompositions. -/
namespace Controller.Graph

variable {V W : Type} [DecidableEq V] [DecidableEq W]

/-- Connectivity within the listed vertices, with paths retaining membership. -/
def ConnectedWithin (G : SimpleGraph V) (S : Finset V) : Prop :=
  S.Nonempty ∧ ∀ u ∈ S, ∀ v ∈ S,
    Relation.ReflTransGen (fun x y => x ∈ S ∧ y ∈ S ∧ G.Adj x y) u v

/-- A minor model uses nonempty, disjoint, connected finite branch sets. -/
structure MinorModel (H : SimpleGraph W) (G : SimpleGraph V) where
  branch : W → Finset V
  connected : ∀ w, ConnectedWithin G (branch w)
  disjoint : ∀ ⦃u v⦄, u ≠ v → Disjoint (branch u) (branch v)
  edge : ∀ ⦃u v⦄, H.Adj u v →
    ∃ x ∈ branch u, ∃ y ∈ branch v, G.Adj x y

namespace TreeDecomposition
variable {G : SimpleGraph V} (D : TreeDecomposition G)

omit [DecidableEq V] in
/-- The union of bag subtrees of a connected graph vertex set is a subtree. -/
theorem connected_region (S : Finset V) (connected : ConnectedWithin G S) :
    ∃ r : D.tree,
      (∃ v ∈ S, r = D.home v) ∧
      (∀ v ∈ S, ∀ i, v ∈ D.bag i → r ≤ i) ∧
      (∀ v ∈ S, ∀ i, v ∈ D.bag i → ∀ j, r ≤ j → j ≤ i →
        ∃ u ∈ S, u ∈ D.bag j) := by
  obtain ⟨start, minimal⟩ := S.exists_minimalFor D.home connected.1
  have paths : ∀ v ∈ S,
      D.home start ≤ D.home v ∧
      (∀ i, v ∈ D.bag i → ∀ j, D.home start ≤ j → j ≤ i →
        ∃ u ∈ S, u ∈ D.bag j) := by
    intro v hv
    have reach := connected.2 start minimal.1 v hv
    induction reach with
    | refl =>
      exact ⟨le_rfl, fun i hi j hj hji =>
        ⟨start, minimal.1, D.interval start i j hi hj hji⟩⟩
    | @tail current next path step ih =>
      have ih := ih step.1
      obtain ⟨i, current_mem, next_mem⟩ := D.edge step.2.2
      have root_le_i := ih.1.trans (D.above_home current i current_mem)
      have next_le_i := D.above_home next i next_mem
      have root_le_next : D.home start ≤ D.home next := by
        rcases le_total_of_directed root_le_i next_le_i with h | h
        · exact minimal.2 step.2.1 h
        · exact h
      refine ⟨root_le_next, ?_⟩
      intro k hk j hj hjk
      rcases le_total_of_directed hjk (D.above_home next k hk) with h | h
      · exact ⟨next, step.2.1, D.interval next k j hk h hjk⟩
      · exact ih.2 i current_mem j hj (h.trans next_le_i)
  refine ⟨D.home start, ⟨start, minimal.1, rfl⟩, ?_, ?_⟩
  · intro v hv i hi
    exact (paths v hv).1.trans (D.above_home v i hi)
  · intro v hv
    exact (paths v hv).2

end TreeDecomposition

namespace MinorModel
variable {G : SimpleGraph V} {H : SimpleGraph W} (M : MinorModel H G)

/-- An injective edge-preserving map is a minor with singleton branch sets. -/
def ofInjective (f : W → V) (injective : Function.Injective f)
    (edges : ∀ ⦃u v⦄, H.Adj u v → G.Adj (f u) (f v)) : MinorModel H G where
  branch w := {f w}
  connected w := by
    refine ⟨Finset.singleton_nonempty _, ?_⟩
    intro u hu v hv
    have hu : u = f w := Finset.mem_singleton.mp hu
    have hv : v = f w := Finset.mem_singleton.mp hv
    subst u; subst v
    exact .refl
  disjoint := by
    intro u v ne
    simp only [Finset.disjoint_singleton_left, Finset.mem_singleton]
    exact fun eq => ne (injective eq)
  edge := by
    intro u v h
    exact ⟨f u, Finset.mem_singleton_self _, f v, Finset.mem_singleton_self _, edges h⟩

omit [DecidableEq V] in
/-- Distinct branch sets cannot contain the same host vertex. -/
theorem eq_of_mem {u v : W} {x : V} (hu : x ∈ M.branch u) (hv : x ∈ M.branch v) :
    u = v := by
  by_contra h
  exact Finset.disjoint_left.mp (M.disjoint h) hu hv

/-- Transport finite branch sets along an injective edge-preserving map. -/
def map {U : Type} [DecidableEq U] {Q : SimpleGraph U}
    (f : V → U) (injective : Function.Injective f)
    (edges : ∀ ⦃x y⦄, G.Adj x y → Q.Adj (f x) (f y)) : MinorModel H Q where
  branch v := (M.branch v).image f
  connected v := by
    refine ⟨(M.connected v).1.image f, ?_⟩
    intro x hx y hy
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hy
    apply ((M.connected v).2 a ha b hb).lift f
    intro u z h
    exact ⟨Finset.mem_image.mpr ⟨u,h.1,rfl⟩,
      Finset.mem_image.mpr ⟨z,h.2.1,rfl⟩, edges h.2.2⟩
  disjoint := by
    intro u v ne
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b,hb,eq⟩ := Finset.mem_image.mp hy
    have same := injective eq
    subst b
    exact ne (M.eq_of_mem ha hb)
  edge := by
    intro u v edge
    obtain ⟨x,hx,y,hy,hxy⟩ := M.edge edge
    exact ⟨f x, Finset.mem_image.mpr ⟨x,hx,rfl⟩,
      f y, Finset.mem_image.mpr ⟨y,hy,rfl⟩,edges hxy⟩

noncomputable def regionHome (D : TreeDecomposition G) (w : W) : D.tree :=
  Classical.choose (D.connected_region (M.branch w) (M.connected w))

omit [DecidableEq V] [DecidableEq W] in
theorem regionHome_spec (D : TreeDecomposition G) (w : W) :
    (∃ v ∈ M.branch w, M.regionHome D w = D.home v) ∧
    (∀ v ∈ M.branch w, ∀ i, v ∈ D.bag i → M.regionHome D w ≤ i) ∧
    (∀ v ∈ M.branch w, ∀ i, v ∈ D.bag i → ∀ j, M.regionHome D w ≤ j → j ≤ i →
      ∃ u ∈ M.branch w, u ∈ D.bag j) :=
  Classical.choose_spec (D.connected_region (M.branch w) (M.connected w))

/-- Replace each host bag by the branch sets meeting it. -/
noncomputable def transport [Fintype W] (D : TreeDecomposition G) : TreeDecomposition H where
  tree := D.tree
  finite := D.finite
  bag i := Finset.univ.filter (fun w => ∃ v ∈ M.branch w, v ∈ D.bag i)
  home := M.regionHome D
  home_mem w := by
    obtain ⟨v, hv, eq⟩ := (M.regionHome_spec D w).1
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨v, hv, eq ▸ D.home_mem v⟩
  above_home w i h := by
    obtain ⟨v, hv, hi⟩ := (Finset.mem_filter.mp h).2
    exact (M.regionHome_spec D w).2.1 v hv i hi
  interval w i j h hj hji := by
    obtain ⟨v, hv, hi⟩ := (Finset.mem_filter.mp h).2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (M.regionHome_spec D w).2.2 v hv i hi j hj hji
  edge := by
    intro u v h
    obtain ⟨x, hx, y, hy, hxy⟩ := M.edge h
    obtain ⟨i, hxi, hyi⟩ := D.edge hxy
    exact ⟨i, by simpa using (show ∃ v ∈ M.branch _, v ∈ D.bag i from ⟨x, hx, hxi⟩),
      by simpa using (show ∃ v ∈ M.branch _, v ∈ D.bag i from ⟨y, hy, hyi⟩)⟩

theorem transport_capacity [Fintype W] (D : TreeDecomposition G) (k : ℕ)
    (capacity : D.Capacity k) : (M.transport D).Capacity k := by
  classical
  intro i
  let S := (M.transport D).bag i
  have exists_member (w : W) (hw : w ∈ S) : ∃ v ∈ M.branch w, v ∈ D.bag i :=
    (Finset.mem_filter.mp hw).2
  let choose (w : S) : V := Classical.choose (exists_member w.val w.property)
  have choose_mem (w : S) : choose w ∈ M.branch w.val ∧ choose w ∈ D.bag i :=
    Classical.choose_spec (exists_member w.val w.property)
  have bound : S.card ≤ (D.bag i).card := by
    rw [← Fintype.card_coe S, ← Fintype.card_coe (D.bag i)]
    exact Fintype.card_le_of_injective (fun w : S =>
      (⟨choose w, (choose_mem w).2⟩ : D.bag i)) (by
        intro u v h
        apply Subtype.ext
        have eq : choose u = choose v := congrArg Subtype.val h
        exact M.eq_of_mem (choose_mem u).1 (eq.symm ▸ (choose_mem v).1))
  exact bound.trans (capacity i)

include M in
theorem capacity_mono [Fintype W] {k : ℕ} (bound : HasTreeCapacity G k) :
    HasTreeCapacity H k := by
  obtain ⟨D, hD⟩ := bound
  exact ⟨M.transport D, M.transport_capacity D k hD⟩

include M in
theorem treewidth_mono [Fintype W] {w : ℕ} (bound : TreewidthLE G w) :
    TreewidthLE H w := M.capacity_mono bound

end MinorModel
end Controller.Graph
