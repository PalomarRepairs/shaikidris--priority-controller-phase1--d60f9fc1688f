module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Mathlib.Order.SuccPred.Tree
public import Mathlib.Order.Preorder.Finite
public import Mathlib.Combinatorics.SimpleGraph.Clique

@[expose] public section

/-!
# Finite rooted tree decompositions

The indexing tree uses mathlib's ancestor order: the root is bottom and the
infimum is the least common ancestor. A vertex's `home` is its highest bag.
The home and interval fields express exactly that its bags form a nonempty
connected subtree. Bag capacity is width plus one; capacity zero is allowed
for an empty graph. Primary inputs and outputs are graph vertices when a
circuit graph is supplied.
-/
namespace Controller.Graph

variable {V W : Type} [DecidableEq V] [DecidableEq W]

/-- A finite rooted tree decomposition, with explicit highest occurrences. -/
structure TreeDecomposition (G : SimpleGraph V) where
  tree : RootedTree
  finite : Fintype tree
  bag : tree → Finset V
  home : V → tree
  home_mem : ∀ v, v ∈ bag (home v)
  above_home : ∀ v i, v ∈ bag i → home v ≤ i
  interval : ∀ v i j, v ∈ bag i → home v ≤ j → j ≤ i → v ∈ bag j
  edge : ∀ ⦃u v⦄, G.Adj u v → ∃ i, u ∈ bag i ∧ v ∈ bag i

namespace TreeDecomposition
variable {G : SimpleGraph V} (D : TreeDecomposition G)

/-- The usual running-intersection condition, expressed on the unique rooted path. -/
def Running (tree : RootedTree) (bag : tree → Finset V) : Prop :=
  ∀ v i j, v ∈ bag i → v ∈ bag j → ∀ k,
    i ⊓ j ≤ k → (k ≤ i ∨ k ≤ j) → v ∈ bag k

omit [DecidableEq V] in
theorem running : Running D.tree D.bag := by
  intro v i j hi hj k hk hki
  have home_le : D.home v ≤ k :=
    (le_inf (D.above_home v i hi) (D.above_home v j hj)).trans hk
  rcases hki with h | h
  · exact D.interval v i k hi home_le h
  · exact D.interval v j k hj home_le h

omit [DecidableEq V] [DecidableEq W] in
theorem exists_home (tree : RootedTree) [Fintype tree] (bag : tree → Finset V)
    (cover : ∀ v, ∃ i, v ∈ bag i) (running : Running tree bag) (v : V) :
    ∃ h, v ∈ bag h ∧ ∀ i, v ∈ bag i → h ≤ i := by
  classical
  let S := Finset.univ.filter fun i => v ∈ bag i
  obtain ⟨i, hi⟩ := cover v
  obtain ⟨h, hh⟩ := S.exists_minimal ⟨i, by simpa [S] using hi⟩
  have hvh : v ∈ bag h := (Finset.mem_filter.mp hh.1).2
  refine ⟨h, hvh, ?_⟩
  intro j hvj
  have hm : v ∈ bag (h ⊓ j) :=
    running v h j hvh hvj (h ⊓ j) le_rfl (Or.inl inf_le_left)
  exact (hh.2 (by simpa [S] using hm) inf_le_left).trans inf_le_right

/-- Construct our representation from ordinary cover, edge and path axioms.
The highest-occurrence witnesses add no hypothesis to a tree decomposition. -/
noncomputable def ofBags (tree : RootedTree) (finite : Fintype tree)
    (bag : tree → Finset V) (cover : ∀ v, ∃ i, v ∈ bag i)
    (running : Running tree bag)
    (edge : ∀ ⦃u v⦄, G.Adj u v → ∃ i, u ∈ bag i ∧ v ∈ bag i) :
    TreeDecomposition G := by
  letI := finite
  let home v := Classical.choose (exists_home tree bag cover running v)
  have home_spec v : v ∈ bag (home v) ∧ ∀ i, v ∈ bag i → home v ≤ i :=
    Classical.choose_spec (exists_home tree bag cover running v)
  exact {
    tree, finite, bag, home
    home_mem := fun v => (home_spec v).1
    above_home := fun v => (home_spec v).2
    interval := fun v i j hi hj hji => running v (home v) i (home_spec v).1 hi j
      (inf_le_left.trans hj) (Or.inr hji)
    edge }

/-- An upper bound on every bag size; this avoids subtracting at the empty case. -/
def Capacity (k : ℕ) : Prop := ∀ i, (D.bag i).card ≤ k

omit [DecidableEq V] in
theorem running_inf {v : V} {i j : D.tree}
    (hi : v ∈ D.bag i) (hj : v ∈ D.bag j) : v ∈ D.bag (i ⊓ j) :=
  D.interval v i (i ⊓ j) hi (le_inf (D.above_home v i hi) (D.above_home v j hj))
    inf_le_left

/-- Every finite clique is contained in a bag, including the empty clique. -/
theorem clique_bag (S : Finset V)
    (clique : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → G.Adj u v) :
    ∃ i, S ⊆ D.bag i := by
  classical
  by_cases nonempty : S.Nonempty
  · obtain ⟨v, hv⟩ := S.exists_maximalFor D.home nonempty
    refine ⟨D.home v, ?_⟩
    intro u hu
    by_cases same : u = v
    · subst u; exact D.home_mem v
    obtain ⟨i, hui, hvi⟩ := D.edge (clique u hu v hv.1 same)
    have hu_le := D.above_home u i hui
    have hv_le := D.above_home v i hvi
    have huv : D.home u ≤ D.home v := by
      rcases le_total_of_directed hu_le hv_le with h | h
      · exact hv.2 hu h
      · exact h
    exact D.interval u i (D.home v) hui huv hv_le
  · exact ⟨⊥, by simp [Finset.not_nonempty_iff_eq_empty.mp nonempty]⟩

theorem clique_card_le (k : ℕ) (capacity : D.Capacity k) (S : Finset V)
    (clique : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → G.Adj u v) : S.card ≤ k := by
  obtain ⟨i, contained⟩ := D.clique_bag S clique
  exact (Finset.card_le_card contained).trans (capacity i)

/-- Removing graph edges preserves the same bags and their capacity. -/
def ofLE {H : SimpleGraph V} (subgraph : H ≤ G) : TreeDecomposition H where
  tree := D.tree
  finite := D.finite
  bag := D.bag
  home := D.home
  home_mem := D.home_mem
  above_home := D.above_home
  interval := D.interval
  edge := by intro u v h; exact D.edge (subgraph h)

/-- Pull bags back along an injective vertex map that preserves edges. -/
noncomputable def comap [Fintype W] {H : SimpleGraph W} (f : W → V)
    (edges : ∀ ⦃u v⦄, H.Adj u v → G.Adj (f u) (f v)) : TreeDecomposition H where
  tree := D.tree
  finite := D.finite
  bag i := Finset.univ.filter (fun v => f v ∈ D.bag i)
  home v := D.home (f v)
  home_mem v := by simp [D.home_mem]
  above_home v i h := D.above_home (f v) i (Finset.mem_filter.mp h).2
  interval v i j h h₁ h₂ := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢
    exact D.interval (f v) i j h h₁ h₂
  edge := by
    intro u v h
    obtain ⟨i, hu, hv⟩ := D.edge (edges h)
    exact ⟨i, by simpa using hu, by simpa using hv⟩

omit [DecidableEq W] in
theorem comap_capacity [Fintype W] {H : SimpleGraph W} (f : W → V)
    (injective : Function.Injective f)
    (edges : ∀ ⦃u v⦄, H.Adj u v → G.Adj (f u) (f v))
    (k : ℕ) (capacity : D.Capacity k) : (D.comap f edges).Capacity k := by
  classical
  intro i
  apply (Finset.card_le_card_of_injOn f ?_ ?_).trans (capacity i)
  · intro v hv
    exact (Finset.mem_filter.mp hv).2
  · exact fun _ _ _ _ h => injective h

end TreeDecomposition

/-- Existence of a tree decomposition with bounded bag capacity. -/
def HasTreeCapacity (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ D : TreeDecomposition G, D.Capacity k

/-- Width at most w means bags of size at most w+1. -/
def TreewidthLE (G : SimpleGraph V) (w : ℕ) : Prop := HasTreeCapacity G (w + 1)

end Controller.Graph
