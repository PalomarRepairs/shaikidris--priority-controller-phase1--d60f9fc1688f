module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Graph.TreeDecomposition
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Order.SuccPred.LinearLocallyFinite
public import Mathlib.Order.Interval.Finset.Fin

@[expose] public section

/-!
# Signal-net cutwidth

Each signal is one hyperedge containing its producer and every consumer.
Repeated uses at a consumer do not duplicate vertices or signals. Vertex
deletion restricts retained nets; signal deletion removes the whole hyperedge.
Graph cutwidth counts edges and is a distinct quantity.
-/
namespace Controller.Graph

variable {V S : Type} [Fintype V] [DecidableEq V] [Fintype S] [DecidableEq S]

structure NetSystem (V S : Type) where
  net : S → Finset V

namespace NetSystem
variable (H : NetSystem V S)

/-- A rank bijection orders every vertex, including primary ports. -/
def crossing (order : V ≃ Fin (Fintype.card V)) (cut : ℕ) : Finset S :=
  Finset.univ.filter fun s =>
    (∃ u ∈ H.net s, (order u).val < cut) ∧
    (∃ v ∈ H.net s, cut ≤ (order v).val)

def CutBound (order : V ≃ Fin (Fintype.card V)) (k : ℕ) : Prop :=
  ∀ cut, (H.crossing order cut).card ≤ k

def NetCutwidthLE (k : ℕ) : Prop := ∃ order, H.CutBound order k

omit [DecidableEq V] [DecidableEq S] in
theorem cutBound_pos_of_distinct (order : V ≃ Fin (Fintype.card V)) (k : ℕ)
    (bound : H.CutBound order k) (s : S) (x y : V) (hx : x ∈ H.net s)
    (hy : y ∈ H.net s) (ne : x ≠ y) : 0 < k := by
  have ranks : (order x).val ≠ (order y).val := fun eq => ne (order.injective (Fin.ext eq))
  have witness : ∃ cut, s ∈ H.crossing order cut := by
    rcases Nat.lt_or_gt_of_ne ranks with lt | lt
    · exact ⟨(order y).val, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        ⟨x,hx,lt⟩,y,hy,le_rfl⟩⟩
    · exact ⟨(order x).val, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        ⟨y,hy,lt⟩,x,hx,le_rfl⟩⟩
  obtain ⟨cut,hs⟩ := witness
  exact (Finset.card_pos.mpr ⟨s,hs⟩).trans_le (bound cut)

/-- Delete whole excluded nets, then restrict the remaining hyperedges. -/
def restrict (vertices : Finset V) (signals : Finset S) : NetSystem V S where
  net s := if s ∈ signals then H.net s ∩ vertices else ∅

omit [Fintype V] [Fintype S] in
theorem mem_restrict (vertices : Finset V) (signals : Finset S) (s : S) (v : V) :
    v ∈ (H.restrict vertices signals).net s ↔ s ∈ signals ∧ v ∈ H.net s ∧ v ∈ vertices := by
  by_cases hs : s ∈ signals <;> simp [restrict, hs]

omit [Fintype V] [Fintype S] in
theorem restrict_net_subset (vertices : Finset V) (signals : Finset S) (s : S) :
    (H.restrict vertices signals).net s ⊆ H.net s := by
  intro v hv
  by_cases hs : s ∈ signals
  · exact (Finset.mem_inter.mp (by simpa [restrict, hs] using hv)).1
  · simp [restrict, hs] at hv

theorem restrict_crossing_subset (vertices : Finset V) (signals : Finset S)
    (order : V ≃ Fin (Fintype.card V)) (cut : ℕ) :
    (H.restrict vertices signals).crossing order cut ⊆ H.crossing order cut := by
  intro s hs
  obtain ⟨⟨u, hu, huc⟩, v, hv, hcv⟩ := (Finset.mem_filter.mp hs).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    ⟨⟨u, H.restrict_net_subset vertices signals s hu, huc⟩,
      ⟨v, H.restrict_net_subset vertices signals s hv, hcv⟩⟩⟩

theorem restrict_cutBound (vertices : Finset V) (signals : Finset S)
    (order : V ≃ Fin (Fintype.card V)) (k : ℕ) (bound : H.CutBound order k) :
    (H.restrict vertices signals).CutBound order k := by
  intro cut
  exact (Finset.card_le_card (H.restrict_crossing_subset vertices signals order cut)).trans
    (bound cut)

/-- Vertices sharing a signal are adjacent, independently of producer polarity. -/
def twoSection : SimpleGraph V where
  Adj u v := u ≠ v ∧ ∃ s, u ∈ H.net s ∧ v ∈ H.net s
  symm := ⟨by
    intro u v h
    obtain ⟨hne, s, hu, hv⟩ := h
    exact ⟨hne.symm, s, hv, hu⟩⟩
  loopless := ⟨by intro v h; exact h.1 rfl⟩

/-- Vertices left of a cut with a neighbor on its right. -/
noncomputable def boundary (order : V ≃ Fin (Fintype.card V)) (cut : ℕ) : Finset V := by
  classical
  exact Finset.univ.filter fun u => (order u).val < cut ∧
    ∃ v, cut ≤ (order v).val ∧ H.twoSection.Adj u v

omit [DecidableEq S] in
theorem boundary_subset_crossing_nets (order : V ≃ Fin (Fintype.card V)) (cut : ℕ) :
    H.boundary order cut ⊆ (H.crossing order cut).biUnion H.net := by
  classical
  intro u hu
  obtain ⟨huc, v, hcv, _, s, hus, hvs⟩ := (Finset.mem_filter.mp hu).2
  exact Finset.mem_biUnion.mpr ⟨s, Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, ⟨⟨u, hus, huc⟩, ⟨v, hvs, hcv⟩⟩⟩, hus⟩

omit [DecidableEq S] in
/-- Each crossing retained net can charge at most its arity many vertices. -/
theorem boundary_card_le (order : V ≃ Fin (Fintype.card V)) (cut arity : ℕ)
    (bounded : ∀ s, (H.net s).card ≤ arity) :
    (H.boundary order cut).card ≤ arity * (H.crossing order cut).card := by
  calc
    _ ≤ ((H.crossing order cut).biUnion H.net).card :=
      Finset.card_le_card (H.boundary_subset_crossing_nets order cut)
    _ ≤ ∑ s ∈ H.crossing order cut, (H.net s).card := Finset.card_biUnion_le
    _ ≤ ∑ _s ∈ H.crossing order cut, arity := Finset.sum_le_sum (fun s _ => bounded s)
    _ = arity * (H.crossing order cut).card := by simp [Nat.mul_comm]

/-- A path index is a linearly ordered rooted tree. -/
noncomputable def pathTree (n : ℕ) : RootedTree := by
  letI : PredOrder (Fin (n + 1)) := LinearLocallyFiniteOrder.predOrder _
  exact { α := Fin (n + 1) }

/-- The usual bags consisting of the left boundary and the current vertex. -/
noncomputable def pathBag (order : V ≃ Fin (Fintype.card V))
    (i : Fin (Fintype.card V + 1)) : Finset V := by
  classical
  exact Finset.univ.filter fun v => (order v).val = i.val ∨
    ((order v).val < i.val ∧ ∃ u, i.val ≤ (order u).val ∧ H.twoSection.Adj v u)

noncomputable def pathDecomposition (order : V ≃ Fin (Fintype.card V)) :
    TreeDecomposition H.twoSection where
  tree := pathTree (Fintype.card V)
  finite := inferInstanceAs (Fintype (Fin (Fintype.card V + 1)))
  bag := H.pathBag order
  home v := ⟨(order v).val, Nat.lt_succ_of_lt (order v).isLt⟩
  home_mem v := by
    classical
    simp [pathBag]
  above_home v i h := by
    classical
    change (order v).val ≤ i.val
    simp only [pathBag, Finset.mem_filter, Finset.mem_univ, true_and] at h
    rcases h with h | h
    · exact h.le
    · exact h.1.le
  interval v i j hi hj hji := by
    classical
    change (order v).val ≤ j.val at hj
    change j.val ≤ i.val at hji
    simp only [pathBag, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    rcases hi with eq | ⟨lt, u, hu, edge⟩
    · left; omega
    · by_cases same : (order v).val = j.val
      · exact Or.inl same
      · exact Or.inr ⟨by omega, u, hji.trans hu, edge⟩
  edge := by
    classical
    intro u v edge
    have ne : (order u).val ≠ (order v).val := by
      intro h
      exact edge.1 (order.injective (Fin.ext h))
    rcases lt_or_gt_of_ne ne with h | h
    · refine ⟨⟨(order v).val, Nat.lt_succ_of_lt (order v).isLt⟩, ?_, ?_⟩
      · simp only [pathBag, Finset.mem_filter, Finset.mem_univ, true_and]
        exact Or.inr ⟨h, v, le_rfl, edge⟩
      · simp [pathBag]
    · refine ⟨⟨(order u).val, Nat.lt_succ_of_lt (order u).isLt⟩, ?_, ?_⟩
      · simp [pathBag]
      · simp only [pathBag, Finset.mem_filter, Finset.mem_univ, true_and]
        exact Or.inr ⟨h, u, le_rfl, edge.symm⟩

omit [Fintype S] [DecidableEq S] in
theorem pathDecomposition_capacity (order : V ≃ Fin (Fintype.card V)) (s : ℕ)
    (separation : ∀ cut, (H.boundary order cut).card ≤ s) :
    (H.pathDecomposition order).Capacity (s + 1) := by
  classical
  intro i
  let current := Finset.univ.filter fun v : V => (order v).val = i.val
  have current_card : current.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro u hu v hv
    apply order.injective
    apply Fin.ext
    exact (Finset.mem_filter.mp hu).2.trans (Finset.mem_filter.mp hv).2.symm
  have contained : H.pathBag order i ⊆ H.boundary order i.val ∪ current := by
    intro v hv
    simp only [pathBag, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    rcases hv with h | h
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  exact (Finset.card_le_card contained).trans
    ((Finset.card_union_le _ _).trans (Nat.add_le_add (separation i.val) current_card))

omit [DecidableEq S] in
/-- Direct vertex-separation to path-decomposition construction, with no loss. -/
theorem cutBound_treewidth (order : V ≃ Fin (Fintype.card V)) (arity k : ℕ)
    (bounded : ∀ s, (H.net s).card ≤ arity) (cutBound : H.CutBound order k) :
    TreewidthLE H.twoSection (arity * k) := by
  refine ⟨H.pathDecomposition order, H.pathDecomposition_capacity order (arity * k) ?_⟩
  intro cut
  exact (H.boundary_card_le order cut arity bounded).trans
    (Nat.mul_le_mul_left arity (cutBound cut))

end NetSystem

/-- A path decomposition is a tree decomposition whose index order is a chain. -/
def PathwidthLE (G : SimpleGraph V) (w : ℕ) : Prop :=
  ∃ D : TreeDecomposition G, D.Capacity (w + 1) ∧
    ∀ i j : D.tree, i ≤ j ∨ j ≤ i

omit [Fintype V] [DecidableEq V] in
theorem pathwidth_treewidth {G : SimpleGraph V} {w : ℕ} (h : PathwidthLE G w) :
    TreewidthLE G w := by
  obtain ⟨D, bound, _⟩ := h
  exact ⟨D, bound⟩

omit [DecidableEq S] in
theorem NetSystem.cutBound_pathwidth (H : NetSystem V S)
    (order : V ≃ Fin (Fintype.card V)) (arity k : ℕ)
    (bounded : ∀ s, (H.net s).card ≤ arity) (cutBound : H.CutBound order k) :
    PathwidthLE H.twoSection (arity * k) := by
  refine ⟨H.pathDecomposition order, ?_, ?_⟩
  · apply H.pathDecomposition_capacity
    intro cut
    exact (H.boundary_card_le order cut arity bounded).trans
      (Nat.mul_le_mul_left arity (cutBound cut))
  · intro i j
    change (i : Fin (Fintype.card V + 1)).val ≤ (j : Fin (Fintype.card V + 1)).val ∨
      (j : Fin (Fintype.card V + 1)).val ≤ (i : Fin (Fintype.card V + 1)).val
    exact Nat.le_total _ _

/-- A single bag also covers the empty graph, where its capacity is zero. -/
noncomputable def TreeDecomposition.oneBag (G : SimpleGraph V) : TreeDecomposition G where
  tree := NetSystem.pathTree 0
  finite := inferInstanceAs (Fintype (Fin 1))
  bag _ := Finset.univ
  home _ := ⟨0, by decide⟩
  home_mem _ := Finset.mem_univ _
  above_home _ _ _ := bot_le
  interval _ _ _ _ _ _ := Finset.mem_univ _
  edge := by intro u v _; exact ⟨⊥, Finset.mem_univ _, Finset.mem_univ _⟩

omit [DecidableEq V] in
theorem TreeDecomposition.oneBag_capacity (G : SimpleGraph V) :
    (oneBag G).Capacity (Fintype.card V) := by
  intro i
  exact le_rfl

/-- Graph cutwidth counts crossing edges once, oriented by their endpoint ranks. -/
noncomputable def graphCrossing (G : SimpleGraph V)
    (order : V ≃ Fin (Fintype.card V)) (cut : ℕ) : Finset (V × V) := by
  classical
  exact Finset.univ.filter fun e => G.Adj e.1 e.2 ∧
    (order e.1).val < cut ∧ cut ≤ (order e.2).val

def GraphCutwidthLE (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ order, ∀ cut, (graphCrossing G order cut).card ≤ k

/-- Circuit ports have their own vertices; gate count is not total vertex count. -/
structure CircuitLayout (Input Gate Output Signal : Type) where
  producer : Signal → Input ⊕ Gate
  consumers : Signal → Finset (Gate ⊕ Output)

namespace CircuitLayout
variable {Input Gate Output Signal : Type}

def inputVertex : Input ⊕ Gate → Input ⊕ Gate ⊕ Output
  | .inl i => .inl i
  | .inr g => .inr (.inl g)

def consumerVertex : Gate ⊕ Output → Input ⊕ Gate ⊕ Output := Sum.inr

/-- The port-inclusive wire graph joins each signal producer to its consumers. -/
def wireGraph (L : CircuitLayout Input Gate Output Signal) :
    SimpleGraph (Input ⊕ Gate ⊕ Output) where
  Adj x y := x ≠ y ∧ ∃ s c, c ∈ L.consumers s ∧
    ((x = inputVertex (L.producer s) ∧ y = consumerVertex c) ∨
     (y = inputVertex (L.producer s) ∧ x = consumerVertex c))
  symm := ⟨by
    rintro x y ⟨ne, s, c, hc, edge⟩
    exact ⟨ne.symm, s, c, hc, edge.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

def nets [DecidableEq Input] [DecidableEq Gate] [DecidableEq Output]
    (L : CircuitLayout Input Gate Output Signal) : NetSystem (Input ⊕ Gate ⊕ Output) Signal where
  net s := insert (inputVertex (L.producer s)) ((L.consumers s).image consumerVertex)

theorem producer_mem_net [DecidableEq Input] [DecidableEq Gate] [DecidableEq Output]
    (L : CircuitLayout Input Gate Output Signal) (s : Signal) :
    inputVertex (L.producer s) ∈ L.nets.net s := Finset.mem_insert_self _ _

theorem primary_mem_net [DecidableEq Input] [DecidableEq Gate] [DecidableEq Output]
    (L : CircuitLayout Input Gate Output Signal) (s : Signal) (i : Input)
    (source : L.producer s = .inl i) : Sum.inl i ∈ L.nets.net s := by
  have member := L.producer_mem_net s
  rw [source] at member
  exact member

/-- A primary-to-gate wire forces a positive cut-width in every ordering. -/
theorem primary_netCutwidth_positive [DecidableEq Input] [DecidableEq Gate]
    [DecidableEq Output] [Fintype (Input ⊕ Gate ⊕ Output)] [Fintype Signal]
    (L : CircuitLayout Input Gate Output Signal) (k : ℕ) (cut : L.nets.NetCutwidthLE k)
    (s : Signal) (i : Input) (g : Gate) (source : L.producer s = .inl i)
    (consumer : Sum.inl g ∈ L.consumers s) : 0 < k := by
  obtain ⟨order,bound⟩ := cut
  have first := L.primary_mem_net s i source
  have second : Sum.inr (Sum.inl g) ∈ L.nets.net s :=
    Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨.inl g,consumer,rfl⟩)
  exact L.nets.cutBound_pos_of_distinct order k bound s _ _ first second (by simp)

/-- Distinct external signals entering a gate block; fan-out is counted once. -/
noncomputable def blockInputs [Fintype Signal] [DecidableEq Gate]
    (L : CircuitLayout Input Gate Output Signal) (block : Finset Gate) : Finset Signal := by
  classical
  exact Finset.univ.filter fun s =>
    (∃ g ∈ block, Sum.inl g ∈ L.consumers s) ∧
      (match L.producer s with | .inl _ => True | .inr g => g ∉ block)

end CircuitLayout
end Controller.Graph
