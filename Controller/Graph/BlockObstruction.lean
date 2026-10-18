module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Graph.Minor
public import Controller.Graph.NetWidth
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

/-!
# Lifting decompositions through connected block regions

A region is the set of blocks met by one graph vertex's branch set. Regions
may overlap. An edge is represented by intersecting or adjacent regions.
If each block belongs to at most K regions, lifting a bag multiplies its
capacity by at most K. This is a finite, representation-specific statement.
-/
namespace Controller.Graph

variable {V B : Type} [Fintype V] [DecidableEq V] [DecidableEq B]

structure RegionProjection (J : SimpleGraph V) (Q : SimpleGraph B) where
  region : V → Finset B
  connected : ∀ v, ConnectedWithin Q (region v)
  edge : ∀ ⦃u v⦄, J.Adj u v →
    ∃ b ∈ region u, ∃ c ∈ region v, b = c ∨ Q.Adj b c

namespace RegionProjection
variable {J : SimpleGraph V} {Q : SimpleGraph B} (P : RegionProjection J Q)

def occupants (b : B) : Finset V := Finset.univ.filter fun v => b ∈ P.region v

def LoadBound (K : ℕ) : Prop := ∀ b, (P.occupants b).card ≤ K

noncomputable def home (D : TreeDecomposition Q) (v : V) : D.tree :=
  Classical.choose (D.connected_region (P.region v) (P.connected v))

omit [Fintype V] [DecidableEq V] [DecidableEq B] in
theorem home_spec (D : TreeDecomposition Q) (v : V) :
    (∃ b ∈ P.region v, P.home D v = D.home b) ∧
    (∀ b ∈ P.region v, ∀ i, b ∈ D.bag i → P.home D v ≤ i) ∧
    (∀ b ∈ P.region v, ∀ i, b ∈ D.bag i → ∀ j, P.home D v ≤ j → j ≤ i →
      ∃ c ∈ P.region v, c ∈ D.bag j) :=
  Classical.choose_spec (D.connected_region (P.region v) (P.connected v))

/-- Replace each block bag by all vertex regions meeting that bag. -/
noncomputable def lift (D : TreeDecomposition Q) : TreeDecomposition J where
  tree := D.tree
  finite := D.finite
  bag i := Finset.univ.filter fun v => ∃ b ∈ P.region v, b ∈ D.bag i
  home := P.home D
  home_mem v := by
    obtain ⟨b, hb, eq⟩ := (P.home_spec D v).1
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, b, hb, eq ▸ D.home_mem b⟩
  above_home v i h := by
    obtain ⟨b, hb, hi⟩ := (Finset.mem_filter.mp h).2
    exact (P.home_spec D v).2.1 b hb i hi
  interval v i j h hj hji := by
    obtain ⟨b, hb, hi⟩ := (Finset.mem_filter.mp h).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (P.home_spec D v).2.2 b hb i hi j hj hji⟩
  edge := by
    intro u v h
    obtain ⟨b, hb, c, hc, edge⟩ := P.edge h
    have together : ∃ i, b ∈ D.bag i ∧ c ∈ D.bag i := by
      rcases edge with rfl | edge
      · exact ⟨D.home b, D.home_mem b, D.home_mem b⟩
      · exact D.edge edge
    obtain ⟨i, hi, hj⟩ := together
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, b, hb, hi⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, c, hc, hj⟩⟩

theorem lift_bag_bound (D : TreeDecomposition Q) (K : ℕ) (load : P.LoadBound K)
    (i : D.tree) : ((P.lift D).bag i).card ≤ K * (D.bag i).card := by
  classical
  have contained : (P.lift D).bag i ⊆ (D.bag i).biUnion P.occupants := by
    intro v hv
    obtain ⟨b, hb, hi⟩ := (Finset.mem_filter.mp hv).2
    exact Finset.mem_biUnion.mpr ⟨b, hi, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩⟩
  calc
    _ ≤ ((D.bag i).biUnion P.occupants).card := Finset.card_le_card contained
    _ ≤ ∑ b ∈ D.bag i, (P.occupants b).card := Finset.card_biUnion_le
    _ ≤ ∑ _b ∈ D.bag i, K := Finset.sum_le_sum (fun b _ => load b)
    _ = K * (D.bag i).card := by simp [Nat.mul_comm]

theorem lift_capacity (D : TreeDecomposition Q) (K k : ℕ) (load : P.LoadBound K)
    (capacity : D.Capacity k) : (P.lift D).Capacity (K * k) := by
  intro i
  exact (P.lift_bag_bound D K load i).trans (Nat.mul_le_mul_left K (capacity i))

include P in
/-- The graph induced by branch-set regions has a decomposition of capacity K(w+1). -/
theorem block_decomposition_lift (K w : ℕ) (load : P.LoadBound K)
    (width : TreewidthLE Q w) : HasTreeCapacity J (K * (w + 1)) := by
  obtain ⟨D, capacity⟩ := width
  exact ⟨P.lift D, P.lift_capacity D K (w + 1) load capacity⟩

end RegionProjection

section Quotient
variable {A B V : Type} [DecidableEq A] [DecidableEq B] [DecidableEq V]

/-- Blocks are adjacent exactly when an original edge crosses between them. -/
def blockGraph (G : SimpleGraph A) (partition : A → B) : SimpleGraph B where
  Adj b c := b ≠ c ∧ ∃ x y, partition x = b ∧ partition y = c ∧ G.Adj x y
  symm := ⟨by
    rintro b c ⟨ne, x, y, hx, hy, edge⟩
    exact ⟨ne.symm, y, x, hy, hx, edge.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

omit [DecidableEq A] in
/-- A connected set remains connected when its vertices are assigned to blocks;
steps internal to a block become length-zero paths. -/
theorem connected_block_image (G : SimpleGraph A) (partition : A → B)
    (S : Finset A) (connected : ConnectedWithin G S) :
    ConnectedWithin (blockGraph G partition) (S.image partition) := by
  refine ⟨connected.1.image _, ?_⟩
  intro b hb c hc
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hc
  have path := connected.2 x hx y hy
  clear hy hc
  induction path with
  | refl => exact .refl
  | @tail u v path step ih =>
    by_cases same : partition u = partition v
    · simpa only [same] using ih
    · exact ih.tail ⟨Finset.mem_image.mpr ⟨u, step.1, rfl⟩,
        Finset.mem_image.mpr ⟨v, step.2.1, rfl⟩,
        same, u, v, rfl, rfl, step.2.2⟩

/-- Actual minor branches induce connected regions in every gate partition. -/
def MinorModel.blockProjection {H : SimpleGraph V} {G : SimpleGraph A}
    (M : MinorModel H G) (partition : A → B) :
    RegionProjection H (blockGraph G partition) where
  region v := (M.branch v).image partition
  connected v := connected_block_image G partition _ (M.connected v)
  edge := by
    intro u v edge
    obtain ⟨x, hx, y, hy, hxy⟩ := M.edge edge
    refine ⟨partition x, Finset.mem_image.mpr ⟨x, hx, rfl⟩,
      partition y, Finset.mem_image.mpr ⟨y, hy, rfl⟩, ?_⟩
    by_cases same : partition x = partition y
    · exact Or.inl same
    · exact Or.inr ⟨same, x, y, rfl, rfl, hxy⟩
end Quotient

namespace CircuitLayout
variable {Input Gate Signal Owner Block : Type}
    [DecidableEq Gate] [DecidableEq Owner] [Fintype Signal] [Fintype Gate]

/-- An owner path starts at a primary signal. Each traversed signal has the same
owner; only the live path edges, rather than other gate inputs, are constrained. -/
inductive OwnedPath (L : CircuitLayout Input Gate Unit Signal)
    (owner : Signal → Option Owner) (v : Owner) : Gate → Prop
  | primary (signal : Signal) (input : Input) (gate : Gate)
      (producer : L.producer signal = .inl input)
      (consumer : Sum.inl gate ∈ L.consumers signal)
      (owned : owner signal = some v) : OwnedPath L owner v gate
  | step (signal : Signal) (previous gate : Gate)
      (path : OwnedPath L owner v previous)
      (producer : L.producer signal = .inr previous)
      (consumer : Sum.inl gate ∈ L.consumers signal)
      (owned : owner signal = some v) : OwnedPath L owner v gate

noncomputable def gateBlock [DecidableEq Block] (partition : Gate → Block) (b : Block) :
    Finset Gate := Finset.univ.filter fun g => partition g = b

omit [DecidableEq Owner] in
/-- Every owner path entering a block supplies an entering signal of that owner. -/
theorem OwnedPath.first_entry [DecidableEq Block]
    {L : CircuitLayout Input Gate Unit Signal} {owner : Signal → Option Owner}
    {v : Owner} {gate : Gate} (path : OwnedPath L owner v gate)
    (partition : Gate → Block) :
    ∃ signal ∈ L.blockInputs (gateBlock partition (partition gate)), owner signal = some v := by
  induction path with
  | primary signal input gate producer consumer owned =>
    refine ⟨signal, ?_, owned⟩
    classical
    simp only [blockInputs, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨⟨gate, by simp [gateBlock], consumer⟩, by simp [producer]⟩
  | step signal previous gate path producer consumer owned ih =>
    by_cases same : partition previous = partition gate
    · simpa only [same] using ih
    · refine ⟨signal, ?_, owned⟩
      classical
      simp only [blockInputs, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨⟨gate, by simp [gateBlock], consumer⟩,
        by simp [producer, gateBlock, same]⟩

omit [DecidableEq Owner] in
/-- A block cannot meet more owner regions than its distinct entering signals. -/
theorem owner_region_charge [Fintype Owner] [DecidableEq Block]
    (L : CircuitLayout Input Gate Unit Signal) (owner : Signal → Option Owner)
    (branch : Owner → Finset Gate)
    (paths : ∀ v, ∀ g ∈ branch v, OwnedPath L owner v g)
    (partition : Gate → Block) (b : Block) :
    (Finset.univ.filter (fun v => ∃ g ∈ branch v, partition g = b)).card ≤
      (L.blockInputs (gateBlock partition b)).card := by
  classical
  let meets := Finset.univ.filter fun v => ∃ g ∈ branch v, partition g = b
  have entry (v : meets) :
      ∃ s ∈ L.blockInputs (gateBlock partition b), owner s = some v.val := by
    obtain ⟨g, hg, hb⟩ := (Finset.mem_filter.mp v.property).2
    simpa only [hb] using (paths v.val g hg).first_entry partition
  let signal (v : meets) : Signal := Classical.choose (entry v)
  have spec (v : meets) :
      signal v ∈ L.blockInputs (gateBlock partition b) ∧ owner (signal v) = some v.val :=
    Classical.choose_spec (entry v)
  have injective : Function.Injective (fun v : meets =>
      (⟨signal v, (spec v).1⟩ : L.blockInputs (gateBlock partition b))) := by
    intro u v eq
    have h : signal u = signal v := congrArg Subtype.val eq
    apply Subtype.ext
    exact Option.some.inj ((spec u).2.symm.trans ((congrArg owner h).trans (spec v).2))
  have count := Fintype.card_le_of_injective _ injective
  simpa only [Fintype.card_coe] using count

end CircuitLayout
end Controller.Graph
