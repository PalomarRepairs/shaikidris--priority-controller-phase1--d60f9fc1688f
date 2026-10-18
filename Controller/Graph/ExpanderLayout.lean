module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Graph.BlockObstruction
public import Controller.Graph.NetWidth
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Linarith
public import Controller.Graph.NativeMinor
public import Controller.Counting.NativeModels

public import Mathlib.Tactic.Ring

@[expose] public section

/-! Finite separator and width estimates for vertex expanders. -/
namespace Controller.Graph

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

namespace TreeDecomposition

noncomputable def descendants (D : TreeDecomposition G) (i : D.tree) : Finset V := by
  classical
  exact Finset.univ.filter fun v => i ≤ D.home v

/-- A balanced separator bag, stated for every connected set outside the bag. -/
theorem balanced_bag (D : TreeDecomposition G) :
    ∃ i : D.tree, ∀ S : Finset V, ConnectedWithin G S → Disjoint S (D.bag i) →
      2 * S.card ≤ Fintype.card V := by
  classical
  let _ := D.finite
  by_cases zero : Fintype.card V = 0
  · exact ⟨⊥, fun S _ _ => by
      have := Finset.card_le_univ S
      omega⟩
  let heavy := Finset.univ.filter fun i : D.tree =>
    Fintype.card V < 2 * (D.descendants i).card
  have root_heavy : (⊥ : D.tree) ∈ heavy := by
    have root : D.descendants ⊥ = Finset.univ := by
      ext v
      exact ⟨fun _ => Finset.mem_univ _,
        fun _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, bot_le⟩⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [root, Finset.card_univ]
    omega
  obtain ⟨i, maximal⟩ := heavy.exists_maximal ⟨⊥, root_heavy⟩
  have heavy_i : Fintype.card V < 2 * (D.descendants i).card :=
    (Finset.mem_filter.mp maximal.1).2
  have proper (r : D.tree) (hr : i < r) :
      2 * (D.descendants r).card ≤ Fintype.card V := by
    by_contra fail
    have mem : r ∈ heavy := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
    exact hr.not_ge (maximal.2 mem hr.le)
  refine ⟨i, ?_⟩
  intro S connected disjoint
  obtain ⟨r, origin, below, intervals⟩ := D.connected_region S connected
  by_cases branch : i < r
  · have contained : S ⊆ D.descendants r := by
      intro v hv
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, below v hv _ (D.home_mem v)⟩
    exact (Nat.mul_le_mul_left 2 (Finset.card_le_card contained)).trans (proper r branch)
  · have contained : S ⊆ Finset.univ \ D.descendants i := by
      intro v hv
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro descendant
      have i_le := (Finset.mem_filter.mp descendant).2
      have r_le := below v hv _ (D.home_mem v)
      have root_le_i : r ≤ i := by
        rcases le_total_of_directed i_le r_le with h | h
        · exact h
        · exact (eq_of_le_of_not_lt h branch).ge
      obtain ⟨u, hu, hi⟩ := intervals v hv _ (D.home_mem v) i root_le_i i_le
      exact Finset.disjoint_left.mp disjoint hu hi
    have size := Finset.card_le_card contained
    have split := Finset.card_sdiff_add_card_eq_card
      (show D.descendants i ⊆ Finset.univ from Finset.subset_univ _)
    rw [Finset.card_univ] at split
    omega

end TreeDecomposition

/-- No edge leaves U except through the designated separator. -/
def SeparatedBy (G : SimpleGraph V) (B U : Finset V) : Prop :=
  Disjoint U B ∧ ∀ u ∈ U, ∀ v, G.Adj u v → v ∈ U ∨ v ∈ B

def avoidsAdj (G : SimpleGraph V) (B : Finset V) (u v : V) : Prop :=
  u ∉ B ∧ v ∉ B ∧ G.Adj u v

noncomputable def componentOutside (G : SimpleGraph V) (B : Finset V) (v : V) : Finset V := by
  classical
  exact Finset.univ.filter fun u => Relation.ReflTransGen (avoidsAdj G B) v u

omit [DecidableEq V] in
theorem componentOutside_self (B : Finset V) (v : V) : v ∈ componentOutside G B v := by
  classical
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, .refl⟩

omit [DecidableEq V] in
theorem componentOutside_not_mem (B : Finset V) (v : V) (outside : v ∉ B)
    {u : V} (member : u ∈ componentOutside G B v) : u ∉ B := by
  classical
  have reach := (Finset.mem_filter.mp member).2
  induction reach with
  | refl => exact outside
  | tail _ step _ => exact step.2.1

theorem componentOutside_separated (B : Finset V) (v : V) (outside : v ∉ B) :
    SeparatedBy G B (componentOutside G B v) := by
  classical
  refine ⟨Finset.disjoint_left.mpr (fun _ h => componentOutside_not_mem B v outside h), ?_⟩
  intro u hu w edge
  by_cases hw : w ∈ B
  · exact Or.inr hw
  · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ((Finset.mem_filter.mp hu).2).tail
        ⟨componentOutside_not_mem B v outside hu, hw, edge⟩⟩)

omit [DecidableEq V] in
theorem componentOutside_connected (B : Finset V) (v : V) :
    ConnectedWithin G (componentOutside G B v) := by
  classical
  let C := componentOutside G B v
  let R := fun x y => x ∈ C ∧ y ∈ C ∧ G.Adj x y
  let : Std.Symm R := ⟨fun _ _ h => ⟨h.2.1, h.1, h.2.2.symm⟩⟩
  have lift (u : V) (reach : Relation.ReflTransGen (avoidsAdj G B) v u) :
      u ∈ C ∧ Relation.ReflTransGen R v u := by
    induction reach with
    | refl => exact ⟨componentOutside_self B v, .refl⟩
    | @tail u w path step ih =>
      have member : w ∈ C := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        ((Finset.mem_filter.mp ih.1).2).tail step⟩
      exact ⟨member, ih.2.tail ⟨ih.1, member, step.2.2⟩⟩
  refine ⟨⟨v, componentOutside_self B v⟩, ?_⟩
  intro u hu w hw
  exact (symm (lift u (Finset.mem_filter.mp hu).2).2).trans
    (lift w (Finset.mem_filter.mp hw).2).2

omit [DecidableEq V] in
theorem componentOutside_disjoint (B U : Finset V) (separated : SeparatedBy G B U)
    (v : V) (outsideU : v ∉ U) : Disjoint U (componentOutside G B v) := by
  classical
  apply Finset.disjoint_right.mpr
  intro u hu
  have reach := (Finset.mem_filter.mp hu).2
  induction reach with
  | refl => exact outsideU
  | @tail u w path step ih =>
    have ih := ih (Finset.mem_filter.mpr ⟨Finset.mem_univ _, path⟩)
    intro hw
    rcases separated.2 w hw u step.2.2.symm with h | h
    · exact ih h
    · exact step.1 h

omit [Fintype V] in
theorem SeparatedBy.union {B U W : Finset V}
    (hU : SeparatedBy G B U) (hW : SeparatedBy G B W) : SeparatedBy G B (U ∪ W) := by
  refine ⟨Finset.disjoint_union_left.mpr ⟨hU.1, hW.1⟩, ?_⟩
  intro u hu v edge
  rcases Finset.mem_union.mp hu with hu | hu
  · exact (hU.2 u hu v edge).imp (Finset.mem_union_left _) id
  · exact (hW.2 u hu v edge).imp (Finset.mem_union_right _) id

/-- Components of size at most half can be grouped between one quarter and one half. -/
theorem balanced_separated_set (B : Finset V)
    (small : 4 * B.card < Fintype.card V)
    (balanced : ∀ S : Finset V, ConnectedWithin G S → Disjoint S B →
      2 * S.card ≤ Fintype.card V) :
    ∃ U : Finset V, SeparatedBy G B U ∧ Fintype.card V ≤ 4 * U.card ∧
      2 * U.card ≤ Fintype.card V := by
  classical
  let candidates := Finset.univ.powerset.filter fun U : Finset V =>
    SeparatedBy G B U ∧ 2 * U.card ≤ Fintype.card V
  have empty : (∅ : Finset V) ∈ candidates := by simp [candidates, SeparatedBy]
  obtain ⟨U, hU, maximal⟩ := candidates.exists_max_image Finset.card ⟨∅, empty⟩
  have prop := (Finset.mem_filter.mp hU).2
  by_cases large : Fintype.card V ≤ 4 * U.card
  · exact ⟨U, prop.1, large, prop.2⟩
  have existsOutside : ∃ v : V, v ∉ U ∪ B := by
    by_contra no
    have cover : Finset.univ ⊆ U ∪ B := by
      intro v _
      by_contra fail
      exact no ⟨v, fail⟩
    have count := (Finset.card_le_card cover).trans (Finset.card_union_le U B)
    rw [Finset.card_univ] at count
    omega
  obtain ⟨v, hv⟩ := existsOutside
  have outsideU : v ∉ U := fun h => hv (Finset.mem_union_left _ h)
  have outsideB : v ∉ B := fun h => hv (Finset.mem_union_right _ h)
  let C := componentOutside G B v
  have sepC : SeparatedBy G B C := componentOutside_separated B v outsideB
  have halfC : 2 * C.card ≤ Fintype.card V :=
    balanced C (componentOutside_connected B v) sepC.1
  by_cases largeC : Fintype.card V ≤ 4 * C.card
  · exact ⟨C, sepC, largeC, halfC⟩
  have disjoint : Disjoint U C := componentOutside_disjoint B U prop.1 v outsideU
  have unionCard := Finset.card_union_of_disjoint disjoint
  have unionMember : U ∪ C ∈ candidates := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), prop.1.union sepC, ?_⟩
    omega
  have max := maximal (U ∪ C) unionMember
  have positive : 0 < C.card := Finset.card_pos.mpr ⟨v, componentOutside_self B v⟩
  omega

/-- Outside vertex boundary; it counts vertices, not crossing edge occurrences. -/
noncomputable def outerBoundary (G : SimpleGraph V) (U : Finset V) : Finset V := by
  classical
  exact Finset.univ.filter fun v => v ∉ U ∧ ∃ u ∈ U, G.Adj u v

/-- Expansion at least 1/c on every set of size at most half the graph. -/
def VertexExpansion (G : SimpleGraph V) (c : ℕ) : Prop :=
  0 < c ∧ ∀ U : Finset V, 2 * U.card ≤ Fintype.card V →
    U.card ≤ c * (outerBoundary G U).card

theorem SeparatedBy.boundary_subset {B U : Finset V} (h : SeparatedBy G B U) :
    outerBoundary G U ⊆ B := by
  classical
  intro v hv
  obtain ⟨outside, u, hu, edge⟩ := (Finset.mem_filter.mp hv).2
  exact (h.2 u hu v edge).resolve_left outside

/-- The balanced-bag argument gives an explicit expansion-to-capacity bound. -/
theorem expansion_capacity_lower (c k : ℕ) (expansion : VertexExpansion G c)
    (capacity : HasTreeCapacity G k) : Fintype.card V ≤ 4 * c * k := by
  obtain ⟨D, bound⟩ := capacity
  obtain ⟨i, balanced⟩ := D.balanced_bag
  by_cases large : Fintype.card V ≤ 4 * (D.bag i).card
  · have cOne : 1 ≤ c := expansion.1
    have bound' : (D.bag i).card ≤ c * k := (bound i).trans (by
      simpa using Nat.mul_le_mul_right k cOne)
    exact large.trans (by simpa [Nat.mul_assoc] using Nat.mul_le_mul_left 4 bound')
  · obtain ⟨U, sep, quarter, half⟩ := balanced_separated_set (D.bag i) (by omega) balanced
    have exp := expansion.2 U half
    have boundary := Finset.card_le_card sep.boundary_subset
    have scaled := Nat.mul_le_mul_left c (boundary.trans (bound i))
    exact quarter.trans (by
      simpa [Nat.mul_assoc] using Nat.mul_le_mul_left 4 (exp.trans scaled))

theorem expansion_treewidth_lower (c w : ℕ) (expansion : VertexExpansion G c)
    (width : TreewidthLE G w) : Fintype.card V ≤ 4 * c * (w + 1) :=
  expansion_capacity_lower c (w + 1) expansion width

section Transfers
variable {Host Signal : Type} [Fintype Host] [DecidableEq Host]
    [Fintype Signal] [DecidableEq Signal]

omit [Fintype Host] in
theorem minor_expansion_treewidth_lower {H : SimpleGraph Host}
    (model : MinorModel G H) (c w : ℕ) (expansion : VertexExpansion G c)
    (width : TreewidthLE H w) : Fintype.card V ≤ 4 * c * (w + 1) :=
  expansion_treewidth_lower c w expansion (model.treewidth_mono width)

/-- Whole-net deletion precedes the retained-net arity estimate. -/
theorem retained_net_cut_lower (H : NetSystem Host Signal)
    (vertices : Finset Host) (signals : Finset Signal)
    (model : MinorModel G ((H.restrict vertices signals).twoSection))
    (c arity k : ℕ) (expansion : VertexExpansion G c)
    (bounded : ∀ s, ((H.restrict vertices signals).net s).card ≤ arity)
    (order : Host ≃ Fin (Fintype.card Host)) (cut : H.CutBound order k) :
    Fintype.card V ≤ 4 * c * (arity * k + 1) := by
  apply minor_expansion_treewidth_lower model c (arity * k) expansion
  exact (H.restrict vertices signals).cutBound_treewidth order arity k bounded
    (H.restrict_cutBound vertices signals order k cut)

end Transfers

section Blocks
open CircuitLayout
variable {Input Gate Signal Block : Type} [Fintype Gate] [DecidableEq Gate]
    [Fintype Signal] [DecidableEq Block]

/-- The input bound is derived from first entering owner signals, rather than
assumed as a bound on the number of regions meeting each block. -/
theorem owner_block_lower (L : CircuitLayout Input Gate Unit Signal)
    (owner : Signal → Option V) (branch : V → Finset Gate)
    (paths : ∀ v, ∀ g ∈ branch v, OwnedPath L owner v g)
    (partition : Gate → Block) {Q : SimpleGraph Block}
    (projection : RegionProjection G Q)
    (regions : ∀ v, projection.region v = (branch v).image partition)
    (c K w : ℕ) (expansion : VertexExpansion G c)
    (inputs : ∀ b, (L.blockInputs (gateBlock partition b)).card ≤ K)
    (width : TreewidthLE Q w) : Fintype.card V ≤ 4 * c * (K * (w + 1)) := by
  have load : projection.LoadBound K := by
    intro b
    have same : projection.occupants b =
        Finset.univ.filter (fun v => ∃ g ∈ branch v, partition g = b) := by
      ext v
      simp [RegionProjection.occupants, regions, Finset.mem_image]
    rw [same]
    exact (owner_region_charge L owner branch paths partition b).trans (inputs b)
  exact expansion_capacity_lower c (K * (w + 1)) expansion
    (projection.block_decomposition_lift K w load width)

end Blocks

namespace CoverNative
open Controller.Reductions Controller.Counting Controller.Native Controller.Native.Parameters Controller.Decoder
variable {n m : ℕ} (J : EnumeratedGraph n m) (driver : Fin n) (layout : PrefixLayout)

def vertex (v : Fin n) : Variable (coverParameters J driver layout) :=
  .internal (.qualifier .faulty v.castSucc)

theorem vertex_injective : Function.Injective (vertex J driver layout) := by
  intro u v h
  have roles := Variable.internal.inj h
  have channels := (Role.qualifier.inj roles).2
  exact Fin.castSucc_injective n channels

theorem edge_primal (e : Fin m) :
    (NativeWidth.primal (coverParameters J driver layout)).Adj
      (vertex J driver layout (J.left e)) (vertex J driver layout (J.right e)) := by
  let p := coverParameters J driver layout
  let role : Internal p := .decoder .faulty ⟨e.val + 1, by change _ < m + 2; omega⟩
  let inputs : List (Lit p) :=
    [internal p (.decoder .faulty ⟨0, by change 0 < m + 2; omega⟩),
      negative (vertex J driver layout (J.left e)), negative (vertex J driver layout (J.right e))]
  have gate_eq : p.gate role = .and inputs := by
    have lt : e.val + 1 < m + 1 := by omega
    simp [p, role, gate, decoderGate, coverParameters, coverDAG, lt,
      inputs, vertex, DAG.childIndex]
  let row := internal p role :: inputs.map CNF.negate
  have row_mem : row ∈ NativeWidth.clauses p := by
    apply List.mem_append_left
    apply List.mem_flatMap.mpr
    refine ⟨role, p.mem_roles role, ?_⟩
    rw [gate_eq]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  refine ⟨?_, row, row_mem, ?_, ?_⟩
  · intro eq
    have same := vertex_injective J driver layout eq
    have ordered := J.ordered e
    rw [same] at ordered
    exact (Nat.lt_irrefl _ ordered)
  · simp [row, inputs, CNF.negate, Std.Sat.Literal.negate, negative]
  · simp [row, inputs, CNF.negate, Std.Sat.Literal.negate, negative]

/-- The graph-CNF cofactor family embeds directly in the complete native primal
graph. This statement concerns the named specification before gate splitting. -/
def primalModel : MinorModel J.graph (NativeWidth.primal (coverParameters J driver layout)) :=
  MinorModel.ofInjective (vertex J driver layout) (vertex_injective J driver layout) (by
    intro u v h
    obtain ⟨e, h | h⟩ := h
    · rw [← h.1, ← h.2]; exact edge_primal J driver layout e
    · rw [← h.2, ← h.1]; exact (edge_primal J driver layout e).symm)

theorem primal_width_lower (c w : ℕ) (expansion : VertexExpansion J.graph c)
    (width : TreewidthLE (NativeWidth.primal (coverParameters J driver layout)) w) :
    n ≤ 4 * c * (w + 1) := by
  simpa using minor_expansion_treewidth_lower (primalModel J driver layout) c w expansion width

end CoverNative

namespace BoundedCover
open Controller.Reductions Controller.Counting Controller.Native Controller.Native.Parameters
open Controller.Native.Bounded Controller.Decoder
variable {n m : ℕ} (J : EnumeratedGraph n m) (driver : Fin n) (layout : PrefixLayout)

theorem edge_bound (e : Fin m) :
    e.val + 1 < (coverParameters J driver layout).decoder.nodeCount := by
  change e.val + 1 < m + 2
  omega

theorem zero_bound :
    0 < (coverParameters J driver layout).decoder.nodeCount := by
  change 0 < m + 2
  omega

def edgeRole (e : Fin m) : Internal (coverParameters J driver layout) :=
  .decoder .faulty ⟨e.val + 1, edge_bound J driver layout e⟩

theorem edge_gate (e : Fin m) :
    (coverParameters J driver layout).gate (edgeRole J driver layout e) = .and
      [internal _ (.decoder .faulty ⟨0, zero_bound J driver layout⟩),
       negative (.internal (.qualifier .faulty (J.left e).castSucc)),
       negative (.internal (.qualifier .faulty (J.right e).castSucc))] := by
  have lt : e.val + 1 < m + 1 := by omega
  simp [edgeRole, gate, decoderGate, coverParameters, coverDAG, lt, DAG.childIndex]

def qualifier (v : Fin n) : GlobalVariable (coverParameters J driver layout) :=
  .original (.internal (.qualifier .faulty v.castSucc))

def auxiliary (e : Fin m) : GlobalVariable (coverParameters J driver layout) :=
  .auxiliary (edgeRole J driver layout e)
    ⟨0, by rw [edge_gate]; simp [auxiliaryCount]⟩

def term (e : Fin m) : GlobalVariable (coverParameters J driver layout) :=
  .original (.internal (edgeRole J driver layout e))

def primal : SimpleGraph (GlobalVariable (coverParameters J driver layout)) :=
  clausePrimal (globalFormula (coverParameters J driver layout)).clauses.toList

private theorem producer_row_mem (p : Parameters) (owner : Internal p)
    (row : CNF.Clause (GlobalVariable p))
    (member : row ∈ (producerFormula p owner).clauses.toList) :
    row ∈ (globalFormula p).clauses.toList := by
  simp only [globalFormula, Controller.CNF.OrderedFormula.Internal.clauses_append, Array.toList_append]
  apply List.mem_append_left
  change row ∈ (globalEquationFormula p).clauses.toList
  have embed (owners : List (Internal p)) (present : owner ∈ owners) :
      row ∈ (owners.foldr (fun role suffix => producerFormula p role ++ suffix)
        Controller.CNF.OrderedFormula.empty).clauses.toList := by
    induction owners with
    | nil => simp at present
    | cons head tail ih =>
      simp only [List.foldr_cons, Controller.CNF.OrderedFormula.Internal.clauses_append, Array.toList_append,
        List.mem_append]
      rcases List.mem_cons.mp present with rfl | present
      · exact Or.inl member
      · exact Or.inr (ih present)
  exact embed p.roles (p.mem_roles owner)

/-- Erasing a local auxiliary index to its natural-number address makes the
row list independent of its arity-indexed local variable type. -/
def addressedRows {α β : Type*} (original : α → β) (aux : ℕ → β)
    (output : CNF.Literal α) (g : CNF.Gate α) : List (CNF.Clause β) :=
  (rows output g).map (Controller.CNF.OrderedFormula.Clause.relabel fun x =>
    match x with | .original v => original v | .auxiliary i => aux i.val)

theorem edge_producer_rows (e : Fin m) :
    (producerFormula (coverParameters J driver layout) (edgeRole J driver layout e)).clauses.toList =
      addressedRows GlobalVariable.original (fun _ => auxiliary J driver layout e)
        (internal _ (edgeRole J driver layout e))
        ((coverParameters J driver layout).gate (edgeRole J driver layout e)) := by
  have count : auxiliaryCount ((coverParameters J driver layout).gate
      (edgeRole J driver layout e)) = 1 := by rw [edge_gate]; rfl
  have slots : localSlots (coverParameters J driver layout) (edgeRole J driver layout e) =
      (fun x => match x with
        | .original v => GlobalVariable.original v
        | .auxiliary _ => auxiliary J driver layout e) := by
    funext x
    cases x with
    | original v => rfl
    | auxiliary i =>
      have value : i.val = 0 := by have h := i.isLt.trans_le count.le; omega
      exact congrArg (GlobalVariable.auxiliary (edgeRole J driver layout e)) (Fin.ext value)
  unfold producerFormula addressedRows
  simp only [CNF.relabel, Controller.CNF.OrderedFormula.relabel, CNF.ofClauses,
    Array.toList_map]
  rw [slots]
  congr 1
  funext row
  apply List.map_congr_left
  intro literal _
  rcases literal with ⟨x, phase⟩
  cases x <;> rfl

set_option backward.isDefEq.respectTransparency false in
/-- The three output-to-input clauses realizing the private edge chain occur
in the complete bounded native formula. -/
theorem edge_rows (e : Fin m) :
    [(auxiliary J driver layout e, false), (qualifier J driver layout (J.left e), false)] ∈
        (globalFormula (coverParameters J driver layout)).clauses.toList ∧
    [(term J driver layout e, false), (auxiliary J driver layout e, true)] ∈
        (globalFormula (coverParameters J driver layout)).clauses.toList ∧
    [(term J driver layout e, false), (qualifier J driver layout (J.right e), false)] ∈
        (globalFormula (coverParameters J driver layout)).clauses.toList := by
  have local_rows : ∀ row ∈ addressedRows GlobalVariable.original
      (fun _ => auxiliary J driver layout e) (internal _ (edgeRole J driver layout e))
      ((coverParameters J driver layout).gate (edgeRole J driver layout e)),
      row ∈ (globalFormula (coverParameters J driver layout)).clauses.toList := by
    intro row member
    apply producer_row_mem _ (edgeRole J driver layout e)
    rw [edge_producer_rows]
    exact member
  rw [edge_gate] at local_rows
  constructor
  · apply local_rows
    simp [addressedRows, rows, expand, foldProducers, foldInputs, foldOutput,
      Junction.gate, Producer.rows, CNF.Gate.clauses, Controller.CNF.OrderedFormula.Clause.relabel,
      originalLiteral, qualifier, internal, negative, CNF.negate, Std.Sat.Literal.negate,
      List.finRange_succ, positive]
  · constructor <;> apply local_rows <;>
      simp [addressedRows, rows, expand, foldProducers, foldInputs, foldOutput,
        Junction.gate, Producer.rows, CNF.Gate.clauses, Controller.CNF.OrderedFormula.Clause.relabel,
        originalLiteral, qualifier, term, internal, negative, CNF.negate, Std.Sat.Literal.negate,
        List.finRange_succ, positive]

abbrev Node (n m : ℕ) := Fin n ⊕ Fin m ⊕ Fin m

def embedding : Node n m → GlobalVariable (coverParameters J driver layout)
  | .inl v => qualifier J driver layout v
  | .inr (.inl e) => auxiliary J driver layout e
  | .inr (.inr e) => term J driver layout e

theorem embedding_injective : Function.Injective (embedding J driver layout) := by
  intro x y eq
  cases x with
  | inl v =>
    cases y with
    | inl u =>
      have equal : v.castSucc = u.castSucc := by
        exact (Role.qualifier.inj (Variable.internal.inj (GlobalVariable.original.inj eq))).2
      exact congrArg Sum.inl (Fin.castSucc_injective n equal)
    | inr y => cases y <;> simp [embedding, qualifier, auxiliary, term, edgeRole] at eq
  | inr x =>
    cases x with
    | inl e =>
      cases y with
      | inl v => simp [embedding, qualifier, auxiliary] at eq
      | inr y =>
        cases y with
        | inl f =>
          have roles := (GlobalVariable.auxiliary.inj eq).1
          have vals : e.val + 1 = f.val + 1 := by
            exact congrArg Fin.val (Role.decoder.inj roles).2
          have same : e = f := Fin.ext (by omega)
          subst f; rfl
        | inr f => simp [embedding, auxiliary, term] at eq
    | inr e =>
      cases y with
      | inl v => simp [embedding, term, qualifier, edgeRole] at eq
      | inr y =>
        cases y with
        | inl f => simp [embedding, term, auxiliary] at eq
        | inr f =>
          have vals : e.val + 1 = f.val + 1 := by
            simpa [embedding, term, edgeRole, Fin.ext_iff] using eq
          have same : e = f := Fin.ext (by omega)
          subst f; rfl

def coreGraph : SimpleGraph (Node n m) where
  Adj x y := (primal J driver layout).Adj (embedding J driver layout x) (embedding J driver layout y)
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem core_edges (e : Fin m) :
    (coreGraph J driver layout).Adj (.inl (J.left e)) (.inr (.inl e)) ∧
    (coreGraph J driver layout).Adj (.inr (.inl e)) (.inr (.inr e)) ∧
    (coreGraph J driver layout).Adj (.inr (.inr e)) (.inl (J.right e)) := by
  have distinct {x y : Node n m} (different : x ≠ y) :
      embedding J driver layout x ≠ embedding J driver layout y :=
    fun h => different (embedding_injective J driver layout h)
  obtain ⟨first, second, third⟩ := edge_rows J driver layout e
  constructor
  · exact ⟨distinct (by simp), _, first, by simp [embedding], by simp [embedding]⟩
  · constructor
    · exact ⟨distinct (by simp), _, second, by simp [embedding], by simp [embedding]⟩
    · exact ⟨distinct (by simp), _, third, by simp [embedding], by simp [embedding]⟩

def owner : Node n m → Fin n
  | .inl v => v
  | .inr (.inl e) | .inr (.inr e) => J.left e

def branch (v : Fin n) : Finset (Node n m) :=
  Finset.univ.filter fun x => owner J x = v

@[simp] theorem mem_branch (v : Fin n) (x : Node n m) :
    x ∈ branch J v ↔ owner J x = v := by
  exact (Finset.mem_filter.trans (and_iff_right (Finset.mem_univ x)))

theorem branch_connected (v : Fin n) :
    ConnectedWithin (coreGraph J driver layout) (branch J v) := by
  have hub : Sum.inl v ∈ branch J v := by simp only [mem_branch, owner]
  let step := fun x y => x ∈ branch J v ∧ y ∈ branch J v ∧ (coreGraph J driver layout).Adj x y
  have paths (x : Node n m) (member : x ∈ branch J v) :
      Relation.ReflTransGen step (.inl v) x ∧ Relation.ReflTransGen step x (.inl v) := by
    cases x with
    | inl u =>
      have same : u = v := by simpa only [mem_branch, owner] using member
      subst u; exact ⟨.refl, .refl⟩
    | inr x =>
      cases x with
      | inl e =>
        have same : J.left e = v := by simpa only [mem_branch, owner] using member
        have edge := (core_edges J driver layout e).1
        rw [same] at edge
        exact ⟨.single ⟨hub, member, edge⟩, .single ⟨member, hub, edge.symm⟩⟩
      | inr e =>
        have same : J.left e = v := by simpa only [mem_branch, owner] using member
        have middle : Sum.inr (Sum.inl e) ∈ branch J v := by simp only [mem_branch, owner, same]
        obtain ⟨first, second, _⟩ := core_edges J driver layout e
        rw [same] at first
        exact ⟨(Relation.ReflTransGen.single (r := step) ⟨hub, middle, first⟩).tail ⟨middle, member, second⟩,
          (Relation.ReflTransGen.single (r := step) ⟨member, middle, second.symm⟩).tail ⟨middle, hub, first.symm⟩⟩
  exact ⟨⟨.inl v, hub⟩, fun x hx y hy => (paths x hx).2.trans (paths y hy).1⟩

/-- Qualifier and outgoing private edge gates give disjoint connected branches.
The right endpoint is joined by the final gate's negative qualifier input. -/
def coreMinor : MinorModel J.graph (coreGraph J driver layout) where
  branch := branch J
  connected := branch_connected J driver layout
  disjoint := by
    intro u v different
    apply Finset.disjoint_left.mpr
    intro x hu hv
    simp only [branch, Finset.mem_filter, Finset.mem_univ, true_and] at hu hv
    exact different (hu.symm.trans hv)
  edge := by
    intro u v edge
    obtain ⟨e, h | h⟩ := edge
    · refine ⟨.inr (.inr e), ?_, .inl v, ?_, ?_⟩
      · simp only [mem_branch, owner, h.1]
      · simp only [mem_branch, owner]
      · simpa [h.2] using (core_edges J driver layout e).2.2
    · refine ⟨.inl u, ?_, .inr (.inr e), ?_, ?_⟩
      · simp only [mem_branch, owner]
      · simp only [mem_branch, owner, h.1]
      · simpa [h.2] using (core_edges J driver layout e).2.2.symm

theorem pattern_connected (G : SimpleGraph (Node n m))
    (edges : ∀ e, G.Adj (.inl (J.left e)) (.inr (.inl e)) ∧
      G.Adj (.inr (.inl e)) (.inr (.inr e)) ∧ G.Adj (.inr (.inr e)) (.inl (J.right e)))
    (v : Fin n) :
    ConnectedWithin G (branch J v) := by
  have hub : Sum.inl v ∈ branch J v := by simp only [mem_branch, owner]
  let step := fun x y => x ∈ branch J v ∧ y ∈ branch J v ∧ G.Adj x y
  have paths (x : Node n m) (member : x ∈ branch J v) :
      Relation.ReflTransGen step (.inl v) x ∧ Relation.ReflTransGen step x (.inl v) := by
    cases x with
    | inl u =>
      have same : u = v := by simpa only [mem_branch, owner] using member
      subst u; exact ⟨.refl, .refl⟩
    | inr x =>
      cases x with
      | inl e =>
        have same : J.left e = v := by simpa only [mem_branch, owner] using member
        have edge := (edges e).1
        rw [same] at edge
        exact ⟨.single ⟨hub, member, edge⟩, .single ⟨member, hub, edge.symm⟩⟩
      | inr e =>
        have same : J.left e = v := by simpa only [mem_branch, owner] using member
        have middle : Sum.inr (Sum.inl e) ∈ branch J v := by simp only [mem_branch, owner, same]
        obtain ⟨first, second, _⟩ := edges e
        rw [same] at first
        exact ⟨(Relation.ReflTransGen.single (r := step) ⟨hub, middle, first⟩).tail ⟨middle, member, second⟩,
          (Relation.ReflTransGen.single (r := step) ⟨member, middle, second.symm⟩).tail ⟨middle, hub, first.symm⟩⟩
  exact ⟨⟨.inl v, hub⟩, fun x hx y hy => (paths x hx).2.trans (paths y hy).1⟩

/-- Qualifier and outgoing private edge gates give disjoint connected branches.
The right endpoint is joined by the final gate's negative qualifier input. -/
def patternMinor (G : SimpleGraph (Node n m))
    (edges : ∀ e, G.Adj (.inl (J.left e)) (.inr (.inl e)) ∧
      G.Adj (.inr (.inl e)) (.inr (.inr e)) ∧ G.Adj (.inr (.inr e)) (.inl (J.right e))) :
    MinorModel J.graph G where
  branch := branch J
  connected := pattern_connected J G edges
  disjoint := by
    intro u v different
    apply Finset.disjoint_left.mpr
    intro x hu hv
    simp only [branch, Finset.mem_filter, Finset.mem_univ, true_and] at hu hv
    exact different (hu.symm.trans hv)
  edge := by
    intro u v edge
    obtain ⟨e, h | h⟩ := edge
    · refine ⟨.inr (.inr e), ?_, .inl v, ?_, ?_⟩
      · simp only [mem_branch, owner, h.1]
      · simp only [mem_branch, owner]
      · simpa [h.2] using (edges e).2.2
    · refine ⟨.inl u, ?_, .inr (.inr e), ?_, ?_⟩
      · simp only [mem_branch, owner]
      · simp only [mem_branch, owner, h.1]
      · simpa [h.2] using (edges e).2.2.symm

/-- The lower bound holds after the concrete binary gate expansion, with the
actual private auxiliary coordinates and complete native clauses. -/
theorem primal_width_lower (c w : ℕ) (expansion : VertexExpansion J.graph c)
    (width : TreewidthLE (primal J driver layout) w) : n ≤ 4 * c * (w + 1) := by
  let inclusion : MinorModel (coreGraph J driver layout) (primal J driver layout) :=
    MinorModel.ofInjective (embedding J driver layout) (embedding_injective J driver layout)
      (by intro u v h; exact h)
  simpa only [Fintype.card_fin] using expansion_treewidth_lower c w expansion
    ((coreMinor J driver layout).treewidth_mono (inclusion.treewidth_mono width))

/-- Branch sets in the declared bounded native variable universe. -/
def nativeMinor : MinorModel J.graph (primal J driver layout) where
  branch v := (branch J v).image (embedding J driver layout)
  connected v := by
    have connected := branch_connected J driver layout v
    refine ⟨connected.1.image _, ?_⟩
    intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    apply (connected.2 a ha b hb).lift (embedding J driver layout)
    intro u z h
    exact ⟨Finset.mem_image.mpr ⟨u, h.1, rfl⟩,
      Finset.mem_image.mpr ⟨z, h.2.1, rfl⟩, h.2.2⟩
  disjoint := by
    intro u v different
    apply Finset.disjoint_left.mpr
    intro x hu hv
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨b, hb, eq⟩ := Finset.mem_image.mp hv
    have same := embedding_injective J driver layout eq
    subst b
    exact Finset.disjoint_left.mp ((coreMinor J driver layout).disjoint different) ha hb
  edge := by
    intro u v h
    obtain ⟨a, ha, b, hb, edge⟩ := (coreMinor J driver layout).edge h
    exact ⟨_, Finset.mem_image.mpr ⟨a, ha, rfl⟩,
      _, Finset.mem_image.mpr ⟨b, hb, rfl⟩, edge⟩

def outgoing (v : Fin n) : Finset (Fin m) :=
  Finset.univ.filter fun e => J.left e = v

noncomputable def neighbors (v : Fin n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun u => J.graph.Adj v u

theorem outgoing_card_le (v : Fin n) :
    (outgoing J v).card ≤ (neighbors J v).card := by
  classical
  have injective : Set.InjOn J.right (outgoing J v) := by
    intro e he f hf same
    have lefts : J.left e = J.left f :=
      ((Finset.mem_filter.mp he).2).trans ((Finset.mem_filter.mp hf).2).symm
    exact J.unique (Prod.ext lefts same)
  calc
    _ = ((outgoing J v).image J.right).card := (Finset.card_image_of_injOn injective).symm
    _ ≤ _ := Finset.card_le_card (by
      intro u hu
      obtain ⟨e, member, rfl⟩ := Finset.mem_image.mp hu
      simp only [neighbors, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨e, Or.inl ⟨?_, rfl⟩⟩
      exact (Finset.mem_filter.mp member).2)

/-- Bounded degree gives linear edge count, retaining isolated declared vertices. -/
theorem edges_linear (D : ℕ)
    (degree : ∀ v, (neighbors J v).card ≤ D) : m ≤ n * D := by
  classical
  have cover : (Finset.univ : Finset (Fin m)) = Finset.univ.biUnion (outgoing J) := by
    ext e
    simp only [Finset.mem_univ, Finset.mem_biUnion, true_and, true_iff]
    exact ⟨J.left e, by simp [outgoing]⟩
  calc
    m = (Finset.univ : Finset (Fin m)).card := by simp
    _ = (Finset.univ.biUnion (outgoing J)).card := congrArg Finset.card cover
    _ ≤ ∑ v : Fin n, (outgoing J v).card := Finset.card_biUnion_le
    _ ≤ ∑ _v : Fin n, D := Finset.sum_le_sum fun v _ => (outgoing_card_le J v).trans (degree v)
    _ = n * D := by simp

def roleWeight : Internal (coverParameters J driver layout) → ℕ
  | .driver | .remaining => n + 2
  | .firstProduct _ => 4
  | .decoder _ i => 4 + if i.val = m + 1 then m else 0
  | _ => 3

set_option backward.isDefEq.respectTransparency false in
theorem gate_weight (role : Internal (coverParameters J driver layout)) :
    ((coverParameters J driver layout).gate role).inputs.length + 1 ≤
      roleWeight J driver layout role := by
  have drivers := (coverParameters J driver layout).bridge.drivers.card_le_univ
  have remaining := (coverParameters J driver layout).bridge.remaining.card_le_univ
  simp only [Fintype.card_fin] at drivers remaining
  change _ ≤ n + 1 at drivers remaining
  cases role with
  | driver => simpa [roleWeight, gate, CNF.Gate.inputs] using Nat.add_le_add_right drivers 1
  | remaining => simpa [roleWeight, gate, CNF.Gate.inputs] using Nat.add_le_add_right remaining 1
  | firstProduct side => cases side <;> simp [roleWeight, gate, CNF.Gate.inputs]
  | term side bus channel =>
    have zero : bus.val = 0 := by have h := bus.isLt; change bus.val < 1 at h; omega
    cases layout <;>
      simp [roleWeight, gate, termGate, rawTermInputs, coverParameters, CNF.Gate.inputs,
        List.finRange_succ, Fin.lt_def]
  | absent side bus channel => simp [roleWeight, gate, CNF.Gate.inputs]
  | flag side bus =>
    have zero : bus.val = 0 := by have h := bus.isLt; change bus.val < 1 at h; omega
    simp [roleWeight, gate, CNF.Gate.inputs]
  | mask side bus channel => simp [roleWeight, gate, CNF.Gate.inputs]
  | active side bus channel =>
    cases layout with
    | raw => exact Fin.elim0 bus
    | shared =>
      have zero : bus.val = 0 := by have h := bus.isLt; change bus.val < 1 at h; omega
      simp [roleWeight, gate, activeGate, coverParameters, CNF.Gate.inputs]
  | qualifierGuard side bus channel => simp [roleWeight, gate, CNF.Gate.inputs]
  | qualifier side channel => simp [roleWeight, gate, CNF.Gate.inputs, coverParameters]
  | decoder side i =>
    have bound : i.val < m + 2 := i.isLt
    by_cases first : i.val = 0
    · have notLast : i.val ≠ m + 1 := by omega
      simp [roleWeight, gate, decoderGate, coverParameters, coverDAG, first,
        CNF.Gate.inputs]
    · by_cases term : i.val < m + 1
      · have notLast : i.val ≠ m + 1 := by omega
        simp [roleWeight, gate, decoderGate, coverParameters, coverDAG, first, term, notLast,
          CNF.Gate.inputs]
      · have last : i.val = m + 1 := by omega
        simp [roleWeight, gate, decoderGate, coverParameters, coverDAG, last,
          CNF.Gate.inputs]
  | difference output => simp [roleWeight, gate, CNF.Gate.inputs]
  | detected => simp [roleWeight, gate, CNF.Gate.inputs, coverParameters, coverDAG]

theorem sparse_decoder_weights : ((List.finRange (m + 2)).map
    (fun i => if i.val = m + 1 then m else 0)).sum = m := by
  rw [← List.ofFn_eq_map, List.sum_ofFn]
  have eq : (fun i : Fin (m + 2) => if i.val = m + 1 then m else 0) =
      fun i => if i = Fin.last (m + 1) then m else 0 := by
    funext i
    simp [Fin.ext_iff]
  rw [eq]
  simp

theorem decoder_weights :
    ((List.finRange (m + 2)).map (fun i => 4 + if i.val = m + 1 then m else 0)).sum =
      4 * (m + 2) + m := by
  rw [List.sum_map_add]
  simp only [List.map_const', List.length_finRange, List.sum_replicate_nat, sparse_decoder_weights]
  omega

set_option backward.isDefEq.respectTransparency false in
theorem role_weights :
    ((coverParameters J driver layout).roles.map (roleWeight J driver layout)).sum ≤
      40 * (n + 1) + 12 * m + 80 := by
  have single : List.finRange 1 = [0] := by decide
  cases layout <;>
    simp [roles, roleWeight, coverParameters, coverDAG, Side.all, PrefixLayout.activeCount,
      List.map_map, Function.comp_def, sparse_decoder_weights, single] <;>
    omega

theorem block_size_bound {α : Type*} (g : CNF.Gate α) :
    auxiliaryCount g + expansionRowCount g + expansionLiteralCount g ≤
      17 * (g.inputs.length + 1) := by
  cases g <;>
    simp only [auxiliaryCount, expansionRowCount, expansionLiteralCount,
      foldRowCount, foldLiteralCount, CNF.Gate.inputs, List.length_cons, List.length_nil] <;>
    (try split_ifs) <;> omega

def size : Controller.NativeSize where
  variableCount := (globalVariables (coverParameters J driver layout)).length
  clauses := (globalFormula (coverParameters J driver layout)).clauses.size
  literals := literalIncidences (globalFormula (coverParameters J driver layout))

theorem size_variables : (size J driver layout).variableCount =
    Fintype.card (GlobalVariable (coverParameters J driver layout)) := by
  have all : (Finset.univ : Finset (GlobalVariable (coverParameters J driver layout))) =
      (globalVariables (coverParameters J driver layout)).toFinset := by ext; simp
  change (globalVariables _).length = _
  rw [← Finset.card_univ, all, List.toFinset_card_of_nodup (globalVariables_nodup _)]

theorem variables_bound : (coverParameters J driver layout).variableRoles.length ≤
    14 * (n + 1) + 2 * m + 13 := by
  rw [variableRoles_length, roles_length]
  cases layout <;> simp [coverParameters, coverDAG, PrefixLayout.activeCount] <;> omega

theorem size_linear : (size J driver layout).total ≤ 700 * (n + 1) + 210 * m + 1400 := by
  let p := coverParameters J driver layout
  have individual (role : Internal p) :
      auxiliaryCount (p.gate role) + expansionRowCount (p.gate role) +
        expansionLiteralCount (p.gate role) ≤ 17 * roleWeight J driver layout role :=
    (block_size_bound _).trans (Nat.mul_le_mul_left 17 (gate_weight J driver layout role))
  have sum := List.sum_le_sum (l := p.roles) (fun role _ => individual role)
  simp only [List.sum_map_add, List.sum_map_mul_left] at sum
  have weights := role_weights J driver layout
  have allocated := variables_bound J driver layout
  have scaled := Nat.mul_le_mul_left 17 weights
  change (globalVariables p).length + (globalFormula p).clauses.size +
    literalIncidences (globalFormula p) ≤ _
  rw [globalVariables_length, globalFormula_rows, globalFormula_literals]
  dsimp only [p] at *
  omega

theorem size_degree_linear (D : ℕ) (degree : ∀ v, (neighbors J v).card ≤ D) :
    (size J driver layout).total ≤ 3000 * (D + 1) * n := by
  have vertices : 1 ≤ n := by have h := driver.isLt; omega
  have edges := edges_linear J D degree
  have bound := size_linear J driver layout
  nlinarith

/-- Linear width in the complete bounded native size, including all declared
variables, assertion rows and literal occurrences. -/
theorem primal_width_size_lower (c D w : ℕ) (expansion : VertexExpansion J.graph c)
    (degree : ∀ v, (neighbors J v).card ≤ D)
    (width : TreewidthLE (primal J driver layout) w) :
    (size J driver layout).total ≤ 12000 * c * (D + 1) * (w + 1) := by
  have bound := size_degree_linear J driver layout D degree
  have native := primal_width_lower J driver layout c w expansion width
  calc
    _ ≤ 3000 * (D + 1) * n := bound
    _ ≤ 3000 * (D + 1) * (4 * c * (w + 1)) := Nat.mul_le_mul_left _ native
    _ = _ := by ring

/-- The variables-plus-literal-occurrences measure used in the manuscript. -/
def variableLiteralSize : ℕ :=
  (size J driver layout).variableCount + (size J driver layout).literals

theorem variableLiteralSize_le : variableLiteralSize J driver layout ≤
    (size J driver layout).total := by
  unfold variableLiteralSize Controller.NativeSize.total
  omega

theorem primal_width_variableLiteralSize_lower (c D w : ℕ)
    (expansion : VertexExpansion J.graph c) (degree : ∀ v, (neighbors J v).card ≤ D)
    (width : TreewidthLE (primal J driver layout) w) :
    variableLiteralSize J driver layout ≤ 12000 * c * (D + 1) * (w + 1) :=
  (variableLiteralSize_le J driver layout).trans
    (primal_width_size_lower J driver layout c D w expansion degree width)

end BoundedCover

end Controller.Graph
