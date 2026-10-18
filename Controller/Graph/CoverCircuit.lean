module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Graph.BoundedCircuit
public import Controller.Graph.ExpanderLayout

public import Mathlib.Tactic.Ring

@[expose] public section

/-! Actual qualifier and private edge gates in the complete binary graph-cover
circuit. Producer data is read from the native expansion, retaining polarity. -/
namespace Controller.Graph.CoverCircuit
open Controller.Reductions Controller.Counting Controller.Native Controller.Native.Parameters
open Controller.Native.Bounded Controller.Graph.BoundedCircuit

/-- Form the owner path before specializing the native parameter package. -/
theorem primary_path {p : Parameters} (owns : GlobalVariable p → Option α)
    (v : α) (input : PrimaryRole p.channels p.buses) (g : Gate p)
    (connection : GlobalVariable.original (.primary input) ∈ (producer p g).gate.inputs.map Prod.fst)
    (owned : owns (.original (.primary input)) = some v) :
    CircuitLayout.OwnedPath (BoundedCircuit.layout p) owns v g := by
  refine CircuitLayout.OwnedPath.primary (L := BoundedCircuit.layout p) (owner := owns) (v := v)
    (.original (.primary input)) input g (layout_primary_producer p input)
    ?_ owned
  rw [layout_connection]
  exact connection

theorem step_path {p : Parameters} (owns : GlobalVariable p → Option α)
    (v : α) (previous g : Gate p)
    (path : CircuitLayout.OwnedPath (BoundedCircuit.layout p) owns v previous)
    (connection : output p previous ∈ (producer p g).gate.inputs.map Prod.fst)
    (owned : owns (output p previous) = some v) :
    CircuitLayout.OwnedPath (BoundedCircuit.layout p) owns v g := by
  have source : (BoundedCircuit.layout p).producer (output p previous) = .inr previous := by
    simpa only [producer_output] using layout_producer p previous
  refine CircuitLayout.OwnedPath.step (L := BoundedCircuit.layout p) (owner := owns) (v := v)
    (output p previous) previous g path source
    ?_ owned
  rw [layout_connection]
  exact connection

variable {n m : ℕ} (J : EnumeratedGraph n m) (driver : Fin n) (layout : PrefixLayout)

abbrev parameters := coverParameters J driver layout

def qualifierGate (v : Fin n) : Gate (parameters J driver layout) :=
  principal _ (.qualifier .faulty v.castSucc)

def edgeAuxGate (e : Fin m) : Gate (parameters J driver layout) :=
  privateGate _ (BoundedCover.edgeRole J driver layout e)
    ⟨0, by rw [BoundedCover.edge_gate]; simp [auxiliaryCount]⟩

def edgeTermGate (e : Fin m) : Gate (parameters J driver layout) :=
  principal _ (BoundedCover.edgeRole J driver layout e)

def edgeAuxProducer (e : Fin m) : Producer (GlobalVariable (parameters J driver layout)) :=
  { output := (BoundedCover.auxiliary J driver layout e, true),
         gate := .and [(.original (.internal (.decoder .faulty ⟨0, by
           change 0 < m + 2; omega⟩)), true),
           (BoundedCover.qualifier J driver layout (J.left e), false)] }

def edgeTermProducer (e : Fin m) : Producer (GlobalVariable (parameters J driver layout)) :=
  { output := (BoundedCover.term J driver layout e, true),
         gate := .and [(BoundedCover.auxiliary J driver layout e, true),
           (BoundedCover.qualifier J driver layout (J.right e), false)] }

def qualifierProducer (v : Fin n) : Producer (GlobalVariable (parameters J driver layout)) :=
  { output := (BoundedCover.qualifier J driver layout v, true),
         gate := .and [(.original (.primary (.enable v.castSucc)), true),
           (.original (.internal (.qualifierGuard .faulty ⟨0, by change 0 < 1; omega⟩ v.castSucc)), true)] }

theorem edge_producers (e : Fin m) :
    gateList (parameters J driver layout) (BoundedCover.edgeRole J driver layout e) =
      [edgeAuxProducer J driver layout e, edgeTermProducer J driver layout e] := by
  rw [gateList_addressed, BoundedCover.edge_gate]
  simp [edgeAuxProducer, edgeTermProducer, addressedProducers, expand, foldProducers, foldInputs, foldOutput,
    List.finRange_succ, Junction.gate, Producer.relabel, CNF.Gate.relabel,
    originalLiteral, auxiliaryAt, BoundedCover.edge_gate, auxiliaryCount,
    BoundedCover.auxiliary, BoundedCover.qualifier, BoundedCover.term,
    internal, negative, positive]

set_option backward.isDefEq.respectTransparency false in
theorem qualifier_producers (v : Fin n) :
    gateList (parameters J driver layout) (.qualifier .faulty v.castSucc) =
      [qualifierProducer J driver layout v] := by
  have native : (parameters J driver layout).gate (.qualifier .faulty v.castSucc) =
      .and [enable _ v.castSucc, internal _ (.qualifierGuard .faulty ⟨0, by change 0 < 1; omega⟩ v.castSucc)] := by
    simp [parameters, gate, coverParameters, List.finRange_succ]
  rw [gateList_addressed, native]
  simp [qualifierProducer, addressedProducers, expand, foldProducers, foldInputs,
    foldOutput, List.finRange_succ, Junction.gate, Producer.relabel, CNF.Gate.relabel,
    originalLiteral, BoundedCover.qualifier, internal, enable, positive]

@[simp] theorem qualifier_output (v : Fin n) :
    output _ (qualifierGate J driver layout v) = BoundedCover.qualifier J driver layout v := by
  simp [qualifierGate, BoundedCover.qualifier]

@[simp] theorem edgeAux_output (e : Fin m) :
    output _ (edgeAuxGate J driver layout e) = BoundedCover.auxiliary J driver layout e := by
  simp [edgeAuxGate, BoundedCover.auxiliary]

@[simp] theorem edgeTerm_output (e : Fin m) :
    output _ (edgeTermGate J driver layout e) = BoundedCover.term J driver layout e := by
  simp [edgeTermGate, BoundedCover.term]

theorem qualifier_data (v : Fin n) :
    producer _ (qualifierGate J driver layout v) = qualifierProducer J driver layout v := by
  apply producer_eq_of_mem
  · apply List.mem_flatMap.mpr
    refine ⟨.qualifier .faulty v.castSucc, mem_roles _ _, ?_⟩
    rw [qualifier_producers]
    simp
  · simp [qualifierProducer]

theorem edgeAux_data (e : Fin m) :
    producer _ (edgeAuxGate J driver layout e) = edgeAuxProducer J driver layout e := by
  apply producer_eq_of_mem
  · apply List.mem_flatMap.mpr
    refine ⟨BoundedCover.edgeRole J driver layout e, mem_roles _ _, ?_⟩
    rw [edge_producers]
    simp
  · simp [edgeAuxProducer]

theorem edgeTerm_data (e : Fin m) :
    producer _ (edgeTermGate J driver layout e) = edgeTermProducer J driver layout e := by
  apply producer_eq_of_mem
  · apply List.mem_flatMap.mpr
    refine ⟨BoundedCover.edgeRole J driver layout e, mem_roles _ _, ?_⟩
    rw [edge_producers]
    simp
  · simp [edgeTermProducer]

theorem qualifier_connection (v : Fin n) :
    Sum.inl (qualifierGate J driver layout v) ∈
      (BoundedCircuit.layout (parameters J driver layout)).consumers
        (.original (.primary (.enable v.castSucc))) := by
  rw [layout_connection, qualifier_data]
  simp [qualifierProducer, CNF.Gate.inputs]

theorem edge_connections (e : Fin m) :
    Sum.inl (edgeAuxGate J driver layout e) ∈
        (BoundedCircuit.layout (parameters J driver layout)).consumers
          (BoundedCover.qualifier J driver layout (J.left e)) ∧
    Sum.inl (edgeTermGate J driver layout e) ∈
        (BoundedCircuit.layout (parameters J driver layout)).consumers
          (BoundedCover.auxiliary J driver layout e) ∧
    Sum.inl (edgeTermGate J driver layout e) ∈
        (BoundedCircuit.layout (parameters J driver layout)).consumers
          (BoundedCover.qualifier J driver layout (J.right e)) := by
  simp [layout_connection, edgeAux_data, edgeTerm_data, edgeAuxProducer,
    edgeTermProducer, CNF.Gate.inputs]

def channelOwner (i : Fin (n + 1)) : Option (Fin n) :=
  if h : i.val < n then some ⟨i.val, h⟩ else none

/-- Only the primary enables, faulty qualifiers and private edge prefixes
used by the branch paths carry graph-vertex owners. -/
def signalOwner : GlobalVariable (parameters J driver layout) → Option (Fin n)
  | .original (.primary (.enable i)) => channelOwner i
  | .original (.internal (.qualifier .faulty i)) => channelOwner i
  | .auxiliary (.decoder .faulty i) _ =>
    if h : 0 < i.val ∧ i.val ≤ m then some (J.left ⟨i.val - 1, by omega⟩) else none
  | _ => none

@[simp] theorem owner_enable (v : Fin n) :
    signalOwner J driver layout (.original (.primary (.enable v.castSucc))) = some v := by
  simp [signalOwner, channelOwner, v.isLt]

@[simp] theorem owner_qualifier (v : Fin n) :
    signalOwner J driver layout (BoundedCover.qualifier J driver layout v) = some v := by
  simp [signalOwner, channelOwner, BoundedCover.qualifier, v.isLt]

@[simp] theorem owner_auxiliary (e : Fin m) :
    signalOwner J driver layout (BoundedCover.auxiliary J driver layout e) = some (J.left e) := by
  have bound : e.val + 1 ≤ m := by omega
  simp [signalOwner, BoundedCover.auxiliary, BoundedCover.edgeRole, bound]

theorem qualifier_path (v : Fin n) :
    CircuitLayout.OwnedPath (BoundedCircuit.layout (parameters J driver layout))
      (signalOwner J driver layout) v (qualifierGate J driver layout v) := by
  apply primary_path (signalOwner J driver layout) v (.enable v.castSucc)
  · rw [qualifier_data]
    simp [qualifierProducer, CNF.Gate.inputs]
  · exact owner_enable J driver layout v

theorem edgeAux_path (e : Fin m) :
    CircuitLayout.OwnedPath (BoundedCircuit.layout (parameters J driver layout))
      (signalOwner J driver layout) (J.left e) (edgeAuxGate J driver layout e) := by
  apply step_path (signalOwner J driver layout) (J.left e)
    (qualifierGate J driver layout (J.left e)) _ (qualifier_path J driver layout (J.left e))
  · rw [qualifier_output, edgeAux_data]
    simp [edgeAuxProducer, CNF.Gate.inputs]
  · rw [qualifier_output]
    exact owner_qualifier J driver layout (J.left e)

theorem edgeTerm_path (e : Fin m) :
    CircuitLayout.OwnedPath (BoundedCircuit.layout (parameters J driver layout))
      (signalOwner J driver layout) (J.left e) (edgeTermGate J driver layout e) := by
  apply step_path (signalOwner J driver layout) (J.left e)
    (edgeAuxGate J driver layout e) _ (edgeAux_path J driver layout e)
  · rw [edgeAux_output, edgeTerm_data]
    simp [edgeTermProducer, CNF.Gate.inputs]
  · rw [edgeAux_output]
    exact owner_auxiliary J driver layout e

def embedding : BoundedCover.Node n m → Gate (parameters J driver layout)
  | .inl v => qualifierGate J driver layout v
  | .inr (.inl e) => edgeAuxGate J driver layout e
  | .inr (.inr e) => edgeTermGate J driver layout e

@[simp] theorem output_embedding (x : BoundedCover.Node n m) :
    output _ (embedding J driver layout x) = BoundedCover.embedding J driver layout x := by
  cases x with
  | inl v => exact qualifier_output J driver layout v
  | inr x => cases x <;> simp [embedding, BoundedCover.embedding]

theorem embedding_injective : Function.Injective (embedding J driver layout) := by
  intro x y eq
  apply BoundedCover.embedding_injective J driver layout
  simpa only [output_embedding] using congrArg (output (parameters J driver layout)) eq

def branch (v : Fin n) : Finset (Gate (parameters J driver layout)) :=
  (BoundedCover.branch J v).image (embedding J driver layout)

set_option backward.isDefEq.respectTransparency false in
theorem embedding_path (x : BoundedCover.Node n m) :
    CircuitLayout.OwnedPath (BoundedCircuit.layout (parameters J driver layout))
      (signalOwner J driver layout) (BoundedCover.owner J x) (embedding J driver layout x) := by
  cases x with
  | inl v => exact qualifier_path J driver layout v
  | inr x =>
    cases x with
    | inl e => exact edgeAux_path J driver layout e
    | inr e => exact edgeTerm_path J driver layout e

set_option backward.isDefEq.respectTransparency false in
theorem branch_paths (v : Fin n) (g : Gate (parameters J driver layout))
    (member : g ∈ branch J driver layout v) :
    CircuitLayout.OwnedPath (BoundedCircuit.layout (parameters J driver layout))
      (signalOwner J driver layout) v g := by
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp member
  have same := (BoundedCover.mem_branch J v x).mp hx
  simpa only [same] using embedding_path J driver layout x

set_option backward.isDefEq.respectTransparency false in
/-- Every gate partition is charged by its actual distinct entering signals,
including primary enable signals. -/
theorem branch_entry_charge {Block : Type} [DecidableEq Block]
    (partition : Gate (parameters J driver layout) → Block) (b : Block) :
    (Finset.univ.filter (fun v => ∃ g ∈ branch J driver layout v, partition g = b)).card ≤
      ((BoundedCircuit.layout (parameters J driver layout)).blockInputs
        (CircuitLayout.gateBlock partition b)).card := by
  exact CircuitLayout.owner_region_charge _ (signalOwner J driver layout)
    (branch J driver layout) (branch_paths J driver layout) partition b

/-- The undirected graph of actual gate-to-gate wires. Sibling inputs do not
create an edge unless one is also the other's output. -/
def gateGraph : SimpleGraph (Gate (parameters J driver layout)) where
  Adj g h := g ≠ h ∧
    (output _ g ∈ (producer _ h).gate.inputs.map Prod.fst ∨
     output _ h ∈ (producer _ g).gate.inputs.map Prod.fst)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

def nodeGraph : SimpleGraph (BoundedCover.Node n m) where
  Adj x y := (gateGraph J driver layout).Adj (embedding J driver layout x) (embedding J driver layout y)
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

set_option linter.constructorNameAsVariable false in
theorem core_edges (e : Fin m) :
    (nodeGraph J driver layout).Adj (.inl (J.left e)) (.inr (.inl e)) ∧
    (nodeGraph J driver layout).Adj (.inr (.inl e)) (.inr (.inr e)) ∧
    (nodeGraph J driver layout).Adj (.inr (.inr e)) (.inl (J.right e)) := by
  have distinct {x y : BoundedCover.Node n m} (different : x ≠ y) :
      embedding J driver layout x ≠ embedding J driver layout y :=
    fun h => different (embedding_injective J driver layout h)
  obtain ⟨first, second, third⟩ := edge_connections J driver layout e
  rw [layout_connection] at first second third
  exact ⟨⟨distinct (by simp), Or.inl (by simpa only [embedding, qualifier_output] using first)⟩,
    ⟨distinct (by simp), Or.inl (by simpa only [embedding, edgeAux_output] using second)⟩,
    ⟨distinct (by simp), Or.inr (by simpa only [embedding, qualifier_output] using third)⟩⟩

theorem nodeBranch_connected (v : Fin n) :
    ConnectedWithin (nodeGraph J driver layout) (BoundedCover.branch J v) := by
  have hub : Sum.inl v ∈ BoundedCover.branch J v := by simp only [BoundedCover.mem_branch, BoundedCover.owner]
  let step := fun x y => x ∈ BoundedCover.branch J v ∧ y ∈ BoundedCover.branch J v ∧ (nodeGraph J driver layout).Adj x y
  have paths (x : BoundedCover.Node n m) (member : x ∈ BoundedCover.branch J v) :
      Relation.ReflTransGen step (.inl v) x ∧ Relation.ReflTransGen step x (.inl v) := by
    cases x with
    | inl u =>
      have same : u = v := by simpa only [BoundedCover.mem_branch, BoundedCover.owner] using member
      subst u; exact ⟨.refl, .refl⟩
    | inr x =>
      cases x with
      | inl e =>
        have same : J.left e = v := by simpa only [BoundedCover.mem_branch, BoundedCover.owner] using member
        have edge := (core_edges J driver layout e).1
        rw [same] at edge
        exact ⟨.single ⟨hub, member, edge⟩, .single ⟨member, hub, edge.symm⟩⟩
      | inr e =>
        have same : J.left e = v := by simpa only [BoundedCover.mem_branch, BoundedCover.owner] using member
        have middle : Sum.inr (Sum.inl e) ∈ BoundedCover.branch J v := by simp only [BoundedCover.mem_branch, BoundedCover.owner, same]
        obtain ⟨first, second, _⟩ := core_edges J driver layout e
        rw [same] at first
        exact ⟨(Relation.ReflTransGen.single (r := step) ⟨hub, middle, first⟩).tail ⟨middle, member, second⟩,
          (Relation.ReflTransGen.single (r := step) ⟨member, middle, second.symm⟩).tail ⟨middle, hub, first.symm⟩⟩
  exact ⟨⟨.inl v, hub⟩, fun x hx y hy => (paths x hx).2.trans (paths y hy).1⟩

/-- Qualifier and outgoing private edge gates give disjoint connected branches.
The right endpoint is joined by the final gate's negative qualifier input. -/
def nodeMinor : MinorModel J.graph (nodeGraph J driver layout) where
  branch := BoundedCover.branch J
  connected := nodeBranch_connected J driver layout
  disjoint := by
    intro u v different
    apply Finset.disjoint_left.mpr
    intro x hu hv
    simp only [BoundedCover.branch, Finset.mem_filter, Finset.mem_univ, true_and] at hu hv
    exact different (hu.symm.trans hv)
  edge := by
    intro u v edge
    obtain ⟨e, h | h⟩ := edge
    · refine ⟨.inr (.inr e), ?_, .inl v, ?_, ?_⟩
      · simp only [BoundedCover.mem_branch, BoundedCover.owner, h.1]
      · simp only [BoundedCover.mem_branch, BoundedCover.owner]
      · simpa [h.2] using (core_edges J driver layout e).2.2
    · refine ⟨.inl u, ?_, .inr (.inr e), ?_, ?_⟩
      · simp only [BoundedCover.mem_branch, BoundedCover.owner]
      · simp only [BoundedCover.mem_branch, BoundedCover.owner, h.1]
      · simpa [h.2] using (core_edges J driver layout e).2.2.symm


def circuitMinor : MinorModel J.graph (gateGraph J driver layout) where
  branch v := branch J driver layout v
  connected v := by
    have connected := nodeBranch_connected J driver layout v
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
    exact Finset.disjoint_left.mp ((nodeMinor J driver layout).disjoint different) ha hb
  edge := by
    intro u v h
    obtain ⟨a, ha, b, hb, edge⟩ := (nodeMinor J driver layout).edge h
    exact ⟨_, Finset.mem_image.mpr ⟨a, ha, rfl⟩,
      _, Finset.mem_image.mpr ⟨b, hb, rfl⟩, edge⟩

/-- Width of the complete gate-wire graph is bounded below by the supplied
graph's vertex expansion. Only actual output-to-input wires are used. -/
theorem gate_width_lower (c w : ℕ) (expansion : VertexExpansion J.graph c)
    (width : TreewidthLE (gateGraph J driver layout) w) : n ≤ 4 * c * (w + 1) := by
  simpa only [Fintype.card_fin] using expansion_treewidth_lower c w expansion
    ((circuitMinor J driver layout).treewidth_mono width)

theorem gate_width_size_lower (c D w : ℕ) (expansion : VertexExpansion J.graph c)
    (degree : ∀ v, (BoundedCover.neighbors J v).card ≤ D)
    (width : TreewidthLE (gateGraph J driver layout) w) :
    (BoundedCover.size J driver layout).total ≤ 12000 * c * (D + 1) * (w + 1) := by
  have bound := BoundedCover.size_degree_linear J driver layout D degree
  have circuit := gate_width_lower J driver layout c w expansion width
  calc
    _ ≤ 3000 * (D + 1) * n := bound
    _ ≤ 3000 * (D + 1) * (4 * c * (w + 1)) := Nat.mul_le_mul_left _ circuit
    _ = _ := by ring

theorem gate_width_variableLiteralSize_lower (c D w : ℕ)
    (expansion : VertexExpansion J.graph c) (degree : ∀ v, (BoundedCover.neighbors J v).card ≤ D)
    (width : TreewidthLE (gateGraph J driver layout) w) :
    BoundedCover.variableLiteralSize J driver layout ≤ 12000 * c * (D + 1) * (w + 1) :=
  (BoundedCover.variableLiteralSize_le J driver layout).trans
    (gate_width_size_lower J driver layout c D w expansion degree width)

/-- Every partition uses the undirected blockgraph of the actual native wires. -/
theorem block_width_lower {Block : Type} [DecidableEq Block]
    (partition : Gate (parameters J driver layout) → Block) (c K w : ℕ)
    (expansion : VertexExpansion J.graph c)
    (inputs : ∀ b, ((BoundedCircuit.layout (parameters J driver layout)).blockInputs
      (CircuitLayout.gateBlock partition b)).card ≤ K)
    (width : TreewidthLE (blockGraph (gateGraph J driver layout) partition) w) :
    n ≤ 4 * c * (K * (w + 1)) := by
  simpa only [Fintype.card_fin] using owner_block_lower
    (BoundedCircuit.layout (parameters J driver layout)) (signalOwner J driver layout)
    (branch J driver layout) (branch_paths J driver layout) partition
    ((circuitMinor J driver layout).blockProjection partition) (fun _ => rfl)
    c K w expansion inputs width

theorem block_width_size_lower {Block : Type} [DecidableEq Block]
    (partition : Gate (parameters J driver layout) → Block) (c D K w : ℕ)
    (expansion : VertexExpansion J.graph c)
    (degree : ∀ v, (BoundedCover.neighbors J v).card ≤ D)
    (inputs : ∀ b, ((BoundedCircuit.layout (parameters J driver layout)).blockInputs
      (CircuitLayout.gateBlock partition b)).card ≤ K)
    (width : TreewidthLE (blockGraph (gateGraph J driver layout) partition) w) :
    (BoundedCover.size J driver layout).total ≤ 12000 * c * (D + 1) * (K * (w + 1)) := by
  calc
    _ ≤ 3000 * (D + 1) * n := BoundedCover.size_degree_linear J driver layout D degree
    _ ≤ 3000 * (D + 1) * (4 * c * (K * (w + 1))) :=
      Nat.mul_le_mul_left _ (block_width_lower J driver layout partition c K w expansion inputs width)
    _ = _ := by ring

theorem block_width_variableLiteralSize_lower {Block : Type} [DecidableEq Block]
    (partition : Gate (parameters J driver layout) → Block) (c D K w : ℕ)
    (expansion : VertexExpansion J.graph c)
    (degree : ∀ v, (BoundedCover.neighbors J v).card ≤ D)
    (inputs : ∀ b, ((BoundedCircuit.layout (parameters J driver layout)).blockInputs
      (CircuitLayout.gateBlock partition b)).card ≤ K)
    (width : TreewidthLE (blockGraph (gateGraph J driver layout) partition) w) :
    BoundedCover.variableLiteralSize J driver layout ≤ 12000 * c * (D + 1) * (K * (w + 1)) :=
  (BoundedCover.variableLiteralSize_le J driver layout).trans
    (block_width_size_lower J driver layout partition c D K w expansion degree inputs width)

/-- The complete native graph includes every primary and output port. -/
noncomputable def portGraph : SimpleGraph (Vertex (parameters J driver layout)) :=
  (BoundedCircuit.layout (parameters J driver layout)).wireGraph

noncomputable def gatePortMinor : MinorModel (gateGraph J driver layout) (portGraph J driver layout) :=
  MinorModel.ofInjective (gateVertex _) (gateVertex_injective _) (by
    intro g h edge
    have source (g : Gate (parameters J driver layout)) :
        (BoundedCircuit.layout (parameters J driver layout)).producer (output _ g) = .inr g := by
      simpa only [producer_output] using layout_producer (parameters J driver layout) g
    refine ⟨fun eq => edge.1 (gateVertex_injective _ eq), ?_⟩
    rcases edge.2 with wire | wire
    · refine ⟨output _ g, .inl h, ?_, Or.inl ?_⟩
      · rw [layout_connection]; exact wire
      · simp only [source, CircuitLayout.inputVertex, CircuitLayout.consumerVertex, gateVertex, and_self]
    · refine ⟨output _ h, .inl g, ?_, Or.inr ?_⟩
      · rw [layout_connection]; exact wire
      · simp only [source, CircuitLayout.inputVertex, CircuitLayout.consumerVertex, gateVertex, and_self])

theorem port_width_lower (c w : ℕ) (expansion : VertexExpansion J.graph c)
    (width : TreewidthLE (portGraph J driver layout) w) : n ≤ 4 * c * (w + 1) :=
  gate_width_lower J driver layout c w expansion ((gatePortMinor J driver layout).treewidth_mono width)

theorem port_width_size_lower (c D w : ℕ) (expansion : VertexExpansion J.graph c)
    (degree : ∀ v, (BoundedCover.neighbors J v).card ≤ D)
    (width : TreewidthLE (portGraph J driver layout) w) :
    (BoundedCover.size J driver layout).total ≤ 12000 * c * (D + 1) * (w + 1) :=
  gate_width_size_lower J driver layout c D w expansion degree
    ((gatePortMinor J driver layout).treewidth_mono width)

theorem port_width_variableLiteralSize_lower (c D w : ℕ)
    (expansion : VertexExpansion J.graph c) (degree : ∀ v, (BoundedCover.neighbors J v).card ≤ D)
    (width : TreewidthLE (portGraph J driver layout) w) :
    BoundedCover.variableLiteralSize J driver layout ≤ 12000 * c * (D + 1) * (w + 1) :=
  (BoundedCover.variableLiteralSize_le J driver layout).trans
    (port_width_size_lower J driver layout c D w expansion degree width)

end Controller.Graph.CoverCircuit
