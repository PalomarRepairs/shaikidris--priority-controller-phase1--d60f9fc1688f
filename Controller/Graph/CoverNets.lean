module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Graph.CoverIncidence

public import Mathlib.Tactic.Ring

@[expose] public section

/-! Whole-net deletion and bounded retained arity in the actual native layout. -/
namespace Controller.Graph.CoverCircuit
open Controller.Reductions Controller.Counting Controller.Native Controller.Native.Parameters
open Controller.Native.Bounded Controller.Graph.BoundedCircuit
variable {n m : ℕ} (J : EnumeratedGraph n m) (driver : Fin n) (layout : PrefixLayout)

/-- The shared target value read by every private edge prefix. -/
def targetSignal : GlobalVariable (parameters J driver layout) :=
  .original (.internal (.decoder .faulty ⟨0, by change 0 < m+2; omega⟩))

def nodeVertex (x : BoundedCover.Node n m) : Vertex (parameters J driver layout) :=
  gateVertex _ (embedding J driver layout x)

theorem nodeVertex_injective : Function.Injective (nodeVertex J driver layout) :=
  (gateVertex_injective _).comp (embedding_injective J driver layout)

noncomputable def fullNets := (BoundedCircuit.layout (parameters J driver layout)).nets

def retainedVertices : Finset (Vertex (parameters J driver layout)) :=
  Finset.univ.image (nodeVertex J driver layout)

/-- Delete the complete shared target and selector nets before restricting vertices. -/
def deletedSignal : GlobalVariable (parameters J driver layout) → Prop
  | .original (.internal (.decoder .faulty i)) => i.val = 0
  | .original (.internal (.qualifier .faulty i)) => i.val = n
  | .original (.internal (.flag _ _)) => True
  | _ => False

noncomputable def retainedSignals : Finset (GlobalVariable (parameters J driver layout)) := by
  classical
  exact Finset.univ.filter fun s => ¬ deletedSignal J driver layout s

noncomputable def retainedNets := (fullNets J driver layout).restrict
  (retainedVertices J driver layout) (retainedSignals J driver layout)

/-- A qualifier has one private enable and one private qualifier-guard input. -/
def qualifierUsers (s : GlobalVariable (parameters J driver layout)) : Finset (Fin n) :=
  Finset.univ.filter fun v => s ∈ (qualifierProducer J driver layout v).gate.inputs.map Prod.fst

theorem qualifierUsers_card (s : GlobalVariable (parameters J driver layout)) :
    (qualifierUsers J driver layout s).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro v hv u hu
  simp only [qualifierUsers, Finset.mem_filter, Finset.mem_univ, true_and,
    qualifierProducer, CNF.Gate.inputs, List.map_cons, List.map_nil,
    List.mem_cons, List.not_mem_nil, or_false] at hv hu
  rcases hv with hv | hv <;> rcases hu with hu | hu
  · have eq := GlobalVariable.original.inj (hv.symm.trans hu)
    exact Fin.castSucc_injective n (PrimaryRole.enable.inj (Variable.primary.inj eq))
  · cases (GlobalVariable.original.inj (hv.symm.trans hu))
  · cases (GlobalVariable.original.inj (hv.symm.trans hu))
  · have eq := GlobalVariable.original.inj (hv.symm.trans hu)
    exact Fin.castSucc_injective n (Role.qualifierGuard.inj (Variable.internal.inj eq)).2.2

/-- Edge consumers of one qualifier, with their opposite graph endpoint. -/
noncomputable def incidentNodes (v : Fin n) : Finset (BoundedCover.Node n m) := by
  classical
  exact Finset.univ.filter fun x => match x with
    | .inl _ => False
    | .inr (.inl e) => J.left e = v
    | .inr (.inr e) => J.right e = v

def opposite : BoundedCover.Node n m → Fin n
  | .inl v => v
  | .inr (.inl e) => J.right e
  | .inr (.inr e) => J.left e

theorem incidentNodes_injective (v : Fin n) : Set.InjOn (opposite J) (incidentNodes J v) := by
  classical
  intro x hx y hy eq
  cases x with
  | inl u => simp [incidentNodes] at hx
  | inr x =>
    cases y with
    | inl u => simp [incidentNodes] at hy
    | inr y =>
      cases x with
      | inl e =>
        have he : J.left e = v := (Finset.mem_filter.mp hx).2
        cases y with
        | inl f =>
          have hf : J.left f = v := (Finset.mem_filter.mp hy).2
          have same := J.unique (Prod.ext (he.trans hf.symm) eq)
          subst f; rfl
        | inr f =>
          have hf : J.right f = v := (Finset.mem_filter.mp hy).2
          have oe := J.ordered e; have of := J.ordered f
          change J.right e = J.left f at eq
          rw [he] at oe; rw [hf, ← eq] at of
          omega
      | inr e =>
        have he : J.right e = v := (Finset.mem_filter.mp hx).2
        cases y with
        | inl f =>
          have hf : J.left f = v := (Finset.mem_filter.mp hy).2
          have oe := J.ordered e; have of := J.ordered f
          change J.left e = J.right f at eq
          rw [he, eq] at oe; rw [hf] at of
          omega
        | inr f =>
          have hf : J.right f = v := (Finset.mem_filter.mp hy).2
          have same := J.unique (Prod.ext eq (he.trans hf.symm))
          subst f; rfl

theorem incidentNodes_card (v : Fin n) :
    (incidentNodes J v).card ≤ (BoundedCover.neighbors J v).card := by
  classical
  calc
    _ = ((incidentNodes J v).image (opposite J)).card :=
      (Finset.card_image_of_injOn (incidentNodes_injective J v)).symm
    _ ≤ _ := Finset.card_le_card (by
      intro u hu
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hu
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      cases x with
      | inl a => simp [incidentNodes] at hx
      | inr x =>
        cases x with
        | inl e => exact ⟨e, Or.inl ⟨(Finset.mem_filter.mp hx).2,rfl⟩⟩
        | inr e => exact ⟨e, Or.inr ⟨rfl,(Finset.mem_filter.mp hx).2⟩⟩)

noncomputable def qualifierEdgeUsers (s : GlobalVariable (parameters J driver layout)) :
    Finset (BoundedCover.Node n m) := by
  classical
  exact Finset.univ.filter fun x => match x with
    | .inl _ => False
    | .inr (.inl e) => s = BoundedCover.qualifier J driver layout (J.left e)
    | .inr (.inr e) => s = BoundedCover.qualifier J driver layout (J.right e)

theorem qualifier_injective : Function.Injective (BoundedCover.qualifier J driver layout) := by
  intro v u eq
  exact Sum.inl.inj (BoundedCover.embedding_injective J driver layout (a₁ := .inl v) (a₂ := .inl u) eq)

theorem qualifierEdgeUsers_card (s : GlobalVariable (parameters J driver layout)) (D : ℕ)
    (degree : ∀ v, (BoundedCover.neighbors J v).card ≤ D) :
    (qualifierEdgeUsers J driver layout s).card ≤ D := by
  classical
  by_cases exists_v : ∃ v, s = BoundedCover.qualifier J driver layout v
  · obtain ⟨v,rfl⟩ := exists_v
    have same : qualifierEdgeUsers J driver layout (BoundedCover.qualifier J driver layout v) =
        incidentNodes J v := by
      ext x
      cases x with
      | inl u => simp [qualifierEdgeUsers, incidentNodes]
      | inr x => cases x <;> simp [qualifierEdgeUsers, incidentNodes,
          (qualifier_injective J driver layout).eq_iff, eq_comm]
    rw [same]
    exact (incidentNodes_card J v).trans (degree v)
  · have empty : qualifierEdgeUsers J driver layout s = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      cases x with
      | inl v => simp [qualifierEdgeUsers] at hx
      | inr x =>
        cases x with
        | inl e => exact exists_v ⟨J.left e, (Finset.mem_filter.mp hx).2⟩
        | inr e => exact exists_v ⟨J.right e, (Finset.mem_filter.mp hx).2⟩
    rw [empty]; simp

def auxiliaryUsers (s : GlobalVariable (parameters J driver layout)) : Finset (Fin m) :=
  Finset.univ.filter fun e => s = BoundedCover.auxiliary J driver layout e

theorem auxiliaryUsers_card (s : GlobalVariable (parameters J driver layout)) :
    (auxiliaryUsers J driver layout s).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro e he f hf
  have eq := ((Finset.mem_filter.mp he).2).symm.trans ((Finset.mem_filter.mp hf).2)
  exact Sum.inl.inj (Sum.inr.inj
    (BoundedCover.embedding_injective J driver layout (a₁ := .inr (.inl e)) (a₂ := .inr (.inl f)) eq))

noncomputable def nodeUsers (s : GlobalVariable (parameters J driver layout)) :
    Finset (BoundedCover.Node n m) := by
  classical
  exact Finset.univ.filter fun x => s ∈ (producer _ (embedding J driver layout x)).gate.inputs.map Prod.fst

theorem nodeUsers_card (s : GlobalVariable (parameters J driver layout)) (away : s ≠ targetSignal J driver layout)
    (D : ℕ) (degree : ∀ v, (BoundedCover.neighbors J v).card ≤ D) :
    (nodeUsers J driver layout s).card ≤ D+2 := by
  classical
  have contained : nodeUsers J driver layout s ⊆
      (qualifierUsers J driver layout s).image Sum.inl ∪ qualifierEdgeUsers J driver layout s ∪
      (auxiliaryUsers J driver layout s).image (fun e => Sum.inr (Sum.inr e)) := by
    intro x hx
    have member := (Finset.mem_filter.mp hx).2
    cases x with
    | inl v =>
      apply Finset.mem_union_left
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        simpa only [embedding, qualifier_data] using member⟩, rfl⟩
    | inr x =>
      cases x with
      | inl e =>
        have inputs : s = targetSignal J driver layout ∨ s = BoundedCover.qualifier J driver layout (J.left e) := by
          simpa [embedding, edgeAux_data, edgeAuxProducer, CNF.Gate.inputs, targetSignal] using member
        have eq := inputs.resolve_left away
        exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _,eq⟩))
      | inr e =>
        have inputs : s = BoundedCover.auxiliary J driver layout e ∨ s = BoundedCover.qualifier J driver layout (J.right e) := by
          simpa [embedding, edgeTerm_data, edgeTermProducer, CNF.Gate.inputs] using member
        rcases inputs with eq | eq
        · exact Finset.mem_union_right _ (Finset.mem_image.mpr
            ⟨e,Finset.mem_filter.mpr ⟨Finset.mem_univ _,eq⟩,rfl⟩)
        · exact Finset.mem_union_left _ (Finset.mem_union_right _
            (Finset.mem_filter.mpr ⟨Finset.mem_univ _,eq⟩))
  have bound := (Finset.card_le_card contained).trans (Finset.card_union_le _ _)
  have unionBound := Finset.card_union_le
    ((qualifierUsers J driver layout s).image (Sum.inl (β := Fin m ⊕ Fin m))) (qualifierEdgeUsers J driver layout s)
  have first := (Finset.card_image_le (s := qualifierUsers J driver layout s)
    (f := Sum.inl (β := Fin m ⊕ Fin m))).trans (qualifierUsers_card J driver layout s)
  have second := qualifierEdgeUsers_card J driver layout s D degree
  have third := (Finset.card_image_le (s := auxiliaryUsers J driver layout s)
    (f := fun e : Fin m => (Sum.inr (Sum.inr e) : BoundedCover.Node n m))).trans (auxiliaryUsers_card J driver layout s)
  omega

def producerNodes (s : GlobalVariable (parameters J driver layout)) : Finset (BoundedCover.Node n m) :=
  Finset.univ.filter fun x => s = BoundedCover.embedding J driver layout x

theorem producerNodes_card (s : GlobalVariable (parameters J driver layout)) :
    (producerNodes J driver layout s).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro x hx y hy
  exact BoundedCover.embedding_injective J driver layout
    (((Finset.mem_filter.mp hx).2).symm.trans ((Finset.mem_filter.mp hy).2))

theorem retained_member (s : GlobalVariable (parameters J driver layout)) (x : BoundedCover.Node n m) :
    nodeVertex J driver layout x ∈ (retainedNets J driver layout).net s ↔
      s ∈ retainedSignals J driver layout ∧
      (s = BoundedCover.embedding J driver layout x ∨
        s ∈ (producer _ (embedding J driver layout x)).gate.inputs.map Prod.fst) := by
  classical
  have vertex : nodeVertex J driver layout x ∈ retainedVertices J driver layout :=
    Finset.mem_image.mpr ⟨x,Finset.mem_univ _,rfl⟩
  change nodeVertex J driver layout x ∈
    (if s ∈ retainedSignals J driver layout then
      (fullNets J driver layout).net s ∩ retainedVertices J driver layout else ∅) ↔ _
  by_cases active : s ∈ retainedSignals J driver layout
  · simp only [active, ite_eq_left, Finset.mem_inter, vertex, and_true, true_and]
    exact (gateVertex_mem_net _ _ s).trans (by rw [output_embedding])
  · simp [active]

theorem retained_arity (D : ℕ) (degree : ∀ v, (BoundedCover.neighbors J v).card ≤ D)
    (s : GlobalVariable (parameters J driver layout)) :
    ((retainedNets J driver layout).net s).card ≤ D+3 := by
  classical
  by_cases active : s ∈ retainedSignals J driver layout
  · have away : s ≠ targetSignal J driver layout := by
      intro eq
      subst s
      have excluded : ¬ deletedSignal J driver layout (targetSignal J driver layout) :=
        (Finset.mem_filter.mp active).2
      exact excluded rfl
    have contained : (retainedNets J driver layout).net s ⊆
        ((producerNodes J driver layout s) ∪ (nodeUsers J driver layout s)).image (nodeVertex J driver layout) := by
      intro y hy
      have vertex : y ∈ retainedVertices J driver layout :=
        ((NetSystem.mem_restrict _ _ _ _ _).mp hy).2.2
      obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp vertex
      have incident := ((retained_member J driver layout s x).mp hy).2
      refine Finset.mem_image.mpr ⟨x, ?_, rfl⟩
      rcases incident with h | h
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
    have size := (Finset.card_le_card contained).trans Finset.card_image_le
    have unionBound := Finset.card_union_le (producerNodes J driver layout s) (nodeUsers J driver layout s)
    have sources := producerNodes_card J driver layout s
    have consumers := nodeUsers_card J driver layout s away D degree
    omega
  · change (if s ∈ retainedSignals J driver layout then
      (fullNets J driver layout).net s ∩ retainedVertices J driver layout else ∅).card ≤ _
    rw [ite_eq_right active]; simp

theorem target_net_deleted :
    (retainedNets J driver layout).net (targetSignal J driver layout) = ∅ := by
  classical
  have absent : targetSignal J driver layout ∉ retainedSignals J driver layout := by
    intro h
    exact (Finset.mem_filter.mp h).2 rfl
  change (if targetSignal J driver layout ∈ retainedSignals J driver layout then _ else ∅) = ∅
  rw [ite_eq_right absent]

theorem selector_net_deleted (side : Side) (bus : Fin (parameters J driver layout).buses) :
    (retainedNets J driver layout).net (.original (.internal (.flag side bus))) = ∅ := by
  classical
  have absent : GlobalVariable.original (.internal (.flag side bus)) ∉ retainedSignals J driver layout := by
    intro h
    exact (Finset.mem_filter.mp h).2 trivial
  change (if GlobalVariable.original (.internal (.flag side bus)) ∈ retainedSignals J driver layout then _ else ∅) = ∅
  rw [ite_eq_right absent]

theorem target_qualifier_net_deleted :
    (retainedNets J driver layout).net (.original (.internal (.qualifier .faulty (Fin.last n)))) = ∅ := by
  classical
  have absent : GlobalVariable.original (.internal (.qualifier .faulty (Fin.last n))) ∉
      retainedSignals J driver layout := by
    intro h
    exact (Finset.mem_filter.mp h).2 rfl
  change (if GlobalVariable.original (.internal (.qualifier .faulty (Fin.last n))) ∈
    retainedSignals J driver layout then _ else ∅) = ∅
  rw [ite_eq_right absent]

theorem qualifier_retained (v : Fin n) :
    BoundedCover.qualifier J driver layout v ∈ retainedSignals J driver layout := by
  classical
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _, by change v.val ≠ n; omega⟩

theorem auxiliary_retained (e : Fin m) :
    BoundedCover.auxiliary J driver layout e ∈ retainedSignals J driver layout := by
  classical
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _, by change ¬False; simp⟩

noncomputable def retainedNodeGraph : SimpleGraph (BoundedCover.Node n m) where
  Adj x y := (retainedNets J driver layout).twoSection.Adj (nodeVertex J driver layout x) (nodeVertex J driver layout y)
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

set_option linter.constructorNameAsVariable false in
theorem retained_core_edges (e : Fin m) :
    (retainedNodeGraph J driver layout).Adj (.inl (J.left e)) (.inr (.inl e)) ∧
    (retainedNodeGraph J driver layout).Adj (.inr (.inl e)) (.inr (.inr e)) ∧
    (retainedNodeGraph J driver layout).Adj (.inr (.inr e)) (.inl (J.right e)) := by
  have ne {x y : BoundedCover.Node n m} (h : x ≠ y) :
      nodeVertex J driver layout x ≠ nodeVertex J driver layout y :=
    fun eq => h (nodeVertex_injective J driver layout eq)
  have qual (v : Fin n) : nodeVertex J driver layout (.inl v) ∈
      (retainedNets J driver layout).net (BoundedCover.qualifier J driver layout v) :=
    (retained_member J driver layout _ _).mpr ⟨qualifier_retained J driver layout v, Or.inl rfl⟩
  have aux : nodeVertex J driver layout (.inr (.inl e)) ∈
      (retainedNets J driver layout).net (BoundedCover.auxiliary J driver layout e) :=
    (retained_member J driver layout _ _).mpr ⟨auxiliary_retained J driver layout e, Or.inl rfl⟩
  obtain ⟨first,second,third⟩ := edge_connections J driver layout e
  rw [layout_connection] at first second third
  have firstMem := (retained_member J driver layout (BoundedCover.qualifier J driver layout (J.left e))
    (.inr (.inl e))).mpr ⟨qualifier_retained J driver layout _, Or.inr first⟩
  have secondMem := (retained_member J driver layout (BoundedCover.auxiliary J driver layout e)
    (.inr (.inr e))).mpr ⟨auxiliary_retained J driver layout _, Or.inr second⟩
  have thirdMem := (retained_member J driver layout (BoundedCover.qualifier J driver layout (J.right e))
    (.inr (.inr e))).mpr ⟨qualifier_retained J driver layout _, Or.inr third⟩
  exact ⟨⟨ne (by simp), _, qual _, firstMem⟩,
    ⟨ne (by simp), _, aux, secondMem⟩, ⟨ne (by simp), _, thirdMem, qual _⟩⟩

/-- The retained two-section contains J after deleting whole shared nets. -/
noncomputable def retainedMinor : MinorModel J.graph (retainedNets J driver layout).twoSection :=
  (BoundedCover.patternMinor J (retainedNodeGraph J driver layout) (retained_core_edges J driver layout)).map
    (nodeVertex J driver layout) (nodeVertex_injective J driver layout) (by intro x y h; exact h)

/-- The retained vertices are exactly the union of the concrete gate branches. -/
theorem retainedVertices_eq : retainedVertices J driver layout =
    Finset.univ.biUnion (fun v => (branch J driver layout v).image (gateVertex _)) := by
  classical
  ext y
  constructor
  · intro hy
    obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hy
    apply Finset.mem_biUnion.mpr
    refine ⟨BoundedCover.owner J x, Finset.mem_univ _, ?_⟩
    exact Finset.mem_image.mpr ⟨embedding J driver layout x,
      Finset.mem_image.mpr ⟨x, by simp [BoundedCover.mem_branch], rfl⟩,rfl⟩
  · intro hy
    obtain ⟨v,_,hy⟩ := Finset.mem_biUnion.mp hy
    obtain ⟨g,hg,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hg
    exact Finset.mem_image.mpr ⟨x,Finset.mem_univ _,rfl⟩

/-- Every ordering of all native ports and gates has a linear net cut bound. -/
theorem net_cut_lower (c D k : ℕ) (expansion : VertexExpansion J.graph c)
    (degree : ∀ v, (BoundedCover.neighbors J v).card ≤ D)
    (order : Vertex (parameters J driver layout) ≃ Fin (Fintype.card (Vertex (parameters J driver layout))))
    (cut : (fullNets J driver layout).CutBound order k) : n ≤ 4*c*((D+3)*k+1) := by
  simpa only [Fintype.card_fin] using retained_net_cut_lower (fullNets J driver layout)
    (retainedVertices J driver layout) (retainedSignals J driver layout) (retainedMinor J driver layout)
    c (D+3) k expansion (retained_arity J driver layout D degree) order cut

theorem net_cut_size_lower (c D k : ℕ) (expansion : VertexExpansion J.graph c)
    (degree : ∀ v, (BoundedCover.neighbors J v).card ≤ D)
    (cut : (fullNets J driver layout).NetCutwidthLE k) :
    (BoundedCover.size J driver layout).total ≤ 12000*c*(D+1)*((D+3)*k+1) := by
  obtain ⟨order,cut⟩ := cut
  calc
    _ ≤ 3000*(D+1)*n := BoundedCover.size_degree_linear J driver layout D degree
    _ ≤ 3000*(D+1)*(4*c*((D+3)*k+1)) := Nat.mul_le_mul_left _ (net_cut_lower J driver layout c D k expansion degree order cut)
    _ = _ := by ring

theorem net_cut_variableLiteralSize_lower (c D k : ℕ)
    (expansion : VertexExpansion J.graph c) (degree : ∀ v, (BoundedCover.neighbors J v).card ≤ D)
    (cut : (fullNets J driver layout).NetCutwidthLE k) :
    BoundedCover.variableLiteralSize J driver layout ≤ 12000*c*(D+1)*((D+3)*k+1) :=
  (BoundedCover.variableLiteralSize_le J driver layout).trans
    (net_cut_size_lower J driver layout c D k expansion degree cut)

theorem net_cut_positive (k : ℕ) (cut : (fullNets J driver layout).NetCutwidthLE k) : 0 < k := by
  refine CircuitLayout.primary_netCutwidth_positive
    (BoundedCircuit.layout (parameters J driver layout)) k cut
    (.original (.primary (.enable driver.castSucc))) (.enable driver.castSucc)
    (qualifierGate J driver layout driver) ?_ ?_
  · rw [layout_primary_producer]
  · rw [layout_connection, qualifier_data]
    simp [qualifierProducer, CNF.Gate.inputs]

/-- An explicit homogeneous linear lower bound for full-circuit net cut-width. -/
theorem net_cut_linear_size_lower (c D k : ℕ) (expansion : VertexExpansion J.graph c)
    (degree : ∀ v, (BoundedCover.neighbors J v).card ≤ D)
    (cut : (fullNets J driver layout).NetCutwidthLE k) :
    (BoundedCover.size J driver layout).total ≤ 12000*c*(D+1)*(D+4)*k := by
  have positive := net_cut_positive J driver layout k cut
  have arithmetic : (D+3)*k+1 ≤ (D+4)*k := by nlinarith
  calc
    _ ≤ 12000*c*(D+1)*((D+3)*k+1) := net_cut_size_lower J driver layout c D k expansion degree cut
    _ ≤ 12000*c*(D+1)*((D+4)*k) := Nat.mul_le_mul_left _ arithmetic
    _ = _ := by ring

/-- Proposition 6.11 for the specified complete native layout and encoding.
The supplied expansion and degree bounds determine constants independent of
circuit size, vertex ordering, and gate partition. -/
theorem linear_width_obstruction (c D : ℕ) (expansion : VertexExpansion J.graph c)
    (degree : ∀ v, (BoundedCover.neighbors J v).card ≤ D) :
    let N := BoundedCover.variableLiteralSize J driver layout
    let C := 12000*c*(D+1)
    (∀ w, TreewidthLE (portGraph J driver layout) w → N ≤ C*(w+1)) ∧
    (∀ w, TreewidthLE (BoundedCover.primal J driver layout) w → N ≤ C*(w+1)) ∧
    (∀ w, TreewidthLE (incidenceGraph J driver layout) w → N ≤ C*(w+1)) ∧
    (∀ k, (fullNets J driver layout).NetCutwidthLE k → N ≤ C*(D+4)*k) ∧
    (∀ (Block : Type) [DecidableEq Block] (partition : Gate (parameters J driver layout) → Block)
      K w, (∀ b, ((BoundedCircuit.layout (parameters J driver layout)).blockInputs
        (CircuitLayout.gateBlock partition b)).card ≤ K) →
      TreewidthLE (blockGraph (gateGraph J driver layout) partition) w → N ≤ C*(K*(w+1))) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · exact fun w h => port_width_variableLiteralSize_lower J driver layout c D w expansion degree h
  · exact fun w h => BoundedCover.primal_width_variableLiteralSize_lower J driver layout c D w expansion degree h
  · exact fun w h => incidence_width_variableLiteralSize_lower J driver layout c D w expansion degree h
  · exact fun k h => (BoundedCover.variableLiteralSize_le J driver layout).trans
      (net_cut_linear_size_lower J driver layout c D k expansion degree h)
  · exact fun _ _ partition K w inputs width => block_width_variableLiteralSize_lower
      J driver layout partition c D K w expansion degree inputs width

end Controller.Graph.CoverCircuit
