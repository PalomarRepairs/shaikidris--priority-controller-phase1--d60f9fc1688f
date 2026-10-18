module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Decoder.Eval
public import Controller.Basic.Admissible
public import Controller.Physical.DetectionBridge
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section

/-!
# Vertex-cover decoder

A finite simple graph is supplied by an injective enumeration of its unordered
edges. The extra final channel is the target. Every edge term shares one
target input and has two negative vertex guards.
-/

namespace Controller.Reductions

open Decoder

/-- Each unordered edge is listed once, with its endpoints in increasing order.
The declared vertex universe includes isolated vertices. -/
structure EnumeratedGraph (n m : ℕ) where
  left : Fin m → Fin n
  right : Fin m → Fin n
  ordered : ∀ e, (left e).val < (right e).val
  unique : Function.Injective (fun e => (left e, right e))

namespace EnumeratedGraph

variable {n m : ℕ} (J : EnumeratedGraph n m)

def Adj (u v : Fin n) : Prop :=
  ∃ e, (J.left e = u ∧ J.right e = v) ∨ (J.left e = v ∧ J.right e = u)

/-- The enumerated relation is an ordinary finite simple graph. -/
def graph : SimpleGraph (Fin n) where
  Adj := J.Adj
  symm := by
    constructor
    rintro u v ⟨e, h | h⟩
    · exact ⟨e, Or.inr h⟩
    · exact ⟨e, Or.inl h⟩
  loopless := by
    constructor
    rintro u ⟨e, h | h⟩ <;> have ho := J.ordered e <;> rw [h.1, h.2] at ho <;> omega

def IsCover (C : Finset (Fin n)) : Prop :=
  ∀ e, J.left e ∈ C ∨ J.right e ∈ C

theorem cover_iff_graph (C : Finset (Fin n)) :
    J.IsCover C ↔ ∀ u v, J.graph.Adj u v → u ∈ C ∨ v ∈ C := by
  constructor
  · intro cover u v adjacent
    obtain ⟨e, h | h⟩ := adjacent
    · simpa [h.1, h.2] using cover e
    · simpa [h.1, h.2, or_comm] using cover e
  · intro cover e
    exact cover _ _ ⟨e, Or.inl ⟨rfl, rfl⟩⟩

end EnumeratedGraph

variable {n m : ℕ}

/-- Increasing endpoints provide one representative of each undirected edge. -/
def SortedEdges (G : SimpleGraph (Fin n)) :=
  {pair : Fin n × Fin n // pair.1.val < pair.2.val ∧ G.Adj pair.1 pair.2}

noncomputable instance sortedEdgesFintype (G : SimpleGraph (Fin n)) :
    Fintype (SortedEdges G) := by
  unfold SortedEdges
  exact Fintype.ofFinite _

def EnumeratedGraph.sortedEdge (J : EnumeratedGraph n m) (e : Fin m) :
    SortedEdges J.graph :=
  ⟨(J.left e, J.right e), J.ordered e, ⟨e, Or.inl ⟨rfl, rfl⟩⟩⟩

theorem EnumeratedGraph.sortedEdge_bijective (J : EnumeratedGraph n m) :
    Function.Bijective J.sortedEdge := by
  constructor
  · intro e f equal
    exact J.unique (congrArg Subtype.val equal)
  · intro edge
    obtain ⟨e, same | swapped⟩ := edge.property.2
    · refine ⟨e, ?_⟩
      apply Subtype.ext
      exact Prod.ext same.1 same.2
    · have oriented := edge.property.1
      have listed := J.ordered e
      have left := congrArg Fin.val swapped.1
      have right := congrArg Fin.val swapped.2
      omega

/-- The stored edge count equals the graph's increasing-endpoint edge count. -/
theorem EnumeratedGraph.sortedEdges_card (J : EnumeratedGraph n m) :
    Fintype.card (SortedEdges J.graph) = m := by
  simpa using (Fintype.card_congr (Equiv.ofBijective J.sortedEdge J.sortedEdge_bijective)).symm

noncomputable def ofSimpleGraph (G : SimpleGraph (Fin n)) :
    EnumeratedGraph n (Fintype.card (SortedEdges G)) :=
  let enumeration := (Fintype.equivFin (SortedEdges G)).symm
  { left := fun e => (enumeration e).val.1
    right := fun e => (enumeration e).val.2
    ordered := fun e => (enumeration e).property.1
    unique := by
      intro e f equal
      apply enumeration.injective
      apply Subtype.ext
      exact equal }

/-- The enumeration adapter represents every finite simple graph exactly. -/
theorem ofSimpleGraph_graph (G : SimpleGraph (Fin n)) : (ofSimpleGraph G).graph = G := by
  let enumeration := (Fintype.equivFin (SortedEdges G)).symm
  apply SimpleGraph.ext
  funext u v
  apply propext
  change (∃ e, ((enumeration e).val.1 = u ∧ (enumeration e).val.2 = v) ∨
      ((enumeration e).val.1 = v ∧ (enumeration e).val.2 = u)) ↔ G.Adj u v
  constructor
  · rintro ⟨e, h | h⟩
    · simpa [h.1, h.2] using (enumeration e).property.2
    · simpa [h.1, h.2] using (enumeration e).property.2.symm
  · intro adjacent
    have different : u.val ≠ v.val := by
      intro equal
      exact adjacent.ne (Fin.ext equal)
    obtain less | greater := lt_or_gt_of_ne different
    · let edge : SortedEdges G := ⟨(u, v), less, adjacent⟩
      refine ⟨enumeration.symm edge, Or.inl ?_⟩
      rw [enumeration.apply_symm_apply]
      exact ⟨rfl, rfl⟩
    · let edge : SortedEdges G := ⟨(v, u), greater, adjacent.symm⟩
      refine ⟨enumeration.symm edge, Or.inr ?_⟩
      rw [enumeration.apply_symm_apply]
      exact ⟨rfl, rfl⟩

def coverTarget (n : ℕ) : Channel (n + 1) := Fin.last n

def coverVertices (K : Finset (Channel (n + 1))) : Finset (Fin n) :=
  Finset.univ.filter fun v => v.castSucc ∈ K

def coverSet (C : Finset (Fin n)) : Finset (Channel (n + 1)) :=
  insert (coverTarget n) (C.image Fin.castSucc)

@[simp] theorem coverVertices_mem (K : Finset (Channel (n + 1))) (v : Fin n) :
    v ∈ coverVertices K ↔ v.castSucc ∈ K := by simp [coverVertices]

@[simp] theorem coverSet_vertex (C : Finset (Fin n)) (v : Fin n) :
    v.castSucc ∈ coverSet C ↔ v ∈ C := by
  have different : v.castSucc ≠ coverTarget n := by
    intro equal
    have values := congrArg Fin.val equal
    change v.val = n at values
    omega
  simp [coverSet, different, (Fin.castSucc_injective n).eq_iff]

@[simp] theorem coverSet_target (C : Finset (Fin n)) :
    coverTarget n ∈ coverSet C := by simp [coverSet]

@[simp] theorem coverVertices_coverSet (C : Finset (Fin n)) :
    coverVertices (coverSet C) = C := by ext v; simp

theorem coverSet_coverVertices (K : Finset (Channel (n + 1)))
    (target : coverTarget n ∈ K) : coverSet (coverVertices K) = K := by
  ext i
  refine Fin.lastCases ?_ (fun v => ?_) i
  · change coverTarget n ∈ coverSet (coverVertices K) ↔ coverTarget n ∈ K
    simp [target]
  · change v.castSucc ∈ coverSet (coverVertices K) ↔ v.castSucc ∈ K
    rw [coverSet_vertex, coverVertices_mem]

theorem coverSet_card (C : Finset (Fin n)) : (coverSet C).card = 1 + C.card := by
  have absent : coverTarget n ∉ C.image Fin.castSucc := by
    rintro membership
    obtain ⟨v, _, equal⟩ := Finset.mem_image.mp membership
    have values := congrArg Fin.val equal
    change v.val = n at values
    omega
  rw [coverSet, Finset.card_insert_of_notMem absent,
    Finset.card_image_of_injective _ (Fin.castSucc_injective n)]
  omega

/-- Literal source formula on eligible sets. -/
def coverValue (J : EnumeratedGraph n m) (K : Finset (Channel (n + 1))) : Bool :=
  (List.ofFn fun e : Fin m => decide (coverTarget n ∈ K) &&
    !(decide ((J.left e).castSucc ∈ K) || decide ((J.right e).castSucc ∈ K))).any id

theorem coverValue_zero_iff (J : EnumeratedGraph n m)
    (K : Finset (Channel (n + 1))) (target : coverTarget n ∈ K) :
    coverValue J K = false ↔ J.IsCover (coverVertices K) := by
  simp only [coverValue, List.any_eq_false, List.mem_ofFn]
  constructor
  · intro zero e
    by_cases left : (J.left e).castSucc ∈ K
    · exact Or.inl (coverVertices_mem K _ |>.mpr left)
    · have right : (J.right e).castSucc ∈ K := by
        simpa [target, left] using zero _ ⟨e, rfl⟩
      exact Or.inr (coverVertices_mem K _ |>.mpr right)
  · intro cover value witness
    obtain ⟨e, rfl⟩ := witness
    obtain left | right := cover e
    · simp [target, (coverVertices_mem K _).mp left]
    · simp [target, (coverVertices_mem K _).mp right]

theorem coverValue_healthy (J : EnumeratedGraph n m) (edge : Fin m) :
    coverValue J {coverTarget n} = true := by
  apply List.any_eq_true.mpr
  refine ⟨_, List.mem_ofFn.mpr ⟨edge, rfl⟩, ?_⟩
  have left : (J.left edge).castSucc ≠ coverTarget n := by
    intro equal
    have values := congrArg Fin.val equal
    change (J.left edge).val = n at values
    omega
  have right : (J.right edge).castSucc ≠ coverTarget n := by
    intro equal
    have values := congrArg Fin.val equal
    change (J.right edge).val = n at values
    omega
  simp [left, right]

/-- Exact detectable eligible sets, under the source's nonempty-edge hypothesis. -/
theorem cover_detects_iff (J : EnumeratedGraph n m) (edge : Fin m)
    (K : Finset (Channel (n + 1))) (legal : Admissible 1 (coverTarget n) K) :
    coverValue J K ≠ coverValue J {coverTarget n} ↔
      ∃ C, J.IsCover C ∧ K = coverSet C := by
  have target := (admissible_one _ _).mp legal
  rw [coverValue_healthy J edge]
  have zero : coverValue J K ≠ true ↔ coverValue J K = false := by
    cases coverValue J K <;> simp
  rw [zero, coverValue_zero_iff J K target]
  constructor
  · intro cover
    exact ⟨coverVertices K, cover, (coverSet_coverVertices K target).symm⟩
  · rintro ⟨C, cover, rfl⟩
    simpa using cover

/-- One target input, one two-guard node per edge, and one final OR. -/
def coverDAG (J : EnumeratedGraph n m) : DAG (n + 1) where
  nodeCount := m + 2
  node := fun index =>
    if first : index.val = 0 then .input (coverTarget n)
    else if term : index.val < m + 1 then
      let e : Fin m := ⟨index.val - 1, by omega⟩
      .guard ⟨0, by omega⟩ [(J.left e).castSucc, (J.right e).castSucc]
    else .disj (List.ofFn fun e : Fin m => ⟨e.val + 1, by omega⟩)
  roots := [⟨m + 1, by omega⟩]

theorem coverDAG_guarded (J : EnumeratedGraph n m) : (coverDAG J).Guarded := by
  intro index
  simp only [coverDAG]
  split
  · rfl
  · split <;> rfl

@[simp] theorem coverDAG_nodes (J : EnumeratedGraph n m) :
    (coverDAG J).nodeCount = m + 2 := rfl

private theorem coverDAG_input (J : EnumeratedGraph n m)
    (K : Finset (Channel (n + 1))) :
    (coverDAG J).eval (assignmentOfSet K) ⟨0, by change 0 < m + 2; omega⟩ =
      decide (coverTarget n ∈ K) := by
  rw [DAG.eval_eq]
  simp [coverDAG, Gate.eval, assignmentOfSet]

private theorem coverDAG_term (J : EnumeratedGraph n m)
    (K : Finset (Channel (n + 1))) (e : Fin m) :
    (coverDAG J).eval (assignmentOfSet K)
      ⟨e.val + 1, by change e.val + 1 < m + 2; omega⟩ =
      (decide (coverTarget n ∈ K) &&
        !(decide ((J.left e).castSucc ∈ K) ||
          decide ((J.right e).castSucc ∈ K))) := by
  rw [DAG.eval_eq]
  have first : e.val + 1 ≠ 0 := by omega
  have term : e.val + 1 < m + 1 := by omega
  simp only [coverDAG, first, dite_false, term, dite_true, Nat.add_sub_cancel,
    Gate.eval, List.any_cons, List.any_nil, Bool.or_false]
  change ((coverDAG J).eval (assignmentOfSet K) ⟨0, by change 0 < m + 2; omega⟩ &&
      !(assignmentOfSet K (J.left e).castSucc ||
        assignmentOfSet K (J.right e).castSucc)) = _
  rw [coverDAG_input]
  rfl

theorem coverDAG_eval (J : EnumeratedGraph n m)
    (K : Finset (Channel (n + 1))) :
    (coverDAG J).eval (assignmentOfSet K)
      ⟨m + 1, by change m + 1 < m + 2; omega⟩ = coverValue J K := by
  rw [DAG.eval_eq]
  have first : m + 1 ≠ 0 := by omega
  simp only [coverDAG, first, dite_false, lt_self_iff_false, Gate.eval]
  apply Bool.eq_iff_iff.mpr
  simp only [coverValue, List.any_eq_true, List.mem_ofFn]
  constructor
  · rintro ⟨value, ⟨e, rfl⟩, h⟩
    exact ⟨_, ⟨e, rfl⟩, (coverDAG_term J K e).symm ▸ h⟩
  · rintro ⟨value, ⟨e, rfl⟩, h⟩
    exact ⟨_, ⟨e, rfl⟩, (coverDAG_term J K e) ▸ h⟩

/-- The size counts all declared vertices, stored gates and incidences. -/
theorem coverDAG_countedSize_le (J : EnumeratedGraph n m) :
    (coverDAG J).countedSize ≤ n + 5 * m + 9 := by
  have children : (coverDAG J).childIncidences ≤ 2 * m + 1 := by
    unfold DAG.childIncidences
    rw [Fin.sum_ofFn]
    change (∑ index : Fin (m + 1 + 1), ((coverDAG J).node index).children.length) ≤ _
    rw [Fin.sum_univ_castSucc]
    have earlierBound : (∑ index : Fin (m + 1),
        ((coverDAG J).node index.castSucc).children.length) ≤ m + 1 := by
      calc
        _ ≤ ∑ _index : Fin (m + 1), 1 := by
          apply Finset.sum_le_sum
          intro index _
          simp only [coverDAG, Fin.val_castSucc]
          split
          · simp [Gate.children]
          · rw [dite_eq_left index.isLt]
            simp [Gate.children]
        _ = _ := by simp [Finset.card_univ]
    have last : ((coverDAG J).node (Fin.last (m + 1))).children.length = m := by
      simp [coverDAG, Gate.children]
    omega
  have guards : (coverDAG J).guardIncidences ≤ 2 * (m + 2) := by
    unfold DAG.guardIncidences
    rw [Fin.sum_ofFn]
    calc
      _ ≤ ∑ _index : Fin (coverDAG J).nodeCount, 2 := by
        apply Finset.sum_le_sum
        intro index _
        simp only [coverDAG]
        split
        · simp [Gate.guardLabels]
        · split <;> simp [Gate.guardLabels]
      _ = _ := by
        rw [Fin.sum_const]
        simp only [nsmul_eq_mul, Nat.cast_id]
        change (m + 2) * 2 = 2 * (m + 2)
        omega
  rw [DAG.countedSize_eq]
  have nodes := coverDAG_nodes J
  have roots : (coverDAG J).roots.length = 1 := rfl
  omega

theorem coverDAG_size_linear (J : EnumeratedGraph n m) (edge : Fin m) :
    (coverDAG J).countedSize ≤ 14 * (n + m) := by
  have bound := coverDAG_countedSize_le J
  have positive := edge.isLt
  omega

abbrev Covers (J : EnumeratedGraph n m) := {C : Finset (Fin n) // J.IsCover C}

abbrev CoverDetections (J : EnumeratedGraph n m) :=
  {K : Finset (Channel (n + 1)) // Admissible 1 (coverTarget n) K ∧
    coverValue J K ≠ coverValue J {coverTarget n}}

noncomputable instance coversFintype (J : EnumeratedGraph n m) : Fintype (Covers J) :=
  Fintype.ofFinite _

noncomputable instance coverDetectionsFintype (J : EnumeratedGraph n m) :
    Fintype (CoverDetections J) := Fintype.ofFinite _

/-- A bijection of sets, with no identification of different primary inputs. -/
noncomputable def coverDetectionEquiv (J : EnumeratedGraph n m) (edge : Fin m) :
    Covers J ≃ CoverDetections J where
  toFun C := ⟨coverSet C.val, by
    have legal : Admissible 1 (coverTarget n) (coverSet C.val) := by simp
    exact ⟨legal, (cover_detects_iff J edge _ legal).mpr ⟨C.val, C.property, rfl⟩⟩⟩
  invFun K := ⟨coverVertices K.val, by
    obtain ⟨C, cover, equation⟩ := (cover_detects_iff J edge _ K.property.1).mp K.property.2
    simpa [equation] using cover⟩
  left_inv C := by apply Subtype.ext; simp
  right_inv K := by
    apply Subtype.ext
    exact coverSet_coverVertices K.val ((admissible_one _ _).mp K.property.1)

theorem cover_detection_count (J : EnumeratedGraph n m) (edge : Fin m) :
    Fintype.card (CoverDetections J) = Fintype.card (Covers J) :=
  (Fintype.card_congr (coverDetectionEquiv J edge)).symm

theorem cover_threshold_iff (J : EnumeratedGraph n m) (edge : Fin m) (k : ℕ) :
    (∃ K : CoverDetections J, K.val.card ≤ k + 1) ↔
      ∃ C : Covers J, C.val.card ≤ k := by
  constructor
  · rintro ⟨K, small⟩
    let C := (coverDetectionEquiv J edge).symm K
    refine ⟨C, ?_⟩
    have same := congrArg (fun L : CoverDetections J => L.val.card)
      ((coverDetectionEquiv J edge).apply_symm_apply K)
    change (coverSet C.val).card = K.val.card at same
    rw [coverSet_card] at same
    omega
  · rintro ⟨C, small⟩
    refine ⟨coverDetectionEquiv J edge C, ?_⟩
    change (coverSet C.val).card ≤ k + 1
    rw [coverSet_card]
    omega

/-- Any declared vertex may be the one bridge driver. -/
def coverBridge (driver : Fin n) : Physical.Bridge (n + 1) where
  target := coverTarget n
  drivers := {driver.castSucc}
  drivers_nonempty := by simp
  target_not_mem := by
    simp only [Finset.mem_singleton]
    intro equal
    have values := congrArg Fin.val equal
    change n = driver.val at values
    omega

/-- The one-bus realizer requests only the target, even when the driver is
eligible. Driver eligibility is determined by enable, not by its request. -/
theorem cover_realizer_driver_request_zero (driver : Fin n)
    (K : Finset (Channel (n + 1))) (bus : Fin 1) :
    (Physical.realizeBridge (coverBridge driver) (by decide : 0 < 1) K).request
      bus driver.castSucc = false := by
  have different : driver.castSucc ≠ coverTarget n := by
    intro equal
    have values := congrArg Fin.val equal
    change driver.val = n at values
    omega
  have zero : bus = 0 := Subsingleton.elim _ _
  subst bus
  simp [Physical.realizeBridge, Physical.realizeRequests, coverBridge,
    assignmentOfSet, different]

def coverObservation (J : EnumeratedGraph n m) :
    Fin 1 → Assignment (n + 1) → Bool := fun _ a => coverValue J (setOfAssignment a)

theorem coverObservation_eq_dag (J : EnumeratedGraph n m) (a : Assignment (n + 1)) :
    coverObservation J 0 a = (coverDAG J).eval a
      ⟨m + 1, by change m + 1 < m + 2; omega⟩ := by
  simpa only [coverObservation, assignmentOfSet_setOfAssignment] using
    (coverDAG_eval J (setOfAssignment a)).symm

theorem cover_physical_detects_only_covers (J : EnumeratedGraph n m) (edge : Fin m)
    (driver : Fin n) (input : Physical.PrimaryInput (n + 1) 1) (wire : Bool)
    (detects : Physical.BridgeInputDetects (coverBridge driver) true
      (coverObservation J) input wire) :
    ∃ C, J.IsCover C ∧
      setOfAssignment (Physical.bridgeQualifiers (coverBridge driver) input wire) = coverSet C := by
  have changed : Physical.stageFlag input.enable (input.request input.firstBus) ≠
      Physical.bridgeFirstFlag (coverBridge driver) input wire := by
    intro equal
    exact Physical.no_observation_change_of_firstFlag_eq (coverBridge driver) input wire
      (coverObservation J) equal detects.2
  have image := Physical.separated_drive_one_image (coverBridge driver) input detects.1 changed
  obtain ⟨index, inequality⟩ := detects.2
  rw [image.1] at inequality
  simp only [coverObservation, setOfAssignment_assignmentOfSet] at inequality
  exact (cover_detects_iff J edge _ image.2).mp inequality.symm

/-- Every cover has the canonical physical witness, including covers omitting
the driver. Eligibility imposes no positive driver-request restriction. -/
theorem cover_realizer_detects_iff (J : EnumeratedGraph n m) (edge : Fin m)
    (driver : Fin n) (K : Finset (Channel (n + 1)))
    (legal : Admissible 1 (coverTarget n) K) :
    Physical.BridgeInputDetects (coverBridge driver) true (coverObservation J)
      (Physical.realizeBridge (coverBridge driver) (by decide : 0 < 1) K) true ↔
      ∃ C, J.IsCover C ∧ K = coverSet C := by
  rw [Physical.realizeBridge_detects_iff (coverBridge driver) (by decide : 0 < 1) K legal]
  simp only [Physical.ObservationsDiffer, coverObservation,
    setOfAssignment_assignmentOfSet]
  change (∃ _i : Fin 1, coverValue J {coverTarget n} ≠ coverValue J K) ↔ _
  have reverse : (∃ _i : Fin 1, coverValue J {coverTarget n} ≠ coverValue J K) ↔
      coverValue J K ≠ coverValue J {coverTarget n} :=
    ⟨fun ⟨_, h⟩ => h.symm, fun h => ⟨0, h.symm⟩⟩
  rw [reverse]
  exact cover_detects_iff J edge K legal

end Controller.Reductions
