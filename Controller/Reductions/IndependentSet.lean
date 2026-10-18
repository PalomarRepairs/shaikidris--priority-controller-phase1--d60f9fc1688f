module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Reductions.GraphCover

@[expose] public section

/-!
# Independent-set decoder

The target and the positive marker are distinct from every graph vertex.
Each edge adds two guarded references to the stored predecessor and an OR.
The edge order changes the represented chain, but its output is the same
independent-set predicate on all assignments.
-/

namespace Controller.Reductions

open Decoder

variable {n m : ℕ}

def independentTarget (n : ℕ) : Channel (n + 2) := Fin.last (n + 1)

def independentMarker (n : ℕ) : Channel (n + 2) := (Fin.last n).castSucc

def independentVertex (v : Fin n) : Channel (n + 2) := v.castSucc.castSucc

theorem independentVertex_injective : Function.Injective (independentVertex (n := n)) := by
  intro u v equal
  apply Fin.ext
  simpa only [independentVertex, Fin.val_castSucc] using
    congrArg (fun i : Channel (n + 2) => i.val) equal

@[simp] theorem independentVertex_ne_target (v : Fin n) :
    independentVertex v ≠ independentTarget n := by
  intro equal
  have values := congrArg Fin.val equal
  change v.val = n + 1 at values
  omega

@[simp] theorem independentVertex_ne_marker (v : Fin n) :
    independentVertex v ≠ independentMarker n := by
  intro equal
  have values := congrArg Fin.val equal
  change v.val = n at values
  omega

@[simp] theorem independentMarker_ne_target : independentMarker n ≠ independentTarget n := by
  intro equal
  have values := congrArg Fin.val equal
  change n = n + 1 at values
  omega

def independentVertices (K : Finset (Channel (n + 2))) : Finset (Fin n) :=
  Finset.univ.filter fun v => independentVertex v ∈ K

def independentSet (I : Finset (Fin n)) : Finset (Channel (n + 2)) :=
  insert (independentTarget n) (insert (independentMarker n) (I.image independentVertex))

def EnumeratedGraph.IsIndependent (J : EnumeratedGraph n m) (I : Finset (Fin n)) : Prop :=
  ∀ e, J.left e ∉ I ∨ J.right e ∉ I

theorem independent_iff_complement_cover (J : EnumeratedGraph n m) (I : Finset (Fin n)) :
    J.IsIndependent I ↔ J.IsCover (Finset.univ \ I) := by
  simp [EnumeratedGraph.IsIndependent, EnumeratedGraph.IsCover]

theorem independent_iff_graph (J : EnumeratedGraph n m) (I : Finset (Fin n)) :
    J.IsIndependent I ↔ ∀ u v, J.graph.Adj u v → u ∉ I ∨ v ∉ I := by
  rw [independent_iff_complement_cover, EnumeratedGraph.cover_iff_graph]
  simp

@[simp] theorem independentVertices_mem (K : Finset (Channel (n + 2))) (v : Fin n) :
    v ∈ independentVertices K ↔ independentVertex v ∈ K := by
  simp [independentVertices]

@[simp] theorem independentSet_vertex (I : Finset (Fin n)) (v : Fin n) :
    independentVertex v ∈ independentSet I ↔ v ∈ I := by
  simp [independentSet, independentVertex_injective.eq_iff]

@[simp] theorem independentSet_target (I : Finset (Fin n)) :
    independentTarget n ∈ independentSet I := by simp [independentSet]

@[simp] theorem independentSet_marker (I : Finset (Fin n)) :
    independentMarker n ∈ independentSet I := by simp [independentSet]

@[simp] theorem independentVertices_independentSet (I : Finset (Fin n)) :
    independentVertices (independentSet I) = I := by ext v; simp

theorem independentSet_independentVertices (K : Finset (Channel (n + 2)))
    (target : independentTarget n ∈ K) (marker : independentMarker n ∈ K) :
    independentSet (independentVertices K) = K := by
  ext i
  refine Fin.lastCases ?_ (fun earlier => ?_) i
  · change independentTarget n ∈ independentSet (independentVertices K) ↔ independentTarget n ∈ K
    simp [target]
  · refine Fin.lastCases ?_ (fun v => ?_) earlier
    · change independentMarker n ∈ independentSet (independentVertices K) ↔ independentMarker n ∈ K
      simp [marker]
    · change independentVertex v ∈ independentSet (independentVertices K) ↔ independentVertex v ∈ K
      rw [independentSet_vertex, independentVertices_mem]

theorem independentSet_card (I : Finset (Fin n)) :
    (independentSet I).card = 2 + I.card := by
  have markerAbsent : independentMarker n ∉ I.image independentVertex := by
    rintro h
    obtain ⟨v, _, equal⟩ := Finset.mem_image.mp h
    exact independentVertex_ne_marker v equal
  have targetAbsent : independentTarget n ∉
      insert (independentMarker n) (I.image independentVertex) := by
    simp only [Finset.mem_insert, Finset.mem_image, not_or]
    refine ⟨Ne.symm independentMarker_ne_target, ?_⟩
    rintro ⟨v, _, equal⟩
    exact independentVertex_ne_target v equal
  rw [independentSet, Finset.card_insert_of_notMem targetAbsent,
    Finset.card_insert_of_notMem markerAbsent,
    Finset.card_image_of_injective _ independentVertex_injective]
  omega

/-- The source's recurrence, using exactly the first `k` edge incidences. -/
def independentPrefix (J : EnumeratedGraph n m) (K : Finset (Channel (n + 2))) :
    (k : ℕ) → k ≤ m → Bool
  | 0, _ => decide (independentMarker n ∈ K)
  | k + 1, bound =>
      let e : Fin m := ⟨k, by omega⟩
      let predecessor := independentPrefix J K k (by omega)
      (predecessor && !decide (independentVertex (J.left e) ∈ K)) ||
        (predecessor && !decide (independentVertex (J.right e) ∈ K))

private theorem diamond_true_iff (p a b : Bool) :
    ((p && !a) || (p && !b)) = true ↔ p = true ∧ (a = false ∨ b = false) := by
  cases p <;> cases a <;> cases b <;> decide

theorem independentPrefix_true_iff (J : EnumeratedGraph n m)
    (K : Finset (Channel (n + 2))) (k : ℕ) (bound : k ≤ m) :
    independentPrefix J K k bound = true ↔
      independentMarker n ∈ K ∧
        ∀ e : Fin m, e.val < k →
          independentVertex (J.left e) ∉ K ∨ independentVertex (J.right e) ∉ K := by
  induction k with
  | zero => simp [independentPrefix]
  | succ k ih =>
      rw [independentPrefix, diamond_true_iff, ih]
      simp only [decide_eq_false_iff_not]
      constructor
      · rintro ⟨⟨marker, earlier⟩, current⟩
        refine ⟨marker, fun e he => ?_⟩
        by_cases old : e.val < k
        · exact earlier e old
        · have equal : e = ⟨k, by omega⟩ := by
            apply Fin.ext
            change e.val = k
            omega
          simpa [equal] using current
      · rintro ⟨marker, edges⟩
        exact ⟨⟨marker, fun e he => edges e (by omega)⟩,
          edges ⟨k, by omega⟩ (by simp)⟩

def independentValue (J : EnumeratedGraph n m) (K : Finset (Channel (n + 2))) : Bool :=
  independentPrefix J K m (Nat.le_refl m)

theorem independentValue_true_iff (J : EnumeratedGraph n m)
    (K : Finset (Channel (n + 2))) :
    independentValue J K = true ↔
      independentMarker n ∈ K ∧ J.IsIndependent (independentVertices K) := by
  rw [independentValue, independentPrefix_true_iff]
  simp [EnumeratedGraph.IsIndependent]

@[simp] theorem independentValue_healthy (J : EnumeratedGraph n m) :
    independentValue J {independentTarget n} = false := by
  have notTrue : independentValue J {independentTarget n} ≠ true := by
    intro equal
    have marker := (independentValue_true_iff J {independentTarget n}).mp equal
    simpa using marker.1
  cases h : independentValue J {independentTarget n} <;> simp_all

/-- The exact source bijection includes isolated vertices and the empty graph. -/
theorem independent_detects_iff (J : EnumeratedGraph n m)
    (K : Finset (Channel (n + 2))) (legal : Admissible 1 (independentTarget n) K) :
    independentValue J K ≠ independentValue J {independentTarget n} ↔
      ∃ I, J.IsIndependent I ∧ K = independentSet I := by
  have target := (admissible_one _ _).mp legal
  rw [independentValue_healthy]
  have nonzero : independentValue J K ≠ false ↔ independentValue J K = true := by
    cases independentValue J K <;> simp
  rw [nonzero, independentValue_true_iff]
  constructor
  · rintro ⟨marker, independent⟩
    exact ⟨independentVertices K, independent,
      (independentSet_independentVertices K target marker).symm⟩
  · rintro ⟨I, independent, rfl⟩
    simpa using And.intro (independentSet_marker I) independent

/-- The predecessor at `3*e` is stored once and referenced by both guards.
The only positive input is the marker; no live AND is introduced. -/
def independentDAG (J : EnumeratedGraph n m) : DAG (n + 2) where
  nodeCount := 3 * m + 1
  node := fun index =>
    if first : index.val = 0 then .input (independentMarker n)
    else
      let e : Fin m := ⟨(index.val - 1) / 3, by omega⟩
      if left : (index.val - 1) % 3 = 0 then
        .guard ⟨3 * e.val, by dsimp [e]; omega⟩ [independentVertex (J.left e)]
      else if right : (index.val - 1) % 3 = 1 then
        .guard ⟨3 * e.val, by dsimp [e]; omega⟩ [independentVertex (J.right e)]
      else .disj [⟨3 * e.val + 1, by dsimp [e]; omega⟩,
        ⟨3 * e.val + 2, by dsimp [e]; omega⟩]
  roots := [⟨3 * m, by omega⟩]

theorem independentDAG_guarded (J : EnumeratedGraph n m) :
    (independentDAG J).Guarded := by
  intro index
  simp only [independentDAG]
  split
  · rfl
  · split
    · rfl
    · split <;> rfl

/-- There is exactly one distinct positive head, even when vertices are isolated. -/
theorem independentDAG_positive_head_iff (J : EnumeratedGraph n m)
    (channel : Channel (n + 2)) :
    (∃ index, (independentDAG J).node index = .input channel) ↔
      channel = independentMarker n := by
  constructor
  · rintro ⟨index, equation⟩
    simp only [independentDAG] at equation
    split at equation
    · cases equation
      rfl
    · split at equation
      · cases equation
      · split at equation <;> cases equation
  · intro equal
    subst channel
    refine ⟨⟨0, by change 0 < 3 * m + 1; omega⟩, ?_⟩
    simp [independentDAG]

@[simp] theorem independentDAG_nodes (J : EnumeratedGraph n m) :
    (independentDAG J).nodeCount = 3 * m + 1 := rfl

private theorem independentDAG_left (J : EnumeratedGraph n m)
    (K : Finset (Channel (n + 2))) (e : Fin m) :
    (independentDAG J).eval (assignmentOfSet K)
      ⟨3 * e.val + 1, by change 3 * e.val + 1 < 3 * m + 1; omega⟩ =
      ((independentDAG J).eval (assignmentOfSet K)
        ⟨3 * e.val, by change 3 * e.val < 3 * m + 1; omega⟩ &&
      !decide (independentVertex (J.left e) ∈ K)) := by
  rw [DAG.eval_eq]
  have quotient : (3 * e.val) / 3 = e.val := by omega
  have remainder : (3 * e.val) % 3 = 0 := by omega
  simp [independentDAG, quotient, remainder,
    Gate.eval, assignmentOfSet]
  rfl

private theorem independentDAG_right (J : EnumeratedGraph n m)
    (K : Finset (Channel (n + 2))) (e : Fin m) :
    (independentDAG J).eval (assignmentOfSet K)
      ⟨3 * e.val + 2, by change 3 * e.val + 2 < 3 * m + 1; omega⟩ =
      ((independentDAG J).eval (assignmentOfSet K)
        ⟨3 * e.val, by change 3 * e.val < 3 * m + 1; omega⟩ &&
      !decide (independentVertex (J.right e) ∈ K)) := by
  rw [DAG.eval_eq]
  have subtract : 3 * e.val + 2 - 1 = 3 * e.val + 1 := by omega
  have quotient : (3 * e.val + 1) / 3 = e.val := by omega
  have remainder : (3 * e.val + 1) % 3 = 1 := by omega
  simp [independentDAG, subtract, quotient, remainder,
    Gate.eval, assignmentOfSet]
  rfl

private theorem independentDAG_diamond (J : EnumeratedGraph n m)
    (K : Finset (Channel (n + 2))) (e : Fin m) :
    (independentDAG J).eval (assignmentOfSet K)
      ⟨3 * (e.val + 1), by change 3 * (e.val + 1) < 3 * m + 1; omega⟩ =
      (((independentDAG J).eval (assignmentOfSet K)
        ⟨3 * e.val, by change 3 * e.val < 3 * m + 1; omega⟩ &&
          !decide (independentVertex (J.left e) ∈ K)) ||
      ((independentDAG J).eval (assignmentOfSet K)
        ⟨3 * e.val, by change 3 * e.val < 3 * m + 1; omega⟩ &&
          !decide (independentVertex (J.right e) ∈ K))) := by
  rw [DAG.eval_eq]
  have first : 3 * (e.val + 1) ≠ 0 := by omega
  have subtract : 3 * (e.val + 1) - 1 = 3 * e.val + 2 := by omega
  have quotient : (3 * e.val + 2) / 3 = e.val := by omega
  have remainder : (3 * e.val + 2) % 3 = 2 := by omega
  have notLeft : ¬ (2 : ℕ) = 0 := by decide
  have notRight : ¬ (2 : ℕ) = 1 := by decide
  simp only [independentDAG, first, dite_false, subtract, quotient, remainder,
    notLeft, notRight, Gate.eval, List.any_cons, List.any_nil,
    Bool.or_false]
  change ((independentDAG J).eval (assignmentOfSet K)
      ⟨3 * e.val + 1, by change 3 * e.val + 1 < 3 * m + 1; omega⟩ ||
    (independentDAG J).eval (assignmentOfSet K)
      ⟨3 * e.val + 2, by change 3 * e.val + 2 < 3 * m + 1; omega⟩) = _
  rw [independentDAG_left, independentDAG_right]
  rfl

theorem independentDAG_prefix_eval (J : EnumeratedGraph n m)
    (K : Finset (Channel (n + 2))) (k : ℕ) (bound : k ≤ m) :
    (independentDAG J).eval (assignmentOfSet K)
      ⟨3 * k, by change 3 * k < 3 * m + 1; omega⟩ =
      independentPrefix J K k bound := by
  induction k with
  | zero =>
      rw [DAG.eval_eq]
      simp [independentDAG, independentPrefix, Gate.eval, assignmentOfSet]
  | succ k ih =>
      have equation := independentDAG_diamond J K (⟨k, by omega⟩ : Fin m)
      change (independentDAG J).eval (assignmentOfSet K)
        ⟨3 * (k + 1), by change 3 * (k + 1) < 3 * m + 1; omega⟩ = _
      rw [equation, ih]
      rfl

theorem independentDAG_eval (J : EnumeratedGraph n m)
    (K : Finset (Channel (n + 2))) :
    (independentDAG J).eval (assignmentOfSet K)
      ⟨3 * m, by change 3 * m < 3 * m + 1; omega⟩ = independentValue J K :=
  independentDAG_prefix_eval J K m (Nat.le_refl m)

/-- A coarse linear bound includes every channel, node, child, guard and root. -/
theorem independentDAG_countedSize_le (J : EnumeratedGraph n m) :
    (independentDAG J).countedSize ≤ n + 12 * m + 7 := by
  have children : (independentDAG J).childIncidences ≤ 2 * (3 * m + 1) := by
    unfold DAG.childIncidences
    rw [Fin.sum_ofFn]
    calc
      _ ≤ ∑ _index : Fin (independentDAG J).nodeCount, 2 := by
        apply Finset.sum_le_sum
        intro index _
        simp only [independentDAG]
        split
        · simp [Gate.children]
        · split
          · simp [Gate.children]
          · split <;> simp [Gate.children]
      _ = _ := by
        rw [Fin.sum_const]
        simp only [nsmul_eq_mul, Nat.cast_id]
        change (3 * m + 1) * 2 = 2 * (3 * m + 1)
        omega
  have guards : (independentDAG J).guardIncidences ≤ 3 * m + 1 := by
    unfold DAG.guardIncidences
    rw [Fin.sum_ofFn]
    calc
      _ ≤ ∑ _index : Fin (independentDAG J).nodeCount, 1 := by
        apply Finset.sum_le_sum
        intro index _
        simp only [independentDAG]
        split
        · simp [Gate.guardLabels]
        · split
          · simp [Gate.guardLabels]
          · split <;> simp [Gate.guardLabels]
      _ = _ := by
        rw [Fin.sum_const]
        simp only [nsmul_eq_mul, Nat.cast_id]
        change (3 * m + 1) * 1 = 3 * m + 1
        omega
  rw [DAG.countedSize_eq]
  have nodes := independentDAG_nodes J
  have roots : (independentDAG J).roots.length = 1 := rfl
  omega

theorem independentDAG_size_linear (J : EnumeratedGraph n m) (nonempty : 0 < n + m) :
    (independentDAG J).countedSize ≤ 19 * (n + m) := by
  have bound := independentDAG_countedSize_le J
  omega

abbrev IndependentSets (J : EnumeratedGraph n m) :=
  {I : Finset (Fin n) // J.IsIndependent I}

abbrev IndependentDetections (J : EnumeratedGraph n m) :=
  {K : Finset (Channel (n + 2)) // Admissible 1 (independentTarget n) K ∧
    independentValue J K ≠ independentValue J {independentTarget n}}

noncomputable instance independentSetsFintype (J : EnumeratedGraph n m) :
    Fintype (IndependentSets J) := Fintype.ofFinite _

noncomputable instance independentDetectionsFintype (J : EnumeratedGraph n m) :
    Fintype (IndependentDetections J) := Fintype.ofFinite _

private theorem vertexComplement_twice (I : Finset (Fin n)) :
    Finset.univ \ (Finset.univ \ I) = I := by
  ext v
  simp

def coverIndependentEquiv (J : EnumeratedGraph n m) : Covers J ≃ IndependentSets J where
  toFun C := ⟨Finset.univ \ C.val, by
    rw [independent_iff_complement_cover, vertexComplement_twice]
    exact C.property⟩
  invFun I := ⟨Finset.univ \ I.val,
    (independent_iff_complement_cover J I.val).mp I.property⟩
  left_inv C := by apply Subtype.ext; exact vertexComplement_twice C.val
  right_inv I := by apply Subtype.ext; exact vertexComplement_twice I.val

theorem independent_count_eq_cover (J : EnumeratedGraph n m) :
    Fintype.card (IndependentSets J) = Fintype.card (Covers J) :=
  (Fintype.card_congr (coverIndependentEquiv J)).symm

noncomputable def independentDetectionEquiv (J : EnumeratedGraph n m) :
    IndependentSets J ≃ IndependentDetections J where
  toFun I := ⟨independentSet I.val, by
    have legal : Admissible 1 (independentTarget n) (independentSet I.val) := by simp
    exact ⟨legal, (independent_detects_iff J _ legal).mpr ⟨I.val, I.property, rfl⟩⟩⟩
  invFun K := ⟨independentVertices K.val, by
    obtain ⟨I, independent, equation⟩ := (independent_detects_iff J _ K.property.1).mp K.property.2
    simpa [equation] using independent⟩
  left_inv I := by apply Subtype.ext; simp
  right_inv K := by
    apply Subtype.ext
    have marker := (independentValue_true_iff J K.val).mp
      (by simpa using K.property.2)
    exact independentSet_independentVertices K.val
      ((admissible_one _ _).mp K.property.1) marker.1

theorem independent_detection_count (J : EnumeratedGraph n m) :
    Fintype.card (IndependentDetections J) = Fintype.card (IndependentSets J) :=
  (Fintype.card_congr (independentDetectionEquiv J)).symm

theorem independent_threshold_iff (J : EnumeratedGraph n m) (k : ℕ) :
    (∃ K : IndependentDetections J, k + 2 ≤ K.val.card) ↔
      ∃ I : IndependentSets J, k ≤ I.val.card := by
  constructor
  · rintro ⟨K, large⟩
    let I := (independentDetectionEquiv J).symm K
    refine ⟨I, ?_⟩
    have same := congrArg (fun L : IndependentDetections J => L.val.card)
      ((independentDetectionEquiv J).apply_symm_apply K)
    change (independentSet I.val).card = K.val.card at same
    rw [independentSet_card] at same
    omega
  · rintro ⟨I, large⟩
    refine ⟨independentDetectionEquiv J I, ?_⟩
    change k + 2 ≤ (independentSet I.val).card
    rw [independentSet_card]
    omega

def independentBridge (n : ℕ) : Physical.Bridge (n + 2) where
  target := independentTarget n
  drivers := {independentMarker n}
  drivers_nonempty := by simp
  target_not_mem := by
    simp only [Finset.mem_singleton]
    intro equal
    have values := congrArg Fin.val equal
    change n + 1 = n at values
    omega

theorem independent_realizer_driver_request_zero (K : Finset (Channel (n + 2)))
    (bus : Fin 1) :
    (Physical.realizeBridge (independentBridge n) (by decide : 0 < 1) K).request
      bus (independentMarker n) = false := by
  have zero : bus = 0 := Subsingleton.elim _ _
  subst bus
  simp [Physical.realizeBridge, Physical.realizeRequests, independentBridge, assignmentOfSet]

def independentObservation (J : EnumeratedGraph n m) :
    Fin 1 → Assignment (n + 2) → Bool := fun _ a => independentValue J (setOfAssignment a)

theorem independentObservation_eq_dag (J : EnumeratedGraph n m) (a : Assignment (n + 2)) :
    independentObservation J 0 a = (independentDAG J).eval a
      ⟨3 * m, by change 3 * m < 3 * m + 1; omega⟩ := by
  simpa only [independentObservation, assignmentOfSet_setOfAssignment] using
    (independentDAG_eval J (setOfAssignment a)).symm

theorem independent_physical_detects_only_sets (J : EnumeratedGraph n m)
    (input : Physical.PrimaryInput (n + 2) 1) (wire : Bool)
    (detects : Physical.BridgeInputDetects (independentBridge n) true
      (independentObservation J) input wire) :
    ∃ I, J.IsIndependent I ∧
      setOfAssignment (Physical.bridgeQualifiers (independentBridge n) input wire) = independentSet I := by
  have changed : Physical.stageFlag input.enable (input.request input.firstBus) ≠
      Physical.bridgeFirstFlag (independentBridge n) input wire := by
    intro equal
    exact Physical.no_observation_change_of_firstFlag_eq (independentBridge n) input wire
      (independentObservation J) equal detects.2
  have image := Physical.separated_drive_one_image (independentBridge n) input detects.1 changed
  obtain ⟨index, inequality⟩ := detects.2
  rw [image.1] at inequality
  simp only [independentObservation, setOfAssignment_assignmentOfSet] at inequality
  exact (independent_detects_iff J _ image.2).mp inequality.symm

theorem independent_realizer_detects_iff (J : EnumeratedGraph n m)
    (K : Finset (Channel (n + 2))) (legal : Admissible 1 (independentTarget n) K) :
    Physical.BridgeInputDetects (independentBridge n) true (independentObservation J)
      (Physical.realizeBridge (independentBridge n) (by decide : 0 < 1) K) true ↔
      ∃ I, J.IsIndependent I ∧ K = independentSet I := by
  rw [Physical.realizeBridge_detects_iff (independentBridge n) (by decide : 0 < 1) K legal]
  simp only [Physical.ObservationsDiffer, independentObservation,
    setOfAssignment_assignmentOfSet]
  change (∃ _i : Fin 1, independentValue J {independentTarget n} ≠ independentValue J K) ↔ _
  have reverse :
      (∃ _i : Fin 1, independentValue J {independentTarget n} ≠ independentValue J K) ↔
      independentValue J K ≠ independentValue J {independentTarget n} :=
    ⟨fun ⟨_, h⟩ => h.symm, fun h => ⟨0, h.symm⟩⟩
  rw [reverse]
  exact independent_detects_iff J K legal

end Controller.Reductions
