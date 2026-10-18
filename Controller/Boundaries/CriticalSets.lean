module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Decoder.Eval
public import Controller.Basic.Admissible
public import Controller.Physical.DetectionBridge
public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# Hidden critical sets

The cycle terms and unconditional outside terms form a guarded decoder with
one nonempty zero. The finite family counts retain the one-bus target promise.
-/

namespace Controller.Boundaries

open Decoder

variable {n : ℕ}

/-- A cyclic successor on precisely the selected channels. -/
noncomputable def successor (K : Finset (Channel n)) : Equiv.Perm (Channel n) :=
  Classical.choose K.exists_cycleOn

theorem successor_cycle (K : Finset (Channel n)) :
    (successor K).IsCycleOn (K : Set (Channel n)) :=
  (Classical.choose_spec K.exists_cycleOn).1

/-- The source formula, including unconditional terms outside the hidden set. -/
noncomputable def criticalValue (K L : Finset (Channel n)) : Bool := by
  classical
  exact (List.ofFn fun i : Channel n =>
    if i ∈ K then decide (i ∈ L) && !decide (successor K i ∈ L)
    else decide (i ∈ L)).any id

theorem criticalValue_false_iff (K L : Finset (Channel n)) :
    criticalValue K L = false ↔
      L ⊆ K ∧ ∀ i ∈ L, successor K i ∈ L := by
  classical
  simp only [criticalValue, List.any_eq_false, List.mem_ofFn]
  constructor
  · intro h
    have each : ∀ i : Channel n,
        (if i ∈ K then decide (i ∈ L) && !decide (successor K i ∈ L)
        else decide (i ∈ L)) = false := fun i => by
          simpa only [id_eq, Bool.eq_false_iff] using h _ ⟨i, rfl⟩
    have subset : L ⊆ K := by
      intro i hi
      by_contra hout
      simpa [hout, hi] using each i
    refine ⟨subset, ?_⟩
    intro i hi
    simpa [subset hi, hi] using each i
  · rintro ⟨subset, closed⟩ value ⟨i, rfl⟩
    by_cases hi : i ∈ L
    · simp [subset hi, hi, closed i hi]
    · simp [hi]

/-- A nonempty successor-closed subset of a finite cycle is the whole cycle. -/
theorem closed_eq_cycle (K L : Finset (Channel n)) (nonempty : L.Nonempty)
    (subset : L ⊆ K) (closed : ∀ i ∈ L, successor K i ∈ L) : L = K := by
  classical
  obtain ⟨start, hs⟩ := nonempty
  apply Finset.Subset.antisymm subset
  intro i hi
  obtain ⟨steps, _, equation⟩ := (successor_cycle K).exists_pow_eq (subset hs) hi
  have iterated : ∀ k : ℕ, ((successor K) ^ k) start ∈ L := by
    intro k
    induction k with
    | zero => simpa using hs
    | succ k ih =>
        simpa [pow_succ', Equiv.Perm.mul_apply] using closed _ ih
  rw [← equation]
  exact iterated steps

/-- Exact response on every nonempty eligible set, uniformly in channel count. -/
theorem criticalValue_nonempty (K L : Finset (Channel n)) (nonempty : L.Nonempty) :
    criticalValue K L = false ↔ L = K := by
  classical
  rw [criticalValue_false_iff]
  constructor
  · rintro ⟨subset, closed⟩
    exact closed_eq_cycle K L nonempty subset closed
  · intro equation
    subst L
    exact ⟨Finset.Subset.refl _, fun i hi => (successor_cycle K).1.mapsTo hi⟩

@[simp] theorem criticalValue_empty (K : Finset (Channel n)) :
    criticalValue K ∅ = false := by
  rw [criticalValue_false_iff]
  simp

/-- The full cycle has no proper nonempty zero set (Example 5.2). -/
theorem full_cycle_unique_zero (L : Finset (Channel n)) (nonempty : L.Nonempty) :
    criticalValue Finset.univ L = false ↔ L = Finset.univ :=
  criticalValue_nonempty _ _ nonempty

/-- The literal modulo-successor formula of Example 5.2. Finite rotation is
addition by one modulo the declared channel count. -/
def moduloCycleValue (L : Finset (Channel n)) : Bool :=
  (List.ofFn fun i : Channel n => decide (i ∈ L) && !decide (finRotate n i ∈ L)).any id

theorem moduloCycle_false_iff (L : Finset (Channel n)) :
    moduloCycleValue L = false ↔ ∀ i ∈ L, finRotate n i ∈ L := by
  simp only [moduloCycleValue, List.any_eq_false, List.mem_ofFn]
  constructor
  · intro h i hi
    simpa [hi] using h _ ⟨i, rfl⟩
  · intro closed value witness
    obtain ⟨i, rfl⟩ := witness
    by_cases hi : i ∈ L
    · simp only [hi, closed i hi, decide_true, Bool.not_true, Bool.and_false,
        id_eq, Bool.false_eq_true, not_false_eq_true]
    · simp [hi]

/-- The exact cycle written in the source has only the all-channel nonempty
zero, including the one-channel boundary case. -/
theorem moduloCycle_unique_nonempty_zero (L : Finset (Channel n))
    (nonempty : L.Nonempty) : moduloCycleValue L = false ↔ L = Finset.univ := by
  rw [moduloCycle_false_iff]
  constructor
  · intro closed
    obtain ⟨start, hs⟩ := nonempty
    by_cases hn : 2 ≤ n
    · have cycle : (finRotate n).IsCycleOn (Finset.univ : Finset (Channel n)) := by
        have hc := (isCycle_finRotate_of_le hn).isCycleOn
        have support := support_finRotate_of_le hn
        have sets : {i : Channel n | finRotate n i ≠ i} =
            (↑(Finset.univ : Finset (Channel n)) : Set (Channel n)) := by
          ext i
          simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_univ, iff_true]
          apply Equiv.Perm.mem_support.mp
          rw [support]
          exact Finset.mem_univ i
        rw [sets] at hc
        exact hc
      apply Finset.eq_univ_iff_forall.mpr
      intro i
      obtain ⟨steps, _, equation⟩ := cycle.exists_pow_eq (Finset.mem_univ start)
        (Finset.mem_univ i)
      have iterated : ∀ k : ℕ, ((finRotate n) ^ k) start ∈ L := by
        intro k
        induction k with
        | zero => simpa using hs
        | succ k ih =>
            simpa [pow_succ', Equiv.Perm.mul_apply] using closed _ ih
      rw [← equation]
      exact iterated steps
    · have hn' : n = 1 := by have := start.isLt; omega
      subst n
      apply Finset.eq_univ_iff_forall.mpr
      intro i
      have equation : i = start := Subsingleton.elim _ _
      simpa [equation] using hs
  · intro equation
    subst L
    simp

theorem moduloCycle_small_nonempty_true (L : Finset (Channel n))
    (nonempty : L.Nonempty) (small : L.card < n) : moduloCycleValue L = true := by
  have notZero : moduloCycleValue L ≠ false := by
    intro zero
    have equation := (moduloCycle_unique_nonempty_zero L nonempty).mp zero
    rw [equation, Finset.card_univ, Fintype.card_fin] at small
    omega
  cases h : moduloCycleValue L <;> simp_all

/-- A stored guarded DAG: inputs, cycle/outside terms, and one final OR. -/
noncomputable def criticalDAG (K : Finset (Channel n)) : DAG n := by
  classical
  exact {
    nodeCount := 2 * n + 1
    node := fun index =>
      if hi : index.val < n then .input ⟨index.val, hi⟩
      else if ht : index.val < 2 * n then
        let channel : Channel n := ⟨index.val - n, by omega⟩
        if channel ∈ K then
          .guard ⟨channel.val, by dsimp [channel]; omega⟩ [successor K channel]
        else .input channel
      else .disj (List.ofFn fun channel : Channel n => ⟨n + channel.val, by omega⟩)
    roots := [⟨2 * n, by omega⟩] }

theorem criticalDAG_guarded (K : Finset (Channel n)) : (criticalDAG K).Guarded := by
  classical
  intro index
  simp only [criticalDAG]
  split
  · rfl
  · split
    · split <;> rfl
    · rfl

@[simp] theorem criticalDAG_nodes (K : Finset (Channel n)) :
    (criticalDAG K).nodeCount = 2 * n + 1 := rfl

/-- A declared target makes the affine node count a uniform linear bound. -/
theorem criticalDAG_nodes_linear (K : Finset (Channel n)) (t : Channel n) :
    (criticalDAG K).nodeCount ≤ 3 * n := by
  rw [criticalDAG_nodes]
  have := t.isLt
  omega

/-- Every node preceding the final OR has at most one live child, while the
final OR lists the `n` term nodes. Shared references are charged as incidences. -/
theorem criticalDAG_childIncidences_le (K : Finset (Channel n)) :
    (criticalDAG K).childIncidences ≤ 3 * n := by
  classical
  unfold DAG.childIncidences
  rw [Fin.sum_ofFn]
  change (∑ index : Fin (2 * n + 1),
    ((criticalDAG K).node index).children.length) ≤ 3 * n
  rw [Fin.sum_univ_castSucc]
  have earlierBound : (∑ index : Fin (2 * n),
      ((criticalDAG K).node index.castSucc).children.length) ≤ 2 * n := by
    calc
      _ ≤ ∑ _index : Fin (2 * n), 1 := by
        apply Finset.sum_le_sum
        intro index _
        simp only [criticalDAG, Fin.val_castSucc]
        split
        · simp [Gate.children]
        · rw [dite_eq_left index.isLt]
          split <;> simp [Gate.children]
      _ = _ := by simp [Finset.card_univ]
  have final : ((criticalDAG K).node (Fin.last (2 * n))).children.length = n := by
    simp only [criticalDAG, Fin.val_last]
    rw [dite_eq_right (by omega : ¬ 2 * n < n), dite_eq_right (Nat.lt_irrefl (2 * n))]
    simp [Gate.children]
  omega

/-- A stored input, guard or OR has at most one negative guard incidence. -/
theorem criticalDAG_guardIncidences_le (K : Finset (Channel n)) :
    (criticalDAG K).guardIncidences ≤ 2 * n + 1 := by
  classical
  unfold DAG.guardIncidences
  rw [Fin.sum_ofFn]
  calc
    _ ≤ ∑ _index : Fin (criticalDAG K).nodeCount, 1 := by
      apply Finset.sum_le_sum
      intro index _
      simp only [criticalDAG]
      split
      · simp [Gate.guardLabels]
      · split
        · split <;> simp [Gate.guardLabels]
        · simp [Gate.guardLabels]
    _ = _ := by
      rw [Fin.sum_const]
      simpa only [nsmul_eq_mul, Nat.cast_id, Nat.mul_one] using criticalDAG_nodes K

/-- Uniform linear size in the shared resource interface. The total charges
declared channels, stored nodes, all child and guard incidences, and roots. -/
theorem criticalDAG_countedSize_le (K : Finset (Channel n)) :
    (criticalDAG K).countedSize ≤ 8 * n + 4 := by
  rw [DAG.countedSize_eq]
  have nodes := criticalDAG_nodes K
  have children := criticalDAG_childIncidences_le K
  have guards := criticalDAG_guardIncidences_le K
  have roots : (criticalDAG K).roots.length = 1 := rfl
  omega

private theorem criticalDAG_input (K L : Finset (Channel n)) (i : Channel n) :
    (criticalDAG K).eval (assignmentOfSet L) ⟨i.val, by change i.val < 2 * n + 1; omega⟩ =
      decide (i ∈ L) := by
  classical
  rw [DAG.eval_eq]
  simp [criticalDAG, i.isLt, Gate.eval, assignmentOfSet]

private theorem criticalDAG_term (K L : Finset (Channel n)) (i : Channel n) :
    (criticalDAG K).eval (assignmentOfSet L)
      ⟨n + i.val, by change n + i.val < 2 * n + 1; omega⟩ =
      (if i ∈ K then decide (i ∈ L) && !decide (successor K i ∈ L)
      else decide (i ∈ L)) := by
  classical
  rw [DAG.eval_eq]
  have hfirst : ¬ n + i.val < n := by omega
  have hsecond : n + i.val < 2 * n := by omega
  simp only [criticalDAG, hfirst, dite_false, hsecond, dite_true, Nat.add_sub_cancel_left]
  change (if i ∈ K then Gate.guard _ [successor K i] else Gate.input i).eval _ _ = _
  by_cases hi : i ∈ K
  · simp only [hi, ite_true, Gate.eval, List.any_cons, List.any_nil, Bool.or_false]
    change ((criticalDAG K).eval (assignmentOfSet L)
        ⟨i.val, by change i.val < 2 * n + 1; omega⟩ &&
      !(assignmentOfSet L (successor K i))) =
        (decide (i ∈ L) && !decide (successor K i ∈ L))
    rw [criticalDAG_input]
    rfl
  · simp [hi, Gate.eval, assignmentOfSet]

/-- The represented DAG evaluates to the literal source formula. -/
theorem criticalDAG_eval (K L : Finset (Channel n)) :
    (criticalDAG K).eval (assignmentOfSet L)
      ⟨2 * n, by change 2 * n < 2 * n + 1; omega⟩ = criticalValue K L := by
  classical
  rw [DAG.eval_eq]
  have hfirst : ¬ 2 * n < n := by omega
  simp only [criticalDAG, hfirst, dite_false, lt_self_iff_false, Gate.eval]
  apply Bool.eq_iff_iff.mpr
  simp only [criticalValue, List.any_eq_true, List.mem_ofFn]
  constructor
  · rintro ⟨value, ⟨i, rfl⟩, hvalue⟩
    exact ⟨_, ⟨i, rfl⟩, (criticalDAG_term K L i).symm ▸ hvalue⟩
  · rintro ⟨value, ⟨i, rfl⟩, hvalue⟩
    exact ⟨_, ⟨i, rfl⟩, (criticalDAG_term K L i) ▸ hvalue⟩

/-- The allowed hidden sets, excluding the healthy singleton. -/
def criticalSets (b : ℕ) (t : Channel n) : Finset (Finset (Channel n)) :=
  if b = 1 then
    (((Finset.univ.erase t).powerset.image (insert t)).erase {t})
  else (Finset.univ.powerset.erase ∅).erase {t}

theorem mem_criticalSets (b : ℕ) (t : Channel n) (K : Finset (Channel n)) :
    K ∈ criticalSets b t ↔ Admissible b t K ∧ K ≠ {t} := by
  classical
  by_cases hb : b = 1
  · subst b
    change K ∈ ((Finset.univ.erase t).powerset.image (insert t)).erase {t} ↔ _
    rw [Finset.mem_erase, Finset.mem_image]
    constructor
    · rintro ⟨hne, L, hL, rfl⟩
      exact ⟨(admissible_one _ _).mpr (by simp), hne⟩
    · rintro ⟨hK, hne⟩
      have ht := (admissible_one _ _).mp hK
      refine ⟨hne, K.erase t, ?_, ?_⟩
      · simp only [Finset.mem_powerset]
        intro i hi
        simp only [Finset.mem_erase] at hi ⊢
        exact ⟨hi.1, Finset.mem_univ _⟩
      · exact Finset.insert_erase ht
  · simp only [criticalSets, hb, ite_false, Finset.mem_erase, Finset.mem_powerset,
      Finset.subset_univ, and_true]
    simp [Admissible, hb, Finset.nonempty_iff_ne_empty, and_comm]

/-- On the physical image, a decoder in the promise family changes the
healthy singleton value exactly at its hidden critical set. -/
theorem criticalValue_detects_iff (b : ℕ) (t : Channel n)
    (K L : Finset (Channel n)) (hK : K ∈ criticalSets b t)
    (hL : Admissible b t L) :
    criticalValue K L ≠ criticalValue K {t} ↔ L = K := by
  have hne := (mem_criticalSets b t K).mp hK |>.2
  have healthy : criticalValue K {t} = true := by
    have hz : criticalValue K {t} ≠ false := by
      intro hz
      exact hne ((criticalValue_nonempty K {t} (by simp)).mp hz).symm
    cases hv : criticalValue K {t} <;> simp_all
  rw [healthy]
  have boolean : ∀ value : Bool, value ≠ true ↔ value = false := by decide
  rw [boolean, criticalValue_nonempty K L hL.1]

/-- A fixed list covering every decoder must contain every hidden set.
Each test contributes just its single faulty eligible set. -/
theorem universal_test_list_lower_bound (b : ℕ) (t : Channel n)
    (tests : List (Finset (Channel n)))
    (legal : ∀ L ∈ tests, Admissible b t L)
    (covers : ∀ K ∈ criticalSets b t, ∃ L ∈ tests,
      criticalValue K L ≠ criticalValue K {t}) :
    (criticalSets b t).card ≤ tests.length := by
  classical
  have subset : criticalSets b t ⊆ tests.toFinset := by
    intro K hK
    obtain ⟨L, hL, detects⟩ := covers K hK
    have equation := (criticalValue_detects_iff b t K L hK (legal L hL)).mp detects
    simpa [equation] using hL
  exact (Finset.card_le_card subset).trans tests.toFinset_card_le

/-- The single qualifier observation supplied by the hidden-set decoder. -/
noncomputable def criticalObservation (K : Finset (Channel n)) :
    Fin 1 → Assignment n → Bool := fun _ assignment =>
  criticalValue K (setOfAssignment assignment)

/-- The represented guarded decoder implements the physical observation on
every assignment, including assignments outside the fault image. -/
theorem criticalObservation_eq_dag (K : Finset (Channel n)) (assignment : Assignment n) :
    criticalObservation K 0 assignment =
      (criticalDAG K).eval assignment ⟨2 * n, by change 2 * n < 2 * n + 1; omega⟩ := by
  simpa only [criticalObservation, assignmentOfSet_setOfAssignment] using
    (criticalDAG_eval K (setOfAssignment assignment)).symm

/-- Every detecting physical input for this decoder has exactly its hidden
faulty eligible set. No abstract image witness is substituted for the input. -/
theorem critical_physical_detects_only_hidden {b : ℕ} (bridge : Physical.Bridge n)
    (K : Finset (Channel n)) (hK : K ∈ criticalSets b bridge.target)
    (input : Physical.PrimaryInput n b) (wire : Bool)
    (detects : Physical.BridgeInputDetects bridge true (criticalObservation K) input wire) :
    setOfAssignment (Physical.bridgeQualifiers bridge input wire) = K := by
  have changed : Physical.stageFlag input.enable (input.request input.firstBus) ≠
      Physical.bridgeFirstFlag bridge input wire := by
    intro equal
    exact Physical.no_observation_change_of_firstFlag_eq bridge input wire
      (criticalObservation K) equal detects.2
  have image := Physical.separated_drive_one_image bridge input detects.1 changed
  obtain ⟨index, inequality⟩ := detects.2
  rw [image.1] at inequality
  simp only [criticalObservation, setOfAssignment_assignmentOfSet] at inequality
  exact (criticalValue_detects_iff b bridge.target K _ hK image.2).mp inequality.symm

/-- The hidden set is attained by a concrete, detecting primary-input realizer. -/
theorem critical_physical_realizer_detects {b : ℕ} (bridge : Physical.Bridge n)
    (hb : 0 < b) (K : Finset (Channel n)) (hK : K ∈ criticalSets b bridge.target) :
    Physical.BridgeInputDetects bridge true (criticalObservation K)
      (Physical.realizeBridge bridge hb K) true := by
  have admissible := ((mem_criticalSets b bridge.target K).mp hK).1
  apply (Physical.realizeBridge_detects_iff bridge hb K admissible _).mpr
  refine ⟨0, ?_⟩
  simp only [criticalObservation, setOfAssignment_assignmentOfSet]
  exact ((criticalValue_detects_iff b bridge.target K K hK admissible).mpr rfl).symm

/-- Fixed primary-input lists obey the same counting bound: a physical input
has one faulty eligible set and detects at most one member of the family. -/
theorem physical_test_list_lower_bound {b : ℕ} (bridge : Physical.Bridge n)
    (tests : List (Physical.PrimaryInput n b))
    (covers : ∀ K ∈ criticalSets b bridge.target, ∃ input ∈ tests,
      Physical.BridgeInputDetects bridge true (criticalObservation K) input true) :
    (criticalSets b bridge.target).card ≤ tests.length := by
  classical
  let eligibleSets := tests.map (fun input =>
    setOfAssignment (Physical.bridgeQualifiers bridge input true))
  have subset : criticalSets b bridge.target ⊆ eligibleSets.toFinset := by
    intro K hK
    obtain ⟨input, member, detects⟩ := covers K hK
    simp only [List.mem_toFinset]
    exact List.mem_map.mpr ⟨input, member,
      critical_physical_detects_only_hidden bridge K hK input true detects⟩
  have count := (Finset.card_le_card subset).trans eligibleSets.toFinset_card_le
  simpa [eligibleSets] using count

/-- Exact exponential count on the one-bus image. -/
theorem criticalSets_card_one (t : Channel n) :
    (criticalSets 1 t).card = 2 ^ (n - 1) - 1 := by
  classical
  have injective : Set.InjOn (insert t : Finset (Channel n) → Finset (Channel n))
      (↑(Finset.univ.erase t).powerset) := by
    intro A hA B hB equation
    have ha : t ∉ A := fun ht =>
      (Finset.mem_erase.mp (Finset.mem_powerset.mp hA ht)).1 rfl
    have hb : t ∉ B := fun ht =>
      (Finset.mem_erase.mp (Finset.mem_powerset.mp hB ht)).1 rfl
    have := congrArg (fun L : Finset (Channel n) => L.erase t) equation
    simpa [ha, hb] using this
  have member : ({t} : Finset (Channel n)) ∈
      (Finset.univ.erase t).powerset.image (insert t) := by
    exact Finset.mem_image.mpr ⟨∅, by simp, by simp⟩
  change (((Finset.univ.erase t).powerset.image (insert t)).erase {t}).card = _
  rw [Finset.card_erase_of_mem member,
    Finset.card_image_of_injOn injective, Finset.card_powerset,
    Finset.card_erase_of_mem (Finset.mem_univ t), Finset.card_univ, Fintype.card_fin]

/-- Exact exponential count when the target-membership restriction is absent. -/
theorem criticalSets_card_many (b : ℕ) (hb : 2 ≤ b) (t : Channel n) :
    (criticalSets b t).card = 2 ^ n - 2 := by
  classical
  have hb' : b ≠ 1 := by omega
  have member : ({t} : Finset (Channel n)) ∈ Finset.univ.powerset.erase ∅ := by simp
  simp only [criticalSets, hb', ite_false, Finset.card_erase_of_mem member,
    Finset.card_erase_of_mem (by simp : (∅ : Finset (Channel n)) ∈ Finset.univ.powerset),
    Finset.card_powerset, Finset.card_univ, Fintype.card_fin]
  omega

end Controller.Boundaries
