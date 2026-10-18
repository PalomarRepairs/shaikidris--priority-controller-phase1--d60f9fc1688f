module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Basic.Admissible
public import Controller.Physical.CandidateInvariant
public import Controller.Physical.BridgeCofactors

@[expose] public section

/-!
# Primary inputs realizing an admissible bridge image

The constructor enables the target and the requested eligible set. The target
is the only first-bus requester. If the target is absent from the desired set,
that set requests on bus two; every other request is false. The constructor is
total, while its exact-image specification assumes admissibility.
-/

namespace Controller.Physical

/-- The suffix is zero except for the desired set on its first bus when the
target is absent. A zero-length suffix needs no bus index. -/
def realizeTailRequests {n : ℕ} (target : Channel n) (K : Finset (Channel n)) :
    (b : ℕ) → Fin b → Assignment n
  | 0 => Fin.elim0
  | _ + 1 => Fin.cases (if target ∈ K then (fun _ => false) else assignmentOfSet K)
      (fun _ _ => false)

/-- The first request singles out the target, followed by the realizing suffix. -/
def realizeRequests {n : ℕ} (target : Channel n) (K : Finset (Channel n)) :
    (b : ℕ) → Fin b → Assignment n
  | 0 => Fin.elim0
  | b + 1 => Fin.cases (assignmentOfSet {target}) (realizeTailRequests target K b)

/-- Explicit primary inputs for the drive-one image construction. -/
def realizeBridge {n b : ℕ} (bridge : Bridge n) (hb : 0 < b)
    (K : Finset (Channel n)) : PrimaryInput n b where
  positiveBuses := hb
  enable := assignmentOfSet (insert bridge.target K)
  request := realizeRequests bridge.target K b

private theorem realizeTailRequests_of_mem {n : ℕ} (target : Channel n)
    (K : Finset (Channel n)) (b : ℕ) (ht : target ∈ K) :
    realizeTailRequests target K b = (fun _ _ => false) := by
  cases b with
  | zero =>
      funext j
      exact Fin.elim0 j
  | succ b =>
      funext j
      refine Fin.cases ?_ (fun k => ?_) j
      · simp [realizeTailRequests, ht]
      · rfl

/-- The constructor's enabled first requests single out the target exactly. -/
theorem realizeBridge_firstTerms {n b : ℕ} (bridge : Bridge n) (hb : 0 < b)
    (K : Finset (Channel n)) :
    firstTerms (realizeBridge bridge hb K) = assignmentOfSet {bridge.target} := by
  cases b with
  | zero => exact (Nat.lt_irrefl 0 hb).elim
  | succ b =>
      funext i
      by_cases hi : i = bridge.target <;>
        simp [firstTerms, stageTerms, realizeBridge, realizeRequests,
          PrimaryInput.firstBus, assignmentOfSet, hi]

/-- Every legal driver group has the required drive-one cofactors, including
the case with no remaining channels. -/
theorem realizeBridge_cofactors {n b : ℕ} (bridge : Bridge n) (hb : 0 < b)
    (K : Finset (Channel n)) :
    bridgeU bridge (realizeBridge bridge hb K) = false ∧
      bridgeD bridge (realizeBridge bridge hb K) = true ∧
      bridgeR bridge (realizeBridge bridge hb K) = true := by
  have hd : ∀ i ∈ bridge.drivers, firstTerms (realizeBridge bridge hb K) i = false := by
    intro i hi
    have hit : i ≠ bridge.target := fun h => bridge.target_not_mem (h ▸ hi)
    simp [realizeBridge_firstTerms, assignmentOfSet, hit]
  have hr : ∀ i ∈ bridge.remaining, firstTerms (realizeBridge bridge hb K) i = false := by
    intro i hi
    have hit := ((bridge.mem_remaining i).mp hi).1
    simp [realizeBridge_firstTerms, assignmentOfSet, hit]
  refine ⟨?_, ?_, ?_⟩
  · simp [bridgeU, realizeBridge_firstTerms, assignmentOfSet]
  · simpa [bridgeD] using hd
  · simpa [bridgeR] using hr

/-- The explicit wire value is one and the primary inputs satisfy the interface. -/
theorem realizeBridge_interface {n b : ℕ} (bridge : Bridge n) (hb : 0 < b)
    (K : Finset (Channel n)) :
    BridgeInterfaceSatisfied bridge (realizeBridge bridge hb K) true true := by
  obtain ⟨hu, hd, _⟩ := realizeBridge_cofactors bridge hb K
  exact ⟨hu, hd, rfl⟩

/-- The faulty first flag of the constructed input is zero. -/
theorem realizeBridge_faultyFirstFlag {n b : ℕ} (bridge : Bridge n) (hb : 0 < b)
    (K : Finset (Channel n)) :
    bridgeFirstFlag bridge (realizeBridge bridge hb K) true = false := by
  obtain ⟨_, hd, hr⟩ := realizeBridge_cofactors bridge hb K
  simp [bridgeFirstFlag, hd, hr]

/-- The healthy eligible set of every constructed input is the target singleton. -/
theorem realizeBridge_healthy {n b : ℕ} (bridge : Bridge n) (hb : 0 < b)
    (K : Finset (Channel n)) :
    healthyQualifiers (realizeBridge bridge hb K) = assignmentOfSet {bridge.target} :=
  healthyQualifiers_eq_singleton_of_firstTerms _ _ (realizeBridge_firstTerms bridge hb K)

private theorem runCandidates_zero_requests {n : ℕ} (b : ℕ) (active : Assignment n) :
    (runCandidates b active (fun _ _ => false)).flags = (fun _ => false) ∧
      (runCandidates b active (fun _ _ => false)).finalActive = active := by
  induction b generalizing active with
  | zero =>
      constructor
      · funext j
        exact Fin.elim0 j
      · rfl
  | succ b ih =>
      have hflag : stageFlag active (fun _ => false) = false := by
        simp [stageFlag, stageTerms, anyTrue]
      have hstep := candidateStep_of_flag_false active (fun _ => false) hflag
      have hrest := ih active
      constructor
      · funext j
        refine Fin.cases ?_ (fun k => ?_) j
        · exact hflag
        · simpa [runCandidates, hstep] using congrFun hrest.1 k
      · simpa [runCandidates, hstep] using hrest.2

private theorem runMasks_zero_requests_flags {n : ℕ} (b : ℕ) (active : Assignment n) :
    (runMasks b active (fun _ _ => false) none).flags = (fun _ => false) :=
  ((runMasks_refines_candidates b active (fun _ _ => false)).1).trans
    (runCandidates_zero_requests b active).1

private theorem qualifiers_first_false_zero_tail {n : ℕ} (b : ℕ)
    (active first : Assignment n) :
    qualifiers active (Fin.cases first (fun _ _ => false))
      (runMasks (b + 1) active (Fin.cases first (fun _ _ => false)) (some false)).flags = active := by
  have hflags : (runMasks (b + 1) active (Fin.cases first (fun _ _ => false))
      (some false)).flags = (fun _ => false) := by
    funext j
    refine Fin.cases ?_ (fun k => ?_) j
    · rfl
    · change (runMasks b (nextActive active first false) (fun _ _ => false) none).flags k = false
      rw [runMasks_zero_requests_flags]
  rw [hflags]
  funext i
  simp [qualifiers]

/-- When the target is included, every faulty flag is zero and enablement gives
exactly the desired eligible vector. -/
theorem realizeBridge_faulty_of_mem {n b : ℕ} (bridge : Bridge n) (hb : 0 < b)
    (K : Finset (Channel n)) (ht : bridge.target ∈ K) :
    bridgeQualifiers bridge (realizeBridge bridge hb K) true = assignmentOfSet K := by
  unfold bridgeQualifiers
  rw [realizeBridge_faultyFirstFlag]
  cases b with
  | zero => exact (Nat.lt_irrefl 0 hb).elim
  | succ b =>
      change qualifiers (assignmentOfSet (insert bridge.target K))
        (Fin.cases (assignmentOfSet {bridge.target}) (realizeTailRequests bridge.target K b))
        (runMasks (b + 1) (assignmentOfSet (insert bridge.target K))
          (Fin.cases (assignmentOfSet {bridge.target}) (realizeTailRequests bridge.target K b))
          (some false)).flags = _
      rw [realizeTailRequests_of_mem _ _ _ ht, qualifiers_first_false_zero_tail,
        Finset.insert_eq_of_mem ht]

private theorem realization_two_flags {n : ℕ} (b : ℕ) (target : Channel n)
    (K : Finset (Channel n)) (ht : target ∉ K) (hK : K.Nonempty) :
    (runMasks (b + 2) (assignmentOfSet (insert target K))
      (Fin.cases (assignmentOfSet {target})
        (Fin.cases (assignmentOfSet K) (fun _ _ => false))) (some false)).flags =
      Fin.cases false (Fin.cases true (fun _ => false)) := by
  have hseed : nextActive (assignmentOfSet (insert target K))
      (assignmentOfSet {target}) false = assignmentOfSet K := by
    funext i
    by_cases hi : i = target
    · subst i
      simp [nextActive, stageMask, stageTerms, assignmentOfSet, ht]
    · by_cases hiK : i ∈ K <;>
        simp [nextActive, stageMask, stageTerms, assignmentOfSet, hi, hiK]
  have hflag : stageFlag (assignmentOfSet K) (assignmentOfSet K) = true := by
    obtain ⟨i, hi⟩ := hK
    apply (anyTrue_eq_true _).mpr
    exact ⟨i, by simp [stageTerms, assignmentOfSet, hi]⟩
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · rfl
  · refine Fin.cases ?_ (fun l => ?_) k
    · change stageFlag (nextActive (assignmentOfSet (insert target K))
        (assignmentOfSet {target}) false) (assignmentOfSet K) = true
      rw [hseed, hflag]
    · change (runMasks b
        (nextActive (nextActive (assignmentOfSet (insert target K))
          (assignmentOfSet {target}) false) (assignmentOfSet K)
          (stageFlag (nextActive (assignmentOfSet (insert target K))
            (assignmentOfSet {target}) false) (assignmentOfSet K)))
        (fun _ _ => false) none).flags l = false
      rw [runMasks_zero_requests_flags]

/-- When the target is excluded, admissibility supplies bus two; its selected
one flag excludes the target and retains precisely the desired set. -/
theorem realizeBridge_faulty_of_not_mem {n b : ℕ} (bridge : Bridge n) (hb : 0 < b)
    (K : Finset (Channel n)) (ht : bridge.target ∉ K) (hK : Admissible b bridge.target K) :
    bridgeQualifiers bridge (realizeBridge bridge hb K) true = assignmentOfSet K := by
  unfold bridgeQualifiers
  rw [realizeBridge_faultyFirstFlag]
  cases b with
  | zero => exact (Nat.lt_irrefl 0 hb).elim
  | succ b =>
      cases b with
      | zero => exact (ht (hK.2 rfl)).elim
      | succ b =>
          change qualifiers (assignmentOfSet (insert bridge.target K))
            (realizeRequests bridge.target K (b + 2))
            (runMasks (b + 2) (assignmentOfSet (insert bridge.target K))
              (realizeRequests bridge.target K (b + 2)) (some false)).flags = _
          simp only [realizeRequests, realizeTailRequests, ite_eq_right ht]
          rw [realization_two_flags b bridge.target K ht hK.1]
          funext i
          by_cases hi : i ∈ K <;>
            simp [qualifiers, Fin.forall_fin_succ, assignmentOfSet, hi]

/-- Complete physical specification of the computable drive-one realizer. -/
theorem realizeBridge_spec {n b : ℕ} (bridge : Bridge n) (hb : 0 < b)
    (K : Finset (Channel n)) (hK : Admissible b bridge.target K) :
    BridgeInterfaceSatisfied bridge (realizeBridge bridge hb K) true true ∧
      (healthyRun (realizeBridge bridge hb K)).flags (realizeBridge bridge hb K).firstBus = true ∧
      (runFromFirst (realizeBridge bridge hb K)
        (bridgeFirstFlag bridge (realizeBridge bridge hb K) true)).flags
          (realizeBridge bridge hb K).firstBus = false ∧
      healthyQualifiers (realizeBridge bridge hb K) = assignmentOfSet {bridge.target} ∧
      bridgeQualifiers bridge (realizeBridge bridge hb K) true = assignmentOfSet K := by
  refine ⟨realizeBridge_interface bridge hb K, ?_, ?_, realizeBridge_healthy bridge hb K, ?_⟩
  · rw [healthyRun_firstFlag]
    exact firstFlag_drive_one bridge _ (realizeBridge_interface bridge hb K)
  · rw [runFromFirst_firstFlag, realizeBridge_faultyFirstFlag]
  · by_cases ht : bridge.target ∈ K
    · exact realizeBridge_faulty_of_mem bridge hb K ht
    · exact realizeBridge_faulty_of_not_mem bridge hb K ht hK

end Controller.Physical
