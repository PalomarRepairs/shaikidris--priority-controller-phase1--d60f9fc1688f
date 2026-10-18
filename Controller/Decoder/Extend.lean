module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Decoder.Detect

@[expose] public section

/-!
# Detecting extensions of fixed eligible coordinates

The executable retains all fixed-true channels, rejects fixed-false conflicts,
and adds the forced target on one bus. Each healthy-zero candidate is evaluated
once over the shared DAG; healthy-one roots use the fixed-unit zero worklist.
The restrictions concern eligibility coordinates. Operational resource bounds
belong to the separate cost refinement.
-/

namespace Controller.Decoder

variable {n : ℕ}

instance fixedConsistentDecidable (T F : Finset (Channel n)) :
    Decidable (FixedConsistent T F) := Finset.decidableDisjoint T F

def extensionBase (b : ℕ) (target : Channel n) (T : Finset (Channel n)) :
    Finset (Channel n) := if b = 1 then insert target T else T

theorem extensionBase_subset_iff (b : ℕ) (target : Channel n)
    (T K : Finset (Channel n)) :
    extensionBase b target T ⊆ K ↔ T ⊆ K ∧ (b = 1 → target ∈ K) := by
  by_cases one : b = 1
  · simp [extensionBase, one, Finset.insert_subset_iff, and_comm]
  · simp [extensionBase, one]

theorem extensionBase_extends (b : ℕ) (target : Channel n)
    (T F K : Finset (Channel n)) (extension : ExtendsFixed (extensionBase b target T) F K) :
    ExtendsFixed T F K ∧ (b = 1 → target ∈ K) := by
  obtain ⟨fixed, targetPresent⟩ := (extensionBase_subset_iff b target T K).mp extension.1
  exact ⟨⟨fixed, extension.2⟩, targetPresent⟩

theorem admissible_extensionBase (b : ℕ) (target : Channel n)
    (T F K : Finset (Channel n)) (eligible : Admissible b target K)
    (extension : ExtendsFixed T F K) : ExtendsFixed (extensionBase b target T) F K :=
  ⟨(extensionBase_subset_iff b target T K).mpr ⟨extension.1, eligible.2⟩, extension.2⟩

/-- One baseline followed by one candidate for each unfixed, non-forbidden head. -/
def extensionCandidates (b : ℕ) (target : Channel n) (T F : Finset (Channel n)) :
    List (Finset (Channel n)) :=
  let base := extensionBase b target T
  base :: ((List.finRange n).filter fun head => head ∉ base ∧ head ∉ F).map
    (fun head => insert head base)

theorem extensionCandidates_extends (b : ℕ) (target : Channel n)
    (T F K : Finset (Channel n)) (consistent : FixedConsistent (extensionBase b target T) F)
    (member : K ∈ extensionCandidates b target T F) :
    ExtendsFixed (extensionBase b target T) F K := by
  rcases List.mem_cons.mp member with rfl | member
  · exact extendsFixed_self consistent
  · obtain ⟨head, present, rfl⟩ := List.mem_map.mp member
    have free := (List.mem_filter.mp present).2
    have notFalse : head ∉ F := (of_decide_eq_true free).2
    exact ⟨Finset.subset_insert _ _, Finset.disjoint_insert_left.mpr ⟨notFalse, consistent⟩⟩

namespace DAG

theorem admissible_fixed_true_iff_candidate (graph : DAG n) (guarded : graph.Guarded)
    (b : ℕ) (target : Channel n) (T F : Finset (Channel n))
    (root : Fin graph.nodeCount) (consistent : FixedConsistent (extensionBase b target T) F) :
    (∃ K, Admissible b target K ∧ ExtendsFixed T F K ∧
      graph.eval (assignmentOfSet K) root = true) ↔
    ∃ K ∈ extensionCandidates b target T F, graph.eval (assignmentOfSet K) root = true := by
  constructor
  · rintro ⟨K, eligible, extension, value⟩
    obtain ⟨_, fixed | ⟨head, notTrue, notFalse, _, withHead⟩⟩ :=
      (graph.exists_true_extension_iff guarded root (extensionBase b target T) F).mp
        ⟨K, admissible_extensionBase b target T F K eligible extension, value⟩
    · exact ⟨extensionBase b target T, List.mem_cons_self, fixed⟩
    · refine ⟨insert head (extensionBase b target T), List.mem_cons_of_mem _ ?_, withHead⟩
      apply List.mem_map.mpr
      exact ⟨head, List.mem_filter.mpr ⟨List.mem_finRange head, by simp [notTrue, notFalse]⟩, rfl⟩
  · rintro ⟨K, member, value⟩
    obtain ⟨extension, forced⟩ := extensionBase_extends b target T F K
      (extensionCandidates_extends b target T F K consistent member)
    exact ⟨K, ⟨graph.nonempty_of_eval_true K root value, forced⟩, extension, value⟩

/-- A single value table serves every healthy-zero root for this candidate. -/
def extensionTrueQuery (graph : DAG n) (healthy : Fin graph.nodeCount → Bool)
    (candidate : Finset (Channel n)) : Option (Finset (Channel n)) :=
  let values := graph.evalTable (assignmentOfSet candidate)
  if graph.roots.any (fun root => !healthy root && values root) then some candidate else none

theorem extensionTrueQuery_none_iff (graph : DAG n) (healthy : Fin graph.nodeCount → Bool)
    (candidate : Finset (Channel n)) :
    graph.extensionTrueQuery healthy candidate = none ↔
      ¬ ∃ root ∈ graph.roots, healthy root = false ∧
        graph.eval (assignmentOfSet candidate) root = true := by
  simp [extensionTrueQuery, evalTable_eq_eval, List.any_eq_true]

theorem extensionTrueQuery_some (graph : DAG n) (healthy : Fin graph.nodeCount → Bool)
    (candidate K : Finset (Channel n))
    (returned : graph.extensionTrueQuery healthy candidate = some K) :
    K = candidate ∧ ∃ root ∈ graph.roots, healthy root = false ∧
      graph.eval (assignmentOfSet K) root = true := by
  unfold extensionTrueQuery at returned
  dsimp only at returned
  split at returned
  next yes =>
    have equal := Option.some.inj returned
    subst K
    exact ⟨rfl, by simpa [evalTable_eq_eval, List.any_eq_true] using yes⟩
  next no => simp at returned

/-- Both fixed signs are passed unchanged to the reachable zero system. -/
def extensionZeroQuery (graph : DAG n) (b : ℕ) (target : Channel n)
    (healthy : Fin graph.nodeCount → Bool) (T F : Finset (Channel n))
    (root : Fin graph.nodeCount) : Option (Finset (Channel n)) :=
  if healthy root then graph.solveZero b target root T F else none

theorem extensionZeroQuery_none_iff (graph : DAG n) (guarded : graph.Guarded)
    (b : ℕ) (target : Channel n) (healthy : Fin graph.nodeCount → Bool)
    (T F : Finset (Channel n)) (root : Fin graph.nodeCount) :
    graph.extensionZeroQuery b target healthy T F root = none ↔
      ¬ (healthy root = true ∧ ∃ K, Admissible b target K ∧ ExtendsFixed T F K ∧
        graph.eval (assignmentOfSet K) root = false) := by
  cases value : healthy root <;> simp [extensionZeroQuery, value, graph.solveZero_none_iff guarded]

/-- Shared candidate passes precede the root-indexed fixed-unit zero queries. -/
def extendSet (graph : DAG n) (b : ℕ) (target : Channel n) (drive : Bool)
    (T F : Finset (Channel n)) : Option (Finset (Channel n)) :=
  if drive then
    if FixedConsistent (extensionBase b target T) F then
      let healthy := graph.evalTable (assignmentOfSet {target})
      match firstSuccess (graph.extensionTrueQuery healthy) (extensionCandidates b target T F) with
      | some K => some K
      | none => firstSuccess (graph.extensionZeroQuery b target healthy T F) graph.roots
    else none
  else none

@[simp] theorem extendSet_drive_false (graph : DAG n) (b : ℕ) (target : Channel n)
    (T F : Finset (Channel n)) : graph.extendSet b target false T F = none := by
  simp [extendSet]

theorem extendSet_conflict (graph : DAG n) (b : ℕ) (target : Channel n) (drive : Bool)
    (T F : Finset (Channel n)) (conflict : ¬ FixedConsistent (extensionBase b target T) F) :
    graph.extendSet b target drive T F = none := by
  cases drive <;> simp [extendSet, conflict]

theorem extendSet_target_false (graph : DAG n) (target : Channel n) (drive : Bool)
    (T F : Finset (Channel n)) (forbidden : target ∈ F) :
    graph.extendSet 1 target drive T F = none := by
  apply graph.extendSet_conflict
  intro consistent
  exact Finset.disjoint_left.mp consistent (by simp [extensionBase]) forbidden

theorem extendSet_some (graph : DAG n) (guarded : graph.Guarded) (b : ℕ)
    (target : Channel n) (drive : Bool) (T F K : Finset (Channel n))
    (returned : graph.extendSet b target drive T F = some K) :
    drive = true ∧ Admissible b target K ∧ ExtendsFixed T F K ∧
      ∃ root ∈ graph.roots,
        graph.eval (assignmentOfSet K) root ≠ graph.eval (assignmentOfSet {target}) root := by
  cases drive with
  | false => simp [extendSet] at returned
  | true =>
    by_cases consistent : FixedConsistent (extensionBase b target T) F
    · simp only [extendSet, ite_true, ite_eq_left consistent, evalTable_eq_eval] at returned
      cases scan : firstSuccess (graph.extensionTrueQuery (graph.eval (assignmentOfSet {target})))
          (extensionCandidates b target T F) with
      | some found =>
        rw [scan] at returned
        have equal := Option.some.inj returned
        subst found
        obtain ⟨candidate, member, found⟩ := firstSuccess_some _ _ K scan
        obtain ⟨rfl, root, present, healthy, faulty⟩ := graph.extensionTrueQuery_some _ candidate K found
        obtain ⟨fixed, forced⟩ := extensionBase_extends b target T F K
          (extensionCandidates_extends b target T F K consistent member)
        exact ⟨rfl, ⟨graph.nonempty_of_eval_true K root faulty, forced⟩, fixed,
          root, present, by rw [healthy, faulty]; decide⟩
      | none =>
        rw [scan] at returned
        obtain ⟨root, present, value⟩ := firstSuccess_some _ _ K returned
        unfold extensionZeroQuery at value
        split at value
        next healthy =>
          obtain ⟨eligible, fixed, faulty⟩ := graph.solveZero_some guarded b target root T F K value
          exact ⟨rfl, eligible, fixed, root, present, by rw [healthy, faulty]; decide⟩
        next impossible => simp at value
    · simp [extendSet, consistent] at returned

theorem extendSet_none_iff (graph : DAG n) (guarded : graph.Guarded) (b : ℕ)
    (target : Channel n) (drive : Bool) (T F : Finset (Channel n)) :
    graph.extendSet b target drive T F = none ↔
      ¬ (drive = true ∧ ∃ root ∈ graph.roots, ∃ K, Admissible b target K ∧
        ExtendsFixed T F K ∧
        graph.eval (assignmentOfSet K) root ≠ graph.eval (assignmentOfSet {target}) root) := by
  cases drive with
  | false => simp [extendSet]
  | true =>
    by_cases consistent : FixedConsistent (extensionBase b target T) F
    · simp only [extendSet, ite_true, ite_eq_left consistent, evalTable_eq_eval, true_and]
      cases scan : firstSuccess (graph.extensionTrueQuery (graph.eval (assignmentOfSet {target})))
          (extensionCandidates b target T F) with
      | some K =>
        simp only [Option.some_ne_none, false_iff, not_not]
        have returned : graph.extendSet b target true T F = some K := by
          simp [extendSet, consistent, evalTable_eq_eval, scan]
        obtain ⟨_, eligible, fixed, root, present, differs⟩ :=
          graph.extendSet_some guarded b target true T F K returned
        exact ⟨root, present, K, eligible, fixed, differs⟩
      | none =>
        rw [firstSuccess_none_iff]
        have absent := (firstSuccess_none_iff _ _).mp scan
        constructor
        · intro zeros
          rintro ⟨root, present, K, eligible, fixed, differs⟩
          cases healthy : graph.eval (assignmentOfSet {target}) root with
          | false =>
            have faulty : graph.eval (assignmentOfSet K) root = true := by
              cases value : graph.eval (assignmentOfSet K) root <;> simp_all
            obtain ⟨candidate, member, value⟩ :=
              (graph.admissible_fixed_true_iff_candidate guarded b target T F root consistent).mp
                ⟨K, eligible, fixed, faulty⟩
            exact (graph.extensionTrueQuery_none_iff _ candidate).mp (absent candidate member)
              ⟨root, present, healthy, value⟩
          | true =>
            have faulty : graph.eval (assignmentOfSet K) root = false := by
              cases value : graph.eval (assignmentOfSet K) root <;> simp_all
            exact (graph.extensionZeroQuery_none_iff guarded b target _ T F root).mp (zeros root present)
              ⟨healthy, K, eligible, fixed, faulty⟩
        · intro no root present
          apply (graph.extensionZeroQuery_none_iff guarded b target _ T F root).mpr
          rintro ⟨healthy, K, eligible, fixed, faulty⟩
          exact no ⟨root, present, K, eligible, fixed, by rw [healthy, faulty]; decide⟩
    · constructor
      · intro _
        rintro ⟨_, root, _, K, eligible, fixed, _⟩
        exact consistent (extendsFixed_consistent (admissible_extensionBase b target T F K eligible fixed))
      · intro _
        exact graph.extendSet_conflict b target true T F consistent

theorem extendSet_all_fixed (graph : DAG n) (guarded : graph.Guarded) (b : ℕ)
    (target : Channel n) (drive : Bool) (T F K : Finset (Channel n))
    (allFixed : T ∪ F = Finset.univ)
    (returned : graph.extendSet b target drive T F = some K) : K = T := by
  have fixed := (graph.extendSet_some guarded b target drive T F K returned).2.2.1
  apply Finset.Subset.antisymm ?_ fixed.1
  intro channel present
  have classified : channel ∈ T ∪ F := by rw [allFixed]; exact Finset.mem_univ channel
  rcases Finset.mem_union.mp classified with inTrue | inFalse
  · exact inTrue
  · exact (Finset.disjoint_left.mp fixed.2 present inFalse).elim

@[simp] theorem extendSet_no_roots (graph : DAG n) (guarded : graph.Guarded)
    (b : ℕ) (target : Channel n) (drive : Bool) (T F : Finset (Channel n))
    (empty : graph.roots = []) : graph.extendSet b target drive T F = none := by
  apply (graph.extendSet_none_iff guarded b target drive T F).mpr
  simp [empty]

/-- Successful extension is equivalent to a returned witness, including all-fixed inputs. -/
theorem extendSet_exists_iff (graph : DAG n) (guarded : graph.Guarded) (b : ℕ)
    (target : Channel n) (drive : Bool) (T F : Finset (Channel n)) :
    (∃ K, graph.extendSet b target drive T F = some K) ↔
      drive = true ∧ ∃ root ∈ graph.roots, ∃ K, Admissible b target K ∧
        ExtendsFixed T F K ∧
        graph.eval (assignmentOfSet K) root ≠ graph.eval (assignmentOfSet {target}) root := by
  constructor
  · rintro ⟨K, returned⟩
    obtain ⟨driveTrue, eligible, fixed, root, present, differs⟩ :=
      graph.extendSet_some guarded b target drive T F K returned
    exact ⟨driveTrue, root, present, K, eligible, fixed, differs⟩
  · intro witness
    cases result : graph.extendSet b target drive T F with
    | none => exact ((graph.extendSet_none_iff guarded b target drive T F).mp result witness).elim
    | some K => exact ⟨K, rfl⟩

end DAG
end Controller.Decoder
