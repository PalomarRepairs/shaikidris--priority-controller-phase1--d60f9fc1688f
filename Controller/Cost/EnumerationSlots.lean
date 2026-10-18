module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedZeroTemplate
public import Controller.Decoder.Extend
public import Controller.Decoder.ForestTraversal

@[expose] public section

/-! Fixed unit slots for prefix queries. Every channel contributes one literal.
Inactive slots repeat the negative queried-root unit already in the zero system.
The model equivalence requires disjoint true and false masks. -/
namespace Controller.Cost.EnumerationSlots
open Controller.CNF Controller.Decoder Controller.Decoder.DAG

variable {n : Nat}

def slot (graph : DAG n) (root : Fin graph.nodeCount)
    (T F : Finset (Channel n)) (channel : Channel n) : Clause graph.ZeroVar :=
  if channel ∈ T then [(.inl channel, true)]
  else if channel ∈ F then [(.inl channel, false)]
  else [(.inr root, false)]

def slots (graph : DAG n) (root : Fin graph.nodeCount)
    (T F : Finset (Channel n)) : List (Clause graph.ZeroVar) :=
  (List.finRange n).map (slot graph root T F)

@[simp] theorem slot_length (graph : DAG n) (root : Fin graph.nodeCount)
    (T F : Finset (Channel n)) (channel : Channel n) :
    (slot graph root T F channel).length = 1 := by
  unfold slot
  split
  · rfl
  · split <;> rfl

@[simp] theorem slots_length (graph : DAG n) (root : Fin graph.nodeCount)
    (T F : Finset (Channel n)) : (slots graph root T F).length = n := by
  simp [slots]

@[simp] theorem slots_literals (graph : DAG n) (root : Fin graph.nodeCount)
    (T F : Finset (Channel n)) : (slots graph root T F).flatten.length = n := by
  simp [List.length_flatten, slots, List.map_map, Function.comp_def]

theorem slot_holds_iff (graph : DAG n) (root : Fin graph.nodeCount)
    (T F : Finset (Channel n)) (consistent : Disjoint T F)
    (assignment : graph.ZeroVar → Bool) (negative : assignment (.inr root) = false)
    (channel : Channel n) :
    ClauseHolds assignment (slot graph root T F channel) ↔
      (channel ∈ T → assignment (.inl channel) = true) ∧
      (channel ∈ F → assignment (.inl channel) = false) := by
  by_cases positive : channel ∈ T
  · have notFalse : channel ∉ F := fun member =>
      Finset.disjoint_left.mp consistent positive member
    simp [slot, positive, notFalse, ClauseHolds, LiteralHolds]
  · by_cases fixedFalse : channel ∈ F <;>
      simp [slot, positive, fixedFalse, ClauseHolds, LiteralHolds, negative]

theorem slots_holds_iff (graph : DAG n) (root : Fin graph.nodeCount)
    (T F : Finset (Channel n)) (consistent : Disjoint T F)
    (assignment : graph.ZeroVar → Bool) (negative : assignment (.inr root) = false) :
    (∀ clause ∈ slots graph root T F, ClauseHolds assignment clause) ↔
      (∀ channel ∈ T, assignment (.inl channel) = true) ∧
      (∀ channel ∈ F, assignment (.inl channel) = false) := by
  simp only [slots, List.forall_mem_map, List.mem_finRange, forall_true_left,
    slot_holds_iff graph root T F consistent assignment negative]
  exact forall_and

def rawFormula (graph : DAG n) (b : Nat) (target : Channel n)
    (root : Fin graph.nodeCount) (T F : Finset (Channel n)) : Formula graph.ZeroVar :=
  ofClauses (((graph.forwardClauses ++ graph.channelClauses b target ∅ ∅) ++
    [ZeroSystem.implicationClause (.inr root) []]) ++ slots graph root T F)

theorem raw_satisfies_iff (graph : DAG n) (b : Nat) (target : Channel n)
    (root : Fin graph.nodeCount) (T F : Finset (Channel n))
    (consistent : Disjoint T F) (assignment : graph.ZeroVar → Bool) :
    Satisfies assignment (rawFormula graph b target root T F) ↔
      Satisfies assignment (graph.zeroSystem b target root T F) := by
  have trueHolds (U : Finset (Channel n)) :
      (∀ clause ∈ graph.trueUnitClauses U, ClauseHolds assignment clause) ↔
        ∀ channel ∈ U, assignment (.inl channel) = true := by
    simp only [trueUnitClauses, List.forall_mem_map, List.forall_mem_filter]
    simp [ZeroSystem.positiveClause, ClauseHolds, LiteralHolds]
  have falseHolds (U : Finset (Channel n)) :
      (∀ clause ∈ graph.falseUnitClauses U, ClauseHolds assignment clause) ↔
        ∀ channel ∈ U, assignment (.inl channel) = false := by
    simp only [falseUnitClauses, List.forall_mem_map, List.forall_mem_filter]
    simp [ZeroSystem.implicationClause, ZeroSystem.positiveClause, ClauseHolds, LiteralHolds]
  have channels : (∀ clause ∈ graph.channelClauses b target T F, ClauseHolds assignment clause) ↔
      (∀ clause ∈ graph.channelClauses b target ∅ ∅, ClauseHolds assignment clause) ∧
        (∀ channel ∈ T, assignment (.inl channel) = true) ∧
        (∀ channel ∈ F, assignment (.inl channel) = false) := by
    simp only [channelClauses, List.forall_mem_append, trueHolds, falseHolds]
    simp [and_assoc]
  have rootHolds : ClauseHolds assignment (ZeroSystem.implicationClause (.inr root) []) ↔
      assignment (.inr root) = false := by
    simp [ZeroSystem.implicationClause, ZeroSystem.positiveClause, ClauseHolds, LiteralHolds]
  simp only [rawFormula, zeroSystem, satisfies_ofClauses, List.forall_mem_append,
    List.forall_mem_singleton, rootHolds]
  by_cases negative : assignment (.inr root) = false
  · rw [slots_holds_iff graph root T F consistent assignment negative]
    rw [channels]
    simp [negative, and_assoc]
  · simp [negative]

def formula (graph : DAG n) (b : Nat) (target : Channel n)
    (root : Fin graph.nodeCount) (T F : Finset (Channel n)) :
    FiniteFormula (n + graph.nodeCount) :=
  ofClauses (SharedZeroTemplate.touchRows (n + graph.nodeCount) ++
    (relabel graph.zeroIndex (rawFormula graph b target root T F)).clauses.toList)

theorem satisfies_iff (graph : DAG n) (b : Nat) (target : Channel n)
    (root : Fin graph.nodeCount) (T F : Finset (Channel n))
    (consistent : Disjoint T F) (assignment : Fin (n + graph.nodeCount) → Bool) :
    Satisfies assignment (formula graph b target root T F) ↔
      Satisfies assignment (SharedZeroTemplate.formula graph b target root T F) := by
  have touched : ∀ clause ∈ SharedZeroTemplate.touchRows (n + graph.nodeCount),
      ClauseHolds assignment clause := by
    intro clause member
    obtain ⟨coordinate, _, rfl⟩ := List.mem_map.mp member
    exact SharedZeroTemplate.touch_holds assignment coordinate
  rw [SharedZeroTemplate.satisfies_iff]
  change Satisfies assignment (formula graph b target root T F) ↔
    Satisfies assignment (relabel graph.zeroIndex (graph.zeroSystem b target root T F))
  rw [satisfies_relabel, ← raw_satisfies_iff graph b target root T F consistent]
  rw [formula, satisfies_ofClauses, List.forall_mem_append]
  constructor
  · intro holds
    exact (satisfies_relabel graph.zeroIndex assignment _).mp
      (fun clause member => holds.2 clause (by simpa using member))
  · intro holds
    refine ⟨touched, ?_⟩
    have renamed := (satisfies_relabel graph.zeroIndex assignment _).mpr holds
    exact fun clause member => renamed clause (by simpa using member)

theorem satisfiable_iff (graph : DAG n) (guarded : graph.Guarded)
    (b : Nat) (target : Channel n) (root : Fin graph.nodeCount)
    (T F : Finset (Channel n)) (consistent : Disjoint T F) :
    Satisfiable (formula graph b target root T F) ↔
      ∃ K, Admissible b target K ∧ ExtendsFixed T F K ∧
        graph.eval (assignmentOfSet K) root = false := by
  have preserved : Satisfiable (formula graph b target root T F) ↔
      Satisfiable (SharedZeroTemplate.formula graph b target root T F) :=
    exists_congr (satisfies_iff graph b target root T F consistent)
  rw [preserved]
  exact SharedZeroTemplate.satisfiable_iff graph guarded b target root T F

/-- Baseline masks include the forced target; the admissibility clause already
requires that same target, so selecting slots from those masks is exact. -/
theorem baseline_satisfiable_iff (graph : DAG n) (guarded : graph.Guarded)
    (b : Nat) (target : Channel n) (root : Fin graph.nodeCount)
    (T F : Finset (Channel n))
    (consistent : FixedConsistent (extensionBase b target T) F) :
    Satisfiable (formula graph b target root (extensionBase b target T) F) ↔
      ∃ K, Admissible b target K ∧ ExtendsFixed T F K ∧
        graph.eval (assignmentOfSet K) root = false := by
  rw [satisfiable_iff graph guarded b target root _ F consistent]
  constructor
  · rintro ⟨K, eligible, fixed, zero⟩
    exact ⟨K, eligible, (extensionBase_extends b target T F K fixed).1, zero⟩
  · rintro ⟨K, eligible, fixed, zero⟩
    exact ⟨K, eligible, admissible_extensionBase b target T F K eligible fixed, zero⟩

theorem raw_rows_length (graph : DAG n) (b : Nat) (target : Channel n)
    (root : Fin graph.nodeCount) (T F : Finset (Channel n)) :
    (rawFormula graph b target root T F).clauses.size =
      graph.forwardClauses.length + (graph.channelClauses b target ∅ ∅).length + 1 + n := by
  simp [rawFormula, ofClauses]
  omega

theorem raw_literals (graph : DAG n) (b : Nat) (target : Channel n)
    (root : Fin graph.nodeCount) (T F : Finset (Channel n)) :
    GuardedZeroSize.literalCount (rawFormula graph b target root T F).clauses.toList =
      GuardedZeroSize.literalCount graph.forwardClauses +
        GuardedZeroSize.literalCount (graph.channelClauses b target ∅ ∅) + 1 + n := by
  simp [rawFormula, ofClauses,
    GuardedZeroSize.literalCount, ZeroSystem.implicationClause, ZeroSystem.positiveClause,
    slots, List.map_map, Function.comp_def]
  omega

theorem raw_dualHorn (graph : DAG n) (guarded : graph.Guarded)
    (b : Nat) (target : Channel n) (root : Fin graph.nodeCount)
    (T F : Finset (Channel n)) : Horn.DualHorn (rawFormula graph b target root T F) := by
  intro clause member
  have rows : clause ∈ ((graph.forwardClauses ++ graph.channelClauses b target ∅ ∅) ++
      [ZeroSystem.implicationClause (.inr root) []]) ++ slots graph root T F := by
    simpa [rawFormula, ofClauses] using member
  rcases List.mem_append.mp rows with base | fixed
  · exact graph.zeroSystem_dualHorn guarded b target root ∅ ∅ clause
      (by simpa [zeroSystem, ofClauses] using base)
  · obtain ⟨channel, _, rfl⟩ := List.mem_map.mp fixed
    have singleton : ∃ literal, slot graph root T F channel = [literal] := by
      unfold slot
      split
      · exact ⟨_, rfl⟩
      · split <;> exact ⟨_, rfl⟩
    obtain ⟨literal, equation⟩ := singleton
    rw [equation]
    right
    intro left leftMember right rightMember _ _
    exact congrArg Prod.fst ((List.mem_singleton.mp leftMember).trans
      (List.mem_singleton.mp rightMember).symm)

theorem dualHorn (graph : DAG n) (guarded : graph.Guarded)
    (b : Nat) (target : Channel n) (root : Fin graph.nodeCount)
    (T F : Finset (Channel n)) : Horn.DualHorn (formula graph b target root T F) := by
  intro clause member
  have rows : clause ∈ SharedZeroTemplate.touchRows (n + graph.nodeCount) ++
      (relabel graph.zeroIndex (rawFormula graph b target root T F)).clauses.toList := by
    simpa [formula, ofClauses] using member
  rcases List.mem_append.mp rows with touched | original
  · obtain ⟨coordinate, _, rfl⟩ := List.mem_map.mp touched
    exact ZeroSystem.implicationClause_dualHorn coordinate [coordinate]
  · exact SparseFormula.relabel_dualHorn graph.zeroIndex _ (raw_dualHorn graph guarded b target root T F)
      clause (by simpa using original)

theorem every_coordinate (graph : DAG n) (b : Nat) (target : Channel n)
    (root : Fin graph.nodeCount) (T F : Finset (Channel n))
    (coordinate : Fin (n + graph.nodeCount)) :
    [(coordinate, false), (coordinate, true)] ∈ (formula graph b target root T F).clauses := by
  simp only [formula, ofClauses, List.mem_toArray, List.mem_append]
  exact Or.inl (List.mem_map.mpr ⟨coordinate, List.mem_finRange coordinate, rfl⟩)

theorem input_size_eq (graph : DAG n) (b : Nat) (target : Channel n)
    (root : Fin graph.nodeCount) (T F : Finset (Channel n)) :
    Horn.inputSize (formula graph b target root T F) =
      Horn.inputSize (SharedZeroTemplate.formula graph b target root ∅ ∅) + 2 * n := by
  simp [Horn.inputSize, formula, SharedZeroTemplate.formula, finiteZeroSystem,
    relabel, Controller.CNF.OrderedFormula.relabel, Controller.CNF.OrderedFormula.Clause.relabel,
    rawFormula, zeroSystem, ofClauses, slots, List.map_map, Function.comp_def,
    ZeroSystem.implicationClause, ZeroSystem.positiveClause]
  omega

theorem input_size_bound (graph : DAG n) (b : Nat) (target : Channel n)
    (root : Fin graph.nodeCount) (T F : Finset (Channel n)) :
    Horn.inputSize (formula graph b target root T F) ≤ 13 * (graph.countedSize + 1) := by
  have base := SharedZeroTemplate.input_size_bound graph b target root ∅ ∅
  have size := graph.countedSize_eq
  rw [input_size_eq]
  omega

end Controller.Cost.EnumerationSlots
