module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.GuardedZeroSize
public import Controller.Cost.SharedRetainedCandidates

@[expose] public section

/-! Tautological coordinate rows give zero queries a uniform declared dictionary without changing their models. -/
namespace Controller.Cost.SharedZeroTemplate
open Controller.Decoder Controller.Decoder.DAG Controller.CNF
open Controller.Decoder.ZeroSystem

def touchRows (ambient : Nat) : List (Clause (Fin ambient)) :=
  (List.finRange ambient).map (fun coordinate => [(coordinate, false), (coordinate, true)])

theorem touch_holds (assignment : Fin ambient → Bool) (coordinate : Fin ambient) :
    ClauseHolds assignment [(coordinate, false), (coordinate, true)] := by
  cases value : assignment coordinate <;> simp [ClauseHolds, LiteralHolds, value]

def formula (graph : DAG n) (b : Nat) (target : Fin n) (root : Fin graph.nodeCount)
    (T F : Finset (Fin n)) : FiniteFormula (n + graph.nodeCount) :=
  ofClauses (touchRows (n + graph.nodeCount) ++ (graph.finiteZeroSystem b target root T F).clauses.toList)

theorem satisfies_iff (graph : DAG n) (b : Nat) (target : Fin n) (root : Fin graph.nodeCount)
    (T F : Finset (Fin n)) (assignment : Fin (n + graph.nodeCount) → Bool) :
    Satisfies assignment (formula graph b target root T F) ↔
      Satisfies assignment (graph.finiteZeroSystem b target root T F) := by
  rw [formula, satisfies_ofClauses, List.forall_mem_append]
  have touched : ∀ clause ∈ touchRows (n + graph.nodeCount), ClauseHolds assignment clause := by
    intro clause member
    obtain ⟨coordinate, present, rfl⟩ := List.mem_map.mp member
    exact touch_holds assignment coordinate
  constructor
  · rintro ⟨_, holds⟩
    intro clause member
    exact holds clause (by simpa using member)
  · intro holds
    exact ⟨touched, fun clause member => holds clause (by simpa using member)⟩

theorem satisfiable_iff (graph : DAG n) (guarded : graph.Guarded) (b : Nat) (target : Fin n)
    (root : Fin graph.nodeCount) (T F : Finset (Fin n)) :
    Satisfiable (formula graph b target root T F) ↔
      ∃ K, Admissible b target K ∧ ExtendsFixed T F K ∧ graph.eval (assignmentOfSet K) root = false := by
  have preserved : Satisfiable (formula graph b target root T F) ↔
      Satisfiable (graph.finiteZeroSystem b target root T F) := by
    unfold Satisfiable
    exact exists_congr (satisfies_iff graph b target root T F)
  rw [preserved, DAG.finiteZeroSystem, satisfiable_relabel_equiv]
  exact graph.zeroSystem_satisfiable_iff guarded b target root T F

theorem dualHorn (graph : DAG n) (guarded : graph.Guarded) (b : Nat) (target : Fin n)
    (root : Fin graph.nodeCount) (T F : Finset (Fin n)) :
    Horn.DualHorn (formula graph b target root T F) := by
  intro clause member
  have rows : clause ∈ touchRows (n + graph.nodeCount) ++ (graph.finiteZeroSystem b target root T F).clauses.toList := by
    simpa [formula, ofClauses] using member
  rcases List.mem_append.mp rows with touched | original
  · obtain ⟨coordinate, present, rfl⟩ := List.mem_map.mp touched
    exact implicationClause_dualHorn coordinate [coordinate]
  · exact graph.finiteZeroSystem_dualHorn guarded b target root T F clause (by simpa using original)

theorem every_coordinate (graph : DAG n) (b : Nat) (target : Fin n) (root : Fin graph.nodeCount)
    (T F : Finset (Fin n)) (coordinate : Fin (n + graph.nodeCount)) :
    [(coordinate, false), (coordinate, true)] ∈ (formula graph b target root T F).clauses := by
  simp only [formula, ofClauses, List.mem_toArray, List.mem_append]
  exact Or.inl (List.mem_map.mpr ⟨coordinate, List.mem_finRange coordinate, rfl⟩)

@[simp] theorem touch_length (ambient : Nat) : (touchRows ambient).length = ambient := by simp [touchRows]

@[simp] theorem touch_literals (ambient : Nat) :
    GuardedZeroSize.literalCount (touchRows ambient) = 2 * ambient := by
  simp [GuardedZeroSize.literalCount, touchRows, List.map_map, Function.comp_def, Nat.mul_comm]

theorem input_size_eq (graph : DAG n) (b : Nat) (target : Fin n) (root : Fin graph.nodeCount)
    (T F : Finset (Fin n)) :
    Horn.inputSize (formula graph b target root T F) =
      Horn.inputSize (graph.finiteZeroSystem b target root T F) + 3 * (n + graph.nodeCount) := by
  simp only [Horn.inputSize, formula, ofClauses, List.size_toArray, List.length_append, touch_length,
    List.toList_toArray, List.map_append, List.sum_append]
  have literals := touch_literals (n + graph.nodeCount)
  unfold GuardedZeroSize.literalCount at literals
  rw [literals]
  simp
  omega

theorem input_size_bound (graph : DAG n) (b : Nat) (target : Fin n) (root : Fin graph.nodeCount)
    (T F : Finset (Fin n)) : Horn.inputSize (formula graph b target root T F) ≤ 11 * (graph.countedSize + 1) := by
  have previous := GuardedZeroSize.finite_input_size graph b target root T F
  have size := graph.countedSize_eq
  rw [input_size_eq]
  omega

end Controller.Cost.SharedZeroTemplate
