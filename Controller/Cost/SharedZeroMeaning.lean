module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedZeroModel

@[expose] public section

/-! The constructed finite solver formula decides admissible fixed extensions that make the queried root false. -/
namespace Controller.Cost.SharedZeroMeaning
open Controller.CNF Controller.Decoder Controller.Decoder.DAG Controller.Decoder.ZeroSystem
open Controller.Cost.ForestZeroAdmissibleCaller

theorem source_nonempty (graph : DAG n) (b : Nat) (target : Fin n) (T F : Finset (Fin n))
    (root : Fin graph.nodeCount) (assignment : Fin (n + graph.nodeCount) → Bool)
    (model : Satisfies assignment
      (ofClauses (ForestZeroAssembly.originalRows (SharedZeroSource.references graph b target T F base slot root)))) :
    ∃ channel : Fin n, assignment ⟨channel.val, by omega⟩ = true := by
  have template : Satisfies assignment (SharedZeroTemplate.formula graph b target root T F) := by
    rw [SharedZeroSource.originalRows_eq] at model
    simpa [ofClauses] using model
  have finite := (SharedZeroTemplate.satisfies_iff graph b target root T F assignment).mp template
  have source := (satisfies_relabel graph.zeroIndex assignment (graph.zeroSystem b target root T F)).mp finite
  rw [DAG.zeroSystem, satisfies_ofClauses] at source
  have member : positiveClause ((List.finRange n).map Sum.inl) ∈ graph.channelClauses b target T F := by
    simp [DAG.channelClauses]
  have positive := source _ (List.mem_append_left _ (List.mem_append_right _ member))
  obtain ⟨coordinate, member, active⟩ := (positiveClause_holds _ _).mp positive
  obtain ⟨channel, present, rfl⟩ := List.mem_map.mp member
  exact ⟨channel, by simpa [DAG.zeroIndex, Function.comp_def, Fin.castAdd, Fin.castLE] using active⟩

theorem constructor_satisfiable_iff (graph : DAG n) (guarded : graph.Guarded) (b : Nat)
    (target : Fin n) (T F : Finset (Fin n)) (root : Fin graph.nodeCount)
    (heap : Array (Word width)) (layout : ForestZeroDictionary.Layout (n + graph.nodeCount) heap.size) :
    Satisfiable (constructorFormula heap layout (ForestZeroCompile.empty _)
      (ForestZeroCompile.empty_coherent _) (SharedZeroSource.references graph b target T F base slot root)
      n (by omega)) ↔
      ∃ K, Admissible b target K ∧ ExtendsFixed T F K ∧ graph.eval (assignmentOfSet K) root = false := by
  rw [SharedZeroModel.constructor_satisfiable heap layout (ForestZeroCompile.empty _)
    (ForestZeroCompile.empty_coherent _) _ n (by omega)
    (fun assignment model => source_nonempty graph b target T F root assignment model)]
  rw [SharedZeroSource.originalRows_eq]
  have same : ofClauses (SharedZeroTemplate.formula graph b target root T F).clauses.toList =
      SharedZeroTemplate.formula graph b target root T F := by simp [ofClauses]
  rw [same]
  exact SharedZeroTemplate.satisfiable_iff graph guarded b target root T F

end Controller.Cost.SharedZeroMeaning
