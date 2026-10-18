module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.EnumerationFixedCapacity
public import Controller.Cost.SharedZeroMeaning

@[expose] public section

/-! Graph source semantics and queried-root uniformity for the fixed runtime-slot query. -/
namespace Controller.Cost.EnumerationFixedGraph
open Controller.CNF Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.GateProgram Controller.Cost.ForestZeroEmit Controller.Cost.ForestZeroDictionary
open Controller.Cost.ForestZeroCompile Controller.Cost.ForestZeroAdmissibleCaller
open Controller.Cost.EnumerationFixedCapacity

abbrev references (parameters : Controller.Native.Parameters) (graph : DAG parameters.channels)
    (root : Fin graph.nodeCount) (T F : Finset (Fin parameters.channels)) (sourceBase rootSlot trueBase falseBase : Nat) :=
  EnumerationFixedResident.selected (baseRows parameters graph sourceBase rootSlot root)
    (slots parameters graph sourceBase rootSlot trueBase falseBase root)
    (EnumerationSlotSource.trueFlags trueBase T) (EnumerationSlotSource.falseFlags falseBase F)

theorem source_rows (parameters : Controller.Native.Parameters) (graph : DAG parameters.channels)
    (root : Fin graph.nodeCount) (T F : Finset (Fin parameters.channels)) :
    ForestZeroAssembly.originalRows (references parameters graph root T F sourceBase rootSlot trueBase falseBase) =
      (EnumerationSlots.formula graph parameters.buses parameters.bridge.target root T F).clauses.toList := by
  have selected := EnumerationSlotSource.selected_references (sourceBase := sourceBase) (rootSlot := rootSlot)
    (trueBase := trueBase) (falseBase := falseBase) root T F
  change (slots parameters graph sourceBase rootSlot trueBase falseBase root).map
      (fun slot => [EnumerationSlotBatch.chosen slot (EnumerationSlotSource.trueFlags trueBase T)
        (EnumerationSlotSource.falseFlags falseBase F)]) = _ at selected
  simp only [references, EnumerationFixedResident.selected, EnumerationFixedConstructor.references,
    EnumerationFixedProfile.selectedRefs, ForestZeroAssembly.originalRows, List.map_append]
  rw [selected]
  change ForestZeroAssembly.originalRows (baseRows parameters graph sourceBase rootSlot root) ++
    ForestZeroAssembly.originalRows (EnumerationSlotSource.references graph.nodeCount sourceBase rootSlot root T F) = _
  rw [SharedZeroSource.originalRows_eq, EnumerationSlotSource.originalRows_eq]
  simp [EnumerationSlots.formula, EnumerationSlots.rawFormula, SharedZeroTemplate.formula,
    DAG.finiteZeroSystem, DAG.zeroSystem, ofClauses, relabel, Controller.CNF.OrderedFormula.relabel,
    Controller.CNF.OrderedFormula.Clause.relabel, List.append_assoc, ZeroSystem.implicationClause]

theorem source_dual (parameters : Controller.Native.Parameters) (graph : DAG parameters.channels)
    (guarded : graph.Guarded) (root : Fin graph.nodeCount) (T F : Finset (Fin parameters.channels)) :
    Controller.Horn.DualHorn (ofClauses (ForestZeroAssembly.originalRows (reservedReferences
      (references parameters graph root T F sourceBase rootSlot trueBase falseBase)))) := by
  have dual := EnumerationSlots.dualHorn graph guarded parameters.buses parameters.bridge.target root T F
  intro clause member
  have rows : clause ∈ ForestZeroAssembly.originalRows
      (references parameters graph root T F sourceBase rootSlot trueBase falseBase) ++ [[]] := by
    simpa [ofClauses, reservedReferences, ForestZeroAssembly.originalRows] using member
  rcases List.mem_append.mp rows with original | empty
  · rw [source_rows] at original
    exact dual clause (by simpa using original)
  · have same : clause = [] := by simpa using empty
    subst clause
    simp [Controller.Horn.DualHornClause, Controller.Horn.NegativeUnique]

theorem constructor_meaning (parameters : Controller.Native.Parameters) (graph : DAG parameters.channels)
    (guarded : graph.Guarded) (root : Fin graph.nodeCount) (T F : Finset (Fin parameters.channels))
    (consistent : Disjoint T F) (heap : Array (Word width)) (layout : Layout (parameters.channels + graph.nodeCount) heap.size) :
    Satisfiable (constructorFormula heap layout (empty _) (empty_coherent _)
      (references parameters graph root T F sourceBase rootSlot trueBase falseBase) parameters.channels (by omega)) ↔
    ∃ K, Admissible parameters.buses parameters.bridge.target K ∧ ExtendsFixed T F K ∧
      graph.eval (assignmentOfSet K) root = false := by
  rw [SharedZeroModel.constructor_satisfiable heap layout (empty _) (empty_coherent _) _ parameters.channels (by omega)]
  · rw [source_rows]
    simpa [ofClauses] using
      EnumerationSlots.satisfiable_iff graph guarded parameters.buses parameters.bridge.target root T F consistent
  · intro assignment model
    have baseModel : Satisfies assignment (ofClauses
        (ForestZeroAssembly.originalRows (baseRows parameters graph sourceBase rootSlot root))) := by
      rw [satisfies_ofClauses] at model ⊢
      intro clause member
      apply model clause
      simpa only [references, EnumerationFixedResident.selected, EnumerationFixedConstructor.references,
        ForestZeroAssembly.originalRows, List.map_append] using
        (List.mem_append_left (ForestZeroAssembly.originalRows
          (EnumerationFixedProfile.selectedRefs (slots parameters graph sourceBase rootSlot trueBase falseBase root)
            (EnumerationSlotSource.trueFlags trueBase T) (EnumerationSlotSource.falseFlags falseBase F))) member)
    exact SharedZeroMeaning.source_nonempty graph parameters.buses parameters.bridge.target ∅ ∅ root assignment baseModel

private theorem base_wire (parameters : Controller.Native.Parameters) (graph : DAG parameters.channels)
    (left right : Fin graph.nodeCount) :
    List.Forall₂ SharedZeroCode.WireEqual
      (baseRows parameters graph sourceBase rootSlot left).flatten
      (baseRows parameters graph sourceBase rootSlot right).flatten := by
  simp only [baseRows, SharedZeroSource.references, List.flatten_append, List.flatten_cons, List.flatten_nil,
    List.append_nil]
  apply List.rel_append
  · exact List.forall₂_same.mpr (fun reference _ => ⟨rfl, rfl, rfl⟩)
  · exact .cons ⟨rfl, rfl, rfl⟩ .nil

theorem query_root_irrel (parameters : Controller.Native.Parameters) (graph : DAG parameters.channels)
    (left right : Fin graph.nodeCount) :
    EnumerationFixedQuery.code width entry keep (baseRows parameters graph sourceBase rootSlot left)
      (slots parameters graph sourceBase rootSlot trueBase falseBase left) =
    EnumerationFixedQuery.code width entry keep (baseRows parameters graph sourceBase rootSlot right)
      (slots parameters graph sourceBase rootSlot trueBase falseBase right) := by
  have emitAll : ∀ start, emitCode width start (baseRows parameters graph sourceBase rootSlot left).flatten =
      emitCode width start (baseRows parameters graph sourceBase rootSlot right).flatten := by
    intro start
    exact SharedZeroCode.emit_congr _ _
      (base_wire (sourceBase := sourceBase) (rootSlot := rootSlot) parameters graph left right)
  have slotAll : ∀ start, EnumerationSlotBatch.code width start
      (slots parameters graph sourceBase rootSlot trueBase falseBase left) =
      EnumerationSlotBatch.code width start (slots parameters graph sourceBase rootSlot trueBase falseBase right) := by
    intro start
    exact EnumerationSlotSource.code_root_irrel left right (List.finRange parameters.channels)
  have directoryEq : ForestZeroDirectory.code width
      (EnumerationFixedProfile.template (baseRows parameters graph sourceBase rootSlot left)
        (slots parameters graph sourceBase rootSlot trueBase falseBase left)) =
      ForestZeroDirectory.code width
      (EnumerationFixedProfile.template (baseRows parameters graph sourceBase rootSlot right)
        (slots parameters graph sourceBase rootSlot trueBase falseBase right)) := by
    apply EnumerationFixedProfile.directory_code_profile
    simp [EnumerationFixedProfile.template, ForestZeroAssembly.originalRows, baseRows, SharedZeroSource.references,
      slots, EnumerationSlotSource.slots, EnumerationSlotSource.slotsFor, List.map_map, Function.comp_def]
  have rowsEq : (baseRows parameters graph sourceBase rootSlot left).length =
      (baseRows parameters graph sourceBase rootSlot right).length := SharedZeroSource.references_length_root_irrel graph _ _ ∅ ∅ left right
  have literalsEq := (base_wire (sourceBase := sourceBase) (rootSlot := rootSlot) parameters graph left right).length_eq
  unfold EnumerationFixedQuery.code EnumerationFixedAssembly.code
    EnumerationDirectoryFrame.code EnumerationFixedEmit.code
  simp only [rowsEq, literalsEq, EnumerationSlotSource.slots_length, slots]
  rw [directoryEq]
  simp only [emitAll, slotAll]

theorem constructor_root_irrel (parameters : Controller.Native.Parameters) (graph : DAG parameters.channels)
    (left right : Fin graph.nodeCount) :
    EnumerationFixedConstructor.code width entry keep ret (baseRows parameters graph sourceBase rootSlot left)
      (slots parameters graph sourceBase rootSlot trueBase falseBase left) =
    EnumerationFixedConstructor.code width entry keep ret (baseRows parameters graph sourceBase rootSlot right)
      (slots parameters graph sourceBase rootSlot trueBase falseBase right) := by
  simp only [EnumerationFixedConstructor.code,
    query_root_irrel (sourceBase := sourceBase) (rootSlot := rootSlot) (trueBase := trueBase) (falseBase := falseBase)
      parameters graph left right]

theorem heap_size_root_irrel (parameters : Controller.Native.Parameters) (graph : DAG parameters.channels)
    (left right : Fin graph.nodeCount) :
    EnumerationFixedResident.heapSize keep parameters.channels (baseRows parameters graph sourceBase rootSlot left)
      (slots parameters graph sourceBase rootSlot trueBase falseBase left) =
    EnumerationFixedResident.heapSize keep parameters.channels (baseRows parameters graph sourceBase rootSlot right)
      (slots parameters graph sourceBase rootSlot trueBase falseBase right) := by
  unfold EnumerationFixedResident.heapSize
  rw [SharedZeroSource.references_length_root_irrel graph parameters.buses parameters.bridge.target ∅ ∅ left right,
    SharedZeroSource.references_literals_root_irrel graph parameters.buses parameters.bridge.target ∅ ∅ left right]
  simp only [slots, EnumerationSlotSource.slots_length]

theorem solver_entry_root_irrel (parameters : Controller.Native.Parameters) (graph : DAG parameters.channels)
    (left right : Fin graph.nodeCount) :
    EnumerationFixedResident.solverEntry width entry keep (baseRows parameters graph sourceBase rootSlot left)
      (slots parameters graph sourceBase rootSlot trueBase falseBase left) =
    EnumerationFixedResident.solverEntry width entry keep (baseRows parameters graph sourceBase rootSlot right)
      (slots parameters graph sourceBase rootSlot trueBase falseBase right) := by
  simp only [EnumerationFixedResident.solverEntry,
    query_root_irrel (sourceBase := sourceBase) (rootSlot := rootSlot) (trueBase := trueBase) (falseBase := falseBase)
      parameters graph left right]

theorem resident_root_irrel (parameters : Controller.Native.Parameters) (graph : DAG parameters.channels)
    (left right : Fin graph.nodeCount) :
    EnumerationFixedResident.code width entry keep parameters.channels (baseRows parameters graph sourceBase rootSlot left)
      (slots parameters graph sourceBase rootSlot trueBase falseBase left) =
    EnumerationFixedResident.code width entry keep parameters.channels (baseRows parameters graph sourceBase rootSlot right)
      (slots parameters graph sourceBase rootSlot trueBase falseBase right) := by
  unfold EnumerationFixedResident.code EnumerationFixedResident.sourceCode
  rw [solver_entry_root_irrel parameters graph left right,
    constructor_root_irrel parameters graph left right,
    heap_size_root_irrel parameters graph left right,
    SharedZeroSource.references_length_root_irrel graph parameters.buses parameters.bridge.target ∅ ∅ left right]
  simp only [slots, EnumerationSlotSource.slots_length]

end Controller.Cost.EnumerationFixedGraph
