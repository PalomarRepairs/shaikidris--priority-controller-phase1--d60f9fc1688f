module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedQueryHeapCapacity

@[expose] public section

namespace Controller.Cost.SharedZeroResidentConditions
open Controller.Cost.ForestZeroTouch Controller.Cost.GateProgram Controller.Cost.ForestZeroCompile
open Controller.Cost.ForestZeroDictionary Controller.Cost.ForestZeroAdmissibleCaller
open Controller.Cost.ForestZeroEmit Controller.CNF Controller.Native Controller.Native.SourceController
open Controller.Decoder Controller.Cost.NativeCircuitExecution Controller.Cost.NativeSourceExecution
open Controller.Cost.SharedZeroNativeComplete Controller.Cost.SharedZeroNativeQuery
open Controller.Cost.SharedMachineCapacity

structure SourceConditions {width ambient : Nat} (parameters : Parameters) (initial : State width 8)
    (sharedLayout : Layout ambient initial.heap.size) (references : List (List (Reference ambient)))
    (sourceEnd nodes : Nat) : Prop where
  sourceReferences : ∀ reference ∈ references.flatten,
          Controller.Cost.ForestZeroEmit.StoredReference (initial.heap) parameters.channels sourceEnd reference
  sourceBeforeTable : sourceEnd ≤ (sharedLayout).tableBase
  sourceBeforeInverse : sourceEnd ≤ (sharedLayout).inverseBase
  sourceBound : sourceEnd ≤ (initial.heap).size
  sourcePositive : 0 < sourceEnd
  sourceChannel : (initial.heap)[0]? = some (word width parameters.channels)
  sourceNodes : (initial.heap)[1]? = some (word width nodes)
  ambientEq : ambient = parameters.channels + nodes
  adjacent : (sharedLayout).inverseBase = (sharedLayout).tableBase + ambient
  tablePositive : 0 < (sharedLayout).tableBase
  sourceHeaderRoom : 1 < sourceEnd
  sourceDual : Controller.Horn.DualHorn
          (ofClauses (ForestZeroAssembly.originalRows (reservedReferences references)))
  sourceEndpoint : (initial.heap).size = (sharedLayout).inverseBase + ambient

set_option maxRecDepth 4096 in
theorem conditions (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels)) (root : Fin graph.nodeCount)
    (program : Program (wordWidth retained graph.countedSize (selectedSize parameters).total) 8) (initial : State (wordWidth retained graph.countedSize (selectedSize parameters).total) 8)
    (sharedLayout : Layout (parameters.channels + graph.nodeCount) initial.heap.size)
    (coordinateBase slot sourceEnd sourceEntry nextEntry : Nat) (rest : List (Word (wordWidth retained graph.countedSize (selectedSize parameters).total)))
    (source : SourceConditions parameters initial sharedLayout (SharedZeroSource.references graph parameters.buses parameters.bridge.target T F coordinateBase slot root) sourceEnd graph.nodeCount)
    (heapBound : initial.heap.size ≤ retained) (entryBound : sourceEntry ≤ retained) :
    SharedQueryDispatch.Conditions parameters program initial sharedLayout (SharedZeroSource.references graph parameters.buses parameters.bridge.target T F coordinateBase slot root)
      sourceEnd graph.nodeCount sourceEntry rest (by omega) nextEntry := by
  refine {
    sourceReferences := source.sourceReferences
    sourceBeforeTable := source.sourceBeforeTable
    sourceBeforeInverse := source.sourceBeforeInverse
    sourceBound := source.sourceBound
    sourcePositive := source.sourcePositive
    sourceChannel := source.sourceChannel
    sourceNodes := source.sourceNodes
    ambientEq := source.ambientEq
    adjacent := source.adjacent
    tablePositive := source.tablePositive
    sourceHeaderRoom := source.sourceHeaderRoom
    sourceDual := source.sourceDual
    sourceEndpoint := source.sourceEndpoint
    constructorRoom := SharedQueryHeapCapacity.constructor_room (base := coordinateBase) (slot := slot)
      parameters graph T F root initial.heap sharedLayout heapBound
    room := by
      simpa only [constructorState, RegisterWiden.widenState, atState, constructorFormula_rows] using
        SharedQueryHeapCapacity.scratch_room (coordinateBase := coordinateBase) (slot := slot)
          parameters graph T F root initial.heap sharedLayout heapBound
    nativeHeap := SharedMachineCapacity.native_heap (base := coordinateBase) (slot := slot)
      parameters graph T F root initial.heap sharedLayout heapBound
    capacity := SharedQueryHeapCapacity.code_capacity (coordinateBase := coordinateBase) (slot := slot)
      parameters graph T F root sourceEntry initial.heap.size
      (constructorDictionary initial.heap sharedLayout (empty _) (SharedZeroSource.references graph parameters.buses parameters.bridge.target T F coordinateBase slot root)).coordinates.size
      (constructorHeap initial.heap sharedLayout (empty _) (SharedZeroSource.references graph parameters.buses parameters.bridge.target T F coordinateBase slot root) parameters.channels).size
      (nativeBase initial.heap sharedLayout (SharedZeroSource.references graph parameters.buses parameters.bridge.target T F coordinateBase slot root) parameters.channels (by omega)) nextEntry entryBound
  }

set_option maxRecDepth 4096 in
theorem execution (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels)) (root : Fin graph.nodeCount)
    (program : Program (wordWidth retained graph.countedSize (selectedSize parameters).total) 8) (initial : State (wordWidth retained graph.countedSize (selectedSize parameters).total) 8)
    (sourceHeap : Array (Word (wordWidth retained graph.countedSize (selectedSize parameters).total)))
    (sharedLayout : Layout (parameters.channels + graph.nodeCount) initial.heap.size)
    (coordinateBase slot sourceEnd sourceEntry nextEntry : Nat) (rest : List (Word (wordWidth retained graph.countedSize (selectedSize parameters).total)))
    (source : SourceConditions parameters initial sharedLayout (SharedZeroSource.references graph parameters.buses parameters.bridge.target T F coordinateBase slot root) sourceEnd graph.nodeCount)
    (heapBound : initial.heap.size ≤ retained) (entryBound : sourceEntry ≤ retained)
    (present : SharedRootRead.BlockAt program sourceEntry
      (SharedQueryDispatch.code parameters (wordWidth retained graph.countedSize (selectedSize parameters).total) sourceEntry initial.heap.size (constructorDictionary initial.heap sharedLayout (empty _) (SharedZeroSource.references graph parameters.buses parameters.bridge.target T F coordinateBase slot root)).coordinates.size (constructorHeap initial.heap sharedLayout (empty _) (SharedZeroSource.references graph parameters.buses parameters.bridge.target T F coordinateBase slot root) parameters.channels).size (nativeBase initial.heap sharedLayout (SharedZeroSource.references graph parameters.buses parameters.bridge.target T F coordinateBase slot root) parameters.channels (by omega)) (SharedZeroSource.references graph parameters.buses parameters.bridge.target T F coordinateBase slot root) nextEntry))
    (ready : QueryReady (ambient := parameters.channels + graph.nodeCount) sourceHeap
      sharedLayout.tableBase sharedLayout.inverseBase sourceEntry rest initial) :
    ∃ answer : Bool, ∃ final ticks peak,
      Execution program initial final ticks peak ∧ final.halted = answer ∧
      ticks ≤ 5000 * (graph.countedSize + 1) + (if answer then 55 * (selectedSize parameters).total else 0) ∧
      peak ≤ initial.liveWords + 200 * (graph.countedSize + 1) + 3 * (selectedSize parameters).total ∧
      (answer = true ↔ Controller.CNF.Satisfiable
        (constructorFormula initial.heap sharedLayout (empty _) (empty_coherent _) (SharedZeroSource.references graph parameters.buses parameters.bridge.target T F coordinateBase slot root)
          parameters.channels (by omega))) ∧
      (answer = true → QueryNativeWitness parameters initial.heap sharedLayout (SharedZeroSource.references graph parameters.buses parameters.bridge.target T F coordinateBase slot root) (by omega) final.output) ∧
      (answer = false → QueryReady (ambient := parameters.channels + graph.nodeCount) sourceHeap
        sharedLayout.tableBase sharedLayout.inverseBase nextEntry rest final) ∧
      final.liveWords ≤ initial.liveWords + 1 + (if answer then (compile parameters).toState.count else 0) ∧
      final.reg 4 = word (wordWidth retained graph.countedSize (selectedSize parameters).total) (if answer then 1 else 0) := by
  obtain ⟨answer, final, ticks, peak, trace, halted, pc, timeBound, spaceBound, meaning, certificate, nextReady, liveBound,
    decision⟩ :=
    SharedQueryDispatch.execution parameters program initial sourceHeap sharedLayout (SharedZeroSource.references graph parameters.buses parameters.bridge.target T F coordinateBase slot root) sourceEnd
      graph.nodeCount sourceEntry rest (by omega) nextEntry
      (conditions parameters graph T F root program initial sharedLayout coordinateBase slot sourceEnd
        sourceEntry nextEntry rest source heapBound entryBound) present ready
  have occurrences := SharedZeroSource.occurrence_bound (base := coordinateBase) (slot := slot)
    graph parameters.buses parameters.bridge.target T F root
  have graphSize := graph.countedSize_eq
  refine ⟨answer, final, ticks, peak, trace, halted, ?_, ?_, meaning, certificate, nextReady, liveBound, decision⟩
  · cases answer <;> simp only [Bool.false_eq_true, ite_false, ite_true] at timeBound ⊢ <;> omega
  · omega

end Controller.Cost.SharedZeroResidentConditions
