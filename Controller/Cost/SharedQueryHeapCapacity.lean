module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedQueryDispatch

@[expose] public section

namespace Controller.Cost.SharedQueryHeapCapacity
open Controller.Cost.GateProgram Controller.Native Controller.Native.SourceController
open Controller.Cost.NativeSourceExecution Controller.Cost.NativeCircuitExecution Controller.Decoder
open Controller.Cost.SharedMachineCapacity Controller.Cost.ForestZeroAdmissibleCaller
open Controller.Cost.ForestZeroCompile

theorem constructor_room (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels)) (root : Fin graph.nodeCount)
    (heap : Array (Word (wordWidth retained graph.countedSize (selectedSize parameters).total)))
    (layout : ForestZeroDictionary.Layout (parameters.channels + graph.nodeCount) heap.size)
    (size : heap.size ≤ retained) :
    let references := SharedZeroSource.references graph parameters.buses parameters.bridge.target T F base slot root
    heap.size + 5 + 2 * (references.length + 1) + 2 * references.flatten.length +
      2 * (parameters.channels + graph.nodeCount) <
      2 ^ wordWidth retained graph.countedSize (selectedSize parameters).total := by
  intro references
  have occurrences := SharedZeroSource.occurrence_bound (base := base) (slot := slot)
    graph parameters.buses parameters.bridge.target T F root
  have room := capacity retained graph.countedSize (selectedSize parameters).total
  have ambientBound := layout.tableBound
  change references.length + references.flatten.length ≤ 11 * (graph.countedSize + 1) at occurrences
  omega

theorem scratch_room (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels)) (root : Fin graph.nodeCount)
    (heap : Array (Word (wordWidth retained graph.countedSize (selectedSize parameters).total)))
    (layout : ForestZeroDictionary.Layout (parameters.channels + graph.nodeCount) heap.size)
    (size : heap.size ≤ retained) :
    let references := SharedZeroSource.references graph parameters.buses parameters.bridge.target T F coordinateBase slot root
    let dictionary := constructorDictionary heap layout (empty _) references
    let clauses := constructorClauses heap layout (empty _) (empty_coherent _) references parameters.channels (by omega)
    let start := (constructorHeap heap layout (empty _) references parameters.channels).size +
      5 * dictionary.coordinates.size + 4
    start + 3 * clauses.length + (clauses.map List.length).sum +
      2 * (Controller.Horn.IndexScan.occurrences clauses start).length <
      2 ^ wordWidth retained graph.countedSize (selectedSize parameters).total := by
  intro references dictionary clauses start
  have heapBound := constructor_heap_local_bound heap layout (empty _) (empty_coherent _) references
    parameters.channels (by omega)
  have rowsEq := constructorClauses_length heap layout (empty _) (empty_coherent _) references
    parameters.channels (by omega)
  have rowsBound : clauses.length ≤ references.length + 1 := by
    change (constructorClauses heap layout (empty _) (empty_coherent _) references parameters.channels (by omega)).length ≤ _
    rw [rowsEq]
    split_ifs <;> omega
  have literalsBound := constructorClauses_profile_bound heap layout (empty _) (empty_coherent _) references
    parameters.channels (by omega)
  have incidenceBound := source_incidence_bound clauses start
  have occurrences := SharedZeroSource.occurrence_bound (base := coordinateBase) (slot := slot)
    graph parameters.buses parameters.bridge.target T F root
  have count : dictionary.coordinates.size = parameters.channels + graph.nodeCount :=
    SharedZeroSource.dictionary_size graph parameters.buses parameters.bridge.target T F root heap layout
  have room := capacity retained graph.countedSize (selectedSize parameters).total
  have graphSize := graph.countedSize_eq
  change (clauses.map List.length).sum ≤ references.flatten.length + dictionary.coordinates.size at literalsBound
  change references.length + references.flatten.length ≤ 11 * (graph.countedSize + 1) at occurrences
  change (constructorHeap heap layout (empty _) references parameters.channels).size ≤
    heap.size + 7 + 2 * references.length + 2 * references.flatten.length +
      2 * dictionary.coordinates.size at heapBound
  dsimp only [start] at incidenceBound ⊢
  omega

theorem native_code_bound (parameters : Parameters) (width base entry : Nat) :
    (NativeRetainedExecution.code parameters width base entry).length ≤
      31 * (selectedSize parameters).total := by
  have roots := (sourceCircuit parameters).roots_le
  have channelBound : parameters.channels ≤ SourceInitialIDs.rootCount parameters := by
    simp only [SourceInitialIDs.rootCount]
    omega
  have variableBound : (compile parameters).toState.count ≤ (selectedSize parameters).total := by
    simp only [selectedSize, NativeSize.total]
    omega
  have rootBound := NativeRetainedExecution.source_code_bound parameters width base entry
  have circuitBound := NativeSourceExecution.code_length_le parameters width (base + parameters.channels)
    (NativeRetainedExecution.circuitEntry parameters width base entry)
  rw [NativeRetainedExecution.code_length]
  change 2 * parameters.channels + (NativeRetainedExecution.rootCode parameters width base entry).length +
    (NativeCircuitExecution.code width (base + parameters.channels)
      (NativeRetainedExecution.circuitEntry parameters width base entry) (sourceCircuit parameters)).length ≤ _
  omega

set_option maxRecDepth 4096 in
theorem code_length_bound (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels)) (root : Fin graph.nodeCount)
    (width entry keep localCount base nativeBase next : Nat) :
    (SharedQueryDispatch.code parameters width entry keep localCount base nativeBase
      (SharedZeroSource.references graph parameters.buses parameters.bridge.target T F coordinateBase slot root) next).length ≤
      410 * (graph.countedSize + 1) + 34 * (selectedSize parameters).total + 512 := by
  let references := SharedZeroSource.references graph parameters.buses parameters.bridge.target T F coordinateBase slot root
  let solver := SharedQuerySourceCode.solverEntry width entry keep references
  have sourceBound := SharedZeroSource.constructor_code_bound (width := width) (entry := entry + 15)
    (protectedEnd := keep) (recordHeader := keep) (endHeader := keep + 4)
    (returnPC := solver) (base := coordinateBase) (slot := slot)
    graph parameters.buses parameters.bridge.target T F root
  change (constructorCode width (entry + 15) keep keep (keep + 4)
    (SharedQuerySourceCode.solverEntry width entry keep references) references).length ≤
    410 * (graph.countedSize + 1) at sourceBound
  have prefixBound : (SharedQuerySourceCode.code width entry keep references).length ≤
      410 * (graph.countedSize + 1) + 15 := by
    unfold SharedQuerySourceCode.code
    simp only [List.length_append, List.length_map, Array.length_toList,
      ForestZeroAdmissibleCaller.reuseEntryCode, List.length_cons, List.length_nil,
      ForestZeroAdmissibleCaller.keepCode_length]
    omega
  have nativeBound := native_code_bound parameters width nativeBase
    (SharedNativeSuccessCode.nativeEntry (SharedQueryTailCode.projection (solver + 261)))
  change (SharedQueryDispatch.code parameters width entry keep localCount base nativeBase references next).length ≤ _
  unfold SharedQueryDispatch.code SharedQueryResidentCode.code SharedQuerySolverCode.code SharedQueryTailCode.code
  simp only [List.length_append, Array.length_toList, SharedSolverPrefix.code_size,
    SharedWorklistCode.code_size, SharedQueryTailCode.success, SharedNativeSuccessCode.code_length,
    SharedQueryCleanupCode.code_length, ForestZeroRootLoop.dispatchCode,
    List.length_cons, List.length_nil]
  dsimp only [solver] at nativeBound
  have variableBound : (compile parameters).toState.count ≤ (selectedSize parameters).total := by
    simp only [selectedSize, NativeSize.total]
    omega
  omega

theorem code_capacity (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels)) (root : Fin graph.nodeCount)
    (entry keep localCount base nativeBase next : Nat) (entryBound : entry ≤ retained) :
    let width := wordWidth retained graph.countedSize (selectedSize parameters).total
    entry + (SharedQueryDispatch.code parameters width entry keep localCount base nativeBase
      (SharedZeroSource.references graph parameters.buses parameters.bridge.target T F coordinateBase slot root) next).length <
      2 ^ width := by
  intro width
  have bound := code_length_bound (coordinateBase := coordinateBase) (slot := slot) parameters graph T F root
    width entry keep localCount base nativeBase next
  have room := capacity retained graph.countedSize (selectedSize parameters).total
  change 131072 * (retained + graph.countedSize + (selectedSize parameters).total + 1) < 2 ^ width at room
  omega

end Controller.Cost.SharedQueryHeapCapacity
