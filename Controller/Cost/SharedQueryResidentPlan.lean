module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedQueryResidentCode

@[expose] public section

namespace Controller.Cost.SharedQueryResidentPlan
open Controller.Cost.ForestZeroTouch Controller.Cost.GateProgram Controller.Cost.ForestZeroCompile
open Controller.Cost.ForestZeroDictionary Controller.Cost.ForestZeroAdmissibleCaller
open Controller.Cost.ForestZeroEmit Controller.CNF Controller.Native Controller.Native.SourceController
open Controller.Decoder Controller.Cost.NativeCircuitExecution Controller.Cost.NativeSourceExecution
open Controller.Cost.SharedZeroNativeComplete Controller.Cost.SharedZeroNativeQuery

structure Conditions {width ambient : Nat}
    (parameters : Parameters) (program : Program width 8) (initial : State width 8)
    (sharedLayout : Layout ambient initial.heap.size)
    (references : List (List (Reference ambient))) (sourceEnd nodes sourceEntry : Nat)
    (rest : List (Word width)) (within : parameters.channels ≤ ambient)
    (dispatchEntry nextEntry : Nat) : Prop where
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
  constructorRoom : (initial.heap).size + 5 + 2 * (references.length + 1) +
          2 * references.flatten.length + 2 * ambient < 2 ^ width
  room : (constructorState initial.heap sharedLayout (ForestZeroCompile.empty ambient) references parameters.channels (SharedQuerySourceCode.solverEntry width sourceEntry initial.heap.size references) (word width initial.heap.size :: rest) initial.output initial.reg).heap.size + 5 * (constructorDictionary initial.heap sharedLayout (ForestZeroCompile.empty ambient) references).coordinates.size + 4 +
          3 * (constructorFormula initial.heap sharedLayout (ForestZeroCompile.empty ambient) (ForestZeroCompile.empty_coherent ambient) references parameters.channels within).clauses.toList.length + ((constructorFormula initial.heap sharedLayout (ForestZeroCompile.empty ambient) (ForestZeroCompile.empty_coherent ambient) references parameters.channels within).clauses.toList.map List.length).sum +
          2 * (Controller.Horn.IndexScan.occurrences (constructorFormula initial.heap sharedLayout (ForestZeroCompile.empty ambient) (ForestZeroCompile.empty_coherent ambient) references parameters.channels within).clauses.toList ((constructorHeap initial.heap sharedLayout (ForestZeroCompile.empty ambient) references parameters.channels).size + 5 * (constructorDictionary initial.heap sharedLayout (ForestZeroCompile.empty ambient) references).coordinates.size + 4)).length < 2 ^ width
  nativeHeap : (nativeBase initial.heap sharedLayout references parameters.channels within) + parameters.channels + (compile parameters).toState.count < 2 ^ width
  dispatchEq : ((SharedQueryTailCode.cleanup parameters width (nativeBase initial.heap sharedLayout references parameters.channels within) ((SharedQuerySourceCode.solverEntry width sourceEntry initial.heap.size references) + 261)) + 7) + 28 = dispatchEntry
  dispatchCapacity : dispatchEntry + 2 < 2 ^ width
  dispatchAt : ∀ phase : Fin 2, program[dispatchEntry + phase.val]? =
    (ForestZeroRootLoop.dispatchCode width nextEntry)[phase.val]?
  residentCapacity : sourceEntry + (SharedQueryResidentCode.code parameters width sourceEntry initial.heap.size (constructorDictionary initial.heap sharedLayout (ForestZeroCompile.empty ambient) references).coordinates.size (constructorHeap initial.heap sharedLayout (ForestZeroCompile.empty ambient) references parameters.channels).size (nativeBase initial.heap sharedLayout references parameters.channels within) references).length < 2 ^ width

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
def of_resident {width ambient : Nat}
    (parameters : Parameters) (program : Program width 8) (initial : State width 8)
    (sharedLayout : Layout ambient initial.heap.size)
    (references : List (List (Reference ambient))) (sourceEnd nodes sourceEntry : Nat)
    (rest : List (Word width)) (within : parameters.channels ≤ ambient)
    (dispatchEntry nextEntry : Nat)
    (conditions : Conditions parameters program initial sharedLayout references sourceEnd nodes sourceEntry rest within dispatchEntry nextEntry)
    (present : SharedRootRead.BlockAt program sourceEntry (SharedQueryResidentCode.code parameters width sourceEntry initial.heap.size (constructorDictionary initial.heap sharedLayout (ForestZeroCompile.empty ambient) references).coordinates.size (constructorHeap initial.heap sharedLayout (ForestZeroCompile.empty ambient) references parameters.channels).size (nativeBase initial.heap sharedLayout references parameters.channels within) references)) :
    SourceQueryPlan parameters program initial sharedLayout references sourceEnd nodes sourceEntry rest within dispatchEntry nextEntry := by
  have physical := SharedQueryResidentCode.physical_at parameters program sourceEntry initial.heap.size
    (constructorDictionary initial.heap sharedLayout (ForestZeroCompile.empty ambient) references).coordinates.size (constructorHeap initial.heap sharedLayout (ForestZeroCompile.empty ambient) references parameters.channels).size (nativeBase initial.heap sharedLayout references parameters.channels within) references present
  have solverBlock := (SharedQueryResidentCode.blocks_at parameters program sourceEntry initial.heap.size
    (constructorDictionary initial.heap sharedLayout (ForestZeroCompile.empty ambient) references).coordinates.size (constructorHeap initial.heap sharedLayout (ForestZeroCompile.empty ambient) references parameters.channels).size (nativeBase initial.heap sharedLayout references parameters.channels within) references present).2
  have preludeProof := SharedNativeSuccessCode.prelude_at parameters program (nativeBase initial.heap sharedLayout references parameters.channels within)
    ((SharedQuerySourceCode.solverEntry width sourceEntry initial.heap.size references) + 395) ((SharedQueryTailCode.cleanup parameters width (nativeBase initial.heap sharedLayout references parameters.channels within) ((SharedQuerySourceCode.solverEntry width sourceEntry initial.heap.size references) + 261)) + 7) physical.solver.tail.success
  have nativeCleanup := SharedNativeSuccessCode.cleanup_at parameters program (nativeBase initial.heap sharedLayout references parameters.channels within)
    ((SharedQuerySourceCode.solverEntry width sourceEntry initial.heap.size references) + 395) ((SharedQueryTailCode.cleanup parameters width (nativeBase initial.heap sharedLayout references parameters.channels within) ((SharedQuerySourceCode.solverEntry width sourceEntry initial.heap.size references) + 261)) + 7) physical.solver.tail.success
  have endpoint := SharedQueryResidentCode.code_end parameters width sourceEntry initial.heap.size
    (constructorDictionary initial.heap sharedLayout (ForestZeroCompile.empty ambient) references).coordinates.size (constructorHeap initial.heap sharedLayout (ForestZeroCompile.empty ambient) references parameters.channels).size (nativeBase initial.heap sharedLayout references parameters.channels within) references
  have endRoom : (SharedQueryTailCode.cleanup parameters width (nativeBase initial.heap sharedLayout references parameters.channels within) ((SharedQuerySourceCode.solverEntry width sourceEntry initial.heap.size references) + 261)) + 35 < 2 ^ width := by
    rw [← endpoint]
    exact conditions.residentCapacity
  have sourceBefore : sourceEntry + 15 ≤ (SharedQuerySourceCode.solverEntry width sourceEntry initial.heap.size references) := by
    unfold SharedQuerySourceCode.solverEntry
    omega
  have constructorEnd : sourceEntry + 15 +
      (constructorCode width (sourceEntry + 15) initial.heap.size initial.heap.size
        (initial.heap.size + 4) (SharedQuerySourceCode.solverEntry width sourceEntry initial.heap.size references) references).length = (SharedQuerySourceCode.solverEntry width sourceEntry initial.heap.size references) := by
    simp only [constructorCode, List.length_append, ForestZeroAdmissibleCaller.code_length,
      SharedQuerySourceCode.solverEntry]
    omega
  have cleanupFormula : (SharedQueryTailCode.cleanup parameters width (nativeBase initial.heap sharedLayout references parameters.channels within) ((SharedQuerySourceCode.solverEntry width sourceEntry initial.heap.size references) + 261)) = (SharedQuerySourceCode.solverEntry width sourceEntry initial.heap.size references) + 395 +
      (NativeRetainedExecution.code parameters width (nativeBase initial.heap sharedLayout references parameters.channels within) ((SharedQuerySourceCode.solverEntry width sourceEntry initial.heap.size references) + 438)).length +
      3 * (compile parameters).toState.count + 65 := by
    simp only [SharedQueryTailCode.cleanup, SharedQueryTailCode.projection,
      SharedNativeSuccessCode.nativeEntry, Nat.add_assoc, Nat.reduceAdd]
  have doneEnd : SharedNativeSuccessCode.done parameters width (nativeBase initial.heap sharedLayout references parameters.channels within) ((SharedQuerySourceCode.solverEntry width sourceEntry initial.heap.size references) + 395) + 15 = (SharedQueryTailCode.cleanup parameters width (nativeBase initial.heap sharedLayout references parameters.channels within) ((SharedQuerySourceCode.solverEntry width sourceEntry initial.heap.size references) + 261)) := by
    simp only [SharedNativeSuccessCode.done, SharedNativeSuccessCode.outputEntry,
      emitEntry, SharedNativeSuccessCode.nativeEntry, SharedQueryTailCode.cleanup,
      SharedQueryTailCode.projection, Nat.add_assoc, Nat.reduceAdd]
    omega
  have constructorRoom := conditions.constructorRoom
  have ambientFits : ambient + 1 < 2 ^ width := by omega
  have dictionaryCoherent := (ForestZeroCompile.rows_dictionary (ForestZeroCompile.empty ambient)
    (ForestZeroCompile.empty_coherent ambient)
    (ForestZeroAssembly.originalRows (reservedReferences references))).1
  have localBound := ForestZeroDictionary.count_le_ambient
    (constructorDictionary initial.heap sharedLayout (ForestZeroCompile.empty ambient) references)
    dictionaryCoherent
  have actualRoom := conditions.room
  simp only [constructorState, RegisterWiden.widenState, atState] at actualRoom
  refine {
    sourceReferences := conditions.sourceReferences
    sourceBeforeTable := conditions.sourceBeforeTable
    sourceBeforeInverse := conditions.sourceBeforeInverse
    sourceBound := conditions.sourceBound
    sourcePositive := conditions.sourcePositive
    sourceChannel := conditions.sourceChannel
    sourceNodes := conditions.sourceNodes
    ambientEq := conditions.ambientEq
    adjacent := conditions.adjacent
    tablePositive := conditions.tablePositive
    sourceHeaderRoom := conditions.sourceHeaderRoom
    sourceDual := conditions.sourceDual
    constructorEntry := (sourceEntry + 15)
    entry := (SharedQuerySourceCode.solverEntry width sourceEntry initial.heap.size references)
    entryEq := by omega
    sourceEndpoint := conditions.sourceEndpoint
    entryCapacity := by omega
    entryAt := by simpa only [SharedNativeSuccessCode.outputEntry, SharedNativeSuccessCode.nativeEntry, SharedQueryTailCode.projection, Nat.add_assoc, Nat.reduceAdd] using physical.source.reuse
    keepAt := by simpa only [SharedNativeSuccessCode.outputEntry, SharedNativeSuccessCode.nativeEntry, SharedQueryTailCode.projection, Nat.add_assoc, Nat.reduceAdd] using physical.source.saved
    cursorAt := by simpa only [SharedNativeSuccessCode.outputEntry, SharedNativeSuccessCode.nativeEntry, SharedQueryTailCode.projection, Nat.add_assoc, Nat.reduceAdd] using physical.source.cursor
    constructorRoom := conditions.constructorRoom
    ambientFits := ambientFits
    constructorCapacity := by omega
    constructorAt := by simpa only [SharedNativeSuccessCode.outputEntry, SharedNativeSuccessCode.nativeEntry, SharedQueryTailCode.projection, Nat.add_assoc, Nat.reduceAdd] using physical.source.constructor
    scan := ((SharedQuerySourceCode.solverEntry width sourceEntry initial.heap.size references) + 261)
    seedDone := ((SharedQuerySourceCode.solverEntry width sourceEntry initial.heap.size references) + 308)
    conflict := ((SharedQuerySourceCode.solverEntry width sourceEntry initial.heap.size references) + 382)
    countAt := by simpa only [SharedNativeSuccessCode.outputEntry, SharedNativeSuccessCode.nativeEntry, SharedQueryTailCode.projection, Nat.add_assoc, Nat.reduceAdd] using physical.solver.prepared.count
    allocateAt := by simpa only [SharedNativeSuccessCode.outputEntry, SharedNativeSuccessCode.nativeEntry, SharedQueryTailCode.projection, Nat.add_assoc, Nat.reduceAdd] using physical.solver.prepared.allocate
    headersAt := by simpa only [SharedNativeSuccessCode.outputEntry, SharedNativeSuccessCode.nativeEntry, SharedQueryTailCode.projection, Nat.add_assoc, Nat.reduceAdd] using physical.solver.prepared.headers
    endpointAt := by simpa only [SharedNativeSuccessCode.outputEntry, SharedNativeSuccessCode.nativeEntry, SharedQueryTailCode.projection, Nat.add_assoc, Nat.reduceAdd] using physical.solver.prepared.endpoint
    saveAt := by simpa only [SharedNativeSuccessCode.outputEntry, SharedNativeSuccessCode.nativeEntry, SharedQueryTailCode.projection, Nat.add_assoc, Nat.reduceAdd] using physical.solver.prepared.saved
    normalizerAt := by
      exact SharedQuerySolverCode.normalizer_at parameters program (SharedQuerySourceCode.solverEntry width sourceEntry initial.heap.size references) (nativeBase initial.heap sharedLayout references parameters.channels within)
        (constructorFormula initial.heap sharedLayout (ForestZeroCompile.empty ambient)
          (ForestZeroCompile.empty_coherent ambient) references parameters.channels within).clauses.toList
        (constructorFormulaBackend initial.heap sharedLayout (ForestZeroCompile.empty ambient)
          (ForestZeroCompile.empty_coherent ambient) references parameters.channels within) solverBlock
    indexSaveAt := by simpa only [SharedNativeSuccessCode.outputEntry, SharedNativeSuccessCode.nativeEntry, SharedQueryTailCode.projection, Nat.add_assoc, Nat.reduceAdd] using physical.solver.prepared.indexSave
    indexAt := by simpa only [SharedNativeSuccessCode.outputEntry, SharedNativeSuccessCode.nativeEntry, SharedQueryTailCode.projection, Nat.add_assoc, Nat.reduceAdd] using physical.solver.prepared.index
    indexRestoreAt := by simpa only [SharedNativeSuccessCode.outputEntry, SharedNativeSuccessCode.nativeEntry, SharedQueryTailCode.projection, Nat.add_assoc, Nat.reduceAdd] using physical.solver.prepared.indexRestore
    captureAt := by simpa only [SharedNativeSuccessCode.outputEntry, SharedNativeSuccessCode.nativeEntry, SharedQueryTailCode.projection, Nat.add_assoc, Nat.reduceAdd] using physical.solver.prepared.capture
    fullCapacity := by omega
    setupAt := by simpa only [SharedNativeSuccessCode.outputEntry, SharedNativeSuccessCode.nativeEntry, SharedQueryTailCode.projection, Nat.add_assoc, Nat.reduceAdd] using physical.solver.prepared.seed
    scanAt := by simpa only [SharedNativeSuccessCode.outputEntry, SharedNativeSuccessCode.nativeEntry, SharedQueryTailCode.projection, Nat.add_assoc, Nat.reduceAdd] using physical.solver.tail.worklist.seed
    room := conditions.room
    scanCapacity := by omega
    fetch := ((SharedQuerySourceCode.solverEntry width sourceEntry initial.heap.size references) + 312)
    headAt := by simpa only [SharedNativeSuccessCode.outputEntry, SharedNativeSuccessCode.nativeEntry, SharedQueryTailCode.projection, Nat.add_assoc, Nat.reduceAdd] using physical.solver.tail.worklist.head
    headCapacity := by omega
    fifoDone := ((SharedQuerySourceCode.solverEntry width sourceEntry initial.heap.size references) + 369)
    bucket := ((SharedQuerySourceCode.solverEntry width sourceEntry initial.heap.size references) + 331)
    advance := ((SharedQuerySourceCode.solverEntry width sourceEntry initial.heap.size references) + 326)
    ready := ((SharedQuerySourceCode.solverEntry width sourceEntry initial.heap.size references) + 343)
    skip := ((SharedQuerySourceCode.solverEntry width sourceEntry initial.heap.size references) + 326)
    fetchAt := by simpa only [SharedNativeSuccessCode.outputEntry, SharedNativeSuccessCode.nativeEntry, SharedQueryTailCode.projection, Nat.add_assoc, Nat.reduceAdd] using physical.solver.tail.worklist.fetch
    advanceAt := by simpa only [SharedNativeSuccessCode.outputEntry, SharedNativeSuccessCode.nativeEntry, SharedQueryTailCode.projection, Nat.add_assoc, Nat.reduceAdd] using physical.solver.tail.worklist.advance
    loopAt := by simpa only [SharedNativeSuccessCode.outputEntry, SharedNativeSuccessCode.nativeEntry, SharedQueryTailCode.projection, Nat.add_assoc, Nat.reduceAdd] using physical.solver.tail.worklist.bucket
    readyAt := by simpa only [SharedNativeSuccessCode.outputEntry, SharedNativeSuccessCode.nativeEntry, SharedQueryTailCode.projection, Nat.add_assoc, Nat.reduceAdd] using physical.solver.tail.worklist.ready
    fetchCapacity := by omega
    advanceCapacity := by omega
    bucketCapacity := by omega
    readyCapacity := by omega
    projectionEntry := ((SharedQuerySourceCode.solverEntry width sourceEntry initial.heap.size references) + 395)
    cleanupEntry := (SharedQueryTailCode.cleanup parameters width (nativeBase initial.heap sharedLayout references parameters.channels within) ((SharedQuerySourceCode.solverEntry width sourceEntry initial.heap.size references) + 261))
    returnPc := ((SharedQueryTailCode.cleanup parameters width (nativeBase initial.heap sharedLayout references parameters.channels within) ((SharedQuerySourceCode.solverEntry width sourceEntry initial.heap.size references) + 261)) + 7)
    successAt := by simpa only [SharedNativeSuccessCode.outputEntry, SharedNativeSuccessCode.nativeEntry, SharedQueryTailCode.projection, Nat.add_assoc, Nat.reduceAdd] using physical.solver.tail.worklist.success
    conflictAt := by simpa only [SharedNativeSuccessCode.outputEntry, SharedNativeSuccessCode.nativeEntry, SharedQueryTailCode.projection, Nat.add_assoc, Nat.reduceAdd] using physical.solver.tail.worklist.conflict
    successCapacity := by omega
    conflictCapacity := by omega
    localFit := by omega
    channelsFit := by omega
    offRoom := by omega
    projectionCapacity := by omega
    constantsAt := by simpa only [SharedNativeSuccessCode.outputEntry, SharedNativeSuccessCode.nativeEntry, SharedQueryTailCode.projection, Nat.add_assoc, Nat.reduceAdd] using preludeProof.constants
    preparationAt := by simpa only [SharedNativeSuccessCode.outputEntry, SharedNativeSuccessCode.nativeEntry, SharedQueryTailCode.projection, Nat.add_assoc, Nat.reduceAdd] using preludeProof.preparation
    saveEntry := ((SharedQuerySourceCode.solverEntry width sourceEntry initial.heap.size references) + 416)
    pushEntry := ((SharedQuerySourceCode.solverEntry width sourceEntry initial.heap.size references) + 424)
    nativeEntry := ((SharedQuerySourceCode.solverEntry width sourceEntry initial.heap.size references) + 438)
    done := (SharedNativeSuccessCode.done parameters width (nativeBase initial.heap sharedLayout references parameters.channels within) ((SharedQuerySourceCode.solverEntry width sourceEntry initial.heap.size references) + 395))
    saveEq := by omega
    projectionEq := by omega
    nativeSaveAt := by simpa only [SharedNativeSuccessCode.outputEntry, SharedNativeSuccessCode.nativeEntry, SharedQueryTailCode.projection, Nat.add_assoc, Nat.reduceAdd] using preludeProof.saved
    restoreRoom := by omega
    restoreAt := by simpa only [SharedNativeSuccessCode.outputEntry, SharedNativeSuccessCode.nativeEntry, SharedQueryTailCode.projection, Nat.add_assoc, Nat.reduceAdd] using SharedNativeSuccessCode.restore_at parameters program (nativeBase initial.heap sharedLayout references parameters.channels within) ((SharedQuerySourceCode.solverEntry width sourceEntry initial.heap.size references) + 395) ((SharedQueryTailCode.cleanup parameters width (nativeBase initial.heap sharedLayout references parameters.channels within) ((SharedQuerySourceCode.solverEntry width sourceEntry initial.heap.size references) + 261)) + 7) physical.solver.tail.success
    projectionRoom := by omega
    projectionAt := by simpa only [SharedNativeSuccessCode.outputEntry, SharedNativeSuccessCode.nativeEntry, SharedQueryTailCode.projection, Nat.add_assoc, Nat.reduceAdd] using preludeProof.projection
    nativeRoom := by omega
    nativeHeap := conditions.nativeHeap
    nativeAt := by simpa only [SharedNativeSuccessCode.outputEntry, SharedNativeSuccessCode.nativeEntry, SharedQueryTailCode.projection, Nat.add_assoc, Nat.reduceAdd] using SharedNativeSuccessCode.native_at parameters program (nativeBase initial.heap sharedLayout references parameters.channels within) ((SharedQuerySourceCode.solverEntry width sourceEntry initial.heap.size references) + 395) ((SharedQueryTailCode.cleanup parameters width (nativeBase initial.heap sharedLayout references parameters.channels within) ((SharedQuerySourceCode.solverEntry width sourceEntry initial.heap.size references) + 261)) + 7) physical.solver.tail.success
    finishRoom := by simp only [emitEntry]; omega
    emitAt := by simpa only [SharedNativeSuccessCode.outputEntry, SharedNativeSuccessCode.nativeEntry, SharedQueryTailCode.projection, Nat.add_assoc, Nat.reduceAdd] using SharedNativeSuccessCode.emit_at parameters program (nativeBase initial.heap sharedLayout references parameters.channels within) ((SharedQuerySourceCode.solverEntry width sourceEntry initial.heap.size references) + 395) ((SharedQueryTailCode.cleanup parameters width (nativeBase initial.heap sharedLayout references parameters.channels within) ((SharedQuerySourceCode.solverEntry width sourceEntry initial.heap.size references) + 261)) + 7) physical.solver.tail.success
    releaseAt := by simpa only [SharedNativeSuccessCode.outputEntry, SharedNativeSuccessCode.nativeEntry, SharedQueryTailCode.projection, Nat.add_assoc, Nat.reduceAdd] using SharedNativeSuccessCode.release_at parameters program (nativeBase initial.heap sharedLayout references parameters.channels within) ((SharedQuerySourceCode.solverEntry width sourceEntry initial.heap.size references) + 395) ((SharedQueryTailCode.cleanup parameters width (nativeBase initial.heap sharedLayout references parameters.channels within) ((SharedQuerySourceCode.solverEntry width sourceEntry initial.heap.size references) + 261)) + 7) physical.solver.tail.success
    nativeSetup := by simpa only [SharedNativeSuccessCode.outputEntry, SharedNativeSuccessCode.nativeEntry, SharedQueryTailCode.projection, Nat.add_assoc, Nat.reduceAdd] using nativeCleanup.1
    nativeLoop := by simpa only [SharedNativeSuccessCode.outputEntry, SharedNativeSuccessCode.nativeEntry, SharedQueryTailCode.projection, Nat.add_assoc, Nat.reduceAdd] using nativeCleanup.2
    nativeCleanupRoom := by omega
    cleanupSetup := by simpa only [SharedNativeSuccessCode.outputEntry, SharedNativeSuccessCode.nativeEntry, SharedQueryTailCode.projection, Nat.add_assoc, Nat.reduceAdd] using physical.solver.tail.cleanup.setup
    cleanupLoop := by simpa only [SharedNativeSuccessCode.outputEntry, SharedNativeSuccessCode.nativeEntry, SharedQueryTailCode.projection, Nat.add_assoc, Nat.reduceAdd] using physical.solver.tail.cleanup.release
    cleanupCapacity := by omega
    resetCapacity := by omega
    resetPrepareAt := by simpa only [SharedNativeSuccessCode.outputEntry, SharedNativeSuccessCode.nativeEntry, SharedQueryTailCode.projection, Nat.add_assoc, Nat.reduceAdd] using physical.solver.tail.cleanup.prepare
    resetLoopAt := by simpa only [SharedNativeSuccessCode.outputEntry, SharedNativeSuccessCode.nativeEntry, SharedQueryTailCode.projection, Nat.add_assoc, Nat.reduceAdd] using physical.solver.tail.cleanup.reset
    decisionCapacity := by omega
    decisionAt := by simpa only [SharedNativeSuccessCode.outputEntry, SharedNativeSuccessCode.nativeEntry, SharedQueryTailCode.projection, Nat.add_assoc, Nat.reduceAdd] using physical.solver.tail.cleanup.decision
    dispatchEq := conditions.dispatchEq
    dispatchCapacity := conditions.dispatchCapacity
    dispatchAt := conditions.dispatchAt
  }

theorem execution {width ambient : Nat}
    (parameters : Parameters)
    (program : Program width 8) (initial : State width 8) (sourceHeap : Array (Word width))
    (sharedLayout : Layout ambient initial.heap.size)
    (references : List (List (Reference ambient))) (sourceEnd nodes sourceEntry : Nat)
    (rest : List (Word width)) (within : parameters.channels ≤ ambient) (dispatchEntry nextEntry : Nat)
    (conditions : Conditions parameters program initial sharedLayout references sourceEnd nodes sourceEntry rest within dispatchEntry nextEntry)
    (present : SharedRootRead.BlockAt program sourceEntry
      (SharedQueryResidentCode.code parameters width sourceEntry initial.heap.size
        (constructorDictionary initial.heap sharedLayout (ForestZeroCompile.empty ambient) references).coordinates.size
        (constructorHeap initial.heap sharedLayout (ForestZeroCompile.empty ambient) references parameters.channels).size
        (nativeBase initial.heap sharedLayout references parameters.channels within) references))
    (initialReady : QueryReady (ambient := ambient) sourceHeap sharedLayout.tableBase sharedLayout.inverseBase sourceEntry rest initial) :
    ∃ answer : Bool, ∃ final ticks peak,
      Execution program initial final ticks peak ∧
      final.pc = word width dispatchEntry ∧ final.halted = false ∧
      final.reg 4 = word width (if answer then 1 else 0) ∧
      ticks ≤ 150 * references.length + 387 * references.flatten.length + 483 +
        (if answer then 55 * (selectedSize parameters).total else 0) ∧
      peak ≤ initial.liveWords + 5 * references.length + 15 * references.flatten.length + parameters.channels + 3 * (selectedSize parameters).total + 28 ∧
      final.liveWords ≤ initial.liveWords + 1 + (if answer then (compile parameters).toState.count else 0) ∧
      (answer = true ↔ Controller.CNF.Satisfiable
        (constructorFormula initial.heap sharedLayout (ForestZeroCompile.empty ambient)
          (ForestZeroCompile.empty_coherent ambient) references parameters.channels within)) ∧
      (answer = true → QueryNativeWitness parameters initial.heap sharedLayout references within final.output) ∧
      (answer = false → QueryReady (ambient := ambient) sourceHeap sharedLayout.tableBase sharedLayout.inverseBase nextEntry rest
        (ForestZeroRootLoop.dispatchState final dispatchEntry nextEntry false)) ∧
      dispatchEntry + 2 < 2 ^ width ∧
      (∀ phase : Fin 2, program[dispatchEntry + phase.val]? =
        (ForestZeroRootLoop.dispatchCode width nextEntry)[phase.val]?) := by
  exact SourceQueryPlan.execute parameters program initial sourceHeap sharedLayout references sourceEnd nodes
    sourceEntry rest within dispatchEntry nextEntry
    (of_resident parameters program initial sharedLayout references sourceEnd nodes sourceEntry rest within
      dispatchEntry nextEntry conditions present) initialReady

end Controller.Cost.SharedQueryResidentPlan
