module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedZeroNativePrepared
public import Controller.Cost.SharedZeroOutput
public import Controller.Cost.SharedNormalizationShape
public import Controller.Cost.NativeRealizedChecked

@[expose] public section

namespace Controller.Cost.SharedZeroNativeQuery
open Controller.Cost.ForestZeroTouch
open Controller.Cost.GateProgram Controller.Cost.ForestZeroCompile Controller.Cost.ForestZeroDictionary
open Controller.Cost.ForestZeroAdmissibleCaller Controller.Cost.ForestZeroEmit Controller.CNF
open Controller.Native Controller.Native.SourceController Controller.Decoder
open Controller.Cost.NativeCircuitExecution Controller.Cost.NativeSourceExecution Controller.Cost.SharedZeroNativeComplete

def nativeBase (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (references : List (List (Reference ambient))) (channels : Nat) (within : channels ≤ ambient) : Nat :=
  let dictionary := constructorDictionary heap layout (ForestZeroCompile.empty ambient) references
  let formula := constructorFormula heap layout (ForestZeroCompile.empty ambient)
    (ForestZeroCompile.empty_coherent ambient) references channels within
  let recordStart := (constructorHeap heap layout (ForestZeroCompile.empty ambient) references channels).size +
    5 * dictionary.coordinates.size + 4
  Controller.Horn.NormalizeLoop.recordOffset formula.clauses.toList recordStart formula.clauses.toList.length +
    2 * (Controller.Horn.IndexScan.occurrences formula.clauses.toList recordStart).length

structure SourceQueryPlan {width ambient : Nat}
    (parameters : Parameters)
    (program : Program width 8) (initial : State width 8)
    (sharedLayout : Layout ambient initial.heap.size)
    (references : List (List (Reference ambient))) (sourceEnd nodes sourceEntry : Nat)
    (rest : List (Word width)) (within : parameters.channels ≤ ambient)
    (dispatchEntry nextEntry : Nat) where
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
  constructorEntry : Nat
  entry : Nat
  entryEq : constructorEntry = sourceEntry + 15
  sourceEndpoint : (initial.heap).size = (sharedLayout).inverseBase + ambient
  entryCapacity : sourceEntry + 15 < 2 ^ width
  entryAt : ∀ phase : Fin 3, program[sourceEntry + phase.val]? = (reuseEntryCode width)[phase.val]?
  keepAt : ForestZeroCallerWiden.WidenedBlockAt program (sourceEntry + 3) (keepCode width)
  cursorAt : program[sourceEntry + 14]? = some (.constant 0
          (word width ((initial.heap).size + 5 + 2 * (references.length + 1))))
  constructorRoom : (initial.heap).size + 5 + 2 * (references.length + 1) +
          2 * references.flatten.length + 2 * ambient < 2 ^ width
  ambientFits : ambient + 1 < 2 ^ width
  constructorCapacity : constructorEntry +
          (constructorCode width constructorEntry (initial.heap).size (initial.heap).size ((initial.heap).size + 4) entry references).length < 2 ^ width
  constructorAt : ForestZeroCallerWiden.WidenedBlockAt program constructorEntry
          (constructorCode width constructorEntry (initial.heap).size (initial.heap).size ((initial.heap).size + 4) entry references)
  scan : Nat
  seedDone : Nat
  conflict : Nat
  countAt : ∀ phase : Fin 11, program[entry + phase.val]? = (scratchCountCode width)[phase.val]?
  allocateAt : Controller.Horn.TrackedAllocate.CodeAt program (entry + 11)
  headersAt : ∀ phase : Fin 15, program[entry + 16 + phase.val]? = (scratchHeaderCode width)[phase.val]?
  endpointAt : ∀ phase : Fin 5, program[entry + 31 + phase.val]? = (scratchEndpointCode (width := width))[phase.val]?
  saveAt : ∀ phase : Fin 6, program[entry + 36 + phase.val]? = (saveProjectionCode (width := width))[phase.val]?
  normalizerAt : Controller.Horn.NormalizeLoop.CodeAt program (entry + 42) (constructorFormula initial.heap sharedLayout (ForestZeroCompile.empty ambient) (ForestZeroCompile.empty_coherent ambient) references parameters.channels within).clauses.toList (constructorFormulaBackend initial.heap sharedLayout (ForestZeroCompile.empty ambient) (ForestZeroCompile.empty_coherent ambient) references parameters.channels within)
  indexSaveAt : Controller.Cost.ForestZeroHeaderBridge.SaveAt program (entry + 203) (initial.heap.size)
  indexAt : Controller.Horn.IndexScan.At (n := (constructorDictionary initial.heap sharedLayout (ForestZeroCompile.empty ambient) references).coordinates.size) program (entry + 210) ((constructorHeap initial.heap sharedLayout (ForestZeroCompile.empty ambient) references parameters.channels).size) ((constructorHeap initial.heap sharedLayout (ForestZeroCompile.empty ambient) references parameters.channels).size + 5 * (constructorDictionary initial.heap sharedLayout (ForestZeroCompile.empty ambient) references).coordinates.size + 4)
  indexRestoreAt : Controller.Cost.ForestZeroHeaderBridge.RestoreAt program (entry + 242)
  captureAt : ∀ phase : Fin 6, program[entry + 245 + phase.val]? = (Controller.Cost.ForestZeroReclaim.captureCode width)[phase.val]?
  fullCapacity : entry + 261 < 2 ^ width
  setupAt : ∀ phase : Fin 10, program[entry + 251 + phase.val]? =
          (Controller.Cost.ForestZeroSeedSetup.code (n := (constructorDictionary initial.heap sharedLayout (ForestZeroCompile.empty ambient) references).coordinates.size) width ((constructorHeap initial.heap sharedLayout (ForestZeroCompile.empty ambient) references parameters.channels).size) (initial.heap.size) ((constructorHeap initial.heap sharedLayout (ForestZeroCompile.empty ambient) references parameters.channels).size + 5 * (constructorDictionary initial.heap sharedLayout (ForestZeroCompile.empty ambient) references).coordinates.size + 4) scan)[phase.val]?
  scanAt : Controller.Horn.WorklistSeed.At (n := (constructorDictionary initial.heap sharedLayout (ForestZeroCompile.empty ambient) references).coordinates.size) program ((constructorHeap initial.heap sharedLayout (ForestZeroCompile.empty ambient) references parameters.channels).size) scan seedDone conflict
  room : (constructorState initial.heap sharedLayout (ForestZeroCompile.empty ambient) references parameters.channels entry (word width initial.heap.size :: rest) initial.output initial.reg).heap.size + 5 * (constructorDictionary initial.heap sharedLayout (ForestZeroCompile.empty ambient) references).coordinates.size + 4 +
          3 * (constructorFormula initial.heap sharedLayout (ForestZeroCompile.empty ambient) (ForestZeroCompile.empty_coherent ambient) references parameters.channels within).clauses.toList.length + ((constructorFormula initial.heap sharedLayout (ForestZeroCompile.empty ambient) (ForestZeroCompile.empty_coherent ambient) references parameters.channels within).clauses.toList.map List.length).sum +
          2 * (Controller.Horn.IndexScan.occurrences (constructorFormula initial.heap sharedLayout (ForestZeroCompile.empty ambient) (ForestZeroCompile.empty_coherent ambient) references parameters.channels within).clauses.toList ((constructorHeap initial.heap sharedLayout (ForestZeroCompile.empty ambient) references parameters.channels).size + 5 * (constructorDictionary initial.heap sharedLayout (ForestZeroCompile.empty ambient) references).coordinates.size + 4)).length < 2 ^ width
  scanCapacity : scan + 47 < 2 ^ width
  fetch : Nat
  headAt : ∀ phase : Fin 4, program[seedDone + phase.val]? =
          (Controller.Horn.WorklistAccept.headSetupCode (n := (constructorDictionary initial.heap sharedLayout (ForestZeroCompile.empty ambient) references).coordinates.size) width ((constructorHeap initial.heap sharedLayout (ForestZeroCompile.empty ambient) references parameters.channels).size) fetch)[phase.val]?
  headCapacity : seedDone + 4 < 2 ^ width
  fifoDone : Nat
  bucket : Nat
  advance : Nat
  ready : Nat
  skip : Nat
  fetchAt : Controller.Horn.WorklistFIFO.FetchAt (n := (constructorDictionary initial.heap sharedLayout (ForestZeroCompile.empty ambient) references).coordinates.size) program ((constructorHeap initial.heap sharedLayout (ForestZeroCompile.empty ambient) references parameters.channels).size) fetch fifoDone bucket
  advanceAt : Controller.Horn.WorklistFIFO.AdvanceAt (n := (constructorDictionary initial.heap sharedLayout (ForestZeroCompile.empty ambient) references).coordinates.size) program ((constructorHeap initial.heap sharedLayout (ForestZeroCompile.empty ambient) references parameters.channels).size) advance fetch
  loopAt : Controller.Horn.WorklistBucketLoop.At program bucket advance ready
  readyAt : Controller.Horn.WorklistBucketReady.At (n := (constructorDictionary initial.heap sharedLayout (ForestZeroCompile.empty ambient) references).coordinates.size) program ((constructorHeap initial.heap sharedLayout (ForestZeroCompile.empty ambient) references parameters.channels).size) ready skip conflict bucket
  fetchCapacity : fetch + 14 < 2 ^ width
  advanceCapacity : advance + 5 < 2 ^ width
  bucketCapacity : bucket + 12 < 2 ^ width
  readyCapacity : ready + 26 < 2 ^ width
  projectionEntry : Nat
  cleanupEntry : Nat
  returnPc : Nat
  successAt : Controller.Cost.ForestZeroAnswer.SavedAt program fifoDone 1 projectionEntry
  conflictAt : Controller.Cost.ForestZeroAnswer.SavedAt program conflict 0 cleanupEntry
  successCapacity : fifoDone + 13 < 2 ^ width
  conflictCapacity : conflict + 13 < 2 ^ width
  localFit : (constructorDictionary initial.heap sharedLayout (ForestZeroCompile.empty ambient) references).coordinates.size + 1 < 2 ^ width
  channelsFit : parameters.channels + 1 < 2 ^ width
  offRoom : ((constructorHeap initial.heap sharedLayout (ForestZeroCompile.empty ambient) references parameters.channels).size) + 1 < 2 ^ width
  projectionCapacity : projectionEntry + 35 < 2 ^ width
  constantsAt : ∀ phase : Fin 2, program[projectionEntry + phase.val]? =
          (projectionConstantsCode width)[phase.val]?
  preparationAt : ∀ phase : Fin 19, program[projectionEntry + 2 + phase.val]? =
          (channelPrepareCode width)[phase.val]?
  saveEntry : Nat
  pushEntry : Nat
  nativeEntry : Nat
  done : Nat
  saveEq : saveEntry = projectionEntry + 21
  projectionEq : pushEntry = saveEntry + 8
  nativeSaveAt : SharedRootRead.BlockAt program saveEntry (SharedRegisterStack.saveCode (width := width) (List.finRange 8))
  restoreRoom : done + 8 < 2 ^ width
  restoreAt : SharedRootRead.BlockAt program done (SharedRegisterStack.restoreCode (width := width) (List.finRange 8).reverse)
  projectionRoom : pushEntry + 14 < 2 ^ width
  projectionAt : ForestZeroChannelPush.CodeAt program pushEntry nativeEntry
  nativeRoom : nativeEntry + (NativeRetainedExecution.code parameters width (nativeBase initial.heap sharedLayout references parameters.channels within) nativeEntry).length < 2 ^ width
  nativeHeap : (nativeBase initial.heap sharedLayout references parameters.channels within) + parameters.channels + (compile parameters).toState.count < 2 ^ width
  nativeAt : ForestZeroCallerWiden.WidenedBlockAt program nativeEntry
      (NativeRetainedExecution.code parameters width (nativeBase initial.heap sharedLayout references parameters.channels within) nativeEntry)
  finishRoom : emitEntry parameters width (nativeBase initial.heap sharedLayout references parameters.channels within) nativeEntry + 3 * (compile parameters).toState.count + 7 < 2 ^ width
  emitAt : ForestZeroCallerWiden.WidenedBlockAt program (emitEntry parameters width (nativeBase initial.heap sharedLayout references parameters.channels within) nativeEntry)
      (OutputProgram.emitCode width (NativeRealizedCore.addresses ((nativeBase initial.heap sharedLayout references parameters.channels within) + parameters.channels) (compile parameters).toState.count))
  releaseAt : Controller.Cost.RawTransferLoops.CodeAt program
      (emitEntry parameters width (nativeBase initial.heap sharedLayout references parameters.channels within) nativeEntry + 3 * (compile parameters).toState.count)
      (SharedEvaluationReclaim.code width (emitEntry parameters width (nativeBase initial.heap sharedLayout references parameters.channels within) nativeEntry + 3 * (compile parameters).toState.count)
        done (parameters.channels + (compile parameters).toState.count))
  nativeSetup : ∀ phase : Fin 3, program[done + 8 + phase.val]? =
      (Controller.Cost.ForestZeroReclaim.setupCode width)[phase.val]?
  nativeLoop : Controller.Cost.ForestZeroReclaim.At program (done + 11) returnPc
  nativeCleanupRoom : done + 15 < 2 ^ width
  cleanupSetup : ∀ phase : Fin 3, program[cleanupEntry + phase.val]? =
          (Controller.Cost.ForestZeroReclaim.setupCode width)[phase.val]?
  cleanupLoop : Controller.Cost.ForestZeroReclaim.At program (cleanupEntry + 3) returnPc
  cleanupCapacity : cleanupEntry + 7 < 2 ^ width
  resetCapacity : returnPc + 27 < 2 ^ width
  resetPrepareAt : ForestZeroCallerWiden.WidenedBlockAt program returnPc (resetPrepareCode width).toList
  resetLoopAt : ForestZeroCallerWiden.WidenedBlockAt program (returnPc + 15)
          (Controller.Cost.ForestZeroReset.code width (returnPc + 15))
  decisionCapacity : returnPc + 28 < 2 ^ width
  decisionAt : program[returnPc + 27]? = some (.pop 4)
  dispatchEq : returnPc + 28 = dispatchEntry
  dispatchCapacity : dispatchEntry + 2 < 2 ^ width
  dispatchAt : ∀ phase : Fin 2, program[dispatchEntry + phase.val]? =
    (ForestZeroRootLoop.dispatchCode width nextEntry)[phase.val]?

def QueryNativeWitness (parameters : Parameters) (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (references : List (List (Reference ambient))) (within : parameters.channels ≤ ambient)
    (observed : List (Word width)) : Prop :=
  let dictionary := constructorDictionary heap layout (ForestZeroCompile.empty ambient) references
  let formula := constructorFormula heap layout (ForestZeroCompile.empty ambient)
    (ForestZeroCompile.empty_coherent ambient) references parameters.channels within
  ∃ queue : List (Fin dictionary.coordinates.size), ∃ previous : List (Word width),
    Controller.CNF.Satisfies (Controller.Horn.WorklistOutcome.offAssignment queue) formula ∧
    Controller.Horn.WorklistOutcome.offAssignment queue = Controller.Horn.greatestCandidate formula ∧
    observed = (NativeRootLoad.words width
      (SourceLift.finite parameters (Physical.realizeBridge parameters.bridge parameters.positiveBuses
        (setOfAssignment (SharedZeroNative.channels parameters dictionary queue within))))).reverse ++
      word width 1 :: previous

theorem SourceQueryPlan.execute {width ambient : Nat}
    (parameters : Parameters)
    (program : Program width 8) (initial : State width 8) (sourceHeap : Array (Word width))
    (sharedLayout : Layout ambient initial.heap.size)
    (references : List (List (Reference ambient))) (sourceEnd nodes sourceEntry : Nat)
    (rest : List (Word width)) (within : parameters.channels ≤ ambient) (dispatchEntry nextEntry : Nat)
    (plan : SourceQueryPlan parameters program initial sharedLayout references sourceEnd nodes sourceEntry rest within dispatchEntry nextEntry)
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
  have represented : Represented initial.heap sharedLayout (ForestZeroCompile.empty ambient) :=
    empty_dictionary_from_zero_table initial.heap sharedLayout initialReady.zeroTable
  have initialEq := initialReady.entry_state
  obtain ⟨answer, queue, final, ticks, peak, trace, timeBound, spaceBound, heapSize, finalStack,
      finalOutput, finalPC, finalRunning, originalFrame, zeroTable, decision, zeroRegister,
      tableRegister, inverseRegister, meaning, greatest, finalLive, sourceFrame,
      actualLayout, actualTable, actualInverse, emptyRepresentation, nextReady⟩ :=
    SharedZeroNativePrepared.source_constructor_native_reuse_execution parameters initial.heap sharedLayout (ForestZeroCompile.empty ambient) represented references sourceEnd nodes plan.sourceReferences plan.sourceBeforeTable plan.sourceBeforeInverse plan.sourceBound plan.sourcePositive plan.sourceChannel plan.sourceNodes plan.ambientEq plan.adjacent plan.tablePositive plan.sourceHeaderRoom plan.sourceDual program sourceEntry plan.constructorEntry plan.entry plan.entryEq (by rfl) plan.sourceEndpoint (initial.reg 3).val plan.entryCapacity plan.entryAt plan.keepAt plan.cursorAt rest initial.output initial.reg plan.constructorRoom plan.ambientFits plan.constructorCapacity plan.constructorAt plan.scan plan.seedDone plan.conflict plan.countAt plan.allocateAt plan.headersAt plan.endpointAt plan.saveAt plan.normalizerAt plan.indexSaveAt plan.indexAt plan.indexRestoreAt plan.captureAt plan.fullCapacity plan.setupAt plan.scanAt plan.room plan.scanCapacity plan.fetch plan.headAt plan.headCapacity plan.fifoDone plan.bucket plan.advance plan.ready plan.skip plan.fetchAt plan.advanceAt plan.loopAt plan.readyAt plan.fetchCapacity plan.advanceCapacity plan.bucketCapacity plan.readyCapacity plan.projectionEntry plan.cleanupEntry plan.returnPc plan.successAt plan.conflictAt plan.successCapacity plan.conflictCapacity plan.localFit plan.channelsFit plan.offRoom plan.projectionCapacity plan.constantsAt plan.preparationAt plan.saveEntry plan.pushEntry plan.nativeEntry plan.done plan.saveEq plan.projectionEq plan.nativeSaveAt plan.restoreRoom plan.restoreAt plan.projectionRoom plan.projectionAt plan.nativeRoom plan.nativeHeap plan.nativeAt plan.finishRoom plan.emitAt plan.releaseAt plan.nativeSetup plan.nativeLoop plan.nativeCleanupRoom plan.cleanupSetup plan.cleanupLoop plan.cleanupCapacity plan.resetCapacity plan.resetPrepareAt plan.resetLoopAt plan.decisionCapacity plan.decisionAt
  rw [initialEq] at trace finalLive
  have budgets := constructor_full_query_budget initial.heap sharedLayout (ForestZeroCompile.empty ambient)
    (ForestZeroCompile.empty_coherent ambient) references parameters.channels within rfl plan.entry sourceEntry
    (initial.reg 3).val rest initial.output initial.reg false
  rw [initialEq] at budgets
  simp only [constructorFormula_rows] at timeBound spaceBound
  simp only [Bool.false_eq_true, ite_false] at budgets
  refine ⟨answer, final, ticks, peak, trace, ?_, finalRunning, decision,
    (by have bound := budgets.1; cases answer <;> simp only [Bool.false_eq_true, ite_false, ite_true] at timeBound ⊢ <;> omega), (by have := budgets.2; omega), finalLive, meaning, ?_, ?_,
    plan.dispatchCapacity, plan.dispatchAt⟩
  · simpa only [plan.dispatchEq] using finalPC
  · intro accepted
    refine ⟨queue, initial.output, (greatest accepted).1, (greatest accepted).2, ?_⟩
    rw [accepted] at finalOutput
    simpa [constructorState, RegisterWiden.widenState, atState] using finalOutput
  · intro rejected
    exact (nextReady nextEntry rejected).rebase initialReady.heapSize initialReady.sourceFrame

theorem occurrence_query_contract {width ambient : Nat}
    (parameters : Parameters)
    (program : Program width 8) (sourceHeap : Array (Word width))
    (layout : Layout ambient sourceHeap.size)
    (queries : List (List (List (Reference ambient)))) (sourceEnd nodes : Nat)
    (rest : List (Word width)) (within : parameters.channels ≤ ambient)
    (resume : List (Fin queries.length) → Nat) (dispatch : Fin queries.length → Nat) (scratch : Nat)
    (scratchBound : ∀ position : Fin queries.length,
      5 * queries[position].length + 15 * queries[position].flatten.length + parameters.channels + 3 * (selectedSize parameters).total + 28 ≤ scratch)
    (plans : ∀ (position : Fin queries.length) (tail : List (Fin queries.length)) (state : State width 8),
      ForestZeroRootLoop.TailOf (List.finRange queries.length) (position :: tail) →
      ∀ initialReady : QueryReady (ambient := ambient) sourceHeap layout.tableBase layout.inverseBase
          (resume (position :: tail)) rest state,
      SourceQueryPlan parameters program state (initialReady.current_layout layout) queries[position] sourceEnd nodes
        (resume (position :: tail)) rest within (dispatch position) (resume tail)) :
    ForestZeroRootLoop.QueryContract program (List.finRange queries.length)
      (fun remaining state => QueryReady (ambient := ambient) sourceHeap layout.tableBase layout.inverseBase
        (resume remaining) rest state)
      (fun position => Controller.CNF.Satisfiable (constructorFormula sourceHeap layout
        (ForestZeroCompile.empty ambient) (ForestZeroCompile.empty_coherent ambient) queries[position] parameters.channels within))
      (fun position observed => QueryNativeWitness parameters sourceHeap layout queries[position] within observed)
      resume dispatch
      (fun position => 150 * queries[position].length + 387 * queries[position].flatten.length + 483)
      scratch (55 * (selectedSize parameters).total) (compile parameters).toState.count := by
  intro position tail state suffix initialReady
  let actualLayout := initialReady.current_layout layout
  have actualReady : QueryReady (ambient := ambient) sourceHeap actualLayout.tableBase actualLayout.inverseBase
      (resume (position :: tail)) rest state := initialReady
  obtain ⟨answer, final, ticks, peak, trace, finalPC, finalRunning, decision, timeBound,
      spaceBound, finalLive, meaning, witnessed, failedReady, dispatchCapacity, dispatchAt⟩ :=
    SourceQueryPlan.execute parameters program state sourceHeap actualLayout queries[position] sourceEnd nodes
      (resume (position :: tail)) rest within (dispatch position) (resume tail)
      (plans position tail state suffix initialReady) actualReady
  refine ⟨answer, final, ticks, peak, trace, finalPC, finalRunning, decision, timeBound,
    ?_, finalLive, ?_, ?_, failedReady, dispatchCapacity, dispatchAt⟩
  · have localScratch := scratchBound position
    omega
  · have same := constructorFormula_heap_irrel state.heap sourceHeap actualLayout layout
      (ForestZeroCompile.empty ambient) (ForestZeroCompile.empty_coherent ambient) queries[position] parameters.channels within
    rw [same] at meaning
    exact meaning
  · exact witnessed


theorem source_first_success_execution {width ambient : Nat}
    (parameters : Parameters)
    (program : Program width 8) (sourceHeap : Array (Word width))
    (layout : Layout ambient sourceHeap.size)
    (queries : List (List (List (Reference ambient)))) (sourceEnd nodes : Nat)
    (rest : List (Word width)) (within : parameters.channels ≤ ambient)
    (resume : List (Fin queries.length) → Nat) (dispatch : Fin queries.length → Nat) (scratch : Nat)
    (scratchBound : ∀ position : Fin queries.length,
      5 * queries[position].length + 15 * queries[position].flatten.length + parameters.channels + 3 * (selectedSize parameters).total + 28 ≤ scratch)
    (plans : ∀ (position : Fin queries.length) (tail : List (Fin queries.length)) (state : State width 8),
      ForestZeroRootLoop.TailOf (List.finRange queries.length) (position :: tail) →
      ∀ initialReady : QueryReady (ambient := ambient) sourceHeap layout.tableBase layout.inverseBase
          (resume (position :: tail)) rest state,
      SourceQueryPlan parameters program state (initialReady.current_layout layout) queries[position] sourceEnd nodes
        (resume (position :: tail)) rest within (dispatch position) (resume tail))
    (emptyFits : resume [] + 2 < 2 ^ width)
    (emptyAt : ∀ phase : Fin 2, program[resume [] + phase.val]? =
      (ForestZeroRootLoop.exhaustedCode width)[phase.val]?)
    (initial : State width 8)
    (initialReady : QueryReady (ambient := ambient) sourceHeap layout.tableBase layout.inverseBase
      (resume (List.finRange queries.length)) rest initial) :
    ∃ answer : Bool, ∃ final ticks peak,
      Execution program initial final ticks peak ∧ final.halted = true ∧
      final.reg 4 = word width (if answer then 1 else 0) ∧
      ticks ≤ 150 * (queries.map List.length).sum +
        387 * (queries.map (fun rows => rows.flatten.length)).sum + 484 * queries.length + 55 * (selectedSize parameters).total + 2 ∧
      peak ≤ initial.liveWords + scratch + queries.length + (compile parameters).toState.count + 1 ∧
      (answer = true ↔ ∃ position : Fin queries.length,
        Controller.CNF.Satisfiable (constructorFormula sourceHeap layout (ForestZeroCompile.empty ambient)
          (ForestZeroCompile.empty_coherent ambient) queries[position] parameters.channels within)) ∧
      (answer = true → ∃ position : Fin queries.length,
        Controller.CNF.Satisfiable (constructorFormula sourceHeap layout (ForestZeroCompile.empty ambient)
          (ForestZeroCompile.empty_coherent ambient) queries[position] parameters.channels within) ∧
        QueryNativeWitness parameters sourceHeap layout queries[position] within final.output) := by
  let actualQueries := List.finRange queries.length
  let ready := fun remaining state => QueryReady (ambient := ambient) sourceHeap layout.tableBase layout.inverseBase
    (resume remaining) rest state
  let feasible := fun position : Fin queries.length => Controller.CNF.Satisfiable
    (constructorFormula sourceHeap layout (ForestZeroCompile.empty ambient)
      (ForestZeroCompile.empty_coherent ambient) queries[position] parameters.channels within)
  let witnessed := fun (position : Fin queries.length) observed => QueryNativeWitness parameters sourceHeap layout queries[position] within observed
  let work := fun position : Fin queries.length => 150 * queries[position].length +
    387 * queries[position].flatten.length + 483
  have contract := occurrence_query_contract parameters program sourceHeap layout queries sourceEnd nodes rest within
    resume dispatch scratch scratchBound plans
  have emptyReady : ∀ state, ready [] state → state.pc = word width (resume []) ∧ state.halted = false := by
    intro state prepared
    exact ⟨prepared.position, prepared.running⟩
  obtain ⟨answer, final, ticks, peak, trace, halted, decision, timeBound, spaceBound, meaning, model⟩ :=
    ForestZeroRootLoop.first_success_execution program actualQueries ready feasible witnessed resume dispatch work
      scratch (55 * (selectedSize parameters).total) (compile parameters).toState.count contract emptyReady emptyFits emptyAt actualQueries
      ⟨[], by simp [actualQueries]⟩ initial initialReady
  have workSum := ForestZeroRootLoop.linear_work_sum actualQueries work
    (fun position => queries[position].length) (fun position => queries[position].flatten.length)
    150 387 483 (by intro position inside; exact le_refl _)
  have rowSum : (actualQueries.map fun position => queries[position].length).sum = (queries.map List.length).sum := by
    change ((List.finRange queries.length).map fun position => queries[position].length).sum = _
    rw [← List.ofFn_eq_map]
    change (List.ofFn fun position : Fin queries.length => queries[position.val].length).sum = _
    exact congrArg List.sum (List.ofFn_getElem_eq_map queries List.length)
  have literalSum : (actualQueries.map fun position => queries[position].flatten.length).sum =
      (queries.map fun rows => rows.flatten.length).sum := by
    change ((List.finRange queries.length).map fun position => queries[position].flatten.length).sum = _
    rw [← List.ofFn_eq_map]
    change (List.ofFn fun position : Fin queries.length => queries[position.val].flatten.length).sum = _
    exact congrArg List.sum (List.ofFn_getElem_eq_map queries (fun rows => rows.flatten.length))
  have positionsLength : actualQueries.length = queries.length := by simp [actualQueries]
  rw [rowSum, literalSum, positionsLength] at workSum
  rw [positionsLength] at timeBound spaceBound
  refine ⟨answer, final, ticks, peak, trace, halted, decision, ?_, ?_, ?_, ?_⟩
  · omega
  · omega
  · simpa only [actualQueries, List.mem_finRange, true_and] using meaning
  · simpa only [actualQueries, List.mem_finRange, true_and] using model


theorem native_witness_projection (parameters : Parameters) (graph : DAG parameters.channels)
    (guarded : graph.Guarded) (T F : Finset (Fin parameters.channels)) (root : Fin graph.nodeCount)
    (heap : Array (Word width)) (layout : Layout (parameters.channels + graph.nodeCount) heap.size)
    (base slot : Nat) (observed : List (Word width))
    (witness : QueryNativeWitness parameters heap layout
      (SharedZeroSource.references graph parameters.buses parameters.bridge.target T F base slot root) (by omega) observed) :
    ∃ K, Admissible parameters.buses parameters.bridge.target K ∧ ExtendsFixed T F K ∧
      graph.eval (assignmentOfSet K) root = false ∧
      ∃ previous, observed = (NativeRootLoad.words width
        (SourceLift.finite parameters (Physical.realizeBridge parameters.bridge parameters.positiveBuses K))).reverse ++
        word width 1 :: previous := by
  let refs := SharedZeroSource.references graph parameters.buses parameters.bridge.target T F base slot root
  let dictionary := constructorDictionary heap layout (ForestZeroCompile.empty _) refs
  obtain ⟨queue, previous, localModel, greatest, output⟩ := witness
  have coherent : Coherent dictionary := (rows_dictionary (ForestZeroCompile.empty _) (empty_coherent _)
    (ForestZeroAssembly.originalRows (reservedReferences refs))).1
  let assignment := ForestZeroModelLift.lift dictionary true
    (extendNat (Controller.Horn.WorklistOutcome.offAssignment queue))
  have original := (SharedZeroModel.constructor_lift_model heap layout (ForestZeroCompile.empty _) (empty_coherent _) refs
    parameters.channels (by omega)
    (fun values model => SharedZeroMeaning.source_nonempty graph parameters.buses parameters.bridge.target T F root values model) _).mp localModel
  have template : Satisfies assignment (SharedZeroTemplate.formula graph parameters.buses parameters.bridge.target root T F) := by
    rw [SharedZeroSource.originalRows_eq] at original
    simpa [ofClauses, assignment, dictionary, refs] using original
  have projected := SharedZeroOutput.finite_model_projection graph guarded parameters.buses parameters.bridge.target T F root assignment
    ((SharedZeroTemplate.satisfies_iff graph parameters.buses parameters.bridge.target root T F assignment).mp template)
  have same : setOfAssignment (SharedZeroNative.channels parameters dictionary queue (by omega)) =
      graph.zeroChannelSet (assignment ∘ graph.zeroIndex) := by
    unfold SharedZeroNative.channels
    change setOfAssignment (fun channel => ForestZeroModelLift.lift dictionary true
      (ForestZeroChannelEmit.localValues queue) _) = _
    rw [SharedZeroOutput.queue_lift dictionary coherent queue]
    rfl
  refine ⟨graph.zeroChannelSet (assignment ∘ graph.zeroIndex), projected.1, projected.2.1, projected.2.2, previous, ?_⟩
  rw [← same]
  exact output



theorem native_witness_checked (parameters : Parameters) (raw : parameters.layout = .raw)
    (drive : parameters.drive = true) (graph : DAG parameters.channels) (guarded : graph.Guarded)
    (T F : Finset (Fin parameters.channels)) (root : Fin graph.nodeCount)
    (heap : Array (Word width)) (layout : Layout (parameters.channels + graph.nodeCount) heap.size)
    (base slot : Nat) (observed : List (Word width)) (fits : 1 < 2 ^ width)
    (observation : Fin parameters.decoder.roots.length)
    (observationEq : ∀ K, parameters.observations observation (assignmentOfSet K) = graph.eval (assignmentOfSet K) root)
    (healthy : graph.eval (assignmentOfSet {parameters.bridge.target}) root = true)
    (witness : QueryNativeWitness parameters heap layout
      (SharedZeroSource.references graph parameters.buses parameters.bridge.target T F base slot root) (by omega) observed) :
    Certificate.ModelCheck.check (formula parameters)
      (NativeRealizedChecked.decodeOutput observed (compile parameters).toState.count) = true := by
  obtain ⟨K, eligible, fixed, zero, previous, output⟩ := native_witness_projection parameters graph guarded T F root
    heap layout base slot observed witness
  have differs : ∃ output, parameters.observations output (assignmentOfSet {parameters.bridge.target}) ≠
      parameters.observations output (assignmentOfSet K) := by
    refine ⟨observation, ?_⟩
    rw [observationEq, observationEq, healthy, zero]
    decide
  rw [output, NativeRealizedChecked.output_decodes _ _ fits]
  exact SourceLift.eligible_checked parameters raw K eligible drive differs



theorem nativeBase_bound (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (references : List (List (Reference ambient))) (channels : Nat) (within : channels ≤ ambient) :
    nativeBase heap layout references channels within ≤ heap.size + 14 + 5 * references.length +
      5 * references.flatten.length + 10 * (constructorDictionary heap layout (ForestZeroCompile.empty _) references).coordinates.size := by
  have bound := constructor_reclaimed_count_bound heap layout (ForestZeroCompile.empty _)
    (ForestZeroCompile.empty_coherent _) references channels within
  have growth := constructorHeap_growth heap layout (ForestZeroCompile.empty _) references channels
  have records := Controller.Horn.NormalizeLoop.recordOffset_above
    (constructorClauses heap layout (ForestZeroCompile.empty _) (ForestZeroCompile.empty_coherent _) references channels within)
    ((constructorHeap heap layout (ForestZeroCompile.empty _) references channels).size +
      5 * (constructorDictionary heap layout (ForestZeroCompile.empty _) references).coordinates.size + 4)
    (constructorClauses heap layout (ForestZeroCompile.empty _) (ForestZeroCompile.empty_coherent _) references channels within).length
  simp only [nativeBase, constructorFormula_rows] at bound records ⊢
  omega

theorem zero_nativeBase_bound (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels)) (root : Fin graph.nodeCount)
    (heap : Array (Word width)) (layout : Layout (parameters.channels + graph.nodeCount) heap.size) :
    nativeBase heap layout (SharedZeroSource.references graph parameters.buses parameters.bridge.target T F base slot root)
      parameters.channels (by omega) ≤ heap.size + 80 * (graph.countedSize + 1) := by
  have bound := nativeBase_bound heap layout
    (SharedZeroSource.references graph parameters.buses parameters.bridge.target T F base slot root) parameters.channels (by omega)
  rw [SharedZeroSource.dictionary_size] at bound
  have occurrences := SharedZeroSource.occurrence_bound (base := base) (slot := slot)
    graph parameters.buses parameters.bridge.target T F root
  have size := graph.countedSize_eq
  omega



theorem nativeBase_root_irrel (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels)) (left right : Fin graph.nodeCount)
    (heap : Array (Word width)) (layout : Layout (parameters.channels + graph.nodeCount) heap.size) :
    nativeBase heap layout (SharedZeroSource.references graph parameters.buses parameters.bridge.target T F base slot left)
      parameters.channels (by omega) =
    nativeBase heap layout (SharedZeroSource.references graph parameters.buses parameters.bridge.target T F base slot right)
      parameters.channels (by omega) := by
  unfold nativeBase
  simp only [constructorFormula_rows, SharedZeroSource.dictionary_size,
    SharedZeroSource.constructor_heap_size_root_irrel graph parameters.buses parameters.bridge.target T F left right heap layout]
  apply SharedNormalizationShape.native_base
  exact SharedNormalizationShape.constructor_root_profile graph parameters.buses parameters.bridge.target T F left right heap layout


theorem native_code_root_irrel (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels)) (left right : Fin graph.nodeCount)
    (heap : Array (Word width)) (layout : Layout (parameters.channels + graph.nodeCount) heap.size) (entry : Nat) :
    NativeRetainedExecution.code parameters width
      (nativeBase heap layout (SharedZeroSource.references graph parameters.buses parameters.bridge.target T F base slot left)
        parameters.channels (by omega)) entry =
    NativeRetainedExecution.code parameters width
      (nativeBase heap layout (SharedZeroSource.references graph parameters.buses parameters.bridge.target T F base slot right)
        parameters.channels (by omega)) entry := by
  rw [nativeBase_root_irrel parameters graph T F left right heap layout]

theorem native_block_root_transport (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels)) (left right : Fin graph.nodeCount)
    (heap : Array (Word width)) (layout : Layout (parameters.channels + graph.nodeCount) heap.size)
    (program : Program width 8) (entry : Nat)
    (present : ForestZeroCallerWiden.WidenedBlockAt program entry
      (NativeRetainedExecution.code parameters width
        (nativeBase heap layout (SharedZeroSource.references graph parameters.buses parameters.bridge.target T F base slot left)
          parameters.channels (by omega)) entry)) :
    ForestZeroCallerWiden.WidenedBlockAt program entry
      (NativeRetainedExecution.code parameters width
        (nativeBase heap layout (SharedZeroSource.references graph parameters.buses parameters.bridge.target T F base slot right)
          parameters.channels (by omega)) entry) := by
  rw [← native_code_root_irrel parameters graph T F left right heap layout entry]
  exact present

end Controller.Cost.SharedZeroNativeQuery
