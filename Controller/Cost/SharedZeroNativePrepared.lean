module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedZeroNativeCleanup
public import Controller.Cost.ForestZeroAdmissibleCaller

@[expose] public section

namespace Controller.Cost.SharedZeroNativePrepared
open Controller.Cost.GateProgram Controller.Cost.NativeCircuitExecution Controller.Cost.NativeSourceExecution
open Controller.Cost.ForestZeroCompile Controller.Native Controller.Native.SourceController Controller.Decoder
open Controller.Cost.SharedZeroNativeComplete
open Controller.CNF Controller.Cost.ForestZeroTouch Controller.Cost.ForestZeroEmit
open Controller.Horn.SourceDirectory Controller.Horn.SourceScan Controller.Horn.RowScan
open Controller.Cost.ForestZeroAdmissibleCaller Controller.Cost.ForestZeroDictionary

theorem execution (parameters : Parameters) (resident : Program width 8) (state : State width 8)
    (entry saveEntry projectionEntry nativeEntry offBase done nodes : Nat) (dictionary : Dictionary ambient)
    (layout : ForestZeroDictionary.Layout ambient state.heap.size)
    (represented : ForestZeroDictionary.Represented state.heap layout dictionary)
    (ambientEq : ambient = parameters.channels + nodes)
    (adjacent : layout.inverseBase = layout.tableBase + ambient)
    (within : parameters.channels ≤ ambient) (queue : List (Fin dictionary.coordinates.size))
    (fifo : Controller.Horn.WorklistMark.Stored queue offBase state.heap)
    (countFits : dictionary.coordinates.size + 1 < 2 ^ width)
    (position : state.pc = word width entry) (running : state.halted = false)
    (projectionEq : projectionEntry = saveEntry + 8)
    (saveAt : SharedRootRead.BlockAt resident saveEntry (SharedRegisterStack.saveCode (width := width) (List.finRange 8)))
    (restoreRoom : done + 8 < 2 ^ width)
    (restoreAt : SharedRootRead.BlockAt resident done (SharedRegisterStack.restoreCode (width := width) (List.finRange 8).reverse))
    (saveEq : saveEntry = entry + 19)
    (zero : state.reg 2 = word width 0) (one : state.reg 5 = word width 1)
    (channelCell : state.heap[0]? = some (word width parameters.channels))
    (nodeCell : state.heap[1]? = some (word width nodes))
    (headerRoom : 1 < state.heap.size) (offRoom : offBase + 1 < 2 ^ width)
    (prepareRoom : entry + 19 < 2 ^ width)
    (prepareAt : ∀ phase : Fin 19, resident[entry + phase.val]? =
      (ForestZeroAdmissibleCaller.channelPrepareCode width)[phase.val]?)
    (channelsFit : parameters.channels + 1 < 2 ^ width) (heapFits : state.heap.size ≤ 2 ^ width)
    (projectionRoom : projectionEntry + 14 < 2 ^ width)
    (projectionAt : ForestZeroChannelPush.CodeAt resident projectionEntry nativeEntry)
    (nativeRoom : nativeEntry + (NativeRetainedExecution.code parameters width state.heap.size nativeEntry).length < 2 ^ width)
    (nativeHeap : state.heap.size + parameters.channels + (compile parameters).toState.count < 2 ^ width)
    (nativeAt : ForestZeroCallerWiden.WidenedBlockAt resident nativeEntry
      (NativeRetainedExecution.code parameters width state.heap.size nativeEntry))
    (finishRoom : emitEntry parameters width state.heap.size nativeEntry + 3 * (compile parameters).toState.count + 7 < 2 ^ width)
    (emitAt : ForestZeroCallerWiden.WidenedBlockAt resident (emitEntry parameters width state.heap.size nativeEntry)
      (OutputProgram.emitCode width (NativeRealizedCore.addresses (state.heap.size + parameters.channels) (compile parameters).toState.count)))
    (releaseAt : Controller.Cost.RawTransferLoops.CodeAt resident
      (emitEntry parameters width state.heap.size nativeEntry + 3 * (compile parameters).toState.count)
      (SharedEvaluationReclaim.code width (emitEntry parameters width state.heap.size nativeEntry + 3 * (compile parameters).toState.count)
        done (parameters.channels + (compile parameters).toState.count))) :
    ∀ (keep count : Nat) (rest : List (Word width)) (returnPC : Nat),
    ∀ setupAt : ∀ phase : Fin 3, resident[done + 8 + phase.val]? = (ForestZeroReclaim.setupCode width)[phase.val]?,
    ∀ loopAt : ForestZeroReclaim.At resident (done + 11) returnPC,
    ∀ cleanupRoom : done + 15 < 2 ^ width,
    ∀ countFit : count < 2 ^ width,
    ∀ savedCount : state.stack = word width count :: word width layout.inverseBase ::
      word width dictionary.coordinates.size :: word width offBase :: rest,
    ∀ allocated : state.heap.size = keep + count,
    let K := setOfAssignment (SharedZeroNative.channels parameters dictionary queue within)
    ∃ final ticks peak, Execution resident state final ticks peak ∧
      ticks ≤ 55 * (selectedSize parameters).total + 4 * count + 44 ∧
      peak ≤ state.liveWords + 3 * (selectedSize parameters).total + 8 ∧
      final.heap.size = keep ∧
      final.stack = word width layout.inverseBase :: word width dictionary.coordinates.size :: word width offBase :: rest ∧
      final.output = (NativeRootLoad.words width
        (SourceLift.finite parameters (Physical.realizeBridge parameters.bridge parameters.positiveBuses K))).reverse ++ state.output ∧
      final.pc = word width returnPC ∧ final.halted = false ∧
      ForestZeroBackendFrame.PrefixFrame keep state.heap final.heap := by
  intro keep count rest returnPC setupAt loopAt cleanupRoom countFit savedCount allocated
  have scalarRoom : layout.tableBase + (parameters.channels + nodes) < 2 ^ width := by
    have bound := layout.inverseBound
    omega
  have saved : state.stack = word width count :: word width (layout.tableBase + (parameters.channels + nodes)) ::
      word width dictionary.coordinates.size :: word width offBase :: rest := by
    simpa only [adjacent, ambientEq] using savedCount
  obtain ⟨prepared, preparation, sameHeap, sameStack, sameOutput,
    preparedZero, preparedChannels, preparedTable, preparedOne, preparedMask, preparedOff, preparedPC, preparedRunning⟩ :=
    ForestZeroAdmissibleCaller.channel_prepare_execution resident state entry layout.tableBase offBase parameters.channels nodes
      dictionary.coordinates.size (word width count) rest position running saved zero one headerRoom channelCell nodeCell
      scalarRoom offRoom prepareRoom prepareAt
  have unchanged : ForestZeroBackendFrame.PrefixFrame state.heap.size state.heap prepared.heap :=
    ⟨by omega, by rw [sameHeap], fun _ _ => by rw [sameHeap]⟩
  let preparedLayout := ForestZeroAdmissibleCaller.retainedDictionaryLayout state.heap prepared.heap state.heap.size layout
    unchanged layout.tableBound layout.inverseBound
  have preparedDictionary : ForestZeroDictionary.Represented prepared.heap preparedLayout dictionary :=
    ForestZeroAdmissibleCaller.dictionary_prefix_transport state.heap prepared.heap state.heap.size layout dictionary
      represented unchanged layout.tableBound layout.inverseBound
  have preparedFifo : Controller.Horn.WorklistMark.Stored queue offBase prepared.heap := by
    simpa only [sameHeap] using fifo
  obtain ⟨final, ticks, peak, trace, timeBound, spaceBound, size, stack, output, pc, active, frame⟩ :=
    SharedZeroNativeCleanup.execution parameters resident prepared saveEntry projectionEntry nativeEntry offBase done dictionary
      preparedLayout preparedDictionary within queue preparedFifo countFits (by simpa [saveEq] using preparedPC)
      preparedRunning projectionEq saveAt restoreRoom restoreAt preparedZero preparedChannels
      (by simpa [preparedLayout, ForestZeroAdmissibleCaller.retainedDictionaryLayout] using preparedTable) preparedOne preparedMask preparedOff channelsFit
      (by simpa only [sameHeap] using heapFits) projectionRoom projectionAt
      (by simpa only [sameHeap] using nativeRoom) (by simpa only [sameHeap] using nativeHeap)
      (by simpa only [sameHeap] using nativeAt) (by simpa only [sameHeap] using finishRoom)
      (by simpa only [sameHeap] using emitAt) (by simpa only [sameHeap] using releaseAt)
      keep count (word width layout.inverseBase :: word width dictionary.coordinates.size :: word width offBase :: rest)
      returnPC setupAt loopAt cleanupRoom countFit (sameStack.trans savedCount) (by simpa only [sameHeap] using allocated)
  have live : prepared.liveWords = state.liveWords := by
    simp only [State.liveWords, sameHeap, sameStack, sameOutput]
  refine ⟨final, 19 + ticks, max state.liveWords peak, preparation.append trace,
    by omega, ?_, size, stack, ?_, pc, active, ?_⟩
  · rw [live] at spaceBound
    omega
  · simpa only [sameOutput] using output
  · simpa only [sameHeap] using frame

theorem terminal_execution (parameters : Parameters) (resident : Program width 8) (state : State width 8)
    (entry saveEntry projectionEntry nativeEntry offBase done nodes : Nat) (dictionary : Dictionary ambient)
    (layout : ForestZeroDictionary.Layout ambient state.heap.size)
    (represented : ForestZeroDictionary.Represented state.heap layout dictionary)
    (ambientEq : ambient = parameters.channels + nodes)
    (adjacent : layout.inverseBase = layout.tableBase + ambient)
    (within : parameters.channels ≤ ambient) (queue : List (Fin dictionary.coordinates.size))
    (fifo : Controller.Horn.WorklistMark.Stored queue offBase state.heap)
    (countFits : dictionary.coordinates.size + 1 < 2 ^ width)
    (position : state.pc = word width entry) (running : state.halted = false)
    (projectionEq : projectionEntry = saveEntry + 8)
    (saveAt : SharedRootRead.BlockAt resident saveEntry (SharedRegisterStack.saveCode (width := width) (List.finRange 8)))
    (restoreRoom : done + 8 < 2 ^ width)
    (restoreAt : SharedRootRead.BlockAt resident done (SharedRegisterStack.restoreCode (width := width) (List.finRange 8).reverse))
    (saveEq : saveEntry = entry + 21)
    (channelCell : state.heap[0]? = some (word width parameters.channels))
    (nodeCell : state.heap[1]? = some (word width nodes))
    (headerRoom : 1 < state.heap.size) (offRoom : offBase + 1 < 2 ^ width)
    (prepareRoom : entry + 21 < 2 ^ width)
    (constantsAt : ∀ phase : Fin 2, resident[entry + phase.val]? =
      (ForestZeroAdmissibleCaller.projectionConstantsCode width)[phase.val]?)
    (prepareAt : ∀ phase : Fin 19, resident[entry + 2 + phase.val]? =
      (ForestZeroAdmissibleCaller.channelPrepareCode width)[phase.val]?)
    (channelsFit : parameters.channels + 1 < 2 ^ width) (heapFits : state.heap.size ≤ 2 ^ width)
    (projectionRoom : projectionEntry + 14 < 2 ^ width)
    (projectionAt : ForestZeroChannelPush.CodeAt resident projectionEntry nativeEntry)
    (nativeRoom : nativeEntry + (NativeRetainedExecution.code parameters width state.heap.size nativeEntry).length < 2 ^ width)
    (nativeHeap : state.heap.size + parameters.channels + (compile parameters).toState.count < 2 ^ width)
    (nativeAt : ForestZeroCallerWiden.WidenedBlockAt resident nativeEntry
      (NativeRetainedExecution.code parameters width state.heap.size nativeEntry))
    (finishRoom : emitEntry parameters width state.heap.size nativeEntry + 3 * (compile parameters).toState.count + 7 < 2 ^ width)
    (emitAt : ForestZeroCallerWiden.WidenedBlockAt resident (emitEntry parameters width state.heap.size nativeEntry)
      (OutputProgram.emitCode width (NativeRealizedCore.addresses (state.heap.size + parameters.channels) (compile parameters).toState.count)))
    (releaseAt : Controller.Cost.RawTransferLoops.CodeAt resident
      (emitEntry parameters width state.heap.size nativeEntry + 3 * (compile parameters).toState.count)
      (SharedEvaluationReclaim.code width (emitEntry parameters width state.heap.size nativeEntry + 3 * (compile parameters).toState.count)
        done (parameters.channels + (compile parameters).toState.count))) :
    ∀ (keep count : Nat) (rest : List (Word width)) (returnPC : Nat),
    ∀ setupAt : ∀ phase : Fin 3, resident[done + 8 + phase.val]? = (ForestZeroReclaim.setupCode width)[phase.val]?,
    ∀ loopAt : ForestZeroReclaim.At resident (done + 11) returnPC,
    ∀ cleanupRoom : done + 15 < 2 ^ width,
    ∀ countFit : count < 2 ^ width,
    ∀ savedCount : state.stack = word width count :: word width layout.inverseBase ::
      word width dictionary.coordinates.size :: word width offBase :: rest,
    ∀ allocated : state.heap.size = keep + count,
    let K := setOfAssignment (SharedZeroNative.channels parameters dictionary queue within)
    ∃ final ticks peak, Execution resident state final ticks peak ∧
      ticks ≤ 55 * (selectedSize parameters).total + 4 * count + 46 ∧
      peak ≤ state.liveWords + 3 * (selectedSize parameters).total + 8 ∧
      final.heap.size = keep ∧
      final.stack = word width layout.inverseBase :: word width dictionary.coordinates.size :: word width offBase :: rest ∧
      final.output = (NativeRootLoad.words width
        (SourceLift.finite parameters (Physical.realizeBridge parameters.bridge parameters.positiveBuses K))).reverse ++ state.output ∧
      final.pc = word width returnPC ∧ final.halted = false ∧
      ForestZeroBackendFrame.PrefixFrame keep state.heap final.heap := by
  intro keep count rest returnPC setupAt loopAt cleanupRoom countFit savedCount allocated
  obtain ⟨ready, constants, heap, stack, output, zero, one, pc, active⟩ :=
    ForestZeroAdmissibleCaller.projection_constants_execution resident state entry position running (by omega) constantsAt
  have unchanged : ForestZeroBackendFrame.PrefixFrame state.heap.size state.heap ready.heap :=
    ⟨by omega, by rw [heap], fun _ _ => by rw [heap]⟩
  let readyLayout := ForestZeroAdmissibleCaller.retainedDictionaryLayout state.heap ready.heap state.heap.size layout
    unchanged layout.tableBound layout.inverseBound
  have readyDictionary : ForestZeroDictionary.Represented ready.heap readyLayout dictionary :=
    ForestZeroAdmissibleCaller.dictionary_prefix_transport state.heap ready.heap state.heap.size layout dictionary
      represented unchanged layout.tableBound layout.inverseBound
  have readyFifo : Controller.Horn.WorklistMark.Stored queue offBase ready.heap := by
    simpa only [heap] using fifo
  obtain ⟨final, ticks, peak, trace, timeBound, spaceBound, size, finalStack, finalOutput, finalPC, finalActive, frame⟩ :=
    execution parameters resident ready (entry + 2) saveEntry projectionEntry nativeEntry offBase done nodes dictionary
      readyLayout readyDictionary ambientEq adjacent within queue readyFifo countFits pc active projectionEq saveAt
      restoreRoom restoreAt (by omega) zero one (by simpa only [heap] using channelCell)
      (by simpa only [heap] using nodeCell) (by simpa only [heap] using headerRoom) offRoom
      (by omega) prepareAt channelsFit (by simpa only [heap] using heapFits) projectionRoom projectionAt
      (by simpa only [heap] using nativeRoom) (by simpa only [heap] using nativeHeap)
      (by simpa only [heap] using nativeAt) (by simpa only [heap] using finishRoom)
      (by simpa only [heap] using emitAt) (by simpa only [heap] using releaseAt)
      keep count rest returnPC setupAt loopAt cleanupRoom countFit
      (by simpa [readyLayout, ForestZeroAdmissibleCaller.retainedDictionaryLayout, stack] using savedCount)
      (by simpa only [heap] using allocated)
  have live : ready.liveWords = state.liveWords := by
    simp only [State.liveWords, heap, stack, output]
  refine ⟨final, 2 + ticks, max state.liveWords peak, constants.append trace,
    by omega, ?_, size, ?_, ?_, finalPC, finalActive, ?_⟩
  · rw [live] at spaceBound
    omega
  · simpa [readyLayout, ForestZeroAdmissibleCaller.retainedDictionaryLayout] using finalStack
  · simpa only [output] using finalOutput
  · simpa only [heap] using frame

theorem initialized_native_execution {ambient : Nat}
    (parameters : Parameters)
    (dictionary : Dictionary ambient) (keep : Nat)
    (formula : Controller.CNF.Formula (Fin dictionary.coordinates.size)) (dual : Controller.Horn.DualHorn formula)
    (recordHeader recordStart recordEnd base entry scan seedDone conflict : Nat)
    (state : State width 8) (program : Program width 8)
    (physical : Controller.Horn.IndexScan.PhysicalIndex (formula.clauses.toList) recordStart recordEnd base
      (Controller.Horn.IndexScan.occurrences (formula.clauses.toList) recordStart).length state.heap)
    (header : Controller.Horn.SourceScan.CursorStored recordEnd recordHeader state.heap)
    (fifo : Controller.Horn.WorklistMark.Stored ([] : List (Fin dictionary.coordinates.size)) base state.heap)
    (separated : base + 5 * dictionary.coordinates.size + 4 ≤ recordStart)
    (setupAt : ∀ phase : Fin 10, program[entry + phase.val]? =
      (Controller.Cost.ForestZeroSeedSetup.code (n := dictionary.coordinates.size) width base recordHeader recordStart scan)[phase.val]?)
    (scanAt : Controller.Horn.WorklistSeed.At (n := dictionary.coordinates.size) program base scan seedDone conflict)
    (position : state.pc = word width entry) (running : state.halted = false)
    (zero : state.reg 2 = word width 0) (one : state.reg 5 = word width 1)
    (room : state.heap.size < 2 ^ width) (setupCapacity : entry + 10 < 2 ^ width)
    (scanCapacity : scan + 47 < 2 ^ width)
    (prefixBound : keep ≤ state.heap.size) (prefixBelow : keep ≤ base)
    (fetch : Nat)
    (headAt : ∀ phase : Fin 4, program[seedDone + phase.val]? =
      (Controller.Horn.WorklistAccept.headSetupCode (n := dictionary.coordinates.size) width base fetch)[phase.val]?)
    (headCapacity : seedDone + 4 < 2 ^ width)
    (fifoDone bucket advance ready skip : Nat)
    (fetchAt : Controller.Horn.WorklistFIFO.FetchAt (n := dictionary.coordinates.size) program base fetch fifoDone bucket)
    (advanceAt : Controller.Horn.WorklistFIFO.AdvanceAt (n := dictionary.coordinates.size) program base advance fetch)
    (loopAt : Controller.Horn.WorklistBucketLoop.At program bucket advance ready)
    (readyAt : Controller.Horn.WorklistBucketReady.At (n := dictionary.coordinates.size) program base ready skip conflict bucket)
    (fetchCapacity : fetch + 14 < 2 ^ width) (advanceCapacity : advance + 5 < 2 ^ width)
    (bucketCapacity : bucket + 12 < 2 ^ width) (readyCapacity : ready + 26 < 2 ^ width)
    (projectionEntry cleanupEntry returnPc : Nat)
    (successAt : Controller.Cost.ForestZeroAnswer.At program fifoDone 1 projectionEntry)
    (conflictAt : Controller.Cost.ForestZeroAnswer.At program conflict 0 cleanupEntry)
    (successCapacity : fifoDone + 4 < 2 ^ width)
    (conflictCapacity : conflict + 4 < 2 ^ width)
    (layout : ForestZeroDictionary.Layout ambient state.heap.size)
    (represented : Represented state.heap layout dictionary)
    (nodes count : Nat)
    (ambientEq : ambient = parameters.channels + nodes)
    (adjacent : layout.inverseBase = layout.tableBase + ambient)
    (tableBefore : layout.tableBase + ambient ≤ keep)
    (inverseBefore : layout.inverseBase + ambient ≤ keep)
    (headersBefore : 1 < keep)
    (channelsCell : state.heap[0]? = some (word width parameters.channels))
    (nodesCell : state.heap[1]? = some (word width nodes))
    (localFit : dictionary.coordinates.size + 1 < 2 ^ width)
    (channelsFit : parameters.channels + 1 < 2 ^ width) (offRoom : base + 1 < 2 ^ width)
    (projectionCapacity : projectionEntry + 35 < 2 ^ width)
    (constantsAt : ∀ phase : Fin 2, program[projectionEntry + phase.val]? =
      (projectionConstantsCode width)[phase.val]?)
    (preparationAt : ∀ phase : Fin 19, program[projectionEntry + 2 + phase.val]? =
      (channelPrepareCode width)[phase.val]?)
    (saveEntry pushEntry nativeEntry done : Nat)
    (saveEq : saveEntry = projectionEntry + 21)
    (projectionEq : pushEntry = saveEntry + 8)
    (saveAt : SharedRootRead.BlockAt program saveEntry (SharedRegisterStack.saveCode (width := width) (List.finRange 8)))
    (restoreRoom : done + 8 < 2 ^ width)
    (restoreAt : SharedRootRead.BlockAt program done (SharedRegisterStack.restoreCode (width := width) (List.finRange 8).reverse))
    (projectionRoom : pushEntry + 14 < 2 ^ width)
    (projectionAt : ForestZeroChannelPush.CodeAt program pushEntry nativeEntry)
    (nativeRoom : nativeEntry + (NativeRetainedExecution.code parameters width state.heap.size nativeEntry).length < 2 ^ width)
    (nativeHeap : state.heap.size + parameters.channels + (compile parameters).toState.count < 2 ^ width)
    (nativeAt : ForestZeroCallerWiden.WidenedBlockAt program nativeEntry
      (NativeRetainedExecution.code parameters width state.heap.size nativeEntry))
    (finishRoom : emitEntry parameters width state.heap.size nativeEntry + 3 * (compile parameters).toState.count + 7 < 2 ^ width)
    (emitAt : ForestZeroCallerWiden.WidenedBlockAt program (emitEntry parameters width state.heap.size nativeEntry)
      (OutputProgram.emitCode width (NativeRealizedCore.addresses (state.heap.size + parameters.channels) (compile parameters).toState.count)))
    (releaseAt : Controller.Cost.RawTransferLoops.CodeAt program
      (emitEntry parameters width state.heap.size nativeEntry + 3 * (compile parameters).toState.count)
      (SharedEvaluationReclaim.code width (emitEntry parameters width state.heap.size nativeEntry + 3 * (compile parameters).toState.count)
        done (parameters.channels + (compile parameters).toState.count)))
    (nativeSetup : ∀ phase : Fin 3, program[done + 8 + phase.val]? =
      (Controller.Cost.ForestZeroReclaim.setupCode width)[phase.val]?)
    (nativeLoop : Controller.Cost.ForestZeroReclaim.At program (done + 11) returnPc)
    (nativeCleanupRoom : done + 15 < 2 ^ width)
    (cleanupSetup : ∀ phase : Fin 3, program[cleanupEntry + phase.val]? =
      (Controller.Cost.ForestZeroReclaim.setupCode width)[phase.val]?)
    (cleanupLoop : Controller.Cost.ForestZeroReclaim.At program (cleanupEntry + 3) returnPc)
    (cleanupCapacity : cleanupEntry + 7 < 2 ^ width) (countFits : count < 2 ^ width)
    (rest : List (Word width))
    (savedCount : state.stack = word width count :: word width layout.inverseBase ::
      word width dictionary.coordinates.size :: word width base :: rest)
    (allocated : state.heap.size = keep + count) :
    ∃ answer : Bool, ∃ queue final ticks peak,
      Execution program state final ticks peak ∧
      ticks ≤ 36 * formula.clauses.toList.length +
        32 * (Controller.Horn.IndexScan.occurrences formula.clauses.toList recordStart).length +
        26 * dictionary.coordinates.size + 55 * (selectedSize parameters).total + 4 * count + 74 ∧
      peak ≤ state.liveWords + 3 * (selectedSize parameters).total + 9 ∧ final.heap.size = keep ∧
      final.stack = word width layout.inverseBase :: word width dictionary.coordinates.size ::
        word width base :: rest ∧
      final.output = (if answer then (NativeRootLoad.words width
        (SourceLift.finite parameters (Physical.realizeBridge parameters.bridge parameters.positiveBuses
          (setOfAssignment (SharedZeroNative.channels parameters dictionary queue
            (by rw [ambientEq]; omega)))))).reverse ++
          word width 1 :: state.output else word width 0 :: state.output) ∧
      final.pc = word width returnPc ∧ final.halted = false ∧
      Controller.Cost.ForestZeroBackendFrame.PrefixFrame keep state.heap final.heap ∧
      (answer = true ↔ ∃ assignment, Controller.CNF.Satisfies assignment formula) ∧
      (answer = true → Controller.CNF.Satisfies (Controller.Horn.WorklistOutcome.offAssignment queue) formula ∧
        Controller.Horn.WorklistOutcome.offAssignment queue = Controller.Horn.greatestCandidate formula)
 := by
  obtain ⟨queue, middle, firstTicks, firstBound, first, middleSize,
      middleStack, middleOutput, firstFrame, outcome⟩ :=
    Controller.Cost.ForestZeroOutcome.initialized_original_execution keep formula dual
      recordHeader recordStart recordEnd base entry scan seedDone conflict state program
      physical header fifo separated setupAt scanAt position running zero one room
      setupCapacity scanCapacity prefixBound prefixBelow fetch headAt headCapacity
      fifoDone bucket advance ready skip fetchAt advanceAt loopAt readyAt
      fetchCapacity advanceCapacity bucketCapacity readyCapacity
  have middleLive : middle.liveWords = state.liveWords := by
    unfold State.liveWords
    rw [middleSize, middleStack, middleOutput]
  rcases outcome with ⟨pc, live, noModels⟩ | ⟨fired, finished, model, forced⟩
  · obtain ⟨tagged, tagTrace, tagHeap, tagStack, tagOutput, tagPC, tagRunning, tagFrame⟩ :=
      Controller.Cost.ForestZeroAnswer.execution keep program conflict 0 cleanupEntry middle
        conflictAt pc live conflictCapacity (by omega) (by rw [middleSize]; exact prefixBound)
    let savedRest := word width layout.inverseBase :: word width dictionary.coordinates.size ::
      word width base :: rest
    obtain ⟨final, cleanup, finalSize, finalStack, finalOutput, finalPC, finalRunning, lastFrame⟩ :=
      Controller.Cost.ForestZeroReclaim.stacked_execution program cleanupEntry returnPc keep count
        tagged savedRest cleanupSetup cleanupLoop tagPC tagRunning cleanupCapacity countFits
        (tagStack.trans (middleStack.trans savedCount))
        (by rw [tagHeap, middleSize]; exact allocated)
    have taggedLive : tagged.liveWords = state.liveWords + 1 := by
      unfold State.liveWords
      rw [tagHeap, middleSize, tagStack, middleStack, tagOutput, middleOutput]
      simp only [List.length_cons]
      omega
    refine ⟨false, queue, final, firstTicks + 4 + (4 * count + 4),
      max state.liveWords (max (middle.liveWords + 1) tagged.liveWords),
      (by simpa only [Nat.add_assoc] using first.append (tagTrace.append cleanup)),
      by omega, ?_, finalSize, finalStack,
      ?_, finalPC, finalRunning,
      Controller.Cost.ForestZeroBackendFrame.trans firstFrame
        (Controller.Cost.ForestZeroBackendFrame.trans tagFrame lastFrame), ?_, ?_⟩
    · rw [middleLive, taggedLive]
      omega
    · simpa only [Bool.false_eq_true, ite_false, savedRest, tagOutput, middleOutput] using finalOutput
    · constructor
      · intro impossible
        cases impossible
      · intro possible
        exact False.elim (noModels possible)
    · intro impossible
      cases impossible
  · obtain ⟨tagged, tagTrace, tagHeap, tagStack, tagOutput, tagPC, tagRunning, tagFrame⟩ :=
      Controller.Cost.ForestZeroAnswer.execution keep program fifoDone 1 projectionEntry middle
        successAt finished.position finished.running successCapacity (by omega)
        (by rw [middleSize]; exact prefixBound)
    have taggedFrame := Controller.Cost.ForestZeroBackendFrame.trans firstFrame tagFrame
    let taggedLayout := retainedDictionaryLayout state.heap tagged.heap keep layout taggedFrame
      tableBefore inverseBefore
    have taggedDictionary : Represented tagged.heap taggedLayout dictionary :=
      dictionary_prefix_transport state.heap tagged.heap keep layout dictionary represented
        taggedFrame tableBefore inverseBefore
    have taggedFifo : Controller.Horn.WorklistMark.Stored queue base tagged.heap := by
      simpa only [tagHeap] using finished.fifo
    obtain ⟨channelsStored, nodesStored⟩ := projection_headers_transport state.heap tagged.heap
      keep parameters.channels nodes taggedFrame headersBefore channelsCell nodesCell
    obtain ⟨final, lastTicks, lastPeak, suffix, suffixTime, suffixSpace, finalSize, finalStack,
        finalOutput, finalPC, finalRunning, suffixFrame⟩ :=
      terminal_execution parameters program tagged projectionEntry saveEntry pushEntry nativeEntry base done nodes
        dictionary taggedLayout taggedDictionary ambientEq adjacent (by rw [ambientEq]; omega) queue taggedFifo
        localFit tagPC tagRunning projectionEq saveAt restoreRoom restoreAt saveEq channelsStored nodesStored
        (by have := taggedFrame.2.1; omega) offRoom (by omega) constantsAt preparationAt channelsFit
        (by rw [tagHeap, middleSize]; omega) projectionRoom projectionAt
        (by simpa only [tagHeap, middleSize] using nativeRoom)
        (by simpa only [tagHeap, middleSize] using nativeHeap)
        (by simpa only [tagHeap, middleSize] using nativeAt)
        (by simpa only [tagHeap, middleSize] using finishRoom)
        (by simpa only [tagHeap, middleSize] using emitAt)
        (by simpa only [tagHeap, middleSize] using releaseAt)
        keep count rest returnPc nativeSetup nativeLoop nativeCleanupRoom countFits
        (tagStack.trans (middleStack.trans savedCount))
        (by rw [tagHeap, middleSize]; exact allocated)
    have taggedLive : tagged.liveWords = state.liveWords + 1 := by
      unfold State.liveWords
      rw [tagHeap, middleSize, tagStack, middleStack, tagOutput, middleOutput]
      simp only [List.length_cons]
      omega
    refine ⟨true, queue, final, firstTicks + 4 + lastTicks,
      max state.liveWords (max (middle.liveWords + 1) lastPeak),
      (by simpa only [Nat.add_assoc] using first.append (tagTrace.append suffix)),
      by omega, ?_, finalSize, finalStack,
      ?_, finalPC, finalRunning,
      Controller.Cost.ForestZeroBackendFrame.trans taggedFrame suffixFrame,
      ⟨fun _ => ⟨Controller.Horn.WorklistOutcome.offAssignment queue, model⟩, fun _ => rfl⟩,
      fun _ => ⟨model, Controller.Cost.ForestZeroAnswerReclaim.terminal_greatest formula dual
        queue model forced⟩⟩
    · rw [taggedLive] at suffixSpace
      rw [middleLive]
      omega
    · simpa only [ite_true, tagOutput, middleOutput] using finalOutput


theorem native_reset_execution {ambient : Nat}
    (parameters : Parameters)
    (dictionary : Dictionary ambient) (keep : Nat)
    (formula : Controller.CNF.Formula (Fin dictionary.coordinates.size)) (dual : Controller.Horn.DualHorn formula)
    (recordHeader recordStart recordEnd base entry scan seedDone conflict : Nat)
    (state : State width 8) (program : Program width 8)
    (physical : Controller.Horn.IndexScan.PhysicalIndex (formula.clauses.toList) recordStart recordEnd base
      (Controller.Horn.IndexScan.occurrences (formula.clauses.toList) recordStart).length state.heap)
    (header : Controller.Horn.SourceScan.CursorStored recordEnd recordHeader state.heap)
    (fifo : Controller.Horn.WorklistMark.Stored ([] : List (Fin dictionary.coordinates.size)) base state.heap)
    (separated : base + 5 * dictionary.coordinates.size + 4 ≤ recordStart)
    (setupAt : ∀ phase : Fin 10, program[entry + phase.val]? =
      (Controller.Cost.ForestZeroSeedSetup.code (n := dictionary.coordinates.size) width base recordHeader recordStart scan)[phase.val]?)
    (scanAt : Controller.Horn.WorklistSeed.At (n := dictionary.coordinates.size) program base scan seedDone conflict)
    (position : state.pc = word width entry) (running : state.halted = false)
    (zero : state.reg 2 = word width 0) (one : state.reg 5 = word width 1)
    (room : state.heap.size < 2 ^ width) (setupCapacity : entry + 10 < 2 ^ width)
    (scanCapacity : scan + 47 < 2 ^ width)
    (prefixBound : keep ≤ state.heap.size) (prefixBelow : keep ≤ base)
    (fetch : Nat)
    (headAt : ∀ phase : Fin 4, program[seedDone + phase.val]? =
      (Controller.Horn.WorklistAccept.headSetupCode (n := dictionary.coordinates.size) width base fetch)[phase.val]?)
    (headCapacity : seedDone + 4 < 2 ^ width)
    (fifoDone bucket advance ready skip : Nat)
    (fetchAt : Controller.Horn.WorklistFIFO.FetchAt (n := dictionary.coordinates.size) program base fetch fifoDone bucket)
    (advanceAt : Controller.Horn.WorklistFIFO.AdvanceAt (n := dictionary.coordinates.size) program base advance fetch)
    (loopAt : Controller.Horn.WorklistBucketLoop.At program bucket advance ready)
    (readyAt : Controller.Horn.WorklistBucketReady.At (n := dictionary.coordinates.size) program base ready skip conflict bucket)
    (fetchCapacity : fetch + 14 < 2 ^ width) (advanceCapacity : advance + 5 < 2 ^ width)
    (bucketCapacity : bucket + 12 < 2 ^ width) (readyCapacity : ready + 26 < 2 ^ width)
    (projectionEntry cleanupEntry returnPc : Nat)
    (successAt : Controller.Cost.ForestZeroAnswer.At program fifoDone 1 projectionEntry)
    (conflictAt : Controller.Cost.ForestZeroAnswer.At program conflict 0 cleanupEntry)
    (successCapacity : fifoDone + 4 < 2 ^ width)
    (conflictCapacity : conflict + 4 < 2 ^ width)
    (layout : ForestZeroDictionary.Layout ambient state.heap.size)
    (represented : Represented state.heap layout dictionary)
    (nodes count : Nat)
    (ambientEq : ambient = parameters.channels + nodes)
    (adjacent : layout.inverseBase = layout.tableBase + ambient)
    (tableBefore : layout.tableBase + ambient ≤ keep)
    (inverseBefore : layout.inverseBase + ambient ≤ keep)
    (headersBefore : 1 < keep)
    (channelsCell : state.heap[0]? = some (word width parameters.channels))
    (nodesCell : state.heap[1]? = some (word width nodes))
    (localFit : dictionary.coordinates.size + 1 < 2 ^ width)
    (channelsFit : parameters.channels + 1 < 2 ^ width) (offRoom : base + 1 < 2 ^ width)
    (projectionCapacity : projectionEntry + 35 < 2 ^ width)
    (constantsAt : ∀ phase : Fin 2, program[projectionEntry + phase.val]? =
      (projectionConstantsCode width)[phase.val]?)
    (preparationAt : ∀ phase : Fin 19, program[projectionEntry + 2 + phase.val]? =
      (channelPrepareCode width)[phase.val]?)
    (saveEntry pushEntry nativeEntry done : Nat)
    (saveEq : saveEntry = projectionEntry + 21)
    (projectionEq : pushEntry = saveEntry + 8)
    (saveAt : SharedRootRead.BlockAt program saveEntry (SharedRegisterStack.saveCode (width := width) (List.finRange 8)))
    (restoreRoom : done + 8 < 2 ^ width)
    (restoreAt : SharedRootRead.BlockAt program done (SharedRegisterStack.restoreCode (width := width) (List.finRange 8).reverse))
    (projectionRoom : pushEntry + 14 < 2 ^ width)
    (projectionAt : ForestZeroChannelPush.CodeAt program pushEntry nativeEntry)
    (nativeRoom : nativeEntry + (NativeRetainedExecution.code parameters width state.heap.size nativeEntry).length < 2 ^ width)
    (nativeHeap : state.heap.size + parameters.channels + (compile parameters).toState.count < 2 ^ width)
    (nativeAt : ForestZeroCallerWiden.WidenedBlockAt program nativeEntry
      (NativeRetainedExecution.code parameters width state.heap.size nativeEntry))
    (finishRoom : emitEntry parameters width state.heap.size nativeEntry + 3 * (compile parameters).toState.count + 7 < 2 ^ width)
    (emitAt : ForestZeroCallerWiden.WidenedBlockAt program (emitEntry parameters width state.heap.size nativeEntry)
      (OutputProgram.emitCode width (NativeRealizedCore.addresses (state.heap.size + parameters.channels) (compile parameters).toState.count)))
    (releaseAt : Controller.Cost.RawTransferLoops.CodeAt program
      (emitEntry parameters width state.heap.size nativeEntry + 3 * (compile parameters).toState.count)
      (SharedEvaluationReclaim.code width (emitEntry parameters width state.heap.size nativeEntry + 3 * (compile parameters).toState.count)
        done (parameters.channels + (compile parameters).toState.count)))
    (nativeSetup : ∀ phase : Fin 3, program[done + 8 + phase.val]? =
      (Controller.Cost.ForestZeroReclaim.setupCode width)[phase.val]?)
    (nativeLoop : Controller.Cost.ForestZeroReclaim.At program (done + 11) returnPc)
    (nativeCleanupRoom : done + 15 < 2 ^ width)
    (cleanupSetup : ∀ phase : Fin 3, program[cleanupEntry + phase.val]? =
      (Controller.Cost.ForestZeroReclaim.setupCode width)[phase.val]?)
    (cleanupLoop : Controller.Cost.ForestZeroReclaim.At program (cleanupEntry + 3) returnPc)
    (cleanupCapacity : cleanupEntry + 7 < 2 ^ width) (countFits : count < 2 ^ width)
    (rest : List (Word width))
    (savedCount : state.stack = word width count :: word width layout.inverseBase ::
      word width dictionary.coordinates.size :: word width base :: rest)
    (allocated : state.heap.size = keep + count)
    (tablePositive : 0 < layout.tableBase)
    (resetCapacity : returnPc + 27 < 2 ^ width)
    (resetPrepareAt : ForestZeroCallerWiden.WidenedBlockAt program returnPc (resetPrepareCode width).toList)
    (resetLoopAt : ForestZeroCallerWiden.WidenedBlockAt program (returnPc + 15)
      (Controller.Cost.ForestZeroReset.code width (returnPc + 15))) :
    ∃ answer : Bool, ∃ queue final ticks peak,
      Execution program state final ticks peak ∧
      ticks ≤ 36 * formula.clauses.toList.length +
        32 * (Controller.Horn.IndexScan.occurrences formula.clauses.toList recordStart).length +
        38 * dictionary.coordinates.size + 55 * (selectedSize parameters).total + 4 * count + 90 ∧
      peak ≤ state.liveWords + 3 * (selectedSize parameters).total + 9 ∧ final.heap.size = keep ∧
      final.stack = rest ∧
      final.output = (if answer then (NativeRootLoad.words width
        (SourceLift.finite parameters (Physical.realizeBridge parameters.bridge parameters.positiveBuses
          (setOfAssignment (SharedZeroNative.channels parameters dictionary queue
            (by rw [ambientEq]; omega)))))).reverse ++
          word width 1 :: state.output else word width 0 :: state.output) ∧
      final.pc = word width (returnPc + 27) ∧ final.halted = false ∧
      Controller.Cost.ForestZeroBackendFrame.PrefixFrame layout.tableBase state.heap final.heap ∧
      (∀ coordinate : Fin ambient, final.heap[layout.tableBase + coordinate.val]? = some (word width 0)) ∧
      (answer = true ↔ ∃ assignment, Controller.CNF.Satisfies assignment formula) ∧
      (answer = true → Controller.CNF.Satisfies (Controller.Horn.WorklistOutcome.offAssignment queue) formula ∧
        Controller.Horn.WorklistOutcome.offAssignment queue = Controller.Horn.greatestCandidate formula) := by
  obtain ⟨answer, queue, reclaimed, firstTicks, firstPeak, first, timeBound, spaceBound,
      reclaimedSize, reclaimedStack, reclaimedOutput, reclaimedPC, reclaimedRunning,
      reclaimedFrame, meaning, greatest⟩ :=
    initialized_native_execution parameters dictionary keep formula dual
      recordHeader recordStart recordEnd base entry scan seedDone conflict state program
      physical header fifo separated setupAt scanAt position running zero one room
      setupCapacity scanCapacity prefixBound prefixBelow fetch headAt headCapacity fifoDone
      bucket advance ready skip fetchAt advanceAt loopAt readyAt fetchCapacity advanceCapacity
      bucketCapacity readyCapacity projectionEntry cleanupEntry returnPc successAt conflictAt
      successCapacity conflictCapacity layout represented nodes count ambientEq adjacent
      tableBefore inverseBefore headersBefore channelsCell nodesCell localFit channelsFit
      offRoom projectionCapacity constantsAt preparationAt saveEntry pushEntry nativeEntry done
      saveEq projectionEq saveAt restoreRoom restoreAt projectionRoom projectionAt nativeRoom nativeHeap nativeAt
      finishRoom emitAt releaseAt nativeSetup nativeLoop nativeCleanupRoom cleanupSetup cleanupLoop
      cleanupCapacity countFits rest savedCount allocated
  let reclaimedLayout := retainedDictionaryLayout state.heap reclaimed.heap keep layout
    reclaimedFrame tableBefore inverseBefore
  have reclaimedDictionary : Represented reclaimed.heap reclaimedLayout dictionary :=
    dictionary_prefix_transport state.heap reclaimed.heap keep layout dictionary represented
      reclaimedFrame tableBefore inverseBefore
  obtain ⟨channelHeader, nodeHeader⟩ := projection_headers_transport state.heap reclaimed.heap
    keep parameters.channels nodes reclaimedFrame headersBefore channelsCell nodesCell
  obtain ⟨final, reset, finalHeap, finalStack, finalOutput, finalPC, finalRunning,
      resetFrame, zeroSlots⟩ :=
    retained_dictionary_reset_execution program reclaimed returnPc parameters.channels nodes dictionary
      reclaimedLayout reclaimedDictionary ambientEq adjacent tablePositive (word width base)
      rest reclaimedStack reclaimedPC reclaimedRunning channelHeader nodeHeader
      (by rw [reclaimedSize]; exact headersBefore)
      (by rw [reclaimedSize]; omega) resetCapacity resetPrepareAt resetLoopAt
  have sourceBound : layout.tableBase ≤ keep := by omega
  have sourceFrame : Controller.Cost.ForestZeroBackendFrame.PrefixFrame layout.tableBase
      state.heap reclaimed.heap :=
    ⟨by omega, by rw [reclaimedSize]; omega,
      fun address below => reclaimedFrame.2.2 address (lt_of_lt_of_le below sourceBound)⟩
  have reclaimedLive : reclaimed.liveWords ≤ firstPeak := first.final_storage_le
  refine ⟨answer, queue, final, firstTicks + (12 * dictionary.coordinates.size + 16),
    max firstPeak reclaimed.liveWords, first.append reset, ?_, ?_, ?_, finalStack,
    finalOutput.trans reclaimedOutput, finalPC, finalRunning,
    Controller.Cost.ForestZeroBackendFrame.trans sourceFrame resetFrame, zeroSlots,
    meaning, greatest⟩
  · omega
  · omega
  · rw [finalHeap, Controller.Cost.ForestZeroReset.resetHeap_size, reclaimedSize]

theorem initialized_native_saved_execution {ambient : Nat}
    (parameters : Parameters)
    (dictionary : Dictionary ambient) (keep : Nat)
    (formula : Controller.CNF.Formula (Fin dictionary.coordinates.size)) (dual : Controller.Horn.DualHorn formula)
    (recordHeader recordStart recordEnd base entry scan seedDone conflict : Nat)
    (state : State width 8) (program : Program width 8)
    (physical : Controller.Horn.IndexScan.PhysicalIndex (formula.clauses.toList) recordStart recordEnd base
      (Controller.Horn.IndexScan.occurrences (formula.clauses.toList) recordStart).length state.heap)
    (header : Controller.Horn.SourceScan.CursorStored recordEnd recordHeader state.heap)
    (fifo : Controller.Horn.WorklistMark.Stored ([] : List (Fin dictionary.coordinates.size)) base state.heap)
    (separated : base + 5 * dictionary.coordinates.size + 4 ≤ recordStart)
    (setupAt : ∀ phase : Fin 10, program[entry + phase.val]? =
      (Controller.Cost.ForestZeroSeedSetup.code (n := dictionary.coordinates.size) width base recordHeader recordStart scan)[phase.val]?)
    (scanAt : Controller.Horn.WorklistSeed.At (n := dictionary.coordinates.size) program base scan seedDone conflict)
    (position : state.pc = word width entry) (running : state.halted = false)
    (zero : state.reg 2 = word width 0) (one : state.reg 5 = word width 1)
    (room : state.heap.size < 2 ^ width) (setupCapacity : entry + 10 < 2 ^ width)
    (scanCapacity : scan + 47 < 2 ^ width)
    (prefixBound : keep ≤ state.heap.size) (prefixBelow : keep ≤ base)
    (fetch : Nat)
    (headAt : ∀ phase : Fin 4, program[seedDone + phase.val]? =
      (Controller.Horn.WorklistAccept.headSetupCode (n := dictionary.coordinates.size) width base fetch)[phase.val]?)
    (headCapacity : seedDone + 4 < 2 ^ width)
    (fifoDone bucket advance ready skip : Nat)
    (fetchAt : Controller.Horn.WorklistFIFO.FetchAt (n := dictionary.coordinates.size) program base fetch fifoDone bucket)
    (advanceAt : Controller.Horn.WorklistFIFO.AdvanceAt (n := dictionary.coordinates.size) program base advance fetch)
    (loopAt : Controller.Horn.WorklistBucketLoop.At program bucket advance ready)
    (readyAt : Controller.Horn.WorklistBucketReady.At (n := dictionary.coordinates.size) program base ready skip conflict bucket)
    (fetchCapacity : fetch + 14 < 2 ^ width) (advanceCapacity : advance + 5 < 2 ^ width)
    (bucketCapacity : bucket + 12 < 2 ^ width) (readyCapacity : ready + 26 < 2 ^ width)
    (projectionEntry cleanupEntry returnPc : Nat)
    (successAt : Controller.Cost.ForestZeroAnswer.SavedAt program fifoDone 1 projectionEntry)
    (conflictAt : Controller.Cost.ForestZeroAnswer.SavedAt program conflict 0 cleanupEntry)
    (successCapacity : fifoDone + 13 < 2 ^ width)
    (conflictCapacity : conflict + 13 < 2 ^ width)
    (layout : ForestZeroDictionary.Layout ambient state.heap.size)
    (represented : Represented state.heap layout dictionary)
    (nodes count : Nat)
    (ambientEq : ambient = parameters.channels + nodes)
    (adjacent : layout.inverseBase = layout.tableBase + ambient)
    (tableBefore : layout.tableBase + ambient ≤ keep)
    (inverseBefore : layout.inverseBase + ambient ≤ keep)
    (headersBefore : 1 < keep)
    (channelsCell : state.heap[0]? = some (word width parameters.channels))
    (nodesCell : state.heap[1]? = some (word width nodes))
    (localFit : dictionary.coordinates.size + 1 < 2 ^ width)
    (channelsFit : parameters.channels + 1 < 2 ^ width) (offRoom : base + 1 < 2 ^ width)
    (projectionCapacity : projectionEntry + 35 < 2 ^ width)
    (constantsAt : ∀ phase : Fin 2, program[projectionEntry + phase.val]? =
      (projectionConstantsCode width)[phase.val]?)
    (preparationAt : ∀ phase : Fin 19, program[projectionEntry + 2 + phase.val]? =
      (channelPrepareCode width)[phase.val]?)
    (saveEntry pushEntry nativeEntry done : Nat)
    (saveEq : saveEntry = projectionEntry + 21)
    (projectionEq : pushEntry = saveEntry + 8)
    (saveAt : SharedRootRead.BlockAt program saveEntry (SharedRegisterStack.saveCode (width := width) (List.finRange 8)))
    (restoreRoom : done + 8 < 2 ^ width)
    (restoreAt : SharedRootRead.BlockAt program done (SharedRegisterStack.restoreCode (width := width) (List.finRange 8).reverse))
    (projectionRoom : pushEntry + 14 < 2 ^ width)
    (projectionAt : ForestZeroChannelPush.CodeAt program pushEntry nativeEntry)
    (nativeRoom : nativeEntry + (NativeRetainedExecution.code parameters width state.heap.size nativeEntry).length < 2 ^ width)
    (nativeHeap : state.heap.size + parameters.channels + (compile parameters).toState.count < 2 ^ width)
    (nativeAt : ForestZeroCallerWiden.WidenedBlockAt program nativeEntry
      (NativeRetainedExecution.code parameters width state.heap.size nativeEntry))
    (finishRoom : emitEntry parameters width state.heap.size nativeEntry + 3 * (compile parameters).toState.count + 7 < 2 ^ width)
    (emitAt : ForestZeroCallerWiden.WidenedBlockAt program (emitEntry parameters width state.heap.size nativeEntry)
      (OutputProgram.emitCode width (NativeRealizedCore.addresses (state.heap.size + parameters.channels) (compile parameters).toState.count)))
    (releaseAt : Controller.Cost.RawTransferLoops.CodeAt program
      (emitEntry parameters width state.heap.size nativeEntry + 3 * (compile parameters).toState.count)
      (SharedEvaluationReclaim.code width (emitEntry parameters width state.heap.size nativeEntry + 3 * (compile parameters).toState.count)
        done (parameters.channels + (compile parameters).toState.count)))
    (nativeSetup : ∀ phase : Fin 3, program[done + 8 + phase.val]? =
      (Controller.Cost.ForestZeroReclaim.setupCode width)[phase.val]?)
    (nativeLoop : Controller.Cost.ForestZeroReclaim.At program (done + 11) returnPc)
    (nativeCleanupRoom : done + 15 < 2 ^ width)
    (cleanupSetup : ∀ phase : Fin 3, program[cleanupEntry + phase.val]? =
      (Controller.Cost.ForestZeroReclaim.setupCode width)[phase.val]?)
    (cleanupLoop : Controller.Cost.ForestZeroReclaim.At program (cleanupEntry + 3) returnPc)
    (cleanupCapacity : cleanupEntry + 7 < 2 ^ width) (countFits : count < 2 ^ width)
    (rest : List (Word width))
    (savedCount : state.stack = word width count :: word width layout.inverseBase ::
      word width dictionary.coordinates.size :: word width base :: rest)
    (allocated : state.heap.size = keep + count) :
    ∃ answer : Bool, ∃ queue final ticks peak,
      Execution program state final ticks peak ∧
      ticks ≤ 36 * formula.clauses.toList.length +
        32 * (Controller.Horn.IndexScan.occurrences formula.clauses.toList recordStart).length +
        26 * dictionary.coordinates.size + 4 * count + (if answer then 55 * (selectedSize parameters).total + 83 else 41) ∧
      peak ≤ state.liveWords + 3 * (selectedSize parameters).total + 10 ∧ final.heap.size = keep ∧
      final.stack = word width layout.inverseBase :: word width dictionary.coordinates.size ::
        word width base :: word width (if answer then 1 else 0) :: rest ∧
      final.output = (if answer then (NativeRootLoad.words width
        (SourceLift.finite parameters (Physical.realizeBridge parameters.bridge parameters.positiveBuses
          (setOfAssignment (SharedZeroNative.channels parameters dictionary queue
            (by rw [ambientEq]; omega)))))).reverse ++
          word width 1 :: state.output else word width 0 :: state.output) ∧
      final.pc = word width returnPc ∧ final.halted = false ∧
      Controller.Cost.ForestZeroBackendFrame.PrefixFrame keep state.heap final.heap ∧
      (answer = true ↔ ∃ assignment, Controller.CNF.Satisfies assignment formula) ∧
      (answer = true → Controller.CNF.Satisfies (Controller.Horn.WorklistOutcome.offAssignment queue) formula ∧
        Controller.Horn.WorklistOutcome.offAssignment queue = Controller.Horn.greatestCandidate formula)
 := by
  obtain ⟨queue, middle, firstTicks, firstBound, first, middleSize,
      middleStack, middleOutput, firstFrame, outcome⟩ :=
    Controller.Cost.ForestZeroOutcome.initialized_original_execution keep formula dual
      recordHeader recordStart recordEnd base entry scan seedDone conflict state program
      physical header fifo separated setupAt scanAt position running zero one room
      setupCapacity scanCapacity prefixBound prefixBelow fetch headAt headCapacity
      fifoDone bucket advance ready skip fetchAt advanceAt loopAt readyAt
      fetchCapacity advanceCapacity bucketCapacity readyCapacity
  have middleLive : middle.liveWords = state.liveWords := by
    unfold State.liveWords
    rw [middleSize, middleStack, middleOutput]
  rcases outcome with ⟨pc, live, noModels⟩ | ⟨fired, finished, model, forced⟩
  · obtain ⟨tagged, tagTrace, tagHeap, tagOutput, tagStack, tagFive, tagPC, tagRunning⟩ :=
      Controller.Cost.ForestZeroAnswer.saved_execution program middle conflict 0 cleanupEntry
        (word width count) (word width layout.inverseBase)
        (word width dictionary.coordinates.size) (word width base) rest
        (middleStack.trans savedCount) pc live conflictCapacity conflictAt
    have tagFrame : Controller.Cost.ForestZeroBackendFrame.PrefixFrame keep middle.heap tagged.heap := by
      simpa only [tagHeap] using Controller.Cost.ForestZeroBackendFrame.refl middle.heap
        (by rw [middleSize]; exact prefixBound)
    let savedRest := word width layout.inverseBase :: word width dictionary.coordinates.size ::
      word width base :: word width 0 :: rest
    obtain ⟨final, cleanup, finalSize, finalStack, finalOutput, finalPC, finalRunning, lastFrame⟩ :=
      Controller.Cost.ForestZeroReclaim.stacked_execution program cleanupEntry returnPc keep count
        tagged savedRest cleanupSetup cleanupLoop tagPC tagRunning cleanupCapacity countFits
        (by simpa only [savedRest] using tagStack)
        (by rw [tagHeap, middleSize]; exact allocated)
    have taggedLive : tagged.liveWords = state.liveWords + 2 := by
      unfold State.liveWords
      rw [tagHeap, middleSize, tagStack, tagOutput, middleOutput, savedCount]
      simp only [List.length_cons]
      omega
    refine ⟨false, queue, final, firstTicks + 13 + (4 * count + 4),
      max state.liveWords (max (middle.liveWords + 2) tagged.liveWords),
      (by simpa only [Nat.add_assoc] using first.append (tagTrace.append cleanup)),
      (by simp only [Bool.false_eq_true, ite_false]; omega), ?_, finalSize, finalStack,
      ?_, finalPC, finalRunning,
      Controller.Cost.ForestZeroBackendFrame.trans firstFrame
        (Controller.Cost.ForestZeroBackendFrame.trans tagFrame lastFrame), ?_, ?_⟩
    · rw [middleLive, taggedLive]
      omega
    · simpa only [Bool.false_eq_true, ite_false, savedRest, tagOutput, middleOutput] using finalOutput
    · constructor
      · intro impossible
        cases impossible
      · intro possible
        exact False.elim (noModels possible)
    · intro impossible
      cases impossible
  · obtain ⟨tagged, tagTrace, tagHeap, tagOutput, tagStack, tagFive, tagPC, tagRunning⟩ :=
      Controller.Cost.ForestZeroAnswer.saved_execution program middle fifoDone 1 projectionEntry
        (word width count) (word width layout.inverseBase)
        (word width dictionary.coordinates.size) (word width base) rest
        (middleStack.trans savedCount) finished.position finished.running successCapacity successAt
    have tagFrame : Controller.Cost.ForestZeroBackendFrame.PrefixFrame keep middle.heap tagged.heap := by
      simpa only [tagHeap] using Controller.Cost.ForestZeroBackendFrame.refl middle.heap
        (by rw [middleSize]; exact prefixBound)
    have taggedFrame := Controller.Cost.ForestZeroBackendFrame.trans firstFrame tagFrame
    let taggedLayout := retainedDictionaryLayout state.heap tagged.heap keep layout taggedFrame
      tableBefore inverseBefore
    have taggedDictionary : Represented tagged.heap taggedLayout dictionary :=
      dictionary_prefix_transport state.heap tagged.heap keep layout dictionary represented
        taggedFrame tableBefore inverseBefore
    have taggedFifo : Controller.Horn.WorklistMark.Stored queue base tagged.heap := by
      simpa only [tagHeap] using finished.fifo
    obtain ⟨channelsStored, nodesStored⟩ := projection_headers_transport state.heap tagged.heap
      keep parameters.channels nodes taggedFrame headersBefore channelsCell nodesCell
    obtain ⟨final, lastTicks, lastPeak, suffix, suffixTime, suffixSpace, finalSize, finalStack,
        finalOutput, finalPC, finalRunning, suffixFrame⟩ :=
      terminal_execution parameters program tagged projectionEntry saveEntry pushEntry nativeEntry base done nodes
        dictionary taggedLayout taggedDictionary ambientEq adjacent (by rw [ambientEq]; omega) queue taggedFifo
        localFit tagPC tagRunning projectionEq saveAt restoreRoom restoreAt saveEq channelsStored nodesStored
        (by have := taggedFrame.2.1; omega) offRoom (by omega) constantsAt preparationAt channelsFit
        (by rw [tagHeap, middleSize]; omega) projectionRoom projectionAt
        (by simpa only [tagHeap, middleSize] using nativeRoom)
        (by simpa only [tagHeap, middleSize] using nativeHeap)
        (by simpa only [tagHeap, middleSize] using nativeAt)
        (by simpa only [tagHeap, middleSize] using finishRoom)
        (by simpa only [tagHeap, middleSize] using emitAt)
        (by simpa only [tagHeap, middleSize] using releaseAt)
        keep count (word width 1 :: rest) returnPc nativeSetup nativeLoop nativeCleanupRoom countFits
        tagStack
        (by rw [tagHeap, middleSize]; exact allocated)
    have taggedLive : tagged.liveWords = state.liveWords + 2 := by
      unfold State.liveWords
      rw [tagHeap, middleSize, tagStack, tagOutput, middleOutput, savedCount]
      simp only [List.length_cons]
      omega
    refine ⟨true, queue, final, firstTicks + 13 + lastTicks,
      max state.liveWords (max (middle.liveWords + 2) lastPeak),
      (by simpa only [Nat.add_assoc] using first.append (tagTrace.append suffix)),
      (by simp only [ite_true]; omega), ?_, finalSize, finalStack,
      ?_, finalPC, finalRunning,
      Controller.Cost.ForestZeroBackendFrame.trans taggedFrame suffixFrame,
      ⟨fun _ => ⟨Controller.Horn.WorklistOutcome.offAssignment queue, model⟩, fun _ => rfl⟩,
      fun _ => ⟨model, Controller.Cost.ForestZeroAnswerReclaim.terminal_greatest formula dual
        queue model forced⟩⟩
    · rw [taggedLive] at suffixSpace
      rw [middleLive]
      omega
    · simpa only [ite_true, tagOutput, middleOutput] using finalOutput

theorem native_saved_reset_execution {ambient : Nat}
    (parameters : Parameters)
    (dictionary : Dictionary ambient) (keep : Nat)
    (formula : Controller.CNF.Formula (Fin dictionary.coordinates.size)) (dual : Controller.Horn.DualHorn formula)
    (recordHeader recordStart recordEnd base entry scan seedDone conflict : Nat)
    (state : State width 8) (program : Program width 8)
    (physical : Controller.Horn.IndexScan.PhysicalIndex (formula.clauses.toList) recordStart recordEnd base
      (Controller.Horn.IndexScan.occurrences (formula.clauses.toList) recordStart).length state.heap)
    (header : Controller.Horn.SourceScan.CursorStored recordEnd recordHeader state.heap)
    (fifo : Controller.Horn.WorklistMark.Stored ([] : List (Fin dictionary.coordinates.size)) base state.heap)
    (separated : base + 5 * dictionary.coordinates.size + 4 ≤ recordStart)
    (setupAt : ∀ phase : Fin 10, program[entry + phase.val]? =
      (Controller.Cost.ForestZeroSeedSetup.code (n := dictionary.coordinates.size) width base recordHeader recordStart scan)[phase.val]?)
    (scanAt : Controller.Horn.WorklistSeed.At (n := dictionary.coordinates.size) program base scan seedDone conflict)
    (position : state.pc = word width entry) (running : state.halted = false)
    (zero : state.reg 2 = word width 0) (one : state.reg 5 = word width 1)
    (room : state.heap.size < 2 ^ width) (setupCapacity : entry + 10 < 2 ^ width)
    (scanCapacity : scan + 47 < 2 ^ width)
    (prefixBound : keep ≤ state.heap.size) (prefixBelow : keep ≤ base)
    (fetch : Nat)
    (headAt : ∀ phase : Fin 4, program[seedDone + phase.val]? =
      (Controller.Horn.WorklistAccept.headSetupCode (n := dictionary.coordinates.size) width base fetch)[phase.val]?)
    (headCapacity : seedDone + 4 < 2 ^ width)
    (fifoDone bucket advance ready skip : Nat)
    (fetchAt : Controller.Horn.WorklistFIFO.FetchAt (n := dictionary.coordinates.size) program base fetch fifoDone bucket)
    (advanceAt : Controller.Horn.WorklistFIFO.AdvanceAt (n := dictionary.coordinates.size) program base advance fetch)
    (loopAt : Controller.Horn.WorklistBucketLoop.At program bucket advance ready)
    (readyAt : Controller.Horn.WorklistBucketReady.At (n := dictionary.coordinates.size) program base ready skip conflict bucket)
    (fetchCapacity : fetch + 14 < 2 ^ width) (advanceCapacity : advance + 5 < 2 ^ width)
    (bucketCapacity : bucket + 12 < 2 ^ width) (readyCapacity : ready + 26 < 2 ^ width)
    (projectionEntry cleanupEntry returnPc : Nat)
    (successAt : Controller.Cost.ForestZeroAnswer.SavedAt program fifoDone 1 projectionEntry)
    (conflictAt : Controller.Cost.ForestZeroAnswer.SavedAt program conflict 0 cleanupEntry)
    (successCapacity : fifoDone + 13 < 2 ^ width)
    (conflictCapacity : conflict + 13 < 2 ^ width)
    (layout : ForestZeroDictionary.Layout ambient state.heap.size)
    (represented : Represented state.heap layout dictionary)
    (nodes count : Nat)
    (ambientEq : ambient = parameters.channels + nodes)
    (adjacent : layout.inverseBase = layout.tableBase + ambient)
    (tableBefore : layout.tableBase + ambient ≤ keep)
    (inverseBefore : layout.inverseBase + ambient ≤ keep)
    (headersBefore : 1 < keep)
    (channelsCell : state.heap[0]? = some (word width parameters.channels))
    (nodesCell : state.heap[1]? = some (word width nodes))
    (localFit : dictionary.coordinates.size + 1 < 2 ^ width)
    (channelsFit : parameters.channels + 1 < 2 ^ width) (offRoom : base + 1 < 2 ^ width)
    (projectionCapacity : projectionEntry + 35 < 2 ^ width)
    (constantsAt : ∀ phase : Fin 2, program[projectionEntry + phase.val]? =
      (projectionConstantsCode width)[phase.val]?)
    (preparationAt : ∀ phase : Fin 19, program[projectionEntry + 2 + phase.val]? =
      (channelPrepareCode width)[phase.val]?)
    (saveEntry pushEntry nativeEntry done : Nat)
    (saveEq : saveEntry = projectionEntry + 21)
    (projectionEq : pushEntry = saveEntry + 8)
    (saveAt : SharedRootRead.BlockAt program saveEntry (SharedRegisterStack.saveCode (width := width) (List.finRange 8)))
    (restoreRoom : done + 8 < 2 ^ width)
    (restoreAt : SharedRootRead.BlockAt program done (SharedRegisterStack.restoreCode (width := width) (List.finRange 8).reverse))
    (projectionRoom : pushEntry + 14 < 2 ^ width)
    (projectionAt : ForestZeroChannelPush.CodeAt program pushEntry nativeEntry)
    (nativeRoom : nativeEntry + (NativeRetainedExecution.code parameters width state.heap.size nativeEntry).length < 2 ^ width)
    (nativeHeap : state.heap.size + parameters.channels + (compile parameters).toState.count < 2 ^ width)
    (nativeAt : ForestZeroCallerWiden.WidenedBlockAt program nativeEntry
      (NativeRetainedExecution.code parameters width state.heap.size nativeEntry))
    (finishRoom : emitEntry parameters width state.heap.size nativeEntry + 3 * (compile parameters).toState.count + 7 < 2 ^ width)
    (emitAt : ForestZeroCallerWiden.WidenedBlockAt program (emitEntry parameters width state.heap.size nativeEntry)
      (OutputProgram.emitCode width (NativeRealizedCore.addresses (state.heap.size + parameters.channels) (compile parameters).toState.count)))
    (releaseAt : Controller.Cost.RawTransferLoops.CodeAt program
      (emitEntry parameters width state.heap.size nativeEntry + 3 * (compile parameters).toState.count)
      (SharedEvaluationReclaim.code width (emitEntry parameters width state.heap.size nativeEntry + 3 * (compile parameters).toState.count)
        done (parameters.channels + (compile parameters).toState.count)))
    (nativeSetup : ∀ phase : Fin 3, program[done + 8 + phase.val]? =
      (Controller.Cost.ForestZeroReclaim.setupCode width)[phase.val]?)
    (nativeLoop : Controller.Cost.ForestZeroReclaim.At program (done + 11) returnPc)
    (nativeCleanupRoom : done + 15 < 2 ^ width)
    (cleanupSetup : ∀ phase : Fin 3, program[cleanupEntry + phase.val]? =
      (Controller.Cost.ForestZeroReclaim.setupCode width)[phase.val]?)
    (cleanupLoop : Controller.Cost.ForestZeroReclaim.At program (cleanupEntry + 3) returnPc)
    (cleanupCapacity : cleanupEntry + 7 < 2 ^ width) (countFits : count < 2 ^ width)
    (rest : List (Word width))
    (savedCount : state.stack = word width count :: word width layout.inverseBase ::
      word width dictionary.coordinates.size :: word width base :: rest)
    (allocated : state.heap.size = keep + count)
    (tablePositive : 0 < layout.tableBase)
    (resetCapacity : returnPc + 27 < 2 ^ width)
    (resetPrepareAt : ForestZeroCallerWiden.WidenedBlockAt program returnPc (resetPrepareCode width).toList)
    (resetLoopAt : ForestZeroCallerWiden.WidenedBlockAt program (returnPc + 15)
      (Controller.Cost.ForestZeroReset.code width (returnPc + 15)))
    (decisionCapacity : returnPc + 28 < 2 ^ width)
    (decisionAt : program[returnPc + 27]? = some (.pop 4)) :
    ∃ answer : Bool, ∃ queue final ticks peak,
      Execution program state final ticks peak ∧
      ticks ≤ 36 * formula.clauses.toList.length +
        32 * (Controller.Horn.IndexScan.occurrences formula.clauses.toList recordStart).length +
        38 * dictionary.coordinates.size + 4 * count + (if answer then 55 * (selectedSize parameters).total + 100 else 58) ∧
      peak ≤ state.liveWords + 3 * (selectedSize parameters).total + 10 ∧ final.heap.size = keep ∧
      final.stack = rest ∧
      final.output = (if answer then (NativeRootLoad.words width
        (SourceLift.finite parameters (Physical.realizeBridge parameters.bridge parameters.positiveBuses
          (setOfAssignment (SharedZeroNative.channels parameters dictionary queue
            (by rw [ambientEq]; omega)))))).reverse ++
          word width 1 :: state.output else word width 0 :: state.output) ∧
      final.pc = word width (returnPc + 28) ∧ final.halted = false ∧
      Controller.Cost.ForestZeroBackendFrame.PrefixFrame layout.tableBase state.heap final.heap ∧
      (∀ coordinate : Fin ambient, final.heap[layout.tableBase + coordinate.val]? = some (word width 0)) ∧
      final.reg 4 = word width (if answer then 1 else 0) ∧
      final.reg 0 = word width 0 ∧ final.reg 1 = word width layout.tableBase ∧
      final.reg 2 = word width layout.inverseBase ∧
      (answer = true ↔ ∃ assignment, Controller.CNF.Satisfies assignment formula) ∧
      (answer = true → Controller.CNF.Satisfies (Controller.Horn.WorklistOutcome.offAssignment queue) formula ∧
        Controller.Horn.WorklistOutcome.offAssignment queue = Controller.Horn.greatestCandidate formula) := by
  obtain ⟨answer, queue, reclaimed, firstTicks, firstPeak, first, timeBound, spaceBound,
      reclaimedSize, reclaimedStack, reclaimedOutput, reclaimedPC, reclaimedRunning,
      reclaimedFrame, meaning, greatest⟩ :=
    initialized_native_saved_execution parameters dictionary keep formula dual
      recordHeader recordStart recordEnd base entry scan seedDone conflict state program
      physical header fifo separated setupAt scanAt position running zero one room
      setupCapacity scanCapacity prefixBound prefixBelow fetch headAt headCapacity fifoDone
      bucket advance ready skip fetchAt advanceAt loopAt readyAt fetchCapacity advanceCapacity
      bucketCapacity readyCapacity projectionEntry cleanupEntry returnPc successAt conflictAt
      successCapacity conflictCapacity layout represented nodes count ambientEq adjacent
      tableBefore inverseBefore headersBefore channelsCell nodesCell localFit channelsFit
      offRoom projectionCapacity constantsAt preparationAt saveEntry pushEntry nativeEntry done
      saveEq projectionEq saveAt restoreRoom restoreAt projectionRoom projectionAt nativeRoom nativeHeap nativeAt
      finishRoom emitAt releaseAt nativeSetup nativeLoop nativeCleanupRoom cleanupSetup cleanupLoop
      cleanupCapacity countFits rest savedCount allocated
  let reclaimedLayout := retainedDictionaryLayout state.heap reclaimed.heap keep layout
    reclaimedFrame tableBefore inverseBefore
  have reclaimedDictionary : Represented reclaimed.heap reclaimedLayout dictionary :=
    dictionary_prefix_transport state.heap reclaimed.heap keep layout dictionary represented
      reclaimedFrame tableBefore inverseBefore
  obtain ⟨channelHeader, nodeHeader⟩ := projection_headers_transport state.heap reclaimed.heap
    keep parameters.channels nodes reclaimedFrame headersBefore channelsCell nodesCell
  obtain ⟨resetFinal, reset, finalHeap, finalStack, finalOutput, finalPC, finalRunning,
      resetFrame, zeroSlots, finalZero, finalTable, finalInverse⟩ :=
    retained_dictionary_reset_registers_execution program reclaimed returnPc parameters.channels nodes dictionary
      reclaimedLayout reclaimedDictionary ambientEq adjacent tablePositive (word width base)
      (word width (if answer then 1 else 0) :: rest) reclaimedStack reclaimedPC reclaimedRunning channelHeader nodeHeader
      (by rw [reclaimedSize]; exact headersBefore)
      (by rw [reclaimedSize]; omega) resetCapacity resetPrepareAt resetLoopAt
  have sourceBound : layout.tableBase ≤ keep := by omega
  have sourceFrame : Controller.Cost.ForestZeroBackendFrame.PrefixFrame layout.tableBase
      state.heap reclaimed.heap :=
    ⟨by omega, by rw [reclaimedSize]; omega,
      fun address below => reclaimedFrame.2.2 address (lt_of_lt_of_le below sourceBound)⟩
  have reclaimedLive : reclaimed.liveWords ≤ firstPeak := first.final_storage_le
  obtain ⟨final, recover, decision, recoverHeap, recoverStack, recoverOutput, recoverPC,
      recoverRunning, recoverRegisters⟩ :=
    decision_recover_execution program resetFinal (returnPc + 27)
      (word width (if answer then 1 else 0)) rest finalStack finalPC finalRunning
      (by omega) decisionAt
  have resetLive : resetFinal.liveWords ≤ reclaimed.liveWords := reset.final_storage_le
  have recoverFrame : Controller.Cost.ForestZeroBackendFrame.PrefixFrame layout.tableBase
      resetFinal.heap final.heap := by
    simpa only [recoverHeap] using Controller.Cost.ForestZeroBackendFrame.refl resetFinal.heap
      (by rw [finalHeap, Controller.Cost.ForestZeroReset.resetHeap_size, reclaimedSize]; omega)
  refine ⟨answer, queue, final, firstTicks + (12 * dictionary.coordinates.size + 16) + 1,
    max (max firstPeak reclaimed.liveWords) resetFinal.liveWords,
    (first.append reset).append recover, ?_, ?_, ?_, recoverStack,
    recoverOutput.trans (finalOutput.trans reclaimedOutput), ?_, recoverRunning,
    Controller.Cost.ForestZeroBackendFrame.trans sourceFrame
      (Controller.Cost.ForestZeroBackendFrame.trans resetFrame recoverFrame),
    ?_, decision, ?_, ?_, ?_, meaning, greatest⟩
  · cases answer <;> simp only [Bool.false_eq_true, ite_false, ite_true] at timeBound ⊢ <;> omega
  · omega
  · rw [recoverHeap, finalHeap, Controller.Cost.ForestZeroReset.resetHeap_size, reclaimedSize]
  · simpa only [Nat.add_assoc, Nat.reduceAdd] using recoverPC
  · have tableScalar : reclaimedLayout.tableBase = layout.tableBase := rfl
    simpa only [recoverHeap, tableScalar] using zeroSlots
  · exact (recoverRegisters 0 (by decide)).trans finalZero
  · exact (recoverRegisters 1 (by decide)).trans finalTable
  · exact (recoverRegisters 2 (by decide)).trans finalInverse


theorem scratch_indexed_native_reuse_execution {ambient : Nat}
    (parameters : Parameters)
    (dictionary : Dictionary ambient) (keep : Nat)
    (formula : Controller.CNF.Formula (Fin dictionary.coordinates.size)) (dual : Controller.Horn.DualHorn formula)
    (recordHeader recordStart recordEnd base entry scan seedDone conflict : Nat)
    (state : State width 8) (program : Program width 8)
    (backend : Controller.Horn.SourceDirectory.Layout formula.clauses.toList)
    (sourceStored : Stored formula.clauses.toList backend.directory backend.source state.heap)
    (directoryCursor : CursorStored backend.directory backend.directoryHeader state.heap)
    (directoryEnd : CursorStored (backend.directory + 2 * formula.clauses.toList.length) backend.endHeader state.heap)
    (baseEq : backend.base = state.heap.size) (recordHeaderEq : backend.recordHeader = keep)
    (headerEq : recordHeader = backend.recordHeader) (backendBaseEq : base = backend.base)
    (recordStartEq : recordStart = state.heap.size + 5 * dictionary.coordinates.size + 4)
    (recordEndEq : recordEnd = Controller.Horn.NormalizeLoop.recordOffset formula.clauses.toList
      recordStart formula.clauses.toList.length)
    (localCount : state.reg 2 = word width dictionary.coordinates.size)
    (sourcePointer : state.reg 1 = word width state.heap.size)
    (countAt : ∀ phase : Fin 11, program[entry + phase.val]? = (scratchCountCode width)[phase.val]?)
    (allocateAt : Controller.Horn.TrackedAllocate.CodeAt program (entry + 11))
    (headersAt : ∀ phase : Fin 15, program[entry + 16 + phase.val]? = (scratchHeaderCode width)[phase.val]?)
    (endpointAt : ∀ phase : Fin 5, program[entry + 31 + phase.val]? = (scratchEndpointCode (width := width))[phase.val]?)
    (saveAt : ∀ phase : Fin 6, program[entry + 36 + phase.val]? = (saveProjectionCode (width := width))[phase.val]?)
    (normalizerAt : Controller.Horn.NormalizeLoop.CodeAt program (entry + 42) formula.clauses.toList backend)
    (headersAbove : ∀ address ∈ [backend.recordHeader, backend.inputHeader, backend.firstHeader,
      backend.directoryHeader, backend.endHeader], backend.recordHeader ≤ address)
    (indexSaveAt : Controller.Cost.ForestZeroHeaderBridge.SaveAt program (entry + 203) recordHeader)
    (indexAt : Controller.Horn.IndexScan.At (n := dictionary.coordinates.size) program (entry + 210) base recordStart)
    (indexRestoreAt : Controller.Cost.ForestZeroHeaderBridge.RestoreAt program (entry + 242))
    (captureAt : ∀ phase : Fin 6, program[entry + 245 + phase.val]? = (Controller.Cost.ForestZeroReclaim.captureCode width)[phase.val]?)
    (fullCapacity : entry + 261 < 2 ^ width)
    (setupAt : ∀ phase : Fin 10, program[entry + 251 + phase.val]? =
      (Controller.Cost.ForestZeroSeedSetup.code (n := dictionary.coordinates.size) width base recordHeader recordStart scan)[phase.val]?)
    (scanAt : Controller.Horn.WorklistSeed.At (n := dictionary.coordinates.size) program base scan seedDone conflict)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : state.heap.size + 5 * dictionary.coordinates.size + 4 +
      3 * formula.clauses.toList.length + (formula.clauses.toList.map List.length).sum +
      2 * (Controller.Horn.IndexScan.occurrences formula.clauses.toList recordStart).length < 2 ^ width)
    (scanCapacity : scan + 47 < 2 ^ width)
    (prefixBound : keep ≤ state.heap.size) (prefixBelow : keep ≤ base)
    (fetch : Nat)
    (headAt : ∀ phase : Fin 4, program[seedDone + phase.val]? =
      (Controller.Horn.WorklistAccept.headSetupCode (n := dictionary.coordinates.size) width base fetch)[phase.val]?)
    (headCapacity : seedDone + 4 < 2 ^ width)
    (fifoDone bucket advance ready skip : Nat)
    (fetchAt : Controller.Horn.WorklistFIFO.FetchAt (n := dictionary.coordinates.size) program base fetch fifoDone bucket)
    (advanceAt : Controller.Horn.WorklistFIFO.AdvanceAt (n := dictionary.coordinates.size) program base advance fetch)
    (loopAt : Controller.Horn.WorklistBucketLoop.At program bucket advance ready)
    (readyAt : Controller.Horn.WorklistBucketReady.At (n := dictionary.coordinates.size) program base ready skip conflict bucket)
    (fetchCapacity : fetch + 14 < 2 ^ width) (advanceCapacity : advance + 5 < 2 ^ width)
    (bucketCapacity : bucket + 12 < 2 ^ width) (readyCapacity : ready + 26 < 2 ^ width)
    (projectionEntry cleanupEntry returnPc : Nat)
    (successAt : Controller.Cost.ForestZeroAnswer.SavedAt program fifoDone 1 projectionEntry)
    (conflictAt : Controller.Cost.ForestZeroAnswer.SavedAt program conflict 0 cleanupEntry)
    (successCapacity : fifoDone + 13 < 2 ^ width)
    (conflictCapacity : conflict + 13 < 2 ^ width)
    (layout : ForestZeroDictionary.Layout ambient state.heap.size)
    (represented : Represented state.heap layout dictionary)
    (nodes : Nat)
    (ambientEq : ambient = parameters.channels + nodes)
    (adjacent : layout.inverseBase = layout.tableBase + ambient)
    (tableBefore : layout.tableBase + ambient ≤ keep)
    (inverseBefore : layout.inverseBase + ambient ≤ keep)
    (headersBefore : 1 < keep)
    (channelsCell : state.heap[0]? = some (word width parameters.channels))
    (nodesCell : state.heap[1]? = some (word width nodes))
    (localFit : dictionary.coordinates.size + 1 < 2 ^ width)
    (channelsFit : parameters.channels + 1 < 2 ^ width) (offRoom : base + 1 < 2 ^ width)
    (projectionCapacity : projectionEntry + 35 < 2 ^ width)
    (constantsAt : ∀ phase : Fin 2, program[projectionEntry + phase.val]? =
      (projectionConstantsCode width)[phase.val]?)
    (preparationAt : ∀ phase : Fin 19, program[projectionEntry + 2 + phase.val]? =
      (channelPrepareCode width)[phase.val]?)
    (saveEntry pushEntry nativeEntry done : Nat)
    (saveEq : saveEntry = projectionEntry + 21)
    (projectionEq : pushEntry = saveEntry + 8)
    (saveAt_1 : SharedRootRead.BlockAt program saveEntry (SharedRegisterStack.saveCode (width := width) (List.finRange 8)))
    (restoreRoom : done + 8 < 2 ^ width)
    (restoreAt : SharedRootRead.BlockAt program done (SharedRegisterStack.restoreCode (width := width) (List.finRange 8).reverse))
    (projectionRoom : pushEntry + 14 < 2 ^ width)
    (projectionAt : ForestZeroChannelPush.CodeAt program pushEntry nativeEntry)
    (nativeRoom : nativeEntry + (NativeRetainedExecution.code parameters width (recordEnd + 2 * (Controller.Horn.IndexScan.occurrences formula.clauses.toList recordStart).length) nativeEntry).length < 2 ^ width)
    (nativeHeap : (recordEnd + 2 * (Controller.Horn.IndexScan.occurrences formula.clauses.toList recordStart).length) + parameters.channels + (compile parameters).toState.count < 2 ^ width)
    (nativeAt : ForestZeroCallerWiden.WidenedBlockAt program nativeEntry
      (NativeRetainedExecution.code parameters width (recordEnd + 2 * (Controller.Horn.IndexScan.occurrences formula.clauses.toList recordStart).length) nativeEntry))
    (finishRoom : emitEntry parameters width (recordEnd + 2 * (Controller.Horn.IndexScan.occurrences formula.clauses.toList recordStart).length) nativeEntry + 3 * (compile parameters).toState.count + 7 < 2 ^ width)
    (emitAt : ForestZeroCallerWiden.WidenedBlockAt program (emitEntry parameters width (recordEnd + 2 * (Controller.Horn.IndexScan.occurrences formula.clauses.toList recordStart).length) nativeEntry)
      (OutputProgram.emitCode width (NativeRealizedCore.addresses ((recordEnd + 2 * (Controller.Horn.IndexScan.occurrences formula.clauses.toList recordStart).length) + parameters.channels) (compile parameters).toState.count)))
    (releaseAt : Controller.Cost.RawTransferLoops.CodeAt program
      (emitEntry parameters width (recordEnd + 2 * (Controller.Horn.IndexScan.occurrences formula.clauses.toList recordStart).length) nativeEntry + 3 * (compile parameters).toState.count)
      (SharedEvaluationReclaim.code width (emitEntry parameters width (recordEnd + 2 * (Controller.Horn.IndexScan.occurrences formula.clauses.toList recordStart).length) nativeEntry + 3 * (compile parameters).toState.count)
        done (parameters.channels + (compile parameters).toState.count)))
    (nativeSetup : ∀ phase : Fin 3, program[done + 8 + phase.val]? =
      (Controller.Cost.ForestZeroReclaim.setupCode width)[phase.val]?)
    (nativeLoop : Controller.Cost.ForestZeroReclaim.At program (done + 11) returnPc)
    (nativeCleanupRoom : done + 15 < 2 ^ width)
    (cleanupSetup : ∀ phase : Fin 3, program[cleanupEntry + phase.val]? =
      (Controller.Cost.ForestZeroReclaim.setupCode width)[phase.val]?)
    (cleanupLoop : Controller.Cost.ForestZeroReclaim.At program (cleanupEntry + 3) returnPc)
    (cleanupCapacity : cleanupEntry + 7 < 2 ^ width)
    (rest : List (Word width))
    (saved : state.stack = word width layout.inverseBase :: word width keep :: rest)
    (tablePositive : 0 < layout.tableBase)
    (resetCapacity : returnPc + 27 < 2 ^ width)
    (resetPrepareAt : ForestZeroCallerWiden.WidenedBlockAt program returnPc (resetPrepareCode width).toList)
    (resetLoopAt : ForestZeroCallerWiden.WidenedBlockAt program (returnPc + 15)
      (Controller.Cost.ForestZeroReset.code width (returnPc + 15)))
    (decisionCapacity : returnPc + 28 < 2 ^ width)
    (decisionAt : program[returnPc + 27]? = some (.pop 4)) :
    ∃ answer : Bool, ∃ queue final ticks peak,
      Execution program state final ticks peak ∧
      ticks ≤ 63 * dictionary.coordinates.size +
        61 * (formula.clauses.toList.map List.length).sum + 125 * formula.clauses.toList.length +
        48 * (Controller.Horn.IndexScan.occurrences formula.clauses.toList recordStart).length +
        4 * (recordEnd + 2 * (Controller.Horn.IndexScan.occurrences formula.clauses.toList recordStart).length - keep) +
        (if answer then 55 * (selectedSize parameters).total + 186 else 144) ∧
      peak ≤ state.liveWords + 5 * dictionary.coordinates.size +
        3 * formula.clauses.toList.length + (formula.clauses.toList.map List.length).sum +
        2 * (Controller.Horn.IndexScan.occurrences formula.clauses.toList recordStart).length + 3 * (selectedSize parameters).total + 16 ∧
      final.heap.size = keep ∧ final.stack = rest ∧
      final.output = (if answer then (NativeRootLoad.words width
        (SourceLift.finite parameters (Physical.realizeBridge parameters.bridge parameters.positiveBuses
          (setOfAssignment (SharedZeroNative.channels parameters dictionary queue
            (by rw [ambientEq]; omega)))))).reverse ++
          word width 1 :: state.output else word width 0 :: state.output) ∧
      final.pc = word width (returnPc + 28) ∧ final.halted = false ∧
      Controller.Cost.ForestZeroBackendFrame.PrefixFrame layout.tableBase state.heap final.heap ∧
      (∀ coordinate : Fin ambient, final.heap[layout.tableBase + coordinate.val]? = some (word width 0)) ∧
      final.reg 4 = word width (if answer then 1 else 0) ∧
      final.reg 0 = word width 0 ∧ final.reg 1 = word width layout.tableBase ∧
      final.reg 2 = word width layout.inverseBase ∧
      (answer = true ↔ ∃ assignment, Controller.CNF.Satisfies assignment formula) ∧
      (answer = true → Controller.CNF.Satisfies (Controller.Horn.WorklistOutcome.offAssignment queue) formula ∧
        Controller.Horn.WorklistOutcome.offAssignment queue = Controller.Horn.greatestCandidate formula) := by
  let incidences := (Controller.Horn.IndexScan.occurrences formula.clauses.toList recordStart).length
  let count := recordEnd + 2 * incidences - keep
  have dualRows : ∀ index : Fin formula.clauses.toList.length, Controller.Horn.DualHornClause formula.clauses.toList[index.val] := by
    intro index
    apply dual
    have member := List.getElem_mem index.isLt
    simpa only [Array.mem_toList_iff] using member
  obtain ⟨normalized, marks, normalizeTicks, normalizePeak, normalizeTrace, complete,
      normalizedPC, normalizeTime, normalizeSpace, normalizedStack, normalizedOutput,
      normalizeFrame⟩ :=
    scratch_normalized_execution program state entry formula.clauses.toList backend sourceStored directoryCursor
      directoryEnd baseEq position running localCount sourcePointer layout.inverseBase rest
      (by simpa only [recordHeaderEq] using saved) (by omega) (by omega)
      countAt allocateAt headersAt endpointAt saveAt normalizerAt dualRows headersAbove
  have completed : Controller.Horn.NormalizeLoop.Invariant formula.clauses.toList backend recordStart formula.clauses.toList.length marks normalized := by
    simpa only [← recordStartEq] using complete
  have normalizedSize : normalized.heap.size = recordEnd := by
    exact completed.records.endpoint.trans recordEndEq.symm
  have endBound : recordEnd ≤ recordStart + 3 * formula.clauses.toList.length + (formula.clauses.toList.map List.length).sum := by
    have sumBound := Controller.Horn.NormalizeLoop.wordSuffix_bound formula.clauses.toList 0
    simp only [Controller.Horn.NormalizeLoop.wordSuffix, Controller.Horn.NormalizeLoop.literalSuffix,
      List.drop_zero] at sumBound
    rw [recordEndEq, Controller.Horn.NormalizeLoop.recordOffset, List.take_length]
    omega
  have keepFrame : Controller.Cost.ForestZeroBackendFrame.PrefixFrame keep state.heap normalized.heap := by
    simpa only [recordHeaderEq] using normalizeFrame
  obtain ⟨physical, cursor, fifo⟩ := Controller.Cost.ForestZeroIndexMarks.normalized_inputs
    formula.clauses.toList backend recordStart marks normalized completed
  have baseBelow : base ≤ normalized.heap.size := by
    have lower := Controller.Horn.NormalizeLoop.recordOffset_above formula.clauses.toList recordStart formula.clauses.toList.length
    rw [← recordEndEq, ← normalizedSize] at lower
    omega
  have headerBelow : recordHeader < base := by
    have headerBound := backend.headersBefore backend.recordHeader (by simp)
    have directoryBound := backend.directoryBefore
    have sourceBound := backend.sourceBefore
    unfold Controller.Horn.SourceDirectory.sourceOffset at sourceBound
    omega
  let savedRest := word width layout.inverseBase :: word width dictionary.coordinates.size ::
    word width base :: rest
  obtain ⟨indexed, indexTrace, indexedPhysical, indexedHeader, indexedFIFO, indexedFrame,
      indexedSize, allocated, indexedStack, indexedOutput, indexedZero, indexedOne,
      indexedPC, indexedRunning⟩ :=
    Controller.Cost.ForestZeroIndexMarks.indexed_capture_inputs keep program formula.clauses.toList
      (entry + 203) recordHeader recordStart recordEnd base normalized indexSaveAt
      (by simpa only [Nat.add_assoc, Nat.reduceAdd] using indexAt)
      (by simpa only [Nat.add_assoc, Nat.reduceAdd] using indexRestoreAt)
      (by simpa only [Nat.add_assoc, Nat.reduceAdd] using captureAt)
      (by simpa only [normalizedSize, backendBaseEq] using physical)
      (by simpa only [normalizedSize, headerEq] using cursor)
      normalizedPC completed.input.running completed.input.zero completed.input.one
      (by omega) baseBelow headerBelow prefixBelow
      (by simpa only [backendBaseEq] using fifo) (by omega)
      (by rw [normalizedSize]; omega) savedRest
      (by simpa only [savedRest, backendBaseEq, baseEq, recordHeaderEq] using normalizedStack)
  have indexKeepFrame : Controller.Cost.ForestZeroBackendFrame.PrefixFrame keep normalized.heap indexed.heap :=
    ⟨by omega, by have := indexedFrame.2.1; omega,
      fun address below => indexedFrame.2.2 address (lt_of_lt_of_le below prefixBelow)⟩
  have prefixFrame := Controller.Cost.ForestZeroBackendFrame.trans keepFrame indexKeepFrame
  let indexedLayout := retainedDictionaryLayout state.heap indexed.heap keep layout prefixFrame
    tableBefore inverseBefore
  have indexedInverse : indexedLayout.inverseBase = layout.inverseBase := rfl
  have indexedTable : indexedLayout.tableBase = layout.tableBase := rfl
  have indexedDictionary : Represented indexed.heap indexedLayout dictionary :=
    dictionary_prefix_transport state.heap indexed.heap keep layout dictionary represented prefixFrame
      tableBefore inverseBefore
  obtain ⟨indexedChannels, indexedNodes⟩ := projection_headers_transport state.heap indexed.heap keep
    parameters.channels nodes prefixFrame headersBefore channelsCell nodesCell
  have actualSize : indexed.heap.size = keep + count := by
    simpa only [count, incidences, normalizedSize] using allocated
  have indexedLive : indexed.liveWords = normalized.liveWords + 2 * incidences := by
    unfold State.liveWords
    rw [indexedSize, indexedStack, indexedOutput, normalizedStack]
    simp only [savedRest, List.length_cons, List.length_nil]
    omega
  obtain ⟨answer, queue, final, terminalTicks, terminalPeak, terminalTrace, terminalTime,
      terminalSpace, finalSize, finalStack, finalOutput, finalPC, finalRunning, terminalFrame,
      zeroSlots, decision, finalZero, finalTable, finalInverse, meaning, greatest⟩ :=
    native_saved_reset_execution parameters dictionary keep formula dual recordHeader recordStart recordEnd
      base (entry + 251) scan seedDone conflict indexed program indexedPhysical indexedHeader indexedFIFO
      (by simpa only [backendBaseEq] using completed.recordsAbove) setupAt scanAt (by simpa only [Nat.add_assoc, Nat.reduceAdd] using indexedPC) indexedRunning
      indexedZero indexedOne (by rw [indexedSize, normalizedSize]; omega) (by omega) scanCapacity
      (by have := prefixFrame.2.1; omega) prefixBelow fetch headAt headCapacity fifoDone bucket advance
      ready skip fetchAt advanceAt loopAt readyAt fetchCapacity advanceCapacity bucketCapacity readyCapacity
      projectionEntry cleanupEntry returnPc successAt conflictAt successCapacity conflictCapacity
      indexedLayout indexedDictionary nodes count ambientEq adjacent tableBefore inverseBefore headersBefore
      indexedChannels indexedNodes localFit channelsFit offRoom projectionCapacity constantsAt preparationAt
      saveEntry pushEntry nativeEntry done saveEq projectionEq saveAt_1 restoreRoom restoreAt projectionRoom projectionAt
      (by simpa only [indexedSize, normalizedSize] using nativeRoom)
      (by simpa only [indexedSize, normalizedSize] using nativeHeap)
      (by simpa only [indexedSize, normalizedSize] using nativeAt)
      (by simpa only [indexedSize, normalizedSize] using finishRoom)
      (by simpa only [indexedSize, normalizedSize] using emitAt)
      (by simpa only [indexedSize, normalizedSize] using releaseAt)
      nativeSetup nativeLoop nativeCleanupRoom cleanupSetup cleanupLoop cleanupCapacity (by unfold count; omega) rest
      (by simpa only [count, incidences, normalizedSize, savedRest, indexedInverse] using indexedStack)
      actualSize tablePositive resetCapacity resetPrepareAt resetLoopAt decisionCapacity decisionAt
  rw [indexedTable] at terminalFrame zeroSlots finalTable
  rw [indexedInverse] at finalInverse
  have indexedTime : 16 * incidences + 18 * formula.clauses.toList.length + 22 =
      16 * (Controller.Horn.IndexScan.occurrences formula.clauses.toList recordStart).length + 18 * formula.clauses.toList.length + 22 := rfl
  have normalizedLive : normalized.liveWords ≤ normalizePeak := normalizeTrace.final_storage_le
  refine ⟨answer, queue, final, normalizeTicks + (16 * incidences + 18 * formula.clauses.toList.length + 22) + terminalTicks,
    max normalizePeak (max (normalized.liveWords + 2 * incidences + 1) terminalPeak),
    (by simpa only [Nat.add_assoc, incidences] using normalizeTrace.append (indexTrace.append terminalTrace)),
    ?_, ?_, finalSize, finalStack, ?_, finalPC, finalRunning, ?_, zeroSlots, decision, finalZero, finalTable, finalInverse, meaning, greatest⟩
  · dsimp only [incidences, count] at normalizeTime terminalTime ⊢
    cases answer <;> simp only [Bool.false_eq_true, ite_false, ite_true] at terminalTime ⊢ <;> omega
  · rw [indexedLive] at terminalSpace
    dsimp only [incidences] at normalizeSpace terminalSpace ⊢
    omega
  · simpa only [indexedOutput, normalizedOutput] using finalOutput
  · have tableBelow : layout.tableBase ≤ keep := by omega
    have sourceFrame : Controller.Cost.ForestZeroBackendFrame.PrefixFrame layout.tableBase state.heap indexed.heap :=
      ⟨by omega, by have := prefixFrame.2.1; omega,
        fun address below => prefixFrame.2.2 address (lt_of_lt_of_le below tableBelow)⟩
    exact Controller.Cost.ForestZeroBackendFrame.trans sourceFrame terminalFrame


theorem source_constructor_native_reuse_execution {ambient : Nat}
    (parameters : Parameters)
    (heap : Array (Word width)) (originalLayout : Layout ambient heap.size)
    (originalDictionary : Dictionary ambient) (originalRepresentation : Represented heap originalLayout originalDictionary)
    (references : List (List (Reference ambient))) (sourceEnd nodes : Nat)
    (sourceReferences : ∀ reference ∈ references.flatten,
      Controller.Cost.ForestZeroEmit.StoredReference heap parameters.channels sourceEnd reference)
    (sourceBeforeTable : sourceEnd ≤ originalLayout.tableBase)
    (sourceBeforeInverse : sourceEnd ≤ originalLayout.inverseBase)
    (sourceBound : sourceEnd ≤ heap.size) (sourcePositive : 0 < sourceEnd)
    (sourceChannel : heap[0]? = some (word width parameters.channels))
    (sourceNodes : heap[1]? = some (word width nodes)) (ambientEq : ambient = parameters.channels + nodes)
    (adjacent : originalLayout.inverseBase = originalLayout.tableBase + ambient)
    (tablePositive : 0 < originalLayout.tableBase) (sourceHeaderRoom : 1 < sourceEnd)
    (sourceDual : Controller.Horn.DualHorn
      (ofClauses (ForestZeroAssembly.originalRows (reservedReferences references))))
    (program : Program width 8) (sourceEntry constructorEntry entry : Nat)
    (entryEq : constructorEntry = sourceEntry + 15)
    (originalCount : originalDictionary.coordinates.size = 0)
    (sourceEndpoint : heap.size = originalLayout.inverseBase + ambient)
    (initialScratch : Nat)
    (entryCapacity : sourceEntry + 15 < 2 ^ width)
    (entryAt : ∀ phase : Fin 3, program[sourceEntry + phase.val]? = (reuseEntryCode width)[phase.val]?)
    (keepAt : ForestZeroCallerWiden.WidenedBlockAt program (sourceEntry + 3) (keepCode width))
    (cursorAt : program[sourceEntry + 14]? = some (.constant 0
      (word width (heap.size + 5 + 2 * (references.length + 1)))))
    (rest output : List (Word width)) (highRegisters : Fin 8 → Word width)
    (constructorRoom : heap.size + 5 + 2 * (references.length + 1) +
      2 * references.flatten.length + 2 * ambient < 2 ^ width)
    (ambientFits : ambient + 1 < 2 ^ width)
    (constructorCapacity : constructorEntry +
      (constructorCode width constructorEntry heap.size heap.size (heap.size + 4) entry references).length < 2 ^ width)
    (constructorAt : ForestZeroCallerWiden.WidenedBlockAt program constructorEntry
      (constructorCode width constructorEntry heap.size heap.size (heap.size + 4) entry references)) :
    let within : parameters.channels ≤ ambient := by omega
    let dictionary := constructorDictionary heap originalLayout originalDictionary references
    let formula := constructorFormula heap originalLayout originalDictionary originalRepresentation.coherent references parameters.channels within
    let state := constructorState heap originalLayout originalDictionary references parameters.channels entry
      (word width heap.size :: rest) output highRegisters
    let backend := constructorFormulaBackend heap originalLayout originalDictionary originalRepresentation.coherent references parameters.channels within
    let layout := constructorDictionaryLayout heap originalLayout originalDictionary references parameters.channels
    let keep := heap.size
    let recordHeader := heap.size
    let base := state.heap.size
    let recordStart := state.heap.size + 5 * dictionary.coordinates.size + 4
    let recordEnd := Controller.Horn.NormalizeLoop.recordOffset formula.clauses.toList recordStart formula.clauses.toList.length
    ∀ (scan seedDone conflict : Nat)
      (countAt : ∀ phase : Fin 11, program[entry + phase.val]? = (scratchCountCode width)[phase.val]?)
      (allocateAt : Controller.Horn.TrackedAllocate.CodeAt program (entry + 11))
      (headersAt : ∀ phase : Fin 15, program[entry + 16 + phase.val]? = (scratchHeaderCode width)[phase.val]?)
      (endpointAt : ∀ phase : Fin 5, program[entry + 31 + phase.val]? = (scratchEndpointCode (width := width))[phase.val]?)
      (saveAt : ∀ phase : Fin 6, program[entry + 36 + phase.val]? = (saveProjectionCode (width := width))[phase.val]?)
      (normalizerAt : Controller.Horn.NormalizeLoop.CodeAt program (entry + 42) formula.clauses.toList backend)
      (indexSaveAt : Controller.Cost.ForestZeroHeaderBridge.SaveAt program (entry + 203) recordHeader)
      (indexAt : Controller.Horn.IndexScan.At (n := dictionary.coordinates.size) program (entry + 210) base recordStart)
      (indexRestoreAt : Controller.Cost.ForestZeroHeaderBridge.RestoreAt program (entry + 242))
      (captureAt : ∀ phase : Fin 6, program[entry + 245 + phase.val]? = (Controller.Cost.ForestZeroReclaim.captureCode width)[phase.val]?)
      (fullCapacity : entry + 261 < 2 ^ width)
      (setupAt : ∀ phase : Fin 10, program[entry + 251 + phase.val]? =
      (Controller.Cost.ForestZeroSeedSetup.code (n := dictionary.coordinates.size) width base recordHeader recordStart scan)[phase.val]?)
      (scanAt : Controller.Horn.WorklistSeed.At (n := dictionary.coordinates.size) program base scan seedDone conflict)
      (room : state.heap.size + 5 * dictionary.coordinates.size + 4 +
      3 * formula.clauses.toList.length + (formula.clauses.toList.map List.length).sum +
      2 * (Controller.Horn.IndexScan.occurrences formula.clauses.toList recordStart).length < 2 ^ width)
      (scanCapacity : scan + 47 < 2 ^ width)
      (fetch : Nat)
      (headAt : ∀ phase : Fin 4, program[seedDone + phase.val]? =
      (Controller.Horn.WorklistAccept.headSetupCode (n := dictionary.coordinates.size) width base fetch)[phase.val]?)
      (headCapacity : seedDone + 4 < 2 ^ width)
      (fifoDone bucket advance ready skip : Nat)
      (fetchAt : Controller.Horn.WorklistFIFO.FetchAt (n := dictionary.coordinates.size) program base fetch fifoDone bucket)
      (advanceAt : Controller.Horn.WorklistFIFO.AdvanceAt (n := dictionary.coordinates.size) program base advance fetch)
      (loopAt : Controller.Horn.WorklistBucketLoop.At program bucket advance ready)
      (readyAt : Controller.Horn.WorklistBucketReady.At (n := dictionary.coordinates.size) program base ready skip conflict bucket)
      (fetchCapacity : fetch + 14 < 2 ^ width)
      (advanceCapacity : advance + 5 < 2 ^ width)
      (bucketCapacity : bucket + 12 < 2 ^ width)
      (readyCapacity : ready + 26 < 2 ^ width)
      (projectionEntry cleanupEntry returnPc : Nat)
      (successAt : Controller.Cost.ForestZeroAnswer.SavedAt program fifoDone 1 projectionEntry)
      (conflictAt : Controller.Cost.ForestZeroAnswer.SavedAt program conflict 0 cleanupEntry)
      (successCapacity : fifoDone + 13 < 2 ^ width)
      (conflictCapacity : conflict + 13 < 2 ^ width)
      (localFit : dictionary.coordinates.size + 1 < 2 ^ width)
      (channelsFit : parameters.channels + 1 < 2 ^ width)
      (offRoom : base + 1 < 2 ^ width)
      (projectionCapacity : projectionEntry + 35 < 2 ^ width)
      (constantsAt : ∀ phase : Fin 2, program[projectionEntry + phase.val]? =
      (projectionConstantsCode width)[phase.val]?)
      (preparationAt : ∀ phase : Fin 19, program[projectionEntry + 2 + phase.val]? =
      (channelPrepareCode width)[phase.val]?)
    (saveEntry pushEntry nativeEntry done : Nat)
    (saveEq : saveEntry = projectionEntry + 21)
    (projectionEq : pushEntry = saveEntry + 8)
    (nativeSaveAt : SharedRootRead.BlockAt program saveEntry (SharedRegisterStack.saveCode (width := width) (List.finRange 8)))
    (restoreRoom : done + 8 < 2 ^ width)
    (restoreAt : SharedRootRead.BlockAt program done (SharedRegisterStack.restoreCode (width := width) (List.finRange 8).reverse))
    (projectionRoom : pushEntry + 14 < 2 ^ width)
    (projectionAt : ForestZeroChannelPush.CodeAt program pushEntry nativeEntry)
    (nativeRoom : nativeEntry + (NativeRetainedExecution.code parameters width (recordEnd + 2 * (Controller.Horn.IndexScan.occurrences formula.clauses.toList recordStart).length) nativeEntry).length < 2 ^ width)
    (nativeHeap : (recordEnd + 2 * (Controller.Horn.IndexScan.occurrences formula.clauses.toList recordStart).length) + parameters.channels + (compile parameters).toState.count < 2 ^ width)
    (nativeAt : ForestZeroCallerWiden.WidenedBlockAt program nativeEntry
      (NativeRetainedExecution.code parameters width (recordEnd + 2 * (Controller.Horn.IndexScan.occurrences formula.clauses.toList recordStart).length) nativeEntry))
    (finishRoom : emitEntry parameters width (recordEnd + 2 * (Controller.Horn.IndexScan.occurrences formula.clauses.toList recordStart).length) nativeEntry + 3 * (compile parameters).toState.count + 7 < 2 ^ width)
    (emitAt : ForestZeroCallerWiden.WidenedBlockAt program (emitEntry parameters width (recordEnd + 2 * (Controller.Horn.IndexScan.occurrences formula.clauses.toList recordStart).length) nativeEntry)
      (OutputProgram.emitCode width (NativeRealizedCore.addresses ((recordEnd + 2 * (Controller.Horn.IndexScan.occurrences formula.clauses.toList recordStart).length) + parameters.channels) (compile parameters).toState.count)))
    (releaseAt : Controller.Cost.RawTransferLoops.CodeAt program
      (emitEntry parameters width (recordEnd + 2 * (Controller.Horn.IndexScan.occurrences formula.clauses.toList recordStart).length) nativeEntry + 3 * (compile parameters).toState.count)
      (SharedEvaluationReclaim.code width (emitEntry parameters width (recordEnd + 2 * (Controller.Horn.IndexScan.occurrences formula.clauses.toList recordStart).length) nativeEntry + 3 * (compile parameters).toState.count)
        done (parameters.channels + (compile parameters).toState.count)))
    (nativeSetup : ∀ phase : Fin 3, program[done + 8 + phase.val]? =
      (Controller.Cost.ForestZeroReclaim.setupCode width)[phase.val]?)
    (nativeLoop : Controller.Cost.ForestZeroReclaim.At program (done + 11) returnPc)
    (nativeCleanupRoom : done + 15 < 2 ^ width)
      (cleanupSetup : ∀ phase : Fin 3, program[cleanupEntry + phase.val]? =
      (Controller.Cost.ForestZeroReclaim.setupCode width)[phase.val]?)
      (cleanupLoop : Controller.Cost.ForestZeroReclaim.At program (cleanupEntry + 3) returnPc)
      (cleanupCapacity : cleanupEntry + 7 < 2 ^ width)
      (resetCapacity : returnPc + 27 < 2 ^ width)
      (resetPrepareAt : ForestZeroCallerWiden.WidenedBlockAt program returnPc (resetPrepareCode width).toList)
      (resetLoopAt : ForestZeroCallerWiden.WidenedBlockAt program (returnPc + 15)
      (Controller.Cost.ForestZeroReset.code width (returnPc + 15)))
      (decisionCapacity : returnPc + 28 < 2 ^ width)
      (decisionAt : program[returnPc + 27]? = some (.pop 4)),
∃ answer : Bool, ∃ queue final ticks peak,
      Execution program
        (Controller.Cost.RegisterWiden.widenState
          (atState heap sourceEntry 0 originalLayout.tableBase originalLayout.inverseBase
            initialScratch rest output) highRegisters)
        final ticks peak ∧
      ticks ≤ 94 + 5 * references.length + 23 * references.flatten.length +
        86 * dictionary.coordinates.size +
        61 * (formula.clauses.toList.map List.length).sum + 125 * formula.clauses.toList.length +
        48 * (Controller.Horn.IndexScan.occurrences formula.clauses.toList recordStart).length +
        4 * (recordEnd + 2 * (Controller.Horn.IndexScan.occurrences formula.clauses.toList recordStart).length - keep) +
        (if answer then 55 * (selectedSize parameters).total + 186 else 144) ∧
      peak ≤ max
        (18 + heap.size + 2 * (references.length + 1) + 2 * references.flatten.length +
          2 * dictionary.coordinates.size + (word width heap.size :: rest).length + output.length)
        (state.liveWords + 5 * dictionary.coordinates.size +
        3 * formula.clauses.toList.length + (formula.clauses.toList.map List.length).sum +
        2 * (Controller.Horn.IndexScan.occurrences formula.clauses.toList recordStart).length + 3 * (selectedSize parameters).total + 16) ∧
      final.heap.size = keep ∧ final.stack = rest ∧
      final.output = (if answer then (NativeRootLoad.words width
        (SourceLift.finite parameters (Physical.realizeBridge parameters.bridge parameters.positiveBuses
          (setOfAssignment (SharedZeroNative.channels parameters dictionary queue
            (by rw [ambientEq]; omega)))))).reverse ++
          word width 1 :: state.output else word width 0 :: state.output) ∧
      final.pc = word width (returnPc + 28) ∧ final.halted = false ∧
      Controller.Cost.ForestZeroBackendFrame.PrefixFrame layout.tableBase state.heap final.heap ∧
      (∀ coordinate : Fin ambient, final.heap[layout.tableBase + coordinate.val]? = some (word width 0)) ∧
      final.reg 4 = word width (if answer then 1 else 0) ∧
      final.reg 0 = word width 0 ∧ final.reg 1 = word width layout.tableBase ∧
      final.reg 2 = word width layout.inverseBase ∧
      (answer = true ↔ ∃ assignment, Controller.CNF.Satisfies assignment formula) ∧
      (answer = true → Controller.CNF.Satisfies (Controller.Horn.WorklistOutcome.offAssignment queue) formula ∧
        Controller.Horn.WorklistOutcome.offAssignment queue = Controller.Horn.greatestCandidate formula) ∧
      final.liveWords ≤ (Controller.Cost.RegisterWiden.widenState
        (atState heap sourceEntry 0 originalLayout.tableBase originalLayout.inverseBase
          initialScratch rest output) highRegisters).liveWords +
        1 + (if answer then (compile parameters).toState.count else 0) ∧
      Controller.Cost.ForestZeroBackendFrame.PrefixFrame originalLayout.tableBase heap final.heap ∧
      ∃ reusableLayout : Layout ambient final.heap.size,
        reusableLayout.tableBase = originalLayout.tableBase ∧
        reusableLayout.inverseBase = originalLayout.inverseBase ∧
        Represented final.heap reusableLayout (ForestZeroCompile.empty ambient) ∧
      (∀ next : Nat, answer = false →
        QueryReady (ambient := ambient) heap originalLayout.tableBase originalLayout.inverseBase next rest
          (ForestZeroRootLoop.dispatchState final (returnPc + 28) next false)) := by
  intro within dictionary formula state backend layout keep recordHeader base recordStart recordEnd
  intro scan seedDone conflict countAt allocateAt headersAt endpointAt saveAt normalizerAt indexSaveAt indexAt indexRestoreAt captureAt fullCapacity setupAt scanAt room scanCapacity fetch headAt headCapacity fifoDone bucket advance ready skip fetchAt advanceAt loopAt readyAt fetchCapacity advanceCapacity bucketCapacity readyCapacity projectionEntry cleanupEntry returnPc successAt conflictAt successCapacity conflictCapacity localFit channelsFit offRoom projectionCapacity constantsAt preparationAt saveEntry pushEntry nativeEntry done saveEq projectionEq nativeSaveAt restoreRoom restoreAt projectionRoom projectionAt nativeRoom nativeHeap nativeAt finishRoom emitAt releaseAt nativeSetup nativeLoop nativeCleanupRoom cleanupSetup cleanupLoop cleanupCapacity resetCapacity resetPrepareAt resetLoopAt decisionCapacity decisionAt
  have actualDual : Controller.Horn.DualHorn formula :=
    constructorClauses_dualHorn heap originalLayout originalDictionary originalRepresentation.coherent
      references parameters.channels within sourceDual
  have originalInputs := constructor_canonical_inputs heap originalLayout originalDictionary
    originalRepresentation references parameters.channels within
  have actualStored : Stored formula.clauses.toList backend.directory backend.source state.heap := by
    simpa only [formula, state, backend, constructorState, RegisterWiden.widenState, atState,
      constructorFormulaBackend, constructorBackend, backendLayout, constructorFormula_rows] using originalInputs.1
  have actualCursor : CursorStored backend.directory backend.directoryHeader state.heap := by
    simpa only [formula, state, backend, constructorState, RegisterWiden.widenState, atState,
      constructorFormulaBackend, constructorBackend, backendLayout, constructorFormula_rows] using originalInputs.2.1
  have actualEnd : CursorStored (backend.directory + 2 * formula.clauses.toList.length) backend.endHeader state.heap := by
    simpa only [formula, state, backend, constructorState, RegisterWiden.widenState, atState,
      constructorFormulaBackend, constructorBackend, backendLayout, constructorFormula_rows] using originalInputs.2.2
  have actualBase : backend.base = state.heap.size := rfl
  have actualRecordHeader : backend.recordHeader = keep := rfl
  have actualLocalCount : state.reg 2 = word width dictionary.coordinates.size := rfl
  have actualSourcePointer : state.reg 1 = word width state.heap.size := rfl
  have actualHeadersAbove : ∀ address ∈ [backend.recordHeader, backend.inputHeader, backend.firstHeader,
      backend.directoryHeader, backend.endHeader], backend.recordHeader ≤ address := by
    intro address member
    change address ∈ [heap.size, heap.size + 1, heap.size + 2, heap.size + 3, heap.size + 4] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> change heap.size ≤ _ <;> omega
  have actualGrowth : keep ≤ state.heap.size := constructorHeap_growth heap originalLayout originalDictionary references parameters.channels
  have actualRepresented : Represented state.heap layout dictionary :=
    constructor_dictionary_represented heap originalLayout originalDictionary originalRepresentation references parameters.channels
  have actualTableBefore : layout.tableBase + ambient ≤ keep := originalLayout.tableBound
  have actualInverseBefore : layout.inverseBase + ambient ≤ keep := originalLayout.inverseBound
  have actualChannels : state.heap[0]? = some (word width parameters.channels) :=
    (constructor_source_cell heap originalLayout originalDictionary references parameters.channels sourceEnd 0
      sourceBeforeTable sourceBeforeInverse sourceBound (by omega)).trans sourceChannel
  have actualNodes : state.heap[1]? = some (word width nodes) :=
    (constructor_source_cell heap originalLayout originalDictionary references parameters.channels sourceEnd 1
      sourceBeforeTable sourceBeforeInverse sourceBound sourceHeaderRoom).trans sourceNodes
  obtain ⟨answer, queue, final, queryTicks, queryPeak, queryTrace, queryTime, querySpace,
      heapSize, finalStack, finalOutput, finalPC, finalRunning, finalFrame, zeroTable,
      decision, zeroRegister, tableRegister, inverseRegister, meaning, greatest⟩ :=
    scratch_indexed_native_reuse_execution parameters dictionary keep formula actualDual recordHeader recordStart recordEnd base entry scan seedDone conflict state program backend actualStored actualCursor actualEnd actualBase actualRecordHeader rfl rfl rfl rfl actualLocalCount actualSourcePointer countAt allocateAt headersAt endpointAt saveAt normalizerAt actualHeadersAbove indexSaveAt indexAt indexRestoreAt captureAt fullCapacity setupAt scanAt rfl rfl room scanCapacity actualGrowth actualGrowth fetch headAt headCapacity fifoDone bucket advance ready skip fetchAt advanceAt loopAt readyAt fetchCapacity advanceCapacity bucketCapacity readyCapacity projectionEntry cleanupEntry returnPc successAt conflictAt successCapacity conflictCapacity layout actualRepresented nodes ambientEq adjacent actualTableBefore actualInverseBefore (by omega) actualChannels actualNodes localFit channelsFit offRoom projectionCapacity constantsAt preparationAt saveEntry pushEntry nativeEntry done saveEq projectionEq nativeSaveAt restoreRoom restoreAt projectionRoom projectionAt nativeRoom nativeHeap nativeAt finishRoom emitAt releaseAt nativeSetup nativeLoop nativeCleanupRoom cleanupSetup cleanupLoop cleanupCapacity rest rfl tablePositive resetCapacity resetPrepareAt resetLoopAt decisionCapacity decisionAt
  obtain ⟨constructorTicks, constructorPeak, constructorTrace, constructorTime, constructorSpace⟩ :=
    constructor_state_execution program heap originalLayout originalDictionary originalRepresentation parameters.channels
      sourceEnd references sourceReferences sourceBeforeTable sourceBeforeInverse sourceBound sourcePositive
      sourceChannel within constructorEntry entry (word width heap.size :: rest) output highRegisters
      constructorRoom ambientFits constructorCapacity constructorAt
  have prepared := reuse_entry_execution program heap sourceEntry originalLayout.tableBase
    originalLayout.inverseBase initialScratch rest output highRegisters (by omega) entryAt
  have kept := keep_cursor_execution8 program heap originalLayout parameters.channels nodes (sourceEntry + 3)
    references rest output highRegisters ambientEq sourceEndpoint (by omega) sourceChannel sourceNodes
    (by omega) (by omega) keepAt (by simpa only [Nat.add_assoc] using cursorAt)
  simp only [Nat.add_assoc] at kept
  simp only [Nat.add_assoc] at constructorTrace
  rw [originalCount, entryEq] at constructorTrace
  have readyTrace := prepared.append kept
  have queryTraceAll := constructorTrace.append queryTrace
  have joined := readyTrace.append queryTraceAll
  refine ⟨answer, queue, final, 15 + (constructorTicks + queryTicks),
    max (max (10 + heap.size + rest.length + output.length)
      (11 + heap.size + rest.length + output.length)) (max constructorPeak queryPeak),
    (by simpa only [← Nat.add_assoc] using joined), ?_, ?_, heapSize, finalStack, finalOutput, finalPC, finalRunning, finalFrame,
    zeroTable, decision, zeroRegister, tableRegister, inverseRegister, meaning, greatest, ?_, ?_, ?_⟩
  · simp only [dictionary, constructorDictionary] at constructorTime queryTime ⊢
    cases answer <;> simp only [Bool.false_eq_true, ite_false, ite_true] at queryTime ⊢ <;> omega
  · have constructorBelow := Nat.le_max_left
        (18 + heap.size + 2 * (references.length + 1) + 2 * references.flatten.length +
          2 * dictionary.coordinates.size + (word width heap.size :: rest).length + output.length)
        (state.liveWords + 5 * dictionary.coordinates.size + 3 * formula.clauses.toList.length +
          (formula.clauses.toList.map List.length).sum +
          2 * (Controller.Horn.IndexScan.occurrences formula.clauses.toList recordStart).length + 3 * (selectedSize parameters).total + 16)
    have combined := max_le_max constructorSpace querySpace
    simp only [dictionary, constructorDictionary] at constructorSpace querySpace constructorBelow combined ⊢
    simp only [List.length_cons] at constructorBelow combined ⊢
    omega
  · unfold State.liveWords
    rw [heapSize, finalStack, finalOutput]
    cases answer <;> simp [keep, state, constructorState, RegisterWiden.widenState, atState, NativeRootLoad.words_length] <;> omega
  · have before := constructor_prefix heap originalLayout originalDictionary references parameters.channels adjacent
    have after : ForestZeroBackendFrame.PrefixFrame originalLayout.tableBase
        (constructorHeap heap originalLayout originalDictionary references parameters.channels) final.heap := by
      simpa only [layout, constructorDictionaryLayout, state, constructorState,
        RegisterWiden.widenState, atState] using finalFrame
    exact ForestZeroBackendFrame.trans before after
  · let reusableLayout : Layout ambient final.heap.size :=
      { tableBase := originalLayout.tableBase
        inverseBase := originalLayout.inverseBase
        tableBound := by rw [heapSize]; exact originalLayout.tableBound
        inverseBound := by rw [heapSize]; exact originalLayout.inverseBound
        disjoint := originalLayout.disjoint }
    have actualZero : ∀ coordinate : Fin ambient,
        final.heap[originalLayout.tableBase + coordinate.val]? = some (word width 0) := by
      intro coordinate
      simpa only [layout, constructorDictionaryLayout] using zeroTable coordinate
    refine ⟨reusableLayout, rfl, rfl,
      empty_dictionary_from_zero_table final.heap reusableLayout actualZero, ?_⟩
    intro next failed
    have originalFrame : ForestZeroBackendFrame.PrefixFrame originalLayout.tableBase heap final.heap := by
      have before := constructor_prefix heap originalLayout originalDictionary references parameters.channels adjacent
      have after : ForestZeroBackendFrame.PrefixFrame originalLayout.tableBase
          (constructorHeap heap originalLayout originalDictionary references parameters.channels) final.heap := by
        simpa only [layout, constructorDictionaryLayout, state, constructorState,
          RegisterWiden.widenState, atState] using finalFrame
      exact ForestZeroBackendFrame.trans before after
    exact failed_query_dispatch_ready heap originalLayout.tableBase originalLayout.inverseBase
      (returnPc + 28) next rest final heapSize originalFrame actualZero finalStack zeroRegister
      (by simpa only [layout, constructorDictionaryLayout] using tableRegister)
      (by simpa only [layout, constructorDictionaryLayout] using inverseRegister)


end Controller.Cost.SharedZeroNativePrepared
