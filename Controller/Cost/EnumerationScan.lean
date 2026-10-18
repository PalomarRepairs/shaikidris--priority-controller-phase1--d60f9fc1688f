module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.EnumerationLoop

@[expose] public section

/-! Loop invariant and the full returning output scan. -/
namespace Controller.Cost.EnumerationScan
open Controller.Cost.GateProgram Controller.Cost.RawTransferLoops
open Controller.Cost.ForestZeroDictionary Controller.Cost.ForestZeroAdmissibleCaller
open Controller.Cost.ForestZeroBackendFrame
open Controller.Native Controller.Native.SourceController Controller.Decoder
open Controller.Cost.NativeSourceExecution Controller.Cost.SharedZeroResidentConditions
open Controller.Cost.EnumerationLoop

abbrev Width (parameters : Parameters) (graph : DAG parameters.channels) (retained : Nat) :=
  SharedMachineCapacity.wordWidth retained graph.countedSize (selectedSize parameters).total

def Ready (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels)) (retained coordinateBase slot sourceEnd offset maskBase entry ret : Nat)
    (program : Program (Width parameters graph retained) 8) (rest : List (Word (Width parameters graph retained)))
    (state : State (Width parameters graph retained) 8) (source : Nat) (positions : List (Fin graph.roots.length)) : Prop :=
  ∃ currentRoot : Fin graph.nodeCount, ∃ sourceHeap : Array (Word (Width parameters graph retained)),
  ∃ layout : Layout (parameters.channels + graph.nodeCount) state.heap.size,
  SourceConditions parameters state layout
    (SharedZeroSource.references graph parameters.buses parameters.bridge.target T F coordinateBase slot currentRoot) sourceEnd graph.nodeCount ∧
  QueryReady (ambient := parameters.channels + graph.nodeCount) sourceHeap layout.tableBase layout.inverseBase entry
    (word (Width parameters graph retained) source :: word (Width parameters graph retained) positions.length ::
      (SharedDetectorData.healthyTags parameters graph (Width parameters graph retained) positions ++ rest)) state ∧
  SharedDetectorData.Stored parameters graph T F maskBase source offset slot positions sourceHeap ∧
  slot < layout.tableBase ∧ slot < sourceEnd ∧ 1 < slot ∧
  coordinateBase + (parameters.channels + graph.nodeCount) ≤ slot ∧
  state.heap.size ≤ retained ∧ positions.length ≤ graph.roots.length ∧
  entry + (EnumerationLoop.code parameters graph T F state.heap layout coordinateBase slot offset entry ret currentRoot).length ≤ retained ∧
  SharedRootRead.BlockAt program entry
    (EnumerationLoop.code parameters graph T F state.heap layout coordinateBase slot offset entry ret currentRoot)

/-- Cells below the query slot are never written by the scan. -/
def Kept (slot : Nat) (before after : Array (Word width)) : Prop :=
  after.size = before.size ∧ ∀ index, index < slot → after[index]? = before[index]?

theorem Kept.refl (slot : Nat) (heap : Array (Word width)) : Kept slot heap heap := ⟨rfl, fun _ _ => rfl⟩

theorem Kept.trans {slot : Nat} {first second third : Array (Word width)}
    (left : Kept slot first second) (right : Kept slot second third) : Kept slot first third :=
  ⟨right.1.trans left.1, fun index below => (right.2 index below).trans (left.2 index below)⟩

theorem kept_of_ready {sourceHeap : Array (Word width)} {tableBase inverseBase entry next slot : Nat}
    {rest next_rest : List (Word width)} {before after : State width 8} {value : Word width}
    (valid : slot < sourceHeap.size)
    (beforeReady : QueryReady (ambient := ambient) sourceHeap tableBase inverseBase entry rest before)
    (afterReady : QueryReady (ambient := ambient) (sourceHeap.set slot value valid) tableBase inverseBase next next_rest after)
    (slotBefore : slot < tableBase) : Kept slot before.heap after.heap := by
  refine ⟨?_, ?_⟩
  · rw [afterReady.heapSize, Array.size_set, beforeReady.heapSize]
  · intro index below
    rw [afterReady.sourceFrame.2.2 index (by omega), Array.getElem?_set_ne valid (by omega),
      beforeReady.sourceFrame.2.2 index (by omega)]

theorem QueryReady.moved {sourceHeap : Array (Word width)} {tableBase inverseBase entry next : Nat}
    {rest : List (Word width)} {before after : State width 8}
    (ready : QueryReady (ambient := ambient) sourceHeap tableBase inverseBase entry rest before)
    (heap : after.heap = before.heap) (stack : after.stack = before.stack) (regs : after.reg = before.reg)
    (position : after.pc = word width next) (running : after.halted = false) :
    QueryReady (ambient := ambient) sourceHeap tableBase inverseBase next rest after :=
  ⟨by rw [heap]; exact ready.heapSize, by rw [heap]; exact ready.sourceFrame,
    by rw [heap]; exact ready.zeroTable, stack.trans ready.stack, position, running,
    by rw [regs]; exact ready.zeroRegister, by rw [regs]; exact ready.tableRegister,
    by rw [regs]; exact ready.inverseRegister⟩

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4096 in
theorem skipped (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels)) (retained coordinateBase slot sourceEnd offset maskBase entry ret : Nat)
    (program : Program (Width parameters graph retained) 8) (rest : List (Word (Width parameters graph retained)))
    (state : State (Width parameters graph retained) 8) (source : Nat)
    (position : Fin graph.roots.length) (positions : List (Fin graph.roots.length))
    (unhealthy : graph.eval (assignmentOfSet {parameters.bridge.target}) graph.roots[position.val] = false)
    (missing : SharedWitnessDecode.tag graph (extensionBase parameters.buses parameters.bridge.target T) F
      (Width parameters graph retained) position = word (Width parameters graph retained) (parameters.channels + 1))
    (prepared : Ready parameters graph T F retained coordinateBase slot sourceEnd offset maskBase entry ret program rest state
      source (position :: positions)) :
    ∃ final ticks peak, Execution program state final ticks peak ∧ ticks ≤ 26 ∧ peak = state.liveWords ∧
      final.liveWords + 1 = state.liveWords ∧ final.output = state.output ∧ Kept slot state.heap final.heap ∧
      Ready parameters graph T F retained coordinateBase slot sourceEnd offset maskBase entry ret program rest final
        (source + 1) positions := by
  rcases prepared with ⟨currentRoot, sourceHeap, layout, sourceData, query, data, slotBefore, slotBound, headerBefore,
    tableBefore, heapBound, countBound, budget, present⟩
  obtain ⟨cursorAt, acceptAt, skipAt, healthyAt, queryAt, dispatchAt, exhaustedAt⟩ :=
    EnumerationLoop.blocks_at parameters graph T F state.heap layout coordinateBase slot offset entry ret currentRoot program present
  have codeSize := EnumerationLoop.code_length parameters graph T F state.heap layout coordinateBase slot offset entry ret currentRoot
  have capacity := SharedMachineCapacity.capacity retained graph.countedSize (selectedSize parameters).total
  change 131072 * (retained + graph.countedSize + (selectedSize parameters).total + 1) < 2 ^ (Width parameters graph retained) at capacity
  have graphSize := graph.countedSize_eq
  have queryEnd := EnumerationLoop.query_end parameters graph T F state.heap layout coordinateBase slot entry currentRoot
  have actualData := SharedDetectorData.ready parameters graph T F maskBase source offset slot (position :: positions)
    sourceHeap state layout.tableBase layout.inverseBase entry _ data query slotBefore
  obtain ⟨candidateStored, rootStored, sourceValid, rootValid⟩ :=
    SharedDetectorData.head parameters graph T F maskBase source offset slot position positions state.heap actualData
  rw [missing] at candidateStored
  obtain ⟨final, ticks, trace, time, heap, output, nextReady, live⟩ :=
    SharedRootTaggedSkip.execution program state sourceHeap layout.tableBase layout.inverseBase parameters.channels entry
      (EnumerationLoop.returnPoint parameters graph T F state.heap.size coordinateBase slot entry currentRoot (Width parameters graph retained) + 5)
      (entry + 37) (entry + 31) source positions.length
      parameters.bridge.target (SharedDetectorData.healthyTags parameters graph (Width parameters graph retained) positions ++ rest)
      (by simpa only [SharedDetectorData.healthyTags, List.map_cons, unhealthy, Bool.false_eq_true, ↓reduceIte, List.cons_append,
        List.length_cons] using query) (by omega) (by omega) (by omega)
      (by simp only [List.length_cons] at countBound; omega) (by omega) sourceValid candidateStored cursorAt skipAt
  have sameSize : final.heap.size = state.heap.size := congrArg Array.size heap
  let nextLayout := SharedQuerySourceFrame.layout state final layout sameSize
  have sameCode := EnumerationLoop.shared parameters graph T F state.heap final.heap layout nextLayout
    coordinateBase slot offset entry ret currentRoot currentRoot sameSize.symm rfl rfl
  have nextSource := SharedQuerySourceFrame.transport parameters state final layout
    (SharedZeroSource.references graph parameters.buses parameters.bridge.target T F coordinateBase slot currentRoot)
    sourceEnd graph.nodeCount sourceData sameSize (by
      refine ⟨sourceData.sourceBound, ?_, ?_⟩
      · rw [heap]; exact sourceData.sourceBound
      · intro index below; rw [heap])
  refine ⟨final, ticks, state.liveWords, trace, time, rfl, live, output, by rw [heap]; exact Kept.refl slot _,
    currentRoot, sourceHeap, nextLayout, nextSource, nextReady,
    SharedDetectorData.tail parameters graph T F maskBase source offset slot position positions sourceHeap data,
    slotBefore, slotBound, headerBefore, tableBefore, sameSize.le.trans heapBound, ?_, ?_, ?_⟩
  · simp only [List.length_cons] at countBound; omega
  · rw [← sameCode]; exact budget
  · rw [← sameCode]; exact present

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4096 in
theorem found (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels)) (retained coordinateBase slot sourceEnd offset maskBase entry ret : Nat)
    (program : Program (Width parameters graph retained) 8) (rest : List (Word (Width parameters graph retained)))
    (state : State (Width parameters graph retained) 8) (source : Nat)
    (position : Fin graph.roots.length) (positions : List (Fin graph.roots.length))
    (unhealthy : graph.eval (assignmentOfSet {parameters.bridge.target}) graph.roots[position.val] = false)
    (candidateFound : SharedWitnessDecode.tag graph (extensionBase parameters.buses parameters.bridge.target T) F
      (Width parameters graph retained) position ≠ word (Width parameters graph retained) (parameters.channels + 1))
    (prepared : Ready parameters graph T F retained coordinateBase slot sourceEnd offset maskBase entry ret program rest state
      source (position :: positions)) :
    ∃ final ticks peak, Execution program state final ticks peak ∧
      ticks ≤ 4 * graph.roots.length + 26 ∧ peak ≤ state.liveWords ∧
      final.halted = false ∧ final.pc = word (Width parameters graph retained) ret ∧ final.reg 4 = word (Width parameters graph retained) 1 ∧
      final.stack = rest ∧ final.output = state.output ∧ Kept slot state.heap final.heap := by
  rcases prepared with ⟨currentRoot, sourceHeap, layout, sourceData, query, data, slotBefore, slotBound, headerBefore,
    tableBefore, heapBound, countBound, budget, present⟩
  obtain ⟨cursorAt, acceptAt, skipAt, healthyAt, queryAt, dispatchAt, exhaustedAt⟩ :=
    EnumerationLoop.blocks_at parameters graph T F state.heap layout coordinateBase slot offset entry ret currentRoot program present
  have codeSize := EnumerationLoop.code_length parameters graph T F state.heap layout coordinateBase slot offset entry ret currentRoot
  have capacity := SharedMachineCapacity.capacity retained graph.countedSize (selectedSize parameters).total
  change 131072 * (retained + graph.countedSize + (selectedSize parameters).total + 1) < 2 ^ (Width parameters graph retained) at capacity
  have graphSize := graph.countedSize_eq
  have queryEnd := EnumerationLoop.query_end parameters graph T F state.heap layout coordinateBase slot entry currentRoot
  have actualData := SharedDetectorData.ready parameters graph T F maskBase source offset slot (position :: positions)
    sourceHeap state layout.tableBase layout.inverseBase entry _ data query slotBefore
  obtain ⟨candidateStored, rootStored, sourceValid, rootValid⟩ :=
    SharedDetectorData.head parameters graph T F maskBase source offset slot position positions state.heap actualData
  obtain ⟨inspected, inspectTicks, inspectTrace, inspectTime, inspectHeap, inspectStack, inspectOutput, inspectPC,
      inspectRunning, inspectNext, inspectCursor, inspectCount, inspectCandidate⟩ :=
    SharedRootTaggedCursor.successor_execution program state parameters.channels entry
      (EnumerationLoop.returnPoint parameters graph T F state.heap.size coordinateBase slot entry currentRoot (Width parameters graph retained) + 5)
      (entry + 37) (entry + 31) source positions.length parameters.bridge.target false
      (SharedWitnessDecode.tag graph (extensionBase parameters.buses parameters.bridge.target T) F (Width parameters graph retained) position)
      (SharedDetectorData.healthyTags parameters graph (Width parameters graph retained) positions ++ rest) query.position query.running
      (by omega) (by omega) (by simp only [List.length_cons] at countBound; omega) (by omega) sourceValid candidateStored
      (by simpa only [SharedDetectorData.healthyTags, List.map_cons, unhealthy, Bool.false_eq_true, ↓reduceIte,
        List.cons_append, List.length_cons] using query.stack) cursorAt
  have acceptPC : inspected.pc = word (Width parameters graph retained) (entry + 22) := by
    simpa only [Bool.false_eq_true, ↓reduceIte, candidateFound] using inspectPC
  obtain ⟨final, acceptTicks, acceptPeak, acceptTrace, acceptTime, acceptSpace, finalHeap, finalStack, finalOutput,
      finalPC, finalRunning, decision⟩ :=
    EnumerationLoop.accept_execution program inspected entry ret
      (SharedDetectorData.healthyTags parameters graph (Width parameters graph retained) positions) rest acceptPC inspectRunning (by omega)
      (by simp only [SharedDetectorData.healthyTags_length]; simp only [List.length_cons] at countBound; omega)
      inspectStack (by simpa only [SharedDetectorData.healthyTags_length] using inspectCount) acceptAt
  have inspectLive : inspected.liveWords ≤ state.liveWords := inspectTrace.final_storage_le
  simp only [SharedDetectorData.healthyTags_length] at acceptTime
  refine ⟨final, inspectTicks + acceptTicks, max state.liveWords acceptPeak, inspectTrace.append acceptTrace,
    by simp only [List.length_cons] at countBound; omega, by omega, finalRunning, finalPC, decision, finalStack,
    finalOutput.trans inspectOutput, by rw [finalHeap, inspectHeap]; exact Kept.refl slot _⟩

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in
theorem healthy (parameters : Parameters) (graph : DAG parameters.channels) (guarded : graph.Guarded)
    (T F : Finset (Fin parameters.channels)) (retained coordinateBase slot sourceEnd offset maskBase entry ret : Nat)
    (program : Program (Width parameters graph retained) 8) (rest : List (Word (Width parameters graph retained)))
    (state : State (Width parameters graph retained) 8) (source : Nat)
    (position : Fin graph.roots.length) (positions : List (Fin graph.roots.length))
    (healthyTrue : graph.eval (assignmentOfSet {parameters.bridge.target}) graph.roots[position.val] = true)
    (prepared : Ready parameters graph T F retained coordinateBase slot sourceEnd offset maskBase entry ret program rest state
      source (position :: positions)) :
    ∃ answer : Bool, ∃ final ticks peak,
      Execution program state final ticks peak ∧ ticks ≤ 4900 * (graph.countedSize + 1) ∧
      peak ≤ state.liveWords + 200 * (graph.countedSize + 1) ∧
      final.output = state.output ∧ Kept slot state.heap final.heap ∧
      (answer = true ↔ SharedDetectorFeasibility.AtRoot parameters graph T F position) ∧
      (answer = true → final.halted = false ∧ final.pc = word (Width parameters graph retained) ret ∧ final.reg 4 = word (Width parameters graph retained) 1 ∧
        final.stack = rest) ∧
      (answer = false → final.liveWords + 1 = state.liveWords ∧
        Ready parameters graph T F retained coordinateBase slot sourceEnd offset maskBase entry ret program rest final
          (source + 1) positions) := by
  rcases prepared with ⟨currentRoot, sourceHeap, layout, sourceData, query, data, slotBefore, slotBound, headerBefore,
    tableBefore, heapBound, countBound, budget, present⟩
  obtain ⟨cursorAt, acceptAt, skipAt, healthyAt, queryAt, dispatchAt, exhaustedAt⟩ :=
    EnumerationLoop.blocks_at parameters graph T F state.heap layout coordinateBase slot offset entry ret currentRoot program present
  have codeSize := EnumerationLoop.code_length parameters graph T F state.heap layout coordinateBase slot offset entry ret currentRoot
  have capacity := SharedMachineCapacity.capacity retained graph.countedSize (selectedSize parameters).total
  change 131072 * (retained + graph.countedSize + (selectedSize parameters).total + 1) < 2 ^ (Width parameters graph retained) at capacity
  have graphSize := graph.countedSize_eq
  have queryEnd := EnumerationLoop.query_end parameters graph T F state.heap layout coordinateBase slot entry currentRoot
  have actualData := SharedDetectorData.ready parameters graph T F maskBase source offset slot (position :: positions)
    sourceHeap state layout.tableBase layout.inverseBase entry _ data query slotBefore
  obtain ⟨candidateStored, rootStored, sourceValid, rootValid⟩ :=
    SharedDetectorData.head parameters graph T F maskBase source offset slot position positions state.heap actualData
  obtain ⟨answer, queried, queryTicks, queryPeak, queryTrace, queryRunning, queryPC, decision, queryTime, querySpace,
      queryOutput, queryLive, meaning, queryReady, querySize, querySource⟩ :=
    EnumerationRootQuery.healthy_execution parameters graph guarded T F currentRoot (graph.roots[position.val]'position.isLt) program
      state sourceHeap layout coordinateBase slot sourceEnd entry
      (EnumerationLoop.returnPoint parameters graph T F state.heap.size coordinateBase slot entry currentRoot (Width parameters graph retained) + 5)
      (entry + 37) (entry + 31) source positions.length offset
      (SharedWitnessDecode.tag graph (extensionBase parameters.buses parameters.bridge.target T) F (Width parameters graph retained) position)
      (SharedDetectorData.healthyTags parameters graph (Width parameters graph retained) positions ++ rest)
      sourceData (by simpa only [SharedDetectorData.healthyTags, List.map_cons, healthyTrue, ↓reduceIte,
        List.cons_append, List.length_cons] using query) heapBound (by omega) (by omega)
      (by simpa only [List.length_cons] using countBound) sourceValid rootValid slotBefore slotBound headerBefore tableBefore
      candidateStored rootStored cursorAt healthyAt (by simpa only [Nat.add_assoc, Nat.reduceAdd] using queryAt)
  simp only [Nat.add_assoc, Nat.reduceAdd] at queryPC queryReady
  rw [EnumerationLoop.returnEntry_point parameters graph T F state.heap.size coordinateBase slot entry
    (Width parameters graph retained) (graph.roots[position.val]'position.isLt) currentRoot] at queryPC queryReady
  have rootValidSlot : slot < sourceHeap.size := by have := query.sourceFrame.1; omega
  have kept : Kept slot state.heap queried.heap := kept_of_ready rootValidSlot query queryReady slotBefore
  have semantic := meaning.trans (SharedDetectorFeasibility.healthy_iff parameters graph T F position healthyTrue).symm
  cases answer with
  | true =>
    obtain ⟨dispatched, dispatchPeak, dispatchTrace, dispatchSpace, dispatchHeap, dispatchStack, dispatchOutput,
        dispatchCount, dispatchPC, dispatchRunning⟩ :=
      EnumerationLoop.dispatch_accepted program queried _ entry _ _ _ queryPC queryRunning (by omega)
        (by simpa using decision) (by omega) queryReady.stack dispatchAt
    obtain ⟨final, acceptTicks, acceptPeak, acceptTrace, acceptTime, acceptSpace, finalHeap, finalStack, finalOutput,
        finalPC, finalRunning, finalDecision⟩ :=
      EnumerationLoop.accept_execution program dispatched entry ret
        (SharedDetectorData.healthyTags parameters graph (Width parameters graph retained) positions) rest dispatchPC dispatchRunning (by omega)
        (by simp only [SharedDetectorData.healthyTags_length]; simp only [List.length_cons] at countBound; omega)
        dispatchStack (by simpa only [SharedDetectorData.healthyTags_length] using dispatchCount) acceptAt
    have queriedLive : queried.liveWords ≤ queryPeak := queryTrace.final_storage_le
    simp only [SharedDetectorData.healthyTags_length] at acceptTime
    refine ⟨true, final, queryTicks + (5 + acceptTicks), max queryPeak (max dispatchPeak acceptPeak),
      queryTrace.append (dispatchTrace.append acceptTrace), ?_, ?_, ?_, ?_, semantic, ?_, ?_⟩
    · simp only [List.length_cons] at countBound; omega
    · have dispatchedLive : dispatched.liveWords ≤ dispatchPeak := dispatchTrace.final_storage_le
      simp only [max_le_iff]; omega
    · rw [finalOutput, dispatchOutput, queryOutput]
    · rw [finalHeap, dispatchHeap]; exact kept
    · intro _; exact ⟨finalRunning, finalPC, finalDecision, finalStack⟩
    · intro impossible; cases impossible
  | false =>
    obtain ⟨final, dispatchTrace, dispatchHeap, dispatchStack, dispatchOutput, dispatchRegs, dispatchPC, dispatchRunning⟩ :=
      EnumerationLoop.dispatch_failed program queried _ entry queryPC queryRunning (by omega)
        (by simpa using decision) dispatchAt
    have finalReady := QueryReady.moved queryReady dispatchHeap dispatchStack dispatchRegs dispatchPC dispatchRunning
    have finalSize : final.heap.size = state.heap.size := by rw [dispatchHeap]; exact querySize
    let nextLayout := SharedQuerySourceFrame.layout state final layout finalSize
    have finalSource : SourceConditions parameters final nextLayout
        (SharedZeroSource.references graph parameters.buses parameters.bridge.target T F coordinateBase slot
          (graph.roots[position.val]'position.isLt)) sourceEnd graph.nodeCount := by
      exact SharedQuerySourceFrame.transport parameters queried final
        (SharedQuerySourceFrame.layout state queried layout querySize)
        (SharedZeroSource.references graph parameters.buses parameters.bridge.target T F coordinateBase slot
          (graph.roots[position.val]'position.isLt)) sourceEnd graph.nodeCount querySource (by rw [dispatchHeap])
        (by rw [dispatchHeap]; exact ForestZeroBackendFrame.refl _ querySource.sourceBound)
    let nextHeap := sourceHeap.set slot (word (Width parameters graph retained) (graph.roots[position.val]'position.isLt).val) rootValidSlot
    have updated := SharedDetectorData.root_update parameters graph T F maskBase source offset slot (position :: positions)
      sourceHeap (word (Width parameters graph retained) (graph.roots[position.val]'position.isLt).val) rootValidSlot data
    have nextData := SharedDetectorData.tail parameters graph T F maskBase source offset slot position positions _ updated
    have sameCode := EnumerationLoop.shared parameters graph T F state.heap final.heap layout nextLayout
      coordinateBase slot offset entry ret currentRoot (graph.roots[position.val]'position.isLt) finalSize.symm rfl rfl
    have queriedLive : queried.liveWords ≤ queryPeak := queryTrace.final_storage_le
    have finalLive : final.liveWords = queried.liveWords := by
      simp only [State.liveWords, dispatchHeap, dispatchStack, dispatchOutput]
    refine ⟨false, final, queryTicks + 1, max queryPeak queried.liveWords, queryTrace.append dispatchTrace,
      by omega, by simp only [max_le_iff]; omega, by rw [dispatchOutput, queryOutput],
      by rw [dispatchHeap]; exact kept, semantic, (fun impossible => by cases impossible), ?_⟩
    intro _
    refine ⟨by omega, (graph.roots[position.val]'position.isLt), nextHeap, nextLayout, finalSource,
      finalReady, nextData,
      slotBefore, slotBound, headerBefore, tableBefore, finalSize.le.trans heapBound, ?_, ?_, ?_⟩
    · simp only [List.length_cons] at countBound; omega
    · rw [← sameCode]; exact budget
    · rw [← sameCode]; exact present

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4096 in
theorem empty (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels)) (retained coordinateBase slot sourceEnd offset maskBase entry ret : Nat)
    (program : Program (Width parameters graph retained) 8) (rest : List (Word (Width parameters graph retained)))
    (state : State (Width parameters graph retained) 8) (source : Nat)
    (prepared : Ready parameters graph T F retained coordinateBase slot sourceEnd offset maskBase entry ret program rest state
      source []) :
    ∃ final, Execution program state final 6 state.liveWords ∧ final.halted = false ∧ final.pc = word (Width parameters graph retained) ret ∧
      final.reg 4 = word (Width parameters graph retained) 0 ∧ final.heap = state.heap ∧ final.stack = rest ∧ final.output = state.output := by
  rcases prepared with ⟨currentRoot, sourceHeap, layout, sourceData, query, data, slotBefore, slotBound, headerBefore,
    tableBefore, heapBound, countBound, budget, present⟩
  obtain ⟨cursorAt, acceptAt, skipAt, healthyAt, queryAt, dispatchAt, exhaustedAt⟩ :=
    EnumerationLoop.blocks_at parameters graph T F state.heap layout coordinateBase slot offset entry ret currentRoot program present
  have codeSize := EnumerationLoop.code_length parameters graph T F state.heap layout coordinateBase slot offset entry ret currentRoot
  have capacity := SharedMachineCapacity.capacity retained graph.countedSize (selectedSize parameters).total
  change 131072 * (retained + graph.countedSize + (selectedSize parameters).total + 1) < 2 ^ (Width parameters graph retained) at capacity
  have queryEnd := EnumerationLoop.query_end parameters graph T F state.heap layout coordinateBase slot entry currentRoot
  obtain ⟨stopped, cursorTrace, stoppedHeap, stoppedOutput, stoppedReady⟩ :=
    SharedRootCursor.zero_ready program state sourceHeap layout.tableBase layout.inverseBase entry
      (EnumerationLoop.returnPoint parameters graph T F state.heap.size coordinateBase slot entry currentRoot (Width parameters graph retained) + 5)
      source rest (by simpa only [SharedDetectorData.healthyTags, List.map_nil, List.nil_append, List.length_nil] using query)
      (by omega) (by simpa [SharedRootTaggedCursor.code] using
        (show CodeAt program entry (SharedRootTaggedCursor.code (Width parameters graph retained) parameters.channels entry
          (EnumerationLoop.returnPoint parameters graph T F state.heap.size coordinateBase slot entry currentRoot (Width parameters graph retained) + 5)
          (entry + 37) (entry + 31)) from cursorAt) |> RawSharedOrdered.takePrefix program entry _ _)
  obtain ⟨final, exitTrace, finalHeap, finalStack, finalOutput, decision, finalPC, finalRunning⟩ :=
    EnumerationLoop.exhausted_execution program stopped _ ret stoppedReady.position stoppedReady.running (by omega) exhaustedAt
  have stoppedLive : stopped.liveWords ≤ state.liveWords := cursorTrace.final_storage_le
  have joined := cursorTrace.append exitTrace
  refine ⟨final, by simpa only [Nat.max_eq_left stoppedLive] using joined, finalRunning, finalPC, decision,
    finalHeap.trans stoppedHeap, finalStack.trans stoppedReady.stack, finalOutput.trans stoppedOutput⟩

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4096 in
theorem step (parameters : Parameters) (graph : DAG parameters.channels) (guarded : graph.Guarded)
    (T F : Finset (Fin parameters.channels))
    (consistent : FixedConsistent (extensionBase parameters.buses parameters.bridge.target T) F)
    (retained coordinateBase slot sourceEnd offset maskBase entry ret : Nat)
    (program : Program (Width parameters graph retained) 8) (rest : List (Word (Width parameters graph retained)))
    (state : State (Width parameters graph retained) 8) (source : Nat)
    (position : Fin graph.roots.length) (positions : List (Fin graph.roots.length))
    (prepared : Ready parameters graph T F retained coordinateBase slot sourceEnd offset maskBase entry ret program rest state
      source (position :: positions)) :
    ∃ answer : Bool, ∃ final ticks peak,
      Execution program state final ticks peak ∧ ticks ≤ 4900 * (graph.countedSize + 1) ∧
      peak ≤ state.liveWords + 200 * (graph.countedSize + 1) ∧
      final.output = state.output ∧ Kept slot state.heap final.heap ∧
      (answer = true ↔ SharedDetectorFeasibility.AtRoot parameters graph T F position) ∧
      (answer = true → final.halted = false ∧ final.pc = word (Width parameters graph retained) ret ∧ final.reg 4 = word (Width parameters graph retained) 1 ∧
        final.stack = rest) ∧
      (answer = false → final.liveWords + 1 = state.liveWords ∧
        Ready parameters graph T F retained coordinateBase slot sourceEnd offset maskBase entry ret program rest final
          (source + 1) positions) := by
  have countBound : (position :: positions).length ≤ graph.roots.length := by
    rcases prepared with ⟨_, _, _, _, _, _, _, _, _, _, _, bound, _⟩; exact bound
  have graphSize := graph.countedSize_eq
  cases health : graph.eval (assignmentOfSet {parameters.bridge.target}) graph.roots[position.val] with
  | true =>
    exact (healthy parameters graph guarded T F retained coordinateBase slot sourceEnd offset maskBase entry ret
      program rest state source position positions health prepared)
  | false =>
    have capacity := SharedMachineCapacity.capacity retained graph.countedSize (selectedSize parameters).total
    have graphCapacity : 256 * (graph.countedSize + 1) < 2 ^ (Width parameters graph retained) := by
      change 131072 * (retained + graph.countedSize + (selectedSize parameters).total + 1) < 2 ^ (Width parameters graph retained) at capacity
      omega
    have criterion := SharedDetectorFeasibility.candidate_iff parameters graph guarded T F position (Width parameters graph retained)
      consistent graphCapacity health
    by_cases missing : SharedWitnessDecode.tag graph (extensionBase parameters.buses parameters.bridge.target T) F
        (Width parameters graph retained) position = word (Width parameters graph retained) (parameters.channels + 1)
    · obtain ⟨final, ticks, peak, trace, time, peakEq, live, output, kept, nextReady⟩ :=
        skipped parameters graph T F retained coordinateBase slot sourceEnd offset maskBase entry ret program rest state
          source position positions health missing prepared
      refine ⟨false, final, ticks, peak, trace, by omega, by omega, output, kept, ?_,
        (fun impossible => by cases impossible), fun _ => ⟨live, nextReady⟩⟩
      simp only [Bool.false_eq_true, false_iff]
      intro feasible
      exact (criterion.mpr feasible) missing
    · obtain ⟨final, ticks, peak, trace, time, space, halted, pc, decision, stack, output, kept⟩ :=
        found parameters graph T F retained coordinateBase slot sourceEnd offset maskBase entry ret program rest state
          source position positions health missing prepared
      simp only [List.length_cons] at countBound
      refine ⟨true, final, ticks, peak, trace, by omega, by omega, output, kept,
        ⟨fun _ => criterion.mp missing, fun _ => rfl⟩, fun _ => ⟨halted, pc, decision, stack⟩,
        fun impossible => by cases impossible⟩

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4096 in
/-- The whole returning scan: register 4 = 1 exactly when some remaining output admits a fixed
extension that differs from its healthy value; the stack, output and every cell below the
query slot are preserved, and control returns to `ret`. -/
theorem execution (parameters : Parameters) (graph : DAG parameters.channels) (guarded : graph.Guarded)
    (T F : Finset (Fin parameters.channels))
    (consistent : FixedConsistent (extensionBase parameters.buses parameters.bridge.target T) F)
    (retained coordinateBase slot sourceEnd offset maskBase entry ret : Nat)
    (program : Program (Width parameters graph retained) 8) (rest : List (Word (Width parameters graph retained)))
    (positions : List (Fin graph.roots.length)) (state : State (Width parameters graph retained) 8) (source : Nat)
    (prepared : Ready parameters graph T F retained coordinateBase slot sourceEnd offset maskBase entry ret program rest state
      source positions) :
    ∃ answer : Bool, ∃ final ticks peak,
      Execution program state final ticks peak ∧ final.halted = false ∧ final.pc = word (Width parameters graph retained) ret ∧
      final.reg 4 = word (Width parameters graph retained) (if answer then 1 else 0) ∧ final.stack = rest ∧ final.output = state.output ∧
      Kept slot state.heap final.heap ∧
      ticks ≤ positions.length * (4900 * (graph.countedSize + 1)) + 6 ∧
      peak ≤ state.liveWords + 200 * (graph.countedSize + 1) ∧
      (answer = true ↔ ∃ position ∈ positions, SharedDetectorFeasibility.AtRoot parameters graph T F position) := by
  induction positions generalizing state source with
  | nil =>
    obtain ⟨final, trace, halted, pc, decision, heap, stack, output⟩ :=
      empty parameters graph T F retained coordinateBase slot sourceEnd offset maskBase entry ret program rest state
        source prepared
    refine ⟨false, final, 6, state.liveWords, trace, halted, pc, by simpa only [Bool.false_eq_true, ↓reduceIte] using decision, stack, output,
      by rw [heap]; exact Kept.refl slot _, by simp, by omega, by simp⟩
  | cons position positions ih =>
    obtain ⟨answer, middle, ticks, peak, trace, time, space, output, kept, meaning, accepted, continued⟩ :=
      step parameters graph guarded T F consistent retained coordinateBase slot sourceEnd offset maskBase entry ret
        program rest state source position positions prepared
    cases answer with
    | true =>
      obtain ⟨halted, pc, decision, stack⟩ := accepted rfl
      refine ⟨true, middle, ticks, peak, trace, halted, pc, by simpa only [↓reduceIte] using decision, stack, output, kept, ?_, space, ?_⟩
      · have scaled := Nat.le_mul_of_pos_left (4900 * (graph.countedSize + 1)) (Nat.succ_pos positions.length)
        rw [List.length_cons]
        exact Nat.le_add_right_of_le (time.trans scaled)
      · constructor
        · intro _; exact ⟨position, List.mem_cons_self, meaning.mp rfl⟩
        · intro _; rfl
    | false =>
      obtain ⟨live, nextReady⟩ := continued rfl
      obtain ⟨result, final, tailTicks, tailPeak, tailTrace, tailHalted, tailPC, tailDecision, tailStack, tailOutput,
        tailKept, tailTime, tailSpace, tailMeaning⟩ := ih middle (source + 1) nextReady
      refine ⟨result, final, ticks + tailTicks, max peak tailPeak, trace.append tailTrace, tailHalted, tailPC,
        tailDecision, tailStack, tailOutput.trans output, kept.trans tailKept, ?_, ?_, ?_⟩
      · simp only [List.length_cons, Nat.add_mul, Nat.one_mul]; omega
      · apply max_le <;> omega
      · constructor
        · intro accepted
          obtain ⟨next, member, feasible⟩ := tailMeaning.mp accepted
          exact ⟨next, List.mem_cons_of_mem position member, feasible⟩
        · rintro ⟨next, member, feasible⟩
          rcases List.mem_cons.mp member with same | member
          · subst next
            have impossible := meaning.mpr feasible
            cases impossible
          · exact tailMeaning.mpr ⟨next, member, feasible⟩

end Controller.Cost.EnumerationScan
