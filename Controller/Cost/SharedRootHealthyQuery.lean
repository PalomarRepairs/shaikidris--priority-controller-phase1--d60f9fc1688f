module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedRootHealthyEntry
public import Controller.Cost.SharedRootResidentLoop

@[expose] public section

namespace Controller.Cost.SharedRootHealthyQuery
open Controller.Cost.GateProgram Controller.Cost.RawTransferLoops
open Controller.Cost.ForestZeroDictionary Controller.Cost.ForestZeroAdmissibleCaller
open Controller.Native Controller.Native.SourceController Controller.Decoder
open Controller.Cost.NativeSourceExecution Controller.Cost.SharedZeroResidentConditions
open Controller.Cost.SharedZeroNativeQuery Controller.Cost.SharedMachineCapacity

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem execution (parameters : Parameters) (graph : DAG parameters.channels) (guarded : graph.Guarded)
    (T F : Finset (Fin parameters.channels)) (oldRoot root : Fin graph.nodeCount)
    (program : Program (wordWidth retained graph.countedSize (selectedSize parameters).total) 8)
    (state : State (wordWidth retained graph.countedSize (selectedSize parameters).total) 8)
    (sourceHeap : Array (Word (wordWidth retained graph.countedSize (selectedSize parameters).total)))
    (original : Layout (parameters.channels + graph.nodeCount) state.heap.size)
    (coordinateBase slot sourceEnd entry exhausted queryEntry skipEntry source count offset : Nat)
    (candidate : Word (wordWidth retained graph.countedSize (selectedSize parameters).total))
    (rest : List (Word (wordWidth retained graph.countedSize (selectedSize parameters).total)))
    (sourceData : SourceConditions parameters state original
      (SharedZeroSource.references graph parameters.buses parameters.bridge.target T F coordinateBase slot oldRoot)
      sourceEnd graph.nodeCount)
    (ready : QueryReady (ambient := parameters.channels + graph.nodeCount) sourceHeap original.tableBase original.inverseBase entry
      (word (wordWidth retained graph.countedSize (selectedSize parameters).total) source ::
       word (wordWidth retained graph.countedSize (selectedSize parameters).total) (count + 1) ::
       word (wordWidth retained graph.countedSize (selectedSize parameters).total) parameters.bridge.target.val :: rest) state)
    (heapBound : state.heap.size ≤ retained) (entryBound : entry + 22 ≤ retained)
    (queryBound : queryEntry + 12 ≤ retained) (countBound : count + 1 ≤ graph.roots.length)
    (sourceValid : source < state.heap.size) (rootValid : source + offset < state.heap.size)
    (slotBefore : slot < original.tableBase) (slotBound : slot < sourceEnd) (headerBefore : 1 < slot)
    (tableBefore : coordinateBase + (parameters.channels + graph.nodeCount) ≤ slot)
    (candidateStored : state.heap[source]? = some candidate)
    (rootStored : state.heap[source + offset]? = some (word (wordWidth retained graph.countedSize (selectedSize parameters).total) root.val))
    (cursorAt : CodeAt program entry (SharedRootTaggedCursor.code
      (wordWidth retained graph.countedSize (selectedSize parameters).total) parameters.channels entry exhausted queryEntry skipEntry))
    (entryAt : CodeAt program queryEntry (SharedRootHealthyEntry.code
      (wordWidth retained graph.countedSize (selectedSize parameters).total) original.tableBase original.inverseBase offset slot))
    (queryAt : SharedRootRead.BlockAt program (queryEntry + 12)
      (SharedQueryReuseCode.code parameters graph T F state.heap original coordinateBase slot (queryEntry + 12) entry oldRoot)) :
    ∃ answer : Bool, ∃ final ticks peak,
      Execution program state final ticks peak ∧ final.halted = answer ∧
      ticks ≤ 5032 * (graph.countedSize + 1) + (if answer then 55 * (selectedSize parameters).total else 0) ∧
      peak ≤ state.liveWords + 200 * (graph.countedSize + 1) + 3 * (selectedSize parameters).total ∧
      final.liveWords ≤ state.liveWords + (if answer then (compile parameters).toState.count else 0) ∧
      (answer = true ↔ ∃ K, Admissible parameters.buses parameters.bridge.target K ∧ ExtendsFixed T F K ∧
        graph.eval (assignmentOfSet K) root = false) ∧
      (answer = true → SharedRootResidentLoop.Witness parameters graph T F coordinateBase slot root final.output) ∧
      (answer = false → QueryReady (ambient := parameters.channels + graph.nodeCount)
        (sourceHeap.set slot (word (wordWidth retained graph.countedSize (selectedSize parameters).total) root.val)
          (by have := ready.sourceFrame.1; omega)) original.tableBase original.inverseBase entry
        (word (wordWidth retained graph.countedSize (selectedSize parameters).total) (source + 1) ::
         word (wordWidth retained graph.countedSize (selectedSize parameters).total) count :: rest) final) ∧
      (answer = false → ∃ finalSize : final.heap.size = state.heap.size,
        SourceConditions parameters final (SharedQuerySourceFrame.layout state final original finalSize)
          (SharedZeroSource.references graph parameters.buses parameters.bridge.target T F coordinateBase slot root)
          sourceEnd graph.nodeCount) ∧
      (answer = true → final.reg 4 = word (wordWidth retained graph.countedSize (selectedSize parameters).total) 1) := by
  have capacity := SharedMachineCapacity.capacity retained graph.countedSize (selectedSize parameters).total
  have size := graph.countedSize_eq
  have tableBound := original.tableBound
  obtain ⟨prepared, prefixTicks, prefixTrace, prefixTime, preparedHeap, preparedOutput, preparedReady, preparedLive⟩ :=
    SharedRootHealthyEntry.tagged_execution program state sourceHeap original.tableBase original.inverseBase parameters.channels
      entry exhausted queryEntry skipEntry source count offset slot parameters.bridge.target candidate
      (word (wordWidth retained graph.countedSize (selectedSize parameters).total) root.val) rest ready
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      sourceValid rootValid slotBefore candidateStored rootStored cursorAt entryAt
  have sameSize : prepared.heap.size = state.heap.size := by simp only [preparedHeap, Array.size_set]
  let preparedLayout := SharedQuerySourceFrame.layout state prepared original sameSize
  have preparedSource := SharedRootQueryRetarget.source_conditions parameters graph guarded T F oldRoot root state prepared
    original coordinateBase slot sourceEnd sourceData slotBound headerBefore tableBefore sameSize preparedHeap
  have sameCode := SharedQueryReuseCode.shared parameters graph T F state.heap prepared.heap original preparedLayout
    coordinateBase slot (queryEntry + 12) entry oldRoot root sameSize.symm
  rw [sameCode] at queryAt
  unfold SharedQueryReuseCode.code at queryAt
  dsimp only at queryAt
  obtain ⟨answer, final, queryTicks, peak, queryTrace, halted, time, memory, meaning, witness, failed, live,
    decision⟩ :=
    SharedZeroResidentConditions.execution parameters graph T F root program prepared _ preparedLayout coordinateBase slot
      sourceEnd (queryEntry + 12) entry _ preparedSource (by rw [sameSize]; exact heapBound) queryBound queryAt preparedReady
  have semantic := meaning.trans (SharedZeroMeaning.constructor_satisfiable_iff (base := coordinateBase) (slot := slot)
    graph guarded parameters.buses parameters.bridge.target T F root prepared.heap preparedLayout)
  refine ⟨answer, final, prefixTicks + queryTicks, max state.liveWords peak, prefixTrace.append queryTrace,
    halted, ?_, ?_, ?_, semantic, (fun success => ⟨prepared.heap, preparedLayout, witness success⟩), failed, ?_, ?_⟩
  · cases answer <;> simp only [Bool.false_eq_true, ↓reduceIte] at time ⊢ <;> omega
  · apply max_le <;> omega
  · omega
  · intro negative
    have afterReady := failed negative
    have preserved := SharedQuerySourceFrame.between_ready _ prepared final original.tableBase original.inverseBase
      (queryEntry + 12) entry _ preparedReady afterReady sourceData.sourceBeforeTable
    have moved := SharedQuerySourceFrame.transport parameters prepared final preparedLayout
      (SharedZeroSource.references graph parameters.buses parameters.bridge.target T F coordinateBase slot root)
      sourceEnd graph.nodeCount preparedSource preserved.1 preserved.2
    exact ⟨preserved.1.trans sameSize, moved⟩
  · intro success
    simpa only [success, ↓reduceIte] using decision

end Controller.Cost.SharedRootHealthyQuery
