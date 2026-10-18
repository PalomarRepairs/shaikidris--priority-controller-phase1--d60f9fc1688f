module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedRootQueryRetarget

@[expose] public section

namespace Controller.Cost.SharedRootIteration
open Controller.Cost.GateProgram Controller.Cost.RawTransferLoops
open Controller.Cost.ForestZeroDictionary Controller.Cost.ForestZeroCompile
open Controller.Cost.ForestZeroAdmissibleCaller Controller.Cost.ForestZeroEmit
open Controller.Native Controller.Native.SourceController Controller.Decoder
open Controller.Cost.NativeSourceExecution Controller.Cost.NativeCircuitExecution
open Controller.Cost.SharedZeroResidentConditions Controller.Cost.SharedZeroNativeQuery

@[irreducible] def code (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels)) (heap : Array (Word width))
    (layout : Layout (parameters.channels + graph.nodeCount) heap.size)
    (coordinateBase slot entry exhausted : Nat) (root : Fin graph.nodeCount) : List (Instruction width 8) :=
  (SharedRootCursorEntry.code width exhausted slot layout.tableBase).toList ++
    SharedQueryReuseCode.code parameters graph T F heap layout coordinateBase slot (entry + 15) entry root

theorem code_shared (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels)) (before after : Array (Word width))
    (beforeLayout : Layout (parameters.channels + graph.nodeCount) before.size)
    (afterLayout : Layout (parameters.channels + graph.nodeCount) after.size)
    (coordinateBase slot entry exhausted : Nat) (left right : Fin graph.nodeCount)
    (sameSize : before.size = after.size) (sameTable : beforeLayout.tableBase = afterLayout.tableBase) :
    code parameters graph T F before beforeLayout coordinateBase slot entry exhausted left =
      code parameters graph T F after afterLayout coordinateBase slot entry exhausted right := by
  unfold code
  rw [sameTable, SharedQueryReuseCode.shared parameters graph T F before after beforeLayout afterLayout
    coordinateBase slot (entry + 15) entry left right sameSize]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem execution (parameters : Parameters) (graph : DAG parameters.channels)
    (guarded : graph.Guarded) (T F : Finset (Fin parameters.channels))
    (oldRoot root : Fin graph.nodeCount)
    (program : Program (SharedMachineCapacity.wordWidth retained graph.countedSize (selectedSize parameters).total) 8) (state : State (SharedMachineCapacity.wordWidth retained graph.countedSize (selectedSize parameters).total) 8)
    (sourceHeap : Array (Word (SharedMachineCapacity.wordWidth retained graph.countedSize (selectedSize parameters).total)))
    (original : Layout (parameters.channels + graph.nodeCount) state.heap.size)
    (coordinateBase slot sourceEnd entry exhausted source count : Nat) (rest : List (Word (SharedMachineCapacity.wordWidth retained graph.countedSize (selectedSize parameters).total)))
    (sourceData : SourceConditions parameters state original
      (SharedZeroSource.references graph parameters.buses parameters.bridge.target T F coordinateBase slot oldRoot)
      sourceEnd graph.nodeCount)
    (ready : QueryReady (ambient := parameters.channels + graph.nodeCount) sourceHeap
      original.tableBase original.inverseBase entry
      (word (SharedMachineCapacity.wordWidth retained graph.countedSize (selectedSize parameters).total) source :: word (SharedMachineCapacity.wordWidth retained graph.countedSize (selectedSize parameters).total) (count + 1) :: rest) state)
    (heapBound : state.heap.size ≤ retained) (entryBound : entry + 15 ≤ retained)
    (countBound : count + 1 ≤ graph.roots.length) (sourceValid : source < state.heap.size)
    (slotBefore : slot < original.tableBase) (slotBound : slot < sourceEnd) (headerBefore : 1 < slot)
    (tableBefore : coordinateBase + (parameters.channels + graph.nodeCount) ≤ slot)
    (stored : state.heap[source]? = some (word (SharedMachineCapacity.wordWidth retained graph.countedSize (selectedSize parameters).total) root.val))
    (present : SharedRootRead.BlockAt program entry
      (code parameters graph T F state.heap original coordinateBase slot entry exhausted oldRoot)) :
    ∃ answer : Bool, ∃ final ticks peak,
      Execution program state final ticks peak ∧ final.halted = answer ∧
      ticks ≤ 5015 * (graph.countedSize + 1) + (if answer then 55 * (selectedSize parameters).total else 0) ∧
      peak ≤ state.liveWords + 200 * (graph.countedSize + 1) + 3 * (selectedSize parameters).total ∧
      (answer = true ↔ ∃ K, Admissible parameters.buses parameters.bridge.target K ∧ ExtendsFixed T F K ∧
        graph.eval (assignmentOfSet K) root = false) ∧
      (answer = true → QueryNativeWitness parameters state.heap original (SharedZeroSource.references graph parameters.buses parameters.bridge.target T F coordinateBase slot root) (by omega) final.output) ∧
      (answer = false → QueryReady (ambient := parameters.channels + graph.nodeCount)
        (sourceHeap.set slot (word (SharedMachineCapacity.wordWidth retained graph.countedSize (selectedSize parameters).total) root.val) (by have := ready.sourceFrame.1; omega))
        original.tableBase original.inverseBase entry
        (word (SharedMachineCapacity.wordWidth retained graph.countedSize (selectedSize parameters).total) (source + 1) :: word (SharedMachineCapacity.wordWidth retained graph.countedSize (selectedSize parameters).total) count :: rest) final) ∧
      (answer = false → ∃ finalSize : final.heap.size = state.heap.size,
        SourceConditions parameters final (SharedQuerySourceFrame.layout state final original finalSize)
          (SharedZeroSource.references graph parameters.buses parameters.bridge.target T F coordinateBase slot root) sourceEnd graph.nodeCount) ∧
      final.liveWords ≤ state.liveWords + 1 + (if answer then (compile parameters).toState.count else 0) := by
  have cursorAt : CodeAt program entry
      (SharedRootCursorEntry.code (SharedMachineCapacity.wordWidth retained graph.countedSize (selectedSize parameters).total) exhausted slot original.tableBase) := by
    unfold code at present
    intro phase
    have found := present phase.val (by simp only [List.length_append, Array.length_toList]; have := phase.isLt; omega)
    rw [List.getElem?_append_left (by simpa only [Array.length_toList] using phase.isLt)] at found
    simpa only [Array.getElem?_toList] using found
  have queryAt : SharedRootRead.BlockAt program (entry + 15)
      (SharedQueryReuseCode.code parameters graph T F state.heap original coordinateBase slot (entry + 15) entry oldRoot) := by
    have joined : SharedRootRead.BlockAt program entry
        ((SharedRootCursorEntry.code (SharedMachineCapacity.wordWidth retained graph.countedSize (selectedSize parameters).total) exhausted slot original.tableBase).toList ++
          SharedQueryReuseCode.code parameters graph T F state.heap original coordinateBase slot (entry + 15) entry oldRoot ++ []) := by
      simpa only [code, List.append_nil] using present
    have found := SharedNativeSuccessCode.segment program entry _ _ _ joined
    simpa only [Array.length_toList, SharedRootCursorEntry.code_size] using found
  obtain ⟨prepared, prepareTrace, preparedHeap, preparedOutput, preparedReady⟩ :=
    SharedRootCursorEntry.bounded_successor_execution parameters graph program state sourceHeap
      original.tableBase original.inverseBase entry exhausted source count slot (word (SharedMachineCapacity.wordWidth retained graph.countedSize (selectedSize parameters).total) root.val) rest
      ready heapBound (by omega) countBound sourceValid slotBefore stored cursorAt
  have sameSize : prepared.heap.size = state.heap.size := by rw [preparedHeap]; simp
  let preparedLayout := SharedQuerySourceFrame.layout state prepared original sameSize
  have preparedSource := SharedRootQueryRetarget.source_conditions parameters graph guarded T F oldRoot root
    state prepared original coordinateBase slot sourceEnd sourceData slotBound headerBefore tableBefore sameSize preparedHeap
  have sharedCode := SharedQueryReuseCode.shared parameters graph T F state.heap prepared.heap original preparedLayout
    coordinateBase slot (entry + 15) entry oldRoot root sameSize.symm
  rw [sharedCode] at queryAt
  unfold SharedQueryReuseCode.code at queryAt
  dsimp only at queryAt
  obtain ⟨answer, final, queryTicks, peak, queryTrace, halted, timeBound, spaceBound, meaning, witness, nextReady, liveBound, -⟩ :=
    SharedZeroResidentConditions.execution parameters graph T F root program prepared
      (sourceHeap.set slot (word (SharedMachineCapacity.wordWidth retained graph.countedSize (selectedSize parameters).total) root.val) (by have := ready.sourceFrame.1; omega))
      preparedLayout coordinateBase slot sourceEnd (entry + 15) entry
      (word (SharedMachineCapacity.wordWidth retained graph.countedSize (selectedSize parameters).total) (source + 1) :: word (SharedMachineCapacity.wordWidth retained graph.countedSize (selectedSize parameters).total) count :: rest)
      preparedSource (by rw [sameSize]; exact heapBound) entryBound queryAt preparedReady
  have preparedLive : prepared.liveWords = state.liveWords := by
    simp only [State.liveWords, preparedHeap, preparedOutput, Array.size_set, preparedReady.stack,
      ready.stack, List.length_cons]
  have peakBound : state.liveWords ≤ peak := by
    rw [← preparedLive]
    exact queryTrace.initial_storage_le
  have semantic := meaning.trans (SharedZeroMeaning.constructor_satisfiable_iff (base := coordinateBase) (slot := slot)
    graph guarded parameters.buses parameters.bridge.target T F root state.heap original)
  refine ⟨answer, final, 15 + queryTicks, peak, ?_, halted, ?_, ?_, semantic, witness, nextReady, ?_, ?_⟩
  · simpa only [Nat.max_eq_right peakBound] using prepareTrace.append queryTrace
  · cases answer <;> simp only [Bool.false_eq_true, ite_false, ite_true] at timeBound ⊢ <;> omega
  · rw [preparedLive] at spaceBound
    exact spaceBound

  · intro failed
    have afterReady := nextReady failed
    have preserved := SharedQuerySourceFrame.between_ready
      (sourceHeap.set slot (word (SharedMachineCapacity.wordWidth retained graph.countedSize (selectedSize parameters).total) root.val)
        (by have := ready.sourceFrame.1; omega)) prepared final
      original.tableBase original.inverseBase (entry + 15) entry
      (word (SharedMachineCapacity.wordWidth retained graph.countedSize (selectedSize parameters).total) (source + 1) ::
        word (SharedMachineCapacity.wordWidth retained graph.countedSize (selectedSize parameters).total) count :: rest)
      preparedReady afterReady sourceData.sourceBeforeTable
    have moved := SharedQuerySourceFrame.transport parameters prepared final preparedLayout (SharedZeroSource.references graph parameters.buses parameters.bridge.target T F coordinateBase slot root)
      sourceEnd graph.nodeCount preparedSource preserved.1 preserved.2
    exact ⟨preserved.1.trans sameSize, moved⟩
  · rw [preparedLive] at liveBound
    exact liveBound

end Controller.Cost.SharedRootIteration
