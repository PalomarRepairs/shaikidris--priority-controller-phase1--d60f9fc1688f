module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.EnumerationResident
public import Controller.Cost.SharedRootHealthyQuery

@[expose] public section

/-! One output's decision-only zero query in the shared detector heap: the healthy-entry prefix
retargets the shared query slot, then the quiet resident query decides and returns. -/
namespace Controller.Cost.EnumerationRootQuery
open Controller.Cost.GateProgram Controller.Cost.RawTransferLoops Controller.Cost.ForestZeroCompile Controller.Cost.ForestZeroTouch
open Controller.CNF
open Controller.Cost.ForestZeroDictionary Controller.Cost.ForestZeroAdmissibleCaller Controller.Cost.ForestZeroEmit
open Controller.Native Controller.Native.SourceController Controller.Decoder
open Controller.Cost.NativeSourceExecution Controller.Cost.SharedZeroResidentConditions
open Controller.Cost.SharedMachineCapacity

/-- The quiet resident query for the root currently named by the shared slot. -/
def code (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels)) (heap : Array (Word width))
    (layout : Layout (parameters.channels + graph.nodeCount) heap.size)
    (coordinateBase slot entry : Nat) (root : Fin graph.nodeCount) : List (Instruction width 8) :=
  let references := SharedZeroSource.references graph parameters.buses parameters.bridge.target T F coordinateBase slot root
  EnumerationResident.code width entry heap.size
    (constructorDictionary heap layout (empty _) references).coordinates.size
    (constructorHeap heap layout (empty _) references parameters.channels).size references

def returnEntry (width : Nat) (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels)) (keep coordinateBase slot entry : Nat) (root : Fin graph.nodeCount) : Nat :=
  SharedQuerySourceCode.solverEntry width entry keep
    (SharedZeroSource.references graph parameters.buses parameters.bridge.target T F coordinateBase slot root) + 430

theorem returnEntry_eq (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels)) (heap : Array (Word width))
    (layout : Layout (parameters.channels + graph.nodeCount) heap.size)
    (coordinateBase slot entry : Nat) (root : Fin graph.nodeCount) :
    entry + (code parameters graph T F heap layout coordinateBase slot entry root).length =
      returnEntry width parameters graph T F heap.size coordinateBase slot entry root := by
  unfold code returnEntry
  exact EnumerationResident.code_end width entry heap.size _ _ _

theorem root_irrel (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels)) (heap : Array (Word width))
    (layout : Layout (parameters.channels + graph.nodeCount) heap.size)
    (coordinateBase slot entry : Nat) (left right : Fin graph.nodeCount) :
    code parameters graph T F heap layout coordinateBase slot entry left =
      code parameters graph T F heap layout coordinateBase slot entry right := by
  unfold code EnumerationResident.code
  dsimp only
  rw [SharedZeroSource.dictionary_size, SharedZeroSource.dictionary_size,
    SharedZeroSource.constructor_heap_size_root_irrel graph parameters.buses parameters.bridge.target T F left right heap layout,
    SharedQuerySourceCode.root_code_irrel graph parameters.buses parameters.bridge.target T F coordinateBase slot entry heap.size left right,
    SharedQuerySourceCode.root_entry_irrel graph parameters.buses parameters.bridge.target T F coordinateBase slot entry heap.size left right]

theorem heap_irrel (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels)) (before after : Array (Word width))
    (beforeLayout : Layout (parameters.channels + graph.nodeCount) before.size)
    (afterLayout : Layout (parameters.channels + graph.nodeCount) after.size)
    (coordinateBase slot entry : Nat) (root : Fin graph.nodeCount) (size : before.size = after.size) :
    code parameters graph T F before beforeLayout coordinateBase slot entry root =
      code parameters graph T F after afterLayout coordinateBase slot entry root := by
  unfold code
  dsimp only
  rw [SharedQueryReuseCode.constructor_heap_size_irrel before after beforeLayout afterLayout _ _ size]
  simp only [SharedZeroSource.dictionary_size, size]

theorem shared (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels)) (before after : Array (Word width))
    (beforeLayout : Layout (parameters.channels + graph.nodeCount) before.size)
    (afterLayout : Layout (parameters.channels + graph.nodeCount) after.size)
    (coordinateBase slot entry : Nat) (left right : Fin graph.nodeCount) (size : before.size = after.size) :
    code parameters graph T F before beforeLayout coordinateBase slot entry left =
      code parameters graph T F after afterLayout coordinateBase slot entry right :=
  (root_irrel parameters graph T F before beforeLayout coordinateBase slot entry left right).trans
    (heap_irrel parameters graph T F before after beforeLayout afterLayout coordinateBase slot entry right size)

theorem solverEntry_bound (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels)) (root : Fin graph.nodeCount) (width entry keep : Nat) :
    SharedQuerySourceCode.solverEntry width entry keep
      (SharedZeroSource.references graph parameters.buses parameters.bridge.target T F coordinateBase slot root) ≤
      entry + 410 * (graph.countedSize + 1) + 15 := by
  have sourceBound := SharedZeroSource.constructor_code_bound (width := width) (entry := entry + 15)
    (protectedEnd := keep) (recordHeader := keep) (endHeader := keep + 4)
    (returnPC := SharedQuerySourceCode.solverEntry width entry keep
      (SharedZeroSource.references graph parameters.buses parameters.bridge.target T F coordinateBase slot root))
    (base := coordinateBase) (slot := slot) graph parameters.buses parameters.bridge.target T F root
  have constructorEnd : entry + 15 +
      (constructorCode width (entry + 15) keep keep (keep + 4)
        (SharedQuerySourceCode.solverEntry width entry keep
          (SharedZeroSource.references graph parameters.buses parameters.bridge.target T F coordinateBase slot root))
        (SharedZeroSource.references graph parameters.buses parameters.bridge.target T F coordinateBase slot root)).length =
      SharedQuerySourceCode.solverEntry width entry keep
        (SharedZeroSource.references graph parameters.buses parameters.bridge.target T F coordinateBase slot root) := by
    simp only [constructorCode, List.length_append, ForestZeroAdmissibleCaller.code_length,
      SharedQuerySourceCode.solverEntry]
    omega
  omega

theorem code_length_bound (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels)) (heap : Array (Word width))
    (layout : Layout (parameters.channels + graph.nodeCount) heap.size)
    (coordinateBase slot entry : Nat) (root : Fin graph.nodeCount) :
    (code parameters graph T F heap layout coordinateBase slot entry root).length ≤
      410 * (graph.countedSize + 1) + 445 := by
  have length := returnEntry_eq parameters graph T F heap layout coordinateBase slot entry root
  have bound := solverEntry_bound (coordinateBase := coordinateBase) (slot := slot) parameters graph T F root
    width entry heap.size
  unfold returnEntry at length
  omega

set_option maxRecDepth 4096 in
theorem conditions (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels)) (root : Fin graph.nodeCount)
    (program : Program (wordWidth retained graph.countedSize (selectedSize parameters).total) 8)
    (initial : State (wordWidth retained graph.countedSize (selectedSize parameters).total) 8)
    (sharedLayout : Layout (parameters.channels + graph.nodeCount) initial.heap.size)
    (coordinateBase slot sourceEnd sourceEntry : Nat)
    (rest : List (Word (wordWidth retained graph.countedSize (selectedSize parameters).total)))
    (source : SourceConditions parameters initial sharedLayout
      (SharedZeroSource.references graph parameters.buses parameters.bridge.target T F coordinateBase slot root)
      sourceEnd graph.nodeCount)
    (heapBound : initial.heap.size ≤ retained) (entryBound : sourceEntry ≤ retained) :
    EnumerationResident.Conditions parameters.channels program initial sharedLayout
      (SharedZeroSource.references graph parameters.buses parameters.bridge.target T F coordinateBase slot root)
      sourceEnd graph.nodeCount sourceEntry rest (by omega) := by
  have entryRoom := solverEntry_bound (coordinateBase := coordinateBase) (slot := slot) parameters graph T F root
    (wordWidth retained graph.countedSize (selectedSize parameters).total) sourceEntry initial.heap.size
  have room := capacity retained graph.countedSize (selectedSize parameters).total
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
    residentCapacity := by omega }

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
/-- One healthy-true output: retarget the shared query slot and decide its zero system without
lifting or emitting. Both answers return to the end of the query block with the shared heap,
the cursor words and the source conditions restored. -/
theorem healthy_execution (parameters : Parameters) (graph : DAG parameters.channels) (guarded : graph.Guarded)
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
      (word (wordWidth retained graph.countedSize (selectedSize parameters).total) source :: word (wordWidth retained graph.countedSize (selectedSize parameters).total) (count + 1) :: word (wordWidth retained graph.countedSize (selectedSize parameters).total) parameters.bridge.target.val :: rest) state)
    (heapBound : state.heap.size ≤ retained) (entryBound : entry + 22 ≤ retained)
    (queryBound : queryEntry + 12 ≤ retained) (countBound : count + 1 ≤ graph.roots.length)
    (sourceValid : source < state.heap.size) (rootValid : source + offset < state.heap.size)
    (slotBefore : slot < original.tableBase) (slotBound : slot < sourceEnd) (headerBefore : 1 < slot)
    (tableBefore : coordinateBase + (parameters.channels + graph.nodeCount) ≤ slot)
    (candidateStored : state.heap[source]? = some candidate)
    (rootStored : state.heap[source + offset]? = some (word (wordWidth retained graph.countedSize (selectedSize parameters).total) root.val))
    (cursorAt : CodeAt program entry (SharedRootTaggedCursor.code (wordWidth retained graph.countedSize (selectedSize parameters).total) parameters.channels entry exhausted queryEntry skipEntry))
    (entryAt : CodeAt program queryEntry (SharedRootHealthyEntry.code (wordWidth retained graph.countedSize (selectedSize parameters).total) original.tableBase original.inverseBase offset slot))
    (queryAt : SharedRootRead.BlockAt program (queryEntry + 12)
      (code parameters graph T F state.heap original coordinateBase slot (queryEntry + 12) oldRoot)) :
    ∃ answer : Bool, ∃ final ticks peak,
      Execution program state final ticks peak ∧ final.halted = false ∧
      final.pc = word (wordWidth retained graph.countedSize (selectedSize parameters).total) (returnEntry (wordWidth retained graph.countedSize (selectedSize parameters).total) parameters graph T F state.heap.size coordinateBase slot (queryEntry + 12) root) ∧
      final.reg 4 = word (wordWidth retained graph.countedSize (selectedSize parameters).total) (if answer then 1 else 0) ∧
      ticks ≤ 4300 * (graph.countedSize + 1) + 500 ∧
      peak ≤ state.liveWords + 200 * (graph.countedSize + 1) ∧
      final.output = state.output ∧ final.liveWords + 1 = state.liveWords ∧
      (answer = true ↔ ∃ K, Admissible parameters.buses parameters.bridge.target K ∧ ExtendsFixed T F K ∧
        graph.eval (assignmentOfSet K) root = false) ∧
      QueryReady (ambient := parameters.channels + graph.nodeCount)
        (sourceHeap.set slot (word (wordWidth retained graph.countedSize (selectedSize parameters).total) root.val) (by have := ready.sourceFrame.1; omega))
        original.tableBase original.inverseBase
        (returnEntry (wordWidth retained graph.countedSize (selectedSize parameters).total) parameters graph T F state.heap.size coordinateBase slot (queryEntry + 12) root)
        (word (wordWidth retained graph.countedSize (selectedSize parameters).total) (source + 1) :: word (wordWidth retained graph.countedSize (selectedSize parameters).total) count :: rest) final ∧
      ∃ finalSize : final.heap.size = state.heap.size,
        SourceConditions parameters final (SharedQuerySourceFrame.layout state final original finalSize)
          (SharedZeroSource.references graph parameters.buses parameters.bridge.target T F coordinateBase slot root)
          sourceEnd graph.nodeCount := by
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
  have sameCode := shared parameters graph T F state.heap prepared.heap original preparedLayout
    coordinateBase slot (queryEntry + 12) oldRoot root sameSize.symm
  rw [sameCode] at queryAt
  have conditionsData := conditions parameters graph T F root program prepared preparedLayout coordinateBase slot sourceEnd
    (queryEntry + 12) (word (wordWidth retained graph.countedSize (selectedSize parameters).total) (source + 1) :: word (wordWidth retained graph.countedSize (selectedSize parameters).total) count :: rest) preparedSource
    (by rw [sameSize]; exact heapBound) (by omega)
  obtain ⟨answer, final, queryTicks, peak, queryTrace, halted, decision, time, memory, output, meaning, finalReady⟩ :=
    EnumerationResident.execution parameters.channels program prepared _ preparedLayout
      (SharedZeroSource.references graph parameters.buses parameters.bridge.target T F coordinateBase slot root)
      sourceEnd graph.nodeCount (queryEntry + 12) _ (by omega) conditionsData queryAt preparedReady
  have semantic := meaning.trans (SharedZeroMeaning.constructor_satisfiable_iff (base := coordinateBase) (slot := slot)
    graph guarded parameters.buses parameters.bridge.target T F root prepared.heap preparedLayout)
  have occurrences := SharedZeroSource.occurrence_bound (base := coordinateBase) (slot := slot)
    graph parameters.buses parameters.bridge.target T F root
  have pcEq : SharedQuerySourceCode.solverEntry (wordWidth retained graph.countedSize (selectedSize parameters).total) (queryEntry + 12) prepared.heap.size
      (SharedZeroSource.references graph parameters.buses parameters.bridge.target T F coordinateBase slot root) + 430 =
      returnEntry (wordWidth retained graph.countedSize (selectedSize parameters).total) parameters graph T F state.heap.size coordinateBase slot (queryEntry + 12) root := by
    rw [sameSize]; rfl
  rw [pcEq] at finalReady
  have finalLive : final.liveWords = prepared.liveWords := by
    unfold State.liveWords
    rw [finalReady.heapSize, preparedReady.heapSize.symm, finalReady.stack, preparedReady.stack, output]
  have preserved := SharedQuerySourceFrame.between_ready _ prepared final original.tableBase original.inverseBase
    (queryEntry + 12) _ _ preparedReady finalReady preparedSource.sourceBeforeTable
  have moved := SharedQuerySourceFrame.transport parameters prepared final preparedLayout
    (SharedZeroSource.references graph parameters.buses parameters.bridge.target T F coordinateBase slot root)
    sourceEnd graph.nodeCount preparedSource preserved.1 preserved.2
  refine ⟨answer, final, prefixTicks + queryTicks, max state.liveWords peak, prefixTrace.append queryTrace,
    halted, finalReady.position, decision, by omega, ?_, output.trans preparedOutput, by omega, semantic, finalReady,
    preserved.1.trans sameSize, moved⟩
  apply max_le
  · omega
  · omega

end Controller.Cost.EnumerationRootQuery
