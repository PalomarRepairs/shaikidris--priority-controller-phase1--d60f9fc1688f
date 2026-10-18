module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.EnumerationFixedRootQuery
public import Controller.Cost.EnumerationRootQuery

@[expose] public section

/-! Healthy-output retargeting followed by the fixed-mask resident query. -/
namespace Controller.Cost.EnumerationUniformRootQuery
open Controller.Cost.GateProgram Controller.Cost.RawTransferLoops
open Controller.Cost.ForestZeroCompile Controller.Cost.ForestZeroDictionary Controller.Cost.ForestZeroAdmissibleCaller
open Controller.CNF Controller.Native Controller.Native.SourceController Controller.Decoder
open Controller.Cost.NativeSourceExecution Controller.Cost.SharedZeroResidentConditions
open Controller.Cost.SharedMachineCapacity Controller.Cost.EnumerationFixedRootQuery
variable {trueBase falseBase : Nat}

def code (parameters : Parameters) (graph : DAG parameters.channels)
    (_T _F : Finset (Fin parameters.channels)) (heap : Array (Word width))
    (_layout : Layout (parameters.channels + graph.nodeCount) heap.size)
    (coordinateBase slot entry : Nat) (root : Fin graph.nodeCount) : List (Instruction width 8) :=
  EnumerationFixedRootQuery.code parameters graph width entry heap.size coordinateBase slot trueBase falseBase root

def returnEntry (width : Nat) (parameters : Parameters) (graph : DAG parameters.channels)
    (_T _F : Finset (Fin parameters.channels)) (keep coordinateBase slot entry : Nat) (root : Fin graph.nodeCount) : Nat :=
  EnumerationFixedRootQuery.returnEntry parameters graph width entry keep coordinateBase slot trueBase falseBase root

theorem returnEntry_eq (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels)) (heap : Array (Word width))
    (layout : Layout (parameters.channels + graph.nodeCount) heap.size)
    (coordinateBase slot entry : Nat) (root : Fin graph.nodeCount) :
    entry + (code (trueBase := trueBase) (falseBase := falseBase) parameters graph T F heap layout coordinateBase slot entry root).length =
      returnEntry (trueBase := trueBase) (falseBase := falseBase) width parameters graph T F heap.size coordinateBase slot entry root :=
  EnumerationFixedRootQuery.code_end parameters graph root

theorem shared (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels)) (before after : Array (Word width))
    (beforeLayout : Layout (parameters.channels + graph.nodeCount) before.size)
    (afterLayout : Layout (parameters.channels + graph.nodeCount) after.size)
    (coordinateBase slot entry : Nat) (left right : Fin graph.nodeCount) (size : before.size = after.size) :
    code (trueBase := trueBase) (falseBase := falseBase) parameters graph T F before beforeLayout coordinateBase slot entry left =
    code (trueBase := trueBase) (falseBase := falseBase) parameters graph T F after afterLayout coordinateBase slot entry right := by
  unfold code
  rw [size, EnumerationFixedRootQuery.root_irrel parameters graph left right]

theorem code_length_bound (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels)) (heap : Array (Word width))
    (layout : Layout (parameters.channels + graph.nodeCount) heap.size)
    (coordinateBase slot entry : Nat) (root : Fin graph.nodeCount) :
    (code (trueBase := trueBase) (falseBase := falseBase) parameters graph T F heap layout coordinateBase slot entry root).length ≤
      403 * (graph.countedSize + 1) + 547 :=
  EnumerationFixedCapacity.code_bound parameters graph root width entry heap.size

theorem masks_retarget (parameters : Parameters) (before after : Array (Word width))
    (coordinateBase slot sourceEnd : Nat) (T F : Finset (Fin parameters.channels)) (value : Word width)
    (valid : slot < before.size) (heap : after = before.set slot value valid)
    (masks : MaskCells parameters before coordinateBase trueBase falseBase sourceEnd T F)
    (coordinateBefore : coordinateBase + parameters.channels ≤ slot)
    (trueBefore : trueBase + parameters.channels ≤ slot) (falseBefore : falseBase + parameters.channels ≤ slot) :
    MaskCells parameters after coordinateBase trueBase falseBase sourceEnd T F := by
  refine ⟨masks.coordinateBound, masks.trueBound, masks.falseBound, ?_, ?_, ?_⟩
  all_goals intro channel
  all_goals have channelBound := channel.isLt
  all_goals rw [heap, Array.getElem?_set_ne valid (by omega)]
  · exact masks.coordinates channel
  · exact masks.trueCells channel
  · exact masks.falseCells channel

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
      (SharedZeroSource.references graph parameters.buses parameters.bridge.target ∅ ∅ coordinateBase slot oldRoot)
      sourceEnd graph.nodeCount)
    (consistent : FixedConsistent (extensionBase parameters.buses parameters.bridge.target T) F)
    (masks : MaskCells parameters state.heap coordinateBase trueBase falseBase sourceEnd
      (extensionBase parameters.buses parameters.bridge.target T) F)
    (trueBefore : trueBase + parameters.channels ≤ slot) (falseBefore : falseBase + parameters.channels ≤ slot)
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
      (code (trueBase := trueBase) (falseBase := falseBase) parameters graph T F state.heap original coordinateBase slot (queryEntry + 12) oldRoot)) :
    ∃ answer : Bool, ∃ final ticks peak,
      Execution program state final ticks peak ∧ final.halted = false ∧
      final.pc = word (wordWidth retained graph.countedSize (selectedSize parameters).total) (returnEntry (trueBase := trueBase) (falseBase := falseBase) (wordWidth retained graph.countedSize (selectedSize parameters).total) parameters graph T F state.heap.size coordinateBase slot (queryEntry + 12) root) ∧
      final.reg 4 = word (wordWidth retained graph.countedSize (selectedSize parameters).total) (if answer then 1 else 0) ∧
      ticks ≤ 6000 * (graph.countedSize + 1) + 700 ∧
      peak ≤ state.liveWords + 200 * (graph.countedSize + 1) ∧
      final.output = state.output ∧ final.liveWords + 1 = state.liveWords ∧
      (answer = true ↔ ∃ K, Admissible parameters.buses parameters.bridge.target K ∧ ExtendsFixed T F K ∧
        graph.eval (assignmentOfSet K) root = false) ∧
      QueryReady (ambient := parameters.channels + graph.nodeCount)
        (sourceHeap.set slot (word (wordWidth retained graph.countedSize (selectedSize parameters).total) root.val) (by have := ready.sourceFrame.1; omega))
        original.tableBase original.inverseBase
        (returnEntry (trueBase := trueBase) (falseBase := falseBase) (wordWidth retained graph.countedSize (selectedSize parameters).total) parameters graph T F state.heap.size coordinateBase slot (queryEntry + 12) root)
        (word (wordWidth retained graph.countedSize (selectedSize parameters).total) (source + 1) :: word (wordWidth retained graph.countedSize (selectedSize parameters).total) count :: rest) final ∧
      ∃ finalSize : final.heap.size = state.heap.size,
        SourceConditions parameters final (SharedQuerySourceFrame.layout state final original finalSize)
          (SharedZeroSource.references graph parameters.buses parameters.bridge.target ∅ ∅ coordinateBase slot root)
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
  have preparedSource := SharedRootQueryRetarget.source_conditions parameters graph guarded ∅ ∅ oldRoot root state prepared
    original coordinateBase slot sourceEnd sourceData slotBound headerBefore tableBefore sameSize preparedHeap
  have sameCode := shared (trueBase := trueBase) (falseBase := falseBase) parameters graph T F state.heap prepared.heap original preparedLayout
    coordinateBase slot (queryEntry + 12) oldRoot root sameSize.symm
  rw [sameCode] at queryAt
  have preparedMasks := masks_retarget (trueBase := trueBase) (falseBase := falseBase) parameters state.heap prepared.heap
    coordinateBase slot sourceEnd (extensionBase parameters.buses parameters.bridge.target T) F _ _ preparedHeap masks
    (by omega) trueBefore falseBefore
  obtain ⟨answer, final, queryTicks, peak, queryTrace, halted, decision, time, memory, output, meaning, finalReady⟩ :=
    EnumerationFixedRootQuery.execution parameters graph guarded
      (extensionBase parameters.buses parameters.bridge.target T) F consistent root program prepared _ preparedLayout
      coordinateBase slot trueBase falseBase sourceEnd (queryEntry + 12)
      (word (wordWidth retained graph.countedSize (selectedSize parameters).total) (source + 1) :: word (wordWidth retained graph.countedSize (selectedSize parameters).total) count :: rest)
      preparedSource preparedMasks (by rw [sameSize]; exact heapBound) (by omega) queryAt preparedReady
  have semantic : (answer = true ↔ ∃ K, Admissible parameters.buses parameters.bridge.target K ∧ ExtendsFixed T F K ∧
      graph.eval (assignmentOfSet K) root = false) := by
    rw [meaning]
    constructor
    · rintro ⟨K, eligible, fixed, zero⟩
      exact ⟨K, eligible, (extensionBase_extends parameters.buses parameters.bridge.target T F K fixed).1, zero⟩
    · rintro ⟨K, eligible, fixed, zero⟩
      exact ⟨K, eligible, admissible_extensionBase parameters.buses parameters.bridge.target T F K eligible fixed, zero⟩
  have occurrences := SharedZeroSource.occurrence_bound (base := coordinateBase) (slot := slot)
    graph parameters.buses parameters.bridge.target T F root
  have pcEq : EnumerationFixedRootQuery.returnEntry parameters graph (wordWidth retained graph.countedSize (selectedSize parameters).total)
      (queryEntry + 12) prepared.heap.size coordinateBase slot trueBase falseBase root =
      returnEntry (trueBase := trueBase) (falseBase := falseBase) (wordWidth retained graph.countedSize (selectedSize parameters).total) parameters graph T F state.heap.size coordinateBase slot (queryEntry + 12) root := by
    rw [sameSize]; rfl
  rw [pcEq] at finalReady
  have finalLive : final.liveWords = prepared.liveWords := by
    unfold State.liveWords
    rw [finalReady.heapSize, preparedReady.heapSize.symm, finalReady.stack, preparedReady.stack, output]
  have preserved := SharedQuerySourceFrame.between_ready _ prepared final original.tableBase original.inverseBase
    (queryEntry + 12) _ _ preparedReady finalReady preparedSource.sourceBeforeTable
  have moved := SharedQuerySourceFrame.transport parameters prepared final preparedLayout
    (SharedZeroSource.references graph parameters.buses parameters.bridge.target ∅ ∅ coordinateBase slot root)
    sourceEnd graph.nodeCount preparedSource preserved.1 preserved.2
  refine ⟨answer, final, prefixTicks + queryTicks, max state.liveWords peak, prefixTrace.append queryTrace,
    halted, finalReady.position, decision, by omega, ?_, output.trans preparedOutput, by omega, semantic, finalReady,
    preserved.1.trans sameSize, moved⟩
  apply max_le
  · omega
  · omega

end Controller.Cost.EnumerationUniformRootQuery
