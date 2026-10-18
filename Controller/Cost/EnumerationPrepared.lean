module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.EnumerationScan

@[expose] public section

/-! The shared detector's prepared heap also satisfies the returning scan's entry invariant. -/
namespace Controller.Cost.EnumerationPrepared
open Controller.Decoder Controller.Decoder.DAG Controller.Cost.GateProgram
open Controller.Cost.ForestIndexedOperands Controller.Cost.UniformDAGSource
open Controller.Cost.UniformDAGRun Controller.Cost.ForestInputPrefixStored Controller.Cost.ForestInputStored
open Controller.Cost.RawTransferLoops Controller.Cost.ForestZeroDictionary Controller.Cost.ForestZeroAdmissibleCaller
open Controller.Cost.ForestZeroBackendFrame Controller.Cost.ForestZeroEmit
open Controller.Native Controller.Native.SourceController Controller.Cost.SharedZeroResidentConditions
open Controller.Cost.SharedDetectorPrepared

/-- The prepared heap, registers and stack satisfy the shared detector loop's entry invariant
for every output position, with the healthy reference tags on the stack. -/
theorem scan_ready (parameters : Parameters) (graph : DAG parameters.channels) (guarded : graph.Guarded)
    (T F : Finset (Fin parameters.channels)) (retained entry ret : Nat)
    (program : Program (EnumerationScan.Width parameters graph retained) 8)
    (rest : List (Word (EnumerationScan.Width parameters graph retained)))
    (packet : Array (Word (EnumerationScan.Width parameters graph retained)))
    (root : Fin graph.nodeCount) (state : State (EnumerationScan.Width parameters graph retained) 8)
    (packetLength : packet.size = packetSize graph)
    (header : packet[0]? = some (word (EnumerationScan.Width parameters graph retained) parameters.channels))
    (nodes : packet[1]? = some (word (EnumerationScan.Width parameters graph retained) graph.nodeCount))
    (mask : ∀ channel : Fin parameters.channels, packet[maskBase graph + channel.val]? =
      some (word (EnumerationScan.Width parameters graph retained)
        (if assignmentOfSet (extensionBase parameters.buses parameters.bridge.target T) channel then 1 else 0)))
    (heap : state.heap = preparedHeap packet graph ((List.finRange graph.roots.length).map
      (SharedWitnessDecode.tag graph (extensionBase parameters.buses parameters.bridge.target T) F
        (EnumerationScan.Width parameters graph retained))) root.val)
    (sizeEq : state.heap.size = preparedSize graph)
    (stack : state.stack = word (EnumerationScan.Width parameters graph retained) (packetSize graph) ::
      word (EnumerationScan.Width parameters graph retained) graph.roots.length ::
        (SharedHealthyReference.reference graph parameters.bridge.target
          (EnumerationScan.Width parameters graph retained) ++ rest))
    (position : state.pc = word (EnumerationScan.Width parameters graph retained) entry)
    (running : state.halted = false)
    (zero : state.reg 0 = word (EnumerationScan.Width parameters graph retained) 0)
    (table : state.reg 1 = word (EnumerationScan.Width parameters graph retained) (tableBase graph))
    (inverse : state.reg 2 = word (EnumerationScan.Width parameters graph retained) (inverseBase graph))
    (heapRoom : preparedSize graph ≤ retained)
    (codeRoom : entry + (EnumerationLoop.code parameters graph T F state.heap
      (layout graph state.heap.size sizeEq) (coordinateBase graph) (slot graph) graph.roots.length
      entry ret root).length ≤ retained)
    (present : SharedRootRead.BlockAt program entry (EnumerationLoop.code parameters graph T F state.heap
      (layout graph state.heap.size sizeEq) (coordinateBase graph) (slot graph) graph.roots.length
      entry ret root)) :
    EnumerationScan.Ready parameters graph T F retained (coordinateBase graph) (slot graph) (slot graph + 1)
      graph.roots.length (maskBase graph) entry ret program rest state (packetSize graph)
      (List.finRange graph.roots.length) := by
  let W := EnumerationScan.Width parameters graph retained
  let tags := (List.finRange graph.roots.length).map
    (SharedWitnessDecode.tag graph (extensionBase parameters.buses parameters.bridge.target T) F W)
  have tagCount : tags.length = graph.roots.length := by simp [tags]
  have packetPositive : 0 < packet.size := (Array.getElem?_eq_some_iff.mp header).1
  have prefixCell : ∀ index, index < packetSize graph → state.heap[index]? = packet[index]? := by
    intro index below
    rw [heap]
    exact preparedHeap_prefix packet graph tags root.val index (by omega)
  have cells : ∀ index : Nat, state.heap[index]? = (preparedHeap packet graph tags root.val)[index]? := by
    intro index
    rw [heap]
  have size := graph.countedSize_eq
  refine ⟨root, state.heap, layout graph state.heap.size sizeEq, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine {
      sourceReferences := ?_
      sourceBeforeTable := by simp [layout, tableBase]
      sourceBeforeInverse := by simp only [layout, inverseBase, tableBase]; omega
      sourceBound := by rw [sizeEq]; simp only [preparedSize, inverseBase, tableBase]; omega
      sourcePositive := by omega
      sourceChannel := (prefixCell 0 (by rw [← packetLength]; exact packetPositive)).trans header
      sourceNodes := (prefixCell 1 (by simp only [packetSize, maskBase, rootBase]; omega)).trans nodes
      ambientEq := rfl
      adjacent := by simp [layout, inverseBase]
      tablePositive := by simp only [layout, tableBase]; omega
      sourceHeaderRoom := by simp only [slot, coordinateBase, packetSize, maskBase, rootBase]; omega
      sourceDual := SharedQuerySourceFrame.zero_dualHorn graph guarded parameters.buses parameters.bridge.target T F
        root (coordinateBase graph) (slot graph)
      sourceEndpoint := by simp only [layout]; rw [sizeEq]; simp [preparedSize] }
    intro item member
    rw [heap]
    exact source_stored graph parameters.buses parameters.bridge.target T F packet tags root packetLength tagCount
      header item member
  · refine {
      heapSize := rfl
      sourceFrame := ForestZeroBackendFrame.refl state.heap (by
        simp only [layout]; rw [sizeEq, preparedSize_eq, tableBase_eq]; omega)
      zeroTable := ?_
      stack := ?_
      position := position
      running := running
      zeroRegister := zero
      tableRegister := table
      inverseRegister := inverse }
    · intro coordinate
      change state.heap[tableBase graph + coordinate.val]? = _
      rw [cells]
      exact preparedHeap_table packet graph tags root.val packetLength tagCount coordinate.val (by omega)
    · rw [stack, ← SharedDetectorData.healthyTags_reference parameters graph W, List.length_finRange]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [List.length_finRange, slot, coordinateBase]; omega
    · simp only [List.length_finRange, slot, coordinateBase]; omega
    · simp only [slot, coordinateBase, packetSize]; omega
    · intro index below
      rw [cells]
      exact preparedHeap_tags packet graph tags root.val packetLength index below
    · intro index below
      rw [cells]
      have roots := preparedHeap_roots packet graph tags root.val packetLength tagCount
      rw [rootWords_positions] at roots
      exact roots index below
    · intro channel
      rw [prefixCell _ (by simp only [packetSize]; omega)]
      exact mask channel
  · simp only [layout, tableBase]; omega
  · omega
  · simp only [slot, coordinateBase, packetSize, maskBase, rootBase]; omega
  · exact le_rfl
  · rw [sizeEq]; exact heapRoom
  · simp
  · exact codeRoom
  · exact present


end Controller.Cost.EnumerationPrepared
