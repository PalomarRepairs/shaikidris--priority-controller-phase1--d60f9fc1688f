module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.EnumerationUniformScan
public import Controller.Cost.EnumerationMasks

@[expose] public section

/-! The oracle source heap includes retained runtime masks before the coordinate
setup and reusable zero-query tables. Packet and output-directory cells retain
their original addresses. -/
namespace Controller.Cost.EnumerationUniformPrepared
open Controller.Decoder Controller.Decoder.DAG Controller.Cost.GateProgram
open Controller.Cost.ForestIndexedOperands Controller.Cost.UniformDAGSource
open Controller.Cost.UniformDAGRun Controller.Cost.ForestInputPrefixStored Controller.Cost.ForestInputStored
open Controller.Cost.RawTransferLoops Controller.Cost.ForestZeroDictionary Controller.Cost.ForestZeroAdmissibleCaller
open Controller.Cost.ForestZeroBackendFrame Controller.Cost.ForestZeroEmit
open Controller.Native Controller.Native.SourceController Controller.Cost.SharedZeroResidentConditions
open Controller.Cost.SharedDetectorPrepared

section Layout
variable {n : Nat}
variable {maskB maskF : Finset (Fin n)}

def trueBase (graph : DAG n) : Nat := SharedDetectorPrepared.coordinateBase graph

def falseBase (graph : DAG n) : Nat := trueBase graph + n

def coordinateBase (graph : DAG n) : Nat := packetSize graph + 2 * graph.roots.length + 2 * n

def slot (graph : DAG n) : Nat := coordinateBase graph + (n + graph.nodeCount)

def tableBase (graph : DAG n) : Nat := slot graph + 1

def inverseBase (graph : DAG n) : Nat := tableBase graph + (n + graph.nodeCount)

def preparedSize (graph : DAG n) : Nat := inverseBase graph + (n + graph.nodeCount)

theorem preparedSize_eq (graph : DAG n) :
    preparedSize graph = coordinateBase graph + 3 * (n + graph.nodeCount) + 1 := by
  simp only [preparedSize, inverseBase, tableBase, slot]; omega

theorem tableBase_eq (graph : DAG n) : tableBase graph = coordinateBase graph + (n + graph.nodeCount) + 1 := rfl

theorem coordinateBase_eq (graph : DAG n) :
    coordinateBase graph = 5 + 6 * graph.nodeCount + graph.childIncidences + graph.guardIncidences +
      3 * graph.roots.length + 3 * n := by
  simp only [coordinateBase, packetSize, maskBase, rootBase]; omega

theorem preparedSize_le (graph : DAG n) : preparedSize graph ≤ 12 * (graph.countedSize + 1) := by
  have size := graph.countedSize_eq
  simp only [preparedSize, inverseBase, tableBase, slot, coordinateBase, packetSize, maskBase, rootBase]
  omega

/-- Words appended once: coordinate identifiers, the query-root slot and both zeroed tables. -/
def setupWords (width : Nat) (graph : DAG n) (root : Nat) : List (Word width) :=
  SharedCoordinateTable.words width (n + graph.nodeCount) ++
    word width root :: List.replicate (2 * (n + graph.nodeCount)) (word width 0)

@[simp] theorem setupWords_length (width : Nat) (graph : DAG n) (root : Nat) :
    (setupWords width graph root).length = 3 * (n + graph.nodeCount) + 1 := by
  simp [setupWords]; omega

def rootWords (width : Nat) (graph : DAG n) : List (Word width) :=
  graph.roots.map (fun root => word width root.val)

@[simp] theorem rootWords_length (width : Nat) (graph : DAG n) :
    (rootWords width graph).length = graph.roots.length := by simp [rootWords]

theorem rootWords_positions (width : Nat) (graph : DAG n) :
    rootWords width graph = (List.finRange graph.roots.length).map (fun index => word width graph.roots[index.val].val) := by
  apply List.ext_getElem <;> simp [rootWords]

theorem tags_positions (graph : DAG n) (B F : Finset (Fin n)) (width : Nat) :
    SharedHeadLoop.witnessFold graph (assignmentOfSet B) 0 ((List.finRange n).map (assignmentOfSet F))
        (SharedBaselineInitialize.witnesses graph (assignmentOfSet B) width) =
      (List.finRange graph.roots.length).map (SharedWitnessDecode.tag graph B F width) := by
  apply List.ext_getElem
  · simp only [List.length_map, List.length_finRange]
    exact SharedWitnessMeaning.fold_length graph _ 0 _ _ (by simp)
  · intro index left right
    simp [SharedWitnessDecode.tag, SharedWitnessDecode.rootWord]

/-- The complete prepared heap, from the healthy packet carrying the baseline mask. -/
def preparedHeap (packet : Array (Word width)) (graph : DAG n) (tags : List (Word width)) (root : Nat) :
    Array (Word width) :=
  (((packet ++ tags.toArray) ++ (rootWords width graph).toArray) ++
    (EnumerationMasks.masksOf width maskB maskF).toArray) ++ (setupWords width graph root).toArray

theorem preparedHeap_size (packet : Array (Word width)) (graph : DAG n) (tags : List (Word width)) (root : Nat)
    (packetLength : packet.size = packetSize graph) (tagCount : tags.length = graph.roots.length) :
    (preparedHeap (maskB := maskB) (maskF := maskF) packet graph tags root).size = preparedSize graph := by
  simp only [preparedHeap, Array.size_append, List.size_toArray, rootWords_length, EnumerationMasks.masksOf_length, setupWords_length,
    packetLength, tagCount, preparedSize, inverseBase, tableBase, slot, coordinateBase]
  omega

theorem preparedHeap_prefix (packet : Array (Word width)) (graph : DAG n) (tags : List (Word width)) (root : Nat)
    (index : Nat) (below : index < packet.size) :
    (preparedHeap (maskB := maskB) (maskF := maskF) packet graph tags root)[index]? = packet[index]? := by
  unfold preparedHeap
  rw [Array.getElem?_append_left (by simp only [Array.size_append, List.size_toArray]; omega),
      Array.getElem?_append_left (by simp only [Array.size_append, List.size_toArray]; omega),
    Array.getElem?_append_left (by simp only [Array.size_append, List.size_toArray]; omega),
    Array.getElem?_append_left below]

theorem preparedHeap_setup (packet : Array (Word width)) (graph : DAG n) (tags : List (Word width)) (root : Nat)
    (packetLength : packet.size = packetSize graph) (tagCount : tags.length = graph.roots.length)
    (index : Nat) (_below : index < 3 * (n + graph.nodeCount) + 1) :
    (preparedHeap (maskB := maskB) (maskF := maskF) packet graph tags root)[coordinateBase graph + index]? =
      (setupWords width graph root)[index]? := by
  have directory : (((packet ++ tags.toArray) ++ (rootWords width graph).toArray) ++
      (EnumerationMasks.masksOf width maskB maskF).toArray).size = coordinateBase graph := by
    simp only [Array.size_append, List.size_toArray, rootWords_length, EnumerationMasks.masksOf_length, packetLength, tagCount, coordinateBase]
    omega
  unfold preparedHeap
  rw [Array.getElem?_append_right (by omega), directory, Nat.add_sub_cancel_left]
  simp

theorem preparedHeap_coordinate (packet : Array (Word width)) (graph : DAG n) (tags : List (Word width)) (root : Nat)
    (packetLength : packet.size = packetSize graph) (tagCount : tags.length = graph.roots.length)
    (coordinate : Fin (n + graph.nodeCount)) :
    (preparedHeap (maskB := maskB) (maskF := maskF) packet graph tags root)[coordinateBase graph + coordinate.val]? =
      some (word width coordinate.val) := by
  rw [preparedHeap_setup (maskB := maskB) (maskF := maskF) packet graph tags root packetLength tagCount coordinate.val (by omega)]
  simp [setupWords, List.getElem?_append_left, SharedCoordinateTable.words]

theorem preparedHeap_slot (packet : Array (Word width)) (graph : DAG n) (tags : List (Word width)) (root : Nat)
    (packetLength : packet.size = packetSize graph) (tagCount : tags.length = graph.roots.length) :
    (preparedHeap (maskB := maskB) (maskF := maskF) packet graph tags root)[slot graph]? = some (word width root) := by
  have at_slot := preparedHeap_setup (maskB := maskB) (maskF := maskF) packet graph tags root packetLength tagCount (n + graph.nodeCount) (by omega)
  rw [show coordinateBase graph + (n + graph.nodeCount) = slot graph from rfl] at at_slot
  rw [at_slot]
  simp [setupWords, SharedCoordinateTable.words]

theorem preparedHeap_table (packet : Array (Word width)) (graph : DAG n) (tags : List (Word width)) (root : Nat)
    (packetLength : packet.size = packetSize graph) (tagCount : tags.length = graph.roots.length)
    (index : Nat) (below : index < 2 * (n + graph.nodeCount)) :
    (preparedHeap (maskB := maskB) (maskF := maskF) packet graph tags root)[tableBase graph + index]? = some (word width 0) := by
  have at_table := preparedHeap_setup (maskB := maskB) (maskF := maskF) packet graph tags root packetLength tagCount
    (n + graph.nodeCount + 1 + index) (by omega)
  rw [show coordinateBase graph + (n + graph.nodeCount + 1 + index) = tableBase graph + index by
    simp only [tableBase, slot]; omega] at at_table
  rw [at_table]
  simp only [setupWords, SharedCoordinateTable.words]
  rw [List.getElem?_append_right (by simp; omega)]
  simp only [List.length_map, List.length_finRange, show n + graph.nodeCount + 1 + index - (n + graph.nodeCount) =
    index + 1 by omega, List.getElem?_cons_succ, List.getElem?_replicate, below, ite_true]

theorem preparedHeap_tags (packet : Array (Word width)) (graph : DAG n) (tags : List (Word width)) (root : Nat)
    (packetLength : packet.size = packetSize graph) :
    SharedDetectorData.Slots (preparedHeap (maskB := maskB) (maskF := maskF) packet graph tags root) (packetSize graph) tags := by
  intro index below
  unfold preparedHeap
  rw [Array.getElem?_append_left (by simp only [Array.size_append, List.size_toArray]; omega),
      Array.getElem?_append_left (by simp only [Array.size_append, List.size_toArray]; omega),
    Array.getElem?_append_left (by simp only [Array.size_append, List.size_toArray]; omega),
    Array.getElem?_append_right (by omega)]
  simp [packetLength, below]

theorem preparedHeap_roots (packet : Array (Word width)) (graph : DAG n) (tags : List (Word width)) (root : Nat)
    (packetLength : packet.size = packetSize graph) (tagCount : tags.length = graph.roots.length) :
    SharedDetectorData.Slots (preparedHeap (maskB := maskB) (maskF := maskF) packet graph tags root) (packetSize graph + graph.roots.length)
      (rootWords width graph) := by
  intro index below
  unfold preparedHeap
  rw [Array.getElem?_append_left (by
      simp only [Array.size_append, List.size_toArray, rootWords_length, EnumerationMasks.masksOf_length, packetLength, tagCount] at below ⊢; omega),
    Array.getElem?_append_left (by
      simp only [Array.size_append, List.size_toArray, rootWords_length, packetLength, tagCount] at below ⊢; omega),
    Array.getElem?_append_right (by simp only [Array.size_append, List.size_toArray, packetLength, tagCount]; omega)]
  simp only [Array.size_append, List.size_toArray, packetLength, tagCount,
    show packetSize graph + graph.roots.length + index - (packetSize graph + graph.roots.length) = index by omega]
  simp

theorem preparedHeap_mask (packet : Array (Word width)) (graph : DAG n) (tags : List (Word width)) (root : Nat)
    (packetLength : packet.size = packetSize graph) (tagCount : tags.length = graph.roots.length)
    (index : Nat) (below : index < 2 * n) :
    (preparedHeap (maskB := maskB) (maskF := maskF) packet graph tags root)[trueBase graph + index]? =
      (EnumerationMasks.masksOf width maskB maskF)[index]? := by
  have directorySize : ((packet ++ tags.toArray) ++ (rootWords width graph).toArray).size = trueBase graph := by
    simp [trueBase, SharedDetectorPrepared.coordinateBase, packetLength, tagCount]
    omega
  unfold preparedHeap
  rw [Array.getElem?_append_left (by simp only [Array.size_append, List.size_toArray,
      EnumerationMasks.masksOf_length, directorySize]; omega),
    Array.getElem?_append_right (by rw [directorySize]; omega), directorySize, Nat.add_sub_cancel_left]
  simp

theorem masks_stored (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels)) (packet : Array (Word width)) (tags : List (Word width)) (root : Nat)
    (packetLength : packet.size = packetSize graph) (tagCount : tags.length = graph.roots.length) :
    EnumerationFixedRootQuery.MaskCells parameters
      (preparedHeap (maskB := T) (maskF := F) packet graph tags root)
      (coordinateBase graph) (trueBase graph) (falseBase graph) (slot graph + 1) T F := by
  have bases : coordinateBase graph = trueBase graph + 2 * parameters.channels := by
    simp only [coordinateBase, trueBase, SharedDetectorPrepared.coordinateBase]
  refine ⟨by unfold slot; omega, by unfold slot; omega, by unfold slot falseBase; omega, ?_, ?_, ?_⟩
  · intro channel
    exact preparedHeap_coordinate packet graph tags root packetLength tagCount ⟨channel.val, by have := channel.isLt; omega⟩
  · intro channel
    rw [preparedHeap_mask packet graph tags root packetLength tagCount channel.val (by have := channel.isLt; omega)]
    exact EnumerationMasks.masksOf_getElem?_base width T F channel
  · intro channel
    change _[trueBase graph + parameters.channels + channel.val]? = _
    rw [show trueBase graph + parameters.channels + channel.val = trueBase graph + (parameters.channels + channel.val) by omega,
      preparedHeap_mask packet graph tags root packetLength tagCount (parameters.channels + channel.val) (by have := channel.isLt; omega)]
    exact EnumerationMasks.masksOf_getElem?_flag width T F channel

end Layout

section Ready
variable {n : Nat}
variable {maskB maskF : Finset (Fin n)}

theorem widen {heap : Array (Word width)} {channels sourceEnd larger : Nat} {reference : Reference ambient}
    (stored : StoredReference heap channels sourceEnd reference) (le : sourceEnd ≤ larger)
    (bound : larger ≤ heap.size) : StoredReference heap channels larger reference :=
  ⟨bound, by have := stored.slotBound; omega, by have := stored.headerBound; omega,
    stored.slotWord, stored.channelWord, stored.coordinateEq⟩

def layout (graph : DAG n) (size : Nat) (sizeEq : size = preparedSize graph) :
    Layout (n + graph.nodeCount) size where
  tableBase := tableBase graph
  inverseBase := inverseBase graph
  tableBound := by subst sizeEq; simp only [preparedSize, inverseBase]; omega
  inverseBound := by subst sizeEq; simp only [preparedSize]; omega
  disjoint := Or.inl (by simp only [inverseBase]; omega)

theorem source_stored (graph : DAG n) (b : Nat) (target : Fin n) (T F : Finset (Fin n))
    (packet : Array (Word width)) (tags : List (Word width)) (root : Fin graph.nodeCount)
    (packetLength : packet.size = packetSize graph) (tagCount : tags.length = graph.roots.length)
    (header : packet[0]? = some (word width n)) :
    ∀ item ∈ (SharedZeroSource.references graph b target T F (coordinateBase graph) (slot graph) root).flatten,
      StoredReference (preparedHeap (maskB := maskB) (maskF := maskF) packet graph tags root.val) n (slot graph + 1) item := by
  have packetPositive : 0 < packet.size := (Array.getElem?_eq_some_iff.mp header).1
  let directory := ((packet ++ tags.toArray) ++ (rootWords width graph).toArray) ++
    (EnumerationMasks.masksOf width maskB maskF).toArray
  have directorySize : directory.size = coordinateBase graph := by
    simp only [directory, Array.size_append, List.size_toArray, rootWords_length, EnumerationMasks.masksOf_length, packetLength, tagCount,
      coordinateBase]
    omega
  have directoryHeader : directory[0]? = some (word width n) := by
    simp only [directory]
    rw [Array.getElem?_append_left (by simp only [Array.size_append, List.size_toArray]; omega),
      Array.getElem?_append_left (by simp only [Array.size_append, List.size_toArray]; omega),
      Array.getElem?_append_left packetPositive]
    exact header
  have split : preparedHeap (maskB := maskB) (maskF := maskF) packet graph tags root.val =
      (directory ++ (SharedCoordinateTable.words width (n + graph.nodeCount)).toArray) ++
        (word width root.val :: List.replicate (2 * (n + graph.nodeCount)) (word width 0)).toArray := by
    simp only [preparedHeap, setupWords, directory, Array.append_assoc, List.append_toArray, List.append_assoc]
  have total := preparedHeap_size (maskB := maskB) (maskF := maskF) packet graph tags root.val packetLength tagCount
  intro item member
  simp only [SharedZeroSource.references, List.flatten_append, List.flatten_cons, List.flatten_nil,
    List.append_nil, List.mem_append, List.mem_singleton] at member
  rcases member with fixed | queried
  · have stored := SharedCoordinateTable.rows_stored directory n directoryHeader
      (by rw [directorySize, coordinateBase_eq]; omega)
      (SharedZeroSource.fixedRows graph b target T F) item (by simpa only [directorySize] using fixed)
    have frame : PrefixFrame (directory.size + (n + graph.nodeCount))
        (directory ++ (SharedCoordinateTable.words width (n + graph.nodeCount)).toArray)
        (preparedHeap (maskB := maskB) (maskF := maskF) packet graph tags root.val) := by
      refine ⟨by simp, by rw [total, directorySize, preparedSize_eq]; omega, ?_⟩
      intro index below
      rw [split, Array.getElem?_append_left (by simpa using below)]
    have moved := stored_reference_prefix stored frame
    rw [directorySize] at moved
    exact widen moved (by simp only [slot]; omega) (by rw [total]; simp only [preparedSize, inverseBase, tableBase]; omega)
  · subst item
    refine ⟨by rw [total]; simp only [preparedSize, inverseBase, tableBase]; omega, by simp [SharedZeroCode.rootReference],
      by omega, ?_, ?_, by simp [SharedZeroCode.rootReference, Nat.add_comm]⟩
    · simpa [SharedZeroCode.rootReference] using preparedHeap_slot (maskB := maskB) (maskF := maskF) packet graph tags root.val packetLength tagCount
    · rw [preparedHeap_prefix (maskB := maskB) (maskF := maskF) packet graph tags root.val 0 packetPositive]
      exact header


end Ready

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem scan_ready (parameters : Parameters) (graph : DAG parameters.channels) (guarded : graph.Guarded)
    (T F : Finset (Fin parameters.channels))
    (consistent : FixedConsistent (extensionBase parameters.buses parameters.bridge.target T) F) (retained entry ret : Nat)
    (program : Program (EnumerationUniformScan.Width parameters graph retained) 8)
    (rest : List (Word (EnumerationUniformScan.Width parameters graph retained)))
    (packet : Array (Word (EnumerationUniformScan.Width parameters graph retained)))
    (root : Fin graph.nodeCount) (state : State (EnumerationUniformScan.Width parameters graph retained) 8)
    (packetLength : packet.size = packetSize graph)
    (header : packet[0]? = some (word (EnumerationUniformScan.Width parameters graph retained) parameters.channels))
    (nodes : packet[1]? = some (word (EnumerationUniformScan.Width parameters graph retained) graph.nodeCount))
    (mask : ∀ channel : Fin parameters.channels, packet[maskBase graph + channel.val]? =
      some (word (EnumerationUniformScan.Width parameters graph retained)
        (if assignmentOfSet (extensionBase parameters.buses parameters.bridge.target T) channel then 1 else 0)))
    (heap : state.heap = preparedHeap (maskB := extensionBase parameters.buses parameters.bridge.target T) (maskF := F) packet graph ((List.finRange graph.roots.length).map
      (SharedWitnessDecode.tag graph (extensionBase parameters.buses parameters.bridge.target T) F
        (EnumerationUniformScan.Width parameters graph retained))) root.val)
    (sizeEq : state.heap.size = preparedSize graph)
    (stack : state.stack = word (EnumerationUniformScan.Width parameters graph retained) (packetSize graph) ::
      word (EnumerationUniformScan.Width parameters graph retained) graph.roots.length ::
        (SharedHealthyReference.reference graph parameters.bridge.target
          (EnumerationUniformScan.Width parameters graph retained) ++ rest))
    (position : state.pc = word (EnumerationUniformScan.Width parameters graph retained) entry)
    (running : state.halted = false)
    (zero : state.reg 0 = word (EnumerationUniformScan.Width parameters graph retained) 0)
    (table : state.reg 1 = word (EnumerationUniformScan.Width parameters graph retained) (tableBase graph))
    (inverse : state.reg 2 = word (EnumerationUniformScan.Width parameters graph retained) (inverseBase graph))
    (heapRoom : preparedSize graph ≤ retained)
    (codeRoom : entry + (EnumerationUniformLoop.code (trueBase := trueBase graph) (falseBase := falseBase graph) parameters graph T F state.heap
      (layout graph state.heap.size sizeEq) (coordinateBase graph) (slot graph) graph.roots.length
      entry ret root).length ≤ retained)
    (present : SharedRootRead.BlockAt program entry (EnumerationUniformLoop.code (trueBase := trueBase graph) (falseBase := falseBase graph) parameters graph T F state.heap
      (layout graph state.heap.size sizeEq) (coordinateBase graph) (slot graph) graph.roots.length
      entry ret root)) :
    EnumerationUniformScan.Ready (trueBase := trueBase graph) (falseBase := falseBase graph) parameters graph T F retained (coordinateBase graph) (slot graph) (slot graph + 1)
      graph.roots.length (maskBase graph) entry ret program rest state (packetSize graph)
      (List.finRange graph.roots.length) := by
  let W := EnumerationUniformScan.Width parameters graph retained
  let tags := (List.finRange graph.roots.length).map
    (SharedWitnessDecode.tag graph (extensionBase parameters.buses parameters.bridge.target T) F W)
  have tagCount : tags.length = graph.roots.length := by simp [tags]
  have packetPositive : 0 < packet.size := (Array.getElem?_eq_some_iff.mp header).1
  have prefixCell : ∀ index, index < packetSize graph → state.heap[index]? = packet[index]? := by
    intro index below
    rw [heap]
    exact preparedHeap_prefix (maskB := extensionBase parameters.buses parameters.bridge.target T) (maskF := F) packet graph tags root.val index (by omega)
  have cells : ∀ index : Nat, state.heap[index]? = (preparedHeap (maskB := extensionBase parameters.buses parameters.bridge.target T) (maskF := F) packet graph tags root.val)[index]? := by
    intro index
    rw [heap]
  have size := graph.countedSize_eq
  refine ⟨root, state.heap, layout graph state.heap.size sizeEq,
    ?_, ?_, ?_, ?_, consistent, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
      sourceDual := SharedQuerySourceFrame.zero_dualHorn graph guarded parameters.buses parameters.bridge.target ∅ ∅
        root (coordinateBase graph) (slot graph)
      sourceEndpoint := by simp only [layout]; rw [sizeEq]; simp [preparedSize] }
    intro item member
    rw [heap]
    exact source_stored (maskB := extensionBase parameters.buses parameters.bridge.target T) (maskF := F) graph parameters.buses parameters.bridge.target ∅ ∅ packet tags root packetLength tagCount
      header item member
  · rw [heap]
    exact masks_stored parameters graph (extensionBase parameters.buses parameters.bridge.target T) F packet tags root.val packetLength tagCount
  · simp only [trueBase, slot, coordinateBase, SharedDetectorPrepared.coordinateBase]
    omega
  · simp only [falseBase, trueBase, slot, coordinateBase, SharedDetectorPrepared.coordinateBase]
    omega
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
      exact preparedHeap_table (maskB := extensionBase parameters.buses parameters.bridge.target T) (maskF := F) packet graph tags root.val packetLength tagCount coordinate.val (by omega)
    · rw [stack, ← SharedDetectorData.healthyTags_reference parameters graph W, List.length_finRange]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [List.length_finRange, slot, coordinateBase]; omega
    · simp only [List.length_finRange, slot, coordinateBase]; omega
    · simp only [slot, coordinateBase, packetSize]; omega
    · intro index below
      rw [cells]
      exact preparedHeap_tags (maskB := extensionBase parameters.buses parameters.bridge.target T) (maskF := F) packet graph tags root.val packetLength index below
    · intro index below
      rw [cells]
      have roots := preparedHeap_roots (maskB := extensionBase parameters.buses parameters.bridge.target T) (maskF := F) packet graph tags root.val packetLength tagCount
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



end Controller.Cost.EnumerationUniformPrepared
