module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedDetectorSteps
public import Controller.Cost.SharedDetectorDirectoryAlloc
public import Controller.Cost.SharedRetainedCandidates

@[expose] public section

/-! The one prepared heap of the shared detector. After the candidate pass, the healthy packet
is followed by the candidate directory (one witness tag and one root identifier per output),
the coordinate table, the shared query-root slot and the reserved dictionary/inverse tables.
Every zero query reuses these cells; nothing here is allocated per output. -/
namespace Controller.Cost.SharedDetectorPrepared
open Controller.Decoder Controller.Decoder.DAG Controller.Cost.GateProgram
open Controller.Cost.ForestIndexedOperands Controller.Cost.UniformDAGSource
open Controller.Cost.UniformDAGRun Controller.Cost.ForestInputPrefixStored Controller.Cost.ForestInputStored
open Controller.Cost.RawTransferLoops Controller.Cost.ForestZeroDictionary Controller.Cost.ForestZeroAdmissibleCaller
open Controller.Cost.ForestZeroBackendFrame Controller.Cost.ForestZeroEmit
open Controller.Native Controller.Native.SourceController Controller.Cost.SharedZeroResidentConditions

section Layout
variable {n : Nat}

/-- First declared-root cell of the loaded packet. -/
def rootBase (graph : DAG n) : Nat :=
  5 + 6 * graph.nodeCount + graph.childIncidences + graph.guardIncidences

/-- First channel-value cell; it holds the baseline mask after the candidate pass. -/
def maskBase (graph : DAG n) : Nat := rootBase graph + graph.roots.length

def packetSize (graph : DAG n) : Nat := maskBase graph + n

def coordinateBase (graph : DAG n) : Nat := packetSize graph + 2 * graph.roots.length

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
      3 * graph.roots.length + n := by
  simp only [coordinateBase, packetSize, maskBase, rootBase]; omega

theorem preparedSize_le (graph : DAG n) : preparedSize graph ≤ 10 * (graph.countedSize + 1) := by
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
  ((packet ++ tags.toArray) ++ (rootWords width graph).toArray) ++ (setupWords width graph root).toArray

theorem preparedHeap_size (packet : Array (Word width)) (graph : DAG n) (tags : List (Word width)) (root : Nat)
    (packetLength : packet.size = packetSize graph) (tagCount : tags.length = graph.roots.length) :
    (preparedHeap packet graph tags root).size = preparedSize graph := by
  simp only [preparedHeap, Array.size_append, List.size_toArray, rootWords_length, setupWords_length,
    packetLength, tagCount, preparedSize, inverseBase, tableBase, slot, coordinateBase]
  omega

theorem preparedHeap_prefix (packet : Array (Word width)) (graph : DAG n) (tags : List (Word width)) (root : Nat)
    (index : Nat) (below : index < packet.size) :
    (preparedHeap packet graph tags root)[index]? = packet[index]? := by
  unfold preparedHeap
  rw [Array.getElem?_append_left (by simp only [Array.size_append, List.size_toArray]; omega),
    Array.getElem?_append_left (by simp only [Array.size_append, List.size_toArray]; omega),
    Array.getElem?_append_left below]

theorem preparedHeap_setup (packet : Array (Word width)) (graph : DAG n) (tags : List (Word width)) (root : Nat)
    (packetLength : packet.size = packetSize graph) (tagCount : tags.length = graph.roots.length)
    (index : Nat) (below : index < 3 * (n + graph.nodeCount) + 1) :
    (preparedHeap packet graph tags root)[coordinateBase graph + index]? =
      (setupWords width graph root)[index]? := by
  have directory : ((packet ++ tags.toArray) ++ (rootWords width graph).toArray).size = coordinateBase graph := by
    simp only [Array.size_append, List.size_toArray, rootWords_length, packetLength, tagCount, coordinateBase]
    omega
  unfold preparedHeap
  rw [Array.getElem?_append_right (by omega), directory, Nat.add_sub_cancel_left]
  simp

theorem preparedHeap_coordinate (packet : Array (Word width)) (graph : DAG n) (tags : List (Word width)) (root : Nat)
    (packetLength : packet.size = packetSize graph) (tagCount : tags.length = graph.roots.length)
    (coordinate : Fin (n + graph.nodeCount)) :
    (preparedHeap packet graph tags root)[coordinateBase graph + coordinate.val]? =
      some (word width coordinate.val) := by
  rw [preparedHeap_setup packet graph tags root packetLength tagCount coordinate.val (by omega)]
  simp [setupWords, List.getElem?_append_left, SharedCoordinateTable.words]

theorem preparedHeap_slot (packet : Array (Word width)) (graph : DAG n) (tags : List (Word width)) (root : Nat)
    (packetLength : packet.size = packetSize graph) (tagCount : tags.length = graph.roots.length) :
    (preparedHeap packet graph tags root)[slot graph]? = some (word width root) := by
  have at_slot := preparedHeap_setup packet graph tags root packetLength tagCount (n + graph.nodeCount) (by omega)
  rw [show coordinateBase graph + (n + graph.nodeCount) = slot graph from rfl] at at_slot
  rw [at_slot]
  simp [setupWords, List.getElem?_append_right, SharedCoordinateTable.words]

theorem preparedHeap_table (packet : Array (Word width)) (graph : DAG n) (tags : List (Word width)) (root : Nat)
    (packetLength : packet.size = packetSize graph) (tagCount : tags.length = graph.roots.length)
    (index : Nat) (below : index < 2 * (n + graph.nodeCount)) :
    (preparedHeap packet graph tags root)[tableBase graph + index]? = some (word width 0) := by
  have at_table := preparedHeap_setup packet graph tags root packetLength tagCount
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
    SharedDetectorData.Slots (preparedHeap packet graph tags root) (packetSize graph) tags := by
  intro index below
  unfold preparedHeap
  rw [Array.getElem?_append_left (by simp only [Array.size_append, List.size_toArray]; omega),
    Array.getElem?_append_left (by simp only [Array.size_append, List.size_toArray]; omega),
    Array.getElem?_append_right (by omega)]
  simp [packetLength, below]

theorem preparedHeap_roots (packet : Array (Word width)) (graph : DAG n) (tags : List (Word width)) (root : Nat)
    (packetLength : packet.size = packetSize graph) (tagCount : tags.length = graph.roots.length) :
    SharedDetectorData.Slots (preparedHeap packet graph tags root) (packetSize graph + graph.roots.length)
      (rootWords width graph) := by
  intro index below
  unfold preparedHeap
  rw [Array.getElem?_append_left (by
      simp only [Array.size_append, List.size_toArray, rootWords_length, packetLength, tagCount] at below ⊢; omega),
    Array.getElem?_append_right (by simp only [Array.size_append, List.size_toArray, packetLength, tagCount]; omega)]
  simp only [Array.size_append, List.size_toArray, packetLength, tagCount,
    show packetSize graph + graph.roots.length + index - (packetSize graph + graph.roots.length) = index by omega]
  simp [below]

end Layout

section Packet
variable {n : Nat}

theorem packet_size (graph : DAG n) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (rootMatches : RootsMatch graph roots) (values : Assignment n) :
    (channelHeap (packetHeaderHeap width n rows roots) rows roots values).size = packetSize graph := by
  obtain ⟨children, guards⟩ := matched_incidence_lengths graph rows matched
  have rootCount : roots.length = graph.roots.length := by rw [rootMatches]; simp
  simp only [channelHeap_size, cacheHeap_size, packetHeaderHeap_size, matched.length_eq, children, guards,
    rootCount, packetSize, maskBase, rootBase]
  try omega

theorem packet_header (graph : DAG n) (rows : List Row) (roots : List Nat) (values : Assignment n)
    (index : Nat) (below : index < 5) :
    (channelHeap (packetHeaderHeap width n rows roots) rows roots values)[index]? =
      some (word width ((globalHeader n rows roots)[index]'(by simpa using below))) := by
  unfold channelHeap withValues cacheHeap Controller.Cost.ForestCursorMaterialize.allocatedHeap
  rw [Array.getElem?_append_left (by simp; omega), Array.getElem?_append_left (by simp; omega)]
  simp [packetHeaderHeap, below]

theorem packet_channels (graph : DAG n) (rows : List Row) (roots : List Nat) (values : Assignment n) :
    (channelHeap (packetHeaderHeap width n rows roots) rows roots values)[0]? = some (word width n) := by
  rw [packet_header graph rows roots values 0 (by decide)]
  rfl

theorem packet_nodes (graph : DAG n) (rows : List Row) (roots : List Nat) (matched : RowsMatch graph rows)
    (values : Assignment n) :
    (channelHeap (packetHeaderHeap width n rows roots) rows roots values)[1]? = some (word width graph.nodeCount) := by
  rw [packet_header graph rows roots values 1 (by decide)]
  simp [globalHeader, countSource_value, matched.length_eq]

theorem packet_outputs (graph : DAG n) (rows : List Row) (roots : List Nat) (rootMatches : RootsMatch graph roots)
    (values : Assignment n) :
    (channelHeap (packetHeaderHeap width n rows roots) rows roots values)[4]? =
      some (word width graph.roots.length) := by
  have rootCount : roots.length = graph.roots.length := by rw [rootMatches]; simp
  rw [packet_header graph rows roots values 4 (by decide)]
  simp [globalHeader, countSource_value, rootCount]

theorem packet_roots (graph : DAG n) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (rootMatches : RootsMatch graph roots) (values : Assignment n) :
    SharedDetectorData.Slots (channelHeap (packetHeaderHeap width n rows roots) rows roots values)
      (rootBase graph) (rootWords width graph) := by
  intro index below
  have rootCount : roots.length = graph.roots.length := by rw [rootMatches]; simp
  obtain ⟨children, guards⟩ := matched_incidence_lengths graph rows matched
  have valid : index < graph.roots.length := by simpa using below
  have cell := cache_declared_root_word (packetHeaderHeap width n rows roots) graph rows roots rootMatches ⟨index, valid⟩
  have bound : rootBase graph + index < (cacheHeap width (packetHeaderHeap width n rows roots) rows roots).size := by
    simp only [cacheHeap_size, packetHeaderHeap_size, matched.length_eq, children, guards, rootCount, rootBase]
    omega
  unfold channelHeap withValues
  rw [Array.getElem?_append_left bound, Array.getElem?_eq_getElem bound]
  simp only [packetHeaderHeap_size, matched.length_eq, children, guards] at cell
  simp only [rootWords, List.getElem_map, Option.some.injEq]
  convert cell using 2
  all_goals first | rfl | (simp only [rootBase]; omega)

theorem packet_mask (graph : DAG n) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (rootMatches : RootsMatch graph roots) (values : Assignment n)
    (channel : Fin n) :
    (channelHeap (packetHeaderHeap width n rows roots) rows roots values)[maskBase graph + channel.val]? =
      some (word width (if values channel then 1 else 0)) := by
  have rootCount : roots.length = graph.roots.length := by rw [rootMatches]; simp
  obtain ⟨children, guards⟩ := matched_incidence_lengths graph rows matched
  have size : (cacheHeap width (packetHeaderHeap width n rows roots) rows roots).size = maskBase graph := by
    simp only [cacheHeap_size, packetHeaderHeap_size, matched.length_eq, children, guards, rootCount,
      maskBase, rootBase]
    try omega
  have cell := value_cell (cacheHeap width (packetHeaderHeap width n rows roots) rows roots) values channel
  unfold channelHeap
  rw [← size, Array.getElem?_eq_getElem (by simp only [withValues_size]; omega), cell]
  rfl

end Packet

section Ready
variable {n : Nat}

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
      StoredReference (preparedHeap packet graph tags root.val) n (slot graph + 1) item := by
  have packetPositive : 0 < packet.size := (Array.getElem?_eq_some_iff.mp header).1
  let directory := (packet ++ tags.toArray) ++ (rootWords width graph).toArray
  have directorySize : directory.size = coordinateBase graph := by
    simp only [directory, Array.size_append, List.size_toArray, rootWords_length, packetLength, tagCount,
      coordinateBase]
    omega
  have directoryHeader : directory[0]? = some (word width n) := by
    simp only [directory]
    rw [Array.getElem?_append_left (by simp only [Array.size_append, List.size_toArray]; omega),
      Array.getElem?_append_left packetPositive]
    exact header
  have split : preparedHeap packet graph tags root.val =
      (directory ++ (SharedCoordinateTable.words width (n + graph.nodeCount)).toArray) ++
        (word width root.val :: List.replicate (2 * (n + graph.nodeCount)) (word width 0)).toArray := by
    simp only [preparedHeap, setupWords, directory, Array.append_assoc, List.append_toArray, List.append_assoc]
  have total := preparedHeap_size packet graph tags root.val packetLength tagCount
  intro item member
  simp only [SharedZeroSource.references, List.flatten_append, List.flatten_cons, List.flatten_nil,
    List.append_nil, List.mem_append, List.mem_singleton] at member
  rcases member with fixed | queried
  · have stored := SharedCoordinateTable.rows_stored directory n directoryHeader
      (by rw [directorySize, coordinateBase_eq]; omega)
      (SharedZeroSource.fixedRows graph b target T F) item (by simpa only [directorySize] using fixed)
    have frame : PrefixFrame (directory.size + (n + graph.nodeCount))
        (directory ++ (SharedCoordinateTable.words width (n + graph.nodeCount)).toArray)
        (preparedHeap packet graph tags root.val) := by
      refine ⟨by simp, by rw [total, directorySize, preparedSize_eq]; omega, ?_⟩
      intro index below
      rw [split, Array.getElem?_append_left (by simpa using below)]
    have moved := stored_reference_prefix stored frame
    rw [directorySize] at moved
    exact widen moved (by simp only [slot]; omega) (by rw [total]; simp only [preparedSize, inverseBase, tableBase]; omega)
  · subst item
    refine ⟨by rw [total]; simp only [preparedSize, inverseBase, tableBase]; omega, by simp [SharedZeroCode.rootReference],
      by omega, ?_, ?_, by simp [SharedZeroCode.rootReference, Nat.add_comm]⟩
    · simpa [SharedZeroCode.rootReference] using preparedHeap_slot packet graph tags root.val packetLength tagCount
    · rw [preparedHeap_prefix packet graph tags root.val 0 packetPositive]
      exact header


/-- The prepared heap, registers and stack satisfy the shared detector loop's entry invariant
for every output position, with the healthy reference tags on the stack. -/
theorem ready (parameters : Parameters) (graph : DAG parameters.channels) (guarded : graph.Guarded)
    (T F : Finset (Fin parameters.channels)) (retained entry : Nat)
    (program : Program (SharedDetectorLoop.Width parameters graph retained) 8)
    (rest : List (Word (SharedDetectorLoop.Width parameters graph retained)))
    (packet : Array (Word (SharedDetectorLoop.Width parameters graph retained)))
    (root : Fin graph.nodeCount) (state : State (SharedDetectorLoop.Width parameters graph retained) 8)
    (packetLength : packet.size = packetSize graph)
    (header : packet[0]? = some (word (SharedDetectorLoop.Width parameters graph retained) parameters.channels))
    (nodes : packet[1]? = some (word (SharedDetectorLoop.Width parameters graph retained) graph.nodeCount))
    (mask : ∀ channel : Fin parameters.channels, packet[maskBase graph + channel.val]? =
      some (word (SharedDetectorLoop.Width parameters graph retained)
        (if assignmentOfSet (extensionBase parameters.buses parameters.bridge.target T) channel then 1 else 0)))
    (heap : state.heap = preparedHeap packet graph ((List.finRange graph.roots.length).map
      (SharedWitnessDecode.tag graph (extensionBase parameters.buses parameters.bridge.target T) F
        (SharedDetectorLoop.Width parameters graph retained))) root.val)
    (sizeEq : state.heap.size = preparedSize graph)
    (stack : state.stack = word (SharedDetectorLoop.Width parameters graph retained) (packetSize graph) ::
      word (SharedDetectorLoop.Width parameters graph retained) graph.roots.length ::
        (SharedHealthyReference.reference graph parameters.bridge.target
          (SharedDetectorLoop.Width parameters graph retained) ++ rest))
    (position : state.pc = word (SharedDetectorLoop.Width parameters graph retained) entry)
    (running : state.halted = false)
    (zero : state.reg 0 = word (SharedDetectorLoop.Width parameters graph retained) 0)
    (table : state.reg 1 = word (SharedDetectorLoop.Width parameters graph retained) (tableBase graph))
    (inverse : state.reg 2 = word (SharedDetectorLoop.Width parameters graph retained) (inverseBase graph))
    (heapRoom : preparedSize graph ≤ retained)
    (codeRoom : entry + (SharedRootDetectorResident.code parameters graph T F state.heap
      (layout graph state.heap.size sizeEq) (coordinateBase graph) (slot graph) graph.roots.length
      (maskBase graph) entry root).length ≤ retained)
    (present : SharedRootRead.BlockAt program entry (SharedRootDetectorResident.code parameters graph T F state.heap
      (layout graph state.heap.size sizeEq) (coordinateBase graph) (slot graph) graph.roots.length
      (maskBase graph) entry root)) :
    SharedDetectorLoop.Ready parameters graph T F retained (coordinateBase graph) (slot graph) (slot graph + 1)
      graph.roots.length (maskBase graph) entry program rest state (packetSize graph)
      (List.finRange graph.roots.length) := by
  let W := SharedDetectorLoop.Width parameters graph retained
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

end Ready

end Controller.Cost.SharedDetectorPrepared
