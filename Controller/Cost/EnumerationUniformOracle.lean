module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.EnumerationUniformOracleCapacity
public import Mathlib.Tactic.ClearExcept

@[expose] public section

namespace Controller.Cost.EnumerationUniformOracle
open Controller.Cost.GateProgram Controller.Cost.RawTransferLoops Controller.Cost.EnumerationOracle

section Execution
open Controller.Decoder Controller.Decoder.DAG Controller.Cost.ForestIndexedOperands Controller.Cost.UniformDAGSource
open Controller.Cost.UniformDAGRun Controller.Cost.ForestInputPrefixStored Controller.Cost.ForestInputStored
open Controller.Native Controller.Native.SourceController Controller.Cost.NativeSourceExecution
open Controller.Cost.SharedDetectorPrepared Controller.Cost.EnumerationUniformPrepared Controller.Cost.SharedDetectorAssembly

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
/-- One re-entrant oracle call. -/
theorem execution (parameters : Parameters) (graph : DAG parameters.channels) (guarded : graph.Guarded)
    (T F : Finset (Fin parameters.channels))
    (consistent : FixedConsistent (extensionBase parameters.buses parameters.bridge.target T) F)
    (retained entry back : Nat) (program : Program (EnumerationUniformScan.Width parameters graph retained) 8)
    (rows : List Row) (roots : List Nat) (matched : RowsMatch graph rows) (heads : HeadsMatch graph rows matched)
    (rootMatches : RootsMatch graph roots) (suffix : List (Word (EnumerationUniformScan.Width parameters graph retained))) (state : State (EnumerationUniformScan.Width parameters graph retained) 8)
    (position : state.pc = word (EnumerationUniformScan.Width parameters graph retained) entry) (running : state.halted = false)
    (heapStored : state.heap = channelHeap (packetHeaderHeap (EnumerationUniformScan.Width parameters graph retained) parameters.channels rows roots) rows roots
      (assignmentOfSet {parameters.bridge.target}))
    (input : state.stack = SharedRetainedCandidates.masks (EnumerationUniformScan.Width parameters graph retained)
      (assignmentOfSet (extensionBase parameters.buses parameters.bridge.target T))
      ((List.finRange parameters.channels).map (assignmentOfSet F)) ++ suffix)
    (held : state.reg 4 = word (EnumerationUniformScan.Width parameters graph retained) parameters.bridge.target.val)
    (room : entry + (code parameters graph T F (EnumerationUniformScan.Width parameters graph retained) rows roots entry back).length + EnumerationUniformPrepared.preparedSize graph ≤ retained)
    (present : SharedRootRead.BlockAt program entry (code parameters graph T F (EnumerationUniformScan.Width parameters graph retained) rows roots entry back)) :
    ∃ answer : Bool, ∃ final ticks peak,
      Execution program state final ticks peak ∧ final.halted = false ∧ final.pc = word (EnumerationUniformScan.Width parameters graph retained) back ∧
      final.reg 4 = word (EnumerationUniformScan.Width parameters graph retained) (if answer then 1 else 0) ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      ticks ≤ (parameters.channels + graph.roots.length + 1) * (8000 * (graph.countedSize + 1)) ∧
      peak ≤ state.liveWords + 240 * (graph.countedSize + 1) ∧
      (answer = true ↔ ∃ output : Fin graph.roots.length, SharedDetectorFeasibility.AtRoot parameters graph T F output) := by
  have capacity := SharedMachineCapacity.capacity retained graph.countedSize (selectedSize parameters).total
  change 131072 * (retained + graph.countedSize + (selectedSize parameters).total + 1) < 2 ^ (EnumerationUniformScan.Width parameters graph retained) at capacity
  have size := graph.countedSize_eq
  have rootCount : roots.length = graph.roots.length := by rw [rootMatches]; simp
  have preparedBound := EnumerationUniformPrepared.preparedSize_le graph
  have preparedValue := EnumerationUniformPrepared.preparedSize_eq graph
  have coordinateValue := EnumerationUniformPrepared.coordinateBase_eq graph
  have coordinatePacket : EnumerationUniformPrepared.coordinateBase graph = SharedDetectorPrepared.packetSize graph + 2 * graph.roots.length + 2 * parameters.channels := rfl
  have packetValue : SharedDetectorPrepared.packetSize graph = SharedDetectorPrepared.rootBase graph + graph.roots.length + parameters.channels := rfl
  have maskValue : SharedDetectorPrepared.maskBase graph = SharedDetectorPrepared.rootBase graph + graph.roots.length := rfl
  have rootBaseValue : SharedDetectorPrepared.rootBase graph =
      5 + 6 * graph.nodeCount + graph.childIncidences + graph.guardIncidences := rfl
  have slotValue : EnumerationUniformPrepared.slot graph = EnumerationUniformPrepared.coordinateBase graph + (parameters.channels + graph.nodeCount) := rfl
  have eC : candidatesEntry entry = entry + 8 := rfl
  have eD : directoryEntry parameters graph entry =
      entry + 8 + (10 * graph.roots.length + 14 * parameters.channels + 620) := rfl
  have eR : retentionEntry parameters graph entry = directoryEntry parameters graph entry + (4 * graph.roots.length + 11) := rfl
  have eS : setupEntry parameters graph entry = retentionEntry parameters graph entry + 3 * graph.roots.length + 4 * parameters.channels + 10 := rfl
  have eH : handoffEntry parameters graph entry =
      setupEntry parameters graph entry + 2 * (3 * (parameters.channels + graph.nodeCount) + 1) := rfl
  have eL : scanEntry parameters graph entry = handoffEntry parameters graph entry + 7 := rfl
  have scanEnd := scanCode_length parameters graph T F (EnumerationUniformScan.Width parameters graph retained) entry
  have lengthEq := code_length parameters graph T F (EnumerationUniformScan.Width parameters graph retained) rows roots entry back rootMatches
  rw [lengthEq] at room
  obtain ⟨guardAt, candidatesAt, directoryAt, retentionAt, setupAt, handoffAt, scanAt, teardownAt⟩ :=
    physical_at parameters graph T F (EnumerationUniformScan.Width parameters graph retained)
      rows roots entry back program rootMatches present
  -- Output-count guard.
  have countCell : state.heap[4]? = some (word (EnumerationUniformScan.Width parameters graph retained) graph.roots.length) := by
    rw [heapStored]; exact packet_outputs graph rows roots rootMatches _
  obtain ⟨guarded', guardTicks, guardTrace, guardTime, guardHeap, guardStack, guardOutput, guardRunning,
      emptyCase, nonemptyCase⟩ :=
    guard_execution program state entry back graph.roots.length position running (by omega) (by omega)
      countCell guardAt
  by_cases emptyOutputs : graph.roots.length = 0
  · obtain ⟨pc, decision⟩ := emptyCase emptyOutputs
    refine ⟨false, guarded', guardTicks, state.liveWords, guardTrace, guardRunning, pc, by simpa using decision,
      guardHeap, guardStack, guardOutput, ?_, by omega, ?_⟩
    · have := Nat.le_mul_of_pos_left (8000 * (graph.countedSize + 1))
        (by omega : 0 < parameters.channels + graph.roots.length + 1)
      omega
    · simp only [Bool.false_eq_true, false_iff, not_exists]
      intro output
      exact absurd output.isLt (by omega)
  obtain ⟨guardPC, guardFrame⟩ := nonemptyCase emptyOutputs
  have nonemptyRoots : graph.roots ≠ [] := fun empty => emptyOutputs (by simp [empty])
  obtain ⟨root, tail, rootsEq⟩ := List.exists_cons_of_ne_nil nonemptyRoots
  have head : graph.roots.head? = some root := by rw [rootsEq]; rfl
  have teardownValue : teardownEntry parameters graph T F (EnumerationUniformScan.Width parameters graph retained) entry =
      EnumerationUniformLoop.returnPoint (trueBase := EnumerationUniformPrepared.trueBase graph) (falseBase := EnumerationUniformPrepared.falseBase graph) parameters graph T F (EnumerationUniformPrepared.preparedSize graph) (EnumerationUniformPrepared.coordinateBase graph) (EnumerationUniformPrepared.slot graph)
        (scanEntry parameters graph entry) root (EnumerationUniformScan.Width parameters graph retained) + 8 := by
    unfold teardownEntry; rw [head]
  have teardownBound := teardownEntry_bound parameters graph T F (EnumerationUniformScan.Width parameters graph retained) entry
  have candidateCapacity := graph_capacity retained graph.countedSize (selectedSize parameters).total
  have codeEndRetained : entry + (code parameters graph T F (EnumerationUniformScan.Width parameters graph retained)
      rows roots entry back).length ≤ retained := by
    rw [lengthEq]
    exact (Nat.le_add_right _ (EnumerationUniformPrepared.preparedSize graph)).trans room
  have candidateRoom : candidatesEntry entry + 10 * roots.length + 14 * parameters.channels + 620 <
      2 ^ EnumerationUniformScan.Width parameters graph retained := by
    have upper := (candidates_end_le parameters graph T F (EnumerationUniformScan.Width parameters graph retained)
      rows roots entry back rootMatches).trans codeEndRetained
    have strict := upper.trans_lt (retained_capacity retained graph.countedSize (selectedSize parameters).total)
    simpa only [directoryEntry, rootCount, Nat.add_assoc] using strict
  -- Shared candidate evaluations.
  obtain ⟨candidated, candidateTicks, candidatePeak, candidateTrace, candidateTime, candidateSpace,
      candidateHeap, candidateStack, candidateOutput, candidatePC, candidateRunning, candidateHead⟩ :=
    SharedRetainedCandidates.execution program guarded' graph rows roots matched heads rootMatches
      parameters.bridge.target (assignmentOfSet (extensionBase parameters.buses parameters.bridge.target T))
      ((List.finRange parameters.channels).map (assignmentOfSet F))
      suffix (candidatesEntry entry) (directoryEntry parameters graph entry)
      candidateCapacity candidatesAt candidateRoom
      (by simpa only [eC] using guardPC) guardRunning (guardHeap.trans heapStored) (guardStack.trans input) (by simp)
      ((guardFrame 4 (by decide)).trans held)
  have packetLength : candidated.heap.size = SharedDetectorPrepared.packetSize graph := by
    rw [candidateHeap]; exact SharedDetectorPrepared.packet_size graph rows roots matched rootMatches _
  have foldEq := SharedDetectorPrepared.tags_positions graph (extensionBase parameters.buses parameters.bridge.target T) F (EnumerationUniformScan.Width parameters graph retained)
  have tagCount : ((List.finRange graph.roots.length).map
      (SharedWitnessDecode.tag graph (extensionBase parameters.buses parameters.bridge.target T) F (EnumerationUniformScan.Width parameters graph retained))).length =
      graph.roots.length := by simp
  -- Candidate directory.
  obtain ⟨directed, directoryPeak, directoryTrace, directorySpace, directoryHeap, directoryStack, directoryOutput,
      directoryPC, directoryRunning⟩ :=
    SharedDetectorDirectoryAlloc.execution program candidated
      ((List.finRange graph.roots.length).map
        (SharedWitnessDecode.tag graph (extensionBase parameters.buses parameters.bridge.target T) F (EnumerationUniformScan.Width parameters graph retained)))
      (EnumerationUniformPrepared.rootWords (EnumerationUniformScan.Width parameters graph retained) graph)
      (SharedHealthyReference.reference graph parameters.bridge.target (EnumerationUniformScan.Width parameters graph retained) ++
        (SharedRetainedCandidates.masks (EnumerationUniformScan.Width parameters graph retained) (assignmentOfSet (extensionBase parameters.buses parameters.bridge.target T))
          ((List.finRange parameters.channels).map (assignmentOfSet F)) ++ suffix))
      (SharedDetectorPrepared.rootBase graph) (directoryEntry parameters graph entry) (by simp) candidatePC candidateRunning
      (by rw [tagCount]; omega)
      (by rw [tagCount, packetLength]; omega)
      (by simp only [SharedDetectorPrepared.rootBase]; omega)
      (by rw [packetLength]; simp only [EnumerationUniformPrepared.rootWords_length, SharedDetectorPrepared.packetSize, SharedDetectorPrepared.maskBase]; omega)
      (by rw [candidateHeap]; exact SharedDetectorPrepared.packet_roots graph rows roots matched rootMatches _)
      (by rw [candidateStack, foldEq]; simp only [List.append_assoc])
      (by rw [packetLength, tagCount]; exact directoryAt)
  -- Coordinate table, query EnumerationUniformPrepared.slot and reserved tables.
  have retainedMasksLength : (SharedRetainedCandidates.masks (EnumerationUniformScan.Width parameters graph retained)
      (assignmentOfSet (extensionBase parameters.buses parameters.bridge.target T))
      ((List.finRange parameters.channels).map (assignmentOfSet F))).length = 2 * parameters.channels := by simp; omega
  have directedSize : directed.heap.size = EnumerationUniformPrepared.trueBase graph := by
    rw [directoryHeap]
    simp only [Array.size_append, List.size_toArray, EnumerationUniformPrepared.rootWords_length, tagCount, packetLength,
      EnumerationUniformPrepared.trueBase, SharedDetectorPrepared.coordinateBase]
    omega
  have retentionPhysical : SharedRootRead.BlockAt program (retentionEntry parameters graph entry)
      (EnumerationMaskRetention.code (EnumerationUniformScan.Width parameters graph retained) (retentionEntry parameters graph entry)
        directed.heap.size (SharedRetainedCandidates.masks (EnumerationUniformScan.Width parameters graph retained)
          (assignmentOfSet (extensionBase parameters.buses parameters.bridge.target T))
          ((List.finRange parameters.channels).map (assignmentOfSet F))).length
        (SharedHealthyReference.reference graph parameters.bridge.target (EnumerationUniformScan.Width parameters graph retained))) := by
    rw [directedSize, retainedMasksLength]; exact retentionAt
  obtain ⟨retainedState, retentionTicks, retentionPeak, retentionTrace, retentionTime, retentionSpace, retentionHeap,
      retentionStack, retentionOutput, retentionPC, retentionRunning, retentionHead⟩ :=
    EnumerationMaskRetention.execution program directed
      (SharedHealthyReference.reference graph parameters.bridge.target (EnumerationUniformScan.Width parameters graph retained))
      (SharedRetainedCandidates.masks (EnumerationUniformScan.Width parameters graph retained)
        (assignmentOfSet (extensionBase parameters.buses parameters.bridge.target T))
        ((List.finRange parameters.channels).map (assignmentOfSet F))) suffix (retentionEntry parameters graph entry)
      (by rw [directoryPC, tagCount, eR]; rfl) directoryRunning
      (by rw [directoryStack]; simp only [List.append_assoc])
      (by rw [directedSize]; simp only [EnumerationUniformPrepared.trueBase, SharedDetectorPrepared.coordinateBase,
        SharedDetectorPrepared.packetSize, SharedDetectorPrepared.maskBase, SharedDetectorPrepared.rootBase]; omega) (by
        rw [directedSize, retainedMasksLength]
        change EnumerationUniformPrepared.coordinateBase graph < _
        omega)
      (by
        rw [EnumerationMaskRetention.code_length, retainedMasksLength]
        simp only [SharedHealthyReference.reference, List.length_map]
        omega) retentionPhysical
  have rootValue := firstRoot_head parameters graph root head
  rw [rootValue] at setupAt
  obtain ⟨prepared, setupTrace, setupHeap, setupStack, setupOutput, setupPC, setupRunning, setupHead⟩ :=
    SharedCoordinateTable.execution program retainedState (EnumerationUniformPrepared.setupWords (EnumerationUniformScan.Width parameters graph retained) graph root.val) (setupEntry parameters graph entry)
      (by
        rw [retentionPC, EnumerationMaskRetention.code_length, retainedMasksLength]
        simp only [SharedHealthyReference.reference, List.length_map, eS]
        congr 1
        omega) retentionRunning
      (by simp only [EnumerationUniformPrepared.setupWords_length]; omega)
      (by rw [retentionHeap, directoryHeap]; simp only [Array.size_append, List.size_toArray, EnumerationUniformPrepared.rootWords_length, tagCount, packetLength,
          EnumerationUniformPrepared.setupWords_length, retainedMasksLength]; omega)
      setupAt
  have preparedEq : prepared.heap = EnumerationUniformPrepared.preparedHeap (maskB := extensionBase parameters.buses parameters.bridge.target T) (maskF := F) candidated.heap graph
      ((List.finRange graph.roots.length).map
        (SharedWitnessDecode.tag graph (extensionBase parameters.buses parameters.bridge.target T) F (EnumerationUniformScan.Width parameters graph retained))) root.val := by
    rw [setupHeap, retentionHeap, directoryHeap]; rfl
  have preparedLength : prepared.heap.size = EnumerationUniformPrepared.preparedSize graph := by
    rw [preparedEq]; exact EnumerationUniformPrepared.preparedHeap_size (maskB := extensionBase parameters.buses parameters.bridge.target T) (maskF := F) _ graph _ root.val packetLength tagCount
  -- Register and stack handoff.
  obtain ⟨handed, handoffPeak, handoffTrace, handoffSpace, handedHeap, handedOutput, handedStack, handedPC,
      handedRunning, handedZero, handedTable, handedInverse⟩ :=
    SharedDetectorSteps.handoff_execution program prepared (handoffEntry parameters graph entry) (EnumerationUniformPrepared.tableBase graph)
      (EnumerationUniformPrepared.inverseBase graph) graph.roots.length (SharedDetectorPrepared.packetSize graph)
      (by rw [setupPC, EnumerationUniformPrepared.setupWords_length, eH]) setupRunning (by omega) handoffAt
  have handedSize : handed.heap.size = EnumerationUniformPrepared.preparedSize graph := by rw [handedHeap]; exact preparedLength
  -- Returning scan.
  have scanCodeEq : scanCode parameters graph T F (EnumerationUniformScan.Width parameters graph retained) entry =
      EnumerationUniformLoop.code (trueBase := EnumerationUniformPrepared.trueBase graph) (falseBase := EnumerationUniformPrepared.falseBase graph) parameters graph T F (Array.replicate (EnumerationUniformPrepared.preparedSize graph) (word (EnumerationUniformScan.Width parameters graph retained) 0))
        (EnumerationUniformPrepared.layout graph _ (by simp)) (EnumerationUniformPrepared.coordinateBase graph) (EnumerationUniformPrepared.slot graph) graph.roots.length
        (scanEntry parameters graph entry) (teardownEntry parameters graph T F (EnumerationUniformScan.Width parameters graph retained) entry) root := by
    unfold scanCode; rw [head]
  have sameCode := EnumerationUniformLoop.shared (trueBase := EnumerationUniformPrepared.trueBase graph) (falseBase := EnumerationUniformPrepared.falseBase graph) parameters graph T F
    (Array.replicate (EnumerationUniformPrepared.preparedSize graph) (word (EnumerationUniformScan.Width parameters graph retained) 0)) handed.heap
    (EnumerationUniformPrepared.layout graph _ (by simp)) (EnumerationUniformPrepared.layout graph handed.heap.size handedSize)
    (EnumerationUniformPrepared.coordinateBase graph) (EnumerationUniformPrepared.slot graph) graph.roots.length (scanEntry parameters graph entry)
    (teardownEntry parameters graph T F (EnumerationUniformScan.Width parameters graph retained) entry) root root (by simp [handedSize]) rfl rfl
  have scanPresent : SharedRootRead.BlockAt program (scanEntry parameters graph entry)
      (EnumerationUniformLoop.code (trueBase := EnumerationUniformPrepared.trueBase graph) (falseBase := EnumerationUniformPrepared.falseBase graph) parameters graph T F handed.heap (EnumerationUniformPrepared.layout graph handed.heap.size handedSize)
        (EnumerationUniformPrepared.coordinateBase graph) (EnumerationUniformPrepared.slot graph) graph.roots.length (scanEntry parameters graph entry)
        (teardownEntry parameters graph T F (EnumerationUniformScan.Width parameters graph retained) entry) root) := by
    rw [← sameCode, ← scanCodeEq]; exact scanAt
  have scanRoom : scanEntry parameters graph entry + (EnumerationUniformLoop.code (trueBase := EnumerationUniformPrepared.trueBase graph) (falseBase := EnumerationUniformPrepared.falseBase graph) parameters graph T F handed.heap
      (EnumerationUniformPrepared.layout graph handed.heap.size handedSize) (EnumerationUniformPrepared.coordinateBase graph) (EnumerationUniformPrepared.slot graph) graph.roots.length
      (scanEntry parameters graph entry) (teardownEntry parameters graph T F (EnumerationUniformScan.Width parameters graph retained) entry) root).length ≤ retained := by
    rw [← sameCode, ← scanCodeEq]; omega
  have ready := EnumerationUniformPrepared.scan_ready parameters graph guarded T F consistent retained (scanEntry parameters graph entry)
    (teardownEntry parameters graph T F (EnumerationUniformScan.Width parameters graph retained) entry)
    program (SharedRetainedCandidates.masks (EnumerationUniformScan.Width parameters graph retained) (assignmentOfSet (extensionBase parameters.buses parameters.bridge.target T))
      ((List.finRange parameters.channels).map (assignmentOfSet F)) ++ suffix)
    candidated.heap root handed packetLength
    (by rw [candidateHeap]; exact SharedDetectorPrepared.packet_channels graph rows roots _)
    (by rw [candidateHeap]; exact SharedDetectorPrepared.packet_nodes graph rows roots matched _)
    (by intro channel; rw [candidateHeap]; exact SharedDetectorPrepared.packet_mask graph rows roots matched rootMatches _ channel)
    (by rw [handedHeap, preparedEq])
    handedSize
    (by rw [handedStack, setupStack, retentionStack, directoryStack])
    (by rw [handedPC, eL]) handedRunning handedZero handedTable handedInverse
    (by omega) scanRoom scanPresent
  obtain ⟨answer, scanned, scanTicks, scanPeak, scanTrace, scanRunning, scanPC, decision, scanStack, scanOutput,
      scanKept, scanTime, scanSpace, meaning⟩ :=
    EnumerationUniformScan.execution (trueBase := EnumerationUniformPrepared.trueBase graph) (falseBase := EnumerationUniformPrepared.falseBase graph) parameters graph guarded T F consistent retained (EnumerationUniformPrepared.coordinateBase graph)
      (EnumerationUniformPrepared.slot graph) (EnumerationUniformPrepared.slot graph + 1) graph.roots.length (SharedDetectorPrepared.maskBase graph) (scanEntry parameters graph entry)
      (teardownEntry parameters graph T F (EnumerationUniformScan.Width parameters graph retained) entry) program _ (List.finRange graph.roots.length) handed
      (SharedDetectorPrepared.packetSize graph) ready
  -- Teardown: release the prepared region.
  have scanHeap : scanned.heap = candidated.heap ++ scanned.heap.extract candidated.heap.size scanned.heap.size := by
    have kept : EnumerationUniformScan.Kept (EnumerationUniformPrepared.slot graph) (EnumerationUniformPrepared.preparedHeap (maskB := extensionBase parameters.buses parameters.bridge.target T) (maskF := F) candidated.heap graph
        ((List.finRange graph.roots.length).map
          (SharedWitnessDecode.tag graph (extensionBase parameters.buses parameters.bridge.target T) F (EnumerationUniformScan.Width parameters graph retained))) root.val)
        scanned.heap := by
      rw [← preparedEq, ← handedHeap]; exact scanKept
    exact kept_split (maskB := extensionBase parameters.buses parameters.bridge.target T) (maskF := F) candidated.heap scanned.heap graph _ root.val (EnumerationUniformPrepared.slot graph) packetLength tagCount (by omega) kept
  have scannedSize : scanned.heap.size = EnumerationUniformPrepared.preparedSize graph := by rw [scanKept.1, handedSize]
  have releaseCount : (scanned.heap.extract candidated.heap.size scanned.heap.size).toList.length =
      2 * graph.roots.length + 2 * parameters.channels + 3 * (parameters.channels + graph.nodeCount) + 1 := by
    simp only [Array.length_toList, Array.size_extract, scannedSize, packetLength]; omega
  have cacheSize : (cacheHeap (EnumerationUniformScan.Width parameters graph retained) (packetHeaderHeap (EnumerationUniformScan.Width parameters graph retained) parameters.channels rows roots) rows roots).size =
      SharedDetectorPrepared.maskBase graph := by
    obtain ⟨children, guards⟩ := matched_incidence_lengths graph rows matched
    simp only [cacheHeap_size, packetHeaderHeap_size, matched.length_eq, children, guards, rootCount, SharedDetectorPrepared.maskBase, SharedDetectorPrepared.rootBase]
  have teardownPresent : SharedRootRead.BlockAt program (teardownEntry parameters graph T F (EnumerationUniformScan.Width parameters graph retained) entry)
      ((SharedEvaluationReclaim.code (EnumerationUniformScan.Width parameters graph retained) (teardownEntry parameters graph T F (EnumerationUniformScan.Width parameters graph retained) entry)
        (teardownEntry parameters graph T F (EnumerationUniformScan.Width parameters graph retained) entry + 7)
        (scanned.heap.extract candidated.heap.size scanned.heap.size).toList.length).toList ++
      (pushCode (EnumerationUniformScan.Width parameters graph retained) ((List.finRange parameters.channels).map
        (fun channel => boolWord (EnumerationUniformScan.Width parameters graph retained) (assignmentOfSet {parameters.bridge.target} channel))) ++
      (SharedChannelRewrite.code (EnumerationUniformScan.Width parameters graph retained)
        (cacheHeap (EnumerationUniformScan.Width parameters graph retained) (packetHeaderHeap (EnumerationUniformScan.Width parameters graph retained) parameters.channels rows roots) rows roots).size
        (List.finRange parameters.channels) ++
      [.constant 0 (word (EnumerationUniformScan.Width parameters graph retained) 0), .branchZero 0 (word (EnumerationUniformScan.Width parameters graph retained) back)]))) := by
    have whole := teardownAt
    unfold teardownCode healthyWords at whole
    rw [releaseCount, cacheSize]; exact whole
  have scannedStored : scanned.heap = withValues
      (cacheHeap (EnumerationUniformScan.Width parameters graph retained) (packetHeaderHeap (EnumerationUniformScan.Width parameters graph retained) parameters.channels rows roots) rows roots)
      (assignmentOfSet (extensionBase parameters.buses parameters.bridge.target T)) ++
      (scanned.heap.extract candidated.heap.size scanned.heap.size).toList.toArray := by
    rw [Array.toArray_toList]
    have packetEq : candidated.heap = withValues
        (cacheHeap (EnumerationUniformScan.Width parameters graph retained)
          (packetHeaderHeap (EnumerationUniformScan.Width parameters graph retained) parameters.channels rows roots) rows roots)
        (assignmentOfSet (extensionBase parameters.buses parameters.bridge.target T)) := candidateHeap
    exact scanHeap.trans (congrArg
      (fun packet => packet ++ scanned.heap.extract candidated.heap.size scanned.heap.size) packetEq)
  obtain ⟨final, teardownPeak, teardownTrace, teardownSpace, finalHeap, finalStack, finalOutput, finalPC,
      finalRunning, finalHead⟩ :=
    teardown_execution program scanned (teardownEntry parameters graph T F (EnumerationUniformScan.Width parameters graph retained) entry) back
      (cacheHeap (EnumerationUniformScan.Width parameters graph retained) (packetHeaderHeap (EnumerationUniformScan.Width parameters graph retained) parameters.channels rows roots) rows roots)
      (assignmentOfSet (extensionBase parameters.buses parameters.bridge.target T))
      (assignmentOfSet {parameters.bridge.target})
      (scanned.heap.extract candidated.heap.size scanned.heap.size).toList scanPC scanRunning
      (by omega) (by rw [cacheSize]; omega) (by rw [releaseCount]; omega) scannedStored teardownPresent
  -- Composition and accounting.
  have finalDecision : final.reg 4 = word (EnumerationUniformScan.Width parameters graph retained) (if answer then 1 else 0) := by
    rw [finalHead]; exact decision
  have restoredHeap : final.heap = state.heap := by
    rw [finalHeap, heapStored]; rfl
  have restoredStack : final.stack = state.stack := by
    rw [finalStack, scanStack, input]
  have restoredOutput : final.output = state.output := by
    rw [finalOutput, scanOutput, handedOutput, setupOutput, retentionOutput, directoryOutput, candidateOutput, guardOutput]
  have packetState : state.heap.size = SharedDetectorPrepared.packetSize graph := by
    rw [heapStored]; exact SharedDetectorPrepared.packet_size graph rows roots matched rootMatches _
  have stackState : state.stack.length = 2 * parameters.channels + suffix.length := by
    rw [input]; simp; omega
  have foldLength : (SharedHeadLoop.witnessFold graph
      (assignmentOfSet (extensionBase parameters.buses parameters.bridge.target T)) 0
      ((List.finRange parameters.channels).map (assignmentOfSet F))
      (SharedBaselineInitialize.witnesses graph
        (assignmentOfSet (extensionBase parameters.buses parameters.bridge.target T)) (EnumerationUniformScan.Width parameters graph retained))).length =
      graph.roots.length := by rw [foldEq]; simp
  have referenceLength : (SharedHealthyReference.reference graph parameters.bridge.target (EnumerationUniformScan.Width parameters graph retained)).length =
      graph.roots.length := by simp [SharedHealthyReference.reference]
  have masksLength : (SharedRetainedCandidates.masks (EnumerationUniformScan.Width parameters graph retained)
      (assignmentOfSet (extensionBase parameters.buses parameters.bridge.target T))
      ((List.finRange parameters.channels).map (assignmentOfSet F))).length = 2 * parameters.channels := by
    simp; omega
  have stateUnfold : state.liveWords = 8 + state.heap.size + state.stack.length + state.output.length + 1 := rfl
  have candidatedLive : candidated.liveWords = state.liveWords + 2 * graph.roots.length := by
    have stackLength : candidated.stack.length =
        graph.roots.length + graph.roots.length + (2 * parameters.channels + suffix.length) := by
      rw [candidateStack]; simp only [List.length_append, foldLength, referenceLength, masksLength]; omega
    have outputSame : candidated.output.length = state.output.length := by rw [candidateOutput, guardOutput]
    have unfold' : candidated.liveWords = 8 + candidated.heap.size + candidated.stack.length + candidated.output.length + 1 := rfl
    omega
  have directedLive : directed.liveWords = state.liveWords + 3 * graph.roots.length := by
    have heapSize : directed.heap.size = SharedDetectorPrepared.packetSize graph + 2 * graph.roots.length := by
      rw [directoryHeap]; simp only [Array.size_append, List.size_toArray, EnumerationUniformPrepared.rootWords_length, tagCount, packetLength]
      omega
    have stackLength : directed.stack.length = graph.roots.length + (2 * parameters.channels + suffix.length) := by
      rw [directoryStack]; simp only [List.length_append, referenceLength, masksLength]
    have outputSame : directed.output.length = state.output.length := by
      rw [directoryOutput, candidateOutput, guardOutput]
    have unfold' : directed.liveWords = 8 + directed.heap.size + directed.stack.length + directed.output.length + 1 := rfl
    omega
  have retainedLive : retainedState.liveWords = directed.liveWords + 2 * parameters.channels := by
    unfold State.liveWords
    rw [retentionHeap, retentionStack, retentionOutput]
    simp only [Array.size_append, List.size_toArray, retainedMasksLength]
    omega
  have preparedLive : prepared.liveWords = state.liveWords + 3 * graph.roots.length + 2 * parameters.channels +
      (3 * (parameters.channels + graph.nodeCount) + 1) := by
    have heapSize : prepared.heap.size = retainedState.heap.size + (3 * (parameters.channels + graph.nodeCount) + 1) := by
      rw [setupHeap]; simp only [Array.size_append, List.size_toArray, EnumerationUniformPrepared.setupWords_length]
    have retainedBudget : retainedState.liveWords = state.liveWords + 3 * graph.roots.length + 2 * parameters.channels := by omega
    simp only [State.liveWords, heapSize, setupStack, setupOutput] at retainedBudget ⊢
    omega
  have handedLive : handed.liveWords = state.liveWords + 3 * graph.roots.length + 2 * parameters.channels +
      (3 * (parameters.channels + graph.nodeCount) + 1) + 2 := by
    simp only [State.liveWords, handedHeap, handedStack, handedOutput, List.length_cons] at preparedLive ⊢
    omega
  have scannedLive : scanned.liveWords = state.liveWords +
      (2 * graph.roots.length + 2 * parameters.channels + 3 * (parameters.channels + graph.nodeCount) + 1) := by
    have unfold' : scanned.liveWords = 8 + scanned.heap.size + scanned.stack.length + scanned.output.length + 1 := rfl
    have heapSize : scanned.heap.size = state.heap.size +
        (2 * graph.roots.length + 2 * parameters.channels + 3 * (parameters.channels + graph.nodeCount) + 1) := by
      rw [scannedSize, packetState, preparedValue, coordinateValue]; omega
    have stackSame : scanned.stack.length = state.stack.length := by rw [scanStack, input]
    have outputSame : scanned.output.length = state.output.length := by
      rw [scanOutput, handedOutput, setupOutput, retentionOutput, directoryOutput, candidateOutput, guardOutput]
    omega
  have guardedStack : guarded'.stack.length = 2 * parameters.channels + suffix.length := by
    rw [guardStack]; exact stackState
  have guardedOutput : guarded'.output.length = state.output.length := by rw [guardOutput]
  rw [guardedStack, guardedOutput] at candidateSpace
  rw [candidatedLive, tagCount] at directorySpace
  rw [directedLive, retainedMasksLength] at retentionSpace
  rw [preparedLive] at handoffSpace
  rw [handedLive] at scanSpace
  rw [scannedLive] at teardownSpace
  simp only [List.length_finRange] at scanTime
  have setupCount : (EnumerationUniformPrepared.setupWords (EnumerationUniformScan.Width parameters graph retained) graph root.val).length = 3 * (parameters.channels + graph.nodeCount) + 1 := by
    simp only [EnumerationUniformPrepared.setupWords_length]
  simp only [SharedHealthyReference.reference, List.length_map, retainedMasksLength] at retentionTime
  have joined := guardTrace.append (candidateTrace.append (directoryTrace.append (retentionTrace.append (setupTrace.append
    (handoffTrace.append (scanTrace.append teardownTrace))))))
  refine ⟨answer, final, _, _, joined, finalRunning, finalPC, finalDecision, restoredHeap, restoredStack, restoredOutput,
    ?_, ?_, ?_⟩
  · have channelRoom : parameters.channels * (84 * graph.countedSize + 54) + parameters.channels * 5 ≤
        parameters.channels * (8000 * (graph.countedSize + 1)) := by
      rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ (by omega)
    have outputRoom : graph.roots.length * (7000 * (graph.countedSize + 1)) + graph.roots.length * 18 ≤
        graph.roots.length * (8000 * (graph.countedSize + 1)) := by
      rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ (by omega)
    simp only [tagCount, setupCount, releaseCount]
    clear * - guardTime candidateTime retentionTime scanTime rootCount setupCount size channelRoom outputRoom
    rw [Nat.add_mul, Nat.add_mul, Nat.one_mul]
    omega
  · have setupPeak : retainedState.liveWords + (EnumerationUniformPrepared.setupWords (EnumerationUniformScan.Width parameters graph retained) graph root.val).length ≤
        state.liveWords + 240 * (graph.countedSize + 1) := by
      rw [retainedLive, directedLive, setupCount]; omega
    clear * - guardTime candidateSpace directorySpace retentionSpace handoffSpace scanSpace teardownSpace setupPeak stackState size
    simp only [max_le_iff]
    refine ⟨by omega, by simp only [State.liveWords] at stackState ⊢; omega, by omega, by omega, setupPeak, by omega,
      by omega, by omega⟩
  · rw [meaning]
    constructor
    · rintro ⟨output, _, feasible⟩; exact ⟨output, feasible⟩
    · rintro ⟨output, feasible⟩; exact ⟨output, List.mem_finRange output, feasible⟩

end Execution


end Controller.Cost.EnumerationUniformOracle
