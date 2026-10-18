module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.EnumerationUniformPrepared
public import Controller.Cost.EnumerationMaskRetention

@[expose] public section

/-! One fixed returning detection oracle with retained runtime prefix masks. -/
namespace Controller.Cost.EnumerationUniformOracle
open Controller.Cost.GateProgram Controller.Cost.RawTransferLoops Controller.Cost.EnumerationOracle

section Code
open Controller.Cost.SharedDetectorAssembly
open Controller.Decoder Controller.Decoder.DAG Controller.Cost.ForestIndexedOperands
open Controller.Native Controller.Native.SourceController Controller.Cost.NativeSourceExecution
open Controller.Cost.SharedDetectorPrepared Controller.Cost.EnumerationUniformPrepared
variable (parameters : Parameters) (graph : DAG parameters.channels) (T F : Finset (Fin parameters.channels))

def candidatesEntry (entry : Nat) : Nat := entry + 8

def directoryEntry (entry : Nat) : Nat :=
  candidatesEntry entry + (10 * graph.roots.length + 14 * parameters.channels + 620)

def retentionEntry (entry : Nat) : Nat := directoryEntry parameters graph entry + (4 * graph.roots.length + 11)

def setupEntry (entry : Nat) : Nat := retentionEntry parameters graph entry + 3 * graph.roots.length + 4 * parameters.channels + 10

def handoffEntry (entry : Nat) : Nat :=
  setupEntry parameters graph entry + 2 * (3 * (parameters.channels + graph.nodeCount) + 1)

def scanEntry (entry : Nat) : Nat := handoffEntry parameters graph entry + 7

/-- First instruction after the scan; the scan's own length does not depend on its return address. -/
def teardownEntry (width entry : Nat) : Nat :=
  match graph.roots.head? with
  | none => scanEntry parameters graph entry
  | some root => EnumerationUniformLoop.returnPoint (trueBase := EnumerationUniformPrepared.trueBase graph) (falseBase := EnumerationUniformPrepared.falseBase graph) parameters graph T F (EnumerationUniformPrepared.preparedSize graph) (EnumerationUniformPrepared.coordinateBase graph)
      (EnumerationUniformPrepared.slot graph) (scanEntry parameters graph entry) root width + 8

def scanCode (width entry : Nat) : List (Instruction width 8) :=
  match graph.roots.head? with
  | none => []
  | some root => EnumerationUniformLoop.code (trueBase := EnumerationUniformPrepared.trueBase graph) (falseBase := EnumerationUniformPrepared.falseBase graph) parameters graph T F (Array.replicate (EnumerationUniformPrepared.preparedSize graph) (word width 0))
      (EnumerationUniformPrepared.layout graph _ (by simp)) (EnumerationUniformPrepared.coordinateBase graph) (EnumerationUniformPrepared.slot graph) graph.roots.length
      (scanEntry parameters graph entry) (teardownEntry parameters graph T F width entry) root

theorem scanCode_length (width entry : Nat) :
    scanEntry parameters graph entry + (scanCode parameters graph T F width entry).length =
      teardownEntry parameters graph T F width entry := by
  unfold scanCode teardownEntry
  split
  · simp
  · rw [EnumerationUniformLoop.code_length]; simp

/-- The healthy singleton channel words written back by the teardown. -/
def healthyWords (width : Nat) : List (Word width) :=
  (List.finRange parameters.channels).map (fun channel =>
    boolWord width (assignmentOfSet {parameters.bridge.target} channel))

def teardownCode (width entry back : Nat) : List (Instruction width 8) :=
  (SharedEvaluationReclaim.code width (teardownEntry parameters graph T F width entry)
    (teardownEntry parameters graph T F width entry + 7)
    (2 * graph.roots.length + 2 * parameters.channels + 3 * (parameters.channels + graph.nodeCount) + 1)).toList ++
  (pushCode width (healthyWords parameters width) ++
  (SharedChannelRewrite.code width (SharedDetectorPrepared.maskBase graph) (List.finRange parameters.channels) ++
  [.constant 0 (word width 0), .branchZero 0 (word width back)]))

@[simp] theorem teardownCode_length (width entry back : Nat) :
    (teardownCode parameters graph T F width entry back).length = 5 * parameters.channels + 9 := by
  simp [teardownCode, healthyWords, SharedEvaluationReclaim.code]; omega

/-- The complete resident oracle at `entry`, returning to `back`. -/
@[irreducible] def code (width : Nat) (rows : List Row) (roots : List Nat) (entry back : Nat) : List (Instruction width 8) :=
  guardCode width entry back ++
    ((SharedRetainedCandidates.code width parameters.channels rows roots (candidatesEntry entry)
      (directoryEntry parameters graph entry)).toList ++
    (SharedDetectorDirectoryAlloc.code width (SharedDetectorPrepared.packetSize graph) (SharedDetectorPrepared.rootBase graph) graph.roots.length
      (directoryEntry parameters graph entry) ++
    (EnumerationMaskRetention.code width (retentionEntry parameters graph entry) (EnumerationUniformPrepared.trueBase graph)
      (2 * parameters.channels) (SharedHealthyReference.reference graph parameters.bridge.target width) ++
    (SharedCoordinateTable.code width (EnumerationUniformPrepared.setupWords width graph (SharedDetectorAssembly.firstRoot parameters graph)) ++
    (SharedDetectorSteps.handoffCode width (EnumerationUniformPrepared.tableBase graph) (EnumerationUniformPrepared.inverseBase graph) graph.roots.length (SharedDetectorPrepared.packetSize graph) ++
    (scanCode parameters graph T F width entry ++ teardownCode parameters graph T F width entry back))))))

theorem code_length (width : Nat) (rows : List Row) (roots : List Nat) (entry back : Nat)
    (rootMatches : RootsMatch graph roots) :
    entry + (code parameters graph T F width rows roots entry back).length =
      teardownEntry parameters graph T F width entry + (5 * parameters.channels + 9) := by
  have rootCount : roots.length = graph.roots.length := by rw [rootMatches]; simp
  have scanEnd := scanCode_length parameters graph T F width entry
  simp only [code, List.length_append, Array.length_toList, SharedRetainedCandidates.code_size, rootCount,
    SharedDetectorDirectoryAlloc.code_length, SharedCoordinateTable.code_length, EnumerationUniformPrepared.setupWords_length,
    guardCode_length, SharedDetectorSteps.handoffCode_length, teardownCode_length,
    scanEntry, handoffEntry, setupEntry, retentionEntry, directoryEntry, candidatesEntry, EnumerationMaskRetention.code_length,
    SharedHealthyReference.reference, List.length_map] at scanEnd ⊢
  omega

theorem teardownEntry_bound (width entry : Nat) :
    teardownEntry parameters graph T F width entry ≤ entry + 600 * (graph.countedSize + 1) + 1600 := by
  have size := graph.countedSize_eq
  have scanEnd := scanCode_length parameters graph T F width entry
  have scanBound : (scanCode parameters graph T F width entry).length ≤ 403 * (graph.countedSize + 1) + 604 := by
    unfold scanCode
    split
    · simp
    · exact EnumerationUniformLoop.code_length_bound (trueBase := EnumerationUniformPrepared.trueBase graph) (falseBase := EnumerationUniformPrepared.falseBase graph) parameters graph T F _ _ _ _ _ _ _ _
  simp only [scanEntry, handoffEntry, setupEntry, retentionEntry, directoryEntry, candidatesEntry] at scanEnd
  omega

structure Physical (width : Nat) (rows : List Row) (roots : List Nat) (entry back : Nat)
    (program : Program width 8) : Prop where
  guardAt : SharedRootRead.BlockAt program entry (guardCode width entry back)
  candidatesAt : CodeAt program (candidatesEntry entry)
    (SharedRetainedCandidates.code width parameters.channels rows roots (candidatesEntry entry) (directoryEntry parameters graph entry))
  directoryAt : SharedRootRead.BlockAt program (directoryEntry parameters graph entry)
    (SharedDetectorDirectoryAlloc.code width (SharedDetectorPrepared.packetSize graph) (SharedDetectorPrepared.rootBase graph)
      graph.roots.length (directoryEntry parameters graph entry))
  retentionAt : SharedRootRead.BlockAt program (retentionEntry parameters graph entry)
    (EnumerationMaskRetention.code width (retentionEntry parameters graph entry) (EnumerationUniformPrepared.trueBase graph)
      (2 * parameters.channels) (SharedHealthyReference.reference graph parameters.bridge.target width))
  setupAt : SharedRootRead.BlockAt program (setupEntry parameters graph entry)
    (SharedCoordinateTable.code width (EnumerationUniformPrepared.setupWords width graph (SharedDetectorAssembly.firstRoot parameters graph)))
  handoffAt : SharedRootRead.BlockAt program (handoffEntry parameters graph entry)
    (SharedDetectorSteps.handoffCode width (EnumerationUniformPrepared.tableBase graph) (EnumerationUniformPrepared.inverseBase graph)
      graph.roots.length (SharedDetectorPrepared.packetSize graph))
  scanAt : SharedRootRead.BlockAt program (scanEntry parameters graph entry) (scanCode parameters graph T F width entry)
  teardownAt : SharedRootRead.BlockAt program (teardownEntry parameters graph T F width entry)
    (teardownCode parameters graph T F width entry back)

set_option maxHeartbeats 400000 in
theorem physical_at (width : Nat) (rows : List Row) (roots : List Nat) (entry back : Nat)
    (program : Program width 8) (rootMatches : RootsMatch graph roots)
    (present : SharedRootRead.BlockAt program entry (code parameters graph T F width rows roots entry back)) :
    Physical parameters graph T F width rows roots entry back program := by
  have rootCount : roots.length = graph.roots.length := by rw [rootMatches]; simp
  have scanEnd := scanCode_length parameters graph T F width entry
  have eC : candidatesEntry entry = entry + 8 := rfl
  have eD : directoryEntry parameters graph entry =
      entry + 8 + (10 * graph.roots.length + 14 * parameters.channels + 620) := rfl
  have eR : retentionEntry parameters graph entry = directoryEntry parameters graph entry + (4 * graph.roots.length + 11) := rfl
  have eS : setupEntry parameters graph entry = retentionEntry parameters graph entry + 3 * graph.roots.length + 4 * parameters.channels + 10 := rfl
  have eH : handoffEntry parameters graph entry =
      setupEntry parameters graph entry + 2 * (3 * (parameters.channels + graph.nodeCount) + 1) := rfl
  have eL : scanEntry parameters graph entry = handoffEntry parameters graph entry + 7 := rfl
  -- Code segments.
  unfold code at present
  have guardAt := block_left program entry _ _ present
  have afterGuard := block_right program entry _ _ present
  have candidatesAt : CodeAt program (candidatesEntry entry)
      (SharedRetainedCandidates.code (width) parameters.channels rows roots (candidatesEntry entry)
        (directoryEntry parameters graph entry)) :=
    block_code program _ _ (block_move program (block_left program _ _ _ afterGuard) (by simp [candidatesEntry]))
  have afterCandidates := block_right program _ _ _ afterGuard
  have directoryAt : SharedRootRead.BlockAt program (directoryEntry parameters graph entry)
      (SharedDetectorDirectoryAlloc.code (width) (SharedDetectorPrepared.packetSize graph) (SharedDetectorPrepared.rootBase graph) graph.roots.length
        (directoryEntry parameters graph entry)) :=
    block_move program (block_left program _ _ _ afterCandidates) (by simp [rootCount]; omega)
  have afterDirectory := block_right program _ _ _ afterCandidates
  have retentionAt : SharedRootRead.BlockAt program (retentionEntry parameters graph entry)
      (EnumerationMaskRetention.code (width) (retentionEntry parameters graph entry)
        (EnumerationUniformPrepared.trueBase graph) (2 * parameters.channels)
        (SharedHealthyReference.reference graph parameters.bridge.target (width))) :=
    block_move program (block_left program _ _ _ afterDirectory) (by simp [rootCount]; omega)
  have afterRetention := block_right program _ _ _ afterDirectory
  have setupAt : SharedRootRead.BlockAt program (setupEntry parameters graph entry)
      (SharedCoordinateTable.code (width) (EnumerationUniformPrepared.setupWords (width) graph (firstRoot parameters graph))) :=
    block_move program (block_left program _ _ _ afterRetention) (by
        simp [rootCount, eS, SharedHealthyReference.reference]; omega)
  have afterSetup := block_right program _ _ _ afterRetention
  have handoffAt : SharedRootRead.BlockAt program (handoffEntry parameters graph entry)
      (SharedDetectorSteps.handoffCode (width) (EnumerationUniformPrepared.tableBase graph) (EnumerationUniformPrepared.inverseBase graph) graph.roots.length (SharedDetectorPrepared.packetSize graph)) :=
    block_move program (block_left program _ _ _ afterSetup) (by simp [rootCount]; omega)
  have afterHandoff := block_right program _ _ _ afterSetup
  have scanAt : SharedRootRead.BlockAt program (scanEntry parameters graph entry)
      (scanCode parameters graph T F (width) entry) :=
    block_move program (block_left program _ _ _ afterHandoff) (by simp [rootCount]; omega)
  have teardownAt : SharedRootRead.BlockAt program (teardownEntry parameters graph T F (width) entry)
      (teardownCode parameters graph T F (width) entry back) :=
    block_move program (block_right program _ _ _ afterHandoff) (by simp [rootCount]; omega)
  exact ⟨guardAt, candidatesAt, directoryAt, retentionAt, setupAt, handoffAt, scanAt, teardownAt⟩

end Code

theorem kept_split (maskB maskF : Finset (Fin n)) (packet heap : Array (Word width)) (graph : Controller.Decoder.DAG n) (tags : List (Word width))
    (root slotBound : Nat) (packetLength : packet.size = SharedDetectorPrepared.packetSize graph) (tagCount : tags.length = graph.roots.length)
    (below : SharedDetectorPrepared.packetSize graph ≤ slotBound)
    (kept : EnumerationUniformScan.Kept slotBound (EnumerationUniformPrepared.preparedHeap (maskB := maskB) (maskF := maskF) packet graph tags root) heap) :
    heap = packet ++ heap.extract packet.size heap.size := by
  have total := EnumerationUniformPrepared.preparedHeap_size (maskB := maskB) (maskF := maskF) packet graph tags root packetLength tagCount
  have preparedBound : SharedDetectorPrepared.packetSize graph ≤ EnumerationUniformPrepared.preparedSize graph := by
    rw [EnumerationUniformPrepared.preparedSize_eq, EnumerationUniformPrepared.coordinateBase]; omega
  apply Array.ext
  · simp only [Array.size_append, Array.size_extract]
    rw [kept.1, total]; omega
  · intro index left right
    by_cases inPacket : index < packet.size
    · rw [Array.getElem_append_left inPacket]
      have cell := kept.2 index (by omega)
      rw [EnumerationUniformPrepared.preparedHeap_prefix (maskB := maskB) (maskF := maskF) packet graph tags root index inPacket, Array.getElem?_eq_getElem left,
        Array.getElem?_eq_getElem inPacket] at cell
      exact Option.some.inj cell
    · rw [Array.getElem_append_right (by omega)]
      simp only [Array.getElem_extract]
      congr 1
      omega


end Controller.Cost.EnumerationUniformOracle
