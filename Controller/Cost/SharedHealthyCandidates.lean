module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedCandidateBatch

@[expose] public section

/-! The singleton reference, baseline mask and all head probes use one resident graph heap. -/
namespace Controller.Cost.SharedHealthyCandidates
open Controller.Decoder Controller.Decoder.DAG Controller.Cost.GateProgram
open Controller.Cost.ForestIndexedOperands Controller.Cost.UniformDAGSource
open Controller.Cost.UniformDAGRun Controller.Cost.ForestInputPrefixStored
open Controller.Cost.RawTransferLoops Controller.Cost.ForestInputStored

@[irreducible] def code (width n : Nat) (rows : List Row) (roots : List Nat) (entry done : Nat) : Program width 8 :=
  SharedHealthyBaseline.code width n rows roots entry (entry + 4 * roots.length + 3 * n + 184) ++
    (SharedStackRotate.code width (SharedReusableProbe.tableSize width n rows roots) roots.length n
      (entry + 4 * roots.length + 3 * n + 184) (entry + 6 * roots.length + 5 * n + 211) ++
      SharedCandidateBatch.code width n rows roots (entry + 6 * roots.length + 5 * n + 211) done)

@[simp] theorem code_size (width n : Nat) (rows : List Row) (roots : List Nat) (entry done : Nat) :
    (code width n rows roots entry done).size = 10 * roots.length + 10 * n + 593 := by
  unfold code; simp; omega

set_option maxHeartbeats 2000000 in
theorem execution (resident : Program width 8) (state : State width 8)
    (graph : DAG n) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (heads : HeadsMatch graph rows matched)
    (rootMatches : RootsMatch graph roots) (target : Fin n) (baseline : Assignment n)
    (flags : List Bool) (suffix : List (Word width)) (entry done : Nat)
    (capacity : 256 * (graph.countedSize + 1) < 2 ^ width)
    (physical : CodeAt resident entry (code width n rows roots entry done))
    (room : entry + 10 * roots.length + 10 * n + 593 < 2 ^ width)
    (position : state.pc = word width entry) (running : state.halted = false)
    (heapStored : state.heap = channelHeap (packetHeaderHeap width n rows roots) rows roots
      (assignmentOfSet {target}))
    (input : state.stack = (List.finRange n).map (fun channel => boolWord width (baseline channel)) ++
      flags.map (boolWord width) ++ suffix)
    (flagCount : flags.length = n) (held : state.reg 4 = word width target.val) :
    ∃ final ticks peak, Execution resident state final ticks peak ∧
      ticks ≤ n * (84 * graph.countedSize + 54) + 180 * graph.countedSize + 76 ∧
      peak ≤ 10 * graph.countedSize + 18 + state.stack.length + state.output.length ∧
      final.heap = channelHeap (packetHeaderHeap width n rows roots) rows roots baseline ∧
      final.stack = SharedHeadLoop.witnessFold graph baseline 0 flags
        (SharedBaselineInitialize.witnesses graph baseline width) ++
        SharedHealthyReference.reference graph target width ++ suffix ∧
      final.output = state.output ∧ final.pc = word width done ∧ final.halted = false ∧
      final.reg 4 = word width n := by
  have all := physical
  unfold code at all
  have healthyCode := RawSharedOrdered.takePrefix resident entry _ _ all
  have tailCode := RawSharedOrdered.takeSuffix resident entry _ _ all
  have restCode : CodeAt resident (entry + 4 * roots.length + 3 * n + 184)
      (SharedStackRotate.code width (SharedReusableProbe.tableSize width n rows roots) roots.length n
        (entry + 4 * roots.length + 3 * n + 184) (entry + 6 * roots.length + 5 * n + 211) ++
        SharedCandidateBatch.code width n rows roots (entry + 6 * roots.length + 5 * n + 211) done) := by
    simpa [Nat.add_assoc] using tailCode
  have rotateCode := RawSharedOrdered.takePrefix resident (entry + 4 * roots.length + 3 * n + 184) _ _ restCode
  have batchCode := RawSharedOrdered.takeSuffix resident (entry + 4 * roots.length + 3 * n + 184) _ _ restCode
  have batchStored : CodeAt resident (entry + 6 * roots.length + 5 * n + 211)
      (SharedCandidateBatch.code width n rows roots (entry + 6 * roots.length + 5 * n + 211) done) := by
    have offsets : entry + 4 * roots.length + 3 * n + 184 +
        (2 * roots.length + 2 * n + 27) = entry + 6 * roots.length + 5 * n + 211 := by omega
    simpa only [SharedStackRotate.code_size, offsets] using batchCode
  obtain ⟨healthy, healthyTicks, healthyPeak, healthyTrace, healthyTime, healthySpace,
    healthyHeap, healthyStack, healthyOutput, healthyPC, healthyRunning, healthyHead⟩ :=
    SharedHealthyBaseline.execution resident state graph rows roots matched heads rootMatches target baseline
      (flags.map (boolWord width) ++ suffix) entry (entry + 4 * roots.length + 3 * n + 184)
      capacity healthyCode (by omega) position running heapStored
      (by simpa only [List.append_assoc] using input) held
  have rootCount : roots.length = graph.roots.length := by rw [rootMatches]; simp
  have size := graph.countedSize_eq
  obtain ⟨children, guards⟩ := matched_incidence_lengths graph rows matched
  have heapSize : (channelHeap (packetHeaderHeap width n rows roots) rows roots baseline).size =
      SharedReusableProbe.tableSize width n rows roots := by simp [SharedReusableProbe.tableSize]
  have tableSize : SharedReusableProbe.tableSize width n rows roots =
      5 + 6 * graph.nodeCount + graph.childIncidences + graph.guardIncidences + graph.roots.length + n := by
    simp only [SharedReusableProbe.tableSize, cacheHeap_size, packetHeaderHeap_size,
      matched.length_eq, children, guards, rootCount]
  obtain ⟨rotated, rotatePeak, rotateTrace, rotateSpace, rotateHeap, rotateStack,
    rotateOutput, rotatePC, rotateRunning, rotateHead⟩ :=
    SharedStackRotate.execution resident healthy
      (channelHeap (packetHeaderHeap width n rows roots) rows roots baseline)
      (SharedHealthyReference.reference graph target width) (flags.map (boolWord width)) suffix
      (entry + 4 * roots.length + 3 * n + 184) (entry + 6 * roots.length + 5 * n + 211)
      healthyPC healthyRunning
      (by simp only [SharedHealthyReference.reference_length, List.length_map, flagCount]; omega)
      (by rw [heapSize, tableSize]; omega)
      (by rw [heapSize, tableSize]; simp only [SharedHealthyReference.reference_length, List.length_map, flagCount]; omega)
      healthyHeap (by simpa only [List.append_assoc] using healthyStack)
      (by simpa only [heapSize, SharedHealthyReference.reference_length, rootCount, List.length_map, flagCount] using rotateCode)
  obtain ⟨final, batchTicks, batchPeak, batchTrace, batchTime, batchSpace,
    finalHeap, finalStack, finalOutput, finalPC, finalRunning, finalHead⟩ :=
    SharedCandidateBatch.execution resident rotated graph rows roots matched heads rootMatches baseline flags
      (SharedHealthyReference.reference graph target width ++ suffix)
      (entry + 6 * roots.length + 5 * n + 211) done capacity batchStored (by omega)
      rotatePC rotateRunning rotateHeap (by simpa only [List.append_assoc] using rotateStack) flagCount
  have initialSpace := SharedGraphRound.live_bound state graph rows roots matched rootMatches
    (assignmentOfSet {target}) heapStored
  have sameHeapSize : healthy.heap.size = state.heap.size := by
    rw [healthyHeap, heapStored]; simp
  have healthyLive : healthy.liveWords + n = state.liveWords + graph.roots.length := by
    simp only [State.liveWords, sameHeapSize, healthyStack, healthyOutput, input,
      List.length_append, List.length_map, List.length_finRange, SharedHealthyReference.reference_length]
    omega
  have rotatedStackSize : rotated.stack.length + n = state.stack.length + graph.roots.length := by
    simp only [rotateStack, input, List.length_append, List.length_map, List.length_finRange,
      SharedHealthyReference.reference_length]
    omega
  have joined := healthyTrace.append (rotateTrace.append batchTrace)
  refine ⟨final, healthyTicks + ((12 * ((SharedHealthyReference.reference graph target width).length +
      (flags.map (boolWord width)).length) + 14) + batchTicks), max healthyPeak (max rotatePeak batchPeak),
    joined, ?_, ?_, finalHeap.trans rotateHeap, ?_,
    finalOutput.trans (rotateOutput.trans healthyOutput), finalPC, finalRunning, finalHead⟩
  · simp only [SharedHealthyReference.reference_length, List.length_map, flagCount]; omega
  · simp only [SharedHealthyReference.reference_length, List.length_map, flagCount] at rotateSpace
    rw [rotateOutput, healthyOutput] at batchSpace
    apply Nat.max_le.mpr
    constructor
    · omega
    · apply Nat.max_le.mpr
      constructor <;> omega
  · simpa only [List.append_assoc] using finalStack

theorem code_bound (graph : DAG n) (width : Nat) (rows : List Row) (roots : List Nat)
    (rootMatches : RootsMatch graph roots) (entry done : Nat) :
    (code width n rows roots entry done).size ≤ 10 * graph.countedSize + 593 := by
  have size := graph.countedSize_eq
  have rootCount : roots.length = graph.roots.length := by rw [rootMatches]; simp
  rw [code_size, rootCount]
  omega

theorem working_bound (graph : DAG n) (state : State width 8) (rows : List Row) (roots : List Nat)
    (rootMatches : RootsMatch graph roots) (baseline : Assignment n)
    (flags : List Bool) (suffix : List (Word width)) (entry done peak : Nat)
    (input : state.stack = (List.finRange n).map (fun channel => boolWord width (baseline channel)) ++
      flags.map (boolWord width) ++ suffix) (flagCount : flags.length = n)
    (peakBound : peak ≤ 10 * graph.countedSize + 18 + state.stack.length + state.output.length) :
    peak + (code width n rows roots entry done).size ≤
      22 * graph.countedSize + 611 + suffix.length + state.output.length := by
  have instructions := code_bound graph width rows roots rootMatches entry done
  have size := graph.countedSize_eq
  rw [input] at peakBound
  simp only [List.length_append, List.length_map, List.length_finRange, flagCount] at peakBound
  omega

end Controller.Cost.SharedHealthyCandidates
