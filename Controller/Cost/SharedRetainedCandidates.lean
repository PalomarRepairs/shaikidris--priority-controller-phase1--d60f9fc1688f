module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedConstraintCopy
public import Controller.Cost.SharedHealthyCandidates

@[expose] public section

/-! One input-mask copy survives the shared candidate run for reuse by all zero queries. -/
namespace Controller.Cost.SharedRetainedCandidates
open Controller.Decoder Controller.Decoder.DAG Controller.Cost.GateProgram
open Controller.Cost.ForestIndexedOperands Controller.Cost.UniformDAGSource
open Controller.Cost.UniformDAGRun Controller.Cost.ForestInputPrefixStored
open Controller.Cost.RawTransferLoops Controller.Cost.ForestInputStored

def masks (width : Nat) (baseline : Assignment n) (flags : List Bool) : List (Word width) :=
  (List.finRange n).map (fun channel => boolWord width (baseline channel)) ++ flags.map (boolWord width)

@[simp] theorem masks_length (baseline : Assignment n) (flags : List Bool) :
    (masks width baseline flags).length = n + flags.length := by simp [masks]

@[irreducible] def code (width n : Nat) (rows : List Row) (roots : List Nat) (entry done : Nat) : Program width 8 :=
  SharedConstraintCopy.code width (SharedReusableProbe.tableSize width n rows roots) (2 * n)
    entry (entry + 4 * n + 27) ++
    SharedHealthyCandidates.code width n rows roots (entry + 4 * n + 27) done

@[simp] theorem code_size (width n : Nat) (rows : List Row) (roots : List Nat) (entry done : Nat) :
    (code width n rows roots entry done).size = 10 * roots.length + 14 * n + 620 := by
  unfold code; simp; omega

set_option maxHeartbeats 2000000 in
theorem execution (resident : Program width 8) (state : State width 8)
    (graph : DAG n) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (heads : HeadsMatch graph rows matched)
    (rootMatches : RootsMatch graph roots) (target : Fin n) (baseline : Assignment n)
    (flags : List Bool) (suffix : List (Word width)) (entry done : Nat)
    (capacity : 256 * (graph.countedSize + 1) < 2 ^ width)
    (physical : CodeAt resident entry (code width n rows roots entry done))
    (room : entry + 10 * roots.length + 14 * n + 620 < 2 ^ width)
    (position : state.pc = word width entry) (running : state.halted = false)
    (heapStored : state.heap = channelHeap (packetHeaderHeap width n rows roots) rows roots (assignmentOfSet {target}))
    (input : state.stack = masks width baseline flags ++ suffix)
    (flagCount : flags.length = n) (held : state.reg 4 = word width target.val) :
    ∃ final ticks peak, Execution resident state final ticks peak ∧
      ticks ≤ n * (84 * graph.countedSize + 54) + 216 * graph.countedSize + 90 ∧
      peak ≤ 12 * graph.countedSize + 18 + state.stack.length + state.output.length ∧
      final.heap = channelHeap (packetHeaderHeap width n rows roots) rows roots baseline ∧
      final.stack = SharedHeadLoop.witnessFold graph baseline 0 flags
        (SharedBaselineInitialize.witnesses graph baseline width) ++
        SharedHealthyReference.reference graph target width ++ masks width baseline flags ++ suffix ∧
      final.output = state.output ∧ final.pc = word width done ∧ final.halted = false ∧ final.reg 4 = word width n := by
  have all := physical
  unfold code at all
  have copyCode := RawSharedOrdered.takePrefix resident entry _ _ all
  have candidateCode := RawSharedOrdered.takeSuffix resident entry _ _ all
  have rootCount : roots.length = graph.roots.length := by rw [rootMatches]; simp
  have size := graph.countedSize_eq
  obtain ⟨children, guards⟩ := matched_incidence_lengths graph rows matched
  have heapSize : state.heap.size = SharedReusableProbe.tableSize width n rows roots := by
    rw [heapStored]; simp [SharedReusableProbe.tableSize]
  have tableSize : SharedReusableProbe.tableSize width n rows roots =
      5 + 6 * graph.nodeCount + graph.childIncidences + graph.guardIncidences + graph.roots.length + n := by
    simp only [SharedReusableProbe.tableSize, cacheHeap_size, packetHeaderHeap_size,
      matched.length_eq, children, guards, rootCount]
  have maskCount : (masks width baseline flags).length = 2 * n := by simp [flagCount]; omega
  obtain ⟨copied, copyPeak, copyTrace, copySpace, copiedHeap, copiedStack, copiedOutput,
    copiedPC, copiedRunning, copiedHead⟩ :=
    SharedConstraintCopy.execution resident state state.heap (masks width baseline flags) suffix entry (entry + 4 * n + 27)
      position running (by rw [maskCount]; omega) (by rw [heapSize, tableSize]; omega)
      (by rw [heapSize, tableSize, maskCount]; omega) rfl input
      (by simpa only [heapSize, maskCount] using copyCode)
  obtain ⟨final, candidateTicks, candidatePeak, candidateTrace, candidateTime, candidateSpace,
    finalHeap, finalStack, finalOutput, finalPC, finalRunning, finalHead⟩ :=
    SharedHealthyCandidates.execution resident copied graph rows roots matched heads rootMatches target baseline flags
      (masks width baseline flags ++ suffix) (entry + 4 * n + 27) done capacity
      (by
        have offsets : entry + (2 * (2 * n) + 27) = entry + 4 * n + 27 := by omega
        simpa only [SharedConstraintCopy.code_size, offsets] using candidateCode) (by omega) copiedPC copiedRunning
      (copiedHeap.trans heapStored) (by simpa only [masks, List.append_assoc] using copiedStack) flagCount
      (copiedHead.trans held)
  have copiedLive : copied.liveWords = state.liveWords + 2 * n := by
    simp only [State.liveWords, copiedHeap, copiedStack, copiedOutput, input, List.length_append, maskCount]
    omega
  have initialSpace := SharedGraphRound.live_bound state graph rows roots matched rootMatches
    (assignmentOfSet {target}) heapStored
  have joined := copyTrace.append candidateTrace
  refine ⟨final, (18 * (masks width baseline flags).length + 14) + candidateTicks,
    max copyPeak candidatePeak, joined, ?_, Nat.max_le.mpr ⟨?_, ?_⟩,
    finalHeap, ?_, finalOutput.trans copiedOutput, finalPC, finalRunning, finalHead⟩
  · rw [maskCount]; omega
  · rw [maskCount] at copySpace; omega
  · simp only [copiedStack, copiedOutput, input, List.length_append, maskCount] at candidateSpace ⊢
    omega
  · simpa only [List.append_assoc] using finalStack

end Controller.Cost.SharedRetainedCandidates
