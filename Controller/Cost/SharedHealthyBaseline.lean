module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedHealthyInitialize
public import Controller.Cost.SharedBaselineLoad

@[expose] public section

/-! The original singleton reference and baseline mask share one graph allocation. -/
namespace Controller.Cost.SharedHealthyBaseline
open Controller.Decoder Controller.Decoder.DAG Controller.Cost.GateProgram
open Controller.Cost.ForestIndexedOperands Controller.Cost.UniformDAGSource
open Controller.Cost.UniformDAGRun Controller.Cost.ForestInputPrefixStored
open Controller.Cost.RawTransferLoops Controller.Cost.ForestInputStored

@[irreducible] def code (width n : Nat) (rows : List Row) (roots : List Nat) (entry done : Nat) : Program width 8 :=
  SharedHealthyInitialize.code width n rows roots entry (entry + 2 * roots.length + 167) ++
    SharedBaselineLoad.code width (cacheHeap width (packetHeaderHeap width n rows roots) rows roots).size
      n roots.length (entry + 2 * roots.length + 167) done

@[simp] theorem code_size (width n : Nat) (rows : List Row) (roots : List Nat) (entry done : Nat) :
    (code width n rows roots entry done).size = 4 * roots.length + 3 * n + 184 := by
  unfold code; simp; omega

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem execution (resident : Program width 8) (state : State width 8)
    (graph : DAG n) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (heads : HeadsMatch graph rows matched)
    (rootMatches : RootsMatch graph roots) (target : Fin n) (baseline : Assignment n)
    (suffix : List (Word width)) (entry done : Nat)
    (capacity : 256 * (graph.countedSize + 1) < 2 ^ width)
    (physical : CodeAt resident entry (code width n rows roots entry done))
    (room : entry + 4 * roots.length + 3 * n + 184 < 2 ^ width)
    (position : state.pc = word width entry) (running : state.halted = false)
    (heapStored : state.heap = channelHeap (packetHeaderHeap width n rows roots) rows roots
      (assignmentOfSet {target}))
    (input : state.stack = (List.finRange n).map (fun channel => boolWord width (baseline channel)) ++ suffix)
    (held : state.reg 4 = word width target.val) :
    ∃ final ticks peak, Execution resident state final ticks peak ∧
      ticks ≤ 89 * graph.countedSize + 31 ∧
      peak ≤ 9 * graph.countedSize + 18 + state.stack.length + state.output.length ∧
      final.heap = channelHeap (packetHeaderHeap width n rows roots) rows roots baseline ∧
      final.stack = SharedHealthyReference.reference graph target width ++ suffix ∧
      final.output = state.output ∧ final.pc = word width done ∧ final.halted = false ∧
      final.reg 4 = word width target.val := by
  have all := physical
  unfold code at all
  have healthyCode := RawSharedOrdered.takePrefix resident entry _ _ all
  have baselineCode := RawSharedOrdered.takeSuffix resident entry _ _ all
  obtain ⟨healthy, healthyTicks, healthyPeak, healthyTrace, healthyTime, healthySpace,
    healthyHeap, healthyStack, healthyOutput, healthyPC, healthyRunning, healthyHead⟩ :=
    SharedHealthyInitialize.execution resident state graph rows roots matched heads rootMatches target entry
      (entry + 2 * roots.length + 167) capacity healthyCode (by omega) position running heapStored held
  have rootCount : roots.length = graph.roots.length := by rw [rootMatches]; simp
  have size := graph.countedSize_eq
  obtain ⟨children, guards⟩ := matched_incidence_lengths graph rows matched
  have cacheSize : (cacheHeap width (packetHeaderHeap width n rows roots) rows roots).size =
      5 + 6 * graph.nodeCount + graph.childIncidences + graph.guardIncidences + graph.roots.length := by
    simp only [cacheHeap_size, packetHeaderHeap_size, matched.length_eq, children, guards, rootCount]
  obtain ⟨final, baselinePeak, baselineTrace, baselineSpace, finalHeap, finalStack,
    finalOutput, finalPC, finalRunning, finalHead⟩ :=
    SharedBaselineLoad.execution resident healthy
      (cacheHeap width (packetHeaderHeap width n rows roots) rows roots)
      (assignmentOfSet {target}) baseline (SharedHealthyReference.reference graph target width) suffix
      (entry + 2 * roots.length + 167) done healthyPC healthyRunning
      (by simp only [SharedHealthyReference.reference_length]; omega)
      (by rw [cacheSize]; omega) (by rw [cacheSize]; simp only [SharedHealthyReference.reference_length]; omega)
      (by simpa only [channelHeap] using healthyHeap.trans heapStored)
      (by rw [healthyStack, input]; simp only [List.append_assoc])
      (by simpa only [SharedHealthyInitialize.code_size, SharedHealthyReference.reference_length, rootCount, Nat.add_assoc] using baselineCode)
  have healthyLive : healthy.liveWords = state.liveWords + graph.roots.length := by
    simp only [State.liveWords, healthyHeap, healthyStack, healthyOutput, List.length_append,
      SharedHealthyReference.reference_length]
    omega
  have initialSpace := SharedGraphRound.live_bound state graph rows roots matched rootMatches
    (assignmentOfSet {target}) heapStored
  refine ⟨final, healthyTicks + (12 * (SharedHealthyReference.reference graph target width).length + 3 * n + 9),
    max healthyPeak baselinePeak, healthyTrace.append baselineTrace, ?_, Nat.max_le.mpr ⟨healthySpace, ?_⟩,
    finalHeap, finalStack, finalOutput.trans healthyOutput, finalPC, finalRunning, finalHead.trans healthyHead⟩
  · simp only [SharedHealthyReference.reference_length]; omega
  · simp only [SharedHealthyReference.reference_length] at baselineSpace
    rw [healthyLive] at baselineSpace
    omega

end Controller.Cost.SharedHealthyBaseline
