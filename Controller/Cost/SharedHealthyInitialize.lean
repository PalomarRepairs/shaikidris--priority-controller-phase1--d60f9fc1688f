module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedWitnessSeed

@[expose] public section

/-! Healthy root reference words are initialized and evaluated in one fetched machine run. -/
namespace Controller.Cost.SharedHealthyInitialize
open Controller.Decoder Controller.Decoder.DAG Controller.Cost.GateProgram
open Controller.Cost.ForestIndexedOperands Controller.Cost.UniformDAGSource
open Controller.Cost.UniformDAGRun Controller.Cost.ForestInputPrefixStored
open Controller.Cost.RawTransferLoops

@[irreducible] def code (width n : Nat) (rows : List Row) (roots : List Nat) (entry done : Nat) : Program width 8 :=
  (SharedWitnessSeed.code width (word width (n + 1)) roots.length).toArray ++
    SharedReusableProbe.code width n rows roots (entry + 2 * roots.length) done

@[simp] theorem code_size (width n : Nat) (rows : List Row) (roots : List Nat) (entry done : Nat) :
    (code width n rows roots entry done).size = 2 * roots.length + 167 := by unfold code; simp

set_option maxHeartbeats 2000000 in
theorem execution (resident : Program width 8) (state : State width 8)
    (graph : DAG n) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (heads : HeadsMatch graph rows matched)
    (rootMatches : RootsMatch graph roots) (target : Fin n) (entry done : Nat)
    (capacity : 256 * (graph.countedSize + 1) < 2 ^ width)
    (physical : CodeAt resident entry (code width n rows roots entry done))
    (room : entry + 2 * roots.length + 167 < 2 ^ width)
    (position : state.pc = word width entry) (running : state.halted = false)
    (heapStored : state.heap = channelHeap (packetHeaderHeap width n rows roots) rows roots
      (assignmentOfSet {target})) (held : state.reg 4 = word width target.val) :
    ∃ final ticks peak, Execution resident state final ticks peak ∧
      ticks ≤ 74 * graph.countedSize + 22 ∧
      peak ≤ 9 * graph.countedSize + 18 + state.stack.length + state.output.length ∧
      final.heap = state.heap ∧ final.stack = SharedHealthyReference.reference graph target width ++ state.stack ∧
      final.output = state.output ∧ final.pc = word width done ∧ final.halted = false ∧
      final.reg 4 = word width target.val := by
  have all := physical
  unfold code at all
  have seedCode := RawSharedOrdered.takePrefix resident entry _ _ all
  have probeCode := RawSharedOrdered.takeSuffix resident entry _ _ all
  have seedBlock : SharedRootRead.BlockAt resident entry
      (SharedWitnessSeed.code width (word width (n + 1)) roots.length) := by
    intro offset bound
    simpa using seedCode ⟨offset, by simpa using bound⟩
  obtain ⟨ready, seedTrace, readyHeap, readyStack, readyOutput, readyPC, readyRunning, readyHead⟩ :=
    SharedWitnessSeed.execution resident state (word width (n + 1)) roots.length entry position running
      (by omega) seedBlock
  have rootCount : roots.length = graph.roots.length := by rw [rootMatches]; simp
  obtain ⟨final, probeTicks, probePeak, probeTrace, probeTime, probeSpace, finalHeap,
    finalStack, finalOutput, finalPC, finalRunning, finalHead⟩ :=
    SharedHealthyReference.execution resident ready graph rows roots matched heads rootMatches target state.stack
      (entry + 2 * roots.length) done capacity
      (by simpa using probeCode) (by omega) readyPC readyRunning (readyHeap.trans heapStored)
      (by simpa only [rootCount] using readyStack) (readyHead.trans held)
  have initialSpace := SharedGraphRound.live_bound state graph rows roots matched rootMatches
    (assignmentOfSet {target}) heapStored
  have size := graph.countedSize_eq
  have stackSize : ready.stack.length = graph.roots.length + state.stack.length := by
    simp [readyStack, rootCount]
  refine ⟨final, 2 * roots.length + probeTicks,
    max (state.liveWords + roots.length) probePeak, seedTrace.append probeTrace,
    by omega, Nat.max_le.mpr ⟨by omega, ?_⟩, finalHeap.trans readyHeap, finalStack,
    finalOutput.trans readyOutput, finalPC, finalRunning, finalHead⟩
  rw [stackSize, readyOutput] at probeSpace
  omega

end Controller.Cost.SharedHealthyInitialize
