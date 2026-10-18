module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedProbeBudget

@[expose] public section

/-! Baseline witness initialization and the empty-baseline guard form one machine run. -/
namespace Controller.Cost.SharedBaselineInitialize
open Controller.Decoder Controller.Decoder.DAG Controller.Cost.GateProgram
open Controller.Cost.ForestIndexedOperands Controller.Cost.UniformDAGSource
open Controller.Cost.UniformDAGRun Controller.Cost.ForestInputPrefixStored
open Controller.Cost.RawTransferLoops

def witnesses (graph : DAG n) (values : Assignment n) (width : Nat) : List (Word width) :=
  if (List.finRange n).any values then
    SharedRootAggregate.updated (word width n)
      (graph.roots.map (fun root => (root.val, graph.eval values root)))
      (List.replicate graph.roots.length (word width (n + 1)))
  else List.replicate graph.roots.length (word width (n + 1))

@[simp] theorem witnesses_length (graph : DAG n) (values : Assignment n) (width : Nat) :
    (witnesses graph values width).length = graph.roots.length := by
  unfold witnesses
  split <;> simp [SharedRootAggregate.updated, List.length_zipWith]

@[irreducible] def code (width n : Nat) (rows : List Row) (roots : List Nat) (entry done : Nat) : Program width 8 :=
  (SharedWitnessSeed.code width (word width (n + 1)) roots.length).toArray ++
    (#[.constant 4 (word width n)] ++
      SharedBaselineProbe.code width n rows roots (entry + 2 * roots.length + 1) done)

@[simp] theorem code_size (width n : Nat) (rows : List Row) (roots : List Nat) (entry done : Nat) :
    (code width n rows roots entry done).size = 2 * roots.length + 5 * n + 172 := by unfold code; simp; omega

set_option maxHeartbeats 2000000 in
theorem execution (resident : Program width 8) (state : State width 8)
    (graph : DAG n) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (heads : HeadsMatch graph rows matched)
    (rootMatches : RootsMatch graph roots) (values : Assignment n) (entry done : Nat)
    (capacity : 256 * (graph.countedSize + 1) < 2 ^ width)
    (physical : CodeAt resident entry (code width n rows roots entry done))
    (room : entry + 2 * roots.length + 5 * n + 172 < 2 ^ width)
    (position : state.pc = word width entry) (running : state.halted = false)
    (heapStored : state.heap = channelHeap (packetHeaderHeap width n rows roots) rows roots values) :
    ∃ final ticks peak, Execution resident state final ticks peak ∧
      ticks ≤ 79 * graph.countedSize + 27 ∧
      peak ≤ 9 * graph.countedSize + 18 + state.stack.length + state.output.length ∧
      final.heap = state.heap ∧ final.stack = witnesses graph values width ++ state.stack ∧
      final.output = state.output ∧ final.pc = word width done ∧ final.halted = false ∧
      final.reg 4 = word width n := by
  have all := physical
  unfold code at all
  have seedCode := RawSharedOrdered.takePrefix resident entry _ _ all
  have tailCode := RawSharedOrdered.takeSuffix resident entry _ _ all
  have seedBlock : SharedRootRead.BlockAt resident entry
      (SharedWitnessSeed.code width (word width (n + 1)) roots.length) := by
    intro offset bound
    simpa using seedCode ⟨offset, by simpa using bound⟩
  obtain ⟨seeded, seedTrace, seededHeap, seededStack, seededOutput, seededPC, seededRunning, seededHead⟩ :=
    SharedWitnessSeed.execution resident state (word width (n + 1)) roots.length entry position running
      (by omega) seedBlock
  have restCode : CodeAt resident (entry + 2 * roots.length)
      (#[.constant 4 (word width n)] ++ SharedBaselineProbe.code width n rows roots
        (entry + 2 * roots.length + 1) done) := by simpa using tailCode
  have constantCode := RawSharedOrdered.takePrefix resident (entry + 2 * roots.length) _ _ restCode
  have probeCode := RawSharedOrdered.takeSuffix resident (entry + 2 * roots.length) _ _ restCode
  obtain ⟨ready, setupTrace, readyPC, readyHead, readyHeap, readyStack, readyOutput, readyRunning, readyFrame⟩ :=
    SharedEvaluationReclaim.constant_execution resident (entry + 2 * roots.length) n 4 seeded seededPC seededRunning
      (by omega) (by simpa using constantCode ⟨0, by simp⟩)
  have rootCount : roots.length = graph.roots.length := by rw [rootMatches]; simp
  obtain ⟨final, probeTicks, probePeak, probeTrace, probeTime, probeSpace, finalHeap,
    finalStack, finalOutput, finalPC, finalRunning, finalHead⟩ :=
    SharedBaselineProbe.execution resident ready graph rows roots matched heads rootMatches values
      (List.replicate graph.roots.length (word width (n + 1))) state.stack
      (entry + 2 * roots.length + 1) done capacity (by simpa using probeCode) (by omega) readyPC readyRunning
      (readyHeap.trans (seededHeap.trans heapStored))
      (by simpa only [rootCount] using readyStack.trans seededStack) (by simp) readyHead
  have seededLive : seeded.liveWords = state.liveWords + roots.length := by
    simp only [State.liveWords, seededHeap, seededStack, seededOutput, List.length_append, List.length_replicate]
    omega
  have readyLive : ready.liveWords = seeded.liveWords := by simp only [State.liveWords, readyHeap, readyStack, readyOutput]
  have size := graph.countedSize_eq
  have initialSpace := SharedGraphRound.live_bound state graph rows roots matched rootMatches values heapStored
  have joined := seedTrace.append (setupTrace.append probeTrace)
  rw [seededLive] at joined
  refine ⟨final, 2 * roots.length + (1 + probeTicks),
    max (state.liveWords + roots.length) (max (state.liveWords + roots.length) probePeak), joined,
    by omega, ?_, finalHeap.trans (readyHeap.trans seededHeap), ?_,
    finalOutput.trans (readyOutput.trans seededOutput), finalPC, finalRunning, finalHead⟩
  · simp only [readyStack, seededStack, readyOutput, seededOutput, List.length_append, List.length_replicate] at probeSpace
    apply Nat.max_le.mpr
    constructor
    · omega
    · apply Nat.max_le.mpr
      constructor <;> omega
  · simpa only [witnesses] using finalStack

end Controller.Cost.SharedBaselineInitialize
