module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedStackRotate

@[expose] public section

/-! Guarded baseline initialization and all allowed head probes share one retained graph. -/
namespace Controller.Cost.SharedCandidateBatch
open Controller.Decoder Controller.Decoder.DAG Controller.Cost.GateProgram
open Controller.Cost.ForestIndexedOperands Controller.Cost.UniformDAGSource
open Controller.Cost.UniformDAGRun Controller.Cost.ForestInputPrefixStored
open Controller.Cost.RawTransferLoops

@[irreducible] def code (width n : Nat) (rows : List Row) (roots : List Nat) (entry done : Nat) : Program width 8 :=
  SharedBaselineInitialize.code width n rows roots entry (entry + 2 * roots.length + 5 * n + 172) ++
    (#[.constant 4 (word width 0)] ++
      SharedHeadLoop.code width n rows roots (entry + 2 * roots.length + 5 * n + 173) done)

@[simp] theorem code_size (width n : Nat) (rows : List Row) (roots : List Nat) (entry done : Nat) :
    (code width n rows roots entry done).size = 4 * roots.length + 5 * n + 382 := by
  unfold code; simp; omega

set_option maxHeartbeats 2000000 in
theorem execution (resident : Program width 8) (state : State width 8)
    (graph : DAG n) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (heads : HeadsMatch graph rows matched)
    (rootMatches : RootsMatch graph roots) (values : Assignment n)
    (flags : List Bool) (suffix : List (Word width)) (entry done : Nat)
    (capacity : 256 * (graph.countedSize + 1) < 2 ^ width)
    (physical : CodeAt resident entry (code width n rows roots entry done))
    (room : entry + 4 * roots.length + 5 * n + 382 < 2 ^ width)
    (position : state.pc = word width entry) (running : state.halted = false)
    (heapStored : state.heap = channelHeap (packetHeaderHeap width n rows roots) rows roots values)
    (input : state.stack = flags.map (boolWord width) ++ suffix) (flagCount : flags.length = n) :
    ∃ final ticks peak, Execution resident state final ticks peak ∧
      ticks ≤ n * (84 * graph.countedSize + 54) + 79 * graph.countedSize + 31 ∧
      peak ≤ 9 * graph.countedSize + 18 + state.stack.length + state.output.length ∧
      final.heap = state.heap ∧
      final.stack = SharedHeadLoop.witnessFold graph values 0 flags
        (SharedBaselineInitialize.witnesses graph values width) ++ suffix ∧
      final.output = state.output ∧ final.pc = word width done ∧ final.halted = false ∧
      final.reg 4 = word width n := by
  have all := physical
  unfold code at all
  have baselineCode := RawSharedOrdered.takePrefix resident entry _ _ all
  have tailCode := RawSharedOrdered.takeSuffix resident entry _ _ all
  obtain ⟨initialized, initTicks, initPeak, initTrace, initTime, initSpace, initHeap,
    initStack, initOutput, initPC, initRunning, initHead⟩ :=
    SharedBaselineInitialize.execution resident state graph rows roots matched heads rootMatches values entry
      (entry + 2 * roots.length + 5 * n + 172) capacity baselineCode (by omega) position running heapStored
  have restCode : CodeAt resident (entry + 2 * roots.length + 5 * n + 172)
      (#[.constant 4 (word width 0)] ++ SharedHeadLoop.code width n rows roots
        (entry + 2 * roots.length + 5 * n + 173) done) := by
    simpa [Nat.add_assoc] using tailCode
  have constantCode := RawSharedOrdered.takePrefix resident (entry + 2 * roots.length + 5 * n + 172) _ _ restCode
  have loopCode := RawSharedOrdered.takeSuffix resident (entry + 2 * roots.length + 5 * n + 172) _ _ restCode
  obtain ⟨ready, setupTrace, readyPC, readyHead, readyHeap, readyStack, readyOutput, readyRunning, readyFrame⟩ :=
    SharedEvaluationReclaim.constant_execution resident (entry + 2 * roots.length + 5 * n + 172) 0 4
      initialized initPC initRunning (by omega) (by simpa using constantCode ⟨0, by simp⟩)
  obtain ⟨final, loopTicks, loopPeak, loopTrace, loopTime, loopSpace, finalHeap,
    finalStack, finalOutput, finalPC, finalRunning, finalHead⟩ :=
    SharedHeadLoop.execution resident ready graph rows roots matched heads rootMatches values 0 flags
      (SharedBaselineInitialize.witnesses graph values width) suffix
      (entry + 2 * roots.length + 5 * n + 173) done capacity
      (by simpa [Nat.add_assoc] using loopCode) (by omega) (by simpa [Nat.add_assoc] using readyPC) readyRunning
      (readyHeap.trans (initHeap.trans heapStored))
      (by rw [readyStack, initStack, input]; simp only [List.append_assoc])
      (by simp) readyHead (by simpa using flagCount)
  have initLive : initialized.liveWords = state.liveWords + graph.roots.length := by
    simp only [State.liveWords, initHeap, initStack, initOutput, List.length_append,
      SharedBaselineInitialize.witnesses_length]
    omega
  have readyLive : ready.liveWords = initialized.liveWords := by
    simp only [State.liveWords, readyHeap, readyStack, readyOutput]
  have size := graph.countedSize_eq
  have initialSpace := SharedGraphRound.live_bound state graph rows roots matched rootMatches values heapStored
  have joined := initTrace.append (setupTrace.append loopTrace)
  refine ⟨final, initTicks + (1 + loopTicks), max initPeak (max initialized.liveWords loopPeak), joined,
    ?_, ?_, finalHeap.trans (readyHeap.trans initHeap), finalStack,
    finalOutput.trans (readyOutput.trans initOutput), finalPC, finalRunning, finalHead⟩
  · rw [flagCount] at loopTime; omega
  · simp only [readyStack, initStack, readyOutput, initOutput, List.length_append,
      SharedBaselineInitialize.witnesses_length] at loopSpace
    apply Nat.max_le.mpr
    constructor
    · exact initSpace
    · apply Nat.max_le.mpr
      constructor <;> omega

end Controller.Cost.SharedCandidateBatch
