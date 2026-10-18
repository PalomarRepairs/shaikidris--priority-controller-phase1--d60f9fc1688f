module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedProbeCleanup

@[expose] public section

/-! Root aggregation and probe cleanup return reusable graph storage and updated witnesses. -/
namespace Controller.Cost.SharedRootFinish
open Controller.Cost.RawTransferLoops

def code (width entry done retained nodes cursor valueBase count : Nat) : Program width 8 :=
  #[.constant 3 (word width cursor), .constant 5 (word width count)] ++
    ((SharedRootAggregate.code width (entry + 2) valueBase).toArray ++
      SharedProbeCleanup.code width (entry + 17) done retained nodes count)

@[simp] theorem code_size (width entry done retained nodes cursor valueBase count : Nat) :
    (code width entry done retained nodes cursor valueBase count).size = 41 := by simp [code]

set_option maxHeartbeats 2000000 in
theorem execution (resident : Program width 8) (state : State width 8)
    (retained : Array (Word width)) (nodes witnesses suffix : List (Word width))
    (roots : List (Nat × Bool)) (entry done cursor valueBase : Nat) (candidate : Word width)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 41 < 2 ^ width) (positive : 0 < retained.size)
    (boolFits : 1 < 2 ^ width)
    (heapFits : retained.size + nodes.length + roots.length < 2 ^ width)
    (cursorFits : cursor + roots.length < 2 ^ width)
    (heapStored : state.heap = retained ++ nodes.toArray)
    (input : state.stack = witnesses ++ suffix) (lengths : witnesses.length = roots.length)
    (candidateHeld : state.reg 4 = candidate)
    (represented : SharedRootLoop.RepresentedRoots state.heap cursor valueBase roots)
    (physical : CodeAt resident entry
      (code width entry done retained.size nodes.length cursor valueBase roots.length)) :
    ∃ final ticks, Execution resident state final ticks (state.liveWords + roots.length) ∧
      ticks ≤ 25 * roots.length + 4 * nodes.length + 16 ∧
      final.heap = retained ∧
      final.stack = SharedRootAggregate.updated candidate roots witnesses ++ suffix ∧
      final.output = state.output ∧ final.pc = word width done ∧ final.halted = false ∧
      final.reg 4 = candidate := by
  have all := physical
  unfold code at all
  have setup := RawSharedOrdered.takePrefix resident entry _ _ all
  have tail := RawSharedOrdered.takeSuffix resident entry _ _ all
  have aggregateCode := RawSharedOrdered.takePrefix resident (entry + 2) _ _ (by simpa using tail)
  have cleanupCode := RawSharedOrdered.takeSuffix resident (entry + 2) _ _ (by simpa using tail)
  have aggregateBlock : SharedRootRead.BlockAt resident (entry + 2)
      (SharedRootAggregate.code width (entry + 2) valueBase) := by
    intro offset bound
    simpa using aggregateCode ⟨offset, by simpa using bound⟩
  obtain ⟨counted, t1, p1, v1, h1, k1, o1, a1, f1⟩ :=
    SharedEvaluationReclaim.constant_execution resident entry cursor 3 state position running (by omega)
      (by simpa using setup ⟨0, by simp⟩)
  obtain ⟨ready, t2, p2, v2, h2, k2, o2, a2, f2⟩ :=
    SharedEvaluationReclaim.constant_execution resident (entry + 1) roots.length 5 counted p1 a1 (by omega)
      (by simpa using setup ⟨1, by simp⟩)
  have readyHeap : ready.heap = state.heap := h2.trans h1
  have readyStack : ready.stack = state.stack := k2.trans k1
  have readyOutput : ready.output = state.output := o2.trans o1
  obtain ⟨observed, observeTicks, observeTrace, observeTime, zero, cursorNext, candidateNext,
    observedHeap, observedStack, observedOutput, observedPC, observedRunning⟩ :=
    SharedRootAggregate.execution resident ready (entry + 2) valueBase cursor roots witnesses suffix candidate
      (by simpa only [readyHeap] using represented) lengths (readyStack.trans input)
      ((f2 3 (by decide)).trans v1) v2
      ((f2 4 (by decide)).trans ((f1 4 (by decide)).trans candidateHeld))
      cursorFits (by omega) (by simp only [readyHeap, heapStored, Array.size_append, List.size_toArray]; exact heapFits)
      (by simpa only [Nat.add_assoc, Nat.reduceAdd] using p2) a2 (by omega) boolFits aggregateBlock
  have updatedLength : (SharedRootAggregate.updated candidate roots witnesses).length = roots.length := by
    simp [SharedRootAggregate.updated, lengths]
  have stored : observed.heap = (retained ++ nodes.toArray) ++
      (SharedRootAggregate.updated candidate roots witnesses).toArray := by
    rw [observedHeap, readyHeap, heapStored]
  obtain ⟨final, cleanupTrace, finalHeap, finalStack, finalOutput, finalPC, finalRunning, finalFrame⟩ :=
    SharedProbeCleanup.execution resident observed retained nodes
      (SharedRootAggregate.updated candidate roots witnesses) (entry + 17) done
      (by simpa only [Nat.add_assoc, Nat.reduceAdd] using observedPC) observedRunning
      (by omega) positive (by simpa only [updatedLength] using heapFits) stored
      (by simpa only [SharedRootAggregate.code_length, List.size_toArray, Nat.add_assoc,
        Nat.reduceAdd, updatedLength] using cleanupCode)
  have countedLive : counted.liveWords = state.liveWords := by simp only [State.liveWords, h1, k1, o1]
  have readyLive : ready.liveWords = state.liveWords := by simp only [State.liveWords, readyHeap, readyStack, readyOutput]
  have observedLive : observed.liveWords = state.liveWords := by
    simp only [State.liveWords, observedHeap, observedStack, observedOutput,
      readyHeap, readyOutput, input, Array.size_append, List.size_toArray, updatedLength,
      List.length_append, lengths]
    omega
  have joined := t1.append (t2.append (observeTrace.append cleanupTrace))
  rw [countedLive, readyLive, observedLive, updatedLength] at joined
  have peakEq : max state.liveWords (max state.liveWords
      (max state.liveWords (state.liveWords + roots.length))) = state.liveWords + roots.length := by omega
  rw [peakEq] at joined
  refine ⟨final, 1 + (1 + (observeTicks + (10 * roots.length + 4 * nodes.length + 13))),
    joined, by omega, finalHeap, ?_, finalOutput.trans (observedOutput.trans readyOutput),
    finalPC, finalRunning, finalFrame.trans candidateNext⟩
  simpa only [observedStack] using finalStack

end Controller.Cost.SharedRootFinish
