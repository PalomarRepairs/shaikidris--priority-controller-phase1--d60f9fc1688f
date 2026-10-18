module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedRootTaggedCursor
public import Controller.Cost.SharedRootPointerShift

@[expose] public section

namespace Controller.Cost.SharedRootHealthyEntry
open Controller.Cost.GateProgram Controller.Cost.RawTransferLoops
open Controller.Cost.ForestZeroAdmissibleCaller Controller.Cost.ForestZeroBackendFrame

def code (width tableBase inverseBase offset slot : Nat) : Program width 8 :=
  SharedRootResumeEntry.code width tableBase inverseBase ++
    (SharedRootPointerShift.code width offset ++ SharedRootQueryEntry.code width slot tableBase)

@[simp] theorem code_size : (code width tableBase inverseBase offset slot).size = 12 := by
  simp [code]

set_option maxHeartbeats 2000000 in
theorem execution (program : Program width 8) (state : State width 8)
    (sourceHeap : Array (Word width)) (tableBase inverseBase entry source offset slot : Nat)
    (cursor count root : Word width)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 12 < 2 ^ width) (sourceFits : source < 2 ^ width) (offsetFits : offset < 2 ^ width)
    (rootAddressFits : source + offset < 2 ^ width) (slotFits : slot < 2 ^ width)
    (cursorHeld : state.reg 5 = cursor) (countHeld : state.reg 6 = count) (sourceHeld : state.reg 3 = word width source)
    (heapSize : state.heap.size = sourceHeap.size) (sourceFrame : PrefixFrame tableBase sourceHeap state.heap)
    (zeroTable : ∀ coordinate : Fin ambient, state.heap[tableBase + coordinate.val]? = some (word width 0))
    (sourceValid : source + offset < state.heap.size) (slotBefore : slot < tableBase)
    (stored : state.heap[source + offset]? = some root)
    (physical : CodeAt program entry (code width tableBase inverseBase offset slot)) :
    ∃ final, Execution program state final 12 (state.liveWords + 2) ∧
      final.heap = state.heap.set slot root (by have := sourceFrame.2.1; omega) ∧
      final.output = state.output ∧
      QueryReady (ambient := ambient) (sourceHeap.set slot root (by have := sourceFrame.1; omega))
        tableBase inverseBase (entry + 12) (cursor :: count :: state.stack) final := by
  have all := physical
  unfold code at all
  have resumeAt := RawSharedOrdered.takePrefix program entry _ _ all
  have tailAt := RawSharedOrdered.takeSuffix program entry _ _ all
  have tailCode : CodeAt program (entry + 5)
      (SharedRootPointerShift.code width offset ++ SharedRootQueryEntry.code width slot tableBase) := by
    simpa only [SharedRootResumeEntry.code_size] using tailAt
  have shiftAt := RawSharedOrdered.takePrefix program (entry + 5) _ _ tailCode
  have selectAt := RawSharedOrdered.takeSuffix program (entry + 5) _ _ tailCode
  obtain ⟨resumed, resumeTrace, resumeHeap, resumeOutput, resumeReady, resumeFrame⟩ :=
    SharedRootResumeEntry.execution program state sourceHeap tableBase inverseBase entry cursor count position running
      (by omega) cursorHeld countHeld heapSize sourceFrame zeroTable resumeAt
  obtain ⟨shifted, shiftTrace, shiftHeap, shiftOutput, rootHeld, shiftReady⟩ :=
    SharedRootPointerShift.execution program resumed sourceHeap tableBase inverseBase (entry + 5) source offset _
      resumeReady (by omega) sourceFits offsetFits ((resumeFrame 3 (by decide) (by decide) (by decide)).trans sourceHeld)
      shiftAt
  have rootReady : QueryReady (ambient := ambient) sourceHeap tableBase inverseBase (entry + 7)
      (cursor :: count :: state.stack) shifted := by
    simpa only [Nat.add_assoc, Nat.reduceAdd] using shiftReady
  obtain ⟨final, selectTrace, finalHeap, finalOutput, finalReady⟩ :=
    SharedRootQueryEntry.execution program shifted sourceHeap tableBase inverseBase (entry + 7) (source + offset) slot root _
      rootReady (by omega) rootAddressFits slotFits (by rw [shiftHeap, resumeHeap]; exact sourceValid) slotBefore rootHeld
      (by rw [shiftHeap, resumeHeap]; exact stored)
      (by simpa only [SharedRootPointerShift.code_size, Nat.add_assoc, Nat.reduceAdd] using selectAt)
  have resumedLive : resumed.liveWords = state.liveWords + 2 := by
    simp only [State.liveWords, resumeHeap, resumeOutput, resumeReady.stack, List.length_cons]
    omega
  have shiftedLive : shifted.liveWords = resumed.liveWords := by
    simp only [State.liveWords, shiftHeap, shiftOutput, shiftReady.stack, resumeReady.stack]
  refine ⟨final, ?_, ?_, finalOutput.trans (shiftOutput.trans resumeOutput), ?_⟩
  · have joined := resumeTrace.append (shiftTrace.append selectTrace)
    simpa only [shiftedLive, resumedLive, Nat.max_self, Nat.reduceAdd] using joined
  · simpa only [shiftHeap, resumeHeap] using finalHeap
  · simpa only [Nat.add_assoc, Nat.reduceAdd] using finalReady


set_option maxHeartbeats 2000000 in
theorem tagged_execution (program : Program width 8) (state : State width 8)
    (sourceHeap : Array (Word width))
    (tableBase inverseBase n entry exhausted queryEntry skipEntry source count offset slot : Nat)
    (target : Fin n) (candidate root : Word width) (rest : List (Word width))
    (ready : QueryReady (ambient := ambient) sourceHeap tableBase inverseBase entry
      (word width source :: word width (count + 1) :: word width target.val :: rest) state)
    (room : entry + 22 < 2 ^ width) (queryRoom : queryEntry + 12 < 2 ^ width)
    (capacity : n + 1 < 2 ^ width) (countFits : count + 1 < 2 ^ width)
    (sourceFits : source < 2 ^ width) (offsetFits : offset < 2 ^ width)
    (rootAddressFits : source + offset < 2 ^ width) (slotFits : slot < 2 ^ width)
    (sourceValid : source < state.heap.size) (rootValid : source + offset < state.heap.size)
    (slotBefore : slot < tableBase)
    (candidateStored : state.heap[source]? = some candidate) (rootStored : state.heap[source + offset]? = some root)
    (cursorAt : CodeAt program entry (SharedRootTaggedCursor.code width n entry exhausted queryEntry skipEntry))
    (queryAt : CodeAt program queryEntry (code width tableBase inverseBase offset slot)) :
    ∃ final ticks, Execution program state final ticks state.liveWords ∧ ticks ≤ 32 ∧
      final.heap = state.heap.set slot root (by have := ready.sourceFrame.2.1; omega) ∧
      final.output = state.output ∧
      QueryReady (ambient := ambient) (sourceHeap.set slot root (by have := ready.sourceFrame.1; omega))
        tableBase inverseBase (queryEntry + 12) (word width (source + 1) :: word width count :: rest) final ∧
      final.liveWords + 1 = state.liveWords := by
  obtain ⟨inspected, ticks, inspectTrace, time, heap, stack, output, pc, active, address, cursorHeld, countHeld, candidateHeld⟩ :=
    SharedRootTaggedCursor.successor_execution program state n entry exhausted queryEntry skipEntry source count target true
      candidate rest ready.position ready.running room capacity countFits sourceFits sourceValid candidateStored
      (by simpa using ready.stack) cursorAt
  obtain ⟨final, queryTrace, finalHeap, finalOutput, finalReady⟩ :=
    execution program inspected sourceHeap tableBase inverseBase queryEntry source offset slot
      (word width (source + 1)) (word width count) root (by simpa using pc) active queryRoom sourceFits offsetFits
      rootAddressFits slotFits cursorHeld countHeld address (by rw [heap]; exact ready.heapSize)
      (by rw [heap]; exact ready.sourceFrame) (by rw [heap]; exact ready.zeroTable)
      (by rw [heap]; exact rootValid) slotBefore (by rw [heap]; exact rootStored) queryAt
  have inspectedLive : inspected.liveWords + 3 = state.liveWords := by
    simp only [State.liveWords, heap, stack, output, ready.stack, List.length_cons]
    omega
  refine ⟨final, ticks + 12, ?_, by omega, ?_, finalOutput.trans output, ?_, ?_⟩
  · simpa only [Nat.max_eq_left (by omega : inspected.liveWords + 2 ≤ state.liveWords)] using
      inspectTrace.append queryTrace
  · simpa only [heap] using finalHeap
  · simpa only [stack] using finalReady
  · simp only [State.liveWords, finalHeap, Array.size_set, heap, finalOutput, output, finalReady.stack,
      stack, ready.stack, List.length_cons]
    omega

end Controller.Cost.SharedRootHealthyEntry
