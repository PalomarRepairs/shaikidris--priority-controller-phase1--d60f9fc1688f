module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedRootTaggedCursor
public import Controller.Cost.SharedRootResumeEntry

@[expose] public section

namespace Controller.Cost.SharedRootTaggedSkip
open Controller.Cost.GateProgram Controller.Cost.RawTransferLoops
open Controller.Cost.ForestZeroAdmissibleCaller

set_option maxHeartbeats 2000000 in
theorem execution (program : Program width 8) (state : State width 8)
    (sourceHeap : Array (Word width)) (tableBase inverseBase n entry exhausted zeroQuery skipEntry source count : Nat)
    (target : Fin n) (rest : List (Word width))
    (ready : QueryReady (ambient := ambient) sourceHeap tableBase inverseBase entry
      (word width source :: word width (count + 1) :: word width (n + 1) :: rest) state)
    (room : entry + 22 < 2 ^ width) (skipRoom : skipEntry + 6 < 2 ^ width)
    (capacity : n + 1 < 2 ^ width) (countFits : count + 1 < 2 ^ width) (sourceFits : source < 2 ^ width)
    (sourceValid : source < state.heap.size) (stored : state.heap[source]? = some (word width (n + 1)))
    (cursorAt : CodeAt program entry (SharedRootTaggedCursor.code width n entry exhausted zeroQuery skipEntry))
    (skipAt : CodeAt program skipEntry (SharedRootResumeEntry.skipCode width tableBase inverseBase entry)) :
    ∃ final ticks, Execution program state final ticks state.liveWords ∧ ticks ≤ 26 ∧
      final.heap = state.heap ∧ final.output = state.output ∧
      QueryReady (ambient := ambient) sourceHeap tableBase inverseBase entry
        (word width (source + 1) :: word width count :: rest) final ∧
      final.liveWords + 1 = state.liveWords := by
  obtain ⟨inspected, ticks, inspectTrace, time, heap, stack, output, pc, active, address, cursorHeld, countHeld, candidateHeld⟩ :=
    SharedRootTaggedCursor.successor_execution program state n entry exhausted zeroQuery skipEntry source count target false
      (word width (n + 1)) rest ready.position ready.running room capacity countFits sourceFits sourceValid stored
      (by simpa using ready.stack) cursorAt
  have inspectedPC : inspected.pc = word width skipEntry := by simpa using pc
  obtain ⟨final, skipTrace, finalHeap, finalOutput, finalReady, frame⟩ :=
    SharedRootResumeEntry.skip_execution program inspected sourceHeap tableBase inverseBase skipEntry entry
      (word width (source + 1)) (word width count) inspectedPC active skipRoom cursorHeld countHeld
      (by rw [heap]; exact ready.heapSize) (by rw [heap]; exact ready.sourceFrame)
      (by rw [heap]; exact ready.zeroTable) skipAt
  have inspectedLive : inspected.liveWords + 3 = state.liveWords := by
    simp only [State.liveWords, heap, output, stack, ready.stack, List.length_cons]
    omega
  refine ⟨final, ticks + 6, ?_, by omega, finalHeap.trans heap, finalOutput.trans output, ?_, ?_⟩
  · simpa only [Nat.max_eq_left (by omega : inspected.liveWords + 2 ≤ state.liveWords)] using
      inspectTrace.append skipTrace
  · simpa only [stack] using finalReady
  · simp only [State.liveWords, finalHeap, heap, finalOutput, output, finalReady.stack, stack,
      ready.stack, List.length_cons]
    omega

end Controller.Cost.SharedRootTaggedSkip
