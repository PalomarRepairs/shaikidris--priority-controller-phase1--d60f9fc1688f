module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedRootTagStack
public import Controller.Cost.SharedRootCursor

@[expose] public section

namespace Controller.Cost.SharedRootTaggedCursor
open Controller.Cost.GateProgram Controller.Cost.RawTransferLoops

def code (width n entry exhausted zeroQuery nextRoot : Nat) : Program width 8 :=
  SharedRootCursor.code width exhausted ++
    SharedRootTagStack.inspectCode width n (entry + 10) zeroQuery nextRoot

@[simp] theorem code_size : (code width n entry exhausted zeroQuery nextRoot).size = 22 := by
  simp [code]

set_option maxHeartbeats 2000000 in
theorem successor_execution (program : Program width 8) (state : State width 8)
    (n entry exhausted zeroQuery nextRoot source count : Nat) (target : Fin n) (healthy : Bool)
    (candidate : Word width) (rest : List (Word width))
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 22 < 2 ^ width) (capacity : n + 1 < 2 ^ width)
    (countFits : count + 1 < 2 ^ width) (sourceFits : source < 2 ^ width)
    (sourceValid : source < state.heap.size) (stored : state.heap[source]? = some candidate)
    (input : state.stack = word width source :: word width (count + 1) ::
      (if healthy then word width target.val else word width (n + 1)) :: rest)
    (physical : CodeAt program entry (code width n entry exhausted zeroQuery nextRoot)) :
    ∃ final ticks, Execution program state final ticks state.liveWords ∧ ticks ≤ 20 ∧
      final.heap = state.heap ∧ final.stack = rest ∧ final.output = state.output ∧
      final.pc = word width (if healthy then zeroQuery else
        if candidate = word width (n + 1) then nextRoot else entry + 22) ∧ final.halted = false ∧
      final.reg 3 = word width source ∧ final.reg 5 = word width (source + 1) ∧ final.reg 6 = word width count ∧ final.reg 4 = candidate := by
  have all := physical
  unfold code at all
  have cursorAt := RawSharedOrdered.takePrefix program entry _ _ all
  have inspectAt := RawSharedOrdered.takeSuffix program entry _ _ all
  obtain ⟨advanced, cursorTrace, cursorHeap, cursorOutput, cursorStack, cursorPC,
    cursorRunning, zero, sourceHeld, cursorFrame⟩ :=
    SharedRootCursor.successor_execution program state entry exhausted source count _ position running
      (by omega) countFits sourceFits input cursorAt
  obtain ⟨final, ticks, inspectTrace, time, heap, stack, output, pc, active, nextHeld, countHeld, sourceFinal, candidateHeld⟩ :=
    SharedRootTagStack.inspect_execution program advanced n (entry + 10) zeroQuery nextRoot source target healthy
      candidate (word width (source + 1)) (word width count) rest cursorPC cursorRunning (by omega) capacity
      sourceFits (by rw [cursorHeap]; exact sourceValid) sourceHeld (by rw [cursorHeap]; exact stored)
      cursorStack (by simpa only [SharedRootCursor.code_size] using inspectAt)
  have sameLive : advanced.liveWords = state.liveWords := by
    simp only [State.liveWords, cursorHeap, cursorOutput, cursorStack, input, List.length_cons]
  refine ⟨final, 10 + ticks, ?_, by omega, heap.trans cursorHeap, stack, output.trans cursorOutput,
    ?_, active, sourceFinal.trans sourceHeld, nextHeld, countHeld, candidateHeld⟩
  · simpa only [sameLive, Nat.max_self] using cursorTrace.append inspectTrace
  · simpa only [Nat.add_assoc, Nat.reduceAdd] using pc

end Controller.Cost.SharedRootTaggedCursor
