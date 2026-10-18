module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.NativeGateStore
public import Controller.Cost.NativeGateOps

@[expose] public section

/-! A native binary XOR reads both signed literals and appends its signed result
in thirteen fetched instructions. -/
namespace Controller.Cost.NativeGateXor
open Controller.Cost.GateProgram Controller.CNF

def code (width base : Nat) (left right : Literal (Fin variableCount)) (phase : Bool) :
    List (Instruction width 4) :=
  NativeGateRead.code width base left ++
    ([.copy 3 1] ++ (NativeGateRead.code width base right ++
      ([.xor 3 3 1] ++ NativeGateStore.code width phase)))

@[simp] theorem code_length (width base : Nat) (left right : Literal (Fin variableCount)) (phase : Bool) :
    (code width base left right phase).length = 13 := by simp [code]

set_option maxHeartbeats 2000000 in
theorem execution (resident : Program width 4) (state : State width 4)
    (values : Fin variableCount → Bool) (left right : Literal (Fin variableCount)) (phase : Bool)
    (base entry : Nat) (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 13 < 2 ^ width) (boolFits : 1 < 2 ^ width)
    (heapFits : state.heap.size < 2 ^ width)
    (leftValid : base + left.1.val < state.heap.size)
    (rightValid : base + right.1.val < state.heap.size)
    (leftCell : state.heap[base + left.1.val]'leftValid = boolWord width (values left.1))
    (rightCell : state.heap[base + right.1.val]'rightValid = boolWord width (values right.1))
    (physical : BlockAt resident entry (code width base left right phase)) :
    ∃ final, Execution resident state final 13 (state.liveWords + 1) ∧
      final.heap = state.heap.push
        (boolWord width ((literalValue values left ^^ literalValue values right) == phase)) ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry + 13) ∧ final.halted = false := by
  have leftBlock : BlockAt resident entry (NativeGateRead.code width base left) :=
    BlockAt.prefix _ _ _ _ physical
  obtain ⟨lread, ltrace, lvalue, _, lheap, lstack, loutput, lpc, lrunning⟩ :=
    NativeGateRead.execution resident state values left base entry position running
      (by omega) (by omega) leftValid leftCell leftBlock
  let copied := lread.advance.put 3 (lread.reg 1)
  have copyFetch : resident[entry + 4]? = some (.copy 3 1) := by
    simpa [code, NativeGateRead.code, NativeGateStore.code] using physical 4 (by simp [code])
  have copyTrace : Execution resident lread copied 1 lread.liveWords :=
    NativeGateOps.put_execution resident lread (.copy 3 1) (entry + 4) 3 (lread.reg 1)
      lpc (by omega) copyFetch (by simp [step, lrunning, copied])
  have copyPC : copied.pc = word width (entry + 5) := by
    simpa [copied, State.put, Nat.add_assoc] using NativeGateOps.advance_pc lread (entry + 4) lpc (by omega)
  have copyLive : copied.liveWords = state.liveWords := by
    simp [copied, State.advance, State.put, State.liveWords, lheap, lstack, loutput]
  have copyRunning : copied.halted = false := lrunning
  have copyHeap : copied.heap = state.heap := lheap
  have copyStack : copied.stack = state.stack := lstack
  have copyOutput : copied.output = state.output := loutput
  have rightBlock : BlockAt resident (entry + 5) (NativeGateRead.code width base right) := by
    have rest := BlockAt.suffix _ _ _ _ physical
    have afterCopy := BlockAt.suffix _ _ _ _ rest
    simpa only [NativeGateRead.code_length, List.length_cons, List.length_nil,
      Nat.add_assoc, Nat.reduceAdd] using BlockAt.prefix _ _ _ _ afterCopy
  obtain ⟨rread, rtrace, rvalue, accumulator, rheap, rstack, routput, rpc, rrunning⟩ :=
    NativeGateRead.execution resident copied values right base (entry + 5) copyPC copyRunning
      (by omega) (by omega) (by simpa only [copyHeap] using rightValid)
      (by simpa only [copyHeap] using rightCell) rightBlock
  have rAccumulator : rread.reg 3 = boolWord width (literalValue values left) := by
    simpa [copied, State.put, lvalue] using accumulator
  let combined := rread.advance.put 3
    (boolWord width (literalValue values left ^^ literalValue values right))
  have xorFetch : resident[entry + 9]? = some (.xor 3 3 1) := by
    simpa [code, NativeGateRead.code, NativeGateStore.code] using physical 9 (by simp [code])
  have xorTransition : step (.xor 3 3 1) rread = some combined := by
    simp only [step, rrunning, Bool.false_eq_true, ite_false, rAccumulator, rvalue]
    rw [NativeGateOps.xor_word width boolFits]
  have xorTrace : Execution resident rread combined 1 rread.liveWords :=
    NativeGateOps.put_execution resident rread (.xor 3 3 1) (entry + 9) 3 _
      (by simpa only [Nat.add_assoc, Nat.reduceAdd] using rpc) (by omega) xorFetch xorTransition
  have combinedPC : combined.pc = word width (entry + 10) := by
    simpa [combined, State.put, Nat.add_assoc] using NativeGateOps.advance_pc rread (entry + 9)
      (by simpa only [Nat.add_assoc, Nat.reduceAdd] using rpc) (by omega)
  have storeBlock : BlockAt resident (entry + 10) (NativeGateStore.code width phase) := by
    have rest := BlockAt.suffix _ _ _ _ physical
    have afterCopy := BlockAt.suffix _ _ _ _ rest
    have afterRight := BlockAt.suffix _ _ _ _ afterCopy
    simpa only [NativeGateRead.code_length, List.length_cons, List.length_nil,
      Nat.add_assoc, Nat.reduceAdd] using BlockAt.suffix _ _ _ _ afterRight
  obtain ⟨final, finalTrace, finalHeap, finalStack, finalOutput, finalPC, finalRunning⟩ :=
    NativeGateStore.execution resident combined
      (literalValue values left ^^ literalValue values right) phase (entry + 10)
      combinedPC rrunning (by omega) boolFits
      (by simpa [combined, State.advance, State.put, rheap, copyHeap] using heapFits)
      (by simp [combined, State.put]) storeBlock
  have lLive : lread.liveWords = state.liveWords := by
    simp [State.liveWords, lheap, lstack, loutput]
  have rLive : rread.liveWords = state.liveWords := by
    simp [State.liveWords, rheap, rstack, routput, copyHeap, copyStack, copyOutput]
  have combinedLive : combined.liveWords = state.liveWords := by
    simp [combined, State.advance, State.put, State.liveWords, rheap, rstack, routput,
      copyHeap, copyStack, copyOutput]
  refine ⟨final, ?_, ?_, ?_, ?_, ?_, finalRunning⟩
  · simpa only [lLive, copyLive, rLive, combinedLive, Nat.reduceAdd, Nat.max_self,
      Nat.max_eq_right (Nat.le_succ _)] using
      (((ltrace.append copyTrace).append rtrace).append xorTrace).append finalTrace
  · simpa [combined, State.advance, State.put, rheap, copyHeap] using finalHeap
  · simpa [combined, State.advance, State.put, rstack, copyStack] using finalStack
  · simpa [combined, State.advance, State.put, routput, copyOutput] using finalOutput
  · simpa only [Nat.add_assoc, Nat.reduceAdd] using finalPC

end Controller.Cost.NativeGateXor
