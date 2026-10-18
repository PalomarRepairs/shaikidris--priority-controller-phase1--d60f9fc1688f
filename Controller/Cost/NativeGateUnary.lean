module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.NativeGateStore

@[expose] public section

/-! Alias and NOT gates execute signed reads and append their signed outputs
without changing the input table or retained stack and observations. -/
namespace Controller.Cost.NativeGateUnary
open Controller.Cost.GateProgram Controller.CNF

abbrev Code (width : Nat) := List (Instruction width 4)

def code (width base : Nat) (literal : Literal (Fin variableCount)) (phase : Bool) : Code width :=
  NativeGateRead.code width base literal ++ [.copy 3 1] ++ NativeGateStore.code width phase

@[simp] theorem code_length (width base : Nat) (literal : Literal (Fin variableCount)) (phase : Bool) :
    (code width base literal phase).length = 8 := by simp [code]

set_option maxHeartbeats 2000000 in
theorem execution (resident : Program width 4) (state : State width 4)
    (values : Fin variableCount → Bool) (literal : Literal (Fin variableCount)) (phase : Bool)
    (base entry : Nat) (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 8 < 2 ^ width) (boolFits : 1 < 2 ^ width)
    (heapFits : state.heap.size < 2 ^ width)
    (valid : base + literal.1.val < state.heap.size)
    (cell : state.heap[base + literal.1.val]'valid = boolWord width (values literal.1))
    (physical : BlockAt resident entry (code width base literal phase)) :
    ∃ final, Execution resident state final 8 (state.liveWords + 1) ∧
      final.heap = state.heap.push (boolWord width (literalValue values literal == phase)) ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry + 8) ∧ final.halted = false := by
  have readBlock : BlockAt resident entry (NativeGateRead.code width base literal) := by
    exact BlockAt.prefix _ _ _ _ (BlockAt.prefix _ _ _ _ physical)
  obtain ⟨read, readTrace, readValue, _, readHeap, readStack, readOutput, readPC, readRunning⟩ :=
    NativeGateRead.execution resident state values literal base entry position running
      (by omega) (by omega) valid cell readBlock
  let copied := read.advance.put 3 (read.reg 1)
  have copyFetch : resident[entry + 4]? = some (.copy 3 1) := by
    simpa [code, NativeGateRead.code, NativeGateStore.code] using physical 4 (by simp [code])
  have copyStep : programStep resident read = some copied := by
    unfold programStep
    rw [readPC, show (word width (entry + 4)).val = entry + 4 from Nat.mod_eq_of_lt (by omega), copyFetch]
    simp [step, copied, readRunning]
  have copyPC : copied.pc = word width (entry + 5) := by
    simp [copied, State.advance, State.put, readPC,
      show (word width (entry + 4)).val = entry + 4 from Nat.mod_eq_of_lt (by omega)]
  have copyLive : copied.liveWords = state.liveWords := by
    simp [copied, State.advance, State.put, State.liveWords, readHeap, readStack, readOutput]
  have copyTrace : Execution resident read copied 1 state.liveWords := by
    have trace := Execution.cons copyStep (Execution.refl copied)
    have readLive : read.liveWords = state.liveWords := by
      simp [State.liveWords, readHeap, readStack, readOutput]
    simpa only [copyLive, readLive, Nat.max_self, Nat.zero_add] using trace
  have storeBlock : BlockAt resident (entry + 5) (NativeGateStore.code width phase) := by
    simpa only [List.length_append, NativeGateRead.code_length, List.length_cons,
      List.length_nil, Nat.reduceAdd] using BlockAt.suffix _ _ _ _ physical
  obtain ⟨final, storeTrace, finalHeap, finalStack, finalOutput, finalPC, finalRunning⟩ :=
    NativeGateStore.execution resident copied (literalValue values literal) phase (entry + 5)
      copyPC readRunning (by omega) boolFits (by simpa [copied, State.advance, State.put, readHeap] using heapFits)
      (by simp [copied, State.put, readValue]) storeBlock
  refine ⟨final, ?_, ?_, ?_, ?_, ?_, finalRunning⟩
  · simpa only [copyLive, Nat.reduceAdd, Nat.max_self, Nat.max_eq_right (Nat.le_succ _)]
      using (readTrace.append copyTrace).append storeTrace
  · simpa [copied, State.advance, State.put, readHeap] using finalHeap
  · simpa [copied, State.advance, State.put, readStack] using finalStack
  · simpa [copied, State.advance, State.put, readOutput] using finalOutput
  · simpa only [Nat.add_assoc, Nat.reduceAdd] using finalPC

theorem not_execution (resident : Program width 4) (state : State width 4)
    (values : Fin variableCount → Bool) (literal : Literal (Fin variableCount)) (phase : Bool)
    (base entry : Nat) (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 8 < 2 ^ width) (boolFits : 1 < 2 ^ width)
    (heapFits : state.heap.size < 2 ^ width)
    (valid : base + literal.1.val < state.heap.size)
    (cell : state.heap[base + literal.1.val]'valid = boolWord width (values literal.1))
    (physical : BlockAt resident entry (code width base (negate literal) phase)) :
    ∃ final, Execution resident state final 8 (state.liveWords + 1) ∧
      final.heap = state.heap.push (boolWord width ((!literalValue values literal) == phase)) ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry + 8) ∧ final.halted = false := by
  simpa only [literalValue_negate] using execution resident state values (negate literal) phase
    base entry position running room boolFits heapFits valid cell physical

end Controller.Cost.NativeGateUnary
