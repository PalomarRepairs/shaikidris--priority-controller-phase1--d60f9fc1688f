module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.NativeGateOps

@[expose] public section

/-! Signed native input cells update an accumulator after one fetched read.
Each occurrence executes at most six instructions and retains all buffers. -/
namespace Controller.Cost.NativeGateConditional
open Controller.Cost.GateProgram Controller.CNF

def code (width base entry : Nat) (literal : Literal (Fin variableCount)) (replacement : Bool) :
    List (Instruction width 4) :=
  NativeGateRead.code width base literal ++
    [.branchZero 1 (word width (entry + 6)), .constant 3 (boolWord width replacement)]

@[simp] theorem code_length (width base entry : Nat)
    (literal : Literal (Fin variableCount)) (replacement : Bool) :
    (code width base entry literal replacement).length = 6 := by simp [code]

set_option maxHeartbeats 2000000 in
theorem execution (resident : Program width 4) (state : State width 4)
    (values : Fin variableCount → Bool) (literal : Literal (Fin variableCount))
    (accumulator replacement : Bool) (base entry : Nat)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 6 < 2 ^ width) (boolFits : 1 < 2 ^ width)
    (heapFits : state.heap.size < 2 ^ width)
    (valid : base + literal.1.val < state.heap.size)
    (cell : state.heap[base + literal.1.val]'valid = boolWord width (values literal.1))
    (held : state.reg 3 = boolWord width accumulator)
    (physical : BlockAt resident entry (code width base entry literal replacement)) :
    ∃ final ticks, Execution resident state final ticks state.liveWords ∧ ticks ≤ 6 ∧
      final.reg 3 = boolWord width (if literalValue values literal then replacement else accumulator) ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry + 6) ∧ final.halted = false := by
  have readBlock : BlockAt resident entry (NativeGateRead.code width base literal) :=
    BlockAt.prefix _ _ _ _ physical
  obtain ⟨read, readTrace, readValue, readAccumulator, readHeap, readStack, readOutput, readPC, readRunning⟩ :=
    NativeGateRead.execution resident state values literal base entry position running
      (by omega) (by omega) valid cell readBlock
  have readHeld : read.reg 3 = boolWord width accumulator := readAccumulator.trans held
  have readLive : read.liveWords = state.liveWords := by
    simp [State.liveWords, readHeap, readStack, readOutput]
  have branchFetch : resident[entry + 4]? = some (.branchZero 1 (word width (entry + 6))) := by
    simpa [code, NativeGateRead.code] using physical 4 (by simp [code])
  have constantFetch : resident[entry + 5]? = some (.constant 3 (boolWord width replacement)) := by
    simpa [code, NativeGateRead.code] using physical 5 (by simp [code])
  cases truth : literalValue values literal with
  | false =>
    let final := { read.advance with pc := word width (entry + 6) }
    have branchStep : programStep resident read = some final := by
      rw [NativeGateOps.fetch resident read (entry + 4) _ readPC (by omega) branchFetch]
      simp [step, readRunning, readValue, truth, boolWord_val width boolFits, final]
    have finalLive : final.liveWords = state.liveWords := by
      simp [final, State.advance, State.liveWords, readHeap, readStack, readOutput]
    have branchTrace : Execution resident read final 1 state.liveWords := by
      simpa only [readLive, finalLive, Nat.zero_add, Nat.max_self] using
        Execution.cons branchStep (Execution.refl final)
    refine ⟨final, 5, ?_, by omega, ?_, readHeap, readStack, readOutput, rfl, readRunning⟩
    · simpa only [Nat.reduceAdd, Nat.max_self] using readTrace.append branchTrace
    · simpa [final, State.advance, truth] using readHeld
  | true =>
    let middle := read.advance
    let final := middle.advance.put 3 (boolWord width replacement)
    have middlePC : middle.pc = word width (entry + 5) := by
      simpa [middle, Nat.add_assoc] using NativeGateOps.advance_pc read (entry + 4) readPC (by omega)
    have branchStep : programStep resident read = some middle := by
      rw [NativeGateOps.fetch resident read (entry + 4) _ readPC (by omega) branchFetch]
      simp [step, readRunning, readValue, truth, boolWord_val width boolFits, middle]
    have constantTrace : Execution resident middle final 1 middle.liveWords :=
      NativeGateOps.put_execution resident middle (.constant 3 (boolWord width replacement))
        (entry + 5) 3 (boolWord width replacement) middlePC (by omega) constantFetch
        (by simp [step, middle, State.advance, readRunning])
    have middleLive : middle.liveWords = state.liveWords := by
      simp [middle, State.advance, State.liveWords, readHeap, readStack, readOutput]
    have branchTrace : Execution resident read middle 1 state.liveWords := by
      simpa only [readLive, middleLive, Nat.zero_add, Nat.max_self] using
        Execution.cons branchStep (Execution.refl middle)
    refine ⟨final, 6, ?_, by omega, ?_, readHeap, readStack, readOutput, ?_, readRunning⟩
    · simpa only [middleLive, Nat.reduceAdd, Nat.max_self] using
        (readTrace.append branchTrace).append constantTrace
    · simp [final, State.put, truth]
    · simpa [final, State.put, Nat.add_assoc] using
        NativeGateOps.advance_pc middle (entry + 5) middlePC (by omega)

end Controller.Cost.NativeGateConditional
