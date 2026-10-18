module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.UniformDAGScanSetup

public import Mathlib.Tactic.FinCases

@[expose] public section

/-! Composition of actual cache reads with the complete fixed scan loop.
The saved count is loaded from its cache cell, rather than supplied in code.
The final stack is the original caller stack, including empty incidence lists. -/
namespace Controller.Cost.UniformDAGScanRun
open Controller.Cost.GateProgram Controller.Cost.UniformDAGScan

def code (width base arityBase sourceBase : ℕ) (replacement : Bool) : Code width :=
  UniformDAGScanSetup.code width arityBase sourceBase ++
    UniformDAGScan.code width (base + 7) replacement
@[simp] theorem code_length : (code width base arityBase sourceBase replacement).length = 25 := rfl

private theorem frame (s t : State width 4)
    (registers : ∀ index, s.reg index = t.reg index)
    (heap : s.heap = t.heap) (stack : s.stack = t.stack)
    (output : s.output = t.output) (pc : s.pc = t.pc) (running : s.halted = t.halted) :
    s = t := by
  have regs : s.reg = t.reg := funext registers
  cases s
  cases t
  simp_all

/-- A source-derived arity and stream address feed the same actual loop.
The fixed twenty-five-opcode code uses at most `18L+9` fetched steps. -/
theorem execution (program : Program width 4) (heap : Array (Word width))
    (base valueBase arityBase sourceBase offset cursor : ℕ) (values : List Bool)
    (temporary accumulator : Word width) (replacement : Bool)
    (suffix output : List (Word width))
    (programFits : base + 25 < 2 ^ width)
    (arityFits : arityBase + offset < 2 ^ width)
    (sourceFits : sourceBase + offset < 2 ^ width)
    (arityBound : arityBase + offset < heap.size)
    (sourceBound : sourceBase + offset < heap.size)
    (arityCell : heap[arityBase + offset]'arityBound = word width values.length)
    (sourceCell : heap[sourceBase + offset]'sourceBound = word width cursor)
    (cursorFits : cursor + values.length < 2 ^ width)
    (countFits : values.length < 2 ^ width)
    (cells : UniformDAGScanLoop.Stored heap valueBase cursor values)
    (block : BlockAt program base (code width base arityBase sourceBase replacement)) :
    ∃ ticks peak, Execution program
      (state heap base temporary (word width valueBase) accumulator (word width offset) suffix output)
      (state heap (base + 25) (word width 0) (word width valueBase)
        (UniformDAGScanLoop.accumulate replacement accumulator values)
        (word width (cursor + values.length)) suffix output) ticks peak ∧
      ticks ≤ 18 * values.length + 9 ∧
      peak ≤ 7 + heap.size + suffix.length + output.length := by
  let start := state heap base temporary (word width valueBase) accumulator (word width offset) suffix output
  have setupBlock : BlockAt program base (UniformDAGScanSetup.code width arityBase sourceBase) :=
    BlockAt.prefix program base _ _ block
  have loopBlock : BlockAt program (base + 7) (UniformDAGScan.code width (base + 7) replacement) := by
    simpa only [UniformDAGScanSetup.code_length] using
      BlockAt.suffix program base (UniformDAGScanSetup.code width arityBase sourceBase) _ block
  obtain ⟨ready, setupTrace, r0, r1, r2, r3, readyHeap, readyStack, readyOutput, readyPC, readyRunning⟩ :=
    UniformDAGScanSetup.execution program start base arityBase sourceBase offset values.length cursor
      (by simp [start, state]) arityFits sourceFits arityBound sourceBound arityCell sourceCell
      rfl rfl (by omega) setupBlock
  have readyEq : ready = state heap (base + 7) (word width (sourceBase + offset))
      (word width valueBase) accumulator (word width cursor) (word width values.length :: suffix) output := by
    apply frame
    · intro register
      fin_cases register
      · simpa [start, state] using r0
      · simpa [start, state] using r1
      · simpa [start, state] using r2
      · simpa [start, state] using r3
    · exact readyHeap
    · exact readyStack
    · exact readyOutput
    · exact readyPC
    · exact readyRunning
  rw [readyEq] at setupTrace
  obtain ⟨loopTicks, loopPeak, loopTrace, loopTime, loopSpace⟩ :=
    UniformDAGScanLoop.execution program heap (base + 7) valueBase cursor values
      (word width (sourceBase + offset)) accumulator replacement suffix output
      (by omega) cursorFits countFits cells loopBlock
  refine ⟨7 + loopTicks, max (start.liveWords + 1) loopPeak, ?_, ?_, ?_⟩
  · simpa [start, Nat.add_assoc] using setupTrace.append loopTrace
  · omega
  · apply max_le
    · simp [start, state, State.liveWords]
      omega
    · exact loopSpace

end Controller.Cost.UniformDAGScanRun
