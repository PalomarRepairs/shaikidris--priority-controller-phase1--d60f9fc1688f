module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.UniformDAGScanRun

@[expose] public section

/-! The fixed scan gate appends its computed Boolean word to the actual heap.
Its scans implement disjunction or negative-guard conjunction. Earlier stored
values and source cells are retained as a prefix; allocation is charged. -/
namespace Controller.Cost.UniformDAGGateScan
open Controller.Cost.GateProgram Controller.Cost.UniformDAGScan

def code (width base arityBase sourceBase : ℕ) (replacement : Bool) : Code width :=
  UniformDAGScanRun.code width base arityBase sourceBase replacement ++ [.allocate 2]
@[simp] theorem code_length : (code width base arityBase sourceBase replacement).length = 26 := rfl
@[simp] theorem code_words : 4 * (code width base arityBase sourceBase replacement).length = 104 := rfl

theorem accumulate_or (values : List Bool) (initial : Bool) :
    UniformDAGScanLoop.accumulate true (boolWord width initial) values =
      boolWord width (initial || values.any (fun value => value)) := by
  induction values generalizing initial with
  | nil => simp [UniformDAGScanLoop.accumulate]
  | cons value rest ih =>
      cases value <;> cases initial <;> simp [UniformDAGScanLoop.accumulate, ih]

theorem accumulate_guard (values : List Bool) (initial : Bool) :
    UniformDAGScanLoop.accumulate false (boolWord width initial) values =
      boolWord width (initial && !(values.any (fun value => value))) := by
  induction values generalizing initial with
  | nil => simp [UniformDAGScanLoop.accumulate]
  | cons value rest ih =>
      cases value <;> cases initial <;> simp [UniformDAGScanLoop.accumulate, ih]

/-- Actual cache setup, all incidence reads, and final result allocation.
The twenty-six fixed instructions take at most `18L+10` fetched steps. -/
theorem execution (program : Program width 4) (heap : Array (Word width))
    (base valueBase arityBase sourceBase offset cursor : ℕ) (values : List Bool)
    (temporary accumulator : Word width) (replacement : Bool)
    (suffix output : List (Word width))
    (programFits : base + 26 < 2 ^ width) (heapRoom : heap.size < 2 ^ width)
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
      (state (heap.push (UniformDAGScanLoop.accumulate replacement accumulator values))
        (base + 26) (word width 0) (word width valueBase)
        (UniformDAGScanLoop.accumulate replacement accumulator values)
        (word width (cursor + values.length)) suffix output) ticks peak ∧
      ticks ≤ 18 * values.length + 10 ∧
      peak ≤ 7 + heap.size + suffix.length + output.length := by
  let result := UniformDAGScanLoop.accumulate replacement accumulator values
  let finished := state heap (base + 25) (word width 0) (word width valueBase)
    result (word width (cursor + values.length)) suffix output
  let final := state (heap.push result) (base + 26) (word width 0) (word width valueBase)
    result (word width (cursor + values.length)) suffix output
  have scanBlock : BlockAt program base (UniformDAGScanRun.code width base arityBase sourceBase replacement) :=
    BlockAt.prefix program base _ _ block
  have lastBlock : BlockAt program (base + 25) ([.allocate 2] : Code width) := by
    simpa only [UniformDAGScanRun.code_length] using
      BlockAt.suffix program base (UniformDAGScanRun.code width base arityBase sourceBase replacement) _ block
  obtain ⟨ticks, peak, trace, time, space⟩ := UniformDAGScanRun.execution program heap
    base valueBase arityBase sourceBase offset cursor values temporary accumulator replacement suffix output
    (by omega) arityFits sourceFits arityBound sourceBound arityCell sourceCell
    cursorFits countFits cells scanBlock
  have p25 : (word width (base + 25)).val = base + 25 := Nat.mod_eq_of_lt (by omega)
  have allocate : programStep program finished = some final := by
    unfold programStep
    rw [show finished.pc.val = base + 25 from p25,
      show program[base + 25]? = some (.allocate 2) from lastBlock 0 (by simp)]
    simp [step, finished, final, state, State.advance, heapRoom, p25]
  have lastTrace := Execution.cons allocate (Execution.refl final)
  refine ⟨ticks + 1, max peak (max finished.liveWords final.liveWords), ?_, ?_, ?_⟩
  · simpa [finished, final, result] using trace.append lastTrace
  · omega
  · apply max_le space
    apply max_le <;> simp [finished, final, state, State.liveWords] <;> omega

end Controller.Cost.UniformDAGGateScan
