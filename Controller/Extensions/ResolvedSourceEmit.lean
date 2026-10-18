module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Extensions.ResolvedSourceRead
public import Controller.Cost.SharedCoordinateTable

@[expose] public section

/-! Expansion literal words are allocated by fetched source reads. Selectors
choose between original child cells; each literal occupies one output cell.
All source cells, selector cells, caller frames and output remain unchanged. -/
namespace Controller.Extensions.ResolvedSourceEmit
open Controller.Cost Controller.Cost.RawTransferLoops Controller.Cost.SharedDetectorAssembly

inductive Operand (width : Nat) where
  | literal (value : Word width)
  | read (address : Nat) (offset : Word width)
  | choice (flag left right : Nat) (offset : Word width)
  deriving Repr

inductive Stored (heap : Array (Word width)) : Operand width → Word width → Prop where
  | literal (value : Word width) : Stored heap (.literal value) value
  | read (address : Nat) (offset value : Word width) (cell : heap[address]? = some value) :
      Stored heap (.read address offset) (word width (value.val + offset.val))
  | choice (flag left right : Nat) (offset first second : Word width) (selected : Bool)
      (flagCell : heap[flag]? = some (boolWord width selected))
      (leftCell : heap[left]? = some first) (rightCell : heap[right]? = some second) :
      Stored heap (.choice flag left right offset)
        (word width ((if selected then second else first).val + offset.val))

theorem Stored.append (heap extra : Array (Word width)) (operand : Operand width) (value : Word width)
    (stored : Stored heap operand value) :
    Stored (heap ++ extra) operand value := by
  have cell : ∀ (address : Nat) (value : Word width), heap[address]? = some value → (heap ++ extra)[address]? = some value := by
    intro address value present
    rw [Array.getElem?_append_left (Array.getElem?_eq_some_iff.mp present).1]
    exact present
  cases stored with
  | literal value => exact .literal value
  | read address offset value present => exact .read address offset value (cell _ _ present)
  | choice flag left right offset first second selected bit lc rc =>
    exact .choice flag left right offset first second selected (cell _ _ bit) (cell _ _ lc) (cell _ _ rc)

def finishCode (offset : Word width) : List (Instruction width 8) :=
  [.constant 0 offset, .add 1 1 0, .allocate 1]

@[simp] theorem finishCode_length : (finishCode offset).length = 3 := rfl

theorem finish_execution (program : Program width 8) (state : State width 8)
    (entry : Nat) (offset value : Word width) (held : state.reg 1 = value)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 3 < 2 ^ width) (capacity : state.heap.size < 2 ^ width)
    (present : SharedRootRead.BlockAt program entry (finishCode offset)) :
    ∃ final, Execution program state final 3 (state.liveWords + 1) ∧
      final.heap = state.heap.push (word width (value.val + offset.val)) ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry + 3) ∧ final.halted = false := by
  have offsetEq : word width offset.val = offset := Fin.ext (Nat.mod_eq_of_lt offset.isLt)
  obtain ⟨s1, t1, p1, v1, h1, st1, o1, r1, f1⟩ :=
    SharedEvaluationReclaim.constant_execution program entry offset.val 0 state position running (by omega)
      (by simpa [offsetEq, finishCode] using present 0 (by simp [finishCode]))
  obtain ⟨s2, t2, p2, v2, h2, st2, o2, r2, _⟩ :=
    EnumerationSteps.add_execution program s1 (entry+1) 1 1 0 p1 r1 (by omega)
      (by simpa [finishCode] using present 1 (by simp [finishCode]))
  obtain ⟨final, t3, p3, h3, st3, o3, r3, _, _⟩ :=
    EnumerationSteps.allocate_execution program s2 (entry+2) 1
      (by simpa only [Nat.add_assoc, Nat.reduceAdd] using p2) r2 (by omega)
      (by simpa [h2, h1] using capacity) (by simpa [finishCode] using present 2 (by simp [finishCode]))
  have live1 : s1.liveWords = state.liveWords := by simp only [State.liveWords, h1, st1, o1]
  have live2 : s2.liveWords = state.liveWords := by simp only [State.liveWords, h2, st2, o2, h1, st1, o1]
  refine ⟨final, by simpa only [live1, live2, Nat.max_eq_right (Nat.le_succ _)] using t1.append (t2.append t3),
    ?_, st3.trans (st2.trans st1), o3.trans (o2.trans o1), ?_, r3⟩
  · simpa only [h2, h1, v2, f1 1 (by decide), held, v1, offsetEq] using h3
  · simpa only [Nat.add_assoc, Nat.reduceAdd] using p3

def oneCode (width entry : Nat) : Operand width → List (Instruction width 8)
  | .literal value => SharedCoordinateTable.code width [value]
  | .read address offset => ResolvedSourceRead.readCode width address ++ finishCode offset
  | .choice flag left right offset => ResolvedSourceRead.choiceCode width entry flag left right ++ finishCode offset

theorem oneCode_length (operand : Operand width) : (oneCode width entry operand).length ≤ 12 := by
  cases operand <;> simp [oneCode]

theorem one_execution (program : Program width 8) (state : State width 8)
    (entry : Nat) (operand : Operand width) (value : Word width) (stored : Stored state.heap operand value)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + (oneCode width entry operand).length < 2 ^ width) (capacity : state.heap.size + 1 < 2 ^ width)
    (present : SharedRootRead.BlockAt program entry (oneCode width entry operand)) :
    ∃ final ticks, Execution program state final ticks (state.liveWords + 1) ∧ ticks ≤ 12 ∧
      final.heap = state.heap.push value ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry + (oneCode width entry operand).length) ∧ final.halted = false := by
  cases stored with
  | literal value =>
    obtain ⟨final, trace, heap, stack, output, pc, active, _⟩ :=
      SharedCoordinateTable.execution program state [value] entry position running (by simpa [oneCode] using room)
        (by simpa using capacity) present
    exact ⟨final, 2, by simpa using trace, by decide, by simpa using heap, stack, output,
      by simpa [oneCode] using pc, active⟩
  | read address offset value cell =>
    have readAt := block_left program entry _ _ present
    have finishAt := block_right program entry _ _ present
    simp only [ResolvedSourceRead.readCode_length] at finishAt
    simp only [oneCode, List.length_append, ResolvedSourceRead.readCode_length, finishCode_length] at room
    obtain ⟨middle, first, reg, heap, stack, output, pc, active, _⟩ :=
      ResolvedSourceRead.read_execution program state entry address value cell position running (by omega)
        (by omega) readAt
    obtain ⟨final, last, fh, fs, fo, fp, fr⟩ :=
      finish_execution program middle (entry+2) offset value reg pc active (by omega)
        (by rw [heap]; omega) finishAt
    have live : middle.liveWords = state.liveWords := by simp only [State.liveWords, heap, stack, output]
    exact ⟨final, 5, by simpa only [live, Nat.max_eq_right (Nat.le_succ _)] using first.append last,
      by decide, by simpa only [heap] using fh, fs.trans stack, fo.trans output,
      by simpa [oneCode, Nat.add_assoc] using fp, fr⟩
  | choice flag left right offset firstValue secondValue selected bit lc rc =>
    have readAt := block_left program entry _ _ present
    have finishAt := block_right program entry _ _ present
    simp only [ResolvedSourceRead.choiceCode_length] at finishAt
    simp only [oneCode, List.length_append, ResolvedSourceRead.choiceCode_length, finishCode_length] at room
    obtain ⟨middle, ticks, first, time, reg, heap, stack, output, pc, active, _⟩ :=
      ResolvedSourceRead.choice_execution program state entry flag left right selected firstValue secondValue
        bit lc rc position running (by omega) (by omega) readAt
    obtain ⟨final, last, fh, fs, fo, fp, fr⟩ :=
      finish_execution program middle (entry+9) offset _ reg pc active (by omega) (by rw [heap]; omega) finishAt
    have live : middle.liveWords = state.liveWords := by simp only [State.liveWords, heap, stack, output]
    exact ⟨final, ticks+3, by simpa only [live, Nat.max_eq_right (Nat.le_succ _)] using first.append last,
      by omega, by simpa only [heap] using fh, fs.trans stack, fo.trans output,
      by simpa [oneCode, Nat.add_assoc] using fp, fr⟩

def code (width : Nat) : Nat → List (Operand width) → List (Instruction width 8)
  | _, [] => []
  | entry, operand :: rest => oneCode width entry operand ++ code width (entry + (oneCode width entry operand).length) rest

theorem code_length (operands : List (Operand width)) : (code width entry operands).length ≤ 12 * operands.length := by
  induction operands generalizing entry with
  | nil => simp [code]
  | cons operand rest ih =>
    have one := oneCode_length (entry := entry) operand
    have tail := ih (entry := entry + (oneCode width entry operand).length)
    simp only [code, List.length_append, List.length_cons]; omega

set_option maxHeartbeats 800000 in
theorem execution (program : Program width 8) (state : State width 8) (entry : Nat)
    (operands : List (Operand width)) (values : List (Word width))
    (stored : List.Forall₂ (Stored state.heap) operands values)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + (code width entry operands).length < 2 ^ width)
    (capacity : state.heap.size + values.length < 2 ^ width)
    (present : SharedRootRead.BlockAt program entry (code width entry operands)) :
    ∃ final ticks, Execution program state final ticks (state.liveWords + values.length) ∧
      ticks ≤ 12 * operands.length ∧ final.heap = state.heap ++ values.toArray ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry + (code width entry operands).length) ∧ final.halted = false := by
  induction operands generalizing state entry values with
  | nil =>
    cases stored
    exact ⟨state, 0, by simpa using Execution.refl (p := program) state,
      by simp, by simp, rfl, rfl, by simpa [code] using position, running⟩
  | cons operand rest ih =>
    cases stored with
    | @cons _ value _ values head tail =>
      have firstAt := block_left program entry _ _ present
      have lastAt := block_right program entry _ _ present
      simp only [code, List.length_append] at room
      obtain ⟨middle, mt, first, time, heap, stack, output, pc, active⟩ :=
        one_execution program state entry operand value head position running (by omega)
          (by simp only [List.length_cons] at capacity; omega) firstAt
      have nextStored : List.Forall₂ (Stored middle.heap) rest values := by
        apply tail.imp
        intro op word represented
        simpa only [heap, Array.push_eq_append] using Stored.append _ #[value] op word represented
      obtain ⟨final, ft, last, ftime, fh, fs, fo, fp, fr⟩ :=
        ih middle (entry + (oneCode width entry operand).length) values nextStored pc active
          (by omega) (by simp only [heap, Array.size_push]; simp only [List.length_cons] at capacity; omega) lastAt
      have live : middle.liveWords = state.liveWords + 1 := by
        simp only [State.liveWords, heap, stack, output, Array.size_push]; omega
      refine ⟨final, mt+ft, ?_, by simp only [List.length_cons]; omega, ?_, fs.trans stack, fo.trans output, ?_, fr⟩
      · have joined := first.append last
        rw [live, Nat.max_eq_right (by omega : state.liveWords+1 ≤ state.liveWords+1+values.length)] at joined
        convert joined using 1 <;> simp only [List.length_cons] <;> omega
      · rw [fh, heap, List.toArray_cons, Array.push_eq_append, Array.append_assoc]
      · simpa only [code, List.length_append, Nat.add_assoc] using fp

end Controller.Extensions.ResolvedSourceEmit
