module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SourceGateInput

@[expose] public section

/-! A fixed fetched kernel forms a child-address constant record from two source
words: the child identifier and the source header's channel count. The addition
is exact under the declared word capacity. Source loading and compiler traversal
have separate costs. -/
namespace Controller.Cost.SourceGateOperands
open Controller.Cost.GateProgram

def fieldCode (width : ℕ) : Code width :=
  [.load 2 3, .load 0 1, .add 2 2 0, .constant 0 (word width 0),
   .constant 1 (word width 0), .constant 3 (word width 0)]
def code (width : ℕ) : Code width := fieldCode width ++ InstructionRecordStore.recordCode
def program (width : ℕ) : Program width 4 := (code width).toArray
@[simp] theorem fieldCode_length : (fieldCode width).length = 6 := rfl
@[simp] theorem code_length : (code width).length = 10 := rfl
@[simp] theorem program_words : programWords (program width) = 40 := by simp [program, programWords]

private theorem fetched (program : Program width 4) (s : State width 4)
    (base : ℕ) (instruction : Instruction width 4)
    (pc : s.pc = word width base) (fits : base < 2 ^ width)
    (entry : program[base]? = some instruction) :
    programStep program s = step instruction s := by
  unfold programStep
  rw [pc, show (word width base).val = base from Nat.mod_eq_of_lt fits, entry]
  rfl

private theorem advance (s : State width 4) (base : ℕ)
    (pc : s.pc = word width base) (fits : base < 2 ^ width) :
    s.advance.pc = word width (base + 1) := by
  simp only [State.advance, pc]
  rw [show (word width base).val = base from Nat.mod_eq_of_lt fits]

theorem fields_execution (program : Program width 4) (s : State width 4)
    (child channels childCursor headerCursor base : ℕ)
    (childAddress : s.reg 3 = word width childCursor)
    (headerAddress : s.reg 1 = word width headerCursor)
    (childBound : childCursor < s.heap.size) (headerBound : headerCursor < s.heap.size)
    (childCursorFits : childCursor < 2 ^ width) (headerCursorFits : headerCursor < 2 ^ width)
    (childSource : s.heap[childCursor]'childBound = word width child)
    (headerSource : s.heap[headerCursor]'headerBound = word width channels)
    (sumFits : channels + child < 2 ^ width)
    (pc : s.pc = word width base) (running : s.halted = false)
    (fits : base + 6 < 2 ^ width) (block : BlockAt program base (fieldCode width)) :
    ∃ ready, Execution program s ready 6 s.liveWords ∧
      [ready.reg 0, ready.reg 1, ready.reg 2, ready.reg 3] =
        InstructionEncoding.encode (.constant 0 (word width (channels + child)) : Instruction width 4) ∧
      (ready.reg 2).val = channels + child ∧
      ready.heap = s.heap ∧ ready.stack = s.stack ∧ ready.output = s.output ∧
      ready.pc = word width (base + 6) ∧ ready.halted = false := by
  let one := s.advance.put 2 (word width child)
  let two := one.advance.put 0 (word width channels)
  let three := two.advance.put 2 (word width (channels + child))
  let four := three.advance.put 0 (word width 0)
  let five := four.advance.put 1 (word width 0)
  let ready := five.advance.put 3 (word width 0)
  have childFits : child < 2 ^ width := by omega
  have channelsFits : channels < 2 ^ width := by omega
  have childVal : (word width child).val = child := Nat.mod_eq_of_lt childFits
  have channelsVal : (word width channels).val = channels := Nat.mod_eq_of_lt channelsFits
  have childCursorVal : (word width childCursor).val = childCursor := Nat.mod_eq_of_lt childCursorFits
  have headerCursorVal : (word width headerCursor).val = headerCursor := Nat.mod_eq_of_lt headerCursorFits
  have onePC : one.pc = word width (base + 1) := by
    simpa [one, State.put, Nat.add_assoc] using advance s (base + 0) pc (by omega)
  have twoPC : two.pc = word width (base + 2) := by
    simpa [two, State.put, Nat.add_assoc] using advance one (base + 1) onePC (by omega)
  have threePC : three.pc = word width (base + 3) := by
    simpa [three, State.put, Nat.add_assoc] using advance two (base + 2) twoPC (by omega)
  have fourPC : four.pc = word width (base + 4) := by
    simpa [four, State.put, Nat.add_assoc] using advance three (base + 3) threePC (by omega)
  have fivePC : five.pc = word width (base + 5) := by
    simpa [five, State.put, Nat.add_assoc] using advance four (base + 4) fourPC (by omega)
  have readyPC : ready.pc = word width (base + 6) := by
    simpa [ready, State.put, Nat.add_assoc] using advance five (base + 5) fivePC (by omega)
  have step0 : programStep program s = some one := by
    rw [fetched program s (base + 0) (.load 2 3) pc (by omega)
      (by simpa [fieldCode] using block 0 (by simp [fieldCode]))]
    simp [step, running, childAddress, headerAddress, childCursorVal, headerCursorVal,
      childBound, headerBound, childSource, headerSource, childVal, channelsVal, Nat.add_comm,
      one, State.put, State.advance]
  have step1 : programStep program one = some two := by
    rw [fetched program one (base + 1) (.load 0 1) onePC (by omega)
      (by simpa [fieldCode] using block 1 (by simp [fieldCode]))]
    simp [step, running, childAddress, headerAddress, childCursorVal, headerCursorVal,
      childBound, headerBound, childSource, headerSource, childVal, channelsVal, Nat.add_comm,
      one, two, State.put, State.advance]
  have step2 : programStep program two = some three := by
    rw [fetched program two (base + 2) (.add 2 2 0) twoPC (by omega)
      (by simpa [fieldCode] using block 2 (by simp [fieldCode]))]
    simp [step, running, childAddress, headerAddress, childCursorVal, headerCursorVal,
      childBound, headerBound, childSource, headerSource, childVal, channelsVal, Nat.add_comm,
      one, two, three, State.put, State.advance]
  have step3 : programStep program three = some four := by
    rw [fetched program three (base + 3) (.constant 0 (word width 0)) threePC (by omega)
      (by simpa [fieldCode] using block 3 (by simp [fieldCode]))]
    simp [step, running, childAddress, headerAddress, childCursorVal, headerCursorVal,
      childBound, headerBound, childSource, headerSource, childVal, channelsVal, Nat.add_comm,
      one, two, three, four, State.put, State.advance]
  have step4 : programStep program four = some five := by
    rw [fetched program four (base + 4) (.constant 1 (word width 0)) fourPC (by omega)
      (by simpa [fieldCode] using block 4 (by simp [fieldCode]))]
    simp [step, running, childAddress, headerAddress, childCursorVal, headerCursorVal,
      childBound, headerBound, childSource, headerSource, childVal, channelsVal, Nat.add_comm,
      one, two, three, four, five, State.put, State.advance]
  have step5 : programStep program five = some ready := by
    rw [fetched program five (base + 5) (.constant 3 (word width 0)) fivePC (by omega)
      (by simpa [fieldCode] using block 5 (by simp [fieldCode]))]
    simp [step, running, childAddress, headerAddress, childCursorVal, headerCursorVal,
      childBound, headerBound, childSource, headerSource, childVal, channelsVal, Nat.add_comm,
      one, two, three, four, five, ready, State.put, State.advance]
  have oneLive : one.liveWords = s.liveWords := rfl
  have twoLive : two.liveWords = s.liveWords := rfl
  have threeLive : three.liveWords = s.liveWords := rfl
  have fourLive : four.liveWords = s.liveWords := rfl
  have fiveLive : five.liveWords = s.liveWords := rfl
  have readyLive : ready.liveWords = s.liveWords := rfl
  refine ⟨ready, ?_, ?_, ?_, rfl, rfl, rfl, readyPC, running⟩
  · have trace := Execution.cons step0 (Execution.cons step1 (Execution.cons step2 (Execution.cons step3 (Execution.cons step4 (Execution.cons step5 (Execution.refl ready))))))
    simpa [oneLive, twoLive, threeLive, fourLive, fiveLive, readyLive] using trace
  · simp [one, two, three, four, five, ready, State.put, State.advance, InstructionEncoding.encode, InstructionEncoding.fields, word]
  · simp [one, two, three, four, five, ready, State.put, State.advance, word, Nat.mod_eq_of_lt sumFits]

/-- Ten fetched transitions append the exact four-word child-address record. -/
theorem record_execution (program : Program width 4) (s : State width 4)
    (child channels childCursor headerCursor base : ℕ)
    (childAddress : s.reg 3 = word width childCursor)
    (headerAddress : s.reg 1 = word width headerCursor)
    (childBound : childCursor < s.heap.size) (headerBound : headerCursor < s.heap.size)
    (childSource : s.heap[childCursor]'childBound = word width child)
    (headerSource : s.heap[headerCursor]'headerBound = word width channels)
    (sumFits : channels + child < 2 ^ width)
    (pc : s.pc = word width base) (running : s.halted = false)
    (fits : base + 10 < 2 ^ width) (room : s.heap.size + 4 ≤ 2 ^ width)
    (block : BlockAt program base (code width)) :
    ∃ final, Execution program s final 10 (s.liveWords + 4) ∧
      final.heap = s.heap ++ (InstructionEncoding.encode
        (.constant 0 (word width (channels + child)) : Instruction width 4)).toArray ∧
      (final.reg 2).val = channels + child ∧
      final.stack = s.stack ∧ final.output = s.output ∧
      final.pc = word width (base + 10) ∧ final.halted = false := by
  have headBlock := BlockAt.prefix program base (fieldCode width) InstructionRecordStore.recordCode block
  obtain ⟨ready, formed, encoded, exactAddress, heap, stack, output, position, active⟩ :=
    fields_execution program s child channels childCursor headerCursor base childAddress headerAddress
      childBound headerBound (by omega) (by omega) childSource headerSource sumFits pc running (by omega) headBlock
  have tailBlock : BlockAt program (base + 6) InstructionRecordStore.recordCode := by
    simpa using BlockAt.suffix program base (fieldCode width) InstructionRecordStore.recordCode block
  obtain ⟨final, stored, finalHeap, finalReg, finalStack, finalOutput, finalPC, finalActive⟩ :=
    InstructionRecordStore.record_execution program ready (.constant 0 (word width (channels + child)))
      (base + 6) encoded position active (by omega) (by rw [heap]; exact room) tailBlock
  have readyLive : ready.liveWords = s.liveWords := by simp [State.liveWords, heap, stack, output]
  refine ⟨final, ?_, ?_, ?_, finalStack.trans stack, finalOutput.trans output, ?_, finalActive⟩
  · have trace := formed.append stored
    rw [readyLive] at trace
    convert trace using 1 <;> omega
  · simpa [heap] using finalHeap
  · simpa [finalReg] using exactAddress
  · simpa [Nat.add_assoc] using finalPC

theorem source_prefix_preserved (old : Array (Word width)) (child channels : ℕ)
    (final : State width 4) (heap : final.heap = old ++ (InstructionEncoding.encode
      (.constant 0 (word width (channels + child)) : Instruction width 4)).toArray) :
    ∀ index, index < old.size → final.heap[index]? = old[index]? := by
  intro index bound
  rw [heap]
  simp [Array.getElem?_append, bound]

/-- The static kernel's forty stored words are independent of source headers. -/
theorem stored_execution (s : State width 4) (child channels childCursor headerCursor : ℕ)
    (childAddress : s.reg 3 = word width childCursor)
    (headerAddress : s.reg 1 = word width headerCursor)
    (childBound : childCursor < s.heap.size) (headerBound : headerCursor < s.heap.size)
    (childSource : s.heap[childCursor]'childBound = word width child)
    (headerSource : s.heap[headerCursor]'headerBound = word width channels)
    (sumFits : channels + child < 2 ^ width)
    (pc : s.pc = word width 0) (running : s.halted = false)
    (fits : 10 < 2 ^ width) (room : s.heap.size + 4 ≤ 2 ^ width) :
    ∃ final, Execution (program width) s final 10 (s.liveWords + 4) ∧
      final.heap = s.heap ++ (InstructionEncoding.encode
        (.constant 0 (word width (channels + child)) : Instruction width 4)).toArray ∧
      (final.reg 2).val = channels + child ∧
      final.stack = s.stack ∧ final.output = s.output ∧ final.halted = false ∧
      residentWords (program width) final = s.liveWords + 44 := by
  have block : BlockAt (program width) 0 (code width) := by
    intro offset bound
    simp [program, List.getElem?_toArray, List.getElem?_eq_getElem bound]
  obtain ⟨final, trace, heap, exactAddress, stack, output, position, active⟩ :=
    record_execution (program width) s child channels childCursor headerCursor 0 childAddress headerAddress
      childBound headerBound childSource headerSource sumFits pc running (by simpa using fits) room block
  refine ⟨final, trace, heap, exactAddress, stack, output, active, ?_⟩
  simp [residentWords, State.liveWords, heap, stack, output, InstructionEncoding.encode]
  omega
end Controller.Cost.SourceGateOperands
