module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.EnumerationDriverAllocate

@[expose] public section

/-! Fixed control tails used by descent and sibling queries: mask updates,
mode selection and actual jumps preserve the counter and retained packet. -/
namespace Controller.Cost.EnumerationDriverControl
open Controller.Cost.GateProgram Controller.Cost.RawTransferLoops Controller.Cost.SharedDetectorAssembly

def modeCode (width mode done : Nat) : List (Instruction width 8) :=
  [.constant 5 (word width mode)] ++ EnumerationDriverCode.jump width done

@[simp] theorem modeCode_length : (modeCode width mode done).length = 3 := rfl

theorem mode_execution (program : Program width 8) (state : State width 8)
    (entry mode done : Nat) (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 3 < 2 ^ width) (present : SharedRootRead.BlockAt program entry (modeCode width mode done)) :
    ∃ final, Execution program state final 3 state.liveWords ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width done ∧ final.halted = false ∧ final.reg 5 = word width mode ∧
      (∀ register : Fin 8, register ≠ 0 → register ≠ 5 → final.reg register = state.reg register) := by
  obtain ⟨selected, first, pc, held, heap, stack, output, live, frame⟩ :=
    SharedEvaluationReclaim.constant_execution program entry mode 5 state position running (by omega)
      (by simpa [modeCode] using present 0 (by simp))
  have jumpAt : SharedRootRead.BlockAt program (entry + 1) (EnumerationDriverCode.jump width done) := by
    simpa using block_right program entry [.constant 5 (word width mode)] (EnumerationDriverCode.jump width done) present
  obtain ⟨final, second, finalHeap, finalStack, finalOutput, finalPC, finalRunning, finalFrame⟩ :=
    EnumerationOracle.jump_execution program selected (entry + 1) done pc live (by omega) jumpAt
  have selectedLive : selected.liveWords = state.liveWords := by simp only [State.liveWords, heap, stack, output]
  refine ⟨final, ?_, finalHeap.trans heap, finalStack.trans stack, finalOutput.trans output,
    finalPC, finalRunning, (finalFrame 5 (by decide)).trans held, ?_⟩
  · simpa only [selectedLive, Nat.max_self, Nat.reduceAdd] using first.append second
  · intro register notZero notFive; rw [finalFrame register notZero, frame register notFive]

def selectCode (width base : Nat) (value : Bool) (mode done : Nat) : List (Instruction width 8) :=
  EnumerationMaskWrite.code width base value ++ modeCode width mode done

@[simp] theorem selectCode_length : (selectCode width base value mode done).length = 7 := rfl

theorem select_execution (program : Program width 8) (state : State width 8)
    (entry offset cursor mode done : Nat) (packet : Array (Word width)) (masks : List (Word width)) (value : Bool)
    (position : state.pc = word width entry) (running : state.halted = false)
    (held : state.reg 3 = word width cursor) (inside : offset + cursor < masks.length)
    (heapStored : state.heap = packet ++ masks.toArray) (heapFits : state.heap.size < 2 ^ width)
    (room : entry + 7 < 2 ^ width)
    (present : SharedRootRead.BlockAt program entry (selectCode width (packet.size + offset) value mode done)) :
    ∃ final, Execution program state final 7 state.liveWords ∧
      final.heap = packet ++ (masks.set (offset + cursor) (boolWord width value)).toArray ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width done ∧ final.halted = false ∧ final.reg 3 = word width cursor ∧ final.reg 5 = word width mode := by
  have writeAt := block_left program entry (EnumerationMaskWrite.code width (packet.size + offset) value)
    (modeCode width mode done) present
  obtain ⟨updated, first, heap, stack, output, pc, live, frame⟩ :=
    EnumerationDriverMask.write_execution program state entry offset cursor packet masks value position running held inside heapStored
      heapFits (by omega) writeAt
  have modeAt : SharedRootRead.BlockAt program (entry + 4) (modeCode width mode done) := by
    simpa using block_right program entry (EnumerationMaskWrite.code width (packet.size + offset) value) (modeCode width mode done) present
  obtain ⟨final, second, finalHeap, finalStack, finalOutput, finalPC, finalRunning, finalMode, finalFrame⟩ :=
    mode_execution program updated (entry + 4) mode done pc live (by omega) modeAt
  have updatedLive : updated.liveWords = state.liveWords := by
    simp only [State.liveWords, heap, stack, output, heapStored, Array.size_append, List.size_toArray, List.length_set]
  refine ⟨final, ?_, finalHeap.trans heap, finalStack.trans stack, finalOutput.trans output,
    finalPC, finalRunning, ?_, finalMode⟩
  · simpa only [updatedLive, Nat.max_self, Nat.reduceAdd] using first.append second
  · rw [finalFrame 3 (by decide) (by decide), frame 3 (by decide) (by decide), held]

def pairCode (width firstBase secondBase : Nat) (firstValue secondValue : Bool) : List (Instruction width 8) :=
  EnumerationMaskWrite.code width firstBase firstValue ++ EnumerationMaskWrite.code width secondBase secondValue

@[simp] theorem pairCode_length : (pairCode width firstBase secondBase firstValue secondValue).length = 8 := rfl

theorem pair_execution (program : Program width 8) (state : State width 8)
    (entry firstOffset secondOffset cursor : Nat) (packet : Array (Word width)) (masks : List (Word width))
    (firstValue secondValue : Bool) (position : state.pc = word width entry) (running : state.halted = false)
    (held : state.reg 3 = word width cursor)
    (firstInside : firstOffset + cursor < masks.length) (secondInside : secondOffset + cursor < masks.length)
    (heapStored : state.heap = packet ++ masks.toArray) (heapFits : state.heap.size < 2 ^ width)
    (room : entry + 8 < 2 ^ width)
    (present : SharedRootRead.BlockAt program entry (pairCode width (packet.size + firstOffset) (packet.size + secondOffset) firstValue secondValue)) :
    ∃ final, Execution program state final 8 state.liveWords ∧
      final.heap = packet ++ ((masks.set (firstOffset + cursor) (boolWord width firstValue)).set (secondOffset + cursor) (boolWord width secondValue)).toArray ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry + 8) ∧ final.halted = false ∧
      (∀ register : Fin 8, register ≠ 0 → register ≠ 1 → final.reg register = state.reg register) := by
  have firstAt := block_left program entry (EnumerationMaskWrite.code width (packet.size + firstOffset) firstValue)
    (EnumerationMaskWrite.code width (packet.size + secondOffset) secondValue) present
  have secondAt : SharedRootRead.BlockAt program (entry + 4) (EnumerationMaskWrite.code width (packet.size + secondOffset) secondValue) := by
    simpa using block_right program entry (EnumerationMaskWrite.code width (packet.size + firstOffset) firstValue)
      (EnumerationMaskWrite.code width (packet.size + secondOffset) secondValue) present
  obtain ⟨middle, first, heap, stack, output, pc, live, frame⟩ :=
    EnumerationDriverMask.write_execution program state entry firstOffset cursor packet masks firstValue position running held firstInside heapStored
      heapFits (by omega) firstAt
  have middleSize : middle.heap.size = state.heap.size := by
    simp only [heap, heapStored, Array.size_append, List.size_toArray, List.length_set]
  obtain ⟨final, second, finalHeap, finalStack, finalOutput, finalPC, finalRunning, finalFrame⟩ :=
    EnumerationDriverMask.write_execution program middle (entry + 4) secondOffset cursor packet
      (masks.set (firstOffset + cursor) (boolWord width firstValue)) secondValue pc live
      ((frame 3 (by decide) (by decide)).trans held) (by simpa using secondInside) heap
      (by simpa only [middleSize] using heapFits) (by omega) secondAt
  have middleLive : middle.liveWords = state.liveWords := by simp only [State.liveWords, middleSize, stack, output]
  refine ⟨final, ?_, finalHeap, finalStack.trans stack, finalOutput.trans output, ?_, finalRunning, ?_⟩
  · simpa only [middleLive, Nat.max_self, Nat.reduceAdd] using first.append second
  · have offsetEq : entry + 4 + 4 = entry + 8 := by omega
    exact finalPC.trans (congrArg (word width) offsetEq)
  · intro register notZero notOne; rw [finalFrame register notZero notOne, frame register notZero notOne]

def incrementCode (width done : Nat) : List (Instruction width 8) :=
  EnumerationCounter.code width 1 ++ EnumerationDriverCode.jump width done

@[simp] theorem incrementCode_length : (incrementCode width done).length = 4 := rfl

theorem increment_execution (program : Program width 8) (state : State width 8)
    (entry cursor done : Nat) (position : state.pc = word width entry) (running : state.halted = false)
    (held : state.reg 3 = word width cursor) (fits : cursor + 1 < 2 ^ width)
    (room : entry + 4 < 2 ^ width) (present : SharedRootRead.BlockAt program entry (incrementCode width done)) :
    ∃ final, Execution program state final 4 state.liveWords ∧ final.reg 3 = word width (cursor + 1) ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width done ∧ final.halted = false ∧
      (∀ register : Fin 8, register ≠ 0 → register ≠ 3 → final.reg register = state.reg register) := by
  have counterAt := block_left program entry (EnumerationCounter.code width 1) (EnumerationDriverCode.jump width done) present
  obtain ⟨incremented, first, counter, heap, stack, output, pc, active, frame⟩ :=
    EnumerationCounter.increment_execution program state entry cursor position running held fits (by omega) counterAt
  have jumpAt : SharedRootRead.BlockAt program (entry + 2) (EnumerationDriverCode.jump width done) := by
    simpa using block_right program entry (EnumerationCounter.code width 1) (EnumerationDriverCode.jump width done) present
  obtain ⟨final, second, finalHeap, finalStack, finalOutput, finalPC, finalRunning, finalFrame⟩ :=
    EnumerationOracle.jump_execution program incremented (entry + 2) done pc active (by omega) jumpAt
  have counterLive : incremented.liveWords = state.liveWords := by simp only [State.liveWords, heap, stack, output]
  refine ⟨final, ?_, (finalFrame 3 (by decide)).trans counter, finalHeap.trans heap, finalStack.trans stack,
    finalOutput.trans output, finalPC, finalRunning, ?_⟩
  · simpa only [counterLive, Nat.max_self, Nat.reduceAdd] using first.append second
  · intro register notZero notThree; rw [finalFrame register notZero, frame register notZero notThree]

def pairModeCode (width firstBase secondBase : Nat) (firstValue secondValue : Bool) (mode done : Nat) : List (Instruction width 8) :=
  pairCode width firstBase secondBase firstValue secondValue ++ modeCode width mode done

@[simp] theorem pairModeCode_length : (pairModeCode width firstBase secondBase firstValue secondValue mode done).length = 11 := rfl

theorem pair_mode_execution (program : Program width 8) (state : State width 8)
    (entry firstOffset secondOffset cursor mode done : Nat) (packet : Array (Word width)) (masks : List (Word width))
    (firstValue secondValue : Bool) (position : state.pc = word width entry) (running : state.halted = false)
    (held : state.reg 3 = word width cursor)
    (firstInside : firstOffset + cursor < masks.length) (secondInside : secondOffset + cursor < masks.length)
    (heapStored : state.heap = packet ++ masks.toArray) (heapFits : state.heap.size < 2 ^ width)
    (room : entry + 11 < 2 ^ width)
    (present : SharedRootRead.BlockAt program entry (pairModeCode width (packet.size + firstOffset) (packet.size + secondOffset) firstValue secondValue mode done)) :
    ∃ final, Execution program state final 11 state.liveWords ∧
      final.heap = packet ++ ((masks.set (firstOffset + cursor) (boolWord width firstValue)).set (secondOffset + cursor) (boolWord width secondValue)).toArray ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width done ∧ final.halted = false ∧ final.reg 3 = word width cursor ∧ final.reg 5 = word width mode := by
  have pairAt := block_left program entry (pairCode width (packet.size + firstOffset) (packet.size + secondOffset) firstValue secondValue)
    (modeCode width mode done) present
  obtain ⟨updated, first, heap, stack, output, pc, active, frame⟩ :=
    pair_execution program state entry firstOffset secondOffset cursor packet masks firstValue secondValue position running held
      firstInside secondInside heapStored heapFits (by omega) pairAt
  have modeAt : SharedRootRead.BlockAt program (entry + 8) (modeCode width mode done) := by
    simpa using block_right program entry (pairCode width (packet.size + firstOffset) (packet.size + secondOffset) firstValue secondValue)
      (modeCode width mode done) present
  obtain ⟨final, second, finalHeap, finalStack, finalOutput, finalPC, finalRunning, finalMode, finalFrame⟩ :=
    mode_execution program updated (entry + 8) mode done pc active (by omega) modeAt
  have updatedLive : updated.liveWords = state.liveWords := by
    simp only [State.liveWords, heap, stack, output, heapStored, Array.size_append, List.size_toArray, List.length_set]
  refine ⟨final, ?_, finalHeap.trans heap, finalStack.trans stack, finalOutput.trans output, finalPC, finalRunning, ?_, finalMode⟩
  · simpa only [updatedLive, Nat.max_self, Nat.reduceAdd] using first.append second
  · rw [finalFrame 3 (by decide) (by decide), frame 3 (by decide) (by decide), held]


end Controller.Cost.EnumerationDriverControl
