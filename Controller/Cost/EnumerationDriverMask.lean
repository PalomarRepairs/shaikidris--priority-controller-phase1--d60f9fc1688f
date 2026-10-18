module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.EnumerationDriverLayout

@[expose] public section

/-! Actual indexed prefix-cell reads and writes, preserving the exact retained
packet-plus-mask heap representation required by the shared oracle caller. -/
namespace Controller.Cost.EnumerationDriverMask
open Controller.Cost.GateProgram Controller.Cost.RawTransferLoops

theorem set_heap_eq (packet : Array (Word width)) (masks : List (Word width)) (index : Nat)
    (inside : index < masks.length) (value : Word width) :
    (packet ++ masks.toArray).set (packet.size + index) value (by simp; omega) =
      packet ++ (masks.set index value).toArray := by
  have appended := Array.set_append_right (xs := packet) (ys := masks.toArray)
    (i := packet.size + index) (x := value) (by simp; omega) (by omega)
  simpa only [Nat.add_sub_cancel_left, List.set_toArray] using appended

theorem write_execution (program : Program width 8) (state : State width 8)
    (entry offset cursor : Nat) (packet : Array (Word width)) (masks : List (Word width)) (value : Bool)
    (position : state.pc = word width entry) (running : state.halted = false)
    (held : state.reg 3 = word width cursor) (inside : offset + cursor < masks.length)
    (heapStored : state.heap = packet ++ masks.toArray)
    (heapFits : state.heap.size < 2 ^ width) (room : entry + 4 < 2 ^ width)
    (present : SharedRootRead.BlockAt program entry (EnumerationMaskWrite.code width (packet.size + offset) value)) :
    ∃ final, Execution program state final 4 state.liveWords ∧
      final.heap = packet ++ (masks.set (offset + cursor) (boolWord width value)).toArray ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry + 4) ∧ final.halted = false ∧
      (∀ register : Fin 8, register ≠ 0 → register ≠ 1 → final.reg register = state.reg register) := by
  have valid : packet.size + offset + cursor < state.heap.size := by
    rw [heapStored]; simp only [Array.size_append, List.size_toArray]; omega
  obtain ⟨final, trace, heap, stack, output, pc, live, frame⟩ :=
    EnumerationMaskWrite.execution program state entry (packet.size + offset) cursor value
      position running held valid heapFits room present
  have updated : state.heap.set (packet.size + offset + cursor) (boolWord width value) valid =
      packet ++ (masks.set (offset + cursor) (boolWord width value)).toArray := by
    simpa only [heapStored, Nat.add_assoc] using set_heap_eq packet masks (offset + cursor) inside (boolWord width value)
  exact ⟨final, trace, heap.trans updated, stack, output, pc, live, frame⟩

theorem read_execution (program : Program width 8) (state : State width 8)
    (entry offset cursor : Nat) (packet : Array (Word width)) (masks : List (Word width))
    (position : state.pc = word width entry) (running : state.halted = false)
    (held : state.reg 3 = word width cursor) (inside : offset + cursor < masks.length)
    (heapStored : state.heap = packet ++ masks.toArray)
    (heapFits : state.heap.size < 2 ^ width) (room : entry + 3 < 2 ^ width)
    (present : SharedRootRead.BlockAt program entry (EnumerationDriverCode.readBit width (packet.size + offset))) :
    ∃ final, Execution program state final 3 state.liveWords ∧
      final.reg 1 = masks[offset + cursor] ∧ final.heap = state.heap ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry + 3) ∧ final.halted = false ∧
      (∀ register : Fin 8, register ≠ 0 → register ≠ 1 → final.reg register = state.reg register) := by
  have valid : packet.size + offset + cursor < state.heap.size := by
    rw [heapStored]; simp only [Array.size_append, List.size_toArray]; omega
  obtain ⟨addressed, t0, pc0, held0, heap0, stack0, output0, running0, frame0⟩ :=
    SharedEvaluationReclaim.constant_execution program entry (packet.size + offset) 0 state position running (by omega)
      (by simpa [EnumerationDriverCode.readBit] using present 0 (by simp [EnumerationDriverCode.readBit]))
  obtain ⟨added, t1, pc1, held1, heap1, stack1, output1, running1, frame1⟩ :=
    EnumerationSteps.add_execution (program := program) addressed (entry + 1) 0 0 3 pc0 running0 (by omega)
      (by simpa [EnumerationDriverCode.readBit] using present 1 (by simp [EnumerationDriverCode.readBit]))
  have actualAddress : (added.reg 0).val = packet.size + offset + cursor := by
    rw [held1, held0, frame0 3 (by decide), held]
    simp only [word, Nat.mod_eq_of_lt (by omega : packet.size + offset < 2 ^ width),
      Nat.mod_eq_of_lt (by omega : cursor < 2 ^ width), Nat.mod_eq_of_lt (by omega : packet.size + offset + cursor < 2 ^ width)]
  obtain ⟨final, t2, pc2, held2, heap2, stack2, output2, running2, frame2⟩ :=
    EnumerationSteps.load_execution (program := program) added (entry + 1 + 1) 1 0 pc1 running1 (by omega)
      (by rw [actualAddress, heap1, heap0]; exact valid)
      (by simpa [EnumerationDriverCode.readBit, Nat.add_assoc] using present 2 (by simp [EnumerationDriverCode.readBit]))
  have actualCell : added.heap[(added.reg 0).val]? = some masks[offset + cursor] := by
    rw [actualAddress, heap1, heap0, heapStored, Nat.add_assoc]
    simp [inside]
  have live0 : addressed.liveWords = state.liveWords := by simp only [State.liveWords, heap0, stack0, output0]
  have live1 : added.liveWords = state.liveWords := by simp only [State.liveWords, heap1, stack1, output1, heap0, stack0, output0]
  refine ⟨final, ?_, held2.trans (Array.getElem?_eq_some_iff.mp actualCell).2, heap2.trans (heap1.trans heap0),
    stack2.trans (stack1.trans stack0), output2.trans (output1.trans output0), ?_, running2, ?_⟩
  · simpa only [live0, live1, Nat.max_self, Nat.reduceAdd] using t0.append (t1.append t2)
  · simpa only [Nat.add_assoc, Nat.reduceAdd] using pc2
  · intro register notZero notOne; rw [frame2 register notOne, frame1 register notZero, frame0 register notZero]

end Controller.Cost.EnumerationDriverMask
