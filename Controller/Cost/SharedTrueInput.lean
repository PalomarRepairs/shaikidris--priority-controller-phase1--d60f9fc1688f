module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedTrueChannelInput

@[expose] public section

namespace Controller.Cost.SharedTrueInput
open Controller.Cost.GateProgram Controller.Cost.RawTransferLoops

def code (width base entry : Nat) : List (Fin n) → List (Instruction width 8)
  | [] => []
  | channel :: rest => (SharedTrueChannelInput.code width entry (base + channel.val) channel.val).toList ++
      code width base (entry + 9) rest

@[simp] theorem code_length (channels : List (Fin n)) : (code width base entry channels).length = 9 * channels.length := by
  induction channels generalizing entry with
  | nil => simp [code]
  | cons channel rest ih => simp [code, ih, Nat.mul_add, Nat.add_comm]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4096 in
theorem execution (program : Program width 8) (state : State width 8) (T : Finset (Fin n))
    (tag : Word width) (base entry : Nat) (channels : List (Fin n))
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 9 * channels.length < 2 ^ width) (addressRoom : base + n < 2 ^ width)
    (tableBound : base + n ≤ state.heap.size) (held : state.reg 4 = tag)
    (stored : ∀ channel : Fin n, state.heap[base + channel.val]? =
      some (word width (if Controller.assignmentOfSet T channel then 1 else 0)))
    (physical : SharedRootRead.BlockAt program entry (code width base entry channels)) :
    ∃ final ticks, Execution program state final ticks (state.liveWords + channels.length) ∧ ticks ≤ 8 * channels.length ∧
      final.heap = state.heap ∧ final.output = state.output ∧
      final.stack = (channels.map (fun channel => word width
        (if Controller.assignmentOfSet (SharedWitnessDecode.decode T tag) channel then 1 else 0))).reverse ++ state.stack ∧
      final.reg 4 = tag ∧ final.pc = word width (entry + 9 * channels.length) ∧ final.halted = false := by
  induction channels generalizing state entry with
  | nil => exact ⟨state, 0, by simpa using Execution.refl (p := program) state, by simp, rfl, rfl,
      by simp, held, by simpa using position, running⟩
  | cons channel channels ih =>
    unfold code at physical
    have firstAt : CodeAt program entry (SharedTrueChannelInput.code width entry (base + channel.val) channel.val) := by
      intro phase
      have found := physical phase.val (by simp only [List.length_append, Array.length_toList, SharedTrueChannelInput.code_size, code_length]; have := phase.isLt; simp only [SharedTrueChannelInput.code_size] at this; omega)
      rw [List.getElem?_append_left (by simpa only [Array.length_toList] using phase.isLt)] at found
      simpa only [Array.getElem?_toList] using found
    have tailAt : SharedRootRead.BlockAt program (entry + 9) (code width base (entry + 9) channels) := by
      intro offset below
      have found := physical (9 + offset) (by simp only [List.length_append, Array.length_toList, SharedTrueChannelInput.code_size]; omega)
      rw [List.getElem?_append_right (by simp only [Array.length_toList, SharedTrueChannelInput.code_size]; omega)] at found
      simpa only [Array.length_toList, SharedTrueChannelInput.code_size, Nat.add_sub_cancel_left, Nat.add_assoc] using found
    obtain ⟨middle, firstTicks, firstTrace, firstTime, heap, output, stack, tagHeld, pc, active⟩ :=
      SharedTrueChannelInput.execution program state entry (base + channel.val) channel.val tag _ position running
        (by simp only [List.length_cons, Nat.mul_add] at room; omega) (by have := channel.isLt; omega)
        (by have := channel.isLt; omega) (by have := channel.isLt; omega) held (stored channel) firstAt
    have selected := SharedTrueChannelInput.decoded_bit T tag channel
    rw [← selected] at stack
    obtain ⟨final, tailTicks, tailTrace, tailTime, finalHeap, finalOutput, finalStack, finalTag, finalPC, finalRunning⟩ :=
      ih middle (entry + 9) pc active (by simp only [List.length_cons, Nat.mul_add] at room; omega)
        (by rw [heap]; exact tableBound) tagHeld (by intro next; rw [heap]; exact stored next) tailAt
    have live : middle.liveWords = state.liveWords + 1 := by
      simp only [State.liveWords, heap, output, stack, List.length_cons]
      omega
    refine ⟨final, firstTicks + tailTicks, ?_, ?_, finalHeap.trans heap, finalOutput.trans output, ?_, finalTag, ?_, finalRunning⟩
    · have joined := firstTrace.append tailTrace
      rw [live] at joined
      convert joined using 1
      simp only [List.length_cons]
      omega
    · simp only [List.length_cons, Nat.mul_add]; omega
    · simpa only [stack, List.map_cons, List.reverse_cons, List.append_assoc, List.singleton_append] using finalStack
    · convert finalPC using 1 <;> simp only [List.length_cons, Nat.mul_add] <;> congr 1 <;> omega


theorem all_channels (program : Program width 8) (state : State width 8) (T : Finset (Fin n))
    (tag : Word width) (base entry : Nat)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 9 * n < 2 ^ width) (addressRoom : base + n < 2 ^ width)
    (tableBound : base + n ≤ state.heap.size) (held : state.reg 4 = tag)
    (stored : ∀ channel : Fin n, state.heap[base + channel.val]? =
      some (word width (if Controller.assignmentOfSet T channel then 1 else 0)))
    (physical : SharedRootRead.BlockAt program entry (code width base entry (List.finRange n).reverse)) :
    ∃ final ticks, Execution program state final ticks (state.liveWords + n) ∧ ticks ≤ 8 * n ∧
      final.heap = state.heap ∧ final.output = state.output ∧
      final.stack = NativeRootLoad.words width (Controller.assignmentOfSet (SharedWitnessDecode.decode T tag)) ++ state.stack ∧
      final.reg 4 = tag ∧ final.pc = word width (entry + 9 * n) ∧ final.halted = false := by
  obtain ⟨final, ticks, trace, time, heap, output, stack, finalTag, pc, active⟩ :=
    execution program state T tag base entry (List.finRange n).reverse position running
      (by simpa using room) addressRoom tableBound held stored physical
  have words : ((List.finRange n).reverse.map (fun channel => word width
      (if Controller.assignmentOfSet (SharedWitnessDecode.decode T tag) channel then 1 else 0))).reverse =
      NativeRootLoad.words width (Controller.assignmentOfSet (SharedWitnessDecode.decode T tag)) := by
    rw [List.map_reverse, List.reverse_reverse]
    unfold NativeRootLoad.words
    rw [List.ofFn_eq_map]
    rfl
  exact ⟨final, ticks, by simpa using trace, by simpa using time, heap, output,
    by simpa only [words] using stack, finalTag, by simpa using pc, active⟩

end Controller.Cost.SharedTrueInput
