module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedGraphReclaim

@[expose] public section

/-! Channel updates use fetched stores in the retained graph heap. -/
namespace Controller.Cost.SharedChannelStore
open Controller.Cost.RawTransferLoops

/-- The address and Boolean are runtime register operands. -/
def code (width : Nat) : Program width 8 := #[.store 0 1]

@[simp] theorem code_size (width : Nat) : (code width).size = 1 := rfl

theorem execution (resident : Program width 8) (state : State width 8)
    (entry address : Nat) (value : Word width)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 1 < 2 ^ width) (addressFits : address < 2 ^ width)
    (valid : address < state.heap.size)
    (addressReg : state.reg 0 = word width address) (valueReg : state.reg 1 = value)
    (physical : CodeAt resident entry (code width)) :
    ∃ final, Execution resident state final 1 state.liveWords ∧
      final.heap = state.heap.set address value ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry + 1) ∧ final.halted = false ∧
      final.reg = state.reg := by
  let final := { state.advance with heap := state.heap.set address value }
  have instruction : resident[entry]? = some (.store 0 1) := by
    simpa [code] using physical ⟨0, by simp [code]⟩
  have transition : programStep resident state = some final := by
    rw [fetched resident state entry _ position (by omega) instruction]
    simp [step, running, addressReg, valueReg,
      show (word width address).val = address from Nat.mod_eq_of_lt addressFits,
      valid, final]
  have live : final.liveWords = state.liveWords := by
    simp [final, State.advance, State.liveWords]
  refine ⟨final, ?_, rfl, rfl, rfl, ?_, running, rfl⟩
  · simpa only [live, Nat.zero_add, Nat.max_self] using
      Execution.cons transition (Execution.refl final)
  · exact advance_position state position (by omega)


open Controller.Cost.ForestInputStored

theorem stored_update (heap : Array (Word width)) (values : Fin n → Bool)
    (channel : Fin n) (value : Bool) :
    (withValues heap values).set (heap.size + channel.val) (boolWord width value)
      (by simp) =
    withValues heap (fun index => if index = channel then value else values index) := by
  unfold withValues
  rw [Array.set_append_right (by simp) (by omega)]
  simp only [Nat.add_sub_cancel_left]
  congr 1
  apply Array.ext
  · simp
  · intro index leftBound rightBound
    simp only [List.size_toArray, List.length_ofFn] at rightBound
    simp only [Array.getElem_set, List.getElem_toArray, List.getElem_ofFn]
    by_cases same : index = channel.val
    · subst index
      simp
    · have different : (⟨index, rightBound⟩ : Fin n) ≠ channel := by
        intro equal
        exact same (congrArg Fin.val equal)
      simp [same, Ne.symm same, different]


theorem channel_execution (resident : Program width 8) (state : State width 8)
    (heap : Array (Word width)) (values : Fin n → Bool) (channel : Fin n) (value : Bool)
    (entry : Nat) (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 1 < 2 ^ width) (capacity : heap.size + n < 2 ^ width)
    (heapStored : state.heap = withValues heap values)
    (addressReg : state.reg 0 = word width (heap.size + channel.val))
    (valueReg : state.reg 1 = boolWord width value)
    (physical : CodeAt resident entry (code width)) :
    ∃ final, Execution resident state final 1 state.liveWords ∧
      final.heap = withValues heap (fun index => if index = channel then value else values index) ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry + 1) ∧ final.halted = false ∧ final.reg = state.reg := by
  have valid : heap.size + channel.val < state.heap.size := by
    rw [heapStored, withValues_size]
    omega
  obtain ⟨final, trace, heapEq, stack, output, pc, halted, registers⟩ :=
    execution resident state entry (heap.size + channel.val) (boolWord width value)
      position running room (by omega) valid addressReg valueReg physical
  refine ⟨final, trace, ?_, stack, output, pc, halted, registers⟩
  have updated := stored_update heap values channel value
  simpa only [heapStored] using heapEq.trans (by simpa only [heapStored] using updated)

end Controller.Cost.SharedChannelStore
