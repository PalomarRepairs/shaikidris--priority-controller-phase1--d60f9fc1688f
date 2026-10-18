module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedZeroNativeChecked
public import Controller.Cost.SharedRootRead

@[expose] public section

/-! Fetched pushes and pops save and restore the caller's registers on its existing stack. -/
namespace Controller.Cost.SharedRegisterStack
open Controller.Cost.GateProgram Controller.Cost.RawTransferLoops

def saveCode (registers : List (Fin 8)) : List (Instruction width 8) := registers.map Instruction.push
def restoreCode (registers : List (Fin 8)) : List (Instruction width 8) := registers.map Instruction.pop

private theorem tail_block (resident : Program width 8) (entry : Nat) (head : Instruction width 8)
    (tail : List (Instruction width 8)) (physical : SharedRootRead.BlockAt resident entry (head :: tail)) :
    SharedRootRead.BlockAt resident (entry + 1) tail := by
  intro offset valid
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using physical (offset + 1) (by simp; omega)

theorem save_execution (resident : Program width 8) (state : State width 8) (entry : Nat)
    (registers : List (Fin 8)) (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + registers.length < 2 ^ width)
    (physical : SharedRootRead.BlockAt resident entry (saveCode registers)) :
    ∃ final, Execution resident state final registers.length (state.liveWords + registers.length) ∧
      final.heap = state.heap ∧ final.output = state.output ∧ final.reg = state.reg ∧
      final.stack = (registers.map state.reg).reverse ++ state.stack ∧
      final.pc = word width (entry + registers.length) ∧ final.halted = false := by
  induction registers generalizing state entry with
  | nil =>
    exact ⟨state, by simpa using Execution.refl (p := resident) state, rfl, rfl, rfl, by simp, by simpa using position, running⟩
  | cons register rest ih =>
    let middle := { state.advance with stack := state.reg register :: state.stack }
    have transition : programStep resident state = some middle := by
      rw [fetched resident state entry _ position (by simp only [List.length_cons] at room; omega)
        (show resident[entry]? = some (.push register) by simpa [saveCode] using physical 0 (by simp [saveCode]))]
      simp [step, running, middle]
    have middlePC : middle.pc = word width (entry + 1) := advance_position state position (by simp only [List.length_cons] at room; omega)
    obtain ⟨final, trace, heap, output, reg, stack, pc, active⟩ := ih middle (entry + 1) middlePC running
      (by simp only [List.length_cons] at room; omega) (tail_block _ _ _ _ physical)
    have live : middle.liveWords = state.liveWords + 1 := by simp [middle, State.liveWords, State.advance]; omega
    have joined := Execution.cons transition trace
    refine ⟨final, ?_, heap, output, reg, ?_, ?_, active⟩
    · rw [live] at joined
      convert joined using 1 <;> simp only [List.length_cons] <;> omega
    · simpa [middle, State.advance, List.reverse_cons, List.append_assoc] using stack
    · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using pc

theorem restore_execution (resident : Program width 8) (state : State width 8) (entry : Nat)
    (registers : List (Fin 8)) (saved : Fin 8 → Word width) (suffix : List (Word width))
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + registers.length < 2 ^ width) (input : state.stack = registers.map saved ++ suffix)
    (physical : SharedRootRead.BlockAt resident entry (restoreCode registers)) :
    ∃ final, Execution resident state final registers.length state.liveWords ∧
      final.heap = state.heap ∧ final.output = state.output ∧ final.stack = suffix ∧
      (∀ register, final.reg register = if register ∈ registers then saved register else state.reg register) ∧
      final.pc = word width (entry + registers.length) ∧ final.halted = false := by
  induction registers generalizing state entry with
  | nil =>
    exact ⟨state, by simpa using Execution.refl (p := resident) state, rfl, rfl, by simpa using input,
      by simp, by simpa using position, running⟩
  | cons register rest ih =>
    let middle := { state.advance.put register (saved register) with stack := rest.map saved ++ suffix }
    have transition : programStep resident state = some middle := by
      rw [fetched resident state entry _ position (by simp only [List.length_cons] at room; omega)
        (show resident[entry]? = some (.pop register) by simpa [restoreCode] using physical 0 (by simp [restoreCode]))]
      simp [step, running, input, middle]
    have middlePC : middle.pc = word width (entry + 1) := by
      simpa [middle, State.put] using advance_position state position (by simp only [List.length_cons] at room; omega)
    obtain ⟨final, trace, heap, output, stack, reg, pc, active⟩ := ih middle (entry + 1) middlePC running
      (by simp only [List.length_cons] at room; omega) rfl (tail_block _ _ _ _ physical)
    have live : middle.liveWords + 1 = state.liveWords := by
      simp [middle, State.liveWords, State.advance, State.put, input]; omega
    have joined := Execution.cons transition trace
    refine ⟨final, ?_, heap, output, stack, ?_, ?_, active⟩
    · simpa only [List.length_cons, Nat.max_eq_left (by omega : middle.liveWords ≤ state.liveWords)] using joined
    · intro target
      rw [reg]
      by_cases present : target ∈ rest
      · simp [present]
      · by_cases same : target = register
        · subst target; simp [present, middle, State.put]
        · simp [present, same, Ne.symm same, middle, State.put, State.advance]
    · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using pc

end Controller.Cost.SharedRegisterStack
