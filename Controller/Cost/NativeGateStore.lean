module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.NativeGateRead

@[expose] public section

/-! Native gate results are phase-normalized and appended to the assignment
heap by three fetched instructions. -/
namespace Controller.Cost.NativeGateStore
open Controller.Cost.GateProgram

abbrev Code (width : Nat) := List (Instruction width 4)

def code (width : Nat) (phase : Bool) : Code width :=
  [.constant 2 (boolWord width (!phase)), .xor 3 3 2, .allocate 3]

@[simp] theorem code_length (width : Nat) (phase : Bool) :
    (code width phase).length = 3 := rfl

set_option maxHeartbeats 2000000 in
theorem execution (resident : Program width 4) (state : State width 4)
    (value phase : Bool) (entry : Nat)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 3 < 2 ^ width) (boolFits : 1 < 2 ^ width)
    (heapFits : state.heap.size < 2 ^ width)
    (held : state.reg 3 = boolWord width value)
    (physical : BlockAt resident entry (code width phase)) :
    ∃ final, Execution resident state final 3 (state.liveWords + 1) ∧
      final.heap = state.heap.push (boolWord width (value == phase)) ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry + 3) ∧ final.halted = false := by
  let first := state.advance.put 2 (boolWord width (!phase))
  let second := first.advance.put 3 (boolWord width (value == phase))
  let final := { second.advance with heap := state.heap.push (boolWord width (value == phase)) }
  have firstPC : first.pc = word width (entry + 1) := by
    simp only [first, State.put, State.advance, position,
      show (word width entry).val = entry from Nat.mod_eq_of_lt (by omega)]
  have secondPC : second.pc = word width (entry + 2) := by
    simp only [second, State.put, State.advance, firstPC,
      show (word width (entry + 1)).val = entry + 1 from Nat.mod_eq_of_lt (by omega)]
  have finalPC : final.pc = word width (entry + 3) := by
    simp only [final, State.advance, secondPC,
      show (word width (entry + 2)).val = entry + 2 from Nat.mod_eq_of_lt (by omega)]
  have fetched (s : State width 4) (pc : Nat) (instruction : Instruction width 4)
      (location : s.pc = word width pc) (fits : pc < 2 ^ width)
      (present : resident[pc]? = some instruction) : programStep resident s = step instruction s := by
    unfold programStep
    rw [location, show (word width pc).val = pc from Nat.mod_eq_of_lt fits, present]
    rfl
  have t₀ : programStep resident state = some first := by
    rw [fetched state entry _ position (by omega)
      (by simpa [code] using physical 0 (by simp [code]))]
    simp [step, running, first]
  have t₁ : programStep resident first = some second := by
    rw [fetched first (entry + 1) _ firstPC (by omega)
      (by simpa [code] using physical 1 (by simp [code]))]
    simp [step, first, second, State.advance, State.put, running, held]
    funext index
    by_cases equal : index = 3
    · subst index
      simpa using NativeGateRead.signed_word width boolFits value phase
    · simp [equal]
  have t₂ : programStep resident second = some final := by
    rw [fetched second (entry + 2) _ secondPC (by omega)
      (by simpa [code] using physical 2 (by simp [code]))]
    simp [step, first, second, final, State.advance, State.put, running, heapFits]
  have trace := Execution.cons t₀ (Execution.cons t₁ (Execution.cons t₂ (Execution.refl final)))
  refine ⟨final, ?_, rfl, rfl, rfl, finalPC, running⟩
  simpa [first, second, final, State.liveWords, State.advance, State.put, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
    Nat.max_eq_right (Nat.le_succ _)] using trace

end Controller.Cost.NativeGateStore
