module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.OutputProgram
public import Controller.CNF.Tseitin

@[expose] public section

/-! Signed native literals are fetched from the stored assignment table.
The four-instruction read handles both literal phases and preserves the heap,
stack, outputs and gate-accumulator register. -/
namespace Controller.Cost.NativeGateRead
open Controller.Cost.GateProgram

abbrev Code (width : Nat) := List (Instruction width 4)

def code (width base : Nat) (literal : Controller.CNF.Literal (Fin variableCount)) : Code width :=
  [.constant 0 (word width (base + literal.1.val)), .load 1 0,
    .constant 2 (boolWord width (!literal.2)), .xor 1 1 2]

@[simp] theorem code_length (width base : Nat) (literal : Controller.CNF.Literal (Fin variableCount)) :
    (code width base literal).length = 4 := rfl

theorem signed_word (width : Nat) (capacity : 1 < 2 ^ width) (value phase : Bool) :
    word width (Nat.xor (boolWord width value).val (boolWord width (!phase)).val) =
      boolWord width (value == phase) := by
  rw [boolWord_val width capacity, boolWord_val width capacity]
  cases value <;> cases phase <;> rfl

set_option maxHeartbeats 2000000 in
theorem execution (resident : Program width 4) (state : State width 4)
    (values : Fin variableCount → Bool) (literal : Controller.CNF.Literal (Fin variableCount))
    (base entry : Nat) (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 4 < 2 ^ width) (addressFits : base + literal.1.val < 2 ^ width)
    (valid : base + literal.1.val < state.heap.size)
    (cell : state.heap[base + literal.1.val]'valid = boolWord width (values literal.1))
    (physical : BlockAt resident entry (code width base literal)) :
    ∃ final, Execution resident state final 4 state.liveWords ∧
      final.reg 1 = boolWord width (Controller.CNF.literalValue values literal) ∧
      final.reg 3 = state.reg 3 ∧ final.heap = state.heap ∧ final.stack = state.stack ∧
      final.output = state.output ∧ final.pc = word width (entry + 4) ∧ final.halted = false := by
  let first := state.advance.put 0 (word width (base + literal.1.val))
  let second := first.advance.put 1 (boolWord width (values literal.1))
  let third := second.advance.put 2 (boolWord width (!literal.2))
  let final := third.advance.put 1 (boolWord width (Controller.CNF.literalValue values literal))
  have firstPC : first.pc = word width (entry + 1) := by
    simp only [first, State.put, State.advance, position,
      show (word width entry).val = entry from Nat.mod_eq_of_lt (by omega)]
  have secondPC : second.pc = word width (entry + 2) := by
    simp only [second, State.put, State.advance, firstPC,
      show (word width (entry + 1)).val = entry + 1 from Nat.mod_eq_of_lt (by omega)]
  have thirdPC : third.pc = word width (entry + 3) := by
    simp only [third, State.put, State.advance, secondPC,
      show (word width (entry + 2)).val = entry + 2 from Nat.mod_eq_of_lt (by omega)]
  have finalPC : final.pc = word width (entry + 4) := by
    simp only [final, State.put, State.advance, thirdPC,
      show (word width (entry + 3)).val = entry + 3 from Nat.mod_eq_of_lt (by omega)]
  have at₀ : resident[entry]? = some (.constant 0 (word width (base + literal.1.val))) := by
    simpa [code] using physical 0 (by simp [code])
  have at₁ : resident[entry + 1]? = some (.load 1 0) := by
    simpa [code] using physical 1 (by simp [code])
  have at₂ : resident[entry + 2]? = some (.constant 2 (boolWord width (!literal.2))) := by
    simpa [code] using physical 2 (by simp [code])
  have at₃ : resident[entry + 3]? = some (.xor 1 1 2) := by
    simpa [code] using physical 3 (by simp [code])
  have fetched (s : State width 4) (pc : Nat) (instruction : Instruction width 4)
      (location : s.pc = word width pc) (fits : pc < 2 ^ width)
      (present : resident[pc]? = some instruction) : programStep resident s = step instruction s := by
    unfold programStep
    rw [location, show (word width pc).val = pc from Nat.mod_eq_of_lt fits, present]
    rfl
  have t₀ : programStep resident state = some first := by
    rw [fetched state entry _ position (by omega) at₀]
    simp [step, running, first]
  have t₁ : programStep resident first = some second := by
    rw [fetched first (entry + 1) _ firstPC (by omega) at₁]
    simp [step, first, second, State.put, State.advance, running,
      word, Nat.mod_eq_of_lt addressFits, valid, cell]
  have t₂ : programStep resident second = some third := by
    rw [fetched second (entry + 2) _ secondPC (by omega) at₂]
    simp [step, first, second, third, State.put, State.advance, running]
  have t₃ : programStep resident third = some final := by
    rw [fetched third (entry + 3) _ thirdPC (by omega) at₃]
    simp [step, first, second, third, final, State.put, State.advance, running,
      Controller.CNF.literalValue]
    funext index
    by_cases equal : index = 1
    · subst index
      simpa using signed_word width (by omega) (values literal.1) literal.2
    · simp [equal]
  have trace := Execution.cons t₀ (Execution.cons t₁ (Execution.cons t₂
    (Execution.cons t₃ (Execution.refl final))))
  refine ⟨final, ?_, ?_, ?_, rfl, rfl, rfl, finalPC, running⟩
  · simpa [first, second, third, final, State.liveWords, State.advance, State.put] using trace
  · simp [final, State.put]
  · simp [first, second, third, final, State.put, State.advance]

end Controller.Cost.NativeGateRead
