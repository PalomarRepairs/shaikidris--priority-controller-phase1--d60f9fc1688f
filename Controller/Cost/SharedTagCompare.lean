module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedWitnessDecode

@[expose] public section

/-! A fetched word comparison directs the detector to the sentinel or candidate branch. -/
namespace Controller.Cost.SharedTagCompare
open Controller.Cost.RawTransferLoops

def code (width done sentinel : Nat) (register : Fin 8) : Program width 8 :=
  #[.constant 0 (word width sentinel), .xor 0 0 register, .branchZero 0 (word width done)]

@[simp] theorem code_size (width done sentinel : Nat) (register : Fin 8) :
    (code width done sentinel register).size = 3 := rfl

private theorem xor_zero_iff (left right : Nat) : Nat.xor left right = 0 ↔ right = left := by
  constructor
  · intro equal
    have derived := congrArg (fun value => Nat.xor left value) equal
    simpa [← Nat.xor_assoc] using derived
  · intro equal; subst right; simp

theorem execution (resident : Program width 8) (state : State width 8)
    (entry done sentinel value : Nat) (register : Fin 8) (different : register ≠ 0) (position : state.pc = word width entry)
    (running : state.halted = false) (room : entry + 3 < 2 ^ width)
    (sentinelFit : sentinel < 2 ^ width) (valueFits : value < 2 ^ width)
    (held : state.reg register = word width value)
    (physical : CodeAt resident entry (code width done sentinel register)) :
    ∃ final, Execution resident state final 3 state.liveWords ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (if value = sentinel then done else entry + 3) ∧ final.halted = false ∧
      (∀ register : Fin 8, register ≠ 0 → final.reg register = state.reg register) := by
  obtain ⟨counted, firstTrace, countedPC, countedValue, heap, stack, output, active, frame⟩ :=
    SharedEvaluationReclaim.constant_execution resident entry sentinel 0 state position running (by omega)
      (by simpa [code] using physical ⟨0, by simp [code]⟩)
  let tested := counted.advance.put 0 (word width (Nat.xor sentinel value))
  have testStep : programStep resident counted = some tested := by
    rw [fetched resident counted (entry + 1) _ countedPC (by omega)
      (show resident[entry + 1]? = some (.xor 0 0 register) by simpa [code] using physical ⟨1, by simp [code]⟩)]
    simp [step, active, countedValue, (frame register different).trans held,
      show (word width sentinel).val = sentinel from Nat.mod_eq_of_lt sentinelFit,
      show (word width value).val = value from Nat.mod_eq_of_lt valueFits, tested]
  have testedPC : tested.pc = word width (entry + 2) := by
    simpa [tested, State.put, Nat.add_assoc] using advance_position counted countedPC (by omega)
  let final := if value = sentinel then { tested.advance with pc := word width done } else tested.advance
  have lastStep : programStep resident tested = some final := by
    rw [fetched resident tested (entry + 2) _ testedPC (by omega)
      (show resident[entry + 2]? = some (.branchZero 0 (word width done)) by simpa [code] using physical ⟨2, by simp [code]⟩)]
    have checked : (tested.reg 0).val = 0 ↔ value = sentinel := by
      change Nat.xor sentinel value % 2 ^ width = 0 ↔ value = sentinel
      have xorFit : Nat.xor sentinel value < 2 ^ width := Nat.xor_lt_two_pow sentinelFit valueFits
      rw [Nat.mod_eq_of_lt xorFit]
      exact xor_zero_iff sentinel value
    simp only [step, show tested.halted = false from active, Bool.false_eq_true, ite_false, checked]
    rfl
  have countedLive : counted.liveWords = state.liveWords := by simp only [State.liveWords, heap, stack, output]
  have testedLive : tested.liveWords = state.liveWords := countedLive
  have finalLive : final.liveWords = state.liveWords := by
    dsimp [final]
    split <;> exact countedLive
  have rest := Execution.cons testStep (Execution.cons lastStep (Execution.refl final))
  have joined := firstTrace.append rest
  rw [countedLive, testedLive, finalLive, Nat.max_self] at joined
  refine ⟨final, by simpa using joined, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [final]; split <;> exact heap
  · dsimp [final]; split <;> exact stack
  · dsimp [final]; split <;> exact output
  · dsimp [final]
    split
    · rfl
    · simpa only [Nat.add_assoc, Nat.reduceAdd] using advance_position tested testedPC (by omega)
  · dsimp [final]; split <;> exact active
  · intro register different
    dsimp [final]
    split <;> simp only [tested, State.advance, State.put, different, ite_false] <;> exact frame register different


end Controller.Cost.SharedTagCompare
