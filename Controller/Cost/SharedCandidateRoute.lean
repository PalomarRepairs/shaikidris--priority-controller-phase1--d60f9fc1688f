module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedCandidateInput

@[expose] public section

/-! Boolean candidate guards either continue to the next test or skip the probe. -/
namespace Controller.Cost.SharedCandidateRoute
open Controller.Cost.RawTransferLoops

def code (width entry skip : Nat) (register : Fin 8) : Program width 8 :=
  #[.branchZero register (word width (entry + 3)), .constant 0 (word width 0), .branchZero 0 (word width skip)]

@[simp] theorem code_size (width entry skip : Nat) (register : Fin 8) :
    (code width entry skip register).size = 3 := rfl

theorem execution (resident : Program width 8) (state : State width 8)
    (entry skip : Nat) (register : Fin 8) (value : Bool)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 3 < 2 ^ width) (boolFits : 1 < 2 ^ width)
    (held : state.reg register = boolWord width value)
    (physical : CodeAt resident entry (code width entry skip register)) :
    ∃ final, Execution resident state final (if value then 3 else 1) state.liveWords ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (if value then skip else entry + 3) ∧ final.halted = false ∧
      (∀ index : Fin 8, index ≠ 0 → final.reg index = state.reg index) := by
  cases value with
  | false =>
    let final := { state.advance with pc := word width (entry + 3) }
    have transition : programStep resident state = some final := by
      rw [fetched resident state entry _ position (by omega)
        (show resident[entry]? = some (.branchZero register (word width (entry + 3))) by
          simpa [code] using physical ⟨0, by simp [code]⟩)]
      simp [step, running, held, boolWord, word, final]
    have live : final.liveWords = state.liveWords := rfl
    refine ⟨final, ?_, rfl, rfl, rfl, rfl, running, ?_⟩
    · simpa only [Bool.false_eq_true, ite_false, live, Nat.zero_add, Nat.max_self] using Execution.cons transition (Execution.refl final)
    · intro index different; rfl
  | true =>
    let entered := state.advance
    have enteredPC : entered.pc = word width (entry + 1) := advance_position state position (by omega)
    have transition : programStep resident state = some entered := by
      rw [fetched resident state entry _ position (by omega)
        (show resident[entry]? = some (.branchZero register (word width (entry + 3))) by
          simpa [code] using physical ⟨0, by simp [code]⟩)]
      simp [step, running, held, boolWord, word, Nat.mod_eq_of_lt boolFits, entered]
    obtain ⟨zeroed, zeroTrace, zeroPC, zeroValue, zeroHeap, zeroStack, zeroOutput, zeroRunning, zeroFrame⟩ :=
      SharedEvaluationReclaim.constant_execution resident (entry + 1) 0 0 entered enteredPC running (by omega)
        (by simpa [code] using physical ⟨1, by simp [code]⟩)
    let final := { zeroed.advance with pc := word width skip }
    have jumpStep : programStep resident zeroed = some final := by
      rw [fetched resident zeroed (entry + 2) _
        (by simpa only [Nat.add_assoc, Nat.reduceAdd] using zeroPC) (by omega)
        (show resident[entry + 2]? = some (.branchZero 0 (word width skip)) by
          simpa [code] using physical ⟨2, by simp [code]⟩)]
      simp [step, zeroRunning, zeroValue, word, final]
    have enteredLive : entered.liveWords = state.liveWords := rfl
    have zeroLive : zeroed.liveWords = state.liveWords := by
      simp only [State.liveWords, zeroHeap, zeroStack, zeroOutput]; rfl
    have finalLive : final.liveWords = state.liveWords := zeroLive
    have firstTrace : Execution resident state entered 1 state.liveWords := by
      simpa only [enteredLive, Nat.zero_add, Nat.max_self] using Execution.cons transition (Execution.refl entered)
    have lastTrace : Execution resident zeroed final 1 zeroed.liveWords := by
      simpa only [show final.liveWords = zeroed.liveWords from rfl, Nat.zero_add, Nat.max_self] using
        Execution.cons jumpStep (Execution.refl final)
    have joined := firstTrace.append (zeroTrace.append lastTrace)
    rw [enteredLive, zeroLive, Nat.max_self] at joined
    refine ⟨final, by simpa using joined, zeroHeap, zeroStack, zeroOutput, rfl, zeroRunning, ?_⟩
    intro index different
    exact zeroFrame index different

end Controller.Cost.SharedCandidateRoute
