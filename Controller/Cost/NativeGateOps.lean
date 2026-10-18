module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.NativeGateRead

@[expose] public section

/-! Fetched accumulator operations used by the native circuit evaluator. -/
namespace Controller.Cost.NativeGateOps
open Controller.Cost.GateProgram

theorem fetch (resident : Program width 4) (state : State width 4)
    (entry : Nat) (instruction : Instruction width 4)
    (position : state.pc = word width entry) (fits : entry < 2 ^ width)
    (physical : resident[entry]? = some instruction) :
    programStep resident state = step instruction state := by
  unfold programStep
  rw [position, show (word width entry).val = entry from Nat.mod_eq_of_lt fits, physical]
  rfl

theorem advance_pc (state : State width 4) (entry : Nat)
    (position : state.pc = word width entry) (fits : entry < 2 ^ width) :
    state.advance.pc = word width (entry + 1) := by
  simp only [State.advance, position,
    show (word width entry).val = entry from Nat.mod_eq_of_lt fits]

theorem put_execution (resident : Program width 4) (state : State width 4)
    (instruction : Instruction width 4) (entry : Nat) (register : Fin 4) (value : Word width)
    (position : state.pc = word width entry) (fits : entry < 2 ^ width)
    (physical : resident[entry]? = some instruction)
    (transition : step instruction state = some (state.advance.put register value)) :
    Execution resident state (state.advance.put register value) 1 state.liveWords := by
  have fetched := fetch resident state entry instruction position fits physical
  rw [transition] at fetched
  have trace := Execution.cons fetched (Execution.refl (state.advance.put register value))
  simpa [State.liveWords, State.advance, State.put] using trace

theorem xor_word (width : Nat) (fits : 1 < 2 ^ width) (left right : Bool) :
    word width (Nat.xor (boolWord width left).val (boolWord width right).val) =
      boolWord width (left ^^ right) := by
  rw [boolWord_val width fits, boolWord_val width fits]
  cases left <;> cases right <;> rfl

end Controller.Cost.NativeGateOps
