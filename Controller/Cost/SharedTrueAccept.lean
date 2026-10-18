module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedTrueNativeFinish

@[expose] public section

namespace Controller.Cost.SharedTrueAccept
open Controller.Cost.GateProgram Controller.Cost.RawTransferLoops

def code (width : Nat) : Program width 8 := #[.constant 4 (word width 1), .halt]

@[simp] theorem code_size : (code width).size = 2 := rfl

theorem execution (program : Program width 8) (state : State width 8) (entry : Nat)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 2 < 2 ^ width) (physical : CodeAt program entry (code width)) :
    ∃ final, Execution program state final 2 state.liveWords ∧ final.halted = true ∧
      final.reg 4 = word width 1 ∧ final.heap = state.heap ∧ final.stack = state.stack ∧
      final.output = state.output := by
  obtain ⟨tagged, tagTrace, pc, tag, heap, stack, output, active, frame⟩ :=
    SharedEvaluationReclaim.constant_execution program entry 1 4 state position running (by omega)
      (by simpa [code] using physical ⟨0, by simp⟩)
  let final := { tagged.advance with halted := true }
  have transition : programStep program tagged = some final := by
    rw [fetched program tagged (entry + 1) .halt pc (by omega)
      (by simpa [code] using physical ⟨1, by simp⟩)]
    simp [step, active, final]
  have taggedLive : tagged.liveWords = state.liveWords := by simp only [State.liveWords, heap, stack, output]
  have last : Execution program tagged final 1 tagged.liveWords := by
    simpa only [show final.liveWords = tagged.liveWords from rfl, Nat.zero_add, Nat.max_self] using
      Execution.cons transition (Execution.refl final)
  exact ⟨final, by simpa only [taggedLive, Nat.max_self, Nat.reduceAdd] using tagTrace.append last,
    rfl, tag, heap, stack, output⟩

end Controller.Cost.SharedTrueAccept
