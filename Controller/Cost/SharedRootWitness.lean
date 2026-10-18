module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedGraphRound

@[expose] public section

/-! Root observations update retained candidate witnesses by fetched instructions. -/
namespace Controller.Cost.SharedRootWitness
open Controller.Cost.RawTransferLoops

def code (width entry : Nat) : Program width 8 :=
  #[.pop 2, .branchZero 1 (word width (entry + 3)), .copy 2 4, .allocate 2]

@[simp] theorem code_size (width entry : Nat) : (code width entry).size = 4 := rfl

theorem execution (resident : Program width 8) (state : State width 8)
    (entry : Nat) (observed : Bool) (old candidate : Word width) (suffix : List (Word width))
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 4 < 2 ^ width) (boolFits : 1 < 2 ^ width)
    (heapFits : state.heap.size < 2 ^ width)
    (input : state.stack = old :: suffix)
    (rootReg : state.reg 1 = boolWord width observed) (candidateReg : state.reg 4 = candidate)
    (physical : CodeAt resident entry (code width entry)) :
    ∃ final ticks, Execution resident state final ticks state.liveWords ∧ ticks ≤ 4 ∧
      final.heap = state.heap.push (if observed then candidate else old) ∧
      final.stack = suffix ∧ final.output = state.output ∧
      final.pc = word width (entry + 4) ∧ final.halted = false ∧
      (∀ index : Fin 8, index ≠ 2 → final.reg index = state.reg index) := by
  let popped := { state.advance.put 2 old with stack := suffix }
  have popPC : popped.pc = word width (entry + 1) := by
    exact advance_position state position (by omega)
  have popStep : programStep resident state = some popped := by
    rw [fetched resident state entry _ position (by omega)
      (show resident[entry]? = some (.pop 2) by simpa [code] using physical ⟨0, by simp [code]⟩)]
    simp [step, running, input, popped]
  have poppedLive : popped.liveWords + 1 = state.liveWords := by
    simp [popped, State.liveWords, State.advance, State.put, input]; omega
  have value : (popped.reg 1).val = if observed then 1 else 0 := by
    simpa [popped, State.put, State.advance, rootReg] using boolWord_val width boolFits observed
  cases observed with
  | false =>
    let jumped := { popped.advance with pc := word width (entry + 3) }
    let final := { jumped.advance with heap := state.heap.push old }
    have jumpStep : programStep resident popped = some jumped := by
      rw [fetched resident popped (entry + 1) _ popPC (by omega)
        (show resident[entry + 1]? = some (.branchZero 1 (word width (entry + 3))) by
          simpa [code] using physical ⟨1, by simp [code]⟩)]
      simp [step, popped, State.put, State.advance, running, rootReg, boolWord, word, Nat.mod_eq_of_lt boolFits, jumped]
    have allocateStep : programStep resident jumped = some final := by
      rw [fetched resident jumped (entry + 3) _ rfl (by omega)
        (show resident[entry + 3]? = some (.allocate 2) by simpa [code] using physical ⟨3, by simp [code]⟩)]
      simp [step, jumped, popped, State.put, State.advance, running, heapFits, final]
    have jumpedLive : jumped.liveWords = popped.liveWords := rfl
    have finalLive : final.liveWords = state.liveWords := by
      simp [final, jumped, popped, State.liveWords, State.advance, State.put, input]; omega
    refine ⟨final, 3, ?_, by decide, rfl, rfl, rfl, ?_, running, ?_⟩
    · have trace := Execution.cons popStep (Execution.cons jumpStep
        (Execution.cons allocateStep (Execution.refl final)))
      simpa only [Nat.zero_add, Nat.reduceAdd, jumpedLive, finalLive, Nat.max_eq_left (by omega : popped.liveWords ≤ state.liveWords), Nat.max_eq_right (by omega : popped.liveWords ≤ state.liveWords), Nat.max_self] using trace
    · exact advance_position jumped rfl (by omega)
    · intro index different
      simp [final, jumped, popped, State.advance, State.put, different]
  | true =>
    let entered := popped.advance
    let copied := entered.advance.put 2 candidate
    let final := { copied.advance with heap := state.heap.push candidate }
    have enterPC : entered.pc = word width (entry + 2) := by
      simpa [entered, Nat.add_assoc] using advance_position popped popPC (by omega)
    have copyPC : copied.pc = word width (entry + 3) := by
      simpa [copied, State.put, Nat.add_assoc] using advance_position entered enterPC (by omega)
    have enterStep : programStep resident popped = some entered := by
      rw [fetched resident popped (entry + 1) _ popPC (by omega)
        (show resident[entry + 1]? = some (.branchZero 1 (word width (entry + 3))) by
          simpa [code] using physical ⟨1, by simp [code]⟩)]
      simp [step, popped, State.put, State.advance, running, rootReg, boolWord, word, Nat.mod_eq_of_lt boolFits, entered]
    have copyStep : programStep resident entered = some copied := by
      rw [fetched resident entered (entry + 2) _ enterPC (by omega)
        (show resident[entry + 2]? = some (.copy 2 4) by simpa [code] using physical ⟨2, by simp [code]⟩)]
      simp [step, entered, popped, State.put, State.advance, running, candidateReg, copied]
    have allocateStep : programStep resident copied = some final := by
      rw [fetched resident copied (entry + 3) _ copyPC (by omega)
        (show resident[entry + 3]? = some (.allocate 2) by simpa [code] using physical ⟨3, by simp [code]⟩)]
      simp [step, copied, entered, popped, State.put, State.advance, running, heapFits, final]
    have enteredLive : entered.liveWords = popped.liveWords := rfl
    have copiedLive : copied.liveWords = popped.liveWords := rfl
    have finalLive : final.liveWords = state.liveWords := by
      simp [final, copied, entered, popped, State.liveWords, State.advance, State.put, input]; omega
    refine ⟨final, 4, ?_, by decide, rfl, rfl, rfl, ?_, running, ?_⟩
    · have trace := Execution.cons popStep (Execution.cons enterStep (Execution.cons copyStep
        (Execution.cons allocateStep (Execution.refl final))))
      simpa only [Nat.zero_add, Nat.reduceAdd, enteredLive, copiedLive, finalLive, Nat.max_eq_left (by omega : popped.liveWords ≤ state.liveWords), Nat.max_eq_right (by omega : popped.liveWords ≤ state.liveWords), Nat.max_self] using trace
    · simpa [final, Nat.add_assoc] using advance_position copied copyPC (by omega)
    · intro index different
      simp [final, copied, entered, popped, State.advance, State.put, different]

end Controller.Cost.SharedRootWitness
