module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedRootClassify

@[expose] public section

/-! Candidate and healthy tags are fetched from the retained witness buffers before detector branching. -/
namespace Controller.Cost.SharedRootInspect
open Controller.Cost.GateProgram Controller.Cost.RawTransferLoops

def code (width n entry zeroQuery nextRoot : Nat) : Program width 8 :=
  #[.load 4 3, .pop 2] ++ SharedRootClassify.code width n (entry + 2) zeroQuery nextRoot

@[simp] theorem code_size (width n entry zeroQuery nextRoot : Nat) :
    (code width n entry zeroQuery nextRoot).size = 10 := by simp [code]

set_option maxHeartbeats 2000000 in
theorem execution (resident : Program width 8) (state : State width 8)
    (n entry zeroQuery nextRoot address : Nat) (target : Fin n) (healthy : Bool) (candidate : Word width)
    (suffix : List (Word width)) (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 10 < 2 ^ width) (capacity : n + 1 < 2 ^ width)
    (addressFits : address < 2 ^ width) (valid : address < state.heap.size)
    (addressHeld : state.reg 3 = word width address) (stored : state.heap[address]? = some candidate)
    (input : state.stack = (if healthy then word width target.val else word width (n + 1)) :: suffix)
    (physical : CodeAt resident entry (code width n entry zeroQuery nextRoot)) :
    ∃ final ticks, Execution resident state final ticks state.liveWords ∧ ticks ≤ 8 ∧
      final.heap = state.heap ∧ final.stack = suffix ∧ final.output = state.output ∧
      final.pc = word width (if healthy then zeroQuery else
        if candidate = word width (n + 1) then nextRoot else entry + 10) ∧
      final.halted = false ∧ final.reg 4 = candidate ∧ final.reg 3 = state.reg 3 ∧
      (∀ register : Fin 8, register ≠ 0 → register ≠ 2 → register ≠ 4 →
        final.reg register = state.reg register) := by
  have all := physical
  unfold code at all
  have readCode := RawSharedOrdered.takePrefix resident entry _ _ all
  have classifyCode := RawSharedOrdered.takeSuffix resident entry _ _ all
  let loaded := state.advance.put 4 candidate
  have cell : state.heap[address]'valid = candidate := by
    simpa only [Array.getElem?_eq_getElem valid, Option.some.injEq] using stored
  have loadStep : programStep resident state = some loaded := by
    rw [fetched resident state entry _ position (by omega)
      (show resident[entry]? = some (.load 4 3) by simpa using readCode ⟨0, by simp⟩)]
    simp [step, running, addressHeld, show (word width address).val = address from Nat.mod_eq_of_lt addressFits,
      valid, cell, loaded]
  have loadedPC : loaded.pc = word width (entry + 1) := by
    simpa [loaded, State.put] using advance_position state position (by omega)
  let ready := { loaded.advance.put 2 (if healthy then word width target.val else word width (n + 1)) with stack := suffix }
  have popStep : programStep resident loaded = some ready := by
    rw [fetched resident loaded (entry + 1) _ loadedPC (by omega)
      (show resident[entry + 1]? = some (.pop 2) by simpa using readCode ⟨1, by simp⟩)]
    simp [step, loaded, ready, State.advance, State.put, running, input]
  have readyPC : ready.pc = word width (entry + 2) := by
    simpa [ready, State.put, Nat.add_assoc] using advance_position loaded loadedPC (by omega)
  obtain ⟨final, ticks, classifyTrace, classifyTime, finalHeap, finalStack, finalOutput, finalPC,
    finalRunning, finalCandidate, finalCursor, finalFrame⟩ :=
    SharedRootClassify.execution resident ready n (entry + 2) zeroQuery nextRoot target healthy candidate
      readyPC running (by omega) capacity (by simp [ready, State.put])
      (by simp [ready, loaded, State.put, State.advance]) (by simpa using classifyCode)
  have loadedLive : loaded.liveWords = state.liveWords := rfl
  have readyLive : ready.liveWords + 1 = state.liveWords := by
    simp [ready, loaded, State.advance, State.put, State.liveWords, input]; omega
  have readTrace : Execution resident state ready 2 state.liveWords := by
    have trace := Execution.cons loadStep (Execution.cons popStep (Execution.refl ready))
    simpa only [loadedLive, Nat.reduceAdd, Nat.max_eq_left (by omega : ready.liveWords ≤ state.liveWords), Nat.max_self] using trace
  have joined := readTrace.append classifyTrace
  rw [Nat.max_eq_left (by omega : ready.liveWords ≤ state.liveWords)] at joined
  refine ⟨final, 2 + ticks, joined, by omega, finalHeap, finalStack, finalOutput,
    ?_, finalRunning, finalCandidate, ?_, ?_⟩
  · simpa only [Nat.add_assoc, Nat.reduceAdd] using finalPC
  · simpa [ready, loaded, State.advance, State.put] using finalCursor
  · intro register nonzero notTwo notFour
    simpa [ready, loaded, State.advance, State.put, nonzero, notTwo, notFour] using finalFrame register nonzero

end Controller.Cost.SharedRootInspect
