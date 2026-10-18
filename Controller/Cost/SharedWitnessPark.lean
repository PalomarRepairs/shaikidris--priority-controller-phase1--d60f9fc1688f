module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedCandidateProbe

@[expose] public section

/-! Witness words move temporarily to the heap to expose candidate input bits. -/
namespace Controller.Cost.SharedWitnessPark
open Controller.Cost.RawTransferLoops

private theorem advance_pc (state : State width 8) (entry : Nat)
    (position : state.pc = word width entry) (fits : entry < 2 ^ width) :
    state.advance.pc = word width (entry + 1) := advance_position state position fits

private theorem suffix_block (program : Program width 8) (base : Nat)
    (first rest : List (Instruction width 8))
    (stored : SharedRootRead.BlockAt program base (first ++ rest)) :
    SharedRootRead.BlockAt program (base + first.length) rest := by
  intro offset bound
  have whole := stored (first.length + offset) (by simp only [List.length_append]; omega)
  rw [List.getElem?_append_right (by omega)] at whole
  simpa only [Nat.add_sub_cancel_left, Nat.add_assoc] using whole

def code (width : Nat) : Nat → List (Instruction width 8)
  | 0 => []
  | count + 1 => [.pop 3, .allocate 3] ++ code width count

@[simp] theorem code_length (width count : Nat) : (code width count).length = 2 * count := by
  induction count with
  | zero => rfl
  | succ count ih => simp [code, ih]; omega

set_option maxHeartbeats 2000000 in
theorem execution (resident : Program width 8) (state : State width 8)
    (words suffix : List (Word width)) (entry : Nat)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 2 * words.length < 2 ^ width)
    (heapFits : state.heap.size + words.length < 2 ^ width)
    (input : state.stack = words ++ suffix)
    (physical : SharedRootRead.BlockAt resident entry (code width words.length)) :
    ∃ final, Execution resident state final (2 * words.length) state.liveWords ∧
      final.heap = state.heap ++ words.toArray ∧ final.stack = suffix ∧ final.output = state.output ∧
      final.pc = word width (entry + 2 * words.length) ∧ final.halted = false ∧
      (∀ register : Fin 8, register ≠ 3 → final.reg register = state.reg register) := by
  induction words generalizing state entry with
  | nil =>
    refine ⟨state, ?_, ?_, ?_, rfl, ?_, running, ?_⟩
    · simpa using Execution.refl (p := resident) state
    · simp
    · simpa using input
    · simpa using position
    · intro register different; rfl
  | cons value rest ih =>
    let first := { state.advance.put 3 value with stack := rest ++ suffix }
    let middle := { first.advance with heap := state.heap.push value }
    have popFetch : resident[entry]? = some (.pop 3) := by
      simpa [code] using physical 0 (by simp [code])
    have allocateFetch : resident[entry + 1]? = some (.allocate 3) := by
      simpa [code] using physical 1 (by simp [code])
    have popStep : programStep resident state = some first := by
      rw [fetched resident state entry _ position (by simp only [List.length_cons] at room; omega) popFetch]
      simp [step, running, input, first]
    have firstPC : first.pc = word width (entry + 1) := by
      simpa [first, State.put] using advance_pc state entry position
        (by simp only [List.length_cons] at room; omega)
    have allocateStep : programStep resident first = some middle := by
      rw [fetched resident first (entry + 1) _ firstPC
        (by simp only [List.length_cons] at room; omega) allocateFetch]
      simp [step, first, middle, State.put, State.advance, running,
        show state.heap.size < 2 ^ width from by omega]
    have middlePC : middle.pc = word width (entry + 2) := by
      simpa [middle, Nat.add_assoc] using advance_pc first (entry + 1) firstPC
        (by simp only [List.length_cons] at room; omega)
    have middleLive : middle.liveWords = state.liveWords := by
      simp [middle, first, State.advance, State.put, State.liveWords, input]
      omega
    have firstLive : first.liveWords ≤ state.liveWords := by
      simp [first, State.advance, State.put, State.liveWords, input]
    have firstTrace : Execution resident state middle 2 state.liveWords := by
      have trace := Execution.cons popStep (Execution.cons allocateStep (Execution.refl middle))
      simpa only [middleLive, Nat.reduceAdd, Nat.max_eq_right firstLive, Nat.max_self] using trace
    have restBlock : SharedRootRead.BlockAt resident (entry + 2) (code width rest.length) := by
      simpa only [List.length_cons, List.length_nil, Nat.reduceAdd] using
        suffix_block resident entry [.pop 3, .allocate 3] (code width rest.length) physical
    obtain ⟨final, restTrace, finalHeap, finalStack, finalOutput, finalPC, finalRunning, finalFrame⟩ :=
      ih middle (entry + 2) middlePC running
        (by simp only [List.length_cons] at room; omega)
        (by simp only [middle, Array.size_push]; simp only [List.length_cons] at heapFits; omega)
        rfl restBlock
    refine ⟨final, ?_, ?_, finalStack, finalOutput, ?_, finalRunning, ?_⟩
    · simpa only [middleLive, Nat.max_self, List.length_cons, Nat.mul_add, Nat.mul_one,
        Nat.add_comm] using firstTrace.append restTrace
    · rw [finalHeap]
      change state.heap.push value ++ rest.toArray = state.heap ++ (value :: rest).toArray
      apply Array.toList_inj.mp
      simp [List.append_assoc]
    · simpa only [List.length_cons, Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using finalPC
    · intro register different
      rw [finalFrame register different]
      simp [middle, first, State.advance, State.put, different]

end Controller.Cost.SharedWitnessPark
