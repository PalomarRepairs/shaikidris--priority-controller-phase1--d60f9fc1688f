module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.NativeCircuitExecution

@[expose] public section

/-! Native root words are consumed from the input stack and appended to the
assignment heap by fetched pop/allocate pairs. Moving a word retains the total
live storage and does not assume an already initialized assignment table. -/
namespace Controller.Cost.NativeRootLoad
open Controller.Cost.GateProgram Controller.Cost.NativeCircuitExecution

def code (width : Nat) : Nat → List (Instruction width 4)
  | 0 => []
  | count + 1 => [.pop 3, .allocate 3] ++ code width count

@[simp] theorem code_length (width count : Nat) : (code width count).length = 2 * count := by
  induction count with
  | zero => rfl
  | succ count ih => simp [code, ih]; omega

set_option maxHeartbeats 2000000 in
theorem execution (resident : Program width 4) (state : State width 4)
    (words suffix : List (Word width)) (entry : Nat)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 2 * words.length < 2 ^ width)
    (heapFits : state.heap.size + words.length < 2 ^ width)
    (input : state.stack = words ++ suffix)
    (physical : BlockAt resident entry (code width words.length)) :
    ∃ final, Execution resident state final (2 * words.length) state.liveWords ∧
      final.heap = state.heap ++ words.toArray ∧ final.stack = suffix ∧ final.output = state.output ∧
      final.pc = word width (entry + 2 * words.length) ∧ final.halted = false := by
  induction words generalizing state entry with
  | nil =>
    refine ⟨state, ?_, ?_, ?_, rfl, ?_, running⟩
    · simpa using Execution.refl (p := resident) state
    · simp
    · simpa using input
    · simpa using position
  | cons value rest ih =>
    let first := { state.advance.put 3 value with stack := rest ++ suffix }
    let middle := { first.advance with heap := state.heap.push value }
    have popFetch : resident[entry]? = some (.pop 3) := by
      simpa [code] using physical 0 (by simp [code])
    have allocateFetch : resident[entry + 1]? = some (.allocate 3) := by
      simpa [code] using physical 1 (by simp [code])
    have popStep : programStep resident state = some first := by
      rw [NativeGateOps.fetch resident state entry _ position (by simp only [List.length_cons] at room; omega) popFetch]
      simp [step, running, input, first]
    have firstPC : first.pc = word width (entry + 1) := by
      simpa [first, State.put] using NativeGateOps.advance_pc state entry position
        (by simp only [List.length_cons] at room; omega)
    have allocateStep : programStep resident first = some middle := by
      rw [NativeGateOps.fetch resident first (entry + 1) _ firstPC
        (by simp only [List.length_cons] at room; omega) allocateFetch]
      simp [step, first, middle, State.put, State.advance, running,
        show state.heap.size < 2 ^ width from by omega]
    have middlePC : middle.pc = word width (entry + 2) := by
      simpa [middle, Nat.add_assoc] using NativeGateOps.advance_pc first (entry + 1) firstPC
        (by simp only [List.length_cons] at room; omega)
    have middleLive : middle.liveWords = state.liveWords := by
      simp [middle, first, State.advance, State.put, State.liveWords, input]
      omega
    have firstLive : first.liveWords ≤ state.liveWords := by
      simp [first, State.advance, State.put, State.liveWords, input]
    have firstTrace : Execution resident state middle 2 state.liveWords := by
      have trace := Execution.cons popStep (Execution.cons allocateStep (Execution.refl middle))
      simpa only [middleLive, Nat.reduceAdd, Nat.max_eq_right firstLive, Nat.max_self] using trace
    have restBlock : BlockAt resident (entry + 2) (code width rest.length) := by
      simpa only [List.length_cons, List.length_nil, Nat.reduceAdd] using
        BlockAt.suffix resident entry [.pop 3, .allocate 3] (code width rest.length) physical
    obtain ⟨final, restTrace, finalHeap, finalStack, finalOutput, finalPC, finalRunning⟩ :=
      ih middle (entry + 2) middlePC running
        (by simp only [List.length_cons] at room; omega)
        (by simp only [middle, Array.size_push]; simp only [List.length_cons] at heapFits; omega)
        rfl restBlock
    refine ⟨final, ?_, ?_, finalStack, finalOutput, ?_, finalRunning⟩
    · simpa only [middleLive, Nat.max_self, List.length_cons, Nat.mul_add, Nat.mul_one,
        Nat.add_comm] using firstTrace.append restTrace
    · rw [finalHeap]
      change state.heap.push value ++ rest.toArray = state.heap ++ (value :: rest).toArray
      apply Array.toList_inj.mp
      simp [List.append_assoc]
    · simpa only [List.length_cons, Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using finalPC

def words (width : Nat) (values : Fin rootCount → Bool) : List (Word width) :=
  List.ofFn (fun index => boolWord width (values index))

@[simp] theorem words_length (width : Nat) (values : Fin rootCount → Bool) :
    (words width values).length = rootCount := by simp [words]

theorem table (width : Nat) (values : Fin rootCount → Bool) :
    TableStored (words width values).toArray 0 values := by
  refine ⟨by simp [words], ?_⟩
  intro index
  refine ⟨by simp [words], ?_⟩
  simp [words]

end Controller.Cost.NativeRootLoad
