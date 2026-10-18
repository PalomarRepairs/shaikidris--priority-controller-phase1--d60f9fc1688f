module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedChannelStore
public import Controller.Cost.SharedWitnessSeed

@[expose] public section

/-! A baseline mask is consumed once and written into the retained channel table. -/
namespace Controller.Cost.SharedChannelRewrite
open Controller.Cost.GateProgram Controller.Cost.RawTransferLoops
open Controller.Cost.ForestInputStored

def code (width base : Nat) : List (Fin n) → List (Instruction width 8)
  | [] => []
  | channel :: rest => [.constant 0 (word width (base + channel.val)), .pop 1, .store 0 1] ++ code width base rest

@[simp] theorem code_length (channels : List (Fin n)) :
    (code width base channels).length = 3 * channels.length := by
  induction channels with
  | nil => rfl
  | cons channel rest ih => simp [code, ih]; omega

def replace (values fresh : Fin n → Bool) : List (Fin n) → Fin n → Bool
  | [] => values
  | channel :: rest => replace (fun index => if index = channel then fresh channel else values index) fresh rest

theorem replace_value (values fresh : Fin n → Bool) (channels : List (Fin n)) (index : Fin n) :
    replace values fresh channels index = if index ∈ channels then fresh index else values index := by
  induction channels generalizing values with
  | nil => simp [replace]
  | cons channel rest ih =>
    rw [replace, ih]
    by_cases same : index = channel <;> by_cases member : index ∈ rest <;> simp [same, member]

@[simp] theorem replace_all (values fresh : Fin n → Bool) :
    replace values fresh (List.finRange n) = fresh := by
  funext index
  simp [replace_value]

set_option maxHeartbeats 2000000 in
theorem execution (resident : Program width 8) (state : State width 8)
    (retained extras : Array (Word width)) (values fresh : Fin n → Bool) (channels : List (Fin n))
    (suffix : List (Word width)) (entry : Nat)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 3 * channels.length < 2 ^ width) (capacity : retained.size + n < 2 ^ width)
    (heapStored : state.heap = withValues retained values ++ extras)
    (input : state.stack = channels.map (fun channel => boolWord width (fresh channel)) ++ suffix)
    (physical : SharedRootRead.BlockAt resident entry (code width retained.size channels)) :
    ∃ final, Execution resident state final (3 * channels.length) state.liveWords ∧
      final.heap = withValues retained (replace values fresh channels) ++ extras ∧
      final.stack = suffix ∧ final.output = state.output ∧
      final.pc = word width (entry + 3 * channels.length) ∧ final.halted = false ∧
      final.reg 4 = state.reg 4 := by
  induction channels generalizing state values entry with
  | nil =>
    refine ⟨state, ?_, heapStored, by simpa using input, rfl, by simpa using position, running, rfl⟩
    simpa using Execution.refl (p := resident) state
  | cons channel rest ih =>
    let first := state.advance.put 0 (word width (retained.size + channel.val))
    let popped := { first.advance.put 1 (boolWord width (fresh channel)) with
      stack := rest.map (fun channel => boolWord width (fresh channel)) ++ suffix }
    let nextValues := fun index => if index = channel then fresh channel else values index
    have f0 : resident[entry]? = some (.constant 0 (word width (retained.size + channel.val))) := by
      simpa [code] using physical 0 (by simp [code])
    have f1 : resident[entry + 1]? = some (.pop 1) := by
      simpa [code] using physical 1 (by simp [code])
    have firstStep : programStep resident state = some first := by
      rw [fetched resident state entry _ position (by simp only [List.length_cons] at room; omega) f0]
      simp [step, running, first]
    have firstPC : first.pc = word width (entry + 1) := by
      simpa [first, State.put] using advance_position state position (by simp only [List.length_cons] at room; omega)
    have popStep : programStep resident first = some popped := by
      rw [fetched resident first (entry + 1) _ firstPC (by simp only [List.length_cons] at room; omega) f1]
      simp [step, first, popped, State.put, State.advance, running, input]
    have poppedPC : popped.pc = word width (entry + 2) := by
      simpa [popped, State.put, Nat.add_assoc] using advance_position first firstPC
        (by simp only [List.length_cons] at room; omega)
    have storeCode : CodeAt resident (entry + 2) (SharedChannelStore.code width) := by
      intro offset
      have offsetZero : offset.val = 0 := by have bound := offset.isLt; simp at bound; omega
      simpa [SharedChannelStore.code, offsetZero, code] using physical 2 (by simp [code])
    have poppedHeap : popped.heap = withValues retained values ++ extras := by
      simpa [popped, first, State.put, State.advance] using heapStored
    have validAddress : retained.size + channel.val < popped.heap.size := by
      rw [poppedHeap]; simp only [Array.size_append, withValues_size]; omega
    obtain ⟨middle, storeTrace, storedHeap, middleStack, middleOutput, middlePC, middleRunning, middleReg⟩ :=
      SharedChannelStore.execution resident popped (entry + 2) (retained.size + channel.val)
        (boolWord width (fresh channel)) poppedPC
        (by simpa [popped, first, State.put, State.advance] using running)
        (by simp only [List.length_cons] at room; omega) (by omega) validAddress
        (by simp [popped, first, State.put, State.advance]) (by simp [popped, State.put]) storeCode
    have middleHeap : middle.heap = withValues retained nextValues ++ extras := by
      have changed := SharedChannelStore.stored_update retained values channel (fresh channel)
      simpa only [poppedHeap, Array.set_append_left (by simp : retained.size + channel.val < (withValues retained values).size), changed] using storedHeap
    have firstLive : first.liveWords = state.liveWords := by simp [first, State.advance, State.put, State.liveWords]
    have poppedLive : popped.liveWords + 1 = state.liveWords := by
      simp [popped, first, State.advance, State.put, State.liveWords, input]; omega
    have middleLive : middle.liveWords = popped.liveWords := by
      simp only [State.liveWords, middleHeap, withValues_size, middleStack, middleOutput,
        popped, first, State.advance, State.put, heapStored, withValues_size, Array.size_append]
    have pairTrace : Execution resident state popped 2 state.liveWords := by
      have trace := Execution.cons firstStep (Execution.cons popStep (Execution.refl popped))
      simpa only [firstLive, Nat.reduceAdd, Nat.max_eq_left (by omega : popped.liveWords ≤ state.liveWords), Nat.max_self] using trace
    have restBlock : SharedRootRead.BlockAt resident (entry + 3) (code width retained.size rest) := by
      intro offset valid
      have offsetBound : offset < 3 * rest.length := by simpa using valid
      have restFetch := physical (3 + offset) (by simp [code]; omega)
      simpa [code, List.getElem_append_right, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using restFetch
    obtain ⟨final, restTrace, finalHeap, finalStack, finalOutput, finalPC, finalRunning, finalReg⟩ :=
      ih middle nextValues (entry + 3) (by simpa [Nat.add_assoc] using middlePC) middleRunning
        (by simp only [List.length_cons] at room; omega) middleHeap
        (by simpa [popped] using middleStack) restBlock
    refine ⟨final, ?_, finalHeap, finalStack, ?_, ?_, finalRunning, ?_⟩
    · have joined := pairTrace.append (storeTrace.append restTrace)
      rw [middleLive, Nat.max_self, Nat.max_eq_left (by omega : popped.liveWords ≤ state.liveWords)] at joined
      convert joined using 1 <;> simp only [List.length_cons] <;> omega
    · simpa [popped, first, State.advance, State.put] using finalOutput.trans middleOutput
    · simpa only [List.length_cons, Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using finalPC
    · simpa [popped, first, State.advance, State.put] using finalReg.trans (congrFun middleReg 4)

end Controller.Cost.SharedChannelRewrite
