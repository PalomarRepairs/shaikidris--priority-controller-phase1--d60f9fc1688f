module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedCandidateRoute

@[expose] public section

/-! Candidate membership is read from the retained baseline channel table. -/
namespace Controller.Cost.SharedCandidateRead
open Controller.Cost.RawTransferLoops Controller.Cost.ForestInputStored

def code (width base : Nat) : Program width 8 :=
  #[.constant 0 (word width base), .add 0 0 4, .load 1 0]

@[simp] theorem code_size (width base : Nat) : (code width base).size = 3 := rfl

theorem execution (resident : Program width 8) (state : State width 8)
    (heap : Array (Word width)) (values : Fin n → Bool) (channel : Fin n) (entry : Nat)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 3 < 2 ^ width) (capacity : heap.size + n < 2 ^ width)
    (heapStored : state.heap = withValues heap values)
    (candidateHeld : state.reg 4 = word width channel.val)
    (physical : CodeAt resident entry (code width heap.size)) :
    ∃ final, Execution resident state final 3 state.liveWords ∧
      final.reg 1 = boolWord width (values channel) ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry + 3) ∧ final.halted = false ∧
      (∀ register : Fin 8, register ≠ 0 → register ≠ 1 → final.reg register = state.reg register) := by
  obtain ⟨addressed, firstTrace, firstPC, firstValue, firstHeap, firstStack, firstOutput, firstRunning, firstFrame⟩ :=
    SharedEvaluationReclaim.constant_execution resident entry heap.size 0 state position running (by omega)
      (by simpa [code] using physical ⟨0, by simp [code]⟩)
  let indexed := addressed.advance.put 0 (word width (heap.size + channel.val))
  have indexStep : programStep resident addressed = some indexed := by
    rw [fetched resident addressed (entry + 1) _ firstPC (by omega)
      (show resident[entry + 1]? = some (.add 0 0 4) by simpa [code] using physical ⟨1, by simp [code]⟩)]
    have head : addressed.reg 4 = word width channel.val := (firstFrame 4 (by decide)).trans candidateHeld
    simp [step, firstRunning, firstValue, head,
      show (word width heap.size).val = heap.size from Nat.mod_eq_of_lt (by omega),
      show (word width channel.val).val = channel.val from Nat.mod_eq_of_lt (by omega), indexed]
  have indexedPC : indexed.pc = word width (entry + 2) := by
    simpa [indexed, State.put, Nat.add_assoc] using advance_position addressed firstPC (by omega)
  let final := indexed.advance.put 1 (boolWord width (values channel))
  have indexedHeap : indexed.heap = withValues heap values := firstHeap.trans heapStored
  have valid : heap.size + channel.val < indexed.heap.size := by rw [indexedHeap, withValues_size]; omega
  have cell : indexed.heap[heap.size + channel.val]'valid = boolWord width (values channel) := by
    simpa only [indexedHeap] using value_cell heap values channel
  have loadStep : programStep resident indexed = some final := by
    rw [fetched resident indexed (entry + 2) _ indexedPC (by omega)
      (show resident[entry + 2]? = some (.load 1 0) by simpa [code] using physical ⟨2, by simp [code]⟩)]
    have addressValue : (indexed.reg 0).val = heap.size + channel.val := by
      simp [indexed, State.put, word, Nat.mod_eq_of_lt (by omega : heap.size + channel.val < 2 ^ width)]
    simp [step, show indexed.halted = false from firstRunning, addressValue, valid, cell, final]
  have firstLive : addressed.liveWords = state.liveWords := by simp only [State.liveWords, firstHeap, firstStack, firstOutput]
  have indexedLive : indexed.liveWords = state.liveWords := firstLive
  have finalLive : final.liveWords = state.liveWords := firstLive
  have restTrace := Execution.cons indexStep (Execution.cons loadStep (Execution.refl final))
  have joined := firstTrace.append restTrace
  rw [firstLive, indexedLive, finalLive, Nat.max_self] at joined
  refine ⟨final, by simpa using joined, ?_, firstHeap, firstStack, firstOutput, ?_, firstRunning, ?_⟩
  · simp [final, State.put]
  · simpa [final, State.put, Nat.add_assoc] using advance_position indexed indexedPC (by omega)
  · intro register different0 different1
    simp only [final, indexed, State.put, State.advance, different0, different1, ite_false]
    exact firstFrame register different0

end Controller.Cost.SharedCandidateRead
