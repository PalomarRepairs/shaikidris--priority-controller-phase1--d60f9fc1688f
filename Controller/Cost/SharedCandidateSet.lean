module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedChannelStore
public import Controller.Cost.SharedReusableProbe

@[expose] public section

/-! Runtime candidate IDs address the retained channel table. -/
namespace Controller.Cost.SharedCandidateSet
open Controller.Cost.RawTransferLoops Controller.Cost.ForestInputStored

def code (width base : Nat) (value : Bool) : Program width 8 :=
  #[.constant 0 (word width base), .add 0 0 4,
    .constant 1 (boolWord width value), .store 0 1]

@[simp] theorem code_size (width base : Nat) (value : Bool) : (code width base value).size = 4 := rfl

theorem execution (resident : Program width 8) (state : State width 8)
    (heap : Array (Word width)) (values : Fin n → Bool) (channel : Fin n) (value : Bool)
    (entry : Nat) (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 4 < 2 ^ width) (capacity : heap.size + n < 2 ^ width)
    (heapStored : state.heap = withValues heap values)
    (candidateHeld : state.reg 4 = word width channel.val)
    (physical : CodeAt resident entry (code width heap.size value)) :
    ∃ final, Execution resident state final 4 state.liveWords ∧
      final.heap = withValues heap (fun index => if index = channel then value else values index) ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry + 4) ∧ final.halted = false ∧
      (∀ register : Fin 8, register ≠ 0 → register ≠ 1 → final.reg register = state.reg register) := by
  obtain ⟨addressed, firstTrace, firstPC, firstValue, firstHeap, firstStack, firstOutput, firstRunning, firstFrame⟩ :=
    SharedEvaluationReclaim.constant_execution resident entry heap.size 0 state position running (by omega)
      (by simpa [code] using physical ⟨0, by simp [code]⟩)
  let indexed := addressed.advance.put 0 (word width (heap.size + channel.val))
  have indexStep : programStep resident addressed = some indexed := by
    rw [fetched resident addressed (entry + 1) _ firstPC (by omega)
      (show resident[entry + 1]? = some (.add 0 0 4) by
        simpa [code] using physical ⟨1, by simp [code]⟩)]
    have head : addressed.reg 4 = word width channel.val :=
      (firstFrame 4 (by decide)).trans candidateHeld
    simp [step, firstRunning, firstValue, head,
      show (word width heap.size).val = heap.size from Nat.mod_eq_of_lt (by omega),
      show (word width channel.val).val = channel.val from Nat.mod_eq_of_lt (by omega), indexed]
  have indexedLive : indexed.liveWords = addressed.liveWords := rfl
  have indexTrace : Execution resident addressed indexed 1 addressed.liveWords := by
    simpa only [indexedLive, Nat.zero_add, Nat.max_self] using
      Execution.cons indexStep (Execution.refl indexed)
  have indexPC : indexed.pc = word width (entry + 2) := by
    simpa [indexed, State.put, Nat.add_assoc] using advance_position addressed firstPC (by omega)
  obtain ⟨ready, valueTrace, readyPC, readyValue, readyHeap, readyStack, readyOutput, readyRunning, readyFrame⟩ :=
    SharedEvaluationReclaim.constant_execution resident (entry + 2) (if value then 1 else 0) 1 indexed
      indexPC firstRunning (by omega)
      (by simpa [code, boolWord] using physical ⟨2, by simp [code]⟩)
  have stored : ready.heap = withValues heap values := readyHeap.trans (firstHeap.trans heapStored)
  have address : ready.reg 0 = word width (heap.size + channel.val) := by
    rw [readyFrame 0 (by decide)]
    simp [indexed, State.put]
  have lastCode : CodeAt resident (entry + 3) (SharedChannelStore.code width) := by
    intro phase
    rcases phase with ⟨index, bound⟩
    have indexZero : index = 0 := by simp [SharedChannelStore.code] at bound; omega
    subst index
    simpa [code, SharedChannelStore.code] using physical ⟨3, by simp [code]⟩
  obtain ⟨final, storeTrace, finalHeap, finalStack, finalOutput, finalPC, finalRunning, finalRegisters⟩ :=
    SharedChannelStore.channel_execution resident ready heap values channel value (entry + 3)
      (by simpa only [Nat.add_assoc, Nat.reduceAdd] using readyPC) readyRunning (by omega)
      capacity stored address (by simpa [boolWord] using readyValue) lastCode
  have firstLive : addressed.liveWords = state.liveWords := by
    simp only [State.liveWords, firstHeap, firstStack, firstOutput]
  have readyLive : ready.liveWords = state.liveWords := by
    simp only [State.liveWords, readyHeap, readyStack, readyOutput, indexed, State.put, State.advance,
      firstHeap, firstStack, firstOutput]
  have joined := firstTrace.append (indexTrace.append (valueTrace.append storeTrace))
  rw [readyLive, indexedLive, firstLive, Nat.max_self] at joined
  refine ⟨final, by simpa using joined, finalHeap, ?_, ?_, ?_, finalRunning, ?_⟩
  · exact finalStack.trans (readyStack.trans firstStack)
  · exact finalOutput.trans (readyOutput.trans firstOutput)
  · simpa only [Nat.add_assoc, Nat.reduceAdd] using finalPC
  · intro register different0 different1
    rw [finalRegisters, readyFrame register different1]
    simp only [indexed, State.put, State.advance, different0, ite_false]
    exact firstFrame register different0

end Controller.Cost.SharedCandidateSet
