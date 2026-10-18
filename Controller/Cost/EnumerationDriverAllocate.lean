module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.EnumerationDriverMask

@[expose] public section

/-! Fetched allocation of the driver's initial mask region. Every supplied
compile-time initial mask word is stored, without changing stack or output. -/
namespace Controller.Cost.EnumerationDriverAllocate
open Controller.Cost.GateProgram Controller.Cost.RawTransferLoops Controller.Cost.SharedDetectorAssembly

private theorem cell_execution (program : Program width 8) (state : State width 8)
    (entry : Nat) (value : Word width) (position : state.pc = word width entry)
    (running : state.halted = false) (room : entry + 2 < 2 ^ width)
    (heapFits : state.heap.size < 2 ^ width)
    (present : SharedRootRead.BlockAt program entry [.constant 0 value, .allocate 0]) :
    ∃ final, Execution program state final 2 (state.liveWords + 1) ∧
      final.heap = state.heap.push value ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry + 2) ∧ final.halted = false ∧
      (∀ register : Fin 8, register ≠ 0 → final.reg register = state.reg register) := by
  have wordValue : word width value.val = value := by apply Fin.ext; exact Nat.mod_eq_of_lt value.isLt
  obtain ⟨loaded, first, pc, held, heap, stack, output, live, frame⟩ :=
    SharedEvaluationReclaim.constant_execution program entry value.val 0 state position running (by omega)
      (by simpa [wordValue] using present 0 (by simp))
  obtain ⟨final, second, finalPC, finalHeap, finalStack, finalOutput, finalRunning, finalFrame, finalLive⟩ :=
    EnumerationSteps.allocate_execution (program := program) loaded (entry + 1) 0 pc live (by omega)
      (by simpa only [heap] using heapFits) (by simpa using present 1 (by simp))
  have loadedLive : loaded.liveWords = state.liveWords := by simp only [State.liveWords, heap, stack, output]
  refine ⟨final, ?_, ?_, finalStack.trans stack, finalOutput.trans output, ?_, finalRunning, ?_⟩
  · simpa only [loadedLive, Nat.max_eq_right (Nat.le_succ _)] using first.append second
  · rw [finalHeap, heap, held, wordValue]
  · simpa only [Nat.add_assoc, Nat.reduceAdd] using finalPC
  · intro register other; rw [finalFrame, frame register other]

theorem execution (program : Program width 8) (state : State width 8)
    (entry : Nat) (words : List (Word width)) (position : state.pc = word width entry)
    (running : state.halted = false) (room : entry + 2 * words.length < 2 ^ width)
    (heapFits : state.heap.size + words.length ≤ 2 ^ width)
    (present : SharedRootRead.BlockAt program entry (EnumerationDriverCode.allocateWords words)) :
    ∃ final, Execution program state final (2 * words.length) (state.liveWords + words.length) ∧
      final.heap = state.heap ++ words.toArray ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry + 2 * words.length) ∧ final.halted = false ∧
      (∀ register : Fin 8, register ≠ 0 → final.reg register = state.reg register) := by
  induction words generalizing state entry with
  | nil =>
    refine ⟨state, ?_, ?_, rfl, rfl, ?_, running, fun _ _ => rfl⟩
    · simpa using Execution.refl (p := program) state
    · simp
    · simpa using position
  | cons value rest ih =>
    have layout : EnumerationDriverCode.allocateWords (value :: rest) =
        [.constant 0 value, .allocate 0] ++ EnumerationDriverCode.allocateWords rest := by
      simp [EnumerationDriverCode.allocateWords]
    have headAt := block_left program entry [.constant 0 value, .allocate 0]
      (EnumerationDriverCode.allocateWords rest) (by simpa only [layout] using present)
    obtain ⟨middle, head, heap, stack, output, pc, active, frame⟩ :=
      cell_execution program state entry value position running
        (by simp only [List.length_cons] at room; omega) (by simp only [List.length_cons] at heapFits; omega) headAt
    have tailAt : SharedRootRead.BlockAt program (entry + 2) (EnumerationDriverCode.allocateWords rest) := by
      simpa using block_right program entry [.constant 0 value, .allocate 0]
        (EnumerationDriverCode.allocateWords rest) (by simpa only [layout] using present)
    obtain ⟨final, tail, finalHeap, finalStack, finalOutput, finalPC, finalRunning, finalFrame⟩ :=
      ih middle (entry + 2) pc active (by simp only [List.length_cons] at room; omega)
        (by rw [heap]; simp only [Array.size_push, List.length_cons] at *; omega) tailAt
    have middleLive : middle.liveWords = state.liveWords + 1 := by
      simp only [State.liveWords, heap, stack, output, Array.size_push]; omega
    refine ⟨final, ?_, ?_, finalStack.trans stack, finalOutput.trans output, ?_, finalRunning, ?_⟩
    · have joined := head.append tail
      rw [middleLive] at joined
      have peakEq : max (state.liveWords + 1) (state.liveWords + 1 + rest.length) = state.liveWords + 1 + rest.length := by omega
      rw [peakEq] at joined
      have ticksEq : 2 + 2 * rest.length = 2 * (value :: rest).length := by simp only [List.length_cons]; omega
      have wordsEq : state.liveWords + 1 + rest.length = state.liveWords + (value :: rest).length := by simp only [List.length_cons]; omega
      rw [ticksEq, wordsEq] at joined
      exact joined
    · rw [finalHeap, heap]
      apply Array.toList_inj.mp
      simp
    · have offsetEq : entry + 2 + 2 * rest.length = entry + 2 * (value :: rest).length := by simp only [List.length_cons]; omega
      exact finalPC.trans (congrArg (word width) offsetEq)
    · intro register other; rw [finalFrame register other, frame register other]

end Controller.Cost.EnumerationDriverAllocate
