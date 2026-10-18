module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedHealthyBaseline
public import Controller.Cost.SharedCandidateRoute

@[expose] public section

/-! Fetched channel reads determine whether the baseline contains any channel. -/
namespace Controller.Cost.SharedBaselineNonempty
open Controller.Cost.GateProgram Controller.Cost.RawTransferLoops
open Controller.Cost.ForestInputStored

def code (width base entry done : Nat) : List (Fin n) → Program width 8
  | [] => #[.constant 1 (boolWord width false), .constant 0 (word width 0), .branchZero 0 (word width done)]
  | channel :: rest => #[.constant 0 (word width (base + channel.val)), .load 1 0] ++
      (SharedCandidateRoute.code width (entry + 2) done 1 ++ code width base (entry + 5) done rest)

@[simp] theorem code_size (channels : List (Fin n)) :
    (code width base entry done channels).size = 5 * channels.length + 3 := by
  induction channels generalizing entry with
  | nil => rfl
  | cons channel rest ih => simp [code, ih]; omega

set_option maxHeartbeats 2000000 in
theorem execution (resident : Program width 8) (state : State width 8)
    (retained : Array (Word width)) (values : Fin n → Bool) (channels : List (Fin n)) (entry done : Nat)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 5 * channels.length + 3 < 2 ^ width)
    (capacity : retained.size + n < 2 ^ width) (boolFits : 1 < 2 ^ width)
    (heapStored : state.heap = withValues retained values)
    (physical : CodeAt resident entry (code width retained.size entry done channels)) :
    ∃ final ticks, Execution resident state final ticks state.liveWords ∧
      ticks ≤ 5 * channels.length + 3 ∧
      final.reg 1 = boolWord width (channels.any values) ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width done ∧ final.halted = false ∧ final.reg 4 = state.reg 4 := by
  induction channels generalizing state entry with
  | nil =>
    obtain ⟨first, firstTrace, firstPC, firstValue, firstHeap, firstStack, firstOutput, firstRunning, firstFrame⟩ :=
      SharedEvaluationReclaim.constant_execution resident entry 0 1 state position running (by omega)
        (by simpa [code, boolWord] using physical ⟨0, by simp [code]⟩)
    obtain ⟨second, secondTrace, secondPC, secondValue, secondHeap, secondStack, secondOutput, secondRunning, secondFrame⟩ :=
      SharedEvaluationReclaim.constant_execution resident (entry + 1) 0 0 first firstPC firstRunning (by omega)
        (by simpa [code] using physical ⟨1, by simp [code]⟩)
    let final := { second.advance with pc := word width done }
    have transition : programStep resident second = some final := by
      rw [fetched resident second (entry + 2) _ (by simpa [Nat.add_assoc] using secondPC) (by omega)
        (show resident[entry + 2]? = some (.branchZero 0 (word width done)) by simpa [code] using physical ⟨2, by simp [code]⟩)]
      simp [step, secondRunning, secondValue, word, final]
    have firstLive : first.liveWords = state.liveWords := by simp only [State.liveWords, firstHeap, firstStack, firstOutput]
    have secondLive : second.liveWords = state.liveWords := by simp only [State.liveWords, secondHeap, secondStack, secondOutput]; exact firstLive
    have lastTrace : Execution resident second final 1 second.liveWords := by
      simpa only [show final.liveWords = second.liveWords from rfl, Nat.zero_add, Nat.max_self] using Execution.cons transition (Execution.refl final)
    have joined := firstTrace.append (secondTrace.append lastTrace)
    rw [firstLive, secondLive, Nat.max_self] at joined
    refine ⟨final, 3, by simpa using joined, by simp, ?_, secondHeap.trans firstHeap,
      secondStack.trans firstStack, secondOutput.trans firstOutput, rfl, secondRunning, ?_⟩
    · exact (secondFrame 1 (by decide)).trans firstValue
    · exact (secondFrame 4 (by decide)).trans (firstFrame 4 (by decide))
  | cons channel rest ih =>
    have all := physical
    simp only [code] at all
    have readCode := RawSharedOrdered.takePrefix resident entry _ _ all
    have tailCode := RawSharedOrdered.takeSuffix resident entry _ _ all
    have routeCode := RawSharedOrdered.takePrefix resident (entry + 2) _ _ (by simpa using tailCode)
    have restCode := RawSharedOrdered.takeSuffix resident (entry + 2) _ _ (by simpa using tailCode)
    obtain ⟨addressed, addressTrace, addressPC, addressValue, addressHeap, addressStack, addressOutput, addressRunning, addressFrame⟩ :=
      SharedEvaluationReclaim.constant_execution resident entry (retained.size + channel.val) 0 state position running
        (by simp only [List.length_cons] at room; omega) (by simpa using readCode ⟨0, by simp⟩)
    let loaded := addressed.advance.put 1 (boolWord width (values channel))
    have loadedHeap : addressed.heap = withValues retained values := addressHeap.trans heapStored
    have valid : retained.size + channel.val < addressed.heap.size := by rw [loadedHeap, withValues_size]; omega
    have cell : addressed.heap[retained.size + channel.val]'valid = boolWord width (values channel) := by
      simpa only [loadedHeap] using value_cell retained values channel
    have loadStep : programStep resident addressed = some loaded := by
      rw [fetched resident addressed (entry + 1) _ addressPC (by simp only [List.length_cons] at room; omega)
        (show resident[entry + 1]? = some (.load 1 0) by simpa using readCode ⟨1, by simp⟩)]
      have addressNat : (addressed.reg 0).val = retained.size + channel.val := by
        rw [addressValue]; exact Nat.mod_eq_of_lt (by omega)
      simp [step, addressRunning, addressNat, valid, cell, loaded]
    have loadedPC : loaded.pc = word width (entry + 2) := by
      simpa [loaded, State.put, Nat.add_assoc] using advance_position addressed addressPC
        (by simp only [List.length_cons] at room; omega)
    obtain ⟨routed, routeTrace, routeHeap, routeStack, routeOutput, routePC, routeRunning, routeFrame⟩ :=
      SharedCandidateRoute.execution resident loaded (entry + 2) done 1 (values channel) loadedPC addressRunning
        (by simp only [List.length_cons] at room; omega) boolFits (by simp [loaded, State.put]) routeCode
    have loadedLive : loaded.liveWords = state.liveWords := by simp only [loaded, State.advance, State.put, State.liveWords, addressHeap, addressStack, addressOutput]
    have addressedLive : addressed.liveWords = state.liveWords := loadedLive
    have readTrace : Execution resident state loaded 2 state.liveWords := by
      have trace := addressTrace.append (Execution.cons loadStep (Execution.refl loaded))
      simpa only [loadedLive, addressedLive, Nat.zero_add, Nat.reduceAdd, Nat.max_self] using trace
    have routedLive : routed.liveWords = state.liveWords := by
      simp only [State.liveWords, routeHeap, routeStack, routeOutput]; exact loadedLive
    have routedHeap : routed.heap = state.heap := routeHeap.trans addressHeap
    have routedStack : routed.stack = state.stack := routeStack.trans addressStack
    have routedOutput : routed.output = state.output := routeOutput.trans addressOutput
    have routedHead : routed.reg 4 = state.reg 4 :=
      (routeFrame 4 (by decide)).trans (addressFrame 4 (by decide))
    cases value : values channel with
    | true =>
      have joined := readTrace.append routeTrace
      rw [loadedLive, Nat.max_self] at joined
      refine ⟨routed, 5, by simpa [value] using joined, by simp only [List.length_cons]; omega, ?_, routedHeap, routedStack,
        routedOutput, by simpa [value] using routePC, routeRunning, routedHead⟩
      simpa [List.any_cons, value, loaded, State.put] using routeFrame 1 (by decide)
    | false =>
      obtain ⟨final, ticks, restTrace, restTime, finalValue, finalHeap, finalStack, finalOutput,
        finalPC, finalRunning, finalHead⟩ :=
        ih routed (entry + 5) (by simpa [value, Nat.add_assoc] using routePC) routeRunning
          (by simp only [List.length_cons] at room; omega) (routedHeap.trans heapStored)
          (by simpa [Nat.add_assoc] using restCode)
      have joined := readTrace.append (routeTrace.append restTrace)
      rw [loadedLive, routedLive, Nat.max_self] at joined
      refine ⟨final, 3 + ticks, by simpa only [value, Bool.false_eq_true, ite_false, ← Nat.add_assoc, Nat.reduceAdd, Nat.max_self] using joined,
        by simp only [List.length_cons]; omega, ?_, finalHeap.trans routedHeap, finalStack.trans routedStack,
        finalOutput.trans routedOutput, finalPC, finalRunning, finalHead.trans routedHead⟩
      simpa [List.any_cons, value] using finalValue

theorem any_set (T : Finset (Fin n)) :
    (List.finRange n).any (assignmentOfSet T) = decide T.Nonempty := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, List.mem_finRange, true_and, assignmentOfSet, decide_eq_true_eq]
  rfl

end Controller.Cost.SharedBaselineNonempty
