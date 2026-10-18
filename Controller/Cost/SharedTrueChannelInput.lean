module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedWitnessDecode
public import Controller.Cost.SharedRootTagStack

public import Mathlib.Tactic.FinCases

@[expose] public section

namespace Controller.Cost.SharedTrueChannelInput
open Controller.Cost.GateProgram Controller.Cost.RawTransferLoops

def code (width entry address channel : Nat) : Program width 8 :=
  #[.constant 3 (word width address), .load 5 3] ++
    (SharedTagCompare.code width (entry + 7) channel 4 ++
      #[.constant 0 (word width 0), .branchZero 0 (word width (entry + 8)),
        .constant 5 (word width 1), .push 5])

@[simp] theorem code_size : (code width entry address channel).size = 9 := rfl

set_option maxHeartbeats 2000000 in
theorem execution (program : Program width 8) (state : State width 8)
    (entry address channel : Nat) (tag baseline : Word width)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 9 < 2 ^ width) (channelFits : channel < 2 ^ width)
    (addressFits : address < 2 ^ width) (valid : address < state.heap.size)
    (held : state.reg 4 = tag) (stored : state.heap[address]? = some baseline)
    (physical : CodeAt program entry (code width entry address channel)) :
    ∃ final ticks, Execution program state final ticks (state.liveWords + 1) ∧ ticks ≤ 8 ∧
      final.heap = state.heap ∧ final.output = state.output ∧
      final.stack = (if tag.val = channel then word width 1 else baseline) :: state.stack ∧
      final.reg 4 = tag ∧ final.pc = word width (entry + 9) ∧ final.halted = false := by
  obtain ⟨addressed, addressTrace, addressPC, addressHeld, addressHeap, addressStack, addressOutput, addressRunning, addressFrame⟩ :=
    SharedEvaluationReclaim.constant_execution program entry address 3 state position running (by omega)
      (by simpa [code] using physical ⟨0, by simp⟩)
  let loaded := addressed.advance.put 5 baseline
  have cell : state.heap[address]'valid = baseline := by
    simpa only [Array.getElem?_eq_getElem valid, Option.some.injEq] using stored
  have loadStep : programStep program addressed = some loaded := by
    rw [fetched program addressed (entry + 1) _ addressPC (by omega)
      (show program[entry + 1]? = some (.load 5 3) by simpa [code] using physical ⟨1, by simp⟩)]
    simp [step, addressRunning, addressHeld, addressHeap, valid, cell,
      show (word width address).val = address from Nat.mod_eq_of_lt addressFits, loaded]
  have loadedPC : loaded.pc = word width (entry + 2) := by
    simpa [loaded, State.put, Nat.add_assoc] using advance_position addressed addressPC (by omega)
  have addressLive : addressed.liveWords = state.liveWords := by simp only [State.liveWords, addressHeap, addressStack, addressOutput]
  have loadedLive : loaded.liveWords = state.liveWords := addressLive
  have initial : Execution program state loaded 2 state.liveWords := by
    simpa only [addressLive, loadedLive, Nat.max_self, Nat.reduceAdd] using
      addressTrace.append (Execution.cons loadStep (Execution.refl loaded))
  have compareAt : CodeAt program (entry + 2) (SharedTagCompare.code width (entry + 7) channel 4) := by
    intro phase
    have found := physical ⟨2 + phase.val, by
      simp only [code_size]
      have bound : phase.val < 3 := by simpa only [SharedTagCompare.code_size] using phase.isLt
      omega⟩
    fin_cases phase <;> simpa [code, SharedTagCompare.code, Nat.add_assoc] using found
  have loadedTag : loaded.reg 4 = tag := by
    simpa [loaded, State.advance, State.put] using (addressFrame 4 (by decide)).trans held
  obtain ⟨tested, compareTrace, testedHeap, testedStack, testedOutput, testedPC, testedRunning, testedFrame⟩ :=
    SharedTagCompare.execution program loaded (entry + 2) (entry + 7) channel tag.val 4 (by decide)
      loadedPC addressRunning (by omega) channelFits tag.isLt
      (by simpa only [word, Nat.mod_eq_of_lt tag.isLt] using loadedTag) compareAt
  have testedLive : tested.liveWords = state.liveWords := by
    simp only [State.liveWords, testedHeap, testedStack, testedOutput]
    exact loadedLive
  have testedBaseline : tested.reg 5 = baseline := by
    simpa [loaded, State.put] using testedFrame 5 (by decide)
  have prefixTrace : Execution program state tested 5 state.liveWords := by
    simpa only [loadedLive, Nat.max_self, Nat.reduceAdd] using initial.append compareTrace
  have prepared : ∃ prepared ticks, Execution program state prepared ticks state.liveWords ∧ ticks ≤ 7 ∧
      prepared.heap = state.heap ∧ prepared.stack = state.stack ∧ prepared.output = state.output ∧
      prepared.reg 5 = (if tag.val = channel then word width 1 else baseline) ∧ prepared.reg 4 = tag ∧
      prepared.pc = word width (entry + 8) ∧ prepared.halted = false := by
    by_cases same : tag.val = channel
    · obtain ⟨prepared, trace, pc, bit, heap, stack, output, active, frame⟩ :=
        SharedEvaluationReclaim.constant_execution program (entry + 7) 1 5 tested
          (by simpa only [same, ↓reduceIte] using testedPC) testedRunning (by omega)
          (by simpa [code, SharedTagCompare.code] using physical ⟨7, by simp⟩)
      refine ⟨prepared, 6, ?_, by decide, heap.trans (testedHeap.trans addressHeap),
        stack.trans (testedStack.trans addressStack), output.trans (testedOutput.trans addressOutput),
        by simpa only [same, ↓reduceIte] using bit,
        (frame 4 (by decide)).trans ((testedFrame 4 (by decide)).trans loadedTag), ?_, active⟩
      · simpa only [testedLive, Nat.max_self, Nat.reduceAdd] using prefixTrace.append trace
      · simpa [Nat.add_assoc] using pc
    · obtain ⟨zeroed, trace, pc, zero, heap, stack, output, active, frame⟩ :=
        SharedEvaluationReclaim.constant_execution program (entry + 5) 0 0 tested
          (by simpa only [ite_eq_right same, Nat.add_assoc, Nat.reduceAdd] using testedPC) testedRunning (by omega)
          (by simpa [code, SharedTagCompare.code] using physical ⟨5, by simp⟩)
      let prepared := { zeroed.advance with pc := word width (entry + 8) }
      have jumpStep : programStep program zeroed = some prepared := by
        rw [fetched program zeroed (entry + 6) _ (by simpa [Nat.add_assoc] using pc) (by omega)
          (show program[entry + 6]? = some (.branchZero 0 (word width (entry + 8))) by
            simpa [code, SharedTagCompare.code] using physical ⟨6, by simp⟩)]
        simp [step, active, zero, word, prepared]
      have zeroLive : zeroed.liveWords = state.liveWords := by
        simp only [State.liveWords, heap, stack, output]
        exact testedLive
      have last : Execution program zeroed prepared 1 zeroed.liveWords := by
        simpa only [show prepared.liveWords = zeroed.liveWords from rfl, Nat.zero_add, Nat.max_self] using
          Execution.cons jumpStep (Execution.refl prepared)
      refine ⟨prepared, 7, ?_, by decide, heap.trans (testedHeap.trans addressHeap),
        stack.trans (testedStack.trans addressStack), output.trans (testedOutput.trans addressOutput),
        ?_, (frame 4 (by decide)).trans ((testedFrame 4 (by decide)).trans loadedTag), rfl, active⟩
      · simpa only [testedLive, zeroLive, Nat.max_self, Nat.reduceAdd] using prefixTrace.append (trace.append last)
      · simpa only [prepared, State.advance, ite_eq_right same] using (frame 5 (by decide)).trans testedBaseline
  obtain ⟨prepared, ticks, savedTrace, time, heap, stack, output, bit, tagHeld, pc, active⟩ := prepared
  let final := { prepared.advance with stack := prepared.reg 5 :: prepared.stack }
  have pushStep : programStep program prepared = some final := by
    rw [fetched program prepared (entry + 8) _ pc (by omega)
      (show program[entry + 8]? = some (.push 5) by simpa [code, SharedTagCompare.code] using physical ⟨8, by simp⟩)]
    simp [step, active, final]
  have preparedLive : prepared.liveWords = state.liveWords := by simp only [State.liveWords, heap, stack, output]
  have finalLive : final.liveWords = state.liveWords + 1 := by simp [final, State.advance, State.liveWords, heap, stack, output]; omega
  refine ⟨final, ticks + 1, ?_, by omega, heap, output, ?_, tagHeld, ?_, active⟩
  · have last := Execution.cons pushStep (Execution.refl final)
    have joined := savedTrace.append last
    simpa only [Nat.zero_add, preparedLive, finalLive, Nat.max_eq_right (by omega : state.liveWords ≤ state.liveWords + 1)] using joined
  · simp [final, bit, stack]
  · simpa [final, Nat.add_assoc] using advance_position prepared pc (by omega)


theorem decoded_bit (T : Finset (Fin n)) (tag : Word width) (channel : Fin n) :
    word width (if Controller.assignmentOfSet (SharedWitnessDecode.decode T tag) channel then 1 else 0) =
      if tag.val = channel.val then word width 1 else
        word width (if Controller.assignmentOfSet T channel then 1 else 0) := by
  by_cases bound : tag.val < n
  · have same : (⟨tag.val, bound⟩ : Fin n) = channel ↔ tag.val = channel.val := Fin.ext_iff
    simp only [SharedWitnessDecode.decode, dite_eq_left bound, Controller.assignmentOfSet,
      Finset.mem_insert]
    by_cases matched : tag.val = channel.val
    · have equal := same.mpr matched
      simp [equal, matched]
    · have different := mt same.mp matched
      have reverse : channel ≠ (⟨tag.val, bound⟩ : Fin n) := Ne.symm different
      simp [matched, reverse]
  · have different : tag.val ≠ channel.val := by have := channel.isLt; omega
    simp [SharedWitnessDecode.decode, bound, different]

end Controller.Cost.SharedTrueChannelInput
