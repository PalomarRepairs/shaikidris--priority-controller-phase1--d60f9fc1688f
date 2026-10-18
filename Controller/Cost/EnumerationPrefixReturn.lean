module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.EnumerationUniformOracle
public import Controller.Cost.EnumerationCanonicalEmit

@[expose] public section

/-! Return from the shared oracle to the mutable prefix. Mask words move from
stack to the retained heap, then two saved control words restore depth and mode. -/
namespace Controller.Cost.EnumerationPrefixReturn
open Controller.Cost.GateProgram Controller.Cost.RawTransferLoops

def code (width count : Nat) : List (Instruction width 8) :=
  SharedWitnessPark.code width count ++ [.pop 3, .pop 5]

@[simp] theorem code_length : (code width count).length = 2 * count + 2 := by
  simp [code]

theorem execution (program : Program width 8) (state : State width 8)
    (entry : Nat) (masks : List (Word width)) (depth mode : Word width) (suffix : List (Word width))
    (position : state.pc = word width entry) (running : state.halted = false)
    (input : state.stack = masks ++ depth :: mode :: suffix)
    (room : entry + 2 * masks.length + 2 < 2 ^ width)
    (heapFits : state.heap.size + masks.length < 2 ^ width)
    (present : SharedRootRead.BlockAt program entry (code width masks.length)) :
    ∃ final, Execution program state final (2 * masks.length + 2) state.liveWords ∧
      final.heap = state.heap ++ masks.toArray ∧ final.stack = suffix ∧ final.output = state.output ∧
      final.pc = word width (entry + 2 * masks.length + 2) ∧ final.halted = false ∧
      final.reg 3 = depth ∧ final.reg 5 = mode ∧ final.reg 4 = state.reg 4 := by
  have parkAt : SharedRootRead.BlockAt program entry (SharedWitnessPark.code width masks.length) := by
    intro offset bound
    have whole := present offset (by simp only [code, List.length_append]; omega)
    simp only [code] at whole
    rw [List.getElem?_append_left bound] at whole
    exact whole
  have depthAt : program[entry + 2 * masks.length]? = some (.pop 3) := by
    simpa [code, SharedWitnessPark.code_length] using present (2 * masks.length) (by simp only [code_length]; omega)
  have modeAt : program[entry + 2 * masks.length + 1]? = some (.pop 5) := by
    simpa [code, SharedWitnessPark.code_length, Nat.add_assoc] using present (2 * masks.length + 1) (by simp only [code_length]; omega)
  obtain ⟨parked, first, heap, stack, output, pc, active, frame⟩ :=
    SharedWitnessPark.execution program state masks (depth :: mode :: suffix) entry position running
      (by omega) heapFits input parkAt
  obtain ⟨restoredDepth, second, depthPC, heldDepth, depthHeap, depthStack, depthOutput, depthRunning, depthFrame⟩ :=
    EnumerationSteps.pop_execution (program := program) parked (entry + 2 * masks.length) 3 depth (mode :: suffix)
      pc active (by omega) stack depthAt
  obtain ⟨final, third, finalPC, heldMode, finalHeap, finalStack, finalOutput, finalRunning, finalFrame⟩ :=
    EnumerationSteps.pop_execution (program := program) restoredDepth (entry + 2 * masks.length + 1) 5 mode suffix
      depthPC depthRunning (by omega) depthStack modeAt
  have parkLive : parked.liveWords = state.liveWords := by
    simp only [State.liveWords, heap, stack, output, input, Array.size_append, List.size_toArray,
      List.length_append, List.length_cons]; omega
  have depthLive : restoredDepth.liveWords ≤ state.liveWords := by
    simp only [State.liveWords, depthHeap, depthStack, depthOutput, heap, output, input,
      Array.size_append, List.size_toArray, List.length_append, List.length_cons]; omega
  refine ⟨final, ?_, finalHeap.trans (depthHeap.trans heap), finalStack,
    finalOutput.trans (depthOutput.trans output), ?_, finalRunning, (finalFrame 3 (by decide)).trans heldDepth,
    heldMode, ?_⟩
  · have joined := first.append (second.append third)
    have peak : max state.liveWords (max parked.liveWords restoredDepth.liveWords) = state.liveWords := by omega
    simpa only [peak, Nat.reduceAdd] using joined
  · simpa only [Nat.add_assoc, Nat.reduceAdd] using finalPC
  · rw [finalFrame 4 (by decide), depthFrame 4 (by decide), frame 4 (by decide)]

end Controller.Cost.EnumerationPrefixReturn
