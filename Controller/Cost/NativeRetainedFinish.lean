module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.NativeRetainedEmit
public import Controller.Cost.RetainedSuffixReclaim

@[expose] public section

/-! The native assignment is emitted before its appended heap suffix is reclaimed. -/
namespace Controller.Cost.NativeRetainedFinish
open Controller.Cost.RawTransferLoops Controller.Cost.GateProgram Controller.Cost.NativeCircuitExecution

theorem execution (resident : Program width 8) (state : State width 8)
    (retained appended : Array (Word width)) (base entry done : Nat) (values : Fin count → Bool)
    (stored : TableStored state.heap base values) (heap : state.heap = retained ++ appended)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 3 * count + 7 < 2 ^ width) (heapFits : state.heap.size < 2 ^ width)
    (emitAt : ForestZeroCallerWiden.WidenedBlockAt resident entry
      (OutputProgram.emitCode width (NativeRealizedCore.addresses base count)))
    (releaseAt : CodeAt resident (entry + 3 * count)
      (SharedEvaluationReclaim.code width (entry + 3 * count) done appended.size)) :
    ∃ final, Execution resident state final (3 * count + 4 * appended.size + 4) (state.liveWords + count) ∧
      final.heap = retained ∧ final.stack = state.stack ∧
      final.output = (NativeRootLoad.words width values).reverse ++ state.output ∧
      final.pc = word width done ∧ final.halted = false := by
  obtain ⟨emitted, emitTrace, emittedHeap, emittedStack, emittedOutput, emittedPC, emittedRunning, high⟩ :=
    NativeRetainedEmit.execution resident state base entry values stored position running (by omega) heapFits emitAt
  have suffixFit : appended.size < 2 ^ width := by
    have size := congrArg Array.size heap
    simp only [Array.size_append] at size
    omega
  obtain ⟨final, reclaimTrace, finalHeap, finalStack, finalOutput, finalPC, finalRunning, zero, zero6, mask7, frame⟩ :=
    RetainedSuffixReclaim.execution resident emitted (entry + 3 * count) done retained appended.toList
      emittedPC emittedRunning (by omega) (by simpa only [Array.toArray_toList] using emittedHeap.trans heap)
      (by simpa using suffixFit) (by simpa using releaseAt)
  have live : emitted.liveWords = state.liveWords + count := by
    simp only [State.liveWords, emittedHeap, emittedStack, emittedOutput, List.length_append,
      List.length_reverse, NativeRootLoad.words_length]
    omega
  have joined := emitTrace.append reclaimTrace
  rw [live, Nat.max_self] at joined
  refine ⟨final, ?_, finalHeap, finalStack.trans emittedStack, finalOutput.trans emittedOutput, finalPC, finalRunning⟩
  simpa only [Array.length_toList, Nat.add_assoc] using joined

end Controller.Cost.NativeRetainedFinish
