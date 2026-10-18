module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedRootInspect

@[expose] public section

/-! Candidate tags move to a temporary heap buffer while healthy reference tags remain on the stack. -/
namespace Controller.Cost.SharedDetectorPrepare
open Controller.Cost.GateProgram Controller.Cost.RawTransferLoops

def code (width base count : Nat) : Program width 8 :=
  (SharedWitnessPark.code width count).toArray ++ #[.constant 3 (word width base)]

@[simp] theorem code_size (width base count : Nat) : (code width base count).size = 2 * count + 1 := by
  simp [code]

set_option maxHeartbeats 2000000 in
theorem execution (resident : Program width 8) (state : State width 8)
    (candidates references : List (Word width)) (entry : Nat)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 2 * candidates.length + 1 < 2 ^ width)
    (capacity : state.heap.size + candidates.length < 2 ^ width)
    (input : state.stack = candidates ++ references)
    (physical : CodeAt resident entry (code width state.heap.size candidates.length)) :
    ∃ final, Execution resident state final (2 * candidates.length + 1) state.liveWords ∧
      final.heap = state.heap ++ candidates.toArray ∧ final.stack = references ∧ final.output = state.output ∧
      final.pc = word width (entry + 2 * candidates.length + 1) ∧ final.halted = false ∧
      final.reg 3 = word width state.heap.size ∧
      (∀ index : Nat, ∀ valid : index < candidates.length,
        final.heap[state.heap.size + index]? = some candidates[index]) := by
  have all := physical
  unfold code at all
  have parkCode := RawSharedOrdered.takePrefix resident entry _ _ all
  have tailCode := RawSharedOrdered.takeSuffix resident entry _ _ all
  have parkBlock : SharedRootRead.BlockAt resident entry (SharedWitnessPark.code width candidates.length) := by
    intro offset valid
    simpa using parkCode ⟨offset, by simpa using valid⟩
  obtain ⟨parked, parkTrace, parkedHeap, parkedStack, parkedOutput, parkedPC, parkedRunning, parkedFrame⟩ :=
    SharedWitnessPark.execution resident state candidates references entry position running (by omega) capacity input parkBlock
  obtain ⟨final, setupTrace, finalPC, finalCursor, finalHeap, finalStack, finalOutput, finalRunning, finalFrame⟩ :=
    SharedEvaluationReclaim.constant_execution resident (entry + 2 * candidates.length) state.heap.size 3
      parked parkedPC parkedRunning (by omega)
      (by simpa using tailCode ⟨0, by simp⟩)
  have parkedLive : parked.liveWords = state.liveWords := by
    simp only [State.liveWords, parkedHeap, parkedStack, parkedOutput, Array.size_append,
      List.size_toArray, input, List.length_append]
    omega
  have joined := parkTrace.append setupTrace
  rw [parkedLive, Nat.max_self] at joined
  refine ⟨final, joined, finalHeap.trans parkedHeap, finalStack.trans parkedStack,
    finalOutput.trans parkedOutput, finalPC, finalRunning, finalCursor, ?_⟩
  intro index valid
  rw [finalHeap, parkedHeap]
  simp [Array.getElem?_append, valid]

end Controller.Cost.SharedDetectorPrepare
