module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedWitnessRestore

@[expose] public section

/-! Witness restoration and temporary node reclamation form one fetched caller run. -/
namespace Controller.Cost.SharedProbeCleanup
open Controller.Cost.RawTransferLoops

def code (width entry done retained nodes witnesses : Nat) : Program width 8 :=
  SharedWitnessRestore.preparedCode width entry (entry + 17) (retained + nodes) witnesses ++
    SharedEvaluationReclaim.code width (entry + 17) done nodes

@[simp] theorem code_size (width entry done retained nodes witnesses : Nat) :
    (code width entry done retained nodes witnesses).size = 24 := by simp [code]

theorem execution (resident : Program width 8) (state : State width 8)
    (retained : Array (Word width)) (nodes witnesses : List (Word width)) (entry done : Nat)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 24 < 2 ^ width) (positive : 0 < retained.size)
    (heapFits : retained.size + nodes.length + witnesses.length < 2 ^ width)
    (heapStored : state.heap = (retained ++ nodes.toArray) ++ witnesses.toArray)
    (physical : CodeAt resident entry
      (code width entry done retained.size nodes.length witnesses.length)) :
    ∃ final, Execution resident state final (10 * witnesses.length + 4 * nodes.length + 13)
      (state.liveWords + witnesses.length) ∧
      final.heap = retained ∧ final.stack = witnesses ++ state.stack ∧ final.output = state.output ∧
      final.pc = word width done ∧ final.halted = false ∧ final.reg 4 = state.reg 4 := by
  have all := physical
  unfold code at all
  have restoreCode := RawSharedOrdered.takePrefix resident entry _ _ all
  have releaseCode := RawSharedOrdered.takeSuffix resident entry _ _ all
  obtain ⟨ready, restoreTrace, restoredHeap, restoredStack, restoredOutput,
    restoredPC, restoredRunning, restoredFrame, restoredBitFrame⟩ :=
    SharedWitnessRestore.prepared_execution resident state (retained ++ nodes.toArray) witnesses entry (entry + 17)
      position running (by omega) (by simp; omega) (by simpa using heapFits) heapStored
      (by simpa using restoreCode)
  obtain ⟨final, releaseTrace, heap, stack, output, pc, active, zero, six, seven, frame⟩ :=
    SharedGraphReclaim.setup_execution resident ready (entry + 17) done retained nodes
      restoredPC restoredRunning (by omega) restoredHeap (by omega)
      (by simpa using releaseCode)
  have readyLive : ready.liveWords = state.liveWords := by
    simp only [State.liveWords, restoredHeap, restoredStack, restoredOutput,
      heapStored, Array.size_append, List.size_toArray, List.length_append]
    omega
  have joined := restoreTrace.append releaseTrace
  rw [readyLive, Nat.max_eq_left (by omega : state.liveWords ≤ state.liveWords + witnesses.length)] at joined
  have timeEq : (10 * witnesses.length + 9) + (4 * nodes.length + 4) =
      10 * witnesses.length + 4 * nodes.length + 13 := by omega
  rw [timeEq] at joined
  refine ⟨final, joined, heap, stack.trans restoredStack, output.trans restoredOutput, pc, active, ?_⟩
  exact (frame 4 (by decide) (by decide) (by decide)).trans restoredFrame

end Controller.Cost.SharedProbeCleanup
