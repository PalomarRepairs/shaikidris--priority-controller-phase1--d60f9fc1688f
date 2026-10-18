module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedBaselineInitialize

@[expose] public section

/-! A heap segment is copied to the stack while every heap cell remains available. -/
namespace Controller.Cost.SharedWitnessCopy
open Controller.Cost.GateProgram Controller.Cost.RawTransferLoops

def code (width entry done base count : Nat) : Program width 8 :=
  #[.constant 0 (word width count), .constant 1 (word width (base + count - 1)),
    .constant 6 (word width 0), .constant 7 (word width (2 ^ width - 1))] ++
    reverseSaveCode width (entry + 4) done

@[simp] theorem code_size (width entry done base count : Nat) :
    (code width entry done base count).size = 10 := by simp [code]

set_option maxHeartbeats 2000000 in
theorem execution (resident : Program width 8) (state : State width 8)
    (base : Nat) (witnesses : List (Word width)) (entry done : Nat)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 10 < 2 ^ width) (positive : 0 < base)
    (heapFits : base + witnesses.length < 2 ^ width)
    (cells : ∀ index : Nat, ∀ valid : index < witnesses.length,
      state.heap[base + index]? = some witnesses[index])
    (physical : CodeAt resident entry (code width entry done base witnesses.length)) :
    ∃ final peak, Execution resident state final (6 * witnesses.length + 5) peak ∧
      peak ≤ state.liveWords + witnesses.length ∧
      final.heap = state.heap ∧ final.stack = witnesses ++ state.stack ∧ final.output = state.output ∧
      final.pc = word width done ∧ final.halted = false ∧ final.reg 4 = state.reg 4 := by
  have all := physical
  unfold code at all
  have setup := RawSharedOrdered.takePrefix resident entry _ _ all
  have tail := RawSharedOrdered.takeSuffix resident entry _ _ all
  obtain ⟨s1, t1, p1, v1, h1, k1, o1, a1, f1⟩ :=
    SharedEvaluationReclaim.constant_execution resident entry witnesses.length 0 state position running (by omega)
      (by simpa using setup ⟨0, by simp⟩)
  obtain ⟨s2, t2, p2, v2, h2, k2, o2, a2, f2⟩ :=
    SharedEvaluationReclaim.constant_execution resident (entry + 1) (base + witnesses.length - 1)
      1 s1 p1 a1 (by omega) (by simpa using setup ⟨1, by simp⟩)
  obtain ⟨s3, t3, p3, v3, h3, k3, o3, a3, f3⟩ :=
    SharedEvaluationReclaim.constant_execution resident (entry + 2) 0 6 s2
      (by simpa only [Nat.add_assoc, Nat.reduceAdd] using p2) a2 (by omega)
      (by simpa using setup ⟨2, by simp⟩)
  obtain ⟨ready, t4, p4, v4, h4, k4, o4, a4, f4⟩ :=
    SharedEvaluationReclaim.constant_execution resident (entry + 3) (2 ^ width - 1) 7 s3
      (by simpa only [Nat.add_assoc, Nat.reduceAdd] using p3) a3 (by omega)
      (by simpa using setup ⟨3, by simp⟩)
  have readyHeap : ready.heap = state.heap := h4.trans (h3.trans (h2.trans h1))
  obtain ⟨final, copyPeak, trace, copySpace, heap, stack, output, pc, active, zero, frame⟩ :=
    reverse_save_execution resident (entry + 4) done base witnesses ready
      (by simpa only [Nat.add_assoc, Nat.reduceAdd] using p4) a4 (by omega) positive heapFits (by omega)
      (by rw [f4 0 (by decide), f3 0 (by decide), f2 0 (by decide)]; exact v1)
      (by rw [f4 1 (by decide), f3 1 (by decide)]; exact v2) v4
      (by rw [f4 6 (by decide)]; exact v3)
      (by simpa only [readyHeap] using cells) (by simpa using tail)
  have live1 : s1.liveWords = state.liveWords := by simp only [State.liveWords, h1, k1, o1]
  have live2 : s2.liveWords = state.liveWords := by simp only [State.liveWords, h2, k2, o2, h1, k1, o1]
  have live3 : s3.liveWords = state.liveWords := by simp only [State.liveWords, h3, k3, o3, h2, k2, o2, h1, k1, o1]
  have readyLive : ready.liveWords = state.liveWords := by
    simp only [State.liveWords, h4, k4, o4, h3, k3, o3, h2, k2, o2, h1, k1, o1]
  have joined := t1.append (t2.append (t3.append (t4.append trace)))
  have timeEq : 1 + (1 + (1 + (1 + (6 * witnesses.length + 1)))) = 6 * witnesses.length + 5 := by omega
  rw [timeEq] at joined
  refine ⟨final, max state.liveWords (max s1.liveWords (max s2.liveWords (max s3.liveWords copyPeak))),
    joined, ?_, heap.trans readyHeap, ?_, output.trans (o4.trans (o3.trans (o2.trans o1))), pc, active, ?_⟩
  · rw [live1, live2, live3]
    rw [readyLive] at copySpace
    omega
  · simpa only [k4, k3, k2, k1] using stack
  · exact (frame 4 (by decide) (by decide) (by decide)).trans
      ((f4 4 (by decide)).trans ((f3 4 (by decide)).trans
        ((f2 4 (by decide)).trans (f1 4 (by decide)))))

end Controller.Cost.SharedWitnessCopy
