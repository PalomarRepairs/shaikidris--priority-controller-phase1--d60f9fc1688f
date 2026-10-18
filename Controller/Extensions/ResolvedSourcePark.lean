module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Extensions.ResolvedSourceRead
public import Controller.Cost.SharedWitnessCopy

@[expose] public section

/-! The retained traversal heap is copied onto its caller stack before a
query packet replaces it. The zero-address word is handled separately from
the positive-base reverse-copy loop. -/
namespace Controller.Extensions.ResolvedSourcePark
open Controller.Cost Controller.Cost.RawTransferLoops Controller.Cost.SharedDetectorAssembly

def code (width entry count : Nat) : List (Instruction width 8) :=
  (SharedWitnessCopy.code width entry (entry+10) 1 (count-1)).toList ++
    (ResolvedSourceRead.readCode width 0 ++ [.push 1])

@[simp] theorem code_length : (code width entry count).length = 13 := by simp [code]

theorem execution (program : Program width 8) (state : State width 8) (entry : Nat)
    (positive : 0 < state.heap.size) (capacity : state.heap.size < 2 ^ width)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 13 < 2 ^ width)
    (present : SharedRootRead.BlockAt program entry (code width entry state.heap.size)) :
    ∃ final peak, Execution program state final (6*state.heap.size+2) peak ∧
      peak ≤ state.liveWords + state.heap.size ∧ final.heap = state.heap ∧
      final.stack = state.heap.toList ++ state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry+13) ∧ final.halted = false ∧ final.reg 4 = state.reg 4 := by
  obtain ⟨head, tail, words⟩ := List.exists_cons_of_ne_nil (show state.heap.toList ≠ [] by simpa using Nat.ne_of_gt positive)
  have size : state.heap.size = tail.length+1 := by
    have length := congrArg List.length words
    simpa using length
  unfold code at present
  have copyAt := block_left program entry _ _ present
  have afterCopy := block_right program entry _ _ present
  simp only [Array.length_toList, SharedWitnessCopy.code_size] at afterCopy
  have readAt := block_left program (entry+10) _ _ afterCopy
  have pushAt := block_right program (entry+10) _ _ afterCopy
  have cells : ∀ i (valid : i < tail.length), state.heap[1+i]? = some tail[i] := by
    intro i valid
    rw [← Array.getElem?_toList, words]
    simp [List.getElem?_eq_getElem valid, Nat.add_comm]
  obtain ⟨copied, cp, first, space, heap, stack, output, pc, active, frame⟩ :=
    SharedWitnessCopy.execution program state 1 tail entry (entry+10) position running (by omega) (by decide)
      (by omega) cells (by simpa only [size, Nat.add_sub_cancel] using block_code _ _ _ copyAt)
  have headCell : copied.heap[0]? = some head := by
    rw [heap, ← Array.getElem?_toList, words]
    rfl
  obtain ⟨loaded, second, held, lh, ls, lo, lp, lr, lf⟩ :=
    ResolvedSourceRead.read_execution program copied (entry+10) 0 head headCell pc active (by omega)
      (by simpa only [heap] using capacity) readAt
  obtain ⟨final, third, fp, fh, fs, fo, fr, ff, _⟩ :=
    EnumerationSteps.push_execution program loaded (entry+12) 1
      (by simpa only [Nat.add_assoc, Nat.reduceAdd] using lp) lr (by omega)
      (by simpa only [ResolvedSourceRead.readCode_length, Nat.add_assoc, Nat.reduceAdd, Nat.add_zero,
        List.getElem?_cons_zero] using pushAt 0 (by simp))
  have copiedLive : copied.liveWords = state.liveWords + tail.length := by
    simp only [State.liveWords, heap, stack, output, List.length_append]; omega
  have loadedLive : loaded.liveWords = copied.liveWords := by simp only [State.liveWords, lh, ls, lo]
  refine ⟨final, max cp (max copied.liveWords (loaded.liveWords+1)), ?_, by omega,
    fh.trans (lh.trans heap), ?_, fo.trans (lo.trans output), ?_, fr, ?_⟩
  · have ticks : (6*tail.length+5)+(2+1) = 6*state.heap.size+2 := by omega
    simpa only [ticks] using first.append (second.append third)
  · rw [fs, held, ls, stack, words]
    rfl
  · simpa only [Nat.add_assoc, Nat.reduceAdd] using fp
  · rw [ff, lf 4 (by decide) (by decide), frame]

end Controller.Extensions.ResolvedSourcePark
