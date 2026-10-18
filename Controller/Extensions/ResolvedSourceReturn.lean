module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedWitnessPark
public import Controller.Cost.SharedCandidateRoute
public import Controller.Cost.SharedDetectorAssembly
public import Controller.Cost.EnumerationSteps

@[expose] public section

/-! A quiet query releases its entire packet and dictionary, reloads the
parked traversal heap, and branches on the retained verdict. Both outcomes
recover the exact original caller stack and output. -/
namespace Controller.Extensions.ResolvedSourceReturn
open Controller.Cost Controller.Cost.RawTransferLoops Controller.Cost.SharedDetectorAssembly

def routeCode (width entry found rejected : Nat) : List (Instruction width 8) :=
  (SharedCandidateRoute.code width entry found 4).toList ++
    [.constant 0 (word width 0), .branchZero 0 (word width rejected)]

@[simp] theorem routeCode_length : (routeCode width entry found rejected).length = 5 := by simp [routeCode]

theorem route_execution (program : Program width 8) (state : State width 8)
    (entry found rejected : Nat) (answer : Bool) (held : state.reg 4 = boolWord width answer)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry+5 < 2 ^ width)
    (present : SharedRootRead.BlockAt program entry (routeCode width entry found rejected)) :
    ∃ final, Execution program state final 3 state.liveWords ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (if answer then found else rejected) ∧ final.halted = false := by
  have firstAt := block_left program entry _ _ present
  have lastAt := block_right program entry _ _ present
  simp only [Array.length_toList, SharedCandidateRoute.code_size] at lastAt
  obtain ⟨tested, first, heap, stack, output, pc, active, _⟩ :=
    SharedCandidateRoute.execution program state entry found 4 answer position running (by omega) (by omega)
      held (block_code _ _ _ firstAt)
  cases answer with
  | true => exact ⟨tested, first, heap, stack, output, pc, active⟩
  | false =>
    obtain ⟨final, last, fp, fh, fs, fo, fr, _⟩ :=
      EnumerationSteps.jump_execution program tested (entry+3) rejected pc active (by omega)
        (by simpa using lastAt 0 (by simp)) (by simpa using lastAt 1 (by simp))
    have live : tested.liveWords = state.liveWords := by simp only [State.liveWords, heap, stack, output]
    exact ⟨final, by simpa only [live, Nat.max_self, Bool.false_eq_true, ite_false, Nat.reduceAdd] using first.append last,
      fh.trans heap, fs.trans stack, fo.trans output, fp, fr⟩

def code (width entry oldCount retainedCount found rejected : Nat) : List (Instruction width 8) :=
  (SharedEvaluationReclaim.code width entry (entry+7) oldCount).toList ++
    (SharedWitnessPark.code width retainedCount ++ routeCode width (entry+7+2*retainedCount) found rejected)

@[simp] theorem code_length : (code width entry oldCount retainedCount found rejected).length = 12+2*retainedCount := by
  simp [code]; omega

theorem execution (program : Program width 8) (state : State width 8)
    (entry found rejected : Nat) (original : Array (Word width)) (rest : List (Word width)) (answer : Bool)
    (saved : state.stack = original.toList ++ rest) (held : state.reg 4 = boolWord width answer)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry+12+2*original.size < 2 ^ width)
    (oldFits : state.heap.size < 2 ^ width) (originalFits : original.size < 2 ^ width)
    (present : SharedRootRead.BlockAt program entry
      (code width entry state.heap.size original.size found rejected)) :
    ∃ final, Execution program state final (4*state.heap.size+2*original.size+7) state.liveWords ∧
      final.heap = original ∧ final.stack = rest ∧ final.output = state.output ∧
      final.pc = word width (if answer then found else rejected) ∧ final.halted = false := by
  unfold code at present
  have releaseAt := block_left program entry _ _ present
  have afterRelease := block_right program entry _ _ present
  simp only [Array.length_toList, SharedEvaluationReclaim.code_size] at afterRelease
  have loadAt := block_left program (entry+7) _ _ afterRelease
  have routeAt := block_right program (entry+7) _ _ afterRelease
  simp only [SharedWitnessPark.code_length] at routeAt
  obtain ⟨empty, first, eh, es, eo, ep, er, _, _, _, ef⟩ :=
    SharedGraphReclaim.setup_execution program state entry (entry+7) #[] state.heap.toList position running
      (by omega) (by simp) (by simpa using oldFits) (by simpa using block_code _ _ _ releaseAt)
  obtain ⟨loaded, second, lh, ls, lo, lp, lr, lf⟩ :=
    SharedWitnessPark.execution program empty original.toList rest (entry+7) ep er (by simpa using (show entry+7+2*original.size<2^width by omega))
      (by simpa [eh] using originalFits) (es.trans saved) (by simpa using loadAt)
  obtain ⟨final, third, fh, fs, fo, fp, fr⟩ :=
    route_execution program loaded (entry+7+2*original.size) found rejected answer
      ((lf 4 (by decide)).trans ((ef 4 (by decide) (by decide) (by decide)).trans held))
      (by simpa using lp) lr (by omega) routeAt
  have emptyLive : empty.liveWords ≤ state.liveWords := Execution.final_storage_le first
  have loadedLive : loaded.liveWords = empty.liveWords := by
    simp only [State.liveWords, lh, ls, lo, es, saved, eh, Array.size_append, Array.size_empty,
      List.size_toArray, Array.length_toList, List.length_append]; omega
  have joined := first.append (second.append third)
  refine ⟨final, ?_, ?_, fs.trans ls, fo.trans (lo.trans eo), fp, fr⟩
  · have ticks : (4*state.heap.toList.length+4)+(2*original.toList.length+3) =
        4*state.heap.size+2*original.size+7 := by simp only [Array.length_toList]; omega
    simpa only [loadedLive, Nat.max_self, Nat.max_eq_left emptyLive, ticks] using joined
  · simpa only [lh, eh, Array.empty_append, Array.toArray_toList] using fh

end Controller.Extensions.ResolvedSourceReturn
