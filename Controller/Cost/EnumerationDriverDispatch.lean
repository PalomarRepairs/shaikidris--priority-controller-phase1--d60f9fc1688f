module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.EnumerationDriverRepair

@[expose] public section

/-! Actual fixed dispatch of the saved initial/completion/sibling mode. -/
namespace Controller.Cost.EnumerationDriverDispatch
open Controller.Decoder Controller.Native Controller.Cost.GateProgram Controller.Cost.RawTransferLoops
open Controller.Cost.SharedDetectorAssembly

def code (width initial completion : Nat) : List (Instruction width 8) :=
  (SharedTagCompare.code width initial 0 5).toList ++ (SharedTagCompare.code width completion 1 5).toList

@[simp] theorem code_length : (code width initial completion).length = 6 := rfl

theorem execution (program : Program width 8) (state : State width 8)
    (entry initial completion mode : Nat) (position : state.pc = word width entry) (running : state.halted = false)
    (held : state.reg 5 = word width mode) (modeFits : mode < 2 ^ width)
    (room : entry + 6 < 2 ^ width) (present : SharedRootRead.BlockAt program entry (code width initial completion)) :
    ∃ final ticks, Execution program state final ticks state.liveWords ∧ ticks ≤ 6 ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (if mode = 0 then initial else if mode = 1 then completion else entry + 6) ∧
      final.halted = false ∧ (∀ register : Fin 8, register ≠ 0 → final.reg register = state.reg register) := by
  have firstAt := block_left program entry (SharedTagCompare.code width initial 0 5).toList
    (SharedTagCompare.code width completion 1 5).toList present
  obtain ⟨tested, first, heap, stack, output, pc, active, frame⟩ :=
    SharedTagCompare.execution program state entry initial 0 mode 5 (by decide) position running (by omega) (by have := Nat.two_pow_pos width; omega)
      modeFits held (by intro phase; simpa only [Array.getElem?_toList] using firstAt phase.val (by simpa using phase.isLt))
  by_cases zero : mode = 0
  · refine ⟨tested, 3, first, by omega, heap, stack, output, ?_, active, frame⟩
    simpa only [ite_eq_left zero] using pc
  · have secondAt : SharedRootRead.BlockAt program (entry + 3) (SharedTagCompare.code width completion 1 5).toList := by
      simpa only [Array.length_toList, SharedTagCompare.code_size] using block_right program entry
        (SharedTagCompare.code width initial 0 5).toList (SharedTagCompare.code width completion 1 5).toList present
    obtain ⟨final, second, finalHeap, finalStack, finalOutput, finalPC, finalRunning, finalFrame⟩ :=
      SharedTagCompare.execution program tested (entry + 3) completion 1 mode 5 (by decide)
        (by simpa only [ite_eq_right zero] using pc) active (by omega) (by omega) modeFits
        ((frame 5 (by decide)).trans held)
        (by intro phase; simpa only [Array.getElem?_toList] using secondAt phase.val (by simpa using phase.isLt))
    have testedLive : tested.liveWords = state.liveWords := by simp only [State.liveWords, heap, stack, output]
    refine ⟨final, 6, ?_, by omega, finalHeap.trans heap, finalStack.trans stack, finalOutput.trans output, ?_, finalRunning, ?_⟩
    · simpa only [testedLive, Nat.max_self, Nat.reduceAdd] using first.append second
    · simpa only [ite_eq_right zero, Nat.add_assoc, Nat.reduceAdd] using finalPC
    · intro register notZero; rw [finalFrame register notZero, frame register notZero]

theorem physical (parameters : Parameters) (graph : DAG parameters.channels) (width entry : Nat)
    (rows : List ForestIndexedOperands.Row) (roots : List Nat) (program : Program width 8)
    (present : SharedRootRead.BlockAt program entry (EnumerationDriverCode.code parameters graph width entry rows roots)) :
    SharedRootRead.BlockAt program (EnumerationDriverCode.labels parameters graph width entry).dispatch
      (code width (EnumerationDriverCode.labels parameters graph width entry).initialPost (EnumerationDriverCode.labels parameters graph width entry).completePost) := by
  have found := EnumerationDriverLayout.physical parameters graph width entry rows roots program present 3 (by decide)
  simpa only [EnumerationDriverLayout.entries, EnumerationDriverCode.chunks, List.getElem_cons_succ, List.getElem_cons_zero, code] using found

end Controller.Cost.EnumerationDriverDispatch
