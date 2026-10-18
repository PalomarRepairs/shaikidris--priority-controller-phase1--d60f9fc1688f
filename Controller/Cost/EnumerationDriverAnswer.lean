module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.EnumerationDriverControlAt

@[expose] public section

/-! Actual answer-dependent continuation after a prefix query. Success advances
the saved parent counter; failureLabel reaches the fixed repair/seek block. -/
namespace Controller.Cost.EnumerationDriverAnswer
open Controller.Decoder Controller.Native Controller.Cost.GateProgram Controller.Cost.RawTransferLoops
open Controller.Cost.SharedDetectorAssembly Controller.Cost.EnumerationDriverPrefix

def code (width failureLabel descend : Nat) : List (Instruction width 8) :=
  [.branchZero 4 (word width failureLabel)] ++ EnumerationDriverControl.incrementCode width descend

@[simp] theorem code_length (width failureLabel descend : Nat) : (code width failureLabel descend).length = 5 := rfl

theorem execution (parameters : Parameters) (program : Program width 8) (state : State width 8)
    (entry failureLabel descend cursor : Nat) (packet : Array (Word width)) (partialSet : Finset (Fin parameters.channels))
    (answer : Bool) (ready : Ready parameters packet (cursor + 1) cursor partialSet state)
    (position : state.pc = word width entry) (flag : state.reg 4 = boolWord width answer)
    (fits : cursor + 1 < 2 ^ width) (room : entry + 5 < 2 ^ width)
    (present : SharedRootRead.BlockAt program entry (code width failureLabel descend)) :
    ∃ final ticks, Execution program state final ticks state.liveWords ∧ ticks ≤ 5 ∧
      Ready parameters packet (cursor + 1) (if answer then cursor + 1 else cursor) partialSet final ∧
      final.pc = word width (if answer then descend else failureLabel) ∧ final.output = state.output := by
  have branchAt : program[entry]? = some (.branchZero 4 (word width failureLabel)) := by
    simpa only [code, List.singleton_append, List.getElem?_cons_zero, Nat.add_zero] using present 0 (by simp [code])
  cases answer with
  | false =>
    obtain ⟨final, trace, pc, heap, stack, output, running, frame⟩ :=
      EnumerationSteps.branch_taken (program := program) state entry failureLabel 4 position ready.running (by omega)
        (by rw [flag]; simp [boolWord, word]) branchAt
    exact ⟨final, 1, trace, by omega, ⟨heap.trans ready.heap, (frame 3).trans ready.counter, stack.trans ready.stack, running⟩, pc, output⟩
  | true =>
    have oneFits : 1 < 2 ^ width := by omega
    obtain ⟨branched, first, pc, heap, stack, output, running, frame⟩ :=
      EnumerationSteps.branch_skipped (program := program) state entry failureLabel 4 position ready.running (by omega)
        (by rw [flag]; simp [boolWord, word, Nat.mod_eq_of_lt oneFits]) branchAt
    have incAt : SharedRootRead.BlockAt program (entry + 1) (EnumerationDriverControl.incrementCode width descend) := by
      simpa using block_right program entry [.branchZero 4 (word width failureLabel)] (EnumerationDriverControl.incrementCode width descend) present
    obtain ⟨final, second, cursorValue, finalHeap, finalStack, finalOutput, finalPC, finalRunning, finalFrame⟩ :=
      EnumerationDriverControl.increment_execution program branched (entry + 1) cursor descend pc running
        ((frame 3).trans ready.counter) fits (by omega) incAt
    have branchLive : branched.liveWords = state.liveWords := by simp only [State.liveWords, heap, stack, output]
    refine ⟨final, 5, ?_, by omega, ⟨finalHeap.trans (heap.trans ready.heap), cursorValue,
      finalStack.trans (stack.trans ready.stack), finalRunning⟩, finalPC, finalOutput.trans output⟩
    simpa only [branchLive, Nat.max_self, Nat.reduceAdd] using first.append second

theorem completion_at (parameters : Parameters) (graph : DAG parameters.channels) (width entry : Nat)
    (rows : List ForestIndexedOperands.Row) (roots : List Nat) (program : Program width 8)
    (present : SharedRootRead.BlockAt program entry (EnumerationDriverCode.code parameters graph width entry rows roots)) :
    SharedRootRead.BlockAt program (EnumerationDriverCode.labels parameters graph width entry).completePost
      (code width (EnumerationDriverCode.labels parameters graph width entry).completeRepair (EnumerationDriverCode.labels parameters graph width entry).descend) := by
  have found := EnumerationDriverLayout.physical parameters graph width entry rows roots program present 7 (by decide)
  simpa [EnumerationDriverLayout.entries, EnumerationDriverCode.chunks, code,
    EnumerationDriverControl.incrementCode, List.append_assoc] using found

theorem sibling_at (parameters : Parameters) (graph : DAG parameters.channels) (width entry : Nat)
    (rows : List ForestIndexedOperands.Row) (roots : List Nat) (program : Program width 8)
    (present : SharedRootRead.BlockAt program entry (EnumerationDriverCode.code parameters graph width entry rows roots)) :
    SharedRootRead.BlockAt program (EnumerationDriverCode.labels parameters graph width entry).seekPost
      (code width (EnumerationDriverCode.labels parameters graph width entry).seekFail (EnumerationDriverCode.labels parameters graph width entry).descend) := by
  have found := EnumerationDriverLayout.physical parameters graph width entry rows roots program present 4 (by decide)
  simpa [EnumerationDriverLayout.entries, EnumerationDriverCode.chunks, code,
    EnumerationDriverControl.incrementCode, List.append_assoc] using found

end Controller.Cost.EnumerationDriverAnswer
