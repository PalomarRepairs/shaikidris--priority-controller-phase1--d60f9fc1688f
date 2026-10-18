module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedRootTagStack
public import Controller.Cost.SharedRootQueryEntry

@[expose] public section

namespace Controller.Cost.SharedRootResumeEntry
open Controller.Cost.GateProgram Controller.Cost.RawTransferLoops
open Controller.Cost.ForestZeroAdmissibleCaller Controller.Cost.ForestZeroBackendFrame

def code (width tableBase inverseBase : Nat) : Program width 8 :=
  SharedRootTagStack.resumeCode width ++
    #[.constant 0 (word width 0), .constant 1 (word width tableBase), .constant 2 (word width inverseBase)]

@[simp] theorem code_size : (code width tableBase inverseBase).size = 5 := rfl

set_option maxHeartbeats 2000000 in
theorem execution (program : Program width 8) (state : State width 8)
    (sourceHeap : Array (Word width)) (tableBase inverseBase entry : Nat) (cursor count : Word width)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 5 < 2 ^ width) (cursorHeld : state.reg 5 = cursor) (countHeld : state.reg 6 = count)
    (heapSize : state.heap.size = sourceHeap.size) (sourceFrame : PrefixFrame tableBase sourceHeap state.heap)
    (zeroTable : ∀ coordinate : Fin ambient, state.heap[tableBase + coordinate.val]? = some (word width 0))
    (physical : CodeAt program entry (code width tableBase inverseBase)) :
    ∃ final, Execution program state final 5 (state.liveWords + 2) ∧
      final.heap = state.heap ∧ final.output = state.output ∧
      QueryReady (ambient := ambient) sourceHeap tableBase inverseBase (entry + 5)
        (cursor :: count :: state.stack) final ∧
      (∀ register : Fin 8, register ≠ 0 → register ≠ 1 → register ≠ 2 →
        final.reg register = state.reg register) := by
  have resumeAt : CodeAt program entry (SharedRootTagStack.resumeCode width) := by
    have all := physical
    unfold code at all
    exact RawSharedOrdered.takePrefix program entry _ _ all
  obtain ⟨resumed, resumeTrace, resumeHeap, resumeOutput, resumeRegisters, resumeStack, resumePC, resumeRunning⟩ :=
    SharedRootTagStack.resume_execution program state entry cursor count position running (by omega) cursorHeld countHeld resumeAt
  obtain ⟨zeroed, zeroTrace, zeroPC, zeroValue, zeroHeap, zeroStack, zeroOutput, zeroRunning, zeroFrame⟩ :=
    SharedEvaluationReclaim.constant_execution program (entry + 2) 0 0 resumed resumePC resumeRunning (by omega)
      (by simpa [code, SharedRootTagStack.resumeCode] using physical ⟨2, by simp⟩)
  obtain ⟨tabled, tableTrace, tablePC, tableValue, tableHeap, tableStack, tableOutput, tableRunning, tableFrame⟩ :=
    SharedEvaluationReclaim.constant_execution program (entry + 3) tableBase 1 zeroed
      (by simpa [Nat.add_assoc] using zeroPC) zeroRunning (by omega)
      (by simpa [code, SharedRootTagStack.resumeCode] using physical ⟨3, by simp⟩)
  obtain ⟨final, inverseTrace, finalPC, inverseValue, finalHeap, finalStack, finalOutput, finalRunning, inverseFrame⟩ :=
    SharedEvaluationReclaim.constant_execution program (entry + 4) inverseBase 2 tabled
      (by simpa [Nat.add_assoc] using tablePC) tableRunning (by omega)
      (by simpa [code, SharedRootTagStack.resumeCode] using physical ⟨4, by simp⟩)
  have heap : final.heap = state.heap := finalHeap.trans (tableHeap.trans (zeroHeap.trans resumeHeap))
  have output : final.output = state.output := finalOutput.trans (tableOutput.trans (zeroOutput.trans resumeOutput))
  have stack : final.stack = cursor :: count :: state.stack := finalStack.trans (tableStack.trans (zeroStack.trans resumeStack))
  have resumedLive : resumed.liveWords = state.liveWords + 2 := by
    simp only [State.liveWords, resumeHeap, resumeOutput, resumeStack, List.length_cons]
    omega
  have zeroLive : zeroed.liveWords = resumed.liveWords := by simp only [State.liveWords, zeroHeap, zeroStack, zeroOutput]
  have tableLive : tabled.liveWords = resumed.liveWords := by simp only [State.liveWords, tableHeap, tableStack, tableOutput]; exact zeroLive
  refine ⟨final, ?_, heap, output, ?_, ?_⟩
  · have joined := resumeTrace.append (zeroTrace.append (tableTrace.append inverseTrace))
    simpa only [resumedLive, zeroLive, tableLive, Nat.max_self, Nat.reduceAdd] using joined
  · exact {
      heapSize := heap ▸ heapSize
      sourceFrame := heap ▸ sourceFrame
      zeroTable := heap ▸ zeroTable
      stack := stack
      position := by simpa [Nat.add_assoc] using finalPC
      running := finalRunning
      zeroRegister := (inverseFrame 0 (by decide)).trans ((tableFrame 0 (by decide)).trans zeroValue)
      tableRegister := (inverseFrame 1 (by decide)).trans tableValue
      inverseRegister := inverseValue
    }
  · intro register nonzero notOne notTwo
    exact (inverseFrame register notTwo).trans ((tableFrame register notOne).trans
      ((zeroFrame register nonzero).trans (congrFun resumeRegisters register)))


def skipCode (width tableBase inverseBase done : Nat) : Program width 8 :=
  code width tableBase inverseBase ++ #[.branchZero 0 (word width done)]

@[simp] theorem skipCode_size : (skipCode width tableBase inverseBase done).size = 6 := by
  simp [skipCode]

set_option maxHeartbeats 2000000 in
theorem skip_execution (program : Program width 8) (state : State width 8)
    (sourceHeap : Array (Word width)) (tableBase inverseBase entry done : Nat) (cursor count : Word width)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 6 < 2 ^ width) (cursorHeld : state.reg 5 = cursor) (countHeld : state.reg 6 = count)
    (heapSize : state.heap.size = sourceHeap.size) (sourceFrame : PrefixFrame tableBase sourceHeap state.heap)
    (zeroTable : ∀ coordinate : Fin ambient, state.heap[tableBase + coordinate.val]? = some (word width 0))
    (physical : CodeAt program entry (skipCode width tableBase inverseBase done)) :
    ∃ final, Execution program state final 6 (state.liveWords + 2) ∧
      final.heap = state.heap ∧ final.output = state.output ∧
      QueryReady (ambient := ambient) sourceHeap tableBase inverseBase done
        (cursor :: count :: state.stack) final ∧
      (∀ register : Fin 8, register ≠ 0 → register ≠ 1 → register ≠ 2 →
        final.reg register = state.reg register) := by
  have resumeAt : CodeAt program entry (code width tableBase inverseBase) := by
    have all := physical
    unfold skipCode at all
    exact RawSharedOrdered.takePrefix program entry _ _ all
  obtain ⟨prepared, trace, heap, output, ready, frame⟩ := execution program state sourceHeap tableBase inverseBase entry
    cursor count position running (by omega) cursorHeld countHeld heapSize sourceFrame zeroTable resumeAt
  let final := { prepared.advance with pc := word width done }
  have transition : programStep program prepared = some final := by
    rw [fetched program prepared (entry + 5) _ ready.position (by omega)
      (show program[entry + 5]? = some (.branchZero 0 (word width done)) by
        simpa [skipCode, code, SharedRootTagStack.resumeCode] using physical ⟨5, by simp⟩)]
    simp [step, ready.running, ready.zeroRegister, word, final]
  have preparedLive : prepared.liveWords = state.liveWords + 2 := by
    simp only [State.liveWords, heap, output, ready.stack, List.length_cons]
    omega
  have jump : Execution program prepared final 1 prepared.liveWords := by
    simpa only [show final.liveWords = prepared.liveWords from rfl, Nat.zero_add, Nat.max_self] using
      Execution.cons transition (Execution.refl final)
  refine ⟨final, ?_, heap, output, ?_, frame⟩
  · simpa only [preparedLive, Nat.max_self, Nat.reduceAdd] using trace.append jump
  · exact {
      heapSize := ready.heapSize
      sourceFrame := ready.sourceFrame
      zeroTable := ready.zeroTable
      stack := ready.stack
      position := rfl
      running := ready.running
      zeroRegister := ready.zeroRegister
      tableRegister := ready.tableRegister
      inverseRegister := ready.inverseRegister
    }

end Controller.Cost.SharedRootResumeEntry
