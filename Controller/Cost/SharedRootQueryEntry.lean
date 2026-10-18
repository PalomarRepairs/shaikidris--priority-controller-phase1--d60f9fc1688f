module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedZeroResidentConditions

public import Mathlib.Tactic.FinCases

@[expose] public section

namespace Controller.Cost.SharedRootQueryEntry
open Controller.Cost.GateProgram Controller.Cost.RawTransferLoops
open Controller.Cost.ForestZeroAdmissibleCaller Controller.Cost.ForestZeroBackendFrame

def code (width slot tableBase : Nat) : Program width 8 :=
  SharedZeroRootSelect.code width slot ++ #[.constant 0 (word width 0), .constant 1 (word width tableBase)]

@[simp] theorem code_size : (code width slot tableBase).size = 5 := rfl

theorem frame_set (frame : PrefixFrame count before after)
    (beforeValid : slot < before.size) (afterValid : slot < after.size) :
    PrefixFrame count (before.set slot value beforeValid) (after.set slot value afterValid) := by
  refine ⟨by simpa using frame.1, by simpa using frame.2.1, ?_⟩
  intro index below
  by_cases same : index = slot
  · subst index
    simp [Array.getElem?_set]
  · rw [Array.getElem?_set_ne afterValid (Ne.symm same),
      Array.getElem?_set_ne beforeValid (Ne.symm same)]
    exact frame.2.2 index below

set_option maxHeartbeats 2000000 in
theorem execution (program : Program width 8) (state : State width 8)
    (sourceHeap : Array (Word width)) (tableBase inverseBase entry source slot : Nat)
    (root : Word width) (rest : List (Word width))
    (ready : QueryReady (ambient := ambient) sourceHeap tableBase inverseBase entry rest state)
    (room : entry + 5 < 2 ^ width) (sourceFits : source < 2 ^ width) (slotFits : slot < 2 ^ width)
    (sourceValid : source < state.heap.size) (slotBefore : slot < tableBase)
    (sourceHeld : state.reg 3 = word width source) (stored : state.heap[source]? = some root)
    (physical : CodeAt program entry (code width slot tableBase)) :
    ∃ final, Execution program state final 5 state.liveWords ∧
      final.heap = state.heap.set slot root (by have := ready.sourceFrame.2.1; omega) ∧
      final.output = state.output ∧
      QueryReady (ambient := ambient)
        (sourceHeap.set slot root (by have := ready.sourceFrame.1; omega))
        tableBase inverseBase (entry + 5) rest final := by
  have slotValid : slot < state.heap.size := by have := ready.sourceFrame.2.1; omega
  have beforeValid : slot < sourceHeap.size := by have := ready.sourceFrame.1; omega
  have selectAt : CodeAt program entry (SharedZeroRootSelect.code width slot) := by
    intro phase
    have found := physical ⟨phase.val, by have := phase.isLt; simp at *; omega⟩
    fin_cases phase <;> simpa [code, SharedZeroRootSelect.code] using found
  obtain ⟨selected, selectTrace, selectedHeap, selectedStack, selectedOutput, selectedPC,
      selectedRunning, selectedRoot, selectedPointer, selectedFrame⟩ :=
    SharedZeroRootSelect.execution program state entry source slot root ready.position ready.running
      (by omega) sourceFits slotFits sourceValid slotValid sourceHeld stored selectAt
  obtain ⟨zeroed, zeroTrace, zeroPC, zeroRegister, zeroHeap, zeroStack, zeroOutput, zeroRunning, zeroFrame⟩ :=
    SharedEvaluationReclaim.constant_execution program (entry + 3) 0 0 selected selectedPC selectedRunning
      (by omega) (by simpa [code, SharedZeroRootSelect.code] using physical ⟨3, by simp⟩)
  obtain ⟨final, tableTrace, finalPC, tableRegister, finalHeap, finalStack, finalOutput, finalRunning, finalFrame⟩ :=
    SharedEvaluationReclaim.constant_execution program (entry + 4) tableBase 1 zeroed
      (by simpa [Nat.add_assoc] using zeroPC) zeroRunning (by omega)
      (by simpa [code, SharedZeroRootSelect.code] using physical ⟨4, by simp⟩)
  have selectedLive : selected.liveWords = state.liveWords := by
    simp only [State.liveWords, selectedHeap, selectedStack, selectedOutput, Array.size_set]
  have zeroLive : zeroed.liveWords = state.liveWords := by
    simp only [State.liveWords, zeroHeap, zeroStack, zeroOutput]
    exact selectedLive
  have heap : final.heap = state.heap.set slot root slotValid := finalHeap.trans (zeroHeap.trans selectedHeap)
  refine ⟨final, ?_, heap, finalOutput.trans (zeroOutput.trans selectedOutput), ?_⟩
  · have joined := (selectTrace.append zeroTrace).append tableTrace
    simpa only [selectedLive, zeroLive, Nat.max_self, Nat.reduceAdd] using joined
  · constructor
    · simp only [heap, Array.size_set]
      exact ready.heapSize
    · rw [heap]
      exact frame_set ready.sourceFrame beforeValid slotValid
    · intro coordinate
      rw [heap, Array.getElem?_set_ne slotValid (by omega)]
      exact ready.zeroTable coordinate
    · exact finalStack.trans (zeroStack.trans (selectedStack.trans ready.stack))
    · simpa only [Nat.add_assoc, Nat.reduceAdd] using finalPC
    · exact finalRunning
    · exact (finalFrame 0 (by decide)).trans zeroRegister
    · exact tableRegister
    · exact (finalFrame 2 (by decide)).trans
        ((zeroFrame 2 (by decide)).trans ((selectedFrame 2 (by decide) (by decide)).trans ready.inverseRegister))

end Controller.Cost.SharedRootQueryEntry
