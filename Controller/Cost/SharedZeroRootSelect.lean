module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedZeroCode
public import Controller.Cost.SharedChannelStore

@[expose] public section

/-! A queried root ID is fetched from the retained source directory and written to the shared query slot. -/
namespace Controller.Cost.SharedZeroRootSelect
open Controller.Cost.GateProgram Controller.Cost.RawTransferLoops

def code (width slot : Nat) : Program width 8 :=
  #[.load 1 3, .constant 0 (word width slot), .store 0 1]

@[simp] theorem code_size (width slot : Nat) : (code width slot).size = 3 := rfl

set_option maxHeartbeats 2000000 in
theorem execution (resident : Program width 8) (state : State width 8)
    (entry source slot : Nat) (root : Word width)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 3 < 2 ^ width) (sourceFits : source < 2 ^ width) (slotFits : slot < 2 ^ width)
    (sourceValid : source < state.heap.size) (slotValid : slot < state.heap.size)
    (sourceHeld : state.reg 3 = word width source) (stored : state.heap[source]? = some root)
    (physical : CodeAt resident entry (code width slot)) :
    ∃ final, Execution resident state final 3 state.liveWords ∧
      final.heap = state.heap.set slot root ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry + 3) ∧ final.halted = false ∧
      final.reg 1 = root ∧ final.reg 3 = state.reg 3 ∧
      (∀ index : Fin 8, index ≠ 0 → index ≠ 1 → final.reg index = state.reg index) := by
  let loaded := state.advance.put 1 root
  have cell : state.heap[source]'sourceValid = root := by
    simpa only [Array.getElem?_eq_getElem sourceValid, Option.some.injEq] using stored
  have loadStep : programStep resident state = some loaded := by
    rw [fetched resident state entry _ position (by omega)
      (show resident[entry]? = some (.load 1 3) by simpa [code] using physical ⟨0, by simp [code]⟩)]
    simp [step, running, sourceHeld, show (word width source).val = source from Nat.mod_eq_of_lt sourceFits,
      sourceValid, cell, loaded]
  have loadedPC : loaded.pc = word width (entry + 1) := by
    simpa [loaded, State.put] using advance_position state position (by omega)
  obtain ⟨ready, setupTrace, readyPC, readyAddress, readyHeap, readyStack, readyOutput, readyRunning, readyFrame⟩ :=
    SharedEvaluationReclaim.constant_execution resident (entry + 1) slot 0 loaded loadedPC running (by omega)
      (by simpa [code] using physical ⟨1, by simp [code]⟩)
  have storeCode : CodeAt resident (entry + 2) (SharedChannelStore.code width) := by
    intro offset
    have zero : offset.val = 0 := by have bound := offset.isLt; simp at bound; omega
    simpa [SharedChannelStore.code, zero, code] using physical ⟨2, by simp [code]⟩
  obtain ⟨final, storeTrace, finalHeap, finalStack, finalOutput, finalPC, finalRunning, finalFrame⟩ :=
    SharedChannelStore.execution resident ready (entry + 2) slot root
      (by simpa [Nat.add_assoc] using readyPC) readyRunning (by omega) slotFits
      (by simpa only [readyHeap, loaded, State.put, State.advance] using slotValid) readyAddress
      (by simpa [loaded, State.put] using readyFrame 1 (by decide)) storeCode
  have loadedLive : loaded.liveWords = state.liveWords := rfl
  have readyLive : ready.liveWords = state.liveWords := by
    simp only [State.liveWords, readyHeap, readyStack, readyOutput]; exact loadedLive
  have loadTrace : Execution resident state loaded 1 state.liveWords := by
    simpa only [loadedLive, Nat.zero_add, Nat.max_self] using Execution.cons loadStep (Execution.refl loaded)
  have joined := loadTrace.append (setupTrace.append storeTrace)
  rw [loadedLive, readyLive, Nat.max_self] at joined
  refine ⟨final, by simpa using joined, ?_, finalStack.trans readyStack, finalOutput.trans readyOutput,
    by simpa [Nat.add_assoc] using finalPC, finalRunning, ?_, ?_, ?_⟩
  · simpa only [readyHeap, loaded, State.put, State.advance] using finalHeap
  · simpa [loaded, State.put] using (congrFun finalFrame 1).trans (readyFrame 1 (by decide))
  · simpa [loaded, State.put, State.advance] using (congrFun finalFrame 3).trans (readyFrame 3 (by decide))

  · intro index notZero notOne
    simpa [loaded, State.put, State.advance, notZero, notOne] using
      (congrFun finalFrame index).trans (readyFrame index notZero)

open Controller.Cost.ForestZeroEmit

theorem root_stored (heap : Array (Word width)) (channels nodes slot sourceEnd : Nat)
    (root : Fin nodes) (sourceBound : sourceEnd ≤ heap.size) (slotBound : slot < sourceEnd)
    (positive : 0 < slot) (header : heap[0]? = some (word width channels)) :
    StoredReference (heap.set slot (word width root.val) (by omega)) channels sourceEnd
      (SharedZeroCode.rootReference channels nodes slot root) := by
  constructor
  · simpa using sourceBound
  · exact slotBound
  · omega
  · simp [SharedZeroCode.rootReference, Array.getElem?_set]
  · simpa [Array.getElem?_set, show slot ≠ (0 : Nat) from by omega] using header
  · simp [SharedZeroCode.rootReference, Nat.add_comm]

theorem reference_preserved (heap : Array (Word width)) (channels slot sourceEnd : Nat)
    (value : Word width) (reference : Reference ambient)
    (stored : StoredReference heap channels sourceEnd reference)
    (valid : slot < heap.size) (positive : 0 < slot) (separate : reference.slot ≠ slot) :
    StoredReference (heap.set slot value valid) channels sourceEnd reference := by
  constructor
  · simpa using stored.sourceBound
  · exact stored.slotBound
  · exact stored.headerBound
  · simpa [Array.getElem?_set, Ne.symm separate] using stored.slotWord
  · simpa [Array.getElem?_set, show slot ≠ (0 : Nat) from by omega] using stored.channelWord
  · exact stored.coordinateEq

end Controller.Cost.SharedZeroRootSelect
