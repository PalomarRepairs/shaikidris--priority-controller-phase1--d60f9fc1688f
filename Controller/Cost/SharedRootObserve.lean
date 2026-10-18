module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedRootRead

@[expose] public section

/-! Root identifiers, evaluated values and candidate witnesses are joined in one run. -/
namespace Controller.Cost.SharedRootObserve
open Controller.Cost.RawTransferLoops

def code (width entry : Nat) : Program width 8 :=
  (SharedRootRead.code width).toArray ++ SharedRootWitness.code width (entry + 3)

@[simp] theorem code_size (width entry : Nat) : (code width entry).size = 7 := by simp [code]

theorem execution (resident : Program width 8) (state : State width 8)
    (cursor valueBase index entry : Nat) (observed : Bool)
    (old candidate : Word width) (suffix : List (Word width))
    (cursorHeld : state.reg 3 = word width cursor)
    (baseHeld : state.reg 1 = word width valueBase)
    (cursorBound : cursor < state.heap.size) (cursorFits : cursor < 2 ^ width)
    (source : state.heap[cursor]'cursorBound = word width index)
    (valueBound : valueBase + index < state.heap.size)
    (valueFits : valueBase + index < 2 ^ width)
    (stored : state.heap[valueBase + index]'valueBound = boolWord width observed)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 7 < 2 ^ width) (boolFits : 1 < 2 ^ width)
    (heapFits : state.heap.size < 2 ^ width)
    (input : state.stack = old :: suffix) (candidateReg : state.reg 4 = candidate)
    (physical : CodeAt resident entry (code width entry)) :
    ∃ final ticks, Execution resident state final ticks state.liveWords ∧ ticks ≤ 7 ∧
      final.heap = state.heap.push (if observed then candidate else old) ∧
      final.stack = suffix ∧ final.output = state.output ∧
      final.pc = word width (entry + 7) ∧ final.halted = false ∧
      (∀ register : Fin 8, register ≠ 0 → register ≠ 1 → register ≠ 2 →
        final.reg register = state.reg register) := by
  have all := physical
  unfold code at all
  have first := RawSharedOrdered.takePrefix resident entry _ _ all
  have second := RawSharedOrdered.takeSuffix resident entry _ _ all
  have readBlock : SharedRootRead.BlockAt resident entry (SharedRootRead.code width) := by
    intro offset bound
    simpa using first ⟨offset, by simpa using bound⟩
  obtain ⟨ready, readTrace, address, root, r2, r3, heap, stack, output, pc, active, frame⟩ :=
    SharedRootRead.execution resident state cursor valueBase index entry observed
      cursorHeld baseHeld cursorBound cursorFits source valueBound valueFits stored
      position running (by omega) readBlock
  have readyLive : ready.liveWords = state.liveWords := by
    simp only [State.liveWords, heap, stack, output]
  obtain ⟨final, ticks, updateTrace, time, finalHeap, finalStack, finalOutput,
    finalPC, finalActive, finalFrame⟩ :=
    SharedRootWitness.execution resident ready (entry + 3) observed old candidate suffix
      pc active (by omega) boolFits (by simpa only [heap] using heapFits)
      (stack.trans input) root ((frame 4 (by decide) (by decide)).trans candidateReg)
      (by simpa only [List.size_toArray, SharedRootRead.code_length] using second)
  have joined := readTrace.append updateTrace
  rw [readyLive, Nat.max_self] at joined
  refine ⟨final, 3 + ticks, joined, by omega, finalHeap.trans (by rw [heap]),
    finalStack, finalOutput.trans output, ?_, finalActive, ?_⟩
  · simpa only [Nat.add_assoc, Nat.reduceAdd] using finalPC
  · intro register different0 different1 different2
    exact (finalFrame register different2).trans (frame register different0 different1)

end Controller.Cost.SharedRootObserve
