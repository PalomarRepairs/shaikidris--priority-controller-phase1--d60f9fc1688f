module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedRootResumeEntry

@[expose] public section

namespace Controller.Cost.SharedRootPointerShift
open Controller.Cost.GateProgram Controller.Cost.RawTransferLoops
open Controller.Cost.ForestZeroAdmissibleCaller

def code (width offset : Nat) : Program width 8 :=
  #[.constant 6 (word width offset), .add 3 3 6]

@[simp] theorem code_size : (code width offset).size = 2 := rfl

set_option maxHeartbeats 2000000 in
theorem execution (program : Program width 8) (state : State width 8)
    (sourceHeap : Array (Word width)) (tableBase inverseBase entry source offset : Nat)
    (rest : List (Word width))
    (ready : QueryReady (ambient := ambient) sourceHeap tableBase inverseBase entry rest state)
    (room : entry + 2 < 2 ^ width) (sourceFits : source < 2 ^ width) (offsetFits : offset < 2 ^ width)
    (held : state.reg 3 = word width source) (physical : CodeAt program entry (code width offset)) :
    ∃ final, Execution program state final 2 state.liveWords ∧
      final.heap = state.heap ∧ final.output = state.output ∧
      final.reg 3 = word width (source + offset) ∧
      QueryReady (ambient := ambient) sourceHeap tableBase inverseBase (entry + 2) rest final := by
  obtain ⟨loaded, firstTrace, loadedPC, offsetHeld, heap, stack, output, active, frame⟩ :=
    SharedEvaluationReclaim.constant_execution program entry offset 6 state ready.position ready.running (by omega)
      (by simpa [code] using physical ⟨0, by simp⟩)
  let final := loaded.advance.put 3 (word width (source + offset))
  have transition : programStep program loaded = some final := by
    rw [fetched program loaded (entry + 1) _ loadedPC (by omega)
      (show program[entry + 1]? = some (.add 3 3 6) by simpa [code] using physical ⟨1, by simp⟩)]
    simp [step, active, (frame 3 (by decide)).trans held, offsetHeld,
      show (word width source).val = source from Nat.mod_eq_of_lt sourceFits,
      show (word width offset).val = offset from Nat.mod_eq_of_lt offsetFits, final]
  have loadedLive : loaded.liveWords = state.liveWords := by simp only [State.liveWords, heap, stack, output]
  have second : Execution program loaded final 1 loaded.liveWords := by
    simpa only [show final.liveWords = loaded.liveWords from rfl, Nat.zero_add, Nat.max_self] using
      Execution.cons transition (Execution.refl final)
  refine ⟨final, ?_, heap, output, ?_, ?_⟩
  · simpa only [loadedLive, Nat.max_self, Nat.reduceAdd] using firstTrace.append second
  · simp [final, State.put]
  · exact {
      heapSize := heap ▸ ready.heapSize
      sourceFrame := heap ▸ ready.sourceFrame
      zeroTable := heap ▸ ready.zeroTable
      stack := stack.trans ready.stack
      position := by simpa [final, State.put, Nat.add_assoc] using advance_position loaded loadedPC (by omega)
      running := active
      zeroRegister := (frame 0 (by decide)).trans ready.zeroRegister
      tableRegister := (frame 1 (by decide)).trans ready.tableRegister
      inverseRegister := (frame 2 (by decide)).trans ready.inverseRegister
    }

end Controller.Cost.SharedRootPointerShift
