module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.UniformDAGHeadRead

@[expose] public section

/-! Runtime input-gate evaluation reads the cached channel identifier, reads
its stored Boolean value, and appends that value to the growing node table. -/
namespace Controller.Cost.UniformDAGInputGate
open Controller.Cost.GateProgram

def code (width headBase : ℕ) : Code width :=
  UniformDAGHeadRead.code width headBase ++ [.allocate 2]
@[simp] theorem code_length : (code width headBase).length = 6 := rfl
@[simp] theorem code_words : 4 * (code width headBase).length = 24 := rfl

/-- Six fetched instructions include the actual result allocation. -/
theorem execution (program : Program width 4) (s : State width 4)
    (base headBase valueBase offset identifier : ℕ) (value : Bool)
    (offsetHeld : s.reg 3 = word width offset) (valueHeld : s.reg 1 = word width valueBase)
    (headFits : headBase + offset < 2 ^ width)
    (valueFits : valueBase + identifier < 2 ^ width)
    (headBound : headBase + offset < s.heap.size)
    (valueBound : valueBase + identifier < s.heap.size)
    (source : s.heap[headBase + offset]'headBound = word width identifier)
    (stored : s.heap[valueBase + identifier]'valueBound = boolWord width value)
    (pc : s.pc = word width base) (running : s.halted = false)
    (programFits : base + 6 < 2 ^ width) (heapRoom : s.heap.size < 2 ^ width)
    (block : BlockAt program base (code width headBase)) :
    ∃ final, Execution program s final 6 (s.liveWords + 1) ∧
      final.reg 2 = boolWord width value ∧ final.reg 3 = s.reg 3 ∧
      final.heap = s.heap.push (boolWord width value) ∧
      final.stack = s.stack ∧ final.output = s.output ∧
      final.pc = word width (base + 6) ∧ final.halted = false := by
  have readBlock : BlockAt program base (UniformDAGHeadRead.code width headBase) :=
    BlockAt.prefix program base _ _ block
  have lastBlock : BlockAt program (base + 5) ([.allocate 2] : Code width) := by
    simpa only [UniformDAGHeadRead.code_length] using
      BlockAt.suffix program base (UniformDAGHeadRead.code width headBase) _ block
  obtain ⟨ready, trace, r0, r1, r2, r3, heap, stack, output, readyPC, readyRunning⟩ :=
    UniformDAGHeadRead.execution program s base headBase valueBase offset identifier value
      offsetHeld valueHeld headFits valueFits headBound valueBound source stored pc running
      (by omega) readBlock
  let final := { ready.advance with heap := ready.heap.push (ready.reg 2) }
  have pcVal : ready.pc.val = base + 5 := by
    rw [readyPC]; exact Nat.mod_eq_of_lt (by omega)
  have allocate : programStep program ready = some final := by
    unfold programStep
    rw [pcVal, show program[base + 5]? = some (.allocate 2) from lastBlock 0 (by simp)]
    simp [step, final, readyRunning, heap, heapRoom]
  have finalPC : final.pc = word width (base + 6) := by
    simp [final, State.advance, pcVal, Nat.add_assoc]
  have liveReady : ready.liveWords = s.liveWords := by
    simp [State.liveWords, heap, stack, output]
  have liveFinal : final.liveWords = s.liveWords + 1 := by
    simp [final, State.advance, State.liveWords, heap, stack, output]
    omega
  have last := Execution.cons allocate (Execution.refl final)
  refine ⟨final, ?_, ?_, ?_, ?_, ?_, ?_, finalPC, ?_⟩
  · have full := trace.append last
    simpa only [liveReady, liveFinal, Nat.max_self, Nat.max_eq_right (by omega : s.liveWords ≤ s.liveWords + 1)] using full
  all_goals simp [final, State.advance, r2, r3, heap, stack, output, readyRunning]

end Controller.Cost.UniformDAGInputGate
