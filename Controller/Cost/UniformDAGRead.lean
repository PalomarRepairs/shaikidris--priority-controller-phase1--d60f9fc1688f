module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SourceGateOperands

@[expose] public section

/-! A fixed indirect read for represented DAG incidences. The program reads the
incidence identifier from the source heap, adds the value-array base held in a
register, and reads the stored Boolean value. Its instructions do not depend on
the graph or on the incidence identifier. -/
namespace Controller.Cost.UniformDAGRead
open Controller.Cost.GateProgram

def code (width : ℕ) : Code width := [.load 0 3, .add 0 0 1, .load 1 0]
@[simp] theorem code_length : (code width).length = 3 := rfl

private theorem fetched (program : Program width 4) (s : State width 4)
    (base : ℕ) (instruction : Instruction width 4)
    (pc : s.pc = word width base) (fits : base < 2 ^ width)
    (entry : program[base]? = some instruction) :
    programStep program s = step instruction s := by
  unfold programStep
  rw [pc, show (word width base).val = base from Nat.mod_eq_of_lt fits, entry]
  rfl

private theorem advance (s : State width 4) (base : ℕ)
    (pc : s.pc = word width base) (fits : base < 2 ^ width) :
    s.advance.pc = word width (base + 1) := by
  simp only [State.advance, pc]
  rw [show (word width base).val = base from Nat.mod_eq_of_lt fits]

/-- Three fetched instructions read an actual source incidence and its stored
value. The accumulator and source cursor remain in registers two and three. -/
theorem execution (program : Program width 4) (s : State width 4)
    (cursor valueBase index base : ℕ) (value : Bool)
    (cursorHeld : s.reg 3 = word width cursor)
    (baseHeld : s.reg 1 = word width valueBase)
    (cursorBound : cursor < s.heap.size) (cursorFits : cursor < 2 ^ width)
    (source : s.heap[cursor]'cursorBound = word width index)
    (valueBound : valueBase + index < s.heap.size)
    (valueFits : valueBase + index < 2 ^ width)
    (stored : s.heap[valueBase + index]'valueBound = boolWord width value)
    (pc : s.pc = word width base) (running : s.halted = false)
    (programFits : base + 3 < 2 ^ width) (block : BlockAt program base (code width)) :
    ∃ ready, Execution program s ready 3 s.liveWords ∧
      ready.reg 0 = word width (valueBase + index) ∧ ready.reg 1 = boolWord width value ∧
      ready.reg 2 = s.reg 2 ∧ ready.reg 3 = s.reg 3 ∧
      ready.heap = s.heap ∧ ready.stack = s.stack ∧ ready.output = s.output ∧
      ready.pc = word width (base + 3) ∧ ready.halted = false := by
  let one := s.advance.put 0 (word width index)
  let two := one.advance.put 0 (word width (valueBase + index))
  let ready := two.advance.put 1 (boolWord width value)
  have indexFits : index < 2 ^ width := by omega
  have baseFits : valueBase < 2 ^ width := by omega
  have indexVal : (word width index).val = index := Nat.mod_eq_of_lt indexFits
  have baseVal : (word width valueBase).val = valueBase := Nat.mod_eq_of_lt baseFits
  have cursorVal : (word width cursor).val = cursor := Nat.mod_eq_of_lt cursorFits
  have valueVal : (word width (valueBase + index)).val = valueBase + index :=
    Nat.mod_eq_of_lt valueFits
  have onePC : one.pc = word width (base + 1) := by
    simpa [one, State.put] using advance s base pc (by omega)
  have twoPC : two.pc = word width (base + 2) := by
    simpa [two, State.put, Nat.add_assoc] using advance one (base + 1) onePC (by omega)
  have readyPC : ready.pc = word width (base + 3) := by
    simpa [ready, State.put, Nat.add_assoc] using advance two (base + 2) twoPC (by omega)
  have step0 : programStep program s = some one := by
    rw [fetched program s base (.load 0 3) pc (by omega)
      (by simpa [code] using block 0 (by simp [code]))]
    simp [step, running, cursorHeld, cursorVal, cursorBound, source, one]
  have step1 : programStep program one = some two := by
    rw [fetched program one (base + 1) (.add 0 0 1) onePC (by omega)
      (by simpa [code] using block 1 (by simp [code]))]
    simp [step, running, one, two, State.advance, State.put, baseHeld,
      indexVal, baseVal, Nat.add_comm]
  have step2 : programStep program two = some ready := by
    rw [fetched program two (base + 2) (.load 1 0) twoPC (by omega)
      (by simpa [code] using block 2 (by simp [code]))]
    simp [step, running, one, two, ready, State.advance, State.put,
      valueVal, valueBound, stored]
  have oneLive : one.liveWords = s.liveWords := rfl
  have twoLive : two.liveWords = s.liveWords := rfl
  have readyLive : ready.liveWords = s.liveWords := rfl
  refine ⟨ready, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, readyPC, running⟩
  · have trace := Execution.cons step0 (Execution.cons step1
      (Execution.cons step2 (Execution.refl ready)))
    simpa [oneLive, twoLive, readyLive] using trace
  all_goals simp [ready, two, one, State.advance, State.put]
end Controller.Cost.UniformDAGRead
