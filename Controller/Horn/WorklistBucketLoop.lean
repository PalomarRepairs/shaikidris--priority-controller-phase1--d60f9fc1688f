module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Horn.WorklistPropagationStep

public import Mathlib.Tactic.FinCases

@[expose] public section

/-! The fixed bucket loop composes fetched link reads, in-place count updates,
and physical next-pointer returns. Kernel frame proofs refer to the same trace. -/
namespace Controller.Horn.WorklistBucketLoop
open Controller.Cost Controller.Horn.WorklistStorage Controller.Horn.WorklistBucket
variable {width n : Nat}

private theorem word_val (value : Nat) (fits : value < 2 ^ width) :
    (word width value).val = value := Nat.mod_eq_of_lt fits

private theorem fetched (program : Program width 8) (state : State width 8)
    (entry : Nat) (instruction : Instruction width 8)
    (position : state.pc = word width entry) (fits : entry < 2 ^ width)
    (present : program[entry]? = some instruction) :
    programStep program state = step instruction state := by
  unfold programStep
  rw [position, word_val entry fits, present]
  rfl

private theorem advance_pc (state : State width 8) (entry : Nat)
    (position : state.pc = word width entry) (fits : entry < 2 ^ width) :
    state.advance.pc = word width (entry + 1) := by
  simp only [State.advance, position, word_val entry fits]

private theorem node_framed (program : Program width 8) (entry row next node : Nat)
    (state : State width 8) (stored : NodeStored row next node state.heap)
    (present : ∀ phase : Fin 3, program[entry + phase.val]? = (nodeCode width)[phase.val]?)
    (held : state.reg 0 = word width node) (one : state.reg 5 = word width 1)
    (position : state.pc = word width entry) (running : state.halted = false)
    (capacity : entry + 3 < 2 ^ width) (room : state.heap.size < 2 ^ width) :
    ∃ final, Execution program state final 3 state.liveWords ∧
      final.reg 1 = word width row ∧ final.reg 4 = word width next ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      (∀ register : Fin 8, register ≠ 0 → register ≠ 1 → register ≠ 4 → final.reg register = state.reg register) ∧
      final.pc = word width (entry + 3) ∧ final.halted = false := by
  have nodeBound : node < state.heap.size := by have := stored.fits; omega
  have nextBound : node + 1 < state.heap.size := by have := stored.fits; omega
  have nextFits : node + 1 < 2 ^ width := by omega
  have oneFits : 1 < 2 ^ width := by omega
  let s1 := state.advance.put 1 (word width row)
  let s2 := s1.advance.put 0 (word width (node + 1))
  let s3 := s2.advance.put 4 (word width next)
  have pc1 : s1.pc = word width (entry + 1) := advance_pc state entry position (by omega)
  have pc2 : s2.pc = word width (entry + 2) := by
    simpa only [s2, State.put, Nat.add_assoc, Nat.reduceAdd] using advance_pc s1 (entry + 1) pc1 (by omega)
  have first : programStep program state = some s1 := by
    rw [fetched program state entry (.load 1 0) position (by omega) (by simpa [nodeCode] using present ⟨0, by decide⟩)]
    simp [step, running, held, word_val node stored.offsetFits, nodeBound, stored.row, s1]
  have second : programStep program s1 = some s2 := by
    rw [fetched program s1 (entry + 1) (.add 0 0 5) pc1 (by omega) (by simpa [nodeCode] using present ⟨1, by decide⟩)]
    simp [step, s1, s2, State.put, State.advance, running, held, one,
      word_val node stored.offsetFits, word_val 1 oneFits]
  have third : programStep program s2 = some s3 := by
    rw [fetched program s2 (entry + 2) (.load 4 0) pc2 (by omega) (by simpa [nodeCode] using present ⟨2, by decide⟩)]
    simp [step, s2, s1, s3, State.put, State.advance, running,
      word_val (node + 1) nextFits, nextBound, stored.next]
  refine ⟨s3, ?_, ?_, ?_, rfl, rfl, rfl, ?_, ?_, running⟩
  · simpa [s3, s2, s1, State.liveWords, State.put, State.advance] using
      Execution.cons first (Execution.cons second (Execution.cons third (Execution.refl s3)))
  · simp [s3, s2, s1, State.put, State.advance]
  · simp [s3, State.put]
  · intro register notZero notRow notNext
    simp [s3, s2, s1, State.put, State.advance, notZero, notRow, notNext]
  · simpa only [s3, State.put, Nat.add_assoc, Nat.reduceAdd] using advance_pc s2 (entry + 2) pc2 (by omega)

private theorem count_framed (program : Program width 8) (entry row remaining : Nat)
    (rule : Controller.Horn.Worklist.Rule (Fin n)) (fired : Bool) (state : State width 8)
    (stored : MutableStored rule row (remaining + 1) fired state.heap)
    (present : ∀ phase : Fin 5, program[entry + phase.val]? = (countCode width)[phase.val]?)
    (held : state.reg 1 = word width row) (one : state.reg 5 = word width 1)
    (decrement : state.reg 6 = word width (2 ^ width - 1))
    (position : state.pc = word width entry) (running : state.halted = false)
    (capacity : entry + 5 < 2 ^ width) (room : state.heap.size < 2 ^ width) :
    ∃ final, Execution program state final 5 state.liveWords ∧
      MutableStored rule row remaining fired final.heap ∧
      final.reg 7 = word width remaining ∧ final.reg 4 = state.reg 4 ∧
      final.heap.size = state.heap.size ∧ final.stack = state.stack ∧ final.output = state.output ∧
      (∀ register : Fin 8, register ≠ 3 → register ≠ 7 → final.reg register = state.reg register) ∧
      final.pc = word width (entry + 5) ∧ final.halted = false := by
  have rowFits : row < 2 ^ width := by have := stored.fits; omega
  have firstFits : row + 1 < 2 ^ width := by have := stored.fits; omega
  have countFits : row + 2 < 2 ^ width := by have := stored.fits; omega
  have bound : row + 2 < state.heap.size := by have := stored.fits; omega
  have oneFits : 1 < 2 ^ width := by omega
  let s1 := state.advance.put 3 (word width (row + 1))
  let s2 := s1.advance.put 3 (word width (row + 2))
  let s3 := s2.advance.put 7 (word width (remaining + 1))
  let s4 := s3.advance.put 7 (word width remaining)
  let s5 : State width 8 := { s4.advance with heap := state.heap.set (row + 2) (word width remaining) bound }
  have pc1 : s1.pc = word width (entry + 1) := advance_pc state entry position (by omega)
  have pc2 : s2.pc = word width (entry + 2) := by simpa only [s2, State.put, Nat.add_assoc, Nat.reduceAdd] using advance_pc s1 (entry + 1) pc1 (by omega)
  have pc3 : s3.pc = word width (entry + 3) := by simpa only [s3, State.put, Nat.add_assoc, Nat.reduceAdd] using advance_pc s2 (entry + 2) pc2 (by omega)
  have pc4 : s4.pc = word width (entry + 4) := by simpa only [s4, State.put, Nat.add_assoc, Nat.reduceAdd] using advance_pc s3 (entry + 3) pc3 (by omega)
  have first : programStep program state = some s1 := by
    rw [fetched program state entry (.add 3 1 5) position (by omega) (by simpa [countCode] using present ⟨0, by decide⟩)]
    simp [step, running, held, one, word_val row rowFits, word_val 1 oneFits, s1]
  have second : programStep program s1 = some s2 := by
    rw [fetched program s1 (entry + 1) (.add 3 3 5) pc1 (by omega) (by simpa [countCode] using present ⟨1, by decide⟩)]
    simp [step, running, s1, s2, State.put, State.advance, one, word_val (row + 1) firstFits, word_val 1 oneFits, Nat.add_assoc]
  have third : programStep program s2 = some s3 := by
    rw [fetched program s2 (entry + 2) (.load 7 3) pc2 (by omega) (by simpa [countCode] using present ⟨2, by decide⟩)]
    simp [step, running, s1, s2, s3, State.put, State.advance, word_val (row + 2) countFits, bound, stored.countValue]
  have fourth : programStep program s3 = some s4 := by
    rw [fetched program s3 (entry + 3) (.add 7 7 6) pc3 (by omega) (by simpa [countCode] using present ⟨3, by decide⟩)]
    simp only [step, s3, s2, s1, State.put, State.advance, running, Bool.false_eq_true, ite_false]
    simp only [show (7 : Fin 8) = 7 from rfl, ite_true,
      show (6 : Fin 8) ≠ 7 by decide, show (6 : Fin 8) ≠ 3 by decide, decrement, ite_false]
    rw [Controller.Horn.Initialize.word_decrement remaining stored.countFits]
    simp only [s4, s3, s2, s1, State.put, State.advance, running]
  have fifth : programStep program s4 = some s5 := by
    rw [fetched program s4 (entry + 4) (.store 3 7) pc4 (by omega) (by simpa [countCode] using present ⟨4, by decide⟩)]
    simp [step, running, s4, s3, s2, s1, s5, State.put, State.advance, word_val (row + 2) countFits, bound]
  refine ⟨s5, ?_, ?_, ?_, ?_, ?_, rfl, rfl, ?_, ?_, running⟩
  · simpa [s5, s4, s3, s2, s1, State.liveWords, State.put, State.advance] using
      Execution.cons first (Execution.cons second (Execution.cons third (Execution.cons fourth (Execution.cons fifth (Execution.refl s5)))))
  · exact store_count stored (by have := stored.countFits; omega)
  · simp [s5, s4, State.put, State.advance]
  · simp [s5, s4, s3, s2, s1, State.put, State.advance]
  · simp [s5]
  · intro register notAddress notCount
    simp [s5, s4, s3, s2, s1, State.put, State.advance, notAddress, notCount]
  · simpa [s5, Nat.add_assoc] using advance_pc s4 (entry + 4) pc4 (by omega)


/-- Node-zero exits; a positive remaining count returns to the same bucket test.
The ready-row continuation receives the original row and successor registers. -/
def code (width entry exit ready : Nat) : Program width 8 :=
  #[.branchZero 0 (word width exit), .load 1 0, .add 0 0 5, .load 4 0,
    .add 3 1 5, .add 3 3 5, .load 7 3, .add 7 7 6, .store 3 7,
    .branchZero 7 (word width ready), .copy 0 4, .branchZero 2 (word width entry)]

def At (program : Program width 8) (entry exit ready : Nat) : Prop :=
  ∀ phase : Fin 12, program[entry + phase.val]? = (code width entry exit ready)[phase.val]?

@[simp] theorem code_size (width entry exit ready : Nat) : (code width entry exit ready).size = 12 := rfl
@[simp] theorem code_words (width entry exit ready : Nat) : programWords (code width entry exit ready) = 48 := rfl

theorem node_at (program : Program width 8) (entry exit ready : Nat) (present : At program entry exit ready) :
    ∀ phase : Fin 3, program[(entry + 1) + phase.val]? = (nodeCode width)[phase.val]? := by
  intro phase
  fin_cases phase
  · simpa [code, nodeCode] using present ⟨1, by decide⟩
  · simpa [code, nodeCode] using present ⟨2, by decide⟩
  · simpa [code, nodeCode] using present ⟨3, by decide⟩

theorem count_at (program : Program width 8) (entry exit ready : Nat) (present : At program entry exit ready) :
    ∀ phase : Fin 5, program[(entry + 4) + phase.val]? = (countCode width)[phase.val]? := by
  intro phase
  fin_cases phase
  · simpa [code, countCode, Nat.add_assoc] using present ⟨4, by decide⟩
  · simpa [code, countCode, Nat.add_assoc] using present ⟨5, by decide⟩
  · simpa [code, countCode, Nat.add_assoc] using present ⟨6, by decide⟩
  · simpa [code, countCode, Nat.add_assoc] using present ⟨7, by decide⟩
  · simpa [code, countCode, Nat.add_assoc] using present ⟨8, by decide⟩

/-- Eight fetched kernels read the actual next link and decrement the original
record; the endpoint enters the count branch without allocating words. -/
theorem visit_execution (program : Program width 8) (entry exit ready row next node remaining : Nat)
    (rule : Controller.Horn.Worklist.Rule (Fin n)) (fired : Bool) (state : State width 8)
    (linked : NodeStored row next node state.heap)
    (stored : MutableStored rule row (remaining + 1) fired state.heap)
    (present : At program entry exit ready)
    (held : state.reg 0 = word width node) (one : state.reg 5 = word width 1)
    (zero : state.reg 2 = word width 0) (decrement : state.reg 6 = word width (2 ^ width - 1))
    (position : state.pc = word width (entry + 1)) (running : state.halted = false)
    (capacity : entry + 12 < 2 ^ width) (room : state.heap.size < 2 ^ width) :
    ∃ final, Execution program state final 8 state.liveWords ∧
      MutableStored rule row remaining fired final.heap ∧
      final.reg 1 = word width row ∧ final.reg 4 = word width next ∧
      final.reg 7 = word width remaining ∧ final.reg 2 = word width 0 ∧
      final.reg 5 = word width 1 ∧ final.reg 6 = word width (2 ^ width - 1) ∧
      final.heap.size = state.heap.size ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry + 9) ∧ final.halted = false := by
  obtain ⟨middle, first, rowHeld, nextHeld, heap, stack, output, regs, pc, live⟩ :=
    node_framed program (entry + 1) row next node state linked (node_at program entry exit ready present)
      held one position running (by omega) room
  obtain ⟨final, second, result, count, next, size, finalStack, finalOutput, finalRegs, finalPC, finalRunning⟩ :=
    count_framed program (entry + 4) row remaining rule fired middle (by simpa only [heap] using stored)
      (count_at program entry exit ready present) rowHeld ((regs 5 (by decide) (by decide) (by decide)).trans one)
      ((regs 6 (by decide) (by decide) (by decide)).trans decrement)
      (by simpa only [Nat.add_assoc, Nat.reduceAdd] using pc) live (by omega) (by simpa only [heap] using room)
  have middleLive : middle.liveWords = state.liveWords := by unfold State.liveWords; rw [heap, stack, output]
  refine ⟨final, ?_, result, (finalRegs 1 (by decide) (by decide)).trans rowHeld,
    next.trans nextHeld, count,
    (finalRegs 2 (by decide) (by decide)).trans ((regs 2 (by decide) (by decide) (by decide)).trans zero),
    (finalRegs 5 (by decide) (by decide)).trans ((regs 5 (by decide) (by decide) (by decide)).trans one),
    (finalRegs 6 (by decide) (by decide)).trans ((regs 6 (by decide) (by decide) (by decide)).trans decrement),
    size.trans (congrArg Array.size heap), finalStack.trans stack, finalOutput.trans output, ?_, finalRunning⟩
  · simpa only [middleLive, Nat.max_self, Nat.reduceAdd] using first.append second
  · simpa only [Nat.add_assoc, Nat.reduceAdd] using finalPC

/-- A positive count takes the actual fallthrough branch, installs the stored
successor pointer, and returns to the fetched bucket-nil test in three ticks. -/
theorem continue_execution (program : Program width 8) (entry exit ready next remaining : Nat)
    (state : State width 8) (present : At program entry exit ready)
    (count : state.reg 7 = word width remaining) (positive : 0 < remaining)
    (countFits : remaining < 2 ^ width) (nextHeld : state.reg 4 = word width next)
    (zero : state.reg 2 = word width 0)
    (position : state.pc = word width (entry + 9)) (running : state.halted = false)
    (capacity : entry + 12 < 2 ^ width) :
    ∃ final, Execution program state final 3 state.liveWords ∧
      final.reg 0 = word width next ∧ final.heap = state.heap ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width entry ∧ final.halted = false := by
  let tested := Controller.Horn.RuleDispatch.branchFinished state 7 ready
  have testedEq : tested = state.advance := by
    unfold tested Controller.Horn.RuleDispatch.branchFinished
    rw [count, word_val remaining countFits]
    simp only [Nat.ne_of_gt positive, ite_false]
  have first := Controller.Horn.RuleDispatch.branch_execution program (entry + 9) ready 7
    (by simpa [code] using present ⟨9, by decide⟩) state position running (by omega)
  have testedPC : tested.pc = word width (entry + 10) := by
    rw [testedEq]
    simpa only [Nat.add_assoc, Nat.reduceAdd] using advance_pc state (entry + 9) position (by omega)
  let advanced := tested.advance.put 0 (word width next)
  have second : programStep program tested = some advanced := by
    rw [fetched program tested (entry + 10) (.copy 0 4) testedPC (by omega)
      (by simpa [code] using present ⟨10, by decide⟩)]
    simp [step, testedEq, running, nextHeld, advanced, State.advance]
  have advancedPC : advanced.pc = word width (entry + 11) := by
    simpa only [advanced, State.put, Nat.add_assoc, Nat.reduceAdd] using
      advance_pc tested (entry + 10) testedPC (by omega)
  let final := Controller.Horn.RuleDispatch.branchFinished advanced 2 entry
  have third := Controller.Horn.RuleDispatch.branch_execution program (entry + 11) entry 2
    (by simpa [code] using present ⟨11, by decide⟩) advanced advancedPC
    (by simpa [advanced, testedEq, State.put, State.advance] using running) (by omega)
  have frame := Controller.Horn.RuleDispatch.branchFinished_frame advanced 2 entry
  have testedLive : tested.liveWords = state.liveWords := by rw [testedEq]; rfl
  have advancedLive : advanced.liveWords = state.liveWords := by rw [show advanced.liveWords = tested.liveWords from rfl, testedLive]
  refine ⟨final, ?_, ?_, frame.2.1.trans (by simp [advanced, testedEq, State.put, State.advance]),
    frame.2.2.1.trans (by simp [advanced, testedEq, State.put, State.advance]),
    frame.2.2.2.1.trans (by simp [advanced, testedEq, State.put, State.advance]), ?_, ?_⟩
  · have trace := first.append (Execution.cons second third)
    change Execution program state final 3 (max state.liveWords (max tested.liveWords advanced.liveWords)) at trace
    simpa only [testedLive, advancedLive, Nat.max_self] using trace
  · change (Controller.Horn.RuleDispatch.branchFinished advanced 2 entry).reg 0 = _
    rw [frame.1]
    simp [advanced, State.put]
  · have advancedZero : advanced.reg 2 = word width 0 := by simpa [advanced, testedEq, State.put, State.advance] using zero
    simp [final, Controller.Horn.RuleDispatch.branchFinished, advancedZero, word]
  · change (Controller.Horn.RuleDispatch.branchFinished advanced 2 entry).halted = false
    rw [frame.2.2.2.2.1]
    simpa [advanced, testedEq, State.put, State.advance] using running

/-- Nil is recognized by the physically fetched bucket pointer branch. -/
theorem nil_execution (program : Program width 8) (entry exit ready : Nat)
    (state : State width 8) (present : At program entry exit ready)
    (nil : state.reg 0 = word width 0) (position : state.pc = word width entry)
    (running : state.halted = false) (capacity : entry + 12 < 2 ^ width) :
    Execution program state (Controller.Horn.RuleDispatch.branchFinished state 0 exit) 1 state.liveWords ∧
      (Controller.Horn.RuleDispatch.branchFinished state 0 exit).pc = word width exit := by
  refine ⟨Controller.Horn.RuleDispatch.branch_execution program entry exit 0
    (by simpa [code] using present ⟨0, by decide⟩) state position running (by omega), ?_⟩
  simp [Controller.Horn.RuleDispatch.branchFinished, nil, word]

end Controller.Horn.WorklistBucketLoop
