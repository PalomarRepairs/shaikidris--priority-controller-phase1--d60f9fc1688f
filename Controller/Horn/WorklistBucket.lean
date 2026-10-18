module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Horn.WorklistEnqueue

@[expose] public section

/-! Bucket traversal reads the actual two-word link and mutates only the count
and scheduling tag of its original rule record. FIFO off flags describe all
queued labels; count decrements describe the processed prefix and current link. -/
namespace Controller.Horn.WorklistBucket
open Controller.Cost Controller.Horn.WorklistStorage
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

/-- The row and successor come from the linked node, with three fetched ticks. -/
def nodeCode (width : Nat) : Program width 8 := #[.load 1 0, .add 0 0 5, .load 4 0]

theorem node_execution (program : Program width 8) (entry row next node : Nat)
    (state : State width 8) (stored : NodeStored row next node state.heap)
    (present : ∀ phase : Fin 3, program[entry + phase.val]? = (nodeCode width)[phase.val]?)
    (held : state.reg 0 = word width node) (one : state.reg 5 = word width 1)
    (position : state.pc = word width entry) (running : state.halted = false)
    (capacity : entry + 3 < 2 ^ width) (room : state.heap.size < 2 ^ width) :
    ∃ final, Execution program state final 3 state.liveWords ∧
      final.reg 1 = word width row ∧ final.reg 4 = word width next ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
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
  refine ⟨s3, ?_, ?_, ?_, rfl, rfl, rfl, ?_, running⟩
  · simpa [s3, s2, s1, State.liveWords, State.put, State.advance] using
      Execution.cons first (Execution.cons second (Execution.cons third (Execution.refl s3)))
  · simp [s3, s2, s1, State.put, State.advance]
  · simp [s3, State.put]
  · simpa only [s3, State.put, Nat.add_assoc, Nat.reduceAdd] using advance_pc s2 (entry + 2) pc2 (by omega)

/-- Five fetched instructions address the original count, decrement it once,
and store it in place. The predecessor count must be positive. -/
def countCode (width : Nat) : Program width 8 :=
  #[.add 3 1 5, .add 3 3 5, .load 7 3, .add 7 7 6, .store 3 7]

theorem count_execution (program : Program width 8) (entry row remaining : Nat)
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
  refine ⟨s5, ?_, ?_, ?_, ?_, ?_, rfl, rfl, ?_, running⟩
  · simpa [s5, s4, s3, s2, s1, State.liveWords, State.put, State.advance] using
      Execution.cons first (Execution.cons second (Execution.cons third (Execution.cons fourth (Execution.cons fifth (Execution.refl s5)))))
  · exact store_count stored (by have := stored.countFits; omega)
  · simp [s5, s4, State.put, State.advance]
  · simp [s5, s4, s3, s2, s1, State.put, State.advance]
  · simp [s5]
  · simpa [s5, Nat.add_assoc] using advance_pc s4 (entry + 4) pc4 (by omega)

/-- Firing stores the zero tag before the caller dispatches the original head. -/
theorem fire_execution (program : Program width 8) (entry row count : Nat)
    (rule : Controller.Horn.Worklist.Rule (Fin n)) (fired : Bool) (state : State width 8)
    (stored : MutableStored rule row count fired state.heap)
    (present : program[entry]? = some (.store 1 2))
    (held : state.reg 1 = word width row) (zero : state.reg 2 = word width 0)
    (position : state.pc = word width entry) (running : state.halted = false)
    (capacity : entry + 1 < 2 ^ width) (room : state.heap.size < 2 ^ width) :
    ∃ final, Execution program state final 1 state.liveWords ∧
      MutableStored rule row count true final.heap ∧
      final.reg = state.reg ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry + 1) ∧ final.halted = false := by
  have bound : row < state.heap.size := by have := stored.fits; omega
  have fits : row < 2 ^ width := by omega
  let final : State width 8 := { state.advance with heap := state.heap.set row (word width 0) bound }
  have transition : programStep program state = some final := by
    rw [fetched program state entry (.store 1 2) position (by omega) present]
    simp [step, running, held, zero, word_val row fits, bound, final]
  refine ⟨final, ?_, store_fired stored, rfl, rfl, rfl, ?_, running⟩
  · simpa [final, State.liveWords, State.advance] using Execution.cons transition (Execution.refl final)
  · exact advance_pc state entry position (by omega)

/-- A fired row's actual scheduling tag is zero, irrespective of its head/body. -/
theorem fired_tag_zero (rule : Controller.Horn.Worklist.Rule (Fin n)) (row count : Nat)
    (heap : Array (Word width)) (stored : MutableStored rule row count true heap) :
    heap[row]? = some (word width 0) := by
  have bound : row < heap.size := by have := stored.fits; omega
  rw [Array.getElem?_eq_getElem bound]
  exact congrArg some (by simpa using stored.tagValue)

end Controller.Horn.WorklistBucket
