module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Horn.WorklistBucketLoop

public import Mathlib.Tactic.FinCases

@[expose] public section

/-! Ready rows store their fired tag before dispatch. The four retired scratch
headers hold FIFO head/tail, active label and the saved physical bucket successor. -/
namespace Controller.Horn.WorklistBucketReady
open Controller.Cost Controller.Horn.WorklistStorage Controller.Horn.WorklistMark
variable {width n : Nat}

def tailSlot (base : Nat) : Nat := base + 2 * n + 1
def nextSlot (base : Nat) : Nat := base + 2 * n + 3

/-- The ready prefix reads the original tag, fires once, then distinguishes a
positive conflict from a negative head by decrementing the original tag. -/
def readyPrefix (width entry skip conflict : Nat) : Program width 8 :=
  #[.load 7 1, .branchZero 7 (word width skip), .store 1 2,
    .add 7 7 6, .branchZero 7 (word width conflict)]

/-- All adapter words are existing scratch cells. No new cell is allocated. -/
def code (width base entry skip conflict bucket : Nat) : Program width 8 :=
  #[.load 7 1, .branchZero 7 (word width skip), .store 1 2,
    .add 7 7 6, .branchZero 7 (word width conflict),
    .constant 3 (word width (nextSlot (n := n) base)), .store 3 4,
    .add 3 1 5, .load 1 3, .add 3 1 1, .constant 7 (word width (base + 1)), .add 3 3 7,
    .constant 0 (word width (tailSlot (n := n) base)), .load 0 0,
    .load 4 3, .branchZero 4 (word width (entry + 17)), .branchZero 2 (word width (entry + 21)),
    .store 3 5, .store 0 1, .add 0 0 5, .branchZero 2 (word width (entry + 21)),
    .constant 3 (word width (tailSlot (n := n) base)), .store 3 0,
    .constant 0 (word width (nextSlot (n := n) base)), .load 0 0,
    .branchZero 2 (word width bucket)]

def At (program : Program width 8) (base entry skip conflict bucket : Nat) : Prop :=
  ∀ phase : Fin 26, program[entry + phase.val]? = (code (n := n) width base entry skip conflict bucket)[phase.val]?

@[simp] theorem code_size (width base entry skip conflict bucket : Nat) :
    (code (n := n) width base entry skip conflict bucket).size = 26 := rfl
@[simp] theorem code_words (width base entry skip conflict bucket : Nat) :
    programWords (code (n := n) width base entry skip conflict bucket) = 104 := rfl

theorem enqueue_at (program : Program width 8) (base entry skip conflict bucket : Nat)
    (present : At (n := n) program base entry skip conflict bucket) :
    Controller.Horn.WorklistMark.At program (entry + 14) (entry + 21) := by
  intro phase
  fin_cases phase
  · simpa [code, readyPrefix, Controller.Horn.WorklistMark.code] using present ⟨14, by decide⟩
  · simpa [code, readyPrefix, Controller.Horn.WorklistMark.code, Nat.add_assoc] using present ⟨15, by decide⟩
  · simpa [code, readyPrefix, Controller.Horn.WorklistMark.code, Nat.add_assoc] using present ⟨16, by decide⟩
  · simpa [code, readyPrefix, Controller.Horn.WorklistMark.code, Nat.add_assoc] using present ⟨17, by decide⟩
  · simpa [code, readyPrefix, Controller.Horn.WorklistMark.code, Nat.add_assoc] using present ⟨18, by decide⟩
  · simpa [code, readyPrefix, Controller.Horn.WorklistMark.code, Nat.add_assoc] using present ⟨19, by decide⟩
  · simpa [code, readyPrefix, Controller.Horn.WorklistMark.code, Nat.add_assoc] using present ⟨20, by decide⟩

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

/-- A negative ready row executes its actual five-instruction tag prefix.
Its fired store occurs before the immutable head load at the continuation. -/
theorem negative_prefix (program : Program width 8) (base entry skip conflict bucket row : Nat)
    (head : Fin n) (labels : List (Fin n)) (state : State width 8)
    (stored : MutableStored (.negative head labels) row 0 false state.heap)
    (present : At (n := n) program base entry skip conflict bucket)
    (held : state.reg 1 = word width row) (zero : state.reg 2 = word width 0)
    (decrement : state.reg 6 = word width (2 ^ width - 1))
    (position : state.pc = word width entry) (running : state.halted = false)
    (capacity : entry + 26 < 2 ^ width) (room : state.heap.size < 2 ^ width) :
    ∃ final, Execution program state final 5 state.liveWords ∧
      MutableStored (.negative head labels) row 0 true final.heap ∧
      final.reg 1 = state.reg 1 ∧ final.reg 4 = state.reg 4 ∧
      final.reg 2 = state.reg 2 ∧ final.reg 5 = state.reg 5 ∧ final.reg 6 = state.reg 6 ∧
      final.heap = state.heap.set row (word width 0) (by have := stored.fits; omega) ∧
      final.heap.size = state.heap.size ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry + 5) ∧ final.halted = false := by
  have bound : row < state.heap.size := by have := stored.fits; omega
  have fits : row < 2 ^ width := by omega
  have twoFits : 2 < 2 ^ width := by omega
  have oneFits : 1 < 2 ^ width := by omega
  have tag : state.heap[row]'bound = word width 2 := by simpa [Controller.Horn.RuleCopy.tag] using stored.tagValue
  let loaded := state.advance.put 7 (word width 2)
  let tested := loaded.advance
  let marked : State width 8 := { tested.advance with heap := state.heap.set row (word width 0) bound }
  let classified := marked.advance.put 7 (word width 1)
  let final := classified.advance
  have pc1 : loaded.pc = word width (entry + 1) := advance_pc state entry position (by omega)
  have pc2 : tested.pc = word width (entry + 2) := by simpa [tested, Nat.add_assoc] using advance_pc loaded (entry + 1) pc1 (by omega)
  have pc3 : marked.pc = word width (entry + 3) := by simpa [marked, Nat.add_assoc] using advance_pc tested (entry + 2) pc2 (by omega)
  have pc4 : classified.pc = word width (entry + 4) := by simpa only [classified, State.put, Nat.add_assoc, Nat.reduceAdd] using advance_pc marked (entry + 3) pc3 (by omega)
  have first : programStep program state = some loaded := by
    rw [fetched program state entry (.load 7 1) position (by omega) (by simpa [code, readyPrefix] using present ⟨0, by decide⟩)]
    simp [step, running, held, word_val row fits, bound, tag, loaded]
  have second : programStep program loaded = some tested := by
    rw [fetched program loaded (entry + 1) (.branchZero 7 (word width skip)) pc1 (by omega) (by simpa [code, readyPrefix] using present ⟨1, by decide⟩)]
    simp [step, loaded, tested, State.put, State.advance, running, word_val 2 twoFits]
  have third : programStep program tested = some marked := by
    rw [fetched program tested (entry + 2) (.store 1 2) pc2 (by omega) (by simpa [code, readyPrefix] using present ⟨2, by decide⟩)]
    simp [step, loaded, tested, marked, State.put, State.advance, running, held, zero, word_val row fits, bound]
  have fourth : programStep program marked = some classified := by
    rw [fetched program marked (entry + 3) (.add 7 7 6) pc3 (by omega) (by simpa [code, readyPrefix] using present ⟨3, by decide⟩)]
    have minus : word width (2 + (2 ^ width - 1)) = word width 1 := by
      simpa only [Nat.reduceAdd, word_val 2 twoFits,
        word_val (width := width) (2 ^ width - 1) (by omega)] using
        Controller.Horn.Initialize.word_decrement (width := width) 1 (by omega)
    simp [step, loaded, tested, marked, classified, State.put, State.advance, running, decrement, word_val 2 twoFits, word_val (width := width) (2 ^ width - 1) (by omega), minus]
  have fifth : programStep program classified = some final := by
    rw [fetched program classified (entry + 4) (.branchZero 7 (word width conflict)) pc4 (by omega) (by simpa [code, readyPrefix] using present ⟨4, by decide⟩)]
    simp [step, classified, marked, tested, loaded, final, State.put, State.advance, running, word_val 1 oneFits]
  refine ⟨final, ?_, store_fired stored, ?_, ?_, ?_, ?_, ?_, rfl, ?_, rfl, rfl, ?_, running⟩
  · simpa [final, classified, marked, tested, loaded, State.liveWords, State.put, State.advance] using
      Execution.cons first (Execution.cons second (Execution.cons third (Execution.cons fourth (Execution.cons fifth (Execution.refl final)))))
  · simp [final, classified, marked, tested, loaded, State.put, State.advance]
  · simp [final, classified, marked, tested, loaded, State.put, State.advance]
  · simp [final, classified, marked, tested, loaded, State.put, State.advance]
  · simp [final, classified, marked, tested, loaded, State.put, State.advance]
  · simp [final, classified, marked, tested, loaded, State.put, State.advance]
  · simp [final, classified, marked, tested, loaded, State.put, State.advance]
  · simpa only [final, Nat.add_assoc, Nat.reduceAdd] using advance_pc classified (entry + 4) pc4 (by omega)

/-- Nine fetched adapter instructions save the physical successor, read the
original negative head, compute its off address and load the saved FIFO tail. -/
theorem prepare_execution (program : Program width 8) (base entry skip conflict bucket row next tail : Nat)
    (head : Fin n) (state : State width 8)
    (present : At (n := n) program base entry skip conflict bucket)
    (scratchFits : base + 4 * n + 4 ≤ state.heap.size)
    (rowBound : row + 1 < state.heap.size) (separated : base + 5 * n + 4 ≤ row)
    (originalHead : state.heap[row + 1]'rowBound = word width head.val)
    (tailBound : tailSlot (n := n) base < state.heap.size)
    (tailValue : state.heap[tailSlot (n := n) base]'tailBound = word width tail)
    (rowHeld : state.reg 1 = word width row) (nextHeld : state.reg 4 = word width next)
    (one : state.reg 5 = word width 1)
    (position : state.pc = word width (entry + 5)) (running : state.halted = false)
    (capacity : entry + 26 < 2 ^ width) (room : state.heap.size < 2 ^ width) :
    ∃ final, Execution program state final 9 state.liveWords ∧
      final.reg 1 = word width head.val ∧ final.reg 3 = word width (offAddress base head) ∧
      final.reg 0 = word width tail ∧ final.reg 2 = state.reg 2 ∧
      final.reg 5 = state.reg 5 ∧ final.reg 6 = state.reg 6 ∧
      final.heap = state.heap.set (nextSlot (n := n) base) (word width next)
        (by unfold nextSlot; omega) ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry + 14) ∧ final.halted = false := by
  have slotBound : nextSlot (n := n) base < state.heap.size := by unfold nextSlot; omega
  have slotFits : nextSlot (n := n) base < 2 ^ width := by omega
  have rowFits : row < 2 ^ width := by omega
  have rowNextFits : row + 1 < 2 ^ width := by omega
  have headFits : head.val < 2 ^ width := by have := head.isLt; omega
  have doubleFits : 2 * head.val < 2 ^ width := by have := head.isLt; omega
  have baseFits : base + 1 < 2 ^ width := by omega
  have offFits : offAddress base head < 2 ^ width := by have := head.isLt; unfold offAddress; omega
  have tailFits : tailSlot (n := n) base < 2 ^ width := by omega
  have oneFits : 1 < 2 ^ width := by omega
  have rowDifferent : nextSlot (n := n) base ≠ row + 1 := by unfold nextSlot; omega
  have tailDifferent : nextSlot (n := n) base ≠ tailSlot (n := n) base := by unfold nextSlot tailSlot; omega
  let s1 := state.advance.put 3 (word width (nextSlot (n := n) base))
  let s2 : State width 8 := { s1.advance with heap := state.heap.set (nextSlot (n := n) base) (word width next) slotBound }
  let s3 := s2.advance.put 3 (word width (row + 1))
  let s4 := s3.advance.put 1 (word width head.val)
  let s5 := s4.advance.put 3 (word width (2 * head.val))
  let s6 := s5.advance.put 7 (word width (base + 1))
  let s7 := s6.advance.put 3 (word width (offAddress base head))
  let s8 := s7.advance.put 0 (word width (tailSlot (n := n) base))
  let s9 := s8.advance.put 0 (word width tail)
  have pc1 : s1.pc = word width (entry + 6) := by
    simpa only [s1, State.put, Nat.add_assoc, Nat.reduceAdd] using advance_pc state (entry + 5) position (by omega)
  have pc2 : s2.pc = word width (entry + 7) := by
    simpa only [s2, State.put, Nat.add_assoc, Nat.reduceAdd] using advance_pc s1 (entry + 6) pc1 (by omega)
  have pc3 : s3.pc = word width (entry + 8) := by
    simpa only [s3, State.put, Nat.add_assoc, Nat.reduceAdd] using advance_pc s2 (entry + 7) pc2 (by omega)
  have pc4 : s4.pc = word width (entry + 9) := by
    simpa only [s4, State.put, Nat.add_assoc, Nat.reduceAdd] using advance_pc s3 (entry + 8) pc3 (by omega)
  have pc5 : s5.pc = word width (entry + 10) := by
    simpa only [s5, State.put, Nat.add_assoc, Nat.reduceAdd] using advance_pc s4 (entry + 9) pc4 (by omega)
  have pc6 : s6.pc = word width (entry + 11) := by
    simpa only [s6, State.put, Nat.add_assoc, Nat.reduceAdd] using advance_pc s5 (entry + 10) pc5 (by omega)
  have pc7 : s7.pc = word width (entry + 12) := by
    simpa only [s7, State.put, Nat.add_assoc, Nat.reduceAdd] using advance_pc s6 (entry + 11) pc6 (by omega)
  have pc8 : s8.pc = word width (entry + 13) := by
    simpa only [s8, State.put, Nat.add_assoc, Nat.reduceAdd] using advance_pc s7 (entry + 12) pc7 (by omega)
  have pc9 : s9.pc = word width (entry + 14) := by
    simpa only [s9, State.put, Nat.add_assoc, Nat.reduceAdd] using advance_pc s8 (entry + 13) pc8 (by omega)
  have step1 : programStep program state = some s1 := by
    rw [fetched program state (entry + 5) (.constant 3 (word width (nextSlot (n := n) base))) position (by omega)
      (by simpa [code, readyPrefix] using present ⟨5, by decide⟩)]
    simp [step, running, State.put, State.advance, s1, rowHeld, nextHeld, one, word_val (nextSlot (n := n) base) slotFits, word_val row rowFits, word_val (row + 1) rowNextFits, word_val head.val headFits, word_val (2 * head.val) doubleFits, word_val (width := width) (head.val + head.val) (by omega), word_val (base + 1) baseFits, word_val (offAddress base head) offFits, word_val (tailSlot (n := n) base) tailFits, word_val 1 oneFits, slotBound, rowBound, tailBound, Array.getElem_set, rowDifferent, tailDifferent, originalHead, tailValue, offAddress, Nat.two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have step2 : programStep program s1 = some s2 := by
    rw [fetched program s1 (entry + 6) (.store 3 4) pc1 (by omega)
      (by simpa [code, readyPrefix] using present ⟨6, by decide⟩)]
    simp [step, running, State.put, State.advance, s2, s1, rowHeld, nextHeld, one, word_val (nextSlot (n := n) base) slotFits, word_val row rowFits, word_val (row + 1) rowNextFits, word_val head.val headFits, word_val (2 * head.val) doubleFits, word_val (width := width) (head.val + head.val) (by omega), word_val (base + 1) baseFits, word_val (offAddress base head) offFits, word_val (tailSlot (n := n) base) tailFits, word_val 1 oneFits, slotBound, rowBound, tailBound, Array.getElem_set, rowDifferent, tailDifferent, originalHead, tailValue, offAddress, Nat.two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have step3 : programStep program s2 = some s3 := by
    rw [fetched program s2 (entry + 7) (.add 3 1 5) pc2 (by omega)
      (by simpa [code, readyPrefix] using present ⟨7, by decide⟩)]
    simp [step, running, State.put, State.advance, s3, s2, s1, rowHeld, nextHeld, one, word_val (nextSlot (n := n) base) slotFits, word_val row rowFits, word_val (row + 1) rowNextFits, word_val head.val headFits, word_val (2 * head.val) doubleFits, word_val (width := width) (head.val + head.val) (by omega), word_val (base + 1) baseFits, word_val (offAddress base head) offFits, word_val (tailSlot (n := n) base) tailFits, word_val 1 oneFits, slotBound, rowBound, tailBound, Array.getElem_set, rowDifferent, tailDifferent, originalHead, tailValue, offAddress, Nat.two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have step4 : programStep program s3 = some s4 := by
    rw [fetched program s3 (entry + 8) (.load 1 3) pc3 (by omega)
      (by simpa [code, readyPrefix] using present ⟨8, by decide⟩)]
    simp [step, running, State.put, State.advance, s4, s3, s2, s1, rowHeld, nextHeld, one, word_val (nextSlot (n := n) base) slotFits, word_val row rowFits, word_val (row + 1) rowNextFits, word_val head.val headFits, word_val (2 * head.val) doubleFits, word_val (width := width) (head.val + head.val) (by omega), word_val (base + 1) baseFits, word_val (offAddress base head) offFits, word_val (tailSlot (n := n) base) tailFits, word_val 1 oneFits, slotBound, rowBound, tailBound, Array.getElem_set, rowDifferent, tailDifferent, originalHead, tailValue, offAddress, Nat.two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have step5 : programStep program s4 = some s5 := by
    rw [fetched program s4 (entry + 9) (.add 3 1 1) pc4 (by omega)
      (by simpa [code, readyPrefix] using present ⟨9, by decide⟩)]
    simp [step, running, State.put, State.advance, s5, s4, s3, s2, s1, rowHeld, nextHeld, one, word_val (nextSlot (n := n) base) slotFits, word_val row rowFits, word_val (row + 1) rowNextFits, word_val head.val headFits, word_val (2 * head.val) doubleFits, word_val (width := width) (head.val + head.val) (by omega), word_val (base + 1) baseFits, word_val (offAddress base head) offFits, word_val (tailSlot (n := n) base) tailFits, word_val 1 oneFits, slotBound, rowBound, tailBound, Array.getElem_set, rowDifferent, tailDifferent, originalHead, tailValue, offAddress, Nat.two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have step6 : programStep program s5 = some s6 := by
    rw [fetched program s5 (entry + 10) (.constant 7 (word width (base + 1))) pc5 (by omega)
      (by simpa [code, readyPrefix] using present ⟨10, by decide⟩)]
    simp [step, running, State.put, State.advance, s6, s5, s4, s3, s2, s1, rowHeld, nextHeld, one, word_val (nextSlot (n := n) base) slotFits, word_val row rowFits, word_val (row + 1) rowNextFits, word_val head.val headFits, word_val (2 * head.val) doubleFits, word_val (width := width) (head.val + head.val) (by omega), word_val (base + 1) baseFits, word_val (offAddress base head) offFits, word_val (tailSlot (n := n) base) tailFits, word_val 1 oneFits, slotBound, rowBound, tailBound, Array.getElem_set, rowDifferent, tailDifferent, originalHead, tailValue, offAddress, Nat.two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have step7 : programStep program s6 = some s7 := by
    rw [fetched program s6 (entry + 11) (.add 3 3 7) pc6 (by omega)
      (by simpa [code, readyPrefix] using present ⟨11, by decide⟩)]
    simp [step, running, State.put, State.advance, s7, s6, s5, s4, s3, s2, s1, rowHeld, nextHeld, one, word_val (nextSlot (n := n) base) slotFits, word_val row rowFits, word_val (row + 1) rowNextFits, word_val head.val headFits, word_val (2 * head.val) doubleFits, word_val (width := width) (head.val + head.val) (by omega), word_val (base + 1) baseFits, word_val (offAddress base head) offFits, word_val (tailSlot (n := n) base) tailFits, word_val 1 oneFits, slotBound, rowBound, tailBound, Array.getElem_set, rowDifferent, tailDifferent, originalHead, tailValue, offAddress, Nat.two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have step8 : programStep program s7 = some s8 := by
    rw [fetched program s7 (entry + 12) (.constant 0 (word width (tailSlot (n := n) base))) pc7 (by omega)
      (by simpa [code, readyPrefix] using present ⟨12, by decide⟩)]
    simp [step, running, State.put, State.advance, s8, s7, s6, s5, s4, s3, s2, s1, rowHeld, nextHeld, one, word_val (nextSlot (n := n) base) slotFits, word_val row rowFits, word_val (row + 1) rowNextFits, word_val head.val headFits, word_val (2 * head.val) doubleFits, word_val (width := width) (head.val + head.val) (by omega), word_val (base + 1) baseFits, word_val (offAddress base head) offFits, word_val (tailSlot (n := n) base) tailFits, word_val 1 oneFits, slotBound, rowBound, tailBound, Array.getElem_set, rowDifferent, tailDifferent, originalHead, tailValue, offAddress, Nat.two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have step9 : programStep program s8 = some s9 := by
    rw [fetched program s8 (entry + 13) (.load 0 0) pc8 (by omega)
      (by simpa [code, readyPrefix] using present ⟨13, by decide⟩)]
    simp [step, running, State.put, State.advance, s9, s8, s7, s6, s5, s4, s3, s2, s1, rowHeld, nextHeld, one, word_val (nextSlot (n := n) base) slotFits, word_val row rowFits, word_val (row + 1) rowNextFits, word_val head.val headFits, word_val (2 * head.val) doubleFits, word_val (width := width) (head.val + head.val) (by omega), word_val (base + 1) baseFits, word_val (offAddress base head) offFits, word_val (tailSlot (n := n) base) tailFits, word_val 1 oneFits, slotBound, rowBound, tailBound, Array.getElem_set, rowDifferent, tailDifferent, originalHead, tailValue, offAddress, Nat.two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  refine ⟨s9, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, pc9, running⟩
  · simpa [s9, s8, s7, s6, s5, s4, s3, s2, s1, State.liveWords, State.put, State.advance] using Execution.cons step1 (Execution.cons step2 (Execution.cons step3 (Execution.cons step4 (Execution.cons step5 (Execution.cons step6 (Execution.cons step7 (Execution.cons step8 (Execution.cons step9 (Execution.refl s9)))))))))
  · simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, State.put, State.advance]
  · simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, State.put, State.advance]
  · simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, State.put, State.advance]
  · simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, State.put, State.advance]
  · simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, State.put, State.advance]
  · simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, State.put, State.advance]

/-- After either enqueue path, five fetched instructions save the FIFO tail,
restore the saved physical successor and return to the bucket test. -/
theorem return_execution (program : Program width 8) (base entry skip conflict bucket next tail : Nat)
    (state : State width 8) (present : At (n := n) program base entry skip conflict bucket)
    (scratchFits : base + 4 * n + 4 ≤ state.heap.size)
    (nextBound : nextSlot (n := n) base < state.heap.size)
    (nextValue : state.heap[nextSlot (n := n) base]'nextBound = word width next)
    (held : state.reg 0 = word width tail) (zero : state.reg 2 = word width 0)
    (position : state.pc = word width (entry + 21)) (running : state.halted = false)
    (capacity : entry + 26 < 2 ^ width) (room : state.heap.size < 2 ^ width) :
    ∃ final, Execution program state final 5 state.liveWords ∧
      final.reg 0 = word width next ∧
      final.heap = state.heap.set (tailSlot (n := n) base) (word width tail)
        (by unfold tailSlot; omega) ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width bucket ∧ final.halted = false := by
  have tailBound : tailSlot (n := n) base < state.heap.size := by unfold tailSlot; omega
  have tailFits : tailSlot (n := n) base < 2 ^ width := by omega
  have nextFits : nextSlot (n := n) base < 2 ^ width := by omega
  have different : tailSlot (n := n) base ≠ nextSlot (n := n) base := by unfold tailSlot nextSlot; omega
  let s1 := state.advance.put 3 (word width (tailSlot (n := n) base))
  let s2 : State width 8 := { s1.advance with heap := state.heap.set (tailSlot (n := n) base) (word width tail) tailBound }
  let s3 := s2.advance.put 0 (word width (nextSlot (n := n) base))
  let s4 := s3.advance.put 0 (word width next)
  let final := Controller.Horn.RuleDispatch.branchFinished s4 2 bucket
  have pc1 : s1.pc = word width (entry + 22) := by
    simpa only [s1, State.put, Nat.add_assoc, Nat.reduceAdd] using advance_pc state (entry + 21) position (by omega)
  have pc2 : s2.pc = word width (entry + 23) := by
    simpa only [s2, State.put, Nat.add_assoc, Nat.reduceAdd] using advance_pc s1 (entry + 22) pc1 (by omega)
  have pc3 : s3.pc = word width (entry + 24) := by
    simpa only [s3, State.put, Nat.add_assoc, Nat.reduceAdd] using advance_pc s2 (entry + 23) pc2 (by omega)
  have pc4 : s4.pc = word width (entry + 25) := by
    simpa only [s4, State.put, Nat.add_assoc, Nat.reduceAdd] using advance_pc s3 (entry + 24) pc3 (by omega)
  have step1 : programStep program state = some s1 := by
    rw [fetched program state (entry + 21) (.constant 3 (word width (tailSlot (n := n) base))) position (by omega)
      (by simpa [code, readyPrefix] using present ⟨21, by decide⟩)]
    simp [step, running, State.put, State.advance, s1, held, word_val (tailSlot (n := n) base) tailFits, word_val (nextSlot (n := n) base) nextFits, tailBound, nextBound, Array.getElem_set, different, nextValue]
  have step2 : programStep program s1 = some s2 := by
    rw [fetched program s1 (entry + 22) (.store 3 0) pc1 (by omega)
      (by simpa [code, readyPrefix] using present ⟨22, by decide⟩)]
    simp [step, running, State.put, State.advance, s2, s1, held, word_val (tailSlot (n := n) base) tailFits, word_val (nextSlot (n := n) base) nextFits, tailBound, nextBound, Array.getElem_set, different, nextValue]
  have step3 : programStep program s2 = some s3 := by
    rw [fetched program s2 (entry + 23) (.constant 0 (word width (nextSlot (n := n) base))) pc2 (by omega)
      (by simpa [code, readyPrefix] using present ⟨23, by decide⟩)]
    simp [step, running, State.put, State.advance, s3, s2, s1, held, word_val (tailSlot (n := n) base) tailFits, word_val (nextSlot (n := n) base) nextFits, tailBound, nextBound, Array.getElem_set, different, nextValue]
  have step4 : programStep program s3 = some s4 := by
    rw [fetched program s3 (entry + 24) (.load 0 0) pc3 (by omega)
      (by simpa [code, readyPrefix] using present ⟨24, by decide⟩)]
    simp [step, running, State.put, State.advance, s4, s3, s2, s1, held, word_val (tailSlot (n := n) base) tailFits, word_val (nextSlot (n := n) base) nextFits, tailBound, nextBound, Array.getElem_set, different, nextValue]
  have fifth := Controller.Horn.RuleDispatch.branch_execution program (entry + 25) bucket 2
    (by simpa [code, readyPrefix] using present ⟨25, by decide⟩) s4 pc4
    (by simpa [s4, s3, s2, s1, State.put, State.advance] using running) (by omega)
  have frame := Controller.Horn.RuleDispatch.branchFinished_frame s4 2 bucket
  have live4 : s4.liveWords = state.liveWords := by simp [s4, s3, s2, s1, State.put, State.advance, State.liveWords]
  refine ⟨final, ?_, ?_, ?_, frame.2.2.1, frame.2.2.2.1, ?_, ?_⟩
  · have trace := Execution.cons step1 (Execution.cons step2 (Execution.cons step3 (Execution.cons step4 fifth)))
    simpa [final, s4, s3, s2, s1, State.put, State.advance, State.liveWords] using trace
  · change (Controller.Horn.RuleDispatch.branchFinished s4 2 bucket).reg 0 = _
    rw [frame.1]
    simp [s4, State.put]
  · change (Controller.Horn.RuleDispatch.branchFinished s4 2 bucket).heap = _
    rw [frame.2.1]
    rfl
  · have finalZero : s4.reg 2 = word width 0 := by simpa [s4, s3, s2, s1, State.put, State.advance] using zero
    simp [final, Controller.Horn.RuleDispatch.branchFinished, finalZero, word]
  · change (Controller.Horn.RuleDispatch.branchFinished s4 2 bucket).halted = false
    rw [frame.2.2.2.2.1]
    exact running

private theorem commit_zero (program : Program width 8) (entry exit base : Nat)
    (enqueued : List (Fin n)) (label : Fin n) (state : State width 8)
    (present : Controller.Horn.WorklistMark.At program entry exit)
    (offBound : offAddress base label < state.heap.size)
    (queueBound : queueStart (n := n) base + enqueued.length < state.heap.size)
    (offHeld : state.reg 3 = word width (offAddress base label))
    (tailHeld : state.reg 0 = word width (queueStart (n := n) base + enqueued.length))
    (labelHeld : state.reg 1 = word width label.val)
    (one : state.reg 5 = word width 1) (zero : state.reg 2 = word width 0)
    (position : state.pc = word width (entry + 3)) (running : state.halted = false)
    (capacity : entry + 7 < 2 ^ width) (exitFits : exit < 2 ^ width)
    (room : state.heap.size < 2 ^ width) :
    ∃ final, Execution program state final 4 state.liveWords ∧
      final.heap = committedHeap state base enqueued label offBound queueBound ∧
      final.heap.size = state.heap.size ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.reg 0 = word width (queueStart (n := n) base + enqueued.length + 1) ∧
      final.pc = word width exit ∧ final.halted = false ∧ final.reg 2 = state.reg 2 := by
  let offAddressWord := offAddress base label
  let tailAddress := queueStart (n := n) base + enqueued.length
  let marked : State width 8 := { state.advance with heap := state.heap.set offAddressWord (word width 1) offBound }
  let queued : State width 8 := { marked.advance with
    heap := marked.heap.set tailAddress (word width label.val) (by simpa [marked] using queueBound) }
  let advanced := queued.advance.put 0 (word width (tailAddress + 1))
  let final := Controller.Horn.RuleDispatch.branchFinished advanced 2 exit
  have storeMark : program[entry + 3]? = some (.store 3 5) := by simpa [Controller.Horn.WorklistMark.code] using present ⟨3, by decide⟩
  have storeQueue : program[entry + 4]? = some (.store 0 1) := by simpa [Controller.Horn.WorklistMark.code] using present ⟨4, by decide⟩
  have increment : program[entry + 5]? = some (.add 0 0 5) := by simpa [Controller.Horn.WorklistMark.code] using present ⟨5, by decide⟩
  have returnAt : program[entry + 6]? = some (.branchZero 2 (word width exit)) := by simpa [Controller.Horn.WorklistMark.code] using present ⟨6, by decide⟩
  have pcFits (phase : Nat) (bound : phase ≤ 7) : entry + phase < 2 ^ width := by omega
  have addrFits : offAddressWord < 2 ^ width := by dsimp [offAddressWord]; omega
  have tailFits : tailAddress < 2 ^ width := by dsimp [tailAddress]; omega
  have oneFits : 1 < 2 ^ width := by omega
  have markedPosition : marked.pc = word width (entry + 4) := by
    simp [marked, State.advance, position, word_val (width := width) (entry + 3) (pcFits 3 (by decide)), Nat.add_assoc]
  have queuedPosition : queued.pc = word width (entry + 5) := by
    simp [queued, State.advance, markedPosition, word_val (width := width) (entry + 4) (pcFits 4 (by decide)), Nat.add_assoc]
  have advancedPosition : advanced.pc = word width (entry + 6) := by
    simp [advanced, State.put, State.advance, queuedPosition, word_val (width := width) (entry + 5) (pcFits 5 (by decide)), Nat.add_assoc]
  have first : programStep program state = some marked := by
    unfold programStep
    rw [position, show (word width (entry + 3)).val = entry + 3 from Nat.mod_eq_of_lt (pcFits 3 (by decide)), storeMark]
    simp [step, running, offBound, offHeld, one, marked,
      word_val (width := width) (offAddress base label) addrFits, offAddressWord]
  have second : programStep program marked = some queued := by
    unfold programStep
    rw [markedPosition, show (word width (entry + 4)).val = entry + 4 from Nat.mod_eq_of_lt (pcFits 4 (by decide)), storeQueue]
    simp [step, running, queueBound, marked, queued, tailHeld, labelHeld, State.advance,
      word_val (width := width) (queueStart (n := n) base + enqueued.length) tailFits, tailAddress]
  have third : programStep program queued = some advanced := by
    unfold programStep
    rw [queuedPosition, show (word width (entry + 5)).val = entry + 5 from Nat.mod_eq_of_lt (pcFits 5 (by decide)), increment]
    simp [step, running, queued, marked, advanced, State.advance, State.put, tailHeld, one,
      word_val (width := width) (queueStart (n := n) base + enqueued.length) tailFits,
      word_val (width := width) 1 oneFits, tailAddress]
  have fourth := Controller.Horn.RuleDispatch.branch_execution program (entry + 6) exit 2 returnAt advanced
    advancedPosition (by simpa [advanced, queued, marked, State.put, State.advance] using running) (pcFits 6 (by decide))
  have frame := Controller.Horn.RuleDispatch.branchFinished_frame advanced 2 exit
  refine ⟨final, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [final, advanced, queued, marked, State.liveWords, State.put, State.advance] using
      Execution.cons first (Execution.cons second (Execution.cons third fourth))
  · change (Controller.Horn.RuleDispatch.branchFinished advanced 2 exit).heap = _
    rw [frame.2.1]
    rfl
  · change (Controller.Horn.RuleDispatch.branchFinished advanced 2 exit).heap.size = _
    rw [frame.2.1]
    simp [advanced, queued, marked, State.put, State.advance]
  · exact frame.2.2.1
  · exact frame.2.2.2.1
  · change (Controller.Horn.RuleDispatch.branchFinished advanced 2 exit).reg 0 = _
    rw [frame.1]
    simp [advanced, State.put, tailAddress]
  · simp [final, Controller.Horn.RuleDispatch.branchFinished, advanced, queued, marked,
      State.put, State.advance, zero, word]
  · change (Controller.Horn.RuleDispatch.branchFinished advanced 2 exit).halted = false
    rw [frame.2.2.2.2.1]
    exact running

  · change (Controller.Horn.RuleDispatch.branchFinished advanced 2 exit).reg 2 = _
    rw [frame.1]
    simp [advanced, queued, marked, State.put, State.advance]

private theorem fresh_saved (program : Program width 8) (entry exit base : Nat)
    (enqueued : List (Fin n)) (label : Fin n) (state : State width 8)
    (present : Controller.Horn.WorklistMark.At program entry exit) (stored : Stored enqueued base state.heap)
    (fresh : label ∉ enqueued)
    (offHeld : state.reg 3 = word width (offAddress base label))
    (tailHeld : state.reg 0 = word width (queueStart (n := n) base + enqueued.length))
    (labelHeld : state.reg 1 = word width label.val)
    (one : state.reg 5 = word width 1) (zero : state.reg 2 = word width 0)
    (position : state.pc = word width entry) (running : state.halted = false)
    (capacity : entry + 7 < 2 ^ width) (exitFits : exit < 2 ^ width)
    (row : Nat) (separated : base + 5 * n + 4 ≤ row)
    (room : state.heap.size < 2 ^ width) :
    ∃ final, Execution program state final 6 state.liveWords ∧
      Stored (enqueued ++ [label]) base final.heap ∧
      final.heap.size = state.heap.size ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.reg 0 = word width (queueStart (n := n) base + enqueued.length + 1) ∧
      final.pc = word width exit ∧ final.halted = false ∧ final.reg 2 = state.reg 2 ∧
      (∀ pos, (base + 2 * n ≤ pos ∧ pos < queueStart (n := n) base) ∨ row ≤ pos →
        final.heap[pos]? = state.heap[pos]?) := by
  have queueRoom := fresh_enqueue_bound enqueued stored.nodup label fresh
  have offBound : offAddress base label < state.heap.size := by
    have := stored.fits; have := label.isLt; unfold offAddress; omega
  have queueBound : queueStart (n := n) base + enqueued.length < state.heap.size := by
    have := stored.fits; unfold queueStart; omega
  have off : state.heap[offAddress base label]'offBound = word width 0 := by
    simpa only [ite_eq_right fresh] using stored.flags label
  let loaded := state.advance.put 4 (word width 0)
  let middle := Controller.Horn.RuleDispatch.branchFinished loaded 4 (entry + 3)
  have first := fresh_guard program entry exit base state label present offBound off offHeld position running capacity room
  have frame := Controller.Horn.RuleDispatch.branchFinished_frame loaded 4 (entry + 3)
  have middleHeap : middle.heap = state.heap := frame.2.1
  have middleLive : middle.liveWords = state.liveWords := by
    change (Controller.Horn.RuleDispatch.branchFinished loaded 4 (entry + 3)).liveWords = _
    rw [frame.2.2.2.2.2]
    rfl
  have middleRegister (register : Fin 8) (different : register ≠ 4) : middle.reg register = state.reg register := by
    change (Controller.Horn.RuleDispatch.branchFinished loaded 4 (entry + 3)).reg register = _
    rw [frame.1]
    simp [loaded, State.put, State.advance, different]
  obtain ⟨final, second, finalHeap, size, stack, output, tail, finalPosition, finalRunning, finalZero⟩ :=
    commit_zero program entry exit base enqueued label middle present
      (by simpa only [middleHeap] using offBound) (by simpa only [middleHeap] using queueBound)
      ((middleRegister 3 (by decide)).trans offHeld) ((middleRegister 0 (by decide)).trans tailHeld)
      ((middleRegister 1 (by decide)).trans labelHeld) ((middleRegister 5 (by decide)).trans one)
      ((middleRegister 2 (by decide)).trans zero) first.2.1
      (by change (Controller.Horn.RuleDispatch.branchFinished loaded 4 (entry + 3)).halted = false
          rw [frame.2.2.2.2.1]; exact running)
      capacity exitFits (by simpa only [middleHeap] using room)
  refine ⟨final, ?_, ?_, size.trans (congrArg Array.size middleHeap),
    stack.trans frame.2.2.1, output.trans frame.2.2.2.1, tail, finalPosition, finalRunning,
    finalZero.trans (middleRegister 2 (by decide)), ?_⟩
  · simpa only [middleLive, Nat.max_self, Nat.reduceAdd] using first.1.append second
  · rw [finalHeap]
    exact committed_stored enqueued base middle (by simpa only [middleHeap] using stored) label fresh _ _

  · intro pos coverage
    have offDifferent : offAddress base label ≠ pos := by
      have := label.isLt
      unfold offAddress at *
      rcases coverage with low | high <;> omega
    have queueDifferent : queueStart (n := n) base + enqueued.length ≠ pos := by
      unfold queueStart at *
      rcases coverage with low | high <;> omega
    rw [finalHeap]
    simp [committedHeap, Array.getElem?_set, offDifferent, queueDifferent, middleHeap]

private theorem stale_zero (program : Program width 8) (entry exit base : Nat) (state : State width 8)
    (label : Fin n) (present : Controller.Horn.WorklistMark.At program entry exit)
    (offBound : offAddress base label < state.heap.size)
    (off : state.heap[offAddress base label]'offBound = word width 1)
    (held : state.reg 3 = word width (offAddress base label)) (zero : state.reg 2 = word width 0)
    (position : state.pc = word width entry) (running : state.halted = false)
    (capacity : entry + 7 < 2 ^ width) (exitFits : exit < 2 ^ width)
    (room : state.heap.size < 2 ^ width) :
    ∃ final, Execution program state final 3 state.liveWords ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.reg 0 = state.reg 0 ∧ final.pc = word width exit ∧ final.halted = false ∧ final.reg 2 = state.reg 2 := by
  let loaded := state.advance.put 4 (word width 1)
  let tested := Controller.Horn.RuleDispatch.branchFinished loaded 4 (entry + 3)
  let final := Controller.Horn.RuleDispatch.branchFinished tested 2 exit
  have loadAt : program[entry]? = some (.load 4 3) := by simpa [Controller.Horn.WorklistMark.code] using present ⟨0, by decide⟩
  have branchAt : program[entry + 1]? = some (.branchZero 4 (word width (entry + 3))) := by simpa [Controller.Horn.WorklistMark.code] using present ⟨1, by decide⟩
  have returnAt : program[entry + 2]? = some (.branchZero 2 (word width exit)) := by simpa [Controller.Horn.WorklistMark.code] using present ⟨2, by decide⟩
  have addressFits : offAddress base label < 2 ^ width := by omega
  have oneFits : 1 < 2 ^ width := by have := label.isLt; unfold offAddress at offBound; omega
  have first : programStep program state = some loaded := by
    unfold programStep
    rw [position, show (word width entry).val = entry from Nat.mod_eq_of_lt (by omega), loadAt]
    simp [step, held, loaded, running, offBound, off, word_val (width := width) (offAddress base label) addressFits]
  have loadedPosition : loaded.pc = word width (entry + 1) := by
    simp [loaded, State.put, State.advance, position, show (word width entry).val = entry from Nat.mod_eq_of_lt (by omega)]
  have second := Controller.Horn.RuleDispatch.branch_execution program (entry + 1) (entry + 3) 4 branchAt loaded
    loadedPosition (by simpa [loaded, State.put, State.advance] using running) (by omega)
  have testedEq : tested = loaded.advance := by
    change Controller.Horn.RuleDispatch.branchFinished loaded 4 (entry + 3) = _
    have loadedOne : (loaded.reg 4).val = 1 := by
      change (word width 1).val = 1
      exact word_val 1 oneFits
    unfold Controller.Horn.RuleDispatch.branchFinished
    rw [loadedOne]
    rfl
  have testedPosition : tested.pc = word width (entry + 2) := by
    rw [testedEq]
    simp only [State.advance, loadedPosition, word_val (width := width) (entry + 1) (by omega)]
  have testedZero : tested.reg 2 = word width 0 := by
    simpa only [testedEq, State.advance, loaded, State.put, ite_eq_right (show (2 : Fin 8) ≠ 4 by decide)] using zero
  have third := Controller.Horn.RuleDispatch.branch_execution program (entry + 2) exit 2 returnAt tested
    testedPosition (by simpa only [testedEq, State.advance, loaded, State.put] using running) (by omega)
  have testedFrame := Controller.Horn.RuleDispatch.branchFinished_frame loaded 4 (entry + 3)
  have finalFrame := Controller.Horn.RuleDispatch.branchFinished_frame tested 2 exit
  refine ⟨final, ?_, finalFrame.2.1.trans testedFrame.2.1,
    finalFrame.2.2.1.trans testedFrame.2.2.1, finalFrame.2.2.2.1.trans testedFrame.2.2.2.1, ?_, ?_, ?_, ?_⟩
  · have loadedLive : loaded.liveWords = state.liveWords := rfl
    have testedLive : tested.liveWords = state.liveWords := by rw [testedEq]; rfl
    simpa only [loadedLive, testedLive, Nat.max_self, Nat.reduceAdd] using Execution.cons first (second.append third)
  · change (Controller.Horn.RuleDispatch.branchFinished tested 2 exit).reg 0 = _
    rw [finalFrame.1, testedEq]
    simp [loaded, State.put, State.advance]
  · simp [final, Controller.Horn.RuleDispatch.branchFinished, testedZero, word]
  · change (Controller.Horn.RuleDispatch.branchFinished tested 2 exit).halted = false
    rw [finalFrame.2.2.2.2.1, testedEq]
    exact running

  · change (Controller.Horn.RuleDispatch.branchFinished tested 2 exit).reg 2 = _
    rw [finalFrame.1, testedEq]
    simp [loaded, State.put, State.advance]


private theorem fifo_frame (queue : List (Fin n)) (base : Nat) (before after : Array (Word width))
    (stored : Controller.Horn.WorklistMark.Stored queue base before) (size : after.size = before.size)
    (frame : ∀ pos, pos < base + 2 * n ∨
      (queueStart (n := n) base ≤ pos ∧ pos < base + 4 * n + 4) → after[pos]? = before[pos]?) :
    Controller.Horn.WorklistMark.Stored queue base after := by
  have cell (pos : Nat) (inside : pos < before.size) (coverage : pos < base + 2 * n ∨
      (queueStart (n := n) base ≤ pos ∧ pos < base + 4 * n + 4)) :
      after[pos]'(by omega) = before[pos]'inside := by
    have equal := frame pos coverage
    rw [Array.getElem?_eq_getElem (by omega), Array.getElem?_eq_getElem inside] at equal
    exact Option.some.inj equal
  refine ⟨stored.nodup, by rw [size]; exact stored.fits, ?_, ?_⟩
  · intro label
    have inside : offAddress base label < before.size := by have := stored.fits; have := label.isLt; unfold offAddress; omega
    exact (cell _ inside (Or.inl (by have := label.isLt; unfold offAddress; omega))).trans (stored.flags label)
  · refine ⟨by rw [size]; exact stored.queue.fits, ?_⟩
    intro index
    have length := enqueue_bound queue stored.nodup
    have inside : queueStart (n := n) base + index.val < before.size := by have := stored.queue.fits; have := index.isLt; omega
    exact (cell _ inside (Or.inr ⟨by omega, by have := index.isLt; unfold queueStart; omega⟩)).trans (stored.queue.entry index)

private theorem fifo_store (queue : List (Fin n)) (base index : Nat) (heap : Array (Word width))
    (stored : Controller.Horn.WorklistMark.Stored queue base heap) (bound : index < heap.size)
    (outside : (base + 2 * n ≤ index ∧ index < queueStart (n := n) base) ∨ base + 4 * n + 4 ≤ index)
    (value : Word width) : Controller.Horn.WorklistMark.Stored queue base (heap.set index value bound) := by
  apply fifo_frame queue base heap _ stored (by simp)
  intro pos coverage
  have different : index ≠ pos := by rcases outside with low | high <;> rcases coverage with flags | queue <;> omega
  exact Array.getElem?_set_ne bound different

private theorem mutable_frame (rule : Controller.Horn.Worklist.Rule (Fin n)) (row count : Nat) (fired : Bool)
    (before after : Array (Word width)) (stored : MutableStored rule row count fired before)
    (size : after.size = before.size)
    (frame : ∀ pos, row ≤ pos → pos < before.size → after[pos]? = before[pos]?) :
    MutableStored rule row count fired after := by
  have cell (pos : Nat) (above : row ≤ pos) (inside : pos < before.size) :
      after[pos]'(by omega) = before[pos]'inside := by
    have equal := frame pos above inside
    rw [Array.getElem?_eq_getElem (by omega), Array.getElem?_eq_getElem inside] at equal
    exact Option.some.inj equal
  refine ⟨by rw [size]; exact stored.fits, stored.countFits,
    (cell row (by omega) (by have := stored.fits; omega)).trans stored.tagValue,
    (cell (row + 1) (by omega) (by have := stored.fits; omega)).trans stored.headValue,
    (cell (row + 2) (by omega) (by have := stored.fits; omega)).trans stored.countValue, ?_⟩
  refine ⟨by rw [size]; exact stored.body.fits, ?_⟩
  intro index
  exact (cell (row + 3 + index.val) (by omega) (by have := stored.body.fits; have := index.isLt; omega)).trans (stored.body.entry index)

private theorem mutable_store_below (rule : Controller.Horn.Worklist.Rule (Fin n)) (row count : Nat) (fired : Bool)
    (heap : Array (Word width)) (stored : MutableStored rule row count fired heap)
    (index : Nat) (bound : index < heap.size) (below : index < row) (value : Word width) :
    MutableStored rule row count fired (heap.set index value bound) := by
  apply mutable_frame rule row count fired heap _ stored (by simp)
  intro pos above inside
  exact Array.getElem?_set_ne bound (by omega)

def queueAfter (queue : List (Fin n)) (head : Fin n) : List (Fin n) :=
  if head ∈ queue then queue else queue ++ [head]

private theorem enqueue_saved (program : Program width 8) (base entry skip conflict bucket row next : Nat)
    (queue : List (Fin n)) (head : Fin n) (labels : List (Fin n)) (state : State width 8)
    (present : At (n := n) program base entry skip conflict bucket)
    (fifo : Controller.Horn.WorklistMark.Stored queue base state.heap)
    (stored : MutableStored (.negative head labels) row 0 true state.heap)
    (separated : base + 5 * n + 4 ≤ row)
    (saved : state.heap[nextSlot (n := n) base]? = some (word width next))
    (offHeld : state.reg 3 = word width (offAddress base head))
    (tailHeld : state.reg 0 = word width (queueStart (n := n) base + queue.length))
    (headHeld : state.reg 1 = word width head.val)
    (one : state.reg 5 = word width 1) (zero : state.reg 2 = word width 0)
    (position : state.pc = word width (entry + 14)) (running : state.halted = false)
    (capacity : entry + 26 < 2 ^ width) (room : state.heap.size < 2 ^ width) :
    ∃ final, Execution program state final (if head ∈ queue then 3 else 6) state.liveWords ∧
      Controller.Horn.WorklistMark.Stored (queueAfter queue head) base final.heap ∧
      MutableStored (.negative head labels) row 0 true final.heap ∧
      final.heap[nextSlot (n := n) base]? = some (word width next) ∧
      final.reg 0 = word width (queueStart (n := n) base + (queueAfter queue head).length) ∧
      final.reg 2 = word width 0 ∧ final.heap.size = state.heap.size ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry + 21) ∧ final.halted = false := by
  by_cases stale : head ∈ queue
  · have offBound : offAddress base head < state.heap.size := by have := fifo.fits; have := head.isLt; unfold offAddress; omega
    have off : state.heap[offAddress base head]'offBound = word width 1 := by simpa only [ite_eq_left stale] using fifo.flags head
    obtain ⟨final, trace, heap, stack, output, tail, pc, live, finalZero⟩ :=
      stale_zero program (entry + 14) (entry + 21) base state head (enqueue_at program base entry skip conflict bucket present)
        offBound off offHeld zero position running (by omega) (by omega) room
    refine ⟨final, by simpa only [ite_eq_left stale] using trace,
      by simpa only [heap, queueAfter, ite_eq_left stale] using fifo,
      by simpa only [heap] using stored, by simpa only [heap] using saved, ?_, finalZero.trans zero,
      congrArg Array.size heap, stack, output, pc, live⟩
    simpa only [queueAfter, ite_eq_left stale] using tail.trans tailHeld
  · obtain ⟨final, trace, fifoFinal, size, stack, output, tail, pc, live, finalZero, frame⟩ :=
      fresh_saved program (entry + 14) (entry + 21) base queue head state
        (enqueue_at program base entry skip conflict bucket present) fifo stale offHeld tailHeld headHeld one zero
        position running (by omega) (by omega) row separated room
    refine ⟨final, by simpa only [ite_eq_right stale] using trace,
      by simpa only [queueAfter, ite_eq_right stale] using fifoFinal, ?_, ?_, ?_, finalZero.trans zero,
      size, stack, output, pc, live⟩
    · exact mutable_frame (.negative head labels) row 0 true state.heap final.heap stored size
        (fun pos above _ => frame pos (Or.inr above))
    · rw [frame _ (Or.inl ⟨by unfold nextSlot; omega, by unfold nextSlot queueStart; omega⟩)]
      exact saved
    · simpa [queueAfter, stale, Nat.add_assoc] using tail

/-- One complete ready negative row reaches the bucket test through actual
fire/head/FIFO stores: twenty-five fresh ticks or twenty-two stale ticks. -/
theorem negative_execution (program : Program width 8) (base entry skip conflict bucket row next : Nat)
    (queue : List (Fin n)) (head : Fin n) (labels : List (Fin n)) (state : State width 8)
    (present : At (n := n) program base entry skip conflict bucket)
    (fifo : Controller.Horn.WorklistMark.Stored queue base state.heap)
    (stored : MutableStored (.negative head labels) row 0 false state.heap)
    (separated : base + 5 * n + 4 ≤ row)
    (tailBound : tailSlot (n := n) base < state.heap.size)
    (tailValue : state.heap[tailSlot (n := n) base]'tailBound =
      word width (queueStart (n := n) base + queue.length))
    (rowHeld : state.reg 1 = word width row) (nextHeld : state.reg 4 = word width next)
    (one : state.reg 5 = word width 1) (zero : state.reg 2 = word width 0)
    (decrement : state.reg 6 = word width (2 ^ width - 1))
    (position : state.pc = word width entry) (running : state.halted = false)
    (capacity : entry + 26 < 2 ^ width) (room : state.heap.size < 2 ^ width) :
    ∃ final, Execution program state final (if head ∈ queue then 22 else 25) state.liveWords ∧
      Controller.Horn.WorklistMark.Stored (queueAfter queue head) base final.heap ∧
      MutableStored (.negative head labels) row 0 true final.heap ∧
      final.reg 0 = word width next ∧ final.heap.size = state.heap.size ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width bucket ∧ final.halted = false := by
  obtain ⟨firedState, fireTrace, firedStored, rowFrame, nextFrame, zeroFrame, oneFrame, decrementFrame,
      firedHeap, firedSize, firedStack, firedOutput, firedPC, firedRunning⟩ :=
    negative_prefix program base entry skip conflict bucket row head labels state stored present rowHeld zero decrement
      position running capacity room
  have rowBound : row < state.heap.size := by have := stored.fits; omega
  have firedFifo : Controller.Horn.WorklistMark.Stored queue base firedState.heap := by
    rw [firedHeap]
    exact fifo_store queue base row state.heap fifo rowBound (Or.inr (by omega)) (word width 0)
  have firedTailBound : tailSlot (n := n) base < firedState.heap.size := by omega
  have firedTail : firedState.heap[tailSlot (n := n) base]'firedTailBound =
      word width (queueStart (n := n) base + queue.length) := by
    simpa only [firedHeap] using
      (Array.getElem_set_ne rowBound tailBound (by unfold tailSlot; omega)).trans tailValue
  have headBound : row + 1 < firedState.heap.size := by have := firedStored.fits; omega
  have originalHead : firedState.heap[row + 1]'headBound = word width head.val := by
    simpa [Controller.Horn.RuleCopy.headWord] using firedStored.headValue
  obtain ⟨prepared, prepareTrace, headReady, offReady, tailReady, preparedZero, preparedOne, preparedDecrement,
      preparedHeap, preparedStack, preparedOutput, preparedPC, preparedRunning⟩ :=
    prepare_execution program base entry skip conflict bucket row next (queueStart (n := n) base + queue.length)
      head firedState present firedFifo.fits headBound separated originalHead firedTailBound firedTail
      (rowFrame.trans rowHeld) (nextFrame.trans nextHeld) (oneFrame.trans one) firedPC firedRunning capacity (by omega)
  have preparedSize : prepared.heap.size = firedState.heap.size := by rw [preparedHeap]; simp
  have nextBound : nextSlot (n := n) base < firedState.heap.size := by have := firedFifo.fits; unfold nextSlot; omega
  have preparedFifo : Controller.Horn.WorklistMark.Stored queue base prepared.heap := by
    rw [preparedHeap]
    exact fifo_store queue base _ firedState.heap firedFifo nextBound
      (Or.inl ⟨by unfold nextSlot; omega, by unfold nextSlot queueStart; omega⟩) (word width next)
  have preparedStored : MutableStored (.negative head labels) row 0 true prepared.heap := by
    rw [preparedHeap]
    exact mutable_store_below _ row 0 true firedState.heap firedStored _ nextBound
      (by unfold nextSlot; omega) (word width next)
  have saved : prepared.heap[nextSlot (n := n) base]? = some (word width next) := by
    rw [preparedHeap]
    simp
  obtain ⟨queued, enqueueTrace, queuedFifo, queuedStored, queuedNext, queuedTail, queuedZero, queuedSize,
      queuedStack, queuedOutput, queuedPC, queuedRunning⟩ :=
    enqueue_saved program base entry skip conflict bucket row next queue head labels prepared present preparedFifo
      preparedStored separated saved offReady tailReady headReady (preparedOne.trans (oneFrame.trans one))
      (preparedZero.trans (zeroFrame.trans zero)) preparedPC preparedRunning capacity (by omega)
  have queuedNextBound : nextSlot (n := n) base < queued.heap.size := by have := queuedFifo.fits; unfold nextSlot; omega
  have queuedNextValue : queued.heap[nextSlot (n := n) base]'queuedNextBound = word width next := by
    rw [Array.getElem?_eq_getElem queuedNextBound] at queuedNext
    exact Option.some.inj queuedNext
  obtain ⟨final, returnTrace, finalNext, finalHeap, finalStack, finalOutput, finalPC, finalRunning⟩ :=
    return_execution program base entry skip conflict bucket next
      (queueStart (n := n) base + (queueAfter queue head).length) queued present queuedFifo.fits queuedNextBound
      queuedNextValue queuedTail queuedZero queuedPC queuedRunning capacity (by omega)
  have finalSize : final.heap.size = queued.heap.size := by rw [finalHeap]; simp
  have finalFifo : Controller.Horn.WorklistMark.Stored (queueAfter queue head) base final.heap := by
    rw [finalHeap]
    exact fifo_store _ base _ queued.heap queuedFifo (by have := queuedFifo.fits; unfold tailSlot; omega)
      (Or.inl ⟨by unfold tailSlot; omega, by unfold tailSlot queueStart; omega⟩) _
  have finalStored : MutableStored (.negative head labels) row 0 true final.heap := by
    rw [finalHeap]
    exact mutable_store_below _ row 0 true queued.heap queuedStored _
      (by have := queuedFifo.fits; unfold tailSlot; omega) (by unfold tailSlot; omega) _
  have fireLive : firedState.liveWords = state.liveWords := by unfold State.liveWords; rw [firedSize, firedStack, firedOutput]
  have prepareLive : prepared.liveWords = state.liveWords := by unfold State.liveWords; rw [preparedSize, preparedStack, preparedOutput]; exact fireLive
  have queueLive : queued.liveWords = state.liveWords := by unfold State.liveWords; rw [queuedSize, queuedStack, queuedOutput]; exact prepareLive
  refine ⟨final, ?_, finalFifo, finalStored, finalNext, ?_,
    finalStack.trans (queuedStack.trans (preparedStack.trans firedStack)),
    finalOutput.trans (queuedOutput.trans (preparedOutput.trans firedOutput)), finalPC, finalRunning⟩
  · have trace := ((fireTrace.append prepareTrace).append enqueueTrace).append returnTrace
    rw [fireLive, prepareLive, queueLive] at trace
    by_cases stale : head ∈ queue <;> simpa [stale] using trace
  · exact finalSize.trans (queuedSize.trans (preparedSize.trans firedSize))

end Controller.Horn.WorklistBucketReady
