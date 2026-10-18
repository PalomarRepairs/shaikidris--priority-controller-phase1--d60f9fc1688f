module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Horn.SourceDirectory

public import Mathlib.Tactic.FinCases

@[expose] public section

/-!
# Fetched clause-directory entry

The shared outer loop tests stored directory pointers, loads one start/end pair,
advances the physical directory cursor by two words, and writes the existing
source headers. The following shared row block consumes those stored pointers.
-/
namespace Controller.Horn.ClauseEntry

open Controller.Cost Controller.Horn.SourceScan Controller.Horn.SourceDirectory

/-- Six termination-test instructions and ten entry instructions. Register two
retains zero, register five retains one, and register six retains minus one. -/
def code (width directoryHeader endHeader inputHeader firstHeader exit : Nat) : Program width 8 :=
  #[.constant 0 (word width directoryHeader), .load 0 0,
    .constant 4 (word width endHeader), .load 4 4, .xor 1 0 4,
    .branchZero 1 (word width exit),
    .load 3 0, .add 0 0 5, .load 4 0, .add 0 0 5,
    .constant 7 (word width directoryHeader), .store 7 0,
    .constant 0 (word width firstHeader), .store 0 3,
    .constant 0 (word width inputHeader), .store 0 4]

@[simp] theorem code_size (width directoryHeader endHeader inputHeader firstHeader exit : Nat) :
    (code width directoryHeader endHeader inputHeader firstHeader exit).size = 16 := rfl

def At (program : Program width 8) (entry directoryHeader endHeader inputHeader firstHeader exit : Nat) : Prop :=
  ∀ phase : Fin 16, program[entry + phase.val]? =
    some (code width directoryHeader endHeader inputHeader firstHeader exit)[phase.val]

/-- A proof index selects the stored directory entry, but no index or row length
is placed in a machine register. -/
structure Input (clauses : List (Controller.CNF.Clause (Fin n))) (layout : Layout clauses)
    (index : Nat) (state : State width 8) : Prop where
  represented : Stored clauses layout.directory layout.source state.heap
  indexBound : index ≤ clauses.length
  cursor : CursorStored (layout.directory + 2 * index) layout.directoryHeader state.heap
  endpoint : CursorStored (layout.directory + 2 * clauses.length) layout.endHeader state.heap
  zero : state.reg 2 = word width 0
  one : state.reg 5 = word width 1
  decrement : state.reg 6 = word width (2 ^ width - 1)
  running : state.halted = false


/-- The shared directory test reuses the checked six-instruction physical
pointer comparison. Both values are fetched from header cells. -/
theorem At.test_at {program : Program width 8}
    {entry directoryHeader endHeader inputHeader firstHeader exit : Nat}
    (present : At program entry directoryHeader endHeader inputHeader firstHeader exit) :
    Controller.Horn.RowScan.TestAt program entry directoryHeader endHeader exit := by
  intro phase
  have fetch := present ⟨phase.val, by have := phase.isLt; omega⟩
  fin_cases phase <;>
    simpa [code, Controller.Horn.RowScan.testCode] using fetch

/-- Canonical state after the actual ten entry instructions. Every updated
pointer is the value loaded from the physical source directory. -/
def prepared (state : State width 8) (pointer rowStart rowEnd directoryHeader firstHeader inputHeader : Nat)
    (directoryBound : directoryHeader < state.heap.size)
    (firstBound : firstHeader < state.heap.size) (inputBound : inputHeader < state.heap.size) : State width 8 :=
  let readStart := state.advance.put 3 (word width rowStart)
  let nextWord := readStart.advance.put 0 (word width (pointer + 1))
  let readEnd := nextWord.advance.put 4 (word width rowEnd)
  let nextEntry := readEnd.advance.put 0 (word width (pointer + 2))
  let addressDirectory := nextEntry.advance.put 7 (word width directoryHeader)
  let updatedDirectory : State width 8 := { addressDirectory.advance with heap :=
      (addressDirectory.heap.set directoryHeader (word width (pointer + 2)) directoryBound) }
  let addressFirst := updatedDirectory.advance.put 0 (word width firstHeader)
  let updatedFirst : State width 8 := { addressFirst.advance with heap :=
      (addressFirst.heap.set firstHeader (word width rowStart) (by simpa [addressFirst, updatedDirectory,
        addressDirectory, nextEntry, readEnd, nextWord, readStart, State.advance, State.put] using firstBound)) }
  let addressInput := updatedFirst.advance.put 0 (word width inputHeader)
  { addressInput.advance with heap := (addressInput.heap.set inputHeader (word width rowEnd)
      (by simpa [addressInput, updatedFirst, addressFirst, updatedDirectory, addressDirectory,
        nextEntry, readEnd, nextWord, readStart, State.advance, State.put] using inputBound)) }


/-- Only four working registers are overwritten during directory entry. -/
theorem prepared_common (state : State width 8) (pointer rowStart rowEnd directoryHeader firstHeader inputHeader : Nat)
    (directoryBound : directoryHeader < state.heap.size)
    (firstBound : firstHeader < state.heap.size) (inputBound : inputHeader < state.heap.size)
    (register : Fin 8) (notAddress : register ≠ 0) (notStart : register ≠ 3)
    (notEnd : register ≠ 4) (notDirectory : register ≠ 7) :
    (prepared state pointer rowStart rowEnd directoryHeader firstHeader inputHeader
      directoryBound firstBound inputBound).reg register = state.reg register := by
  simp [prepared, State.advance, State.put, notAddress, notStart, notEnd, notDirectory]

theorem prepared_caller (state : State width 8) (pointer rowStart rowEnd directoryHeader firstHeader inputHeader : Nat)
    (directoryBound : directoryHeader < state.heap.size)
    (firstBound : firstHeader < state.heap.size) (inputBound : inputHeader < state.heap.size) :
    (prepared state pointer rowStart rowEnd directoryHeader firstHeader inputHeader
      directoryBound firstBound inputBound).stack = state.stack ∧
    (prepared state pointer rowStart rowEnd directoryHeader firstHeader inputHeader
      directoryBound firstBound inputBound).output = state.output := ⟨rfl, rfl⟩

/-- Input/directory stores precede both immutable directory rows and source
pairs. This fact is independent of the values copied into those headers. -/
theorem prepared_frame (state : State width 8) (pointer rowStart rowEnd directoryHeader firstHeader inputHeader : Nat)
    (directoryBound : directoryHeader < state.heap.size)
    (firstBound : firstHeader < state.heap.size) (inputBound : inputHeader < state.heap.size)
    (index : Nat) (notDirectory : directoryHeader ≠ index)
    (notFirst : firstHeader ≠ index) (notInput : inputHeader ≠ index) :
    (prepared state pointer rowStart rowEnd directoryHeader firstHeader inputHeader
      directoryBound firstBound inputBound).heap[index]? = state.heap[index]? := by
  simp only [prepared, State.advance, State.put]
  rw [Array.getElem?_set_ne _ notInput, Array.getElem?_set_ne _ notFirst,
    Array.getElem?_set_ne _ notDirectory]


/-- The directory termination test is an actual fetched execution. It branches
on equality of the two loaded pointer words, rather than a supplied row count. -/
theorem directory_test_execution (program : Program width 8)
    (entry directoryHeader endHeader inputHeader firstHeader exit : Nat)
    (clauses : List (Controller.CNF.Clause (Fin n))) (directory index : Nat)
    (present : At program entry directoryHeader endHeader inputHeader firstHeader exit)
    (state : State width 8)
    (cursor : CursorStored (directory + 2 * index) directoryHeader state.heap)
    (endpoint : CursorStored (directory + 2 * clauses.length) endHeader state.heap)
    (indexBound : index ≤ clauses.length)
    (directoryFits : directory + 2 * clauses.length ≤ state.heap.size)
    (position : state.pc = word width entry) (running : state.halted = false)
    (capacity : entry + 16 < 2 ^ width) (heapFits : state.heap.size < 2 ^ width) :
    Execution program state
      (Controller.Horn.RowScan.testFinished state directoryHeader endHeader
        (directory + 2 * index) (directory + 2 * clauses.length) exit) 6 state.liveWords ∧
    (Controller.Horn.RowScan.testFinished state directoryHeader endHeader
      (directory + 2 * index) (directory + 2 * clauses.length) exit).pc =
        word width (if index = clauses.length then exit else entry + 6) ∧
    (Controller.Horn.RowScan.testFinished state directoryHeader endHeader
      (directory + 2 * index) (directory + 2 * clauses.length) exit).heap = state.heap := by
  have pointerFits : directory + 2 * index < 2 ^ width := by omega
  have endFits : directory + 2 * clauses.length < 2 ^ width := by omega
  have trace := Controller.Horn.RowScan.test_execution program entry directoryHeader endHeader
    (directory + 2 * index) (directory + 2 * clauses.length) exit present.test_at
    state cursor endpoint position running (by omega) heapFits pointerFits endFits
  have pc := Controller.Horn.RowScan.testFinished_position state directoryHeader endHeader
    (directory + 2 * index) (directory + 2 * clauses.length) exit entry position (by omega)
  have equal : (directory + 2 * index = directory + 2 * clauses.length) ↔ index = clauses.length := by omega
  refine ⟨trace, ?_, (Controller.Horn.RowScan.testFinished_frame state directoryHeader endHeader
    (directory + 2 * index) (directory + 2 * clauses.length) exit).2.1⟩
  simpa only [equal] using pc


/-- Fetch for the entry routine is justified from a physical program position. -/
theorem fetched (program : Program width 8)
    (entry directoryHeader endHeader inputHeader firstHeader exit : Nat)
    (present : At program entry directoryHeader endHeader inputHeader firstHeader exit)
    (state : State width 8) (phase : Fin 16)
    (position : state.pc = word width (entry + phase.val))
    (capacity : entry + 16 < 2 ^ width) :
    program[state.pc.val]? = some (code width directoryHeader endHeader inputHeader firstHeader exit)[phase.val] := by
  have fits : entry + phase.val < 2 ^ width := by have := phase.isLt; omega
  rw [position, show (word width (entry + phase.val)).val = entry + phase.val from Nat.mod_eq_of_lt fits]
  exact present phase

/-- Every microstep consumes the opcode actually stored in the shared entry
routine. The abstract operation transition does not replace a fetch. -/
theorem step_at (program : Program width 8)
    (entry directoryHeader endHeader inputHeader firstHeader exit : Nat)
    (present : At program entry directoryHeader endHeader inputHeader firstHeader exit)
    (state next : State width 8) (phase : Fin 16)
    (position : state.pc = word width (entry + phase.val))
    (capacity : entry + 16 < 2 ^ width)
    (actual : step (code width directoryHeader endHeader inputHeader firstHeader exit)[phase.val] state = some next) :
    programStep program state = some next := by
  unfold programStep
  rw [fetched program entry directoryHeader endHeader inputHeader firstHeader exit present state phase position capacity]
  exact actual


private theorem word_value (value : Nat) (fits : value < 2 ^ width) :
    (word width value).val = value := Nat.mod_eq_of_lt fits

/-- Ten actual fetched operations load a directory pair and write the three
control headers. The proof uses the two stored boundary words as load values. -/
theorem setup_execution (program : Program width 8)
    (entry directoryHeader endHeader inputHeader firstHeader exit pointer rowStart rowEnd : Nat)
    (present : At program entry directoryHeader endHeader inputHeader firstHeader exit)
    (state : State width 8)
    (first : CursorStored rowStart pointer state.heap)
    (last : CursorStored rowEnd (pointer + 1) state.heap)
    (directoryBound : directoryHeader < state.heap.size)
    (firstBound : firstHeader < state.heap.size) (inputBound : inputHeader < state.heap.size)
    (heldPointer : state.reg 0 = word width pointer) (one : state.reg 5 = word width 1)
    (position : state.pc = word width (entry + 6)) (running : state.halted = false)
    (capacity : entry + 16 < 2 ^ width) (heapFits : state.heap.size < 2 ^ width)
    (pointerFits : pointer + 2 < 2 ^ width) :
    Execution program state
      (prepared state pointer rowStart rowEnd directoryHeader firstHeader inputHeader
        directoryBound firstBound inputBound) 10 state.liveWords := by
  let s1 := state.advance.put 3 (word width rowStart)
  let s2 := s1.advance.put 0 (word width (pointer + 1))
  let s3 := s2.advance.put 4 (word width rowEnd)
  let s4 := s3.advance.put 0 (word width (pointer + 2))
  let s5 := s4.advance.put 7 (word width directoryHeader)
  let s6 : State width 8 := { s5.advance with heap := (s5.heap.set directoryHeader
      (word width (pointer + 2)) (by simpa [s5, s4, s3, s2, s1, State.advance, State.put] using directoryBound)) }
  let s7 := s6.advance.put 0 (word width firstHeader)
  let s8 : State width 8 := { s7.advance with heap := (s7.heap.set firstHeader
      (word width rowStart) (by simpa [s7, s6, s5, s4, s3, s2, s1, State.advance, State.put] using firstBound)) }
  let s9 := s8.advance.put 0 (word width inputHeader)
  let s10 : State width 8 := { s9.advance with heap := (s9.heap.set inputHeader
      (word width rowEnd) (by simpa [s9, s8, s7, s6, s5, s4, s3, s2, s1, State.advance, State.put] using inputBound)) }
  have oneFits : 1 < 2 ^ width := by omega
  have directoryFits : directoryHeader < 2 ^ width := by omega
  have firstFits : firstHeader < 2 ^ width := by omega
  have inputFits : inputHeader < 2 ^ width := by omega
  have pc1 : state.pc = word width (entry + 6) := by
    simp only [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, State.advance, State.put, position, Nat.add_assoc, Nat.reduceAdd,
      word_value (width := width) (entry + 6) (by omega),
      word_value (width := width) (entry + 7) (by omega),
      word_value (width := width) (entry + 8) (by omega),
      word_value (width := width) (entry + 9) (by omega),
      word_value (width := width) (entry + 10) (by omega),
      word_value (width := width) (entry + 11) (by omega),
      word_value (width := width) (entry + 12) (by omega),
      word_value (width := width) (entry + 13) (by omega),
      word_value (width := width) (entry + 14) (by omega),
      word_value (width := width) (entry + 15) (by omega)]
  have step1 : programStep program state = some s1 := by
    apply step_at program entry directoryHeader endHeader inputHeader firstHeader exit
      present state s1 ⟨6, by decide⟩ pc1 capacity
    simp [code, step, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, State.advance, State.put, running, heldPointer, one,
      word_value (width := width) pointer (by omega),
      word_value (width := width) (pointer + 1) (by omega),
      word_value (width := width) 1 oneFits,
      word_value (width := width) directoryHeader directoryFits,
      word_value (width := width) firstHeader firstFits,
      word_value (width := width) inputHeader inputFits,
      first.bound, last.bound, first.value, last.value,
      directoryBound, firstBound, inputBound, Nat.add_assoc]
  have pc2 : s1.pc = word width (entry + 7) := by
    simp only [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, State.advance, State.put, position, Nat.add_assoc, Nat.reduceAdd,
      word_value (width := width) (entry + 6) (by omega),
      word_value (width := width) (entry + 7) (by omega),
      word_value (width := width) (entry + 8) (by omega),
      word_value (width := width) (entry + 9) (by omega),
      word_value (width := width) (entry + 10) (by omega),
      word_value (width := width) (entry + 11) (by omega),
      word_value (width := width) (entry + 12) (by omega),
      word_value (width := width) (entry + 13) (by omega),
      word_value (width := width) (entry + 14) (by omega),
      word_value (width := width) (entry + 15) (by omega)]
  have step2 : programStep program s1 = some s2 := by
    apply step_at program entry directoryHeader endHeader inputHeader firstHeader exit
      present s1 s2 ⟨7, by decide⟩ pc2 capacity
    simp [code, step, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, State.advance, State.put, running, heldPointer, one,
      word_value (width := width) pointer (by omega),
      word_value (width := width) (pointer + 1) (by omega),
      word_value (width := width) 1 oneFits,
      word_value (width := width) directoryHeader directoryFits,
      word_value (width := width) firstHeader firstFits,
      word_value (width := width) inputHeader inputFits,
      first.bound, last.bound, first.value, last.value,
      directoryBound, firstBound, inputBound, Nat.add_assoc]
  have pc3 : s2.pc = word width (entry + 8) := by
    simp only [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, State.advance, State.put, position, Nat.add_assoc, Nat.reduceAdd,
      word_value (width := width) (entry + 6) (by omega),
      word_value (width := width) (entry + 7) (by omega),
      word_value (width := width) (entry + 8) (by omega),
      word_value (width := width) (entry + 9) (by omega),
      word_value (width := width) (entry + 10) (by omega),
      word_value (width := width) (entry + 11) (by omega),
      word_value (width := width) (entry + 12) (by omega),
      word_value (width := width) (entry + 13) (by omega),
      word_value (width := width) (entry + 14) (by omega),
      word_value (width := width) (entry + 15) (by omega)]
  have step3 : programStep program s2 = some s3 := by
    apply step_at program entry directoryHeader endHeader inputHeader firstHeader exit
      present s2 s3 ⟨8, by decide⟩ pc3 capacity
    simp [code, step, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, State.advance, State.put, running, heldPointer, one,
      word_value (width := width) pointer (by omega),
      word_value (width := width) (pointer + 1) (by omega),
      word_value (width := width) 1 oneFits,
      word_value (width := width) directoryHeader directoryFits,
      word_value (width := width) firstHeader firstFits,
      word_value (width := width) inputHeader inputFits,
      first.bound, last.bound, first.value, last.value,
      directoryBound, firstBound, inputBound, Nat.add_assoc]
  have pc4 : s3.pc = word width (entry + 9) := by
    simp only [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, State.advance, State.put, position, Nat.add_assoc, Nat.reduceAdd,
      word_value (width := width) (entry + 6) (by omega),
      word_value (width := width) (entry + 7) (by omega),
      word_value (width := width) (entry + 8) (by omega),
      word_value (width := width) (entry + 9) (by omega),
      word_value (width := width) (entry + 10) (by omega),
      word_value (width := width) (entry + 11) (by omega),
      word_value (width := width) (entry + 12) (by omega),
      word_value (width := width) (entry + 13) (by omega),
      word_value (width := width) (entry + 14) (by omega),
      word_value (width := width) (entry + 15) (by omega)]
  have step4 : programStep program s3 = some s4 := by
    apply step_at program entry directoryHeader endHeader inputHeader firstHeader exit
      present s3 s4 ⟨9, by decide⟩ pc4 capacity
    simp [code, step, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, State.advance, State.put, running, heldPointer, one,
      word_value (width := width) pointer (by omega),
      word_value (width := width) (pointer + 1) (by omega),
      word_value (width := width) 1 oneFits,
      word_value (width := width) directoryHeader directoryFits,
      word_value (width := width) firstHeader firstFits,
      word_value (width := width) inputHeader inputFits,
      first.bound, last.bound, first.value, last.value,
      directoryBound, firstBound, inputBound, Nat.add_assoc]
  have pc5 : s4.pc = word width (entry + 10) := by
    simp only [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, State.advance, State.put, position, Nat.add_assoc, Nat.reduceAdd,
      word_value (width := width) (entry + 6) (by omega),
      word_value (width := width) (entry + 7) (by omega),
      word_value (width := width) (entry + 8) (by omega),
      word_value (width := width) (entry + 9) (by omega),
      word_value (width := width) (entry + 10) (by omega),
      word_value (width := width) (entry + 11) (by omega),
      word_value (width := width) (entry + 12) (by omega),
      word_value (width := width) (entry + 13) (by omega),
      word_value (width := width) (entry + 14) (by omega),
      word_value (width := width) (entry + 15) (by omega)]
  have step5 : programStep program s4 = some s5 := by
    apply step_at program entry directoryHeader endHeader inputHeader firstHeader exit
      present s4 s5 ⟨10, by decide⟩ pc5 capacity
    simp [code, step, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, State.advance, State.put, running, heldPointer, one,
      word_value (width := width) pointer (by omega),
      word_value (width := width) (pointer + 1) (by omega),
      word_value (width := width) 1 oneFits,
      word_value (width := width) directoryHeader directoryFits,
      word_value (width := width) firstHeader firstFits,
      word_value (width := width) inputHeader inputFits,
      first.bound, last.bound, first.value, last.value,
      directoryBound, firstBound, inputBound, Nat.add_assoc]
  have pc6 : s5.pc = word width (entry + 11) := by
    simp only [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, State.advance, State.put, position, Nat.add_assoc, Nat.reduceAdd,
      word_value (width := width) (entry + 6) (by omega),
      word_value (width := width) (entry + 7) (by omega),
      word_value (width := width) (entry + 8) (by omega),
      word_value (width := width) (entry + 9) (by omega),
      word_value (width := width) (entry + 10) (by omega),
      word_value (width := width) (entry + 11) (by omega),
      word_value (width := width) (entry + 12) (by omega),
      word_value (width := width) (entry + 13) (by omega),
      word_value (width := width) (entry + 14) (by omega),
      word_value (width := width) (entry + 15) (by omega)]
  have step6 : programStep program s5 = some s6 := by
    apply step_at program entry directoryHeader endHeader inputHeader firstHeader exit
      present s5 s6 ⟨11, by decide⟩ pc6 capacity
    simp [code, step, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, State.advance, State.put, running, heldPointer, one,
      word_value (width := width) pointer (by omega),
      word_value (width := width) (pointer + 1) (by omega),
      word_value (width := width) 1 oneFits,
      word_value (width := width) directoryHeader directoryFits,
      word_value (width := width) firstHeader firstFits,
      word_value (width := width) inputHeader inputFits,
      first.bound, last.bound, first.value, last.value,
      directoryBound, firstBound, inputBound, Nat.add_assoc]
  have pc7 : s6.pc = word width (entry + 12) := by
    simp only [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, State.advance, State.put, position, Nat.add_assoc, Nat.reduceAdd,
      word_value (width := width) (entry + 6) (by omega),
      word_value (width := width) (entry + 7) (by omega),
      word_value (width := width) (entry + 8) (by omega),
      word_value (width := width) (entry + 9) (by omega),
      word_value (width := width) (entry + 10) (by omega),
      word_value (width := width) (entry + 11) (by omega),
      word_value (width := width) (entry + 12) (by omega),
      word_value (width := width) (entry + 13) (by omega),
      word_value (width := width) (entry + 14) (by omega),
      word_value (width := width) (entry + 15) (by omega)]
  have step7 : programStep program s6 = some s7 := by
    apply step_at program entry directoryHeader endHeader inputHeader firstHeader exit
      present s6 s7 ⟨12, by decide⟩ pc7 capacity
    simp [code, step, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, State.advance, State.put, running, heldPointer, one,
      word_value (width := width) pointer (by omega),
      word_value (width := width) (pointer + 1) (by omega),
      word_value (width := width) 1 oneFits,
      word_value (width := width) directoryHeader directoryFits,
      word_value (width := width) firstHeader firstFits,
      word_value (width := width) inputHeader inputFits,
      first.bound, last.bound, first.value, last.value,
      directoryBound, firstBound, inputBound, Nat.add_assoc]
  have pc8 : s7.pc = word width (entry + 13) := by
    simp only [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, State.advance, State.put, position, Nat.add_assoc, Nat.reduceAdd,
      word_value (width := width) (entry + 6) (by omega),
      word_value (width := width) (entry + 7) (by omega),
      word_value (width := width) (entry + 8) (by omega),
      word_value (width := width) (entry + 9) (by omega),
      word_value (width := width) (entry + 10) (by omega),
      word_value (width := width) (entry + 11) (by omega),
      word_value (width := width) (entry + 12) (by omega),
      word_value (width := width) (entry + 13) (by omega),
      word_value (width := width) (entry + 14) (by omega),
      word_value (width := width) (entry + 15) (by omega)]
  have step8 : programStep program s7 = some s8 := by
    apply step_at program entry directoryHeader endHeader inputHeader firstHeader exit
      present s7 s8 ⟨13, by decide⟩ pc8 capacity
    simp [code, step, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, State.advance, State.put, running, heldPointer, one,
      word_value (width := width) pointer (by omega),
      word_value (width := width) (pointer + 1) (by omega),
      word_value (width := width) 1 oneFits,
      word_value (width := width) directoryHeader directoryFits,
      word_value (width := width) firstHeader firstFits,
      word_value (width := width) inputHeader inputFits,
      first.bound, last.bound, first.value, last.value,
      directoryBound, firstBound, inputBound, Nat.add_assoc]
  have pc9 : s8.pc = word width (entry + 14) := by
    simp only [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, State.advance, State.put, position, Nat.add_assoc, Nat.reduceAdd,
      word_value (width := width) (entry + 6) (by omega),
      word_value (width := width) (entry + 7) (by omega),
      word_value (width := width) (entry + 8) (by omega),
      word_value (width := width) (entry + 9) (by omega),
      word_value (width := width) (entry + 10) (by omega),
      word_value (width := width) (entry + 11) (by omega),
      word_value (width := width) (entry + 12) (by omega),
      word_value (width := width) (entry + 13) (by omega),
      word_value (width := width) (entry + 14) (by omega),
      word_value (width := width) (entry + 15) (by omega)]
  have step9 : programStep program s8 = some s9 := by
    apply step_at program entry directoryHeader endHeader inputHeader firstHeader exit
      present s8 s9 ⟨14, by decide⟩ pc9 capacity
    simp [code, step, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, State.advance, State.put, running, heldPointer, one,
      word_value (width := width) pointer (by omega),
      word_value (width := width) (pointer + 1) (by omega),
      word_value (width := width) 1 oneFits,
      word_value (width := width) directoryHeader directoryFits,
      word_value (width := width) firstHeader firstFits,
      word_value (width := width) inputHeader inputFits,
      first.bound, last.bound, first.value, last.value,
      directoryBound, firstBound, inputBound, Nat.add_assoc]
  have pc10 : s9.pc = word width (entry + 15) := by
    simp only [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, State.advance, State.put, position, Nat.add_assoc, Nat.reduceAdd,
      word_value (width := width) (entry + 6) (by omega),
      word_value (width := width) (entry + 7) (by omega),
      word_value (width := width) (entry + 8) (by omega),
      word_value (width := width) (entry + 9) (by omega),
      word_value (width := width) (entry + 10) (by omega),
      word_value (width := width) (entry + 11) (by omega),
      word_value (width := width) (entry + 12) (by omega),
      word_value (width := width) (entry + 13) (by omega),
      word_value (width := width) (entry + 14) (by omega),
      word_value (width := width) (entry + 15) (by omega)]
  have step10 : programStep program s9 = some s10 := by
    apply step_at program entry directoryHeader endHeader inputHeader firstHeader exit
      present s9 s10 ⟨15, by decide⟩ pc10 capacity
    simp [code, step, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, State.advance, State.put, running, heldPointer, one,
      word_value (width := width) pointer (by omega),
      word_value (width := width) (pointer + 1) (by omega),
      word_value (width := width) 1 oneFits,
      word_value (width := width) directoryHeader directoryFits,
      word_value (width := width) firstHeader firstFits,
      word_value (width := width) inputHeader inputFits,
      first.bound, last.bound, first.value, last.value,
      directoryBound, firstBound, inputBound, Nat.add_assoc]
  have trace := Execution.cons step1 (Execution.cons step2 (Execution.cons step3 (Execution.cons step4 (Execution.cons step5 (Execution.cons step6 (Execution.cons step7 (Execution.cons step8 (Execution.cons step9 (Execution.cons step10 (Execution.refl (p := program) s10))))))))))
  simpa [prepared, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, State.liveWords, State.advance, State.put, Nat.max_self] using trace

end Controller.Horn.ClauseEntry
