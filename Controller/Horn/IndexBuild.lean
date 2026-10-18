module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Horn.WorklistStorage

public import Mathlib.Tactic.FinCases

@[expose] public section

/-! One physical retained-positive incidence reads its label and bucket head,
allocates a two-word link, stores its new head, and advances actual cursors.
The row scan/end tests and completed index invariant are separate consumers. -/
namespace Controller.Horn.IndexBuild
open Controller.Cost Controller.Horn.WorklistStorage
variable {width n : Nat}

def code (width base : Nat) : Program width 8 :=
  #[.load 3 0, .add 3 3 3, .constant 4 (word width base), .add 3 3 4,
    .load 4 3, .allocate 1, .allocate 4, .store 3 7,
    .add 7 7 5, .add 7 7 5, .add 0 0 5]

@[simp] theorem code_size (width base : Nat) : (code width base).size = 11 := rfl
@[simp] theorem code_words (width base : Nat) : programWords (code width base) = 44 := rfl

def At (program : Program width 8) (entry base : Nat) : Prop :=
  ∀ phase : Fin 11, program[entry + phase.val]? = some (code width base)[phase.val]

def linkedHeap (state : State width 8) (base : Nat) (label : Fin n)
    (rowAddress previous : Nat) (bound : headAddress base label < state.heap.size) : Array (Word width) :=
  ((state.heap.push (word width rowAddress)).push (word width previous)).set
    (headAddress base label) (word width state.heap.size) (by simp only [Array.size_push]; omega)

def finished (state : State width 8) (entry base bodyCursor rowAddress previous : Nat)
    (label : Fin n) (bound : headAddress base label < state.heap.size) : State width 8 :=
  { state with
    reg := fun register =>
      if register = 0 then word width (bodyCursor + 1)
      else if register = 3 then word width (headAddress base label)
      else if register = 4 then word width previous
      else if register = 7 then word width (state.heap.size + 2)
      else state.reg register
    heap := linkedHeap state base label rowAddress previous bound
    pc := word width (entry + 11)
    halted := false }

@[simp] theorem finished_size (state : State width 8) (entry base bodyCursor rowAddress previous : Nat)
    (label : Fin n) (bound : headAddress base label < state.heap.size) :
    (finished state entry base bodyCursor rowAddress previous label bound).heap.size = state.heap.size + 2 := by
  simp [finished, linkedHeap]

@[simp] theorem finished_live (state : State width 8) (entry base bodyCursor rowAddress previous : Nat)
    (label : Fin n) (bound : headAddress base label < state.heap.size) :
    (finished state entry base bodyCursor rowAddress previous label bound).liveWords = state.liveWords + 2 := by
  simp [State.liveWords, finished, linkedHeap]; omega

private theorem word_value (value : Nat) (fits : value < 2 ^ width) :
    (word width value).val = value := Nat.mod_eq_of_lt fits

private def snapshot (state : State width 8) (pc : Nat) (r0 r3 r4 r7 : Word width)
    (heap : Array (Word width)) : State width 8 :=
  { state with
    pc := word width pc
    halted := false
    heap := heap
    reg := fun register => if register = 0 then r0 else if register = 3 then r3
      else if register = 4 then r4 else if register = 7 then r7 else state.reg register }

/-- Every source/cursor/header fact refers to the actual machine state.
The two allocated words are the exact natural row/link addresses. -/
theorem incidence_execution (program : Program width 8) (entry base bodyCursor rowAddress previous : Nat)
    (state : State width 8) (label : Fin n)
    (present : At program entry base)
    (bodyBound : bodyCursor < state.heap.size)
    (headBound : headAddress base label < state.heap.size)
    (source : state.heap[bodyCursor]'bodyBound = word width label.val)
    (head : state.heap[headAddress base label]'headBound = word width previous)
    (previousBound : previous < state.heap.size) (rowBound : rowAddress < state.heap.size)
    (sourceHeld : state.reg 0 = word width bodyCursor)
    (rowHeld : state.reg 1 = word width rowAddress)
    (pointerHeld : state.reg 7 = word width state.heap.size)
    (one : state.reg 5 = word width 1)
    (position : state.pc = word width entry) (running : state.halted = false)
    (capacity : entry + 11 < 2 ^ width) (room : state.heap.size + 2 < 2 ^ width) :
    Execution program state (finished state entry base bodyCursor rowAddress previous label headBound)
      11 (state.liveWords + 2) := by
  have labelFits : label.val < 2 ^ width := by unfold headAddress at headBound; omega
  have doubleFits : 2 * label.val < 2 ^ width := by unfold headAddress at headBound; omega
  have baseFits : base < 2 ^ width := by unfold headAddress at headBound; omega
  have addressFits : headAddress base label < 2 ^ width := by omega
  have inputFits : bodyCursor < 2 ^ width := by omega
  have pointerFits : state.heap.size < 2 ^ width := by omega
  have pointerOneFits : state.heap.size + 1 < 2 ^ width := by omega
  have oneFits : 1 < 2 ^ width := by omega
  have fetch (phase : Fin 11) : program[entry + phase.val]? = some (code width base)[phase.val] := present phase
  have f0 := fetch ⟨0, by decide⟩
  have f1 := fetch ⟨1, by decide⟩
  have f2 := fetch ⟨2, by decide⟩
  have f3 := fetch ⟨3, by decide⟩
  have f4 := fetch ⟨4, by decide⟩
  have f5 := fetch ⟨5, by decide⟩
  have f6 := fetch ⟨6, by decide⟩
  have f7 := fetch ⟨7, by decide⟩
  have f8 := fetch ⟨8, by decide⟩
  have f9 := fetch ⟨9, by decide⟩
  have f10 := fetch ⟨10, by decide⟩
  have pcFits (phase : Nat) (bound : phase ≤ 11) : entry + phase < 2 ^ width := by omega
  have sourceOneFits : bodyCursor + 1 < 2 ^ width := by omega
  have doubleWord : word width (label.val + label.val) = word width (2 * label.val) := by
    congr 1
    omega
  have addressWord : word width (2 * label.val + base) = word width (headAddress base label) := by
    unfold headAddress
    congr 1
    omega
  let s1 := snapshot state (entry + 1) (word width bodyCursor) (word width label.val) (state.reg 4) (word width state.heap.size) (state.heap)
  let s2 := snapshot state (entry + 2) (word width bodyCursor) (word width (2 * label.val)) (state.reg 4) (word width state.heap.size) (state.heap)
  let s3 := snapshot state (entry + 3) (word width bodyCursor) (word width (2 * label.val)) (word width base) (word width state.heap.size) (state.heap)
  let s4 := snapshot state (entry + 4) (word width bodyCursor) (word width (headAddress base label)) (word width base) (word width state.heap.size) (state.heap)
  let s5 := snapshot state (entry + 5) (word width bodyCursor) (word width (headAddress base label)) (word width previous) (word width state.heap.size) (state.heap)
  let s6 := snapshot state (entry + 6) (word width bodyCursor) (word width (headAddress base label)) (word width previous) (word width state.heap.size) (state.heap.push (word width rowAddress))
  let s7 := snapshot state (entry + 7) (word width bodyCursor) (word width (headAddress base label)) (word width previous) (word width state.heap.size) ((state.heap.push (word width rowAddress)).push (word width previous))
  let s8 := snapshot state (entry + 8) (word width bodyCursor) (word width (headAddress base label)) (word width previous) (word width state.heap.size) (linkedHeap state base label rowAddress previous headBound)
  let s9 := snapshot state (entry + 9) (word width bodyCursor) (word width (headAddress base label)) (word width previous) (word width (state.heap.size + 1)) (linkedHeap state base label rowAddress previous headBound)
  let s10 := snapshot state (entry + 10) (word width bodyCursor) (word width (headAddress base label)) (word width previous) (word width (state.heap.size + 2)) (linkedHeap state base label rowAddress previous headBound)
  let s11 := snapshot state (entry + 11) (word width (bodyCursor + 1)) (word width (headAddress base label)) (word width previous) (word width (state.heap.size + 2)) (linkedHeap state base label rowAddress previous headBound)
  simp [code] at f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10
  have t0 : programStep program state = some s1 := by
    simp [programStep, step, snapshot, State.advance, State.put, s1, f0, sourceHeld, rowHeld, pointerHeld, one, position, running, bodyBound, headBound, source, head, room, word_value (width := width) entry (by omega), word_value (width := width) (entry + 1) (pcFits 1 (by omega)), word_value (width := width) (entry + 2) (pcFits 2 (by omega)), word_value (width := width) (entry + 3) (pcFits 3 (by omega)), word_value (width := width) (entry + 4) (pcFits 4 (by omega)), word_value (width := width) (entry + 5) (pcFits 5 (by omega)), word_value (width := width) (entry + 6) (pcFits 6 (by omega)), word_value (width := width) (entry + 7) (pcFits 7 (by omega)), word_value (width := width) (entry + 8) (pcFits 8 (by omega)), word_value (width := width) (entry + 9) (pcFits 9 (by omega)), word_value (width := width) (entry + 10) (pcFits 10 (by omega)), word_value (width := width) (entry + 11) (pcFits 11 (by omega)), word_value (width := width) label.val labelFits, word_value (width := width) (2 * label.val) doubleFits, word_value (width := width) base baseFits, word_value (width := width) (headAddress base label) addressFits, word_value (width := width) bodyCursor inputFits, word_value (width := width) state.heap.size pointerFits, word_value (width := width) (state.heap.size + 1) pointerOneFits, word_value (width := width) 1 oneFits, linkedHeap, doubleWord, addressWord, Nat.add_assoc]
    all_goals first | omega | rfl | (congr 1 <;> try (ext register; fin_cases register <;> simp [snapshot, State.advance, State.put, sourceHeld, pointerHeld, running]))
  have t1 : programStep program s1 = some s2 := by
    simp [programStep, step, snapshot, State.advance, State.put, s1, s2, f1, sourceHeld, rowHeld, pointerHeld, one, position, running, bodyBound, headBound, source, head, room, word_value (width := width) entry (by omega), word_value (width := width) (entry + 1) (pcFits 1 (by omega)), word_value (width := width) (entry + 2) (pcFits 2 (by omega)), word_value (width := width) (entry + 3) (pcFits 3 (by omega)), word_value (width := width) (entry + 4) (pcFits 4 (by omega)), word_value (width := width) (entry + 5) (pcFits 5 (by omega)), word_value (width := width) (entry + 6) (pcFits 6 (by omega)), word_value (width := width) (entry + 7) (pcFits 7 (by omega)), word_value (width := width) (entry + 8) (pcFits 8 (by omega)), word_value (width := width) (entry + 9) (pcFits 9 (by omega)), word_value (width := width) (entry + 10) (pcFits 10 (by omega)), word_value (width := width) (entry + 11) (pcFits 11 (by omega)), word_value (width := width) label.val labelFits, word_value (width := width) (2 * label.val) doubleFits, word_value (width := width) base baseFits, word_value (width := width) (headAddress base label) addressFits, word_value (width := width) bodyCursor inputFits, word_value (width := width) state.heap.size pointerFits, word_value (width := width) (state.heap.size + 1) pointerOneFits, word_value (width := width) 1 oneFits, linkedHeap, doubleWord, addressWord, Nat.add_assoc]
    all_goals first | omega | rfl | (congr 1 <;> try (ext register; fin_cases register <;> simp [snapshot, State.advance, State.put, sourceHeld, pointerHeld, running]))
  have t2 : programStep program s2 = some s3 := by
    simp [programStep, step, snapshot, State.advance, State.put, s2, s3, f2, sourceHeld, rowHeld, pointerHeld, one, position, running, bodyBound, headBound, source, head, room, word_value (width := width) entry (by omega), word_value (width := width) (entry + 1) (pcFits 1 (by omega)), word_value (width := width) (entry + 2) (pcFits 2 (by omega)), word_value (width := width) (entry + 3) (pcFits 3 (by omega)), word_value (width := width) (entry + 4) (pcFits 4 (by omega)), word_value (width := width) (entry + 5) (pcFits 5 (by omega)), word_value (width := width) (entry + 6) (pcFits 6 (by omega)), word_value (width := width) (entry + 7) (pcFits 7 (by omega)), word_value (width := width) (entry + 8) (pcFits 8 (by omega)), word_value (width := width) (entry + 9) (pcFits 9 (by omega)), word_value (width := width) (entry + 10) (pcFits 10 (by omega)), word_value (width := width) (entry + 11) (pcFits 11 (by omega)), word_value (width := width) label.val labelFits, word_value (width := width) (2 * label.val) doubleFits, word_value (width := width) base baseFits, word_value (width := width) (headAddress base label) addressFits, word_value (width := width) bodyCursor inputFits, word_value (width := width) state.heap.size pointerFits, word_value (width := width) (state.heap.size + 1) pointerOneFits, word_value (width := width) 1 oneFits, linkedHeap, doubleWord, addressWord, Nat.add_assoc]
    all_goals first | omega | rfl | (congr 1 <;> try (ext register; fin_cases register <;> simp [snapshot, State.advance, State.put, sourceHeld, pointerHeld, running]))
  have t3 : programStep program s3 = some s4 := by
    simp [programStep, step, snapshot, State.advance, State.put, s3, s4, f3, sourceHeld, rowHeld, pointerHeld, one, position, running, bodyBound, headBound, source, head, room, word_value (width := width) entry (by omega), word_value (width := width) (entry + 1) (pcFits 1 (by omega)), word_value (width := width) (entry + 2) (pcFits 2 (by omega)), word_value (width := width) (entry + 3) (pcFits 3 (by omega)), word_value (width := width) (entry + 4) (pcFits 4 (by omega)), word_value (width := width) (entry + 5) (pcFits 5 (by omega)), word_value (width := width) (entry + 6) (pcFits 6 (by omega)), word_value (width := width) (entry + 7) (pcFits 7 (by omega)), word_value (width := width) (entry + 8) (pcFits 8 (by omega)), word_value (width := width) (entry + 9) (pcFits 9 (by omega)), word_value (width := width) (entry + 10) (pcFits 10 (by omega)), word_value (width := width) (entry + 11) (pcFits 11 (by omega)), word_value (width := width) label.val labelFits, word_value (width := width) (2 * label.val) doubleFits, word_value (width := width) base baseFits, word_value (width := width) (headAddress base label) addressFits, word_value (width := width) bodyCursor inputFits, word_value (width := width) state.heap.size pointerFits, word_value (width := width) (state.heap.size + 1) pointerOneFits, word_value (width := width) 1 oneFits, linkedHeap, doubleWord, addressWord, Nat.add_assoc]
    all_goals first | omega | rfl | (congr 1 <;> try (ext register; fin_cases register <;> simp [snapshot, State.advance, State.put, sourceHeld, pointerHeld, running]))
  have t4 : programStep program s4 = some s5 := by
    simp [programStep, step, snapshot, State.advance, State.put, s4, s5, f4, sourceHeld, rowHeld, pointerHeld, one, position, running, bodyBound, headBound, source, head, room, word_value (width := width) entry (by omega), word_value (width := width) (entry + 1) (pcFits 1 (by omega)), word_value (width := width) (entry + 2) (pcFits 2 (by omega)), word_value (width := width) (entry + 3) (pcFits 3 (by omega)), word_value (width := width) (entry + 4) (pcFits 4 (by omega)), word_value (width := width) (entry + 5) (pcFits 5 (by omega)), word_value (width := width) (entry + 6) (pcFits 6 (by omega)), word_value (width := width) (entry + 7) (pcFits 7 (by omega)), word_value (width := width) (entry + 8) (pcFits 8 (by omega)), word_value (width := width) (entry + 9) (pcFits 9 (by omega)), word_value (width := width) (entry + 10) (pcFits 10 (by omega)), word_value (width := width) (entry + 11) (pcFits 11 (by omega)), word_value (width := width) label.val labelFits, word_value (width := width) (2 * label.val) doubleFits, word_value (width := width) base baseFits, word_value (width := width) (headAddress base label) addressFits, word_value (width := width) bodyCursor inputFits, word_value (width := width) state.heap.size pointerFits, word_value (width := width) (state.heap.size + 1) pointerOneFits, word_value (width := width) 1 oneFits, linkedHeap, doubleWord, addressWord, Nat.add_assoc]
    all_goals first | omega | rfl | (congr 1 <;> try (ext register; fin_cases register <;> simp [snapshot, State.advance, State.put, sourceHeld, pointerHeld, running]))
  have t5 : programStep program s5 = some s6 := by
    simp [programStep, step, snapshot, State.advance, State.put, s5, s6, f5, sourceHeld, rowHeld, pointerHeld, one, position, running, bodyBound, headBound, source, head, room, word_value (width := width) entry (by omega), word_value (width := width) (entry + 1) (pcFits 1 (by omega)), word_value (width := width) (entry + 2) (pcFits 2 (by omega)), word_value (width := width) (entry + 3) (pcFits 3 (by omega)), word_value (width := width) (entry + 4) (pcFits 4 (by omega)), word_value (width := width) (entry + 5) (pcFits 5 (by omega)), word_value (width := width) (entry + 6) (pcFits 6 (by omega)), word_value (width := width) (entry + 7) (pcFits 7 (by omega)), word_value (width := width) (entry + 8) (pcFits 8 (by omega)), word_value (width := width) (entry + 9) (pcFits 9 (by omega)), word_value (width := width) (entry + 10) (pcFits 10 (by omega)), word_value (width := width) (entry + 11) (pcFits 11 (by omega)), word_value (width := width) label.val labelFits, word_value (width := width) (2 * label.val) doubleFits, word_value (width := width) base baseFits, word_value (width := width) (headAddress base label) addressFits, word_value (width := width) bodyCursor inputFits, word_value (width := width) state.heap.size pointerFits, word_value (width := width) (state.heap.size + 1) pointerOneFits, word_value (width := width) 1 oneFits, linkedHeap, doubleWord, addressWord, Nat.add_assoc]
    all_goals first | omega | rfl | (congr 1 <;> try (ext register; fin_cases register <;> simp [snapshot, State.advance, State.put, sourceHeld, pointerHeld, running]))
  have t6 : programStep program s6 = some s7 := by
    simp [programStep, step, snapshot, State.advance, State.put, s6, s7, f6, sourceHeld, rowHeld, pointerHeld, one, position, running, bodyBound, headBound, source, head, room, word_value (width := width) entry (by omega), word_value (width := width) (entry + 1) (pcFits 1 (by omega)), word_value (width := width) (entry + 2) (pcFits 2 (by omega)), word_value (width := width) (entry + 3) (pcFits 3 (by omega)), word_value (width := width) (entry + 4) (pcFits 4 (by omega)), word_value (width := width) (entry + 5) (pcFits 5 (by omega)), word_value (width := width) (entry + 6) (pcFits 6 (by omega)), word_value (width := width) (entry + 7) (pcFits 7 (by omega)), word_value (width := width) (entry + 8) (pcFits 8 (by omega)), word_value (width := width) (entry + 9) (pcFits 9 (by omega)), word_value (width := width) (entry + 10) (pcFits 10 (by omega)), word_value (width := width) (entry + 11) (pcFits 11 (by omega)), word_value (width := width) label.val labelFits, word_value (width := width) (2 * label.val) doubleFits, word_value (width := width) base baseFits, word_value (width := width) (headAddress base label) addressFits, word_value (width := width) bodyCursor inputFits, word_value (width := width) state.heap.size pointerFits, word_value (width := width) (state.heap.size + 1) pointerOneFits, word_value (width := width) 1 oneFits, linkedHeap, doubleWord, addressWord, Nat.add_assoc]
    all_goals first | omega | rfl | (congr 1 <;> try (ext register; fin_cases register <;> simp [snapshot, State.advance, State.put, sourceHeld, pointerHeld, running]))
  have t7 : programStep program s7 = some s8 := by
    simp [programStep, step, snapshot, State.advance, State.put, s7, s8, f7, sourceHeld, rowHeld, pointerHeld, one, position, running, bodyBound, headBound, source, head, room, word_value (width := width) entry (by omega), word_value (width := width) (entry + 1) (pcFits 1 (by omega)), word_value (width := width) (entry + 2) (pcFits 2 (by omega)), word_value (width := width) (entry + 3) (pcFits 3 (by omega)), word_value (width := width) (entry + 4) (pcFits 4 (by omega)), word_value (width := width) (entry + 5) (pcFits 5 (by omega)), word_value (width := width) (entry + 6) (pcFits 6 (by omega)), word_value (width := width) (entry + 7) (pcFits 7 (by omega)), word_value (width := width) (entry + 8) (pcFits 8 (by omega)), word_value (width := width) (entry + 9) (pcFits 9 (by omega)), word_value (width := width) (entry + 10) (pcFits 10 (by omega)), word_value (width := width) (entry + 11) (pcFits 11 (by omega)), word_value (width := width) label.val labelFits, word_value (width := width) (2 * label.val) doubleFits, word_value (width := width) base baseFits, word_value (width := width) (headAddress base label) addressFits, word_value (width := width) bodyCursor inputFits, word_value (width := width) state.heap.size pointerFits, word_value (width := width) (state.heap.size + 1) pointerOneFits, word_value (width := width) 1 oneFits, linkedHeap, doubleWord, addressWord, Nat.add_assoc]
    all_goals first | omega | rfl | (congr 1 <;> try (ext register; fin_cases register <;> simp [snapshot, State.advance, State.put, sourceHeld, pointerHeld, running]))
  have t8 : programStep program s8 = some s9 := by
    simp [programStep, step, snapshot, State.advance, State.put, s8, s9, f8, sourceHeld, rowHeld, pointerHeld, one, position, running, bodyBound, headBound, source, head, room, word_value (width := width) entry (by omega), word_value (width := width) (entry + 1) (pcFits 1 (by omega)), word_value (width := width) (entry + 2) (pcFits 2 (by omega)), word_value (width := width) (entry + 3) (pcFits 3 (by omega)), word_value (width := width) (entry + 4) (pcFits 4 (by omega)), word_value (width := width) (entry + 5) (pcFits 5 (by omega)), word_value (width := width) (entry + 6) (pcFits 6 (by omega)), word_value (width := width) (entry + 7) (pcFits 7 (by omega)), word_value (width := width) (entry + 8) (pcFits 8 (by omega)), word_value (width := width) (entry + 9) (pcFits 9 (by omega)), word_value (width := width) (entry + 10) (pcFits 10 (by omega)), word_value (width := width) (entry + 11) (pcFits 11 (by omega)), word_value (width := width) label.val labelFits, word_value (width := width) (2 * label.val) doubleFits, word_value (width := width) base baseFits, word_value (width := width) (headAddress base label) addressFits, word_value (width := width) bodyCursor inputFits, word_value (width := width) state.heap.size pointerFits, word_value (width := width) (state.heap.size + 1) pointerOneFits, word_value (width := width) 1 oneFits, linkedHeap, doubleWord, addressWord, Nat.add_assoc]
    all_goals first | omega | rfl | (congr 1 <;> try (ext register; fin_cases register <;> simp [snapshot, State.advance, State.put, sourceHeld, pointerHeld, running]))
  have t9 : programStep program s9 = some s10 := by
    simp [programStep, step, snapshot, State.advance, State.put, s9, s10, f9, sourceHeld, rowHeld, pointerHeld, one, position, running, bodyBound, headBound, source, head, room, word_value (width := width) entry (by omega), word_value (width := width) (entry + 1) (pcFits 1 (by omega)), word_value (width := width) (entry + 2) (pcFits 2 (by omega)), word_value (width := width) (entry + 3) (pcFits 3 (by omega)), word_value (width := width) (entry + 4) (pcFits 4 (by omega)), word_value (width := width) (entry + 5) (pcFits 5 (by omega)), word_value (width := width) (entry + 6) (pcFits 6 (by omega)), word_value (width := width) (entry + 7) (pcFits 7 (by omega)), word_value (width := width) (entry + 8) (pcFits 8 (by omega)), word_value (width := width) (entry + 9) (pcFits 9 (by omega)), word_value (width := width) (entry + 10) (pcFits 10 (by omega)), word_value (width := width) (entry + 11) (pcFits 11 (by omega)), word_value (width := width) label.val labelFits, word_value (width := width) (2 * label.val) doubleFits, word_value (width := width) base baseFits, word_value (width := width) (headAddress base label) addressFits, word_value (width := width) bodyCursor inputFits, word_value (width := width) state.heap.size pointerFits, word_value (width := width) (state.heap.size + 1) pointerOneFits, word_value (width := width) 1 oneFits, linkedHeap, doubleWord, addressWord, Nat.add_assoc]
    all_goals first | omega | rfl | (congr 1 <;> try (ext register; fin_cases register <;> simp [snapshot, State.advance, State.put, sourceHeld, pointerHeld, running]))
  have t10 : programStep program s10 = some s11 := by
    simp [programStep, step, snapshot, State.advance, State.put, s10, s11, f10, sourceHeld, rowHeld, pointerHeld, one, position, running, bodyBound, headBound, source, head, room, word_value (width := width) entry (by omega), word_value (width := width) (entry + 1) (pcFits 1 (by omega)), word_value (width := width) (entry + 2) (pcFits 2 (by omega)), word_value (width := width) (entry + 3) (pcFits 3 (by omega)), word_value (width := width) (entry + 4) (pcFits 4 (by omega)), word_value (width := width) (entry + 5) (pcFits 5 (by omega)), word_value (width := width) (entry + 6) (pcFits 6 (by omega)), word_value (width := width) (entry + 7) (pcFits 7 (by omega)), word_value (width := width) (entry + 8) (pcFits 8 (by omega)), word_value (width := width) (entry + 9) (pcFits 9 (by omega)), word_value (width := width) (entry + 10) (pcFits 10 (by omega)), word_value (width := width) (entry + 11) (pcFits 11 (by omega)), word_value (width := width) label.val labelFits, word_value (width := width) (2 * label.val) doubleFits, word_value (width := width) base baseFits, word_value (width := width) (headAddress base label) addressFits, word_value (width := width) bodyCursor inputFits, word_value (width := width) state.heap.size pointerFits, word_value (width := width) (state.heap.size + 1) pointerOneFits, word_value (width := width) 1 oneFits, linkedHeap, doubleWord, addressWord, Nat.add_assoc]
    all_goals first | omega | rfl | (congr 1 <;> try (ext register; fin_cases register <;> simp [snapshot, State.advance, State.put, sourceHeld, pointerHeld, running]))
  have finalState : s11 = finished state entry base bodyCursor rowAddress previous label headBound := by
    rfl
  have live1 : s1.liveWords = state.liveWords := by
    rfl
  have live2 : s2.liveWords = state.liveWords := by
    rfl
  have live3 : s3.liveWords = state.liveWords := by
    rfl
  have live4 : s4.liveWords = state.liveWords := by
    rfl
  have live5 : s5.liveWords = state.liveWords := by
    rfl
  have live6 : s6.liveWords = state.liveWords + 1 := by
    simp [s6, snapshot, State.liveWords, linkedHeap]
    all_goals omega
  have live7 : s7.liveWords = state.liveWords + 2 := by
    simp [s7, snapshot, State.liveWords, linkedHeap]
    all_goals omega
  have live8 : s8.liveWords = state.liveWords + 2 := by
    simp [s8, snapshot, State.liveWords, linkedHeap]
    all_goals omega
  have live9 : s9.liveWords = state.liveWords + 2 := by
    simp [s9, snapshot, State.liveWords, linkedHeap]
    all_goals omega
  have live10 : s10.liveWords = state.liveWords + 2 := by
    simp [s10, snapshot, State.liveWords, linkedHeap]
    all_goals omega
  have live11 : s11.liveWords = state.liveWords + 2 := by
    simp [s11, snapshot, State.liveWords, linkedHeap]
    all_goals omega
  have trace := Execution.cons t0 (Execution.cons t1 (Execution.cons t2 (Execution.cons t3 (Execution.cons t4 (Execution.cons t5 (Execution.cons t6 (Execution.cons t7 (Execution.cons t8 (Execution.cons t9 (Execution.cons t10 (Execution.refl s11)))))))))))
  rw [finalState] at trace
  simpa only [live1, live2, live3, live4, live5, live6, live7, live8, live9, live10, finished_live, Nat.reduceAdd, Nat.max_self, Nat.max_eq_right (by omega : state.liveWords ≤ state.liveWords + 2), Nat.max_eq_right (by omega : state.liveWords + 1 ≤ state.liveWords + 2)] using trace

/-- Actual links decode exactly and their allocated address cannot alias nil. -/
theorem incidence_node (state : State width 8) (base rowAddress previous : Nat) (label : Fin n)
    (headBound : headAddress base label < state.heap.size)
    (rowBound : rowAddress < state.heap.size) (previousBound : previous < state.heap.size)
    (room : state.heap.size + 2 < 2 ^ width) :
    NodeStored rowAddress previous state.heap.size (linkedHeap state base label rowAddress previous headBound) ∧
      0 < state.heap.size := by
  have first : state.heap.size < (state.heap.push (word width rowAddress)).size := by simp
  have second : state.heap.size + 1 < ((state.heap.push (word width rowAddress)).push (word width previous)).size := by simp
  refine ⟨⟨by simp [linkedHeap], by omega, by omega, by omega, ?_, ?_⟩, by omega⟩
  · unfold linkedHeap
    rw [Array.getElem_set_ne (by simp only [Array.size_push]; omega) (by simp only [Array.size_push]; omega) (by omega)]
    rw [Array.getElem_push_lt first]
    exact Array.getElem_push_eq
  · unfold linkedHeap
    rw [Array.getElem_set_ne (by simp only [Array.size_push]; omega) (by simp only [Array.size_push]; omega) (by omega)]
    simpa only [Array.size_push] using (Array.getElem_push_eq (xs := state.heap.push (word width rowAddress)) (x := word width previous))

/-- Only one old bucket head changes; allocated nodes preserve every other old word. -/
theorem incidence_old_frame (state : State width 8) (base rowAddress previous : Nat) (label : Fin n)
    (headBound : headAddress base label < state.heap.size) (index : Nat)
    (inside : index < state.heap.size) (different : headAddress base label ≠ index) :
    (linkedHeap state base label rowAddress previous headBound)[index]? = state.heap[index]? := by
  rw [Array.getElem?_eq_getElem (by simp [linkedHeap]; omega), Array.getElem?_eq_getElem inside]
  apply congrArg some
  unfold linkedHeap
  exact (Array.getElem_set_ne (by simp only [Array.size_push]; omega)
    (by simp only [Array.size_push]; omega) different).trans
    ((Array.getElem_push_lt (by simp only [Array.size_push]; omega)).trans (Array.getElem_push_lt inside))

end Controller.Horn.IndexBuild
