module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Horn.SuffixDispatch

@[expose] public section

/-!
# Physical source literal pairs for the normalizer

Each source occurrence occupies a label word followed by a polarity word. The
reader loads an actual cursor header, moves backwards by two cells, reads both
words and writes the new cursor before dispatching on the observed polarity.
Repeated source occurrences remain separate cells and separate iterations.
-/
namespace Controller.Horn.SourceScan

open Controller.Cost Controller.Horn.Worklist.IndexedNormalize

structure PairStored (literal : CNF.Literal (Fin n)) (pointer : Nat)
    (heap : Array (Word width)) : Prop where
  fits : pointer + 2 ≤ heap.size
  label : heap[pointer]'(by omega) = word width literal.1.val
  polarity : heap[pointer + 1]'(by omega) = MarkStorage.encode width literal.2

/-- A store outside this two-word occurrence preserves both source values. -/
theorem PairStored.after_store {literal : CNF.Literal (Fin n)} {pointer : Nat}
    {heap : Array (Word width)} (stored : PairStored literal pointer heap)
    (index : Nat) (bound : index < heap.size) (value : Word width)
    (outside : index < pointer ∨ pointer + 2 ≤ index) :
    PairStored literal pointer (heap.set index value bound) := by
  have firstBound : pointer < heap.size := by have := stored.fits; omega
  have secondBound : pointer + 1 < heap.size := by have := stored.fits; omega
  have firstDifferent : index ≠ pointer := by omega
  have secondDifferent : index ≠ pointer + 1 := by omega
  refine ⟨by simpa using stored.fits, ?_, ?_⟩
  · exact (Array.getElem_set_ne bound firstBound firstDifferent).trans stored.label
  · exact (Array.getElem_set_ne bound secondBound secondDifferent).trans stored.polarity

structure CursorStored (pointer header : Nat) (heap : Array (Word width)) : Prop where
  bound : header < heap.size
  value : heap[header]'bound = word width pointer

def pairCode (width entry header negativeTarget : Nat) : Program width 8 :=
  #[.constant 0 (word width header), .load 0 0, .add 0 0 6, .load 7 0,
    .add 0 0 6, .load 3 0, .copy 4 0, .constant 0 (word width header),
    .store 0 4, .branchZero 7 (word width negativeTarget)]

@[simp] theorem pairCode_size (width entry header negativeTarget : Nat) :
    (pairCode width entry header negativeTarget).size = 10 := rfl

def PairAt (destination : Program width 8) (entry header negativeTarget : Nat) : Prop :=
  ∀ phase : Fin 10, destination[entry + phase.val]? =
    some (pairCode width entry header negativeTarget)[phase.val]

private theorem word_val (value : Nat) (fits : value < 2 ^ width) :
    (word width value).val = value := Nat.mod_eq_of_lt fits

private theorem advance_position (state : State width 8) (position : Nat)
    (atPosition : state.pc = word width position) (fits : position < 2 ^ width) :
    state.advance.pc = word width (position + 1) := by
  simp only [State.advance, atPosition, word_val (width := width) position fits]

private theorem fetched (destination : Program width 8) (entry header negativeTarget : Nat)
    (present : PairAt destination entry header negativeTarget) (state : State width 8)
    (phase : Fin 10) (position : state.pc = word width (entry + phase.val))
    (capacity : entry + 10 < 2 ^ width) :
    destination[state.pc.val]? = some (pairCode width entry header negativeTarget)[phase.val] := by
  rw [position, word_val (width := width) (entry + phase.val) (by have := phase.isLt; omega)]
  exact present phase

private theorem constant_step (destination : Program width 8) (state : State width 8)
    (register : Fin 8) (value : Word width) (running : state.halted = false)
    (read : destination[state.pc.val]? = some (.constant register value)) :
    programStep destination state = some (state.advance.put register value) := by
  unfold programStep
  rw [read]
  simp [step, running]

private theorem load_step (destination : Program width 8) (state : State width 8)
    (destinationRegister addressRegister : Fin 8) (index : Nat)
    (bound : index < state.heap.size) (points : (state.reg addressRegister).val = index)
    (value : Word width) (held : state.heap[index]'bound = value) (running : state.halted = false)
    (read : destination[state.pc.val]? = some (.load destinationRegister addressRegister)) :
    programStep destination state = some (state.advance.put destinationRegister value) := by
  unfold programStep
  rw [read]
  change step (.load destinationRegister addressRegister) state = _
  simp only [step, running, Bool.false_eq_true, ite_false, points, bound, dite_eq_left, held]

private theorem decrement_step (destination : Program width 8) (state : State width 8)
    (remaining : Nat) (held : state.reg 0 = word width (remaining + 1))
    (decrement : state.reg 6 = word width (2 ^ width - 1))
    (fits : remaining + 1 < 2 ^ width) (running : state.halted = false)
    (read : destination[state.pc.val]? = some (.add 0 0 6)) :
    programStep destination state = some (state.advance.put 0 (word width remaining)) := by
  unfold programStep
  rw [read]
  change step (.add 0 0 6) state = _
  simp only [step, running, Bool.false_eq_true, ite_false, held, decrement]
  rw [Initialize.word_decrement remaining fits]

/-- Exact state produced by the nine straight-line instructions; its cursor
word is derived from the source header and its label/sign from source cells. -/
def pairPrepared (state : State width 8) (header pointer : Nat)
    (literal : CNF.Literal (Fin n)) (bound : header < state.heap.size) : State width 8 :=
  let s1 := state.advance.put 0 (word width header)
  let s2 := s1.advance.put 0 (word width (pointer + 2))
  let s3 := s2.advance.put 0 (word width (pointer + 1))
  let s4 := s3.advance.put 7 (MarkStorage.encode width literal.2)
  let s5 := s4.advance.put 0 (word width pointer)
  let s6 := s5.advance.put 3 (word width literal.1.val)
  let s7 := s6.advance.put 4 (word width pointer)
  let s8 := s7.advance.put 0 (word width header)
  { s8.advance with heap := state.heap.set header (word width pointer) bound }

def pairFinished (state : State width 8) (entry header pointer negativeTarget : Nat)
    (literal : CNF.Literal (Fin n)) (bound : header < state.heap.size) : State width 8 :=
  let prepared := pairPrepared state header pointer literal bound
  if literal.2 then prepared.advance else { prepared.advance with pc := word width negativeTarget }

theorem pairPrepared_frame (state : State width 8) (header pointer : Nat)
    (literal : CNF.Literal (Fin n)) (bound : header < state.heap.size) :
    (∀ register : Fin 8, register ≠ 0 → register ≠ 3 → register ≠ 4 → register ≠ 7 →
      (pairPrepared state header pointer literal bound).reg register = state.reg register) ∧
    (pairPrepared state header pointer literal bound).stack = state.stack ∧
    (pairPrepared state header pointer literal bound).output = state.output ∧
    (pairPrepared state header pointer literal bound).heap.size = state.heap.size := by
  refine ⟨?_, rfl, rfl, by simp [pairPrepared]⟩
  intro register address label cursor sign
  simp [pairPrepared, State.advance, State.put, address, label, cursor, sign]

theorem pairPrepared_label (state : State width 8) (header pointer : Nat)
    (literal : CNF.Literal (Fin n)) (bound : header < state.heap.size) :
    (pairPrepared state header pointer literal bound).reg 3 = word width literal.1.val := by
  simp [pairPrepared, State.advance, State.put]

theorem pairPrepared_polarity (state : State width 8) (header pointer : Nat)
    (literal : CNF.Literal (Fin n)) (bound : header < state.heap.size) :
    (pairPrepared state header pointer literal bound).reg 7 = MarkStorage.encode width literal.2 := by
  simp [pairPrepared, State.advance, State.put]

theorem pairPrepared_cursor (state : State width 8) (header pointer : Nat)
    (literal : CNF.Literal (Fin n)) (bound : header < state.heap.size) :
    CursorStored pointer header (pairPrepared state header pointer literal bound).heap := by
  refine ⟨by simpa [pairPrepared] using bound, ?_⟩
  simp [pairPrepared]


/-- Ten fetched instructions read both source words, decrement the actual
header cursor and select polarity. Semantic labels appear only through the
proved contents of the physically read source cells. -/
theorem pair_execution (destination : Program width 8) (entry header pointer negativeTarget : Nat)
    (literal : CNF.Literal (Fin n)) (present : PairAt destination entry header negativeTarget)
    (state : State width 8) (cursor : CursorStored (pointer + 2) header state.heap)
    (pair : PairStored literal pointer state.heap) (position : state.pc = word width entry)
    (decrement : state.reg 6 = word width (2 ^ width - 1)) (running : state.halted = false)
    (capacity : entry + 10 < 2 ^ width) (heapFits : state.heap.size < 2 ^ width) :
    Execution destination state (pairFinished state entry header pointer negativeTarget literal cursor.bound)
      10 state.liveWords := by
  have headerFits : header < 2 ^ width := cursor.bound.trans heapFits
  have pointerFits : pointer < 2 ^ width := by have := pair.fits; omega
  have signFits : pointer + 1 < 2 ^ width := by have := pair.fits; omega
  have cursorFits : pointer + 2 < 2 ^ width := by have := pair.fits; omega
  let s1 := state.advance.put 0 (word width header)
  let s2 := s1.advance.put 0 (word width (pointer + 2))
  let s3 := s2.advance.put 0 (word width (pointer + 1))
  let s4 := s3.advance.put 7 (MarkStorage.encode width literal.2)
  let s5 := s4.advance.put 0 (word width pointer)
  let s6 := s5.advance.put 3 (word width literal.1.val)
  let s7 := s6.advance.put 4 (word width pointer)
  let s8 := s7.advance.put 0 (word width header)
  let s9 : State width 8 := { s8.advance with heap := state.heap.set header (word width pointer) cursor.bound }
  have p1 : s1.pc = word width (entry + 1) := by
    simpa [s1, State.put, Nat.add_assoc] using advance_position state (entry + 0) (by simpa using position) (by omega)
  have p2 : s2.pc = word width (entry + 2) := by
    simpa [s2, State.put, Nat.add_assoc] using advance_position s1 (entry + 1) p1 (by omega)
  have p3 : s3.pc = word width (entry + 3) := by
    simpa [s3, State.put, Nat.add_assoc] using advance_position s2 (entry + 2) p2 (by omega)
  have p4 : s4.pc = word width (entry + 4) := by
    simpa [s4, State.put, Nat.add_assoc] using advance_position s3 (entry + 3) p3 (by omega)
  have p5 : s5.pc = word width (entry + 5) := by
    simpa [s5, State.put, Nat.add_assoc] using advance_position s4 (entry + 4) p4 (by omega)
  have p6 : s6.pc = word width (entry + 6) := by
    simpa [s6, State.put, Nat.add_assoc] using advance_position s5 (entry + 5) p5 (by omega)
  have p7 : s7.pc = word width (entry + 7) := by
    simpa [s7, State.put, Nat.add_assoc] using advance_position s6 (entry + 6) p6 (by omega)
  have p8 : s8.pc = word width (entry + 8) := by
    simpa [s8, State.put, Nat.add_assoc] using advance_position s7 (entry + 7) p7 (by omega)
  have p9 : s9.pc = word width (entry + 9) := by
    simpa [s9, State.put, Nat.add_assoc] using advance_position s8 (entry + 8) p8 (by omega)
  have t1 : programStep destination state = some s1 :=
    constant_step destination state 0 (word width header) running
      (by simpa [pairCode] using fetched destination entry header negativeTarget present state ⟨0, by decide⟩ (by simpa using position) capacity)
  have t2 : programStep destination s1 = some s2 := by
    apply load_step destination s1 0 0 header cursor.bound
      (by simp only [s1, State.put, ite_true]; exact word_val (width := width) header headerFits)
      (word width (pointer + 2)) cursor.value running
    simpa [pairCode] using fetched destination entry header negativeTarget present s1 ⟨1, by decide⟩ p1 capacity
  have t3 : programStep destination s2 = some s3 :=
    decrement_step destination s2 (pointer + 1) rfl
      (by simpa [s2, s1, State.put, State.advance] using decrement) cursorFits running
      (by simpa [pairCode] using fetched destination entry header negativeTarget present s2 ⟨2, by decide⟩ p2 capacity)
  have t4 : programStep destination s3 = some s4 := by
    apply load_step destination s3 7 0 (pointer + 1) (by change pointer + 1 < state.heap.size; have := pair.fits; omega)
      (by simp only [s3, State.put, ite_true]; exact word_val (width := width) _ signFits)
      (MarkStorage.encode width literal.2) pair.polarity running
    simpa [pairCode] using fetched destination entry header negativeTarget present s3 ⟨3, by decide⟩ p3 capacity
  have t5 : programStep destination s4 = some s5 :=
    decrement_step destination s4 pointer (by simp [s4, s3, State.put, State.advance])
      (by simpa [s4, s3, s2, s1, State.put, State.advance] using decrement) signFits running
      (by simpa [pairCode] using fetched destination entry header negativeTarget present s4 ⟨4, by decide⟩ p4 capacity)
  have t6 : programStep destination s5 = some s6 := by
    apply load_step destination s5 3 0 pointer (by change pointer < state.heap.size; have := pair.fits; omega)
      (by simp only [s5, State.put, ite_true]; exact word_val (width := width) _ pointerFits)
      (word width literal.1.val) pair.label running
    simpa [pairCode] using fetched destination entry header negativeTarget present s5 ⟨5, by decide⟩ p5 capacity
  have t7 : programStep destination s6 = some s7 := by
    have instruction : destination[s6.pc.val]? = some (.copy 4 0) := by
      simpa [pairCode] using fetched destination entry header negativeTarget present s6 ⟨6, by decide⟩ p6 capacity
    unfold programStep
    rw [instruction]
    change step (.copy 4 0) s6 = _
    simp only [step, show s6.halted = false from running, Bool.false_eq_true, ite_false]
    simp [s7, s6, s5, State.put, State.advance]
  have t8 : programStep destination s7 = some s8 :=
    constant_step destination s7 0 (word width header) running
      (by simpa [pairCode] using fetched destination entry header negativeTarget present s7 ⟨7, by decide⟩ p7 capacity)
  have t9 : programStep destination s8 = some s9 := by
    have instruction : destination[s8.pc.val]? = some (.store 0 4) := by
      simpa [pairCode] using fetched destination entry header negativeTarget present s8 ⟨8, by decide⟩ p8 capacity
    unfold programStep
    rw [instruction]
    change step (.store 0 4) s8 = _
    have points : (s8.reg 0).val = header := by
      simp only [s8, State.put, ite_true]
      exact word_val (width := width) header headerFits
    have value : s8.reg 4 = word width pointer := by simp [s8, s7, State.put, State.advance]
    have valid : header < s8.heap.size := cursor.bound
    simp only [step, show s8.halted = false from running, Bool.false_eq_true, ite_false, points, valid, dite_eq_left, value]
    rfl
  have t10 : programStep destination s9 = some (pairFinished state entry header pointer negativeTarget literal cursor.bound) := by
    have instruction : destination[s9.pc.val]? = some (.branchZero 7 (word width negativeTarget)) := by
      simpa [pairCode] using fetched destination entry header negativeTarget present s9 ⟨9, by decide⟩ p9 capacity
    unfold programStep
    rw [instruction]
    change step (.branchZero 7 (word width negativeTarget)) s9 = _
    have held : s9.reg 7 = MarkStorage.encode width literal.2 := by
      simp [s9, s8, s7, s6, s5, s4, State.put, State.advance]
    have oneFits : 1 < 2 ^ width := by omega
    simp only [step, show s9.halted = false from running, Bool.false_eq_true, ite_false, held]
    cases sign : literal.2 <;>
      simp [sign, MarkStorage.encode, word, Nat.mod_eq_of_lt oneFits,
        pairFinished, pairPrepared, s9, s8, s7, s6, s5, s4, s3, s2, s1, running, State.advance, State.put]
  have trace := Execution.cons t1 (Execution.cons t2 (Execution.cons t3 (Execution.cons t4
    (Execution.cons t5 (Execution.cons t6 (Execution.cons t7 (Execution.cons t8
      (Execution.cons t9 (Execution.cons t10 (Execution.refl
        (pairFinished state entry header pointer negativeTarget literal cursor.bound)))))))))))
  cases sign : literal.2 <;>
    simpa [pairFinished, pairPrepared, sign, s9, s8, s7, s6, s5, s4, s3, s2, s1,
      State.advance, State.put, State.liveWords] using trace

theorem pairFinished_frame (state : State width 8) (entry header pointer negativeTarget : Nat)
    (literal : CNF.Literal (Fin n)) (bound : header < state.heap.size) :
    (∀ register : Fin 8, register ≠ 0 → register ≠ 3 → register ≠ 4 → register ≠ 7 →
      (pairFinished state entry header pointer negativeTarget literal bound).reg register = state.reg register) ∧
    (pairFinished state entry header pointer negativeTarget literal bound).stack = state.stack ∧
    (pairFinished state entry header pointer negativeTarget literal bound).output = state.output ∧
    (pairFinished state entry header pointer negativeTarget literal bound).halted = state.halted ∧
    (pairFinished state entry header pointer negativeTarget literal bound).heap =
      state.heap.set header (word width pointer) bound := by
  cases sign : literal.2 <;>
    simp only [pairFinished, sign, Bool.false_eq_true, ite_false, ite_true]
  all_goals
    refine ⟨?_, rfl, rfl, rfl, rfl⟩
    intro register address label cursor polarity
    exact (pairPrepared_frame state header pointer literal bound).1 register address label cursor polarity

theorem pairFinished_label (state : State width 8) (entry header pointer negativeTarget : Nat)
    (literal : CNF.Literal (Fin n)) (bound : header < state.heap.size) :
    (pairFinished state entry header pointer negativeTarget literal bound).reg 3 = word width literal.1.val := by
  cases sign : literal.2 <;>
    simpa [pairFinished, sign, State.advance] using pairPrepared_label state header pointer literal bound

theorem pairFinished_position (state : State width 8) (entry header pointer negativeTarget : Nat)
    (literal : CNF.Literal (Fin n)) (bound : header < state.heap.size)
    (position : state.pc = word width entry) (capacity : entry + 10 < 2 ^ width) :
    (pairFinished state entry header pointer negativeTarget literal bound).pc =
      word width (if literal.2 then entry + 10 else negativeTarget) := by
  cases sign : literal.2
  · simp [pairFinished, sign]
  · simp only [pairFinished, pairPrepared, sign, Bool.true_eq_false, ite_true, State.advance, State.put,
      position, Nat.add_assoc, Nat.reduceAdd,
      word_val (width := width) entry (by omega),
      word_val (width := width) (entry + 1) (by omega),
      word_val (width := width) (entry + 2) (by omega),
      word_val (width := width) (entry + 3) (by omega),
      word_val (width := width) (entry + 4) (by omega),
      word_val (width := width) (entry + 5) (by omega),
      word_val (width := width) (entry + 6) (by omega),
      word_val (width := width) (entry + 7) (by omega),
      word_val (width := width) (entry + 8) (by omega),
      word_val (width := width) (entry + 9) (by omega)]

end Controller.Horn.SourceScan
