module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Horn.SourceScan
public import Mathlib.Tactic.NormNum

public import Mathlib.Tactic.FinCases

@[expose] public section

/-!
# Stored source rows and the backwards normalizer loop invariant

Source literals occupy two words each, in their original order. The actual
cursor and start pointers occupy input headers. The semantic suffix index is a
proof invariant; the emitted loop tests two physically stored pointer words.
-/
namespace Controller.Horn.RowScan

open Controller.Cost Controller.Horn.Worklist.IndexedNormalize
open Controller.Horn.SourceScan Controller.Horn.LiteralDispatch
open Controller.Horn.JoinedLiteral Controller.Horn.NormalizeProgram

/-- Every occurrence has its own pair, including duplicate literals. -/
structure SourceStored (clause : CNF.Clause (Fin n)) (start : Nat)
    (heap : Array (Word width)) : Prop where
  fits : start + 2 * clause.length ≤ heap.size
  entry : ∀ index : Fin clause.length,
    PairStored clause[index.val] (start + 2 * index.val) heap

/-- Scratch stores outside the source interval retain every original pair. -/
theorem SourceStored.after_store {clause : CNF.Clause (Fin n)} {start : Nat}
    {heap : Array (Word width)} (stored : SourceStored clause start heap)
    (index : Nat) (bound : index < heap.size) (value : Word width)
    (outside : index < start ∨ start + 2 * clause.length ≤ index) :
    SourceStored clause start (heap.set index value bound) := by
  refine ⟨by simpa using stored.fits, ?_⟩
  intro position
  apply PairStored.after_store (stored.entry position) index bound value
  have := position.isLt
  omega

/-- Headers contain pointers, never a semantic clause length. -/
structure RowInput (clause : CNF.Clause (Fin n)) (start cursorHeader startHeader : Nat)
    (heap : Array (Word width)) : Prop where
  source : SourceStored clause start heap
  cursor : CursorStored (start + 2 * clause.length) cursorHeader heap
  first : CursorStored start startHeader heap
  separateHeaders : cursorHeader ≠ startHeader
  cursorOutside : cursorHeader < start ∨ start + 2 * clause.length ≤ cursorHeader
  startOutside : startHeader < start ∨ start + 2 * clause.length ≤ startHeader

/-- Input cursor writes before the scratch region preserve the complete row. -/
theorem rowStored_after_input_store {row : Row n} {base positiveCursor negativeCursor touchedCursor : Nat}
    {heap : Array (Word width)}
    (stored : RowStored row base positiveCursor negativeCursor touchedCursor heap)
    (index : Nat) (bound : index < heap.size) (value : Word width) (before : index < base) :
    RowStored row base positiveCursor negativeCursor touchedCursor (heap.set index value bound) := by
  refine ⟨marks_after_store stored.marks index bound value (Or.inl before),
    header_after_store stored.positive index bound value (Or.inl (by omega)) (by omega),
    header_after_store stored.negative index bound value (Or.inl (by omega)) (by omega),
    header_after_store stored.touched index bound value (Or.inl (by omega)) (by omega),
    by simpa using stored.flagBound, ?_⟩
  exact (Array.getElem_set_ne bound stored.flagBound (by omega)).trans stored.flag

/-- At index k the machine has processed exactly the suffix starting at k.
The row scratch and original source cells are simultaneously represented. -/
structure Invariant (clause : CNF.Clause (Fin n)) (row : Row n)
    (start cursorHeader startHeader base positiveCursor negativeCursor touchedCursor k : Nat)
    (state : State width 8) : Prop where
  indexBound : k ≤ clause.length
  source : SourceStored clause start state.heap
  cursor : CursorStored (start + 2 * k) cursorHeader state.heap
  first : CursorStored start startHeader state.heap
  rowStored : RowStored row base positiveCursor negativeCursor touchedCursor state.heap
  correct : row.Correct (clause.drop k)
  zero : state.reg 2 = word width 0
  trueHeld : state.reg 5 = MarkStorage.encode width true
  decrement : state.reg 6 = word width (2 ^ width - 1)
  running : state.halted = false

/-- Both pointer words are physically loaded before the termination test. -/
def testCode (width cursorHeader startHeader exit : Nat) : Program width 8 :=
  #[.constant 0 (word width cursorHeader), .load 0 0,
    .constant 4 (word width startHeader), .load 4 4,
    .xor 1 0 4, .branchZero 1 (word width exit)]

@[simp] theorem testCode_size (width cursorHeader startHeader exit : Nat) :
    (testCode width cursorHeader startHeader exit).size = 6 := rfl

/-- Mark addresses are computed from the source label held in register three.
The static polarity only determines which old mark is same or opposite. -/
def readMarksCode (width base : Nat) (positive : Bool) : Program width 8 :=
  #[.add 0 3 3, .constant 4 (word width base), .add 0 0 4,
    .load (if positive then 1 else 7) 0, .add 0 0 5,
    .load (if positive then 7 else 1) 0]

@[simp] theorem readMarksCode_size (width base : Nat) (positive : Bool) :
    (readMarksCode width base positive).size = 6 := rfl

/-- No literal label is encoded in the mark-writing program. -/
def writeMarkCode (width base : Nat) (positive : Bool) : Program width 8 :=
  #[.add 0 3 3, .constant 4 (word width base), .add 0 0 4] ++
    (if positive then #[] else #[.add 0 0 5]) ++ #[.store 0 5]

@[simp] theorem writeMarkCode_size (width base : Nat) (positive : Bool) :
    (writeMarkCode width base positive).size = if positive then 4 else 5 := by
  cases positive <;> rfl

/-- Concrete six-step target state. The stored mark representation supplies
only the values of the two actual heap loads, not any initial register. -/
def readMarksFinished (state : State width 8) (base : Nat)
    (literal : CNF.Literal (Fin n)) (marks : Marks n) : State width 8 :=
  let s1 := state.advance.put 0 (word width (2 * literal.1.val))
  let s2 := s1.advance.put 4 (word width base)
  let s3 := s2.advance.put 0 (word width (base + 2 * literal.1.val))
  let s4 := s3.advance.put (if literal.2 then 1 else 7)
    (MarkStorage.encode width (marks.read (literal.1, true)))
  let s5 := s4.advance.put 0 (word width (base + 2 * literal.1.val + 1))
  s5.advance.put (if literal.2 then 7 else 1)
    (MarkStorage.encode width (marks.read (literal.1, false)))

theorem readMarksFinished_frame (state : State width 8) (base : Nat)
    (literal : CNF.Literal (Fin n)) (marks : Marks n) :
    (readMarksFinished state base literal marks).heap = state.heap ∧
    (readMarksFinished state base literal marks).stack = state.stack ∧
    (readMarksFinished state base literal marks).output = state.output ∧
    (readMarksFinished state base literal marks).halted = state.halted := by
  cases sign : literal.2 <;> simp [readMarksFinished, sign, State.put, State.advance]

/-- Once the computed-address reads execute, their actual old flags establish
exactly the invariant consumed by the checked dispatch suffix. -/
theorem readMarksFinished_control (state : State width 8) (base : Nat)
    (literal : CNF.Literal (Fin n)) (marks : Marks n)
    (zero : state.reg 2 = word width 0)
    (trueHeld : state.reg 5 = MarkStorage.encode width true)
    (decrement : state.reg 6 = word width (2 ^ width - 1))
    (label : state.reg 3 = word width literal.1.val) (running : state.halted = false) :
    JoinedLiteral.Control (readMarksFinished state base literal marks) literal
      (marks.read literal) (marks.read (CNF.negate literal)) := by
  cases sign : literal.2 <;>
    constructor <;>
    simp [readMarksFinished, sign, State.advance, State.put, CNF.negate, Std.Sat.Literal.negate,
      Marks.read, zero, trueHeld, decrement, label, running]

def ReadMarksAt (destination : Program width 8) (entry base : Nat) (positive : Bool) : Prop :=
  ∀ phase : Fin 6, destination[entry + phase.val]? =
    some (readMarksCode width base positive)[phase.val]

private theorem word_val (value : Nat) (fits : value < 2 ^ width) :
    (word width value).val = value := Nat.mod_eq_of_lt fits

private theorem next_position (state : State width 8) (position : Nat)
    (held : state.pc = word width position) (fits : position < 2 ^ width) :
    state.advance.pc = word width (position + 1) := by
  simp only [State.advance, held, word_val (width := width) position fits]

private theorem read_fetched (destination : Program width 8) (entry base : Nat)
    (positive : Bool) (present : ReadMarksAt destination entry base positive)
    (state : State width 8) (phase : Fin 6)
    (position : state.pc = word width (entry + phase.val)) (capacity : entry + 6 < 2 ^ width) :
    destination[state.pc.val]? = some (readMarksCode width base positive)[phase.val] := by
  rw [position, word_val (width := width) (entry + phase.val) (by have := phase.isLt; omega)]
  exact present phase

private theorem add_step (destination : Program width 8) (state : State width 8)
    (dst left right : Fin 8) (a b : Nat)
    (first : state.reg left = word width a) (second : state.reg right = word width b)
    (firstFits : a < 2 ^ width) (secondFits : b < 2 ^ width)
    (running : state.halted = false)
    (read : destination[state.pc.val]? = some (.add dst left right)) :
    programStep destination state = some (state.advance.put dst (word width (a + b))) := by
  unfold programStep
  rw [read]
  change step (.add dst left right) state = _
  simp only [step, running, Bool.false_eq_true, ite_false, first, second,
    word_val (width := width) a firstFits, word_val (width := width) b secondFits]

private theorem constant_step (destination : Program width 8) (state : State width 8)
    (dst : Fin 8) (value : Word width) (running : state.halted = false)
    (read : destination[state.pc.val]? = some (.constant dst value)) :
    programStep destination state = some (state.advance.put dst value) := by
  unfold programStep
  rw [read]
  simp [step, running]

private theorem load_step (destination : Program width 8) (state : State width 8)
    (dst : Fin 8) (index : Nat) (bound : index < state.heap.size)
    (points : (state.reg 0).val = index) (value : Word width)
    (held : state.heap[index]'bound = value) (running : state.halted = false)
    (read : destination[state.pc.val]? = some (.load dst 0)) :
    programStep destination state = some (state.advance.put dst value) := by
  unfold programStep
  rw [read]
  change step (.load dst 0) state = _
  simp only [step, running, Bool.false_eq_true, ite_false, points, bound, dite_eq_left, held]

/-- Six actual fetched instructions compute addresses from the already read
label word and load both old polarity marks from their indexed heap cells. -/
theorem read_marks_execution (destination : Program width 8) (entry base : Nat)
    (literal : CNF.Literal (Fin n)) (marks : Marks n)
    (present : ReadMarksAt destination entry base literal.2)
    (state : State width 8) (stored : MarkStorage.Stored marks base state.heap)
    (position : state.pc = word width entry) (label : state.reg 3 = word width literal.1.val)
    (trueHeld : state.reg 5 = MarkStorage.encode width true) (running : state.halted = false)
    (capacity : entry + 6 < 2 ^ width) (heapFits : state.heap.size < 2 ^ width) :
    Execution destination state (readMarksFinished state base literal marks) 6 state.liveWords := by
  have positiveBound : base + 2 * literal.1.val < state.heap.size := by
    simpa [MarkStorage.address] using stored.bound (literal.1, true)
  have negativeBound : base + 2 * literal.1.val + 1 < state.heap.size := by
    simpa [MarkStorage.address, Nat.add_assoc] using stored.bound (literal.1, false)
  have labelFits : literal.1.val < 2 ^ width := by omega
  have doubleFits : 2 * literal.1.val < 2 ^ width := by omega
  have baseFits : base < 2 ^ width := by omega
  have positiveFits : base + 2 * literal.1.val < 2 ^ width := positiveBound.trans heapFits
  have negativeFits : base + 2 * literal.1.val + 1 < 2 ^ width := negativeBound.trans heapFits
  let s1 := state.advance.put 0 (word width (2 * literal.1.val))
  let s2 := s1.advance.put 4 (word width base)
  let s3 := s2.advance.put 0 (word width (base + 2 * literal.1.val))
  let s4 := s3.advance.put (if literal.2 then 1 else 7)
    (MarkStorage.encode width (marks.read (literal.1, true)))
  let s5 := s4.advance.put 0 (word width (base + 2 * literal.1.val + 1))
  let s6 := s5.advance.put (if literal.2 then 7 else 1)
    (MarkStorage.encode width (marks.read (literal.1, false)))
  have p1 : s1.pc = word width (entry + 1) := by
    simpa [s1, State.put] using next_position state entry position (by omega)
  have p2 : s2.pc = word width (entry + 2) := by
    simpa [s2, State.put, Nat.add_assoc] using next_position s1 (entry + 1) p1 (by omega)
  have p3 : s3.pc = word width (entry + 3) := by
    simpa [s3, State.put, Nat.add_assoc] using next_position s2 (entry + 2) p2 (by omega)
  have p4 : s4.pc = word width (entry + 4) := by
    simpa [s4, State.put, Nat.add_assoc] using next_position s3 (entry + 3) p3 (by omega)
  have p5 : s5.pc = word width (entry + 5) := by
    simpa [s5, State.put, Nat.add_assoc] using next_position s4 (entry + 4) p4 (by omega)
  have t1 : programStep destination state = some s1 := by
    simpa [s1, Nat.two_mul] using add_step destination state 0 3 3 literal.1.val literal.1.val
      label label labelFits labelFits running
      (by simpa [readMarksCode] using read_fetched destination entry base literal.2 present state ⟨0, by decide⟩ (by simpa using position) capacity)
  have t2 : programStep destination s1 = some s2 :=
    constant_step destination s1 4 (word width base) running
      (by simpa [readMarksCode] using read_fetched destination entry base literal.2 present s1 ⟨1, by decide⟩ p1 capacity)
  have t3 : programStep destination s2 = some s3 := by
    simpa [s3, Nat.add_comm] using add_step destination s2 0 0 4 (2 * literal.1.val) base
      (by simp [s2, s1, State.put, State.advance]) rfl doubleFits baseFits running
      (by simpa [readMarksCode] using read_fetched destination entry base literal.2 present s2 ⟨2, by decide⟩ p2 capacity)
  have t4 : programStep destination s3 = some s4 := by
    apply load_step destination s3 (if literal.2 then 1 else 7)
      (base + 2 * literal.1.val) positiveBound
      (by simp only [s3, State.put, ite_true]; exact word_val (width := width) _ positiveFits)
      (MarkStorage.encode width (marks.read (literal.1, true)))
      (by simpa [MarkStorage.address, s3, s2, s1, State.put, State.advance] using stored.entry (literal.1, true)) running
    simpa [readMarksCode] using read_fetched destination entry base literal.2 present s3 ⟨3, by decide⟩ p3 capacity
  have t5 : programStep destination s4 = some s5 := by
    apply add_step destination s4 0 0 5 (base + 2 * literal.1.val) 1
      (by cases sign : literal.2 <;> simp [s4, s3, State.put, State.advance, sign])
      (by cases sign : literal.2 <;> simpa [s4, s3, s2, s1, State.put, State.advance, sign, MarkStorage.encode] using trueHeld)
      positiveFits (by omega) running
    simpa [readMarksCode] using read_fetched destination entry base literal.2 present s4 ⟨4, by decide⟩ p4 capacity
  have t6 : programStep destination s5 = some s6 := by
    apply load_step destination s5 (if literal.2 then 7 else 1)
      (base + 2 * literal.1.val + 1) negativeBound
      (by simp only [s5, State.put, ite_true]; exact word_val (width := width) _ negativeFits)
      (MarkStorage.encode width (marks.read (literal.1, false)))
      (by simpa [MarkStorage.address, Nat.add_assoc, s5, s4, s3, s2, s1, State.put, State.advance] using stored.entry (literal.1, false)) running
    simpa [readMarksCode] using read_fetched destination entry base literal.2 present s5 ⟨5, by decide⟩ p5 capacity
  have trace := Execution.cons t1 (Execution.cons t2 (Execution.cons t3
    (Execution.cons t4 (Execution.cons t5 (Execution.cons t6 (Execution.refl s6))))))
  simpa [s6, s5, s4, s3, s2, s1, readMarksFinished, State.put, State.advance,
    State.liveWords] using trace

/-- Concrete target for the computed-address writer. Only the final store
changes heap data; all previous instructions compute its address in register 0. -/
def writeMarkFinished (state : State width 8) (base : Nat)
    (literal : CNF.Literal (Fin n)) (bound : MarkStorage.address base literal < state.heap.size) :
    State width 8 :=
  let s1 := state.advance.put 0 (word width (2 * literal.1.val))
  let s2 := s1.advance.put 4 (word width base)
  let s3 := s2.advance.put 0 (word width (base + 2 * literal.1.val))
  let prepared := if literal.2 then s3 else
    s3.advance.put 0 (word width (base + 2 * literal.1.val + 1))
  { prepared.advance with heap := (state.heap.set (MarkStorage.address base literal) (MarkStorage.encode width true) bound) }

/-- The same canonical storage update used by the checked literal block is
obtained when its final mark address is computed from a stored source label. -/
theorem writeMarkFinished_stored (state : State width 8) (row : Row n)
    (literal : CNF.Literal (Fin n)) (base positiveCursor negativeCursor touchedCursor : Nat)
    (stored : RowStored row base positiveCursor negativeCursor touchedCursor state.heap) :
    RowStored { row with marks := MarkStorage.write row.marks literal true }
      base positiveCursor negativeCursor touchedCursor
      (writeMarkFinished state base literal (stored.marks.bound literal)).heap := by
  simpa [writeMarkFinished, marked, rowLayout] using
    RowStored.set_mark state row literal base positiveCursor negativeCursor touchedCursor stored

def WriteMarkAt (destination : Program width 8) (entry base : Nat) (positive : Bool) : Prop :=
  ∀ phase : Fin (writeMarkCode width base positive).size,
    destination[entry + phase.val]? = some (writeMarkCode width base positive)[phase.val]

/-- Four or five actual instructions calculate the source label's polarity
address and set its mark; no label-specific immediate occurs in the program. -/
theorem write_mark_execution (destination : Program width 8) (entry base : Nat)
    (literal : CNF.Literal (Fin n)) (present : WriteMarkAt destination entry base literal.2)
    (state : State width 8) (bound : MarkStorage.address base literal < state.heap.size)
    (position : state.pc = word width entry) (label : state.reg 3 = word width literal.1.val)
    (trueHeld : state.reg 5 = MarkStorage.encode width true) (running : state.halted = false)
    (capacity : entry + 5 < 2 ^ width) (heapFits : state.heap.size < 2 ^ width) :
    Execution destination state (writeMarkFinished state base literal bound)
      (if literal.2 then 4 else 5) state.liveWords := by
  have labelFits : literal.1.val < 2 ^ width := by
    have addressLower : literal.1.val ≤ MarkStorage.address base literal := by
      cases sign : literal.2 <;> simp only [MarkStorage.address, sign, ite_true, ite_false] <;> omega
    omega
  have doubleFits : 2 * literal.1.val < 2 ^ width := by
    have addressLower : 2 * literal.1.val ≤ MarkStorage.address base literal := by
      cases sign : literal.2 <;> simp only [MarkStorage.address, sign, ite_true, ite_false] <;> omega
    omega
  have baseFits : base < 2 ^ width := by
    have addressLower : base ≤ MarkStorage.address base literal := by
      unfold MarkStorage.address
      omega
    omega
  have addressFits : MarkStorage.address base literal < 2 ^ width := bound.trans heapFits
  let s1 := state.advance.put 0 (word width (2 * literal.1.val))
  let s2 := s1.advance.put 4 (word width base)
  let s3 := s2.advance.put 0 (word width (base + 2 * literal.1.val))
  have p1 : s1.pc = word width (entry + 1) := by
    simpa [s1, State.put] using next_position state entry position (by omega)
  have p2 : s2.pc = word width (entry + 2) := by
    simpa [s2, State.put, Nat.add_assoc] using next_position s1 (entry + 1) p1 (by omega)
  have p3 : s3.pc = word width (entry + 3) := by
    simpa [s3, State.put, Nat.add_assoc] using next_position s2 (entry + 2) p2 (by omega)
  have fetched (phase : Nat) (valid : phase < (writeMarkCode width base literal.2).size)
      (current : State width 8) (pc : current.pc = word width (entry + phase)) :
      destination[current.pc.val]? = some (writeMarkCode width base literal.2)[phase] := by
    have phaseBound : phase < 5 := by cases sign : literal.2 <;> simp [sign] at valid <;> omega
    rw [pc, word_val (width := width) (entry + phase) (by omega)]
    exact present ⟨phase, valid⟩
  have t1 : programStep destination state = some s1 := by
    simpa [s1, Nat.two_mul] using add_step destination state 0 3 3 literal.1.val literal.1.val
      label label labelFits labelFits running
      (by simpa [writeMarkCode] using fetched 0 (by cases sign : literal.2 <;> simp [sign]) state (by simpa using position))
  have t2 : programStep destination s1 = some s2 :=
    constant_step destination s1 4 (word width base) running
      (by simpa [writeMarkCode] using fetched 1 (by cases sign : literal.2 <;> simp [sign]) s1 p1)
  have t3 : programStep destination s2 = some s3 := by
    simpa [s3, Nat.add_comm] using add_step destination s2 0 0 4 (2 * literal.1.val) base
      (by simp [s2, s1, State.put, State.advance]) rfl doubleFits baseFits running
      (by simpa [writeMarkCode] using fetched 2 (by cases sign : literal.2 <;> simp [sign]) s2 p2)
  have storeStep (current : State width 8)
      (points : (current.reg 0).val = MarkStorage.address base literal)
      (held : current.reg 5 = MarkStorage.encode width true)
      (sameHeap : current.heap = state.heap) (isRunning : current.halted = false)
      (read : destination[current.pc.val]? = some (.store 0 5)) :
      programStep destination current = some
        { current.advance with heap := (state.heap.set (MarkStorage.address base literal) (MarkStorage.encode width true) bound) } := by
    unfold programStep
    rw [read]
    change step (.store 0 5) current = _
    simp only [step, isRunning, Bool.false_eq_true, ite_false, points, sameHeap, bound, dite_eq_left, held]
  cases sign : literal.2
  · let s4 := s3.advance.put 0 (word width (base + 2 * literal.1.val + 1))
    have positiveFits : base + 2 * literal.1.val < 2 ^ width := by
      simp [MarkStorage.address, sign] at addressFits
      omega
    have t4 : programStep destination s3 = some s4 := by
      apply add_step destination s3 0 0 5 (base + 2 * literal.1.val) 1 rfl
        (by simpa [s3, s2, s1, State.put, State.advance, MarkStorage.encode] using trueHeld)
        positiveFits (by omega) running
      simpa [writeMarkCode, sign] using fetched 3 (by simp [sign]) s3 p3
    have p4 : s4.pc = word width (entry + 4) := by
      simpa [s4, State.put, Nat.add_assoc] using next_position s3 (entry + 3) p3 (by omega)
    have t5 : programStep destination s4 = some (writeMarkFinished state base literal bound) := by
      simpa [writeMarkFinished, sign, s4, s3, s2, s1] using storeStep s4
        (by
          change (word width (base + 2 * literal.1.val + 1)).val = MarkStorage.address base literal
          simpa [MarkStorage.address, sign, Nat.add_assoc] using
            word_val (width := width) (base + 2 * literal.1.val + 1)
              (by simpa [MarkStorage.address, sign, Nat.add_assoc] using addressFits))
        (by simpa [s4, s3, s2, s1, State.put, State.advance, MarkStorage.encode] using trueHeld) rfl running
        (by simpa [writeMarkCode, sign] using fetched 4 (by simp [sign]) s4 p4)
    have trace := Execution.cons t1 (Execution.cons t2 (Execution.cons t3
      (Execution.cons t4 (Execution.cons t5 (Execution.refl (writeMarkFinished state base literal bound))))))
    simpa [sign, s4, s3, s2, s1, writeMarkFinished, State.put, State.advance, State.liveWords] using trace
  · have t4 : programStep destination s3 = some (writeMarkFinished state base literal bound) := by
      simpa [writeMarkFinished, sign, s3, s2, s1] using storeStep s3
        (by
          change (word width (base + 2 * literal.1.val)).val = MarkStorage.address base literal
          simpa [MarkStorage.address, sign] using
            word_val (width := width) (base + 2 * literal.1.val)
              (by simpa [MarkStorage.address, sign] using addressFits))
        (by simpa [s3, s2, s1, State.put, State.advance, MarkStorage.encode] using trueHeld) rfl running
        (by simpa [writeMarkCode, sign] using fetched 3 (by simp [sign]) s3 p3)
    have trace := Execution.cons t1 (Execution.cons t2 (Execution.cons t3
      (Execution.cons t4 (Execution.refl (writeMarkFinished state base literal bound)))))
    simpa [sign, s3, s2, s1, writeMarkFinished, State.put, State.advance, State.liveWords] using trace

theorem readMarksFinished_position (state : State width 8) (base : Nat)
    (literal : CNF.Literal (Fin n)) (marks : Marks n) (entry : Nat)
    (position : state.pc = word width entry) (capacity : entry + 6 < 2 ^ width) :
    (readMarksFinished state base literal marks).pc = word width (entry + 6) := by
  simp only [readMarksFinished, State.put, State.advance, position, Nat.add_assoc, Nat.reduceAdd,
    word_val (width := width) entry (by omega),
    word_val (width := width) (entry + 1) (by omega),
    word_val (width := width) (entry + 2) (by omega),
    word_val (width := width) (entry + 3) (by omega),
    word_val (width := width) (entry + 4) (by omega),
    word_val (width := width) (entry + 5) (by omega)]

def dynamicTicks (same opposite positive : Bool) : Nat :=
  6 + (if same then 2 else 6) + (if opposite then 3 else 1) +
    (if same then 2 else if opposite then 3 else 7) + (if positive then 4 else 5)

theorem dynamicTicks_le (same opposite positive : Bool) : dynamicTicks same opposite positive ≤ 25 := by
  cases same <;> cases opposite <;> cases positive <;> decide

theorem writeMarkFinished_control (state : State width 8) (base : Nat)
    (literal : CNF.Literal (Fin n)) (bound : MarkStorage.address base literal < state.heap.size)
    (same opposite : Bool) (control : Control state literal same opposite) :
    Control (writeMarkFinished state base literal bound) literal same opposite := by
  cases sign : literal.2 <;> constructor <;>
    simp [writeMarkFinished, sign, State.put, State.advance, control.zero,
      control.trueHeld, control.decrement, control.label, control.sameHeld,
      control.oppositeHeld, control.running]

theorem writeMarkFinished_position (state : State width 8) (base : Nat)
    (literal : CNF.Literal (Fin n)) (bound : MarkStorage.address base literal < state.heap.size)
    (entry : Nat) (position : state.pc = word width entry) (capacity : entry + 5 < 2 ^ width) :
    (writeMarkFinished state base literal bound).pc =
      word width (entry + if literal.2 then 4 else 5) := by
  cases sign : literal.2 <;>
    simp only [writeMarkFinished, sign, Bool.false_eq_true, ite_false, ite_true, State.advance, State.put,
      position, Nat.add_assoc, Nat.reduceAdd,
      word_val (width := width) entry (by omega),
      word_val (width := width) (entry + 1) (by omega),
      word_val (width := width) (entry + 2) (by omega),
      word_val (width := width) (entry + 3) (by omega),
      word_val (width := width) (entry + 4) (by omega)]

/-- Exact preservation of every input cell preceding the scratch allocation. -/
def LowFrame (base : Nat) (before after : Array (Word width)) : Prop :=
  ∀ index : Nat, index < base → after[index]? = before[index]?

theorem LowFrame.refl (base : Nat) (heap : Array (Word width)) : LowFrame base heap heap := by
  intro index below
  rfl

theorem LowFrame.trans {base : Nat} {first middle last : Array (Word width)}
    (left : LowFrame base first middle) (right : LowFrame base middle last) :
    LowFrame base first last := by
  intro index below
  exact (right index below).trans (left index below)

theorem LowFrame.entry {base : Nat} {before after : Array (Word width)}
    (frame : LowFrame base before after) (index : Nat) (below : index < base)
    (oldBound : index < before.size) (newBound : index < after.size) :
    after[index]'newBound = before[index]'oldBound := by
  have equal := frame index below
  rw [Array.getElem?_eq_getElem newBound, Array.getElem?_eq_getElem oldBound] at equal
  exact Option.some.inj equal

/-- Equal-length traces from one state have the same endpoint, irrespective
of their proof-level peak annotations. -/
theorem execution_endpoint {destination : Program width registers}
    {state left right : State width registers} {ticks leftPeak rightPeak : Nat}
    (first : Execution destination state left ticks leftPeak)
    (second : Execution destination state right ticks rightPeak) : left = right := by
  induction ticks generalizing state left right leftPeak rightPeak with
  | zero => cases first; cases second; rfl
  | succ ticks ih =>
    cases first with
    | cons transition rest =>
      cases second with
      | cons other following =>
        have equal := Option.some.inj (transition.symm.trans other)
        subst_vars
        exact ih rest following

theorem inserted_low_frame (state : State width 8) (entry : Nat) (layout : Layout)
    (literal : CNF.Literal (Fin n)) (labels : List (Fin n)) (lower cursor limit : Nat)
    (stored : RecordStorage.HeaderStored labels (layout.signHeader literal.2) lower cursor limit state.heap)
    (room : lower < cursor) (base : Nat)
    (headerLower : base ≤ layout.signHeader literal.2) (bufferLower : base ≤ lower) :
    LowFrame base state.heap (inserted state entry layout literal labels lower cursor limit stored room).heap := by
  intro index below
  simpa [inserted, insertStart, State.put, State.advance] using
    RecordStorage.finished_heap_frame (insertStart state entry (layout.signHeader literal.2)) labels
      (layout.signHeader literal.2) lower cursor limit stored room literal.1 index (by omega) (by omega)

theorem conflicted_low_frame (state : State width 8) (header : Nat)
    (bound : header < state.heap.size) (base : Nat) (headerLower : base ≤ header) :
    LowFrame base state.heap (conflicted state header bound).heap := by
  intro index below
  exact (conflicted_frame state header bound).2.2.2 index (by omega)

theorem touchedInserted_low_frame (state : State width 8) (entry : Nat) (layout : Layout)
    (literal : CNF.Literal (Fin n)) (labels : List (Fin n)) (lower cursor limit : Nat)
    (stored : RecordStorage.HeaderStored labels layout.touchedHeader lower cursor limit state.heap)
    (room : lower < cursor) (base : Nat)
    (headerLower : base ≤ layout.touchedHeader) (bufferLower : base ≤ lower) :
    LowFrame base state.heap (touchedInserted state entry layout literal labels lower cursor limit stored room).heap := by
  intro index below
  simpa [touchedInserted, touchedStart, State.put, State.advance] using
    RecordStorage.finished_heap_frame (touchedStart state entry layout.touchedHeader) labels
      layout.touchedHeader lower cursor limit stored room literal.1 index (by omega) (by omega)

theorem writeMarkFinished_low_frame (state : State width 8) (base : Nat)
    (literal : CNF.Literal (Fin n)) (bound : MarkStorage.address base literal < state.heap.size) :
    LowFrame base state.heap (writeMarkFinished state base literal bound).heap := by
  intro index below
  have lower : base ≤ MarkStorage.address base literal := by unfold MarkStorage.address; omega
  cases sign : literal.2 <;>
    simpa [writeMarkFinished, sign, State.put, State.advance] using
      Array.getElem?_set_ne bound (show MarkStorage.address base literal ≠ index by omega)

theorem SourceStored.of_low_frame {clause : CNF.Clause (Fin n)} {start base : Nat}
    {before after : Array (Word width)} (stored : SourceStored clause start before)
    (region : start + 2 * clause.length ≤ base) (size : after.size = before.size)
    (frame : LowFrame base before after) : SourceStored clause start after := by
  refine ⟨by simpa only [size] using stored.fits, ?_⟩
  intro index
  have old := stored.entry index
  have firstBelow : start + 2 * index.val < base := by have := index.isLt; omega
  have secondBelow : start + 2 * index.val + 1 < base := by have := index.isLt; omega
  have firstBound : start + 2 * index.val < before.size := by have := old.fits; omega
  have secondBound : start + 2 * index.val + 1 < before.size := by have := old.fits; omega
  refine ⟨by simpa only [size] using old.fits, ?_, ?_⟩
  · exact (frame.entry _ firstBelow firstBound (by simpa only [size] using firstBound)).trans old.label
  · exact (frame.entry _ secondBelow secondBound (by simpa only [size] using secondBound)).trans old.polarity

theorem CursorStored.of_low_frame {pointer header base : Nat}
    {before after : Array (Word width)} (stored : CursorStored pointer header before)
    (below : header < base) (size : after.size = before.size)
    (frame : LowFrame base before after) : CursorStored pointer header after := by
  refine ⟨by simpa only [size] using stored.bound, ?_⟩
  exact (frame.entry header below stored.bound (by simpa only [size] using stored.bound)).trans stored.value

/-- One physical occurrence advances the suffix invariant even if its label
or polarity duplicates an occurrence already processed. -/
theorem correct_record_drop (clause : CNF.Clause (Fin n)) (row : Row n) (index : Nat)
    (bound : index < clause.length) (correct : row.Correct (clause.drop (index + 1))) :
    (row.record clause[index]).Correct (clause.drop index) := by
  rw [List.drop_eq_getElem_cons bound]
  exact Row.record_correct correct clause[index]

/-- The checked sign stage also preserves the entire input prefix. Its
endpoint is identified with the concrete fetched branch trace. -/
theorem sign_trace_low_frame (destination : Program width 8) (entry base : Nat)
    (literal : CNF.Literal (Fin n))
    (present : SuffixDispatch.SuffixAt destination entry (rowLayout n base) literal)
    (clause : CNF.Clause (Fin n)) (row : Row n) (correct : row.Correct clause)
    (state next : State width 8) (positiveCursor negativeCursor touchedCursor : Nat)
    (stored : RowStored row base positiveCursor negativeCursor touchedCursor state.heap)
    (control : Control state literal (row.marks.read literal) (row.marks.read (CNF.negate literal)))
    (position : state.pc = word width (entry + 5))
    (capacity : entry + 26 < 2 ^ width) (heapFits : state.heap.size < 2 ^ width)
    (trace : Execution destination state next (if row.marks.read literal then 2 else 6) state.liveWords) :
    LowFrame base state.heap next.heap := by
  cases same : row.marks.read literal
  · cases polarity : literal.2
    · have fresh : row.marks.read (literal.1, false) = false := by simpa [Marks.read, polarity] using same
      have room := RowStored.negative_room clause row correct literal.1 fresh base
        positiveCursor negativeCursor touchedCursor state.heap stored
      have header : RecordStorage.HeaderStored row.negative ((rowLayout n base).signHeader literal.2)
          (base + 3 * n + 4) negativeCursor (base + 4 * n + 4) state.heap := by
        simpa [rowLayout, Layout.signHeader, polarity] using stored.negative
      have upper : negativeCursor ≤ base + 4 * n + 4 := by have := stored.negative.buffer.ends; omega
      have fit := RowStored.scratch_fits row base positiveCursor negativeCursor touchedCursor state.heap stored
      have actual := SuffixDispatch.signed_insert_execution destination entry (rowLayout n base) literal present
        state position (by simpa [same] using control.sameHeld) control.label control.decrement
        control.running capacity row.negative (base + 3 * n + 4) negativeCursor (base + 4 * n + 4)
        header room (by simp [rowLayout, Layout.signHeader, polarity]; omega) (by omega)
      have endpoint := execution_endpoint trace (by simpa [same] using actual)
      rw [endpoint]
      exact inserted_low_frame state entry (rowLayout n base) literal row.negative
        (base + 3 * n + 4) negativeCursor (base + 4 * n + 4) header room base
        (by simp [rowLayout, Layout.signHeader, polarity]; omega) (by omega)
    · have fresh : row.marks.read (literal.1, true) = false := by simpa [Marks.read, polarity] using same
      have room := RowStored.positive_room clause row correct literal.1 fresh base
        positiveCursor negativeCursor touchedCursor state.heap stored
      have header : RecordStorage.HeaderStored row.positive ((rowLayout n base).signHeader literal.2)
          (base + 2 * n + 4) positiveCursor (base + 3 * n + 4) state.heap := by
        simpa [rowLayout, Layout.signHeader, polarity] using stored.positive
      have upper : positiveCursor ≤ base + 3 * n + 4 := by have := stored.positive.buffer.ends; omega
      have fit := RowStored.scratch_fits row base positiveCursor negativeCursor touchedCursor state.heap stored
      have actual := SuffixDispatch.signed_insert_execution destination entry (rowLayout n base) literal present
        state position (by simpa [same] using control.sameHeld) control.label control.decrement
        control.running capacity row.positive (base + 2 * n + 4) positiveCursor (base + 3 * n + 4)
        header room (by simp [rowLayout, Layout.signHeader, polarity]; omega) (by omega)
      have endpoint := execution_endpoint trace (by simpa [same] using actual)
      rw [endpoint]
      exact inserted_low_frame state entry (rowLayout n base) literal row.positive
        (base + 2 * n + 4) positiveCursor (base + 3 * n + 4) header room base
        (by simp only [rowLayout, Layout.signHeader, polarity, Bool.false_eq_true, ite_false, ite_true]; omega) (by omega)
  · have actual := SuffixDispatch.signed_skip_execution destination entry (rowLayout n base) literal present
      state position (by simpa [same] using control.sameHeld) control.zero control.running capacity
    have endpoint := execution_endpoint trace (by simpa [same] using actual)
    rw [endpoint]
    intro index below
    rfl

theorem conflict_trace_low_frame (destination : Program width 8) (entry base : Nat)
    (literal : CNF.Literal (Fin n))
    (present : SuffixDispatch.SuffixAt destination entry (rowLayout n base) literal)
    (row : Row n) (state next : State width 8) (positiveCursor negativeCursor touchedCursor : Nat)
    (stored : RowStored row base positiveCursor negativeCursor touchedCursor state.heap)
    (control : Control state literal (row.marks.read literal) (row.marks.read (CNF.negate literal)))
    (position : state.pc = word width (entry + 12))
    (capacity : entry + 26 < 2 ^ width) (heapFits : state.heap.size < 2 ^ width)
    (trace : Execution destination state next (if row.marks.read (CNF.negate literal) then 3 else 1) state.liveWords) :
    LowFrame base state.heap next.heap := by
  cases opposite : row.marks.read (CNF.negate literal)
  · have actual := SuffixDispatch.conflict_skip_execution destination entry (rowLayout n base) literal present
      state position (by simpa [opposite] using control.oppositeHeld) control.running capacity
    have endpoint := execution_endpoint trace (by simpa [opposite] using actual)
    rw [endpoint]
    intro index below
    rfl
  · have actual := SuffixDispatch.conflict_set_execution destination entry (rowLayout n base) literal present
      state position (by simpa [opposite] using control.oppositeHeld) control.trueHeld control.running capacity
      stored.flagBound (by change base + 2 * n + 3 < 2 ^ width; have := stored.flagBound; omega)
    have endpoint := execution_endpoint trace (by simpa [opposite] using actual)
    rw [endpoint]
    exact conflicted_low_frame state (base + 2 * n + 3) stored.flagBound base (by omega)

theorem touched_trace_low_frame (destination : Program width 8) (entry base : Nat)
    (literal : CNF.Literal (Fin n))
    (present : SuffixDispatch.SuffixAt destination entry (rowLayout n base) literal)
    (row : Row n) (state next : State width 8) (positiveCursor negativeCursor touchedCursor : Nat)
    (stored : RowStored row base positiveCursor negativeCursor touchedCursor state.heap)
    (control : Control state literal (row.marks.read literal) (row.marks.read (CNF.negate literal)))
    (position : state.pc = word width (entry + 15))
    (capacity : entry + 26 < 2 ^ width) (heapFits : state.heap.size < 2 ^ width)
    (freshRoom : row.marks.read literal = false → row.marks.read (CNF.negate literal) = false →
      base + 4 * n + 4 < touchedCursor)
    (trace : Execution destination state next
      (if row.marks.read literal then 2 else if row.marks.read (CNF.negate literal) then 3 else 7) state.liveWords) :
    LowFrame base state.heap next.heap := by
  cases same : row.marks.read literal
  · cases opposite : row.marks.read (CNF.negate literal)
    · have room := freshRoom same opposite
      have upper : touchedCursor ≤ base + 5 * n + 4 := by have := stored.touched.buffer.ends; omega
      have fit := RowStored.scratch_fits row base positiveCursor negativeCursor touchedCursor state.heap stored
      have actual := SuffixDispatch.touched_insert_execution destination entry (rowLayout n base) literal present
        state position (by simpa [same] using control.sameHeld) (by simpa [opposite] using control.oppositeHeld)
        control.label control.decrement control.running capacity row.touched (base + 4 * n + 4)
        touchedCursor (base + 5 * n + 4) stored.touched room
        (by simp [rowLayout]; have := stored.touched.bound; omega) (by omega)
      have endpoint := execution_endpoint trace (by simpa [same, opposite] using actual)
      rw [endpoint]
      exact touchedInserted_low_frame state entry (rowLayout n base) literal row.touched
        (base + 4 * n + 4) touchedCursor (base + 5 * n + 4) stored.touched room base
        (by simp [rowLayout]; omega) (by omega)
    · have actual := SuffixDispatch.touched_opposite_skip_execution destination entry (rowLayout n base) literal present
        state position (by simpa [same] using control.sameHeld) (by simpa [opposite] using control.oppositeHeld)
        control.zero control.running capacity
      have endpoint := execution_endpoint trace (by simpa [same, opposite] using actual)
      rw [endpoint]
      intro index below
      rfl
  · have actual := SuffixDispatch.touched_same_skip_execution destination entry (rowLayout n base) literal present
      state position (by simpa [same] using control.sameHeld) control.zero control.running capacity
    have endpoint := execution_endpoint trace (by simpa [same] using actual)
    rw [endpoint]
    intro index below
    rfl

/-- The computed-address reads, reusable branch suffix and computed-address
store compose in one destination program, refining one semantic row record.
The source label is an actual register precondition supplied by the pair reader. -/
theorem dynamic_record_execution (destination : Program width 8) (entry base : Nat)
    (literal : CNF.Literal (Fin n))
    (readPresent : ReadMarksAt destination entry base literal.2)
    (suffixPresent : SuffixDispatch.SuffixAt destination (entry + 1) (rowLayout n base) literal)
    (writePresent : WriteMarkAt destination (entry + 25) base literal.2)
    (clause : CNF.Clause (Fin n)) (row : Row n) (correct : row.Correct clause)
    (state : State width 8) (positiveCursor negativeCursor touchedCursor : Nat)
    (stored : RowStored row base positiveCursor negativeCursor touchedCursor state.heap)
    (position : state.pc = word width entry) (zero : state.reg 2 = word width 0)
    (trueHeld : state.reg 5 = MarkStorage.encode width true)
    (decrement : state.reg 6 = word width (2 ^ width - 1))
    (label : state.reg 3 = word width literal.1.val) (running : state.halted = false)
    (capacity : entry + 30 < 2 ^ width) (heapFits : state.heap.size < 2 ^ width) :
    ∃ final : State width 8,
      Execution destination state final
        (dynamicTicks (row.marks.read literal) (row.marks.read (CNF.negate literal)) literal.2) state.liveWords ∧
      RowStored (row.record literal) base (positiveNext row literal positiveCursor)
        (negativeNext row literal negativeCursor) (touchedNext row literal touchedCursor) final.heap ∧
      Control final literal (row.marks.read literal) (row.marks.read (CNF.negate literal)) ∧
      final.pc = word width (entry + 25 + if literal.2 then 4 else 5) ∧
      final.liveWords = state.liveWords ∧ final.heap.size = state.heap.size ∧
      LowFrame base state.heap final.heap ∧
      dynamicTicks (row.marks.read literal) (row.marks.read (CNF.negate literal)) literal.2 ≤ 25 := by
  let read := readMarksFinished state base literal row.marks
  have readTrace := read_marks_execution destination entry base literal row.marks readPresent state
    stored.marks position label trueHeld running (by omega) heapFits
  have readLive : read.liveWords = state.liveWords := by
    cases sign : literal.2 <;> simp [read, readMarksFinished, sign, State.put, State.advance, State.liveWords]
  have readHeap : read.heap = state.heap := (readMarksFinished_frame state base literal row.marks).1
  have readStored : RowStored row base positiveCursor negativeCursor touchedCursor read.heap := by
    simpa only [readHeap] using stored
  have readControl := readMarksFinished_control state base literal row.marks zero trueHeld decrement label running
  have readPosition : read.pc = word width ((entry + 1) + 5) := by
    simpa [read, Nat.add_assoc] using readMarksFinished_position state base literal row.marks entry position (by omega)
  obtain ⟨signed, signTrace, signStored, signControl, signPosition, signLive, signSize⟩ :=
    SuffixDispatch.sign_stage destination (entry + 1) base literal suffixPresent clause row correct read
      positiveCursor negativeCursor touchedCursor readStored readControl readPosition (by omega)
      (by simpa only [readHeap] using heapFits)
  let signedRow := signRow row literal
  have signedControl : Control signed literal (signedRow.marks.read literal)
      (signedRow.marks.read (CNF.negate literal)) := by simpa [signedRow] using signControl
  obtain ⟨conflict, conflictTrace, conflictStored, conflictControl, conflictPosition, conflictLive, conflictSize⟩ :=
    SuffixDispatch.conflict_stage destination (entry + 1) base literal suffixPresent signedRow signed
      (positiveNext row literal positiveCursor) (negativeNext row literal negativeCursor) touchedCursor
      signStored signedControl signPosition (by omega) (by simpa [signSize, readHeap] using heapFits)
  let conflictRowValue := conflictRow signedRow literal
  have conflictControl' : Control conflict literal (conflictRowValue.marks.read literal)
      (conflictRowValue.marks.read (CNF.negate literal)) := by simpa [conflictRowValue] using conflictControl
  have freshRoom : conflictRowValue.marks.read literal = false →
      conflictRowValue.marks.read (CNF.negate literal) = false → base + 4 * n + 4 < touchedCursor := by
    intro same opposite
    apply RowStored.touched_room clause row correct literal _ _ base positiveCursor negativeCursor touchedCursor state.heap stored
    · simpa [conflictRowValue, signedRow] using same
    · simpa [conflictRowValue, signedRow] using opposite
  obtain ⟨touched, touchedTrace, touchedStored, touchedControl, touchedPosition, touchedLive, touchedSize⟩ :=
    SuffixDispatch.touched_stage destination (entry + 1) base literal suffixPresent conflictRowValue conflict
      (positiveNext row literal positiveCursor) (negativeNext row literal negativeCursor) touchedCursor
      conflictStored conflictControl' conflictPosition (by omega)
      (by simpa [conflictSize, signSize, readHeap] using heapFits) freshRoom
  let touchedRowValue := touchedRow conflictRowValue literal
  let final := writeMarkFinished touched base literal (touchedStored.marks.bound literal)
  have lastTrace := write_mark_execution destination (entry + 25) base literal writePresent touched
    (touchedStored.marks.bound literal) (by simpa [Nat.add_assoc] using touchedPosition)
    touchedControl.label touchedControl.trueHeld touchedControl.running (by omega)
    (by simpa [touchedSize, conflictSize, signSize, readHeap] using heapFits)
  have finalStored := writeMarkFinished_stored touched touchedRowValue literal base
    (positiveNext row literal positiveCursor) (negativeNext row literal negativeCursor)
    (touchedNext conflictRowValue literal touchedCursor) touchedStored
  have allTrace := ((readTrace.append signTrace).append conflictTrace).append (touchedTrace.append lastTrace)
  have signFrame := sign_trace_low_frame destination (entry + 1) base literal suffixPresent clause row correct
    read signed positiveCursor negativeCursor touchedCursor readStored readControl readPosition
    (by omega) (by simpa only [readHeap] using heapFits) signTrace
  have conflictFrame := conflict_trace_low_frame destination (entry + 1) base literal suffixPresent signedRow
    signed conflict (positiveNext row literal positiveCursor) (negativeNext row literal negativeCursor)
    touchedCursor signStored signedControl signPosition (by omega)
    (by simpa [signSize, readHeap] using heapFits) conflictTrace
  have touchedFrame := touched_trace_low_frame destination (entry + 1) base literal suffixPresent conflictRowValue
    conflict touched (positiveNext row literal positiveCursor) (negativeNext row literal negativeCursor)
    touchedCursor conflictStored conflictControl' conflictPosition (by omega)
    (by simpa [conflictSize, signSize, readHeap] using heapFits) freshRoom touchedTrace
  refine ⟨final, ?_, ?_, ?_, ?_, ?_, ?_, ?_, dynamicTicks_le _ _ _⟩
  · simpa only [dynamicTicks, signedRow, conflictRowValue, signRow_marks, conflictRow_marks,
      touchedLive, conflictLive, signLive, readLive, Nat.max_self, Nat.add_assoc] using allTrace
  · have equality : { touchedRowValue with marks := MarkStorage.write touchedRowValue.marks literal true } = row.record literal := by
      simpa [touchedRowValue, conflictRowValue, signedRow] using stages_record row literal
    simpa [final, equality, touchedNext, conflictRowValue, signedRow] using finalStored
  · simpa only [conflictRowValue, signedRow, conflictRow_marks, signRow_marks] using
      writeMarkFinished_control touched base literal (touchedStored.marks.bound literal) _ _ touchedControl
  · exact writeMarkFinished_position touched base literal (touchedStored.marks.bound literal)
      (entry + 25) (by simpa [Nat.add_assoc] using touchedPosition) (by omega)
  · have finalLive : final.liveWords = touched.liveWords := by
      cases sign : literal.2 <;>
        simp [final, writeMarkFinished, sign, State.advance, State.put, State.liveWords]
    exact finalLive.trans (touchedLive.trans (conflictLive.trans (signLive.trans readLive)))

  · cases sign : literal.2 <;>
      simp [final, writeMarkFinished, sign, State.advance, State.put,
        touchedSize, conflictSize, signSize, readHeap]
  · have readFrame : LowFrame base state.heap read.heap := by
      rw [readHeap]
      exact LowFrame.refl base state.heap
    exact (((readFrame.trans signFrame).trans conflictFrame).trans touchedFrame).trans
      (writeMarkFinished_low_frame touched base literal (touchedStored.marks.bound literal))

/-- The physical source reader and the computed-label record trace execute
in the same destination program. Polarity selects one of two fixed blocks.
The input cursor is actually decremented and remains stored after dispatch. -/
theorem physical_record_execution (destination : Program width 8)
    (sourceEntry header pointer negativeTarget base : Nat) (literal : CNF.Literal (Fin n))
    (pairPresent : PairAt destination sourceEntry header negativeTarget)
    (readPresent : ReadMarksAt destination (if literal.2 then sourceEntry + 10 else negativeTarget) base literal.2)
    (suffixPresent : SuffixDispatch.SuffixAt destination
      ((if literal.2 then sourceEntry + 10 else negativeTarget) + 1) (rowLayout n base) literal)
    (writePresent : WriteMarkAt destination
      ((if literal.2 then sourceEntry + 10 else negativeTarget) + 25) base literal.2)
    (clause : CNF.Clause (Fin n)) (row : Row n) (correct : row.Correct clause)
    (state : State width 8) (positiveCursor negativeCursor touchedCursor : Nat)
    (stored : RowStored row base positiveCursor negativeCursor touchedCursor state.heap)
    (cursor : CursorStored (pointer + 2) header state.heap) (pair : PairStored literal pointer state.heap)
    (headerBefore : header < base) (position : state.pc = word width sourceEntry)
    (zero : state.reg 2 = word width 0) (trueHeld : state.reg 5 = MarkStorage.encode width true)
    (decrement : state.reg 6 = word width (2 ^ width - 1)) (running : state.halted = false)
    (sourceCapacity : sourceEntry + 10 < 2 ^ width)
    (recordCapacity : (if literal.2 then sourceEntry + 10 else negativeTarget) + 30 < 2 ^ width)
    (heapFits : state.heap.size < 2 ^ width) :
    ∃ final : State width 8,
      Execution destination state final
        (10 + dynamicTicks (row.marks.read literal) (row.marks.read (CNF.negate literal)) literal.2) state.liveWords ∧
      RowStored (row.record literal) base (positiveNext row literal positiveCursor)
        (negativeNext row literal negativeCursor) (touchedNext row literal touchedCursor) final.heap ∧
      Control final literal (row.marks.read literal) (row.marks.read (CNF.negate literal)) ∧
      final.pc = word width ((if literal.2 then sourceEntry + 10 else negativeTarget) + 25 +
        if literal.2 then 4 else 5) ∧
      final.liveWords = state.liveWords ∧ final.heap.size = state.heap.size ∧
      LowFrame base (state.heap.set header (word width pointer) cursor.bound) final.heap ∧
      CursorStored pointer header final.heap ∧
      10 + dynamicTicks (row.marks.read literal) (row.marks.read (CNF.negate literal)) literal.2 ≤ 35 := by
  let readerState := pairFinished state sourceEntry header pointer negativeTarget literal cursor.bound
  have prefixTrace := pair_execution destination sourceEntry header pointer negativeTarget literal pairPresent
    state cursor pair position decrement running sourceCapacity heapFits
  have prefixFrame := pairFinished_frame state sourceEntry header pointer negativeTarget literal cursor.bound
  have prefixHeap : readerState.heap = state.heap.set header (word width pointer) cursor.bound := prefixFrame.2.2.2.2
  have prefixSize : readerState.heap.size = state.heap.size := by rw [prefixHeap]; simp
  have prefixLive : readerState.liveWords = state.liveWords := by
    cases sign : literal.2 <;> simp [readerState, pairFinished, pairPrepared, sign, State.put, State.advance, State.liveWords]
  have prefixStored : RowStored row base positiveCursor negativeCursor touchedCursor readerState.heap := by
    rw [prefixHeap]
    exact rowStored_after_input_store stored header cursor.bound (word width pointer) headerBefore
  have prefixPosition := pairFinished_position state sourceEntry header pointer negativeTarget literal
    cursor.bound position sourceCapacity
  have prefixLabel := pairFinished_label state sourceEntry header pointer negativeTarget literal cursor.bound
  have prefixZero : readerState.reg 2 = word width 0 :=
    (prefixFrame.1 2 (by decide) (by decide) (by decide) (by decide)).trans zero
  have prefixTrue : readerState.reg 5 = MarkStorage.encode width true :=
    (prefixFrame.1 5 (by decide) (by decide) (by decide) (by decide)).trans trueHeld
  have prefixDecrement : readerState.reg 6 = word width (2 ^ width - 1) :=
    (prefixFrame.1 6 (by decide) (by decide) (by decide) (by decide)).trans decrement
  have prefixRunning : readerState.halted = false := prefixFrame.2.2.2.1.trans running
  obtain ⟨final, recordTrace, finalStored, finalControl, finalPosition, finalLive, finalSize, finalFrame, cost⟩ :=
    dynamic_record_execution destination (if literal.2 then sourceEntry + 10 else negativeTarget) base literal
      readPresent suffixPresent writePresent clause row correct readerState positiveCursor negativeCursor touchedCursor
      prefixStored prefixPosition prefixZero prefixTrue prefixDecrement prefixLabel prefixRunning
      recordCapacity (by simpa only [prefixSize] using heapFits)
  refine ⟨final, ?_, finalStored, finalControl, finalPosition, finalLive.trans prefixLive,
    finalSize.trans prefixSize, ?_, ?_, by omega⟩
  · simpa only [prefixLive, Nat.max_self] using prefixTrace.append recordTrace
  · simpa only [prefixHeap] using finalFrame
  · have prefixCursor : CursorStored pointer header readerState.heap := by
      cases sign : literal.2 <;>
        simpa [readerState, pairFinished, sign, State.advance] using pairPrepared_cursor state header pointer literal cursor.bound
    exact CursorStored.of_low_frame prefixCursor headerBefore finalSize finalFrame

/-- The nineteen shared dispatch instructions contain only static header
addresses and branch targets. They never contain a source literal label. -/
def dispatchCode (width virtualEntry : Nat) (layout : Layout) (positive : Bool) : Program width 8 :=
  #[.branchZero 1 (word width (virtualEntry + 7)), .branchZero 2 (word width (virtualEntry + 12)),
    .constant 0 (word width (layout.signHeader positive)), .load 4 0, .add 4 4 6, .store 4 3, .store 0 4,
    .branchZero 7 (word width (virtualEntry + 15)), .constant 0 (word width layout.tautologyHeader), .store 0 5,
    .branchZero 1 (word width (virtualEntry + 17)), .branchZero 2 (word width (virtualEntry + 24)),
    .branchZero 7 (word width (virtualEntry + 19)), .branchZero 2 (word width (virtualEntry + 24)),
    .constant 0 (word width layout.touchedHeader), .load 4 0, .add 4 4 6, .store 4 3, .store 0 4]

@[simp] theorem dispatchCode_size (width virtualEntry : Nat) (layout : Layout) (positive : Bool) :
    (dispatchCode width virtualEntry layout positive).size = 19 := rfl

/-- A fixed source-driven loop: test six, reader ten, positive arm thirty,
negative arm thirty-one. Both arms return to the stored-pointer test. -/
def rowCode (width entry n base cursorHeader startHeader exit : Nat) : Program width 8 :=
  testCode width cursorHeader startHeader exit ++
  pairCode width (entry + 6) cursorHeader (entry + 46) ++
  readMarksCode width base true ++ dispatchCode width (entry + 17) (rowLayout n base) true ++
  writeMarkCode width base true ++ #[.branchZero 2 (word width entry)] ++
  readMarksCode width base false ++ dispatchCode width (entry + 47) (rowLayout n base) false ++
  writeMarkCode width base false ++ #[.branchZero 2 (word width entry)]

@[simp] theorem rowCode_size (width entry n base cursorHeader startHeader exit : Nat) :
    (rowCode width entry n base cursorHeader startHeader exit).size = 77 := by
  simp only [rowCode, Array.size_append, testCode_size, pairCode_size, readMarksCode_size,
    dispatchCode_size, writeMarkCode_size, Array.size_singleton, ite_true, Bool.false_eq_true, ite_false]

def RowAt (destination : Program width 8) (entry n base cursorHeader startHeader exit : Nat) : Prop :=
  ∀ phase : Fin 77, destination[entry + phase.val]? =
    some ((rowCode width entry n base cursorHeader startHeader exit)[phase.val]'(by
      rw [rowCode_size]
      exact phase.isLt))

theorem row_pair_at (destination : Program width 8) (entry n base cursorHeader startHeader exit : Nat)
    (present : RowAt destination entry n base cursorHeader startHeader exit) :
    PairAt destination (entry + 6) cursorHeader (entry + 46) := by
  intro phase
  have fetched := present ⟨6 + phase.val, by
    have bound : phase.val < 10 := by simpa using phase.isLt
    omega⟩
  fin_cases phase <;> simpa [rowCode, testCode, pairCode, readMarksCode, dispatchCode, writeMarkCode, Nat.add_assoc] using fetched

theorem row_positive_read_at (destination : Program width 8) (entry n base cursorHeader startHeader exit : Nat)
    (present : RowAt destination entry n base cursorHeader startHeader exit) :
    ReadMarksAt destination (entry + 16) base true := by
  intro phase
  have fetched := present ⟨16 + phase.val, by
    have bound : phase.val < 6 := by simpa using phase.isLt
    omega⟩
  fin_cases phase <;> simpa [rowCode, testCode, pairCode, readMarksCode, dispatchCode, writeMarkCode, Nat.add_assoc] using fetched

theorem row_negative_read_at (destination : Program width 8) (entry n base cursorHeader startHeader exit : Nat)
    (present : RowAt destination entry n base cursorHeader startHeader exit) :
    ReadMarksAt destination (entry + 46) base false := by
  intro phase
  have fetched := present ⟨46 + phase.val, by
    have bound : phase.val < 6 := by simpa using phase.isLt
    omega⟩
  fin_cases phase <;> simpa [rowCode, testCode, pairCode, readMarksCode, dispatchCode, writeMarkCode, Nat.add_assoc] using fetched

theorem row_positive_write_at (destination : Program width 8) (entry n base cursorHeader startHeader exit : Nat)
    (present : RowAt destination entry n base cursorHeader startHeader exit) :
    WriteMarkAt destination (entry + 41) base true := by
  intro phase
  have fetched := present ⟨41 + phase.val, by
    have bound : phase.val < 4 := by simpa using phase.isLt
    omega⟩
  fin_cases phase <;> simpa [rowCode, testCode, pairCode, readMarksCode, dispatchCode, writeMarkCode, Nat.add_assoc] using fetched

theorem row_negative_write_at (destination : Program width 8) (entry n base cursorHeader startHeader exit : Nat)
    (present : RowAt destination entry n base cursorHeader startHeader exit) :
    WriteMarkAt destination (entry + 71) base false := by
  intro phase
  have fetched := present ⟨71 + phase.val, by
    have bound : phase.val < 5 := by simpa using phase.isLt
    omega⟩
  fin_cases phase <;> simpa [rowCode, testCode, pairCode, readMarksCode, dispatchCode, writeMarkCode, Nat.add_assoc] using fetched

theorem row_positive_suffix_at (destination : Program width 8) (entry base cursorHeader startHeader exit : Nat)
    (literal : CNF.Literal (Fin n)) (polarity : literal.2 = true)
    (present : RowAt destination entry n base cursorHeader startHeader exit) :
    SuffixDispatch.SuffixAt destination (entry + 17) (rowLayout n base) literal := by
  intro phase lower upper
  change 5 ≤ phase.val at lower
  change phase.val < 24 at upper
  have fetched := present ⟨17 + phase.val, by have := phase.isLt; omega⟩
  fin_cases phase <;>
    simp_all [rowCode, testCode, pairCode, readMarksCode, dispatchCode, writeMarkCode, Nat.add_assoc, literalCode, polarity]
  all_goals (norm_num at lower <;> norm_num at upper)

theorem row_negative_suffix_at (destination : Program width 8) (entry base cursorHeader startHeader exit : Nat)
    (literal : CNF.Literal (Fin n)) (polarity : literal.2 = false)
    (present : RowAt destination entry n base cursorHeader startHeader exit) :
    SuffixDispatch.SuffixAt destination (entry + 47) (rowLayout n base) literal := by
  intro phase lower upper
  change 5 ≤ phase.val at lower
  change phase.val < 24 at upper
  have fetched := present ⟨47 + phase.val, by have := phase.isLt; omega⟩
  fin_cases phase <;>
    simp_all [rowCode, testCode, pairCode, readMarksCode, dispatchCode, writeMarkCode, Nat.add_assoc, literalCode, polarity]
  all_goals (norm_num at lower <;> norm_num at upper)

def TestAt (destination : Program width 8) (entry cursorHeader startHeader exit : Nat) : Prop :=
  ∀ phase : Fin 6, destination[entry + phase.val]? =
    some (testCode width cursorHeader startHeader exit)[phase.val]

def testPrepared (state : State width 8) (cursorHeader startHeader pointer start : Nat) : State width 8 :=
  let s1 := state.advance.put 0 (word width cursorHeader)
  let s2 := s1.advance.put 0 (word width pointer)
  let s3 := s2.advance.put 4 (word width startHeader)
  let s4 := s3.advance.put 4 (word width start)
  s4.advance.put 1 (word width (Nat.xor pointer start))

def testFinished (state : State width 8) (cursorHeader startHeader pointer start exit : Nat) : State width 8 :=
  let ready := testPrepared state cursorHeader startHeader pointer start
  if pointer = start then { ready.advance with pc := word width exit } else ready.advance

theorem testFinished_frame (state : State width 8) (cursorHeader startHeader pointer start exit : Nat) :
    (∀ register : Fin 8, register ≠ 0 → register ≠ 1 → register ≠ 4 →
      (testFinished state cursorHeader startHeader pointer start exit).reg register = state.reg register) ∧
    (testFinished state cursorHeader startHeader pointer start exit).heap = state.heap ∧
    (testFinished state cursorHeader startHeader pointer start exit).stack = state.stack ∧
    (testFinished state cursorHeader startHeader pointer start exit).output = state.output ∧
    (testFinished state cursorHeader startHeader pointer start exit).halted = state.halted := by
  by_cases equal : pointer = start <;>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
  all_goals try simp [testFinished, testPrepared, equal, State.put, State.advance]
  all_goals
    intro register address comparison first
    simp [testFinished, testPrepared, equal, State.put, State.advance, address, comparison, first]

theorem test_execution (destination : Program width 8) (entry cursorHeader startHeader pointer start exit : Nat)
    (present : TestAt destination entry cursorHeader startHeader exit)
    (state : State width 8) (cursor : CursorStored pointer cursorHeader state.heap)
    (first : CursorStored start startHeader state.heap) (position : state.pc = word width entry)
    (running : state.halted = false) (capacity : entry + 6 < 2 ^ width)
    (heapFits : state.heap.size < 2 ^ width) (pointerFits : pointer < 2 ^ width) (startFits : start < 2 ^ width) :
    Execution destination state (testFinished state cursorHeader startHeader pointer start exit) 6 state.liveWords := by
  let s1 := state.advance.put 0 (word width cursorHeader)
  let s2 := s1.advance.put 0 (word width pointer)
  let s3 := s2.advance.put 4 (word width startHeader)
  let s4 := s3.advance.put 4 (word width start)
  let s5 := s4.advance.put 1 (word width (Nat.xor pointer start))
  have headerFits : cursorHeader < 2 ^ width := cursor.bound.trans heapFits
  have firstHeaderFits : startHeader < 2 ^ width := first.bound.trans heapFits
  have p1 : s1.pc = word width (entry + 1) := by
    simpa [s1, State.put] using next_position state entry position (by omega)
  have p2 : s2.pc = word width (entry + 2) := by
    simpa [s2, State.put, Nat.add_assoc] using next_position s1 (entry + 1) p1 (by omega)
  have p3 : s3.pc = word width (entry + 3) := by
    simpa [s3, State.put, Nat.add_assoc] using next_position s2 (entry + 2) p2 (by omega)
  have p4 : s4.pc = word width (entry + 4) := by
    simpa [s4, State.put, Nat.add_assoc] using next_position s3 (entry + 3) p3 (by omega)
  have p5 : s5.pc = word width (entry + 5) := by
    simpa [s5, State.put, Nat.add_assoc] using next_position s4 (entry + 4) p4 (by omega)
  have fetched (phase : Fin 6) (current : State width 8)
      (pc : current.pc = word width (entry + phase.val)) :
      destination[current.pc.val]? = some (testCode width cursorHeader startHeader exit)[phase.val] := by
    rw [pc, word_val (width := width) (entry + phase.val) (by have := phase.isLt; omega)]
    exact present phase
  have t1 : programStep destination state = some s1 :=
    constant_step destination state 0 (word width cursorHeader) running
      (by simpa [testCode] using fetched ⟨0, by decide⟩ state (by simpa using position))
  have t2 : programStep destination s1 = some s2 := by
    apply load_step destination s1 0 cursorHeader cursor.bound
      (by simp only [s1, State.put, ite_true]; exact word_val (width := width) _ headerFits)
      (word width pointer) cursor.value running
    simpa [testCode] using fetched ⟨1, by decide⟩ s1 p1
  have t3 : programStep destination s2 = some s3 :=
    constant_step destination s2 4 (word width startHeader) running
      (by simpa [testCode] using fetched ⟨2, by decide⟩ s2 p2)
  have t4 : programStep destination s3 = some s4 := by
    have read : destination[s3.pc.val]? = some (.load 4 4) := by
      simpa [testCode] using fetched ⟨3, by decide⟩ s3 p3
    unfold programStep
    rw [read]
    change step (.load 4 4) s3 = _
    have points : (s3.reg 4).val = startHeader := by
      simp only [s3, State.put, ite_true]
      exact word_val (width := width) _ firstHeaderFits
    simp only [step, show s3.halted = false from running, Bool.false_eq_true, ite_false, points]
    have bound : startHeader < s3.heap.size := first.bound
    rw [dite_eq_left bound]
    change some (s3.advance.put 4 (state.heap[startHeader]'first.bound)) = some s4
    rw [first.value]
  have t5 : programStep destination s4 = some s5 := by
    have read : destination[s4.pc.val]? = some (.xor 1 0 4) := by
      simpa [testCode] using fetched ⟨4, by decide⟩ s4 p4
    unfold programStep
    rw [read]
    change step (.xor 1 0 4) s4 = _
    have pointerHeld : s4.reg 0 = word width pointer := by simp [s4, s3, s2, State.put, State.advance]
    have startHeld : s4.reg 4 = word width start := rfl
    simp only [step, show s4.halted = false from running, Bool.false_eq_true, ite_false, pointerHeld, startHeld,
      word_val (width := width) pointer pointerFits, word_val (width := width) start startFits]
    rfl
  have t6 : programStep destination s5 = some (testFinished state cursorHeader startHeader pointer start exit) := by
    have read : destination[s5.pc.val]? = some (.branchZero 1 (word width exit)) := by
      simpa [testCode] using fetched ⟨5, by decide⟩ s5 p5
    unfold programStep
    rw [read]
    change step (.branchZero 1 (word width exit)) s5 = _
    have xorFits := Nat.xor_lt_two_pow pointerFits startFits
    have held : s5.reg 1 = word width (Nat.xor pointer start) := rfl
    simp only [step, show s5.halted = false from running, Bool.false_eq_true, ite_false, held,
      word_val (width := width) (Nat.xor pointer start) xorFits]
    simp only [ResetPointer.xor_zero_iff]
    by_cases equal : pointer = start <;>
      simp [equal, testFinished, testPrepared, s5, s4, s3, s2, s1]
  have trace := Execution.cons t1 (Execution.cons t2 (Execution.cons t3
    (Execution.cons t4 (Execution.cons t5 (Execution.cons t6
      (Execution.refl (testFinished state cursorHeader startHeader pointer start exit)))))))
  by_cases equal : pointer = start <;>
    simpa [equal, testFinished, testPrepared, s5, s4, s3, s2, s1, State.put, State.advance, State.liveWords] using trace

theorem testFinished_position (state : State width 8) (cursorHeader startHeader pointer start exit entry : Nat)
    (position : state.pc = word width entry) (capacity : entry + 6 < 2 ^ width) :
    (testFinished state cursorHeader startHeader pointer start exit).pc =
      word width (if pointer = start then exit else entry + 6) := by
  by_cases equal : pointer = start
  · simp [testFinished, equal]
  · simp only [testFinished, testPrepared, equal, ite_false, State.advance, State.put,
      position, Nat.add_assoc, Nat.reduceAdd,
      word_val (width := width) entry (by omega),
      word_val (width := width) (entry + 1) (by omega),
      word_val (width := width) (entry + 2) (by omega),
      word_val (width := width) (entry + 3) (by omega),
      word_val (width := width) (entry + 4) (by omega),
      word_val (width := width) (entry + 5) (by omega)]

theorem row_test_at (destination : Program width 8) (entry n base cursorHeader startHeader exit : Nat)
    (present : RowAt destination entry n base cursorHeader startHeader exit) :
    TestAt destination entry cursorHeader startHeader exit := by
  intro phase
  have fetched := present ⟨phase.val, by have := phase.isLt; omega⟩
  fin_cases phase <;>
    simpa [rowCode, testCode, pairCode, readMarksCode, dispatchCode, writeMarkCode, Nat.add_assoc] using fetched

theorem row_return_fetch (destination : Program width 8) (entry n base cursorHeader startHeader exit : Nat)
    (present : RowAt destination entry n base cursorHeader startHeader exit) (positive : Bool)
    (state : State width 8) (position : state.pc = word width (entry + if positive then 45 else 76))
    (capacity : entry + 77 < 2 ^ width) :
    destination[state.pc.val]? = some (.branchZero 2 (word width entry)) := by
  cases sign : positive
  · have fetched := present ⟨76, by decide⟩
    rw [position, ite_eq_right (by simp [sign]), word_val (width := width) (entry + 76) (by omega)]
    simpa [rowCode, testCode, pairCode, readMarksCode, dispatchCode, writeMarkCode, Nat.add_assoc] using fetched
  · have fetched := present ⟨45, by decide⟩
    rw [position, ite_eq_left (by simp [sign]), word_val (width := width) (entry + 45) (by omega)]
    simpa [rowCode, testCode, pairCode, readMarksCode, dispatchCode, writeMarkCode, Nat.add_assoc] using fetched

theorem return_execution (destination : Program width 8) (entry : Nat) (state : State width 8)
    (fetched : destination[state.pc.val]? = some (.branchZero 2 (word width entry)))
    (zero : state.reg 2 = word width 0) (running : state.halted = false) :
    Execution destination state { state.advance with pc := word width entry } 1 state.liveWords := by
  have transition : programStep destination state = some { state.advance with pc := word width entry } := by
    unfold programStep
    rw [fetched]
    change step (.branchZero 2 (word width entry)) state = _
    simp [step, running, zero, word]
  simpa [State.advance, State.liveWords] using
    Execution.cons transition (Execution.refl { state.advance with pc := word width entry })

structure Separation (clause : CNF.Clause (Fin n)) (start cursorHeader startHeader base : Nat) : Prop where
  sourceBefore : start + 2 * clause.length ≤ base
  cursorBefore : cursorHeader < base
  firstBefore : startHeader < base
  headersDifferent : cursorHeader ≠ startHeader
  cursorOutside : cursorHeader < start ∨ start + 2 * clause.length ≤ cursorHeader

theorem CursorStored.after_store {pointer header : Nat} {heap : Array (Word width)}
    (stored : CursorStored pointer header heap) (index : Nat) (bound : index < heap.size)
    (value : Word width) (different : index ≠ header) :
    CursorStored pointer header (heap.set index value bound) := by
  refine ⟨by simpa using stored.bound, ?_⟩
  exact (Array.getElem_set_ne bound stored.bound different).trans stored.value

theorem Invariant.after_test {clause : CNF.Clause (Fin n)} {row : Row n}
    {start cursorHeader startHeader base positiveCursor negativeCursor touchedCursor k : Nat}
    {state : State width 8}
    (invariant : Invariant clause row start cursorHeader startHeader base
      positiveCursor negativeCursor touchedCursor k state) (pointer exit : Nat) :
    Invariant clause row start cursorHeader startHeader base positiveCursor negativeCursor touchedCursor k
      (testFinished state cursorHeader startHeader pointer start exit) := by
  have frame := testFinished_frame state cursorHeader startHeader pointer start exit
  refine ⟨invariant.indexBound, ?_, ?_, ?_, ?_, invariant.correct, ?_, ?_, ?_, ?_⟩
  · simpa only [frame.2.1] using invariant.source
  · simpa only [frame.2.1] using invariant.cursor
  · simpa only [frame.2.1] using invariant.first
  · simpa only [frame.2.1] using invariant.rowStored
  · exact (frame.1 2 (by decide) (by decide) (by decide)).trans invariant.zero
  · exact (frame.1 5 (by decide) (by decide) (by decide)).trans invariant.trueHeld
  · exact (frame.1 6 (by decide) (by decide) (by decide)).trans invariant.decrement
  · exact frame.2.2.2.2.trans invariant.running

/-- One real cursor-loop iteration processes one original stored occurrence.
The logical suffix index falls by one; the program contains no such counter. -/
theorem row_iteration (destination : Program width 8) (entry base cursorHeader startHeader start exit : Nat)
    (clause : CNF.Clause (Fin n)) (present : RowAt destination entry n base cursorHeader startHeader exit)
    (separate : Separation clause start cursorHeader startHeader base)
    (row : Row n) (state : State width 8) (positiveCursor negativeCursor touchedCursor k : Nat)
    (invariant : Invariant clause row start cursorHeader startHeader base
      positiveCursor negativeCursor touchedCursor (k + 1) state)
    (position : state.pc = word width entry) (capacity : entry + 77 < 2 ^ width)
    (heapFits : state.heap.size < 2 ^ width) :
    ∃ next : State width 8, ∃ ticks : Nat,
      Execution destination state next ticks state.liveWords ∧
      Invariant clause (row.record (clause[k]'(by have := invariant.indexBound; omega)))
        start cursorHeader startHeader base
        (positiveNext row (clause[k]'(by have := invariant.indexBound; omega)) positiveCursor)
        (negativeNext row (clause[k]'(by have := invariant.indexBound; omega)) negativeCursor)
        (touchedNext row (clause[k]'(by have := invariant.indexBound; omega)) touchedCursor) k next ∧
      next.pc = word width entry ∧ next.liveWords = state.liveWords ∧ next.heap.size = state.heap.size ∧ ticks ≤ 42 := by
  have bound : k < clause.length := by have := invariant.indexBound; omega
  let literal := clause[k]'bound
  let tested := testFinished state cursorHeader startHeader (start + 2 * (k + 1)) start exit
  have different : start + 2 * (k + 1) ≠ start := by omega
  have pointerFits : start + 2 * (k + 1) < 2 ^ width := by
    have := invariant.source.fits
    have := invariant.indexBound
    omega
  have startFits : start < 2 ^ width := by have := invariant.source.fits; omega
  have testTrace := test_execution destination entry cursorHeader startHeader (start + 2 * (k + 1)) start exit
    (row_test_at destination entry n base cursorHeader startHeader exit present) state invariant.cursor invariant.first
    position invariant.running (by omega) heapFits pointerFits startFits
  have testedInvariant := invariant.after_test (start + 2 * (k + 1)) exit
  have testedFrame := testFinished_frame state cursorHeader startHeader (start + 2 * (k + 1)) start exit
  have testedHeap : tested.heap = state.heap := testedFrame.2.1
  have testedSize : tested.heap.size = state.heap.size := by rw [testedHeap]
  have testedLive : tested.liveWords = state.liveWords := by
    simp [tested, testFinished, testPrepared, different, State.put, State.advance, State.liveWords]
  have testedPosition : tested.pc = word width (entry + 6) := by
    simpa [tested, different] using testFinished_position state cursorHeader startHeader
      (start + 2 * (k + 1)) start exit entry position (by omega)
  have cursor : CursorStored (start + 2 * k + 2) cursorHeader tested.heap := by
    simpa [tested, Nat.mul_add, Nat.add_assoc] using testedInvariant.cursor
  have pair : PairStored literal (start + 2 * k) tested.heap := testedInvariant.source.entry ⟨k, bound⟩
  have readPresent : ReadMarksAt destination (if literal.2 then entry + 6 + 10 else entry + 46) base literal.2 := by
    cases polarity : literal.2
    · simpa [polarity] using row_negative_read_at destination entry n base cursorHeader startHeader exit present
    · simpa [polarity, Nat.add_assoc] using row_positive_read_at destination entry n base cursorHeader startHeader exit present
  have suffixPresent : SuffixDispatch.SuffixAt destination
      ((if literal.2 then entry + 6 + 10 else entry + 46) + 1) (rowLayout n base) literal := by
    cases polarity : literal.2
    · simpa [polarity, Nat.add_assoc] using row_negative_suffix_at destination entry base cursorHeader startHeader exit literal polarity present
    · simpa [polarity, Nat.add_assoc] using row_positive_suffix_at destination entry base cursorHeader startHeader exit literal polarity present
  have writePresent : WriteMarkAt destination
      ((if literal.2 then entry + 6 + 10 else entry + 46) + 25) base literal.2 := by
    cases polarity : literal.2
    · simpa [polarity, Nat.add_assoc] using row_negative_write_at destination entry n base cursorHeader startHeader exit present
    · simpa [polarity, Nat.add_assoc] using row_positive_write_at destination entry n base cursorHeader startHeader exit present
  obtain ⟨recorded, recordTrace, recordStored, recordControl, recordPosition, recordLive, recordSize,
    recordFrame, recordCursor, cost⟩ :=
    physical_record_execution destination (entry + 6) cursorHeader (start + 2 * k) (entry + 46) base literal
      (row_pair_at destination entry n base cursorHeader startHeader exit present) readPresent suffixPresent writePresent
      (clause.drop (k + 1)) row testedInvariant.correct tested positiveCursor negativeCursor touchedCursor
      testedInvariant.rowStored cursor pair separate.cursorBefore testedPosition testedInvariant.zero
      testedInvariant.trueHeld testedInvariant.decrement testedInvariant.running (by omega)
      (by cases polarity : literal.2 <;> simp [polarity, Nat.add_assoc] <;> omega)
      (by simpa only [testedSize] using heapFits)
  have returnPosition : recorded.pc = word width (entry + if literal.2 then 45 else 76) := by
    cases polarity : literal.2 <;> simpa [polarity, Nat.add_assoc] using recordPosition
  let next : State width 8 := { recorded.advance with pc := word width entry }
  have returnTrace := return_execution destination entry recorded
    (row_return_fetch destination entry n base cursorHeader startHeader exit present literal.2 recorded returnPosition capacity)
    recordControl.zero recordControl.running
  have updatedSource := testedInvariant.source.after_store cursorHeader cursor.bound (word width (start + 2 * k)) separate.cursorOutside
  have preservedSource := updatedSource.of_low_frame separate.sourceBefore
    (by simpa using recordSize) recordFrame
  have updatedFirst := CursorStored.after_store testedInvariant.first cursorHeader cursor.bound (word width (start + 2 * k)) separate.headersDifferent
  have preservedFirst := CursorStored.of_low_frame updatedFirst separate.firstBefore (by simpa using recordSize) recordFrame
  have nextInvariant : Invariant clause (row.record literal) start cursorHeader startHeader base
      (positiveNext row literal positiveCursor) (negativeNext row literal negativeCursor)
      (touchedNext row literal touchedCursor) k next := by
    refine ⟨by omega, preservedSource, recordCursor, preservedFirst, recordStored,
      correct_record_drop clause row k bound invariant.correct,
      recordControl.zero, recordControl.trueHeld, recordControl.decrement, recordControl.running⟩
  have allTrace := (testTrace.append recordTrace).append returnTrace
  refine ⟨next, 6 + (10 + dynamicTicks (row.marks.read literal) (row.marks.read (CNF.negate literal)) literal.2) + 1,
    ?_, nextInvariant, rfl, ?_, ?_, by omega⟩
  · simpa only [testedLive, recordLive, Nat.max_self] using allTrace
  · have : next.liveWords = recorded.liveWords := rfl
    exact this.trans (recordLive.trans testedLive)
  · exact recordSize.trans testedSize

/-- Actual backwards traversal of all remaining source occurrences. The
induction index lives only in this proof; runtime termination reads the two
stored pointer headers on every visit. Source duplicates are never skipped. -/
theorem row_loop_execution (destination : Program width 8) (entry base cursorHeader startHeader start exit : Nat)
    (clause : CNF.Clause (Fin n)) (present : RowAt destination entry n base cursorHeader startHeader exit)
    (separate : Separation clause start cursorHeader startHeader base)
    (remaining : Nat) (row : Row n) (state : State width 8)
    (positiveCursor negativeCursor touchedCursor : Nat)
    (invariant : Invariant clause row start cursorHeader startHeader base
      positiveCursor negativeCursor touchedCursor remaining state)
    (position : state.pc = word width entry) (capacity : entry + 77 < 2 ^ width)
    (heapFits : state.heap.size < 2 ^ width) :
    ∃ final : State width 8, ∃ result : Row n, ∃ positive negative touched ticks : Nat,
      Execution destination state final ticks state.liveWords ∧
      Invariant clause result start cursorHeader startHeader base positive negative touched 0 final ∧
      final.pc = word width exit ∧ final.liveWords = state.liveWords ∧ final.heap.size = state.heap.size ∧
      ticks ≤ 42 * remaining + 6 := by
  induction remaining generalizing row state positiveCursor negativeCursor touchedCursor with
  | zero =>
    let final := testFinished state cursorHeader startHeader start start exit
    have startFits : start < 2 ^ width := by have := invariant.source.fits; omega
    have cursor : CursorStored start cursorHeader state.heap := by simpa using invariant.cursor
    have trace := test_execution destination entry cursorHeader startHeader start start exit
      (row_test_at destination entry n base cursorHeader startHeader exit present) state cursor invariant.first
      position invariant.running (by omega) heapFits startFits startFits
    have finalInvariant := invariant.after_test start exit
    have finalPosition : final.pc = word width exit := by simp [final, testFinished]
    have finalLive : final.liveWords = state.liveWords := by
      simp [final, testFinished, testPrepared, State.put, State.advance, State.liveWords]
    have finalSize : final.heap.size = state.heap.size := by
      simp [final, testFinished, testPrepared, State.put, State.advance]
    exact ⟨final, row, positiveCursor, negativeCursor, touchedCursor, 6,
      trace, finalInvariant, finalPosition, finalLive, finalSize, by omega⟩
  | succ remaining ih =>
    obtain ⟨middle, used, firstTrace, middleInvariant, middlePosition, middleLive, middleSize, usedBound⟩ :=
      row_iteration destination entry base cursorHeader startHeader start exit clause present separate
        row state positiveCursor negativeCursor touchedCursor remaining invariant position capacity heapFits
    have bound : remaining < clause.length := by have := invariant.indexBound; omega
    let literal := clause[remaining]'bound
    obtain ⟨final, result, positive, negative, touched, ticks, restTrace, finalInvariant,
      finalPosition, finalLive, finalSize, ticksBound⟩ :=
      ih (row.record literal) middle (positiveNext row literal positiveCursor)
        (negativeNext row literal negativeCursor) (touchedNext row literal touchedCursor)
        middleInvariant middlePosition (by simpa only [middleSize] using heapFits)
    refine ⟨final, result, positive, negative, touched, used + ticks, ?_, finalInvariant,
      finalPosition, finalLive.trans middleLive, finalSize.trans middleSize, by omega⟩
    simpa only [middleLive, Nat.max_self] using firstTrace.append restTrace

/-- A represented complete source row is normalized by the same fixed loop;
its final semantic row agrees with the full original clause. -/
theorem normalize_row_execution (destination : Program width 8)
    (entry base cursorHeader startHeader start exit : Nat) (clause : CNF.Clause (Fin n))
    (present : RowAt destination entry n base cursorHeader startHeader exit)
    (separate : Separation clause start cursorHeader startHeader base)
    (row : Row n) (state : State width 8) (positiveCursor negativeCursor touchedCursor : Nat)
    (invariant : Invariant clause row start cursorHeader startHeader base
      positiveCursor negativeCursor touchedCursor clause.length state)
    (position : state.pc = word width entry) (capacity : entry + 77 < 2 ^ width)
    (heapFits : state.heap.size < 2 ^ width) :
    ∃ final : State width 8, ∃ result : Row n, ∃ positive negative touched ticks : Nat,
      Execution destination state final ticks state.liveWords ∧
      RowStored result base positive negative touched final.heap ∧ result.Correct clause ∧
      CursorStored start cursorHeader final.heap ∧ final.pc = word width exit ∧
      final.liveWords = state.liveWords ∧ final.heap.size = state.heap.size ∧ ticks ≤ 42 * clause.length + 6 := by
  obtain ⟨final, result, positive, negative, touched, ticks, trace, finalInvariant,
    finalPosition, finalLive, finalSize, bound⟩ :=
    row_loop_execution destination entry base cursorHeader startHeader start exit clause present separate
      clause.length row state positiveCursor negativeCursor touchedCursor invariant position capacity heapFits
  exact ⟨final, result, positive, negative, touched, ticks, trace, finalInvariant.rowStored,
    by simpa using finalInvariant.correct, by simpa using finalInvariant.cursor,
    finalPosition, finalLive, finalSize, bound⟩

end Controller.Horn.RowScan
