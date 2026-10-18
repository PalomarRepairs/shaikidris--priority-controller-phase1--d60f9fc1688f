module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Horn.ResetReuse

public import Mathlib.Tactic.FinCases

@[expose] public section

/-!
# Fetched scratch-header restoration

Cursor restoration writes the three allocated buffer endpoints into their
physical headers. The tautology header is cleared from the caller's actual
zero register. The routine is used after the normalized rule is copied.
-/
namespace Controller.Horn.HeaderReuse

open Controller.Cost Controller.Horn.Worklist.IndexedNormalize

private theorem word_val (value : Nat) (fits : value < 2 ^ width) :
    (word width value).val = value := Nat.mod_eq_of_lt fits

private theorem advance_position (state : State width 8) (entry : Nat)
    (position : state.pc = word width entry) (fits : entry < 2 ^ width) :
    state.advance.pc = word width (entry + 1) := by
  simp only [State.advance, position, word_val (width := width) entry fits]

def cursorCode (width header value : Nat) : Program width 8 :=
  #[.constant 0 (word width header), .constant 4 (word width value), .store 0 4]

@[simp] theorem cursorCode_size (width header value : Nat) :
    (cursorCode width header value).size = 3 := rfl

def CursorAt (program : Program width 8) (entry header value : Nat) : Prop :=
  ∀ phase : Fin 3, program[entry + phase.val]? = some ((cursorCode width header value)[phase.val])

def cursorFinished (state : State width 8) (header value : Nat) (bound : header < state.heap.size) : State width 8 :=
  let s1 := state.advance.put 0 (word width header)
  let s2 := s1.advance.put 4 (word width value)
  { s2.advance with heap := state.heap.set header (word width value) bound }

/-- The restored cursor is written by three genuine fetched instructions. -/
theorem cursor_execution (program : Program width 8) (entry header value : Nat)
    (present : CursorAt program entry header value) (state : State width 8)
    (bound : header < state.heap.size) (position : state.pc = word width entry)
    (running : state.halted = false) (capacity : entry + 3 < 2 ^ width)
    (heapFits : state.heap.size < 2 ^ width) :
    Execution program state (cursorFinished state header value bound) 3 state.liveWords := by
  let s1 := state.advance.put 0 (word width header)
  let s2 := s1.advance.put 4 (word width value)
  let s3 := cursorFinished state header value bound
  have p1 : s1.pc = word width (entry + 1) := advance_position state entry position (by omega)
  have p2 : s2.pc = word width (entry + 2) := by
    simpa [s2, State.put, Nat.add_assoc] using advance_position s1 (entry + 1) p1 (by omega)
  have t1 : programStep program state = some s1 := by
    have read : program[state.pc.val]? = some (.constant 0 (word width header)) := by
      rw [position, word_val (width := width) entry (by omega)]
      simpa [cursorCode] using present 0
    unfold programStep
    rw [read]
    change step (.constant 0 (word width header)) state = _
    simp [step, running, s1]
  have t2 : programStep program s1 = some s2 := by
    have read : program[s1.pc.val]? = some (.constant 4 (word width value)) := by
      rw [p1, word_val (width := width) (entry + 1) (by omega)]
      simpa [cursorCode] using present 1
    unfold programStep
    rw [read]
    change step (.constant 4 (word width value)) s1 = _
    simp [step, s2, s1, State.put, State.advance, running]
  have t3 : programStep program s2 = some s3 := by
    have read : program[s2.pc.val]? = some (.store 0 4) := by
      rw [p2, word_val (width := width) (entry + 2) (by omega)]
      simpa [cursorCode] using present 2
    unfold programStep
    rw [read]
    change step (.store 0 4) s2 = _
    have address : (s2.reg 0).val = header := by
      simp [s2, s1, State.put, State.advance, word_val (width := width) header (bound.trans heapFits)]
    have held : s2.reg 4 = word width value := by simp [s2, State.put]
    have storeBound : header < s2.heap.size := bound
    simp only [step, show s2.halted = false from running, Bool.false_eq_true, ite_false,
      address, dite_eq_left storeBound, held]
    rfl
  have trace := Execution.cons t1 (Execution.cons t2 (Execution.cons t3 (Execution.refl s3)))
  simpa [s3, cursorFinished, s2, s1, State.liveWords, State.put, State.advance] using trace

theorem cursorFinished_frame (state : State width 8) (header value : Nat) (bound : header < state.heap.size) :
    (∀ register : Fin 8, register ≠ 0 → register ≠ 4 →
      (cursorFinished state header value bound).reg register = state.reg register) ∧
    (cursorFinished state header value bound).heap = state.heap.set header (word width value) bound ∧
    (cursorFinished state header value bound).stack = state.stack ∧
    (cursorFinished state header value bound).output = state.output ∧
    (cursorFinished state header value bound).halted = state.halted := by
  refine ⟨?_, rfl, rfl, rfl, rfl⟩
  intro register address count
  simp [cursorFinished, State.put, State.advance, address, count]

theorem cursorFinished_position (state : State width 8) (entry header value : Nat)
    (bound : header < state.heap.size) (position : state.pc = word width entry)
    (capacity : entry + 3 < 2 ^ width) :
    (cursorFinished state header value bound).pc = word width (entry + 3) := by
  simp only [cursorFinished, State.put, State.advance, position,
    word_val (width := width) entry (by omega), word_val (width := width) (entry + 1) (by omega),
    word_val (width := width) (entry + 2) (by omega), Nat.add_assoc, Nat.reduceAdd]

/-- The full routine supplies each cursor store as an actual fetched slice. -/
theorem positive_at (program : Program width 8) (entry base : Nat)
    (present : Controller.Horn.ResetReuse.HeaderAt program entry n base) :
    CursorAt program entry (base + 2 * n) (base + 3 * n + 4) := by
  intro phase
  have fetched := present ⟨phase.val, by have := phase.isLt; omega⟩
  fin_cases phase <;> simpa [Controller.Horn.ResetReuse.headerCode, cursorCode] using fetched

theorem negative_at (program : Program width 8) (entry base : Nat)
    (present : Controller.Horn.ResetReuse.HeaderAt program entry n base) :
    CursorAt program (entry + 3) (base + 2 * n + 1) (base + 4 * n + 4) := by
  intro phase
  have fetched := present ⟨3 + phase.val, by have := phase.isLt; omega⟩
  fin_cases phase <;> simpa [Controller.Horn.ResetReuse.headerCode, cursorCode, Nat.add_assoc] using fetched

theorem touched_at (program : Program width 8) (entry base : Nat)
    (present : Controller.Horn.ResetReuse.HeaderAt program entry n base) :
    CursorAt program (entry + 6) (base + 2 * n + 2) (base + 5 * n + 4) := by
  intro phase
  have fetched := present ⟨6 + phase.val, by have := phase.isLt; omega⟩
  fin_cases phase <;> simpa [Controller.Horn.ResetReuse.headerCode, cursorCode, Nat.add_assoc] using fetched

def ZeroAt (program : Program width 8) (entry header : Nat) : Prop :=
  program[entry]? = some (.constant 0 (word width header)) ∧
  program[entry + 1]? = some (.store 0 2)

def zeroFinished (state : State width 8) (header : Nat) (bound : header < state.heap.size) : State width 8 :=
  { (state.advance.put 0 (word width header)).advance with heap := state.heap.set header (word width 0) bound }

/-- Two fetched instructions clear the flag from the real zero register. -/
theorem zero_execution (program : Program width 8) (entry header : Nat)
    (present : ZeroAt program entry header) (state : State width 8)
    (bound : header < state.heap.size) (position : state.pc = word width entry)
    (zero : state.reg 2 = word width 0) (running : state.halted = false)
    (capacity : entry + 2 < 2 ^ width) (heapFits : state.heap.size < 2 ^ width) :
    Execution program state (zeroFinished state header bound) 2 state.liveWords := by
  let middle := state.advance.put 0 (word width header)
  have middlePC : middle.pc = word width (entry + 1) := advance_position state entry position (by omega)
  have first : programStep program state = some middle := by
    unfold programStep
    rw [position, word_val (width := width) entry (by omega), present.1]
    change step (.constant 0 (word width header)) state = _
    simp [step, middle, running]
  have second : programStep program middle = some (zeroFinished state header bound) := by
    unfold programStep
    rw [middlePC, word_val (width := width) (entry + 1) (by omega), present.2]
    change step (.store 0 2) middle = _
    have address : (middle.reg 0).val = header := by
      simp [middle, State.put, word_val (width := width) header (bound.trans heapFits)]
    have held : middle.reg 2 = word width 0 := by simp [middle, State.put, State.advance, zero]
    have storeBound : header < middle.heap.size := bound
    simp only [step, show middle.halted = false from running, Bool.false_eq_true, ite_false,
      address, dite_eq_left storeBound, held]
    rfl
  have trace := Execution.cons first (Execution.cons second (Execution.refl (zeroFinished state header bound)))
  simpa [middle, zeroFinished, State.liveWords, State.put, State.advance] using trace

theorem flag_at (program : Program width 8) (entry base : Nat)
    (present : Controller.Horn.ResetReuse.HeaderAt program entry n base) :
    ZeroAt program (entry + 9) (base + 2 * n + 3) := by
  constructor
  · simpa [Controller.Horn.ResetReuse.headerCode] using present ⟨9, by decide⟩
  · simpa [Controller.Horn.ResetReuse.headerCode, Nat.add_assoc] using present ⟨10, by decide⟩

theorem zeroFinished_frame (state : State width 8) (header : Nat) (bound : header < state.heap.size) :
    (∀ register : Fin 8, register ≠ 0 → (zeroFinished state header bound).reg register = state.reg register) ∧
    (zeroFinished state header bound).heap = state.heap.set header (word width 0) bound ∧
    (zeroFinished state header bound).stack = state.stack ∧
    (zeroFinished state header bound).output = state.output ∧
    (zeroFinished state header bound).halted = state.halted := by
  refine ⟨?_, rfl, rfl, rfl, rfl⟩
  intro register address
  simp [zeroFinished, State.put, State.advance, address]

theorem zeroFinished_position (state : State width 8) (entry header : Nat)
    (bound : header < state.heap.size) (position : state.pc = word width entry)
    (capacity : entry + 2 < 2 ^ width) :
    (zeroFinished state header bound).pc = word width (entry + 2) := by
  simp only [zeroFinished, State.put, State.advance, position,
    word_val (width := width) entry (by omega), word_val (width := width) (entry + 1) (by omega), Nat.add_assoc, Nat.reduceAdd]

theorem cursorFinished_marks (state : State width 8) (header value base : Nat)
    (bound : header < state.heap.size) (marks : Marks n)
    (stored : Controller.Horn.MarkStorage.Stored marks base state.heap)
    (afterMarks : base + 2 * n ≤ header) :
    Controller.Horn.MarkStorage.Stored marks base (cursorFinished state header value bound).heap := by
  refine ⟨by simpa [cursorFinished] using stored.fits, ?_⟩
  intro literal
  have different : header ≠ Controller.Horn.MarkStorage.address base literal := by
    have := Controller.Horn.MarkStorage.address_lt base literal
    omega
  exact (Array.getElem_set_ne bound (stored.bound literal) different).trans (stored.entry literal)

theorem zeroFinished_marks (state : State width 8) (header base : Nat)
    (bound : header < state.heap.size) (marks : Marks n)
    (stored : Controller.Horn.MarkStorage.Stored marks base state.heap)
    (afterMarks : base + 2 * n ≤ header) :
    Controller.Horn.MarkStorage.Stored marks base (zeroFinished state header bound).heap := by
  refine ⟨by simpa [zeroFinished] using stored.fits, ?_⟩
  intro literal
  have different : header ≠ Controller.Horn.MarkStorage.address base literal := by
    have := Controller.Horn.MarkStorage.address_lt base literal
    omega
  exact (Array.getElem_set_ne bound (stored.bound literal) different).trans (stored.entry literal)

def HeaderFrame (n base : Nat) (before after : Array (Word width)) : Prop :=
  ∀ index : Nat, (index < base + 2 * n ∨ base + 2 * n + 4 ≤ index) → after[index]? = before[index]?

theorem HeaderFrame.trans {n base : Nat} {first middle last : Array (Word width)}
    (left : HeaderFrame n base first middle) (right : HeaderFrame n base middle last) :
    HeaderFrame n base first last := by
  intro index outside
  exact (right index outside).trans (left index outside)

theorem cursorFinished_heap_frame (state : State width 8) (header value base : Nat)
    (bound : header < state.heap.size) (inHeaders : base + 2 * n ≤ header ∧ header < base + 2 * n + 4) :
    HeaderFrame n base state.heap (cursorFinished state header value bound).heap := by
  intro index outside
  have different : header ≠ index := by rcases outside with before | after <;> omega
  exact Array.getElem?_set_ne bound different

theorem zeroFinished_heap_frame (state : State width 8) (header base : Nat)
    (bound : header < state.heap.size) (inHeaders : base + 2 * n ≤ header ∧ header < base + 2 * n + 4) :
    HeaderFrame n base state.heap (zeroFinished state header bound).heap := by
  intro index outside
  have different : header ≠ index := by rcases outside with before | after <;> omega
  exact Array.getElem?_set_ne bound different


/-- The entire physical header routine executes eleven fetched instructions.
Only the four scratch headers change; buffered labels and copied records remain.
-/
theorem headers_execution (program : Program width 8) (entry base : Nat)
    (present : Controller.Horn.ResetReuse.HeaderAt program entry n base)
    (state : State width 8) (marks : Marks n)
    (stored : Controller.Horn.MarkStorage.Stored marks base state.heap)
    (scratchFits : base + 5 * n + 4 ≤ state.heap.size)
    (position : state.pc = word width entry) (zero : state.reg 2 = word width 0)
    (running : state.halted = false) (capacity : entry + 11 < 2 ^ width)
    (heapFits : state.heap.size < 2 ^ width) :
    ∃ final : State width 8,
      Execution program state final 11 state.liveWords ∧
      Controller.Horn.MarkStorage.Stored marks base final.heap ∧
      HeaderFrame n base state.heap final.heap ∧
      final.heap[base + 2 * n]? = some (word width (base + 3 * n + 4)) ∧
      final.heap[base + 2 * n + 1]? = some (word width (base + 4 * n + 4)) ∧
      final.heap[base + 2 * n + 2]? = some (word width (base + 5 * n + 4)) ∧
      final.heap[base + 2 * n + 3]? = some (word width 0) ∧
      final.heap.size = state.heap.size ∧ final.pc = word width (entry + 11) ∧
      final.reg 2 = word width 0 ∧ final.reg 5 = state.reg 5 ∧
      final.reg 6 = state.reg 6 ∧ final.halted = false ∧
      final.stack = state.stack ∧ final.output = state.output := by
  have b0 : base + 2 * n < state.heap.size := by omega
  let a := cursorFinished state (base + 2 * n) (base + 3 * n + 4) b0
  have asize : a.heap.size = state.heap.size := by simp [a, cursorFinished]
  have b1 : base + 2 * n + 1 < a.heap.size := by omega
  let b := cursorFinished a (base + 2 * n + 1) (base + 4 * n + 4) b1
  have bsize : b.heap.size = state.heap.size := by simp [b, cursorFinished, asize]
  have b2 : base + 2 * n + 2 < b.heap.size := by omega
  let c := cursorFinished b (base + 2 * n + 2) (base + 5 * n + 4) b2
  have csize : c.heap.size = state.heap.size := by simp [c, cursorFinished, bsize]
  have b3 : base + 2 * n + 3 < c.heap.size := by omega
  let final := zeroFinished c (base + 2 * n + 3) b3
  have apc : a.pc = word width (entry + 3) := cursorFinished_position state entry _ _ b0 position (by omega)
  have bpc : b.pc = word width (entry + 6) := by
    simpa [b, Nat.add_assoc] using cursorFinished_position a (entry + 3) _ _ b1 apc (by omega)
  have cpc : c.pc = word width (entry + 9) := by
    simpa [c, Nat.add_assoc] using cursorFinished_position b (entry + 6) _ _ b2 bpc (by omega)
  have arun : a.halted = false := running
  have brun : b.halted = false := running
  have crun : c.halted = false := running
  have czero : c.reg 2 = word width 0 := by simp [c, b, a, cursorFinished, State.advance, State.put, zero]
  have t0 := cursor_execution program entry _ _ (positive_at program entry base present)
    state b0 position running (by omega) heapFits
  have t1 := cursor_execution program (entry + 3) _ _ (negative_at program entry base present)
    a b1 apc arun (by omega) (by omega)
  have t2 := cursor_execution program (entry + 6) _ _ (touched_at program entry base present)
    b b2 bpc brun (by omega) (by omega)
  have t3 := zero_execution program (entry + 9) _ (flag_at program entry base present)
    c b3 cpc czero crun (by omega) (by omega)
  have alive : a.liveWords = state.liveWords := by simp [a, cursorFinished, State.liveWords, State.advance, State.put]
  have blive : b.liveWords = state.liveWords := by simp [b, a, cursorFinished, State.liveWords, State.advance, State.put]
  have clive : c.liveWords = state.liveWords := by simp [c, b, a, cursorFinished, State.liveWords, State.advance, State.put]
  have trace := ((t0.append t1).append t2).append t3
  have amarks := cursorFinished_marks state (base + 2 * n) (base + 3 * n + 4) base b0 marks stored (by omega)
  have bmarks := cursorFinished_marks a (base + 2 * n + 1) (base + 4 * n + 4) base b1 marks amarks (by omega)
  have cmarks := cursorFinished_marks b (base + 2 * n + 2) (base + 5 * n + 4) base b2 marks bmarks (by omega)
  have fmarks := zeroFinished_marks c (base + 2 * n + 3) base b3 marks cmarks (by omega)
  have f0 := cursorFinished_heap_frame state (base + 2 * n) (base + 3 * n + 4) base b0 (n := n) (by omega)
  have f1 := cursorFinished_heap_frame a (base + 2 * n + 1) (base + 4 * n + 4) base b1 (n := n) (by omega)
  have f2 := cursorFinished_heap_frame b (base + 2 * n + 2) (base + 5 * n + 4) base b2 (n := n) (by omega)
  have f3 := zeroFinished_heap_frame c (base + 2 * n + 3) base b3 (n := n) (by omega)
  refine ⟨final, ?_, fmarks, ((f0.trans f1).trans f2).trans f3, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [alive, blive, clive] using trace
  · simp [final, c, b, a, zeroFinished, cursorFinished, Array.getElem?_set,
      show base + 2 * n + 3 ≠ base + 2 * n by omega,
      show base + 2 * n + 2 ≠ base + 2 * n by omega,
      show base + 2 * n + 1 ≠ base + 2 * n by omega]
  · simp [final, c, b, a, zeroFinished, cursorFinished, Array.getElem?_set,
      show base + 2 * n + 3 ≠ base + 2 * n + 1 by omega,
      show base + 2 * n + 2 ≠ base + 2 * n + 1 by omega]
  · simp [final, c, b, a, zeroFinished, cursorFinished, Array.getElem?_set,
      show base + 2 * n + 3 ≠ base + 2 * n + 2 by omega]
  · simp [final, zeroFinished, Array.getElem?_set]
  · simpa [final, zeroFinished] using csize
  · simpa [final, Nat.add_assoc] using zeroFinished_position c (entry + 9) _ b3 cpc (by omega)
  · simp [final, c, b, a, zeroFinished, cursorFinished, State.put, State.advance, zero, running]


/-- Empty buffers impose no condition on stale label cells. The restored cursor
words and cleared flag alone re-establish the complete row representation. -/
theorem empty_row_stored (marks : Marks n) (base : Nat) (heap : Array (Word width))
    (stored : Controller.Horn.MarkStorage.Stored marks base heap)
    (scratchFits : base + 5 * n + 4 ≤ heap.size)
    (positive : heap[base + 2 * n]? = some (word width (base + 3 * n + 4)))
    (negative : heap[base + 2 * n + 1]? = some (word width (base + 4 * n + 4)))
    (touched : heap[base + 2 * n + 2]? = some (word width (base + 5 * n + 4)))
    (flag : heap[base + 2 * n + 3]? = some (word width 0)) :
    Controller.Horn.LiteralDispatch.RowStored (Row.empty marks) base
      (base + 3 * n + 4) (base + 4 * n + 4) (base + 5 * n + 4) heap := by
  have b0 : base + 2 * n < heap.size := by omega
  have b1 : base + 2 * n + 1 < heap.size := by omega
  have b2 : base + 2 * n + 2 < heap.size := by omega
  have b3 : base + 2 * n + 3 < heap.size := by omega
  refine ⟨stored, ?_, ?_, ?_, b3, ?_⟩
  · refine ⟨Controller.Horn.LabelBuffer.empty_stored heap _ _ (by omega) (by omega), b0, Or.inl (by omega), ?_⟩
    simpa only [Array.getElem?_eq_getElem b0, Option.some.injEq] using positive
  · refine ⟨Controller.Horn.LabelBuffer.empty_stored heap _ _ (by omega) (by omega), b1, Or.inl (by omega), ?_⟩
    simpa only [Array.getElem?_eq_getElem b1, Option.some.injEq] using negative
  · refine ⟨Controller.Horn.LabelBuffer.empty_stored heap _ _ (by omega) (by omega), b2, Or.inl (by omega), ?_⟩
    simpa only [Array.getElem?_eq_getElem b2, Option.some.injEq] using touched
  · simpa [Array.getElem?_eq_getElem b3, Controller.Horn.MarkStorage.encode, Row.empty] using flag


/-- Restoring the physical headers re-establishes the complete scratch row in
exactly eleven instructions, without reallocating any buffer or record. -/
theorem restore_row_execution (program : Program width 8) (entry base : Nat)
    (present : Controller.Horn.ResetReuse.HeaderAt program entry n base)
    (state : State width 8) (marks : Marks n)
    (stored : Controller.Horn.MarkStorage.Stored marks base state.heap)
    (scratchFits : base + 5 * n + 4 ≤ state.heap.size)
    (position : state.pc = word width entry) (zero : state.reg 2 = word width 0)
    (running : state.halted = false) (capacity : entry + 11 < 2 ^ width)
    (heapFits : state.heap.size < 2 ^ width) :
    ∃ final : State width 8,
      Execution program state final 11 state.liveWords ∧
      Controller.Horn.LiteralDispatch.RowStored (Row.empty marks) base
        (base + 3 * n + 4) (base + 4 * n + 4) (base + 5 * n + 4) final.heap ∧
      HeaderFrame n base state.heap final.heap ∧
      final.heap.size = state.heap.size ∧ final.pc = word width (entry + 11) ∧
      final.reg 2 = word width 0 ∧ final.reg 5 = state.reg 5 ∧
      final.reg 6 = state.reg 6 ∧ final.halted = false ∧
      final.stack = state.stack ∧ final.output = state.output := by
  obtain ⟨final, trace, marksStored, frame, positive, negative, touched, flag,
    size, pc, control⟩ := headers_execution program entry base present state marks stored
      scratchFits position zero running capacity heapFits
  exact ⟨final, trace, empty_row_stored marks base final.heap marksStored (by omega)
    positive negative touched flag, frame, size, pc, control⟩


/-- Actual touched-label clearing followed by actual header restoration prepares
an empty correct row. This consumer is invoked after the rule record is copied.
-/
theorem reuse_row_execution (program : Program width 8) (entry base pcur ncur tcur : Nat)
    (setupAt : Controller.Horn.ResetPointer.SetupAt program entry (base + 2 * n + 2) base)
    (loopAt : Controller.Horn.ResetPointer.CodeAt program (entry + 3) (base + 5 * n + 4))
    (headersAt : Controller.Horn.ResetReuse.HeaderAt program (entry + 14) n base)
    (state : State width 8) (row : Row n) (clause : Controller.CNF.Clause (Fin n))
    (correct : row.Correct clause)
    (stored : Controller.Horn.LiteralDispatch.RowStored row base pcur ncur tcur state.heap)
    (position : state.pc = word width entry) (zero : state.reg 2 = word width 0)
    (one : state.reg 5 = Controller.Horn.MarkStorage.encode width true)
    (decrement : state.reg 6 = word width (2 ^ width - 1)) (running : state.halted = false)
    (capacity : entry + 25 < 2 ^ width) (heapFits : state.heap.size < 2 ^ width) :
    ∃ final : State width 8,
      Execution program state final (11 * row.touched.length + 17) state.liveWords ∧
      Controller.Horn.LiteralDispatch.RowStored (Row.empty (Marks.clear row.touched row.marks)) base
        (base + 3 * n + 4) (base + 4 * n + 4) (base + 5 * n + 4) final.heap ∧
      (Row.empty (Marks.clear row.touched row.marks)).Correct [] ∧
      (∀ index : Nat, (index < base ∨ base + 2 * n + 4 ≤ index) → final.heap[index]? = state.heap[index]?) ∧
      final.heap.size = state.heap.size ∧ final.pc = word width (entry + 25) ∧
      final.reg 2 = word width 0 ∧ final.reg 5 = Controller.Horn.MarkStorage.encode width true ∧
      final.reg 6 = word width (2 ^ width - 1) ∧ final.halted = false ∧
      final.stack = state.stack ∧ final.output = state.output := by
  obtain ⟨middle, resetTrace, cleared, middleSize, resetFrame, middleStack, middleOutput,
    middlePC, middleZero, middleOne, middleDecrement, middleRunning, middleLive⟩ :=
    Controller.Horn.ResetReuse.reset_execution program entry (base + 2 * n + 2) base
      tcur (base + 5 * n + 4) setupAt loopAt state row.marks row.touched stored.marks
      stored.touched.buffer.labels stored.touched.buffer.ends
      (by have := stored.touched.buffer.lower_le_cursor; omega)
      stored.touched.bound stored.touched.value position zero one decrement running (by omega) heapFits
  obtain ⟨final, headerTrace, emptyStored, headerFrame, size, pc, finalZero, finalOne,
    finalDecrement, finalRunning, finalStack, finalOutput⟩ :=
    restore_row_execution program (entry + 14) base headersAt middle
      (Marks.clear row.touched row.marks) cleared
      (by have := stored.scratch_fits; omega) middlePC middleZero middleRunning
      (by omega) (by omega)
  refine ⟨final, ?_, emptyStored, Row.empty_correct (Marks.clear row.touched row.marks) (Row.clear_clean correct), ?_,
    size.trans middleSize, ?_, finalZero, finalOne.trans middleOne,
    finalDecrement.trans middleDecrement, finalRunning,
    finalStack.trans middleStack, finalOutput.trans middleOutput⟩
  · have trace := resetTrace.append headerTrace
    simpa [middleLive, Nat.max_self, Nat.add_assoc] using trace
  · intro index outside
    have headerOutside : index < base + 2 * n ∨ base + 2 * n + 4 ≤ index := by
      rcases outside with before | after
      · exact Or.inl (by omega)
      · exact Or.inr after
    have resetOutside : index < base ∨ base + 2 * n ≤ index := by
      rcases outside with before | after
      · exact Or.inl before
      · exact Or.inr (by omega)
    exact (headerFrame index headerOutside).trans (resetFrame index resetOutside)
  · simpa [Nat.add_assoc] using pc

end Controller.Horn.HeaderReuse
