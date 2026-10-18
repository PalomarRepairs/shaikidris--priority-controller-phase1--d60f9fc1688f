module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Horn.RecordStorage

@[expose] public section

/-!
# Literal-dispatch code for the shared indexed normalizer

All retained-list cursors live in heap headers. A literal block reads both
polarity marks, records a fresh sign, records an opposite-sign conflict, records
a fresh touched channel, and finally sets the sign mark. Duplicate occurrences
remain input occurrences, with their list insertions skipped by machine branches.
Code is unrolled per input occurrence; program storage is linear in literal
incidences. Execution and complete row refinement are separate obligations.
-/
namespace Controller.Horn.NormalizeProgram

open Controller.Cost

structure Layout where
  markBase : Nat
  positiveHeader : Nat
  negativeHeader : Nat
  touchedHeader : Nat
  tautologyHeader : Nat

def Layout.signHeader (layout : Layout) (sign : Bool) : Nat :=
  if sign then layout.positiveHeader else layout.negativeHeader

/-- The zero and true constants are held in registers 2 and 5. Registers 1 and
7 retain the old same/opposite marks across every list update. Register 4 is the
reusable cursor. Labels are loaded in register 3; register 6 holds minus one. -/
def literalCode (width entry : Nat) (layout : Layout) (literal : CNF.Literal (Fin n)) : Program width 8 :=
  #[.constant 3 (word width literal.1.val),
    .constant 0 (word width (MarkStorage.address layout.markBase literal)),
    .load 1 0,
    .constant 0 (word width (MarkStorage.address layout.markBase (CNF.negate literal))),
    .load 7 0,
    .branchZero 1 (word width (entry + 7)),
    .branchZero 2 (word width (entry + 12)),
    .constant 0 (word width (layout.signHeader literal.2)),
    .load 4 0, .add 4 4 6, .store 4 3, .store 0 4,
    .branchZero 7 (word width (entry + 15)),
    .constant 0 (word width layout.tautologyHeader),
    .store 0 5,
    .branchZero 1 (word width (entry + 17)),
    .branchZero 2 (word width (entry + 24)),
    .branchZero 7 (word width (entry + 19)),
    .branchZero 2 (word width (entry + 24)),
    .constant 0 (word width layout.touchedHeader),
    .load 4 0, .add 4 4 6, .store 4 3, .store 0 4,
    .constant 0 (word width (MarkStorage.address layout.markBase literal)),
    .store 0 5]

@[simp] theorem literalCode_size (width entry : Nat) (layout : Layout)
    (literal : CNF.Literal (Fin n)) : (literalCode width entry layout literal).size = 26 := rfl

def LiteralAt (destination : Program width 8) (entry : Nat) (layout : Layout)
    (literal : CNF.Literal (Fin n)) : Prop :=
  ∀ phase : Fin 26,
    destination[entry + phase.val]? = some (literalCode width entry layout literal)[phase.val]

theorem signed_prepend_at (destination : Program width 8) (entry : Nat) (layout : Layout)
    (literal : CNF.Literal (Fin n)) (present : LiteralAt destination entry layout literal) :
    RecordStorage.CodeAt destination (entry + 8) := by
  intro phase
  have fetched := present ⟨8 + phase.val, by have := phase.isLt; omega⟩
  have cases : phase.val = 0 ∨ phase.val = 1 ∨ phase.val = 2 ∨ phase.val = 3 := by
    have := phase.isLt
    omega
  rcases cases with equal | equal | equal | equal <;>
    simpa [literalCode, RecordStorage.code, equal, Nat.add_assoc] using fetched

theorem touched_prepend_at (destination : Program width 8) (entry : Nat) (layout : Layout)
    (literal : CNF.Literal (Fin n)) (present : LiteralAt destination entry layout literal) :
    RecordStorage.CodeAt destination (entry + 20) := by
  intro phase
  have fetched := present ⟨20 + phase.val, by have := phase.isLt; omega⟩
  have cases : phase.val = 0 ∨ phase.val = 1 ∨ phase.val = 2 ∨ phase.val = 3 := by
    have := phase.isLt
    omega
  rcases cases with equal | equal | equal | equal <;>
    simpa [literalCode, RecordStorage.code, equal, Nat.add_assoc] using fetched

private theorem word_val (value : Nat) (fits : value < 2 ^ width) :
    (word width value).val = value := Nat.mod_eq_of_lt fits

theorem fetched (destination : Program width 8) (entry : Nat) (layout : Layout)
    (literal : CNF.Literal (Fin n)) (present : LiteralAt destination entry layout literal)
    (state : State width 8) (phase : Fin 26)
    (position : state.pc = word width (entry + phase.val))
    (capacity : entry + 26 < 2 ^ width) :
    destination[state.pc.val]? = some (literalCode width entry layout literal)[phase.val] := by
  rw [position, word_val (entry + phase.val) (by have := phase.isLt; omega)]
  exact present phase

private theorem constant_step (destination : Program width 8) (state : State width 8)
    (register : Fin 8) (value : Word width)
    (fetched : destination[state.pc.val]? = some (.constant register value))
    (running : state.halted = false) :
    programStep destination state = some (state.advance.put register value) := by
  simp only [programStep, fetched, step, running, Bool.false_eq_true, ite_false]
  rfl

private theorem advance_position (state : State width 8) (entry : Nat)
    (position : state.pc = word width entry) (fits : entry < 2 ^ width) :
    state.advance.pc = word width (entry + 1) := by
  simp only [State.advance, position, word_val entry fits]

/-- Machine state after the block has fetched the label and both polarity marks. -/
def readState (state : State width 8) (layout : Layout) (literal : CNF.Literal (Fin n))
    (marks : Worklist.IndexedNormalize.Marks n) : State width 8 :=
  let s1 := state.advance.put 3 (word width literal.1.val)
  let s2 := s1.advance.put 0 (word width (MarkStorage.address layout.markBase literal))
  let s3 := s2.advance.put 1 (MarkStorage.encode width (marks.read literal))
  let s4 := s3.advance.put 0 (word width (MarkStorage.address layout.markBase (CNF.negate literal)))
  s4.advance.put 7 (MarkStorage.encode width (marks.read (CNF.negate literal)))

@[simp] theorem readState_heap (state : State width 8) (layout : Layout)
    (literal : CNF.Literal (Fin n)) (marks : Worklist.IndexedNormalize.Marks n) :
    (readState state layout literal marks).heap = state.heap := rfl

@[simp] theorem readState_same (state : State width 8) (layout : Layout)
    (literal : CNF.Literal (Fin n)) (marks : Worklist.IndexedNormalize.Marks n) :
    (readState state layout literal marks).reg 1 = MarkStorage.encode width (marks.read literal) := by
  simp [readState, State.put, State.advance]

@[simp] theorem readState_opposite (state : State width 8) (layout : Layout)
    (literal : CNF.Literal (Fin n)) (marks : Worklist.IndexedNormalize.Marks n) :
    (readState state layout literal marks).reg 7 = MarkStorage.encode width (marks.read (CNF.negate literal)) := by
  simp [readState, State.put]

@[simp] theorem readState_label (state : State width 8) (layout : Layout)
    (literal : CNF.Literal (Fin n)) (marks : Worklist.IndexedNormalize.Marks n) :
    (readState state layout literal marks).reg 3 = word width literal.1.val := by
  simp [readState, State.put, State.advance]

theorem readState_frame (state : State width 8) (layout : Layout)
    (literal : CNF.Literal (Fin n)) (marks : Worklist.IndexedNormalize.Marks n) :
    (∀ register : Fin 8, register ≠ 0 → register ≠ 1 → register ≠ 3 → register ≠ 7 →
      (readState state layout literal marks).reg register = state.reg register) ∧
    (readState state layout literal marks).stack = state.stack ∧
    (readState state layout literal marks).output = state.output := by
  refine ⟨?_, rfl, rfl⟩
  intro register address same label opposite
  simp [readState, State.put, State.advance, address, same, label, opposite]

theorem readState_position (state : State width 8) (layout : Layout)
    (literal : CNF.Literal (Fin n)) (marks : Worklist.IndexedNormalize.Marks n)
    (entry : Nat) (position : state.pc = word width entry) (capacity : entry + 5 < 2 ^ width) :
    (readState state layout literal marks).pc = word width (entry + 5) := by
  simp only [readState, State.put, State.advance, position,
    word_val entry (by omega : entry < 2 ^ width),
    word_val (entry + 1) (by omega : entry + 1 < 2 ^ width),
    word_val (entry + 2) (by omega : entry + 2 < 2 ^ width),
    word_val (entry + 3) (by omega : entry + 3 < 2 ^ width),
    word_val (entry + 4) (by omega : entry + 4 < 2 ^ width), Nat.add_assoc]

/-- Five actual fetched instructions establish both branch flags from the
represented mark table. Labels and polarity addresses are literal immediates
in this specialized block; a fixed input scanner remains a separate refinement. -/
theorem read_marks_execution (destination : Program width 8) (entry : Nat) (layout : Layout)
    (literal : CNF.Literal (Fin n)) (present : LiteralAt destination entry layout literal)
    (state : State width 8) (marks : Worklist.IndexedNormalize.Marks n)
    (stored : MarkStorage.Stored marks layout.markBase state.heap)
    (position : state.pc = word width entry) (running : state.halted = false)
    (capacity : entry + 26 < 2 ^ width)
    (heapFits : state.heap.size ≤ 2 ^ width) :
    Execution destination state (readState state layout literal marks) 5 state.liveWords := by
  let s1 := state.advance.put 3 (word width literal.1.val)
  let s2 := s1.advance.put 0 (word width (MarkStorage.address layout.markBase literal))
  let s3 := s2.advance.put 1 (MarkStorage.encode width (marks.read literal))
  let s4 := s3.advance.put 0 (word width (MarkStorage.address layout.markBase (CNF.negate literal)))
  have p1 : s1.pc = word width (entry + 1) := by
    simpa [s1, State.put] using advance_position state entry position (by omega)
  have p2 : s2.pc = word width (entry + 2) := by
    simpa [s2, State.put, Nat.add_assoc] using advance_position s1 (entry + 1) p1 (by omega)
  have p3 : s3.pc = word width (entry + 3) := by
    simpa [s3, State.put, Nat.add_assoc] using advance_position s2 (entry + 2) p2 (by omega)
  have p4 : s4.pc = word width (entry + 4) := by
    simpa [s4, State.put, Nat.add_assoc] using advance_position s3 (entry + 3) p3 (by omega)
  have first : programStep destination state = some s1 := by
    apply constant_step destination state 3 (word width literal.1.val) _ running
    simpa [literalCode] using fetched destination entry layout literal present state ⟨0, by decide⟩
      (by simpa using position) capacity
  have second : programStep destination s1 = some s2 := by
    apply constant_step destination s1 0 (word width (MarkStorage.address layout.markBase literal)) _ running
    simpa [literalCode] using fetched destination entry layout literal present s1 ⟨1, by decide⟩ p1 capacity
  have third : Execution destination s2 s3 1 s2.liveWords := by
    have points : (s2.reg 0).val = MarkStorage.address layout.markBase literal := by
      simp only [s2, State.put, ite_true]
      exact word_val _ ((stored.bound literal).trans_le heapFits)
    exact (MarkStorage.load_mark_execution destination s2 marks layout.markBase stored literal 1 0
      running (by simpa [literalCode] using fetched destination entry layout literal present s2 ⟨2, by decide⟩ p2 capacity)
      points).1
  have fourth : programStep destination s3 = some s4 := by
    apply constant_step destination s3 0 (word width (MarkStorage.address layout.markBase (CNF.negate literal))) _ running
    simpa [literalCode] using fetched destination entry layout literal present s3 ⟨3, by decide⟩ p3 capacity
  have fifth : Execution destination s4 (readState state layout literal marks) 1 s4.liveWords := by
    have points : (s4.reg 0).val = MarkStorage.address layout.markBase (CNF.negate literal) := by
      simp only [s4, State.put, ite_true]
      exact word_val _ ((stored.bound (CNF.negate literal)).trans_le heapFits)
    exact (MarkStorage.load_mark_execution destination s4 marks layout.markBase stored (CNF.negate literal) 7 0
      running (by simpa [literalCode] using fetched destination entry layout literal present s4 ⟨4, by decide⟩ p4 capacity)
      points).1
  have trace := Execution.cons first (Execution.cons second
    (third.append (Execution.cons fourth fifth)))
  simpa [s1, s2, s3, s4, State.put, State.advance, State.liveWords] using trace

def emit (width entry : Nat) (layout : Layout) : List (CNF.Literal (Fin n)) → Program width 8
  | [] => #[]
  | literal :: rest => literalCode width entry layout literal ++ emit width (entry + 26) layout rest

/-- Compilation retains every literal occurrence and reverses the traversal to
match `IndexedNormalize.scan`; it does not silently deduplicate source rows. -/
def rowCode (width entry : Nat) (layout : Layout) (clause : CNF.Clause (Fin n)) : Program width 8 :=
  emit width entry layout clause.reverse

@[simp] theorem emit_size (width entry : Nat) (layout : Layout)
    (literals : List (CNF.Literal (Fin n))) :
    (emit width entry layout literals).size = 26 * literals.length := by
  induction literals generalizing entry with
  | nil => rfl
  | cons literal rest ih =>
    simp only [emit, Array.size_append, literalCode_size, ih, List.length_cons]
    omega

@[simp] theorem rowCode_size (width entry : Nat) (layout : Layout)
    (clause : CNF.Clause (Fin n)) : (rowCode width entry layout clause).size = 26 * clause.length := by
  simp [rowCode]

end Controller.Horn.NormalizeProgram
