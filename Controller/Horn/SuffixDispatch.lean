module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Horn.ResetEntry

@[expose] public section

/-!
# Input-independent normalizer dispatch suffix

Only phases 5 through 23 of the emitted literal block are used here. They
contain static polarity-header addresses and register-based label stores. The
literal-specific prefix and final mark-address constant are excluded; an input
reader and dynamic mark writer must supply those operations.
-/
namespace Controller.Horn.SuffixDispatch

open Controller.Cost Controller.Horn.NormalizeProgram Controller.Horn.LiteralDispatch
open Controller.Horn.JoinedLiteral Controller.Horn.Worklist.IndexedNormalize

/-- Agreement on exactly the nineteen input-independent dispatch instructions. -/
def SuffixAt (destination : Program width 8) (entry : Nat) (layout : Layout)
    (literal : CNF.Literal (Fin n)) : Prop :=
  ∀ phase : Fin 26, 5 ≤ phase.val → phase.val < 24 →
    destination[entry + phase.val]? = some (literalCode width entry layout literal)[phase.val]

private theorem word_val (value : Nat) (fits : value < 2 ^ width) :
    (word width value).val = value := Nat.mod_eq_of_lt fits

private theorem constant_transition (destination : Program width 8) (state : State width 8)
    (register : Fin 8) (value : Word width)
    (fetched : destination[state.pc.val]? = some (.constant register value))
    (running : state.halted = false) :
    programStep destination state = some (state.advance.put register value) := by
  unfold programStep
  rw [fetched]
  change step (.constant register value) state = _
  simp only [step, running, Bool.false_eq_true, ite_false]

private theorem zero_transition (destination : Program width 8) (state : State width 8)
    (register : Fin 8) (target : Word width)
    (fetched : destination[state.pc.val]? = some (.branchZero register target))
    (held : state.reg register = word width 0) (running : state.halted = false) :
    programStep destination state = some { state.advance with pc := target } := by
  unfold programStep
  rw [fetched]
  change step (.branchZero register target) state = _
  simp only [step, running, Bool.false_eq_true, ite_false, held]
  simp [word]

private theorem nonzero_transition (destination : Program width 8) (state : State width 8)
    (register : Fin 8) (target : Word width)
    (fetched : destination[state.pc.val]? = some (.branchZero register target))
    (held : state.reg register = MarkStorage.encode width true)
    (running : state.halted = false) (capacity : 1 < 2 ^ width) :
    programStep destination state = some state.advance := by
  unfold programStep
  rw [fetched]
  change step (.branchZero register target) state = _
  simp [step, running, held, MarkStorage.encode, word, Nat.mod_eq_of_lt capacity]

theorem fetched (destination : Program width 8) (entry : Nat) (layout : Layout)
    (literal : CNF.Literal (Fin n)) (present : SuffixAt destination entry layout literal)
    (state : State width 8) (phase : Fin 26) (lower : 5 ≤ phase.val) (upper : phase.val < 24)
    (position : state.pc = word width (entry + phase.val)) (capacity : entry + 26 < 2 ^ width) :
    destination[state.pc.val]? = some (literalCode width entry layout literal)[phase.val] := by
  rw [position, word_val (width := width) (entry + phase.val) (by have := phase.isLt; omega)]
  exact present phase lower upper

theorem signed_prepend_at (destination : Program width 8) (entry : Nat) (layout : Layout)
    (literal : CNF.Literal (Fin n)) (present : SuffixAt destination entry layout literal) :
    RecordStorage.CodeAt destination (entry + 8) := by
  intro phase
  have fetched := present ⟨8 + phase.val, by have := phase.isLt; omega⟩
    (by change 5 ≤ 8 + phase.val; omega) (by change 8 + phase.val < 24; have := phase.isLt; omega)
  have cases : phase.val = 0 ∨ phase.val = 1 ∨ phase.val = 2 ∨ phase.val = 3 := by
    have := phase.isLt
    omega
  rcases cases with equal | equal | equal | equal <;>
    simpa [literalCode, RecordStorage.code, equal, Nat.add_assoc] using fetched

theorem touched_prepend_at (destination : Program width 8) (entry : Nat) (layout : Layout)
    (literal : CNF.Literal (Fin n)) (present : SuffixAt destination entry layout literal) :
    RecordStorage.CodeAt destination (entry + 20) := by
  intro phase
  have fetched := present ⟨20 + phase.val, by have := phase.isLt; omega⟩
    (by change 5 ≤ 20 + phase.val; omega) (by change 20 + phase.val < 24; have := phase.isLt; omega)
  have cases : phase.val = 0 ∨ phase.val = 1 ∨ phase.val = 2 ∨ phase.val = 3 := by
    have := phase.isLt
    omega
  rcases cases with equal | equal | equal | equal <;>
    simpa [literalCode, RecordStorage.code, equal, Nat.add_assoc] using fetched

theorem signed_skip_execution (destination : Program width 8) (entry : Nat) (layout : Layout)
    (literal : CNF.Literal (Fin n)) (present : SuffixAt destination entry layout literal)
    (state : State width 8) (position : state.pc = word width (entry + 5))
    (same : state.reg 1 = MarkStorage.encode width true)
    (zero : state.reg 2 = word width 0) (running : state.halted = false)
    (capacity : entry + 26 < 2 ^ width) :
    Execution destination state { state.advance.advance with pc := word width (entry + 12) }
      2 state.liveWords := by
  have first := nonzero_transition destination state 1 (word width (entry + 7))
    (by simpa [literalCode] using fetched destination entry layout literal present state ⟨5, by decide⟩ (by decide) (by decide) position capacity)
    same running (by omega)
  have nextPosition : state.advance.pc = word width (entry + 6) := by
    simp only [State.advance, position, word_val (width := width) (entry + 5) (by omega)]
  have second := zero_transition destination state.advance 2 (word width (entry + 12))
    (by simpa [literalCode] using fetched destination entry layout literal present state.advance ⟨6, by decide⟩ (by decide) (by decide) nextPosition capacity)
    zero running
  have trace := Execution.cons first (Execution.cons second
    (Execution.refl { state.advance.advance with pc := word width (entry + 12) }))
  simpa [State.advance, State.liveWords] using trace

theorem signed_insert_execution (destination : Program width 8) (entry : Nat) (layout : Layout)
    (literal : CNF.Literal (Fin n)) (present : SuffixAt destination entry layout literal)
    (state : State width 8) (position : state.pc = word width (entry + 5))
    (same : state.reg 1 = MarkStorage.encode width false)
    (held : state.reg 3 = word width literal.1.val)
    (decrement : state.reg 6 = word width (2 ^ width - 1))
    (running : state.halted = false) (capacity : entry + 26 < 2 ^ width)
    (labels : List (Fin n)) (lower cursor limit : Nat)
    (stored : RecordStorage.HeaderStored labels (layout.signHeader literal.2) lower cursor limit state.heap)
    (room : lower < cursor) (headerFits : layout.signHeader literal.2 < 2 ^ width)
    (cursorFits : cursor < 2 ^ width) :
    Execution destination state (inserted state entry layout literal labels lower cursor limit stored room)
      6 state.liveWords := by
  let jumped : State width 8 := { state.advance with pc := word width (entry + 7) }
  have first : programStep destination state = some jumped := by
    exact zero_transition destination state 1 (word width (entry + 7))
      (by simpa [literalCode] using fetched destination entry layout literal present state ⟨5, by decide⟩ (by decide) (by decide) position capacity)
      same running
  have second : programStep destination jumped =
      some (insertStart state entry (layout.signHeader literal.2)) := by
    apply constant_transition destination jumped 0 (word width (layout.signHeader literal.2)) _ running
    simpa [literalCode] using fetched destination entry layout literal present jumped ⟨7, by decide⟩ (by decide) (by decide) rfl capacity
  have insertPosition : (insertStart state entry (layout.signHeader literal.2)).pc = word width (entry + 8) := by
    simp only [insertStart, State.put, State.advance, word_val (width := width) (entry + 7) (by omega)]
  have tail := RecordStorage.execution destination (entry + 8)
    (signed_prepend_at destination entry layout literal present)
    (insertStart state entry (layout.signHeader literal.2)) labels (layout.signHeader literal.2)
    lower cursor limit stored room literal.1
    (by simp [insertStart, State.put])
    (by simpa [insertStart, State.put, State.advance] using held)
    (by simpa [insertStart, State.put, State.advance] using decrement)
    insertPosition running (by omega) headerFits cursorFits
  have trace := Execution.cons first (Execution.cons second tail)
  simpa [inserted, insertStart, jumped, State.put, State.advance, State.liveWords] using trace

theorem conflict_skip_execution (destination : Program width 8) (entry : Nat) (layout : Layout)
    (literal : CNF.Literal (Fin n)) (present : SuffixAt destination entry layout literal)
    (state : State width 8) (position : state.pc = word width (entry + 12))
    (opposite : state.reg 7 = MarkStorage.encode width false)
    (running : state.halted = false) (capacity : entry + 26 < 2 ^ width) :
    Execution destination state { state.advance with pc := word width (entry + 15) }
      1 state.liveWords := by
  have transition := zero_transition destination state 7 (word width (entry + 15))
    (by simpa [literalCode] using fetched destination entry layout literal present state ⟨12, by decide⟩ (by decide) (by decide) position capacity)
    opposite running
  have trace := Execution.cons transition
    (Execution.refl { state.advance with pc := word width (entry + 15) })
  simpa [State.advance, State.liveWords] using trace

theorem conflict_set_execution (destination : Program width 8) (entry : Nat) (layout : Layout)
    (literal : CNF.Literal (Fin n)) (present : SuffixAt destination entry layout literal)
    (state : State width 8) (position : state.pc = word width (entry + 12))
    (opposite : state.reg 7 = MarkStorage.encode width true)
    (trueHeld : state.reg 5 = MarkStorage.encode width true)
    (running : state.halted = false) (capacity : entry + 26 < 2 ^ width)
    (valid : layout.tautologyHeader < state.heap.size)
    (headerFits : layout.tautologyHeader < 2 ^ width) :
    Execution destination state (conflicted state layout.tautologyHeader valid) 3 state.liveWords := by
  have first := nonzero_transition destination state 7 (word width (entry + 15))
    (by simpa [literalCode] using fetched destination entry layout literal present state ⟨12, by decide⟩ (by decide) (by decide) position capacity)
    opposite running (by omega)
  have nextPosition : state.advance.pc = word width (entry + 13) := by
    simp only [State.advance, position, word_val (width := width) (entry + 12) (by omega)]
  have second : programStep destination state.advance = some (conflictStart state layout.tautologyHeader) := by
    apply constant_transition destination state.advance 0 (word width layout.tautologyHeader) _ running
    simpa [literalCode] using fetched destination entry layout literal present state.advance ⟨13, by decide⟩ (by decide) (by decide) nextPosition capacity
  have storePosition : (conflictStart state layout.tautologyHeader).pc = word width (entry + 14) := by
    simp only [conflictStart, State.put, State.advance, position,
      word_val (width := width) (entry + 12) (by omega), word_val (width := width) (entry + 13) (by omega)]
  have third : programStep destination (conflictStart state layout.tautologyHeader) =
      some (conflicted state layout.tautologyHeader valid) := by
    have read : destination[(conflictStart state layout.tautologyHeader).pc.val]? = some (.store 0 5) := by
      simpa [literalCode] using fetched destination entry layout literal present
        (conflictStart state layout.tautologyHeader) ⟨14, by decide⟩ (by decide) (by decide) storePosition capacity
    unfold programStep
    rw [read]
    change step (.store 0 5) _ = _
    have address : ((conflictStart state layout.tautologyHeader).reg 0).val = layout.tautologyHeader := by
      simp only [conflictStart, State.put, ite_true]
      exact word_val (width := width) _ headerFits
    have value : (conflictStart state layout.tautologyHeader).reg 5 = MarkStorage.encode width true := by
      simpa [conflictStart, State.put, State.advance] using trueHeld
    have headerBound : layout.tautologyHeader < (conflictStart state layout.tautologyHeader).heap.size := valid
    simp only [step, show (conflictStart state layout.tautologyHeader).halted = false from running,
      Bool.false_eq_true, ite_false, address, headerBound, dite_eq_left, value]
    rfl
  have trace := Execution.cons first (Execution.cons second (Execution.cons third
    (Execution.refl (conflicted state layout.tautologyHeader valid))))
  simpa [conflicted, conflictStart, State.put, State.advance, State.liveWords] using trace

theorem touched_same_skip_execution (destination : Program width 8) (entry : Nat) (layout : Layout)
    (literal : CNF.Literal (Fin n)) (present : SuffixAt destination entry layout literal)
    (state : State width 8) (position : state.pc = word width (entry + 15))
    (same : state.reg 1 = MarkStorage.encode width true)
    (zero : state.reg 2 = word width 0) (running : state.halted = false)
    (capacity : entry + 26 < 2 ^ width) :
    Execution destination state { state.advance.advance with pc := word width (entry + 24) }
      2 state.liveWords := by
  have first := nonzero_transition destination state 1 (word width (entry + 17))
    (by simpa [literalCode] using fetched destination entry layout literal present state ⟨15, by decide⟩ (by decide) (by decide) position capacity)
    same running (by omega)
  have nextPosition : state.advance.pc = word width (entry + 16) := by
    simp only [State.advance, position, word_val (width := width) (entry + 15) (by omega)]
  have second := zero_transition destination state.advance 2 (word width (entry + 24))
    (by simpa [literalCode] using fetched destination entry layout literal present state.advance ⟨16, by decide⟩ (by decide) (by decide) nextPosition capacity)
    zero running
  have trace := Execution.cons first (Execution.cons second
    (Execution.refl { state.advance.advance with pc := word width (entry + 24) }))
  simpa [State.advance, State.liveWords] using trace

/-- A first occurrence of this sign still skips the touched list when its
opposite has already marked the channel. -/
theorem touched_opposite_skip_execution (destination : Program width 8) (entry : Nat) (layout : Layout)
    (literal : CNF.Literal (Fin n)) (present : SuffixAt destination entry layout literal)
    (state : State width 8) (position : state.pc = word width (entry + 15))
    (same : state.reg 1 = MarkStorage.encode width false)
    (opposite : state.reg 7 = MarkStorage.encode width true)
    (zero : state.reg 2 = word width 0) (running : state.halted = false)
    (capacity : entry + 26 < 2 ^ width) :
    Execution destination state
      { ({ state.advance with pc := word width (entry + 17) } : State width 8).advance.advance
          with pc := word width (entry + 24) } 3 state.liveWords := by
  let jumped : State width 8 := { state.advance with pc := word width (entry + 17) }
  have first : programStep destination state = some jumped :=
    zero_transition destination state 1 (word width (entry + 17))
      (by simpa [literalCode] using fetched destination entry layout literal present state ⟨15, by decide⟩ (by decide) (by decide) position capacity)
      same running
  have second := nonzero_transition destination jumped 7 (word width (entry + 19))
    (by simpa [literalCode] using fetched destination entry layout literal present jumped ⟨17, by decide⟩ (by decide) (by decide) rfl capacity)
    opposite running (by omega)
  have nextPosition : jumped.advance.pc = word width (entry + 18) := by
    simp only [jumped, State.advance, word_val (width := width) (entry + 17) (by omega)]
  have third := zero_transition destination jumped.advance 2 (word width (entry + 24))
    (by simpa [literalCode] using fetched destination entry layout literal present jumped.advance ⟨18, by decide⟩ (by decide) (by decide) nextPosition capacity)
    zero running
  have trace := Execution.cons first (Execution.cons second (Execution.cons third
    (Execution.refl { jumped.advance.advance with pc := word width (entry + 24) })))
  simpa [jumped, State.advance, State.liveWords] using trace

theorem touched_insert_execution (destination : Program width 8) (entry : Nat) (layout : Layout)
    (literal : CNF.Literal (Fin n)) (present : SuffixAt destination entry layout literal)
    (state : State width 8) (position : state.pc = word width (entry + 15))
    (same : state.reg 1 = MarkStorage.encode width false)
    (opposite : state.reg 7 = MarkStorage.encode width false)
    (held : state.reg 3 = word width literal.1.val)
    (decrement : state.reg 6 = word width (2 ^ width - 1))
    (running : state.halted = false) (capacity : entry + 26 < 2 ^ width)
    (labels : List (Fin n)) (lower cursor limit : Nat)
    (stored : RecordStorage.HeaderStored labels layout.touchedHeader lower cursor limit state.heap)
    (room : lower < cursor) (headerFits : layout.touchedHeader < 2 ^ width)
    (cursorFits : cursor < 2 ^ width) :
    Execution destination state (touchedInserted state entry layout literal labels lower cursor limit stored room)
      7 state.liveWords := by
  let jumped : State width 8 := { state.advance with pc := word width (entry + 17) }
  let jumpedAgain : State width 8 := { jumped.advance with pc := word width (entry + 19) }
  have first : programStep destination state = some jumped :=
    zero_transition destination state 1 (word width (entry + 17))
      (by simpa [literalCode] using fetched destination entry layout literal present state ⟨15, by decide⟩ (by decide) (by decide) position capacity)
      same running
  have second : programStep destination jumped = some jumpedAgain :=
    zero_transition destination jumped 7 (word width (entry + 19))
      (by simpa [literalCode] using fetched destination entry layout literal present jumped ⟨17, by decide⟩ (by decide) (by decide) rfl capacity)
      opposite running
  have third : programStep destination jumpedAgain = some (touchedStart state entry layout.touchedHeader) := by
    apply constant_transition destination jumpedAgain 0 (word width layout.touchedHeader) _ running
    simpa [literalCode] using fetched destination entry layout literal present jumpedAgain ⟨19, by decide⟩ (by decide) (by decide) rfl capacity
  have insertPosition : (touchedStart state entry layout.touchedHeader).pc = word width (entry + 20) := by
    simp only [touchedStart, State.put, State.advance, word_val (width := width) (entry + 19) (by omega)]
  have tail := RecordStorage.execution destination (entry + 20)
    (touched_prepend_at destination entry layout literal present)
    (touchedStart state entry layout.touchedHeader) labels layout.touchedHeader lower cursor limit
    stored room literal.1
    (by simp [touchedStart, State.put])
    (by simpa [touchedStart, State.put, State.advance] using held)
    (by simpa [touchedStart, State.put, State.advance] using decrement)
    insertPosition running (by omega) headerFits cursorFits
  have trace := Execution.cons first (Execution.cons second (Execution.cons third tail))
  simpa [touchedInserted, touchedStart, jumped, jumpedAgain, State.put, State.advance, State.liveWords] using trace

theorem sign_stage (destination : Program width 8) (entry base : Nat)
    (literal : CNF.Literal (Fin n)) (present : SuffixAt destination entry (rowLayout n base) literal)
    (clause : CNF.Clause (Fin n)) (row : Row n) (correct : row.Correct clause)
    (state : State width 8) (positiveCursor negativeCursor touchedCursor : Nat)
    (stored : RowStored row base positiveCursor negativeCursor touchedCursor state.heap)
    (control : Control state literal (row.marks.read literal) (row.marks.read (CNF.negate literal)))
    (position : state.pc = word width (entry + 5))
    (capacity : entry + 26 < 2 ^ width) (heapFits : state.heap.size < 2 ^ width) :
    ∃ next : State width 8,
      Execution destination state next (if row.marks.read literal then 2 else 6) state.liveWords ∧
      RowStored (signRow row literal) base (positiveNext row literal positiveCursor)
        (negativeNext row literal negativeCursor) touchedCursor next.heap ∧
      Control next literal (row.marks.read literal) (row.marks.read (CNF.negate literal)) ∧
      next.pc = word width (entry + 12) ∧ next.liveWords = state.liveWords ∧
      next.heap.size = state.heap.size := by
  cases same : row.marks.read literal
  · cases polarity : literal.2
    · have fresh : row.marks.read (literal.1, false) = false := by simpa [Marks.read, polarity] using same
      have room := RowStored.negative_room clause row correct literal.1 fresh base positiveCursor negativeCursor touchedCursor state.heap stored
      have header : RecordStorage.HeaderStored row.negative ((rowLayout n base).signHeader literal.2)
          (base + 3 * n + 4) negativeCursor (base + 4 * n + 4) state.heap := by
        simpa [rowLayout, Layout.signHeader, polarity] using stored.negative
      let next := inserted state entry (rowLayout n base) literal row.negative
        (base + 3 * n + 4) negativeCursor (base + 4 * n + 4) header room
      have upper : negativeCursor ≤ base + 4 * n + 4 := by have := stored.negative.buffer.ends; omega
      have fit := RowStored.scratch_fits row base positiveCursor negativeCursor touchedCursor state.heap stored
      refine ⟨next, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [same] using signed_insert_execution destination entry (rowLayout n base) literal present
          state position (by simpa [same] using control.sameHeld) control.label control.decrement
          control.running capacity row.negative (base + 3 * n + 4) negativeCursor (base + 4 * n + 4)
          header room (by simp [rowLayout, Layout.signHeader, polarity]; omega) (by omega)
      · have refined := RowStored.prepend_negative
          (insertStart state entry ((rowLayout n base).signHeader literal.2)) row literal.1
          base positiveCursor negativeCursor touchedCursor stored room
        simpa [next, inserted, signRow, positiveNext, negativeNext, same, polarity, rowLayout,
          Layout.signHeader] using refined
      · simpa only [same] using Control.after_sign_insert state entry (rowLayout n base) literal _ _ control
          row.negative (base + 3 * n + 4) negativeCursor (base + 4 * n + 4) header room
      · exact inserted_position state entry (rowLayout n base) literal row.negative
          (base + 3 * n + 4) negativeCursor (base + 4 * n + 4) header room capacity
      · simp [next, inserted, RecordStorage.finished, RecordStorage.afterPrepend, RecordStorage.loaded,
          LabelBuffer.prependedState, State.liveWords, insertStart, State.advance, State.put]
      · simp [next, inserted, RecordStorage.finished, RecordStorage.afterPrepend, RecordStorage.loaded,
          LabelBuffer.prependedState, insertStart, State.advance, State.put]
    · have fresh : row.marks.read (literal.1, true) = false := by simpa [Marks.read, polarity] using same
      have room := RowStored.positive_room clause row correct literal.1 fresh base positiveCursor negativeCursor touchedCursor state.heap stored
      have header : RecordStorage.HeaderStored row.positive ((rowLayout n base).signHeader literal.2)
          (base + 2 * n + 4) positiveCursor (base + 3 * n + 4) state.heap := by
        simpa [rowLayout, Layout.signHeader, polarity] using stored.positive
      let next := inserted state entry (rowLayout n base) literal row.positive
        (base + 2 * n + 4) positiveCursor (base + 3 * n + 4) header room
      have upper : positiveCursor ≤ base + 3 * n + 4 := by have := stored.positive.buffer.ends; omega
      have fit := RowStored.scratch_fits row base positiveCursor negativeCursor touchedCursor state.heap stored
      refine ⟨next, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [same] using signed_insert_execution destination entry (rowLayout n base) literal present
          state position (by simpa [same] using control.sameHeld) control.label control.decrement
          control.running capacity row.positive (base + 2 * n + 4) positiveCursor (base + 3 * n + 4)
          header room (by simp [rowLayout, Layout.signHeader, polarity]; omega) (by omega)
      · have refined := RowStored.prepend_positive
          (insertStart state entry ((rowLayout n base).signHeader literal.2)) row literal.1
          base positiveCursor negativeCursor touchedCursor stored room
        simpa [next, inserted, signRow, positiveNext, negativeNext, same, polarity, rowLayout,
          Layout.signHeader] using refined
      · simpa only [same] using Control.after_sign_insert state entry (rowLayout n base) literal _ _ control
          row.positive (base + 2 * n + 4) positiveCursor (base + 3 * n + 4) header room
      · exact inserted_position state entry (rowLayout n base) literal row.positive
          (base + 2 * n + 4) positiveCursor (base + 3 * n + 4) header room capacity
      · simp [next, inserted, RecordStorage.finished, RecordStorage.afterPrepend, RecordStorage.loaded,
          LabelBuffer.prependedState, State.liveWords, insertStart, State.advance, State.put]
      · simp [next, inserted, RecordStorage.finished, RecordStorage.afterPrepend, RecordStorage.loaded,
          LabelBuffer.prependedState, insertStart, State.advance, State.put]
  · let next : State width 8 := { state.advance.advance with pc := word width (entry + 12) }
    refine ⟨next, ?_, ?_, ?_, rfl, rfl, rfl⟩
    · simpa [same] using signed_skip_execution destination entry (rowLayout n base) literal present
        state position (by simpa [same] using control.sameHeld) control.zero control.running capacity
    · simpa [next, signRow, positiveNext, negativeNext, same, State.advance] using stored
    · have kept : Control next literal (row.marks.read literal) (row.marks.read (CNF.negate literal)) :=
        ⟨control.zero, control.trueHeld, control.decrement, control.label, control.sameHeld, control.oppositeHeld, control.running⟩
      simpa only [same] using kept


/-- Conflict dispatch updates the physical flag word and otherwise retains the
complete row representation. Its branch reads the original opposite register. -/
theorem conflict_stage (destination : Program width 8) (entry base : Nat)
    (literal : CNF.Literal (Fin n)) (present : SuffixAt destination entry (rowLayout n base) literal)
    (row : Row n) (state : State width 8) (positiveCursor negativeCursor touchedCursor : Nat)
    (stored : RowStored row base positiveCursor negativeCursor touchedCursor state.heap)
    (control : Control state literal (row.marks.read literal) (row.marks.read (CNF.negate literal)))
    (position : state.pc = word width (entry + 12))
    (capacity : entry + 26 < 2 ^ width) (heapFits : state.heap.size < 2 ^ width) :
    ∃ next : State width 8,
      Execution destination state next (if row.marks.read (CNF.negate literal) then 3 else 1) state.liveWords ∧
      RowStored (conflictRow row literal) base positiveCursor negativeCursor touchedCursor next.heap ∧
      Control next literal (row.marks.read literal) (row.marks.read (CNF.negate literal)) ∧
      next.pc = word width (entry + 15) ∧ next.liveWords = state.liveWords ∧
      next.heap.size = state.heap.size := by
  cases opposite : row.marks.read (CNF.negate literal)
  · let next : State width 8 := { state.advance with pc := word width (entry + 15) }
    refine ⟨next, ?_, ?_, ?_, rfl, rfl, rfl⟩
    · simpa [opposite] using conflict_skip_execution destination entry (rowLayout n base) literal present
        state position (by simpa [opposite] using control.oppositeHeld) control.running capacity
    · simpa [next, conflictRow, opposite, State.advance] using stored
    · have kept : Control next literal (row.marks.read literal) (row.marks.read (CNF.negate literal)) :=
        ⟨control.zero, control.trueHeld, control.decrement, control.label, control.sameHeld, control.oppositeHeld, control.running⟩
      simpa only [opposite] using kept
  · let next := conflicted state (base + 2 * n + 3) stored.flagBound
    refine ⟨next, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [opposite, rowLayout] using conflict_set_execution destination entry (rowLayout n base)
        literal present state position (by simpa [opposite] using control.oppositeHeld)
        control.trueHeld control.running capacity stored.flagBound (by change base + 2 * n + 3 < 2 ^ width; have := stored.flagBound; omega)
    · simpa [next, conflictRow, opposite] using
        RowStored.set_conflict state row base positiveCursor negativeCursor touchedCursor stored
    · simpa only [opposite] using Control.after_conflict state literal _ _ control (base + 2 * n + 3) stored.flagBound
    · exact conflicted_position state (base + 2 * n + 3) stored.flagBound entry position capacity
    · simp [next, conflicted, conflictStart, State.liveWords, State.advance, State.put]
    · simp [next, conflicted, conflictStart, State.advance, State.put]


theorem touched_stage (destination : Program width 8) (entry base : Nat)
    (literal : CNF.Literal (Fin n)) (present : SuffixAt destination entry (rowLayout n base) literal)
    (row : Row n) (state : State width 8) (positiveCursor negativeCursor touchedCursor : Nat)
    (stored : RowStored row base positiveCursor negativeCursor touchedCursor state.heap)
    (control : Control state literal (row.marks.read literal) (row.marks.read (CNF.negate literal)))
    (position : state.pc = word width (entry + 15))
    (capacity : entry + 26 < 2 ^ width) (heapFits : state.heap.size < 2 ^ width)
    (room : row.marks.read literal = false → row.marks.read (CNF.negate literal) = false →
      base + 4 * n + 4 < touchedCursor) :
    ∃ next : State width 8,
      Execution destination state next
        (if row.marks.read literal then 2 else if row.marks.read (CNF.negate literal) then 3 else 7) state.liveWords ∧
      RowStored (touchedRow row literal) base positiveCursor negativeCursor
        (touchedNext row literal touchedCursor) next.heap ∧
      Control next literal (row.marks.read literal) (row.marks.read (CNF.negate literal)) ∧
      next.pc = word width (entry + 24) ∧ next.liveWords = state.liveWords ∧
      next.heap.size = state.heap.size := by
  cases same : row.marks.read literal
  · cases opposite : row.marks.read (CNF.negate literal)
    · have freshRoom := room same opposite
      let next := touchedInserted state entry (rowLayout n base) literal row.touched
        (base + 4 * n + 4) touchedCursor (base + 5 * n + 4) stored.touched freshRoom
      have upper : touchedCursor ≤ base + 5 * n + 4 := by have := stored.touched.buffer.ends; omega
      have fit := RowStored.scratch_fits row base positiveCursor negativeCursor touchedCursor state.heap stored
      refine ⟨next, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [same, opposite] using touched_insert_execution destination entry (rowLayout n base)
          literal present state position (by simpa [same] using control.sameHeld)
          (by simpa [opposite] using control.oppositeHeld) control.label control.decrement control.running
          capacity row.touched (base + 4 * n + 4) touchedCursor (base + 5 * n + 4)
          stored.touched freshRoom (by change base + 2 * n + 2 < 2 ^ width; omega) (by omega)
      · have refined := RowStored.prepend_touched (touchedStart state entry ((rowLayout n base).touchedHeader))
          row literal.1 base positiveCursor negativeCursor touchedCursor stored freshRoom
        simpa [next, touchedInserted, touchedRow, touchedNext, same, opposite, rowLayout] using refined
      · simpa only [same, opposite] using Control.after_touched_insert state entry (rowLayout n base) literal _ _ control
          row.touched (base + 4 * n + 4) touchedCursor (base + 5 * n + 4) stored.touched freshRoom
      · exact touchedInserted_position state entry (rowLayout n base) literal row.touched
          (base + 4 * n + 4) touchedCursor (base + 5 * n + 4) stored.touched freshRoom capacity
      · simp [next, touchedInserted, RecordStorage.finished, RecordStorage.afterPrepend, RecordStorage.loaded,
          LabelBuffer.prependedState, State.liveWords, touchedStart, State.advance, State.put]
      · simp [next, touchedInserted, RecordStorage.finished, RecordStorage.afterPrepend, RecordStorage.loaded,
          LabelBuffer.prependedState, touchedStart, State.advance, State.put]
    · let jumped : State width 8 := { state.advance with pc := word width (entry + 17) }
      let next : State width 8 := { jumped.advance.advance with pc := word width (entry + 24) }
      refine ⟨next, ?_, ?_, ?_, rfl, rfl, rfl⟩
      · simpa [same, opposite, next, jumped] using touched_opposite_skip_execution destination entry
          (rowLayout n base) literal present state position (by simpa [same] using control.sameHeld)
          (by simpa [opposite] using control.oppositeHeld) control.zero control.running capacity
      · simpa [next, jumped, touchedRow, touchedNext, same, opposite, State.advance] using stored
      · have kept : Control next literal (row.marks.read literal) (row.marks.read (CNF.negate literal)) :=
          ⟨control.zero, control.trueHeld, control.decrement, control.label, control.sameHeld, control.oppositeHeld, control.running⟩
        simpa only [same, opposite] using kept
  · let next : State width 8 := { state.advance.advance with pc := word width (entry + 24) }
    refine ⟨next, ?_, ?_, ?_, rfl, rfl, rfl⟩
    · simpa [same] using touched_same_skip_execution destination entry (rowLayout n base) literal present
        state position (by simpa [same] using control.sameHeld) control.zero control.running capacity
    · simpa [next, touchedRow, touchedNext, same, State.advance] using stored
    · have kept : Control next literal (row.marks.read literal) (row.marks.read (CNF.negate literal)) :=
        ⟨control.zero, control.trueHeld, control.decrement, control.label, control.sameHeld, control.oppositeHeld, control.running⟩
      simpa only [same] using kept


end Controller.Horn.SuffixDispatch
