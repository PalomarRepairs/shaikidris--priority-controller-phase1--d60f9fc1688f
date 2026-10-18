module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Horn.NormalizeProgram

@[expose] public section

/-!
# Actual sign-list dispatch for one normalizer occurrence

The old sign mark selects a two-instruction skip or a six-instruction insertion.
Both alternatives execute in the same relocated literal block and resume at
its conflict-flag stage. List insertions use the heap-header representation,
not a computed list supplied by the host.
-/
namespace Controller.Horn.LiteralDispatch

open Controller.Cost Controller.Horn.NormalizeProgram

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

/-- A duplicated sign skips the sign-list header without changing any heap cell. -/
theorem signed_skip_execution (destination : Program width 8) (entry : Nat) (layout : Layout)
    (literal : CNF.Literal (Fin n)) (present : LiteralAt destination entry layout literal)
    (state : State width 8) (position : state.pc = word width (entry + 5))
    (same : state.reg 1 = MarkStorage.encode width true)
    (zero : state.reg 2 = word width 0) (running : state.halted = false)
    (capacity : entry + 26 < 2 ^ width) :
    Execution destination state { state.advance.advance with pc := word width (entry + 12) }
      2 state.liveWords := by
  have first := nonzero_transition destination state 1 (word width (entry + 7))
    (by simpa [literalCode] using fetched destination entry layout literal present state ⟨5, by decide⟩ position capacity)
    same running (by omega)
  have nextPosition : state.advance.pc = word width (entry + 6) := by
    simp only [State.advance, position, word_val (width := width) (entry + 5) (by omega)]
    all_goals rfl
  have second := zero_transition destination state.advance 2 (word width (entry + 12))
    (by simpa [literalCode] using fetched destination entry layout literal present state.advance ⟨6, by decide⟩ nextPosition capacity)
    zero running
  have trace := Execution.cons first (Execution.cons second
    (Execution.refl { state.advance.advance with pc := word width (entry + 12) }))
  simpa [State.advance, State.liveWords] using trace

def insertStart (state : State width 8) (entry : Nat) (header : Nat) : State width 8 :=
  ({ state.advance with pc := word width (entry + 7) } : State width 8).advance.put 0 (word width header)

def inserted (state : State width 8) (entry : Nat) (layout : Layout)
    (literal : CNF.Literal (Fin n)) (labels : List (Fin n)) (lower cursor limit : Nat)
    (stored : RecordStorage.HeaderStored labels (layout.signHeader literal.2) lower cursor limit state.heap)
    (room : lower < cursor) : State width 8 :=
  RecordStorage.finished (insertStart state entry (layout.signHeader literal.2)) labels
    (layout.signHeader literal.2) lower cursor limit stored room literal.1

/-- A fresh sign branches into its header and executes the actual four-operation
list update. The prefix's held label and decrement register are retained. -/
theorem signed_insert_execution (destination : Program width 8) (entry : Nat) (layout : Layout)
    (literal : CNF.Literal (Fin n)) (present : LiteralAt destination entry layout literal)
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
      (by simpa [literalCode] using fetched destination entry layout literal present state ⟨5, by decide⟩ position capacity)
      same running
  have second : programStep destination jumped =
      some (insertStart state entry (layout.signHeader literal.2)) := by
    apply constant_transition destination jumped 0 (word width (layout.signHeader literal.2)) _ running
    simpa [literalCode] using fetched destination entry layout literal present jumped ⟨7, by decide⟩ rfl capacity
  have insertPosition : (insertStart state entry (layout.signHeader literal.2)).pc = word width (entry + 8) := by
    simp only [insertStart, State.put, State.advance, word_val (width := width) (entry + 7) (by omega)]
    all_goals rfl
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

theorem inserted_stored (state : State width 8) (entry : Nat) (layout : Layout)
    (literal : CNF.Literal (Fin n)) (labels : List (Fin n)) (lower cursor limit : Nat)
    (stored : RecordStorage.HeaderStored labels (layout.signHeader literal.2) lower cursor limit state.heap)
    (room : lower < cursor) :
    RecordStorage.HeaderStored (literal.1 :: labels) (layout.signHeader literal.2) lower (cursor - 1) limit
      (inserted state entry layout literal labels lower cursor limit stored room).heap :=
  RecordStorage.finished_stored (insertStart state entry (layout.signHeader literal.2)) labels
    (layout.signHeader literal.2) lower cursor limit stored room literal.1

theorem inserted_position (state : State width 8) (entry : Nat) (layout : Layout)
    (literal : CNF.Literal (Fin n)) (labels : List (Fin n)) (lower cursor limit : Nat)
    (stored : RecordStorage.HeaderStored labels (layout.signHeader literal.2) lower cursor limit state.heap)
    (room : lower < cursor) (capacity : entry + 26 < 2 ^ width) :
    (inserted state entry layout literal labels lower cursor limit stored room).pc = word width (entry + 12) := by
  have initial : (insertStart state entry (layout.signHeader literal.2)).pc = word width (entry + 8) := by
    simp only [insertStart, State.put, State.advance, word_val (width := width) (entry + 7) (by omega)]
    all_goals rfl
  simpa [inserted, Nat.add_assoc] using RecordStorage.finished_position
    (insertStart state entry (layout.signHeader literal.2)) labels (layout.signHeader literal.2)
    lower cursor limit stored room literal.1 (entry + 8) initial (by omega)

/-- Sign insertion changes only the address and cursor registers. -/
theorem inserted_frame (state : State width 8) (entry : Nat) (layout : Layout)
    (literal : CNF.Literal (Fin n)) (labels : List (Fin n)) (lower cursor limit : Nat)
    (stored : RecordStorage.HeaderStored labels (layout.signHeader literal.2) lower cursor limit state.heap)
    (room : lower < cursor) :
    (∀ register : Fin 8, register ≠ 0 → register ≠ 4 →
      (inserted state entry layout literal labels lower cursor limit stored room).reg register = state.reg register) ∧
    (inserted state entry layout literal labels lower cursor limit stored room).stack = state.stack ∧
    (inserted state entry layout literal labels lower cursor limit stored room).output = state.output := by
  refine ⟨?_, rfl, rfl⟩
  intro register address cursorRegister
  have preserved := (RecordStorage.finished_frame
    (insertStart state entry (layout.signHeader literal.2)) labels (layout.signHeader literal.2)
    lower cursor limit stored room literal.1).1 register cursorRegister
  exact preserved.trans (by simp [insertStart, State.put, State.advance, address])

/-- An absent opposite sign bypasses the tautology header in one instruction. -/
theorem conflict_skip_execution (destination : Program width 8) (entry : Nat) (layout : Layout)
    (literal : CNF.Literal (Fin n)) (present : LiteralAt destination entry layout literal)
    (state : State width 8) (position : state.pc = word width (entry + 12))
    (opposite : state.reg 7 = MarkStorage.encode width false)
    (running : state.halted = false) (capacity : entry + 26 < 2 ^ width) :
    Execution destination state { state.advance with pc := word width (entry + 15) }
      1 state.liveWords := by
  have transition := zero_transition destination state 7 (word width (entry + 15))
    (by simpa [literalCode] using fetched destination entry layout literal present state ⟨12, by decide⟩ position capacity)
    opposite running
  have trace := Execution.cons transition
    (Execution.refl { state.advance with pc := word width (entry + 15) })
  simpa [State.advance, State.liveWords] using trace

def conflictStart (state : State width 8) (header : Nat) : State width 8 :=
  state.advance.advance.put 0 (word width header)

def conflicted (state : State width 8) (header : Nat) (valid : header < state.heap.size) : State width 8 :=
  { (conflictStart state header).advance with
    heap := (state.heap.set header (MarkStorage.encode width true) valid) }

/-- An opposite mark executes the conflict write, retaining all list cells
unless the declared layout illegally aliases the tautology header with them. -/
theorem conflict_set_execution (destination : Program width 8) (entry : Nat) (layout : Layout)
    (literal : CNF.Literal (Fin n)) (present : LiteralAt destination entry layout literal)
    (state : State width 8) (position : state.pc = word width (entry + 12))
    (opposite : state.reg 7 = MarkStorage.encode width true)
    (trueHeld : state.reg 5 = MarkStorage.encode width true)
    (running : state.halted = false) (capacity : entry + 26 < 2 ^ width)
    (valid : layout.tautologyHeader < state.heap.size)
    (headerFits : layout.tautologyHeader < 2 ^ width) :
    Execution destination state (conflicted state layout.tautologyHeader valid) 3 state.liveWords := by
  have first := nonzero_transition destination state 7 (word width (entry + 15))
    (by simpa [literalCode] using fetched destination entry layout literal present state ⟨12, by decide⟩ position capacity)
    opposite running (by omega)
  have nextPosition : state.advance.pc = word width (entry + 13) := by
    simp only [State.advance, position, word_val (width := width) (entry + 12) (by omega)]
    all_goals rfl
  have second : programStep destination state.advance = some (conflictStart state layout.tautologyHeader) := by
    apply constant_transition destination state.advance 0 (word width layout.tautologyHeader) _ running
    simpa [literalCode] using fetched destination entry layout literal present state.advance ⟨13, by decide⟩ nextPosition capacity
  have storePosition : (conflictStart state layout.tautologyHeader).pc = word width (entry + 14) := by
    simp only [conflictStart, State.put, State.advance, position,
      word_val (width := width) (entry + 12) (by omega), word_val (width := width) (entry + 13) (by omega)]
    all_goals rfl
  have third : programStep destination (conflictStart state layout.tautologyHeader) =
      some (conflicted state layout.tautologyHeader valid) := by
    have read : destination[(conflictStart state layout.tautologyHeader).pc.val]? = some (.store 0 5) := by
      simpa [literalCode] using fetched destination entry layout literal present
        (conflictStart state layout.tautologyHeader) ⟨14, by decide⟩ storePosition capacity
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
    all_goals rfl
  have trace := Execution.cons first (Execution.cons second (Execution.cons third
    (Execution.refl (conflicted state layout.tautologyHeader valid))))
  simpa [conflicted, conflictStart, State.put, State.advance, State.liveWords] using trace

theorem conflicted_flag (state : State width 8) (header : Nat) (valid : header < state.heap.size) :
    (conflicted state header valid).heap[header]'(by simpa [conflicted] using valid) = MarkStorage.encode width true := by
  simp [conflicted]

theorem conflicted_position (state : State width 8) (header : Nat) (valid : header < state.heap.size)
    (entry : Nat) (position : state.pc = word width (entry + 12)) (capacity : entry + 26 < 2 ^ width) :
    (conflicted state header valid).pc = word width (entry + 15) := by
  simp only [conflicted, conflictStart, State.put, State.advance, position,
    word_val (width := width) (entry + 12) (by omega), word_val (width := width) (entry + 13) (by omega),
    word_val (width := width) (entry + 14) (by omega)]
  all_goals rfl

theorem conflicted_frame (state : State width 8) (header : Nat) (valid : header < state.heap.size) :
    (∀ register : Fin 8, register ≠ 0 → (conflicted state header valid).reg register = state.reg register) ∧
    (conflicted state header valid).stack = state.stack ∧
    (conflicted state header valid).output = state.output ∧
    (∀ index : Nat, header ≠ index → (conflicted state header valid).heap[index]? = state.heap[index]?) := by
  refine ⟨?_, rfl, rfl, ?_⟩
  · intro register address
    simp [conflicted, conflictStart, State.put, State.advance, address]
  · intro index different
    exact Array.getElem?_set_ne valid different

/-- A marked same polarity skips the touched list in two branches. -/
theorem touched_same_skip_execution (destination : Program width 8) (entry : Nat) (layout : Layout)
    (literal : CNF.Literal (Fin n)) (present : LiteralAt destination entry layout literal)
    (state : State width 8) (position : state.pc = word width (entry + 15))
    (same : state.reg 1 = MarkStorage.encode width true)
    (zero : state.reg 2 = word width 0) (running : state.halted = false)
    (capacity : entry + 26 < 2 ^ width) :
    Execution destination state { state.advance.advance with pc := word width (entry + 24) }
      2 state.liveWords := by
  have first := nonzero_transition destination state 1 (word width (entry + 17))
    (by simpa [literalCode] using fetched destination entry layout literal present state ⟨15, by decide⟩ position capacity)
    same running (by omega)
  have nextPosition : state.advance.pc = word width (entry + 16) := by
    simp only [State.advance, position, word_val (width := width) (entry + 15) (by omega)]
    all_goals rfl
  have second := zero_transition destination state.advance 2 (word width (entry + 24))
    (by simpa [literalCode] using fetched destination entry layout literal present state.advance ⟨16, by decide⟩ nextPosition capacity)
    zero running
  have trace := Execution.cons first (Execution.cons second
    (Execution.refl { state.advance.advance with pc := word width (entry + 24) }))
  simpa [State.advance, State.liveWords] using trace

/-- A first occurrence of this sign still skips the touched list when its
opposite has already marked the channel. -/
theorem touched_opposite_skip_execution (destination : Program width 8) (entry : Nat) (layout : Layout)
    (literal : CNF.Literal (Fin n)) (present : LiteralAt destination entry layout literal)
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
      (by simpa [literalCode] using fetched destination entry layout literal present state ⟨15, by decide⟩ position capacity)
      same running
  have second := nonzero_transition destination jumped 7 (word width (entry + 19))
    (by simpa [literalCode] using fetched destination entry layout literal present jumped ⟨17, by decide⟩ rfl capacity)
    opposite running (by omega)
  have nextPosition : jumped.advance.pc = word width (entry + 18) := by
    simp only [jumped, State.advance, word_val (width := width) (entry + 17) (by omega)]
    all_goals rfl
  have third := zero_transition destination jumped.advance 2 (word width (entry + 24))
    (by simpa [literalCode] using fetched destination entry layout literal present jumped.advance ⟨18, by decide⟩ nextPosition capacity)
    zero running
  have trace := Execution.cons first (Execution.cons second (Execution.cons third
    (Execution.refl { jumped.advance.advance with pc := word width (entry + 24) })))
  simpa [jumped, State.advance, State.liveWords] using trace

def touchedStart (state : State width 8) (entry : Nat) (header : Nat) : State width 8 :=
  ({ ({ state.advance with pc := word width (entry + 17) } : State width 8).advance
      with pc := word width (entry + 19) } : State width 8).advance.put 0 (word width header)

def touchedInserted (state : State width 8) (entry : Nat) (layout : Layout)
    (literal : CNF.Literal (Fin n)) (labels : List (Fin n)) (lower cursor limit : Nat)
    (stored : RecordStorage.HeaderStored labels layout.touchedHeader lower cursor limit state.heap)
    (room : lower < cursor) : State width 8 :=
  RecordStorage.finished (touchedStart state entry layout.touchedHeader) labels
    layout.touchedHeader lower cursor limit stored room literal.1

/-- Two zero branches select a fresh touched channel, followed by the actual
header load and backward-store block. -/
theorem touched_insert_execution (destination : Program width 8) (entry : Nat) (layout : Layout)
    (literal : CNF.Literal (Fin n)) (present : LiteralAt destination entry layout literal)
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
      (by simpa [literalCode] using fetched destination entry layout literal present state ⟨15, by decide⟩ position capacity)
      same running
  have second : programStep destination jumped = some jumpedAgain :=
    zero_transition destination jumped 7 (word width (entry + 19))
      (by simpa [literalCode] using fetched destination entry layout literal present jumped ⟨17, by decide⟩ rfl capacity)
      opposite running
  have third : programStep destination jumpedAgain = some (touchedStart state entry layout.touchedHeader) := by
    apply constant_transition destination jumpedAgain 0 (word width layout.touchedHeader) _ running
    simpa [literalCode] using fetched destination entry layout literal present jumpedAgain ⟨19, by decide⟩ rfl capacity
  have insertPosition : (touchedStart state entry layout.touchedHeader).pc = word width (entry + 20) := by
    simp only [touchedStart, State.put, State.advance, word_val (width := width) (entry + 19) (by omega)]
    all_goals rfl
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

def markStart (state : State width 8) (layout : Layout) (literal : CNF.Literal (Fin n)) : State width 8 :=
  state.advance.put 0 (word width (MarkStorage.address layout.markBase literal))

def marked (state : State width 8) (layout : Layout) (literal : CNF.Literal (Fin n))
    (marks : Worklist.IndexedNormalize.Marks n) (stored : MarkStorage.Stored marks layout.markBase state.heap) : State width 8 :=
  { (markStart state layout literal).advance with
    heap := state.heap.set (MarkStorage.address layout.markBase literal) (MarkStorage.encode width true) (stored.bound literal) }

/-- The final two instructions set the selected polarity and refine precisely
`Row.record`'s mark-vector component. -/
theorem mark_execution (destination : Program width 8) (entry : Nat) (layout : Layout)
    (literal : CNF.Literal (Fin n)) (present : LiteralAt destination entry layout literal)
    (state : State width 8) (position : state.pc = word width (entry + 24))
    (trueHeld : state.reg 5 = MarkStorage.encode width true)
    (running : state.halted = false) (capacity : entry + 26 < 2 ^ width)
    (marks : Worklist.IndexedNormalize.Marks n) (stored : MarkStorage.Stored marks layout.markBase state.heap)
    (heapFits : state.heap.size ≤ 2 ^ width) :
    Execution destination state (marked state layout literal marks stored) 2 state.liveWords ∧
    MarkStorage.Stored (MarkStorage.write marks literal true) layout.markBase
      (marked state layout literal marks stored).heap := by
  have first : programStep destination state = some (markStart state layout literal) := by
    apply constant_transition destination state 0 (word width (MarkStorage.address layout.markBase literal)) _ running
    simpa [literalCode] using fetched destination entry layout literal present state ⟨24, by decide⟩ position capacity
  have nextPosition : (markStart state layout literal).pc = word width (entry + 25) := by
    simp only [markStart, State.put, State.advance, position, word_val (width := width) (entry + 24) (by omega)]
    all_goals rfl
  have points : ((markStart state layout literal).reg 0).val = MarkStorage.address layout.markBase literal := by
    simp only [markStart, State.put, ite_true]
    exact word_val (width := width) _ ((stored.bound literal).trans_le heapFits)
  have writeFetched : destination[(markStart state layout literal).pc.val]? = some (.store 0 5) := by
    simpa [literalCode] using fetched destination entry layout literal present (markStart state layout literal) ⟨25, by decide⟩ nextPosition capacity
  have second := MarkStorage.store_mark_execution destination (markStart state layout literal)
    marks layout.markBase stored literal true 0 5 running writeFetched points
    (by simpa [markStart, State.put, State.advance] using trueHeld)
  constructor
  · have trace := Execution.cons first second.1
    simpa [marked, markStart, State.put, State.advance, State.liveWords] using trace
  · exact second.2

theorem touchedInserted_stored (state : State width 8) (entry : Nat) (layout : Layout)
    (literal : CNF.Literal (Fin n)) (labels : List (Fin n)) (lower cursor limit : Nat)
    (stored : RecordStorage.HeaderStored labels layout.touchedHeader lower cursor limit state.heap)
    (room : lower < cursor) :
    RecordStorage.HeaderStored (literal.1 :: labels) layout.touchedHeader lower (cursor - 1) limit
      (touchedInserted state entry layout literal labels lower cursor limit stored room).heap :=
  RecordStorage.finished_stored (touchedStart state entry layout.touchedHeader) labels
    layout.touchedHeader lower cursor limit stored room literal.1

theorem touchedInserted_position (state : State width 8) (entry : Nat) (layout : Layout)
    (literal : CNF.Literal (Fin n)) (labels : List (Fin n)) (lower cursor limit : Nat)
    (stored : RecordStorage.HeaderStored labels layout.touchedHeader lower cursor limit state.heap)
    (room : lower < cursor) (capacity : entry + 26 < 2 ^ width) :
    (touchedInserted state entry layout literal labels lower cursor limit stored room).pc = word width (entry + 24) := by
  have initial : (touchedStart state entry layout.touchedHeader).pc = word width (entry + 20) := by
    simp only [touchedStart, State.put, State.advance, word_val (width := width) (entry + 19) (by omega)]
    all_goals rfl
  simpa [touchedInserted, Nat.add_assoc] using RecordStorage.finished_position
    (touchedStart state entry layout.touchedHeader) labels layout.touchedHeader
    lower cursor limit stored room literal.1 (entry + 20) initial (by omega)

theorem touchedInserted_frame (state : State width 8) (entry : Nat) (layout : Layout)
    (literal : CNF.Literal (Fin n)) (labels : List (Fin n)) (lower cursor limit : Nat)
    (stored : RecordStorage.HeaderStored labels layout.touchedHeader lower cursor limit state.heap)
    (room : lower < cursor) :
    (∀ register : Fin 8, register ≠ 0 → register ≠ 4 →
      (touchedInserted state entry layout literal labels lower cursor limit stored room).reg register = state.reg register) ∧
    (touchedInserted state entry layout literal labels lower cursor limit stored room).stack = state.stack ∧
    (touchedInserted state entry layout literal labels lower cursor limit stored room).output = state.output := by
  refine ⟨?_, rfl, rfl⟩
  intro register address cursorRegister
  have preserved := (RecordStorage.finished_frame (touchedStart state entry layout.touchedHeader) labels
    layout.touchedHeader lower cursor limit stored room literal.1).1 register cursorRegister
  exact preserved.trans (by simp [touchedStart, State.put, State.advance, address])

theorem marked_position (state : State width 8) (layout : Layout) (literal : CNF.Literal (Fin n))
    (marks : Worklist.IndexedNormalize.Marks n) (stored : MarkStorage.Stored marks layout.markBase state.heap)
    (entry : Nat) (position : state.pc = word width (entry + 24)) (capacity : entry + 26 < 2 ^ width) :
    (marked state layout literal marks stored).pc = word width (entry + 26) := by
  simp only [marked, markStart, State.put, State.advance, position,
    word_val (width := width) (entry + 24) (by omega), word_val (width := width) (entry + 25) (by omega)]
  all_goals rfl

theorem marked_frame (state : State width 8) (layout : Layout) (literal : CNF.Literal (Fin n))
    (marks : Worklist.IndexedNormalize.Marks n) (stored : MarkStorage.Stored marks layout.markBase state.heap) :
    (∀ register : Fin 8, register ≠ 0 → (marked state layout literal marks stored).reg register = state.reg register) ∧
    (marked state layout literal marks stored).stack = state.stack ∧
    (marked state layout literal marks stored).output = state.output ∧
    (∀ index : Nat, MarkStorage.address layout.markBase literal ≠ index →
      (marked state layout literal marks stored).heap[index]? = state.heap[index]?) := by
  refine ⟨?_, rfl, rfl, ?_⟩
  · intro register address
    simp [marked, markStart, State.put, State.advance, address]
  · intro index different
    exact Array.getElem?_set_ne (stored.bound literal) different

/-- A scalar flag or mark update preserves a disjoint header/list pair. -/
theorem header_after_store {labels : List (Fin n)} {header lower cursor limit : Nat}
    {heap : Array (Word width)} (represented : RecordStorage.HeaderStored labels header lower cursor limit heap)
    (index : Nat) (valid : index < heap.size) (value : Word width)
    (outside : index < lower ∨ limit ≤ index) (different : index ≠ header) :
    RecordStorage.HeaderStored labels header lower cursor limit (heap.set index value valid) := by
  refine ⟨RecordStorage.buffer_after_store represented.buffer index valid value outside,
    by simpa using represented.bound, represented.separate, ?_⟩
  exact (Array.getElem_set_ne valid represented.bound different).trans represented.value

/-- A flag store outside the mark region preserves both polarities of every
channel, supplying the representation for the final actual mark instruction. -/
theorem marks_after_store {marks : Worklist.IndexedNormalize.Marks n} {base : Nat}
    {heap : Array (Word width)} (represented : MarkStorage.Stored marks base heap)
    (index : Nat) (valid : index < heap.size) (value : Word width)
    (outside : index < base ∨ base + 2 * n ≤ index) :
    MarkStorage.Stored marks base (heap.set index value valid) := by
  refine ⟨by simpa using represented.fits, ?_⟩
  intro literal
  have upper := MarkStorage.address_lt base literal
  have lower : base ≤ MarkStorage.address base literal := by
    unfold MarkStorage.address
    omega
  have different : index ≠ MarkStorage.address base literal := by omega
  exact (Array.getElem_set_ne valid (represented.bound literal) different).trans (represented.entry literal)

end Controller.Horn.LiteralDispatch

namespace Controller.Horn.LiteralDispatch

open Controller.Horn.Worklist Controller.Horn.Worklist.IndexedNormalize

/-- Correct suffix normalization guarantees a declared-channel-sized buffer has
room whenever the selected sign is fresh. -/
theorem signed_room_of_correct (clause : CNF.Clause (Fin n)) (row : Row n)
    (correct : row.Correct clause) (literal : CNF.Literal (Fin n))
    (fresh : row.marks.read literal = false) (lower cursor : Nat)
    (heap : Array (Cost.Word width))
    (stored : LabelBuffer.BufferStored
      (if literal.2 then row.positive else row.negative) lower cursor (lower + n) heap) :
    lower < cursor := by
  have absent : literal ∉ clause := by
    have marked := correct.marked literal
    rw [fresh] at marked
    simpa using marked.symm
  apply LabelBuffer.room_of_fresh stored _ literal.1 _
  · cases sign : literal.2
    · simpa [sign, correct.negative, signedLabels] using
        List.nodup_dedup (((clause.filter fun lit => decide (lit.2 = false)).map Prod.fst))
    · simpa [sign, correct.positive, signedLabels] using
        List.nodup_dedup (((clause.filter fun lit => decide (lit.2 = true)).map Prod.fst))
  · cases sign : literal.2
    · simpa [sign, correct.negative, mem_signedLabels] using (show (literal.1, literal.2) ∉ clause from absent)
    · simpa [sign, correct.positive, mem_signedLabels] using (show (literal.1, literal.2) ∉ clause from absent)

/-- A fresh channel has neither polarity in the suffix, so its touched buffer
also has room without an ambient variable scan. -/
theorem touched_room_of_correct (clause : CNF.Clause (Fin n)) (row : Row n)
    (correct : row.Correct clause) (literal : CNF.Literal (Fin n))
    (same : row.marks.read literal = false)
    (opposite : row.marks.read (CNF.negate literal) = false)
    (lower cursor : Nat) (heap : Array (Cost.Word width))
    (stored : LabelBuffer.BufferStored row.touched lower cursor (lower + n) heap) :
    lower < cursor := by
  apply LabelBuffer.room_of_fresh stored (Row.touched_nodup correct) literal.1
  intro touched
  have any := Row.any_mark_correct correct literal.1
  have present : literal.1 ∈ clause.map Prod.fst := by
    simpa [correct.touched] using touched
  rw [show decide (literal.1 ∈ clause.map Prod.fst) = true by simp [present]] at any
  rcases literal with ⟨label, sign⟩
  cases sign <;> simp_all [Marks.read, CNF.negate, Std.Sat.Literal.negate]

end Controller.Horn.LiteralDispatch

namespace Controller.Horn.LiteralDispatch

open Controller.Cost Controller.Horn.Worklist Controller.Horn.Worklist.IndexedNormalize

/-- Scratch addresses reserve all declared channels, including unused ones. -/
def rowLayout (n base : Nat) : NormalizeProgram.Layout :=
  ⟨base, base + 2 * n, base + 2 * n + 1, base + 2 * n + 2, base + 2 * n + 3⟩

/-- Representation used at a row boundary. The flag is an actual heap word,
and all three list cursors are actual heap headers. Regions are disjoint by
construction, rather than by an assumed update-time frame oracle. -/
structure RowStored (row : Row n) (base positiveCursor negativeCursor touchedCursor : Nat)
    (heap : Array (Word width)) : Prop where
  marks : MarkStorage.Stored row.marks base heap
  positive : RecordStorage.HeaderStored row.positive (base + 2 * n)
    (base + 2 * n + 4) positiveCursor (base + 3 * n + 4) heap
  negative : RecordStorage.HeaderStored row.negative (base + 2 * n + 1)
    (base + 3 * n + 4) negativeCursor (base + 4 * n + 4) heap
  touched : RecordStorage.HeaderStored row.touched (base + 2 * n + 2)
    (base + 4 * n + 4) touchedCursor (base + 5 * n + 4) heap
  flagBound : base + 2 * n + 3 < heap.size
  flag : heap[base + 2 * n + 3]'flagBound = MarkStorage.encode width row.tautology

theorem RowStored.scratch_fits (row : Row n) (base positiveCursor negativeCursor touchedCursor : Nat)
    (heap : Array (Word width))
    (stored : RowStored row base positiveCursor negativeCursor touchedCursor heap) :
    base + 5 * n + 4 ≤ heap.size := stored.touched.buffer.fits

theorem RowStored.positive_room (clause : CNF.Clause (Fin n)) (row : Row n)
    (correct : row.Correct clause) (label : Fin n) (fresh : row.marks.read (label, true) = false)
    (base positiveCursor negativeCursor touchedCursor : Nat) (heap : Array (Word width))
    (stored : RowStored row base positiveCursor negativeCursor touchedCursor heap) :
    base + 2 * n + 4 < positiveCursor := by
  apply signed_room_of_correct clause row correct (label, true) fresh
    (base + 2 * n + 4) positiveCursor heap
  change LabelBuffer.BufferStored row.positive (base + 2 * n + 4) positiveCursor (base + 2 * n + 4 + n) heap
  rw [show base + 2 * n + 4 + n = base + 3 * n + 4 by omega]
  exact stored.positive.buffer

theorem RowStored.negative_room (clause : CNF.Clause (Fin n)) (row : Row n)
    (correct : row.Correct clause) (label : Fin n) (fresh : row.marks.read (label, false) = false)
    (base positiveCursor negativeCursor touchedCursor : Nat) (heap : Array (Word width))
    (stored : RowStored row base positiveCursor negativeCursor touchedCursor heap) :
    base + 3 * n + 4 < negativeCursor := by
  apply signed_room_of_correct clause row correct (label, false) fresh
    (base + 3 * n + 4) negativeCursor heap
  change LabelBuffer.BufferStored row.negative (base + 3 * n + 4) negativeCursor (base + 3 * n + 4 + n) heap
  rw [show base + 3 * n + 4 + n = base + 4 * n + 4 by omega]
  exact stored.negative.buffer

theorem RowStored.touched_room (clause : CNF.Clause (Fin n)) (row : Row n)
    (correct : row.Correct clause) (literal : CNF.Literal (Fin n))
    (same : row.marks.read literal = false) (opposite : row.marks.read (CNF.negate literal) = false)
    (base positiveCursor negativeCursor touchedCursor : Nat) (heap : Array (Word width))
    (stored : RowStored row base positiveCursor negativeCursor touchedCursor heap) :
    base + 4 * n + 4 < touchedCursor := by
  apply touched_room_of_correct clause row correct literal same opposite
    (base + 4 * n + 4) touchedCursor heap
  change LabelBuffer.BufferStored row.touched (base + 4 * n + 4) touchedCursor (base + 4 * n + 4 + n) heap
  rw [show base + 4 * n + 4 + n = base + 5 * n + 4 by omega]
  exact stored.touched.buffer

end Controller.Horn.LiteralDispatch

namespace Controller.Horn.LiteralDispatch

open Controller.Cost Controller.Horn.Worklist.IndexedNormalize

/-- The actual positive-header update composes with the complete row heap
representation, including untouched sign lists, marks and the conflict flag. -/
theorem RowStored.prepend_positive (state : State width 8) (row : Row n) (label : Fin n)
    (base positiveCursor negativeCursor touchedCursor : Nat)
    (stored : RowStored row base positiveCursor negativeCursor touchedCursor state.heap)
    (room : base + 2 * n + 4 < positiveCursor) :
    RowStored { row with positive := label :: row.positive }
      base (positiveCursor - 1) negativeCursor touchedCursor
      (RecordStorage.finished state row.positive (base + 2 * n) (base + 2 * n + 4)
        positiveCursor (base + 3 * n + 4) stored.positive room label).heap := by
  have upper : positiveCursor ≤ base + 3 * n + 4 := by
    have := stored.positive.buffer.ends
    omega
  have labelLower : base + 2 * n + 4 ≤ positiveCursor - 1 := by omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact RecordStorage.finished_preserves_marks state row.positive (base + 2 * n)
      (base + 2 * n + 4) positiveCursor (base + 3 * n + 4) stored.positive room label
      row.marks base stored.marks (Or.inr (by omega)) (Or.inr (by omega))
  · exact RecordStorage.finished_stored state row.positive (base + 2 * n)
      (base + 2 * n + 4) positiveCursor (base + 3 * n + 4) stored.positive room label
  · exact RecordStorage.finished_preserves_header state row.positive (base + 2 * n)
      (base + 2 * n + 4) positiveCursor (base + 3 * n + 4) stored.positive room label
      row.negative (base + 2 * n + 1) (base + 3 * n + 4) negativeCursor (base + 4 * n + 4)
      stored.negative (Or.inl (by omega)) (Or.inl (by omega)) (by omega) (by omega)
  · exact RecordStorage.finished_preserves_header state row.positive (base + 2 * n)
      (base + 2 * n + 4) positiveCursor (base + 3 * n + 4) stored.positive room label
      row.touched (base + 2 * n + 2) (base + 4 * n + 4) touchedCursor (base + 5 * n + 4)
      stored.touched (Or.inl (by omega)) (Or.inl (by omega)) (by omega) (by omega)
  · simpa [RecordStorage.finished] using stored.flagBound
  · have unchanged := RecordStorage.finished_heap_frame state row.positive (base + 2 * n)
      (base + 2 * n + 4) positiveCursor (base + 3 * n + 4) stored.positive room label
      (base + 2 * n + 3) (by omega) (by omega)
    have before : state.heap[base + 2 * n + 3]? = some (MarkStorage.encode width row.tautology) := by
      rw [Array.getElem?_eq_getElem stored.flagBound, stored.flag]
    have after := unchanged.trans before
    rw [Array.getElem?_eq_getElem (by simpa [RecordStorage.finished] using stored.flagBound)] at after
    exact Option.some.inj after

end Controller.Horn.LiteralDispatch

namespace Controller.Horn.LiteralDispatch

open Controller.Cost Controller.Horn.Worklist.IndexedNormalize

theorem RowStored.prepend_negative (state : State width 8) (row : Row n) (label : Fin n)
    (base positiveCursor negativeCursor touchedCursor : Nat)
    (stored : RowStored row base positiveCursor negativeCursor touchedCursor state.heap)
    (room : base + 3 * n + 4 < negativeCursor) :
    RowStored { row with negative := label :: row.negative }
      base positiveCursor (negativeCursor - 1) touchedCursor
      (RecordStorage.finished state row.negative (base + 2 * n + 1) (base + 3 * n + 4)
        negativeCursor (base + 4 * n + 4) stored.negative room label).heap := by
  have upper : negativeCursor ≤ base + 4 * n + 4 := by
    have := stored.negative.buffer.ends
    omega
  have labelLower : base + 3 * n + 4 ≤ negativeCursor - 1 := by omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact RecordStorage.finished_preserves_marks state row.negative (base + 2 * n + 1)
      (base + 3 * n + 4) negativeCursor (base + 4 * n + 4) stored.negative room label
      row.marks base stored.marks (Or.inr (by omega)) (Or.inr (by omega))
  · exact RecordStorage.finished_preserves_header state row.negative (base + 2 * n + 1)
      (base + 3 * n + 4) negativeCursor (base + 4 * n + 4) stored.negative room label
      row.positive (base + 2 * n) (base + 2 * n + 4) positiveCursor (base + 3 * n + 4)
      stored.positive (Or.inr (by omega)) (Or.inl (by omega)) (by omega) (by omega)
  · exact RecordStorage.finished_stored state row.negative (base + 2 * n + 1)
      (base + 3 * n + 4) negativeCursor (base + 4 * n + 4) stored.negative room label
  · exact RecordStorage.finished_preserves_header state row.negative (base + 2 * n + 1)
      (base + 3 * n + 4) negativeCursor (base + 4 * n + 4) stored.negative room label
      row.touched (base + 2 * n + 2) (base + 4 * n + 4) touchedCursor (base + 5 * n + 4)
      stored.touched (Or.inl (by omega)) (Or.inl (by omega)) (by omega) (by omega)
  · simpa [RecordStorage.finished] using stored.flagBound
  · have unchanged := RecordStorage.finished_heap_frame state row.negative (base + 2 * n + 1)
      (base + 3 * n + 4) negativeCursor (base + 4 * n + 4) stored.negative room label
      (base + 2 * n + 3) (by omega) (by omega)
    have before : state.heap[base + 2 * n + 3]? = some (MarkStorage.encode width row.tautology) := by
      rw [Array.getElem?_eq_getElem stored.flagBound, stored.flag]
    have after := unchanged.trans before
    rw [Array.getElem?_eq_getElem (by simpa [RecordStorage.finished] using stored.flagBound)] at after
    exact Option.some.inj after

theorem RowStored.prepend_touched (state : State width 8) (row : Row n) (label : Fin n)
    (base positiveCursor negativeCursor touchedCursor : Nat)
    (stored : RowStored row base positiveCursor negativeCursor touchedCursor state.heap)
    (room : base + 4 * n + 4 < touchedCursor) :
    RowStored { row with touched := label :: row.touched }
      base positiveCursor negativeCursor (touchedCursor - 1)
      (RecordStorage.finished state row.touched (base + 2 * n + 2) (base + 4 * n + 4)
        touchedCursor (base + 5 * n + 4) stored.touched room label).heap := by
  have labelLower : base + 4 * n + 4 ≤ touchedCursor - 1 := by omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact RecordStorage.finished_preserves_marks state row.touched (base + 2 * n + 2)
      (base + 4 * n + 4) touchedCursor (base + 5 * n + 4) stored.touched room label
      row.marks base stored.marks (Or.inr (by omega)) (Or.inr (by omega))
  · exact RecordStorage.finished_preserves_header state row.touched (base + 2 * n + 2)
      (base + 4 * n + 4) touchedCursor (base + 5 * n + 4) stored.touched room label
      row.positive (base + 2 * n) (base + 2 * n + 4) positiveCursor (base + 3 * n + 4)
      stored.positive (Or.inr (by omega)) (Or.inl (by omega)) (by omega) (by omega)
  · exact RecordStorage.finished_preserves_header state row.touched (base + 2 * n + 2)
      (base + 4 * n + 4) touchedCursor (base + 5 * n + 4) stored.touched room label
      row.negative (base + 2 * n + 1) (base + 3 * n + 4) negativeCursor (base + 4 * n + 4)
      stored.negative (Or.inr (by omega)) (Or.inl (by omega)) (by omega) (by omega)
  · exact RecordStorage.finished_stored state row.touched (base + 2 * n + 2)
      (base + 4 * n + 4) touchedCursor (base + 5 * n + 4) stored.touched room label
  · simpa [RecordStorage.finished] using stored.flagBound
  · have unchanged := RecordStorage.finished_heap_frame state row.touched (base + 2 * n + 2)
      (base + 4 * n + 4) touchedCursor (base + 5 * n + 4) stored.touched room label
      (base + 2 * n + 3) (by omega) (by omega)
    have before : state.heap[base + 2 * n + 3]? = some (MarkStorage.encode width row.tautology) := by
      rw [Array.getElem?_eq_getElem stored.flagBound, stored.flag]
    have after := unchanged.trans before
    rw [Array.getElem?_eq_getElem (by simpa [RecordStorage.finished] using stored.flagBound)] at after
    exact Option.some.inj after

end Controller.Horn.LiteralDispatch

namespace Controller.Horn.LiteralDispatch

open Controller.Cost Controller.Horn.Worklist.IndexedNormalize

theorem RowStored.set_conflict (state : State width 8) (row : Row n)
    (base positiveCursor negativeCursor touchedCursor : Nat)
    (stored : RowStored row base positiveCursor negativeCursor touchedCursor state.heap) :
    RowStored { row with tautology := true } base positiveCursor negativeCursor touchedCursor
      (conflicted state (base + 2 * n + 3) stored.flagBound).heap := by
  refine ⟨?_, ?_, ?_, ?_, by simpa [conflicted] using stored.flagBound, ?_⟩
  · exact marks_after_store stored.marks (base + 2 * n + 3) stored.flagBound
      (MarkStorage.encode width true) (Or.inr (by omega))
  · exact header_after_store stored.positive (base + 2 * n + 3) stored.flagBound
      (MarkStorage.encode width true) (Or.inl (by omega)) (by omega)
  · exact header_after_store stored.negative (base + 2 * n + 3) stored.flagBound
      (MarkStorage.encode width true) (Or.inl (by omega)) (by omega)
  · exact header_after_store stored.touched (base + 2 * n + 3) stored.flagBound
      (MarkStorage.encode width true) (Or.inl (by omega)) (by omega)
  · exact conflicted_flag state (base + 2 * n + 3) stored.flagBound

theorem RowStored.set_mark (state : State width 8) (row : Row n) (literal : CNF.Literal (Fin n))
    (base positiveCursor negativeCursor touchedCursor : Nat)
    (stored : RowStored row base positiveCursor negativeCursor touchedCursor state.heap) :
    RowStored { row with marks := MarkStorage.write row.marks literal true }
      base positiveCursor negativeCursor touchedCursor
      (marked state (rowLayout n base) literal row.marks stored.marks).heap := by
  have upper := MarkStorage.address_lt base literal
  refine ⟨?_, ?_, ?_, ?_, by simpa [marked] using stored.flagBound, ?_⟩
  · exact stored.marks.write literal true
  · exact header_after_store stored.positive (MarkStorage.address base literal)
      (stored.marks.bound literal) (MarkStorage.encode width true) (Or.inl (by omega)) (by omega)
  · exact header_after_store stored.negative (MarkStorage.address base literal)
      (stored.marks.bound literal) (MarkStorage.encode width true) (Or.inl (by omega)) (by omega)
  · exact header_after_store stored.touched (MarkStorage.address base literal)
      (stored.marks.bound literal) (MarkStorage.encode width true) (Or.inl (by omega)) (by omega)
  · have different : MarkStorage.address base literal ≠ base + 2 * n + 3 := by omega
    exact (Array.getElem_set_ne (stored.marks.bound literal) stored.flagBound different).trans stored.flag

end Controller.Horn.LiteralDispatch

namespace Controller.Horn.LiteralDispatch

open Controller.Horn.Worklist.IndexedNormalize

/-- The stage order implemented by the literal block equals the accepted
semantic `Row.record`, including opposite-sign conflicts and duplicated labels. -/
theorem record_stage_decomposition (row : Row n) (literal : CNF.Literal (Fin n)) :
    (let signed := if row.marks.read literal then row else
        if literal.2 then { row with positive := literal.1 :: row.positive }
        else { row with negative := literal.1 :: row.negative }
     let conflicted := if row.marks.read (CNF.negate literal) then
        { signed with tautology := true } else signed
     let touched := if row.marks.read literal || row.marks.read (CNF.negate literal) then
        conflicted else { conflicted with touched := literal.1 :: row.touched }
     { touched with marks := MarkStorage.write row.marks literal true }) = row.record literal := by
  rcases literal with ⟨label, sign⟩
  cases old : row.marks[label.val] with
  | mk positive negative =>
    cases positive <;> cases negative <;> cases sign <;>
      simp [Marks.read, CNF.negate, Std.Sat.Literal.negate, old, Row.record, MarkStorage.write]

end Controller.Horn.LiteralDispatch
