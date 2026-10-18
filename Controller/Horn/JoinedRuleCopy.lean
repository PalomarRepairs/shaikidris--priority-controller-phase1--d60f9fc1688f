module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Horn.JoinedDispatch

@[expose] public section

/-!
# Physical normalized-rule record construction

The combined program selects a tag and head from stored scratch data, appends
one record for every source row, copies an active body's actual positive buffer,
and updates the persistent record cursor using the runtime visit counter.
Inert records retain a zero count and bypass the buffer even when it is nonempty.
-/
namespace Controller.Horn.JoinedRuleCopy

open Controller.Cost Controller.Horn.Worklist Controller.Horn.Worklist.IndexedNormalize

@[simp] private theorem word_val (value : Nat) (fits : value < 2 ^ width) :
    (word width value).val = value := Nat.mod_eq_of_lt fits

private theorem advance_position (state : Controller.Cost.State width 8) (entry : Nat)
    (position : state.pc = word width entry) (fits : entry < 2 ^ width) :
    state.advance.pc = word width (entry + 1) := by
  simp only [Controller.Cost.State.advance, position, word_val (width := width) entry fits]

/-- The complete record-copy block has forty-two stored instructions.
Its return is the entry of the separate scratch-reset block. -/
def code (width n entry base cursorHeader : Nat) : Program width 8 :=
  Controller.Horn.RuleDispatch.code width n entry base (entry + 17) ++
  Controller.Horn.RuleCopy.recordAddressCode width cursorHeader ++
  Controller.Horn.RuleCopy.headerCode width ++
  Controller.Horn.RuleDispatch.skipCode width (entry + 37) ++
  Controller.Horn.RuleCopy.setupCode width (base + 2 * n) ++
  Controller.Horn.RuleCopy.bodyCode width (entry + 29) (base + 3 * n + 4) (entry + 37) ++
  Controller.Horn.RuleCopy.finishCode width ++
  Controller.Horn.RuleCopy.cursorUpdateCode width cursorHeader

@[simp] theorem code_size (width n entry base cursorHeader : Nat) :
    (code width n entry base cursorHeader).size = 42 := by
  simp [code]

/-- Exact same-program entry points for all fetched stage consumers. -/
structure CodeAt (program : Program width 8) (entry base cursorHeader n : Nat) : Prop where
  selection : Controller.Horn.RuleDispatch.CodeAt program entry base (entry + 17) n
  address : Controller.Horn.RuleCopy.RecordAddressAt program (entry + 17) cursorHeader
  header : Controller.Horn.RuleCopy.HeaderAt program (entry + 21)
  bypass : program[entry + 24]? = some (.constant 4 (word width 0)) ∧
    program[entry + 25]? = some (.branchZero 1 (word width (entry + 37)))
  setup : Controller.Horn.RuleCopy.SetupAt program (entry + 26) (base + 2 * n)
  body : Controller.Horn.RuleCopy.BodyAt program (entry + 29) (base + 3 * n + 4) (entry + 37)
  finish : Controller.Horn.RuleCopy.FinishAt program (entry + 37)
  cursor : Controller.Horn.RuleCopy.CursorUpdateAt program (entry + 38) cursorHeader

def bypassFinished (state : Controller.Cost.State width 8) (exit : Nat) : Controller.Cost.State width 8 :=
  Controller.Horn.RuleDispatch.branchFinished (state.advance.put 4 (word width 0)) 1 exit

theorem address_position (state : Controller.Cost.State width 8) (entry header start : Nat)
    (position : state.pc = word width entry) (capacity : entry + 4 < 2 ^ width) :
    (Controller.Horn.RuleCopy.recordAddressFinished state header start).pc = word width (entry + 4) := by
  let a := state.advance.put 7 (word width header)
  let b := a.advance.put 7 (word width start)
  let c := b.advance.put 7 (word width (start + 1))
  have pa : a.pc = word width (entry + 1) := advance_position state entry position (by omega)
  have pb : b.pc = word width (entry + 2) := by
    simpa [b, Controller.Cost.State.put, Nat.add_assoc] using advance_position a (entry + 1) pa (by omega)
  have pc : c.pc = word width (entry + 3) := by
    simpa [c, Controller.Cost.State.put, Nat.add_assoc] using advance_position b (entry + 2) pb (by omega)
  simpa [Controller.Horn.RuleCopy.recordAddressFinished, a, b, c, Controller.Cost.State.put, Nat.add_assoc] using
    advance_position c (entry + 3) pc (by omega)

theorem header_position (state : Controller.Cost.State width 8) (entry : Nat)
    (position : state.pc = word width entry) (capacity : entry + 3 < 2 ^ width) :
    (Controller.Horn.RuleCopy.headerFinished state).pc = word width (entry + 3) := by
  let a := { state.advance with heap := state.heap.push (state.reg 1) }
  let b := { a.advance with heap := a.heap.push (a.reg 3) }
  have pa : a.pc = word width (entry + 1) := advance_position state entry position (by omega)
  have pb : b.pc = word width (entry + 2) := by
    simpa [b, Controller.Cost.State.put, Nat.add_assoc] using advance_position a (entry + 1) pa (by omega)
  simpa [Controller.Horn.RuleCopy.headerFinished, a, b, Controller.Cost.State.advance, Nat.add_assoc] using
    advance_position b (entry + 2) pb (by omega)

/-- Both runtime tags execute the same two fetched bypass instructions. Only
an actual zero tag jumps over positive-buffer setup and traversal. -/
theorem bypass_execution (program : Program width 8) (entry exit : Nat)
    (present : program[entry]? = some (.constant 4 (word width 0)) ∧
      program[entry + 1]? = some (.branchZero 1 (word width exit)))
    (state : Controller.Cost.State width 8) (position : state.pc = word width entry)
    (running : state.halted = false) (capacity : entry + 2 < 2 ^ width) :
    Execution program state (bypassFinished state exit) 2 state.liveWords := by
  let middle := state.advance.put 4 (word width 0)
  have first : programStep program state = some middle := by
    unfold programStep
    rw [position, word_val (width := width) entry (by omega), present.1]
    change step (.constant 4 (word width 0)) state = _
    simp [step, middle, running]
  have middlePC : middle.pc = word width (entry + 1) :=
    advance_position state entry position (by omega)
  have second := Controller.Horn.RuleDispatch.branch_execution program (entry + 1) exit 1
    present.2 middle middlePC running (by omega)
  have trace := (Execution.cons first (Execution.refl middle)).append second
  simpa [bypassFinished, middle, Controller.Cost.State.liveWords, Controller.Cost.State.advance, Controller.Cost.State.put] using trace

theorem bypass_frame (state : Controller.Cost.State width 8) (exit : Nat) :
    (bypassFinished state exit).heap = state.heap ∧
    (bypassFinished state exit).stack = state.stack ∧
    (bypassFinished state exit).output = state.output ∧
    (bypassFinished state exit).reg 4 = word width 0 ∧
    (∀ register : Fin 8, register ≠ 4 →
      (bypassFinished state exit).reg register = state.reg register) ∧
    (bypassFinished state exit).halted = state.halted := by
  unfold bypassFinished Controller.Horn.RuleDispatch.branchFinished
  split <;> constructor <;> simp [Controller.Cost.State.advance, Controller.Cost.State.put]
    <;> intro register different equal <;> exact (different equal).elim

theorem bypass_position (state : Controller.Cost.State width 8) (entry exit : Nat)
    (position : state.pc = word width entry) (capacity : entry + 2 < 2 ^ width) :
    (bypassFinished state exit).pc =
      if (state.reg 1).val = 0 then word width exit else word width (entry + 2) := by
  simp only [bypassFinished, Controller.Horn.RuleDispatch.branchFinished]
  have held : ((state.advance.put 4 (word width 0)).reg 1).val = (state.reg 1).val := by
    simp [Controller.Cost.State.advance, Controller.Cost.State.put]
  rw [held]
  split
  · rfl
  · have middlePC : (state.advance.put 4 (word width 0)).pc = word width (entry + 1) :=
      advance_position state entry position (by omega)
    simpa [Nat.add_assoc] using advance_position (state.advance.put 4 (word width 0))
      (entry + 1) middlePC (by omega)

/-- Before the count store, all record words are physically allocated. -/
def allocatedHeap (heap : Array (Word width)) (rule : Rule (Fin n)) : Array (Word width) :=
  ((heap.push (word width (Controller.Horn.RuleCopy.tag rule))).push
    (Controller.Horn.RuleCopy.headWord width rule)).push (word width 0)

@[simp] theorem allocatedHeap_size (heap : Array (Word width)) (rule : Rule (Fin n)) :
    (allocatedHeap heap rule).size = heap.size + 3 := by
  simp [allocatedHeap, Nat.add_assoc]

/-- Actual allocation preserves every original source and scratch cell. -/
theorem allocatedHeap_frame (heap : Array (Word width)) (rule : Rule (Fin n))
    (index : Nat) (bound : index < heap.size) :
    (allocatedHeap heap rule)[index]'(by simp <;> omega) = heap[index] := by
  simp only [allocatedHeap]
  rw [Array.getElem_push_lt (by simp <;> omega), Array.getElem_push_lt (by simp <;> omega),
    Array.getElem_push_lt bound]

/-- The actual appended header is not an abstract record write. -/
theorem allocated_header (heap : Array (Word width)) (rule : Rule (Fin n)) :
    (allocatedHeap heap rule)[heap.size]'(by simp) = word width (Controller.Horn.RuleCopy.tag rule) ∧
    (allocatedHeap heap rule)[heap.size + 1]'(by simp <;> omega) = Controller.Horn.RuleCopy.headWord width rule ∧
    (allocatedHeap heap rule)[heap.size + 2]'(by simp <;> omega) = word width 0 := by
  simp [allocatedHeap, Array.getElem_push, Nat.add_assoc]

/-- The fetched allocator appends precisely the physically selected words. -/
theorem header_execution_heap (state : Controller.Cost.State width 8) (rule : Rule (Fin n))
    (tagHeld : state.reg 1 = word width (Controller.Horn.RuleCopy.tag rule))
    (headHeld : state.reg 3 = Controller.Horn.RuleCopy.headWord width rule)
    (zero : state.reg 2 = word width 0) :
    (Controller.Horn.RuleCopy.headerFinished state).heap = allocatedHeap state.heap rule := by
  simp [Controller.Horn.RuleCopy.headerFinished, allocatedHeap, Controller.Cost.State.advance,
    tagHeld, headHeld, zero]

/-- A skip record has no body even if the normalized scratch buffer does. -/
theorem skip_body (row : Row n) (inert : row.tautology = true) :
    row.rule.positives = [] ∧ Controller.Horn.RuleCopy.tag row.rule = 0 ∧
    Controller.Horn.RuleCopy.headWord width row.rule = word width 0 := by
  simp [Row.rule, inert, Controller.Horn.RuleCopy.tag, Controller.Horn.RuleCopy.headWord,
    Rule.positives]

/-- Active selected records copy exactly the normalized positive source buffer. -/
theorem active_body (row : Row n) (active : row.tautology = false) :
    row.rule.positives = row.positive := by
  cases negatives : row.negative <;>
    simp [Row.rule, active, negatives, Rule.positives]

/-- An inert header is already a complete zero-body physical rule record. -/
theorem allocated_skip_stored (heap : Array (Word width)) (positiveWidth : 0 < 2 ^ width) :
    Controller.Horn.RuleCopy.Stored (.skip : Rule (Fin n)) heap.size
      (allocatedHeap heap (.skip : Rule (Fin n))) := by
  have header := allocated_header heap (.skip : Rule (Fin n))
  refine ⟨by simp [Rule.positives], by simpa [Rule.positives] using positiveWidth,
    header.1, header.2.1, ?_, ?_⟩
  · simpa [Rule.positives] using header.2.2
  · refine ⟨by simp [Rule.positives], ?_⟩
    intro index
    exact Fin.elim0 index

/-- Actual selection, physical record-cursor loading and header allocation
reach the runtime bypass with the complete scratch row still stored. -/
theorem record_prefix_execution (program : Program width 8) (entry base cursorHeader pcur ncur tcur : Nat)
    (present : CodeAt program entry base cursorHeader n)
    (state : Controller.Cost.State width 8) (row : Row n)
    (stored : Controller.Horn.LiteralDispatch.RowStored row base pcur ncur tcur state.heap)
    (supported : Controller.Horn.RuleDispatch.Supported row)
    (cursor : Controller.Horn.SourceScan.CursorStored state.heap.size cursorHeader state.heap)
    (position : state.pc = word width entry) (zero : state.reg 2 = word width 0)
    (one : state.reg 5 = word width 1) (running : state.halted = false)
    (capacity : entry + 42 < 2 ^ width) (heapFits : state.heap.size + 3 < 2 ^ width) :
    ∃ final : Controller.Cost.State width 8,
      Execution program state final (if row.tautology then 13 else 18) (state.liveWords + 3) ∧
      final.heap = allocatedHeap state.heap row.rule ∧
      Controller.Horn.LiteralDispatch.RowStored row base pcur ncur tcur final.heap ∧
      final.pc = word width (entry + 24) ∧
      final.reg 1 = word width (Controller.Horn.RuleCopy.tag row.rule) ∧
      final.reg 3 = Controller.Horn.RuleCopy.headWord width row.rule ∧
      final.reg 7 = word width (state.heap.size + 2) ∧
      final.reg 2 = word width 0 ∧ final.reg 5 = word width 1 ∧
      final.reg 6 = state.reg 6 ∧ final.halted = false ∧
      final.stack = state.stack ∧ final.output = state.output := by
  obtain ⟨selected, selection, frame, selectedPC, tagHeld, headHeld⟩ :=
    Controller.Horn.JoinedDispatch.selection_execution program entry base (entry + 17)
      pcur ncur tcur present.selection state row stored supported position zero running
      (by omega) (by omega)
  let address := Controller.Horn.RuleCopy.recordAddressFinished selected cursorHeader state.heap.size
  have selectedCursor : Controller.Horn.SourceScan.CursorStored state.heap.size cursorHeader selected.heap := by
    rw [frame.heap]
    exact cursor
  have addressTrace := Controller.Horn.RuleCopy.record_address_execution program (entry + 17)
    cursorHeader state.heap.size present.address selected selectedCursor selectedPC
    (frame.running.trans running) (frame.one.trans one) (by omega) (by omega)
    (by rw [frame.heap]; omega)
  have addressPC : address.pc = word width (entry + 21) := by
    simpa [address, Nat.add_assoc] using address_position selected (entry + 17)
      cursorHeader state.heap.size selectedPC (by omega)
  have addressHeap : address.heap = state.heap := by
    simpa [address, Controller.Horn.RuleCopy.recordAddressFinished, Controller.Cost.State.advance, Controller.Cost.State.put] using frame.heap
  have addressTag : address.reg 1 = word width (Controller.Horn.RuleCopy.tag row.rule) := by
    simpa [address, Controller.Horn.RuleCopy.recordAddressFinished, Controller.Cost.State.advance, Controller.Cost.State.put] using tagHeld
  have addressHead : address.reg 3 = Controller.Horn.RuleCopy.headWord width row.rule := by
    simpa [address, Controller.Horn.RuleCopy.recordAddressFinished, Controller.Cost.State.advance, Controller.Cost.State.put] using headHeld
  have addressZero : address.reg 2 = word width 0 := by
    simpa [address, Controller.Horn.RuleCopy.recordAddressFinished, Controller.Cost.State.advance, Controller.Cost.State.put] using frame.zero.trans zero
  have addressRunning : address.halted = false := by
    simpa [address, Controller.Horn.RuleCopy.recordAddressFinished, Controller.Cost.State.advance, Controller.Cost.State.put] using frame.running.trans running
  let final := Controller.Horn.RuleCopy.headerFinished address
  have allocation := Controller.Horn.RuleCopy.header_execution program (entry + 21)
    present.header address addressPC addressRunning (by omega) (by rw [addressHeap]; exact heapFits)
  have trace := (selection.append addressTrace).append allocation
  have heap : final.heap = allocatedHeap state.heap row.rule := by
    rw [show final.heap = allocatedHeap address.heap row.rule from
      header_execution_heap address row.rule addressTag addressHead addressZero, addressHeap]
  have scratch : Controller.Horn.LiteralDispatch.RowStored row base pcur ncur tcur final.heap := by
    rw [heap]
    exact Controller.Horn.RuleCopy.row_after_push
      (Controller.Horn.RuleCopy.row_after_push
        (Controller.Horn.RuleCopy.row_after_push stored _) _) _
  have addressLive : address.liveWords = state.liveWords := by
    simp [address, Controller.Horn.RuleCopy.recordAddressFinished, Controller.Cost.State.liveWords,
      Controller.Cost.State.advance, Controller.Cost.State.put, frame.heap, frame.stack, frame.output]
  refine ⟨final, ?_, heap, scratch, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cases flag : row.tautology <;> simpa [flag, frame.liveWords, addressLive] using trace
  · simpa [final, Nat.add_assoc] using header_position address (entry + 21) addressPC (by omega)
  · simpa [final, Controller.Horn.RuleCopy.headerFinished, Controller.Cost.State.advance] using addressTag
  · simpa [final, Controller.Horn.RuleCopy.headerFinished, Controller.Cost.State.advance] using addressHead
  · simp [final, address, Controller.Horn.RuleCopy.headerFinished,
      Controller.Horn.RuleCopy.recordAddressFinished, Controller.Cost.State.advance, Controller.Cost.State.put]
  · simpa [final, Controller.Horn.RuleCopy.headerFinished, Controller.Cost.State.advance] using addressZero
  · simpa [final, address, Controller.Horn.RuleCopy.headerFinished,
      Controller.Horn.RuleCopy.recordAddressFinished, Controller.Cost.State.advance, Controller.Cost.State.put] using frame.one.trans one
  · simpa [final, address, Controller.Horn.RuleCopy.headerFinished,
      Controller.Horn.RuleCopy.recordAddressFinished, Controller.Cost.State.advance, Controller.Cost.State.put] using frame.decrement
  · simpa [final, Controller.Horn.RuleCopy.headerFinished, Controller.Cost.State.advance] using addressRunning
  · simpa [final, address, Controller.Horn.RuleCopy.headerFinished,
      Controller.Horn.RuleCopy.recordAddressFinished, Controller.Cost.State.advance, Controller.Cost.State.put] using frame.stack
  · simpa [final, address, Controller.Horn.RuleCopy.headerFinished,
      Controller.Horn.RuleCopy.recordAddressFinished, Controller.Cost.State.advance, Controller.Cost.State.put] using frame.output

theorem setup_position (state : Controller.Cost.State width 8) (entry header pointer : Nat)
    (position : state.pc = word width entry) (capacity : entry + 3 < 2 ^ width) :
    (Controller.Horn.RuleCopy.setupFinished state header pointer).pc = word width (entry + 3) := by
  let a := state.advance.put 0 (word width header)
  let b := a.advance.put 0 (word width pointer)
  have pa : a.pc = word width (entry + 1) := advance_position state entry position (by omega)
  have pb : b.pc = word width (entry + 2) := by
    simpa [b, Controller.Cost.State.put, Nat.add_assoc] using advance_position a (entry + 1) pa (by omega)
  simpa [Controller.Horn.RuleCopy.setupFinished, a, b, Controller.Cost.State.put, Nat.add_assoc] using
    advance_position b (entry + 2) pb (by omega)

/-- The active body route uses only the physically loaded cursor and the actual
visit counter. Its proof index retains every positive buffer occurrence. -/
theorem active_copy_execution (program : Program width 8) (entry base cursorHeader pcur ncur tcur : Nat)
    (present : CodeAt program entry base cursorHeader n)
    (state : Controller.Cost.State width 8) (row : Row n)
    (stored : Controller.Horn.LiteralDispatch.RowStored row base pcur ncur tcur state.heap)
    (active : row.tautology = false)
    (tagHeld : state.reg 1 = word width (Controller.Horn.RuleCopy.tag row.rule))
    (position : state.pc = word width (entry + 24))
    (zero : state.reg 2 = word width 0) (one : state.reg 5 = word width 1)
    (running : state.halted = false) (capacity : entry + 42 < 2 ^ width)
    (countFits : row.positive.length < 2 ^ width)
    (heapFits : state.heap.size + row.positive.length < 2 ^ width) :
    ∃ final : Controller.Cost.State width 8,
      Execution program state final (8 * row.positive.length + 8)
        (state.liveWords + row.positive.length) ∧
      final.heap = Controller.Horn.RuleCopy.copiedHeap state.heap row.positive ∧
      final.reg 4 = word width row.positive.length ∧
      final.reg 2 = word width 0 ∧ final.reg 5 = word width 1 ∧
      final.reg 6 = state.reg 6 ∧ final.reg 7 = state.reg 7 ∧
      final.halted = false ∧ final.pc = word width (entry + 37) ∧
      final.stack = state.stack ∧ final.output = state.output := by
  let bypass := bypassFinished state (entry + 37)
  have bypassFrame := bypass_frame state (entry + 37)
  have tags : Controller.Horn.RuleCopy.tag row.rule = 1 ∨
      Controller.Horn.RuleCopy.tag row.rule = 2 := by
    cases negatives : row.negative <;>
      simp [Row.rule, active, negatives, Controller.Horn.RuleCopy.tag]
  have tagFits : Controller.Horn.RuleCopy.tag row.rule < 2 ^ width := by rcases tags with h | h <;> omega
  have tagNonzero : Controller.Horn.RuleCopy.tag row.rule ≠ 0 := by rcases tags with h | h <;> omega
  have heldNonzero : (state.reg 1).val ≠ 0 := by
    rw [tagHeld, word_val (width := width) _ tagFits]
    exact tagNonzero
  have bypassPC : bypass.pc = word width (entry + 26) := by
    simpa [heldNonzero, Nat.add_assoc] using
      bypass_position state (entry + 24) (entry + 37) position (by omega)
  have bypassHeap : bypass.heap = state.heap := bypassFrame.1
  have bypassStack : bypass.stack = state.stack := bypassFrame.2.1
  have bypassOutput : bypass.output = state.output := bypassFrame.2.2.1
  have unchanged := bypassFrame.2.2.2.2.1
  have bypassRunning : bypass.halted = false := bypassFrame.2.2.2.2.2.trans running
  have bypassZero : bypass.reg 2 = word width 0 := (unchanged 2 (by decide)).trans zero
  have bypassOne : bypass.reg 5 = word width 1 := (unchanged 5 (by decide)).trans one
  have sourceCursor : Controller.Horn.SourceScan.CursorStored pcur (base + 2 * n) bypass.heap := by
    rw [bypassHeap]
    exact ⟨stored.positive.bound, stored.positive.value⟩
  let setup := Controller.Horn.RuleCopy.setupFinished bypass (base + 2 * n) pcur
  have first := bypass_execution program (entry + 24) (entry + 37) present.bypass
    state position running (by omega)
  have second := Controller.Horn.RuleCopy.setup_execution program (entry + 26)
    (base + 2 * n) pcur present.setup bypass sourceCursor bypassPC bypassRunning
    (by omega) (by rw [bypassHeap]; omega)
  have setupPC : setup.pc = word width (entry + 29) := by
    simpa [setup, Nat.add_assoc] using setup_position bypass (entry + 26)
      (base + 2 * n) pcur bypassPC (by omega)
  have setupHeap : setup.heap = state.heap := by
    simpa [setup, Controller.Horn.RuleCopy.setupFinished, Controller.Cost.State.advance, Controller.Cost.State.put] using bypassHeap
  have setupZero : setup.reg 2 = word width 0 := by
    simpa [setup, Controller.Horn.RuleCopy.setupFinished, Controller.Cost.State.advance, Controller.Cost.State.put] using bypassZero
  have setupOne : setup.reg 5 = word width 1 := by
    simpa [setup, Controller.Horn.RuleCopy.setupFinished, Controller.Cost.State.advance, Controller.Cost.State.put] using bypassOne
  obtain ⟨final, bodyTrace, heap, pointer, count, finalZero, finalOne,
    decrement, address, finalRunning, finalPC, stack, output⟩ :=
    Controller.Horn.RuleCopy.body_execution program (entry + 29) pcur
      (base + 3 * n + 4) (entry + 37) 0 present.body setup row.positive
      (by rw [setupHeap]; exact stored.positive.buffer.labels)
      stored.positive.buffer.ends setupPC (by simpa [setup, Controller.Horn.RuleCopy.setupFinished,
        Controller.Cost.State.advance, Controller.Cost.State.put] using bypassRunning)
      (by simp [setup, Controller.Horn.RuleCopy.setupFinished, Controller.Cost.State.advance, Controller.Cost.State.put])
      (by simp [setup, Controller.Horn.RuleCopy.setupFinished, Controller.Cost.State.advance, Controller.Cost.State.put])
      setupOne setupZero (by omega)
      (by have := stored.positive.buffer.fits; have := stored.positive.buffer.ends; omega)
      (by simpa using countFits) (by rw [setupHeap]; exact heapFits)
  have trace := (first.append second).append bodyTrace
  have bypassLive : bypass.liveWords = state.liveWords := by
    simp [Controller.Cost.State.liveWords, bypassHeap, bypassStack, bypassOutput]
  have setupLive : setup.liveWords = state.liveWords := by
    simp [setup, Controller.Horn.RuleCopy.setupFinished, Controller.Cost.State.liveWords, Controller.Cost.State.advance, Controller.Cost.State.put, bypassHeap, bypassStack, bypassOutput]
  refine ⟨final, ?_, ?_, ?_, finalZero, finalOne, ?_, ?_, finalRunning, finalPC, ?_, ?_⟩
  · convert trace using 1 <;> simp [bypassLive, setupLive, Nat.add_assoc] <;> omega
  · simpa [setupHeap] using heap
  · simpa using count
  · exact decrement.trans (by simpa [setup, Controller.Horn.RuleCopy.setupFinished,
      Controller.Cost.State.advance, Controller.Cost.State.put] using unchanged 6 (by decide))
  · exact address.trans (by simpa [setup, Controller.Horn.RuleCopy.setupFinished,
      Controller.Cost.State.advance, Controller.Cost.State.put] using unchanged 7 (by decide))
  · simpa [setup, Controller.Horn.RuleCopy.setupFinished, Controller.Cost.State.advance, Controller.Cost.State.put, bypassStack] using stack
  · simpa [setup, Controller.Horn.RuleCopy.setupFinished, Controller.Cost.State.advance, Controller.Cost.State.put, bypassOutput] using output

/-- A fetched count-store completes the allocated record using the live visit
counter. The source-label witness refers to physical copied cells. -/
theorem counted_record (state : Controller.Cost.State width 8) (rule : Rule (Fin n)) (offset : Nat)
    (fits : offset + 3 + rule.positives.length ≤ state.heap.size)
    (countFits : rule.positives.length < 2 ^ width)
    (tagValue : state.heap[offset]'(by omega) = word width (Controller.Horn.RuleCopy.tag rule))
    (headValue : state.heap[offset + 1]'(by omega) = Controller.Horn.RuleCopy.headWord width rule)
    (body : Controller.Horn.ResetTouched.LabelsStored rule.positives (offset + 3) state.heap)
    (counter : state.reg 4 = word width rule.positives.length) :
    Controller.Horn.RuleCopy.Stored rule offset
      (Controller.Horn.RuleCopy.finishStored state (offset + 2) (by omega)).heap := by
  let valid : offset + 2 < state.heap.size := by omega
  have size : (Controller.Horn.RuleCopy.finishStored state (offset + 2) valid).heap.size =
      state.heap.size := by simp [Controller.Horn.RuleCopy.finishStored]
  refine ⟨by rw [size]; exact fits, countFits, ?_, ?_, ?_, ?_⟩
  · exact (Controller.Horn.RuleCopy.finishStored_frame state (offset + 2) valid offset
      (by omega) (by omega)).trans tagValue
  · exact (Controller.Horn.RuleCopy.finishStored_frame state (offset + 2) valid (offset + 1)
      (by omega) (by omega)).trans headValue
  · exact (Controller.Horn.RuleCopy.finishStored_count state (offset + 2) valid).trans counter
  · refine ⟨by rw [size]; exact body.fits, ?_⟩
    intro index
    have old := body.entry index
    have bound : offset + 3 + index.val < state.heap.size := by
      have := index.isLt
      omega
    exact (Controller.Horn.RuleCopy.finishStored_frame state (offset + 2) valid
      (offset + 3 + index.val) bound (by omega)).trans old

/-- Full traversal appends a physical body after the three allocated header
cells. Both header words survive and body length counts source occurrences. -/
theorem copied_record_fields (heap : Array (Word width)) (rule : Rule (Fin n)) :
    (Controller.Horn.RuleCopy.copiedHeap (allocatedHeap heap rule) rule.positives)[heap.size]'(by simp <;> omega) =
      word width (Controller.Horn.RuleCopy.tag rule) ∧
    (Controller.Horn.RuleCopy.copiedHeap (allocatedHeap heap rule) rule.positives)[heap.size + 1]'(by simp <;> omega) =
      Controller.Horn.RuleCopy.headWord width rule ∧
    Controller.Horn.ResetTouched.LabelsStored rule.positives (heap.size + 3)
      (Controller.Horn.RuleCopy.copiedHeap (allocatedHeap heap rule) rule.positives) := by
  have header := allocated_header heap rule
  refine ⟨?_, ?_, ?_⟩
  · exact (Controller.Horn.RuleCopy.copiedHeap_frame (allocatedHeap heap rule) rule.positives
      heap.size (by simp)).trans header.1
  · exact (Controller.Horn.RuleCopy.copiedHeap_frame (allocatedHeap heap rule) rule.positives
      (heap.size + 1) (by simp <;> omega)).trans header.2.1
  · simpa using Controller.Horn.RuleCopy.copied_labels (allocatedHeap heap rule) rule.positives

/-- Updating the persistent cursor below the allocated record preserves every
record field, including head zero and each counted duplicate body occurrence. -/
theorem Stored.cursor_update {rule : Rule (Fin n)} {offset : Nat} {heap : Array (Word width)}
    (stored : Controller.Horn.RuleCopy.Stored rule offset heap) (header : Nat)
    (bound : header < heap.size) (beforeRecord : header < offset) (value : Word width) :
    Controller.Horn.RuleCopy.Stored rule offset (heap.set header value bound) := by
  refine ⟨by simpa using stored.fits, stored.countFits, ?_, ?_, ?_, ?_⟩
  · exact (Array.getElem_set_ne bound (by have := stored.fits; omega) (by omega)).trans stored.tagValue
  · exact (Array.getElem_set_ne bound (by have := stored.fits; omega) (by omega)).trans stored.headValue
  · exact (Array.getElem_set_ne bound (by have := stored.fits; omega) (by omega)).trans stored.countValue
  · refine ⟨by simpa using stored.body.fits, ?_⟩
    intro index
    have valid : offset + 3 + index.val < heap.size := by
      have := index.isLt
      have := stored.fits
      omega
    exact (Array.getElem_set_ne bound valid (by omega)).trans (stored.body.entry index)

/-- The fetched count store and persistent cursor update complete an actual
record in five executed instructions, retaining the physical copied body. -/
theorem finish_record_execution (program : Program width 8) (entry cursorHeader offset : Nat)
    (finishAt : Controller.Horn.RuleCopy.FinishAt program entry)
    (cursorAt : Controller.Horn.RuleCopy.CursorUpdateAt program (entry + 1) cursorHeader)
    (state : Controller.Cost.State width 8) (rule : Rule (Fin n))
    (fits : offset + 3 + rule.positives.length = state.heap.size)
    (countFits : rule.positives.length < 2 ^ width)
    (tagValue : state.heap[offset]'(by omega) = word width (Controller.Horn.RuleCopy.tag rule))
    (headValue : state.heap[offset + 1]'(by omega) = Controller.Horn.RuleCopy.headWord width rule)
    (body : Controller.Horn.ResetTouched.LabelsStored rule.positives (offset + 3) state.heap)
    (counter : state.reg 4 = word width rule.positives.length)
    (address : state.reg 7 = word width (offset + 2))
    (headerBound : cursorHeader < state.heap.size) (beforeRecord : cursorHeader < offset)
    (position : state.pc = word width entry) (one : state.reg 5 = word width 1)
    (running : state.halted = false) (capacity : entry + 5 < 2 ^ width)
    (heapFits : state.heap.size < 2 ^ width) :
    ∃ final : Controller.Cost.State width 8,
      Execution program state final 5 state.liveWords ∧
      Controller.Horn.RuleCopy.Stored rule offset final.heap ∧
      Controller.Horn.SourceScan.CursorStored final.heap.size cursorHeader final.heap ∧
      final.heap.size = state.heap.size := by
  let bound : offset + 2 < state.heap.size := by omega
  let middle := Controller.Horn.RuleCopy.finishStored state (offset + 2) bound
  have middleSize : middle.heap.size = state.heap.size := by
    simp [middle, Controller.Horn.RuleCopy.finishStored]
  have middlePC : middle.pc = word width (entry + 1) := by
    simpa [middle, Controller.Horn.RuleCopy.finishStored] using
      advance_position state entry position (by omega)
  have middleStored : Controller.Horn.RuleCopy.Stored rule offset middle.heap :=
    counted_record state rule offset (by omega) countFits tagValue headValue body counter
  have nextBound : cursorHeader < middle.heap.size := by rw [middleSize]; exact headerBound
  let final := Controller.Horn.RuleCopy.cursorUpdateFinished middle cursorHeader (offset + 2)
    rule.positives.length nextBound
  have first := Controller.Horn.RuleCopy.finish_execution program entry (offset + 2)
    finishAt state bound position address running (by omega) heapFits
  have second := Controller.Horn.RuleCopy.cursor_update_execution program (entry + 1)
    cursorHeader (offset + 2) rule.positives.length cursorAt middle nextBound middlePC
    address counter one running (by omega) (by omega) (by rw [middleSize]; exact heapFits)
  have trace := first.append second
  refine ⟨final, ?_, ?_, ?_, ?_⟩
  · simpa [final, middle, Controller.Horn.RuleCopy.finishStored, Controller.Cost.State.liveWords, Controller.Cost.State.advance] using trace
  · exact Stored.cursor_update middleStored cursorHeader nextBound beforeRecord
      (word width (offset + 2 + 1 + rule.positives.length))
  · refine ⟨by simp [final, Controller.Horn.RuleCopy.cursorUpdateFinished, middleSize]; exact headerBound, ?_⟩
    simp [final, Controller.Horn.RuleCopy.cursorUpdateFinished, middleSize, fits, Nat.add_assoc]
  · simp [final, Controller.Horn.RuleCopy.cursorUpdateFinished, middleSize]

/-- The complete fetched copy block returns a physically stored selected
record and an updated endpoint cursor. Inert rows take the actual bypass;
active rows traverse and count the stored positive buffer before writing it. -/
theorem copy_record_execution (program : Program width 8) (entry base cursorHeader pcur ncur tcur : Nat)
    (present : CodeAt program entry base cursorHeader n)
    (state : Controller.Cost.State width 8) (row : Row n)
    (stored : Controller.Horn.LiteralDispatch.RowStored row base pcur ncur tcur state.heap)
    (supported : Controller.Horn.RuleDispatch.Supported row)
    (cursor : Controller.Horn.SourceScan.CursorStored state.heap.size cursorHeader state.heap)
    (position : state.pc = word width entry) (zero : state.reg 2 = word width 0)
    (one : state.reg 5 = word width 1) (running : state.halted = false)
    (capacity : entry + 42 < 2 ^ width)
    (heapFits : state.heap.size + 3 + row.positive.length < 2 ^ width) :
    ∃ final : Controller.Cost.State width 8,
      Execution program state final (if row.tautology then 20 else 8 * row.positive.length + 31)
        (state.liveWords + 3 + row.rule.positives.length) ∧
      Controller.Horn.RuleCopy.Stored row.rule state.heap.size final.heap ∧
      Controller.Horn.SourceScan.CursorStored final.heap.size cursorHeader final.heap ∧
      final.heap.size = state.heap.size + 3 + row.rule.positives.length := by
  obtain ⟨allocated, allocationTrace, allocatedHeapEq, scratch, allocatedPC,
    allocatedTag, allocatedHead, allocatedAddress, allocatedZero, allocatedOne,
    allocatedDecrement, allocatedRunning, allocatedStack, allocatedOutput⟩ :=
    record_prefix_execution program entry base cursorHeader pcur ncur tcur present state row
      stored supported cursor position zero one running capacity (by omega)
  have allocatedSize : allocated.heap.size = state.heap.size + 3 := by
    rw [allocatedHeapEq, allocatedHeap_size]
  have allocatedLive : allocated.liveWords = state.liveWords + 3 := by
    simp [Controller.Cost.State.liveWords, allocatedSize, allocatedStack, allocatedOutput, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have sourceBefore : cursorHeader < state.heap.size := cursor.bound
  cases flag : row.tautology with
  | false =>
    have bodyIdentity := active_body row flag
    have countFits : row.positive.length < 2 ^ width := by omega
    obtain ⟨copied, copyTrace, copiedHeapEq, copiedCount, copiedZero, copiedOne,
      copiedDecrement, copiedAddress, copiedRunning, copiedPC, copiedStack, copiedOutput⟩ :=
      active_copy_execution program entry base cursorHeader pcur ncur tcur present allocated row
        scratch flag allocatedTag allocatedPC allocatedZero allocatedOne allocatedRunning
        capacity countFits (by rw [allocatedSize]; exact heapFits)
    have copiedHeap : copied.heap = Controller.Horn.RuleCopy.copiedHeap
        (allocatedHeap state.heap row.rule) row.rule.positives := by
      rw [copiedHeapEq, allocatedHeapEq, bodyIdentity]
    have fields := copied_record_fields state.heap row.rule
    have copiedSize : copied.heap.size = state.heap.size + 3 + row.rule.positives.length := by
      simp [copiedHeap]
    have copiedLive : copied.liveWords = state.liveWords + 3 + row.positive.length := by
      simp [Controller.Cost.State.liveWords, copiedSize, copiedStack, copiedOutput,
        allocatedStack, allocatedOutput, bodyIdentity, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    obtain ⟨final, finishTrace, record, finalCursor, finalSize⟩ :=
      finish_record_execution program (entry + 37) cursorHeader state.heap.size present.finish
        (by simpa [Nat.add_assoc] using present.cursor) copied row.rule copiedSize.symm
        (by rw [bodyIdentity]; exact countFits)
        (by simpa only [copiedHeap] using fields.1)
        (by simpa only [copiedHeap] using fields.2.1)
        (by rw [copiedHeap]; exact fields.2.2)
        (by rw [bodyIdentity]; exact copiedCount)
        (copiedAddress.trans allocatedAddress) (by rw [copiedSize]; omega) sourceBefore
        copiedPC copiedOne copiedRunning (by omega)
        (by rw [copiedSize, bodyIdentity]; exact heapFits)
    have trace := (allocationTrace.append copyTrace).append finishTrace
    refine ⟨final, ?_, record, finalCursor, finalSize.trans copiedSize⟩
    convert trace using 1 <;> simp [flag, bodyIdentity, allocatedLive, copiedLive, Nat.add_assoc] <;> omega
  | true =>
    have ruleIdentity : row.rule = .skip := by simp [Row.rule, flag]
    let bypass := bypassFinished allocated (entry + 37)
    have bypassFrame := bypass_frame allocated (entry + 37)
    have bypassHeap : bypass.heap = allocated.heap := bypassFrame.1
    have bypassCounter : bypass.reg 4 = word width 0 := bypassFrame.2.2.2.1
    have unchanged := bypassFrame.2.2.2.2.1
    have bypassRunning : bypass.halted = false := bypassFrame.2.2.2.2.2.trans allocatedRunning
    have bypassTag : (allocated.reg 1).val = 0 := by
      rw [allocatedTag, ruleIdentity]
      simp [Controller.Horn.RuleCopy.tag, word]
    have bypassPC : bypass.pc = word width (entry + 37) := by
      simpa [bypassTag] using bypass_position allocated (entry + 24) (entry + 37) allocatedPC (by omega)
    have bypassTrace := bypass_execution program (entry + 24) (entry + 37)
      present.bypass allocated allocatedPC allocatedRunning (by omega)
    have bypassSize : bypass.heap.size = state.heap.size + 3 := by rw [bypassHeap, allocatedSize]
    have bypassLive : bypass.liveWords = state.liveWords + 3 := by
      calc
        bypass.liveWords = allocated.liveWords := by
          simp only [Controller.Cost.State.liveWords, show bypass.heap = allocated.heap from bypassFrame.1,
            show bypass.stack = allocated.stack from bypassFrame.2.1,
            show bypass.output = allocated.output from bypassFrame.2.2.1]
        _ = state.liveWords + 3 := allocatedLive
    have fields := allocated_header state.heap row.rule
    have body : Controller.Horn.ResetTouched.LabelsStored row.rule.positives
        (state.heap.size + 3) bypass.heap := by
      refine ⟨by simp [ruleIdentity, Rule.positives, bypassSize], ?_⟩
      intro index
      simp only [ruleIdentity, Rule.positives] at index
      exact Fin.elim0 index
    obtain ⟨final, finishTrace, record, finalCursor, finalSize⟩ :=
      finish_record_execution program (entry + 37) cursorHeader state.heap.size present.finish
        (by simpa [Nat.add_assoc] using present.cursor) bypass row.rule
        (by simpa [ruleIdentity, Rule.positives] using bypassSize.symm)
        (by simp [ruleIdentity, Rule.positives] <;> omega)
        (by simpa only [bypassHeap, allocatedHeapEq] using fields.1)
        (by simpa only [bypassHeap, allocatedHeapEq] using fields.2.1) body
        (by simpa [ruleIdentity, Rule.positives] using bypassCounter)
        ((unchanged 7 (by decide)).trans allocatedAddress) (by rw [bypassSize]; omega) sourceBefore
        bypassPC ((unchanged 5 (by decide)).trans allocatedOne) bypassRunning
        (by omega) (by rw [bypassSize]; omega)
    have trace := (allocationTrace.append bypassTrace).append finishTrace
    refine ⟨final, ?_, record, finalCursor, ?_⟩
    · simpa [flag, ruleIdentity, Rule.positives, allocatedLive, bypassLive, Nat.add_assoc] using trace
    · simpa [ruleIdentity, Rule.positives] using finalSize.trans bypassSize

/-- A physical store outside the complete allocated scratch interval preserves
all mark cells, four headers and each positive/negative/touched buffer. -/
theorem row_after_store {row : Row n} {base pcur ncur tcur : Nat}
    {heap : Array (Word width)}
    (stored : Controller.Horn.LiteralDispatch.RowStored row base pcur ncur tcur heap)
    (index : Nat) (bound : index < heap.size) (value : Word width)
    (outside : index < base ∨ base + 5 * n + 4 ≤ index) :
    Controller.Horn.LiteralDispatch.RowStored row base pcur ncur tcur (heap.set index value bound) := by
  have headerFrame (labels : List (Fin n)) (header lower cursor limit : Nat)
      (old : Controller.Horn.RecordStorage.HeaderStored labels header lower cursor limit heap)
      (headerInside : base ≤ header ∧ header < base + 5 * n + 4)
      (bufferInside : base ≤ lower ∧ limit ≤ base + 5 * n + 4) :
      Controller.Horn.RecordStorage.HeaderStored labels header lower cursor limit (heap.set index value bound) := by
    refine ⟨Controller.Horn.RecordStorage.buffer_after_store old.buffer index bound value
      (by rcases outside with h | h
          · exact Or.inl (by omega)
          · exact Or.inr (by omega)),
      by simpa using old.bound, old.separate, ?_⟩
    exact (Array.getElem_set_ne bound old.bound (by rcases outside with h | h <;> omega)).trans old.value
  refine ⟨?_, ?_, ?_, ?_, by simpa using stored.flagBound, ?_⟩
  · refine ⟨by simpa using stored.marks.fits, ?_⟩
    intro literal
    have valid := stored.marks.bound literal
    have upper := Controller.Horn.MarkStorage.address_lt base literal
    have lower : base ≤ Controller.Horn.MarkStorage.address base literal := by
      unfold Controller.Horn.MarkStorage.address
      omega
    exact (Array.getElem_set_ne bound valid (by rcases outside with h | h <;> omega)).trans
      (stored.marks.entry literal)
  · exact headerFrame row.positive (base + 2 * n) (base + 2 * n + 4) pcur
      (base + 3 * n + 4) stored.positive (by omega) (by omega)
  · exact headerFrame row.negative (base + 2 * n + 1) (base + 3 * n + 4) ncur
      (base + 4 * n + 4) stored.negative (by omega) (by omega)
  · exact headerFrame row.touched (base + 2 * n + 2) (base + 4 * n + 4) tcur
      (base + 5 * n + 4) stored.touched (by omega) (by omega)
  · exact (Array.getElem_set_ne bound stored.flagBound
      (by rcases outside with h | h <;> omega)).trans stored.flag

/-- The actual terminal stores preserve the scratch representation when the
count belongs to an appended record and the persistent cursor is below scratch.
These address inequalities must come from the initialized heap layout. -/
theorem finish_row_stored (state : Controller.Cost.State width 8) (row : Row n)
    (base pcur ncur tcur countAddress cursorHeader count : Nat)
    (stored : Controller.Horn.LiteralDispatch.RowStored row base pcur ncur tcur state.heap)
    (countBound : countAddress < state.heap.size)
    (countAbove : base + 5 * n + 4 ≤ countAddress)
    (cursorBound : cursorHeader < state.heap.size) (cursorBelow : cursorHeader < base) :
    let middle := Controller.Horn.RuleCopy.finishStored state countAddress countBound
    let final := Controller.Horn.RuleCopy.cursorUpdateFinished middle cursorHeader countAddress count
      (by simpa [middle, Controller.Horn.RuleCopy.finishStored] using cursorBound)
    Controller.Horn.LiteralDispatch.RowStored row base pcur ncur tcur final.heap := by
  let middle := Controller.Horn.RuleCopy.finishStored state countAddress countBound
  have first : Controller.Horn.LiteralDispatch.RowStored row base pcur ncur tcur middle.heap :=
    row_after_store stored countAddress countBound (state.reg 4) (Or.inr countAbove)
  have bound : cursorHeader < middle.heap.size := by
    simpa [middle, Controller.Horn.RuleCopy.finishStored] using cursorBound
  exact row_after_store first cursorHeader bound
    (word width (countAddress + 1 + count)) (Or.inl cursorBelow)

/-- The target interface for the complete fetched block; its proof must compose
all stage executions and establish storage before the separate reset runs. -/
structure Result (program : Program width 8) (entry base cursorHeader pcur ncur tcur : Nat)
    (row : Row n) (initial final : Controller.Cost.State width 8) : Prop where
  execution : Execution program initial final
    (if row.tautology then 20 else 8 * row.positive.length + 31)
    (initial.liveWords + 3 + row.rule.positives.length)
  record : Controller.Horn.RuleCopy.Stored row.rule initial.heap.size final.heap
  scratch : Controller.Horn.LiteralDispatch.RowStored row base pcur ncur tcur final.heap
  cursor : Controller.Horn.SourceScan.CursorStored final.heap.size cursorHeader final.heap
  size : final.heap.size = initial.heap.size + 3 + row.rule.positives.length
  sourceFrame : ∀ index : Nat, ∀ valid : index < initial.heap.size,
    index ≠ cursorHeader → final.heap[index]'(by rw [size]; omega) = initial.heap[index]
  position : final.pc = word width (entry + 42)
  zero : final.reg 2 = word width 0
  one : final.reg 5 = word width 1
  decrement : final.reg 6 = initial.reg 6
  running : final.halted = false
  stack : final.stack = initial.stack
  output : final.output = initial.output

end Controller.Horn.JoinedRuleCopy
