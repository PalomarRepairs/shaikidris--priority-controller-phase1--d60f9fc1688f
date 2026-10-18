module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Horn.JoinedRuleCopy
public import Controller.Horn.HeaderReuse

@[expose] public section

/-!
# Record-copy frames and scratch reuse

The physical cursor lies below the complete initialized scratch interval.
Count stores belong to appended records. Successful trace uniqueness permits
transport from the checked construction consumer to explicit terminal states.
-/
namespace Controller.Horn.JoinedRuleFrame

open Controller.Cost Controller.Horn.Worklist.IndexedNormalize

/-- Equal-length successful executions of the deterministic stored program
have the same terminal state, irrespective of their resource indices. -/
theorem execution_endpoint_unique {program : Program width registers}
    {initial leftFinal rightFinal : Controller.Cost.State width registers}
    {ticks leftPeak rightPeak : Nat}
    (left : Execution program initial leftFinal ticks leftPeak)
    (right : Execution program initial rightFinal ticks rightPeak) : leftFinal = rightFinal := by
  induction left generalizing rightFinal rightPeak with
  | refl state =>
    cases right
    rfl
  | cons transition rest ih =>
    cases right with
    | cons otherTransition otherRest =>
      have same := Option.some.inj (transition.symm.trans otherTransition)
      cases same
      exact ih otherRest

/-- The initialized storage invariant supplies the complete scratch boundary;
it is not a supplied clause length or a free memory frame. -/
theorem count_above_scratch (row : Row n) (base pcur ncur tcur : Nat)
    (heap : Array (Word width))
    (stored : Controller.Horn.LiteralDispatch.RowStored row base pcur ncur tcur heap) :
    base + 5 * n + 4 ≤ heap.size + 2 := by
  have := stored.touched.buffer.fits
  omega

/-- An actual persistent cursor below the mark base is separate from every
scratch mark, header and reserved label cell. -/
theorem initialized_cursor_disjoint (base header n : Nat) (below : header < base) :
    header < base + 2 * n ∧ header < base + 2 * n + 4 ∧ header < base + 5 * n + 4 := by
  omega

@[simp] private theorem word_val (value : Nat) (fits : value < 2 ^ width) :
    (word width value).val = value := Nat.mod_eq_of_lt fits

private theorem advance_position (state : Controller.Cost.State width 8) (entry : Nat)
    (position : state.pc = word width entry) (fits : entry < 2 ^ width) :
    state.advance.pc = word width (entry + 1) := by
  simp only [Controller.Cost.State.advance, position, word_val (width := width) entry fits]

/-- Explicit result of the actual count-store and cursor-update instructions. -/
def terminal (state : Controller.Cost.State width 8) (address header count : Nat)
    (addressBound : address < state.heap.size) (headerBound : header < state.heap.size) :
    Controller.Cost.State width 8 :=
  let middle := Controller.Horn.RuleCopy.finishStored state address addressBound
  Controller.Horn.RuleCopy.cursorUpdateFinished middle header address count
    (by simpa [middle, Controller.Horn.RuleCopy.finishStored] using headerBound)

@[simp] theorem terminal_size (state : Controller.Cost.State width 8) (address header count : Nat)
    (addressBound : address < state.heap.size) (headerBound : header < state.heap.size) :
    (terminal state address header count addressBound headerBound).heap.size = state.heap.size := by
  simp [terminal, Controller.Horn.RuleCopy.finishStored, Controller.Horn.RuleCopy.cursorUpdateFinished]

theorem terminal_common (state : Controller.Cost.State width 8) (address header count : Nat)
    (addressBound : address < state.heap.size) (headerBound : header < state.heap.size) :
    let final := terminal state address header count addressBound headerBound
    final.reg 2 = state.reg 2 ∧ final.reg 5 = state.reg 5 ∧
    final.reg 6 = state.reg 6 ∧ final.reg 7 = state.reg 7 ∧
    final.halted = state.halted ∧ final.stack = state.stack ∧ final.output = state.output := by
  simp [terminal, Controller.Horn.RuleCopy.finishStored, Controller.Horn.RuleCopy.cursorUpdateFinished,
    Controller.Cost.State.advance, Controller.Cost.State.put]

/-- Every original cell except the two actual store destinations is preserved. -/
theorem terminal_source_frame (state : Controller.Cost.State width 8) (address header count : Nat)
    (addressBound : address < state.heap.size) (headerBound : header < state.heap.size)
    (index : Nat) (valid : index < state.heap.size) (notCount : address ≠ index)
    (notCursor : header ≠ index) :
    (terminal state address header count addressBound headerBound).heap[index]'(by simpa using valid) =
      state.heap[index] := by
  let middle := Controller.Horn.RuleCopy.finishStored state address addressBound
  have nextBound : header < middle.heap.size := by
    simpa [middle, Controller.Horn.RuleCopy.finishStored] using headerBound
  have nextValid : index < middle.heap.size := by
    simpa [middle, Controller.Horn.RuleCopy.finishStored] using valid
  have second : (middle.heap.set header (word width (address + 1 + count)) nextBound)[index]'(by simpa using nextValid) =
      middle.heap[index] := Array.getElem_set_ne nextBound nextValid notCursor
  exact second.trans (Controller.Horn.RuleCopy.finishStored_frame state address addressBound
    index valid notCount)

/-- The concrete two-store terminal state preserves all scratch storage when
its actual count address is above scratch and its cursor is below scratch. -/
theorem terminal_row_stored (state : Controller.Cost.State width 8) (row : Row n)
    (base pcur ncur tcur address header count : Nat)
    (stored : Controller.Horn.LiteralDispatch.RowStored row base pcur ncur tcur state.heap)
    (addressBound : address < state.heap.size) (headerBound : header < state.heap.size)
    (countAbove : base + 5 * n + 4 ≤ address) (cursorBelow : header < base) :
    Controller.Horn.LiteralDispatch.RowStored row base pcur ncur tcur
      (terminal state address header count addressBound headerBound).heap :=
  Controller.Horn.JoinedRuleCopy.finish_row_stored state row base pcur ncur tcur address header count
    stored addressBound countAbove headerBound cursorBelow

theorem terminal_position (state : Controller.Cost.State width 8) (entry address header count : Nat)
    (addressBound : address < state.heap.size) (headerBound : header < state.heap.size)
    (position : state.pc = word width entry) (capacity : entry + 5 < 2 ^ width) :
    (terminal state address header count addressBound headerBound).pc = word width (entry + 5) := by
  let middle := Controller.Horn.RuleCopy.finishStored state address addressBound
  let a := middle.advance.put 1 (word width (address + 1))
  let b := a.advance.put 1 (word width (address + 1 + count))
  let c := b.advance.put 0 (word width header)
  have pm : middle.pc = word width (entry + 1) := advance_position state entry position (by omega)
  have pa : a.pc = word width (entry + 2) := by
    simpa [a, Controller.Cost.State.put, Nat.add_assoc] using advance_position middle (entry + 1) pm (by omega)
  have pb : b.pc = word width (entry + 3) := by
    simpa [b, Controller.Cost.State.put, Nat.add_assoc] using advance_position a (entry + 2) pa (by omega)
  have pc : c.pc = word width (entry + 4) := by
    simpa [c, Controller.Cost.State.put, Nat.add_assoc] using advance_position b (entry + 3) pb (by omega)
  simpa [terminal, Controller.Horn.RuleCopy.cursorUpdateFinished, middle, a, b, c,
    Controller.Cost.State.put, Nat.add_assoc] using advance_position c (entry + 4) pc (by omega)

/-- Five actual terminal instructions return the explicit state whose frames
are proved above; no generic heap update is substituted for machine execution. -/
theorem terminal_execution (program : Program width 8) (entry address header count : Nat)
    (finishAt : Controller.Horn.RuleCopy.FinishAt program entry)
    (cursorAt : Controller.Horn.RuleCopy.CursorUpdateAt program (entry + 1) header)
    (state : Controller.Cost.State width 8)
    (addressBound : address < state.heap.size) (headerBound : header < state.heap.size)
    (held : state.reg 7 = word width address) (counter : state.reg 4 = word width count)
    (position : state.pc = word width entry) (one : state.reg 5 = word width 1)
    (running : state.halted = false) (capacity : entry + 5 < 2 ^ width)
    (endFits : address + 1 + count < 2 ^ width) (heapFits : state.heap.size < 2 ^ width) :
    Execution program state (terminal state address header count addressBound headerBound) 5 state.liveWords := by
  let middle := Controller.Horn.RuleCopy.finishStored state address addressBound
  have pc : middle.pc = word width (entry + 1) := advance_position state entry position (by omega)
  have headerValid : header < middle.heap.size := by
    simpa [middle, Controller.Horn.RuleCopy.finishStored] using headerBound
  have first := Controller.Horn.RuleCopy.finish_execution program entry address finishAt state
    addressBound position held running (by omega) heapFits
  have second := Controller.Horn.RuleCopy.cursor_update_execution program (entry + 1) header address count
    cursorAt middle headerValid pc held counter one running (by omega) endFits
    (by simpa [middle, Controller.Horn.RuleCopy.finishStored] using heapFits)
  simpa [terminal, middle, Controller.Horn.RuleCopy.finishStored, Controller.Cost.State.liveWords,
    Controller.Cost.State.advance] using first.append second

/-- The checked construction record is transported to the explicit terminal
state by deterministic successful trace uniqueness. -/
theorem terminal_record (program : Program width 8) (entry header offset : Nat)
    (finishAt : Controller.Horn.RuleCopy.FinishAt program entry)
    (cursorAt : Controller.Horn.RuleCopy.CursorUpdateAt program (entry + 1) header)
    (state : Controller.Cost.State width 8) (rule : Controller.Horn.Worklist.Rule (Fin n))
    (fits : offset + 3 + rule.positives.length = state.heap.size)
    (countFits : rule.positives.length < 2 ^ width)
    (tagValue : state.heap[offset]'(by omega) = word width (Controller.Horn.RuleCopy.tag rule))
    (headValue : state.heap[offset + 1]'(by omega) = Controller.Horn.RuleCopy.headWord width rule)
    (body : Controller.Horn.ResetTouched.LabelsStored rule.positives (offset + 3) state.heap)
    (counter : state.reg 4 = word width rule.positives.length)
    (held : state.reg 7 = word width (offset + 2))
    (headerBound : header < state.heap.size) (beforeRecord : header < offset)
    (position : state.pc = word width entry) (one : state.reg 5 = word width 1)
    (running : state.halted = false) (capacity : entry + 5 < 2 ^ width)
    (heapFits : state.heap.size < 2 ^ width) :
    let final := terminal state (offset + 2) header rule.positives.length (by omega) headerBound
    Controller.Horn.RuleCopy.Stored rule offset final.heap ∧
    Controller.Horn.SourceScan.CursorStored final.heap.size header final.heap := by
  obtain ⟨checked, trace, record, cursor, size⟩ :=
    Controller.Horn.JoinedRuleCopy.finish_record_execution program entry header offset finishAt cursorAt
      state rule fits countFits tagValue headValue body counter held headerBound beforeRecord
      position one running capacity heapFits
  have actual := terminal_execution program entry (offset + 2) header rule.positives.length finishAt cursorAt
    state (by omega) headerBound held counter position one running capacity (by omega) heapFits
  have same := execution_endpoint_unique actual trace
  rw [← same] at record cursor
  exact ⟨record, cursor⟩

theorem copied_allocated_frame (heap : Array (Word width))
    (rule : Controller.Horn.Worklist.Rule (Fin n)) (index : Nat) (valid : index < heap.size) :
    (Controller.Horn.RuleCopy.copiedHeap
      (Controller.Horn.JoinedRuleCopy.allocatedHeap heap rule) rule.positives)[index]'(by simp <;> omega) =
      heap[index] := by
  exact (Controller.Horn.RuleCopy.copiedHeap_frame
    (Controller.Horn.JoinedRuleCopy.allocatedHeap heap rule) rule.positives index (by simp; omega)).trans
    (Controller.Horn.JoinedRuleCopy.allocatedHeap_frame heap rule index valid)

/-- The same actual copy pipeline satisfies the complete Result frame contract.
The cursor-header location is physically below scratch; all count destinations
belong to the appended output record. -/
theorem copy_result (program : Program width 8) (entry base header pcur ncur tcur : Nat)
    (present : Controller.Horn.JoinedRuleCopy.CodeAt program entry base header n)
    (state : Controller.Cost.State width 8) (row : Row n)
    (stored : Controller.Horn.LiteralDispatch.RowStored row base pcur ncur tcur state.heap)
    (supported : Controller.Horn.RuleDispatch.Supported row)
    (cursor : Controller.Horn.SourceScan.CursorStored state.heap.size header state.heap)
    (below : header < base)
    (position : state.pc = word width entry) (zero : state.reg 2 = word width 0)
    (one : state.reg 5 = word width 1) (running : state.halted = false)
    (capacity : entry + 42 < 2 ^ width)
    (heapFits : state.heap.size + 3 + row.positive.length < 2 ^ width) :
    ∃ final : Controller.Cost.State width 8,
      Controller.Horn.JoinedRuleCopy.Result program entry base header pcur ncur tcur row state final := by
  obtain ⟨allocated, allocationTrace, allocatedHeapEq, scratch, allocatedPC,
    allocatedTag, allocatedHead, allocatedAddress, allocatedZero, allocatedOne,
    allocatedDecrement, allocatedRunning, allocatedStack, allocatedOutput⟩ :=
    Controller.Horn.JoinedRuleCopy.record_prefix_execution program entry base header pcur ncur tcur
      present state row stored supported cursor position zero one running capacity (by omega)
  have allocatedSize : allocated.heap.size = state.heap.size + 3 := by
    rw [allocatedHeapEq, Controller.Horn.JoinedRuleCopy.allocatedHeap_size]
  have allocatedLive : allocated.liveWords = state.liveWords + 3 := by
    simp [Controller.Cost.State.liveWords, allocatedSize, allocatedStack, allocatedOutput,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have countAbove := count_above_scratch row base pcur ncur tcur state.heap stored
  have beforeRecord : header < state.heap.size := cursor.bound
  cases flag : row.tautology with
  | false =>
    have identity := Controller.Horn.JoinedRuleCopy.active_body row flag
    obtain ⟨copied, copyTrace, copiedHeapEq, copiedCount, copiedZero, copiedOne,
      copiedDecrement, copiedAddress, copiedRunning, copiedPC, copiedStack, copiedOutput⟩ :=
      Controller.Horn.JoinedRuleCopy.active_copy_execution program entry base header pcur ncur tcur
        present allocated row scratch flag allocatedTag allocatedPC allocatedZero allocatedOne
        allocatedRunning capacity (by omega) (by rw [allocatedSize]; exact heapFits)
    have copiedHeap : copied.heap = Controller.Horn.RuleCopy.copiedHeap
        (Controller.Horn.JoinedRuleCopy.allocatedHeap state.heap row.rule) row.rule.positives := by
      rw [copiedHeapEq, allocatedHeapEq, identity]
    have copiedSize : copied.heap.size = state.heap.size + 3 + row.rule.positives.length := by simp [copiedHeap]
    have copiedLive : copied.liveWords = state.liveWords + 3 + row.positive.length := by
      simp [Controller.Cost.State.liveWords, copiedSize, copiedStack, copiedOutput,
        allocatedStack, allocatedOutput, identity, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    have copiedScratch : Controller.Horn.LiteralDispatch.RowStored row base pcur ncur tcur copied.heap := by
      rw [copiedHeapEq]
      exact Controller.Horn.RuleCopy.row_after_copy scratch row.positive
    have addressBound : state.heap.size + 2 < copied.heap.size := by rw [copiedSize]; omega
    have headerBound : header < copied.heap.size := by rw [copiedSize]; omega
    let final := terminal copied (state.heap.size + 2) header row.rule.positives.length addressBound headerBound
    have fields := Controller.Horn.JoinedRuleCopy.copied_record_fields state.heap row.rule
    have actualCounter : copied.reg 4 = word width row.rule.positives.length := by simpa [identity] using copiedCount
    have actualAddress : copied.reg 7 = word width (state.heap.size + 2) := copiedAddress.trans allocatedAddress
    have last := terminal_execution program (entry + 37) (state.heap.size + 2) header
      row.rule.positives.length present.finish (by simpa [Nat.add_assoc] using present.cursor)
      copied addressBound headerBound actualAddress actualCounter copiedPC copiedOne copiedRunning
      (by omega) (by rw [identity]; omega) (by rw [copiedSize, identity]; exact heapFits)
    have record := terminal_record program (entry + 37) header state.heap.size present.finish
      (by simpa [Nat.add_assoc] using present.cursor) copied row.rule copiedSize.symm
      (by rw [identity]; omega) (by simpa only [copiedHeap] using fields.1)
      (by simpa only [copiedHeap] using fields.2.1) (by rw [copiedHeap]; exact fields.2.2)
      actualCounter actualAddress headerBound beforeRecord copiedPC copiedOne copiedRunning
      (by omega) (by rw [copiedSize, identity]; exact heapFits)
    have common := terminal_common copied (state.heap.size + 2) header row.rule.positives.length addressBound headerBound
    refine ⟨final, ?_⟩
    constructor
    · have trace := (allocationTrace.append copyTrace).append last
      convert trace using 1 <;> simp [flag, identity, allocatedLive, copiedLive, Nat.add_assoc] <;> omega
    · exact record.1
    · exact terminal_row_stored copied row base pcur ncur tcur (state.heap.size + 2) header
        row.rule.positives.length copiedScratch addressBound headerBound countAbove below
    · exact record.2
    · intro index valid different
      have nextValid : index < copied.heap.size := by rw [copiedSize]; omega
      have frame := terminal_source_frame copied (state.heap.size + 2) header row.rule.positives.length
        addressBound headerBound index nextValid (by omega) (Ne.symm different)
      have old : copied.heap[index]'nextValid = state.heap[index] := by
        simpa only [copiedHeap] using copied_allocated_frame state.heap row.rule index valid
      exact frame.trans old
    · simpa [final, Nat.add_assoc] using terminal_position copied (entry + 37) (state.heap.size + 2)
        header row.rule.positives.length addressBound headerBound copiedPC (by omega)
    · exact common.1.trans copiedZero
    · exact common.2.1.trans copiedOne
    · exact common.2.2.1.trans (copiedDecrement.trans allocatedDecrement)
    · exact common.2.2.2.2.1.trans copiedRunning
    · exact common.2.2.2.2.2.1.trans (copiedStack.trans allocatedStack)
    · exact common.2.2.2.2.2.2.trans (copiedOutput.trans allocatedOutput)
    · simpa [final] using (terminal_size copied (state.heap.size + 2) header
        row.rule.positives.length addressBound headerBound).trans copiedSize
  | true =>
    have identity : row.rule = .skip := by simp [Row.rule, flag]
    let bypass := Controller.Horn.JoinedRuleCopy.bypassFinished allocated (entry + 37)
    have bypassFrame := Controller.Horn.JoinedRuleCopy.bypass_frame allocated (entry + 37)
    have bypassHeap : bypass.heap = allocated.heap := bypassFrame.1
    have unchanged := bypassFrame.2.2.2.2.1
    have bypassRunning : bypass.halted = false := bypassFrame.2.2.2.2.2.trans allocatedRunning
    have held : (allocated.reg 1).val = 0 := by rw [allocatedTag, identity]; simp [Controller.Horn.RuleCopy.tag, word]
    have bypassPC : bypass.pc = word width (entry + 37) := by
      simpa [held] using Controller.Horn.JoinedRuleCopy.bypass_position allocated
        (entry + 24) (entry + 37) allocatedPC (by omega)
    have bypassTrace := Controller.Horn.JoinedRuleCopy.bypass_execution program (entry + 24) (entry + 37)
      present.bypass allocated allocatedPC allocatedRunning (by omega)
    have bypassSize : bypass.heap.size = state.heap.size + 3 := by rw [bypassHeap, allocatedSize]
    have bypassLive : bypass.liveWords = state.liveWords + 3 := by
      calc
        bypass.liveWords = allocated.liveWords := by
          simp only [Controller.Cost.State.liveWords, show bypass.heap = allocated.heap from bypassFrame.1,
            show bypass.stack = allocated.stack from bypassFrame.2.1,
            show bypass.output = allocated.output from bypassFrame.2.2.1]
        _ = state.liveWords + 3 := allocatedLive
    have addressBound : state.heap.size + 2 < bypass.heap.size := by rw [bypassSize]; omega
    have headerBound : header < bypass.heap.size := by rw [bypassSize]; omega
    have actualCounter : bypass.reg 4 = word width row.rule.positives.length := by
      simpa [identity, Controller.Horn.Worklist.Rule.positives] using bypassFrame.2.2.2.1
    have actualAddress : bypass.reg 7 = word width (state.heap.size + 2) :=
      (unchanged 7 (by decide)).trans allocatedAddress
    have bypassOne := (unchanged 5 (by decide)).trans allocatedOne
    let final := terminal bypass (state.heap.size + 2) header row.rule.positives.length addressBound headerBound
    have fields := Controller.Horn.JoinedRuleCopy.allocated_header state.heap row.rule
    have emptyBody : Controller.Horn.ResetTouched.LabelsStored row.rule.positives (state.heap.size + 3) bypass.heap := by
      refine ⟨by simp [identity, Controller.Horn.Worklist.Rule.positives, bypassSize], ?_⟩
      intro index
      simp only [identity, Controller.Horn.Worklist.Rule.positives] at index
      exact Fin.elim0 index
    have last := terminal_execution program (entry + 37) (state.heap.size + 2) header
      row.rule.positives.length present.finish (by simpa [Nat.add_assoc] using present.cursor)
      bypass addressBound headerBound actualAddress actualCounter bypassPC bypassOne bypassRunning
      (by omega) (by simp [identity, Controller.Horn.Worklist.Rule.positives] <;> omega) (by rw [bypassSize]; omega)
    have record := terminal_record program (entry + 37) header state.heap.size present.finish
      (by simpa [Nat.add_assoc] using present.cursor) bypass row.rule
      (by simpa [identity, Controller.Horn.Worklist.Rule.positives] using bypassSize.symm)
      (by simp [identity, Controller.Horn.Worklist.Rule.positives] <;> omega)
      (by simpa only [bypassHeap, allocatedHeapEq] using fields.1)
      (by simpa only [bypassHeap, allocatedHeapEq] using fields.2.1) emptyBody actualCounter
      actualAddress headerBound beforeRecord bypassPC bypassOne bypassRunning (by omega) (by rw [bypassSize]; omega)
    have common := terminal_common bypass (state.heap.size + 2) header row.rule.positives.length addressBound headerBound
    refine ⟨final, ?_⟩
    constructor
    · have trace := (allocationTrace.append bypassTrace).append last
      simpa [final, flag, identity, Controller.Horn.Worklist.Rule.positives, allocatedLive, bypassLive, Nat.add_assoc] using trace
    · exact record.1
    · exact terminal_row_stored bypass row base pcur ncur tcur (state.heap.size + 2) header
        row.rule.positives.length (by rw [bypassHeap]; exact scratch) addressBound headerBound countAbove below
    · exact record.2
    · intro index valid different
      have nextValid : index < bypass.heap.size := by rw [bypassSize]; omega
      have frame := terminal_source_frame bypass (state.heap.size + 2) header row.rule.positives.length
        addressBound headerBound index nextValid (by omega) (Ne.symm different)
      have old : bypass.heap[index]'nextValid = state.heap[index] := by
        simpa only [bypassHeap, allocatedHeapEq] using
          Controller.Horn.JoinedRuleCopy.allocatedHeap_frame state.heap row.rule index valid
      exact frame.trans old
    · simpa [final, Nat.add_assoc] using terminal_position bypass (entry + 37) (state.heap.size + 2)
        header row.rule.positives.length addressBound headerBound bypassPC (by omega)
    · exact common.1.trans ((unchanged 2 (by decide)).trans allocatedZero)
    · exact common.2.1.trans bypassOne
    · exact common.2.2.1.trans ((unchanged 6 (by decide)).trans allocatedDecrement)
    · exact common.2.2.2.2.1.trans bypassRunning
    · exact common.2.2.2.2.2.1.trans (bypassFrame.2.1.trans allocatedStack)
    · exact common.2.2.2.2.2.2.trans (bypassFrame.2.2.1.trans allocatedOutput)
    · simpa [final, identity, Controller.Horn.Worklist.Rule.positives] using
        (terminal_size bypass (state.heap.size + 2) header row.rule.positives.length addressBound headerBound).trans bypassSize

/-- Scratch reuse preserves an appended physical record outside the reset
mark and header interval. The frame is supplied by the fetched reuse consumer. -/
theorem record_after_reuse {rule : Controller.Horn.Worklist.Rule (Fin n)} {offset base : Nat}
    {before after : Array (Word width)}
    (stored : Controller.Horn.RuleCopy.Stored rule offset before)
    (size : after.size = before.size) (above : base + 2 * n + 4 ≤ offset)
    (frame : ∀ index : Nat, (index < base ∨ base + 2 * n + 4 ≤ index) → after[index]? = before[index]?) :
    Controller.Horn.RuleCopy.Stored rule offset after := by
  have held (index : Nat) (valid : index < before.size) (outside : base + 2 * n + 4 ≤ index) :
      after[index]'(by rw [size]; exact valid) = before[index] := by
    have eq := frame index (Or.inr outside)
    simpa only [Array.getElem?_eq_getElem valid,
      Array.getElem?_eq_getElem (by rw [size]; exact valid), Option.some.injEq] using eq
  refine ⟨by rw [size]; exact stored.fits, stored.countFits, ?_, ?_, ?_, ?_⟩
  · exact (held offset (by have := stored.fits; omega) above).trans stored.tagValue
  · exact (held (offset + 1) (by have := stored.fits; omega) (by omega)).trans stored.headValue
  · exact (held (offset + 2) (by have := stored.fits; omega) (by omega)).trans stored.countValue
  · refine ⟨by rw [size]; exact stored.body.fits, ?_⟩
    intro index
    have valid : offset + 3 + index.val < before.size := by
      have := stored.fits
      have := index.isLt
      omega
    exact (held (offset + 3 + index.val) valid (by omega)).trans (stored.body.entry index)

/-- Complete same-program copied-record construction followed by fetched
scratch reset and header reuse. The appended record and persistent cursor
survive, while the scratch row returns to the clean empty representation. -/
theorem copy_and_reuse (program : Program width 8) (entry base header pcur ncur tcur : Nat)
    (copyAt : Controller.Horn.JoinedRuleCopy.CodeAt program entry base header n)
    (setupAt : Controller.Horn.ResetPointer.SetupAt program (entry + 42) (base + 2 * n + 2) base)
    (loopAt : Controller.Horn.ResetPointer.CodeAt program (entry + 45) (base + 5 * n + 4))
    (headersAt : Controller.Horn.ResetReuse.HeaderAt program (entry + 56) n base)
    (state : Controller.Cost.State width 8) (row : Row n) (clause : Controller.CNF.Clause (Fin n))
    (correct : row.Correct clause)
    (stored : Controller.Horn.LiteralDispatch.RowStored row base pcur ncur tcur state.heap)
    (supported : Controller.Horn.RuleDispatch.Supported row)
    (cursor : Controller.Horn.SourceScan.CursorStored state.heap.size header state.heap)
    (below : header < base)
    (position : state.pc = word width entry) (zero : state.reg 2 = word width 0)
    (one : state.reg 5 = word width 1) (decrement : state.reg 6 = word width (2 ^ width - 1))
    (running : state.halted = false) (capacity : entry + 67 < 2 ^ width)
    (heapFits : state.heap.size + 3 + row.positive.length < 2 ^ width) :
    ∃ final : Controller.Cost.State width 8,
      Execution program state final
        ((if row.tautology then 20 else 8 * row.positive.length + 31) + 11 * row.touched.length + 17)
        (state.liveWords + 3 + row.rule.positives.length) ∧
      Controller.Horn.RuleCopy.Stored row.rule state.heap.size final.heap ∧
      Controller.Horn.SourceScan.CursorStored final.heap.size header final.heap ∧
      Controller.Horn.LiteralDispatch.RowStored (Row.empty (Marks.clear row.touched row.marks)) base
        (base + 3 * n + 4) (base + 4 * n + 4) (base + 5 * n + 4) final.heap ∧
      (Row.empty (Marks.clear row.touched row.marks)).Correct [] ∧
      final.heap.size = state.heap.size + 3 + row.rule.positives.length ∧
      (∀ index : Nat, index < state.heap.size →
        (index < base ∨ base + 2 * n + 4 ≤ index) → index ≠ header →
          final.heap[index]? = state.heap[index]?) ∧
      final.pc = word width (entry + 67) ∧ final.reg 2 = word width 0 ∧
      final.reg 5 = word width 1 ∧ final.reg 6 = word width (2 ^ width - 1) ∧
      final.halted = false ∧ final.stack = state.stack ∧ final.output = state.output := by
  obtain ⟨copied, result⟩ := copy_result program entry base header pcur ncur tcur copyAt
    state row stored supported cursor below position zero one running (by omega) heapFits
  have bodyLength : row.rule.positives.length ≤ row.positive.length := by
    cases flag : row.tautology
    · rw [Controller.Horn.JoinedRuleCopy.active_body row flag]
    · simp [Row.rule, flag, Controller.Horn.Worklist.Rule.positives]
  have copiedFits : copied.heap.size < 2 ^ width := by rw [result.size]; omega
  have copiedOne : copied.reg 5 = Controller.Horn.MarkStorage.encode width true := by
    simpa [Controller.Horn.MarkStorage.encode] using result.one
  obtain ⟨final, reuseTrace, empty, clean, frame, size, pc, finalZero, finalOne,
    finalDecrement, finalRunning, finalStack, finalOutput⟩ :=
    Controller.Horn.HeaderReuse.reuse_row_execution program (entry + 42) base pcur ncur tcur
      setupAt (by simpa [Nat.add_assoc] using loopAt) (by simpa [Nat.add_assoc] using headersAt)
      copied row clause correct result.scratch result.position result.zero copiedOne
      (result.decrement.trans decrement) result.running (by omega) copiedFits
  have record := record_after_reuse result.record size
    (by have := stored.touched.buffer.fits; omega) frame
  have headerBound : header < final.heap.size := by rw [size]; exact result.cursor.bound
  have headerValue : final.heap[header]'headerBound = copied.heap[header] := by
    have eq := frame header (Or.inl below)
    simpa only [Array.getElem?_eq_getElem headerBound,
      Array.getElem?_eq_getElem result.cursor.bound, Option.some.injEq] using eq
  have finalCursor : Controller.Horn.SourceScan.CursorStored final.heap.size header final.heap :=
    ⟨headerBound, by rw [headerValue, result.cursor.value, size]⟩
  have copiedLive : copied.liveWords = state.liveWords + 3 + row.rule.positives.length := by
    simp [Controller.Cost.State.liveWords, result.size, result.stack, result.output,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] <;> omega
  refine ⟨final, ?_, record, finalCursor, empty, clean, size.trans result.size, ?_, ?_, finalZero,
    ?_, finalDecrement, finalRunning, finalStack.trans result.stack, finalOutput.trans result.output⟩
  · have trace := result.execution.append reuseTrace
    simpa [copiedLive, Nat.max_self, Nat.add_assoc] using trace
  · intro index valid outside different
    have copiedValid : index < copied.heap.size := by rw [result.size]; omega
    have old := result.sourceFrame index valid different
    have oldOption : copied.heap[index]? = state.heap[index]? := by
      simpa only [Array.getElem?_eq_getElem copiedValid, Array.getElem?_eq_getElem valid,
        Option.some.injEq] using old
    exact (frame index outside).trans oldOption
  · simpa [Nat.add_assoc] using pc
  · simpa [Controller.Horn.MarkStorage.encode] using finalOne

end Controller.Horn.JoinedRuleFrame




