module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Horn.NormalizeCode
public import Controller.Horn.TrackedInput

public import Mathlib.Tactic.FinCases

@[expose] public section

/-! Physical initialization for the shared CNF normalizer. Source directory
pointers are supplied input words. Scratch is allocated by a counted machine
loop; its endpoint is copied from the operational heap-end register into the
record header. The eleven fetched header stores prepare the first clean row. -/
namespace Controller.Horn.NormalizeInitialize
open Controller.Cost Controller.Horn.Worklist.IndexedNormalize
open Controller.Horn.SourceDirectory Controller.Horn.SourceScan

/-- The pointer store reads register seven, rather than a compiled size constant. -/
def endpointCode (width recordHeader : Nat) : Program width 8 :=
  #[.constant 0 (word width recordHeader), .store 0 7]

@[simp] theorem endpointCode_size (width recordHeader : Nat) :
    (endpointCode width recordHeader).size = 2 := rfl

def EndpointAt (program : Program width 8) (entry recordHeader : Nat) : Prop :=
  ∀ phase : Fin 2, program[entry + phase.val]? = some (endpointCode width recordHeader)[phase.val]

def endpointFinished (state : State width 8) (recordHeader : Nat)
    (bound : recordHeader < state.heap.size) : State width 8 :=
  { (state.advance.put 0 (word width recordHeader)).advance with
    heap := state.heap.set recordHeader (word width state.heap.size) bound }

private theorem word_val (value : Nat) (fits : value < 2 ^ width) :
    (word width value).val = value := Nat.mod_eq_of_lt fits

/-- Two actual fetched operations store the physical endpoint. -/
theorem endpoint_execution (program : Program width 8) (entry recordHeader : Nat)
    (present : EndpointAt program entry recordHeader) (state : State width 8)
    (bound : recordHeader < state.heap.size) (pointer : state.reg 7 = word width state.heap.size)
    (position : state.pc = word width entry) (running : state.halted = false)
    (capacity : entry + 2 < 2 ^ width) (heapFits : state.heap.size < 2 ^ width) :
    Execution program state (endpointFinished state recordHeader bound) 2 state.liveWords := by
  let addressed := state.advance.put 0 (word width recordHeader)
  have p1 : addressed.pc = word width (entry + 1) := by
    simp [addressed, State.advance, State.put, position, word_val (width := width) entry (by omega)]
  have t0 : programStep program state = some addressed := by
    have fetch := present ⟨0, by decide⟩
    simp only [Nat.add_zero] at fetch
    unfold programStep
    rw [position, word_val (width := width) entry (by omega), fetch]
    simp [endpointCode, step, running, addressed]
  have t1 : programStep program addressed = some (endpointFinished state recordHeader bound) := by
    have fetch := present ⟨1, by decide⟩
    change program[entry + 1]? = some (.store 0 7) at fetch
    unfold programStep
    rw [p1, word_val (width := width) (entry + 1) (by omega), fetch]
    change step (.store 0 7) addressed = some (endpointFinished state recordHeader bound)
    have location : (addressed.reg 0).val = recordHeader := by
      simp [addressed, State.put, word_val (width := width) recordHeader (by omega)]
    have held : addressed.reg 7 = word width state.heap.size := by
      simp [addressed, State.put, State.advance, pointer]
    simp only [step, show addressed.halted = false from running,
      Bool.false_eq_true, ite_false, location,
      dite_eq_left (show recordHeader < addressed.heap.size from bound), held]
    rfl
  have trace := Execution.cons t0 (Execution.cons t1
    (Execution.refl (endpointFinished state recordHeader bound)))
  simpa [addressed, endpointFinished, State.liveWords, State.advance, State.put] using trace

theorem endpoint_position (state : State width 8) (entry recordHeader : Nat)
    (bound : recordHeader < state.heap.size) (position : state.pc = word width entry)
    (capacity : entry + 2 < 2 ^ width) :
    (endpointFinished state recordHeader bound).pc = word width (entry + 2) := by
  simp [endpointFinished, State.advance, State.put, position,
    word_val (width := width) entry (by omega), word_val (width := width) (entry + 1) (by omega), Nat.add_assoc]

theorem endpoint_cursor (state : State width 8) (recordHeader : Nat)
    (bound : recordHeader < state.heap.size) :
    CursorStored (endpointFinished state recordHeader bound).heap.size recordHeader
      (endpointFinished state recordHeader bound).heap := by
  refine ⟨by simpa [endpointFinished] using bound, ?_⟩
  simp [endpointFinished]

theorem endpoint_frame (state : State width 8) (recordHeader : Nat)
    (bound : recordHeader < state.heap.size) :
    (∀ register : Fin 8, register ≠ 0 →
      (endpointFinished state recordHeader bound).reg register = state.reg register) ∧
    (∀ cell, cell ≠ recordHeader →
      (endpointFinished state recordHeader bound).heap[cell]? = state.heap[cell]?) ∧
    (endpointFinished state recordHeader bound).heap.size = state.heap.size ∧
    (endpointFinished state recordHeader bound).stack = state.stack ∧
    (endpointFinished state recordHeader bound).output = state.output ∧
    (endpointFinished state recordHeader bound).halted = state.halted := by
  refine ⟨?_, ?_, by simp [endpointFinished], rfl, rfl, rfl⟩
  · intro register other
    simp [endpointFinished, State.advance, State.put, other]
  · intro cell other
    exact Array.getElem?_set_ne bound (Ne.symm other)

/-- The entire zero-filled scratch allocation initializes every declared mark. -/
theorem scratch_marks (heap : Array (Word width)) (n : Nat) :
    Controller.Horn.MarkStorage.Stored (Marks.initial n) heap.size
      (heap ++ Array.replicate (5 * n + 4) (word width 0)) := by
  refine ⟨by simp; omega, ?_⟩
  intro literal
  cases polarity : literal.2 <;>
    simp [Controller.Horn.MarkStorage.address, Controller.Horn.MarkStorage.encode,
      Marks.read, Marks.initial, polarity]

/-- Initializer boundaries all refer to one physically fetched program. -/
structure At (program : Program width 8) (entry n base recordHeader : Nat) : Prop where
  counter : program[entry]? = some (.constant 1 (word width (5 * n + 4)))
  allocate : Controller.Horn.TrackedAllocate.CodeAt program (entry + 1)
  endpoint : EndpointAt program (entry + 6) recordHeader
  headers : Controller.Horn.ResetReuse.HeaderAt program (entry + 8) n base

/-- The initializer has a fixed code footprint independent of source incidences. -/
def code (width entry n base recordHeader : Nat) : Program width 8 :=
  #[.constant 1 (word width (5 * n + 4))] ++
    Controller.Horn.TrackedAllocate.code width (entry + 1) ++ endpointCode width recordHeader ++
    Controller.Horn.ResetReuse.headerCode width n base

@[simp] theorem code_size (width entry n base recordHeader : Nat) :
    (code width entry n base recordHeader).size = 19 := by
  simp [code]

@[simp] theorem code_words (width entry n base recordHeader : Nat) :
    programWords (code width entry n base recordHeader) = 76 := by
  simp [programWords]

/-- Exact stored-prefix placement supplies all initializer consumers. -/
theorem stored_at (storedPrefix : Program width 8) (n base recordHeader : Nat) :
    At (storedPrefix ++ code width storedPrefix.size n base recordHeader)
      storedPrefix.size n base recordHeader := by
  have phase : ∀ position : Fin 19,
      (storedPrefix ++ code width storedPrefix.size n base recordHeader)[storedPrefix.size + position.val]? =
      (code width storedPrefix.size n base recordHeader)[position.val]? := by
    intro position
    rw [Array.getElem?_append_right (by omega)]
    simp only [Nat.add_sub_cancel_left]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [code, Controller.Horn.TrackedAllocate.code, endpointCode,
      Controller.Horn.ResetReuse.headerCode] using phase ⟨0, by decide⟩
  · intro i
    have fetched := phase ⟨1 + i.val, by have := i.isLt; omega⟩
    fin_cases i <;> simpa [code, Controller.Horn.TrackedAllocate.code,
      endpointCode, Controller.Horn.ResetReuse.headerCode, Nat.add_assoc] using fetched
  · intro i
    have fetched := phase ⟨6 + i.val, by have := i.isLt; omega⟩
    fin_cases i <;> simpa [code, Controller.Horn.TrackedAllocate.code,
      endpointCode, Controller.Horn.ResetReuse.headerCode, Nat.add_assoc] using fetched
  · intro i
    have fetched := phase ⟨8 + i.val, by have := i.isLt; omega⟩
    fin_cases i <;> simpa [code, Controller.Horn.TrackedAllocate.code,
      endpointCode, Controller.Horn.ResetReuse.headerCode, Nat.add_assoc] using fetched

/-- This state changes only through the first actual constant instruction. -/
def counted (state : State width 8) (n : Nat) : State width 8 :=
  state.advance.put 1 (word width (5 * n + 4))

private theorem directory_ne_record (layout : Layout clauses) :
    layout.directoryHeader ≠ layout.recordHeader := by
  have absent := (List.nodup_cons.mp layout.headersDistinct).1
  intro same
  apply absent
  rw [← same]
  simp

private theorem end_ne_record (layout : Layout clauses) :
    layout.endHeader ≠ layout.recordHeader := by
  have absent := (List.nodup_cons.mp layout.headersDistinct).1
  intro same
  apply absent
  rw [← same]
  simp

/-- Physical scratch allocation, dynamic endpoint store, and clean-row setup
compose in the same program. The starting directory and headers are represented
original input, and no normalized rule list is an input. -/
theorem execution (program : Program width 8) (entry : Nat)
    (clauses : List (Controller.CNF.Clause (Fin n))) (layout : Layout clauses)
    (present : At program entry n layout.base layout.recordHeader)
    (state : State width 8) (input : Controller.Horn.ClauseEntry.Input clauses layout 0 state)
    (base : layout.base = state.heap.size) (pointer : state.reg 7 = word width state.heap.size)
    (position : state.pc = word width entry) (capacity : entry + 19 < 2 ^ width)
    (room : state.heap.size + 5 * n + 4 < 2 ^ width) :
    ∃ final : State width 8,
      Execution program state final (5 * (5 * n + 4) + 15) (state.liveWords + 5 * n + 4) ∧
      Controller.Horn.NormalizeLoop.Invariant clauses layout (state.heap.size + 5 * n + 4)
        0 (Marks.initial n) final ∧
      final.pc = word width (entry + 19) ∧
      final.stack = state.stack ∧ final.output = state.output := by
  let start := counted state n
  have startPC : start.pc = word width (entry + 1) := by
    simp [start, counted, State.put, State.advance, position, word_val (width := width) entry (by omega)]
  have startTrace : Execution program state start 1 state.liveWords := by
    have first : programStep program state = some start := by
      unfold programStep
      rw [position, word_val (width := width) entry (by omega), present.counter]
      simp [step, start, counted, input.running]
    have trace := Execution.cons first (Execution.refl start)
    simpa [start, counted, State.liveWords, State.put, State.advance] using trace
  let allocated := Controller.Horn.TrackedAllocate.configuration start
    (state.heap ++ Array.replicate (5 * n + 4) (word width 0)) 0 (entry + 6)
  have allocTrace : Execution program start allocated (5 * (5 * n + 4) + 1)
      (state.liveWords + 5 * n + 4) := by
    have trace := Controller.Horn.TrackedAllocate.execution_from_state program (entry + 1)
      present.allocate start (5 * n + 4) (by simp [start, counted, State.put])
      startPC input.running (by simpa [start, counted, State.put, State.advance] using pointer)
      (by simpa [start, counted, State.put, State.advance] using input.zero)
      (by simpa [start, counted, State.put, State.advance] using input.one)
      (by simpa [start, counted, State.put, State.advance] using input.decrement)
      (by omega) room
    simpa [allocated, start, counted, State.liveWords, State.advance, State.put, Nat.add_assoc] using trace
  have allocatedSize : allocated.heap.size = state.heap.size + 5 * n + 4 := by
    simp [allocated, Controller.Horn.TrackedAllocate.configuration]; omega
  have recordBelow : layout.recordHeader < layout.base := by
    have h := layout.headersBefore layout.recordHeader (by simp)
    have d := layout.directoryBefore
    have s := layout.sourceBefore
    have a : layout.source ≤ sourceOffset clauses layout.source clauses.length := by
      unfold sourceOffset; omega
    omega
  have recordBound : layout.recordHeader < allocated.heap.size := by omega
  have allocatedRunning : allocated.halted = false := rfl
  let saved := endpointFinished allocated layout.recordHeader recordBound
  have savedRunning : saved.halted = false := allocatedRunning
  have storeTrace := endpoint_execution program (entry + 6) layout.recordHeader present.endpoint allocated
    recordBound (by simp [allocated, Controller.Horn.TrackedAllocate.configuration]) rfl allocatedRunning
    (by omega) (by omega)
  have savedSize : saved.heap.size = state.heap.size + 5 * n + 4 := by
    simp [saved, endpointFinished, allocatedSize]
  have savedPC : saved.pc = word width (entry + 8) := by
    simpa [saved, Nat.add_assoc] using endpoint_position allocated (entry + 6) layout.recordHeader
      recordBound rfl (by omega)
  have initialMarks : Controller.Horn.MarkStorage.Stored (Marks.initial n) layout.base saved.heap := by
    have marks : Controller.Horn.MarkStorage.Stored (Marks.initial n) layout.base allocated.heap := by
      simpa [base, allocated, Controller.Horn.TrackedAllocate.configuration] using scratch_marks state.heap n
    refine ⟨by omega, ?_⟩
    intro literal
    have lower : layout.base ≤ Controller.Horn.MarkStorage.address layout.base literal := by
      unfold Controller.Horn.MarkStorage.address; omega
    exact (Array.getElem_set_ne recordBound (marks.bound literal) (by omega)).trans (marks.entry literal)
  have storeFrame := endpoint_frame allocated layout.recordHeader recordBound
  obtain ⟨final, headersTrace, scratch, headerFrame, finalSize, finalPC, finalZero,
    finalOne, finalDecrement, finalRunning, finalStack, finalOutput⟩ :=
    Controller.Horn.HeaderReuse.restore_row_execution program (entry + 8) layout.base present.headers
      saved (Marks.initial n) initialMarks (by omega) savedPC
      (by simp [saved, endpointFinished, allocated, Controller.Horn.TrackedAllocate.configuration,
        start, counted, State.put, State.advance, input.zero]) savedRunning (by omega) (by omega)
  have allocatedCaller : allocated.stack = state.stack ∧ allocated.output = state.output := ⟨rfl, rfl⟩
  have allocatedLive : allocated.liveWords = state.liveWords + 5 * n + 4 := by
    simp [allocated, Controller.Horn.TrackedAllocate.configuration, start, counted,
      State.liveWords, State.put, State.advance]; omega
  have savedLive : saved.liveWords = allocated.liveWords := by
    simp [saved, endpointFinished, State.liveWords, State.put, State.advance]
  have lowFrame : ∀ cell, cell < state.heap.size → cell ≠ layout.recordHeader →
      final.heap[cell]? = state.heap[cell]? := by
    intro cell valid different
    have before : cell < layout.base := by omega
    have h := headerFrame cell (Or.inl (by omega))
    have e := storeFrame.2.1 cell different
    have a : allocated.heap[cell]? = state.heap[cell]? := by
      simp only [allocated, Controller.Horn.TrackedAllocate.configuration]
      exact Array.getElem?_append_left valid
    exact h.trans (e.trans a)
  have growing : state.heap.size ≤ final.heap.size := by omega
  have represented : Stored clauses layout.directory layout.source final.heap :=
    Controller.Horn.NormalizeLoop.directory_frame layout input.represented growing (by
      intro cell lower upper
      have before := layout.headersBefore layout.recordHeader (by simp)
      exact lowFrame cell (by omega) (by omega))
  have headerBefore : ∀ header ∈ [layout.directoryHeader, layout.endHeader], header < state.heap.size := by
    intro header member
    have h := layout.headersBefore header (by
      simp only [List.mem_cons, List.mem_singleton] at member ⊢
      tauto)
    have d := layout.directoryBefore
    have s := layout.sourceBefore
    have a : layout.source ≤ sourceOffset clauses layout.source clauses.length := by
      unfold sourceOffset; omega
    omega
  have directoryDifferent := directory_ne_record layout
  have endDifferent := end_ne_record layout
  have directoryCursor := Controller.Horn.JoinedNormalizeRow.cursor_of_option_frame input.cursor growing
    (lowFrame _ (headerBefore _ (by simp)) directoryDifferent)
  have endCursor := Controller.Horn.JoinedNormalizeRow.cursor_of_option_frame input.endpoint growing
    (lowFrame _ (headerBefore _ (by simp)) endDifferent)
  have recordSaved := endpoint_cursor allocated layout.recordHeader recordBound
  have recordCursor : CursorStored final.heap.size layout.recordHeader final.heap := by
    rw [finalSize]
    exact Controller.Horn.JoinedNormalizeRow.cursor_of_option_frame recordSaved (by omega)
      (headerFrame _ (Or.inl (by omega)))
  have preparedInput : Controller.Horn.ClauseEntry.Input clauses layout 0 final := by
    refine ⟨represented, input.indexBound, directoryCursor, endCursor, finalZero, ?_, ?_, finalRunning⟩
    · simpa [saved, endpointFinished, allocated, Controller.Horn.TrackedAllocate.configuration,
        start, counted, State.put, State.advance, input.one] using finalOne
    · simpa [saved, endpointFinished, allocated, Controller.Horn.TrackedAllocate.configuration,
        start, counted, State.put, State.advance, input.decrement] using finalDecrement
  have invariant : Controller.Horn.NormalizeLoop.Invariant clauses layout
      (state.heap.size + 5 * n + 4) 0 (Marks.initial n) final := by
    refine ⟨preparedInput, ⟨by omega, ?_, ?_⟩, recordCursor, by omega, scratch,
      Row.empty_correct _ (Marks.initial_clean n)⟩
    · simpa [Controller.Horn.NormalizeLoop.recordOffset, savedSize] using finalSize
    · intro index; exact Fin.elim0 index
  refine ⟨final, ?_, invariant, ?_, finalStack.trans storeFrame.2.2.2.1,
    finalOutput.trans storeFrame.2.2.2.2.1⟩
  · have whole := (startTrace.append allocTrace).append (storeTrace.append headersTrace)
    rw [allocatedLive, savedLive] at whole
    convert whole using 1 <;> omega
  · simpa [Nat.add_assoc] using finalPC

end Controller.Horn.NormalizeInitialize
