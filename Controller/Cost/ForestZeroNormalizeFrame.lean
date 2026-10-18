module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Horn.NormalizeLoop
public import Controller.Cost.ForestZeroBackendFrame

@[expose] public section

/-! Complete physical row normalization retains a protected caller prefix.
The actual source scan, record allocation and scratch reset share one trace. -/
namespace Controller.Cost.ForestZeroNormalizeFrame
open Controller.Cost Controller.Horn.SourceDirectory
open Controller.Horn.Worklist.IndexedNormalize
open Controller.Horn.RowScan Controller.Horn.SourceScan Controller.Horn.LiteralDispatch
open Controller.Horn.JoinedLiteral Controller.Horn.NormalizeProgram
open Controller.Cost.ForestZeroBackendFrame

/-- A proof-local program masks caller-stack/output instructions. A successful
nonhalting normalizer trace cannot execute any masked instruction. -/
def neutralInstruction : Instruction width registers → Instruction width registers
  | .push _ | .pop _ | .emit _ => .halt
  | instruction => instruction

def neutralProgram (program : Program width registers) : Program width registers :=
  program.map neutralInstruction

theorem neutral_program (program : Program width registers) :
    ∀ (position : Nat) (instruction : Instruction width registers), (neutralProgram program)[position]? = some instruction →
      CallerNeutral instruction := by
  intro position instruction found
  simp only [neutralProgram, Array.getElem?_map] at found
  cases original : program[position]? with
  | none => simp [original] at found
  | some source =>
    simp only [original, Option.map_some, Option.some.injEq] at found
    subst instruction
    cases source <;> trivial

/-- Mapping a fetched neutral code block preserves the block itself. This
uses array membership rather than expanding every finite index. -/
theorem neutral_block (block : Program width registers)
    (instructions : ∀ instruction ∈ block, CallerNeutral instruction) :
    neutralProgram block = block := by
  have identity : ∀ instruction ∈ block, neutralInstruction instruction = instruction := by
    intro instruction member
    have neutral := instructions instruction member
    cases instruction <;> first | rfl | contradiction
  unfold neutralProgram
  calc
    block.map neutralInstruction = block.map id := Array.map_congr_left identity
    _ = block := Array.map_id block

/-- A fetched neutral instruction is unchanged by the proof-local mask. -/
theorem neutral_fetch (program : Program width registers) (position : Nat)
    (instruction : Instruction width registers) (found : program[position]? = some instruction)
    (neutral : CallerNeutral instruction) :
    (neutralProgram program)[position]? = some instruction := by
  have identity : neutralInstruction instruction = instruction := by
    cases instruction <;> first | rfl | contradiction
  simp only [neutralProgram, Array.getElem?_map, found, Option.map_some, identity]

theorem execution_running {program : Program width registers}
    {before after : State width registers} {ticks peak : Nat}
    (trace : Execution program before after ticks peak) (running : after.halted = false) :
    before.halted = false := by
  cases trace with
  | refl => exact running
  | cons transition rest =>
    by_cases stopped : before.halted = true
    · unfold programStep at transition
      cases found : program[before.pc.val]? <;> simp [found, step, stopped] at transition
    · exact Bool.eq_false_iff.mpr stopped

theorem neutral_execution {program : Program width registers}
    {before after : State width registers} {ticks peak : Nat}
    (trace : Execution (neutralProgram program) before after ticks peak)
    (running : after.halted = false) : Execution program before after ticks peak := by
  induction trace with
  | refl state => exact Execution.refl state
  | @cons state middle final count bound transition rest ih =>
    have middleRunning := execution_running rest running
    have stateRunning := execution_running (Execution.cons transition rest) running
    apply Execution.cons _ (ih running)
    unfold programStep at transition ⊢
    simp only [neutralProgram, Array.getElem?_map] at transition
    cases found : program[state.pc.val]? with
    | none => simp [found] at transition
    | some instruction =>
      simp only [found, Option.map_some, Option.bind_some] at transition ⊢
      cases instruction <;> try exact transition
      all_goals
        simp only [neutralInstruction, step, stateRunning, Bool.false_eq_true, ite_false] at transition
        cases transition
        contradiction

theorem row_execution (prefixSize : Nat) (program : Program width 8)
    (entry base inputHeader firstHeader recordHeader start pcur ncur tcur : Nat)
    (clause : Controller.CNF.Clause (Fin n))
    (scanAt : RowAt program entry n base inputHeader firstHeader (entry + 77))
    (copyAt : Controller.Horn.JoinedRuleCopy.CodeAt program (entry + 77) base recordHeader n)
    (setupAt : Controller.Horn.ResetPointer.SetupAt program (entry + 119) (base + 2 * n + 2) base)
    (loopAt : Controller.Horn.ResetPointer.CodeAt program (entry + 122) (base + 5 * n + 4))
    (headersAt : Controller.Horn.ResetReuse.HeaderAt program (entry + 133) n base)
    (separate : Separation clause start inputHeader firstHeader base)
    (state : Controller.Cost.State width 8) (initialRow : Row n)
    (invariant : Controller.Horn.RowScan.Invariant clause initialRow start inputHeader firstHeader base
      pcur ncur tcur clause.length state)
    (dual : Controller.Horn.DualHornClause clause)
    (recordCursor : CursorStored state.heap.size recordHeader state.heap)
    (recordBelow : recordHeader < base)
    (differentInput : recordHeader ≠ inputHeader)
    (differentFirst : recordHeader ≠ firstHeader)
    (recordOutside : recordHeader < start ∨ start + 2 * clause.length ≤ recordHeader)
    (position : state.pc = word width entry) (capacity : entry + 144 < 2 ^ width)
    (heapFits : state.heap.size + 3 + clause.length < 2 ^ width)
    (neutral : ∀ (position : Nat) (instruction : Instruction width 8), program[position]? = some instruction → CallerNeutral instruction)
    (prefixBound : prefixSize ≤ state.heap.size)
    (prefixBase : prefixSize ≤ base)
    (prefixInput : prefixSize ≤ inputHeader)
    (prefixRecord : prefixSize ≤ recordHeader) :
    ∃ final : Controller.Cost.State width 8, ∃ normalized : Row n, ∃ ticks : Nat,
      (Execution program state final ticks (state.liveWords + 3 + (Controller.Horn.Worklist.compileClause clause).positives.length) ∧
      ticks ≤ 61 * clause.length + 54 ∧ normalized.Correct clause ∧
      Controller.Horn.RuleCopy.Stored (Controller.Horn.Worklist.compileClause clause) state.heap.size final.heap ∧
      CursorStored final.heap.size recordHeader final.heap ∧
      RowStored (Row.empty (Marks.clear normalized.touched normalized.marks)) base
        (base + 3 * n + 4) (base + 4 * n + 4) (base + 5 * n + 4) final.heap ∧
      (Row.empty (Marks.clear normalized.touched normalized.marks)).Correct [] ∧
      SourceStored clause start final.heap ∧ CursorStored start inputHeader final.heap ∧
      CursorStored start firstHeader final.heap ∧
      final.heap.size = state.heap.size + 3 + (Controller.Horn.Worklist.compileClause clause).positives.length ∧
      final.pc = word width (entry + 144) ∧ final.reg 2 = word width 0 ∧
      final.reg 5 = word width 1 ∧ final.reg 6 = word width (2 ^ width - 1) ∧
      final.halted = false ∧
      (∀ index, index < state.heap.size →
        ((index < base ∧ index ≠ inputHeader ∧ index ≠ recordHeader) ∨ base + 5 * n + 4 ≤ index) →
        final.heap[index]? = state.heap[index]?) ∧
      final.stack = state.stack ∧ final.output = state.output ) ∧ PrefixFrame prefixSize state.heap final.heap := by
  obtain ⟨final, normalized, ticks, facts⟩ :=
    Controller.Horn.NormalizeLoop.normalize_row_frames program entry base inputHeader firstHeader
      recordHeader start pcur ncur tcur clause scanAt copyAt setupAt loopAt headersAt separate
      state initialRow invariant dual recordCursor recordBelow differentInput differentFirst
      recordOutside position capacity heapFits neutral
  refine ⟨final, normalized, ticks, facts, ?_⟩
  have parts := facts
  rcases parts with ⟨trace, ticksBound, correct, stored, cursor, scratch, clean,
    source, input, first, size, pc, zero, one, decrement, running, cells, stack, output⟩
  refine ⟨prefixBound, by omega, ?_⟩
  intro index below
  apply cells index (by omega)
  exact Or.inl ⟨by omega, by omega, by omega⟩

open Controller.Horn.NormalizeLoop

theorem iteration_execution (prefixSize : Nat) (program : Program width 8) (entry : Nat)
    (clauses : List (Controller.CNF.Clause (Fin n)))
    (layout : Controller.Horn.SourceDirectory.Layout clauses)
    (present : CodeAt program entry clauses layout)
    (recordStart index : Nat) (marks : Marks n) (state : Controller.Cost.State width 8)
    (invariant : Invariant clauses layout recordStart index marks state)
    (nonempty : index < clauses.length)
    (dual : Controller.Horn.DualHornClause clauses[index])
    (position : state.pc = word width entry) (capacity : entry + 161 < 2 ^ width)
    (heapFits : state.heap.size + 3 + clauses[index].length < 2 ^ width)
    (neutral : ∀ (position : Nat) (instruction : Instruction width 8), program[position]? = some instruction → CallerNeutral instruction)
    (prefixBound : prefixSize ≤ state.heap.size)
    (prefixBase : prefixSize ≤ layout.base)
    (headersAbove : ∀ header ∈ [layout.recordHeader, layout.inputHeader, layout.firstHeader,
      layout.directoryHeader, layout.endHeader], prefixSize ≤ header) :
    ∃ next : Controller.Cost.State width 8, ∃ nextMarks : Marks n, ∃ ticks : Nat,
      Execution program state next ticks
        (state.liveWords + 3 + (Controller.Horn.Worklist.compileClause clauses[index]).positives.length) ∧
      Invariant clauses layout recordStart (index + 1) nextMarks next ∧
      next.pc = word width entry ∧
      ticks ≤ 61 * clauses[index].length + 71 ∧
      PrefixFrame prefixSize state.heap next.heap := by
  have headers := layout.headersDistinct
  have recordInput : layout.recordHeader ≠ layout.inputHeader := by
    have h := headers; simp only [List.nodup_cons, List.mem_cons, List.mem_singleton] at h; tauto
  have recordFirst : layout.recordHeader ≠ layout.firstHeader := by
    have h := headers; simp only [List.nodup_cons, List.mem_cons, List.mem_singleton] at h; tauto
  have recordDirectory : layout.recordHeader ≠ layout.directoryHeader := by
    have h := headers; simp only [List.nodup_cons, List.mem_cons, List.mem_singleton] at h; tauto
  have recordEnd : layout.recordHeader ≠ layout.endHeader := by
    have h := headers; simp only [List.nodup_cons, List.mem_cons, List.mem_singleton] at h; tauto
  have directoryInput : layout.directoryHeader ≠ layout.inputHeader := by
    have h := headers; simp only [List.nodup_cons, List.mem_cons, List.mem_singleton] at h; tauto
  have endDirectory : layout.endHeader ≠ layout.directoryHeader := by
    have h := headers; simp only [List.nodup_cons, List.mem_cons, List.mem_singleton] at h; tauto
  have endFirst : layout.endHeader ≠ layout.firstHeader := by
    have h := headers; simp only [List.nodup_cons, List.mem_cons, List.mem_singleton] at h; tauto
  have endInput : layout.endHeader ≠ layout.inputHeader := by
    have h := headers; simp only [List.nodup_cons, List.mem_cons, List.mem_singleton] at h; tauto
  have sourceAbove : layout.source ≤ sourceOffset clauses layout.source clauses.length := by
    unfold sourceOffset; omega
  have beforeBase : ∀ header ∈ [layout.recordHeader, layout.inputHeader, layout.firstHeader,
      layout.directoryHeader, layout.endHeader], header < layout.base := by
    intro header member
    have h := layout.headersBefore header member
    have := layout.directoryBefore
    have := layout.sourceBefore
    omega
  obtain ⟨entered, entryTrace, rowInput, scratch, entryPosition, entrySize,
    entryZero, entryOne, entryDecrement, entryRunning, directoryCursor, entryFrame⟩ :=
    entry_row_execution program entry (entry + 161) clauses layout index state present.directory
      invariant.input nonempty position (by omega) (by omega) (Row.empty marks)
      (layout.base + 3 * n + 4) (layout.base + 4 * n + 4) (layout.base + 5 * n + 4) invariant.scratch
  have entryCaller := caller_execution neutral entryTrace
  have entryLive : entered.liveWords = state.liveWords := by
    simp only [State.liveWords, entrySize, entryCaller.1, entryCaller.2]
  have enteredRecords := packed_records_frame invariant.records invariant.recordsAbove
    (show HighFrame (layout.base + 5 * n + 4) state.heap entered.heap from
      ⟨by omega, by
        intro cell above valid
        exact entryFrame cell
          (by have h := beforeBase layout.directoryHeader (by simp); omega)
          (by have h := beforeBase layout.firstHeader (by simp); omega)
          (by have h := beforeBase layout.inputHeader (by simp); omega)⟩) entrySize
  have enteredRecordCursor : CursorStored entered.heap.size layout.recordHeader entered.heap := by
    rw [entrySize]
    apply Controller.Horn.JoinedNormalizeRow.cursor_of_option_frame invariant.recordCursor (by omega)
    exact entryFrame _ (Ne.symm recordDirectory) (Ne.symm recordFirst) (Ne.symm recordInput)
  have enteredDirectory : Stored clauses layout.directory layout.source entered.heap :=
    directory_frame layout invariant.input.represented (by omega) (by
    intro cell lower upper
    exact entryFrame cell
      (by have := layout.headersBefore layout.directoryHeader (by simp); omega)
      (by have := layout.headersBefore layout.firstHeader (by simp); omega)
      (by have := layout.headersBefore layout.inputHeader (by simp); omega))
  have enteredEndpoint := Controller.Horn.JoinedNormalizeRow.cursor_of_option_frame invariant.input.endpoint
    (by omega) (entryFrame _ (Ne.symm endDirectory) (Ne.symm endFirst) (Ne.symm endInput))
  have sourceBoundary := Controller.Horn.NormalizeCNF.sourceOffset_succ clauses layout.source index nonempty
  have sourceEnd := Controller.Horn.NormalizeCNF.sourceOffset_le_end clauses layout.source (index + 1)
  have separation : Separation clauses[index] (sourceOffset clauses layout.source index)
      layout.inputHeader layout.firstHeader layout.base := by
    refine ⟨?_, beforeBase _ (by simp), beforeBase _ (by simp), rowInput.separateHeaders,
      rowInput.cursorOutside⟩
    have := layout.sourceBefore
    omega
  have scanInvariant : Controller.Horn.RowScan.Invariant clauses[index] (Row.empty marks)
      (sourceOffset clauses layout.source index) layout.inputHeader layout.firstHeader layout.base
      (layout.base + 3 * n + 4) (layout.base + 4 * n + 4) (layout.base + 5 * n + 4)
      clauses[index].length entered := by
    refine ⟨le_rfl, rowInput.source, rowInput.cursor, rowInput.first, scratch, ?_,
      entryZero, ?_, entryDecrement, entryRunning⟩
    · simpa only [List.drop_length] using invariant.clean
    · simpa [Controller.Horn.MarkStorage.encode] using entryOne
  obtain ⟨finished, normalized, used, rowTrace, rowCost, correct, record, recordCursor,
    emptyScratch, clean, source, inputCursor, firstCursor, size, rowPosition,
    zero, one, decrement, running, rowFrame, stack, output⟩ :=
    normalize_row_frames program (entry + 16) layout.base layout.inputHeader layout.firstHeader
      layout.recordHeader (sourceOffset clauses layout.source index)
      (layout.base + 3 * n + 4) (layout.base + 4 * n + 4) (layout.base + 5 * n + 4)
      clauses[index] present.row
      (by simpa only [Nat.add_assoc] using present.copy)
      (by simpa only [Nat.add_assoc] using present.setup)
      (by simpa only [Nat.add_assoc] using present.reset)
      (by simpa only [Nat.add_assoc] using present.headers)
      separation entered (Row.empty marks) scanInvariant dual enteredRecordCursor
      (beforeBase _ (by simp)) recordInput recordFirst
      (Or.inl (by
        have := layout.headersBefore layout.recordHeader (by simp)
        have := layout.directoryBefore
        unfold sourceOffset
        omega))
      entryPosition (by omega) (by simpa only [entrySize] using heapFits) neutral
  have growing : entered.heap.size ≤ finished.heap.size := by omega
  have recordsNext := packed_records_append enteredRecords nonempty invariant.recordsAbove
    (show HighFrame (layout.base + 5 * n + 4) entered.heap finished.heap from
      ⟨growing, fun cell above valid => rowFrame cell valid (Or.inr above)⟩) record size
  have immutable := directory_frame layout enteredDirectory growing (by
    intro cell lower upper
    apply rowFrame cell
    · have sourceSize := enteredDirectory.fits
      have scratchFits := RowStored.scratch_fits (Row.empty marks) layout.base
        (layout.base + 3 * n + 4) (layout.base + 4 * n + 4) (layout.base + 5 * n + 4) entered.heap scratch
      omega
    · refine Or.inl ⟨upper, ?_, ?_⟩
      · have before := layout.headersBefore layout.inputHeader (by simp); omega
      · have before := layout.headersBefore layout.recordHeader (by simp); omega)
  have nextDirectory := Controller.Horn.JoinedNormalizeRow.cursor_of_option_frame directoryCursor growing
    (rowFrame _ directoryCursor.bound (Or.inl ⟨beforeBase _ (by simp), directoryInput, Ne.symm recordDirectory⟩))
  have nextEndpoint := Controller.Horn.JoinedNormalizeRow.cursor_of_option_frame enteredEndpoint growing
    (rowFrame _ enteredEndpoint.bound (Or.inl ⟨beforeBase _ (by simp), endInput, Ne.symm recordEnd⟩))
  have returnFetch : program[finished.pc.val]? = some (.branchZero 2 (word width entry)) := by
    have pcValue : finished.pc.val = entry + 160 := by
      rw [rowPosition]
      simp only [word, Nat.add_assoc, Nat.mod_eq_of_lt (show entry + 16 + 144 < 2 ^ width by omega)]
    simpa only [pcValue] using present.returnBranch
  let next : Controller.Cost.State width 8 := { finished.advance with pc := word width entry }
  have returnTrace := return_execution program entry finished returnFetch zero running
  have nextInput : Controller.Horn.ClauseEntry.Input clauses layout (index + 1) next :=
    ⟨immutable, by omega, nextDirectory, nextEndpoint, zero, one, decrement, running⟩
  have nextInvariant : Invariant clauses layout recordStart (index + 1)
      (Marks.clear normalized.touched normalized.marks) next :=
    ⟨nextInput, recordsNext, recordCursor, invariant.recordsAbove, emptyScratch, clean⟩
  have finishedLive : finished.liveWords = entered.liveWords + 3 +
      (Controller.Horn.Worklist.compileClause clauses[index]).positives.length := by
    simp only [State.liveWords, size, stack, output]
    omega
  refine ⟨next, Marks.clear normalized.touched normalized.marks, 16 + used + 1,
    ?_, nextInvariant, rfl, by omega, ?_⟩
  · have whole := (entryTrace.append rowTrace).append returnTrace
    have peak : state.liveWords ≤ state.liveWords + 3 +
        (Controller.Horn.Worklist.compileClause clauses[index]).positives.length := by omega
    simpa only [entryLive, finishedLive, Nat.max_eq_right peak, Nat.max_self] using whole
  · have inputAbove := headersAbove layout.inputHeader (by simp)
    have firstAbove := headersAbove layout.firstHeader (by simp)
    have recordAbove := headersAbove layout.recordHeader (by simp)
    have directoryAbove := headersAbove layout.directoryHeader (by simp)
    refine ⟨prefixBound, ?_, ?_⟩
    · change prefixSize ≤ finished.heap.size
      omega
    · intro cell below
      change finished.heap[cell]? = state.heap[cell]?
      have rowHeld := rowFrame cell (by omega)
        (Or.inl ⟨by omega, by omega, by omega⟩)
      exact rowHeld.trans (entryFrame cell (by omega) (by omega) (by omega))



theorem cnf_execution (prefixSize : Nat) (program : Program width 8) (entry : Nat)
    (clauses : List (Controller.CNF.Clause (Fin n)))
    (layout : Controller.Horn.SourceDirectory.Layout clauses)
    (present : CodeAt program entry clauses layout) (recordStart index remaining : Nat)
    (marks : Marks n) (state : Controller.Cost.State width 8)
    (invariant : Invariant clauses layout recordStart index marks state)
    (suffix : index + remaining = clauses.length)
    (dual : ∀ i : Fin clauses.length, Controller.Horn.DualHornClause clauses[i.val])
    (position : state.pc = word width entry) (capacity : entry + 161 < 2 ^ width)
    (room : state.heap.size + 3 * remaining + literalSuffix clauses index < 2 ^ width)
    (neutral : ∀ (position : Nat) (instruction : Instruction width 8), program[position]? = some instruction → CallerNeutral instruction)
    (prefixBound : prefixSize ≤ state.heap.size)
    (prefixBase : prefixSize ≤ layout.base)
    (headersAbove : ∀ header ∈ [layout.recordHeader, layout.inputHeader, layout.firstHeader,
      layout.directoryHeader, layout.endHeader], prefixSize ≤ header) :
    ∃ final : Controller.Cost.State width 8, ∃ finalMarks : Marks n, ∃ ticks : Nat,
      Execution program state final ticks (state.liveWords + wordSuffix clauses index) ∧
      Invariant clauses layout recordStart clauses.length finalMarks final ∧
      final.pc = word width (entry + 161) ∧
      ticks ≤ 61 * literalSuffix clauses index + 71 * remaining + 6 ∧
      PrefixFrame prefixSize state.heap final.heap := by
  induction remaining generalizing index marks state with
  | zero =>
    have complete : index = clauses.length := by omega
    let final := testFinished state layout.directoryHeader layout.endHeader
      (layout.directory + 2 * clauses.length) (layout.directory + 2 * clauses.length) (entry + 161)
    have trace := Controller.Horn.ClauseEntry.directory_test_execution program entry layout.directoryHeader
      layout.endHeader layout.inputHeader layout.firstHeader (entry + 161) clauses layout.directory
      index present.directory state invariant.input.cursor invariant.input.endpoint invariant.input.indexBound
      invariant.input.represented.fits position invariant.input.running (by omega) (by omega)
    have frame := testFinished_frame state layout.directoryHeader layout.endHeader
      (layout.directory + 2 * clauses.length) (layout.directory + 2 * clauses.length) (entry + 161)
    have finalHeap : final.heap = state.heap := frame.2.1
    have finalInput : Controller.Horn.ClauseEntry.Input clauses layout clauses.length final := by
      refine ⟨?_, le_rfl, ?_, ?_,
        ?_, ?_, ?_, ?_⟩
      · simpa only [finalHeap] using invariant.input.represented
      · simpa only [complete, finalHeap] using invariant.input.cursor
      · simpa only [finalHeap] using invariant.input.endpoint
      · exact (frame.1 2 (by decide) (by decide) (by decide)).trans invariant.input.zero
      · exact (frame.1 5 (by decide) (by decide) (by decide)).trans invariant.input.one
      · exact (frame.1 6 (by decide) (by decide) (by decide)).trans invariant.input.decrement
      · exact frame.2.2.2.2.trans invariant.input.running
    have finalInvariant : Invariant clauses layout recordStart clauses.length marks final := by
      refine ⟨finalInput, ?_, ?_, invariant.recordsAbove, ?_, invariant.clean⟩
      · simpa only [complete, finalHeap] using invariant.records
      · simpa only [finalHeap] using invariant.recordCursor
      · simpa only [finalHeap] using invariant.scratch
    refine ⟨final, marks, 6, ?_, finalInvariant, ?_, ?_, ?_⟩
    · simpa only [complete, wordSuffix, List.drop_length, List.map_nil, List.sum_nil, Nat.add_zero] using trace.1
    · simp [final, testFinished]
    · omega
    · rw [finalHeap]
      exact ForestZeroBackendFrame.refl state.heap prefixBound
  | succ remaining ih =>
    have nonempty : index < clauses.length := by omega
    have steps := suffix_step clauses index nonempty
    obtain ⟨middle, middleMarks, used, firstTrace, middleInvariant, middlePosition, usedBound, firstPrefix⟩ :=
      iteration_execution prefixSize program entry clauses layout present recordStart index marks state invariant nonempty
        (dual ⟨index, nonempty⟩) position capacity (by omega) neutral prefixBound prefixBase headersAbove
    have oldEndpoint := invariant.records.endpoint
    have newEndpoint := middleInvariant.records.endpoint
    have offsetStep := recordOffset_succ clauses recordStart index nonempty
    have bodyBound := compiled_body_le clauses[index]
    have size : middle.heap.size = state.heap.size + 3 +
        (Controller.Horn.Worklist.compileClause clauses[index]).positives.length := by omega
    have caller := caller_execution neutral firstTrace
    have live : middle.liveWords = state.liveWords + 3 +
        (Controller.Horn.Worklist.compileClause clauses[index]).positives.length := by
      simp only [State.liveWords, size, caller.1, caller.2]
      omega
    have remainingRoom : middle.heap.size + 3 * remaining + literalSuffix clauses (index + 1) < 2 ^ width := by
      omega
    obtain ⟨final, finalMarks, ticks, restTrace, finalInvariant, finalPosition, ticksBound, restPrefix⟩ :=
      ih (index + 1) middleMarks middle middleInvariant (by omega) dual middlePosition remainingRoom firstPrefix.2.1
    have peak : max (state.liveWords + 3 +
        (Controller.Horn.Worklist.compileClause clauses[index]).positives.length)
        (middle.liveWords + wordSuffix clauses (index + 1)) = state.liveWords + wordSuffix clauses index := by
      rw [live, steps.2]
      omega
    refine ⟨final, finalMarks, used + ticks, ?_, finalInvariant, finalPosition, by omega, ForestZeroBackendFrame.trans firstPrefix restPrefix⟩
    simpa only [peak] using firstTrace.append restTrace




theorem all_execution (prefixSize : Nat) (program : Program width 8) (entry : Nat)
    (clauses : List (Controller.CNF.Clause (Fin n)))
    (layout : Controller.Horn.SourceDirectory.Layout clauses)
    (present : CodeAt program entry clauses layout) (recordStart : Nat)
    (marks : Marks n) (state : Controller.Cost.State width 8)
    (invariant : Invariant clauses layout recordStart 0 marks state)
    (dual : ∀ i : Fin clauses.length, Controller.Horn.DualHornClause clauses[i.val])
    (position : state.pc = word width entry) (capacity : entry + 161 < 2 ^ width)
    (room : state.heap.size + 3 * clauses.length + (clauses.map List.length).sum < 2 ^ width)
    (neutral : ∀ (position : Nat) (instruction : Instruction width 8), program[position]? = some instruction → CallerNeutral instruction)
    (prefixBound : prefixSize ≤ state.heap.size)
    (prefixBase : prefixSize ≤ layout.base)
    (headersAbove : ∀ header ∈ [layout.recordHeader, layout.inputHeader, layout.firstHeader,
      layout.directoryHeader, layout.endHeader], prefixSize ≤ header) :
    ∃ final : Controller.Cost.State width 8, ∃ finalMarks : Marks n, ∃ ticks peak : Nat,
      Execution program state final ticks peak ∧
      Invariant clauses layout recordStart clauses.length finalMarks final ∧
      final.pc = word width (entry + 161) ∧
      ticks ≤ 61 * (clauses.map List.length).sum + 71 * clauses.length + 6 ∧
      programWords program + peak ≤ programWords program + state.liveWords +
        3 * clauses.length + (clauses.map List.length).sum ∧
      PrefixFrame prefixSize state.heap final.heap := by
  obtain ⟨final, finalMarks, ticks, trace, complete, finalPosition, cost, sourceFrame⟩ :=
    cnf_execution prefixSize program entry clauses layout present recordStart 0 clauses.length marks state
      invariant (by omega) dual position capacity
      (by simpa only [literalSuffix, List.drop_zero] using room) neutral prefixBound prefixBase headersAbove
  have storage := wordSuffix_bound clauses 0
  refine ⟨final, finalMarks, ticks, state.liveWords + wordSuffix clauses 0,
    trace, complete, finalPosition, ?_, ?_, sourceFrame⟩
  · simpa only [literalSuffix, List.drop_zero] using cost
  · simp only [literalSuffix, List.drop_zero] at storage
    omega

/-! The local entry requires only the fetched normalizer blocks after proof-local
masking. Caller stack/output instructions elsewhere impose no restriction. -/
theorem all_execution_local (prefixSize : Nat) (program : Program width 8) (entry : Nat)
    (clauses : List (Controller.CNF.Clause (Fin n)))
    (layout : Controller.Horn.SourceDirectory.Layout clauses)
    (present : CodeAt (neutralProgram program) entry clauses layout) (recordStart : Nat)
    (marks : Marks n) (state : Controller.Cost.State width 8)
    (invariant : Invariant clauses layout recordStart 0 marks state)
    (dual : ∀ i : Fin clauses.length, Controller.Horn.DualHornClause clauses[i.val])
    (position : state.pc = word width entry) (capacity : entry + 161 < 2 ^ width)
    (room : state.heap.size + 3 * clauses.length + (clauses.map List.length).sum < 2 ^ width)
    (prefixBound : prefixSize ≤ state.heap.size)
    (prefixBase : prefixSize ≤ layout.base)
    (headersAbove : ∀ header ∈ [layout.recordHeader, layout.inputHeader, layout.firstHeader,
      layout.directoryHeader, layout.endHeader], prefixSize ≤ header) :
    ∃ final : Controller.Cost.State width 8, ∃ finalMarks : Marks n, ∃ ticks peak : Nat,
      Execution program state final ticks peak ∧
      Invariant clauses layout recordStart clauses.length finalMarks final ∧
      final.pc = word width (entry + 161) ∧
      ticks ≤ 61 * (clauses.map List.length).sum + 71 * clauses.length + 6 ∧
      programWords program + peak ≤ programWords program + state.liveWords +
        3 * clauses.length + (clauses.map List.length).sum ∧
      PrefixFrame prefixSize state.heap final.heap := by
  obtain ⟨final, finalMarks, ticks, peak, trace, complete, finalPosition, cost, storage, frame⟩ :=
    all_execution prefixSize (neutralProgram program) entry clauses layout present recordStart
      marks state invariant dual position capacity room (neutral_program program)
      prefixBound prefixBase headersAbove
  refine ⟨final, finalMarks, ticks, peak,
    neutral_execution trace complete.input.running, complete, finalPosition, cost, ?_, frame⟩
  simpa only [programWords, neutralProgram, Array.size_map] using storage

end Controller.Cost.ForestZeroNormalizeFrame
