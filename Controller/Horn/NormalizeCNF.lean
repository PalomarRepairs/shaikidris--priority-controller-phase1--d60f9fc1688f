module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Horn.ClauseEntry

@[expose] public section

/-!
# Shared physical CNF normalizer program

One stored entry routine and one stored row routine serve every clause. Literal
occurrences reside in input memory. Tautological clauses retain allocated
three-word inert records, so source and rule directories have the same row count.
-/
namespace Controller.Horn.NormalizeCNF

open Controller.Cost Controller.Horn.SourceDirectory

/-- The161-instruction shared loop uses physical directory endpoints and source
pointers. No program block is duplicated for a source literal or clause. -/
def code (width entry n base recordHeader inputHeader firstHeader directoryHeader endHeader : Nat) :
    Program width 8 :=
  Controller.Horn.ClauseEntry.code width directoryHeader endHeader inputHeader firstHeader (entry + 161) ++
  Controller.Horn.RowScan.rowCode width (entry + 16) n base inputHeader firstHeader (entry + 93) ++
  Controller.Horn.JoinedRuleCopy.code width n (entry + 93) base recordHeader ++
  Controller.Horn.ResetPointer.setupCode width (base + 2 * n + 2) base ++
  Controller.Horn.ResetPointer.code width (entry + 138) (base + 5 * n + 4) ++
  Controller.Horn.ResetReuse.headerCode width n base ++
  #[.branchZero 2 (word width entry)]

@[simp] theorem code_size (width entry n base recordHeader inputHeader firstHeader directoryHeader endHeader : Nat) :
    (code width entry n base recordHeader inputHeader firstHeader directoryHeader endHeader).size = 161 := by
  simp [code, Controller.Horn.ResetPointer.setupCode]

@[simp] theorem code_words (width entry n base recordHeader inputHeader firstHeader directoryHeader endHeader : Nat) :
    programWords (code width entry n base recordHeader inputHeader firstHeader directoryHeader endHeader) = 644 := by
  simp [programWords]

/-- The bound charges each repeated directory test as well as each physical
source occurrence. The final empty-directory test uses six instructions. -/
def tickBound (clauses : List (Controller.CNF.Clause (Fin n))) : Nat :=
  61 * (clauses.map List.length).sum + 71 * clauses.length + 6

/-- Old allocated records remain represented separately from the immutable
source directory and reusable scratch buffers. -/
structure Records (rules : List (Controller.Horn.Worklist.Rule (Fin n))) (offsets : List Nat)
    (start : Nat) (heap : Array (Word width)) : Prop where
  sameLength : offsets.length = rules.length
  first : offsets.head? = if rules.isEmpty then none else some start
  entry : ∀ index : Fin rules.length,
    Controller.Horn.RuleCopy.Stored rules[index.val] (offsets[index.val]'(by simpa [sameLength] using index.isLt)) heap
  contiguous : ∀ index : Nat, ∀ bound : index + 1 < rules.length,
    offsets[index + 1]'(by simpa [sameLength] using bound) =
      offsets[index]'(by rw [sameLength]; omega) + 3 + (rules[index]'(by omega)).positives.length


/-- Full nonempty directory entry consumes the six fetched test instructions
and the ten fetched setup instructions on the same actual program. -/
theorem entry_execution (program : Program width 8) (entry exit : Nat)
    (clauses : List (Controller.CNF.Clause (Fin n))) (layout : Layout clauses)
    (index : Nat) (state : State width 8)
    (present : Controller.Horn.ClauseEntry.At program entry layout.directoryHeader layout.endHeader
      layout.inputHeader layout.firstHeader exit)
    (input : Controller.Horn.ClauseEntry.Input clauses layout index state)
    (nonempty : index < clauses.length)
    (position : state.pc = word width entry) (capacity : entry + 16 < 2 ^ width)
    (heapFits : state.heap.size < 2 ^ width) :
    ∃ entered : State width 8, Execution program state entered 16 state.liveWords := by
  let pointer := layout.directory + 2 * index
  let endpoint := layout.directory + 2 * clauses.length
  let tested := Controller.Horn.RowScan.testFinished state layout.directoryHeader layout.endHeader pointer endpoint exit
  have directoryFits := input.represented.fits
  have different : pointer ≠ endpoint := by dsimp [pointer, endpoint]; omega
  obtain ⟨testTrace, testPC, testHeap⟩ := Controller.Horn.ClauseEntry.directory_test_execution
    program entry layout.directoryHeader layout.endHeader layout.inputHeader layout.firstHeader exit
    clauses layout.directory index present state input.cursor input.endpoint input.indexBound directoryFits
    position input.running capacity heapFits
  have testedPC : tested.pc = word width (entry + 6) := by
    simpa [tested, pointer, endpoint, show index ≠ clauses.length by omega] using testPC
  have testedHeap : tested.heap = state.heap := testHeap
  have frame := Controller.Horn.RowScan.testFinished_frame state layout.directoryHeader layout.endHeader pointer endpoint exit
  have testedLive : tested.liveWords = state.liveWords := by
    change (Controller.Horn.RowScan.testFinished state layout.directoryHeader layout.endHeader pointer endpoint exit).liveWords = state.liveWords
    simp only [State.liveWords, frame.2.1, frame.2.2.1, frame.2.2.2.1]
  have heldPointer : tested.reg 0 = word width pointer := by
    simp [tested, Controller.Horn.RowScan.testFinished, Controller.Horn.RowScan.testPrepared,
      different, State.advance, State.put]
  have testedOne : tested.reg 5 = word width 1 := (frame.1 5 (by decide) (by decide) (by decide)).trans input.one
  have testedRunning : tested.halted = false := frame.2.2.2.2.trans input.running
  obtain ⟨first, last⟩ := input.represented.entry ⟨index, nonempty⟩
  have firstTested : Controller.Horn.SourceScan.CursorStored (sourceOffset clauses layout.source index)
      pointer tested.heap := by simpa only [testedHeap] using first
  have lastTested : Controller.Horn.SourceScan.CursorStored (sourceOffset clauses layout.source (index + 1))
      (pointer + 1) tested.heap := by simpa only [testedHeap, pointer, Nat.add_assoc] using last
  have directoryBound : layout.directoryHeader < tested.heap.size := by
    rw [testedHeap]
    exact input.cursor.bound
  have firstBelow : layout.firstHeader < layout.directory := layout.headersBefore layout.firstHeader (by simp)
  have inputBelow : layout.inputHeader < layout.directory := layout.headersBefore layout.inputHeader (by simp)
  have firstBound : layout.firstHeader < tested.heap.size := by rw [testedHeap]; omega
  have inputBound : layout.inputHeader < tested.heap.size := by rw [testedHeap]; omega
  have pointerFits : pointer + 2 < 2 ^ width := by dsimp [pointer]; omega
  let entered := Controller.Horn.ClauseEntry.prepared tested pointer
    (sourceOffset clauses layout.source index) (sourceOffset clauses layout.source (index + 1))
    layout.directoryHeader layout.firstHeader layout.inputHeader directoryBound firstBound inputBound
  have setupTrace := Controller.Horn.ClauseEntry.setup_execution program entry
    layout.directoryHeader layout.endHeader layout.inputHeader layout.firstHeader exit pointer
    (sourceOffset clauses layout.source index) (sourceOffset clauses layout.source (index + 1))
    present tested firstTested lastTested directoryBound firstBound inputBound heldPointer testedOne
    testedPC testedRunning capacity (by simpa only [testedHeap] using heapFits) pointerFits
  refine ⟨entered, ?_⟩
  simpa only [testedLive, Nat.max_self, Nat.reduceAdd] using testTrace.append setupTrace


/-- Source directory entry only overwrites existing header cells. -/
theorem prepared_size (state : State width 8) (pointer rowStart rowEnd directoryHeader firstHeader inputHeader : Nat)
    (directoryBound : directoryHeader < state.heap.size)
    (firstBound : firstHeader < state.heap.size) (inputBound : inputHeader < state.heap.size) :
    (Controller.Horn.ClauseEntry.prepared state pointer rowStart rowEnd directoryHeader firstHeader inputHeader
      directoryBound firstBound inputBound).heap.size = state.heap.size := by
  simp [Controller.Horn.ClauseEntry.prepared, State.advance, State.put]

private theorem cursor_from_option {heap : Array (Word width)} {header pointer : Nat}
    (bound : header < heap.size) (value : heap[header]? = some (word width pointer)) :
    Controller.Horn.SourceScan.CursorStored pointer header heap := by
  refine ⟨bound, ?_⟩
  simpa only [Array.getElem?_eq_getElem bound, Option.some.injEq] using value

/-- All three control words contain the boundary values actually loaded by the
entry trace. Distinctness is a property of the initialized physical layout. -/
theorem prepared_cursors (state : State width 8) (pointer rowStart rowEnd directoryHeader firstHeader inputHeader : Nat)
    (directoryBound : directoryHeader < state.heap.size)
    (firstBound : firstHeader < state.heap.size) (inputBound : inputHeader < state.heap.size)
    (directoryFirst : directoryHeader ≠ firstHeader) (directoryInput : directoryHeader ≠ inputHeader)
    (firstInput : firstHeader ≠ inputHeader) :
    Controller.Horn.SourceScan.CursorStored (pointer + 2) directoryHeader
      (Controller.Horn.ClauseEntry.prepared state pointer rowStart rowEnd directoryHeader firstHeader inputHeader
        directoryBound firstBound inputBound).heap ∧
    Controller.Horn.SourceScan.CursorStored rowStart firstHeader
      (Controller.Horn.ClauseEntry.prepared state pointer rowStart rowEnd directoryHeader firstHeader inputHeader
        directoryBound firstBound inputBound).heap ∧
    Controller.Horn.SourceScan.CursorStored rowEnd inputHeader
      (Controller.Horn.ClauseEntry.prepared state pointer rowStart rowEnd directoryHeader firstHeader inputHeader
        directoryBound firstBound inputBound).heap := by
  have size := prepared_size state pointer rowStart rowEnd directoryHeader firstHeader inputHeader
    directoryBound firstBound inputBound
  refine ⟨cursor_from_option (by rw [size]; exact directoryBound) ?_,
    cursor_from_option (by rw [size]; exact firstBound) ?_,
    cursor_from_option (by rw [size]; exact inputBound) ?_⟩
  · simp only [Controller.Horn.ClauseEntry.prepared, State.advance, State.put]
    rw [Array.getElem?_set_ne _ (Ne.symm directoryInput),
      Array.getElem?_set_ne _ (Ne.symm directoryFirst), Array.getElem?_set_self]
  · simp only [Controller.Horn.ClauseEntry.prepared, State.advance, State.put]
    rw [Array.getElem?_set_ne _ (Ne.symm firstInput), Array.getElem?_set_self]
  · simp [Controller.Horn.ClauseEntry.prepared, State.advance, State.put]


/-- The opcode-neutral condition in the universal row caller-frame theorem is
discharged by the concrete emitted outer program. -/
theorem code_caller_neutral (width entry n base recordHeader inputHeader firstHeader directoryHeader endHeader : Nat)
    (position : Nat) (instruction : Instruction width 8)
    (fetch : (code width entry n base recordHeader inputHeader firstHeader directoryHeader endHeader)[position]? = some instruction) :
    CallerNeutral instruction := by
  have every : ∀ operation ∈ code width entry n base recordHeader inputHeader firstHeader directoryHeader endHeader,
      CallerNeutral operation := by
    simp only [code, Array.forall_mem_append]
    repeat' apply And.intro
    all_goals simp [Controller.Horn.ClauseEntry.code,
      Controller.Horn.RowScan.rowCode, Controller.Horn.RowScan.testCode,
      Controller.Horn.SourceScan.pairCode, Controller.Horn.RowScan.readMarksCode,
      Controller.Horn.RowScan.dispatchCode, Controller.Horn.RowScan.writeMarkCode,
      Controller.Horn.JoinedRuleCopy.code, Controller.Horn.RuleDispatch.code,
      Controller.Horn.RuleCopy.recordAddressCode, Controller.Horn.RuleCopy.headerCode,
      Controller.Horn.RuleDispatch.skipCode, Controller.Horn.RuleCopy.setupCode,
      Controller.Horn.RuleCopy.bodyCode, Controller.Horn.RuleCopy.finishCode,
      Controller.Horn.RuleCopy.cursorUpdateCode, Controller.Horn.ResetPointer.setupCode,
      Controller.Horn.ResetPointer.code, Controller.Horn.ResetReuse.headerCode,
      CallerNeutral, Array.mem_def, -Array.mem_toList_iff]
  exact every instruction (Array.mem_of_getElem? fetch)


/-- The difference of two adjacent directory pointers is exactly the physical
two-word source incidence count for that row. -/
theorem sourceOffset_succ (clauses : List (Controller.CNF.Clause (Fin n)))
    (source index : Nat) (bound : index < clauses.length) :
    sourceOffset clauses source (index + 1) = sourceOffset clauses source index + 2 * clauses[index].length := by
  simp only [sourceOffset, List.take_succ_eq_append_getElem bound, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero,
    Nat.mul_add, Nat.add_assoc]

/-- Every source prefix boundary precedes the complete physical source end. -/
theorem sourceOffset_le_end (clauses : List (Controller.CNF.Clause (Fin n))) (source index : Nat) :
    sourceOffset clauses source index ≤ sourceOffset clauses source clauses.length := by
  have decomposition : (clauses.map List.length).sum =
      ((clauses.take index).map List.length).sum + ((clauses.drop index).map List.length).sum := by
    conv_lhs => rw [← List.take_append_drop index clauses]
    simp only [List.map_append, List.sum_append]
  simp only [sourceOffset, List.take_length]
  omega


/-- The physical directory setup supplies the exact source-input representation
consumed by the shared row scan, including duplicate source occurrences. -/
theorem prepared_row_input (clauses : List (Controller.CNF.Clause (Fin n))) (layout : Layout clauses)
    (index : Nat) (bound : index < clauses.length) (state : State width 8)
    (represented : Stored clauses layout.directory layout.source state.heap)
    (directoryBound : layout.directoryHeader < state.heap.size)
    (firstBound : layout.firstHeader < state.heap.size) (inputBound : layout.inputHeader < state.heap.size) :
    Controller.Horn.RowScan.RowInput clauses[index] (sourceOffset clauses layout.source index)
      layout.inputHeader layout.firstHeader
      (Controller.Horn.ClauseEntry.prepared state (layout.directory + 2 * index)
        (sourceOffset clauses layout.source index) (sourceOffset clauses layout.source (index + 1))
        layout.directoryHeader layout.firstHeader layout.inputHeader directoryBound firstBound inputBound).heap := by
  have tail1 : [layout.inputHeader, layout.firstHeader, layout.directoryHeader, layout.endHeader].Nodup :=
    (List.nodup_cons.mp layout.headersDistinct).2
  have tail2 : [layout.firstHeader, layout.directoryHeader, layout.endHeader].Nodup :=
    (List.nodup_cons.mp tail1).2
  have inputNot := (List.nodup_cons.mp tail1).1
  have firstNot := (List.nodup_cons.mp tail2).1
  have directoryFirst : layout.directoryHeader ≠ layout.firstHeader := by
    intro equal
    exact firstNot (by simp [equal])
  have directoryInput : layout.directoryHeader ≠ layout.inputHeader := by
    intro equal
    exact inputNot (by simp [equal])
  have firstInput : layout.firstHeader ≠ layout.inputHeader := by
    intro equal
    exact inputNot (by simp [equal])
  have cursors := prepared_cursors state (layout.directory + 2 * index)
    (sourceOffset clauses layout.source index) (sourceOffset clauses layout.source (index + 1))
    layout.directoryHeader layout.firstHeader layout.inputHeader directoryBound firstBound inputBound
    directoryFirst directoryInput firstInput
  have directoryBelow : layout.directoryHeader < sourceOffset clauses layout.source index := by
    have before := layout.headersBefore layout.directoryHeader (by simp)
    have dataBefore := layout.directoryBefore
    unfold sourceOffset
    omega
  have firstBelow : layout.firstHeader < sourceOffset clauses layout.source index := by
    have before := layout.headersBefore layout.firstHeader (by simp)
    have dataBefore := layout.directoryBefore
    unfold sourceOffset
    omega
  have inputBelow : layout.inputHeader < sourceOffset clauses layout.source index := by
    have before := layout.headersBefore layout.inputHeader (by simp)
    have dataBefore := layout.directoryBefore
    unfold sourceOffset
    omega
  have oldSource := represented.literals ⟨index, bound⟩
  have growing := prepared_size state (layout.directory + 2 * index)
    (sourceOffset clauses layout.source index) (sourceOffset clauses layout.source (index + 1))
    layout.directoryHeader layout.firstHeader layout.inputHeader directoryBound firstBound inputBound
  have newSource : Controller.Horn.RowScan.SourceStored clauses[index]
      (sourceOffset clauses layout.source index)
      (Controller.Horn.ClauseEntry.prepared state (layout.directory + 2 * index)
        (sourceOffset clauses layout.source index) (sourceOffset clauses layout.source (index + 1))
        layout.directoryHeader layout.firstHeader layout.inputHeader directoryBound firstBound inputBound).heap :=
    Controller.Horn.JoinedNormalizeRow.source_of_option_frame oldSource
    (by rw [growing]) (by
      intro position lower upper
      change sourceOffset clauses layout.source index ≤ position at lower
      exact Controller.Horn.ClauseEntry.prepared_frame state (layout.directory + 2 * index)
        (sourceOffset clauses layout.source index) (sourceOffset clauses layout.source (index + 1))
        layout.directoryHeader layout.firstHeader layout.inputHeader directoryBound firstBound inputBound
        position (by omega) (by omega) (by omega))
  refine ⟨newSource, ?_, cursors.2.1, Ne.symm firstInput, Or.inl inputBelow, Or.inl firstBelow⟩
  simpa only [sourceOffset_succ clauses layout.source index bound] using cursors.2.2

end Controller.Horn.NormalizeCNF
