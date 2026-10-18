module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestZeroBuild
public import Controller.Cost.ForestZeroDirectory

public import Mathlib.Tactic.FinCases

@[expose] public section

/-! Query assembly places the complete directory before the signed pair stream.
Dictionary stores are confined below that directory. Every finite source row is
recovered from the actual allocated pairs, with occurrence order retained. -/
namespace Controller.Cost.ForestZeroAssembly
open Controller.CNF Controller.Cost.GateProgram
open Controller.Cost.ForestZeroCompile Controller.Cost.ForestZeroDictionary
open Controller.Cost.ForestZeroRows Controller.Cost.ForestZeroEmit Controller.Cost.ForestZeroBuild
open Controller.Cost.ForestZeroQuery

/-- Restrict an actual signed pair stream to its first clause. -/
theorem RawStored.first (left right : Clause ℕ)
    (stored : RawStored width (left ++ right) start heap) : RawStored width left start heap := by
  induction left generalizing start with
  | nil => exact RawStored.nil start heap (by have := stored.fits; omega)
  | cons literal rest ih =>
    cases stored with
    | cons _ _ _ _ label polarity tail =>
      exact RawStored.cons literal rest start heap label polarity (ih tail)

/-- A row boundary advances by two cells for every preceding occurrence. -/
theorem RawStored.after (left right : Clause ℕ)
    (stored : RawStored width (left ++ right) start heap) :
    RawStored width right (start + 2 * left.length) heap := by
  induction left generalizing start with
  | nil => simpa using stored
  | cons literal rest ih =>
    cases stored with
    | cons _ _ _ _ label polarity tail =>
      simpa only [List.length_cons, Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using ih tail

/-- Exact row slices are obtained from the one physically emitted flat stream. -/
theorem RawStored.row (rows : List (Clause ℕ))
    (stored : RawStored width rows.flatten start heap) (index : ℕ) (bound : index < rows.length) :
    RawStored width rows[index]
      (start + 2 * ((rows.take index).map List.length).sum) heap := by
  induction rows generalizing index start with
  | nil => simp at bound
  | cons first rest ih =>
    cases index with
    | zero =>
      simpa only [List.flatten_cons, List.take_zero, List.map_nil, List.sum_nil, Nat.mul_zero,
        Nat.add_zero, List.getElem_cons_zero] using RawStored.first first rest.flatten stored
    | succ index =>
      have tail := RawStored.after first rest.flatten stored
      have row := ih tail index (by simpa using bound)
      simpa only [List.take_succ_cons, List.map_cons, List.sum_cons, List.getElem_cons_succ,
        Nat.mul_add, Nat.add_assoc] using row

/-- Finite conversion changes the variable type, not any allocated pair value. -/
theorem finiteClause_raw (row : Clause ℕ) (bound : ∀ literal ∈ row, literal.1 < locals) :
    (finiteClause row bound).map (fun literal => (literal.1.val, literal.2)) = row := by
  simp only [finiteClause, List.map_map]
  change row.attach.map (fun literal => literal.val) = row
  exact List.attach_map_subtype_val row

def finiteClauses (rows : List (Clause ℕ)) (bound : BoundedRows locals rows) : List (Clause (Fin locals)) :=
  rows.attach.map fun row => finiteClause row.val (bound row.val row.property)

theorem finiteClauses_raw (rows : List (Clause ℕ)) (bound : BoundedRows locals rows) :
    (finiteClauses rows bound).map (List.map (fun literal => (literal.1.val, literal.2))) = rows := by
  unfold finiteClauses
  simp only [List.map_map, Function.comp_def, finiteClause_raw]
  exact List.attach_map_subtype_val rows

theorem finiteClauses_profile (rows : List (Clause ℕ)) (bound : BoundedRows locals rows) :
    (finiteClauses rows bound).map List.length = rows.map List.length := by
  have same := congrArg (List.map List.length) (finiteClauses_raw rows bound)
  simpa only [List.map_map, List.length_map, Function.comp_def] using same

/-- Actual directory words encode the running source cursor, with no repeated
prefix scan in the constructor. Prefix sums below are ghost specifications. -/
theorem directoryValues_entry (rows : List (Clause α)) (cursor index : ℕ) (bound : index < rows.length) :
    (directoryValues cursor rows)[2 * index]? =
      some (cursor + 2 * ((rows.take index).map List.length).sum) ∧
    (directoryValues cursor rows)[2 * index + 1]? =
      some (cursor + 2 * ((rows.take (index + 1)).map List.length).sum) := by
  induction rows generalizing cursor index with
  | nil => simp at bound
  | cons first rest ih =>
    cases index with
    | zero => simp [directoryValues, countClause_exact]
    | succ index =>
      have tail := ih (cursor + 2 * first.length) index (by simpa using bound)
      rw [show 2 * (index + 1) = 2 * index + 1 + 1 by omega]
      simp only [directoryValues, countClause_exact, List.getElem?_cons_succ]
      constructor
      · simpa only [List.take_succ_cons, List.map_cons, List.sum_cons, Nat.mul_add, Nat.add_assoc]
          using tail.1
      · simpa only [List.take_succ_cons, List.map_cons, List.sum_cons, Nat.mul_add, Nat.add_assoc]
          using tail.2

/-- Appending the directory retains the shared natural/physical dictionary. -/
def directoryLayout (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (cursor count : ℕ) (rows : List (Clause α)) :
    Layout ambient (ForestZeroDirectory.build heap cursor count rows).heap.size where
  tableBase := layout.tableBase
  inverseBase := layout.inverseBase
  tableBound := by rw [ForestZeroDirectory.build_size]; have := layout.tableBound; omega
  inverseBound := by rw [ForestZeroDirectory.build_size]; have := layout.inverseBound; omega
  disjoint := layout.disjoint

theorem directory_represented (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (state : Dictionary ambient) (represented : Represented heap layout state)
    (cursor count : ℕ) (rows : List (Clause α)) :
    Represented (ForestZeroDirectory.build heap cursor count rows).heap
      (directoryLayout heap layout cursor count rows) state := by
  refine ⟨represented.coherent, ?_, ?_⟩
  · intro coordinate
    exact (ForestZeroDirectory.build_prefix heap cursor count rows _ (layout.table_valid coordinate)).trans
      (represented.slots coordinate)
  · intro index coordinate present
    have valid : index < ambient := lt_of_lt_of_le (Array.getElem?_eq_some_iff.mp present).choose
      (count_le_ambient state represented.coherent)
    exact (ForestZeroDirectory.build_prefix heap cursor count rows _ (layout.inverse_valid index valid)).trans
      (represented.inverse index coordinate present)

/-- A checked directory cell survives every subsequent source occurrence,
including fresh dictionary allocation and duplicate signed occurrences. -/
theorem emitted_directory_cell (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (state : Dictionary ambient) (represented : Represented heap layout state)
    (cursor count input scratch : ℕ) (rows : List (Clause α)) (references : List (Reference ambient))
    (index : ℕ) (bound : index < (directoryValues cursor rows).length) :
    let directory := ForestZeroDirectory.build heap cursor count rows
    let extended := directoryLayout heap layout cursor count rows
    (emitReferences directory.heap extended state input scratch references).heap[heap.size + index]? =
      some (word width ((directoryValues cursor rows)[index]'bound)) := by
  let directory := ForestZeroDirectory.build heap cursor count rows
  let extended := directoryLayout heap layout cursor count rows
  have original : directory.heap[heap.size + index]? =
      some (word width ((directoryValues cursor rows)[index]'bound)) := by
    rw [show directory.heap = ForestCursorMaterialize.allocatedHeap width heap
      (directoryValues cursor rows) from ForestZeroDirectory.build_heap heap cursor count rows]
    have valid : heap.size + index <
        (ForestCursorMaterialize.allocatedHeap width heap (directoryValues cursor rows)).size := by
      rw [ForestCursorMaterialize.allocatedHeap_size]; omega
    rw [Array.getElem?_eq_getElem valid]
    exact congrArg some (ForestCursorMaterialize.allocatedHeap_cell width heap (directoryValues cursor rows) index bound)
  have frame := emit_suffix_frame directory.heap extended state
    (directory_represented heap layout state represented cursor count rows) input scratch references
    heap.size (heap.size + index) layout.tableBound layout.inverseBound (by omega)
    (by have lengths := directoryValues_length cursor rows; dsimp only [directory]; rw [ForestZeroDirectory.build_size]; omega)
  exact frame.trans original


/-- Allocation changes variable identifiers while retaining every row length. -/
theorem compileRows_profile (state : Dictionary ambient) (coherent : Coherent state)
    (rows : List (Clause (Fin ambient))) :
    (compileRows state rows).2.1.map List.length = rows.map List.length := by
  have profiles : ∀ {left : List (Clause ℕ)} {right : List (Clause (Fin ambient))},
      List.Forall₂ (fun a b => a.length = b.length) left right →
        left.map List.length = right.map List.length := by
    intro left right relation
    induction relation with
    | nil => rfl
    | cons rowRelation tailRelation ih => simp only [List.map_cons, rowRelation, ih]
  exact profiles (List.Forall₂.imp (fun _ _ relation => List.Forall₂.length_eq relation)
    (rows_correspondence state coherent rows))

theorem profile_take {left : List (Clause α)} {right : List (Clause β)}
    (same : left.map List.length = right.map List.length) (index : ℕ) :
    (left.take index).map List.length = (right.take index).map List.length := by
  rw [List.map_take, List.map_take, same]

/-- The finite source directory is obtained from the actual flat stream. -/
theorem raw_stream_rows (clauses : List (Clause (Fin locals)))
    (stored : RawStored width
      ((clauses.map (List.map (fun literal => (literal.1.val, literal.2)))).flatten) source heap) :
    ∀ index : Fin clauses.length,
      Controller.Horn.RowScan.SourceStored clauses[index.val]
        (Controller.Horn.SourceDirectory.sourceOffset clauses source index.val) heap := by
  intro index
  have row := RawStored.row (clauses.map (List.map (fun literal => (literal.1.val, literal.2))))
    stored index.val (by simpa only [List.length_map] using index.isLt)
  apply raw_to_source
  simpa only [List.getElem_map, ← List.map_take, List.map_map, List.length_map,
    Function.comp_def, Controller.Horn.SourceDirectory.sourceOffset] using row

/-- This is the actual complete query input representation. The directory was
allocated first, the emitter performed dictionary touches and pair allocations,
and finite rows come from the same executed local-ID compiler. No source-word
array, row model or directory oracle is supplied. Query headers are separate. -/
theorem assembled_stored (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (state : Dictionary ambient) (represented : Represented heap layout state)
    (references : List (List (Reference ambient))) (count input scratch : ℕ) :
    let original := references.map (List.map (fun reference => (reference.coordinate, reference.positive)))
    let compiled := compileRows state original
    let clauses := finiteClauses compiled.2.1 (rows_bounds state represented.coherent original)
    let source := heap.size + 2 * original.length
    let directory := ForestZeroDirectory.build heap source count original
    let extended := directoryLayout heap layout source count original
    let emitted := emitReferences directory.heap extended state input scratch references.flatten
    Controller.Horn.SourceDirectory.Stored clauses heap.size source emitted.heap := by
  let original := references.map (List.map (fun reference => (reference.coordinate, reference.positive)))
  let compiled := compileRows state original
  let clauses := finiteClauses compiled.2.1 (rows_bounds state represented.coherent original)
  let source := heap.size + 2 * original.length
  let directory := ForestZeroDirectory.build heap source count original
  let extended := directoryLayout heap layout source count original
  let emitted := emitReferences directory.heap extended state input scratch references.flatten
  have extendedRep := directory_represented heap layout state represented source count original
  have emittedSize : emitted.heap.size = heap.size + 2 * original.length + 2 * references.flatten.length := by
    dsimp only [emitted, directory]
    rw [emitReferences_size, ForestZeroDirectory.build_size]
  have profile : clauses.map List.length = original.map List.length :=
    (finiteClauses_profile compiled.2.1 (rows_bounds state represented.coherent original)).trans
      (compileRows_profile state represented.coherent original)
  have sameLength : clauses.length = original.length := by
    have lengths := congrArg List.length profile
    simpa only [List.length_map] using lengths
  have originalFlat : original.flatten =
      references.flatten.map (fun reference => (reference.coordinate, reference.positive)) := by
    simp only [original, List.map_flatten]
  have raw : RawStored width compiled.2.1.flatten source emitted.heap := by
    have actual := emit_raw_stored directory.heap extended state extendedRep input scratch
      references.flatten heap.size layout.tableBound layout.inverseBound
      (by dsimp only [directory]; rw [ForestZeroDirectory.build_size]; omega)
    have same := (compileRows_flatten state original).2
    rw [originalFlat] at same
    rw [← same] at actual
    simpa only [directory, source, ForestZeroDirectory.build_size] using actual
  have finiteRaw : RawStored width
      ((clauses.map (List.map (fun literal => (literal.1.val, literal.2)))).flatten) source emitted.heap := by
    simpa only [clauses, finiteClauses_raw] using raw
  refine ⟨?_, ?_, raw_stream_rows clauses finiteRaw⟩
  · rw [sameLength, emittedSize]; omega
  · intro index
    have valid : index.val < original.length := by rw [← sameLength]; exact index.isLt
    have entries := directoryValues_entry original source index.val valid
    have startBound : 2 * index.val < (directoryValues source original).length := by
      rw [directoryValues_length]; omega
    have endBound : 2 * index.val + 1 < (directoryValues source original).length := by
      rw [directoryValues_length]; omega
    have first := emitted_directory_cell heap layout state represented source count input scratch
      original references.flatten (2 * index.val) startBound
    have last := emitted_directory_cell heap layout state represented source count input scratch
      original references.flatten (2 * index.val + 1) endBound
    have startWord : (directoryValues source original)[2 * index.val]'startBound =
        source + 2 * ((original.take index.val).map List.length).sum := by
      have option := entries.1
      rw [List.getElem?_eq_getElem startBound] at option
      exact Option.some.inj option
    have endWord : (directoryValues source original)[2 * index.val + 1]'endBound =
        source + 2 * ((original.take (index.val + 1)).map List.length).sum := by
      have option := entries.2
      rw [List.getElem?_eq_getElem endBound] at option
      exact Option.some.inj option
    have firstValid : heap.size + 2 * index.val < emitted.heap.size := by rw [emittedSize]; omega
    have lastValid : heap.size + 2 * index.val + 1 < emitted.heap.size := by rw [emittedSize]; omega
    constructor
    · refine ⟨firstValid, ?_⟩
      have actual : emitted.heap[heap.size + 2 * index.val]? = some (word width
          (source + 2 * ((original.take index.val).map List.length).sum)) := by
        simpa only [startWord] using first
      rw [Array.getElem?_eq_getElem firstValid] at actual
      change emitted.heap[heap.size + 2 * index.val] =
        word width (source + 2 * ((clauses.take index.val).map List.length).sum)
      rw [profile_take profile index.val]
      exact Option.some.inj actual
    · refine ⟨lastValid, ?_⟩
      have actual : emitted.heap[heap.size + 2 * index.val + 1]? = some (word width
          (source + 2 * ((original.take (index.val + 1)).map List.length).sum)) := by
        simpa only [endWord, Nat.add_assoc] using last
      rw [Array.getElem?_eq_getElem lastValid] at actual
      change emitted.heap[heap.size + 2 * index.val + 1] =
        word width (source + 2 * ((clauses.take (index.val + 1)).map List.length).sum)
      rw [profile_take profile (index.val + 1)]
      exact Option.some.inj actual


private theorem fetched (program : Program width 4) (s : State width 4)
    (cursor : ℕ) (instruction : Instruction width 4)
    (pc : s.pc = word width cursor) (fits : cursor < 2 ^ width)
    (entry : program[cursor]? = some instruction) :
    programStep program s = step instruction s := by
  unfold programStep
  rw [pc, show (word width cursor).val = cursor from Nat.mod_eq_of_lt fits, entry]
  rfl

/-- Preserve the actual allocator count across the register-two directory pass. -/
private theorem save_count (program : Program width 4) (heap : Array (Word width))
    (base cursor table count scratch : ℕ) (stack output : List (Word width))
    (fits : base + 1 < 2 ^ width) (entry : program[base]? = some (.push 2)) :
    Execution program (ForestZeroTouch.atState heap base cursor table count scratch stack output)
      (ForestZeroTouch.atState heap (base + 1) cursor table count scratch (word width count :: stack) output)
      1 (6 + heap.size + stack.length + output.length) := by
  let first := ForestZeroTouch.atState heap base cursor table count scratch stack output
  let last := ForestZeroTouch.atState heap (base + 1) cursor table count scratch (word width count :: stack) output
  have transition : programStep program first = some last := by
    rw [fetched program first base (.push 2) rfl (by omega) entry]
    change some { first.advance with stack := word width count :: stack } = some last
    simp only [first, last, ForestZeroTouch.atState, State.advance,
      show (word width base).val = base from Nat.mod_eq_of_lt (by omega)]
  convert Execution.cons transition (Execution.refl last) using 1 <;>
    simp only [first, last, ForestZeroTouch.atState_liveWords, List.length_cons] <;> omega

/-- Pop the saved word into the physical count register before first touch. -/
private theorem restore_count (program : Program width 4) (heap : Array (Word width))
    (base cursor table oldCount count scratch : ℕ) (stack output : List (Word width))
    (fits : base + 1 < 2 ^ width) (entry : program[base]? = some (.pop 2)) :
    Execution program
      (ForestZeroTouch.atState heap base cursor table oldCount scratch (word width count :: stack) output)
      (ForestZeroTouch.atState heap (base + 1) cursor table count scratch stack output)
      1 (6 + heap.size + stack.length + output.length) := by
  let first := ForestZeroTouch.atState heap base cursor table oldCount scratch (word width count :: stack) output
  let last := ForestZeroTouch.atState heap (base + 1) cursor table count scratch stack output
  have transition : programStep program first = some last := by
    rw [fetched program first base (.pop 2) rfl (by omega) entry]
    change some { first.advance.put 2 (word width count) with stack := stack } = some last
    simp only [first, last, ForestZeroTouch.atState, State.advance, State.put,
      show (word width base).val = base from Nat.mod_eq_of_lt (by omega)]
    simp only [Option.some.injEq, State.mk.injEq, and_true, true_and]
    funext register
    fin_cases register <;> rfl
  convert Execution.cons transition (Execution.refl last) using 1 <;>
    simp only [first, last, ForestZeroTouch.atState_liveWords, List.length_cons] <;> omega

def originalRows (references : List (List (Reference ambient))) : List (Clause (Fin ambient)) :=
  references.map (List.map (fun reference => (reference.coordinate, reference.positive)))

def assemblyCode (width base : ℕ) (references : List (List (Reference ambient))) : Code width :=
  [.push 2] ++ ForestZeroDirectory.code width (originalRows references) ++ [.pop 2] ++
    emitCode width (base + 2 + (ForestZeroDirectory.code width (originalRows references)).length) references.flatten

theorem assemblyCode_length (width base : ℕ) (references : List (List (Reference ambient))) :
    (assemblyCode width base references).length ≤ 2 + 5 * references.length + 28 * references.flatten.length := by
  have emitter := emitCode_length width
    (base + 2 + (ForestZeroDirectory.code width (originalRows references)).length) references.flatten
  simp only [assemblyCode, List.length_append, List.length_cons, List.length_nil,
    ForestZeroDirectory.code_length, originalRows, List.length_map] at *
  omega

theorem originalRows_literals (references : List (List (Reference ambient))) :
    ((originalRows references).map List.length).sum = references.flatten.length := by
  simp only [originalRows, List.map_map, List.length_map, Function.comp_def, List.length_flatten]

/-- Complete actual directory/pair construction, including physical allocator
count preservation. All directory boundaries precede the first pair; source
cells are retained rather than copied between the two phases. -/
theorem assembly_execution (program : Program width 4) (heap : Array (Word width))
    (layout : Layout ambient heap.size) (state : Dictionary ambient)
    (represented : Represented heap layout state) (channels sourceEnd : ℕ)
    (references : List (List (Reference ambient)))
    (stored : ∀ reference ∈ references.flatten, StoredReference heap channels sourceEnd reference)
    (beforeTable : sourceEnd ≤ layout.tableBase) (beforeInverse : sourceEnd ≤ layout.inverseBase)
    (base scratch : ℕ) (stack output : List (Word width))
    (room : heap.size + 2 * references.length + 2 * references.flatten.length < 2 ^ width)
    (ambientFits : ambient + 1 < 2 ^ width)
    (programFits : base + (assemblyCode width base references).length < 2 ^ width)
    (block : BlockAt program base (assemblyCode width base references)) :
    let rows := originalRows references
    let source := heap.size + 2 * rows.length
    let directory := ForestZeroDirectory.build heap source state.coordinates.size rows
    let extended := directoryLayout heap layout source state.coordinates.size rows
    let emitted := emitReferences directory.heap extended state directory.cursor scratch references.flatten
    ∃ ticks peak, Execution program
      (ForestZeroTouch.atState heap base source layout.tableBase state.coordinates.size scratch
        (word width layout.inverseBase :: stack) output)
      (ForestZeroTouch.atState emitted.heap (base + (assemblyCode width base references).length)
        emitted.input layout.tableBase emitted.dictionary.coordinates.size emitted.scratch
        (word width layout.inverseBase :: stack) output)
      ticks peak ∧ ticks ≤ 2 + 5 * references.length + 23 * references.flatten.length ∧
      peak ≤ 8 + heap.size + 2 * references.length + 2 * references.flatten.length + stack.length + output.length := by
  let rows := originalRows references
  let source := heap.size + 2 * rows.length
  let directory := ForestZeroDirectory.build heap source state.coordinates.size rows
  let extended := directoryLayout heap layout source state.coordinates.size rows
  let emitterBase := base + 2 + (ForestZeroDirectory.code width rows).length
  let emitted := emitReferences directory.heap extended state directory.cursor scratch references.flatten
  have rowsLength : rows.length = references.length := by simp only [rows, originalRows, List.length_map]
  have whole : BlockAt program base ([.push 2] ++
      (ForestZeroDirectory.code width rows ++ ([.pop 2] ++ emitCode width emitterBase references.flatten))) := by
    simpa only [assemblyCode, rows, emitterBase, List.append_assoc] using block
  have pushBlock := BlockAt.prefix program base _ _ whole
  have afterPush := BlockAt.suffix program base _ _ whole
  have directoryBlock : BlockAt program (base + 1) (ForestZeroDirectory.code width rows) := by
    simpa only [List.length_cons, List.length_nil, Nat.add_zero] using BlockAt.prefix program _ _ _ afterPush
  have afterDirectory : BlockAt program (base + 1 + (ForestZeroDirectory.code width rows).length)
      ([.pop 2] ++ emitCode width emitterBase references.flatten) := by
    simpa only [List.length_cons, List.length_nil, Nat.add_zero] using BlockAt.suffix program _ _ _ afterPush
  have popBlock := BlockAt.prefix program _ _ _ afterDirectory
  have emitterBlock : BlockAt program emitterBase (emitCode width emitterBase references.flatten) := by
    convert BlockAt.suffix program _ _ _ afterDirectory using 1 <;>
      simp only [emitterBase, List.length_cons, List.length_nil] <;> omega
  have allLength : (assemblyCode width base references).length =
      2 + (ForestZeroDirectory.code width rows).length + (emitCode width emitterBase references.flatten).length := by
    simp only [assemblyCode, rows, emitterBase, List.length_append, List.length_cons, List.length_nil]; omega
  have first := save_count program heap base source layout.tableBase state.coordinates.size scratch
    (word width layout.inverseBase :: stack) output (by omega) (by simpa using pushBlock 0 (by simp))
  have middle := ForestZeroDirectory.execution program heap (base + 1) source layout.tableBase
    state.coordinates.size scratch (word width state.coordinates.size :: word width layout.inverseBase :: stack) output
    rows (by rw [rowsLength]; omega)
    (by
      dsimp only [source]
      have literals : (rows.map countClause).sum = references.flatten.length := by
        have countEq : (countClause : Clause (Fin ambient) → ℕ) = List.length :=
          funext countClause_exact
        rw [countEq]
        exact originalRows_literals references
      rw [rowsLength, literals]
      exact room)
    (by omega) directoryBlock
  have restored := restore_count program directory.heap
    (base + 1 + (ForestZeroDirectory.code width rows).length) directory.cursor layout.tableBase directory.count
    state.coordinates.size scratch (word width layout.inverseBase :: stack) output (by omega)
    (by simpa using popBlock 0 (by simp))
  have retained : ∀ reference ∈ references.flatten,
      StoredReference directory.heap channels sourceEnd reference := by
    intro reference member
    have original := stored reference member
    refine ⟨?_, original.slotBound, original.headerBound, ?_, ?_, original.coordinateEq⟩
    · dsimp only [directory]; rw [ForestZeroDirectory.build_size]; have := original.sourceBound; omega
    · exact (ForestZeroDirectory.build_prefix heap source state.coordinates.size rows reference.slot
        (lt_of_lt_of_le original.slotBound original.sourceBound)).trans original.slotWord
    · exact (ForestZeroDirectory.build_prefix heap source state.coordinates.size rows 0
        (lt_of_lt_of_le original.headerBound original.sourceBound)).trans original.channelWord
  have directorySize : directory.heap.size = heap.size + 2 * rows.length :=
    ForestZeroDirectory.build_size heap source state.coordinates.size rows
  have dirCodeLength : (ForestZeroDirectory.code width rows).length = 5 * rows.length :=
    ForestZeroDirectory.code_length (width := width) rows
  have callerCodeFits : emitterBase + (emitCode width emitterBase references.flatten).length < 2 ^ width := by
    have position : emitterBase + (emitCode width emitterBase references.flatten).length =
        base + (assemblyCode width base references).length := by
      rw [allLength, show emitterBase = base + 2 + (ForestZeroDirectory.code width rows).length from rfl]
      omega
    rw [position]; exact programFits
  obtain ⟨emitTicks, emitPeak, final, ticksBound, peakBound⟩ := emitReferences_execution program directory.heap extended
    state (directory_represented heap layout state represented source state.coordinates.size rows)
    channels sourceEnd references.flatten retained beforeTable beforeInverse emitterBase directory.cursor scratch stack output
    (by rw [directorySize, rowsLength]; exact room) ambientFits
    callerCodeFits emitterBlock
  have restored' : Execution program
      (ForestZeroTouch.atState directory.heap (base + 1 + (ForestZeroDirectory.code width rows).length)
        directory.cursor layout.tableBase directory.count scratch
        (word width state.coordinates.size :: word width layout.inverseBase :: stack) output)
      (ForestZeroTouch.atState directory.heap emitterBase directory.cursor layout.tableBase state.coordinates.size scratch
        (word width layout.inverseBase :: stack) output)
      1 (6 + directory.heap.size + (word width layout.inverseBase :: stack).length + output.length) := by
    have position : base + 1 + (ForestZeroDirectory.code width rows).length + 1 = emitterBase := by
      dsimp only [emitterBase]; omega
    simpa only [position] using restored
  have prefixTrace := (first.append middle).append restored'
  have full := prefixTrace.append final
  let priorPeak := max
    (max (6 + heap.size + (word width layout.inverseBase :: stack).length + output.length)
      (5 + heap.size + 2 * rows.length +
        (word width state.coordinates.size :: word width layout.inverseBase :: stack).length + output.length))
    (6 + directory.heap.size + (word width layout.inverseBase :: stack).length + output.length)
  refine ⟨1 + 5 * rows.length + 1 + emitTicks, max priorPeak emitPeak, ?_, ?_, ?_⟩
  · convert full using 1 <;>
      simp only [allLength, priorPeak, List.length_cons, Nat.add_assoc] <;>
      first | rfl | (congr 1 <;> omega) | omega
  · rw [rowsLength]; omega
  · apply Nat.max_le.mpr
    constructor
    · dsimp only [priorPeak]
      apply Nat.max_le.mpr
      constructor
      · apply Nat.max_le.mpr
        constructor <;> simp only [List.length_cons] <;> omega
      · rw [directorySize, rowsLength]
        simp only [List.length_cons]
        omega
    · rw [directorySize, rowsLength] at peakBound
      omega

end Controller.Cost.ForestZeroAssembly
