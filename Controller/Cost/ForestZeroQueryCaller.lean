module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestZeroAssembly
public import Controller.Cost.ForestCursorMaterialize

public import Mathlib.Tactic.FinCases

@[expose] public section

/-! A query appends five physical control words above the reusable source and
dictionary prefix. Its local-variable count is stored from the allocator's
actual register after emission. Directory/source cells are preserved through
that store; source-dependent reads precede the hot backend's header-zero lease.
Source count formation and generated-code loading are separately charged. -/
namespace Controller.Cost.ForestZeroQueryCaller
open Controller.CNF Controller.Cost.GateProgram
open Controller.Cost.ForestZeroCompile Controller.Cost.ForestZeroDictionary
open Controller.Cost.ForestZeroRows Controller.Cost.ForestZeroEmit Controller.Cost.ForestZeroBuild
open Controller.Cost.ForestZeroQuery Controller.Cost.ForestZeroAssembly
open Controller.Cost.ForestCursorMaterialize

/-- All addresses are formed from the counted row/literal totals. The fifth
word is the directory endpoint, not the literal-stream endpoint. -/
def headerValues (protectedEnd rows literals : ℕ) : List ℕ :=
  [protectedEnd + 5 + 2 * rows + 2 * literals, 0,
   protectedEnd + 5 + 2 * rows, protectedEnd + 5, protectedEnd + 5 + 2 * rows]

@[simp] theorem headerValues_length : (headerValues protectedEnd rows literals).length = 5 := rfl

def headerHeap (width : ℕ) (heap : Array (Word width)) (rows literals : ℕ) : Array (Word width) :=
  allocatedHeap width heap (headerValues heap.size rows literals)

@[simp] theorem headerHeap_size : (headerHeap width heap rows literals).size = heap.size + 5 := by
  simp only [headerHeap, allocatedHeap_size, headerValues_length]

def headerLayout (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (rows literals : ℕ) : Layout ambient (headerHeap width heap rows literals).size where
  tableBase := layout.tableBase
  inverseBase := layout.inverseBase
  tableBound := by rw [headerHeap_size]; have := layout.tableBound; omega
  inverseBound := by rw [headerHeap_size]; have := layout.inverseBound; omega
  disjoint := layout.disjoint

theorem header_represented (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (state : Dictionary ambient) (represented : Represented heap layout state) (rows literals : ℕ) :
    Represented (headerHeap width heap rows literals) (headerLayout heap layout rows literals) state := by
  refine ⟨represented.coherent, ?_, ?_⟩
  · intro coordinate
    exact (allocatedHeap_prefix width heap (headerValues heap.size rows literals) _
      (layout.table_valid coordinate)).trans (represented.slots coordinate)
  · intro index coordinate member
    have valid : index < ambient := lt_of_lt_of_le (Array.getElem?_eq_some_iff.mp member).choose
      (count_le_ambient state represented.coherent)
    exact (allocatedHeap_prefix width heap (headerValues heap.size rows literals) _
      (layout.inverse_valid index valid)).trans (represented.inverse index coordinate member)

theorem header_cell (heap : Array (Word width)) (rows literals : ℕ) (index : ℕ) (bound : index < 5) :
    (headerHeap width heap rows literals)[heap.size + index]? =
      some (word width ((headerValues heap.size rows literals)[index]'bound)) := by
  have valid : heap.size + index < (headerHeap width heap rows literals).size := by rw [headerHeap_size]; omega
  rw [Array.getElem?_eq_getElem valid]
  exact congrArg some (allocatedHeap_cell width heap (headerValues heap.size rows literals) index bound)

/-- Header creation is ten fetched instructions and five real allocations. -/
theorem header_execution (program : Program width 4) (heap : Array (Word width))
    (base rows literals : ℕ) (address loaded temporary : Word width) (stack output : List (Word width))
    (programFits : base + 10 < 2 ^ width) (room : heap.size + 5 ≤ 2 ^ width)
    (block : BlockAt program base (writeCode width (headerValues heap.size rows literals))) :
    ∃ finalTemporary : Word width,
      Execution program ((ForestCounter.counterState heap base address loaded temporary).frame stack output)
        ((ForestCounter.counterState (headerHeap width heap rows literals) (base + 10)
          address loaded finalTemporary).frame stack output)
        10 (10 + heap.size + stack.length + output.length) := by
  obtain ⟨last, trace⟩ := write_execution program heap base (headerValues heap.size rows literals)
    address loaded temporary (by simpa only [headerValues_length] using programFits)
    (by simpa only [headerValues_length] using room) block
  refine ⟨last, ?_⟩
  convert trace.frame stack output using 1 <;>
    simp only [headerValues_length, headerHeap, Nat.add_assoc] <;> omega

/-- The finite source's directory and pairs survive a header write below both
regions. This is an actual one-cell heap update, not a source-copy operation. -/
theorem stored_after_header (clauses : List (Clause (Fin locals))) (directory source : ℕ)
    (heap : Array (Word width)) (stored : Controller.Horn.SourceDirectory.Stored clauses directory source heap)
    (header : ℕ) (valid : header < heap.size) (value : Word width)
    (beforeDirectory : header < directory) (beforeSource : header < source) :
    Controller.Horn.SourceDirectory.Stored clauses directory source (heap.set header value valid) := by
  refine ⟨by simpa using stored.fits, ?_, ?_⟩
  · intro index
    have original := stored.entry index
    constructor
    · exact Controller.Horn.RowScan.CursorStored.after_store original.1 header valid value (by omega)
    · exact Controller.Horn.RowScan.CursorStored.after_store original.2 header valid value (by omega)
  · intro index
    apply (stored.literals index).after_store header valid value
    left
    unfold Controller.Horn.SourceDirectory.sourceOffset
    omega

private theorem fetched (program : Program width 4) (s : State width 4) (cursor : ℕ)
    (instruction : Instruction width 4) (pc : s.pc = word width cursor)
    (fits : cursor < 2 ^ width) (entry : program[cursor]? = some instruction) :
    programStep program s = step instruction s := by
  unfold programStep
  rw [pc, show (word width cursor).val = cursor from Nat.mod_eq_of_lt fits, entry]
  rfl

/-- Header allocation preserves the allocator count on the real stack. -/
def preservingHeaderCode (width protectedEnd rows literals : ℕ) : Code width :=
  [.push 2] ++ writeCode width (headerValues protectedEnd rows literals) ++ [.pop 2]

@[simp] theorem preservingHeaderCode_length :
    (preservingHeaderCode width protectedEnd rows literals).length = 12 := by
  simp only [preservingHeaderCode, List.length_append, List.length_cons, List.length_nil,
    writeCode_length, headerValues_length]

private theorem push_count_word (program : Program width 4) (heap : Array (Word width))
    (base : ℕ) (address table count : Word width) (stack output : List (Word width))
    (fits : base + 1 < 2 ^ width) (entry : program[base]? = some (.push 2)) :
    Execution program ((ForestCounter.counterState heap base address table count).frame stack output)
      ((ForestCounter.counterState heap (base + 1) address table count).frame (count :: stack) output)
      1 (6 + heap.size + stack.length + output.length) := by
  let first := (ForestCounter.counterState heap base address table count).frame stack output
  let last := (ForestCounter.counterState heap (base + 1) address table count).frame (count :: stack) output
  have transition : programStep program first = some last := by
    rw [fetched program first base (.push 2) rfl (by omega) entry]
    simp only [step, first, last, State.frame, ForestCounter.counterState, State.advance,
      Bool.false_eq_true, ite_false, ite_true, List.nil_append,
      show (2 : Fin 4) ≠ 0 from by decide, show (2 : Fin 4) ≠ 1 from by decide,
      show (word width base).val = base from Nat.mod_eq_of_lt (by omega)]
  convert Execution.cons transition (Execution.refl last) using 1 <;>
    simp only [first, last, State.frame, ForestCounter.counterState, State.liveWords,
      List.length_cons, List.nil_append] <;> omega

private theorem pop_count_word (program : Program width 4) (heap : Array (Word width))
    (base : ℕ) (address table temporary count : Word width) (stack output : List (Word width))
    (fits : base + 1 < 2 ^ width) (entry : program[base]? = some (.pop 2)) :
    Execution program
      ((ForestCounter.counterState heap base address table temporary).frame (count :: stack) output)
      ((ForestCounter.counterState heap (base + 1) address table count).frame stack output)
      1 (6 + heap.size + stack.length + output.length) := by
  let first := (ForestCounter.counterState heap base address table temporary).frame (count :: stack) output
  let last := (ForestCounter.counterState heap (base + 1) address table count).frame stack output
  have transition : programStep program first = some last := by
    rw [fetched program first base (.pop 2) rfl (by omega) entry]
    simp only [step, first, last, State.frame, ForestCounter.counterState, State.advance,
      State.put, Bool.false_eq_true, ite_false, ite_true, List.nil_append,
      show (2 : Fin 4) ≠ 0 from by decide, show (2 : Fin 4) ≠ 1 from by decide,
      show (word width base).val = base from Nat.mod_eq_of_lt (by omega)]
    simp only [Option.some.injEq, State.mk.injEq, and_true, true_and]
    funext register
    fin_cases register <;> rfl
  convert Execution.cons transition (Execution.refl last) using 1 <;>
    simp only [first, last, State.frame, ForestCounter.counterState, State.liveWords,
      List.length_cons, List.nil_append] <;> omega

/-- Twelve actual instructions allocate the five query words while restoring
register two exactly; the saved count never becomes a generated constant. -/
theorem preserving_header_execution (program : Program width 4) (heap : Array (Word width))
    (base rows literals : ℕ) (address table count : Word width) (stack output : List (Word width))
    (programFits : base + 12 < 2 ^ width) (room : heap.size + 5 ≤ 2 ^ width)
    (block : BlockAt program base (preservingHeaderCode width heap.size rows literals)) :
    Execution program ((ForestCounter.counterState heap base address table count).frame stack output)
      ((ForestCounter.counterState (headerHeap width heap rows literals) (base + 12)
        address table count).frame stack output)
      12 (11 + heap.size + stack.length + output.length) := by
  have whole : BlockAt program base
      ([.push 2] ++ (writeCode width (headerValues heap.size rows literals) ++ [.pop 2])) := by
    simpa only [preservingHeaderCode, List.append_assoc] using block
  have firstBlock := BlockAt.prefix program base _ _ whole
  have tailBlock := BlockAt.suffix program base _ _ whole
  have writeBlock : BlockAt program (base + 1) (writeCode width (headerValues heap.size rows literals)) := by
    simpa only [List.length_cons, List.length_nil, Nat.add_zero] using BlockAt.prefix program _ _ _ tailBlock
  have lastBlock : BlockAt program (base + 11) [.pop 2] := by
    simpa only [List.length_cons, List.length_nil, Nat.add_zero, writeCode_length,
      headerValues_length, Nat.add_assoc] using BlockAt.suffix program _ _ _ tailBlock
  have first := push_count_word program heap base address table count stack output (by omega)
    (by simpa using firstBlock 0 (by simp))
  obtain ⟨temporary, middle⟩ := header_execution program heap (base + 1) rows literals
    address table count (count :: stack) output (by omega) room writeBlock
  have last := pop_count_word program (headerHeap width heap rows literals) (base + 11)
    address table temporary count stack output (by omega) (by simpa using lastBlock 0 (by simp))
  have joined := first.append (middle.append last)
  convert joined using 1 <;>
    simp only [headerHeap_size, List.length_cons, Nat.add_assoc] <;>
    (try simp only [Nat.max_eq_right (by omega :
      6 + heap.size + stack.length + output.length ≤ 11 + heap.size + stack.length + output.length)]) <;>
    omega

/-- The source-local count comes from register two, which the executed first
-touch allocator maintains. Register one, the reusable table base, survives. -/
def countCode (width header : ℕ) : Code width := [.constant 0 (word width header), .store 0 2]

@[simp] theorem countCode_length : (countCode width header).length = 2 := rfl

theorem count_execution (program : Program width 4) (heap : Array (Word width))
    (base header input table count scratch : ℕ) (stack output : List (Word width))
    (programFits : base + 2 < 2 ^ width) (headerFits : header < 2 ^ width)
    (valid : header < heap.size) (block : BlockAt program base (countCode width header)) :
    Execution program (ForestZeroTouch.atState heap base input table count scratch stack output)
      (ForestZeroTouch.atState (heap.set header (word width count) valid) (base + 2)
        header table count scratch stack output)
      2 (5 + heap.size + stack.length + output.length) := by
  let first := ForestZeroTouch.atState heap base input table count scratch stack output
  let middle := ForestZeroTouch.atState heap (base + 1) header table count scratch stack output
  let last := ForestZeroTouch.atState (heap.set header (word width count) valid) (base + 2)
    header table count scratch stack output
  have start : programStep program first = some middle := by
    rw [fetched program first base (.constant 0 (word width header)) rfl (by omega)
      (by simpa [countCode] using block 0 (by simp [countCode]))]
    simp only [step, first, middle, ForestZeroTouch.atState, State.advance, State.put,
      Bool.false_eq_true, ite_false, show (word width base).val = base from Nat.mod_eq_of_lt (by omega)]
    simp only [Option.some.injEq, State.mk.injEq, and_true, true_and]
    funext register
    fin_cases register <;> rfl
  have finish : programStep program middle = some last := by
    rw [fetched program middle (base + 1) (.store 0 2) rfl (by omega)
      (by simpa [countCode] using block 1 (by simp [countCode]))]
    simp only [step, middle, last, ForestZeroTouch.atState, State.advance,
      Bool.false_eq_true, ite_false, show (word width header).val = header from Nat.mod_eq_of_lt headerFits,
      show (word width (base + 1)).val = base + 1 from Nat.mod_eq_of_lt (by omega), valid, ite_true,
      Nat.add_assoc, dite_eq_left trivial,
      show (2 : Fin 4) ≠ 0 from by decide, show (2 : Fin 4) ≠ 1 from by decide]
  have trace := Execution.cons start (Execution.cons finish (Execution.refl last))
  convert trace using 1 <;>
    simp only [first, middle, last, ForestZeroTouch.atState_liveWords, Array.size_set, Nat.max_self]


/-- The complete allocated input before its count-header store. -/
def queryEmission (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (state : Dictionary ambient) (references : List (List (Reference ambient))) (scratch : ℕ) :
    ForestZeroEmit.Result ambient width :=
  let head := headerHeap width heap references.length references.flatten.length
  let headLayout := headerLayout heap layout references.length references.flatten.length
  let rows := originalRows references
  let source := head.size + 2 * rows.length
  let directory := ForestZeroDirectory.build head source state.coordinates.size rows
  let extended := directoryLayout head headLayout source state.coordinates.size rows
  emitReferences directory.heap extended state directory.cursor scratch references.flatten

theorem queryEmission_size (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (state : Dictionary ambient) (references : List (List (Reference ambient))) (scratch : ℕ) :
    (queryEmission heap layout state references scratch).heap.size =
      heap.size + 5 + 2 * references.length + 2 * references.flatten.length := by
  simp only [queryEmission, emitReferences_size, ForestZeroDirectory.build_size,
    headerHeap_size, originalRows, List.length_map]

def queryHeap (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (state : Dictionary ambient) (references : List (List (Reference ambient))) (scratch : ℕ) :=
  let emitted := queryEmission heap layout state references scratch
  emitted.heap.set (heap.size + 1) (word width emitted.dictionary.coordinates.size)
    (by rw [queryEmission_size]; omega)

@[simp] theorem queryHeap_size (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (state : Dictionary ambient) (references : List (List (Reference ambient))) (scratch : ℕ) :
    (queryHeap heap layout state references scratch).size =
      heap.size + 5 + 2 * references.length + 2 * references.flatten.length := by
  simp only [queryHeap, Array.size_set, queryEmission_size]

/-- The stored local count is derived from the same actual compiler as the
finite source clauses. It is not a caller-provided header value. -/
theorem queryEmission_dictionary (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (state : Dictionary ambient) (references : List (List (Reference ambient))) (scratch : ℕ) :
    (queryEmission heap layout state references scratch).dictionary =
      (compileRows state (originalRows references)).1 := by
  unfold queryEmission
  rw [emitReferences_dictionary]
  have rows := (compileRows_flatten state (originalRows references)).1
  have flat : (originalRows references).flatten =
      references.flatten.map (fun reference => (reference.coordinate, reference.positive)) := by
    simp only [originalRows, List.map_flatten]
  rw [flat] at rows
  exact rows.symm

theorem query_count_cell (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (state : Dictionary ambient) (references : List (List (Reference ambient))) (scratch : ℕ) :
    (queryHeap heap layout state references scratch)[heap.size + 1]? =
      some (word width (compileRows state (originalRows references)).1.coordinates.size) := by
  simp only [queryHeap, Array.getElem?_set_self, queryEmission_dictionary]

/-- Every other appended control word survives directory and pair emission. -/
theorem query_header_cell (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (state : Dictionary ambient) (represented : Represented heap layout state)
    (references : List (List (Reference ambient))) (scratch index : ℕ)
    (bound : index < 5) (notCount : index ≠ 1) :
    (queryHeap heap layout state references scratch)[heap.size + index]? =
      some (word width ((headerValues heap.size references.length references.flatten.length)[index]'bound)) := by
  let head := headerHeap width heap references.length references.flatten.length
  let headLayout := headerLayout heap layout references.length references.flatten.length
  let rows := originalRows references
  let source := head.size + 2 * rows.length
  let directory := ForestZeroDirectory.build head source state.coordinates.size rows
  let extended := directoryLayout head headLayout source state.coordinates.size rows
  have headerValid : heap.size + index < head.size := by dsimp only [head]; rw [headerHeap_size]; omega
  have original := header_cell heap references.length references.flatten.length index bound
  have allocated := ForestZeroDirectory.build_prefix head source state.coordinates.size rows
    (heap.size + index) headerValid
  have afterDirectory : directory.heap[heap.size + index]? =
      some (word width ((headerValues heap.size references.length references.flatten.length)[index]'bound)) :=
    allocated.trans original
  have retained := emit_suffix_frame directory.heap extended state
    (directory_represented head headLayout state
      (header_represented heap layout state represented references.length references.flatten.length)
      source state.coordinates.size rows)
    directory.cursor scratch references.flatten heap.size (heap.size + index)
    layout.tableBound layout.inverseBound (by omega)
    (by dsimp only [directory]; rw [ForestZeroDirectory.build_size]; omega)
  have beforeStore : (queryEmission heap layout state references scratch).heap[heap.size + index]? =
      some (word width ((headerValues heap.size references.length references.flatten.length)[index]'bound)) :=
    retained.trans afterDirectory
  unfold queryHeap
  rw [Array.getElem?_set_ne _ (by omega)]
  exact beforeStore

/-- The hot solver receives actual source cells from the completed constructor,
with all five mutable headers above the original protected prefix. -/
theorem query_stored (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (state : Dictionary ambient) (represented : Represented heap layout state)
    (references : List (List (Reference ambient))) (scratch : ℕ) :
    let compiled := compileRows state (originalRows references)
    let clauses := finiteClauses compiled.2.1 (rows_bounds state represented.coherent (originalRows references))
    Controller.Horn.SourceDirectory.Stored clauses (heap.size + 5)
      (heap.size + 5 + 2 * references.length) (queryHeap heap layout state references scratch) := by
  let head := headerHeap width heap references.length references.flatten.length
  let headLayout := headerLayout heap layout references.length references.flatten.length
  have constructed := assembled_stored head headLayout state
    (header_represented heap layout state represented references.length references.flatten.length)
    references state.coordinates.size
    ((ForestZeroDirectory.build head (head.size + 2 * (originalRows references).length)
      state.coordinates.size (originalRows references)).cursor) scratch
  have actual : Controller.Horn.SourceDirectory.Stored
      (finiteClauses (compileRows state (originalRows references)).2.1
        (rows_bounds state represented.coherent (originalRows references)))
      (heap.size + 5) (heap.size + 5 + 2 * references.length)
      (queryEmission heap layout state references scratch).heap := by
    simpa only [head, headLayout, queryEmission, headerHeap_size, originalRows, List.length_map] using constructed
  exact stored_after_header _ _ _ _ actual (heap.size + 1)
    (by rw [queryEmission_size]; omega)
    (word width (queryEmission heap layout state references scratch).dictionary.coordinates.size)
    (by omega) (by omega)

/-- Header allocation, directory/pair construction, then the actual allocator
count store. No source reads occur after this program's final store. -/
def queryCode (width base protectedEnd : ℕ) (references : List (List (Reference ambient))) : Code width :=
  preservingHeaderCode width protectedEnd references.length references.flatten.length ++
    assemblyCode width (base + 12) references ++ countCode width (protectedEnd + 1)

theorem queryCode_length (width base protectedEnd : ℕ)
    (references : List (List (Reference ambient))) :
    (queryCode width base protectedEnd references).length ≤
      16 + 5 * references.length + 28 * references.flatten.length := by
  have assemblyBound := assemblyCode_length width (base + 12) references
  simp only [queryCode, List.length_append, preservingHeaderCode_length, countCode_length]
  omega

/-- The complete physical query-input constructor starts from the reusable
source/dictionary heap. Both header allocation and directory construction save
the existing allocator count; the final input header comes from the emitted
count register. Its source/directory correspondence is `query_stored`. -/
theorem query_execution (program : Program width 4) (heap : Array (Word width))
    (layout : Layout ambient heap.size) (state : Dictionary ambient)
    (represented : Represented heap layout state) (channels sourceEnd : ℕ)
    (references : List (List (Reference ambient)))
    (stored : ∀ reference ∈ references.flatten, StoredReference heap channels sourceEnd reference)
    (beforeTable : sourceEnd ≤ layout.tableBase) (beforeInverse : sourceEnd ≤ layout.inverseBase)
    (base : ℕ) (stack output : List (Word width))
    (room : heap.size + 5 + 2 * references.length + 2 * references.flatten.length < 2 ^ width)
    (ambientFits : ambient + 1 < 2 ^ width)
    (programFits : base + (queryCode width base heap.size references).length < 2 ^ width)
    (block : BlockAt program base (queryCode width base heap.size references)) :
    let emitted := queryEmission heap layout state references 0
    ∃ ticks peak, Execution program
      (ForestZeroTouch.atState heap base (heap.size + 5 + 2 * references.length)
        layout.tableBase state.coordinates.size 0 (word width layout.inverseBase :: stack) output)
      (ForestZeroTouch.atState (queryHeap heap layout state references 0)
        (base + (queryCode width base heap.size references).length)
        (heap.size + 1) layout.tableBase emitted.dictionary.coordinates.size emitted.scratch
        (word width layout.inverseBase :: stack) output)
      ticks peak ∧ ticks ≤ 16 + 5 * references.length + 23 * references.flatten.length ∧
      peak ≤ 13 + heap.size + 2 * references.length + 2 * references.flatten.length +
        stack.length + output.length := by
  let head := headerHeap width heap references.length references.flatten.length
  let headLayout := headerLayout heap layout references.length references.flatten.length
  let source := heap.size + 5 + 2 * references.length
  let emitted := queryEmission heap layout state references 0
  let assemblyBase := base + 12
  let storeBase := assemblyBase + (assemblyCode width assemblyBase references).length
  have whole : BlockAt program base
      (preservingHeaderCode width heap.size references.length references.flatten.length ++
        (assemblyCode width assemblyBase references ++ countCode width (heap.size + 1))) := by
    simpa only [queryCode, assemblyBase, List.append_assoc] using block
  have headerBlock := BlockAt.prefix program base _ _ whole
  have tailBlock : BlockAt program assemblyBase
      (assemblyCode width assemblyBase references ++ countCode width (heap.size + 1)) := by
    simpa only [assemblyBase, preservingHeaderCode_length] using BlockAt.suffix program base _ _ whole
  have assemblyBlock := BlockAt.prefix program assemblyBase _ _ tailBlock
  have storeBlock : BlockAt program storeBase (countCode width (heap.size + 1)) :=
    BlockAt.suffix program assemblyBase _ _ tailBlock
  have allLength : (queryCode width base heap.size references).length =
      12 + (assemblyCode width assemblyBase references).length + 2 := by
    simp only [queryCode, assemblyBase, List.length_append, preservingHeaderCode_length, countCode_length]
  have headerTrace := preserving_header_execution program heap base references.length references.flatten.length
    (word width source) (word width layout.tableBase) (word width state.coordinates.size)
    (word width layout.inverseBase :: stack) output (by omega) (by omega) headerBlock
  have headerTrace' : Execution program
      (ForestZeroTouch.atState heap base source layout.tableBase state.coordinates.size 0
        (word width layout.inverseBase :: stack) output)
      (ForestZeroTouch.atState head assemblyBase source layout.tableBase state.coordinates.size 0
        (word width layout.inverseBase :: stack) output)
      12 (12 + heap.size + stack.length + output.length) := by
    convert headerTrace using 1 <;>
      simp only [head, assemblyBase, ForestZeroTouch.atState, ForestCounter.counterState,
        State.frame, List.nil_append, List.length_cons] <;> omega
  have retained : ∀ reference ∈ references.flatten, StoredReference head channels sourceEnd reference := by
    intro reference member
    have original := stored reference member
    refine ⟨?_, original.slotBound, original.headerBound, ?_, ?_, original.coordinateEq⟩
    · dsimp only [head]; rw [headerHeap_size]; have := original.sourceBound; omega
    · exact (allocatedHeap_prefix width heap (headerValues heap.size references.length references.flatten.length)
        reference.slot (lt_of_lt_of_le original.slotBound original.sourceBound)).trans original.slotWord
    · exact (allocatedHeap_prefix width heap (headerValues heap.size references.length references.flatten.length)
        0 (lt_of_lt_of_le original.headerBound original.sourceBound)).trans original.channelWord
  obtain ⟨assemblyTicks, assemblyPeak, assemblyTrace, assemblyTicksBound, assemblyPeakBound⟩ :=
    assembly_execution program head headLayout state
      (header_represented heap layout state represented references.length references.flatten.length)
      channels sourceEnd references retained beforeTable beforeInverse assemblyBase 0 stack output
      (by dsimp only [head]; rw [headerHeap_size]; exact room) ambientFits (by omega) assemblyBlock
  have assemblyTrace' : Execution program
      (ForestZeroTouch.atState head assemblyBase source layout.tableBase state.coordinates.size 0
        (word width layout.inverseBase :: stack) output)
      (ForestZeroTouch.atState emitted.heap storeBase emitted.input layout.tableBase
        emitted.dictionary.coordinates.size emitted.scratch (word width layout.inverseBase :: stack) output)
      assemblyTicks assemblyPeak := by
    simpa only [head, headLayout, source, emitted, queryEmission, headerHeap_size,
      originalRows, List.length_map, storeBase, headerLayout] using assemblyTrace
  have finalTrace := count_execution program emitted.heap storeBase (heap.size + 1)
    emitted.input layout.tableBase emitted.dictionary.coordinates.size emitted.scratch
    (word width layout.inverseBase :: stack) output (by omega) (by omega)
    (by dsimp only [emitted]; rw [queryEmission_size]; omega) storeBlock
  let prefixPeak := max (12 + heap.size + stack.length + output.length) assemblyPeak
  refine ⟨12 + assemblyTicks + 2,
    max prefixPeak (5 + emitted.heap.size + (word width layout.inverseBase :: stack).length + output.length),
    ?_, ?_, ?_⟩
  · convert (headerTrace'.append assemblyTrace').append finalTrace using 1 <;>
      simp only [source, storeBase, assemblyBase, allLength, queryHeap, emitted, prefixPeak,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  · omega
  · dsimp only [prefixPeak]
    dsimp only [head] at assemblyPeakBound
    rw [headerHeap_size] at assemblyPeakBound
    dsimp only [emitted]
    rw [queryEmission_size]
    simp only [List.length_cons]
    omega

end Controller.Cost.ForestZeroQueryCaller
