module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.EnumerationFixedEmit
public import Controller.Cost.EnumerationDirectoryFrame

@[expose] public section

/-! One fixed directory and source-pair constructor for every prefix. The
directory template is compiled once; actual selected rows share its profile.
Fixed base occurrences precede the resident mask-selected unit-slot batch. -/
namespace Controller.Cost.EnumerationFixedAssembly
open Controller.CNF Controller.Cost.GateProgram Controller.Cost.ForestZeroTouch
open Controller.Cost.ForestZeroEmit Controller.Cost.ForestZeroDictionary
open Controller.Cost.ForestZeroCompile Controller.Cost.ForestZeroRows
open Controller.Cost.ForestZeroAssembly Controller.Cost.EnumerationSlotBatch

def code (width base : Nat) (baseRefs : List (List (Reference ambient))) (slots : List (Slot ambient)) : Code width :=
  EnumerationDirectoryFrame.code width (EnumerationFixedProfile.template baseRefs slots) ++
    EnumerationFixedEmit.code width
      (base + (EnumerationDirectoryFrame.code width (EnumerationFixedProfile.template baseRefs slots)).length)
      baseRefs slots

def result (trueFlags falseFlags : Slot ambient → Bool) (heap : Array (Word width))
    (layout : Layout ambient heap.size) (dictionary : Dictionary ambient) (scratch : Nat)
    (baseRefs : List (List (Reference ambient))) (slots : List (Slot ambient)) : Result ambient width :=
  let rows := originalRows (EnumerationFixedProfile.references baseRefs slots trueFlags falseFlags)
  let source := heap.size + 2 * rows.length
  let directory := ForestZeroDirectory.build heap source dictionary.coordinates.size rows
  let extended := directoryLayout heap layout source dictionary.coordinates.size rows
  EnumerationFixedEmit.result trueFlags falseFlags directory.heap extended dictionary directory.cursor scratch baseRefs slots

theorem code_bound (baseRefs : List (List (Reference ambient))) (slots : List (Slot ambient)) :
    (code width base baseRefs slots).length ≤
      2 + 5 * (baseRefs.length + slots.length + 1) + 28 * baseRefs.flatten.length + 90 * slots.length := by
  have emission := EnumerationFixedEmit.code_bound (width := width)
    (base := base + (EnumerationDirectoryFrame.code width (EnumerationFixedProfile.template baseRefs slots)).length)
    baseRefs slots
  simp only [code, List.length_append, EnumerationDirectoryFrame.code_length,
    EnumerationFixedProfile.template_length]
  simp only [EnumerationDirectoryFrame.code_length, EnumerationFixedProfile.template_length] at emission
  omega

@[simp] theorem result_size (trueFlags falseFlags : Slot ambient → Bool)
    (heap : Array (Word width)) (layout : Layout ambient heap.size) (dictionary : Dictionary ambient)
    (scratch : Nat) (baseRefs : List (List (Reference ambient))) (slots : List (Slot ambient)) :
    (result trueFlags falseFlags heap layout dictionary scratch baseRefs slots).heap.size =
      heap.size + 2 * (baseRefs.length + slots.length + 1) + 2 * baseRefs.flatten.length + 2 * slots.length := by
  simp [result, EnumerationFixedEmit.result_size, ForestZeroDirectory.build_size, originalRows]

theorem result_heap (trueFlags falseFlags : Slot ambient → Bool)
    (heap : Array (Word width)) (layout : Layout ambient heap.size) (dictionary : Dictionary ambient)
    (scratch : Nat) (baseRefs : List (List (Reference ambient))) (slots : List (Slot ambient)) :
    let refs := EnumerationFixedProfile.references baseRefs slots trueFlags falseFlags
    let rows := originalRows refs
    let source := heap.size + 2 * rows.length
    let directory := ForestZeroDirectory.build heap source dictionary.coordinates.size rows
    (result trueFlags falseFlags heap layout dictionary scratch baseRefs slots).heap =
      (emitReferences directory.heap (directoryLayout heap layout source dictionary.coordinates.size rows)
        dictionary directory.cursor scratch refs.flatten).heap := by
  exact EnumerationFixedEmit.result_heap _ _ _ _ _ _ _ _ _

theorem result_dictionary (trueFlags falseFlags : Slot ambient → Bool)
    (heap : Array (Word width)) (layout : Layout ambient heap.size) (dictionary : Dictionary ambient)
    (scratch : Nat) (baseRefs : List (List (Reference ambient))) (slots : List (Slot ambient)) :
    let refs := EnumerationFixedProfile.references baseRefs slots trueFlags falseFlags
    let rows := originalRows refs
    let source := heap.size + 2 * rows.length
    let directory := ForestZeroDirectory.build heap source dictionary.coordinates.size rows
    (result trueFlags falseFlags heap layout dictionary scratch baseRefs slots).dictionary =
      (emitReferences directory.heap (directoryLayout heap layout source dictionary.coordinates.size rows)
        dictionary directory.cursor scratch refs.flatten).dictionary := by
  exact EnumerationFixedEmit.result_dictionary _ _ _ _ _ _ _ _ _

theorem stored (trueFlags falseFlags : Slot ambient → Bool)
    (heap : Array (Word width)) (layout : Layout ambient heap.size) (dictionary : Dictionary ambient)
    (represented : Represented heap layout dictionary) (scratch : Nat)
    (baseRefs : List (List (Reference ambient))) (slots : List (Slot ambient)) :
    let refs := EnumerationFixedProfile.references baseRefs slots trueFlags falseFlags
    let rows := originalRows refs
    let compiled := compileRows dictionary rows
    let clauses := finiteClauses compiled.2.1 (rows_bounds dictionary represented.coherent rows)
    Controller.Horn.SourceDirectory.Stored clauses heap.size (heap.size + 2 * rows.length)
      (result trueFlags falseFlags heap layout dictionary scratch baseRefs slots).heap := by
  dsimp only
  rw [result_heap]
  exact assembled_stored heap layout dictionary represented _ dictionary.coordinates.size _ scratch

set_option maxHeartbeats 4000000 in
theorem execution (program : Program width 4) (trueFlags falseFlags : Slot ambient → Bool)
    (heap : Array (Word width)) (layout : Layout ambient heap.size) (dictionary : Dictionary ambient)
    (represented : Represented heap layout dictionary) (channels sourceEnd : Nat)
    (baseRefs : List (List (Reference ambient))) (slots : List (Slot ambient))
    (sourceBound : sourceEnd ≤ heap.size)
    (baseStored : ∀ reference ∈ baseRefs.flatten, StoredReference heap channels sourceEnd reference)
    (slotStored : ∀ slot ∈ slots, StoredReference heap channels sourceEnd slot.positive ∧
      StoredReference heap channels sourceEnd slot.negative ∧ StoredReference heap channels sourceEnd slot.inactive)
    (maskBounds : ∀ slot ∈ slots, slot.trueMask < sourceEnd ∧ slot.falseMask < sourceEnd)
    (maskCells : ∀ slot ∈ slots, heap[slot.trueMask]? = some (boolWord width (trueFlags slot)) ∧
      heap[slot.falseMask]? = some (boolWord width (falseFlags slot)))
    (beforeTable : sourceEnd ≤ layout.tableBase) (beforeInverse : sourceEnd ≤ layout.inverseBase)
    (base scratch : Nat) (stack output : List (Word width)) (widthPositive : 0 < width)
    (room : heap.size + 2 * (baseRefs.length + slots.length + 1) +
      2 * baseRefs.flatten.length + 2 * slots.length < 2 ^ width)
    (ambientFits : ambient + 1 < 2 ^ width)
    (programFits : base + (code width base baseRefs slots).length < 2 ^ width)
    (block : BlockAt program base (code width base baseRefs slots)) :
    let final := result trueFlags falseFlags heap layout dictionary scratch baseRefs slots
    ∃ ticks peak, Execution program
      (atState heap base (heap.size + 2 * (baseRefs.length + slots.length + 1))
        layout.tableBase dictionary.coordinates.size scratch (word width layout.inverseBase :: stack) output)
      (atState final.heap (base + (code width base baseRefs slots).length) final.input
        layout.tableBase final.dictionary.coordinates.size final.scratch
        (word width layout.inverseBase :: stack) output)
      ticks peak ∧ ticks ≤ 2 + 5 * (baseRefs.length + slots.length + 1) +
        23 * baseRefs.flatten.length + 31 * slots.length ∧
      peak ≤ 8 + heap.size + 2 * (baseRefs.length + slots.length + 1) +
        2 * baseRefs.flatten.length + 2 * slots.length + stack.length + output.length := by
  let rows := originalRows (EnumerationFixedProfile.references baseRefs slots trueFlags falseFlags)
  let source := heap.size + 2 * rows.length
  let directory := ForestZeroDirectory.build heap source dictionary.coordinates.size rows
  let extended := directoryLayout heap layout source dictionary.coordinates.size rows
  let emitterBase := base + (EnumerationDirectoryFrame.code width (EnumerationFixedProfile.template baseRefs slots)).length
  have rowsLength : rows.length = baseRefs.length + slots.length + 1 := by simp [rows, originalRows]
  have rowLiterals : (rows.map List.length).sum = baseRefs.flatten.length + slots.length := by
    have size := originalRows_literals (EnumerationFixedProfile.references baseRefs slots trueFlags falseFlags)
    simpa [rows] using size
  have directoryAt := BlockAt.prefix program base _ _ block
  have emitterAt := BlockAt.suffix program base _ _ block
  have directoryEq : EnumerationDirectoryFrame.code width rows =
      EnumerationDirectoryFrame.code width (EnumerationFixedProfile.template baseRefs slots) := by
    simp only [EnumerationDirectoryFrame.code, rows, EnumerationFixedProfile.directory_code]
  have directoryTrace := EnumerationDirectoryFrame.execution program heap base source layout.tableBase dictionary.coordinates.size
    scratch (word width layout.inverseBase :: stack) output rows (by rw [rowsLength]; omega)
    (by dsimp only [source]; rw [rowsLength, rowLiterals]; omega)
    (by rw [directoryEq]; simp only [code, List.length_append] at programFits; omega)
    (by rw [directoryEq]; exact directoryAt)
  have baseRetained : ∀ reference ∈ baseRefs.flatten, StoredReference directory.heap channels sourceEnd reference := by
    intro reference member
    have old := baseStored reference member
    refine ⟨?_, old.slotBound, old.headerBound, ?_, ?_, old.coordinateEq⟩
    · dsimp only [directory]; rw [ForestZeroDirectory.build_size]; omega
    · exact (ForestZeroDirectory.build_prefix heap source dictionary.coordinates.size rows reference.slot
        (lt_of_lt_of_le old.slotBound old.sourceBound)).trans old.slotWord
    · exact (ForestZeroDirectory.build_prefix heap source dictionary.coordinates.size rows 0
        (lt_of_lt_of_le old.headerBound old.sourceBound)).trans old.channelWord
  have slotsRetained : ∀ slot ∈ slots, StoredReference directory.heap channels sourceEnd slot.positive ∧
      StoredReference directory.heap channels sourceEnd slot.negative ∧ StoredReference directory.heap channels sourceEnd slot.inactive := by
    intro slot member
    have keep (reference : Reference ambient) (old : StoredReference heap channels sourceEnd reference) :
        StoredReference directory.heap channels sourceEnd reference := by
      refine ⟨?_, old.slotBound, old.headerBound, ?_, ?_, old.coordinateEq⟩
      · dsimp only [directory]; rw [ForestZeroDirectory.build_size]; omega
      · exact (ForestZeroDirectory.build_prefix heap source dictionary.coordinates.size rows reference.slot
          (lt_of_lt_of_le old.slotBound old.sourceBound)).trans old.slotWord
      · exact (ForestZeroDirectory.build_prefix heap source dictionary.coordinates.size rows 0
          (lt_of_lt_of_le old.headerBound old.sourceBound)).trans old.channelWord
    obtain ⟨pos, neg, inactive⟩ := slotStored slot member
    exact ⟨keep _ pos, keep _ neg, keep _ inactive⟩
  have cells : ∀ slot ∈ slots, directory.heap[slot.trueMask]? = some (boolWord width (trueFlags slot)) ∧
      directory.heap[slot.falseMask]? = some (boolWord width (falseFlags slot)) := by
    intro slot member
    obtain ⟨boundsT, boundsF⟩ := maskBounds slot member
    obtain ⟨cellsT, cellsF⟩ := maskCells slot member
    exact ⟨(ForestZeroDirectory.build_prefix heap source dictionary.coordinates.size rows slot.trueMask (by omega)).trans cellsT,
      (ForestZeroDirectory.build_prefix heap source dictionary.coordinates.size rows slot.falseMask (by omega)).trans cellsF⟩
  obtain ⟨emitTicks, emitPeak, emission, emitTime, emitSpace⟩ := EnumerationFixedEmit.execution program trueFlags falseFlags
    directory.heap extended dictionary (directory_represented heap layout dictionary represented source dictionary.coordinates.size rows)
    channels sourceEnd baseRefs slots (by dsimp only [directory]; rw [ForestZeroDirectory.build_size]; omega)
    baseRetained slotsRetained maskBounds cells beforeTable beforeInverse emitterBase directory.cursor scratch stack output
    widthPositive (by dsimp only [directory]; rw [ForestZeroDirectory.build_size, rowsLength]; exact room) ambientFits
    (by simp only [code, List.length_append] at programFits; dsimp only [emitterBase]; omega) emitterAt
  have prefix' : Execution program (atState heap base source layout.tableBase dictionary.coordinates.size scratch
      (word width layout.inverseBase :: stack) output)
      (atState directory.heap emitterBase directory.cursor layout.tableBase dictionary.coordinates.size scratch
        (word width layout.inverseBase :: stack) output)
      (2 + 5 * rows.length) (6 + heap.size + 2 * rows.length + (word width layout.inverseBase :: stack).length + output.length) := by
    simpa only [directoryEq, directory, emitterBase] using directoryTrace
  refine ⟨2 + 5 * rows.length + emitTicks,
    max (6 + heap.size + 2 * rows.length + (word width layout.inverseBase :: stack).length + output.length) emitPeak,
    ?_, ?_, ?_⟩
  · convert prefix'.append emission using 1 <;>
      simp only [result, rows, source, directory, extended, emitterBase, code, List.length_append,
        originalRows, List.length_map, EnumerationFixedProfile.references_length, directoryLayout, Nat.add_assoc]
  · rw [rowsLength]
    omega
  · dsimp only [directory] at emitSpace
    rw [ForestZeroDirectory.build_size, rowsLength] at emitSpace
    simp only [rowsLength, List.length_cons, max_le_iff]
    constructor <;> omega

end Controller.Cost.EnumerationFixedAssembly
