module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.EnumerationFixedDecision
public import Controller.Cost.EnumerationResident
public import Controller.Cost.SharedZeroSource

public import Mathlib.Tactic.FinCases

@[expose] public section

/-! A resident decision query whose constructor and solver addresses are fixed
across every runtime unit-slot selection. Touching every coordinate first fixes
the dictionary and optional-row allocation; the solver code is reused verbatim. -/
namespace Controller.Cost.EnumerationFixedResident
open Controller.CNF Controller.Cost.GateProgram Controller.Cost.ForestZeroEmit
open Controller.Cost.ForestZeroCompile Controller.Cost.ForestZeroDictionary
open Controller.Cost.ForestZeroAdmissibleCaller Controller.Cost.EnumerationSlotBatch

abbrev selected (baseRefs : List (List (Reference ambient))) (slots : List (Slot ambient))
    (yes no : Slot ambient → Bool) := EnumerationFixedConstructor.references baseRefs slots yes no

theorem selected_literals (baseRefs : List (List (Reference ambient))) (slots : List (Slot ambient)) :
    (selected baseRefs slots yes no).flatten.length = baseRefs.flatten.length + slots.length := by
  simp only [selected, EnumerationFixedConstructor.references, List.flatten_append, List.length_append,
    EnumerationFixedProfile.selectedRefs_flatten, List.length_map]

/-- No consistency premise on the masks is needed to fix the dictionary. -/
theorem dictionary_fixed (baseRefs : List (List (Reference ambient))) (slots : List (Slot ambient))
    (touched : ∃ tail, ForestZeroAssembly.originalRows baseRefs = SharedZeroTemplate.touchRows ambient ++ tail)
    (yes no : Slot ambient → Bool) (heap : Array (Word width)) (layout : Layout ambient heap.size) :
    constructorDictionary heap layout (empty ambient) (selected baseRefs slots yes no) =
      (compileRows (empty ambient) (SharedZeroTemplate.touchRows ambient)).1 := by
  obtain ⟨tail, rows⟩ := touched
  unfold constructorDictionary reservedReferences selected EnumerationFixedConstructor.references
  simp only [ForestZeroAssembly.originalRows, List.map_append, List.map_cons, List.map_nil]
  change (compileRows (empty ambient)
    (ForestZeroAssembly.originalRows baseRefs ++
      ForestZeroAssembly.originalRows (EnumerationFixedProfile.selectedRefs slots yes no) ++ [[]])).1 = _
  rw [rows]
  simp only [List.append_assoc]
  exact SharedZeroDictionary.dictionary_fixed _

theorem dictionary_size (baseRefs : List (List (Reference ambient))) (slots : List (Slot ambient))
    (touched : ∃ tail, ForestZeroAssembly.originalRows baseRefs = SharedZeroTemplate.touchRows ambient ++ tail)
    (yes no : Slot ambient → Bool) (heap : Array (Word width)) (layout : Layout ambient heap.size) :
    (constructorDictionary heap layout (empty ambient) (selected baseRefs slots yes no)).coordinates.size = ambient := by
  rw [dictionary_fixed baseRefs slots touched yes no heap layout]
  simpa only [List.append_nil] using SharedZeroDictionary.dictionary_size ([] : List (Clause (Fin ambient)))

def heapSize (keep channels : Nat) (baseRefs : List (List (Reference ambient))) (slots : List (Slot ambient)) : Nat :=
  keep + 5 + 2 * (baseRefs.length + slots.length + 1) + 2 * (baseRefs.flatten.length + slots.length) +
    (if (ForestZeroNonempty.search
      (compileRows (empty ambient) (SharedZeroTemplate.touchRows ambient)).1
      (ambient + 1) channels 0).reason = .covered then 2 * channels else 0)

theorem heap_size (baseRefs : List (List (Reference ambient))) (slots : List (Slot ambient))
    (touched : ∃ tail, ForestZeroAssembly.originalRows baseRefs = SharedZeroTemplate.touchRows ambient ++ tail)
    (yes no : Slot ambient → Bool) (heap : Array (Word width)) (layout : Layout ambient heap.size) (channels : Nat) :
    (constructorHeap heap layout (empty ambient) (selected baseRefs slots yes no) channels).size =
      heapSize heap.size channels baseRefs slots := by
  rw [constructorHeap_size, EnumerationFixedConstructor.references_length, selected_literals,
    dictionary_fixed baseRefs slots touched yes no heap layout]
  have size := SharedZeroDictionary.dictionary_size ([] : List (Clause (Fin ambient)))
  simp only [List.append_nil] at size
  rw [size]
  rfl

theorem heap_size_bound (baseRefs : List (List (Reference ambient))) (slots : List (Slot ambient)) :
    heapSize keep channels baseRefs slots ≤
      keep + 5 + 2 * (baseRefs.length + slots.length + 1) +
        2 * baseRefs.flatten.length + 2 * slots.length + 2 * channels := by
  unfold heapSize
  split_ifs <;> omega

/-- A single flag-independent capacity bounds allocation, records and incidences. -/
theorem backend_heap_capacity (baseRefs : List (List (Reference ambient))) (slots : List (Slot ambient))
    (touched : ∃ tail, ForestZeroAssembly.originalRows baseRefs = SharedZeroTemplate.touchRows ambient ++ tail)
    (yes no : Slot ambient → Bool) (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (channels : Nat) (within : channels ≤ ambient) (recordStart : Nat)
    (fits : heapSize heap.size channels baseRefs slots + 5 * ambient + 4 +
      3 * (baseRefs.length + slots.length + 1) +
      3 * (baseRefs.flatten.length + slots.length + ambient) < 2 ^ width) :
    let dictionary := constructorDictionary heap layout (empty ambient) (selected baseRefs slots yes no)
    let rows := constructorClauses heap layout (empty ambient) (empty_coherent ambient)
      (selected baseRefs slots yes no) channels within
    (constructorHeap heap layout (empty ambient) (selected baseRefs slots yes no) channels).size +
      5 * dictionary.coordinates.size + 4 + 3 * rows.length + (rows.map List.length).sum +
      2 * (Controller.Horn.IndexScan.occurrences rows recordStart).length < 2 ^ width := by
  intro dictionary rows
  have dictionarySize := dictionary_size baseRefs slots touched yes no heap layout
  have heapSizeEq := heap_size baseRefs slots touched yes no heap layout channels
  have rowCount := constructorClauses_length heap layout (empty ambient) (empty_coherent ambient)
    (selected baseRefs slots yes no) channels within
  have rowBound : rows.length ≤ baseRefs.length + slots.length + 1 := by
    dsimp only [rows]
    rw [rowCount, EnumerationFixedConstructor.references_length]
    split_ifs <;> omega
  have literalBound := constructorClauses_profile_bound heap layout (empty ambient) (empty_coherent ambient)
    (selected baseRefs slots yes no) channels within
  rw [selected_literals] at literalBound
  have incidenceBound := Controller.Horn.IndexScanCold.occurrences_length_le rows recordStart
  change (rows.map List.length).sum ≤ baseRefs.flatten.length + slots.length + dictionary.coordinates.size at literalBound
  change dictionary.coordinates.size = ambient at dictionarySize
  omega

def solverEntry (width entry keep : Nat) (baseRefs : List (List (Reference ambient))) (slots : List (Slot ambient)) : Nat :=
  entry + 15 + (EnumerationFixedQuery.code width (entry + 15) keep baseRefs slots).length + 81

def sourceCode (width entry keep : Nat) (baseRefs : List (List (Reference ambient))) (slots : List (Slot ambient)) :
    List (Instruction width 8) :=
  (reuseEntryCode width).toList ++ (keepCode width).map RegisterWiden.widenInstruction ++
  [.constant 0 (word width (keep + 5 + 2 * (baseRefs.length + slots.length + 1)))] ++
  (EnumerationFixedConstructor.code width (entry + 15) keep (solverEntry width entry keep baseRefs slots)
    baseRefs slots).map RegisterWiden.widenInstruction

theorem source_length (baseRefs : List (List (Reference ambient))) (slots : List (Slot ambient)) :
    entry + (sourceCode width entry keep baseRefs slots).length = solverEntry width entry keep baseRefs slots := by
  simp only [sourceCode, List.length_append, List.length_map, reuseEntryCode,
    keepCode_length, List.length_cons, List.length_nil, EnumerationFixedConstructor.code,
    ForestZeroAdmissibleCaller.code_length, solverEntry]
  omega

def code (width entry keep channels : Nat) (baseRefs : List (List (Reference ambient))) (slots : List (Slot ambient)) :
    List (Instruction width 8) :=
  sourceCode width entry keep baseRefs slots ++
  EnumerationResident.solverCode width (solverEntry width entry keep baseRefs slots) ambient
    (heapSize keep channels baseRefs slots) (keep + 3) (keep + 4) (keep + 1) (keep + 2) keep

theorem code_end (baseRefs : List (List (Reference ambient))) (slots : List (Slot ambient)) :
    entry + (code width entry keep channels baseRefs slots).length =
      solverEntry width entry keep baseRefs slots + 430 := by
  have source := source_length (width := width) (entry := entry) (keep := keep) baseRefs slots
  simp only [code, List.length_append, EnumerationResident.solverCode_length]
  omega

theorem code_bound (baseRefs : List (List (Reference ambient))) (slots : List (Slot ambient)) :
    (code width entry keep channels baseRefs slots).length ≤
      542 + 5 * (baseRefs.length + slots.length + 1) + 28 * baseRefs.flatten.length + 90 * slots.length := by
  have query := EnumerationFixedQuery.code_bound (width := width) (base := entry + 15) (keep := keep) baseRefs slots
  have finish := code_end (width := width) (entry := entry) (keep := keep) (channels := channels) baseRefs slots
  unfold solverEntry at finish
  omega

/-- All solver instruction addresses fit from one resident end-capacity check. -/
theorem solver_capacity (baseRefs : List (List (Reference ambient))) (slots : List (Slot ambient))
    (fits : entry + (code width entry keep channels baseRefs slots).length < 2 ^ width) :
    solverEntry width entry keep baseRefs slots + 430 < 2 ^ width := by
  rw [code_end] at fits
  exact fits

theorem backend_address_capacity (baseRefs : List (List (Reference ambient))) (slots : List (Slot ambient))
    (fits : entry + (code width entry keep channels baseRefs slots).length < 2 ^ width)
    (offset : Nat) (below : offset ≤ 430) :
    solverEntry width entry keep baseRefs slots + offset < 2 ^ width := by
  have bound := solver_capacity baseRefs slots fits
  omega

/-- The resident solver uses the exact dictionary and scratch base of every selection. -/
theorem solver_matches (baseRefs : List (List (Reference ambient))) (slots : List (Slot ambient))
    (touched : ∃ tail, ForestZeroAssembly.originalRows baseRefs = SharedZeroTemplate.touchRows ambient ++ tail)
    (yes no : Slot ambient → Bool) (heap : Array (Word width)) (layout : Layout ambient heap.size) :
    EnumerationResident.solverCode width (solverEntry width entry heap.size baseRefs slots)
      (constructorDictionary heap layout (empty ambient) (selected baseRefs slots yes no)).coordinates.size
      (constructorHeap heap layout (empty ambient) (selected baseRefs slots yes no) channels).size
      (heap.size + 3) (heap.size + 4) (heap.size + 1) (heap.size + 2) heap.size =
    EnumerationResident.solverCode width (solverEntry width entry heap.size baseRefs slots)
      ambient (heapSize heap.size channels baseRefs slots)
      (heap.size + 3) (heap.size + 4) (heap.size + 1) (heap.size + 2) heap.size := by
  rw [dictionary_size baseRefs slots touched yes no heap layout,
    heap_size baseRefs slots touched yes no heap layout channels]

private theorem left_at (program : Program width 8) (entry : Nat) (first rest : List (Instruction width 8))
    (present : SharedRootRead.BlockAt program entry (first ++ rest)) : SharedRootRead.BlockAt program entry first := by
  intro offset below
  have found := present offset (by simp only [List.length_append]; omega)
  rwa [List.getElem?_append_left below] at found

private theorem right_at (program : Program width 8) (entry : Nat) (first rest : List (Instruction width 8))
    (present : SharedRootRead.BlockAt program entry (first ++ rest)) :
    SharedRootRead.BlockAt program (entry + first.length) rest := by
  intro offset below
  have found := present (first.length + offset) (by simp only [List.length_append]; omega)
  rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left] at found
  simpa only [Nat.add_assoc] using found

structure SourcePhysical (program : Program width 8) (entry keep : Nat)
    (baseRefs : List (List (Reference ambient))) (slots : List (Slot ambient)) : Prop where
  reuse : ∀ phase : Fin 3, program[entry + phase.val]? = (reuseEntryCode width)[phase.val]?
  saved : ForestZeroCallerWiden.WidenedBlockAt program (entry + 3) (keepCode width)
  cursor : program[entry + 14]? = some (.constant 0
    (word width (keep + 5 + 2 * (baseRefs.length + slots.length + 1))))
  constructor : ForestZeroCallerWiden.WidenedBlockAt program (entry + 15)
    (EnumerationFixedConstructor.code width (entry + 15) keep
      (solverEntry width entry keep baseRefs slots) baseRefs slots)

theorem source_physical_at (program : Program width 8) (entry keep : Nat)
    (baseRefs : List (List (Reference ambient))) (slots : List (Slot ambient))
    (present : SharedRootRead.BlockAt program entry (sourceCode width entry keep baseRefs slots)) :
    SourcePhysical program entry keep baseRefs slots := by
  unfold sourceCode at present
  constructor
  · intro phase
    have found := present phase.val (by
      simp only [List.length_append, List.length_map,
        reuseEntryCode, List.length_cons, List.length_nil, keepCode_length]
      have := phase.isLt
      omega)
    fin_cases phase
    all_goals simpa [reuseEntryCode, keepCode] using found
  · intro offset bound
    have small : offset < 11 := by simpa using bound
    have found := present (3 + offset) (by
      simp only [List.length_append, List.length_map,
        reuseEntryCode, List.length_cons, List.length_nil, keepCode_length]
      omega)
    interval_cases offset
    all_goals simpa [reuseEntryCode, keepCode, RegisterWiden.widenInstruction,
      Nat.add_assoc] using found
  · have found := present 14 (by
      simp only [List.length_append, List.length_map,
        reuseEntryCode, List.length_cons, List.length_nil, keepCode_length]
      omega)
    simpa [reuseEntryCode, keepCode] using found
  · intro offset bound
    have prefixLength : ((reuseEntryCode width).toList ++
        (keepCode width).map RegisterWiden.widenInstruction ++
        [(Instruction.constant 0 (word width (keep + 5 + 2 * ((baseRefs.length + slots.length) + 1))) : Instruction width 8)]).length = 15 := by
      simp [reuseEntryCode]
    have prepared : SharedRootRead.BlockAt program entry
        (((reuseEntryCode width).toList ++ (keepCode width).map RegisterWiden.widenInstruction ++
          [.constant 0 (word width (keep + 5 + 2 * ((baseRefs.length + slots.length) + 1)))]) ++
          (EnumerationFixedConstructor.code width (entry + 15) keep
            (solverEntry width entry keep baseRefs slots) baseRefs slots).map RegisterWiden.widenInstruction ++ []) := by
      simpa only [List.append_assoc, List.append_nil] using present
    have block := SharedNativeSuccessCode.segment program entry _ _ _ prepared
    rw [prefixLength] at block
    simpa only [List.getElem?_map] using block offset (by simpa using bound)

structure Physical (program : Program width 8) (entry keep channels : Nat)
    (baseRefs : List (List (Reference ambient))) (slots : List (Slot ambient)) : Prop where
  source : SourcePhysical program entry keep baseRefs slots
  prepared : SharedSolverPrefix.Physical program (solverEntry width entry keep baseRefs slots)
    ambient (heapSize keep channels baseRefs slots) keep (solverEntry width entry keep baseRefs slots + 261)
  prefixBlock : SharedRootRead.BlockAt program (solverEntry width entry keep baseRefs slots)
    (SharedSolverPrefix.code width (solverEntry width entry keep baseRefs slots) ambient
      (heapSize keep channels baseRefs slots) (keep + 3) (keep + 4) (keep + 1) (keep + 2) keep
      (solverEntry width entry keep baseRefs slots + 261)).toList
  worklist : EnumerationResident.WorklistPhysical program (solverEntry width entry keep baseRefs slots + 261)
    ambient (heapSize keep channels baseRefs slots) (solverEntry width entry keep baseRefs slots + 395)
  cleanup : SharedQueryCleanupCode.Physical program (solverEntry width entry keep baseRefs slots + 395)

/-- One actual resident block supplies every backend fetch obligation. -/
theorem physical_at (program : Program width 8) (entry keep channels : Nat)
    (baseRefs : List (List (Reference ambient))) (slots : List (Slot ambient))
    (present : SharedRootRead.BlockAt program entry (code width entry keep channels baseRefs slots)) :
    Physical program entry keep channels baseRefs slots := by
  unfold code at present
  have sourceAt := left_at program entry _ _ present
  have solverAt := right_at program entry _ _ present
  rw [source_length] at solverAt
  unfold EnumerationResident.solverCode at solverAt
  have prefixAt := left_at program _ _ _ (left_at program _ _ _ solverAt)
  have worklistAt := right_at program _ _ _ (left_at program _ _ _ solverAt)
  have cleanupAt := right_at program _ _ _ solverAt
  simp only [Array.length_toList, SharedSolverPrefix.code_size] at worklistAt
  simp only [List.length_append, Array.length_toList, SharedSolverPrefix.code_size,
    EnumerationResident.worklistCode_size, Nat.reduceAdd] at cleanupAt
  exact ⟨source_physical_at program entry keep baseRefs slots sourceAt, SharedSolverPrefix.physical_at program _ ambient _ _ _ _ _ keep _ prefixAt,
    prefixAt, EnumerationResident.worklist_physical_at program _ ambient _ _ worklistAt,
    SharedQueryCleanupCode.physical_at program _ cleanupAt⟩

/-- The existing graph source supplies the complete coordinate-touch prefix. -/
theorem graph_base_touches (graph : Controller.Decoder.DAG n) (b : Nat) (target : Fin n)
    (root : Fin graph.nodeCount) :
    ∃ tail, ForestZeroAssembly.originalRows
      (SharedZeroSource.references graph b target ∅ ∅ sourceBase rootSlot root) =
      SharedZeroTemplate.touchRows (n + graph.nodeCount) ++ tail := by
  refine ⟨((graph.forwardClauses ++ graph.channelClauses b target ∅ ∅).map
    (fun clause => clause.map (fun literal => (graph.zeroIndex literal.1, literal.2)))) ++
    [[((⟨n + root.val, by omega⟩ : Fin (n + graph.nodeCount)), false)]], ?_⟩
  simp [ForestZeroAssembly.originalRows, SharedZeroSource.references, SharedZeroSource.fixedRows,
    SharedCoordinateTable.rows, SharedCoordinateTable.reference, SharedZeroCode.rootReference,
    List.map_map, Function.comp_def, List.append_assoc]

end Controller.Cost.EnumerationFixedResident
