module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.EnumerationFixedResident

@[expose] public section

/-! Fetched execution of the fixed resident query. Every runtime slot choice
uses the same instruction array; decisions return with the retained source,
empty dictionary, caller stack and output ready for the next query. -/
namespace Controller.Cost.EnumerationFixedExecution
open Controller.Cost.ForestZeroTouch Controller.Cost.GateProgram Controller.Cost.ForestZeroCompile
open Controller.Cost.ForestZeroDictionary Controller.Cost.ForestZeroAdmissibleCaller
open Controller.Cost.ForestZeroEmit Controller.CNF Controller.Cost.EnumerationQuery
open Controller.Cost.EnumerationSlotBatch

structure Conditions {width ambient : Nat} (channels : Nat) (program : Program width 8) (initial : State width 8)
    (sharedLayout : Layout ambient initial.heap.size)
    (references baseRefs : List (List (Reference ambient))) (slots : List (Slot ambient))
    (yes no : Slot ambient → Bool) (sourceEnd nodes sourceEntry : Nat)
    (rest : List (Word width)) (within : channels ≤ ambient) : Prop where
  selectedRefs : references = EnumerationFixedResident.selected baseRefs slots yes no
  touched : ∃ tail, ForestZeroAssembly.originalRows baseRefs = SharedZeroTemplate.touchRows ambient ++ tail
  baseStored : ∀ reference ∈ baseRefs.flatten, StoredReference initial.heap channels sourceEnd reference
  slotStored : ∀ slot ∈ slots, StoredReference initial.heap channels sourceEnd slot.positive ∧
    StoredReference initial.heap channels sourceEnd slot.negative ∧ StoredReference initial.heap channels sourceEnd slot.inactive
  maskBounds : ∀ slot ∈ slots, slot.trueMask < sourceEnd ∧ slot.falseMask < sourceEnd
  maskCells : ∀ slot ∈ slots, initial.heap[slot.trueMask]? = some (boolWord width (yes slot)) ∧
    initial.heap[slot.falseMask]? = some (boolWord width (no slot))
  sourceBeforeTable : sourceEnd ≤ sharedLayout.tableBase
  sourceBeforeInverse : sourceEnd ≤ sharedLayout.inverseBase
  sourceBound : sourceEnd ≤ initial.heap.size
  sourcePositive : 0 < sourceEnd
  sourceChannel : initial.heap[0]? = some (word width channels)
  sourceNodes : initial.heap[1]? = some (word width nodes)
  ambientEq : ambient = channels + nodes
  adjacent : sharedLayout.inverseBase = sharedLayout.tableBase + ambient
  tablePositive : 0 < sharedLayout.tableBase
  sourceHeaderRoom : 1 < sourceEnd
  sourceDual : Controller.Horn.DualHorn
    (ofClauses (ForestZeroAssembly.originalRows (reservedReferences references)))
  sourceEndpoint : initial.heap.size = sharedLayout.inverseBase + ambient
  constructorRoom : initial.heap.size + 5 + 2 * (references.length + 1) +
    2 * references.flatten.length + 2 * ambient < 2 ^ width
  room : (constructorState initial.heap sharedLayout (ForestZeroCompile.empty ambient) references channels
      (EnumerationFixedResident.solverEntry width sourceEntry initial.heap.size baseRefs slots)
      (word width initial.heap.size :: rest) initial.output initial.reg).heap.size +
    5 * (constructorDictionary initial.heap sharedLayout (ForestZeroCompile.empty ambient) references).coordinates.size + 4 +
    3 * (constructorFormula initial.heap sharedLayout (ForestZeroCompile.empty ambient)
      (ForestZeroCompile.empty_coherent ambient) references channels within).clauses.toList.length +
    ((constructorFormula initial.heap sharedLayout (ForestZeroCompile.empty ambient)
      (ForestZeroCompile.empty_coherent ambient) references channels within).clauses.toList.map List.length).sum +
    2 * (Controller.Horn.IndexScan.occurrences (constructorFormula initial.heap sharedLayout
      (ForestZeroCompile.empty ambient) (ForestZeroCompile.empty_coherent ambient) references channels within).clauses.toList
      ((constructorHeap initial.heap sharedLayout (ForestZeroCompile.empty ambient) references channels).size +
        5 * (constructorDictionary initial.heap sharedLayout (ForestZeroCompile.empty ambient) references).coordinates.size + 4)).length
    < 2 ^ width
  residentCapacity : EnumerationFixedResident.solverEntry width sourceEntry initial.heap.size baseRefs slots + 430 < 2 ^ width

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem execution {width ambient : Nat} (channels : Nat)
    (program : Program width 8) (initial : State width 8) (sourceHeap : Array (Word width))
    (sharedLayout : Layout ambient initial.heap.size)
    (references baseRefs : List (List (Reference ambient))) (slots : List (Slot ambient))
    (yes no : Slot ambient → Bool) (sourceEnd nodes sourceEntry : Nat)
    (rest : List (Word width)) (within : channels ≤ ambient)
    (conditions : Conditions channels program initial sharedLayout references baseRefs slots yes no sourceEnd nodes sourceEntry rest within)
    (present : SharedRootRead.BlockAt program sourceEntry
      (EnumerationFixedResident.code width sourceEntry initial.heap.size channels baseRefs slots))
    (initialReady : QueryReady (ambient := ambient) sourceHeap sharedLayout.tableBase sharedLayout.inverseBase
      sourceEntry rest initial) :
    ∃ answer : Bool, ∃ final ticks peak,
      Execution program initial final ticks peak ∧
      final.halted = false ∧
      final.reg 4 = word width (if answer then 1 else 0) ∧
      ticks ≤ 150 * references.length + 387 * references.flatten.length + 8 * slots.length + 441 ∧
      peak ≤ initial.liveWords + 5 * references.length + 15 * references.flatten.length + channels + 20 ∧
      final.output = initial.output ∧
      (answer = true ↔ Controller.CNF.Satisfiable
        (constructorFormula initial.heap sharedLayout (ForestZeroCompile.empty ambient)
          (ForestZeroCompile.empty_coherent ambient) references channels within)) ∧
      QueryReady (ambient := ambient) sourceHeap sharedLayout.tableBase sharedLayout.inverseBase
        (EnumerationFixedResident.solverEntry width sourceEntry initial.heap.size baseRefs slots + 430) rest final := by
  have physical := EnumerationFixedResident.physical_at program sourceEntry initial.heap.size channels baseRefs slots present
  have dictionarySize : (constructorDictionary initial.heap sharedLayout (empty ambient) references).coordinates.size = ambient := by
    rw [conditions.selectedRefs]
    exact EnumerationFixedResident.dictionary_size baseRefs slots conditions.touched yes no initial.heap sharedLayout
  have heapSizeEq : (constructorHeap initial.heap sharedLayout (empty ambient) references channels).size =
      EnumerationFixedResident.heapSize initial.heap.size channels baseRefs slots := by
    rw [conditions.selectedRefs]
    exact EnumerationFixedResident.heap_size baseRefs slots conditions.touched yes no initial.heap sharedLayout channels
  have refsLength : references.length = baseRefs.length + slots.length := by
    rw [conditions.selectedRefs, EnumerationFixedConstructor.references_length]
  have refsLiterals : references.flatten.length = baseRefs.flatten.length + slots.length := by
    rw [conditions.selectedRefs]
    exact EnumerationFixedResident.selected_literals baseRefs slots
  have represented : Represented initial.heap sharedLayout (ForestZeroCompile.empty ambient) :=
    empty_dictionary_from_zero_table initial.heap sharedLayout initialReady.zeroTable
  have initialEq := initialReady.entry_state
  have sourceBefore : sourceEntry + 15 ≤ EnumerationFixedResident.solverEntry width sourceEntry initial.heap.size baseRefs slots := by
    unfold EnumerationFixedResident.solverEntry; omega
  have constructorEnd : sourceEntry + 15 +
      (EnumerationFixedConstructor.code width (sourceEntry + 15) initial.heap.size
        (EnumerationFixedResident.solverEntry width sourceEntry initial.heap.size baseRefs slots) baseRefs slots).length =
      EnumerationFixedResident.solverEntry width sourceEntry initial.heap.size baseRefs slots := by
    simp only [EnumerationFixedConstructor.code, List.length_append, ForestZeroAdmissibleCaller.code_length,
      EnumerationFixedResident.solverEntry]
    omega
  have constructorRoom := conditions.constructorRoom
  have residentCapacity := conditions.residentCapacity
  have ambientFits : ambient + 1 < 2 ^ width := by omega
  have dictionaryCoherent := (ForestZeroCompile.rows_dictionary (ForestZeroCompile.empty ambient)
    (ForestZeroCompile.empty_coherent ambient)
    (ForestZeroAssembly.originalRows (reservedReferences references))).1
  have localBound := ForestZeroDictionary.count_le_ambient
    (constructorDictionary initial.heap sharedLayout (ForestZeroCompile.empty ambient) references)
    dictionaryCoherent
  have actualRoom := conditions.room
  simp only [constructorState, RegisterWiden.widenState, atState] at actualRoom
  have stateHeap : (constructorState initial.heap sharedLayout (ForestZeroCompile.empty ambient) references channels
      (EnumerationFixedResident.solverEntry width sourceEntry initial.heap.size baseRefs slots)
      (word width initial.heap.size :: rest) initial.output initial.reg).heap.size =
      (constructorHeap initial.heap sharedLayout (ForestZeroCompile.empty ambient) references channels).size := rfl
  obtain ⟨answer, final, ticks, peak, trace, timeBound, spaceBound, heapSize, finalStack, finalOutput,
      finalPC, finalRunning, finalFrame, zeroTable, decision, zeroRegister, tableRegister, inverseRegister,
      meaning, finalLive, sourceFrame, reusable⟩ :=
    EnumerationFixedDecision.execution initial.heap sharedLayout (ForestZeroCompile.empty ambient) represented references
      baseRefs slots yes no conditions.selectedRefs sourceEnd nodes conditions.baseStored conditions.slotStored
      conditions.maskBounds conditions.maskCells conditions.sourceBeforeTable conditions.sourceBeforeInverse
      conditions.sourceBound conditions.sourcePositive conditions.sourceChannel conditions.sourceNodes
      conditions.ambientEq conditions.adjacent conditions.tablePositive conditions.sourceHeaderRoom
      conditions.sourceDual program sourceEntry (sourceEntry + 15)
      (EnumerationFixedResident.solverEntry width sourceEntry initial.heap.size baseRefs slots) rfl rfl
      conditions.sourceEndpoint (initial.reg 3).val (by omega)
      physical.source.reuse physical.source.saved (by simpa only [refsLength] using physical.source.cursor) rest initial.output initial.reg
      conditions.constructorRoom ambientFits (by omega) physical.source.constructor
      (EnumerationFixedResident.solverEntry width sourceEntry initial.heap.size baseRefs slots + 261)
      (EnumerationFixedResident.solverEntry width sourceEntry initial.heap.size baseRefs slots + 308)
      (EnumerationFixedResident.solverEntry width sourceEntry initial.heap.size baseRefs slots + 382)
      (by simpa only [Nat.add_assoc, Nat.reduceAdd, constructorState, RegisterWiden.widenState, atState, dictionarySize, heapSizeEq] using physical.prepared.count)
      (by simpa only [Nat.add_assoc, Nat.reduceAdd, constructorState, RegisterWiden.widenState, atState, dictionarySize, heapSizeEq] using physical.prepared.allocate)
      (by simpa only [Nat.add_assoc, Nat.reduceAdd, constructorState, RegisterWiden.widenState, atState, dictionarySize, heapSizeEq] using physical.prepared.headers)
      (by simpa only [Nat.add_assoc, Nat.reduceAdd, constructorState, RegisterWiden.widenState, atState, dictionarySize, heapSizeEq] using physical.prepared.endpoint)
      (by simpa only [Nat.add_assoc, Nat.reduceAdd, constructorState, RegisterWiden.widenState, atState, dictionarySize, heapSizeEq] using physical.prepared.saved)
      (SharedSolverPrefix.normalizer_at program _ _
        (constructorFormula initial.heap sharedLayout (ForestZeroCompile.empty ambient)
          (ForestZeroCompile.empty_coherent ambient) references channels within).clauses.toList
        (constructorFormulaBackend initial.heap sharedLayout (ForestZeroCompile.empty ambient)
          (ForestZeroCompile.empty_coherent ambient) references channels within)
        (by simpa only [dictionarySize, heapSizeEq, constructorFormulaBackend, constructorBackend, backendLayout] using physical.prefixBlock))
      (by simpa only [Nat.add_assoc, Nat.reduceAdd, constructorState, RegisterWiden.widenState, atState, dictionarySize, heapSizeEq] using physical.prepared.indexSave)
      (by simpa only [Nat.add_assoc, Nat.reduceAdd, constructorState, RegisterWiden.widenState, atState, dictionarySize, heapSizeEq] using physical.prepared.index)
      (by simpa only [Nat.add_assoc, Nat.reduceAdd, constructorState, RegisterWiden.widenState, atState, dictionarySize, heapSizeEq] using physical.prepared.indexRestore)
      (by simpa only [Nat.add_assoc, Nat.reduceAdd, constructorState, RegisterWiden.widenState, atState, dictionarySize, heapSizeEq] using physical.prepared.capture)
      (by omega)
      (by simpa only [Nat.add_assoc, Nat.reduceAdd, constructorState, RegisterWiden.widenState, atState, dictionarySize, heapSizeEq] using physical.prepared.seed)
      (by simpa only [Nat.add_assoc, Nat.reduceAdd, constructorState, RegisterWiden.widenState, atState, dictionarySize, heapSizeEq] using physical.worklist.seed)
      conditions.room (by omega)
      (EnumerationFixedResident.solverEntry width sourceEntry initial.heap.size baseRefs slots + 312)
      (by simpa only [Nat.add_assoc, Nat.reduceAdd, constructorState, RegisterWiden.widenState, atState, dictionarySize, heapSizeEq] using physical.worklist.head) (by omega)
      (EnumerationFixedResident.solverEntry width sourceEntry initial.heap.size baseRefs slots + 369)
      (EnumerationFixedResident.solverEntry width sourceEntry initial.heap.size baseRefs slots + 331)
      (EnumerationFixedResident.solverEntry width sourceEntry initial.heap.size baseRefs slots + 326)
      (EnumerationFixedResident.solverEntry width sourceEntry initial.heap.size baseRefs slots + 343)
      (EnumerationFixedResident.solverEntry width sourceEntry initial.heap.size baseRefs slots + 326)
      (by simpa only [Nat.add_assoc, Nat.reduceAdd, constructorState, RegisterWiden.widenState, atState, dictionarySize, heapSizeEq] using physical.worklist.fetch)
      (by simpa only [Nat.add_assoc, Nat.reduceAdd, constructorState, RegisterWiden.widenState, atState, dictionarySize, heapSizeEq] using physical.worklist.advance)
      (by simpa only [Nat.add_assoc, Nat.reduceAdd, constructorState, RegisterWiden.widenState, atState, dictionarySize, heapSizeEq] using physical.worklist.bucket)
      (by simpa only [Nat.add_assoc, Nat.reduceAdd, constructorState, RegisterWiden.widenState, atState, dictionarySize, heapSizeEq] using physical.worklist.ready)
      (by omega) (by omega) (by omega) (by omega)
      (EnumerationFixedResident.solverEntry width sourceEntry initial.heap.size baseRefs slots + 395)
      (EnumerationFixedResident.solverEntry width sourceEntry initial.heap.size baseRefs slots + 402)
      (by simpa only [Nat.add_assoc, Nat.reduceAdd, constructorState, RegisterWiden.widenState, atState, dictionarySize, heapSizeEq] using physical.worklist.success)
      (by simpa only [Nat.add_assoc, Nat.reduceAdd, constructorState, RegisterWiden.widenState, atState, dictionarySize, heapSizeEq] using physical.worklist.conflict)
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (by simpa only [Nat.add_assoc, Nat.reduceAdd, constructorState, RegisterWiden.widenState, atState, dictionarySize, heapSizeEq] using physical.cleanup.setup)
      (by simpa only [Nat.add_assoc, Nat.reduceAdd, constructorState, RegisterWiden.widenState, atState, dictionarySize, heapSizeEq] using physical.cleanup.release)
      (by omega) (by omega)
      (by simpa only [Nat.add_assoc, Nat.reduceAdd, constructorState, RegisterWiden.widenState, atState, dictionarySize, heapSizeEq] using physical.cleanup.prepare)
      (by simpa only [Nat.add_assoc, Nat.reduceAdd, constructorState, RegisterWiden.widenState, atState, dictionarySize, heapSizeEq] using physical.cleanup.reset)
      (by omega)
      (by simpa only [Nat.add_assoc, Nat.reduceAdd, constructorState, RegisterWiden.widenState, atState, dictionarySize, heapSizeEq] using physical.cleanup.decision)
  rw [initialEq] at trace finalLive
  have budgets := constructor_full_query_budget initial.heap sharedLayout (ForestZeroCompile.empty ambient)
    (ForestZeroCompile.empty_coherent ambient) references channels within rfl
    (EnumerationFixedResident.solverEntry width sourceEntry initial.heap.size baseRefs slots) sourceEntry
    (initial.reg 3).val rest initial.output initial.reg false
  rw [initialEq] at budgets
  simp only [constructorFormula_rows] at timeBound spaceBound
  rw [← refsLength] at timeBound
  simp only [Bool.false_eq_true, ite_false] at budgets
  refine ⟨answer, final, ticks, peak, trace, finalRunning, decision,
    (by have bound := budgets.1; rw [refsLength, refsLiterals] at bound ⊢; omega), (by have bound := budgets.2; rw [refsLength, refsLiterals] at bound ⊢; omega), ?_, ?_, ?_⟩
  · simpa [constructorState, RegisterWiden.widenState, atState] using finalOutput
  · simpa only [Controller.CNF.Satisfiable] using meaning
  · have ready : QueryReady (ambient := ambient) initial.heap sharedLayout.tableBase sharedLayout.inverseBase
        (EnumerationFixedResident.solverEntry width sourceEntry initial.heap.size baseRefs slots + 430) rest final := by
      refine ⟨heapSize, sourceFrame, ?_, finalStack, ?_, finalRunning, zeroRegister, ?_, ?_⟩
      · simpa only [constructorDictionaryLayout] using zeroTable
      · simpa only [Nat.add_assoc, Nat.reduceAdd] using finalPC
      · simpa only [constructorDictionaryLayout] using tableRegister
      · simpa only [constructorDictionaryLayout] using inverseRegister
    exact ready.rebase initialReady.heapSize initialReady.sourceFrame

end Controller.Cost.EnumerationFixedExecution
