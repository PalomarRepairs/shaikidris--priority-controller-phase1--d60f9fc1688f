module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.EnumerationQuery
public import Controller.Cost.EnumerationFixedConstructorWiden

@[expose] public section

namespace Controller.Cost.EnumerationFixedConstructorWiden
open Controller.CNF Controller.Cost.GateProgram Controller.Cost.ForestZeroTouch
open Controller.Cost.ForestZeroEmit Controller.Cost.ForestZeroDictionary
open Controller.Cost.ForestZeroCompile Controller.Cost.EnumerationSlotBatch
open Controller.Cost.ForestZeroAdmissibleCaller Controller.Cost.ForestZeroAdmissible
open Controller.Cost.ForestZeroCallerWiden Controller.Cost.RegisterWiden

/-- The fixed constructor returns exactly the state consumed by the quiet backend. -/
theorem final_state (trueFlags falseFlags : Slot ambient → Bool) (heap : Array (Word width))
    (layout : Layout ambient heap.size) (dictionary : Dictionary ambient) (channels returnPc : Nat)
    (baseRefs : List (List (Reference ambient))) (slots : List (Slot ambient))
    (stack output : List (Word width)) (saved : Fin 8 → Word width) :
    widenState (finalState trueFlags falseFlags heap layout dictionary channels returnPc baseRefs slots stack output) saved =
      constructorState heap layout dictionary
        (EnumerationFixedConstructor.references baseRefs slots trueFlags falseFlags) channels returnPc stack output saved := by
  have endScalar :
      (if (ForestZeroNonempty.search
          (constructorDictionary heap layout dictionary (EnumerationFixedConstructor.references baseRefs slots trueFlags falseFlags))
          ((constructorDictionary heap layout dictionary (EnumerationFixedConstructor.references baseRefs slots trueFlags falseFlags)).coordinates.size + 1)
          channels 0).reason = .covered
        then (ForestZeroQueryCaller.queryHeap heap layout dictionary
          (reservedReferences (EnumerationFixedConstructor.references baseRefs slots trueFlags falseFlags)) 0).size + 2 * channels
        else (ForestZeroQueryCaller.queryHeap heap layout dictionary
          (reservedReferences (EnumerationFixedConstructor.references baseRefs slots trueFlags falseFlags)) 0).size) =
      (constructorHeap heap layout dictionary
        (EnumerationFixedConstructor.references baseRefs slots trueFlags falseFlags) channels).size := by
    unfold constructorHeap
    dsimp only
    split_ifs <;> simp only [activeHeap_size, boundaryHeap_size, ForestZeroPositive.pairHeap_size,
      ForestZeroPositive.channelLabels_length]
  simp only [constructorDictionary] at endScalar
  simp only [finalState, constructorState, ForestZeroQueryCaller.queryEmission_dictionary,
    EnumerationFixedConstructor.references_length, constructorDictionary]
  rw [endScalar]
  congr 2
  simpa only [finalState, atState, ForestZeroQueryCaller.queryEmission_dictionary,
    EnumerationFixedConstructor.references_length, constructorDictionary] using
    final_heap trueFlags falseFlags heap layout dictionary channels returnPc baseRefs slots stack output

end Controller.Cost.EnumerationFixedConstructorWiden

/-! Fixed runtime-slot construction followed by the existing quiet solver,
counted cleanup and dictionary reset. Neither answer emits output. -/
namespace Controller.Cost.EnumerationFixedDecision
open Controller.Cost Controller.Cost.ForestZeroBackendFrame Controller.Cost.ForestZeroDictionary
open Controller.Cost.ForestZeroAdmissibleCaller
open Controller.CNF Controller.Cost.ForestZeroCompile Controller.Cost.GateProgram Controller.Cost.ForestZeroTouch
open Controller.Cost.ForestZeroAdmissible Controller.Cost.ForestZeroEmit
open Controller.Horn.SourceDirectory Controller.Horn.SourceScan Controller.Horn.RowScan
open Controller.Cost.EnumerationQuery

set_option maxHeartbeats 8000000 in
theorem execution {channels ambient : Nat}
    (heap : Array (Word width)) (originalLayout : Layout ambient heap.size)
    (originalDictionary : Dictionary ambient) (originalRepresentation : Represented heap originalLayout originalDictionary)
    (references : List (List (Reference ambient)))
    (baseRefs : List (List (Reference ambient))) (slots : List (EnumerationSlotBatch.Slot ambient))
    (trueFlags falseFlags : EnumerationSlotBatch.Slot ambient → Bool)
    (selected : references = EnumerationFixedConstructor.references baseRefs slots trueFlags falseFlags)
    (sourceEnd nodes : Nat)
    (baseStored : ∀ reference ∈ baseRefs.flatten, StoredReference heap channels sourceEnd reference)
    (slotStored : ∀ slot ∈ slots, StoredReference heap channels sourceEnd slot.positive ∧
      StoredReference heap channels sourceEnd slot.negative ∧ StoredReference heap channels sourceEnd slot.inactive)
    (maskBounds : ∀ slot ∈ slots, slot.trueMask < sourceEnd ∧ slot.falseMask < sourceEnd)
    (maskCells : ∀ slot ∈ slots, heap[slot.trueMask]? = some (boolWord width (trueFlags slot)) ∧
      heap[slot.falseMask]? = some (boolWord width (falseFlags slot)))
    (sourceBeforeTable : sourceEnd ≤ originalLayout.tableBase)
    (sourceBeforeInverse : sourceEnd ≤ originalLayout.inverseBase)
    (sourceBound : sourceEnd ≤ heap.size) (sourcePositive : 0 < sourceEnd)
    (sourceChannel : heap[0]? = some (word width channels))
    (sourceNodes : heap[1]? = some (word width nodes)) (ambientEq : ambient = channels + nodes)
    (adjacent : originalLayout.inverseBase = originalLayout.tableBase + ambient)
    (tablePositive : 0 < originalLayout.tableBase) (sourceHeaderRoom : 1 < sourceEnd)
    (sourceDual : Controller.Horn.DualHorn
      (ofClauses (ForestZeroAssembly.originalRows (reservedReferences references))))
    (program : Program width 8) (sourceEntry constructorEntry entry : Nat)
    (entryEq : constructorEntry = sourceEntry + 15)
    (originalCount : originalDictionary.coordinates.size = 0)
    (sourceEndpoint : heap.size = originalLayout.inverseBase + ambient)
    (initialScratch : Nat)
    (entryCapacity : sourceEntry + 15 < 2 ^ width)
    (entryAt : ∀ phase : Fin 3, program[sourceEntry + phase.val]? = (reuseEntryCode width)[phase.val]?)
    (keepAt : ForestZeroCallerWiden.WidenedBlockAt program (sourceEntry + 3) (keepCode width))
    (cursorAt : program[sourceEntry + 14]? = some (.constant 0
      (word width (heap.size + 5 + 2 * (references.length + 1)))))
    (rest output : List (Word width)) (highRegisters : Fin 8 → Word width)
    (constructorRoom : heap.size + 5 + 2 * (references.length + 1) +
      2 * references.flatten.length + 2 * ambient < 2 ^ width)
    (ambientFits : ambient + 1 < 2 ^ width)
    (constructorCapacity : constructorEntry +
      (EnumerationFixedConstructor.code width constructorEntry heap.size entry baseRefs slots).length < 2 ^ width)
    (constructorAt : ForestZeroCallerWiden.WidenedBlockAt program constructorEntry
      (EnumerationFixedConstructor.code width constructorEntry heap.size entry baseRefs slots)) :
    let within : channels ≤ ambient := by omega
    let dictionary := constructorDictionary heap originalLayout originalDictionary references
    let formula := constructorFormula heap originalLayout originalDictionary originalRepresentation.coherent references channels within
    let state := constructorState heap originalLayout originalDictionary references channels entry
      (word width heap.size :: rest) output highRegisters
    let backend := constructorFormulaBackend heap originalLayout originalDictionary originalRepresentation.coherent references channels within
    let layout := constructorDictionaryLayout heap originalLayout originalDictionary references channels
    let keep := heap.size
    let recordHeader := heap.size
    let base := state.heap.size
    let recordStart := state.heap.size + 5 * dictionary.coordinates.size + 4
    let recordEnd := Controller.Horn.NormalizeLoop.recordOffset formula.clauses.toList recordStart formula.clauses.toList.length
    ∀ (scan seedDone conflict : Nat)
      (countAt : ∀ phase : Fin 11, program[entry + phase.val]? = (scratchCountCode width)[phase.val]?)
      (allocateAt : Controller.Horn.TrackedAllocate.CodeAt program (entry + 11))
      (headersAt : ∀ phase : Fin 15, program[entry + 16 + phase.val]? = (scratchHeaderCode width)[phase.val]?)
      (endpointAt : ∀ phase : Fin 5, program[entry + 31 + phase.val]? = (scratchEndpointCode (width := width))[phase.val]?)
      (saveAt : ∀ phase : Fin 6, program[entry + 36 + phase.val]? = (saveProjectionCode (width := width))[phase.val]?)
      (normalizerAt : Controller.Horn.NormalizeLoop.CodeAt program (entry + 42) formula.clauses.toList backend)
      (indexSaveAt : Controller.Cost.ForestZeroHeaderBridge.SaveAt program (entry + 203) recordHeader)
      (indexAt : Controller.Horn.IndexScan.At (n := dictionary.coordinates.size) program (entry + 210) base recordStart)
      (indexRestoreAt : Controller.Cost.ForestZeroHeaderBridge.RestoreAt program (entry + 242))
      (captureAt : ∀ phase : Fin 6, program[entry + 245 + phase.val]? = (Controller.Cost.ForestZeroReclaim.captureCode width)[phase.val]?)
      (fullCapacity : entry + 261 < 2 ^ width)
      (setupAt : ∀ phase : Fin 10, program[entry + 251 + phase.val]? =
      (Controller.Cost.ForestZeroSeedSetup.code (n := dictionary.coordinates.size) width base recordHeader recordStart scan)[phase.val]?)
      (scanAt : Controller.Horn.WorklistSeed.At (n := dictionary.coordinates.size) program base scan seedDone conflict)
      (room : state.heap.size + 5 * dictionary.coordinates.size + 4 +
      3 * formula.clauses.toList.length + (formula.clauses.toList.map List.length).sum +
      2 * (Controller.Horn.IndexScan.occurrences formula.clauses.toList recordStart).length < 2 ^ width)
      (scanCapacity : scan + 47 < 2 ^ width)
      (fetch : Nat)
      (headAt : ∀ phase : Fin 4, program[seedDone + phase.val]? =
      (Controller.Horn.WorklistAccept.headSetupCode (n := dictionary.coordinates.size) width base fetch)[phase.val]?)
      (headCapacity : seedDone + 4 < 2 ^ width)
      (fifoDone bucket advance ready skip : Nat)
      (fetchAt : Controller.Horn.WorklistFIFO.FetchAt (n := dictionary.coordinates.size) program base fetch fifoDone bucket)
      (advanceAt : Controller.Horn.WorklistFIFO.AdvanceAt (n := dictionary.coordinates.size) program base advance fetch)
      (loopAt : Controller.Horn.WorklistBucketLoop.At program bucket advance ready)
      (readyAt : Controller.Horn.WorklistBucketReady.At (n := dictionary.coordinates.size) program base ready skip conflict bucket)
      (fetchCapacity : fetch + 14 < 2 ^ width)
      (advanceCapacity : advance + 5 < 2 ^ width)
      (bucketCapacity : bucket + 12 < 2 ^ width)
      (readyCapacity : ready + 26 < 2 ^ width)
      (cleanupEntry returnPc : Nat)
      (successAt : QuietSavedAt program fifoDone 1 cleanupEntry)
      (conflictAt : QuietSavedAt program conflict 0 cleanupEntry)
      (successCapacity : fifoDone + 13 < 2 ^ width)
      (conflictCapacity : conflict + 13 < 2 ^ width)
      (localFit : dictionary.coordinates.size + 1 < 2 ^ width)
      (channelsFit : channels + 1 < 2 ^ width)
      (offRoom : base + 1 < 2 ^ width)
      (cleanupSetup : ∀ phase : Fin 3, program[cleanupEntry + phase.val]? =
      (Controller.Cost.ForestZeroReclaim.setupCode width)[phase.val]?)
      (cleanupLoop : Controller.Cost.ForestZeroReclaim.At program (cleanupEntry + 3) returnPc)
      (cleanupCapacity : cleanupEntry + 7 < 2 ^ width)
      (resetCapacity : returnPc + 27 < 2 ^ width)
      (resetPrepareAt : ForestZeroCallerWiden.WidenedBlockAt program returnPc (resetPrepareCode width).toList)
      (resetLoopAt : ForestZeroCallerWiden.WidenedBlockAt program (returnPc + 15)
      (Controller.Cost.ForestZeroReset.code width (returnPc + 15)))
      (decisionCapacity : returnPc + 28 < 2 ^ width)
      (decisionAt : program[returnPc + 27]? = some (.pop 4)),
∃ answer : Bool, ∃ final ticks peak,
      Execution program
        (Controller.Cost.RegisterWiden.widenState
          (atState heap sourceEntry 0 originalLayout.tableBase originalLayout.inverseBase
            initialScratch rest output) highRegisters)
        final ticks peak ∧
      ticks ≤ 94 + 5 * (baseRefs.length + slots.length) + 23 * baseRefs.flatten.length + 31 * slots.length +
        86 * dictionary.coordinates.size +
        61 * (formula.clauses.toList.map List.length).sum + 125 * formula.clauses.toList.length +
        48 * (Controller.Horn.IndexScan.occurrences formula.clauses.toList recordStart).length +
        4 * (recordEnd + 2 * (Controller.Horn.IndexScan.occurrences formula.clauses.toList recordStart).length - keep) +
        144 ∧
      peak ≤ max
        (18 + heap.size + 2 * (baseRefs.length + slots.length + 1) + 2 * baseRefs.flatten.length + 2 * slots.length +
          2 * dictionary.coordinates.size + (word width heap.size :: rest).length + output.length)
        (state.liveWords + 5 * dictionary.coordinates.size +
        3 * formula.clauses.toList.length + (formula.clauses.toList.map List.length).sum +
        2 * (Controller.Horn.IndexScan.occurrences formula.clauses.toList recordStart).length + 8) ∧
      final.heap.size = keep ∧ final.stack = rest ∧ final.output = output ∧
      final.pc = word width (returnPc + 28) ∧ final.halted = false ∧
      Controller.Cost.ForestZeroBackendFrame.PrefixFrame layout.tableBase state.heap final.heap ∧
      (∀ coordinate : Fin ambient, final.heap[layout.tableBase + coordinate.val]? = some (word width 0)) ∧
      final.reg 4 = word width (if answer then 1 else 0) ∧
      final.reg 0 = word width 0 ∧ final.reg 1 = word width layout.tableBase ∧
      final.reg 2 = word width layout.inverseBase ∧
      (answer = true ↔ ∃ assignment, Controller.CNF.Satisfies assignment formula) ∧
      final.liveWords ≤ (Controller.Cost.RegisterWiden.widenState
        (atState heap sourceEntry 0 originalLayout.tableBase originalLayout.inverseBase
          initialScratch rest output) highRegisters).liveWords +
        1 ∧
      Controller.Cost.ForestZeroBackendFrame.PrefixFrame originalLayout.tableBase heap final.heap ∧
      ∃ reusableLayout : Layout ambient final.heap.size,
        reusableLayout.tableBase = originalLayout.tableBase ∧
        reusableLayout.inverseBase = originalLayout.inverseBase ∧
        Represented final.heap reusableLayout (ForestZeroCompile.empty ambient) ∧
      (∀ next : Nat, answer = false →
        QueryReady (ambient := ambient) heap originalLayout.tableBase originalLayout.inverseBase next rest
          (ForestZeroRootLoop.dispatchState final (returnPc + 28) next false)) := by
  intro within dictionary formula state backend layout keep recordHeader base recordStart recordEnd scan seedDone conflict countAt allocateAt headersAt endpointAt saveAt normalizerAt indexSaveAt indexAt indexRestoreAt captureAt fullCapacity setupAt scanAt room scanCapacity fetch headAt headCapacity fifoDone bucket advance ready skip fetchAt advanceAt loopAt readyAt fetchCapacity advanceCapacity bucketCapacity readyCapacity cleanupEntry returnPc successAt conflictAt successCapacity conflictCapacity localFit channelsFit offRoom cleanupSetup cleanupLoop cleanupCapacity resetCapacity resetPrepareAt resetLoopAt decisionCapacity decisionAt
  have actualDual : Controller.Horn.DualHorn formula :=
    constructorClauses_dualHorn heap originalLayout originalDictionary originalRepresentation.coherent
      references channels within sourceDual
  have originalInputs := constructor_canonical_inputs heap originalLayout originalDictionary
    originalRepresentation references channels within
  have actualStored : Stored formula.clauses.toList backend.directory backend.source state.heap := by
    simpa only [formula, state, backend, constructorState, RegisterWiden.widenState, atState,
      constructorFormulaBackend, constructorBackend, backendLayout, constructorFormula_rows] using originalInputs.1
  have actualCursor : CursorStored backend.directory backend.directoryHeader state.heap := by
    simpa only [formula, state, backend, constructorState, RegisterWiden.widenState, atState,
      constructorFormulaBackend, constructorBackend, backendLayout, constructorFormula_rows] using originalInputs.2.1
  have actualEnd : CursorStored (backend.directory + 2 * formula.clauses.toList.length) backend.endHeader state.heap := by
    simpa only [formula, state, backend, constructorState, RegisterWiden.widenState, atState,
      constructorFormulaBackend, constructorBackend, backendLayout, constructorFormula_rows] using originalInputs.2.2
  have actualBase : backend.base = state.heap.size := rfl
  have actualRecordHeader : backend.recordHeader = keep := rfl
  have actualLocalCount : state.reg 2 = word width dictionary.coordinates.size := rfl
  have actualSourcePointer : state.reg 1 = word width state.heap.size := rfl
  have actualHeadersAbove : ∀ address ∈ [backend.recordHeader, backend.inputHeader, backend.firstHeader,
      backend.directoryHeader, backend.endHeader], backend.recordHeader ≤ address := by
    intro address member
    change address ∈ [heap.size, heap.size + 1, heap.size + 2, heap.size + 3, heap.size + 4] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> change heap.size ≤ _ <;> omega
  have actualGrowth : keep ≤ state.heap.size := constructorHeap_growth heap originalLayout originalDictionary references channels
  have actualRepresented : Represented state.heap layout dictionary :=
    constructor_dictionary_represented heap originalLayout originalDictionary originalRepresentation references channels
  have actualTableBefore : layout.tableBase + ambient ≤ keep := originalLayout.tableBound
  have actualInverseBefore : layout.inverseBase + ambient ≤ keep := originalLayout.inverseBound
  have actualChannels : state.heap[0]? = some (word width channels) :=
    (constructor_source_cell heap originalLayout originalDictionary references channels sourceEnd 0
      sourceBeforeTable sourceBeforeInverse sourceBound (by omega)).trans sourceChannel
  have actualNodes : state.heap[1]? = some (word width nodes) :=
    (constructor_source_cell heap originalLayout originalDictionary references channels sourceEnd 1
      sourceBeforeTable sourceBeforeInverse sourceBound sourceHeaderRoom).trans sourceNodes
  obtain ⟨answer, final, queryTicks, queryPeak, queryTrace, queryTime, querySpace,
      heapSize, finalStack, finalOutput, finalPC, finalRunning, finalFrame, zeroTable,
      decision, zeroRegister, tableRegister, inverseRegister, meaning⟩ :=
    quiet_scratch_indexed_execution dictionary keep formula actualDual recordHeader recordStart recordEnd base entry scan seedDone conflict state program backend actualStored actualCursor actualEnd actualBase actualRecordHeader rfl rfl rfl rfl actualLocalCount actualSourcePointer countAt allocateAt headersAt endpointAt saveAt normalizerAt actualHeadersAbove indexSaveAt indexAt indexRestoreAt captureAt fullCapacity setupAt scanAt rfl rfl room scanCapacity actualGrowth actualGrowth fetch headAt headCapacity fifoDone bucket advance ready skip fetchAt advanceAt loopAt readyAt fetchCapacity advanceCapacity bucketCapacity readyCapacity cleanupEntry returnPc successAt conflictAt successCapacity conflictCapacity layout actualRepresented nodes ambientEq adjacent actualTableBefore actualInverseBefore (by omega) actualChannels actualNodes localFit channelsFit offRoom cleanupSetup cleanupLoop cleanupCapacity rest rfl tablePositive resetCapacity resetPrepareAt resetLoopAt decisionCapacity decisionAt
  have refsLength : references.length = baseRefs.length + slots.length := by
    rw [selected, EnumerationFixedConstructor.references_length]
  have refsLiterals : references.flatten.length = baseRefs.flatten.length + slots.length := by
    rw [selected]
    simp only [EnumerationFixedConstructor.references, List.flatten_append, List.length_append,
      EnumerationFixedProfile.selectedRefs_flatten, List.length_map]
  have widthPositive : 0 < width := by
    by_contra h
    have zero : width = 0 := by omega
    rw [zero] at entryCapacity
    norm_num at entryCapacity
  obtain ⟨constructorTicks, constructorPeak, constructorTrace, constructorTime, constructorSpace⟩ :=
    EnumerationFixedConstructorWiden.execution program highRegisters trueFlags falseFlags heap originalLayout
      originalDictionary originalRepresentation channels sourceEnd baseRefs slots sourceBound sourcePositive
      sourceChannel within baseStored slotStored maskBounds maskCells sourceBeforeTable sourceBeforeInverse
      constructorEntry entry (word width heap.size :: rest) output widthPositive
      (by rw [refsLength, refsLiterals] at constructorRoom; omega) ambientFits constructorCapacity constructorAt
  rw [← selected] at constructorTime constructorSpace
  have finalEq := EnumerationFixedConstructorWiden.final_state trueFlags falseFlags heap originalLayout
    originalDictionary channels entry baseRefs slots (word width heap.size :: rest) output highRegisters
  rw [← selected] at finalEq
  rw [finalEq] at constructorTrace
  change Execution program
    (RegisterWiden.widenState
      (atState heap constructorEntry (heap.size + 5 + 2 * (baseRefs.length + slots.length + 1))
        originalLayout.tableBase originalDictionary.coordinates.size 0
        (word width originalLayout.inverseBase :: word width heap.size :: rest) output) highRegisters)
    state constructorTicks constructorPeak at constructorTrace
  rw [← refsLength] at constructorTrace
  have prepared := reuse_entry_execution program heap sourceEntry originalLayout.tableBase
    originalLayout.inverseBase initialScratch rest output highRegisters (by omega) entryAt
  have kept := keep_cursor_execution8 program heap originalLayout channels nodes (sourceEntry + 3)
    references rest output highRegisters ambientEq sourceEndpoint (by omega) sourceChannel sourceNodes
    (by omega) (by omega) keepAt (by simpa only [Nat.add_assoc] using cursorAt)
  simp only [Nat.add_assoc] at kept
  simp only [Nat.add_assoc] at constructorTrace
  rw [originalCount, entryEq] at constructorTrace
  have readyTrace := prepared.append kept
  have queryTraceAll := constructorTrace.append queryTrace
  have joined := readyTrace.append queryTraceAll
  refine ⟨answer, final, 15 + (constructorTicks + queryTicks),
    max (max (10 + heap.size + rest.length + output.length)
      (11 + heap.size + rest.length + output.length)) (max constructorPeak queryPeak),
    (by simpa only [← Nat.add_assoc] using joined), ?_, ?_, heapSize, finalStack, ?_, finalPC, finalRunning, finalFrame,
    zeroTable, decision, zeroRegister, tableRegister, inverseRegister, meaning, ?_, ?_, ?_⟩
  · simp only [dictionary, constructorDictionary] at constructorTime queryTime ⊢
    omega
  · have constructorBelow := Nat.le_max_left
        (18 + heap.size + 2 * (baseRefs.length + slots.length + 1) + 2 * baseRefs.flatten.length + 2 * slots.length +
          2 * dictionary.coordinates.size + (word width heap.size :: rest).length + output.length)
        (state.liveWords + 5 * dictionary.coordinates.size + 3 * formula.clauses.toList.length +
          (formula.clauses.toList.map List.length).sum +
          2 * (Controller.Horn.IndexScan.occurrences formula.clauses.toList recordStart).length + channels + 8)
    have combined := max_le_max constructorSpace querySpace
    simp only [dictionary, constructorDictionary] at constructorSpace querySpace constructorBelow combined ⊢
    simp only [List.length_cons] at constructorBelow combined ⊢
    omega
  · simpa [state, constructorState, RegisterWiden.widenState, atState] using finalOutput
  · unfold State.liveWords
    rw [heapSize, finalStack, finalOutput]
    simp [keep, state, constructorState, RegisterWiden.widenState, atState]
  · have before := constructor_prefix heap originalLayout originalDictionary references channels adjacent
    have after : ForestZeroBackendFrame.PrefixFrame originalLayout.tableBase
        (constructorHeap heap originalLayout originalDictionary references channels) final.heap := by
      simpa only [layout, constructorDictionaryLayout, state, constructorState,
        RegisterWiden.widenState, atState] using finalFrame
    exact ForestZeroBackendFrame.trans before after
  · let reusableLayout : Layout ambient final.heap.size :=
      { tableBase := originalLayout.tableBase
        inverseBase := originalLayout.inverseBase
        tableBound := by rw [heapSize]; exact originalLayout.tableBound
        inverseBound := by rw [heapSize]; exact originalLayout.inverseBound
        disjoint := originalLayout.disjoint }
    have actualZero : ∀ coordinate : Fin ambient,
        final.heap[originalLayout.tableBase + coordinate.val]? = some (word width 0) := by
      intro coordinate
      simpa only [layout, constructorDictionaryLayout] using zeroTable coordinate
    refine ⟨reusableLayout, rfl, rfl,
      empty_dictionary_from_zero_table final.heap reusableLayout actualZero, ?_⟩
    intro next failed
    have originalFrame : ForestZeroBackendFrame.PrefixFrame originalLayout.tableBase heap final.heap := by
      have before := constructor_prefix heap originalLayout originalDictionary references channels adjacent
      have after : ForestZeroBackendFrame.PrefixFrame originalLayout.tableBase
          (constructorHeap heap originalLayout originalDictionary references channels) final.heap := by
        simpa only [layout, constructorDictionaryLayout, state, constructorState,
          RegisterWiden.widenState, atState] using finalFrame
      exact ForestZeroBackendFrame.trans before after
    exact failed_query_dispatch_ready heap originalLayout.tableBase originalLayout.inverseBase
      (returnPc + 28) next rest final heapSize originalFrame actualZero finalStack zeroRegister
      (by simpa only [layout, constructorDictionaryLayout] using tableRegister)
      (by simpa only [layout, constructorDictionaryLayout] using inverseRegister)


end Controller.Cost.EnumerationFixedDecision
