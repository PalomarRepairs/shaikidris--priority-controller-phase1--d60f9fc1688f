module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedDetectorFeasibility

@[expose] public section

namespace Controller.Cost.SharedDetectorLoop
open Controller.Cost.GateProgram Controller.Cost.RawTransferLoops
open Controller.Cost.ForestZeroDictionary Controller.Cost.ForestZeroAdmissibleCaller
open Controller.Cost.ForestZeroBackendFrame
open Controller.Native Controller.Native.SourceController Controller.Decoder
open Controller.Cost.NativeSourceExecution Controller.Cost.SharedZeroResidentConditions

abbrev Width (parameters : Parameters) (graph : DAG parameters.channels) (retained : Nat) :=
  SharedMachineCapacity.wordWidth retained graph.countedSize (selectedSize parameters).total

def Ready (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels)) (retained coordinateBase slot sourceEnd offset maskBase entry : Nat)
    (program : Program (Width parameters graph retained) 8) (rest : List (Word (Width parameters graph retained)))
    (state : State (Width parameters graph retained) 8) (source : Nat) (positions : List (Fin graph.roots.length)) : Prop :=
  ∃ currentRoot : Fin graph.nodeCount, ∃ sourceHeap : Array (Word (Width parameters graph retained)),
  ∃ layout : Layout (parameters.channels + graph.nodeCount) state.heap.size,
  SourceConditions parameters state layout
    (SharedZeroSource.references graph parameters.buses parameters.bridge.target T F coordinateBase slot currentRoot) sourceEnd graph.nodeCount ∧
  QueryReady (ambient := parameters.channels + graph.nodeCount) sourceHeap layout.tableBase layout.inverseBase entry
    (word (Width parameters graph retained) source :: word (Width parameters graph retained) positions.length ::
      (SharedDetectorData.healthyTags parameters graph (Width parameters graph retained) positions ++ rest)) state ∧
  SharedDetectorData.Stored parameters graph T F maskBase source offset slot positions sourceHeap ∧
  slot < layout.tableBase ∧ slot < sourceEnd ∧ 1 < slot ∧
  coordinateBase + (parameters.channels + graph.nodeCount) ≤ slot ∧
  state.heap.size ≤ retained ∧ positions.length ≤ graph.roots.length ∧
  entry + (SharedRootDetectorResident.code parameters graph T F state.heap layout coordinateBase slot offset maskBase entry currentRoot).length ≤ retained ∧
  SharedRootRead.BlockAt program entry
    (SharedRootDetectorResident.code parameters graph T F state.heap layout coordinateBase slot offset maskBase entry currentRoot)

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4096 in
theorem skipped (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels)) (retained coordinateBase slot sourceEnd offset maskBase entry : Nat)
    (program : Program (Width parameters graph retained) 8) (rest : List (Word (Width parameters graph retained)))
    (state : State (Width parameters graph retained) 8) (source : Nat)
    (position : Fin graph.roots.length) (positions : List (Fin graph.roots.length))
    (unhealthy : graph.eval (assignmentOfSet {parameters.bridge.target}) graph.roots[position.val] = false)
    (missing : SharedWitnessDecode.tag graph (extensionBase parameters.buses parameters.bridge.target T) F
      (Width parameters graph retained) position = word (Width parameters graph retained) (parameters.channels + 1))
    (prepared : Ready parameters graph T F retained coordinateBase slot sourceEnd offset maskBase entry program rest state source (position :: positions)) :
    ∃ final ticks peak, Execution program state final ticks peak ∧ ticks ≤ 26 ∧ peak = state.liveWords ∧
      final.liveWords + 1 = state.liveWords ∧
      Ready parameters graph T F retained coordinateBase slot sourceEnd offset maskBase entry program rest final (source + 1) positions := by
  rcases prepared with ⟨currentRoot, sourceHeap, layout, sourceData, query, data, slotBefore, slotBound, headerBefore,
    tableBefore, heapBound, countBound, budget, present⟩
  let trueCode := SharedTrueHandler.code parameters (Width parameters graph retained) state.heap.size maskBase (entry + 22)
  have all := present
  unfold SharedRootDetectorResident.code at all
  obtain ⟨cursorAt, trueAt, skipAt, healthyAt, queryAt, exhaustedAt⟩ :=
    SharedRootDetectorCode.blocks_at parameters graph T F state.heap layout coordinateBase slot offset entry trueCode currentRoot program all
  have codeSize : entry + 22 + trueCode.length + 6 ≤ retained := by
    unfold SharedRootDetectorResident.code SharedRootDetectorCode.code at budget
    simp only [List.length_append, Array.length_toList, SharedRootTaggedCursor.code_size,
      SharedRootResumeEntry.skipCode_size, SharedRootHealthyEntry.code_size] at budget
    dsimp only [trueCode]
    omega
  have capacity := SharedMachineCapacity.capacity retained graph.countedSize (selectedSize parameters).total
  change 131072 * (retained + graph.countedSize + (selectedSize parameters).total + 1) <
    2 ^ Width parameters graph retained at capacity
  have graphSize := graph.countedSize_eq
  have actualData := SharedDetectorData.ready parameters graph T F maskBase source offset slot (position :: positions)
    sourceHeap state layout.tableBase layout.inverseBase entry _ data query slotBefore
  obtain ⟨candidateStored, rootStored, sourceValid, rootValid⟩ :=
    SharedDetectorData.head parameters graph T F maskBase source offset slot position positions state.heap actualData
  rw [missing] at candidateStored
  obtain ⟨final, ticks, trace, time, heap, output, nextReady, live⟩ :=
    SharedRootTaggedSkip.execution program state sourceHeap layout.tableBase layout.inverseBase parameters.channels entry
      (SharedRootDetectorCode.exhausted parameters graph T F state.heap layout coordinateBase slot entry trueCode currentRoot)
      (SharedRootDetectorCode.healthyEntry entry trueCode) (SharedRootDetectorCode.skipEntry entry trueCode) source positions.length
      parameters.bridge.target (SharedDetectorData.healthyTags parameters graph (Width parameters graph retained) positions ++ rest)
      (by simpa only [SharedDetectorData.healthyTags, List.map_cons, unhealthy, Bool.false_eq_true, ↓reduceIte, List.cons_append,
        List.length_cons] using query) (by omega)
      (by dsimp only [SharedRootDetectorCode.skipEntry]; omega) (by omega)
      (by simp only [List.length_cons] at countBound; omega) (by omega) sourceValid candidateStored cursorAt skipAt
  have sameSize : final.heap.size = state.heap.size := congrArg Array.size heap
  let nextLayout := SharedQuerySourceFrame.layout state final layout sameSize
  have sameCode := SharedRootDetectorResident.shared parameters graph T F state.heap final.heap layout nextLayout
    coordinateBase slot offset maskBase entry currentRoot currentRoot sameSize.symm rfl rfl
  have nextSource := SharedQuerySourceFrame.transport parameters state final layout
    (SharedZeroSource.references graph parameters.buses parameters.bridge.target T F coordinateBase slot currentRoot)
    sourceEnd graph.nodeCount sourceData sameSize (by
      refine ⟨sourceData.sourceBound, ?_, ?_⟩
      · rw [heap]; exact sourceData.sourceBound
      · intro index below; rw [heap])
  refine ⟨final, ticks, state.liveWords, trace, time, rfl, live,
    currentRoot, sourceHeap, nextLayout, nextSource, nextReady,
    SharedDetectorData.tail parameters graph T F maskBase source offset slot position positions sourceHeap data,
    slotBefore, slotBound, headerBefore, tableBefore, sameSize.le.trans heapBound, ?_, ?_, ?_⟩
  · simp only [List.length_cons] at countBound; omega
  · rw [← sameCode]; exact budget
  · rw [← sameCode]; exact present


set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4096 in
theorem healthy (parameters : Parameters) (raw : parameters.layout = .raw) (drive : parameters.drive = true)
    (graph : DAG parameters.channels) (guarded : graph.Guarded)
    (T F : Finset (Fin parameters.channels)) (retained coordinateBase slot sourceEnd offset maskBase entry : Nat)
    (program : Program (Width parameters graph retained) 8) (rest : List (Word (Width parameters graph retained)))
    (state : State (Width parameters graph retained) 8) (source : Nat)
    (position : Fin graph.roots.length) (positions : List (Fin graph.roots.length))
    (observation : Fin parameters.decoder.roots.length)
    (observationEq : ∀ K, parameters.observations observation (assignmentOfSet K) = graph.eval (assignmentOfSet K) graph.roots[position.val])
    (healthyTrue : graph.eval (assignmentOfSet {parameters.bridge.target}) graph.roots[position.val] = true)
    (prepared : Ready parameters graph T F retained coordinateBase slot sourceEnd offset maskBase entry program rest state source (position :: positions)) :
    ∃ answer : Bool, ∃ final ticks peak,
      Execution program state final ticks peak ∧ final.halted = answer ∧
      ticks ≤ 5032 * (graph.countedSize + 1) + (if answer then 55 * (selectedSize parameters).total else 0) ∧
      peak ≤ state.liveWords + 200 * (graph.countedSize + 1) + 3 * (selectedSize parameters).total ∧
      final.liveWords ≤ state.liveWords + (if answer then (compile parameters).toState.count else 0) ∧
      (answer = true ↔ SharedDetectorFeasibility.AtRoot parameters graph T F position) ∧
      (answer = true → Certificate.ModelCheck.check (formula parameters)
        (NativeRealizedChecked.decodeOutput final.output (compile parameters).toState.count) = true) ∧
      (answer = false → Ready parameters graph T F retained coordinateBase slot sourceEnd offset maskBase entry
        program rest final (source + 1) positions) ∧
      (answer = true → final.reg 4 = word (Width parameters graph retained) 1) := by
  rcases prepared with ⟨currentRoot, sourceHeap, layout, sourceData, query, data, slotBefore, slotBound, headerBefore,
    tableBefore, heapBound, countBound, budget, present⟩
  let trueCode := SharedTrueHandler.code parameters (Width parameters graph retained) state.heap.size maskBase (entry + 22)
  have all := present
  unfold SharedRootDetectorResident.code at all
  obtain ⟨cursorAt, trueAt, skipAt, healthyAt, queryAt, exhaustedAt⟩ :=
    SharedRootDetectorCode.blocks_at parameters graph T F state.heap layout coordinateBase slot offset entry trueCode currentRoot program all
  have queryBound : SharedRootDetectorCode.healthyEntry entry trueCode + 12 ≤ retained := by
    unfold SharedRootDetectorResident.code SharedRootDetectorCode.code at budget
    simp only [List.length_append, Array.length_toList, SharedRootTaggedCursor.code_size,
      SharedRootResumeEntry.skipCode_size, SharedRootHealthyEntry.code_size] at budget
    dsimp only [SharedRootDetectorCode.healthyEntry, SharedRootDetectorCode.skipEntry, trueCode]
    omega
  have entryBound : entry + 22 ≤ retained := by
    dsimp only [SharedRootDetectorCode.healthyEntry, SharedRootDetectorCode.skipEntry] at queryBound
    omega
  have actualData := SharedDetectorData.ready parameters graph T F maskBase source offset slot (position :: positions)
    sourceHeap state layout.tableBase layout.inverseBase entry _ data query slotBefore
  obtain ⟨candidateStored, rootStored, sourceValid, rootValid⟩ :=
    SharedDetectorData.head parameters graph T F maskBase source offset slot position positions state.heap actualData
  change SharedRootRead.BlockAt program (SharedRootDetectorCode.healthyEntry entry trueCode + 12)
    (SharedQueryReuseCode.code parameters graph T F state.heap layout coordinateBase slot
      (SharedRootDetectorCode.healthyEntry entry trueCode + 12) entry currentRoot) at queryAt
  obtain ⟨answer, final, ticks, peak, trace, halted, time, memory, live, meaning, witness, failed, sourcePreserved,
    accepted⟩ :=
    SharedRootHealthyQuery.execution parameters graph guarded T F currentRoot graph.roots[position.val] program state sourceHeap layout
      coordinateBase slot sourceEnd entry
      (SharedRootDetectorCode.exhausted parameters graph T F state.heap layout coordinateBase slot entry trueCode currentRoot)
      (SharedRootDetectorCode.healthyEntry entry trueCode) (SharedRootDetectorCode.skipEntry entry trueCode) source positions.length offset
      (SharedWitnessDecode.tag graph (extensionBase parameters.buses parameters.bridge.target T) F (Width parameters graph retained) position)
      (SharedDetectorData.healthyTags parameters graph (Width parameters graph retained) positions ++ rest)
      sourceData (by simpa only [SharedDetectorData.healthyTags, List.map_cons, healthyTrue, ↓reduceIte,
        List.cons_append, List.length_cons] using query) heapBound entryBound queryBound
      (by simpa only [List.length_cons] using countBound) sourceValid rootValid slotBefore slotBound headerBefore tableBefore
      candidateStored rootStored cursorAt healthyAt queryAt
  refine ⟨answer, final, ticks, peak, trace, halted, time, memory, live,
    meaning.trans (SharedDetectorFeasibility.healthy_iff parameters graph T F position healthyTrue).symm, ?_, ?_, accepted⟩
  · intro success
    have capacity := SharedMachineCapacity.capacity retained graph.countedSize (selectedSize parameters).total
    exact SharedRootResidentLoop.Witness.checked parameters raw drive graph guarded T F coordinateBase slot
      graph.roots[position.val] final.output (by omega) observation observationEq healthyTrue (witness success)
  · intro negative
    obtain ⟨sameSize, nextSource⟩ := sourcePreserved negative
    let nextLayout := SharedQuerySourceFrame.layout state final layout sameSize
    have valid : slot < sourceHeap.size := by have := query.sourceFrame.1; have := query.sourceFrame.2.1; omega
    let nextHeap := sourceHeap.set slot (word (Width parameters graph retained) graph.roots[position.val].val) valid
    have updated := SharedDetectorData.root_update parameters graph T F maskBase source offset slot (position :: positions)
      sourceHeap (word (Width parameters graph retained) graph.roots[position.val].val) valid data
    have nextData := SharedDetectorData.tail parameters graph T F maskBase source offset slot position positions _ updated
    have sameCode := SharedRootDetectorResident.shared parameters graph T F state.heap final.heap layout nextLayout
      coordinateBase slot offset maskBase entry currentRoot graph.roots[position.val] sameSize.symm rfl rfl
    refine ⟨graph.roots[position.val], nextHeap, nextLayout, nextSource, failed negative, nextData,
      slotBefore, slotBound, headerBefore, tableBefore, sameSize.le.trans heapBound, ?_, ?_, ?_⟩
    · simp only [List.length_cons] at countBound; omega
    · rw [← sameCode]; exact budget
    · rw [← sameCode]; exact present


set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4096 in
theorem found (parameters : Parameters) (raw : parameters.layout = .raw) (drive : parameters.drive = true)
    (graph : DAG parameters.channels) (T F : Finset (Fin parameters.channels))
    (consistent : FixedConsistent (extensionBase parameters.buses parameters.bridge.target T) F)
    (retained coordinateBase slot sourceEnd offset maskBase entry : Nat)
    (program : Program (Width parameters graph retained) 8) (rest : List (Word (Width parameters graph retained)))
    (state : State (Width parameters graph retained) 8) (source : Nat)
    (position : Fin graph.roots.length) (positions : List (Fin graph.roots.length))
    (observation : Fin parameters.decoder.roots.length)
    (observationEq : ∀ K, parameters.observations observation (assignmentOfSet K) = graph.eval (assignmentOfSet K) graph.roots[position.val])
    (unhealthy : graph.eval (assignmentOfSet {parameters.bridge.target}) graph.roots[position.val] = false)
    (candidateFound : SharedWitnessDecode.tag graph (extensionBase parameters.buses parameters.bridge.target T) F
      (Width parameters graph retained) position ≠ word (Width parameters graph retained) (parameters.channels + 1))
    (prepared : Ready parameters graph T F retained coordinateBase slot sourceEnd offset maskBase entry program rest state source (position :: positions)) :
    ∃ final ticks peak, Execution program state final ticks peak ∧
      ticks ≤ 5032 * (graph.countedSize + 1) + 55 * (selectedSize parameters).total ∧
      peak ≤ state.liveWords + 200 * (graph.countedSize + 1) + 3 * (selectedSize parameters).total ∧
      final.halted = true ∧ final.reg 4 = word (Width parameters graph retained) 1 ∧
      Certificate.ModelCheck.check (formula parameters)
        (NativeRealizedChecked.decodeOutput final.output (compile parameters).toState.count) = true := by
  rcases prepared with ⟨currentRoot, sourceHeap, layout, sourceData, query, data, slotBefore, slotBound, headerBefore,
    tableBefore, heapBound, countBound, budget, present⟩
  let trueCode := SharedTrueHandler.code parameters (Width parameters graph retained) state.heap.size maskBase (entry + 22)
  have all := present
  unfold SharedRootDetectorResident.code at all
  obtain ⟨cursorAt, trueAt, skipAt, healthyAt, queryAt, exhaustedAt⟩ :=
    SharedRootDetectorCode.blocks_at parameters graph T F state.heap layout coordinateBase slot offset entry trueCode currentRoot program all
  have trueBound : entry + 22 + trueCode.length ≤ retained := by
    unfold SharedRootDetectorResident.code SharedRootDetectorCode.code at budget
    simp only [List.length_append, Array.length_toList, SharedRootTaggedCursor.code_size,
      SharedRootResumeEntry.skipCode_size, SharedRootHealthyEntry.code_size] at budget
    dsimp only [trueCode]
    omega
  have capacity := SharedMachineCapacity.capacity retained graph.countedSize (selectedSize parameters).total
  change 131072 * (retained + graph.countedSize + (selectedSize parameters).total + 1) <
    2 ^ Width parameters graph retained at capacity
  have graphSize := graph.countedSize_eq
  have variablesBound : (compile parameters).toState.count ≤ (selectedSize parameters).total := by
    simp only [selectedSize, NativeSize.total]
    omega
  have roots := (sourceCircuit parameters).roots_le
  have channelsBound : parameters.channels ≤ SourceInitialIDs.rootCount parameters := by
    simp only [SourceInitialIDs.rootCount]
    omega
  have actualData := SharedDetectorData.ready parameters graph T F maskBase source offset slot (position :: positions)
    sourceHeap state layout.tableBase layout.inverseBase entry _ data query slotBefore
  obtain ⟨candidateStored, rootStored, sourceValid, rootValid⟩ :=
    SharedDetectorData.head parameters graph T F maskBase source offset slot position positions state.heap actualData
  obtain ⟨candidateBound, rootBound, maskBound, candidates, identifiers, maskStored⟩ := actualData
  have sourceBound := sourceData.sourceBound
  obtain ⟨final, ticks, peak, trace, time, memory, halted, decision, heap, stack, checked⟩ :=
    SharedRootTaggedTrue.execution parameters raw drive graph T F position observation observationEq consistent unhealthy program state
      sourceHeap layout.tableBase layout.inverseBase maskBase entry
      (SharedRootDetectorCode.exhausted parameters graph T F state.heap layout coordinateBase slot entry trueCode currentRoot)
      (SharedRootDetectorCode.healthyEntry entry trueCode) (SharedRootDetectorCode.skipEntry entry trueCode) source positions.length
      (SharedDetectorData.healthyTags parameters graph (Width parameters graph retained) positions ++ rest) candidateFound
      (by simpa only [SharedDetectorData.healthyTags, List.map_cons, unhealthy, Bool.false_eq_true, ↓reduceIte, List.cons_append,
        List.length_cons] using query) (by omega)
      (by simp only [List.length_cons] at countBound; omega) (by omega) sourceValid candidateStored
      (by change entry + 22 + trueCode.length < _; omega) (by omega) (by omega) (by omega) maskStored cursorAt trueAt
  exact ⟨final, ticks, peak, trace, by omega, by omega, halted, decision, checked⟩


theorem Ready.running (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels)) (retained coordinateBase slot sourceEnd offset maskBase entry : Nat)
    (program : Program (Width parameters graph retained) 8) (rest : List (Word (Width parameters graph retained)))
    (state : State (Width parameters graph retained) 8) (source : Nat) (positions : List (Fin graph.roots.length))
    (ready : Ready parameters graph T F retained coordinateBase slot sourceEnd offset maskBase entry program rest state source positions) :
    state.halted = false := by
  rcases ready with ⟨root, heap, layout, sourceData, query, other⟩
  exact query.running

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4096 in
theorem step (parameters : Parameters) (raw : parameters.layout = .raw) (drive : parameters.drive = true)
    (graph : DAG parameters.channels) (guarded : graph.Guarded) (T F : Finset (Fin parameters.channels))
    (consistent : FixedConsistent (extensionBase parameters.buses parameters.bridge.target T) F)
    (retained coordinateBase slot sourceEnd offset maskBase entry : Nat)
    (program : Program (Width parameters graph retained) 8) (rest : List (Word (Width parameters graph retained)))
    (state : State (Width parameters graph retained) 8) (source : Nat)
    (position : Fin graph.roots.length) (positions : List (Fin graph.roots.length))
    (observation : Fin parameters.decoder.roots.length)
    (observationEq : ∀ K, parameters.observations observation (assignmentOfSet K) = graph.eval (assignmentOfSet K) graph.roots[position.val])
    (prepared : Ready parameters graph T F retained coordinateBase slot sourceEnd offset maskBase entry program rest state source (position :: positions)) :
    ∃ answer : Bool, ∃ final ticks peak,
      Execution program state final ticks peak ∧ final.halted = answer ∧
      ticks ≤ 5032 * (graph.countedSize + 1) + (if answer then 55 * (selectedSize parameters).total else 0) ∧
      peak ≤ state.liveWords + 200 * (graph.countedSize + 1) + 3 * (selectedSize parameters).total ∧
      (answer = true ↔ SharedDetectorFeasibility.AtRoot parameters graph T F position) ∧
      (answer = true → Certificate.ModelCheck.check (formula parameters)
        (NativeRealizedChecked.decodeOutput final.output (compile parameters).toState.count) = true) ∧
      (answer = false → Ready parameters graph T F retained coordinateBase slot sourceEnd offset maskBase entry
        program rest final (source + 1) positions) ∧
      (answer = false → final.liveWords ≤ state.liveWords) ∧
      (answer = true → final.reg 4 = word (Width parameters graph retained) 1) := by
  cases health : graph.eval (assignmentOfSet {parameters.bridge.target}) graph.roots[position.val] with
  | true =>
    obtain ⟨answer, final, ticks, peak, trace, halted, time, memory, live, meaning, checked, continued, accepted⟩ :=
      healthy parameters raw drive graph guarded T F retained coordinateBase slot sourceEnd offset maskBase entry
        program rest state source position positions observation observationEq health prepared
    refine ⟨answer, final, ticks, peak, trace, halted, time, memory, meaning, checked, continued, ?_, accepted⟩
    intro negative
    simpa only [negative, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] using live
  | false =>
    have capacity := SharedMachineCapacity.capacity retained graph.countedSize (selectedSize parameters).total
    have graphCapacity : 256 * (graph.countedSize + 1) < 2 ^ Width parameters graph retained := by
      change 131072 * (retained + graph.countedSize + (selectedSize parameters).total + 1) <
        2 ^ Width parameters graph retained at capacity
      omega
    have criterion := SharedDetectorFeasibility.candidate_iff parameters graph guarded T F position
      (Width parameters graph retained) consistent graphCapacity health
    by_cases missing : SharedWitnessDecode.tag graph (extensionBase parameters.buses parameters.bridge.target T) F
        (Width parameters graph retained) position = word (Width parameters graph retained) (parameters.channels + 1)
    · obtain ⟨final, ticks, peak, trace, time, peakEq, live, nextReady⟩ :=
        skipped parameters graph T F retained coordinateBase slot sourceEnd offset maskBase entry program rest state source
          position positions health missing prepared
      have noFeasible : ¬ SharedDetectorFeasibility.AtRoot parameters graph T F position := by
        intro feasible
        exact (criterion.mpr feasible) missing
      refine ⟨false, final, ticks, peak, trace, Ready.running parameters graph T F retained coordinateBase slot sourceEnd
        offset maskBase entry program rest final (source + 1) positions nextReady, ?_, ?_, ?_, ?_,
        (fun _ => nextReady), (fun _ => by omega), (fun impossible => by cases impossible)⟩
      · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]; omega
      · rw [peakEq]; omega
      · simp only [Bool.false_eq_true, false_iff]; exact noFeasible
      · intro impossible; cases impossible
    · obtain ⟨final, ticks, peak, trace, time, memory, halted, decision, checked⟩ :=
        found parameters raw drive graph T F consistent retained coordinateBase slot sourceEnd offset maskBase entry
          program rest state source position positions observation observationEq health missing prepared
      refine ⟨true, final, ticks, peak, trace, halted, ?_, memory, ?_, (fun _ => checked), ?_, ?_, (fun _ => decision)⟩
      · simpa only [↓reduceIte] using time
      · constructor
        · intro _; exact criterion.mp missing
        · intro _; rfl
      · intro impossible; cases impossible
      · intro impossible; cases impossible


set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4096 in
theorem empty (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels)) (retained coordinateBase slot sourceEnd offset maskBase entry : Nat)
    (program : Program (Width parameters graph retained) 8) (rest : List (Word (Width parameters graph retained)))
    (state : State (Width parameters graph retained) 8) (source : Nat)
    (prepared : Ready parameters graph T F retained coordinateBase slot sourceEnd offset maskBase entry program rest state source []) :
    ∃ final, Execution program state final 5 state.liveWords ∧ final.halted = true ∧
      final.reg 4 = word (Width parameters graph retained) 0 ∧ final.heap = state.heap ∧
      final.stack = rest ∧ final.output = state.output := by
  rcases prepared with ⟨currentRoot, sourceHeap, layout, sourceData, query, data, slotBefore, slotBound, headerBefore,
    tableBefore, heapBound, countBound, budget, present⟩
  let trueCode := SharedTrueHandler.code parameters (Width parameters graph retained) state.heap.size maskBase (entry + 22)
  have all := present
  unfold SharedRootDetectorResident.code at all
  obtain ⟨cursorAt, trueAt, skipAt, healthyAt, queryAt, exhaustedAt⟩ :=
    SharedRootDetectorCode.blocks_at parameters graph T F state.heap layout coordinateBase slot offset entry trueCode currentRoot program all
  have cursorBlock := cursorAt
  unfold SharedRootTaggedCursor.code at cursorBlock
  have cursorHead := RawSharedOrdered.takePrefix program entry _ _ cursorBlock
  have endpoint := SharedRootDetectorCode.code_end parameters graph T F state.heap layout coordinateBase slot offset entry trueCode currentRoot
  unfold SharedRootDetectorResident.code at budget
  have endBound : SharedRootDetectorCode.exhausted parameters graph T F state.heap layout coordinateBase slot entry trueCode currentRoot + 2 ≤ retained := by
    rw [endpoint]
    exact budget
  have startBound : entry + 10 ≤ retained := by
    unfold SharedRootDetectorCode.code at budget
    simp only [List.length_append, Array.length_toList, SharedRootTaggedCursor.code_size] at budget
    omega
  have capacity := SharedMachineCapacity.capacity retained graph.countedSize (selectedSize parameters).total
  change 131072 * (retained + graph.countedSize + (selectedSize parameters).total + 1) <
    2 ^ Width parameters graph retained at capacity
  exact SharedRootCursor.zero_halts program state sourceHeap layout.tableBase layout.inverseBase entry
    (SharedRootDetectorCode.exhausted parameters graph T F state.heap layout coordinateBase slot entry trueCode currentRoot)
    source rest (by simpa only [SharedDetectorData.healthyTags, List.map_nil, List.nil_append, List.length_nil] using query)
    (by omega) cursorHead (by omega) exhaustedAt

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4096 in
theorem execution (parameters : Parameters) (raw : parameters.layout = .raw) (drive : parameters.drive = true)
    (graph : DAG parameters.channels) (guarded : graph.Guarded) (T F : Finset (Fin parameters.channels))
    (consistent : FixedConsistent (extensionBase parameters.buses parameters.bridge.target T) F)
    (retained coordinateBase slot sourceEnd offset maskBase entry : Nat)
    (program : Program (Width parameters graph retained) 8) (rest : List (Word (Width parameters graph retained)))
    (observations : Fin graph.roots.length → Fin parameters.decoder.roots.length)
    (observationEq : ∀ position K, parameters.observations (observations position) (assignmentOfSet K) =
      graph.eval (assignmentOfSet K) graph.roots[position.val])
    (positions : List (Fin graph.roots.length)) (state : State (Width parameters graph retained) 8) (source : Nat)
    (prepared : Ready parameters graph T F retained coordinateBase slot sourceEnd offset maskBase entry program rest state source positions) :
    ∃ answer : Bool, ∃ final ticks peak,
      Execution program state final ticks peak ∧ final.halted = true ∧
      ticks ≤ positions.length * (5032 * (graph.countedSize + 1)) +
        (if answer then 55 * (selectedSize parameters).total else 0) + 5 ∧
      peak ≤ state.liveWords + 200 * (graph.countedSize + 1) + 3 * (selectedSize parameters).total ∧
      (answer = true ↔ ∃ position ∈ positions, SharedDetectorFeasibility.AtRoot parameters graph T F position) ∧
      (answer = true → Certificate.ModelCheck.check (formula parameters)
        (NativeRealizedChecked.decodeOutput final.output (compile parameters).toState.count) = true) ∧
      final.reg 4 = word (Width parameters graph retained) (if answer then 1 else 0) := by
  induction positions generalizing state source with
  | nil =>
    obtain ⟨final, trace, halted, decision, heap, stack, output⟩ :=
      empty parameters graph T F retained coordinateBase slot sourceEnd offset maskBase entry program rest state source prepared
    refine ⟨false, final, 5, state.liveWords, trace, halted, ?_, ?_, ?_, ?_, ?_⟩
    · simp
    · omega
    · simp
    · intro impossible; cases impossible
    · simpa only [Bool.false_eq_true, ↓reduceIte] using decision
  | cons position positions ih =>
    obtain ⟨answer, middle, ticks, peak, trace, halted, time, memory, meaning, checked, continued, live, accepted⟩ :=
      step parameters raw drive graph guarded T F consistent retained coordinateBase slot sourceEnd offset maskBase entry
        program rest state source position positions (observations position) (observationEq position) prepared
    cases answer with
    | true =>
      refine ⟨true, middle, ticks, peak, trace, halted, ?_, memory, ?_, checked, ?_⟩
      · simp only [List.length_cons, Nat.add_mul, Nat.one_mul, ↓reduceIte]
        simp only [↓reduceIte] at time
        omega
      · constructor
        · intro _; exact ⟨position, List.mem_cons_self, meaning.mp rfl⟩
        · intro _; rfl
      · simpa only [↓reduceIte] using accepted rfl
    | false =>
      obtain ⟨result, final, tailTicks, tailPeak, tailTrace, tailHalted, tailTime, tailMemory, tailMeaning, tailChecked,
        tailDecision⟩ := ih middle (source + 1) (continued rfl)
      refine ⟨result, final, ticks + tailTicks, max peak tailPeak, trace.append tailTrace, tailHalted, ?_, ?_, ?_, tailChecked,
        tailDecision⟩
      · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at time
        simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
        omega
      · have liveBound := live rfl
        apply max_le <;> omega
      · constructor
        · intro accepted
          obtain ⟨next, member, feasible⟩ := tailMeaning.mp accepted
          exact ⟨next, List.mem_cons_of_mem position member, feasible⟩
        · rintro ⟨next, member, feasible⟩
          rcases List.mem_cons.mp member with same | member
          · subst next
            have impossible := meaning.mpr feasible
            contradiction
          · exact tailMeaning.mpr ⟨next, member, feasible⟩

end Controller.Cost.SharedDetectorLoop
