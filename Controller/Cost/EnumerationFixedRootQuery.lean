module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.EnumerationFixedGraph
public import Controller.Cost.SharedZeroResidentConditions

@[expose] public section

/-! An exact fixed resident zero query with physically stored prefix masks. -/
namespace Controller.Cost.EnumerationFixedRootQuery
open Controller.CNF Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestZeroTouch
open Controller.Cost.GateProgram Controller.Cost.ForestZeroEmit Controller.Cost.ForestZeroDictionary
open Controller.Cost.ForestZeroCompile Controller.Cost.ForestZeroAdmissibleCaller
open Controller.Native Controller.Native.SourceController Controller.Cost.NativeSourceExecution
open Controller.Cost.EnumerationFixedCapacity Controller.Cost.SharedZeroResidentConditions

structure MaskCells (parameters : Parameters) (heap : Array (Word width))
    (coordinateBase trueBase falseBase sourceEnd : Nat) (T F : Finset (Fin parameters.channels)) : Prop where
  coordinateBound : coordinateBase + parameters.channels ≤ sourceEnd
  trueBound : trueBase + parameters.channels ≤ sourceEnd
  falseBound : falseBase + parameters.channels ≤ sourceEnd
  coordinates : ∀ channel : Fin parameters.channels, heap[coordinateBase + channel.val]? = some (word width channel.val)
  trueCells : ∀ channel : Fin parameters.channels, heap[trueBase + channel.val]? = some (boolWord width (decide (channel ∈ T)))
  falseCells : ∀ channel : Fin parameters.channels, heap[falseBase + channel.val]? = some (boolWord width (decide (channel ∈ F)))

def code (parameters : Parameters) (graph : DAG parameters.channels) (width entry keep : Nat)
    (coordinateBase rootSlot trueBase falseBase : Nat) (root : Fin graph.nodeCount) : List (Instruction width 8) :=
  EnumerationFixedResident.code width entry keep parameters.channels
    (baseRows parameters graph coordinateBase rootSlot root)
    (slots parameters graph coordinateBase rootSlot trueBase falseBase root)

def returnEntry (parameters : Parameters) (graph : DAG parameters.channels) (width entry keep : Nat)
    (coordinateBase rootSlot trueBase falseBase : Nat) (root : Fin graph.nodeCount) : Nat :=
  EnumerationFixedResident.solverEntry width entry keep (baseRows parameters graph coordinateBase rootSlot root)
    (slots parameters graph coordinateBase rootSlot trueBase falseBase root) + 430

theorem root_irrel (parameters : Parameters) (graph : DAG parameters.channels) (left right : Fin graph.nodeCount) :
    code parameters graph width entry keep coordinateBase rootSlot trueBase falseBase left =
    code parameters graph width entry keep coordinateBase rootSlot trueBase falseBase right :=
  EnumerationFixedGraph.resident_root_irrel parameters graph left right

theorem return_root_irrel (parameters : Parameters) (graph : DAG parameters.channels) (left right : Fin graph.nodeCount) :
    returnEntry parameters graph width entry keep coordinateBase rootSlot trueBase falseBase left =
    returnEntry parameters graph width entry keep coordinateBase rootSlot trueBase falseBase right := by
  unfold returnEntry
  rw [EnumerationFixedGraph.solver_entry_root_irrel parameters graph left right]

theorem code_end (parameters : Parameters) (graph : DAG parameters.channels) (root : Fin graph.nodeCount) :
    entry + (code parameters graph width entry keep coordinateBase rootSlot trueBase falseBase root).length =
    returnEntry parameters graph width entry keep coordinateBase rootSlot trueBase falseBase root :=
  EnumerationFixedResident.code_end _ _

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in
theorem conditions (parameters : Parameters) (graph : DAG parameters.channels) (guarded : graph.Guarded)
    (T F : Finset (Fin parameters.channels)) (root : Fin graph.nodeCount)
    (program : Program (SharedMachineCapacity.wordWidth retained graph.countedSize (selectedSize parameters).total) 8)
    (state : State (SharedMachineCapacity.wordWidth retained graph.countedSize (selectedSize parameters).total) 8)
    (layout : Layout (parameters.channels + graph.nodeCount) state.heap.size)
    (coordinateBase rootSlot trueBase falseBase sourceEnd entry : Nat)
    (rest : List (Word (SharedMachineCapacity.wordWidth retained graph.countedSize (selectedSize parameters).total)))
    (source : SourceConditions parameters state layout (baseRows parameters graph coordinateBase rootSlot root) sourceEnd graph.nodeCount)
    (masks : MaskCells parameters state.heap coordinateBase trueBase falseBase sourceEnd T F)
    (heapBound : state.heap.size ≤ retained) (entryBound : entry ≤ retained) :
    EnumerationFixedExecution.Conditions parameters.channels program state layout
      (EnumerationFixedGraph.references parameters graph root T F coordinateBase rootSlot trueBase falseBase)
      (baseRows parameters graph coordinateBase rootSlot root) (slots parameters graph coordinateBase rootSlot trueBase falseBase root)
      (EnumerationSlotSource.trueFlags trueBase T) (EnumerationSlotSource.falseFlags falseBase F)
      sourceEnd graph.nodeCount entry rest (by omega) := by
  have rootStored : StoredReference state.heap parameters.channels sourceEnd
      (SharedZeroCode.rootReference parameters.channels graph.nodeCount rootSlot root) :=
    source.sourceReferences _ (by simp [baseRows, SharedZeroSource.references])
  refine {
    selectedRefs := rfl
    touched := EnumerationFixedResident.graph_base_touches graph parameters.buses parameters.bridge.target root
    baseStored := source.sourceReferences
    slotStored := ?_
    maskBounds := ?_
    maskCells := ?_
    sourceBeforeTable := source.sourceBeforeTable
    sourceBeforeInverse := source.sourceBeforeInverse
    sourceBound := source.sourceBound
    sourcePositive := source.sourcePositive
    sourceChannel := source.sourceChannel
    sourceNodes := source.sourceNodes
    ambientEq := rfl
    adjacent := source.adjacent
    tablePositive := source.tablePositive
    sourceHeaderRoom := source.sourceHeaderRoom
    sourceDual := EnumerationFixedGraph.source_dual parameters graph guarded root T F
    sourceEndpoint := source.sourceEndpoint
    constructorRoom := EnumerationFixedCapacity.selected_room parameters graph root state.heap _ _ heapBound
    room := ?_
    residentCapacity := ?_ }
  · intro slot member
    obtain ⟨channel, _, rfl⟩ := List.mem_map.mp member
    exact EnumerationSlotSource.slot_stored state.heap root channel source.sourceBound masks.coordinateBound
      rootStored.slotBound source.sourcePositive source.sourceChannel (masks.coordinates channel) rootStored.slotWord
  · intro slot member
    obtain ⟨channel, _, rfl⟩ := List.mem_map.mp member
    have channelBound := channel.isLt
    exact ⟨by change trueBase + channel.val < sourceEnd; have := masks.trueBound; omega,
      by change falseBase + channel.val < sourceEnd; have := masks.falseBound; omega⟩
  · intro slot member
    obtain ⟨channel, _, rfl⟩ := List.mem_map.mp member
    constructor
    · rw [EnumerationSlotSource.trueFlags_channel]
      exact masks.trueCells channel
    · rw [EnumerationSlotSource.falseFlags_channel]
      exact masks.falseCells channel
  · simpa only [constructorState, RegisterWiden.widenState, atState, constructorFormula_rows] using
      EnumerationFixedCapacity.scratch_room parameters graph root state.heap layout _ _ heapBound
  · have room := EnumerationFixedCapacity.resident_room (sourceBase := coordinateBase) (rootSlot := rootSlot)
      (trueBase := trueBase) (falseBase := falseBase) parameters graph root state.heap.size entry entryBound
    rw [EnumerationFixedResident.code_end] at room
    exact room

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in
theorem execution (parameters : Parameters) (graph : DAG parameters.channels) (guarded : graph.Guarded)
    (T F : Finset (Fin parameters.channels)) (consistent : Disjoint T F) (root : Fin graph.nodeCount)
    (program : Program (SharedMachineCapacity.wordWidth retained graph.countedSize (selectedSize parameters).total) 8)
    (state : State (SharedMachineCapacity.wordWidth retained graph.countedSize (selectedSize parameters).total) 8)
    (sourceHeap : Array (Word (SharedMachineCapacity.wordWidth retained graph.countedSize (selectedSize parameters).total)))
    (layout : Layout (parameters.channels + graph.nodeCount) state.heap.size)
    (coordinateBase rootSlot trueBase falseBase sourceEnd entry : Nat)
    (rest : List (Word (SharedMachineCapacity.wordWidth retained graph.countedSize (selectedSize parameters).total)))
    (source : SourceConditions parameters state layout (baseRows parameters graph coordinateBase rootSlot root) sourceEnd graph.nodeCount)
    (masks : MaskCells parameters state.heap coordinateBase trueBase falseBase sourceEnd T F)
    (heapBound : state.heap.size ≤ retained) (entryBound : entry ≤ retained)
    (present : SharedRootRead.BlockAt program entry
      (code parameters graph (SharedMachineCapacity.wordWidth retained graph.countedSize (selectedSize parameters).total) entry state.heap.size coordinateBase rootSlot trueBase falseBase root))
    (ready : QueryReady (ambient := parameters.channels + graph.nodeCount) sourceHeap layout.tableBase layout.inverseBase entry rest state) :
    ∃ answer : Bool, ∃ final ticks peak,
      Execution program state final ticks peak ∧ final.halted = false ∧
      final.reg 4 = word (SharedMachineCapacity.wordWidth retained graph.countedSize (selectedSize parameters).total) (if answer then 1 else 0) ∧
      ticks ≤ 5200 * (graph.countedSize + 1) ∧ peak ≤ state.liveWords + 200 * (graph.countedSize + 1) ∧
      final.output = state.output ∧
      (answer = true ↔ ∃ K, Admissible parameters.buses parameters.bridge.target K ∧ ExtendsFixed T F K ∧
        graph.eval (assignmentOfSet K) root = false) ∧
      QueryReady (ambient := parameters.channels + graph.nodeCount) sourceHeap layout.tableBase layout.inverseBase
        (returnEntry parameters graph (SharedMachineCapacity.wordWidth retained graph.countedSize (selectedSize parameters).total) entry state.heap.size coordinateBase rootSlot trueBase falseBase root) rest final := by
  have inputConditions := conditions parameters graph guarded T F root program state layout coordinateBase rootSlot
    trueBase falseBase sourceEnd entry rest source masks heapBound entryBound
  obtain ⟨answer, final, ticks, peak, trace, running, decision, time, space, output, meaning, finalReady⟩ :=
    EnumerationFixedExecution.execution parameters.channels program state sourceHeap layout _ _ _ _ _ sourceEnd graph.nodeCount entry
      rest (by omega) inputConditions present ready
  have semantic := EnumerationFixedGraph.constructor_meaning (sourceBase := coordinateBase) (rootSlot := rootSlot)
    (trueBase := trueBase) (falseBase := falseBase) parameters graph guarded root T F consistent state.heap layout
  have profile := SharedZeroSource.occurrence_bound (base := coordinateBase) (slot := rootSlot)
    graph parameters.buses parameters.bridge.target ∅ ∅ root
  have rowsCount := EnumerationFixedConstructor.references_length
    (baseRows parameters graph coordinateBase rootSlot root) (slots parameters graph coordinateBase rootSlot trueBase falseBase root)
    (trueFlags := EnumerationSlotSource.trueFlags trueBase T) (falseFlags := EnumerationSlotSource.falseFlags falseBase F)
  have literalCount := EnumerationFixedResident.selected_literals
    (baseRows parameters graph coordinateBase rootSlot root) (slots parameters graph coordinateBase rootSlot trueBase falseBase root)
    (yes := EnumerationSlotSource.trueFlags trueBase T) (no := EnumerationSlotSource.falseFlags falseBase F)
  have masksCount := EnumerationSlotSource.slots_length (n := parameters.channels) (sourceBase := coordinateBase)
    (rootSlot := rootSlot) (trueBase := trueBase) (falseBase := falseBase) root
  have graphSize := graph.countedSize_eq
  refine ⟨answer, final, ticks, peak, trace, running, decision, ?_, ?_, output, meaning.trans semantic, finalReady⟩
  · change ticks ≤ _ at time
    simp only [EnumerationFixedGraph.references, EnumerationFixedResident.selected,
      EnumerationFixedConstructor.references_length, EnumerationFixedResident.selected_literals,
      slots, EnumerationSlotSource.slots_length] at time
    change (baseRows parameters graph coordinateBase rootSlot root).length +
      (baseRows parameters graph coordinateBase rootSlot root).flatten.length ≤ 11 * (graph.countedSize + 1) at profile
    omega
  · simp only [EnumerationFixedGraph.references, EnumerationFixedResident.selected,
      EnumerationFixedConstructor.references_length, EnumerationFixedResident.selected_literals,
      slots, EnumerationSlotSource.slots_length] at space
    change (baseRows parameters graph coordinateBase rootSlot root).length +
      (baseRows parameters graph coordinateBase rootSlot root).flatten.length ≤ 11 * (graph.countedSize + 1) at profile
    omega

end Controller.Cost.EnumerationFixedRootQuery
