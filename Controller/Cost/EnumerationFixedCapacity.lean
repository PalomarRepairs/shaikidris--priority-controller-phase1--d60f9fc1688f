module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.EnumerationFixedExecution
public import Controller.Cost.EnumerationSlotSource
public import Controller.Cost.SharedMachineCapacity

@[expose] public section

/-! Graph-specific word capacities for the fixed runtime-slot decision query.
The retained heap/entry bounds and counted graph size instantiate the existing
word-width formula uniformly over the prefix masks. -/
namespace Controller.Cost.EnumerationFixedCapacity
open Controller.Cost.GateProgram Controller.Native Controller.Native.SourceController
open Controller.Cost.NativeSourceExecution Controller.Decoder
open Controller.Cost.SharedMachineCapacity Controller.Cost.ForestZeroAdmissibleCaller
open Controller.Cost.ForestZeroCompile Controller.Cost.EnumerationFixedResident

abbrev baseRows (parameters : Parameters) (graph : DAG parameters.channels)
    (sourceBase rootSlot : Nat) (root : Fin graph.nodeCount) :=
  SharedZeroSource.references graph parameters.buses parameters.bridge.target ∅ ∅ sourceBase rootSlot root

abbrev slots (parameters : Parameters) (graph : DAG parameters.channels)
    (sourceBase rootSlot trueBase falseBase : Nat) (root : Fin graph.nodeCount) :=
  EnumerationSlotSource.slots (n := parameters.channels) graph.nodeCount sourceBase rootSlot trueBase falseBase root

theorem constructor_room (parameters : Parameters) (graph : DAG parameters.channels) (root : Fin graph.nodeCount)
    (heap : Array (Word (wordWidth retained graph.countedSize (selectedSize parameters).total)))
    (size : heap.size ≤ retained) :
    let base := baseRows parameters graph sourceBase rootSlot root
    let masks := slots parameters graph sourceBase rootSlot trueBase falseBase root
    heap.size + 5 + 2 * (base.length + masks.length + 1) +
      2 * base.flatten.length + 2 * masks.length + 2 * (parameters.channels + graph.nodeCount) <
      2 ^ wordWidth retained graph.countedSize (selectedSize parameters).total := by
  intro base masks
  have profile := SharedZeroSource.occurrence_bound (base := sourceBase) (slot := rootSlot)
    graph parameters.buses parameters.bridge.target ∅ ∅ root
  change base.length + base.flatten.length ≤ 11 * (graph.countedSize + 1) at profile
  have masksLength : masks.length = parameters.channels := EnumerationSlotSource.slots_length root
  have graphSize := graph.countedSize_eq
  have room := capacity retained graph.countedSize (selectedSize parameters).total
  omega

theorem backend_room (parameters : Parameters) (graph : DAG parameters.channels) (root : Fin graph.nodeCount)
    (heap : Array (Word (wordWidth retained graph.countedSize (selectedSize parameters).total)))
    (size : heap.size ≤ retained) :
    let base := baseRows parameters graph sourceBase rootSlot root
    let masks := slots parameters graph sourceBase rootSlot trueBase falseBase root
    heapSize heap.size parameters.channels base masks + 5 * (parameters.channels + graph.nodeCount) + 4 +
      3 * (base.length + masks.length + 1) +
      3 * (base.flatten.length + masks.length + (parameters.channels + graph.nodeCount)) <
      2 ^ wordWidth retained graph.countedSize (selectedSize parameters).total := by
  intro base masks
  have upper := heap_size_bound (keep := heap.size) (channels := parameters.channels) base masks
  have profile := SharedZeroSource.occurrence_bound (base := sourceBase) (slot := rootSlot)
    graph parameters.buses parameters.bridge.target ∅ ∅ root
  change base.length + base.flatten.length ≤ 11 * (graph.countedSize + 1) at profile
  have masksLength : masks.length = parameters.channels := EnumerationSlotSource.slots_length root
  have graphSize := graph.countedSize_eq
  have room := capacity retained graph.countedSize (selectedSize parameters).total
  omega

theorem code_bound (parameters : Parameters) (graph : DAG parameters.channels) (root : Fin graph.nodeCount)
    (width entry keep : Nat) :
    (EnumerationFixedResident.code width entry keep parameters.channels
      (baseRows parameters graph sourceBase rootSlot root)
      (slots parameters graph sourceBase rootSlot trueBase falseBase root)).length ≤
      403 * (graph.countedSize + 1) + 547 := by
  have upper := EnumerationFixedResident.code_bound (width := width) (entry := entry) (keep := keep)
    (channels := parameters.channels) (baseRows parameters graph sourceBase rootSlot root)
    (slots parameters graph sourceBase rootSlot trueBase falseBase root)
  have profile := SharedZeroSource.occurrence_bound (base := sourceBase) (slot := rootSlot)
    graph parameters.buses parameters.bridge.target ∅ ∅ root
  have masksLength := EnumerationSlotSource.slots_length (n := parameters.channels)
    (sourceBase := sourceBase) (rootSlot := rootSlot) (trueBase := trueBase) (falseBase := falseBase) root
  change (slots parameters graph sourceBase rootSlot trueBase falseBase root).length = parameters.channels at masksLength
  change (baseRows parameters graph sourceBase rootSlot root).length +
    (baseRows parameters graph sourceBase rootSlot root).flatten.length ≤ 11 * (graph.countedSize + 1) at profile
  have graphSize := graph.countedSize_eq
  omega

theorem resident_room (parameters : Parameters) (graph : DAG parameters.channels) (root : Fin graph.nodeCount)
    (keep entry : Nat) (entryBound : entry ≤ retained) :
    entry + (EnumerationFixedResident.code
      (wordWidth retained graph.countedSize (selectedSize parameters).total) entry keep parameters.channels
      (baseRows parameters graph sourceBase rootSlot root)
      (slots parameters graph sourceBase rootSlot trueBase falseBase root)).length <
      2 ^ wordWidth retained graph.countedSize (selectedSize parameters).total := by
  have upper := code_bound (sourceBase := sourceBase) (rootSlot := rootSlot)
    (trueBase := trueBase) (falseBase := falseBase) parameters graph root
    (wordWidth retained graph.countedSize (selectedSize parameters).total) entry keep
  have room := capacity retained graph.countedSize (selectedSize parameters).total
  omega

/-- The selected reference stream satisfies the exact constructor capacity premise. -/
theorem selected_room (parameters : Parameters) (graph : DAG parameters.channels) (root : Fin graph.nodeCount)
    (heap : Array (Word (wordWidth retained graph.countedSize (selectedSize parameters).total)))
    (yes no : EnumerationSlotBatch.Slot (parameters.channels + graph.nodeCount) → Bool)
    (size : heap.size ≤ retained) :
    let refs := EnumerationFixedResident.selected (baseRows parameters graph sourceBase rootSlot root)
      (slots parameters graph sourceBase rootSlot trueBase falseBase root) yes no
    heap.size + 5 + 2 * (refs.length + 1) + 2 * refs.flatten.length +
      2 * (parameters.channels + graph.nodeCount) <
      2 ^ wordWidth retained graph.countedSize (selectedSize parameters).total := by
  intro refs
  have bound := constructor_room (sourceBase := sourceBase) (rootSlot := rootSlot)
    (trueBase := trueBase) (falseBase := falseBase) parameters graph root heap size
  dsimp only [refs]
  rw [EnumerationFixedConstructor.references_length, selected_literals]
  omega

/-- The actual selected clauses and indexed scratch region fit for every mask. -/
theorem scratch_room (parameters : Parameters) (graph : DAG parameters.channels) (root : Fin graph.nodeCount)
    (heap : Array (Word (wordWidth retained graph.countedSize (selectedSize parameters).total)))
    (layout : ForestZeroDictionary.Layout (parameters.channels + graph.nodeCount) heap.size)
    (yes no : EnumerationSlotBatch.Slot (parameters.channels + graph.nodeCount) → Bool)
    (size : heap.size ≤ retained) :
    let refs := EnumerationFixedResident.selected (baseRows parameters graph sourceBase rootSlot root)
      (slots parameters graph sourceBase rootSlot trueBase falseBase root) yes no
    let dictionary := constructorDictionary heap layout (empty _) refs
    let rows := constructorClauses heap layout (empty _) (empty_coherent _) refs parameters.channels (by omega)
    let start := (constructorHeap heap layout (empty _) refs parameters.channels).size +
      5 * dictionary.coordinates.size + 4
    start + 3 * rows.length + (rows.map List.length).sum +
      2 * (Controller.Horn.IndexScan.occurrences rows start).length <
      2 ^ wordWidth retained graph.countedSize (selectedSize parameters).total := by
  intro refs dictionary rows start
  exact backend_heap_capacity (baseRows parameters graph sourceBase rootSlot root)
    (slots parameters graph sourceBase rootSlot trueBase falseBase root)
    (graph_base_touches graph parameters.buses parameters.bridge.target root) yes no heap layout
    parameters.channels (by omega) start
    (backend_room (sourceBase := sourceBase) (rootSlot := rootSlot)
      (trueBase := trueBase) (falseBase := falseBase) parameters graph root heap size)

end Controller.Cost.EnumerationFixedCapacity
