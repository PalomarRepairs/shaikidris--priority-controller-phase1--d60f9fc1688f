module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.EnumerationFixedQuery

@[expose] public section

/-! The complete fixed source constructor, including optional nonemptiness.
Runtime unit masks determine data, while header/directory, base emission,
slot branches and optional-row dispatch occupy one immutable program. -/
namespace Controller.Cost.EnumerationFixedConstructor
open Controller.CNF Controller.Cost.GateProgram Controller.Cost.ForestZeroTouch
open Controller.Cost.ForestZeroEmit Controller.Cost.ForestZeroDictionary
open Controller.Cost.ForestZeroCompile Controller.Cost.ForestZeroRows
open Controller.Cost.ForestZeroAssembly Controller.Cost.EnumerationSlotBatch
open Controller.Cost.ForestZeroAdmissibleCaller
open Controller.Cost.ForestZeroAdmissible

def references (baseRefs : List (List (Reference ambient))) (slots : List (Slot ambient))
    (trueFlags falseFlags : Slot ambient → Bool) : List (List (Reference ambient)) :=
  baseRefs ++ EnumerationFixedProfile.selectedRefs slots trueFlags falseFlags

@[simp] theorem references_length (baseRefs : List (List (Reference ambient))) (slots : List (Slot ambient)) :
    (references baseRefs slots trueFlags falseFlags).length = baseRefs.length + slots.length := by
  simp [references, EnumerationFixedProfile.selectedRefs]

theorem reserved_eq (baseRefs : List (List (Reference ambient))) (slots : List (Slot ambient)) :
    reservedReferences (references baseRefs slots trueFlags falseFlags) =
      EnumerationFixedProfile.references baseRefs slots trueFlags falseFlags := rfl

def code (width base keep returnPc : Nat)
    (baseRefs : List (List (Reference ambient))) (slots : List (Slot ambient)) : Code width :=
  let query := EnumerationFixedQuery.code width base keep baseRefs slots
  query ++ ForestZeroAdmissibleCaller.code width (base + query.length) keep (keep + 4) returnPc

theorem code_bound (baseRefs : List (List (Reference ambient))) (slots : List (Slot ambient)) :
    (code width base keep returnPc baseRefs slots).length ≤
      97 + 5 * (baseRefs.length + slots.length + 1) + 28 * baseRefs.flatten.length + 90 * slots.length := by
  have query := EnumerationFixedQuery.code_bound (width := width) (base := base) (keep := keep) baseRefs slots
  simp only [code, List.length_append, ForestZeroAdmissibleCaller.code_length]
  omega

set_option maxHeartbeats 8000000 in
theorem execution (program : Program width 4) (trueFlags falseFlags : Slot ambient → Bool)
    (heap : Array (Word width)) (layout : Layout ambient heap.size) (dictionary : Dictionary ambient)
    (represented : Represented heap layout dictionary) (channels sourceEnd : Nat)
    (baseRefs : List (List (Reference ambient))) (slots : List (Slot ambient))
    (sourceBound : sourceEnd ≤ heap.size) (sourcePositive : 0 < sourceEnd)
    (channelCell : heap[0]? = some (word width channels)) (within : channels ≤ ambient)
    (baseStored : ∀ reference ∈ baseRefs.flatten, StoredReference heap channels sourceEnd reference)
    (slotStored : ∀ slot ∈ slots, StoredReference heap channels sourceEnd slot.positive ∧
      StoredReference heap channels sourceEnd slot.negative ∧ StoredReference heap channels sourceEnd slot.inactive)
    (maskBounds : ∀ slot ∈ slots, slot.trueMask < sourceEnd ∧ slot.falseMask < sourceEnd)
    (maskCells : ∀ slot ∈ slots, heap[slot.trueMask]? = some (boolWord width (trueFlags slot)) ∧
      heap[slot.falseMask]? = some (boolWord width (falseFlags slot)))
    (beforeTable : sourceEnd ≤ layout.tableBase) (beforeInverse : sourceEnd ≤ layout.inverseBase)
    (base returnPc : Nat) (stack output : List (Word width)) (widthPositive : 0 < width)
    (room : heap.size + 5 + 2 * (baseRefs.length + slots.length + 1) +
      2 * baseRefs.flatten.length + 2 * slots.length + 2 * ambient < 2 ^ width)
    (ambientFits : ambient + 1 < 2 ^ width)
    (programFits : base + (code width base heap.size returnPc baseRefs slots).length < 2 ^ width)
    (block : BlockAt program base (code width base heap.size returnPc baseRefs slots)) :
    let refs := reservedReferences (references baseRefs slots trueFlags falseFlags)
    let prepared := ForestZeroQueryCaller.queryHeap heap layout dictionary refs 0
    let emitted := ForestZeroQueryCaller.queryEmission heap layout dictionary refs 0
    let found := ForestZeroNonempty.search emitted.dictionary (emitted.dictionary.coordinates.size + 1) channels 0
    let covered := found.reason = .covered
    let slot := heap.size + 5 + 2 * (baseRefs.length + slots.length)
    let installed := boundaryHeap
      (ForestZeroPositive.pairHeap prepared (ForestZeroPositive.channelLabels emitted.dictionary channels))
      slot prepared.size (prepared.size + 2 * channels)
    let finalHeap := if covered then activeHeap installed heap.size (heap.size + 4)
      (prepared.size + 2 * channels) (slot + 2)
      else activeHeap prepared heap.size (heap.size + 4) prepared.size slot
    ∃ ticks peak, Execution program
      (atState heap base (heap.size + 5 + 2 * (baseRefs.length + slots.length + 1))
        layout.tableBase dictionary.coordinates.size 0 (word width layout.inverseBase :: stack) output)
      (atState finalHeap returnPc (if covered then slot + 2 else slot)
        (if covered then prepared.size + 2 * channels else prepared.size) emitted.dictionary.coordinates.size 0
        (word width layout.inverseBase :: stack) output)
      ticks peak ∧ ticks ≤ 79 + 5 * (baseRefs.length + slots.length) +
        23 * baseRefs.flatten.length + 31 * slots.length + 23 * emitted.dictionary.coordinates.size ∧
      peak ≤ 14 + heap.size + 2 * (baseRefs.length + slots.length + 1) +
        2 * baseRefs.flatten.length + 2 * slots.length + 2 * emitted.dictionary.coordinates.size + stack.length + output.length := by
  let refs := EnumerationFixedProfile.references baseRefs slots trueFlags falseFlags
  let query := EnumerationFixedQuery.code width base heap.size baseRefs slots
  let optionalBase := base + query.length
  let prepared := ForestZeroQueryCaller.queryHeap heap layout dictionary refs 0
  let emitted := ForestZeroQueryCaller.queryEmission heap layout dictionary refs 0
  let extended := constructedLayout heap layout dictionary refs 0
  let slot := heap.size + 5 + 2 * (baseRefs.length + slots.length)
  have lengthEq : (code width base heap.size returnPc baseRefs slots).length = query.length + 81 := by
    simp [code, query]
  have fullCapacity := programFits
  rw [lengthEq] at fullCapacity
  dsimp only [query] at fullCapacity
  have queryAt := BlockAt.prefix program base _ _ block
  have optionalAt := BlockAt.suffix program base _ _ block
  have preparedSize : prepared.size = heap.size + 5 + 2 * (baseRefs.length + slots.length + 1) +
      2 * baseRefs.flatten.length + 2 * slots.length := by
    simp only [prepared, ForestZeroQueryCaller.queryHeap_size, refs, EnumerationFixedProfile.references_length,
      EnumerationFixedProfile.references_literals, Nat.mul_add]
    omega
  have actual := constructed_represented heap layout dictionary represented refs 0
  have firstCell := ForestZeroQueryCaller.query_header_cell heap layout dictionary represented refs 0 0 (by decide) (by decide)
  have lastCell := ForestZeroQueryCaller.query_header_cell heap layout dictionary represented refs 0 4 (by decide) (by decide)
  have sourceCell : prepared[heap.size]? = some (word width prepared.size) := by
    simpa only [prepared, refs, ForestZeroQueryCaller.headerValues, EnumerationFixedProfile.references_length,
      EnumerationFixedProfile.references_literals, List.getElem_cons_zero, Nat.add_zero, preparedSize, Nat.mul_add,
      Nat.add_assoc] using firstCell
  have directoryCell : prepared[heap.size + 4]? = some (word width (slot + 2)) := by
    simpa [prepared, refs, slot, ForestZeroQueryCaller.headerValues, Nat.mul_add, Nat.add_assoc] using lastCell
  have preservedChannel : prepared[0]? = some (word width channels) :=
    (query_original_cell heap layout dictionary refs 0 sourceEnd 0 beforeTable beforeInverse sourcePositive sourceBound).trans channelCell
  obtain ⟨queryTicks, queryPeak, queryTrace, queryTime, querySpace⟩ := EnumerationFixedQuery.execution program trueFlags falseFlags
    heap layout dictionary represented channels sourceEnd baseRefs slots sourceBound baseStored slotStored maskBounds maskCells
    beforeTable beforeInverse base stack output widthPositive (by omega) ambientFits
    (by omega) queryAt
  have queryTrace' : Execution program
      (atState heap base (heap.size + 5 + 2 * (baseRefs.length + slots.length + 1))
        layout.tableBase dictionary.coordinates.size 0 (word width layout.inverseBase :: stack) output)
      (atState prepared optionalBase (heap.size + 1) layout.tableBase emitted.dictionary.coordinates.size
        (EnumerationFixedQuery.emission trueFlags falseFlags heap layout dictionary baseRefs slots).scratch
        (word width layout.inverseBase :: stack) output) queryTicks queryPeak := by
    simpa only [EnumerationFixedQuery.queryHeap_eq, EnumerationFixedQuery.emission_dictionary,
      prepared, emitted, optionalBase, query, refs] using queryTrace
  obtain ⟨bodyTicks, bodyPeak, bodyTrace, bodyTime, bodySpace⟩ := ForestZeroAdmissibleCaller.execution
    program prepared extended emitted.dictionary actual optionalBase heap.size (heap.size + 4) returnPc prepared.size slot
    channels (heap.size + 1) (EnumerationFixedQuery.emission trueFlags falseFlags heap layout dictionary baseRefs slots).scratch
    (word width layout.inverseBase :: stack) output within (by rw [preparedSize]; omega) preservedChannel
    (by rw [preparedSize]; omega) (by rw [preparedSize]; omega) (by omega) (by omega)
    sourceCell directoryCell (by rw [preparedSize]; dsimp only [slot]; omega) (by dsimp only [slot]; omega)
    le_rfl (by rw [preparedSize]; omega) ambientFits
    (by dsimp only [optionalBase, query]; omega) optionalAt
  refine ⟨queryTicks + bodyTicks, max queryPeak bodyPeak, ?_, ?_, ?_⟩
  · convert queryTrace'.append bodyTrace using 1
    simp only [reserved_eq, refs, prepared, emitted, slot]
    all_goals rfl
  · change queryTicks + bodyTicks ≤ 79 + 5 * (baseRefs.length + slots.length) +
      23 * baseRefs.flatten.length + 31 * slots.length + 23 * emitted.dictionary.coordinates.size
    omega
  · change max queryPeak bodyPeak ≤ 14 + heap.size + 2 * (baseRefs.length + slots.length + 1) +
      2 * baseRefs.flatten.length + 2 * slots.length + 2 * emitted.dictionary.coordinates.size + stack.length + output.length
    simp only [List.length_cons] at bodySpace
    rw [preparedSize] at bodySpace
    omega

end Controller.Cost.EnumerationFixedConstructor
