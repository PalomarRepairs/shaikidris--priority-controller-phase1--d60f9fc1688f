module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.EnumerationFixedAssembly

@[expose] public section

/-! Header, fixed directory/base rows, runtime slots and the physical local-count
store form one prefix-independent query constructor. Its heap equals the R04
query heap for the selected rows, including the reserved empty row. -/
namespace Controller.Cost.EnumerationFixedQuery
open Controller.CNF Controller.Cost.GateProgram Controller.Cost.ForestZeroTouch
open Controller.Cost.ForestZeroEmit Controller.Cost.ForestZeroDictionary
open Controller.Cost.ForestZeroCompile Controller.Cost.ForestZeroRows
open Controller.Cost.ForestZeroAssembly Controller.Cost.EnumerationSlotBatch
open Controller.Cost.ForestZeroQueryCaller

def code (width base keep : Nat) (baseRefs : List (List (Reference ambient))) (slots : List (Slot ambient)) : Code width :=
  preservingHeaderCode width keep (baseRefs.length + slots.length + 1) (baseRefs.flatten.length + slots.length) ++
    (EnumerationFixedAssembly.code width (base + 12) baseRefs slots ++ countCode width (keep + 1))

def emission (trueFlags falseFlags : Slot ambient → Bool) (heap : Array (Word width))
    (layout : Layout ambient heap.size) (dictionary : Dictionary ambient)
    (baseRefs : List (List (Reference ambient))) (slots : List (Slot ambient)) : Result ambient width :=
  EnumerationFixedAssembly.result trueFlags falseFlags
    (headerHeap width heap (baseRefs.length + slots.length + 1) (baseRefs.flatten.length + slots.length))
    (headerLayout heap layout (baseRefs.length + slots.length + 1) (baseRefs.flatten.length + slots.length))
    dictionary 0 baseRefs slots

@[simp] theorem emission_size (trueFlags falseFlags : Slot ambient → Bool)
    (heap : Array (Word width)) (layout : Layout ambient heap.size) (dictionary : Dictionary ambient)
    (baseRefs : List (List (Reference ambient))) (slots : List (Slot ambient)) :
    (emission trueFlags falseFlags heap layout dictionary baseRefs slots).heap.size =
      heap.size + 5 + 2 * (baseRefs.length + slots.length + 1) + 2 * baseRefs.flatten.length + 2 * slots.length := by
  simp [emission]

def queryHeap (trueFlags falseFlags : Slot ambient → Bool) (heap : Array (Word width))
    (layout : Layout ambient heap.size) (dictionary : Dictionary ambient)
    (baseRefs : List (List (Reference ambient))) (slots : List (Slot ambient)) : Array (Word width) :=
  let emitted := emission trueFlags falseFlags heap layout dictionary baseRefs slots
  emitted.heap.set (heap.size + 1) (word width emitted.dictionary.coordinates.size)
    (by dsimp only [emitted]; rw [emission_size]; omega)

@[simp] theorem queryHeap_size (trueFlags falseFlags : Slot ambient → Bool)
    (heap : Array (Word width)) (layout : Layout ambient heap.size) (dictionary : Dictionary ambient)
    (baseRefs : List (List (Reference ambient))) (slots : List (Slot ambient)) :
    (queryHeap trueFlags falseFlags heap layout dictionary baseRefs slots).size =
      heap.size + 5 + 2 * (baseRefs.length + slots.length + 1) + 2 * baseRefs.flatten.length + 2 * slots.length := by
  simp [queryHeap]

theorem emission_heap (trueFlags falseFlags : Slot ambient → Bool)
    (heap : Array (Word width)) (layout : Layout ambient heap.size) (dictionary : Dictionary ambient)
    (baseRefs : List (List (Reference ambient))) (slots : List (Slot ambient)) :
    (emission trueFlags falseFlags heap layout dictionary baseRefs slots).heap =
      (ForestZeroQueryCaller.queryEmission heap layout dictionary
        (EnumerationFixedProfile.references baseRefs slots trueFlags falseFlags) 0).heap := by
  unfold emission
  rw [EnumerationFixedAssembly.result_heap]
  unfold ForestZeroQueryCaller.queryEmission
  rw [EnumerationFixedProfile.references_length, EnumerationFixedProfile.references_literals]

theorem emission_dictionary (trueFlags falseFlags : Slot ambient → Bool)
    (heap : Array (Word width)) (layout : Layout ambient heap.size) (dictionary : Dictionary ambient)
    (baseRefs : List (List (Reference ambient))) (slots : List (Slot ambient)) :
    (emission trueFlags falseFlags heap layout dictionary baseRefs slots).dictionary =
      (ForestZeroQueryCaller.queryEmission heap layout dictionary
        (EnumerationFixedProfile.references baseRefs slots trueFlags falseFlags) 0).dictionary := by
  unfold emission
  rw [EnumerationFixedAssembly.result_dictionary]
  unfold ForestZeroQueryCaller.queryEmission
  rw [EnumerationFixedProfile.references_length, EnumerationFixedProfile.references_literals]

theorem queryHeap_eq (trueFlags falseFlags : Slot ambient → Bool)
    (heap : Array (Word width)) (layout : Layout ambient heap.size) (dictionary : Dictionary ambient)
    (baseRefs : List (List (Reference ambient))) (slots : List (Slot ambient)) :
    queryHeap trueFlags falseFlags heap layout dictionary baseRefs slots =
      ForestZeroQueryCaller.queryHeap heap layout dictionary
        (EnumerationFixedProfile.references baseRefs slots trueFlags falseFlags) 0 := by
  simp only [queryHeap, ForestZeroQueryCaller.queryHeap, emission_heap, emission_dictionary]

theorem code_bound (baseRefs : List (List (Reference ambient))) (slots : List (Slot ambient)) :
    (code width base keep baseRefs slots).length ≤
      16 + 5 * (baseRefs.length + slots.length + 1) + 28 * baseRefs.flatten.length + 90 * slots.length := by
  have assembly := EnumerationFixedAssembly.code_bound (width := width) (base := base + 12) baseRefs slots
  simp only [code, List.length_append, preservingHeaderCode_length, countCode_length]
  omega

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
    (base : Nat) (stack output : List (Word width)) (widthPositive : 0 < width)
    (room : heap.size + 5 + 2 * (baseRefs.length + slots.length + 1) +
      2 * baseRefs.flatten.length + 2 * slots.length < 2 ^ width)
    (ambientFits : ambient + 1 < 2 ^ width)
    (programFits : base + (code width base heap.size baseRefs slots).length < 2 ^ width)
    (block : BlockAt program base (code width base heap.size baseRefs slots)) :
    let emitted := emission trueFlags falseFlags heap layout dictionary baseRefs slots
    ∃ ticks peak, Execution program
      (atState heap base (heap.size + 5 + 2 * (baseRefs.length + slots.length + 1))
        layout.tableBase dictionary.coordinates.size 0 (word width layout.inverseBase :: stack) output)
      (atState (queryHeap trueFlags falseFlags heap layout dictionary baseRefs slots)
        (base + (code width base heap.size baseRefs slots).length) (heap.size + 1)
        layout.tableBase emitted.dictionary.coordinates.size emitted.scratch
        (word width layout.inverseBase :: stack) output)
      ticks peak ∧ ticks ≤ 16 + 5 * (baseRefs.length + slots.length + 1) +
        23 * baseRefs.flatten.length + 31 * slots.length ∧
      peak ≤ 13 + heap.size + 2 * (baseRefs.length + slots.length + 1) +
        2 * baseRefs.flatten.length + 2 * slots.length + stack.length + output.length := by
  let rows := baseRefs.length + slots.length + 1
  let literals := baseRefs.flatten.length + slots.length
  let head := headerHeap width heap rows literals
  let headLayout := headerLayout heap layout rows literals
  let source := heap.size + 5 + 2 * rows
  let assemblyBase := base + 12
  let storeBase := assemblyBase + (EnumerationFixedAssembly.code width assemblyBase baseRefs slots).length
  let emitted := emission trueFlags falseFlags heap layout dictionary baseRefs slots
  have headerAt := BlockAt.prefix program base _ _ block
  have rest := BlockAt.suffix program base _ _ block
  simp only [preservingHeaderCode_length] at rest
  have assemblyAt := BlockAt.prefix program assemblyBase _ _ rest
  have countAt := BlockAt.suffix program assemblyBase _ _ rest
  have totalLength : (code width base heap.size baseRefs slots).length =
      12 + (EnumerationFixedAssembly.code width assemblyBase baseRefs slots).length + 2 := by
    simp [code, assemblyBase]
    omega
  have fullCapacity := programFits
  rw [totalLength] at fullCapacity
  dsimp only [assemblyBase] at fullCapacity
  have headerTrace := preserving_header_execution program heap base rows literals
    (word width source) (word width layout.tableBase) (word width dictionary.coordinates.size)
    (word width layout.inverseBase :: stack) output (by omega) (by omega) headerAt
  have headerTrace' : Execution program
      (atState heap base source layout.tableBase dictionary.coordinates.size 0 (word width layout.inverseBase :: stack) output)
      (atState head assemblyBase source layout.tableBase dictionary.coordinates.size 0 (word width layout.inverseBase :: stack) output)
      12 (12 + heap.size + stack.length + output.length) := by
    convert headerTrace using 1
    all_goals simp only [head, assemblyBase, atState, ForestCounter.counterState, State.frame, List.nil_append, List.length_cons]
    all_goals omega
  have retain (reference : Reference ambient) (old : StoredReference heap channels sourceEnd reference) :
      StoredReference head channels sourceEnd reference := by
    refine ⟨?_, old.slotBound, old.headerBound, ?_, ?_, old.coordinateEq⟩
    · dsimp only [head]; rw [headerHeap_size]; omega
    · exact (ForestCursorMaterialize.allocatedHeap_prefix width heap (headerValues heap.size rows literals)
        reference.slot (lt_of_lt_of_le old.slotBound old.sourceBound)).trans old.slotWord
    · exact (ForestCursorMaterialize.allocatedHeap_prefix width heap (headerValues heap.size rows literals)
        0 (lt_of_lt_of_le old.headerBound old.sourceBound)).trans old.channelWord
  have retained : ∀ slot ∈ slots, StoredReference head channels sourceEnd slot.positive ∧
      StoredReference head channels sourceEnd slot.negative ∧ StoredReference head channels sourceEnd slot.inactive := by
    intro slot member
    obtain ⟨pos, neg, inactive⟩ := slotStored slot member
    exact ⟨retain _ pos, retain _ neg, retain _ inactive⟩
  have cells : ∀ slot ∈ slots, head[slot.trueMask]? = some (boolWord width (trueFlags slot)) ∧
      head[slot.falseMask]? = some (boolWord width (falseFlags slot)) := by
    intro slot member
    obtain ⟨boundsT, boundsF⟩ := maskBounds slot member
    obtain ⟨cellsT, cellsF⟩ := maskCells slot member
    exact ⟨(ForestCursorMaterialize.allocatedHeap_prefix width heap (headerValues heap.size rows literals)
      slot.trueMask (by omega)).trans cellsT,
      (ForestCursorMaterialize.allocatedHeap_prefix width heap (headerValues heap.size rows literals)
      slot.falseMask (by omega)).trans cellsF⟩
  obtain ⟨assemblyTicks, assemblyPeak, assemblyTrace, assemblyTime, assemblySpace⟩ := EnumerationFixedAssembly.execution
    program trueFlags falseFlags head headLayout dictionary (header_represented heap layout dictionary represented rows literals)
    channels sourceEnd baseRefs slots (by dsimp only [head]; rw [headerHeap_size]; omega)
    (fun reference member => retain reference (baseStored reference member)) retained maskBounds cells beforeTable beforeInverse
    assemblyBase 0 stack output widthPositive (by dsimp only [head]; rw [headerHeap_size]; exact room) ambientFits
    (by dsimp only [assemblyBase]; omega) assemblyAt
  have assemblyTrace' : Execution program
      (atState head assemblyBase source layout.tableBase dictionary.coordinates.size 0 (word width layout.inverseBase :: stack) output)
      (atState emitted.heap storeBase emitted.input layout.tableBase emitted.dictionary.coordinates.size emitted.scratch
        (word width layout.inverseBase :: stack) output) assemblyTicks assemblyPeak := by
    simpa only [head, headLayout, source, rows, literals, emitted, emission, storeBase, headerLayout, headerHeap_size] using assemblyTrace
  have counted := count_execution program emitted.heap storeBase (heap.size + 1) emitted.input layout.tableBase
    emitted.dictionary.coordinates.size emitted.scratch (word width layout.inverseBase :: stack) output
    (by dsimp only [storeBase, assemblyBase]; omega) (by omega)
    (by dsimp only [emitted]; rw [emission_size]; omega) countAt
  refine ⟨12 + assemblyTicks + 2,
    max (max (12 + heap.size + stack.length + output.length) assemblyPeak)
      (5 + emitted.heap.size + (word width layout.inverseBase :: stack).length + output.length), ?_, ?_, ?_⟩
  · convert (headerTrace'.append assemblyTrace').append counted using 1
    simp only [queryHeap, emitted, storeBase, assemblyBase, totalLength, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  · omega
  · dsimp only [head] at assemblySpace
    rw [headerHeap_size] at assemblySpace
    dsimp only [emitted]
    rw [emission_size]
    simp only [List.length_cons]
    omega

end Controller.Cost.EnumerationFixedQuery
