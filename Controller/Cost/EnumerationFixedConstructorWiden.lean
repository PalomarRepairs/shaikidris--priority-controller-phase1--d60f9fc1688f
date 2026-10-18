module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.EnumerationFixedConstructor

@[expose] public section

/-! Complete source construction inside an arbitrary eight-register caller.
Its final heap is the existing R04 constructor heap for the selected rows,
so the stored clauses and dictionary representation are unchanged. -/
namespace Controller.Cost.EnumerationFixedConstructorWiden
open Controller.CNF Controller.Cost.GateProgram Controller.Cost.ForestZeroTouch
open Controller.Cost.ForestZeroEmit Controller.Cost.ForestZeroDictionary
open Controller.Cost.ForestZeroCompile Controller.Cost.EnumerationSlotBatch
open Controller.Cost.ForestZeroAdmissibleCaller Controller.Cost.ForestZeroAdmissible
open Controller.Cost.ForestZeroCallerWiden Controller.Cost.RegisterWiden

def initialState (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (dictionary : Dictionary ambient) (base : Nat) (baseRefs : List (List (Reference ambient)))
    (slots : List (Slot ambient)) (stack output : List (Word width)) : State width 4 :=
  atState heap base (heap.size + 5 + 2 * (baseRefs.length + slots.length + 1)) layout.tableBase
    dictionary.coordinates.size 0 (word width layout.inverseBase :: stack) output

def finalState (trueFlags falseFlags : Slot ambient → Bool) (heap : Array (Word width))
    (layout : Layout ambient heap.size) (dictionary : Dictionary ambient) (channels returnPc : Nat)
    (baseRefs : List (List (Reference ambient))) (slots : List (Slot ambient))
    (stack output : List (Word width)) : State width 4 :=
  let refs := reservedReferences (EnumerationFixedConstructor.references baseRefs slots trueFlags falseFlags)
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
  atState finalHeap returnPc (if covered then slot + 2 else slot)
    (if covered then prepared.size + 2 * channels else prepared.size) emitted.dictionary.coordinates.size 0
    (word width layout.inverseBase :: stack) output

theorem final_heap (trueFlags falseFlags : Slot ambient → Bool) (heap : Array (Word width))
    (layout : Layout ambient heap.size) (dictionary : Dictionary ambient) (channels returnPc : Nat)
    (baseRefs : List (List (Reference ambient))) (slots : List (Slot ambient)) (stack output : List (Word width)) :
    (finalState trueFlags falseFlags heap layout dictionary channels returnPc baseRefs slots stack output).heap =
      constructorHeap heap layout dictionary (EnumerationFixedConstructor.references baseRefs slots trueFlags falseFlags) channels := by
  simp only [finalState, atState, constructorHeap, constructorDictionary,
    ForestZeroQueryCaller.queryEmission_dictionary, EnumerationFixedConstructor.references_length]

theorem final_stored (trueFlags falseFlags : Slot ambient → Bool) (heap : Array (Word width))
    (layout : Layout ambient heap.size) (dictionary : Dictionary ambient) (represented : Represented heap layout dictionary)
    (channels returnPc : Nat) (within : channels ≤ ambient) (baseRefs : List (List (Reference ambient)))
    (slots : List (Slot ambient)) (stack output : List (Word width)) :
    Controller.Horn.SourceDirectory.Stored
      (constructorClauses heap layout dictionary represented.coherent
        (EnumerationFixedConstructor.references baseRefs slots trueFlags falseFlags) channels within)
      (heap.size + 5) (heap.size + 5 + 2 * (baseRefs.length + slots.length + 1))
      (finalState trueFlags falseFlags heap layout dictionary channels returnPc baseRefs slots stack output).heap := by
  rw [final_heap]
  simpa only [EnumerationFixedConstructor.references_length] using
    constructor_clauses_stored heap layout dictionary represented
      (EnumerationFixedConstructor.references baseRefs slots trueFlags falseFlags) channels within

theorem execution (program : Program width 8) (saved : Fin 8 → Word width)
    (trueFlags falseFlags : Slot ambient → Bool)
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
    (programFits : base + (EnumerationFixedConstructor.code width base heap.size returnPc baseRefs slots).length < 2 ^ width)
    (block : WidenedBlockAt program base (EnumerationFixedConstructor.code width base heap.size returnPc baseRefs slots)) :
    ∃ ticks peak, Execution program
      (widenState (initialState heap layout dictionary base baseRefs slots stack output) saved)
      (widenState (finalState trueFlags falseFlags heap layout dictionary channels returnPc baseRefs slots stack output) saved)
      ticks peak ∧ ticks ≤ 79 + 5 * (baseRefs.length + slots.length) +
        23 * baseRefs.flatten.length + 31 * slots.length +
        23 * (constructorDictionary heap layout dictionary
          (EnumerationFixedConstructor.references baseRefs slots trueFlags falseFlags)).coordinates.size ∧
      peak ≤ 18 + heap.size + 2 * (baseRefs.length + slots.length + 1) +
        2 * baseRefs.flatten.length + 2 * slots.length +
        2 * (constructorDictionary heap layout dictionary
          (EnumerationFixedConstructor.references baseRefs slots trueFlags falseFlags)).coordinates.size + stack.length + output.length := by
  obtain ⟨ticks, peak, trace, time, space⟩ := EnumerationFixedConstructor.execution (lowerProgram program)
    trueFlags falseFlags heap layout dictionary represented channels sourceEnd baseRefs slots sourceBound sourcePositive channelCell within
    baseStored slotStored maskBounds maskCells beforeTable beforeInverse base returnPc stack output widthPositive room ambientFits
    programFits (lower_block program base _ block)
  have lowTrace : Execution (lowerProgram program)
      (initialState heap layout dictionary base baseRefs slots stack output)
      (finalState trueFlags falseFlags heap layout dictionary channels returnPc baseRefs slots stack output) ticks peak := trace
  rw [ForestZeroQueryCaller.queryEmission_dictionary] at time space
  refine ⟨ticks, peak + 4, ForestZeroCallerWiden.execution program _ _ ticks peak lowTrace rfl saved, time, ?_⟩
  dsimp only [constructorDictionary]
  omega

end Controller.Cost.EnumerationFixedConstructorWiden
