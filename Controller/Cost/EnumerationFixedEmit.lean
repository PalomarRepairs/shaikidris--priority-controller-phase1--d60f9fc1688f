module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.EnumerationFixedProfile

@[expose] public section

/-! Fixed base-row emission followed by the runtime unit slots. The resulting
heap equals the R04 emitter on the full selected reference stream; source and
mask cells retain their physical addresses across both phases. -/
namespace Controller.Cost.EnumerationFixedEmit
open Controller.CNF Controller.Cost.GateProgram Controller.Cost.ForestZeroTouch
open Controller.Cost.ForestZeroEmit Controller.Cost.ForestZeroDictionary
open Controller.Cost.ForestZeroCompile Controller.Cost.ForestZeroRows
open Controller.Cost.EnumerationSlotBatch

def code (width base : Nat) (baseRefs : List (List (Reference ambient))) (slots : List (Slot ambient)) : Code width :=
  emitCode width base baseRefs.flatten ++ EnumerationSlotBatch.code width
    (base + (emitCode width base baseRefs.flatten).length) slots

def result (trueFlags falseFlags : Slot ambient → Bool) (heap : Array (Word width))
    (layout : Layout ambient heap.size) (dictionary : Dictionary ambient) (input scratch : Nat)
    (baseRefs : List (List (Reference ambient))) (slots : List (Slot ambient)) : Result ambient width :=
  let first := emitReferences heap layout dictionary input scratch baseRefs.flatten
  produce trueFlags falseFlags first.heap first.layout first.dictionary first.input first.scratch slots

@[simp] theorem code_length (baseRefs : List (List (Reference ambient))) (slots : List (Slot ambient)) :
    (code width base baseRefs slots).length = (emitCode width base baseRefs.flatten).length + 90 * slots.length := by
  simp [code]

theorem code_bound (baseRefs : List (List (Reference ambient))) (slots : List (Slot ambient)) :
    (code width base baseRefs slots).length ≤ 28 * baseRefs.flatten.length + 90 * slots.length := by
  have first := emitCode_length width base baseRefs.flatten
  rw [code_length]
  omega

theorem emit_append (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (dictionary : Dictionary ambient) (input scratch : Nat) (left right : List (Reference ambient)) :
    emitReferences heap layout dictionary input scratch (left ++ right) =
      let first := emitReferences heap layout dictionary input scratch left
      emitReferences first.heap first.layout first.dictionary first.input first.scratch right := by
  induction left generalizing heap dictionary input scratch with
  | nil => rfl
  | cons reference rest ih =>
    exact ih _ _ _ _ _

theorem produce_dictionary_eq (trueFlags falseFlags : Slot ambient → Bool)
    (heap : Array (Word width)) (layout : Layout ambient heap.size) (dictionary : Dictionary ambient)
    (input scratch otherInput otherScratch : Nat) (slots : List (Slot ambient)) :
    (produce trueFlags falseFlags heap layout dictionary input scratch slots).dictionary =
      (emitReferences heap layout dictionary otherInput otherScratch
        (slots.map (fun slot => chosen slot trueFlags falseFlags))).dictionary := by
  induction slots generalizing heap dictionary input scratch otherInput otherScratch with
  | nil => rfl
  | cons slot rest ih =>
    simpa only [produce, List.map_cons, emitReferences] using
      ih _ _ _ _ 0 _ (if (chosen slot trueFlags falseFlags).positive then 1 else 0)

theorem result_heap (trueFlags falseFlags : Slot ambient → Bool)
    (heap : Array (Word width)) (layout : Layout ambient heap.size) (dictionary : Dictionary ambient)
    (input scratch : Nat) (baseRefs : List (List (Reference ambient))) (slots : List (Slot ambient)) :
    (result trueFlags falseFlags heap layout dictionary input scratch baseRefs slots).heap =
      (emitReferences heap layout dictionary input scratch
        (EnumerationFixedProfile.references baseRefs slots trueFlags falseFlags).flatten).heap := by
  rw [EnumerationFixedProfile.references_flatten, emit_append]
  exact produce_heap_eq _ _ _ _ _ _ _ _ _ _

theorem result_dictionary (trueFlags falseFlags : Slot ambient → Bool)
    (heap : Array (Word width)) (layout : Layout ambient heap.size) (dictionary : Dictionary ambient)
    (input scratch : Nat) (baseRefs : List (List (Reference ambient))) (slots : List (Slot ambient)) :
    (result trueFlags falseFlags heap layout dictionary input scratch baseRefs slots).dictionary =
      (emitReferences heap layout dictionary input scratch
        (EnumerationFixedProfile.references baseRefs slots trueFlags falseFlags).flatten).dictionary := by
  rw [EnumerationFixedProfile.references_flatten, emit_append]
  exact produce_dictionary_eq _ _ _ _ _ _ _ _ _ _

@[simp] theorem result_size (trueFlags falseFlags : Slot ambient → Bool)
    (heap : Array (Word width)) (layout : Layout ambient heap.size) (dictionary : Dictionary ambient)
    (input scratch : Nat) (baseRefs : List (List (Reference ambient))) (slots : List (Slot ambient)) :
    (result trueFlags falseFlags heap layout dictionary input scratch baseRefs slots).heap.size =
      heap.size + 2 * baseRefs.flatten.length + 2 * slots.length := by
  simp [result, emitReferences_size]

theorem source_frame (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (dictionary : Dictionary ambient) (input scratch : Nat) (references : List (Reference ambient))
    (sourceEnd address : Nat) (beforeTable : sourceEnd ≤ layout.tableBase)
    (beforeInverse : sourceEnd ≤ layout.inverseBase) (valid : address < sourceEnd)
    (sourceBound : sourceEnd ≤ heap.size) :
    (emitReferences heap layout dictionary input scratch references).heap[address]? = heap[address]? := by
  induction references generalizing heap dictionary input scratch with
  | nil => rfl
  | cons reference rest ih =>
    exact (ih (literalHeap heap layout dictionary (reference.coordinate, reference.positive))
      (literalLayout heap layout dictionary (reference.coordinate, reference.positive))
      (touch dictionary reference.coordinate).1 (touch dictionary reference.coordinate).2.1
      (if reference.positive then 1 else 0) beforeTable beforeInverse
      (by rw [literalHeap_size]; omega)).trans
      (literal_source_frame heap layout dictionary _ sourceEnd beforeTable beforeInverse address valid sourceBound)

theorem stored_retained (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (dictionary : Dictionary ambient) (input scratch : Nat) (references : List (Reference ambient))
    (channels sourceEnd : Nat) (reference : Reference ambient)
    (stored : StoredReference heap channels sourceEnd reference)
    (beforeTable : sourceEnd ≤ layout.tableBase) (beforeInverse : sourceEnd ≤ layout.inverseBase) :
    StoredReference (emitReferences heap layout dictionary input scratch references).heap channels sourceEnd reference := by
  refine ⟨?_, stored.slotBound, stored.headerBound, ?_, ?_, stored.coordinateEq⟩
  · rw [emitReferences_size]
    have := stored.sourceBound
    omega
  · exact (source_frame heap layout dictionary input scratch references sourceEnd reference.slot
      beforeTable beforeInverse stored.slotBound stored.sourceBound).trans stored.slotWord
  · exact (source_frame heap layout dictionary input scratch references sourceEnd 0
      beforeTable beforeInverse stored.headerBound stored.sourceBound).trans stored.channelWord

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
    (base input scratch : Nat) (stack output : List (Word width)) (widthPositive : 0 < width)
    (room : heap.size + 2 * baseRefs.flatten.length + 2 * slots.length < 2 ^ width)
    (ambientFits : ambient + 1 < 2 ^ width)
    (programFits : base + (code width base baseRefs slots).length < 2 ^ width)
    (block : BlockAt program base (code width base baseRefs slots)) :
    let final := result trueFlags falseFlags heap layout dictionary input scratch baseRefs slots
    ∃ ticks peak, Execution program
      (atState heap base input layout.tableBase dictionary.coordinates.size scratch
        (word width layout.inverseBase :: stack) output)
      (atState final.heap (base + (code width base baseRefs slots).length) final.input
        layout.tableBase final.dictionary.coordinates.size final.scratch
        (word width layout.inverseBase :: stack) output)
      ticks peak ∧ ticks ≤ 23 * baseRefs.flatten.length + 31 * slots.length ∧
      peak ≤ 8 + heap.size + 2 * baseRefs.flatten.length + 2 * slots.length + stack.length + output.length := by
  have firstAt := BlockAt.prefix program base _ _ block
  have tailAt := BlockAt.suffix program base _ _ block
  obtain ⟨firstTicks, firstPeak, first, firstTime, firstSpace⟩ := emitReferences_execution program heap layout dictionary
    represented channels sourceEnd baseRefs.flatten baseStored beforeTable beforeInverse base input scratch stack output
    (by omega) ambientFits (by rw [code_length] at programFits; omega) firstAt
  let emitted := emitReferences heap layout dictionary input scratch baseRefs.flatten
  obtain ⟨tableSame, inverseSame⟩ := emitReferences_bases heap layout dictionary input scratch baseRefs.flatten
  have retained : ∀ slot ∈ slots, StoredReference emitted.heap channels sourceEnd slot.positive ∧
      StoredReference emitted.heap channels sourceEnd slot.negative ∧ StoredReference emitted.heap channels sourceEnd slot.inactive := by
    intro slot member
    obtain ⟨pos, neg, inactive⟩ := slotStored slot member
    exact ⟨stored_retained heap layout dictionary input scratch _ channels sourceEnd _ pos beforeTable beforeInverse,
      stored_retained heap layout dictionary input scratch _ channels sourceEnd _ neg beforeTable beforeInverse,
      stored_retained heap layout dictionary input scratch _ channels sourceEnd _ inactive beforeTable beforeInverse⟩
  have cells : ∀ slot ∈ slots, emitted.heap[slot.trueMask]? = some (boolWord width (trueFlags slot)) ∧
      emitted.heap[slot.falseMask]? = some (boolWord width (falseFlags slot)) := by
    intro slot member
    obtain ⟨boundsT, boundsF⟩ := maskBounds slot member
    obtain ⟨cellsT, cellsF⟩ := maskCells slot member
    exact ⟨(source_frame heap layout dictionary input scratch _ sourceEnd slot.trueMask
      beforeTable beforeInverse boundsT sourceBound).trans cellsT,
      (source_frame heap layout dictionary input scratch _ sourceEnd slot.falseMask
      beforeTable beforeInverse boundsF sourceBound).trans cellsF⟩
  obtain ⟨tailTicks, tailPeak, tail, tailTime, tailSpace⟩ := EnumerationSlotBatch.execution program trueFlags falseFlags
    emitted.heap emitted.layout emitted.dictionary (emitReferences_represented heap layout dictionary represented _ _ _)
    channels sourceEnd slots (by dsimp only [emitted]; rw [emitReferences_size]; omega) retained maskBounds cells
    (by rw [tableSame]; exact beforeTable) (by rw [inverseSame]; exact beforeInverse)
    (base + (emitCode width base baseRefs.flatten).length) emitted.input emitted.scratch
    stack output widthPositive (by dsimp only [emitted]; rw [emitReferences_size]; exact room) ambientFits
    (by rw [code_length] at programFits; omega) tailAt
  change emitted.layout.tableBase = layout.tableBase at tableSame
  change emitted.layout.inverseBase = layout.inverseBase at inverseSame
  rw [tableSame, inverseSame] at tail
  refine ⟨firstTicks + tailTicks, max firstPeak tailPeak, ?_, by omega, ?_⟩
  · convert first.append tail using 1
    simp only [result, code_length, emitted, Nat.add_assoc]
  · dsimp only [emitted] at tailSpace
    rw [emitReferences_size] at tailSpace
    omega

end Controller.Cost.EnumerationFixedEmit
