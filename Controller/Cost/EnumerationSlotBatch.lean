module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.EnumerationSlotEmit

@[expose] public section

/-! A resident sequence of mask-selected unit slots. Code generation depends
on source and mask addresses; the flag functions appear only in the semantic
correspondence. Every executed slot appends two solver-source words. -/
namespace Controller.Cost.EnumerationSlotBatch
open Controller.CNF Controller.Cost.GateProgram Controller.Cost.ForestZeroTouch
open Controller.Cost.ForestZeroEmit Controller.Cost.ForestZeroDictionary
open Controller.Cost.ForestZeroCompile Controller.Cost.ForestZeroRows

structure Slot (ambient : Nat) where
  trueMask : Nat
  falseMask : Nat
  positive : Reference ambient
  negative : Reference ambient
  inactive : Reference ambient
  positiveChannel : positive.activity = false
  negativeChannel : negative.activity = false
  inactiveRoot : inactive.activity = true

def chosen (slot : Slot ambient) (trueFlags falseFlags : Slot ambient → Bool) : Reference ambient :=
  EnumerationSlotCode.selected slot.positive slot.negative slot.inactive (trueFlags slot) (falseFlags slot)

def code (width base : Nat) : List (Slot ambient) → Code width
  | [] => []
  | slot :: rest =>
      EnumerationSlotCode.code width base slot.trueMask slot.falseMask slot.positive slot.negative slot.inactive ++
        code width (base + 90) rest

@[simp] theorem code_length (slots : List (Slot ambient)) :
    (code width base slots).length = 90 * slots.length := by
  induction slots generalizing base with
  | nil => simp [code]
  | cons slot rest ih =>
    simp only [code, List.length_append, EnumerationSlotCode.code_length slot.positive slot.negative slot.inactive
      slot.positiveChannel slot.negativeChannel slot.inactiveRoot, ih, List.length_cons]
    omega

def produce (trueFlags falseFlags : Slot ambient → Bool) (heap : Array (Word width))
    (layout : Layout ambient heap.size) (dictionary : Dictionary ambient) (input scratch : Nat) :
    List (Slot ambient) → Result ambient width
  | [] => ⟨heap, layout, dictionary, input, scratch⟩
  | slot :: rest =>
      let reference := chosen slot trueFlags falseFlags
      produce trueFlags falseFlags
        (literalHeap heap layout dictionary (reference.coordinate, reference.positive))
        (literalLayout heap layout dictionary (reference.coordinate, reference.positive))
        (touch dictionary reference.coordinate).1 (touch dictionary reference.coordinate).2.1 0 rest

@[simp] theorem produce_size (trueFlags falseFlags : Slot ambient → Bool)
    (heap : Array (Word width)) (layout : Layout ambient heap.size) (dictionary : Dictionary ambient)
    (input scratch : Nat) (slots : List (Slot ambient)) :
    (produce trueFlags falseFlags heap layout dictionary input scratch slots).heap.size =
      heap.size + 2 * slots.length := by
  induction slots generalizing heap dictionary input scratch with
  | nil => simp [produce]
  | cons slot rest ih =>
    simp only [produce, ih, literalHeap_size, List.length_cons]
    omega

theorem produce_dictionary (trueFlags falseFlags : Slot ambient → Bool)
    (heap : Array (Word width)) (layout : Layout ambient heap.size) (dictionary : Dictionary ambient)
    (input scratch : Nat) (slots : List (Slot ambient)) :
    (produce trueFlags falseFlags heap layout dictionary input scratch slots).dictionary =
      (compileRows dictionary (slots.map (fun slot =>
        let reference := chosen slot trueFlags falseFlags
        [(reference.coordinate, reference.positive)]))).1 := by
  induction slots generalizing heap dictionary input scratch with
  | nil => rfl
  | cons slot rest ih =>
    simpa only [produce, List.map_cons, compileRows, compileClause] using
      ih (literalHeap heap layout dictionary ((chosen slot trueFlags falseFlags).coordinate,
        (chosen slot trueFlags falseFlags).positive))
        (literalLayout heap layout dictionary ((chosen slot trueFlags falseFlags).coordinate,
          (chosen slot trueFlags falseFlags).positive))
        (touch dictionary (chosen slot trueFlags falseFlags).coordinate).1
        (touch dictionary (chosen slot trueFlags falseFlags).coordinate).2.1 0

/-- The selected resident branches produce the same heap as R04's emitter on
the selected reference list. Input and scratch registers do not enter that heap. -/
theorem produce_heap_eq (trueFlags falseFlags : Slot ambient → Bool)
    (heap : Array (Word width)) (layout : Layout ambient heap.size) (dictionary : Dictionary ambient)
    (input scratch otherInput otherScratch : Nat) (slots : List (Slot ambient)) :
    (produce trueFlags falseFlags heap layout dictionary input scratch slots).heap =
      (emitReferences heap layout dictionary otherInput otherScratch
        (slots.map (fun slot => chosen slot trueFlags falseFlags))).heap := by
  induction slots generalizing heap dictionary input scratch otherInput otherScratch with
  | nil => rfl
  | cons slot rest ih =>
    simpa only [produce, List.map_cons, emitReferences] using
      ih (literalHeap heap layout dictionary ((chosen slot trueFlags falseFlags).coordinate,
        (chosen slot trueFlags falseFlags).positive))
        (literalLayout heap layout dictionary ((chosen slot trueFlags falseFlags).coordinate,
          (chosen slot trueFlags falseFlags).positive))
        (touch dictionary (chosen slot trueFlags falseFlags).coordinate).1
        (touch dictionary (chosen slot trueFlags falseFlags).coordinate).2.1 0
        (touch dictionary (chosen slot trueFlags falseFlags).coordinate).2.1
        (if (chosen slot trueFlags falseFlags).positive then 1 else 0)

theorem produce_represented (trueFlags falseFlags : Slot ambient → Bool)
    (heap : Array (Word width)) (layout : Layout ambient heap.size) (dictionary : Dictionary ambient)
    (represented : Represented heap layout dictionary) (input scratch : Nat) (slots : List (Slot ambient)) :
    let result := produce trueFlags falseFlags heap layout dictionary input scratch slots
    Represented result.heap result.layout result.dictionary := by
  induction slots generalizing heap dictionary input scratch with
  | nil => exact represented
  | cons slot rest ih =>
    exact ih _ _ _ (literal_represented heap layout dictionary represented
      ((chosen slot trueFlags falseFlags).coordinate, (chosen slot trueFlags falseFlags).positive)) _ _

set_option maxHeartbeats 4000000 in
theorem execution (program : Program width 4) (trueFlags falseFlags : Slot ambient → Bool)
    (heap : Array (Word width)) (layout : Layout ambient heap.size) (dictionary : Dictionary ambient)
    (represented : Represented heap layout dictionary) (channels sourceEnd : Nat)
    (slots : List (Slot ambient)) (sourceBound : sourceEnd ≤ heap.size)
    (stored : ∀ slot ∈ slots,
      StoredReference heap channels sourceEnd slot.positive ∧
      StoredReference heap channels sourceEnd slot.negative ∧
      StoredReference heap channels sourceEnd slot.inactive)
    (maskBounds : ∀ slot ∈ slots, slot.trueMask < sourceEnd ∧ slot.falseMask < sourceEnd)
    (maskCells : ∀ slot ∈ slots,
      heap[slot.trueMask]? = some (boolWord width (trueFlags slot)) ∧
      heap[slot.falseMask]? = some (boolWord width (falseFlags slot)))
    (beforeTable : sourceEnd ≤ layout.tableBase) (beforeInverse : sourceEnd ≤ layout.inverseBase)
    (base input scratch : Nat) (stack output : List (Word width)) (widthPositive : 0 < width)
    (room : heap.size + 2 * slots.length < 2 ^ width) (ambientFits : ambient + 1 < 2 ^ width)
    (programFits : base + 90 * slots.length < 2 ^ width) (block : BlockAt program base (code width base slots)) :
    let result := produce trueFlags falseFlags heap layout dictionary input scratch slots
    ∃ ticks peak, Execution program
      (atState heap base input layout.tableBase dictionary.coordinates.size scratch
        (word width layout.inverseBase :: stack) output)
      (atState result.heap (base + 90 * slots.length) result.input
        layout.tableBase result.dictionary.coordinates.size result.scratch
        (word width layout.inverseBase :: stack) output)
      ticks peak ∧ ticks ≤ 31 * slots.length ∧
      peak ≤ 8 + heap.size + 2 * slots.length + stack.length + output.length := by
  induction slots generalizing heap dictionary base input scratch with
  | nil =>
    refine ⟨0, (atState heap base input layout.tableBase dictionary.coordinates.size scratch
      (word width layout.inverseBase :: stack) output).liveWords, ?_, by simp, ?_⟩
    · simpa only [produce, List.length_nil, Nat.mul_zero, Nat.add_zero] using
        Execution.refl (p := program) (atState heap base input layout.tableBase dictionary.coordinates.size scratch
          (word width layout.inverseBase :: stack) output)
    · simp only [atState_liveWords, List.length_cons, List.length_nil, Nat.mul_zero]
      omega
  | cons slot rest ih =>
    have firstAt := BlockAt.prefix program base _ _ block
    have restAt := BlockAt.suffix program base _ _ block
    rw [EnumerationSlotCode.code_length slot.positive slot.negative slot.inactive
      slot.positiveChannel slot.negativeChannel slot.inactiveRoot] at restAt
    obtain ⟨positiveStored, negativeStored, inactiveStored⟩ := stored slot (by simp)
    obtain ⟨trueBound, falseBound⟩ := maskBounds slot (by simp)
    obtain ⟨trueCell, falseCell⟩ := maskCells slot (by simp)
    obtain ⟨firstTicks, firstTime, first⟩ := EnumerationSlotEmit.execution program heap layout dictionary represented
      channels sourceEnd slot.positive slot.negative slot.inactive
      slot.positiveChannel slot.negativeChannel slot.inactiveRoot positiveStored negativeStored inactiveStored
      base slot.trueMask slot.falseMask input scratch (trueFlags slot) (falseFlags slot) stack output widthPositive
      (by simp only [List.length_cons] at room; omega) (by simp only [List.length_cons] at room; omega)
      (by omega) (by omega) trueCell falseCell (by simp only [List.length_cons] at room; omega) ambientFits
      (by simp only [List.length_cons] at programFits; omega) firstAt
    let reference := chosen slot trueFlags falseFlags
    let nextHeap := literalHeap heap layout dictionary (reference.coordinate, reference.positive)
    let nextLayout := literalLayout heap layout dictionary (reference.coordinate, reference.positive)
    let nextDictionary := (touch dictionary reference.coordinate).1
    have tailStored : ∀ other ∈ rest,
        StoredReference nextHeap channels sourceEnd other.positive ∧
        StoredReference nextHeap channels sourceEnd other.negative ∧
        StoredReference nextHeap channels sourceEnd other.inactive := by
      intro other member
      obtain ⟨pos, neg, inactive⟩ := stored other (by simp [member])
      exact ⟨storedReference_retained heap layout dictionary _ channels sourceEnd _ pos beforeTable beforeInverse,
        storedReference_retained heap layout dictionary _ channels sourceEnd _ neg beforeTable beforeInverse,
        storedReference_retained heap layout dictionary _ channels sourceEnd _ inactive beforeTable beforeInverse⟩
    have tailCells : ∀ other ∈ rest,
        nextHeap[other.trueMask]? = some (boolWord width (trueFlags other)) ∧
        nextHeap[other.falseMask]? = some (boolWord width (falseFlags other)) := by
      intro other member
      obtain ⟨boundsT, boundsF⟩ := maskBounds other (by simp [member])
      obtain ⟨cellsT, cellsF⟩ := maskCells other (by simp [member])
      exact ⟨(literal_source_frame heap layout dictionary _ sourceEnd beforeTable beforeInverse
        other.trueMask boundsT sourceBound).trans cellsT,
        (literal_source_frame heap layout dictionary _ sourceEnd beforeTable beforeInverse
        other.falseMask boundsF sourceBound).trans cellsF⟩
    obtain ⟨tailTicks, tailPeak, tail, tailTime, tailSpace⟩ := ih nextHeap nextLayout nextDictionary
      (literal_represented heap layout dictionary represented (reference.coordinate, reference.positive))
      (by dsimp only [nextHeap]; rw [literalHeap_size]; omega) tailStored
      (fun other member => maskBounds other (by simp [member])) tailCells beforeTable beforeInverse
      (base + 90) (touch dictionary reference.coordinate).2.1 0
      (by dsimp only [nextHeap]; simp only [literalHeap_size, List.length_cons] at room ⊢; omega)
      (by simp only [List.length_cons] at programFits; omega) restAt
    have joined := first.append tail
    refine ⟨firstTicks + tailTicks, max (8 + heap.size + stack.length + output.length) tailPeak, ?_, ?_, ?_⟩
    · convert joined using 1
      simp only [produce, chosen, reference, nextHeap, nextLayout, nextDictionary, literalLayout,
        List.length_cons, Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.add_comm]
    · simp only [List.length_cons]
      omega
    · dsimp only [nextHeap] at tailSpace
      simp only [literalHeap_size] at tailSpace
      simp only [List.length_cons, max_le_iff]
      constructor <;> omega

end Controller.Cost.EnumerationSlotBatch
