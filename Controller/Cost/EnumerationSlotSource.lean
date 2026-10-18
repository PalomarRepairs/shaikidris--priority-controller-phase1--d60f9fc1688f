module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.EnumerationSlotBatch
public import Controller.Cost.SharedZeroCode

@[expose] public section

/-! Channel unit slots use retained coordinate cells; inactive slots use the
shared queried-root cell. The complete resident slot code is independent of
both the prefix flags and the value stored in that root cell. -/
namespace Controller.Cost.EnumerationSlotSource
open Controller.CNF Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.GateProgram Controller.Cost.ForestZeroEmit
open Controller.Cost.EnumerationSlotBatch

def channelReference (nodes sourceBase : Nat) (channel : Channel n) (positive : Bool) : Reference (n + nodes) where
  slot := sourceBase + channel.val
  raw := channel.val
  activity := false
  coordinate := ⟨channel.val, by omega⟩
  positive := positive

def channelSlot (nodes sourceBase rootSlot trueBase falseBase : Nat)
    (root : Fin nodes) (channel : Channel n) : Slot (n + nodes) where
  trueMask := trueBase + channel.val
  falseMask := falseBase + channel.val
  positive := channelReference nodes sourceBase channel true
  negative := channelReference nodes sourceBase channel false
  inactive := SharedZeroCode.rootReference n nodes rootSlot root
  positiveChannel := rfl
  negativeChannel := rfl
  inactiveRoot := rfl

def slotsFor (nodes sourceBase rootSlot trueBase falseBase : Nat)
    (root : Fin nodes) (channels : List (Channel n)) : List (Slot (n + nodes)) :=
  channels.map (channelSlot nodes sourceBase rootSlot trueBase falseBase root)

def slots (nodes sourceBase rootSlot trueBase falseBase : Nat)
    (root : Fin nodes) : List (Slot (n + nodes)) :=
  slotsFor nodes sourceBase rootSlot trueBase falseBase root (List.finRange n)

@[simp] theorem slots_length (root : Fin nodes) :
    (slots (n := n) nodes sourceBase rootSlot trueBase falseBase root).length = n := by
  simp [slots, slotsFor]

theorem code_length (root : Fin nodes) :
    (EnumerationSlotBatch.code width base
      (slots (n := n) nodes sourceBase rootSlot trueBase falseBase root)).length = 90 * n := by
  simp

theorem code_root_irrel (left right : Fin nodes) (channels : List (Channel n)) :
    EnumerationSlotBatch.code width base (slotsFor nodes sourceBase rootSlot trueBase falseBase left channels) =
      EnumerationSlotBatch.code width base (slotsFor nodes sourceBase rootSlot trueBase falseBase right channels) := by
  induction channels generalizing base with
  | nil => rfl
  | cons channel rest ih =>
    simp only [slotsFor, List.map_cons, EnumerationSlotBatch.code] at ih ⊢
    rw [ih]
    simp [EnumerationSlotCode.code, channelSlot, channelReference, SharedZeroCode.rootReference,
      literalCode, readCode]

theorem channel_stored (heap : Array (Word width)) (channel : Channel n) (positive : Bool)
    (sourceBound : sourceEnd ≤ heap.size) (sourceFits : sourceBase + n ≤ sourceEnd)
    (headerBound : 0 < sourceEnd) (header : heap[0]? = some (word width n))
    (cell : heap[sourceBase + channel.val]? = some (word width channel.val)) :
    StoredReference heap n sourceEnd (channelReference nodes sourceBase channel positive) := by
  refine ⟨sourceBound, ?_, headerBound, cell, header, ?_⟩
  · simp only [channelReference]
    have := channel.isLt
    omega
  · simp [channelReference]

theorem slot_stored (heap : Array (Word width)) (root : Fin nodes) (channel : Channel n)
    (sourceBound : sourceEnd ≤ heap.size) (sourceFits : sourceBase + n ≤ sourceEnd)
    (rootBound : rootSlot < sourceEnd) (headerBound : 0 < sourceEnd)
    (header : heap[0]? = some (word width n))
    (channelCell : heap[sourceBase + channel.val]? = some (word width channel.val))
    (rootCell : heap[rootSlot]? = some (word width root.val)) :
    let slot := channelSlot nodes sourceBase rootSlot trueBase falseBase root channel
    StoredReference heap n sourceEnd slot.positive ∧
    StoredReference heap n sourceEnd slot.negative ∧
    StoredReference heap n sourceEnd slot.inactive := by
  refine ⟨channel_stored heap channel true sourceBound sourceFits headerBound header channelCell,
    channel_stored heap channel false sourceBound sourceFits headerBound header channelCell, ?_⟩
  refine ⟨sourceBound, rootBound, headerBound, rootCell, header, ?_⟩
  simp [channelSlot, SharedZeroCode.rootReference]
  omega

def references (nodes sourceBase rootSlot : Nat) (root : Fin nodes)
    (T F : Finset (Channel n)) : List (List (Reference (n + nodes))) :=
  (List.finRange n).map (fun channel =>
    [EnumerationSlotCode.selected (channelReference nodes sourceBase channel true)
      (channelReference nodes sourceBase channel false)
      (SharedZeroCode.rootReference n nodes rootSlot root)
      (decide (channel ∈ T)) (decide (channel ∈ F))])

theorem originalRows_eq (graph : DAG n) (root : Fin graph.nodeCount) (T F : Finset (Channel n)) :
    ForestZeroAssembly.originalRows (references graph.nodeCount sourceBase rootSlot root T F) =
      (EnumerationSlots.slots graph root T F).map
        (fun clause => clause.map (fun literal => (graph.zeroIndex literal.1, literal.2))) := by
  simp only [references, ForestZeroAssembly.originalRows, EnumerationSlots.slots, List.map_map]
  apply List.map_congr_left
  intro channel _
  by_cases positive : channel ∈ T
  · simp [EnumerationSlotCode.selected, EnumerationSlots.slot, positive, channelReference, zeroIndex]
    exact Fin.ext rfl
  · by_cases negative : channel ∈ F <;>
      simp [EnumerationSlotCode.selected, EnumerationSlots.slot, positive, negative,
        channelReference, SharedZeroCode.rootReference, zeroIndex]
    all_goals exact Fin.ext rfl

def trueFlags (trueBase : Nat) (T : Finset (Channel n)) (slot : Slot (n + nodes)) : Bool :=
  decide (∃ channel ∈ T, slot.trueMask = trueBase + channel.val)

def falseFlags (falseBase : Nat) (F : Finset (Channel n)) (slot : Slot (n + nodes)) : Bool :=
  decide (∃ channel ∈ F, slot.falseMask = falseBase + channel.val)

@[simp] theorem trueFlags_channel (root : Fin nodes) (channel : Channel n) (T : Finset (Channel n)) :
    trueFlags trueBase T (channelSlot nodes sourceBase rootSlot trueBase falseBase root channel) =
      decide (channel ∈ T) := by
  simp [trueFlags, channelSlot, Fin.val_inj]

@[simp] theorem falseFlags_channel (root : Fin nodes) (channel : Channel n) (F : Finset (Channel n)) :
    falseFlags falseBase F (channelSlot nodes sourceBase rootSlot trueBase falseBase root channel) =
      decide (channel ∈ F) := by
  simp [falseFlags, channelSlot, Fin.val_inj]

theorem selected_references (root : Fin nodes) (T F : Finset (Channel n)) :
    (slots nodes sourceBase rootSlot trueBase falseBase root).map
      (fun slot => [chosen slot (trueFlags trueBase T) (falseFlags falseBase F)]) =
      references nodes sourceBase rootSlot root T F := by
  simp [slots, slotsFor, List.map_map, Function.comp_def, chosen, channelSlot, references,
    trueFlags, falseFlags, Fin.val_inj]

theorem selected_rows_eq (graph : DAG n) (root : Fin graph.nodeCount) (T F : Finset (Channel n)) :
    (slots graph.nodeCount sourceBase rootSlot trueBase falseBase root).map
      (fun slot => let reference := chosen slot (trueFlags trueBase T) (falseFlags falseBase F)
        [(reference.coordinate, reference.positive)]) =
      (EnumerationSlots.slots graph root T F).map
        (fun clause => clause.map (fun literal => (graph.zeroIndex literal.1, literal.2))) := by
  have rows := congrArg ForestZeroAssembly.originalRows
    (selected_references (sourceBase := sourceBase) (rootSlot := rootSlot)
      (trueBase := trueBase) (falseBase := falseBase) root T F)
  rw [originalRows_eq graph root T F] at rows
  simpa only [ForestZeroAssembly.originalRows, List.map_map, List.map_cons, List.map_nil,
    Function.comp_def] using rows

theorem produced_dictionary (graph : DAG n) (root : Fin graph.nodeCount) (T F : Finset (Channel n))
    (heap : Array (Word width)) (layout : ForestZeroDictionary.Layout (n + graph.nodeCount) heap.size)
    (dictionary : ForestZeroCompile.Dictionary (n + graph.nodeCount)) (input scratch : Nat) :
    (produce (trueFlags trueBase T) (falseFlags falseBase F) heap layout dictionary input scratch
      (slots graph.nodeCount sourceBase rootSlot trueBase falseBase root)).dictionary =
      (ForestZeroCompile.compileRows dictionary
        ((EnumerationSlots.slots graph root T F).map
          (fun clause => clause.map (fun literal => (graph.zeroIndex literal.1, literal.2))))).1 := by
  rw [produce_dictionary, selected_rows_eq graph root T F]

end Controller.Cost.EnumerationSlotSource
