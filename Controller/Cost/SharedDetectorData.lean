module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedRootDetectorResident

@[expose] public section

namespace Controller.Cost.SharedDetectorData
open Controller.Cost.GateProgram Controller.Cost.ForestZeroAdmissibleCaller
open Controller.Cost.ForestZeroBackendFrame
open Controller.Native Controller.Native.SourceController Controller.Decoder

def Slots (heap : Array (Word width)) (base : Nat) (words : List (Word width)) : Prop :=
  ∀ index (below : index < words.length), heap[base + index]? = some words[index]

theorem Slots.head (heap : Array (Word width)) (base : Nat) (value : Word width) (words : List (Word width))
    (stored : Slots heap base (value :: words)) : heap[base]? = some value := by
  have found := stored 0 (by simp)
  change heap[base + 0]? = some value at found
  simpa only [Nat.add_zero] using found

theorem Slots.tail (heap : Array (Word width)) (base : Nat) (value : Word width) (words : List (Word width))
    (stored : Slots heap base (value :: words)) : Slots heap (base + 1) words := by
  intro index below
  have found := stored (index + 1) (by simp only [List.length_cons]; omega)
  simpa only [List.getElem_cons_succ, Nat.add_assoc, Nat.add_comm 1 index] using found

theorem Slots.root_update (heap : Array (Word width)) (base slot : Nat) (words : List (Word width))
    (value : Word width) (valid : slot < heap.size) (stored : Slots heap base words)
    (before : base + words.length ≤ slot) : Slots (heap.set slot value valid) base words := by
  intro index below
  rw [Array.getElem?_set_ne valid (by omega)]
  exact stored index below

theorem Slots.transport (before after : Array (Word width)) (base sourceEnd : Nat) (words : List (Word width))
    (stored : Slots before base words) (bound : base + words.length ≤ sourceEnd)
    (frame : PrefixFrame sourceEnd before after) : Slots after base words := by
  intro index below
  exact (frame.2.2 (base + index) (by omega)).trans (stored index below)

/-- Candidate tags, root identifiers and baseline mask cells precede the mutable query-root cell. -/
def Stored (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels)) (maskBase candidateBase offset slot : Nat)
    (positions : List (Fin graph.roots.length)) (heap : Array (Word width)) : Prop :=
  candidateBase + positions.length ≤ slot ∧
  candidateBase + offset + positions.length ≤ slot ∧
  maskBase + parameters.channels ≤ slot ∧
  Slots heap candidateBase (positions.map (SharedWitnessDecode.tag graph
    (extensionBase parameters.buses parameters.bridge.target T) F width)) ∧
  Slots heap (candidateBase + offset) (positions.map (fun index => word width graph.roots[index.val].val)) ∧
  ∀ channel : Fin parameters.channels, heap[maskBase + channel.val]? =
    some (word width (if assignmentOfSet (extensionBase parameters.buses parameters.bridge.target T) channel then 1 else 0))

set_option maxHeartbeats 2000000 in
theorem tail (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels)) (maskBase candidateBase offset slot : Nat)
    (position : Fin graph.roots.length) (positions : List (Fin graph.roots.length)) (heap : Array (Word width))
    (stored : Stored parameters graph T F maskBase candidateBase offset slot (position :: positions) heap) :
    Stored parameters graph T F maskBase (candidateBase + 1) offset slot positions heap := by
  obtain ⟨candidatesBound, rootsBound, maskBound, candidates, roots, mask⟩ := stored
  refine ⟨?_, ?_, maskBound, ?_, ?_, mask⟩
  · simp only [List.length_cons] at candidatesBound; omega
  · simp only [List.length_cons] at rootsBound; omega
  · exact Slots.tail heap candidateBase _ _ candidates
  · simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using Slots.tail heap (candidateBase + offset) _ _ roots

set_option maxHeartbeats 2000000 in
theorem root_update (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels)) (maskBase candidateBase offset slot : Nat)
    (positions : List (Fin graph.roots.length)) (heap : Array (Word width)) (value : Word width)
    (valid : slot < heap.size) (stored : Stored parameters graph T F maskBase candidateBase offset slot positions heap) :
    Stored parameters graph T F maskBase candidateBase offset slot positions (heap.set slot value valid) := by
  obtain ⟨candidatesBound, rootsBound, maskBound, candidates, roots, mask⟩ := stored
  refine ⟨candidatesBound, rootsBound, maskBound,
    Slots.root_update heap candidateBase slot _ value valid candidates (by simpa using candidatesBound),
    Slots.root_update heap (candidateBase + offset) slot _ value valid roots (by simpa using rootsBound), ?_⟩
  intro channel
  rw [Array.getElem?_set_ne valid (by have := channel.isLt; omega)]
  exact mask channel

set_option maxHeartbeats 2000000 in
theorem ready (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels)) (maskBase candidateBase offset slot : Nat)
    (positions : List (Fin graph.roots.length)) (sourceHeap : Array (Word width)) (state : State width 8)
    (tableBase inverseBase entry : Nat) (rest : List (Word width))
    (stored : Stored parameters graph T F maskBase candidateBase offset slot positions sourceHeap)
    (query : QueryReady (ambient := ambient) sourceHeap tableBase inverseBase entry rest state) (slotBefore : slot < tableBase) :
    Stored parameters graph T F maskBase candidateBase offset slot positions state.heap := by
  obtain ⟨candidatesBound, rootsBound, maskBound, candidates, roots, mask⟩ := stored
  refine ⟨candidatesBound, rootsBound, maskBound,
    Slots.transport sourceHeap state.heap candidateBase tableBase _ candidates (by simp only [List.length_map]; omega) query.sourceFrame,
    Slots.transport sourceHeap state.heap (candidateBase + offset) tableBase _ roots (by simp only [List.length_map]; omega) query.sourceFrame, ?_⟩
  intro channel
  exact (query.sourceFrame.2.2 (maskBase + channel.val) (by have := channel.isLt; omega)).trans (mask channel)


def healthyTags (parameters : Parameters) (graph : DAG parameters.channels) (width : Nat)
    (positions : List (Fin graph.roots.length)) : List (Word width) :=
  positions.map (fun index => if graph.eval (assignmentOfSet {parameters.bridge.target}) graph.roots[index.val] then
    word width parameters.bridge.target.val else word width (parameters.channels + 1))

@[simp] theorem healthyTags_length (parameters : Parameters) (graph : DAG parameters.channels)
    (positions : List (Fin graph.roots.length)) : (healthyTags parameters graph width positions).length = positions.length := by
  simp [healthyTags]

theorem healthyTags_reference (parameters : Parameters) (graph : DAG parameters.channels) (width : Nat) :
    healthyTags parameters graph width (List.finRange graph.roots.length) =
      SharedHealthyReference.reference graph parameters.bridge.target width := by
  unfold healthyTags SharedHealthyReference.reference
  rw [← List.ofFn_eq_map]
  exact List.ofFn_getElem_eq_map graph.roots (fun root =>
    if graph.eval (assignmentOfSet {parameters.bridge.target}) root then
      word width parameters.bridge.target.val else word width (parameters.channels + 1))

theorem Slots.valid (heap : Array (Word width)) (base : Nat) (value : Word width) (words : List (Word width))
    (stored : Slots heap base (value :: words)) : base < heap.size := by
  have found := stored.head heap base value words
  by_contra outside
  have missing : heap[base]? = none := Array.getElem?_eq_none (by omega)
  rw [missing] at found
  contradiction

set_option maxHeartbeats 2000000 in
theorem head (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels)) (maskBase candidateBase offset slot : Nat)
    (position : Fin graph.roots.length) (positions : List (Fin graph.roots.length)) (heap : Array (Word width))
    (stored : Stored parameters graph T F maskBase candidateBase offset slot (position :: positions) heap) :
    heap[candidateBase]? = some (SharedWitnessDecode.tag graph
      (extensionBase parameters.buses parameters.bridge.target T) F width position) ∧
    heap[candidateBase + offset]? = some (word width graph.roots[position.val].val) ∧
    candidateBase < heap.size ∧ candidateBase + offset < heap.size := by
  obtain ⟨candidatesBound, rootsBound, maskBound, candidates, roots, mask⟩ := stored
  exact ⟨Slots.head heap candidateBase _ _ candidates, Slots.head heap (candidateBase + offset) _ _ roots,
    Slots.valid heap candidateBase _ _ candidates, Slots.valid heap (candidateBase + offset) _ _ roots⟩


set_option maxHeartbeats 2000000 in
theorem failed_query_tail (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels)) (maskBase candidateBase offset slot : Nat)
    (position : Fin graph.roots.length) (positions : List (Fin graph.roots.length))
    (sourceHeap : Array (Word width)) (final : State width 8) (value : Word width)
    (valid : slot < sourceHeap.size) (tableBase inverseBase entry : Nat) (rest : List (Word width))
    (stored : Stored parameters graph T F maskBase candidateBase offset slot (position :: positions) sourceHeap)
    (query : QueryReady (ambient := ambient) (sourceHeap.set slot value valid) tableBase inverseBase entry rest final)
    (slotBefore : slot < tableBase) :
    Stored parameters graph T F maskBase (candidateBase + 1) offset slot positions final.heap := by
  have updated := root_update parameters graph T F maskBase candidateBase offset slot (position :: positions) sourceHeap value valid stored
  have advanced := tail parameters graph T F maskBase candidateBase offset slot position positions _ updated
  exact ready parameters graph T F maskBase (candidateBase + 1) offset slot positions _ final
    tableBase inverseBase entry rest advanced query slotBefore

theorem skipped_tail (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels)) (maskBase candidateBase offset slot : Nat)
    (position : Fin graph.roots.length) (positions : List (Fin graph.roots.length))
    (before after : Array (Word width))
    (stored : Stored parameters graph T F maskBase candidateBase offset slot (position :: positions) before)
    (sameHeap : after = before) :
    Stored parameters graph T F maskBase (candidateBase + 1) offset slot positions after := by
  rw [sameHeap]
  exact tail parameters graph T F maskBase candidateBase offset slot position positions before stored

end Controller.Cost.SharedDetectorData
