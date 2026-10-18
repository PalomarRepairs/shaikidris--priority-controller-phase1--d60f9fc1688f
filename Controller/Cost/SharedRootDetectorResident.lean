module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedRootDetectorCode
public import Controller.Cost.SharedRootTaggedTrue

@[expose] public section

namespace Controller.Cost.SharedRootDetectorResident
open Controller.Cost.GateProgram Controller.Cost.ForestZeroDictionary
open Controller.Native Controller.Native.SourceController Controller.Decoder
open Controller.Cost.NativeSourceExecution

@[irreducible] def code (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels)) (heap : Array (Word width))
    (layout : Layout (parameters.channels + graph.nodeCount) heap.size)
    (coordinateBase slot offset maskBase entry : Nat) (root : Fin graph.nodeCount) : List (Instruction width 8) :=
  SharedRootDetectorCode.code parameters graph T F heap layout coordinateBase slot offset entry
    (SharedTrueHandler.code parameters width heap.size maskBase (entry + 22)) root

set_option maxHeartbeats 2000000 in
theorem shared (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels)) (before after : Array (Word width))
    (leftLayout : Layout (parameters.channels + graph.nodeCount) before.size)
    (rightLayout : Layout (parameters.channels + graph.nodeCount) after.size)
    (coordinateBase slot offset maskBase entry : Nat) (left right : Fin graph.nodeCount)
    (sameSize : before.size = after.size) (sameTable : leftLayout.tableBase = rightLayout.tableBase)
    (sameInverse : leftLayout.inverseBase = rightLayout.inverseBase) :
    code parameters graph T F before leftLayout coordinateBase slot offset maskBase entry left =
      code parameters graph T F after rightLayout coordinateBase slot offset maskBase entry right := by
  unfold code
  have fixed := SharedRootDetectorCode.shared parameters graph T F before after leftLayout rightLayout
    coordinateBase slot offset entry (SharedTrueHandler.code parameters width before.size maskBase (entry + 22))
    left right sameSize sameTable sameInverse
  simpa only [sameSize] using fixed

set_option maxHeartbeats 2000000 in
theorem true_length_bound (parameters : Parameters) (width heapSize maskBase entry : Nat) :
    (SharedTrueHandler.code parameters width heapSize maskBase entry).length ≤ 43 * (selectedSize parameters).total + 9 := by
  have native := SharedQueryHeapCapacity.native_code_bound parameters width heapSize (SharedTrueNative.nativeEntry parameters entry)
  have variablesBound : (compile parameters).toState.count ≤ (selectedSize parameters).total := by
    simp only [selectedSize, NativeSize.total]
    omega
  have roots := (sourceCircuit parameters).roots_le
  have channelsBound : parameters.channels ≤ SourceInitialIDs.rootCount parameters := by
    simp only [SourceInitialIDs.rootCount]
    omega
  rw [SharedTrueHandler.code_length]
  unfold SharedTrueNative.code
  simp only [List.length_append, List.length_map, SharedTrueInput.code_length, List.length_reverse, List.length_finRange]
  omega

set_option maxHeartbeats 2000000 in
theorem code_length_bound (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels)) (heap : Array (Word width))
    (layout : Layout (parameters.channels + graph.nodeCount) heap.size)
    (coordinateBase slot offset maskBase entry : Nat) (root : Fin graph.nodeCount) :
    (code parameters graph T F heap layout coordinateBase slot offset maskBase entry root).length ≤
      410 * (graph.countedSize + 1) + 77 * (selectedSize parameters).total + 563 := by
  have handler := true_length_bound parameters width heap.size maskBase (entry + 22)
  have bound := SharedRootDetectorCode.code_length_bound parameters graph T F heap layout coordinateBase slot offset entry
    (SharedTrueHandler.code parameters width heap.size maskBase (entry + 22)) root
  unfold code
  omega

theorem code_capacity (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels))
    (heap : Array (Word (SharedMachineCapacity.wordWidth retained graph.countedSize (selectedSize parameters).total)))
    (layout : Layout (parameters.channels + graph.nodeCount) heap.size)
    (coordinateBase slot offset maskBase entry : Nat) (root : Fin graph.nodeCount) (entryBound : entry ≤ retained) :
    entry + (code parameters graph T F heap layout coordinateBase slot offset maskBase entry root).length <
      2 ^ SharedMachineCapacity.wordWidth retained graph.countedSize (selectedSize parameters).total := by
  have bound := code_length_bound parameters graph T F heap layout coordinateBase slot offset maskBase entry root
  have capacity := SharedMachineCapacity.capacity retained graph.countedSize (selectedSize parameters).total
  omega

end Controller.Cost.SharedRootDetectorResident
