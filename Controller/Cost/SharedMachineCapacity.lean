module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedZeroNativeQuery

@[expose] public section

namespace Controller.Cost.SharedMachineCapacity
open Controller.Cost.GateProgram Controller.Native Controller.Native.SourceController
open Controller.Cost.NativeSourceExecution
open Controller.Cost.NativeCircuitExecution Controller.Decoder

def wordWidth (retained graphSize nativeSize : Nat) : Nat :=
  Nat.log2 (retained + graphSize + nativeSize + 1) + 18

theorem capacity (retained graphSize nativeSize : Nat) :
    131072 * (retained + graphSize + nativeSize + 1) < 2 ^ wordWidth retained graphSize nativeSize := by
  let total := retained + graphSize + nativeSize
  have basic : total + 1 < 2 ^ (Nat.log2 (total + 1) + 1) :=
    (Nat.log2_lt (by omega : total + 1 ≠ 0)).mp (Nat.lt_succ_self _)
  have scaled := Nat.mul_lt_mul_of_pos_left basic (by decide : 0 < 131072)
  have identity : 131072 * 2 ^ (Nat.log2 (total + 1) + 1) =
      2 ^ wordWidth retained graphSize nativeSize := by
    simp only [wordWidth, total, Nat.pow_add, Nat.pow_one, Nat.reducePow]
    omega
  simpa only [identity, total] using scaled

theorem native_heap (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels)) (root : Fin graph.nodeCount)
    (heap : Array (Word (wordWidth retained graph.countedSize (selectedSize parameters).total)))
    (layout : ForestZeroDictionary.Layout (parameters.channels + graph.nodeCount) heap.size)
    (size : heap.size ≤ retained) :
    SharedZeroNativeQuery.nativeBase heap layout
      (SharedZeroSource.references graph parameters.buses parameters.bridge.target T F base slot root)
      parameters.channels (by omega) + parameters.channels + (compile parameters).toState.count <
      2 ^ wordWidth retained graph.countedSize (selectedSize parameters).total := by
  have upper := SharedZeroNativeQuery.zero_nativeBase_bound (base := base) (slot := slot)
    parameters graph T F root heap layout
  have room := capacity retained graph.countedSize (selectedSize parameters).total
  have graphSize := graph.countedSize_eq
  have nativeSize : (compile parameters).toState.count ≤ (selectedSize parameters).total := by
    simp only [selectedSize, NativeSize.total]
    omega
  omega

end Controller.Cost.SharedMachineCapacity
