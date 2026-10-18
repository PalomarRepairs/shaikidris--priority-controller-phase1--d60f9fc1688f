module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.EnumerationUniformOracleLayout

@[expose] public section

namespace Controller.Cost.EnumerationUniformOracle
open Controller.Cost.GateProgram Controller.Cost.SharedMachineCapacity
open Controller.Decoder Controller.Native Controller.Native.SourceController
open Controller.Cost.NativeSourceExecution Controller.Cost.ForestIndexedOperands

theorem retained_capacity (retained graphSize nativeSize : Nat) :
    retained < 2 ^ wordWidth retained graphSize nativeSize := by
  have bound := capacity retained graphSize nativeSize
  omega

theorem graph_capacity (retained graphSize nativeSize : Nat) :
    256 * (graphSize + 1) < 2 ^ wordWidth retained graphSize nativeSize := by
  have bound := capacity retained graphSize nativeSize
  omega

theorem candidates_end_le (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels)) (width : Nat) (rows : List Row) (roots : List Nat)
    (entry back : Nat) (matched : RootsMatch graph roots) :
    directoryEntry parameters graph entry ≤ entry + (code parameters graph T F width rows roots entry back).length := by
  have rootCount : roots.length = graph.roots.length := by rw [matched]; simp
  simp only [code, List.length_append, EnumerationOracle.guardCode_length, Array.length_toList,
    SharedRetainedCandidates.code_size, directoryEntry, candidatesEntry, rootCount]
  omega

end Controller.Cost.EnumerationUniformOracle
