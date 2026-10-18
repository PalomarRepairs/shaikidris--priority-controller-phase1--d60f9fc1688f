module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.EnumerationDriverSeek

@[expose] public section

/-! Concrete retained capacity and the actual immutable driver array. The
resident-code, oracle-scratch and heap address hypotheses are discharged from
graph and native-coordinate sizes. -/
namespace Controller.Cost.EnumerationDriverCapacity
open Controller.Decoder Controller.Native Controller.Native.SourceController
open Controller.Cost.GateProgram Controller.Cost.NativeSourceExecution
open Controller.Cost.EnumerationDriverQuery

/-- Address capacity covering fixed code and the selected oracle workspace. -/
def retained (parameters : Parameters) (graph : DAG parameters.channels) : Nat :=
  10000 * (graph.countedSize + EnumerationCanonicalEmit.Coordinates parameters + 1)

/-- Pinned machine word width at the concrete retained capacity. -/
abbrev Width (parameters : Parameters) (graph : DAG parameters.channels) : Nat :=
  EnumerationPrefixOracle.Width parameters graph (retained parameters graph)

/-- The complete seventeen-block instruction array at entry zero. -/
def program (parameters : Parameters) (graph : DAG parameters.channels)
    (rows : List ForestIndexedOperands.Row) (roots : List Nat) : Program (Width parameters graph) 8 :=
  EnumerationDriverLayout.program parameters graph (Width parameters graph) rows roots

theorem retained_fits (parameters : Parameters) (graph : DAG parameters.channels) :
    retained parameters graph < 2 ^ Width parameters graph := by
  have room := SharedMachineCapacity.capacity (retained parameters graph) graph.countedSize (selectedSize parameters).total
  exact (by omega : retained parameters graph ≤ 131072 * (retained parameters graph + graph.countedSize + (selectedSize parameters).total + 1)).trans_lt room

theorem code_and_scratch (parameters : Parameters) (graph : DAG parameters.channels)
    (rows : List ForestIndexedOperands.Row) (roots : List Nat) (rootMatches : ForestIndexedOperands.RootsMatch graph roots) :
    (EnumerationDriverCode.code parameters graph (Width parameters graph) 0 rows roots).length +
      EnumerationUniformPrepared.preparedSize graph ≤ retained parameters graph := by
  have code := EnumerationDriverCode.code_length_bound parameters graph (Width parameters graph) 0 rows roots rootMatches
  have scratch := EnumerationUniformPrepared.preparedSize_le graph
  have size := graph.countedSize_eq
  dsimp [retained]
  omega

set_option maxHeartbeats 2000000 in
theorem context (parameters : Parameters) (graph : DAG parameters.channels) (guarded : graph.Guarded)
    (rows : List ForestIndexedOperands.Row) (roots : List Nat) (matched : ForestIndexedOperands.RowsMatch graph rows)
    (heads : UniformDAGSource.HeadsMatch graph rows matched) (rootMatches : ForestIndexedOperands.RootsMatch graph roots) :
    Context parameters graph (retained parameters graph) 0 rows roots (program parameters graph rows roots) := by
  have present := EnumerationDriverLayout.resident_at parameters graph (Width parameters graph) rows roots
  have extent := code_and_scratch parameters graph rows roots rootMatches
  have room := retained_fits parameters graph
  have oracleEnd := EnumerationDriverBounds.block_end parameters graph (Width parameters graph) 0 rows roots 16 (by decide)
  simp only [EnumerationDriverLayout.entries, EnumerationDriverCode.chunks, List.getElem_cons_succ, List.getElem_cons_zero, Nat.zero_add] at oracleEnd
  have packetSize : (EnumerationPrefixOracle.packet parameters (Width parameters graph) rows roots).size = SharedDetectorPrepared.packetSize graph :=
    SharedDetectorPrepared.packet_size graph rows roots matched rootMatches (assignmentOfSet {parameters.bridge.target})
  have codeFits : (EnumerationDriverCode.code parameters graph (Width parameters graph) 0 rows roots).length < 2 ^ Width parameters graph :=
    (Nat.le_add_right _ _).trans_lt (extent.trans_lt room)
  have oracleFits := (Nat.add_le_add_right oracleEnd (EnumerationUniformPrepared.preparedSize graph)).trans extent
  refine ⟨guarded, matched, heads, rootMatches, present, by simpa only [Nat.zero_add] using codeFits, oracleFits, ?_⟩
  rw [packetSize]
  change SharedDetectorPrepared.packetSize graph + 2 * parameters.channels < 2 ^ Width parameters graph
  have size := graph.countedSize_eq
  dsimp [SharedDetectorPrepared.packetSize, SharedDetectorPrepared.maskBase, SharedDetectorPrepared.rootBase]
  dsimp [retained] at room
  omega

end Controller.Cost.EnumerationDriverCapacity
