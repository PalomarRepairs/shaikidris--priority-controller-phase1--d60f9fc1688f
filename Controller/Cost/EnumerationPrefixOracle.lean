module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.EnumerationPrefixCall
public import Controller.Cost.EnumerationUniformOracleBounds

@[expose] public section

/-! A complete prefix query: the fixed caller, actual fixed returning oracle,
and prefix restoration execute in the same immutable resident program. -/
namespace Controller.Cost.EnumerationPrefixOracle
open Controller.Decoder Controller.Decoder.DAG Controller.Cost.GateProgram
open Controller.Cost.ForestIndexedOperands Controller.Cost.UniformDAGSource Controller.Cost.UniformDAGRun
open Controller.Cost.ForestInputPrefixStored Controller.Cost.ForestInputStored
open Controller.Native Controller.Native.SourceController Controller.Cost.NativeSourceExecution

abbrev Width (parameters : Parameters) (graph : DAG parameters.channels) (retained : Nat) :=
  EnumerationUniformScan.Width parameters graph retained

def packet (parameters : Parameters) (width : Nat) (rows : List Row) (roots : List Nat) : Array (Word width) :=
  channelHeap (packetHeaderHeap width parameters.channels rows roots) rows roots
    (assignmentOfSet {parameters.bridge.target})

def masks (parameters : Parameters) (width : Nat) (T F : Finset (Fin parameters.channels)) : List (Word width) :=
  EnumerationMasks.masksOf width (extensionBase parameters.buses parameters.bridge.target T) F

@[simp] theorem masks_length (parameters : Parameters) (width : Nat) (T F : Finset (Fin parameters.channels)) :
    (masks parameters width T F).length = 2 * parameters.channels := EnumerationMasks.masksOf_length _ _ _

def callCode (parameters : Parameters) (graph : DAG parameters.channels) (width entry oracle : Nat) : List (Instruction width 8) :=
  EnumerationPrefixCall.code width entry oracle parameters.bridge.target.val
    (SharedDetectorPrepared.packetSize graph) (2 * parameters.channels)

def oracleCode (parameters : Parameters) (graph : DAG parameters.channels) (width : Nat)
    (rows : List Row) (roots : List Nat) (entry back : Nat) : List (Instruction width 8) :=
  EnumerationUniformOracle.code parameters graph ∅ ∅ width rows roots entry back

set_option maxHeartbeats 2000000 in
theorem execution (parameters : Parameters) (graph : DAG parameters.channels) (guarded : graph.Guarded)
    (T F : Finset (Fin parameters.channels))
    (consistent : FixedConsistent (extensionBase parameters.buses parameters.bridge.target T) F)
    (retained callEntry oracleEntry returnEntry : Nat) (program : Program (Width parameters graph retained) 8)
    (rows : List Row) (roots : List Nat) (matched : RowsMatch graph rows) (heads : HeadsMatch graph rows matched)
    (rootMatches : RootsMatch graph roots) (state : State (Width parameters graph retained) 8)
    (position : state.pc = word (Width parameters graph retained) callEntry) (running : state.halted = false)
    (heapStored : state.heap = packet parameters (Width parameters graph retained) rows roots ++
      (masks parameters (Width parameters graph retained) T F).toArray)
    (callRoom : callEntry + 22 < 2 ^ (Width parameters graph retained))
    (returnRoom : returnEntry + 4 * parameters.channels + 2 < 2 ^ (Width parameters graph retained))
    (heapFits : (packet parameters (Width parameters graph retained) rows roots).size + 2 * parameters.channels <
      2 ^ (Width parameters graph retained))
    (oracleRoom : oracleEntry + (oracleCode parameters graph (Width parameters graph retained) rows roots oracleEntry returnEntry).length +
      EnumerationUniformPrepared.preparedSize graph ≤ retained)
    (callAt : SharedRootRead.BlockAt program callEntry (callCode parameters graph (Width parameters graph retained) callEntry oracleEntry))
    (oracleAt : SharedRootRead.BlockAt program oracleEntry (oracleCode parameters graph (Width parameters graph retained) rows roots oracleEntry returnEntry))
    (returnAt : SharedRootRead.BlockAt program returnEntry (EnumerationPrefixReturn.code (Width parameters graph retained) (2 * parameters.channels))) :
    ∃ answer : Bool, ∃ final ticks peak,
      Execution program state final ticks peak ∧
      ticks ≤ 24 * parameters.channels + 16 + (parameters.channels + graph.roots.length + 1) * (8000 * (graph.countedSize + 1)) ∧
      peak ≤ state.liveWords + 244 * (graph.countedSize + 1) ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word (Width parameters graph retained) (returnEntry + 4 * parameters.channels + 2) ∧
      final.halted = false ∧ final.reg 3 = state.reg 3 ∧ final.reg 5 = state.reg 5 ∧
      final.reg 4 = word (Width parameters graph retained) (if answer then 1 else 0) ∧
      (answer = true ↔ ∃ output : Fin graph.roots.length, SharedDetectorFeasibility.AtRoot parameters graph T F output) := by
  have packetSize : (packet parameters (Width parameters graph retained) rows roots).size = SharedDetectorPrepared.packetSize graph :=
    SharedDetectorPrepared.packet_size graph rows roots matched rootMatches _
  have maskSize := masks_length parameters (Width parameters graph retained) T F
  have positive : 0 < (packet parameters (Width parameters graph retained) rows roots).size := by
    rw [packetSize]
    simp only [SharedDetectorPrepared.packetSize, SharedDetectorPrepared.maskBase, SharedDetectorPrepared.rootBase]
    omega
  have callerAt : SharedRootRead.BlockAt program callEntry
      (EnumerationPrefixCall.code (Width parameters graph retained) callEntry oracleEntry parameters.bridge.target.val
        (packet parameters (Width parameters graph retained) rows roots).size
        (masks parameters (Width parameters graph retained) T F).length) := by
    rw [packetSize, maskSize]; exact callAt
  obtain ⟨called, callPeak, front, frontSpace, frontHeap, frontStack, frontOutput, frontPC, frontRunning, frontHead⟩ :=
    EnumerationPrefixCall.execution program state callEntry oracleEntry parameters.bridge.target.val
      (packet parameters (Width parameters graph retained) rows roots) (masks parameters (Width parameters graph retained) T F)
      position running heapStored positive callRoom (by simpa only [maskSize] using heapFits) callerAt
  have sameCode := EnumerationUniformOracle.code_prefix_irrel parameters graph T F ∅ ∅
    (Width parameters graph retained) rows roots oracleEntry returnEntry
  have queryAt : SharedRootRead.BlockAt program oracleEntry
      (EnumerationUniformOracle.code parameters graph T F (Width parameters graph retained) rows roots oracleEntry returnEntry) := by
    rw [sameCode]; exact oracleAt
  obtain ⟨answer, decided, oracleTicks, oraclePeak, oracleTrace, oracleRunning, oraclePC, decision,
      oracleHeap, oracleStack, oracleOutput, oracleTime, oracleSpace, meaning⟩ :=
    EnumerationUniformOracle.execution parameters graph guarded T F consistent retained oracleEntry returnEntry program
      rows roots matched heads rootMatches (state.reg 3 :: state.reg 5 :: state.stack) called frontPC frontRunning frontHeap
      frontStack frontHead (by rw [sameCode]; exact oracleRoom) queryAt
  obtain ⟨final, back, finalHeap, finalStack, finalOutput, finalPC, finalRunning, finalDepth, finalMode, finalDecision⟩ :=
    EnumerationPrefixReturn.execution program decided returnEntry (masks parameters (Width parameters graph retained) T F)
      (state.reg 3) (state.reg 5) state.stack oraclePC oracleRunning (oracleStack.trans frontStack)
      (by rw [maskSize]; omega) (by rw [oracleHeap, frontHeap, maskSize]; exact heapFits)
      (by rw [maskSize]; exact returnAt)
  have calledLive : called.liveWords = state.liveWords + 2 := by
    simp only [State.liveWords, frontHeap, frontStack, frontOutput, heapStored,
      Array.size_append, List.size_toArray, List.length_append, List.length_cons]
    omega
  have decidedLive : decided.liveWords = called.liveWords := by
    simp only [State.liveWords, oracleHeap, oracleStack, oracleOutput]
  have joined := front.append (oracleTrace.append back)
  have size := graph.countedSize_eq
  refine ⟨answer, final, _, max callPeak (max oraclePeak decided.liveWords), joined, ?_, ?_, ?_, finalStack, ?_, ?_,
    finalRunning, finalDepth, finalMode, finalDecision.trans decision, meaning⟩
  · rw [maskSize]
    omega
  · clear * - calledLive decidedLive maskSize oracleSpace frontSpace size
    rw [calledLive] at oracleSpace
    rw [maskSize] at frontSpace
    simp only [max_le_iff]
    omega
  · rw [finalHeap, oracleHeap, frontHeap]; exact heapStored.symm
  · rw [finalOutput, oracleOutput, frontOutput]
  · have offsetEq : returnEntry + 2 * (masks parameters (Width parameters graph retained) T F).length + 2 =
        returnEntry + 4 * parameters.channels + 2 := by rw [maskSize]; omega
    exact finalPC.trans (congrArg (word (Width parameters graph retained)) offsetEq)

/-- Instantiation of the actual oracle answer as D08's prefix query. -/
theorem answer_iff_query (parameters : Parameters) (graph : DAG parameters.channels) (guarded : graph.Guarded)
    (depth : Nat) (partialSet : Finset (Fin parameters.channels)) (answer : Bool)
    (meaning : answer = true ↔ ∃ output : Fin graph.roots.length,
      SharedDetectorFeasibility.AtRoot parameters graph (Enumeration.fixedTrue depth partialSet)
        (Enumeration.fixedFalse depth partialSet) output) :
    answer = true ↔ Enumeration.query graph parameters.buses parameters.bridge.target true depth partialSet = true :=
  meaning.trans (EnumerationMasks.atRoot_iff_query parameters graph guarded depth partialSet)

end Controller.Cost.EnumerationPrefixOracle
