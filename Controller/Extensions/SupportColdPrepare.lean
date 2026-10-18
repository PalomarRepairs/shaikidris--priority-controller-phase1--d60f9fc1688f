module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Extensions.SupportHealthyPrepare

@[expose] public section

/-! Cold preparation consumes the encoded original DAG and singleton channel
vector from an empty heap. The healthy node table is computed and retained
by the same fetched run, with caller suffix and output charged explicitly. -/
namespace Controller.Extensions.SupportColdPrepare
open Controller Controller.Decoder Controller.Decoder.DAG Controller.Cost
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestInputStored
open Controller.Cost.ForestInputPrefixStored Controller.Cost.SharedDetectorAssembly

def code (width : Nat) (graph : DAG n) (rows : List Row) (roots : List Nat) : List (Instruction width 8) :=
  let count := SharedDetectorPrepared.packetSize graph
  SharedWitnessPark.code width count ++ SupportHealthyPrepare.code width n graph.nodeCount rows roots (2*count)

theorem packet_bound (graph : DAG n) : SharedDetectorPrepared.packetSize graph ≤ 7*graph.countedSize+5 := by
  have size := graph.countedSize_eq
  simp only [SharedDetectorPrepared.packetSize,SharedDetectorPrepared.maskBase,SharedDetectorPrepared.rootBase]
  omega

theorem code_bound (graph : DAG n) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (rootMatches : RootsMatch graph roots) :
    (code width graph rows roots).length ≤ 400*(graph.countedSize+1) := by
  have prep := SupportHealthyPrepare.code_bound (width := width)
    (entry := 2*SharedDetectorPrepared.packetSize graph) graph rows roots matched rootMatches
  have packet := packet_bound graph
  simp only [code,List.length_append,SharedWitnessPark.code_length]
  omega

set_option maxHeartbeats 1400000 in
theorem execution (resident : Program width 8) (state : State width 8)
    (graph : DAG n) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (heads : UniformDAGSource.HeadsMatch graph rows matched)
    (rootMatches : RootsMatch graph roots) (target : Channel n) (suffix : List (Word width))
    (empty : state.heap = #[]) (position : state.pc = word width 0) (running : state.halted = false)
    (input : state.stack = SharedDetectorCold.inputWords width rows roots (assignmentOfSet {target}) ++ suffix)
    (capacity : 4096*(graph.countedSize+1)<2^width)
    (present : SharedRootRead.BlockAt resident 0 (code width graph rows roots)) :
    ∃ final ticks peak, Execution resident state final ticks peak ∧
      ticks ≤ 500*(graph.countedSize+1) ∧ peak ≤ state.liveWords+30*(graph.countedSize+1) ∧
      final.heap = cacheHeap width (SupportCandidate.header width n rows roots (graph.evalTable (assignmentOfSet {target}))) rows roots ∧
      final.stack = suffix ∧ final.output = state.output ∧
      final.pc = word width (code width graph rows roots).length ∧ final.halted = false := by
  let words := SharedDetectorCold.inputWords width rows roots (assignmentOfSet {target})
  let count := SharedDetectorPrepared.packetSize graph
  have length : words.length = count := SharedDetectorCold.inputWords_length width graph rows roots matched rootMatches _
  have packet := packet_bound graph
  change count ≤ _ at packet
  have codeSize := code_bound (width := width) graph rows roots matched rootMatches
  unfold code at present
  have loadAt := block_left resident 0 _ _ present
  have prepareAt := block_right resident 0 _ _ present
  simp only [SharedWitnessPark.code_length,Nat.zero_add] at prepareAt
  obtain ⟨loaded,load,lh,ls,lo,lp,lr,_⟩ :=
    SharedWitnessPark.execution resident state words suffix 0 position running (by rw [length]; omega)
      (by rw [empty,length]; simp; omega) input (by simpa only [length] using loadAt)
  have loadedHeap : loaded.heap = channelHeap (UniformDAGRun.packetHeaderHeap width n rows roots) rows roots
      (assignmentOfSet {target}) := by
    rw [lh,empty]
    exact SharedDetectorCold.inputWords_heap width rows roots _
  obtain ⟨final,pt,pp,prepare,time,space,fh,fs,fo,fp,fr⟩ :=
    SupportHealthyPrepare.execution resident loaded graph rows roots matched heads rootMatches target (2*count)
      loadedHeap (by simpa only [length,Nat.zero_add] using lp) lr (by omega) capacity prepareAt
  have loadedLive : loaded.liveWords = state.liveWords := by
    simp only [State.liveWords,lh,ls,lo,empty,Array.size_append,Array.size_empty,List.size_toArray,
      input,List.length_append,words]; omega
  refine ⟨final,2*count+pt,max state.liveWords pp,?_,by omega,by omega,fh,fs.trans ls,fo.trans lo,?_,fr⟩
  · simpa only [length] using load.append prepare
  · rw [fp]
    congr 1
    simp only [code,List.length_append,SharedWitnessPark.code_length]
    rfl

end Controller.Extensions.SupportColdPrepare
