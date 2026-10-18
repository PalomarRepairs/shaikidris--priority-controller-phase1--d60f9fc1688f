module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Extensions.SupportHealthyLayout
public import Controller.Extensions.SupportSourceRound
public import Controller.Cost.SharedDetectorCold

@[expose] public section

/-! The healthy singleton is evaluated by the shared DAG interpreter. Its
value table is then installed in the retained source header by fetched reads
and a physical heap exchange. No healthy evaluation table is an input. -/
namespace Controller.Extensions.SupportHealthyPrepare
open Controller Controller.Decoder Controller.Decoder.DAG Controller.Cost Controller.Cost.GateProgram
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestInputStored
open Controller.Cost.ForestInputPrefixStored Controller.Cost.SharedDetectorAssembly

def code (width n m : Nat) (rows : List Row) (roots : List Nat) (entry : Nat) : List (Instruction width 8) :=
  let header := UniformDAGRun.packetHeaderHeap width n rows roots
  let oldCount := (cacheHeap width header rows roots).size+n+m
  (SupportSourceRound.code width n header rows roots entry).toList ++
    SupportSourceRepack.code width (entry+126) oldCount (SupportHealthyLayout.plan width n m header rows roots)

theorem code_bound (graph : DAG n) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (rootMatches : RootsMatch graph roots) :
    (code width n graph.nodeCount rows roots entry).length ≤ 300*(graph.countedSize+1) := by
  have bound := SupportSourceRepack.code_bound (width := width) (entry := entry+126)
    (oldCount := (cacheHeap width (UniformDAGRun.packetHeaderHeap width n rows roots) rows roots).size+n+graph.nodeCount)
    (SupportHealthyLayout.plan width n graph.nodeCount (UniformDAGRun.packetHeaderHeap width n rows roots) rows roots)
  rw [SupportHealthyLayout.plan_length] at bound
  have size := graph.countedSize_eq
  obtain ⟨children,guards⟩ := matched_incidence_lengths graph rows matched
  have rootLength : roots.length = graph.roots.length := by rw [rootMatches]; simp
  simp only [cacheHeap_size,UniformDAGRun.packetHeaderHeap_size,matched.length_eq,children,guards,rootLength] at bound
  simp only [code,List.length_append,Array.length_toList,SupportSourceRound.code_size,
    cacheHeap_size,UniformDAGRun.packetHeaderHeap_size,matched.length_eq,children,guards,rootLength]
  omega

set_option maxHeartbeats 1600000 in
theorem execution (resident : Program width 8) (state : State width 8)
    (graph : DAG n) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (heads : UniformDAGSource.HeadsMatch graph rows matched)
    (rootMatches : RootsMatch graph roots) (target : Channel n) (entry : Nat)
    (heapStored : state.heap = channelHeap (UniformDAGRun.packetHeaderHeap width n rows roots) rows roots
      (assignmentOfSet {target}))
    (position : state.pc = word width entry) (running : state.halted = false)
    (entryBound : entry ≤ 128*(graph.countedSize+1)) (capacity : 4096*(graph.countedSize+1)<2^width)
    (present : SharedRootRead.BlockAt resident entry (code width n graph.nodeCount rows roots entry)) :
    ∃ final ticks peak, Execution resident state final ticks peak ∧
      ticks ≤ 400*(graph.countedSize+1) ∧ peak ≤ state.liveWords+30*(graph.countedSize+1) ∧
      final.heap = cacheHeap width (SupportCandidate.header width n rows roots (graph.evalTable (assignmentOfSet {target}))) rows roots ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry+(code width n graph.nodeCount rows roots entry).length) ∧ final.halted = false := by
  let header := UniformDAGRun.packetHeaderHeap width n rows roots
  let healthy := graph.evalTable (assignmentOfSet {target})
  let plan := SupportHealthyLayout.plan width n graph.nodeCount header rows roots
  let oldCount := (cacheHeap width header rows roots).size+n+graph.nodeCount
  have size := graph.countedSize_eq
  obtain ⟨children,guards⟩ := matched_incidence_lengths graph rows matched
  have rootLength : roots.length = graph.roots.length := by rw [rootMatches]; simp
  have cachedSize : (cacheHeap width header rows roots).size ≤ 6*graph.countedSize+5 := by
    simp only [cacheHeap_size,header,UniformDAGRun.packetHeaderHeap_size,matched.length_eq,children,guards,rootLength]
    omega
  have planSize : plan.length = (cacheHeap width header rows roots).size+graph.nodeCount :=
    SupportHealthyLayout.plan_length header rows roots
  have oldSize : oldCount ≤ 8*graph.countedSize+5 := by dsimp only [oldCount]; omega
  unfold code at present
  have roundAt := block_left resident entry _ _ present
  have repackAt := block_right resident entry _ _ present
  simp only [Array.length_toList,SupportSourceRound.code_size] at repackAt
  have countCell : state.heap[1]? = some (word width graph.nodeCount) := by
    rw [heapStored]
    unfold channelHeap withValues
    rw [Array.getElem?_append_left (by simp; omega),Array.getElem?_eq_getElem (by simp; omega)]
    exact congrArg some (UniformDAGRun.packet_node_count graph rows roots matched)
  obtain ⟨evaluated,et,ep,evaluation,etime,espace,eh,es,eo,ec,er,_⟩ :=
    SupportSourceRound.execution resident state header graph rows roots matched heads (assignmentOfSet {target}) entry
      heapStored countCell position running (by omega) (by omega) (block_code _ _ _ roundAt)
  have values := SupportHealthyLayout.stored (width := width) header rows roots (assignmentOfSet {target}) healthy
  have physical : List.Forall₂ (ResolvedSourceEmit.Stored evaluated.heap) plan
      (cacheHeap width (SupportCandidate.header width n rows roots healthy) rows roots).toList := by
    simpa only [eh,plan,healthy,SupportCandidate.header,header] using values
  have evalSize : evaluated.heap.size = oldCount := by simpa only [eh,evaluationHeap_size,oldCount] using rfl
  have oldPositive : 0<oldCount := by
    have headerPositive : 0<(cacheHeap width header rows roots).size := by simp [header]
    dsimp only [oldCount]; omega
  obtain ⟨final,rt,rp,repack,rtime,rspace,rh,rs,ro,rc,rr⟩ :=
    SupportSourceRepack.execution resident evaluated (entry+126) plan _ physical
      (by simpa only [evalSize] using oldPositive) ec er
      (by omega) (by rw [evalSize]; omega) (by simpa only [evalSize,plan] using repackAt)
  have evaluatedLive : evaluated.liveWords = state.liveWords+graph.nodeCount := by
    have initialHeap : state.heap = channelHeap header rows roots (assignmentOfSet {target}) := heapStored
    simp only [State.liveWords,eh,initialHeap,evaluationHeap_size,channelHeap_size,es,eo]; omega
  refine ⟨final,et+rt,max ep rp,evaluation.append repack,by omega,by omega,
    by simpa only [Array.toArray_toList] using rh,rs.trans es,ro.trans eo,?_,rr⟩
  rw [rc]
  congr 1
  simp only [code,List.length_append,Array.length_toList,SupportSourceRound.code_size,evalSize]
  dsimp only [plan,oldCount,header]
  omega

end Controller.Extensions.SupportHealthyPrepare
