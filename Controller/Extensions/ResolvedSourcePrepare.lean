module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Extensions.ResolvedSourceCallback

@[expose] public section

/-! A successful selector mask is converted to the zero solver's physical
packet and dictionary entry. The original heap is reclaimed after its source
fields have been read; the terminal native continuation consumes this entry. -/
namespace Controller.Extensions.ResolvedSourcePrepare
open Controller Controller.Decoder Controller.Decoder.DAG Controller.Cost
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestInputStored
open Controller.Cost.SharedDetectorAssembly

structure Positions where
  copy : Nat
  nodes : Nat
  channels : Nat
  handoff : Nat
  solver : Nat

def positions (width : Nat) (graph : DAG n) (packet : Array (Word width)) (rows : List Row) (roots : List Nat)
    (b : Nat) (target : Channel n) (reference : Fin graph.nodeCount) (rootSlot entry : Nat) : Positions :=
  let count := ResolvedSourceCallback.querySize graph b target reference
  let copy := entry+(ResolvedSourceCallback.emitCode width graph packet rows roots b target rootSlot entry).length
  let nodes := copy+10
  let channels := nodes+3
  let handoff := channels+3
  ⟨copy,nodes,channels,handoff,handoff+10+2*(2+count)+4*(n+graph.nodeCount)⟩

def code (width : Nat) (graph : DAG n) (packet : Array (Word width)) (rows : List Row) (roots : List Nat)
    (b : Nat) (target : Channel n) (reference : Fin graph.nodeCount) (rootSlot entry sourceCount : Nat) : List (Instruction width 8) :=
  let p := positions width graph packet rows roots b target reference rootSlot entry
  let count := ResolvedSourceCallback.querySize graph b target reference
  ResolvedSourceCallback.emitCode width graph packet rows roots b target rootSlot entry ++
    ((SharedWitnessCopy.code width p.copy p.nodes sourceCount count).toList ++
    (ResolvedSourceRead.pushCode width 1 ++
    (ResolvedSourceRead.pushCode width 0 ++
    ResolvedPacketHandoff.code width p.handoff (sourceCount+count) (2+count) (n+graph.nodeCount))))

theorem code_end (graph : DAG n) (packet : Array (Word width)) (rows : List Row) (roots : List Nat)
    (b : Nat) (target : Channel n) (reference : Fin graph.nodeCount) :
    entry+(code width graph packet rows roots b target reference rootSlot entry sourceCount).length =
      (positions width graph packet rows roots b target reference rootSlot entry).solver := by
  simp only [code,List.length_append,Array.length_toList,SharedWitnessCopy.code_size,
    ResolvedSourceRead.pushCode_length,ResolvedPacketHandoff.code_length,positions]
  omega

theorem code_bound (graph : DAG n) (packet : Array (Word width)) (rows : List Row) (roots : List Nat)
    (b : Nat) (target : Channel n) (reference : Fin graph.nodeCount) :
    (code width graph packet rows roots b target reference rootSlot entry sourceCount).length ≤ 200*(graph.countedSize+1) := by
  have emit := ResolvedSourceEmit.code_length (entry := entry)
    (ResolvedSourcePlan.query width graph packet rows roots b target rootSlot)
  rw [ResolvedSourcePlan.query_length graph packet rows roots b target reference] at emit
  have count := ResolvedResident.rows_bound graph ∅ b target reference
  have size := graph.countedSize_eq
  simp only [code,List.length_append,Array.length_toList,SharedWitnessCopy.code_size,
    ResolvedSourceRead.pushCode_length,ResolvedPacketHandoff.code_length,
    ResolvedSourceCallback.emitCode,ResolvedSourceCallback.querySize]
  omega

set_option maxHeartbeats 1800000 in
theorem execution (resident : Program width 8) (state : State width 8)
    (packet : Array (Word width)) (graph : DAG n) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (right : Finset (Fin graph.nodeCount)) (b : Nat)
    (target : Channel n) (reference root : Fin graph.nodeCount) (rootSlot entry : Nat)
    (heapStored : state.heap = withValues (cacheHeap width packet rows roots) (ResolvedSourcePlan.selectorValues graph right))
    (rootStored : state.heap[rootSlot]? = some (word width root.val))
    (channelStored : state.heap[0]? = some (word width n))
    (nodeStored : state.heap[1]? = some (word width graph.nodeCount))
    (positive : 0<state.heap.size) (position : state.pc = word width entry) (running : state.halted = false)
    (entryBound : entry ≤ 128*(graph.countedSize+1)) (sourceBound : state.heap.size ≤ 40*(graph.countedSize+1))
    (capacity : 4096*(graph.countedSize+1)<2^width)
    (present : SharedRootRead.BlockAt resident entry
      (code width graph packet rows roots b target reference rootSlot entry state.heap.size)) :
    let p := positions width graph packet rows roots b target reference rootSlot entry
    ∃ final ticks peak, Execution resident state final ticks peak ∧ ticks ≤ 1000*(graph.countedSize+1) ∧
      peak ≤ state.liveWords+30*(graph.countedSize+1) ∧ final.output = state.output ∧
      p.solver ≤ 512*(graph.countedSize+1) ∧
      ResolvedResident.Ready graph right b target root p.solver state.stack final := by
  let p := positions width graph packet rows roots b target reference rootSlot entry
  let count := ResolvedSourceCallback.querySize graph b target reference
  let values := ResolvedSourcePlan.words width graph right b target root
  have size := graph.countedSize_eq
  have sameCount : values.length = count := by
    have same := ResolvedResident.source_size_uniform (width := width) graph right ∅ b target root reference
    simp only [ResolvedResident.sourceHeap_size] at same
    simpa only [values,ResolvedSourcePlan.words,List.length_map,count,ResolvedSourceCallback.querySize] using
      (show (ResolvedResident.rows graph right b target root).flatten.length =
        (ResolvedResident.rows graph ∅ b target reference).flatten.length by omega)
  have countBound : count ≤ 11*(graph.countedSize+1) := by
    have bound := ResolvedSourcePlan.words_bound (width := width) graph right b target root
    rw [sameCount] at bound; exact bound
  have clauseLength : (ResolvedResident.rows graph right b target root).flatten.length = count := by
    simpa only [values,ResolvedSourcePlan.words,List.length_map] using sameCount
  have valueLength : (ResolvedSourcePlan.words width graph right b target root).length = count := sameCount
  have emitBound : (ResolvedSourceCallback.emitCode width graph packet rows roots b target rootSlot entry).length ≤ 132*(graph.countedSize+1) := by
    have bound := ResolvedSourceEmit.code_length (entry := entry)
      (ResolvedSourcePlan.query width graph packet rows roots b target rootSlot)
    rw [ResolvedSourcePlan.query_length graph packet rows roots b target reference] at bound
    dsimp only [count,ResolvedSourceCallback.querySize] at countBound
    exact bound.trans (by omega)
  have rawEmitBound : (ResolvedSourceEmit.code width entry
      (ResolvedSourcePlan.query width graph packet rows roots b target rootSlot)).length ≤ 132*(graph.countedSize+1) := emitBound
  have solverBound : p.solver ≤ 512*(graph.countedSize+1) := by
    dsimp only [p,positions] at emitBound ⊢
    dsimp only [count] at countBound
    omega
  unfold code at present
  have emitAt := block_left resident entry _ _ present
  have afterEmit := block_right resident entry _ _ present
  have copyAt := block_left resident p.copy _ _ afterEmit
  have afterCopy := block_right resident p.copy _ _ afterEmit
  simp only [Array.length_toList,SharedWitnessCopy.code_size] at afterCopy
  have nodesAt := block_left resident p.nodes _ _ afterCopy
  have afterNodes := block_right resident p.nodes _ _ afterCopy
  simp only [ResolvedSourceRead.pushCode_length] at afterNodes
  have channelsAt := block_left resident p.channels _ _ afterNodes
  have handoffAt := block_right resident p.channels _ _ afterNodes
  simp only [ResolvedSourceRead.pushCode_length] at handoffAt
  obtain ⟨emitted,et,emit,etime,eh,es,eo,ep,er⟩ :=
    ResolvedSourcePlan.execution resident state packet graph rows roots matched right b target root rootSlot entry
      heapStored rootStored (by omega) position running (by omega) (by omega) emitAt
  change emitted.heap = state.heap++values.toArray at eh
  have sourceWords : emitted.heap.size = state.heap.size+count := by
    simp only [eh,Array.size_append,List.size_toArray,sameCount]
  obtain ⟨copied,cp,copy,cspace,ch,cs,co,cc,cr,_⟩ :=
    SharedWitnessCopy.execution resident emitted state.heap.size values p.copy p.nodes ep er
      (by dsimp only [p,positions] at emitBound ⊢; omega) positive (by omega)
      (by intro i below; rw [eh,Array.getElem?_append_right (Nat.le_add_right _ _)];
          simp only [Nat.add_sub_cancel_left,List.getElem?_toArray,List.getElem?_eq_getElem below])
      (by simpa only [sameCount] using block_code _ _ _ copyAt)
  obtain ⟨nodes,nt,nh,ns,no,np,nr,_⟩ :=
    ResolvedSourceRead.push_execution resident copied p.nodes 1 (word width graph.nodeCount)
      (by rw [ch,eh,Array.getElem?_append_left (Array.getElem?_eq_some_iff.mp nodeStored).1]; exact nodeStored)
      cc cr (by dsimp only [p,positions] at emitBound ⊢; omega) (by rw [ch,sourceWords]; omega) nodesAt
  obtain ⟨channels,ct,cph,cps,cpo,cpp,cpr,_⟩ :=
    ResolvedSourceRead.push_execution resident nodes p.channels 0 (word width n)
      (by rw [nh,ch,eh,Array.getElem?_append_left (Array.getElem?_eq_some_iff.mp channelStored).1]; exact channelStored)
      (by simpa only [p,positions] using np) nr (by dsimp only [p,positions] at emitBound ⊢; omega)
      (by rw [nh,ch,sourceWords]; omega) channelsAt
  have input : channels.stack = ResolvedPacketHandoff.packetWords width n graph.nodeCount
      (ResolvedResident.rows graph right b target root) ++ state.stack := by
    rw [cps,ns,cs,es]
    simp only [ResolvedPacketHandoff.packetWords,ResolvedResident.packet,Array.toList_append,List.toList_toArray,
      values,ResolvedSourcePlan.words,List.cons_append,List.append_assoc]
    rfl
  have channelHeapSize : channels.heap.size = state.heap.size+count := by rw [cph,nh,ch,sourceWords]
  obtain ⟨final,ht,hp,handoff,htime,hspace,_,ho,ready⟩ :=
    ResolvedPacketHandoff.execution resident channels graph right b target root p.handoff state.stack input
      (by simpa only [p,positions] using cpp) cpr
      (by rw [clauseLength]; dsimp only [p,positions] at emitBound ⊢; omega)
      (by rw [channelHeapSize]; omega) (by rw [clauseLength]; omega)
      (by simpa only [channelHeapSize,clauseLength,p,positions,count] using handoffAt)
  have emittedLive : emitted.liveWords = state.liveWords+count := by
    simp only [State.liveWords,eh,es,eo,Array.size_append,List.size_toArray,sameCount]; omega
  have copiedLive : copied.liveWords = emitted.liveWords+count := by
    simp only [State.liveWords,ch,cs,co,List.length_append,sameCount]; omega
  have nodesLive : nodes.liveWords = copied.liveWords+1 := by
    simp only [State.liveWords,nh,ns,no,List.length_cons]; omega
  have channelsLive : channels.liveWords = nodes.liveWords+1 := by
    simp only [State.liveWords,cph,cps,cpo,List.length_cons]; omega
  refine ⟨final,_,_,emit.append (copy.append (nt.append (ct.append handoff))),?_,?_,
    ho.trans (cpo.trans (no.trans (co.trans eo))),solverBound,?_⟩
  · rw [channelHeapSize,clauseLength] at htime
    omega
  · rw [emittedLive] at cspace
    rw [channelsLive,nodesLive,copiedLive,emittedLive] at hspace
    omega
  · simpa only [clauseLength,p,positions,count,ResolvedSourceCallback.querySize] using ready

end Controller.Extensions.ResolvedSourcePrepare
