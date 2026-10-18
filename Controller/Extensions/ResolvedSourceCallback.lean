module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Extensions.ResolvedSourcePlan
public import Controller.Extensions.ResolvedSourcePark
public import Controller.Extensions.ResolvedPacketHandoff
public import Controller.Extensions.ResolvedSourceReturn

@[expose] public section

/-! A selector query reads its original DAG, generates the selected occurrence
packet, invokes the returning zero solver, and restores the traversal heap.
The original heap is parked on the stack while the solver owns the heap. -/
namespace Controller.Extensions.ResolvedSourceCallback
open Controller Controller.Decoder Controller.Decoder.DAG Controller.CNF
open Controller.Extensions.BoundedAnd Controller.Cost Controller.Cost.GateProgram
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestInputStored
open Controller.Cost.SharedDetectorAssembly

structure Positions where
  emit : Nat
  copyWords : Nat
  pushNodes : Nat
  pushChannels : Nat
  handoff : Nat
  solver : Nat
  restore : Nat

def querySize (graph : DAG n) (b : Nat) (target : Channel n) (reference : Fin graph.nodeCount) : Nat :=
  (ResolvedResident.rows graph ∅ b target reference).flatten.length

def emitCode (width : Nat) (graph : DAG n) (packet : Array (Word width)) (rows : List Row) (roots : List Nat)
    (b : Nat) (target : Channel n) (rootSlot entry : Nat) : List (Instruction width 8) :=
  ResolvedSourceEmit.code width entry (ResolvedSourcePlan.query width graph packet rows roots b target rootSlot)

def positions (width : Nat) (graph : DAG n) (packet : Array (Word width)) (rows : List Row) (roots : List Nat)
    (b : Nat) (target : Channel n) (reference : Fin graph.nodeCount) (rootSlot entry : Nat) : Positions :=
  let count := querySize graph b target reference
  let emitter := entry+13
  let copyWords := emitter+(emitCode width graph packet rows roots b target rootSlot emitter).length
  let pushNodes := copyWords+10
  let pushChannels := pushNodes+3
  let handoff := pushChannels+3
  let solver := handoff+10+2*(2+count)+4*(n+graph.nodeCount)
  let keep := 2+count+2*(n+graph.nodeCount)
  let restore := solver+(ResolvedResident.queryCode graph ∅ b target reference width solver keep).length
  ⟨emitter,copyWords,pushNodes,pushChannels,handoff,solver,restore⟩

def code (width : Nat) (graph : DAG n) (packet : Array (Word width)) (rows : List Row) (roots : List Nat)
    (b : Nat) (target : Channel n) (reference : Fin graph.nodeCount) (rootSlot entry sourceCount found rejected : Nat) :
    List (Instruction width 8) :=
  let p := positions width graph packet rows roots b target reference rootSlot entry
  let count := querySize graph b target reference
  let keep := 2+count+2*(n+graph.nodeCount)
  ResolvedSourcePark.code width entry sourceCount ++
    (emitCode width graph packet rows roots b target rootSlot p.emit ++
    ((SharedWitnessCopy.code width p.copyWords p.pushNodes sourceCount count).toList ++
    (ResolvedSourceRead.pushCode width 1 ++
    (ResolvedSourceRead.pushCode width 0 ++
    (ResolvedPacketHandoff.code width p.handoff (sourceCount+count) (2+count) (n+graph.nodeCount) ++
    (ResolvedResident.queryCode graph ∅ b target reference width p.solver keep ++
    ResolvedSourceReturn.code width p.restore keep sourceCount found rejected))))))

theorem code_length_bound (graph : DAG n) (packet : Array (Word width)) (rows : List Row) (roots : List Nat)
    (b : Nat) (target : Channel n) (reference : Fin graph.nodeCount)
    (sourceBound : sourceCount ≤ 40*(graph.countedSize+1)) :
    (code width graph packet rows roots b target reference rootSlot entry sourceCount found rejected).length ≤
      1200*(graph.countedSize+1) := by
  let p := positions width graph packet rows roots b target reference rootSlot entry
  have emitBound := ResolvedSourceEmit.code_length (entry := p.emit)
    (ResolvedSourcePlan.query width graph packet rows roots b target rootSlot)
  rw [ResolvedSourcePlan.query_length graph packet rows roots b target reference] at emitBound
  have queryBound := ResolvedResident.query_code_bound (width := width) (entry := p.solver)
    (keep := 2+querySize graph b target reference+2*(n+graph.nodeCount)) graph ∅ b target reference
  have count := ResolvedResident.rows_bound graph ∅ b target reference
  have size := graph.countedSize_eq
  unfold code
  simp only [List.length_append, ResolvedSourcePark.code_length, Array.length_toList,
    SharedWitnessCopy.code_size, ResolvedSourceRead.pushCode_length, ResolvedPacketHandoff.code_length,
    ResolvedSourceReturn.code_length]
  change (ResolvedSourceEmit.code width p.emit (ResolvedSourcePlan.query width graph packet rows roots b target rootSlot)).length ≤ _ at emitBound
  dsimp only [p, querySize, emitCode] at *
  omega

theorem code_length_destinations (graph : DAG n) (packet : Array (Word width)) (rows : List Row) (roots : List Nat)
    (b : Nat) (target : Channel n) (reference : Fin graph.nodeCount)
    (rootSlot entry sourceCount firstFound firstRejected secondFound secondRejected : Nat) :
    (code width graph packet rows roots b target reference rootSlot entry sourceCount firstFound firstRejected).length =
      (code width graph packet rows roots b target reference rootSlot entry sourceCount secondFound secondRejected).length := by
  simp only [code,List.length_append,ResolvedSourceReturn.code_length]

set_option maxHeartbeats 2000000 in
theorem execution (program : Program width 8) (state : State width 8)
    (packet : Array (Word width)) (graph : DAG n) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (right : Finset (Fin graph.nodeCount)) (b : Nat)
    (target : Channel n) (reference root : Fin graph.nodeCount) (rootSlot entry found rejected : Nat)
    (heapStored : state.heap = withValues (cacheHeap width packet rows roots) (ResolvedSourcePlan.selectorValues graph right))
    (rootStored : state.heap[rootSlot]? = some (word width root.val))
    (channelStored : state.heap[0]? = some (word width n))
    (nodeStored : state.heap[1]? = some (word width graph.nodeCount))
    (positive : 0 < state.heap.size)
    (position : state.pc = word width entry) (running : state.halted = false)
    (entryBound : entry ≤ 128*(graph.countedSize+1))
    (sourceBound : state.heap.size ≤ 40*(graph.countedSize+1))
    (capacity : 4096*(graph.countedSize+1) < 2 ^ width)
    (present : SharedRootRead.BlockAt program entry
      (code width graph packet rows roots b target reference rootSlot entry state.heap.size found rejected)) :
    ∃ answer : Bool, ∃ final ticks peak, Execution program state final ticks peak ∧
      ticks ≤ 7000*(graph.countedSize+1) ∧ peak ≤ state.liveWords+300*(graph.countedSize+1) ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (if answer then found else rejected) ∧ final.halted = false ∧
      (answer = true ↔ ∃ K, Admissible b target K ∧ (resolved graph right).eval (assignmentOfSet K) root = false) := by
  let p := positions width graph packet rows roots b target reference rootSlot entry
  let count := querySize graph b target reference
  let values := ResolvedSourcePlan.words width graph right b target root
  let keep := 2+count+2*(n+graph.nodeCount)
  have size := graph.countedSize_eq
  have rowsBound := ResolvedResident.rows_bound graph right b target root
  have sameCount : values.length = count := by
    have same := ResolvedResident.source_size_uniform (width := width) graph right ∅ b target root reference
    simp only [ResolvedResident.sourceHeap_size] at same
    simpa only [values, ResolvedSourcePlan.words, List.length_map, count, querySize] using
      (show (ResolvedResident.rows graph right b target root).flatten.length =
        (ResolvedResident.rows graph ∅ b target reference).flatten.length by omega)
  have countBound : count ≤ 11*(graph.countedSize+1) := by
    have bound := ResolvedSourcePlan.words_bound (width := width) graph right b target root
    rw [sameCount] at bound
    exact bound
  have valueLength : (ResolvedSourcePlan.words width graph right b target root).length = count := sameCount
  have clauseLength : (ResolvedResident.rows graph right b target root).flatten.length = count := by
    simpa only [values, ResolvedSourcePlan.words, List.length_map] using sameCount
  have represented := ResolvedSourcePlan.query_stored packet graph rows roots matched right b target root rootSlot
    (by simpa only [heapStored] using rootStored) (by omega)
  have emitterBound : (emitCode width graph packet rows roots b target rootSlot p.emit).length ≤ 132*(graph.countedSize+1) := by
    have bound := ResolvedSourceEmit.code_length (entry := p.emit)
      (ResolvedSourcePlan.query width graph packet rows roots b target rootSlot)
    rw [represented.length_eq, sameCount] at bound
    exact bound.trans (by omega)
  have positionsBound : p.handoff ≤ 512*(graph.countedSize+1) ∧ p.restore+12+2*state.heap.size < 2 ^ width := by
    have queryBound := ResolvedResident.query_code_bound (width := width) (entry := p.solver) (keep := keep)
      graph ∅ b target reference
    dsimp only [p, positions] at emitterBound queryBound ⊢
    dsimp only [keep, count] at queryBound
    constructor <;> omega
  unfold code at present
  have parkAt := block_left program entry _ _ present
  have afterPark := block_right program entry _ _ present
  simp only [ResolvedSourcePark.code_length] at afterPark
  have emitAt := block_left program p.emit _ _ afterPark
  have afterEmit := block_right program p.emit _ _ afterPark
  have copyAt := block_left program p.copyWords _ _ afterEmit
  have afterCopy := block_right program p.copyWords _ _ afterEmit
  simp only [Array.length_toList, SharedWitnessCopy.code_size] at afterCopy
  have nodesAt := block_left program p.pushNodes _ _ afterCopy
  have afterNodes := block_right program p.pushNodes _ _ afterCopy
  simp only [ResolvedSourceRead.pushCode_length] at afterNodes
  have channelsAt := block_left program p.pushChannels _ _ afterNodes
  have afterChannels := block_right program p.pushChannels _ _ afterNodes
  simp only [ResolvedSourceRead.pushCode_length] at afterChannels
  have handoffAt := block_left program p.handoff _ _ afterChannels
  have afterHandoff := block_right program p.handoff _ _ afterChannels
  simp only [ResolvedPacketHandoff.code_length, ← Nat.add_assoc] at afterHandoff
  have solverAt := block_left program p.solver _ _ afterHandoff
  have returnAt := block_right program p.solver _ _ afterHandoff
  obtain ⟨parked, pp, park, pspace, ph, ps, po, pc, pr, _⟩ :=
    ResolvedSourcePark.execution program state entry positive (by omega) position running (by omega) parkAt
  obtain ⟨emitted, et, emit, etime, eh, es, eo, ep, er⟩ :=
    ResolvedSourcePlan.execution program parked packet graph rows roots matched right b target root rootSlot p.emit
      (ph.trans heapStored) (by simpa only [ph] using rootStored) (by omega) pc pr
      (by dsimp only [p, positions, emitCode] at emitterBound ⊢; omega) (by rw [ph, valueLength]; omega) emitAt
  change emitted.heap = parked.heap ++ values.toArray at eh
  have emittedPC : emitted.pc = word width p.copyWords := ep
  have sourceWords : emitted.heap.size = state.heap.size+count := by
    simp only [eh, ph, List.size_toArray, Array.size_append, sameCount]
  obtain ⟨copied, cp, copy, cspace, ch, cs, co, cpc, cr, _⟩ :=
    SharedWitnessCopy.execution program emitted state.heap.size values p.copyWords p.pushNodes
      emittedPC er (by dsimp only [p, positions] at emitterBound ⊢; omega)
      positive (by omega) (by intro i valid; rw [eh, ph, Array.getElem?_append_right (by omega)]
                              simp only [Nat.add_sub_cancel_left, List.getElem?_toArray, List.getElem?_eq_getElem valid])
      (by simpa only [sameCount] using block_code _ _ _ copyAt)
  obtain ⟨nodesPushed, nt, nh, ns, no, np, nr, _⟩ :=
    ResolvedSourceRead.push_execution program copied p.pushNodes 1 (word width graph.nodeCount)
      (by rw [ch, eh, ph, Array.getElem?_append_left (Array.getElem?_eq_some_iff.mp nodeStored).1]; exact nodeStored)
      cpc cr (by dsimp only [p, positions] at emitterBound ⊢; omega) (by rw [ch, sourceWords]; omega) nodesAt
  obtain ⟨channelsPushed, ct, cph, cps, cpo, cpp, cpr, _⟩ :=
    ResolvedSourceRead.push_execution program nodesPushed p.pushChannels 0 (word width n)
      (by rw [nh, ch, eh, ph, Array.getElem?_append_left (Array.getElem?_eq_some_iff.mp channelStored).1]; exact channelStored)
      (by simpa only [p, positions] using np) nr (by dsimp only [p, positions] at emitterBound ⊢; omega)
      (by rw [nh, ch, sourceWords]; omega) channelsAt
  have queryInput : channelsPushed.stack = ResolvedPacketHandoff.packetWords width n graph.nodeCount
      (ResolvedResident.rows graph right b target root) ++ (state.heap.toList ++ state.stack) := by
    rw [cps, ns, cs, es, ps]
    simp only [ResolvedPacketHandoff.packetWords, ResolvedResident.packet, Array.toList_append,
      List.toList_toArray, values, ResolvedSourcePlan.words, List.map_map, List.cons_append, List.append_assoc]
    rfl
  have queryHeapSize : channelsPushed.heap.size = state.heap.size+count := by rw [cph, nh, ch, sourceWords]
  have queryStart : ResolvedPacketHandoff.queryEntry graph right b target root p.handoff = p.solver := by
    unfold ResolvedPacketHandoff.queryEntry
    rw [clauseLength]
    rfl
  have querySourceSize : (ResolvedResident.sourceHeap width n graph.nodeCount
      (ResolvedResident.rows graph right b target root)).size = keep := by
    rw [ResolvedResident.sourceHeap_size, clauseLength]
  obtain ⟨answer, queried, qt, qp, query, qtime, qspace, decision, qo, meaning, ready⟩ :=
    ResolvedPacketHandoff.query_execution program channelsPushed graph right b target reference root p.handoff
      (state.heap.toList ++ state.stack) queryInput (by simpa only [p, positions] using cpp) cpr positionsBound.1
      (by rw [queryHeapSize]; omega) capacity
      (by simpa only [queryHeapSize, clauseLength] using handoffAt)
      (by simpa only [queryStart, querySourceSize] using solverAt)
  have queryKeep : queried.heap.size = keep := by
    exact ready.heapSize.trans querySourceSize
  have restorePosition : p.solver+
      (ResolvedResident.queryCode graph ∅ b target reference width p.solver keep).length = p.restore := rfl
  obtain ⟨final, finish, fh, fs, fo, fp, fr⟩ :=
    ResolvedSourceReturn.execution program queried p.restore found rejected state.heap state.stack answer ready.stack
      (by simpa only [boolWord] using decision)
      (by simpa only [queryStart, querySourceSize, restorePosition] using ready.position)
      ready.running positionsBound.2 (by rw [queryKeep]; dsimp only [keep]; omega) (by omega)
      (by simpa only [queryKeep, p, positions, keep, count, querySize] using returnAt)
  have parkedLive : parked.liveWords = state.liveWords+state.heap.size := by
    simp only [State.liveWords, ph, ps, po, List.length_append, Array.length_toList]; omega
  have emittedLive : emitted.liveWords = parked.liveWords+count := by
    simp only [State.liveWords, eh, es, eo, Array.size_append, List.size_toArray, sameCount]; omega
  have copiedLive : copied.liveWords = emitted.liveWords+count := by
    simp only [State.liveWords, ch, cs, co, List.length_append, sameCount]; omega
  have nodesLive : nodesPushed.liveWords = copied.liveWords+1 := by
    simp only [State.liveWords, nh, ns, no, List.length_cons]; omega
  have channelsLive : channelsPushed.liveWords = nodesPushed.liveWords+1 := by
    simp only [State.liveWords, cph, cps, cpo, List.length_cons]; omega
  have queriedLive : queried.liveWords ≤ channelsPushed.liveWords+202*(graph.countedSize+1) :=
    (Execution.final_storage_le query).trans qspace
  refine ⟨answer, final, _, _, park.append (emit.append (copy.append (nt.append (ct.append (query.append finish))))),
    ?_, ?_, fh, fs, fo.trans (qo.trans (cpo.trans (no.trans (co.trans (eo.trans po))))), fp, fr, meaning⟩
  · simp only [ph, queryKeep, sameCount]
    dsimp only [keep]
    omega
  · simp only [parkedLive, emittedLive, copiedLive, nodesLive, channelsLive, sameCount]
    omega

end Controller.Extensions.ResolvedSourceCallback
