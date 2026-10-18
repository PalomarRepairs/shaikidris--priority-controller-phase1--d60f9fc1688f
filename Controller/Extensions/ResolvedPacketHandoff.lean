module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Extensions.ResolvedResident
public import Controller.Cost.SharedWitnessPark
public import Controller.Cost.SharedCoordinateTable
public import Controller.Cost.SharedDetectorAssembly

@[expose] public section

/-! A generated occurrence packet is transferred from the caller stack into
the zero solver's exact entry layout. Temporary source storage is reclaimed,
the dictionary is initialized, and the low-register ABI is fetched. -/
namespace Controller.Extensions.ResolvedPacketHandoff
open Controller.Cost Controller.Cost.RawTransferLoops Controller.Cost.SharedDetectorAssembly
open Controller.Decoder Controller.Decoder.DAG Controller.CNF
open Controller.Cost.ForestZeroAdmissibleCaller

def packetWords (width channels nodes : Nat) (clauses : List (Clause (Fin ambient))) : List (Word width) :=
  (ResolvedResident.packet width channels nodes clauses).toList

@[simp] theorem packetWords_length (clauses : List (Clause (Fin ambient))) :
    (packetWords width channels nodes clauses).length = 2 + clauses.flatten.length := by simp [packetWords]

def abi (width sourceEnd ambient : Nat) : List (Instruction width 8) :=
  [.constant 0 (word width 0), .constant 1 (word width sourceEnd), .constant 2 (word width (sourceEnd+ambient))]

@[simp] theorem abi_length : (abi width sourceEnd ambient).length = 3 := rfl

def code (width entry oldCount sourceEnd ambient : Nat) : List (Instruction width 8) :=
  (SharedEvaluationReclaim.code width entry (entry+7) oldCount).toList ++
    (SharedWitnessPark.code width sourceEnd ++
    (SharedCoordinateTable.code width (List.replicate (2*ambient) (word width 0)) ++ abi width sourceEnd ambient))

@[simp] theorem code_length : (code width entry oldCount sourceEnd ambient).length = 10+2*sourceEnd+4*ambient := by
  simp [code]; omega

set_option maxHeartbeats 1000000 in
theorem execution (program : Program width 8) (state : State width 8)
    (graph : DAG n) (right : Finset (Fin graph.nodeCount)) (b : Nat) (target : Fin n)
    (root : Fin graph.nodeCount) (entry : Nat) (rest : List (Word width))
    (input : state.stack = packetWords width n graph.nodeCount (ResolvedResident.rows graph right b target root) ++ rest)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry+10+2*(2+(ResolvedResident.rows graph right b target root).flatten.length)+
      4*(n+graph.nodeCount) < 2 ^ width)
    (oldFits : state.heap.size < 2 ^ width)
    (newFits : 2+(ResolvedResident.rows graph right b target root).flatten.length+2*(n+graph.nodeCount) < 2 ^ width)
    (present : SharedRootRead.BlockAt program entry (code width entry state.heap.size
      (2+(ResolvedResident.rows graph right b target root).flatten.length) (n+graph.nodeCount))) :
    ∃ final ticks peak, Execution program state final ticks peak ∧
      ticks = 4*state.heap.size+2*(2+(ResolvedResident.rows graph right b target root).flatten.length)+4*(n+graph.nodeCount)+7 ∧
      peak ≤ state.liveWords + 2*(n+graph.nodeCount) ∧
      final.heap = ResolvedResident.sourceHeap width n graph.nodeCount (ResolvedResident.rows graph right b target root) ∧
      final.output = state.output ∧
      ResolvedResident.Ready graph right b target root
        (entry+10+2*(2+(ResolvedResident.rows graph right b target root).flatten.length)+4*(n+graph.nodeCount)) rest final := by
  let clauses := ResolvedResident.rows graph right b target root
  let words := packetWords width n graph.nodeCount clauses
  let sourceEnd := 2+clauses.flatten.length
  let ambient := n+graph.nodeCount
  have countEq : clauses.flatten.length = (ResolvedResident.rows graph right b target root).flatten.length := rfl
  have wordsLength : words.length = sourceEnd := by simp only [words, packetWords_length, sourceEnd]
  have codeRoom : entry+10+2*sourceEnd+4*ambient < 2 ^ width := room
  have heapRoom : sourceEnd+2*ambient < 2 ^ width := newFits
  change state.stack = words ++ rest at input
  unfold code at present
  have releaseAt := block_left program entry _ _ present
  have afterRelease := block_right program entry _ _ present
  simp only [Array.length_toList, SharedEvaluationReclaim.code_size] at afterRelease
  have loadAt := block_left program (entry+7) _ _ afterRelease
  have afterLoad := block_right program (entry+7) _ _ afterRelease
  simp only [SharedWitnessPark.code_length] at afterLoad
  have zerosAt := block_left program (entry+7+2*sourceEnd) _ _ afterLoad
  have abiAt := block_right program (entry+7+2*sourceEnd) _ _ afterLoad
  simp only [SharedCoordinateTable.code_length, List.length_replicate] at abiAt
  obtain ⟨empty, release, eh, es, eo, ep, er, _, _, _, _⟩ :=
    SharedGraphReclaim.setup_execution program state entry (entry+7) #[] state.heap.toList position running
      (by omega) (by simp) (by simpa using oldFits) (by simpa using block_code _ _ _ releaseAt)
  obtain ⟨loaded, load, lh, ls, lo, lp, lr, _⟩ :=
    SharedWitnessPark.execution program empty words rest (entry+7) ep er (by rw [wordsLength]; omega)
      (by simp only [eh, Array.size_empty, Nat.zero_add, wordsLength]; omega) (es.trans input)
      (by simpa only [wordsLength] using loadAt)
  obtain ⟨zeroed, zeros, zh, zs, zo, zp, zr, _⟩ :=
    SharedCoordinateTable.execution program loaded (List.replicate (2*ambient) (word width 0))
      (entry+7+2*sourceEnd) (by simpa only [wordsLength] using lp) lr
      (by simp only [List.length_replicate]; omega)
      (by simp only [lh, eh, Array.empty_append, List.size_toArray, wordsLength, List.length_replicate]; omega) zerosAt
  let start := entry+7+2*sourceEnd+4*ambient
  have zeroPos : zeroed.pc = word width start := by
    simpa only [start, List.length_replicate, ← Nat.mul_assoc, Nat.reduceMul] using zp
  have abiPhysical : SharedRootRead.BlockAt program start (abi width sourceEnd ambient) := by
    simpa only [start, ← Nat.mul_assoc, Nat.reduceMul] using abiAt
  obtain ⟨s1, t1, p1, v1, h1, st1, o1, r1, f1⟩ :=
    SharedEvaluationReclaim.constant_execution program start 0 0 zeroed zeroPos zr
      (by dsimp [start, ambient, sourceEnd, clauses]; omega)
      (by simpa [abi] using abiPhysical 0 (by simp))
  obtain ⟨s2, t2, p2, v2, h2, st2, o2, r2, f2⟩ :=
    SharedEvaluationReclaim.constant_execution program (start+1) sourceEnd 1 s1 p1 r1
      (by dsimp [start, ambient, sourceEnd, clauses]; omega)
      (by simpa [abi] using abiPhysical 1 (by simp))
  obtain ⟨final, t3, p3, v3, h3, st3, o3, r3, f3⟩ :=
    SharedEvaluationReclaim.constant_execution program (start+2) (sourceEnd+ambient) 2 s2
      (by simpa only [Nat.add_assoc, Nat.reduceAdd] using p2) r2
      (by dsimp [start, ambient, sourceEnd, clauses]; omega)
      (by simpa [abi] using abiPhysical 2 (by simp))
  have finalHeap : final.heap = ResolvedResident.sourceHeap width n graph.nodeCount clauses := by
    simp only [h3, h2, h1, zh, lh, eh, Array.empty_append]
    rfl
  have finalStack : final.stack = rest := st3.trans (st2.trans (st1.trans (zs.trans ls)))
  have finalOutput : final.output = state.output := o3.trans (o2.trans (o1.trans (zo.trans (lo.trans eo))))
  have finalPC : final.pc = word width (entry+10+2*sourceEnd+4*ambient) := by
    rw [p3]
    congr 1
    dsimp [start]
    omega
  have emptyLive : empty.liveWords ≤ state.liveWords := Execution.final_storage_le release
  have loadedLive : loaded.liveWords = empty.liveWords := by
    simp only [State.liveWords, lh, ls, lo, es, input, eh, List.length_append, Array.size_append,
      List.size_toArray, Array.size_empty]; omega
  have zeroedLive : zeroed.liveWords = loaded.liveWords+2*ambient := by
    simp only [State.liveWords, zh, zs, zo, Array.size_append, List.size_toArray, List.length_replicate]; omega
  have live1 : s1.liveWords = zeroed.liveWords := by simp only [State.liveWords, h1, st1, o1]
  have live2 : s2.liveWords = zeroed.liveWords := by simp only [State.liveWords, h2, st2, o2, h1, st1, o1]
  have joined := release.append (load.append (zeros.append (t1.append (t2.append t3))))
  refine ⟨final, _, _, joined, ?_, ?_, finalHeap, finalOutput, ?_⟩
  · simp only [Array.length_toList, List.length_replicate, wordsLength]
    omega
  · simp only [live1, live2, zeroedLive, loadedLive, List.length_replicate]
    omega
  · refine ⟨congrArg Array.size finalHeap, ?_, ?_, finalStack, finalPC, r3, ?_, ?_, ?_⟩
    · rw [finalHeap]
      exact ForestZeroBackendFrame.refl _ (by simp [ResolvedResident.sourceHeap, ResolvedResident.endSource])
    · intro coordinate
      rw [finalHeap]
      change (ResolvedResident.packet width n graph.nodeCount clauses ++
        Array.replicate (2*(n+graph.nodeCount)) (word width 0))[2+clauses.flatten.length+coordinate.val]? = _
      rw [Array.getElem?_append_right (by rw [ResolvedResident.packet_size]; omega)]
      simp only [ResolvedResident.packet_size, Nat.add_sub_cancel_left, Array.getElem?_replicate]
      exact ite_eq_left (by have := coordinate.isLt; omega)
    · rw [f3 0 (by decide), f2 0 (by decide), v1]
    · rw [f3 1 (by decide), v2]
      rfl
    · simpa only [ResolvedResident.endSource, sourceEnd, clauses, ambient, Nat.add_assoc] using v3

def queryEntry (graph : DAG n) (right : Finset (Fin graph.nodeCount)) (b : Nat)
    (target : Fin n) (root : Fin graph.nodeCount) (entry : Nat) : Nat :=
  entry+10+2*(2+(ResolvedResident.rows graph right b target root).flatten.length)+4*(n+graph.nodeCount)

set_option maxHeartbeats 1000000 in
theorem query_execution (program : Program width 8) (state : State width 8)
    (graph : DAG n) (right : Finset (Fin graph.nodeCount)) (b : Nat) (target : Fin n)
    (reference root : Fin graph.nodeCount) (entry : Nat) (rest : List (Word width))
    (input : state.stack = packetWords width n graph.nodeCount (ResolvedResident.rows graph right b target root) ++ rest)
    (position : state.pc = word width entry) (running : state.halted = false)
    (entryBound : entry ≤ 512*(graph.countedSize+1))
    (oldBound : state.heap.size ≤ 100*(graph.countedSize+1))
    (capacity : 4096*(graph.countedSize+1) < 2 ^ width)
    (handoffAt : SharedRootRead.BlockAt program entry (code width entry state.heap.size
      (2+(ResolvedResident.rows graph right b target root).flatten.length) (n+graph.nodeCount)))
    (solverAt : SharedRootRead.BlockAt program (queryEntry graph right b target root entry)
      (ResolvedResident.queryCode graph ∅ b target reference width (queryEntry graph right b target root entry)
        (ResolvedResident.sourceHeap width n graph.nodeCount (ResolvedResident.rows graph right b target root)).size)) :
    ∃ answer : Bool, ∃ final ticks peak, Execution program state final ticks peak ∧
      ticks ≤ 6000*(graph.countedSize+1) ∧ peak ≤ state.liveWords+202*(graph.countedSize+1) ∧
      final.reg 4 = word width (if answer then 1 else 0) ∧ final.output = state.output ∧
      (answer = true ↔ ∃ K, Admissible b target K ∧ (BoundedAnd.resolved graph right).eval (assignmentOfSet K) root = false) ∧
      ResolvedResident.Ready graph right b target root
        (queryEntry graph right b target root entry+
          (ResolvedResident.queryCode graph ∅ b target reference width (queryEntry graph right b target root entry)
            (ResolvedResident.sourceHeap width n graph.nodeCount (ResolvedResident.rows graph right b target root)).size).length)
        rest final := by
  have counts := ResolvedResident.rows_bound graph right b target root
  have size := graph.countedSize_eq
  have sourceEndBound : 2+(ResolvedResident.rows graph right b target root).flatten.length ≤
      13*(graph.countedSize+1) := by omega
  obtain ⟨prepared, ht, hp, handoff, htime, hspace, heap, output, ready⟩ :=
    execution program state graph right b target root entry rest input position running
      (by omega) (by omega) (by omega) handoffAt
  obtain ⟨answer, final, qt, qp, query, active, decision, time, space, out, _, meaning, finalReady⟩ :=
    ResolvedResident.execution graph right b target reference root program
      (queryEntry graph right b target root entry) rest prepared ready
      (by dsimp [queryEntry]; omega) capacity (by simpa only [heap] using solverAt)
  have preparedLive : prepared.liveWords ≤ state.liveWords + 2*(n+graph.nodeCount) :=
    (Execution.final_storage_le handoff).trans hspace
  refine ⟨answer, final, ht+qt, max hp qp, handoff.append query, by omega, by omega,
    decision, out.trans output, meaning, ?_⟩
  simpa only [heap] using finalReady

end Controller.Extensions.ResolvedPacketHandoff
