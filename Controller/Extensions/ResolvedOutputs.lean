module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Extensions.ResolvedRootLoop
public import Controller.Extensions.ResolvedRootSource

@[expose] public section

/-! The original source and healthy table supply every callback premise of
the returning output loop. All declared root occurrences share one selector
core and one occurrence-producing callback. -/
namespace Controller.Extensions.ResolvedOutputs
open Controller Controller.Decoder Controller.Decoder.DAG Controller.Cost
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestInputStored
open Controller.Cost.UniformDAGRuntimeOutputs

theorem scan_eq (graph : DAG n) (b : Nat) (target : Channel n) (healthy : Fin graph.nodeCount → Bool)
    (observations : List (Fin graph.nodeCount)) :
    ResolvedRootLoop.scan (ResolvedSelector.query graph b target) healthy observations =
      firstSuccess (fun root => if healthy root then SupportStream.scanExpansions graph b target root else none) observations := by
  induction observations with
  | nil => rfl
  | cons root rest ih =>
    simp only [ResolvedRootLoop.scan,ResolvedSelector.search_eq,firstSuccess]
    split <;> simp_all

set_option maxRecDepth 2000 in
set_option maxHeartbeats 1800000 in
theorem execution (resident : Program width 8) (graph : DAG n) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (rootMatches : RootsMatch graph roots)
    (healthy : Fin graph.nodeCount → Bool) (b k : Nat) (target : Channel n)
    (reference : Fin graph.nodeCount) (loop seek call found done : Nat)
    (andBound : graph.liveAndCount ≤ k) (callBound : call ≤ 128*(graph.countedSize+1))
    (capacity : 4096*(graph.countedSize+1) < 2^width)
    (loopRoom : loop+28 < 2^width) (searchRoom : seek+37 < 2^width)
    (driverAt : SharedRootRead.BlockAt resident loop
      (ResolvedRootLoop.driverCode width loop graph.roots.length
        (rootBase (ResolvedRootSource.packet width n rows roots healthy 0) rows) 4 5 seek done graph.liveAndCount))
    (advanceAt : SharedRootRead.BlockAt resident (loop+23) (ResolvedRootLoop.advanceCode width loop))
    (coreAt : SharedRootRead.BlockAt resident seek
      (SupportTraversal.endingCode width seek graph.liveAndCount
        (ResolvedRootSource.source width n rows roots healthy 0).size call (.constant 0 (word width 0))))
    (returnAt : SharedRootRead.BlockAt resident (SupportTraversal.done seek) (EnumerationDriverCode.jump width (loop+23)))
    (callbackAt : SharedRootRead.BlockAt resident call
      (ResolvedSourceCallback.code width graph (ResolvedRootSource.packet width n rows roots healthy 0) rows roots b target
        reference 4 call ((ResolvedRootSource.source width n rows roots healthy 0).size+graph.liveAndCount)
        found (SupportTraversal.backtrack seek)))
    (before : Nat) (state : State width 8)
    (heapStored : state.heap = SupportSearch.maskHeap (ResolvedRootSource.source width n rows roots healthy before)
      (∅ : Finset (Fin graph.liveAndCount)))
    (held : state.reg 3 = word width 0) (position : state.pc = word width loop) (running : state.halted = false) :
    ∃ final ticks peak, Execution resident state final ticks peak ∧
      ticks ≤ (7000*(graph.countedSize+1)+90)*2^k*graph.roots.length+3 ∧
      peak ≤ 320*(graph.countedSize+1)+state.stack.length+state.output.length+12 ∧ final.output = state.output ∧
      ResolvedRootLoop.SearchOutcome (ResolvedRootSource.source width n rows roots healthy)
        (ResolvedSelector.query graph b target) healthy graph.roots found done state.stack final
        (firstSuccess (fun root => if healthy root then SupportStream.scanExpansions graph b target root else none) graph.roots) := by
  let source := ResolvedRootSource.source width n rows roots healthy
  let packet := ResolvedRootSource.packet width n rows roots healthy
  have rootEq : roots = graph.roots.map Fin.val := rootMatches
  have size := graph.countedSize_eq
  have ands := graph.liveAndCount_le_nodeCount
  have sourceBound := ResolvedRootSource.source_bound (width := width) graph healthy 0 matched rootMatches
  have sourceExact : (source 0).size ≤ 7*graph.countedSize+5 := by
    obtain ⟨children,guards⟩ := matched_incidence_lengths graph rows matched
    have rootLength : roots.length = graph.roots.length := by rw [rootMatches]; simp
    simp only [source,ResolvedRootSource.source,cacheHeap_size,ResolvedRootSource.packet_size,
      matched.length_eq,children,guards,rootLength]
    omega
  have uniform : ∀ root, (source root).size = (source 0).size := ResolvedRootSource.source_size_uniform healthy
  have callbacks : ∀ root : Fin graph.nodeCount, SupportSearch.Callback resident (source root.val)
      (ResolvedSelector.query graph b target root) seek call found (7000*(graph.countedSize+1)) (300*(graph.countedSize+1)) := by
    intro root
    have physical : SharedRootRead.BlockAt resident call
        (ResolvedSourceCallback.code width graph (packet root.val) rows roots b target reference 4 call
          ((source root.val).size+graph.liveAndCount) found (SupportTraversal.backtrack seek)) := by
      rw [uniform]
      rw [ResolvedRootSource.callback_uniform graph (packet root.val) (packet 0) rows roots (by simp [packet])]
      exact callbackAt
    exact ResolvedSelector.contract resident (packet root.val) graph rows roots matched b target reference root
      4 seek call found (ResolvedRootSource.root_cell healthy root.val)
      (ResolvedRootSource.channel_cell healthy root.val) (ResolvedRootSource.node_cell graph healthy root.val matched)
      (ResolvedRootSource.source_bound graph healthy root.val matched rootMatches) callBound capacity physical
  obtain ⟨final,ticks,peak,trace,time,space,out,result⟩ :=
    ResolvedRootLoop.execution resident source (ResolvedSelector.query graph b target) healthy
      loop graph.roots.length (rootBase (packet 0) rows) 4 5 seek call found done
      (7000*(graph.countedSize+1)) (300*(graph.countedSize+1)) uniform
      (by simp [source,ResolvedRootSource.source]; omega) (by intro root; omega)
      (ResolvedRootSource.source_mask_update healthy · · graph.liveAndCount)
      (ResolvedRootSource.healthy_cell healthy) callbacks driverAt advanceAt coreAt returnAt loopRoom searchRoom
      (by omega) (by omega) (by omega) graph.roots 0 before state (by simp)
      (by intro before i below
          have cell := ResolvedRootSource.root_occurrence (width := width) (n := n) (rows := rows) (roots := roots)
            healthy before i (by simpa only [rootEq,List.length_map] using below)
          simpa only [source,packet,Nat.add_zero,rootEq,List.getElem_map] using cell)
      heapStored held position running
  have powers : 2^graph.liveAndCount ≤ 2^k := Nat.pow_le_pow_right (by decide) andBound
  rw [scan_eq] at result
  refine ⟨final,ticks,peak,trace,?_,by omega,out,result⟩
  exact time.trans (Nat.add_le_add_right
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ powers)) 3)

end Controller.Extensions.ResolvedOutputs
