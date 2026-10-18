module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Extensions.ResolvedOutputs

@[expose] public section

/-! The healthy-one search body has external success and exhaustion labels.
It allocates its selector mask and shares one callback across all root occurrences.
The resident program supplies the terminal continuations. -/
namespace Controller.Extensions.ResolvedOutputBody
open Controller Controller.Decoder Controller.Decoder.DAG Controller.Cost
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestInputStored
open Controller.Cost.SharedDetectorAssembly

structure Positions where
  loop : Nat
  seek : Nat
  call : Nat
  found : Nat
  done : Nat

def positions (graph : DAG n) (found done : Nat) : Positions :=
  let loop := 2*graph.liveAndCount+1
  let seek := loop+28
  let call := loop+65
  ⟨loop,seek,call,found,done⟩

def code (width : Nat) (graph : DAG n) (rows : List Row) (roots : List Nat)
    (healthy : Fin graph.nodeCount → Bool) (b : Nat) (target : Channel n) (reference : Fin graph.nodeCount) (found done : Nat) :
    List (Instruction width 8) :=
  let p := positions graph found done
  let packet := ResolvedRootSource.packet width n rows roots healthy 0
  let source := cacheHeap width packet rows roots
  SharedCoordinateTable.code width (List.replicate graph.liveAndCount (word width 0)) ++
    ([.constant 3 (word width 0)] ++
    (ResolvedRootLoop.driverCode width p.loop graph.roots.length (UniformDAGRuntimeOutputs.rootBase packet rows)
      4 5 p.seek p.done graph.liveAndCount ++
    (ResolvedRootLoop.advanceCode width p.loop ++
    (SupportTraversal.endingCode width p.seek graph.liveAndCount source.size p.call (.constant 0 (word width 0)) ++
    ([.branchZero 0 (word width (p.loop+23))] ++
    (ResolvedSourceCallback.code width graph packet rows roots b target reference 4 p.call
      (source.size+graph.liveAndCount) p.found (SupportTraversal.backtrack p.seek)))))))

theorem healthy_independent (graph : DAG n) (rows : List Row) (roots : List Nat)
    (left right : Fin graph.nodeCount → Bool) (b : Nat) (target : Channel n) (reference : Fin graph.nodeCount) (found done : Nat) :
    code width graph rows roots left b target reference found done = code width graph rows roots right b target reference found done := by
  have plan := ResolvedRootSource.plan_uniform graph (ResolvedRootSource.packet width n rows roots left 0)
    (ResolvedRootSource.packet width n rows roots right 0) rows roots (by simp) b target 4
  simp only [code,positions,cacheHeap_size,ResolvedRootSource.packet_size,
    UniformDAGRuntimeOutputs.rootBase,ResolvedSourceCallback.code,ResolvedSourceCallback.positions,
    ResolvedSourceCallback.emitCode,plan,cacheHeap_size,ResolvedRootSource.packet_size]

theorem code_length_destinations (graph : DAG n) (rows : List Row) (roots : List Nat)
    (healthy : Fin graph.nodeCount → Bool) (b : Nat) (target : Channel n)
    (reference : Fin graph.nodeCount) (found done otherFound otherDone : Nat) :
    (code width graph rows roots healthy b target reference found done).length =
      (code width graph rows roots healthy b target reference otherFound otherDone).length := by
  simp only [code,List.length_append,SharedCoordinateTable.code_length,List.length_replicate,
    List.length_cons,List.length_nil,ResolvedRootLoop.driverCode_length,ResolvedRootLoop.advanceCode_length,
    SupportTraversal.endingCode_length]
  have equal := ResolvedSourceCallback.code_length_destinations (width := width) graph
    (ResolvedRootSource.packet width n rows roots healthy 0) rows roots b target reference 4
    (2*graph.liveAndCount+1+65)
    ((cacheHeap width (ResolvedRootSource.packet width n rows roots healthy 0) rows roots).size+graph.liveAndCount)
    found (SupportTraversal.backtrack (2*graph.liveAndCount+1+28))
    otherFound (SupportTraversal.backtrack (2*graph.liveAndCount+1+28))
  dsimp only [positions] at *
  omega

theorem code_bound (graph : DAG n) (rows : List Row) (roots : List Nat) (matched : RowsMatch graph rows)
    (rootMatches : RootsMatch graph roots) (healthy : Fin graph.nodeCount → Bool) (b : Nat)
    (target : Channel n) (reference : Fin graph.nodeCount) (found done : Nat) :
    (code width graph rows roots healthy b target reference found done).length ≤ 1400*(graph.countedSize+1) := by
  have bound := ResolvedSourceCallback.code_length_bound (width := width) (rootSlot := 4)
    (entry := (positions graph found done).call)
    (found := (positions graph found done).found)
    (rejected := SupportTraversal.backtrack (positions graph found done).seek)
    graph (ResolvedRootSource.packet width n rows roots healthy 0) rows roots b target reference
    (ResolvedRootSource.source_bound (width := width) graph healthy 0 matched rootMatches)
  have size := graph.countedSize_eq
  have ands := graph.liveAndCount_le_nodeCount
  simp only [ResolvedRootSource.source] at bound
  simp only [code,List.length_append,SharedCoordinateTable.code_length,List.length_replicate,
    List.length_cons,List.length_nil,ResolvedRootLoop.driverCode_length,ResolvedRootLoop.advanceCode_length,
    SupportTraversal.endingCode_length] at *
  omega

set_option maxRecDepth 3000 in
set_option maxHeartbeats 2000000 in
theorem execution (width : Nat) (graph : DAG n) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (rootMatches : RootsMatch graph roots)
    (healthy : Fin graph.nodeCount → Bool) (b k : Nat) (target : Channel n) (reference : Fin graph.nodeCount) (found done : Nat)
    (andBound : graph.liveAndCount ≤ k) (capacity : 4096*(graph.countedSize+1) < 2^width)
    (resident : Program width 8) (state : State width 8)
    (heapStored : state.heap = ResolvedRootSource.source width n rows roots healthy 0)
    (position : state.pc = word width 0) (running : state.halted = false)
    (present : SharedRootRead.BlockAt resident 0 (code width graph rows roots healthy b target reference found done)) :
    let p := positions graph found done
    ∃ final ticks peak, Execution resident state final ticks peak ∧
      ticks ≤ (7000*(graph.countedSize+1)+90)*2^k*graph.roots.length+2*graph.liveAndCount+4 ∧
      peak ≤ 320*(graph.countedSize+1)+state.stack.length+state.output.length+12 ∧
      final.output = state.output ∧
      ResolvedRootLoop.SearchOutcome (ResolvedRootSource.source width n rows roots healthy)
        (ResolvedSelector.query graph b target) healthy graph.roots p.found p.done state.stack final
        (firstSuccess (fun root => if healthy root then SupportStream.scanExpansions graph b target root else none) graph.roots) := by
  let p := positions graph found done
  let packet := ResolvedRootSource.packet width n rows roots healthy 0
  let source := cacheHeap width packet rows roots
  have size := graph.countedSize_eq
  have ands := graph.liveAndCount_le_nodeCount
  have sourceBound := ResolvedRootSource.source_bound (width := width) graph healthy 0 matched rootMatches
  have callBound : p.call ≤ 128*(graph.countedSize+1) := by dsimp only [p,positions]; omega
  have loopRoom : p.loop+28<2^width := by dsimp only [p,positions]; omega
  have searchRoom : p.seek+37<2^width := by dsimp only [p,positions]; omega
  unfold code at present
  have allocateAt := block_left resident 0 _ _ present
  have afterAllocate := block_right resident 0 _ _ present
  simp only [SharedCoordinateTable.code_length,List.length_replicate,Nat.zero_add] at afterAllocate
  have constantAt := block_left resident (2*graph.liveAndCount) _ _ afterAllocate
  have afterConstant := block_right resident (2*graph.liveAndCount) _ _ afterAllocate
  simp only [List.length_singleton] at afterConstant
  have driverAt := block_left resident p.loop _ _ afterConstant
  have afterDriver := block_right resident p.loop _ _ afterConstant
  simp only [ResolvedRootLoop.driverCode_length] at afterDriver
  have advanceAt := block_left resident (p.loop+23) _ _ afterDriver
  have afterAdvance := block_right resident (p.loop+23) _ _ afterDriver
  simp only [ResolvedRootLoop.advanceCode_length,Nat.add_assoc,Nat.reduceAdd] at afterAdvance
  have coreAt := block_left resident p.seek _ _ afterAdvance
  have afterCore := block_right resident p.seek _ _ afterAdvance
  simp only [SupportTraversal.endingCode_length] at afterCore
  have branchAt := block_left resident (p.seek+36) _ _ afterCore
  have afterBranch := block_right resident (p.seek+36) _ _ afterCore
  simp only [List.length_singleton,Nat.add_assoc,Nat.reduceAdd] at afterBranch
  have callbackAt := afterBranch
  have returnAt : SharedRootRead.BlockAt resident (SupportTraversal.done p.seek)
      (EnumerationDriverCode.jump width (p.loop+23)) := by
    have last := (SupportTraversal.ending_blocks resident p.seek graph.liveAndCount source.size p.call
      (.constant 0 (word width 0)) coreAt).2.2.2.2
    intro offset below
    have bound : offset<2 := by simpa [EnumerationDriverCode.jump] using below
    interval_cases offset
    · simpa [EnumerationDriverCode.jump] using last
    · simpa [EnumerationDriverCode.jump,SupportTraversal.done,Nat.add_assoc] using branchAt 0 (by simp)
  obtain ⟨allocated,allocation,ah,ast,ao,ap,ar,_⟩ :=
    SharedCoordinateTable.execution resident state (List.replicate graph.liveAndCount (word width 0)) 0
      position running (by simp; omega) (by simp only [heapStored,List.length_replicate]; omega) allocateAt
  have mask : allocated.heap = SupportSearch.maskHeap (ResolvedRootSource.source width n rows roots healthy 0)
      (∅ : Finset (Fin graph.liveAndCount)) := by
    rw [ah,heapStored]
    simp [SupportSearch.maskHeap,withValues,boolWord,List.ofFn_const]
  obtain ⟨ready,initialization,rp,rc,rh,rs,ro,rr,_⟩ :=
    SharedEvaluationReclaim.constant_execution resident (2*graph.liveAndCount) 0 3 allocated
      (by simpa using ap) ar (by omega) (by simpa using constantAt 0 (by simp))
  obtain ⟨final,ticks,peak,trace,time,space,out,result⟩ :=
    ResolvedOutputs.execution resident graph rows roots matched rootMatches healthy b k target reference
      p.loop p.seek p.call p.found p.done andBound callBound capacity loopRoom searchRoom driverAt advanceAt coreAt
      returnAt callbackAt 0 ready (rh.trans mask) rc (by simpa only [p,positions] using rp) rr
  have readyStack : ready.stack = state.stack := rs.trans ast
  have readyOutput : ready.output = state.output := ro.trans ao
  have words := code_bound (width := width) graph rows roots matched rootMatches healthy b target reference found done
  have initialLive : state.liveWords ≤ 50*(graph.countedSize+1)+state.stack.length+state.output.length := by
    simp only [State.liveWords,heapStored]
    omega
  have allocatedLive : allocated.liveWords = state.liveWords+graph.liveAndCount := by
    simp only [State.liveWords,ah,ast,ao,Array.size_append,List.size_toArray,List.length_replicate]; omega
  refine ⟨final,2*graph.liveAndCount+(1+ticks),max (state.liveWords+graph.liveAndCount)
    (max allocated.liveWords peak),?_,by omega,?_,out.trans readyOutput,?_⟩
  · simpa only [List.length_replicate,Nat.zero_add] using allocation.append (initialization.append trace)
  · rw [readyStack,readyOutput] at space
    omega
  · simpa only [readyStack] using result

end Controller.Extensions.ResolvedOutputBody
