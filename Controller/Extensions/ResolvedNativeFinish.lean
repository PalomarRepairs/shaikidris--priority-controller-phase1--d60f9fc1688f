module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Extensions.ResolvedNativeSearch

@[expose] public section

/-! The transition from the healthy source to the complete healthy-one phase
resets the reusable root slot by fetched instructions and enters the relocated
search. Both acceptance and exhaustion halt in the resident program. -/
namespace Controller.Extensions.ResolvedNativeFinish
open Controller Controller.Decoder Controller.Decoder.DAG Controller.Cost
open Controller.Native Controller.Native.SourceController Controller.Cost.NativeSourceExecution
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestInputStored
open Controller.Cost.SharedDetectorAssembly Controller.Cost.RawAdapterProgram

def setupCode (width : Nat) : List (Instruction width 8) :=
  [.constant 1 (word width 0)] ++ ResolvedRootRead.storeCode width 4

@[simp] theorem setupCode_length : (setupCode width).length = 3 := rfl

def code (parameters : Parameters) (width entry : Nat) (rows : List Row) (roots : List Nat)
    (reference : Fin parameters.decoder.nodeCount) : List (Instruction width 8) :=
  setupCode width ++ ResidentSegment.code (entry+3) (ResolvedNativeSearch.code parameters width rows roots reference)

theorem code_bound (parameters : Parameters) (rows : List Row) (roots : List Nat)
    (reference : Fin parameters.decoder.nodeCount) (matched : RowsMatch parameters.decoder rows)
    (rootMatches : RootsMatch parameters.decoder roots) :
    (code parameters width entry rows roots reference).length ≤
      2600*(parameters.decoder.countedSize+1)+34*(selectedSize parameters).total+5 := by
  have bound := ResolvedNativeSearch.code_bound (width := width) parameters rows roots reference matched rootMatches
  simp only [code,List.length_append,setupCode_length,ResidentSegment.code_length]
  omega

set_option maxHeartbeats 2000000 in
theorem execution (parameters : Parameters) (raw : parameters.layout = .raw) (drive : parameters.drive = true)
    (resident : Program width 8) (rows : List Row) (roots : List Nat) (matched : RowsMatch parameters.decoder rows)
    (rootMatches : RootsMatch parameters.decoder roots) (reference : Fin parameters.decoder.nodeCount)
    (k : Nat) (andBound : parameters.decoder.liveAndCount ≤ k) (entry : Nat)
    (capacity : 16384*(parameters.decoder.countedSize+(selectedSize parameters).total+1)<2^width)
    (room : entry+(code parameters width entry rows roots reference).length<2^width)
    (state : State width 8)
    (heapStored : state.heap = cacheHeap width (SupportCandidate.header width parameters.channels rows roots
      (parameters.decoder.evalTable (assignmentOfSet {parameters.bridge.target}))) rows roots)
    (position : state.pc = word width entry) (running : state.halted = false)
    (present : SharedRootRead.BlockAt resident entry (code parameters width entry rows roots reference)) :
    ∃ final ticks peak, Execution resident state final ticks peak ∧ final.halted = true ∧
      final.reg 4 = word width (if (ResolvedNativeSearch.answer parameters).isSome then 1 else 0) ∧
      ticks ≤ (7000*(parameters.decoder.countedSize+1)+90)*2^k*parameters.decoder.roots.length+
        6200*(parameters.decoder.countedSize+1)+55*(selectedSize parameters).total ∧
      peak ≤ 620*(parameters.decoder.countedSize+1)+state.stack.length+state.output.length+
        3*(selectedSize parameters).total+12 ∧
      ((ResolvedNativeSearch.answer parameters).isSome = true → Certificate.ModelCheck.check (formula parameters)
        (NativeRealizedChecked.decodeOutput final.output (compile parameters).toState.count) = true) ∧
      (ResolvedNativeSearch.answer parameters = none → final.output = state.output) := by
  let healthy := parameters.decoder.evalTable (assignmentOfSet {parameters.bridge.target})
  let source := cacheHeap width (SupportCandidate.header width parameters.channels rows roots healthy) rows roots
  have retained := ResolvedRootSource.source_bound (width := width) parameters.decoder healthy 0 matched rootMatches
  have sourceBound : source.size ≤ 40*(parameters.decoder.countedSize+1) := by
    simpa only [source,ResolvedRootSource.source,cacheHeap_size,ResolvedRootSource.packet_size,
      SupportCandidate.header_size] using le_trans (Nat.le_add_right _ _) retained
  have firstAt := block_left resident entry _ _ present
  have nativeAt := block_right resident entry _ _ present
  simp only [setupCode_length] at nativeAt
  have constantAt := block_left resident entry _ _ firstAt
  have storeAt := block_right resident entry _ _ firstAt
  simp only [List.length_singleton] at storeAt
  obtain ⟨tagged,tag,tp,tv,th,ts,tout,tr,_⟩ :=
    SharedEvaluationReclaim.constant_execution resident entry 0 1 state position running
      (by simp only [code,List.length_append,setupCode_length,ResidentSegment.code_length] at room; omega)
      (by simpa only [Nat.add_zero,List.getElem?_cons_zero] using constantAt 0 (by simp))
  obtain ⟨ready,prepare,rh,rs,ro,rp,rr,_⟩ :=
    ResolvedRootRead.store_execution resident tagged (entry+1) 4 (word width 0) tv
      (by rw [th,heapStored]; simp; omega) tp tr
      (by simp only [code,List.length_append,setupCode_length,ResidentSegment.code_length] at room; omega)
      (by rw [th,heapStored]; change source.size<2^width; omega) storeAt
  have actualHeap : ready.heap = ResolvedRootSource.source width parameters.channels rows roots healthy 0 := by
    simp only [rh,th,heapStored]
    exact ResolvedRootSource.cache_set _ _ _ 4 (by simp; omega) _
  have readyStack : ready.stack = state.stack := rs.trans ts
  have readyOutput : ready.output = state.output := ro.trans tout
  have taggedLive : tagged.liveWords = state.liveWords := by simp only [State.liveWords,th,ts,tout]
  have stateLive : state.liveWords ≤ 40*(parameters.decoder.countedSize+1)+state.stack.length+state.output.length+9 := by
    simp only [State.liveWords,heapStored]
    change 8+source.size+state.stack.length+state.output.length+1 ≤ _
    omega
  obtain ⟨emitted,nt,np,emit,halted,decision,ntime,nspace,checked,unchanged⟩ :=
    ResolvedNativeSearch.execution parameters raw drive rows roots matched rootMatches reference k andBound capacity
      { ready with pc := word width 0 } actualHeap rfl rr
  have moved := ResidentSegment.execution resident (ResolvedNativeSearch.code parameters width rows roots reference)
    (entry+3) ready emitted nt np (by simpa only [Nat.add_assoc,Nat.reduceAdd] using rp) nativeAt
    (by simpa only [code,List.length_append,setupCode_length,ResidentSegment.code_length,Nat.add_assoc] using room) emit
  refine ⟨relocatedState (entry+3) emitted,3+nt,max state.liveWords (max tagged.liveWords np),
    by simpa only [← Nat.add_assoc,Nat.reduceAdd] using tag.append (prepare.append moved),halted,decision,
    by omega,?_,checked,?_⟩
  · change np ≤ _ at nspace
    rw [readyStack,readyOutput] at nspace
    rw [taggedLive]
    omega
  · intro none
    exact (unchanged none).trans readyOutput

end Controller.Extensions.ResolvedNativeFinish
