module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Extensions.ResolvedOutputBody
public import Controller.Extensions.ResolvedNativeSource
public import Controller.Extensions.ResidentSegment

@[expose] public section

/-! The complete healthy-one phase uses one selector-search body and one
native continuation. Exhaustion rejects; success reads the retained selector,
emits the checked raw model, records acceptance and halts. -/
namespace Controller.Extensions.ResolvedNativeSearch
open Controller Controller.Decoder Controller.Decoder.DAG Controller.Cost
open Controller.Native Controller.Native.SourceController Controller.Cost.NativeSourceExecution
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestInputStored
open Controller.Cost.SharedDetectorAssembly Controller.Cost.RawAdapterProgram

def bodyLength (parameters : Parameters) (width : Nat) (rows : List Row) (roots : List Nat)
    (reference : Fin parameters.decoder.nodeCount) : Nat :=
  (ResolvedOutputBody.code width parameters.decoder rows roots (fun _ => false)
    parameters.buses parameters.bridge.target reference 0 0).length

def nativeCode (parameters : Parameters) (width : Nat) (rows : List Row) (roots : List Nat)
    (reference : Fin parameters.decoder.nodeCount) : List (Instruction width 8) :=
  let packet := ResolvedRootSource.packet width parameters.channels rows roots
    (fun _ : Fin parameters.decoder.nodeCount => false) 0
  ResolvedNativeSource.code parameters width packet rows roots reference 4 0
    ((cacheHeap width packet rows roots).size+parameters.decoder.liveAndCount)

def code (parameters : Parameters) (width : Nat) (rows : List Row) (roots : List Nat)
    (reference : Fin parameters.decoder.nodeCount) : List (Instruction width 8) :=
  let start := bodyLength parameters width rows roots reference
  let native := nativeCode parameters width rows roots reference
  ResolvedOutputBody.code width parameters.decoder rows roots (fun _ => false)
    parameters.buses parameters.bridge.target reference start (start+native.length) ++
    (ResidentSegment.code start native ++ [.constant 4 (word width 0),.halt])

theorem code_bound (parameters : Parameters) (rows : List Row) (roots : List Nat)
    (reference : Fin parameters.decoder.nodeCount) (matched : RowsMatch parameters.decoder rows)
    (rootMatches : RootsMatch parameters.decoder roots) :
    (code parameters width rows roots reference).length ≤
      2600*(parameters.decoder.countedSize+1)+34*(selectedSize parameters).total+2 := by
  have body := ResolvedOutputBody.code_bound (width := width) parameters.decoder rows roots matched rootMatches
    (fun _ => false) parameters.buses parameters.bridge.target reference
    (bodyLength parameters width rows roots reference)
    (bodyLength parameters width rows roots reference+(nativeCode parameters width rows roots reference).length)
  have native := ResolvedNativeSource.code_bound (width := width) (rootSlot := 4) (entry := 0)
    (sourceCount := (cacheHeap width (ResolvedRootSource.packet width parameters.channels rows roots
      (fun _ : Fin parameters.decoder.nodeCount => false) 0) rows roots).size+parameters.decoder.liveAndCount)
    parameters (ResolvedRootSource.packet width parameters.channels rows roots
      (fun _ : Fin parameters.decoder.nodeCount => false) 0) rows roots reference
  change (nativeCode parameters width rows roots reference).length ≤ _ at native
  simp only [code,List.length_append,ResidentSegment.code_length,List.length_cons,List.length_nil]
  omega

def answer (parameters : Parameters) : Option (Finset (Channel parameters.channels)) :=
  let healthy := parameters.decoder.evalTable (assignmentOfSet {parameters.bridge.target})
  firstSuccess (fun root => if healthy root then
    SupportStream.scanExpansions parameters.decoder parameters.buses parameters.bridge.target root else none)
    parameters.decoder.roots

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2500000 in
theorem execution (parameters : Parameters) (raw : parameters.layout = .raw) (drive : parameters.drive = true)
    (rows : List Row) (roots : List Nat) (matched : RowsMatch parameters.decoder rows)
    (rootMatches : RootsMatch parameters.decoder roots) (reference : Fin parameters.decoder.nodeCount)
    (k : Nat) (andBound : parameters.decoder.liveAndCount ≤ k)
    (capacity : 16384*(parameters.decoder.countedSize+(selectedSize parameters).total+1)<2^width)
    (state : State width 8)
    (heapStored : state.heap = ResolvedRootSource.source width parameters.channels rows roots
      (parameters.decoder.evalTable (assignmentOfSet {parameters.bridge.target})) 0)
    (position : state.pc = word width 0) (running : state.halted = false) :
    ∃ final ticks peak, Execution (code parameters width rows roots reference).toArray state final ticks peak ∧
      final.halted = true ∧ final.reg 4 = word width (if (answer parameters).isSome then 1 else 0) ∧
      ticks ≤ (7000*(parameters.decoder.countedSize+1)+90)*2^k*parameters.decoder.roots.length+
        6100*(parameters.decoder.countedSize+1)+55*(selectedSize parameters).total ∧
      peak ≤ 620*(parameters.decoder.countedSize+1)+state.stack.length+state.output.length+
        3*(selectedSize parameters).total+12 ∧
      ((answer parameters).isSome = true → Certificate.ModelCheck.check (formula parameters)
        (NativeRealizedChecked.decodeOutput final.output (compile parameters).toState.count) = true) ∧
      (answer parameters = none → final.output = state.output) := by
  let graph := parameters.decoder
  let healthy := graph.evalTable (assignmentOfSet {parameters.bridge.target})
  let start := bodyLength parameters width rows roots reference
  let native := nativeCode parameters width rows roots reference
  let done := start+native.length
  let resident := (code parameters width rows roots reference).toArray
  have size := graph.countedSize_eq
  have ands := graph.liveAndCount_le_nodeCount
  have startBound : start ≤ 1400*(graph.countedSize+1) :=
    ResolvedOutputBody.code_bound graph rows roots matched rootMatches (fun _ => false)
      parameters.buses parameters.bridge.target reference 0 0
  have nativeBound : native.length ≤ 1200*(graph.countedSize+1)+34*(selectedSize parameters).total :=
    ResolvedNativeSource.code_bound parameters _ rows roots reference
  have bodyLengthEq : (ResolvedOutputBody.code width graph rows roots (fun _ => false)
      parameters.buses parameters.bridge.target reference start done).length = start :=
    ResolvedOutputBody.code_length_destinations graph rows roots (fun _ => false)
      parameters.buses parameters.bridge.target reference start done 0 0
  have present : SharedRootRead.BlockAt resident 0 (code parameters width rows roots reference) := by
    intro offset below
    simp only [resident,List.getElem?_toArray,Nat.zero_add]
  have bodyAt := block_left resident 0 _ _ present
  have restAt := block_right resident 0 _ _ present
  change SharedRootRead.BlockAt resident (0+(ResolvedOutputBody.code width graph rows roots (fun _ => false)
    parameters.buses parameters.bridge.target reference start done).length)
    (ResidentSegment.code start native ++ [.constant 4 (word width 0),.halt]) at restAt
  rw [bodyLengthEq,Nat.zero_add] at restAt
  have nativeAt := block_left resident start _ _ restAt
  have rejectAt := block_right resident start _ _ restAt
  simp only [ResidentSegment.code_length] at rejectAt
  have actualBody : SharedRootRead.BlockAt resident 0
      (ResolvedOutputBody.code width graph rows roots healthy parameters.buses parameters.bridge.target reference start done) := by
    rw [ResolvedOutputBody.healthy_independent graph rows roots healthy (fun _ => false)]
    exact bodyAt
  obtain ⟨searched,st,sp,search,stime,sspace,out,result⟩ :=
    ResolvedOutputBody.execution width graph rows roots matched rootMatches healthy parameters.buses k
      parameters.bridge.target reference start done andBound (by dsimp only [graph]; omega)
      resident state heapStored position running actualBody
  change ResolvedRootLoop.SearchOutcome _ _ _ _ start done state.stack searched (answer parameters) at result
  have searchLive : searched.liveWords ≤ sp := search.final_storage_le
  have searchSpace : sp ≤ 320*(parameters.decoder.countedSize+1)+state.stack.length+state.output.length+12 := sspace
  cases found : answer parameters with
  | none =>
    have failed := result
    rw [found] at failed
    obtain ⟨_,_,pc,active⟩ := failed
    obtain ⟨tagged,tag,tp,tv,th,ts,tout,tr,_⟩ :=
      SharedEvaluationReclaim.constant_execution resident done 0 4 searched pc active
        (by dsimp only [done]; dsimp only [graph] at *; omega)
        (by simpa only [done,Nat.add_zero,List.getElem?_cons_zero] using rejectAt 0 (by simp))
    let final := { tagged.advance with halted := true }
    have halt := SharedDetectorSteps.single resident tagged final (done+1) Instruction.halt tp
      (by dsimp only [done]; dsimp only [graph] at *; omega)
      (by simpa only [done,Nat.add_assoc,List.getElem?_cons_succ,List.getElem?_cons_zero] using rejectAt 1 (by simp))
      (by simp [step,tr,final])
    have tagLive : tagged.liveWords = searched.liveWords := by simp only [State.liveWords,th,ts,tout]
    have finalLive : final.liveWords = tagged.liveWords := rfl
    refine ⟨final,st+2,max sp (max searched.liveWords (max tagged.liveWords final.liveWords)),
      ?_,rfl,by simpa only [final,State.advance,found,Option.isSome_none,Bool.false_eq_true,ite_false] using tv,?_,?_,
      by simp [found],by intro _; exact tout.trans out⟩
    · simpa only [Nat.add_assoc,Nat.reduceAdd] using search.append (tag.append halt)
    · dsimp only [graph] at *; omega
    · simp only [finalLive,tagLive,Nat.max_self]; omega
  | some K =>
    have succeeded := result
    rw [found] at succeeded
    obtain ⟨⟨root,member,healthyRoot,chosen,chosenHeap,returned⟩,_,pc,active⟩ := succeeded
    let packet := ResolvedRootSource.packet width parameters.channels rows roots healthy root.val
    let localState := { searched with pc := word width 0 }
    have sourceBound := ResolvedRootSource.source_bound (width := width) graph healthy root.val matched rootMatches
    have actualHeap : localState.heap = withValues (cacheHeap width packet rows roots)
        (ResolvedSourcePlan.selectorValues graph (ResolvedSelector.selection graph chosen)) := by
      rw [ResolvedSelector.selectorValues_selection]
      exact chosenHeap
    have retained : ∀ (address : Nat) (value : Word width), (ResolvedRootSource.source width parameters.channels rows roots healthy root.val)[address]? = some value →
        localState.heap[address]? = some value := by
      intro address value stored
      rw [show localState.heap = SupportSearch.maskHeap _ chosen from chosenHeap]
      unfold SupportSearch.maskHeap withValues
      rw [Array.getElem?_append_left (Array.getElem?_eq_some_iff.mp stored).1]
      exact stored
    have sourceSize : localState.heap.size = (cacheHeap width packet rows roots).size+graph.liveAndCount := by
      simp only [actualHeap,withValues_size]
    have actualCode : ResolvedNativeSource.code parameters width packet rows roots reference 4 0 localState.heap.size = native := by
      rw [sourceSize]
      have uniform := ResolvedNativeSource.code_uniform (width := width) parameters packet
        (ResolvedRootSource.packet width parameters.channels rows roots (fun _ : Fin graph.nodeCount => false) 0)
        rows roots (by simp [packet]) reference 4 0 ((cacheHeap width packet rows roots).size+graph.liveAndCount)
      simpa only [packet,cacheHeap_size,ResolvedRootSource.packet_size,native,nativeCode] using uniform
    have nativePresent : SharedRootRead.BlockAt native.toArray 0
        (ResolvedNativeSource.code parameters width packet rows roots reference 4 0 localState.heap.size) := by
      rw [actualCode]
      intro offset below
      simp only [Nat.zero_add,List.getElem?_toArray]
    obtain ⟨emitted,nt,np,emit,halted,decision,ntime,nspace,checked⟩ :=
      ResolvedNativeSource.execution parameters raw drive native.toArray localState packet rows roots matched
        (ResolvedSelector.selection graph chosen) reference root 4 0 member
        (by rw [← DAG.evalTable_eq_eval]; exact healthyRoot) actualHeap
        (retained _ _ (ResolvedRootSource.root_cell healthy root.val))
        (retained _ _ (ResolvedRootSource.channel_cell healthy root.val))
        (retained _ _ (ResolvedRootSource.node_cell graph healthy root.val matched))
        (by rw [sourceSize]; simp [packet]) rfl active (by omega)
        (by rw [sourceSize]; exact sourceBound)
        (by dsimp only [graph] at *; omega)
        ((ResolvedSelector.query_isSome graph parameters.buses parameters.bridge.target root chosen).mp
          (by rw [returned]; rfl)) nativePresent
    have moved := ResidentSegment.execution resident native start searched emitted nt np pc nativeAt
      (by dsimp only [graph] at *; omega) emit
    refine ⟨relocatedState start emitted,st+nt,max sp np,search.append moved,halted,?_,?_,?_,
      by intro _; exact checked,by simp [found]⟩
    · simpa only [relocatedState,found,Option.isSome_some,ite_true] using decision
    · dsimp only [graph] at *; omega
    · have sameLive : localState.liveWords = searched.liveWords := rfl
      rw [sameLive] at nspace
      dsimp only [graph] at *; omega

end Controller.Extensions.ResolvedNativeSearch
