module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Extensions.SupportNativeSearch
public import Controller.Extensions.ResolvedNativeFinish
public import Controller.Extensions.SupportHealthyScan

@[expose] public section

/-! One resident detector scans the healthy roots, skips support enumeration
when all are true, otherwise runs the bounded-support phase, and continues
into the shared selector phase after support exhaustion. -/
namespace Controller.Extensions.BoundedNativePrepared
open Controller Controller.Decoder Controller.Decoder.DAG Controller.Cost
open Controller.Native Controller.Native.SourceController Controller.Cost.NativeSourceExecution
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestInputStored
open Controller.Cost.SharedDetectorAssembly Controller.Cost.RawAdapterProgram

def supportEntry (roots : List Nat) : Nat := 6*roots.length+2
def rootEntry (parameters : Parameters) (width : Nat) (rows : List Row) (roots : List Nat) (k : Nat) : Nat :=
  supportEntry roots+(SupportNativeSearch.code parameters width rows roots k).length

def code (parameters : Parameters) (width : Nat) (rows : List Row) (roots : List Nat) (k : Nat)
    (reference : Fin parameters.decoder.nodeCount) : List (Instruction width 8) :=
  let root := rootEntry parameters width rows roots k
  let packet := SupportCandidate.header width parameters.channels rows roots
    (fun _ : Fin parameters.decoder.nodeCount => false)
  SupportHealthyScan.code width (UniformDAGRuntimeOutputs.rootBase packet rows) 5 (supportEntry roots) roots.length ++
    (EnumerationDriverCode.jump width root ++
    (ResidentSegment.code (supportEntry roots) (SupportNativeSearch.code parameters width rows roots k) ++
      ResolvedNativeFinish.code parameters width root rows roots reference))

theorem code_bound (parameters : Parameters) (rows : List Row) (roots : List Nat) (k : Nat)
    (reference : Fin parameters.decoder.nodeCount) (matched : RowsMatch parameters.decoder rows)
    (rootMatches : RootsMatch parameters.decoder roots) :
    (code parameters width rows roots k reference).length ≤
      3000*(parameters.decoder.countedSize+1)+68*(selectedSize parameters).total := by
  have support := SupportNativeSearch.code_bound (width := width) (k := k) parameters rows roots rootMatches
  have native := ResolvedNativeFinish.code_bound (width := width)
    (entry := rootEntry parameters width rows roots k) parameters rows roots reference matched rootMatches
  have size := parameters.decoder.countedSize_eq
  have rootCount : roots.length = parameters.decoder.roots.length := by rw [rootMatches]; simp
  simp only [code,List.length_append,SupportHealthyScan.code_length,ResidentSegment.code_length,
    EnumerationDriverCode.jump,List.length_cons,List.length_nil]
  omega

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2500000 in
theorem execution (parameters : Parameters) (raw : parameters.layout = .raw) (drive : parameters.drive = true)
    (rows : List Row) (roots : List Nat) (matched : RowsMatch parameters.decoder rows)
    (heads : UniformDAGSource.HeadsMatch parameters.decoder rows matched)
    (rootMatches : RootsMatch parameters.decoder roots) (k : Nat) (andBound : parameters.decoder.liveAndCount ≤ k)
    (reference : Fin parameters.decoder.nodeCount)
    (capacity : 65536*(parameters.decoder.countedSize+(selectedSize parameters).total+1)<2^width)
    (state : State width 8)
    (heapStored : state.heap = cacheHeap width (SupportCandidate.header width parameters.channels rows roots
      (parameters.decoder.evalTable (assignmentOfSet {parameters.bridge.target}))) rows roots)
    (position : state.pc = word width 0) (running : state.halted = false) :
    ∃ final ticks peak, Execution (code parameters width rows roots k reference).toArray state final ticks peak ∧
      final.halted = true ∧ final.reg 4 = word width
        (if (SupportStream.detectSet parameters.decoder k parameters.buses parameters.bridge.target parameters.drive).isSome then 1 else 0) ∧
      ticks ≤ (if parameters.decoder.roots.all (parameters.decoder.evalTable (assignmentOfSet {parameters.bridge.target}))
        then 0 else (100*(parameters.decoder.countedSize+1)+50)*BoundedAnd.supportCount parameters.channels k)+
        (7000*(parameters.decoder.countedSize+1)+90)*2^k*parameters.decoder.roots.length+
        6500*(parameters.decoder.countedSize+1)+100*(selectedSize parameters).total ∧
      peak ≤ 700*(parameters.decoder.countedSize+1)+state.stack.length+state.output.length+
        3*(selectedSize parameters).total+12 ∧
      ((SupportStream.detectSet parameters.decoder k parameters.buses parameters.bridge.target parameters.drive).isSome = true →
        Certificate.ModelCheck.check (formula parameters)
          (NativeRealizedChecked.decodeOutput final.output (compile parameters).toState.count) = true) ∧
      (SupportStream.detectSet parameters.decoder k parameters.buses parameters.bridge.target parameters.drive = none →
        final.output = state.output) := by
  let packet := SupportCandidate.header width parameters.channels rows roots (parameters.decoder.evalTable (assignmentOfSet {parameters.bridge.target}))
  let source := cacheHeap width packet rows roots
  let root := rootEntry parameters width rows roots k
  let resident := (code parameters width rows roots k reference).toArray
  have size := parameters.decoder.countedSize_eq
  have rootCount : roots.length = parameters.decoder.roots.length := by rw [rootMatches]; simp only [List.length_map]
  have wholeBound := code_bound (width := width) parameters rows roots k reference matched rootMatches
  have retained := ResolvedRootSource.source_bound (width := width) parameters.decoder (parameters.decoder.evalTable (assignmentOfSet {parameters.bridge.target})) 0 matched rootMatches
  have sourceBound : source.size ≤ 40*(parameters.decoder.countedSize+1) := by
    simpa only [source,packet,ResolvedRootSource.source,cacheHeap_size,ResolvedRootSource.packet_size,
      SupportCandidate.header_size] using le_trans (Nat.le_add_right _ _) retained
  have initialLive : state.liveWords ≤ 40*(parameters.decoder.countedSize+1)+state.stack.length+state.output.length+9 := by
    simp only [State.liveWords,heapStored]
    change 8+source.size+state.stack.length+state.output.length+1 ≤ _
    omega
  have present : SharedRootRead.BlockAt resident 0 (code parameters width rows roots k reference) := by
    intro offset below
    simp only [resident,List.getElem?_toArray,Nat.zero_add]
  have scanAt := block_left resident 0 _ _ present
  have afterScan := block_right resident 0 _ _ present
  simp only [SupportHealthyScan.code_length,Nat.zero_add] at afterScan
  have jumpAt := block_left resident (6*roots.length) _ _ afterScan
  have afterJump := block_right resident (6*roots.length) _ _ afterScan
  simp only [EnumerationDriverCode.jump,List.length_cons,List.length_nil] at afterJump
  have supportAt := block_left resident (supportEntry roots) _ _ afterJump
  have rootAt := block_right resident (supportEntry roots) _ _ afterJump
  simp only [ResidentSegment.code_length] at rootAt
  have rootRoom : root+(ResolvedNativeFinish.code parameters width root rows roots reference).length<2^width := by
    have exactLength : (code parameters width rows roots k reference).length =
        root+(ResolvedNativeFinish.code parameters width root rows roots reference).length := by
      simp only [code,List.length_append,SupportHealthyScan.code_length,EnumerationDriverCode.jump,
        List.length_cons,List.length_nil,ResidentSegment.code_length,root,rootEntry,supportEntry]
      omega
    rw [← exactLength]
    omega
  have finish : ∀ (current : State width 8), current.heap = state.heap → current.stack = state.stack →
      current.output = state.output → current.pc = word width root → current.halted = false →
      ∃ final ticks peak, Execution resident current final ticks peak ∧ final.halted = true ∧
        final.reg 4 = word width (if (ResolvedNativeSearch.answer parameters).isSome then 1 else 0) ∧
        ticks ≤ (7000*(parameters.decoder.countedSize+1)+90)*2^k*parameters.decoder.roots.length+
          6200*(parameters.decoder.countedSize+1)+55*(selectedSize parameters).total ∧
        peak ≤ 620*(parameters.decoder.countedSize+1)+state.stack.length+state.output.length+
          3*(selectedSize parameters).total+12 ∧
        ((ResolvedNativeSearch.answer parameters).isSome = true → Certificate.ModelCheck.check (formula parameters)
          (NativeRealizedChecked.decodeOutput final.output (compile parameters).toState.count) = true) ∧
        (ResolvedNativeSearch.answer parameters = none → final.output = state.output) := by
    intro current heap stack output pc active
    obtain ⟨final,ticks,peak,trace,halted,decision,time,space,checked,unchanged⟩ :=
      ResolvedNativeFinish.execution parameters raw drive resident rows roots matched rootMatches reference k andBound root
        (by omega) rootRoom current (heap.trans heapStored) pc active rootAt
    exact ⟨final,ticks,peak,trace,halted,decision,time,by simpa only [stack,output] using space,checked,
      fun none => (unchanged none).trans output⟩
  have sourceCells : ∀ i (below : i<roots.length), state.heap[UniformDAGRuntimeOutputs.rootBase packet rows+i]? =
      some (word width roots[i]) := by
    intro i below
    rw [heapStored,Array.getElem?_eq_getElem (by change UniformDAGRuntimeOutputs.rootBase packet rows+i < (cacheHeap width packet rows roots).size; simp only [cacheHeap_size,UniformDAGRuntimeOutputs.rootBase]; omega)]
    exact congrArg some (UniformDAGRuntimeOutputs.cache_root_cell packet rows roots i below)
  have healthyCells : ∀ node ∈ roots, state.heap[5+node]? = some (boolWord width (SupportCandidate.lookup (parameters.decoder.evalTable (assignmentOfSet {parameters.bridge.target})) node)) := by
    intro node member
    rw [rootMatches] at member
    obtain ⟨id,_,equal⟩ := List.mem_map.mp member
    subst node
    rw [SupportCandidate.lookup_fin,heapStored]
    unfold cacheHeap Controller.Cost.ForestCursorMaterialize.allocatedHeap
    rw [Array.getElem?_append_left (by simp [packet])]
    exact SupportCandidate.header_value roots (parameters.decoder.evalTable (assignmentOfSet {parameters.bridge.target})) id
  have scanPhysical : SharedRootRead.BlockAt resident 0
      (SupportHealthyScan.code width (UniformDAGRuntimeOutputs.rootBase packet rows) 5 (supportEntry roots) roots.length) := by
    simpa only [packet,UniformDAGRuntimeOutputs.rootBase,SupportCandidate.header_size] using scanAt
  have allRoots : roots.all (SupportCandidate.lookup (parameters.decoder.evalTable (assignmentOfSet {parameters.bridge.target}))) = parameters.decoder.roots.all (parameters.decoder.evalTable (assignmentOfSet {parameters.bridge.target})) := by
    rw [rootMatches,List.all_map]
    simp only [Function.comp_def,SupportCandidate.lookup_fin]
  obtain ⟨scanned,sc,scan,sctime,sh,ss,so,sp,sr⟩ :=
    SupportHealthyScan.execution resident state 0 (UniformDAGRuntimeOutputs.rootBase packet rows) 5 (supportEntry roots)
      roots (SupportCandidate.lookup (parameters.decoder.evalTable (assignmentOfSet {parameters.bridge.target}))) sourceCells healthyCells position running (by omega)
      (by rw [heapStored]; change source.size<2^width; omega) scanPhysical
  rw [allRoots,Nat.zero_add] at sp
  cases allHealthy : parameters.decoder.roots.all (parameters.decoder.evalTable (assignmentOfSet {parameters.bridge.target})) with
  | true =>
    obtain ⟨jumped,jump,jp,jh,js,jo,jr,_⟩ :=
      EnumerationSteps.jump_execution resident scanned (6*roots.length) root
        (by simpa only [allHealthy,ite_true] using sp) sr (by omega)
        (by simpa [EnumerationDriverCode.jump] using jumpAt 0 (by simp [EnumerationDriverCode.jump]))
        (by simpa [EnumerationDriverCode.jump] using jumpAt 1 (by simp [EnumerationDriverCode.jump]))
    obtain ⟨final,ft,fp,finishTrace,halted,decision,ftime,fspace,checked,unchanged⟩ :=
      finish jumped (jh.trans sh) (js.trans ss) (jo.trans so) jp jr
    have semantic : SupportStream.detectSet parameters.decoder k parameters.buses parameters.bridge.target parameters.drive =
        ResolvedNativeSearch.answer parameters := by
      simp only [SupportStream.detectSet,drive,ite_true,allHealthy]
      rfl
    have jumpedLive : jumped.liveWords = state.liveWords := by simp only [State.liveWords,jh,js,jo,sh,ss,so]
    refine ⟨final,sc+(2+ft),max state.liveWords (max scanned.liveWords fp),scan.append (jump.append finishTrace),
      halted,by simpa only [semantic] using decision,by simp only [allHealthy,ite_true]; omega,?_,
      by simpa only [semantic] using checked,by simpa only [semantic] using unchanged⟩
    have scannedLive : scanned.liveWords = state.liveWords := by simp only [State.liveWords,sh,ss,so]
    rw [scannedLive]
    omega
  | false =>
    have supportPC : scanned.pc = word width (supportEntry roots) := by simpa only [allHealthy,Bool.false_eq_true,ite_false] using sp
    let localState := { scanned with pc := word width 0 }
    obtain ⟨searched,st,speak,search,stime,sspace,result⟩ :=
      SupportNativeSearch.execution parameters raw drive rows roots matched heads rootMatches k (by omega)
        localState (sh.trans heapStored) rfl sr
    have moved := ResidentSegment.execution resident (SupportNativeSearch.code parameters width rows roots k)
      (supportEntry roots) scanned searched st speak supportPC supportAt
      (by have bound := SupportNativeSearch.code_bound (width := width) (k := k) parameters rows roots rootMatches
          dsimp only [supportEntry]; rw [rootCount]; omega) search
    let current := relocatedState (supportEntry roots) searched
    have scannedLive : scanned.liveWords = state.liveWords := by simp only [State.liveWords,sh,ss,so]
    have supportSpace : speak ≤ 120*(parameters.decoder.countedSize+1)+state.stack.length+state.output.length+
        2*(selectedSize parameters).total := by simpa only [localState,ss,so] using sspace
    cases candidate : SupportStream.scanSupports parameters.decoder k parameters.buses parameters.bridge.target (parameters.decoder.evalTable (assignmentOfSet {parameters.bridge.target})) with
    | some K =>
      change SupportStream.scanSupports parameters.decoder k parameters.buses parameters.bridge.target
        (parameters.decoder.evalTable (assignmentOfSet {parameters.bridge.target})) = some K at candidate
      simp only [SupportNativeSearch.Outcome,candidate] at result
      obtain ⟨halted,decision,checked⟩ := result
      have semantic : SupportStream.detectSet parameters.decoder k parameters.buses parameters.bridge.target parameters.drive = some K := by
        simp only [SupportStream.detectSet,drive,ite_true,allHealthy,Bool.false_eq_true,ite_false,candidate]
      refine ⟨current,sc+st,max state.liveWords speak,scan.append moved,halted,?_,
        by simp only [allHealthy,Bool.false_eq_true,ite_false]; omega,by omega,by intro _; exact checked,by simp [semantic]⟩
      simpa only [semantic,Option.isSome_some,ite_true,relocatedState,current] using decision
    | none =>
      change SupportStream.scanSupports parameters.decoder k parameters.buses parameters.bridge.target
        (parameters.decoder.evalTable (assignmentOfSet {parameters.bridge.target})) = none at candidate
      simp only [SupportNativeSearch.Outcome,candidate] at result
      obtain ⟨heap,stack,output,pc,active⟩ := result
      have currentPC : current.pc = word width root := by
        simp only [current,relocatedState,pc,root,rootEntry]
        have lenFits : (SupportNativeSearch.code parameters width rows roots k).length<2^width := by
          have bound := SupportNativeSearch.code_bound (width := width) (k := k) parameters rows roots rootMatches
          omega
        simp only [word,Fin.val_mk,Nat.mod_eq_of_lt lenFits,Nat.add_comm]
      obtain ⟨final,ft,fp,finishTrace,halted,decision,ftime,fspace,checked,unchanged⟩ :=
        finish current (heap.trans sh) (stack.trans ss) (output.trans so) currentPC active
      have semantic : SupportStream.detectSet parameters.decoder k parameters.buses parameters.bridge.target parameters.drive =
          ResolvedNativeSearch.answer parameters := by
        simp only [SupportStream.detectSet,drive,ite_true,allHealthy,Bool.false_eq_true,ite_false,candidate]
        rfl
      have beforeFinish : current.liveWords ≤ speak := search.final_storage_le
      refine ⟨final,sc+(st+ft),max state.liveWords (max speak fp),scan.append (moved.append finishTrace),
        halted,by simpa only [semantic] using decision,by simp only [allHealthy,Bool.false_eq_true,ite_false]; omega,by omega,
        by simpa only [semantic] using checked,by simpa only [semantic] using unchanged⟩

end Controller.Extensions.BoundedNativePrepared
