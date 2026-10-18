module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Extensions.SupportSearchBody
public import Controller.Extensions.SupportNativeSource
public import Controller.Extensions.ResidentSegment

@[expose] public section

/-! The healthy-zero phase shares one canonical native continuation across
all successful supports. Exhaustion returns the healthy source without a
mask; acceptance emits a checked model and halts. -/
namespace Controller.Extensions.SupportNativeSearch
open Controller Controller.Decoder Controller.Decoder.DAG Controller.Cost
open Controller.Native Controller.Native.SourceController Controller.Cost.NativeSourceExecution
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestInputStored
open Controller.Cost.SharedDetectorAssembly Controller.Cost.RawAdapterProgram

def source (parameters : Parameters) (width : Nat) (rows : List Row) (roots : List Nat) : Array (Word width) :=
  cacheHeap width (SupportCandidate.header width parameters.channels rows roots
    (fun _ : Fin parameters.decoder.nodeCount => false)) rows roots

def nativeCode (parameters : Parameters) (width : Nat) (rows : List Row) (roots : List Nat) : List (Instruction width 8) :=
  SupportNativeSource.code parameters width (source parameters width rows roots).size 0

def start (parameters : Parameters) (roots : List Nat) : Nat :=
  SupportSearchBody.cleanup parameters.channels parameters.buses roots+7

def code (parameters : Parameters) (width : Nat) (rows : List Row) (roots : List Nat) (k : Nat) :
    List (Instruction width 8) :=
  let entry := start parameters roots
  let native := nativeCode parameters width rows roots
  SupportSearchBody.code width parameters.decoder rows roots (fun _ => false) k parameters.buses
    parameters.bridge.target entry (entry+native.length) ++ ResidentSegment.code entry native

theorem code_length (parameters : Parameters) (rows : List Row) (roots : List Nat) (k : Nat) :
    (code parameters width rows roots k).length =
    start parameters roots+(nativeCode parameters width rows roots).length := by
  simp only [code,List.length_append,ResidentSegment.code_length,SupportSearchBody.code_length,start]

theorem code_bound (parameters : Parameters) (rows : List Row) (roots : List Nat)
    (rootMatches : RootsMatch parameters.decoder roots) :
    (code parameters width rows roots k).length ≤
      300*(parameters.decoder.countedSize+1)+34*(selectedSize parameters).total := by
  have native := SupportNativeSource.code_bound (width := width) (base := (source parameters width rows roots).size)
    (entry := 0) parameters
  have size := parameters.decoder.countedSize_eq
  have rootCount : roots.length = parameters.decoder.roots.length := by rw [rootMatches]; simp
  rw [code_length]
  dsimp only [start,SupportSearchBody.cleanup,SupportSearchBody.call,SupportSearchBody.seek,nativeCode]
  split <;> omega

def Outcome (parameters : Parameters) (rows : List Row) (roots : List Nat) (k : Nat)
    (state final : State width 8) : Prop :=
  let healthy := parameters.decoder.evalTable (assignmentOfSet {parameters.bridge.target})
  match SupportStream.scanSupports parameters.decoder k parameters.buses parameters.bridge.target healthy with
  | none => final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (code parameters width rows roots k).length ∧ final.halted = false
  | some _ => final.halted = true ∧ final.reg 4 = word width 1 ∧
      Certificate.ModelCheck.check (formula parameters)
        (NativeRealizedChecked.decodeOutput final.output (compile parameters).toState.count) = true

set_option maxHeartbeats 2000000 in
theorem execution (parameters : Parameters) (raw : parameters.layout = .raw) (drive : parameters.drive = true)
    (rows : List Row) (roots : List Nat) (matched : RowsMatch parameters.decoder rows)
    (heads : UniformDAGSource.HeadsMatch parameters.decoder rows matched)
    (rootMatches : RootsMatch parameters.decoder roots) (k : Nat)
    (capacity : 16384*(parameters.decoder.countedSize+(selectedSize parameters).total+1)<2^width)
    (state : State width 8)
    (heapStored : state.heap = cacheHeap width (SupportCandidate.header width parameters.channels rows roots
      (parameters.decoder.evalTable (assignmentOfSet {parameters.bridge.target}))) rows roots)
    (position : state.pc = word width 0) (running : state.halted = false) :
    ∃ final ticks peak, Execution (code parameters width rows roots k).toArray state final ticks peak ∧
      ticks ≤ (100*(parameters.decoder.countedSize+1)+50)*BoundedAnd.supportCount parameters.channels k+
        200*(parameters.decoder.countedSize+1)+34*(selectedSize parameters).total ∧
      peak ≤ 120*(parameters.decoder.countedSize+1)+state.stack.length+state.output.length+
        2*(selectedSize parameters).total ∧ Outcome parameters rows roots k state final := by
  let graph := parameters.decoder
  let healthy := graph.evalTable (assignmentOfSet {parameters.bridge.target})
  let actual := cacheHeap width (SupportCandidate.header width parameters.channels rows roots healthy) rows roots
  let entry := start parameters roots
  let native := nativeCode parameters width rows roots
  let resident := (code parameters width rows roots k).toArray
  have size := graph.countedSize_eq
  have rootCount : roots.length = graph.roots.length := by rw [rootMatches]; simp only [List.length_map]; rfl
  have present : SharedRootRead.BlockAt resident 0 (code parameters width rows roots k) := by
    intro offset below
    simp only [resident,List.getElem?_toArray,Nat.zero_add]
  have bodyAt := block_left resident 0 _ _ present
  have nativeAt := block_right resident 0 _ _ present
  simp only [SupportSearchBody.code_length,Nat.zero_add] at nativeAt
  have actualBody : SharedRootRead.BlockAt resident 0
      (SupportSearchBody.code width graph rows roots healthy k parameters.buses parameters.bridge.target entry (entry+native.length)) := by
    rw [SupportSearchBody.healthy_independent graph rows roots healthy (fun _ => false)]
    exact bodyAt
  obtain ⟨searched,st,sp,search,stime,sspace,out,result⟩ :=
    SupportSearchBody.execution resident graph rows roots matched heads rootMatches healthy k parameters.buses
      parameters.bridge.target entry (entry+native.length) state heapStored position running (by dsimp only [graph]; omega) actualBody
  have searchSpace : sp ≤ 100*(parameters.decoder.countedSize+1)+state.stack.length+state.output.length := sspace
  cases found : SupportStream.scanSupports graph k parameters.buses parameters.bridge.target healthy with
  | none =>
    rw [found] at result
    obtain ⟨heap,stack,pc,active⟩ := result
    refine ⟨searched,st,sp,search,by dsimp only [graph] at *; omega,by omega,?_⟩
    change Outcome parameters rows roots k state searched
    change SupportStream.scanSupports parameters.decoder k parameters.buses parameters.bridge.target
      (parameters.decoder.evalTable (assignmentOfSet {parameters.bridge.target})) = none at found
    simp only [Outcome,found]
    exact ⟨heap.trans heapStored.symm,stack,out,by simpa only [code_length] using pc,active⟩
  | some K =>
    rw [found] at result
    obtain ⟨⟨chosen,heap,returned⟩,_,pc,active⟩ := result
    let localState := { searched with pc := word width 0 }
    have sourceSize : actual.size = (source parameters width rows roots).size := by
      simp only [actual,source,cacheHeap_size,SupportCandidate.header_size]
      rfl
    have sourceBound := ResolvedRootSource.source_bound (width := width) graph healthy 0 matched rootMatches
    have actualBound : actual.size+parameters.channels ≤ 40*(graph.countedSize+1) := by
      have counted := parameters.decoder.countedSize_eq
      obtain ⟨children,guards⟩ := matched_incidence_lengths parameters.decoder rows matched
      simp only [actual,cacheHeap_size,SupportCandidate.header_size,matched.length_eq,children,guards,rootCount]
      dsimp only [graph] at *
      omega
    have actualNative : SupportNativeSource.code parameters width actual.size 0 = native := by rw [sourceSize]; rfl
    have nativePresent : SharedRootRead.BlockAt native.toArray 0 (SupportNativeSource.code parameters width actual.size 0) := by
      rw [actualNative]
      intro offset below
      simp only [Nat.zero_add,List.getElem?_toArray]
    obtain ⟨emitted,nt,np,emit,halted,decision,ntime,nspace,checked⟩ :=
      SupportNativeSource.execution parameters raw drive native.toArray localState actual chosen K 0 returned heap
        (by simp [actual]) rfl active (by omega) actualBound (by dsimp only [graph] at *; omega) nativePresent
    have moved := ResidentSegment.execution resident native entry searched emitted nt np pc nativeAt
      (by have bound := code_bound (width := width) (k := k) parameters rows roots rootMatches
          rw [code_length] at bound; dsimp only [entry,native] at *; omega) emit
    have searchLive : searched.liveWords ≤ sp := search.final_storage_le
    have sameLive : localState.liveWords = searched.liveWords := rfl
    rw [sameLive] at nspace
    refine ⟨relocatedState entry emitted,st+nt,max sp np,search.append moved,
      by dsimp only [graph] at *; omega,by omega,?_⟩
    change SupportStream.scanSupports parameters.decoder k parameters.buses parameters.bridge.target
      (parameters.decoder.evalTable (assignmentOfSet {parameters.bridge.target})) = some K at found
    simp only [Outcome,found]
    exact ⟨halted,decision,checked⟩

end Controller.Extensions.SupportNativeSearch
