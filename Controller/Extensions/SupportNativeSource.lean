module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Extensions.SupportCallback
public import Controller.Extensions.SupportNativeFinish

@[expose] public section

/-! A successful support mask is turned into the forced-target candidate,
copied by fetched reads to the channel input stack, and consumed by the
canonical native model continuation in the same resident program. -/
namespace Controller.Extensions.SupportNativeSource
open Controller Controller.Decoder Controller.Decoder.DAG Controller.Cost
open Controller.Native Controller.Native.SourceController Controller.Cost.NativeSourceExecution
open Controller.Cost.ForestInputStored Controller.Cost.SharedDetectorAssembly

def copyEntry (parameters : Parameters) (width base entry : Nat) : Nat :=
  entry+(SupportCallback.prepareCode width parameters.buses (base+parameters.bridge.target.val)).length

def code (parameters : Parameters) (width base entry : Nat) : List (Instruction width 8) :=
  let copy := copyEntry parameters width base entry
  SupportCallback.prepareCode width parameters.buses (base+parameters.bridge.target.val) ++
    ((SharedWitnessCopy.code width copy (copy+10) base parameters.channels).toList ++
    SupportNativeFinish.code parameters width (base+parameters.channels) (copy+10))

theorem code_bound (parameters : Parameters) :
    (code parameters width base entry).length ≤ 34*(selectedSize parameters).total+17 := by
  have bound := SupportNativeFinish.code_bound (width := width) (base := base+parameters.channels)
    (entry := copyEntry parameters width base entry+10) parameters
  have prepare : (SupportCallback.prepareCode width parameters.buses (base+parameters.bridge.target.val)).length ≤ 5 := by
    rw [SupportCallback.prepareCode_length]; split <;> omega
  simp only [code,List.length_append,Array.length_toList,SharedWitnessCopy.code_size]
  omega

set_option maxHeartbeats 1800000 in
theorem execution (parameters : Parameters) (raw : parameters.layout = .raw) (drive : parameters.drive = true)
    (resident : Program width 8) (state : State width 8) (source : Array (Word width))
    (chosen K : Finset (Channel parameters.channels)) (entry : Nat)
    (returned : BoundedAnd.supportQuery parameters.decoder parameters.buses parameters.bridge.target
      (parameters.decoder.evalTable (assignmentOfSet {parameters.bridge.target})) chosen = some K)
    (heapStored : state.heap = withValues source (assignmentOfSet chosen))
    (positive : 0<source.size) (position : state.pc = word width entry) (running : state.halted = false)
    (entryBound : entry ≤ 128*(parameters.decoder.countedSize+1))
    (sourceBound : source.size+parameters.channels ≤ 40*(parameters.decoder.countedSize+1))
    (capacity : 4096*(parameters.decoder.countedSize+(selectedSize parameters).total+1)<2^width)
    (present : SharedRootRead.BlockAt resident entry (code parameters width source.size entry)) :
    ∃ final ticks peak, Execution resident state final ticks peak ∧ final.halted = true ∧ final.reg 4 = word width 1 ∧
      ticks ≤ 100*(parameters.decoder.countedSize+1)+34*(selectedSize parameters).total ∧
      peak ≤ state.liveWords+20*(parameters.decoder.countedSize+1)+2*(selectedSize parameters).total ∧
      Certificate.ModelCheck.check (formula parameters)
        (NativeRealizedChecked.decodeOutput final.output (compile parameters).toState.count) = true := by
  have candidate : K = BoundedAnd.candidate parameters.buses parameters.bridge.target chosen := by
    unfold BoundedAnd.supportQuery at returned
    dsimp only at returned
    split at returned
    · exact (Option.some.inj returned).symm
    · contradiction
  obtain ⟨eligible,root,member,healthy,truth⟩ := BoundedAnd.supportQuery_some parameters.decoder parameters.buses
    parameters.bridge.target _ chosen K returned
  have differs : ∃ output, parameters.observations output (assignmentOfSet {parameters.bridge.target}) ≠
      parameters.observations output (assignmentOfSet K) := by
    obtain ⟨index,equal⟩ := List.mem_iff_get.mp member
    refine ⟨index,?_⟩
    change parameters.decoder.eval (assignmentOfSet {parameters.bridge.target}) parameters.decoder.roots[index.val] ≠
      parameters.decoder.eval (assignmentOfSet K) parameters.decoder.roots[index.val]
    change parameters.decoder.roots[index.val] = root at equal
    rw [equal,← DAG.evalTable_eq_eval,healthy,truth]
    decide
  let c := copyEntry parameters width source.size entry
  have size := parameters.decoder.countedSize_eq
  have prepLength : (SupportCallback.prepareCode width parameters.buses (source.size+parameters.bridge.target.val)).length ≤ 5 := by
    rw [SupportCallback.prepareCode_length]; split <;> omega
  have cBound : c ≤ entry+5 := by dsimp only [c,copyEntry]; omega
  have nativeBound := SupportNativeFinish.code_bound (width := width) (base := source.size+parameters.channels) (entry := c+10) parameters
  have nativeCount : (compile parameters).toState.count ≤ (selectedSize parameters).total := by
    simp only [selectedSize,NativeSize.total]; omega
  have prepAt := block_left resident entry _ _ present
  have afterPrep := block_right resident entry _ _ present
  have copyAt := block_left resident c _ _ afterPrep
  have nativeAt := block_right resident c _ _ afterPrep
  simp only [Array.length_toList,SharedWitnessCopy.code_size] at nativeAt
  obtain ⟨prepared,pt,pp,prepare,ptime,pspace,ph,ps,po,pc,pr⟩ :=
    SupportCallback.prepare_execution resident state source chosen parameters.bridge.target parameters.buses entry
      heapStored position running (by omega) (by omega) prepAt
  have preparedHeap : prepared.heap = withValues source (assignmentOfSet K) := by simpa only [← candidate] using ph
  let words := LiteralWitnessReturn.words width K
  have wordsLength : words.length = parameters.channels := LiteralWitnessReturn.words_length K
  have cells : ∀ i (below : i<words.length), prepared.heap[source.size+i]? = some words[i] := by
    intro i below
    let channel : Channel parameters.channels := ⟨i,by simpa only [wordsLength] using below⟩
    rw [preparedHeap,Array.getElem?_eq_getElem (by simp; omega)]
    have cell := value_cell source (assignmentOfSet K) channel
    simpa only [words,LiteralWitnessReturn.words,channel,List.getElem_map,List.getElem_finRange,assignmentOfSet,
      Fin.cast_mk] using congrArg some cell
  obtain ⟨copied,cp,copy,cspace,ch,cs,co,cc,cr,_⟩ :=
    SharedWitnessCopy.execution resident prepared source.size words c (c+10) pc pr (by omega) positive
      (by rw [wordsLength]; omega) cells (by simpa only [wordsLength] using block_code _ _ _ copyAt)
  have copiedSize : copied.heap.size = source.size+parameters.channels := by simp only [ch,preparedHeap,withValues_size]
  obtain ⟨final,nt,np,native,ntime,nspace,_,halted,decision,checked⟩ :=
    SupportNativeFinish.execution parameters raw K eligible drive differs resident copied (c+10) prepared.stack cc cr cs
      (by rw [copiedSize]; omega) (by omega) (by rw [copiedSize]; omega)
      (by simpa only [copiedSize] using nativeAt)
  have preparedLive : prepared.liveWords ≤ state.liveWords+1 := (Execution.final_storage_le prepare).trans pspace
  have copiedLive : copied.liveWords = prepared.liveWords+parameters.channels := by
    simp only [State.liveWords,ch,cs,co,List.length_append,wordsLength]; omega
  refine ⟨final,pt+((6*words.length+5)+nt),max pp (max cp np),prepare.append (copy.append native),
    halted,decision,?_,?_,checked⟩
  · rw [wordsLength]; omega
  · rw [wordsLength] at cspace
    omega

end Controller.Extensions.SupportNativeSource
