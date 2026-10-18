module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Extensions.ResolvedSourceEmit
public import Controller.Cost.SharedWitnessCopy
public import Controller.Cost.SharedWitnessPark

@[expose] public section

/-! A new retained source is generated from stored operands, copied to the
stack, and installed after reclaiming the old heap. The caller frame and
output are preserved throughout this physical heap exchange. -/
namespace Controller.Extensions.SupportSourceRepack
open Controller.Cost Controller.Cost.RawTransferLoops Controller.Cost.SharedDetectorAssembly
open Controller.Extensions.ResolvedSourceEmit

def code (width entry oldCount : Nat) (operands : List (Operand width)) : List (Instruction width 8) :=
  let emit := ResolvedSourceEmit.code width entry operands
  let copyEntry := entry+emit.length
  let releaseEntry := copyEntry+10
  emit ++ ((SharedWitnessCopy.code width copyEntry releaseEntry oldCount operands.length).toList ++
    ((SharedEvaluationReclaim.code width releaseEntry (releaseEntry+7) (oldCount+operands.length)).toList ++
    SharedWitnessPark.code width operands.length))

theorem code_bound (operands : List (Operand width)) :
    (code width entry oldCount operands).length ≤ 14*operands.length+17 := by
  have bound := ResolvedSourceEmit.code_length (entry := entry) operands
  simp only [code,List.length_append,Array.length_toList,SharedWitnessCopy.code_size,
    SharedEvaluationReclaim.code_size,SharedWitnessPark.code_length]
  omega

set_option maxHeartbeats 1200000 in
theorem execution (program : Program width 8) (state : State width 8)
    (entry : Nat) (operands : List (Operand width)) (values : List (Word width))
    (stored : List.Forall₂ (Stored state.heap) operands values)
    (positive : 0<state.heap.size)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry+14*operands.length+17 < 2^width)
    (capacity : state.heap.size+operands.length < 2^width)
    (present : SharedRootRead.BlockAt program entry (code width entry state.heap.size operands)) :
    ∃ final ticks peak, Execution program state final ticks peak ∧
      ticks ≤ 4*state.heap.size+24*operands.length+9 ∧ peak ≤ state.liveWords+2*operands.length ∧
      final.heap = values.toArray ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry+(code width entry state.heap.size operands).length) ∧ final.halted = false := by
  let emitLength := (ResolvedSourceEmit.code width entry operands).length
  let copyEntry := entry+emitLength
  let releaseEntry := copyEntry+10
  have length := stored.length_eq
  have emitBound := ResolvedSourceEmit.code_length (entry := entry) operands
  change emitLength ≤ 12*operands.length at emitBound
  unfold code at present
  have emitAt := block_left program entry _ _ present
  have afterEmit := block_right program entry _ _ present
  have copyAt := block_left program copyEntry _ _ afterEmit
  have afterCopy := block_right program copyEntry _ _ afterEmit
  simp only [Array.length_toList,SharedWitnessCopy.code_size] at afterCopy
  have releaseAt := block_left program releaseEntry _ _ afterCopy
  have loadAt := block_right program releaseEntry _ _ afterCopy
  simp only [Array.length_toList,SharedEvaluationReclaim.code_size] at loadAt
  obtain ⟨emitted,et,emit,etime,eh,es,eo,ep,er⟩ :=
    ResolvedSourceEmit.execution program state entry operands values stored position running
      (by dsimp only [emitLength] at emitBound ⊢; omega) (by omega) emitAt
  have cells : ∀ i (below : i<values.length), emitted.heap[state.heap.size+i]? = some values[i] := by
    intro i below
    rw [eh,Array.getElem?_append_right (Nat.le_add_right _ _)]
    simp only [Nat.add_sub_cancel_left,List.getElem?_toArray,List.getElem?_eq_getElem below]
  obtain ⟨copied,cp,copy,cspace,ch,cs,co,cc,cr,_⟩ :=
    SharedWitnessCopy.execution program emitted state.heap.size values copyEntry releaseEntry ep er
      (by dsimp only [copyEntry]; omega) positive (by omega) cells
      (by simpa only [length] using block_code _ _ _ copyAt)
  have copiedHeap : copied.heap.size = state.heap.size+operands.length := by
    simp only [ch,eh,Array.size_append,List.size_toArray,← length]
  obtain ⟨empty,release,hh,hs,ho,hp,hr,_,_,_,_⟩ :=
    SharedGraphReclaim.setup_execution program copied releaseEntry (releaseEntry+7) #[] copied.heap.toList cc cr
      (by dsimp only [releaseEntry,copyEntry]; omega) (by simp) (by simpa only [Array.length_toList,copiedHeap] using capacity)
      (by simpa only [Array.length_toList,copiedHeap] using block_code _ _ _ releaseAt)
  obtain ⟨final,load,fh,fs,fo,fp,fr,_⟩ :=
    SharedWitnessPark.execution program empty values state.stack (releaseEntry+7) hp hr
      (by dsimp only [releaseEntry,copyEntry]; omega) (by simp only [hh,Array.size_empty]; omega)
      (by rw [hs,cs,es]) (by simpa only [length] using loadAt)
  have emittedLive : emitted.liveWords = state.liveWords+values.length := by
    simp only [State.liveWords,eh,es,eo,Array.size_append,List.size_toArray]; omega
  have copiedLive : copied.liveWords = state.liveWords+2*values.length := by
    simp only [State.liveWords,ch,eh,cs,es,co,eo,Array.size_append,List.size_toArray,List.length_append]; omega
  have emptyLive : empty.liveWords ≤ copied.liveWords := Execution.final_storage_le release
  refine ⟨final,et+((6*values.length+5)+((4*copied.heap.toList.length+4)+2*values.length)),
    max (state.liveWords+values.length) (max cp (max copied.liveWords empty.liveWords)),
    emit.append (copy.append (release.append load)),?_,?_,?_,fs,fo.trans (ho.trans (co.trans eo)),?_,fr⟩
  · simp only [Array.length_toList,copiedHeap]; omega
  · rw [emittedLive] at cspace; omega
  · simpa only [hh,Array.empty_append] using fh
  · rw [fp]
    congr 1
    simp only [code,List.length_append,Array.length_toList,SharedWitnessCopy.code_size,
      SharedEvaluationReclaim.code_size,SharedWitnessPark.code_length]
    dsimp only [releaseEntry,copyEntry,emitLength]
    omega

end Controller.Extensions.SupportSourceRepack
