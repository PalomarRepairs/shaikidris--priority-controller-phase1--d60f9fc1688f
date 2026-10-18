module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.UnaryAdjust

@[expose] public section

/-! A persistent field is copied and its actual count delimiter consumed before
dynamic list operations. Readiness states physical workspace contents and a
well-formed fixed-width stored field; no semantic execution hypothesis is used. -/
namespace Controller.Complexity.FieldPrepare
open StackMachine WordReader
open scoped BigOperators

structure Ready (slot : Fin 5) (input : Port → List Bool) (width : Nat) (words : List (List Bool)) : Prop where
  packet : input (some (FieldGet.field slot))=Encoding.frameCount words.length words.flatten
  widthStored : input (some 8)=List.replicate width true
  widths : ∀ word ∈ words, word.length=width
  clear : ∀ port ∈ FieldSet.work, input port=[]

abbrev program := FieldSet.prepare
abbrev prepared := FieldSet.prepared
abbrev frame := FieldSet.frame

theorem execution (slot : Fin 5) (input : Port → List Bool) (width : Nat) (words : List (List Bool))
    (ready : Ready slot input width words) :
    ∃ peak, Execution (program slot) ⟨some (program slot).main,input⟩ ⟨none,prepared input words⟩
      (5*(Encoding.frameCount words.length words.flatten).length+4*words.length+8) peak := by
  obtain ⟨copyPeak,copying⟩ := FieldGet.copy_execution slot input _ ready.packet (ready.clear _ (by simp [FieldSet.work])) (ready.clear _ (by simp [FieldSet.work]))
  have reading := ColdInput.read_save_execution input 10 (by decide) (by decide) (by decide) words.length words.flatten [] (ready.clear _ (by simp [FieldSet.work]))
  have entry : bank input [] (Encoding.frameCount words.length words.flatten) []=
      Function.update input (some 0) (Encoding.frameCount words.length words.flatten) := by
    funext address
    have status := ready.clear none (by simp [FieldSet.work])
    have wordClean := ready.clear (some 1) (by simp [FieldSet.work])
    have scratch := ready.clear (some 2) (by simp [FieldSet.work])
    by_cases hc : address=none <;> by_cases hs : address=some 0 <;> by_cases hw : address=some 1 <;>
      by_cases ht : address=some 2 <;> simp_all [WordSkip.reader_at]
  have next : bank (frame input words) [] words.flatten []=prepared input words := by
    funext address
    have countClean := ready.clear (some 4) (by simp [FieldSet.work])
    by_cases hn : address=some 4 <;> simp_all [prepared,FieldSet.prepared,frame,FieldSet.frame,WordSkip.reader_at,WordSkip.data_at]
  change Execution (ColdInput.readSave 10) _ ⟨none,bank (frame input words) [] words.flatten []⟩ _ _ at reading
  rw [entry,next] at reading
  have ticks : (5*(Encoding.frameCount words.length words.flatten).length+4)+(4*words.length+4)=
      5*(Encoding.frameCount words.length words.flatten).length+4*words.length+8 := by omega
  exact ⟨_,by simpa only [program,FieldSet.prepare,ticks] using copying.link reading⟩

theorem prefix_ready (slot : Fin 5) (input : Port → List Bool) (width : Nat) (words : List (List Bool)) (ready : Ready slot input width words) :
    prepared input words=WordPrefix.data (frame input words) 0 words.flatten [] := by
  funext address
  have buffer := ready.clear (some 20) (by simp [FieldSet.work])
  by_cases hb : address=some 20 <;> simp_all [prepared,FieldSet.prepared,frame,FieldSet.frame,WordSkip.data_at,WordPrefix.data_at]

theorem count_update (input : Port → List Bool) (source buffer count : List Bool) :
    Function.update (WordPrefix.data input 0 source buffer) (some 10) count=
      WordPrefix.data (Function.update input (some 10) count) 0 source buffer := by
  funext address
  by_cases same : address=some 10 <;> simp_all [WordPrefix.data_at]

theorem output_count (input : Port → List Bool) (slot : Fin 5) (count packet : List Bool) :
    FieldReplace.output (Function.update input (some 10) count) slot packet=FieldReplace.output input slot packet := by
  funext address
  by_cases ht : address=some (FieldGet.field slot) <;> by_cases hc : address=none <;> by_cases hs : address=some 0 <;>
    by_cases hw : address=some 1 <;> by_cases hk : address=some 2 <;> by_cases hi : address=some 4 <;>
    by_cases hn : address=some 10 <;> by_cases hb : address=some 20 <;>
      simp_all [FieldReplace.output,WordSelect.output,WordSkip.reader_at]

theorem frame_output (input : Port → List Bool) (slot : Fin 5) (words : List (List Bool)) (packet : List Bool) :
    FieldReplace.output (frame input words) slot packet=FieldReplace.output input slot packet :=
  output_count input slot (List.replicate words.length true) packet

theorem saved_output (input : Port → List Bool) (words : List (List Bool)) (status word : List Bool) :
    WordSelect.output (frame input words) status word=WordSelect.output input status word :=
  FieldGet.saved_output input words.length status word

theorem resident (slot : Fin 5) : (∑ label, statementSize (tmStatement ((program slot).code label))) ≤ 171 := by
  simpa only [Fintype.card_sum,Fintype.card_option,Fintype.card_fin,Nat.reduceAdd,Nat.reduceMul] using finiteTM_resident (program slot)

end Controller.Complexity.FieldPrepare
