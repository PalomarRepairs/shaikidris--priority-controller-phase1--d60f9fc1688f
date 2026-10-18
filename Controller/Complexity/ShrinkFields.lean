module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.FieldPop
public import Controller.Complexity.HeapRelease

@[expose] public section

/-! Native-word interfaces for first-word popping and last-word heap release.
Status distinguishes empty rejection from successful zero-width removal.
Returned pop words and retained fields are decoded from actual final banks. -/
namespace Controller.Complexity.ShrinkFields
open StackMachine WordReader

structure Ready (slot : Fin 5) (input : Port → List Bool) (words : List (Controller.Cost.Word width)) : Prop where
  packet : input (some (FieldGet.field slot))=Encoding.encodeWords width words
  widthStored : input (some 8)=List.replicate width true
  clear : ∀ port ∈ FieldSet.work, input port=[]

theorem Ready.fields (slot : Fin 5) (input : Port → List Bool) (words : List (Controller.Cost.Word width))
    (ready : Ready slot input words) : FieldPrepare.Ready slot input width (FieldSetNative.bits words) where
  packet := by simpa only [FieldSetNative.bits,List.length_map,FieldGet.mapped_flatten,Encoding.encodeWords] using ready.packet
  widthStored := ready.widthStored
  widths := by
    intro word member
    obtain ⟨item,_,rfl⟩ := List.mem_map.mp member
    exact Encoding.bits_length width item.val
  clear := ready.clear

def pop_output (slot : Fin 5) (input : Port → List Bool) : List (Controller.Cost.Word width) → Port → List Bool
  | [] => WordSelect.output input [false] []
  | head :: rest => FieldPop.output input slot (Encoding.encodeWords width rest) (Encoding.bits width head.val)

def release_output (input : Port → List Bool) (words : List (Controller.Cost.Word width)) :=
  if words=[] then WordSelect.output input [false] [] else FieldReplace.output input 1 (Encoding.encodeWords width words.dropLast)

theorem pop_result (slot : Fin 5) (input : Port → List Bool) (words : List (Controller.Cost.Word width)) :
    FieldPop.result slot input (FieldSetNative.bits words)=pop_output slot input words := by
  cases words with
  | nil => rfl
  | cons head rest => simp only [FieldSetNative.bits,List.map_cons,FieldPop.result,List.length_map,FieldGet.mapped_flatten,pop_output,Encoding.encodeWords]

theorem release_result (input : Port → List Bool) (words : List (Controller.Cost.Word width)) :
    HeapRelease.result input (FieldSetNative.bits words)=release_output input words := by
  have retained : (FieldSetNative.bits words).dropLast.flatten=Encoding.wordList width words.dropLast := by
    rw [FieldSetNative.bits,← List.map_dropLast,FieldGet.mapped_flatten]
  simp only [HeapRelease.result,retained]
  simp only [FieldSetNative.bits,List.map_eq_nil_iff,List.length_dropLast,List.length_map,release_output,Encoding.encodeWords]

theorem pop_total (slot : Fin 5) (input : Port → List Bool) (words : List (Controller.Cost.Word width)) (ready : Ready slot input words) :
    ∃ ticks peak, Execution (FieldPop.program slot) ⟨some (FieldPop.program slot).main,input⟩
      ⟨none,pop_output slot input words⟩ ticks peak ∧ ticks ≤ 30*FieldGrowth.size input+34 ∧ peak ≤ 31*FieldGrowth.size input+34 := by
  simpa only [pop_result] using FieldPop.total_resources slot input width (FieldSetNative.bits words) (ready.fields slot input words)

theorem release_total (input : Port → List Bool) (words : List (Controller.Cost.Word width)) (ready : Ready 1 input words) :
    ∃ ticks peak, Execution HeapRelease.program ⟨some HeapRelease.program.main,input⟩
      ⟨none,release_output input words⟩ ticks peak ∧
      ticks ≤ 16*(FieldGrowth.size input)^2+49*FieldGrowth.size input+50 ∧ peak ≤ 16*(FieldGrowth.size input)^2+50*FieldGrowth.size input+50 := by
  simpa only [release_result] using HeapRelease.total_polynomial input width (FieldSetNative.bits words) (ready.fields 1 input words)

theorem pop_head (slot : Fin 5) (input : Port → List Bool) (head : Controller.Cost.Word width) (rest : List (Controller.Cost.Word width)) :
    Encoding.decodeWord width (pop_output slot input (head :: rest) (some 1))=some head := by
  simp only [pop_output,FieldPop.output,Function.update_self]
  exact (Encoding.wordEncoding width).decode_encode head

theorem pop_observation (slot : Fin 5) (input : Port → List Bool) (words : List (Controller.Cost.Word width)) (ready : Ready slot input words) :
    Option.isNone ((pop_output slot input words none).head?)=(!words.isEmpty) ∧
    Encoding.decodeWords width (pop_output slot input words (some (FieldGet.field slot)))=some words.tail := by
  cases words with
  | nil =>
    constructor
    · simp [pop_output,WordSelect.output,bank_counter]
    · have packet : pop_output slot input ([] : List (Controller.Cost.Word width)) (some (FieldGet.field slot))=Encoding.encodeWords width [] := by
        simp [pop_output,WordSelect.output,WordSkip.reader_at,FieldGet.field_ne slot 0 (by decide),FieldGet.field_ne slot 1 (by decide),
          FieldGet.field_ne slot 2 (by decide),FieldGet.field_ne slot 4 (by decide),FieldGet.field_ne slot 10 (by decide),ready.packet]
      rw [packet]
      exact (Encoding.wordsEncoding width).decode_encode []
  | cons head rest =>
    constructor
    · simp [pop_output,FieldPop.output,FieldReplace.output,WordSelect.output,bank_counter]
    · have packet : pop_output slot input (head :: rest) (some (FieldGet.field slot))=Encoding.encodeWords width rest := by
        simp [pop_output,FieldPop.output,FieldReplace.output,FieldGet.field_ne slot 1 (by decide)]
      rw [packet]
      exact (Encoding.wordsEncoding width).decode_encode rest

theorem release_observation (input : Port → List Bool) (words : List (Controller.Cost.Word width)) (ready : Ready 1 input words) :
    Option.isNone ((release_output input words none).head?)=(!words.isEmpty) ∧
    Encoding.decodeWords width (release_output input words (some (FieldGet.field 1)))=some words.dropLast := by
  by_cases empty : words=[]
  · subst words
    constructor
    · simp [release_output,WordSelect.output,bank_counter]
    · have packet : release_output input ([] : List (Controller.Cost.Word width)) (some (FieldGet.field 1))=Encoding.encodeWords width [] := by
        simp [release_output,WordSelect.output,WordSkip.reader_at,FieldGet.field_ne 1 0 (by decide),FieldGet.field_ne 1 1 (by decide),
          FieldGet.field_ne 1 2 (by decide),FieldGet.field_ne 1 4 (by decide),FieldGet.field_ne 1 10 (by decide),ready.packet]
      rw [packet]
      exact (Encoding.wordsEncoding width).decode_encode []
  · constructor
    · simp [release_output,empty,FieldReplace.output,WordSelect.output,bank_counter]
    · have packet : release_output input words (some (FieldGet.field 1))=Encoding.encodeWords width words.dropLast := by
        simp [release_output,empty,FieldReplace.output]
      rw [packet]
      exact (Encoding.wordsEncoding width).decode_encode words.dropLast

end Controller.Complexity.ShrinkFields
