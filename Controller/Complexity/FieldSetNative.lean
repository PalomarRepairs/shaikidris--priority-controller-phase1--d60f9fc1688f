module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.FieldSet

@[expose] public section

/-! Native-word semantics for executed persistent-field updates. The actual
status agrees with indexed-list membership; acceptance writes the exact native
list update and rejection retains the original encoded field. -/
namespace Controller.Complexity.FieldSetNative
open StackMachine WordReader
open scoped BigOperators

def bits (words : List (Controller.Cost.Word width)) := words.map fun word => Encoding.bits width word.val

structure Ready (slot : Fin 5) (input : Port → List Bool) (words : List (Controller.Cost.Word width)) (index replacement : Controller.Cost.Word width) : Prop where
  packet : input (some (FieldGet.field slot))=Encoding.encodeWords width words
  widthStored : input (some 8)=List.replicate width true
  indexStored : input (some 3)=Encoding.bits width index.val
  replacementStored : input (some 27)=Encoding.bits width replacement.val
  clear : ∀ port ∈ FieldSet.work, input port=[]

theorem Ready.fields (slot : Fin 5) (input : Port → List Bool) (words : List (Controller.Cost.Word width)) (index replacement : Controller.Cost.Word width)
    (ready : Ready slot input words index replacement) :
    FieldSet.Ready slot input width (bits words) (Encoding.bits width index.val) (Encoding.bits width replacement.val) where
  packet := by simpa only [bits,List.length_map,FieldGet.mapped_flatten,Encoding.encodeWords] using ready.packet
  widthStored := ready.widthStored
  indexStored := ready.indexStored
  replacementStored := ready.replacementStored
  widths := by
    intro word member
    obtain ⟨item,_,rfl⟩ := List.mem_map.mp member
    exact Encoding.bits_length width item.val
  replacementWidth := Encoding.bits_length width replacement.val
  clear := ready.clear

def output (slot : Fin 5) (input : Port → List Bool) (words : List (Controller.Cost.Word width)) (index replacement : Controller.Cost.Word width) : Port → List Bool :=
  if index.val<words.length then FieldReplace.output (FieldSet.frame input (bits words)) slot (Encoding.encodeWords width (words.set index.val replacement))
  else WordSelect.output (FieldSet.frame input (bits words)) [false] []

theorem result_set (slot : Fin 5) (input : Port → List Bool) (words : List (List Bool)) (index replacement : List Bool) :
    FieldSet.result slot input words index replacement=
      if Encoding.value index<words.length then FieldReplace.output (FieldSet.frame input words) slot
        (Encoding.frameCount words.length (words.set (Encoding.value index) replacement).flatten)
      else WordSelect.output (FieldSet.frame input words) [false] [] := by
  by_cases valid : Encoding.value index<words.length <;>
    simp [FieldSet.result,valid,List.set_eq_take_append_cons_drop,List.flatten_append,List.flatten_cons]

theorem result_native (slot : Fin 5) (input : Port → List Bool) (words : List (Controller.Cost.Word width)) (index replacement : Controller.Cost.Word width) :
    FieldSet.result slot input (bits words) (Encoding.bits width index.val) (Encoding.bits width replacement.val)=output slot input words index replacement := by
  rw [result_set]
  have updated : ((bits words).set index.val (Encoding.bits width replacement.val)).flatten=Encoding.wordList width (words.set index.val replacement) := by
    rw [bits,← List.map_set,FieldGet.mapped_flatten]
  simp only [Encoding.value_bits width index.val index.isLt,bits,List.length_map] at updated ⊢
  simp only [updated,output,Encoding.encodeWords,List.length_set,bits]

theorem observation (slot : Fin 5) (input : Port → List Bool) (words : List (Controller.Cost.Word width)) (index replacement : Controller.Cost.Word width)
    (ready : Ready slot input words index replacement) :
    Option.isNone ((output slot input words index replacement none).head?)=(words[index.val]?).isSome ∧
    Encoding.decodeWords width (output slot input words index replacement (some (FieldGet.field slot)))=
      some (if index.val<words.length then words.set index.val replacement else words) := by
  constructor
  · by_cases valid : index.val<words.length
    · simp [output,valid,FieldReplace.output,WordSelect.output,bank_counter]
    · simp [output,valid,WordSelect.output,bank_counter]
  · by_cases valid : index.val<words.length
    · have packet : output slot input words index replacement (some (FieldGet.field slot))=
          Encoding.encodeWords width (words.set index.val replacement) := by
        simp [output,valid,FieldReplace.output]
      rw [packet,ite_eq_left valid]
      exact (Encoding.wordsEncoding width).decode_encode (words.set index.val replacement)
    · have packet : output slot input words index replacement (some (FieldGet.field slot))=
          Encoding.encodeWords width words := by
        simp [output,valid,WordSelect.output,WordSkip.reader_at,FieldSet.frame,FieldGet.field_ne slot 0 (by decide),
          FieldGet.field_ne slot 1 (by decide),FieldGet.field_ne slot 2 (by decide),FieldGet.field_ne slot 4 (by decide),FieldGet.field_ne slot 10 (by decide),ready.packet]
      rw [packet,ite_eq_right valid]
      exact (Encoding.wordsEncoding width).decode_encode words

theorem encoded_total (slot : Fin 5) (input : Port → List Bool) (words : List (Controller.Cost.Word width)) (index replacement : Controller.Cost.Word width)
    (ready : Ready slot input words index replacement) :
    ∃ ticks peak, Execution (FieldSet.program slot) ⟨some (FieldSet.program slot).main,input⟩
      ⟨none,output slot input words index replacement⟩ ticks peak ∧
      ticks ≤ 31*(FieldSet.size input)^2+88*FieldSet.size input+74 ∧ peak ≤ 31*(FieldSet.size input)^2+89*FieldSet.size input+74 := by
  simpa only [result_native] using FieldSet.total_polynomial slot input width (bits words)
    (Encoding.bits width index.val) (Encoding.bits width replacement.val) (ready.fields slot input words index replacement)

end Controller.Complexity.FieldSetNative
