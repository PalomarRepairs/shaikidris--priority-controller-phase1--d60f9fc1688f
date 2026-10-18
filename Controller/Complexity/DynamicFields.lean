module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.HeapAllocate

@[expose] public section

/-! Native-word interfaces for executed list growth and capacity-checked heap
allocation. Stack/output insertion prepends; heap allocation appends only when
the actual count is below word capacity. Rejection retains the original field. -/
namespace Controller.Complexity.DynamicFields
open StackMachine WordReader

structure Ready (slot : Fin 5) (input : Port → List Bool) (words : List (Controller.Cost.Word width)) (value : Controller.Cost.Word width) : Prop where
  packet : input (some (FieldGet.field slot))=Encoding.encodeWords width words
  widthStored : input (some 8)=List.replicate width true
  valueStored : input (some 27)=Encoding.bits width value.val
  clear : ∀ port ∈ FieldSet.work, input port=[]

theorem Ready.fields (slot : Fin 5) (input : Port → List Bool) (words : List (Controller.Cost.Word width)) (value : Controller.Cost.Word width)
    (ready : Ready slot input words value) :
    FieldGrowth.Ready slot input width (FieldSetNative.bits words) (Encoding.bits width value.val) where
  packet := by simpa only [FieldSetNative.bits,List.length_map,FieldGet.mapped_flatten,Encoding.encodeWords] using ready.packet
  widthStored := ready.widthStored
  widths := by
    intro word member
    obtain ⟨item,_,rfl⟩ := List.mem_map.mp member
    exact Encoding.bits_length width item.val
  clear := ready.clear
  replacementStored := ready.valueStored
  replacementWidth := Encoding.bits_length width value.val

theorem front_packet (words : List (Controller.Cost.Word width)) (value : Controller.Cost.Word width) :
    Encoding.frameCount ((FieldSetNative.bits words).length+1) (Encoding.bits width value.val++(FieldSetNative.bits words).flatten)=
      Encoding.encodeWords width (value :: words) := by
  simp only [FieldSetNative.bits,List.length_map,FieldGet.mapped_flatten,Encoding.encodeWords,List.length_cons,Encoding.wordList,List.flatMap_cons]
  rfl

theorem back_packet (words : List (Controller.Cost.Word width)) (value : Controller.Cost.Word width) :
    Encoding.frameCount ((FieldSetNative.bits words).length+1) ((FieldSetNative.bits words).flatten++Encoding.bits width value.val)=
      Encoding.encodeWords width (words++[value]) := by
  simp only [FieldSetNative.bits,List.length_map,FieldGet.mapped_flatten,Encoding.encodeWords,List.length_append,List.length_cons,List.length_nil,Nat.zero_add,
    Encoding.wordList,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  rfl

def prepend_output (slot : Fin 5) (input : Port → List Bool) (words : List (Controller.Cost.Word width)) (value : Controller.Cost.Word width) :=
  FieldReplace.output input slot (Encoding.encodeWords width (value :: words))

def append_output (slot : Fin 5) (input : Port → List Bool) (words : List (Controller.Cost.Word width)) (value : Controller.Cost.Word width) :=
  FieldReplace.output input slot (Encoding.encodeWords width (words++[value]))

def allocate_output (input : Port → List Bool) (words : List (Controller.Cost.Word width)) (value : Controller.Cost.Word width) :=
  if words.length<2^width then append_output 1 input words value else WordSelect.output input [false] []

theorem prepend_total (slot : Fin 5) (input : Port → List Bool) (words : List (Controller.Cost.Word width)) (value : Controller.Cost.Word width)
    (ready : Ready slot input words value) :
    ∃ ticks peak, Execution (FieldGrowth.prepend slot) ⟨some (FieldGrowth.prepend slot).main,input⟩
      ⟨none,prepend_output slot input words value⟩ ticks peak ∧ ticks ≤ 25*FieldGrowth.size input+28 ∧ peak ≤ 26*FieldGrowth.size input+28 := by
  simpa only [front_packet,prepend_output] using FieldGrowth.prepend_resources slot input width (FieldSetNative.bits words)
    (Encoding.bits width value.val) (ready.fields slot input words value)

theorem append_total (slot : Fin 5) (input : Port → List Bool) (words : List (Controller.Cost.Word width)) (value : Controller.Cost.Word width)
    (ready : Ready slot input words value) :
    ∃ ticks peak, Execution (FieldGrowth.append slot) ⟨some (FieldGrowth.append slot).main,input⟩
      ⟨none,append_output slot input words value⟩ ticks peak ∧ ticks ≤ 25*FieldGrowth.size input+28 ∧ peak ≤ 26*FieldGrowth.size input+28 := by
  simpa only [back_packet,append_output] using FieldGrowth.append_resources slot input width (FieldSetNative.bits words)
    (Encoding.bits width value.val) (ready.fields slot input words value)

theorem allocate_result (input : Port → List Bool) (words : List (Controller.Cost.Word width)) (value : Controller.Cost.Word width) :
    HeapAllocate.result input width (FieldSetNative.bits words) (Encoding.bits width value.val)=allocate_output input words value := by
  unfold HeapAllocate.result
  rw [back_packet]
  simp only [FieldSetNative.bits,List.length_map,allocate_output,append_output]

theorem allocate_total (input : Port → List Bool) (words : List (Controller.Cost.Word width)) (value : Controller.Cost.Word width)
    (ready : Ready 1 input words value) :
    ∃ ticks peak, Execution HeapAllocate.program ⟨some HeapAllocate.program.main,input⟩
      ⟨none,allocate_output input words value⟩ ticks peak ∧
      ticks ≤ 4*(FieldGrowth.size input)^2+41*FieldGrowth.size input+48 ∧ peak ≤ 4*(FieldGrowth.size input)^2+42*FieldGrowth.size input+48 := by
  simpa only [allocate_result] using HeapAllocate.total_polynomial input width (FieldSetNative.bits words)
    (Encoding.bits width value.val) (ready.fields 1 input words value)

theorem prepend_observation (slot : Fin 5) (input : Port → List Bool) (words : List (Controller.Cost.Word width)) (value : Controller.Cost.Word width) :
    Option.isNone ((prepend_output slot input words value none).head?)=true ∧
    Encoding.decodeWords width (prepend_output slot input words value (some (FieldGet.field slot)))=some (value :: words) := by
  constructor
  · simp [prepend_output,FieldReplace.output,WordSelect.output,bank_counter]
  · have packet : prepend_output slot input words value (some (FieldGet.field slot))=Encoding.encodeWords width (value :: words) := by
      simp [prepend_output,FieldReplace.output]
    rw [packet]
    exact (Encoding.wordsEncoding width).decode_encode (value :: words)

theorem append_observation (slot : Fin 5) (input : Port → List Bool) (words : List (Controller.Cost.Word width)) (value : Controller.Cost.Word width) :
    Option.isNone ((append_output slot input words value none).head?)=true ∧
    Encoding.decodeWords width (append_output slot input words value (some (FieldGet.field slot)))=some (words++[value]) := by
  constructor
  · simp [append_output,FieldReplace.output,WordSelect.output,bank_counter]
  · have packet : append_output slot input words value (some (FieldGet.field slot))=Encoding.encodeWords width (words++[value]) := by
      simp [append_output,FieldReplace.output]
    rw [packet]
    exact (Encoding.wordsEncoding width).decode_encode (words++[value])

theorem allocate_observation (input : Port → List Bool) (words : List (Controller.Cost.Word width)) (value : Controller.Cost.Word width)
    (ready : Ready 1 input words value) :
    Option.isNone ((allocate_output input words value none).head?)=decide (words.length<2^width) ∧
    Encoding.decodeWords width (allocate_output input words value (some (FieldGet.field 1)))=
      some (if words.length<2^width then words++[value] else words) := by
  by_cases valid : words.length<2^width
  · simpa [allocate_output,valid] using append_observation 1 input words value
  · constructor
    · simp [allocate_output,valid,WordSelect.output,bank_counter]
    · have packet : allocate_output input words value (some (FieldGet.field 1))=Encoding.encodeWords width words := by
        simp [allocate_output,valid,WordSelect.output,WordSkip.reader_at,FieldGet.field_ne 1 0 (by decide),
          FieldGet.field_ne 1 1 (by decide),FieldGet.field_ne 1 2 (by decide),FieldGet.field_ne 1 4 (by decide),FieldGet.field_ne 1 10 (by decide),ready.packet]
      rw [packet,ite_eq_right valid]
      exact (Encoding.wordsEncoding width).decode_encode words

end Controller.Complexity.DynamicFields
