module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.LoadBody

@[expose] public section

/-! The physical indexed heap writer returns its actual guard status and
preserves every other native state packet. Invalid addresses retain the
original heap; valid addresses perform the native array update. -/
namespace Controller.Complexity.HeapWrite
open StackMachine WordReader
open scoped BigOperators

structure Ready (input : Port → List Bool) (state : Controller.Cost.State width registers)
    (index value : Controller.Cost.Word width) : Prop where
  stored : NativeStore.Stored input state
  indexStored : input (some 3)=Encoding.bits width index.val
  valueStored : input (some 27)=Encoding.bits width value.val
  clear : ∀ port ∈ FieldSet.work, input port=[]

def program : Program (Fin 31) PcAdvance.SetterLabel := FieldSet.program 1
def output (input : Port → List Bool) (state : Controller.Cost.State width registers) (index value : Controller.Cost.Word width) :=
  if index.val<state.heap.size then Function.update input (some 22) (Encoding.encodeWords width (state.heap.toList.set index.val value))
  else Function.update input none [false]
def updated (state : Controller.Cost.State width registers) (index value : Controller.Cost.Word width) :=
  if valid : index.val<state.heap.size then { state with heap := state.heap.set index.val value } else state

theorem native_output (input : Port → List Bool) (state : Controller.Cost.State width registers) (index value : Controller.Cost.Word width)
    (ready : Ready input state index value) : FieldSetNative.output 1 input state.heap.toList index value=output input state index value := by
  have status := ready.clear none (by simp [FieldSet.work])
  have source := ready.clear (some 0) (by simp [FieldSet.work])
  have word := ready.clear (some 1) (by simp [FieldSet.work])
  have scratch := ready.clear (some 2) (by simp [FieldSet.work])
  have counter := ready.clear (some 4) (by simp [FieldSet.work])
  have count := ready.clear (some 10) (by simp [FieldSet.work])
  have buffer := ready.clear (some 20) (by simp [FieldSet.work])
  by_cases valid : index.val<state.heap.size
  · simp only [FieldSetNative.output,Array.length_toList,ite_eq_left valid,FieldPrepare.frame_output,output]
    funext port
    by_cases ht : port=some 22 <;> by_cases hc : port=none <;> by_cases hs : port=some 0 <;>
      by_cases hw : port=some 1 <;> by_cases hk : port=some 2 <;> by_cases hi : port=some 4 <;>
      by_cases hn : port=some 10 <;> by_cases hb : port=some 20 <;>
        simp_all [FieldReplace.output,FieldGet.field,WordSelect.output,WordSkip.reader_at]
  · simp only [FieldSetNative.output,Array.length_toList,ite_eq_right valid,FieldPrepare.saved_output,output]
    funext port
    by_cases hc : port=none <;> by_cases hs : port=some 0 <;> by_cases hw : port=some 1 <;>
      by_cases hk : port=some 2 <;> by_cases hi : port=some 4 <;> by_cases hn : port=some 10 <;>
        simp_all [WordSelect.output,WordSkip.reader_at]

theorem execution (input : Port → List Bool) (state : Controller.Cost.State width registers) (index value : Controller.Cost.Word width)
    (ready : Ready input state index value) :
    ∃ ticks peak, Execution program ⟨some program.main,input⟩ ⟨none,output input state index value⟩ ticks peak ∧
      ticks ≤ 31*(FetchSetup.size input)^2+88*FetchSetup.size input+74 ∧
      peak ≤ 31*(FetchSetup.size input)^2+89*FetchSetup.size input+74 := by
  have fields : FieldSetNative.Ready 1 input state.heap.toList index value := {
    packet := by simpa [FieldGet.field] using ready.stored.heapStored
    widthStored := ready.stored.widthStored
    indexStored := ready.indexStored
    replacementStored := ready.valueStored
    clear := ready.clear }
  obtain ⟨ticks,peak,trace,time,space⟩ := FieldSetNative.encoded_total 1 input state.heap.toList index value fields
  rw [native_output input state index value ready] at trace
  exact ⟨ticks,peak,trace,time,space⟩

theorem stored_output (input : Port → List Bool) (state : Controller.Cost.State width registers) (index value : Controller.Cost.Word width)
    (stored : NativeStore.Stored input state) : NativeStore.Stored (output input state index value) (updated state index value) := by
  by_cases valid : index.val<state.heap.size
  · constructor
    · simpa [output,updated,valid] using stored.widthStored
    · simpa [output,updated,valid] using stored.countStored
    · simpa [output,updated,valid] using stored.registersStored
    · simp [output,updated,valid]
    · simpa [output,updated,valid] using stored.stackStored
    · simpa [output,updated,valid] using stored.outputStored
    · simpa [output,updated,valid] using stored.pcStored
    · simpa [output,updated,valid] using stored.haltStored
  · simpa only [output,updated,ite_eq_right valid,dite_eq_right valid] using stored.update_other input state none [false] (by decide)

theorem status (input : Port → List Bool) (state : Controller.Cost.State width registers) (index value : Controller.Cost.Word width)
    (ready : Ready input state index value) :
    (output input state index value none).head?.isNone=decide (index.val<state.heap.size) := by
  by_cases valid : index.val<state.heap.size <;> simp [output,valid,ready.clear none (by simp [FieldSet.work])]

theorem success_size (input : Port → List Bool) (state : Controller.Cost.State width registers) (index value : Controller.Cost.Word width)
    (valid : index.val<state.heap.size) : FetchSetup.size (output input state index value) ≤
      FetchSetup.size input+(Encoding.encodeWords width (state.heap.toList.set index.val value)).length := by
  simpa only [output,ite_eq_left valid] using OperandLoad.update_size_le input (some 22) (Encoding.encodeWords width (state.heap.toList.set index.val value))

theorem resident : (∑ label, statementSize (tmStatement (program.code label))) ≤ 1854 := by
  have bound := finiteTM_resident program
  rw [PcAdvance.setter_card] at bound
  exact bound

end Controller.Complexity.HeapWrite
