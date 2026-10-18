module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.CopyBody

@[expose] public section

/-! The physical heap read preserves all native state packets. Its actual
status distinguishes a successful width-zero word from an invalid address;
rejection is not a native halt transition. -/
namespace Controller.Complexity.HeapRead
open StackMachine WordReader
open scoped BigOperators

structure Ready (input : Port → List Bool) (state : Controller.Cost.State width registers) (index : Controller.Cost.Word width) : Prop where
  stored : NativeStore.Stored input state
  indexStored : input (some 3)=Encoding.bits width index.val
  clear : ∀ port ∈ FieldSet.work, input port=[]

def program : Program (Fin 31) PcAdvance.GetterLabel := FieldGet.program 1

def output (input : Port → List Bool) (state : Controller.Cost.State width registers) (index : Controller.Cost.Word width) :=
  if valid : index.val<state.heap.size then Function.update input (some 1) (Encoding.bits width state.heap[index.val].val)
  else Function.update input none [false]

theorem native_output (input : Port → List Bool) (state : Controller.Cost.State width registers) (index : Controller.Cost.Word width)
    (ready : Ready input state index) : FieldGet.native_output input state.heap.toList index=output input state index := by
  funext address
  have status := ready.clear none (by simp [FieldSet.work])
  have source := ready.clear (some 0) (by simp [FieldSet.work])
  have word := ready.clear (some 1) (by simp [FieldSet.work])
  have scratch := ready.clear (some 2) (by simp [FieldSet.work])
  have counter := ready.clear (some 4) (by simp [FieldSet.work])
  have count := ready.clear (some 10) (by simp [FieldSet.work])
  by_cases valid : index.val<state.heap.size <;>
    simp only [FieldGet.native_output,output,Array.length_toList,valid,↓reduceDIte,Array.getElem_toList] <;>
    by_cases hc : address=none <;> by_cases hs : address=some 0 <;> by_cases hw : address=some 1 <;>
    by_cases ht : address=some 2 <;> by_cases hn : address=some 4 <;> by_cases hb : address=some 10 <;>
      simp_all [WordSelect.output,WordSkip.reader_at]

theorem execution (input : Port → List Bool) (state : Controller.Cost.State width registers) (index : Controller.Cost.Word width) (ready : Ready input state index) :
    ∃ ticks peak, Execution program ⟨some program.main,input⟩ ⟨none,output input state index⟩ ticks peak ∧
      ticks ≤ 27*(FetchSetup.size input)^2+78*FetchSetup.size input+56 ∧
      peak ≤ 27*(FetchSetup.size input)^2+79*FetchSetup.size input+56 := by
  obtain ⟨ticks,peak,trace,time,space⟩ := FieldGet.encoded_total 1 input state.heap.toList index
    (by simpa [FieldGet.field] using ready.stored.heapStored) ready.stored.widthStored ready.indexStored
    (ready.clear _ (by simp [FieldSet.work])) (ready.clear _ (by simp [FieldSet.work])) (ready.clear _ (by simp [FieldSet.work]))
    (ready.clear _ (by simp [FieldSet.work])) (ready.clear _ (by simp [FieldSet.work])) (ready.clear _ (by simp [FieldSet.work]))
    (ready.clear _ (by simp [FieldSet.work])) (ready.clear _ (by simp [FieldSet.work])) (ready.clear _ (by simp [FieldSet.work]))
    (ready.clear _ (by simp [FieldSet.work])) (ready.clear _ (by simp [FieldSet.work]))
  rw [native_output input state index ready] at trace
  exact ⟨ticks,peak,trace,time,space⟩

theorem status (input : Port → List Bool) (state : Controller.Cost.State width registers) (index : Controller.Cost.Word width) (ready : Ready input state index) :
    (output input state index none).head?.isNone=decide (index.val<state.heap.size) := by
  by_cases valid : index.val<state.heap.size <;> simp [output,valid,ready.clear none (by simp [FieldSet.work])]

theorem stored_output (input : Port → List Bool) (state : Controller.Cost.State width registers) (index : Controller.Cost.Word width) (stored : NativeStore.Stored input state) :
    NativeStore.Stored (output input state index) state := by
  by_cases valid : index.val<state.heap.size
  · simpa only [output,dite_eq_left valid] using stored.update_other input state (some 1) (Encoding.bits width state.heap[index.val].val) (by decide)
  · simpa only [output,dite_eq_right valid] using stored.update_other input state none [false] (by decide)

theorem success_size (input : Port → List Bool) (state : Controller.Cost.State width registers) (index : Controller.Cost.Word width) (valid : index.val<state.heap.size) :
    FetchSetup.size (output input state index) ≤ FetchSetup.size input+width := by
  simpa only [output,dite_eq_left valid,Encoding.bits_length] using OperandLoad.update_size_le input (some 1) (Encoding.bits width state.heap[index.val].val)

theorem resident : (∑ label, statementSize (tmStatement (program.code label))) ≤ 1548 := by
  have bound := finiteTM_resident program
  rw [PcAdvance.getter_card] at bound
  exact bound

end Controller.Complexity.HeapRead
