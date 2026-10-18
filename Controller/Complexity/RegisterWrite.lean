module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.NativeStore

@[expose] public section

/-! A native register update executes the indexed field writer, then erases
the binary address and replacement temporaries. The exact stored-state
relation identifies the new register function and retains every other field. -/
namespace Controller.Complexity.RegisterWrite
open StackMachine WordReader
open scoped BigOperators

structure Ready (input : Port → List Bool) (state : Controller.Cost.State width registers)
    (bound : registers ≤ 2^width) (dst : Fin registers) (value : Controller.Cost.Word width) : Prop where
  stored : NativeStore.Stored input state
  indexStored : input (some 3)=Encoding.bits width dst.val
  valueStored : input (some 27)=Encoding.bits width value.val
  clear : ∀ port ∈ FieldSet.work, input port=[]

def cleared (input : Port → List Bool) := Function.update (Function.update input (some 3) []) (some 27) []
def output (input : Port → List Bool) (state : Controller.Cost.State width registers) (dst : Fin registers) (value : Controller.Cost.Word width) :=
  Function.update (cleared input) (some 21) (Encoding.encodeWords width ((List.ofFn state.reg).set dst.val value))

def setterProgram : Program (Fin 31) PcAdvance.SetterLabel := FieldSet.program 0
def program := link (link setterProgram (StackClear.program (some 3 : Port))) (StackClear.program (some 27 : Port))

theorem replacement_output (input : Port → List Bool) (packet : List Bool) (clean : ∀ port ∈ FieldSet.work, input port=[]) :
    FieldReplace.output input 0 packet=Function.update input (some 21) packet := by
  have workspace : WordSelect.output (Function.update input (some 20) []) [] []=input := by
    funext address
    have status := clean none (by simp [FieldSet.work])
    have source := clean (some 0) (by simp [FieldSet.work])
    have word := clean (some 1) (by simp [FieldSet.work])
    have scratch := clean (some 2) (by simp [FieldSet.work])
    have counter := clean (some 4) (by simp [FieldSet.work])
    have count := clean (some 10) (by simp [FieldSet.work])
    have buffer := clean (some 20) (by simp [FieldSet.work])
    by_cases hc : address=none <;> by_cases hs : address=some 0 <;> by_cases hw : address=some 1 <;>
      by_cases ht : address=some 2 <;> by_cases hn : address=some 4 <;> by_cases hb : address=some 10 <;>
      by_cases hf : address=some 20 <;> simp_all [WordSelect.output,WordSkip.reader_at]
  change Function.update (WordSelect.output (Function.update input (some 20) []) [] []) (some 21) packet=_
  rw [workspace]

theorem set_output (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (dst : Fin registers) (value : Controller.Cost.Word width) (ready : Ready input state bound dst value) :
    FieldSetNative.output 0 input (List.ofFn state.reg) (InstructionCodec.registerWord bound dst) value=
      Function.update input (some 21) (Encoding.encodeWords width ((List.ofFn state.reg).set dst.val value)) := by
  simp only [FieldSetNative.output,InstructionCodec.registerWord,List.length_ofFn,dst.isLt,ite_eq_left]
  rw [FieldPrepare.frame_output,replacement_output input _ ready.clear]

theorem execution (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (dst : Fin registers) (value : Controller.Cost.Word width) (ready : Ready input state bound dst value) :
    ∃ ticks peak, Execution program ⟨some program.main,input⟩ ⟨none,output input state dst value⟩ ticks peak ∧
      ticks ≤ 31*(FetchSetup.size input)^2+90*FetchSetup.size input+78 ∧
      peak ≤ 31*(FetchSetup.size input)^2+91*FetchSetup.size input+78 := by
  have fields : FieldSetNative.Ready 0 input (List.ofFn state.reg) (InstructionCodec.registerWord bound dst) value := {
    packet := by simpa [FieldGet.field] using ready.stored.registersStored
    widthStored := ready.stored.widthStored
    indexStored := ready.indexStored
    replacementStored := ready.valueStored
    clear := ready.clear }
  obtain ⟨setTicks,setPeak,setting,setBound,_⟩ := FieldSetNative.encoded_total 0 input (List.ofFn state.reg) (InstructionCodec.registerWord bound dst) value fields
  rw [set_output input state bound dst value ready] at setting
  let packet := Encoding.encodeWords width ((List.ofFn state.reg).set dst.val value)
  obtain ⟨indexPeak,indexing⟩ := StackClear.ready_execution (Function.update input (some 21) packet) (some 3)
  obtain ⟨valuePeak,clearing⟩ := StackClear.ready_execution (Function.update (Function.update input (some 21) packet) (some 3) []) (some 27)
  have final : Function.update (Function.update (Function.update input (some 21) packet) (some 3) []) (some 27) []=output input state dst value := by
    funext address
    by_cases hr : address=some 21 <;> by_cases hi : address=some 3 <;> by_cases hv : address=some 27 <;> simp_all [output,cleared,packet]
  rw [final] at clearing
  simp only [Function.update_of_ne (show (some 3 : Port) ≠ some 21 by decide),ready.indexStored,Encoding.bits_length] at indexing
  simp only [Function.update_of_ne (show (some 27 : Port) ≠ some 3 by decide),
    Function.update_of_ne (show (some 27 : Port) ≠ some 21 by decide),ready.valueStored,Encoding.bits_length] at clearing
  have trace := (setting.link indexing).link clearing
  have cell : (input (some 8)).length ≤ FetchSetup.size input :=
    Finset.single_le_sum (f := fun address : Port => (input address).length) (fun _ _ => Nat.zero_le _) (Finset.mem_univ (some 8))
  have wBound : width ≤ FetchSetup.size input := by simpa only [ready.stored.widthStored,List.length_replicate] using cell
  change setTicks ≤ 31*(FetchSetup.size input)^2+88*FetchSetup.size input+74 at setBound
  have timeBound : (setTicks+(width+2))+(width+2) ≤ 31*(FetchSetup.size input)^2+90*FetchSetup.size input+78 := by omega
  have space := trace.peak_le
  change max (max setPeak indexPeak) valuePeak ≤ FetchSetup.size input+((setTicks+(width+2))+(width+2)) at space
  exact ⟨_,_,trace,timeBound,by omega⟩

theorem put_registers (state : Controller.Cost.State width registers) (dst : Fin registers) (value : Controller.Cost.Word width) :
    List.ofFn (state.put dst value).reg=(List.ofFn state.reg).set dst.val value := by
  apply List.ext_getElem (by simp)
  intro index leftBound rightBound
  simp only [Controller.Cost.State.put,List.getElem_ofFn,List.getElem_set]
  have finEqual : (⟨index,by simpa only [List.length_ofFn] using leftBound⟩ : Fin registers)=dst ↔ index=dst.val := Fin.ext_iff
  simp only [finEqual]
  by_cases same : index=dst.val
  · simp only [ite_eq_left same,ite_eq_left same.symm]
  · simp only [ite_eq_right same,ite_eq_right (Ne.symm same)]

theorem stored_output (input : Port → List Bool) (state : Controller.Cost.State width registers) (dst : Fin registers)
    (value : Controller.Cost.Word width) (stored : NativeStore.Stored input state) :
    NativeStore.Stored (output input state dst value) (state.put dst value) := by
  constructor
  · simpa [output,cleared,Controller.Cost.State.put] using stored.widthStored
  · simpa [output,cleared,Controller.Cost.State.put] using stored.countStored
  · simp [output,put_registers]
  · simpa [output,cleared,Controller.Cost.State.put] using stored.heapStored
  · simpa [output,cleared,Controller.Cost.State.put] using stored.stackStored
  · simpa [output,cleared,Controller.Cost.State.put] using stored.outputStored
  · simpa [output,cleared,Controller.Cost.State.put] using stored.pcStored
  · simpa [output,cleared,Controller.Cost.State.put] using stored.haltStored

theorem Ready.pc (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (dst : Fin registers) (value : Controller.Cost.Word width) (ready : Ready input state bound dst value) :
    PcAdvance.Ready (output input state dst value) state.pc where
  stored := by simpa [output,cleared] using ready.stored.widthStored
  pcStored := by simpa [output,cleared,FieldGet.field] using ready.stored.pcStored
  indexEmpty := by simp [output,cleared]
  valueEmpty := by simp [output,cleared]
  clear := by
    intro port member
    have indexOutside : port ≠ (some 3 : Port) := by intro equal; subst port; simp [FieldSet.work] at member
    have valueOutside : port ≠ (some 27 : Port) := by intro equal; subst port; simp [FieldSet.work] at member
    have registerOutside : port ≠ (some 21 : Port) := by intro equal; subst port; simp [FieldSet.work] at member
    simpa [output,cleared,indexOutside,valueOutside,registerOutside] using ready.clear port member

def completeProgram := link program PcAdvance.program
def completeOutput (input : Port → List Bool) (state : Controller.Cost.State width registers) (dst : Fin registers) (value : Controller.Cost.Word width) :=
  PcAdvance.output (output input state dst value) state.pc

theorem complete_execution (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (dst : Fin registers) (value : Controller.Cost.Word width) (ready : Ready input state bound dst value) :
    ∃ ticks peak, Execution completeProgram ⟨some completeProgram.main,input⟩ ⟨none,completeOutput input state dst value⟩ ticks peak ∧
      ticks ≤ 31*(FetchSetup.size input)^2+90*FetchSetup.size input+92*width+293 ∧
      peak ≤ 31*(FetchSetup.size input)^2+91*FetchSetup.size input+92*width+293 := by
  obtain ⟨writeTicks,writePeak,writing,writeBound,_⟩ := execution input state bound dst value ready
  obtain ⟨pcTicks,pcPeak,advancing,pcBound,_⟩ := PcAdvance.execution (output input state dst value) state.pc (ready.pc input state bound dst value)
  have trace := writing.link advancing
  have timeBound : writeTicks+pcTicks ≤ 31*(FetchSetup.size input)^2+90*FetchSetup.size input+92*width+293 := by omega
  have space := trace.peak_le
  change max writePeak pcPeak ≤ FetchSetup.size input+(writeTicks+pcTicks) at space
  exact ⟨_,_,trace,timeBound,by omega⟩

theorem complete_stored (input : Port → List Bool) (state : Controller.Cost.State width registers) (dst : Fin registers)
    (value : Controller.Cost.Word width) (stored : NativeStore.Stored input state) :
    NativeStore.Stored (completeOutput input state dst value) (state.put dst value).advance :=
  (stored_output input state dst value stored).advance (output input state dst value) (state.put dst value)

theorem complete_resident : (∑ label, statementSize (tmStatement (completeProgram.code label))) ≤ 5481 := by
  simpa only [Fintype.card_sum,PcAdvance.setter_card,PcAdvance.canonical_card,Fintype.card_fin,Nat.reduceAdd,Nat.reduceMul]
    using finiteTM_resident completeProgram

theorem resident : (∑ label, statementSize (tmStatement (program.code label))) ≤ 1890 := by
  simpa only [Fintype.card_sum,PcAdvance.setter_card,Fintype.card_fin,Nat.reduceAdd,Nat.reduceMul] using finiteTM_resident program

end Controller.Complexity.RegisterWrite
