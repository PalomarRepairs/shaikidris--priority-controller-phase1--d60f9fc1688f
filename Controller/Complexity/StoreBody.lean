module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.StoreOperands

public import Mathlib.Tactic.Ring

@[expose] public section

/-! The store body prepares both old register operands, executes the indexed
heap writer, clears its temporaries and advances the native PC only when
the actual write status accepts. Failure preserves every native state field. -/
namespace Controller.Complexity.StoreBody
open StackMachine WordReader
open scoped BigOperators

structure Ready (input : Port → List Bool) (state : Controller.Cost.State width registers)
    (bound : registers ≤ 2^width) (address src : Fin registers) : Prop where
  stored : NativeStore.Stored input state
  running : state.halted=false
  payload : input (some 11)=Encoding.wordList width [InstructionCodec.registerWord bound address,InstructionCodec.registerWord bound src]
  clear : ∀ port ∈ FieldSet.work, input port=[]
  bufferEmpty : input (some 28)=[]

def prepared := @StoreOperands.output
def written (input : Port → List Bool) (state : Controller.Cost.State width registers) (address src : Fin registers) :=
  HeapWrite.output (prepared input state address src) state (state.reg address) (state.reg src)
def cleaned (input : Port → List Bool) (state : Controller.Cost.State width registers) (address src : Fin registers) :=
  RegisterWrite.cleared (written input state address src)
def base (input : Port → List Bool) := Function.update (RegisterWrite.cleared input) (some 28) []
def output (input : Port → List Bool) (state : Controller.Cost.State width registers) (address src : Fin registers) :=
  if (state.reg address).val<state.heap.size then PcAdvance.output
    (Function.update (base input) (some 22) (Encoding.encodeWords width (state.heap.toList.set (state.reg address).val (state.reg src)))) state.pc
  else Function.update (base input) none [false]

def WriteLabel : Type := PcAdvance.SetterLabel ⊕ (Fin 2 ⊕ Fin 2)
instance writeFintype : Fintype WriteLabel := inferInstanceAs (Fintype (PcAdvance.SetterLabel ⊕ (Fin 2 ⊕ Fin 2)))
def writeProgram : Program (Fin 31) WriteLabel := link HeapWrite.program LoadBody.cleanup
def GuardLabel : Type := WriteLabel ⊕ Option PcAdvance.Label
instance guardFintype : Fintype GuardLabel := inferInstanceAs (Fintype (WriteLabel ⊕ Option PcAdvance.Label))
def guarded : Program (Fin 31) GuardLabel := GuardedLink.program writeProgram PcAdvance.program none Option.isNone
def Label : Type := StoreOperands.Label ⊕ GuardLabel
instance labelFintype : Fintype Label := inferInstanceAs (Fintype (StoreOperands.Label ⊕ GuardLabel))
def program : Program (Fin 31) Label := link StoreOperands.program guarded

theorem Ready.operands (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (address src : Fin registers) (ready : Ready input state bound address src) : StoreOperands.Ready input state bound address src where
  stored := ready.stored
  payload := ready.payload
  clear := ready.clear
  bufferEmpty := ready.bufferEmpty

theorem cleaned_shape (input : Port → List Bool) (state : Controller.Cost.State width registers) (address src : Fin registers) :
    cleaned input state address src=if (state.reg address).val<state.heap.size then
      Function.update (base input) (some 22) (Encoding.encodeWords width (state.heap.toList.set (state.reg address).val (state.reg src)))
    else Function.update (base input) none [false] := by
  by_cases valid : (state.reg address).val<state.heap.size <;>
    simp only [cleaned,written,HeapWrite.output,valid,↓reduceIte] <;>
    funext port <;>
    by_cases h3 : port=some 3 <;> by_cases h27 : port=some 27 <;> by_cases h28 : port=some 28 <;>
      by_cases h22 : port=some 22 <;> by_cases hn : port=none <;>
        simp_all [base,RegisterWrite.cleared,prepared,StoreOperands.output]

theorem cleaned_stored (input : Port → List Bool) (state : Controller.Cost.State width registers) (address src : Fin registers)
    (stored : NativeStore.Stored input state) : NativeStore.Stored (cleaned input state address src) (HeapWrite.updated state (state.reg address) (state.reg src)) :=
  ((HeapWrite.stored_output _ state _ _ (StoreOperands.stored_output input state address src stored)).update_other _ _ (some 3) [] (by decide)).update_other _ _ (some 27) [] (by decide)

theorem advance_output (input : Port → List Bool) (state : Controller.Cost.State width registers) (address src : Fin registers)
    (valid : (state.reg address).val<state.heap.size) : PcAdvance.output (cleaned input state address src) state.pc=output input state address src := by
  rw [cleaned_shape]
  simp only [output,ite_eq_left valid]

theorem success_stored (input : Port → List Bool) (state : Controller.Cost.State width registers) (address src : Fin registers)
    (stored : NativeStore.Stored input state) (valid : (state.reg address).val<state.heap.size) :
    NativeStore.Stored (output input state address src) { state.advance with heap := state.heap.set (state.reg address).val (state.reg src) } := by
  have relation := cleaned_stored input state address src stored
  simp only [HeapWrite.updated,dite_eq_left valid] at relation
  have advanced := relation.advance (cleaned input state address src) { state with heap := state.heap.set (state.reg address).val (state.reg src) }
  rw [advance_output input state address src valid] at advanced
  exact advanced

theorem invalid_stored (input : Port → List Bool) (state : Controller.Cost.State width registers) (address src : Fin registers)
    (stored : NativeStore.Stored input state) (invalid : ¬(state.reg address).val<state.heap.size) : NativeStore.Stored (output input state address src) state := by
  have relation := cleaned_stored input state address src stored
  simpa only [HeapWrite.updated,dite_eq_right invalid,cleaned_shape,ite_eq_right invalid,output] using relation

theorem status (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (address src : Fin registers) (ready : Ready input state bound address src) :
    (output input state address src none).head?.isNone=decide ((state.reg address).val<state.heap.size) := by
  by_cases valid : (state.reg address).val<state.heap.size <;>
    simp [output,valid,PcAdvance.output,FieldGet.field,base,RegisterWrite.cleared,ready.clear none (by simp [FieldSet.work])]

theorem native_transition (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (address src : Fin registers) (ready : Ready input state bound address src) :
    LoadBody.observation width registers (output input state address src)=Controller.Cost.step (.store address src) state := by
  unfold LoadBody.observation
  rw [status input state bound address src ready]
  by_cases valid : (state.reg address).val<state.heap.size
  · simp only [valid,decide_true,↓reduceIte]
    rw [(success_stored input state address src ready.stored valid).observation]
    simp [Controller.Cost.step,ready.running,valid]
  · simp [valid,Controller.Cost.step,ready.running]

theorem Ready.pc (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (address src : Fin registers) (ready : Ready input state bound address src) (valid : (state.reg address).val<state.heap.size) :
    PcAdvance.Ready (cleaned input state address src) state.pc where
  stored := by simpa only [HeapWrite.updated,dite_eq_left valid] using (cleaned_stored input state address src ready.stored).widthStored
  pcStored := by simpa [HeapWrite.updated,valid,FieldGet.field] using (cleaned_stored input state address src ready.stored).pcStored
  indexEmpty := by simp [cleaned,RegisterWrite.cleared]
  valueEmpty := by simp [cleaned,RegisterWrite.cleared]
  clear := by
    intro port member
    have h3 : port ≠ (some 3 : Port) := by intro equal; subst port; simp [FieldSet.work] at member
    have h27 : port ≠ (some 27 : Port) := by intro equal; subst port; simp [FieldSet.work] at member
    have h22 : port ≠ (some 22 : Port) := by intro equal; subst port; simp [FieldSet.work] at member
    simpa only [cleaned,written,HeapWrite.output,ite_eq_left valid,RegisterWrite.cleared,prepared,
      Function.update_of_ne h3,Function.update_of_ne h27,Function.update_of_ne h22] using
      StoreOperands.clear_output input state address src ready.clear port member

theorem execution (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (address src : Fin registers) (ready : Ready input state bound address src) :
    ∃ ticks peak, Execution program ⟨some program.main,input⟩ ⟨none,output input state address src⟩ ticks peak ∧
      ticks ≤ 738*(FetchSetup.size input)^2+1076*FetchSetup.size input+549 ∧
      peak ≤ 738*(FetchSetup.size input)^2+1077*FetchSetup.size input+549 := by
  obtain ⟨sourceTicks,sourcePeak,sourcing,sourceBound,_⟩ := StoreOperands.execution input state bound address src (ready.operands input state bound address src)
  obtain ⟨writeTicks,writePeak,writing,writeBound,_⟩ := HeapWrite.execution (prepared input state address src) state (state.reg address) (state.reg src)
    (StoreOperands.heap_ready input state address src ready.stored ready.clear)
  obtain ⟨cleanPeak,cleaning⟩ := LoadBody.cleanup_execution (written input state address src)
  have indexLength : (written input state address src (some 3)).length=width := by
    by_cases valid : (state.reg address).val<state.heap.size <;> simp [written,HeapWrite.output,valid,prepared,StoreOperands.output,Encoding.bits_length]
  have valueLength : (written input state address src (some 27)).length=width := by
    by_cases valid : (state.reg address).val<state.heap.size <;> simp [written,HeapWrite.output,valid,prepared,StoreOperands.output,Encoding.bits_length]
  rw [indexLength,valueLength] at cleaning
  have writeCleanTrace := writing.link cleaning
  have cell : (input (some 8)).length ≤ FetchSetup.size input :=
    Finset.single_le_sum (f := fun port : Port => (input port).length) (fun _ _ => Nat.zero_le _) (Finset.mem_univ (some 8))
  have wBound : width ≤ FetchSetup.size input := by simpa only [ready.stored.widthStored,List.length_replicate] using cell
  have mass := StoreOperands.size_output input state address src
  have massBound : FetchSetup.size (prepared input state address src) ≤ 3*FetchSetup.size input := by change FetchSetup.size (prepared input state address src) ≤ _ at mass; omega
  have product := Nat.mul_le_mul_left 31 (Nat.pow_le_pow_left massBound 2)
  have identity : 31*(3*FetchSetup.size input)^2+88*(3*FetchSetup.size input)+74=
      279*(FetchSetup.size input)^2+264*FetchSetup.size input+74 := by ring
  have writeTime : writeTicks ≤ 279*(FetchSetup.size input)^2+264*FetchSetup.size input+74 := by rw [← identity]; omega
  by_cases valid : (state.reg address).val<state.heap.size
  · obtain ⟨pcTicks,pcPeak,advancing,pcBound,_⟩ := PcAdvance.execution (cleaned input state address src) state.pc (ready.pc input state bound address src valid)
    rw [advance_output input state address src valid] at advancing
    have accepted : Option.isNone ((cleaned input state address src none).head?)=true := by
      simp [cleaned_shape,valid,base,RegisterWrite.cleared,ready.clear none (by simp [FieldSet.work])]
    have guardedTrace := GuardedLink.success none Option.isNone writeCleanTrace advancing accepted
    have trace := sourcing.link guardedTrace
    have timeBound : sourceTicks+((writeTicks+(width+width+4))+pcTicks) ≤ 738*(FetchSetup.size input)^2+1076*FetchSetup.size input+549 := by omega
    have space := trace.peak_le
    exact ⟨_,_,trace,timeBound,by change _ ≤ FetchSetup.size input+_ at space; omega⟩
  · have rejected : Option.isNone ((cleaned input state address src none).head?)=false := by simp [cleaned_shape,valid]
    have guardedTrace := GuardedLink.failure PcAdvance.program none Option.isNone writeCleanTrace rejected
    have same : cleaned input state address src=output input state address src := by simp only [cleaned_shape,output,ite_eq_right valid]
    rw [show RegisterWrite.cleared (written input state address src)=output input state address src from same] at guardedTrace
    have trace := sourcing.link guardedTrace
    have timeBound : sourceTicks+((writeTicks+(width+width+4))+1) ≤ 738*(FetchSetup.size input)^2+1076*FetchSetup.size input+549 := by omega
    have space := trace.peak_le
    exact ⟨_,_,trace,timeBound,by change _ ≤ FetchSetup.size input+_ at space; omega⟩

theorem write_card : Fintype.card WriteLabel=210 := by
  have split : Fintype.card WriteLabel=Fintype.card PcAdvance.SetterLabel+(2+2) := by
    change Fintype.card (PcAdvance.SetterLabel ⊕ (Fin 2 ⊕ Fin 2))=_
    simp only [Fintype.card_sum,Fintype.card_fin]
  rw [PcAdvance.setter_card] at split
  exact split

theorem guard_card : Fintype.card GuardLabel=610 := by
  have split : Fintype.card GuardLabel=Fintype.card WriteLabel+(Fintype.card PcAdvance.Label+1) := by
    change Fintype.card (WriteLabel ⊕ Option PcAdvance.Label)=_
    simp only [Fintype.card_sum,Fintype.card_option]
  rw [write_card,PcAdvance.canonical_card] at split
  exact split

theorem canonical_card : Fintype.card Label=1176 := by
  have split : Fintype.card Label=Fintype.card StoreOperands.Label+Fintype.card GuardLabel := by
    change Fintype.card (StoreOperands.Label ⊕ GuardLabel)=_
    simp only [Fintype.card_sum]
  rw [StoreOperands.canonical_card,guard_card] at split
  exact split

theorem resident : (∑ label, statementSize (tmStatement (program.code label))) ≤ 10584 := by
  have bound := finiteTM_resident program
  rw [canonical_card] at bound
  exact bound

end Controller.Complexity.StoreBody
