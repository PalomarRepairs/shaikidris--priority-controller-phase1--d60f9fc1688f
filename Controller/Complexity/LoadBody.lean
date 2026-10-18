module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.LoadCommit

public import Mathlib.Tactic.Ring

@[expose] public section

/-! The native load body reads its address from the old register file,
executes a guarded heap read, and commits the destination and PC only on
success. Both branches erase their address/value temporaries. -/
namespace Controller.Complexity.LoadBody
open StackMachine WordReader
open scoped BigOperators

structure Ready (input : Port → List Bool) (state : Controller.Cost.State width registers)
    (bound : registers ≤ 2^width) (dst address : Fin registers) : Prop where
  stored : NativeStore.Stored input state
  running : state.halted=false
  payload : input (some 11)=Encoding.wordList width [InstructionCodec.registerWord bound dst,InstructionCodec.registerWord bound address]
  clear : ∀ port ∈ FieldSet.work, input port=[]

def prepared (input : Port → List Bool) (state : Controller.Cost.State width registers) (address : Fin registers) :=
  IndirectAddress.output input (state.reg address)
def readOutput (input : Port → List Bool) (state : Controller.Cost.State width registers) (address : Fin registers) :=
  HeapRead.output (prepared input state address) state (state.reg address)
def output (input : Port → List Bool) (state : Controller.Cost.State width registers) (dst address : Fin registers) :=
  if valid : (state.reg address).val<state.heap.size then
    RegisterWrite.completeOutput input state dst state.heap[(state.reg address).val]
  else Function.update (RegisterWrite.cleared input) none [false]

/-- Failure is observed from the actual status stack before decoding state. -/
def observation (width registers : Nat) (storage : Port → List Bool) :=
  if (storage none).head?.isNone then StateNative.observe width registers storage else none

def GuardLabel : Type := PcAdvance.GetterLabel ⊕ Option LoadCommit.Label
instance guardFintype : Fintype GuardLabel := inferInstanceAs (Fintype (PcAdvance.GetterLabel ⊕ Option LoadCommit.Label))
def guarded : Program (Fin 31) GuardLabel := GuardedLink.program HeapRead.program LoadCommit.program none Option.isNone
def cleanup := link (StackClear.program (some 3 : Port)) (StackClear.program (some 27 : Port))
def Label : Type := (IndirectAddress.Label ⊕ GuardLabel) ⊕ (Fin 2 ⊕ Fin 2)
instance labelFintype : Fintype Label := inferInstanceAs (Fintype ((IndirectAddress.Label ⊕ GuardLabel) ⊕ (Fin 2 ⊕ Fin 2)))
def program : Program (Fin 31) Label := link (link (IndirectAddress.program 1) guarded) cleanup

theorem Ready.source (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (dst address : Fin registers) (ready : Ready input state bound dst address) :
    RegisterRead.Ready input [InstructionCodec.registerWord bound dst,InstructionCodec.registerWord bound address] (List.ofFn state.reg) where
  payload := ready.payload
  stored := ready.stored.widthStored
  registersStored := by simpa [FieldGet.field] using ready.stored.registersStored
  clear := ready.clear

theorem Ready.heap (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (dst address : Fin registers) (ready : Ready input state bound dst address) :
    HeapRead.Ready (prepared input state address) state (state.reg address) where
  stored := IndirectAddress.stored_output input _ state ready.stored
  indexStored := by simp [prepared,IndirectAddress.output]
  clear := IndirectAddress.clear_output input _ ready.clear

theorem Ready.commit (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (dst address : Fin registers) (ready : Ready input state bound dst address) (valid : (state.reg address).val<state.heap.size) :
    LoadCommit.Ready (readOutput input state address) state bound dst address state.heap[(state.reg address).val] where
  stored := HeapRead.stored_output _ state _ (ready.heap input state bound dst address).stored
  payload := by simpa [readOutput,HeapRead.output,valid,prepared,IndirectAddress.output] using ready.payload
  wordStored := by simp [readOutput,HeapRead.output,valid]
  valueEmpty := by simp [readOutput,HeapRead.output,valid,prepared,IndirectAddress.output]
  clear := by
    intro port member other
    simpa only [readOutput,HeapRead.output,dite_eq_left valid,Function.update_of_ne other] using
      (ready.heap input state bound dst address).clear port member

theorem cleanup_execution (input : Port → List Bool) :
    ∃ peak, Execution cleanup ⟨some cleanup.main,input⟩ ⟨none,RegisterWrite.cleared input⟩
      ((input (some 3)).length+(input (some 27)).length+4) peak := by
  obtain ⟨a,first⟩ := StackClear.ready_execution input (some 3)
  obtain ⟨b,second⟩ := StackClear.ready_execution (Function.update input (some 3) []) (some 27)
  simp only [Function.update_of_ne (show (some 27 : Port) ≠ some 3 by decide)] at second
  have trace := first.link second
  have total : ((input (some 3)).length+2)+((input (some 27)).length+2)=
      (input (some 3)).length+(input (some 27)).length+4 := by omega
  rw [total] at trace
  exact ⟨max a b,trace⟩

theorem success_output (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (dst address : Fin registers) (ready : Ready input state bound dst address) (valid : (state.reg address).val<state.heap.size) :
    RegisterWrite.cleared (LoadCommit.output (readOutput input state address) state dst state.heap[(state.reg address).val])=
      output input state dst address := by
  funext port
  have clean := ready.clear (some 1) (by simp [FieldSet.work])
  by_cases h1 : port=some 1 <;> by_cases h3 : port=some 3 <;> by_cases h27 : port=some 27 <;>
    by_cases h21 : port=some 21 <;> by_cases h25 : port=some 25 <;>
      simp_all [output,LoadCommit.output,readOutput,HeapRead.output,prepared,IndirectAddress.output,
        RegisterWrite.completeOutput,RegisterWrite.output,RegisterWrite.cleared,PcAdvance.output,FieldGet.field]

theorem failure_output (input : Port → List Bool) (state : Controller.Cost.State width registers) (dst address : Fin registers)
    (invalid : ¬(state.reg address).val<state.heap.size) :
    RegisterWrite.cleared (readOutput input state address)=output input state dst address := by
  simp only [readOutput,HeapRead.output,dite_eq_right invalid,output]
  funext port
  by_cases h3 : port=some 3 <;> by_cases h27 : port=some 27 <;> by_cases hn : port=none <;>
    simp_all [RegisterWrite.cleared,prepared,IndirectAddress.output]

theorem status (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (dst address : Fin registers) (ready : Ready input state bound dst address) :
    (output input state dst address none).head?.isNone=decide ((state.reg address).val<state.heap.size) := by
  by_cases valid : (state.reg address).val<state.heap.size <;>
    simp [output,valid,RegisterWrite.completeOutput,RegisterWrite.output,RegisterWrite.cleared,PcAdvance.output,FieldGet.field,
      ready.clear none (by simp [FieldSet.work])]

theorem invalid_stored (input : Port → List Bool) (state : Controller.Cost.State width registers) (dst address : Fin registers)
    (stored : NativeStore.Stored input state) (invalid : ¬(state.reg address).val<state.heap.size) :
    NativeStore.Stored (output input state dst address) state := by
  simpa only [output,dite_eq_right invalid,RegisterWrite.cleared] using
    ((stored.update_other input state (some 3) [] (by decide)).update_other _ state (some 27) [] (by decide)).update_other _ state none [false] (by decide)

theorem native_transition (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (dst address : Fin registers) (ready : Ready input state bound dst address) :
    observation width registers (output input state dst address)=Controller.Cost.step (.load dst address) state := by
  unfold observation
  rw [status input state bound dst address ready]
  by_cases valid : (state.reg address).val<state.heap.size
  · simp only [valid,decide_true,↓reduceIte,output,↓reduceDIte]
    rw [(RegisterWrite.complete_stored input state dst _ ready.stored).observation]
    simp [Controller.Cost.step,ready.running,valid,Controller.Cost.State.put,Controller.Cost.State.advance]
  · simp [valid,Controller.Cost.step,ready.running]

theorem execution (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (dst address : Fin registers) (ready : Ready input state bound dst address) :
    ∃ ticks peak, Execution program ⟨some program.main,input⟩ ⟨none,output input state dst address⟩ ticks peak ∧
      ticks ≤ 2646*(FetchSetup.size input)^2+1727*FetchSetup.size input+543 ∧
      peak ≤ 2646*(FetchSetup.size input)^2+1728*FetchSetup.size input+543 := by
  have validIndex : ([InstructionCodec.registerWord bound dst,InstructionCodec.registerWord bound address][(1 : Fin 3).val]).val<(List.ofFn state.reg).length := by
    simp [InstructionCodec.registerWord]
  obtain ⟨sourceTicks,sourcePeak,sourcing,sourceBound,_⟩ := IndirectAddress.execution input
    [InstructionCodec.registerWord bound dst,InstructionCodec.registerWord bound address] (List.ofFn state.reg) 1 (by simp) validIndex (ready.source input state bound dst address)
  have sourceValue : (List.ofFn state.reg)[(InstructionCodec.registerWord bound address).val]=state.reg address := by simp [InstructionCodec.registerWord,List.getElem_ofFn]
  change Execution (IndirectAddress.program 1) _ ⟨none,IndirectAddress.output input ((List.ofFn state.reg)[(InstructionCodec.registerWord bound address).val])⟩ _ _ at sourcing
  rw [sourceValue] at sourcing
  obtain ⟨readTicks,readPeak,reading,readBound,_⟩ := HeapRead.execution (prepared input state address) state (state.reg address) (ready.heap input state bound dst address)
  have cell : (input (some 8)).length ≤ FetchSetup.size input :=
    Finset.single_le_sum (f := fun port : Port => (input port).length) (fun _ _ => Nat.zero_le _) (Finset.mem_univ (some 8))
  have wBound : width ≤ FetchSetup.size input := by simpa only [ready.stored.widthStored,List.length_replicate] using cell
  have prepMass := IndirectAddress.size_output input (state.reg address)
  change FetchSetup.size (prepared input state address) ≤ FetchSetup.size input+width at prepMass
  have prepBound : FetchSetup.size (prepared input state address) ≤ 2*FetchSetup.size input := by omega
  have product := Nat.mul_le_mul_left 27 (Nat.pow_le_pow_left prepBound 2)
  have identity : 27*(2*FetchSetup.size input)^2+78*(2*FetchSetup.size input)+56=
      108*(FetchSetup.size input)^2+156*FetchSetup.size input+56 := by ring
  have readTime : readTicks ≤ 108*(FetchSetup.size input)^2+156*FetchSetup.size input+56 := by rw [← identity]; omega
  by_cases valid : (state.reg address).val<state.heap.size
  · obtain ⟨commitTicks,commitPeak,committing,commitBound,_⟩ := LoadCommit.execution (readOutput input state address) state bound dst address _ (ready.commit input state bound dst address valid)
    have accepted : Option.isNone ((readOutput input state address none).head?)=true := by
      simpa only [readOutput,valid,decide_true] using HeapRead.status (prepared input state address) state (state.reg address) (ready.heap input state bound dst address)
    have guardedTrace := GuardedLink.success none Option.isNone reading committing accepted
    obtain ⟨cleanPeak,cleaning⟩ := cleanup_execution (LoadCommit.output (readOutput input state address) state dst state.heap[(state.reg address).val])
    have indexEmpty : LoadCommit.output (readOutput input state address) state dst state.heap[(state.reg address).val] (some 3)=[] := by
      simp [LoadCommit.output,RegisterWrite.completeOutput,RegisterWrite.output,RegisterWrite.cleared,PcAdvance.output,FieldGet.field]
    have valueEmpty : LoadCommit.output (readOutput input state address) state dst state.heap[(state.reg address).val] (some 27)=[] := by
      simp [LoadCommit.output,RegisterWrite.completeOutput,RegisterWrite.output,RegisterWrite.cleared,PcAdvance.output,FieldGet.field]
    rw [indexEmpty,valueEmpty,List.length_nil,Nat.zero_add,success_output input state bound dst address ready valid] at cleaning
    have trace := (sourcing.link guardedTrace).link cleaning
    have mass := HeapRead.success_size (prepared input state address) state (state.reg address) valid
    have massBound : FetchSetup.size (readOutput input state address) ≤ 3*FetchSetup.size input := by change FetchSetup.size (readOutput input state address) ≤ _ at mass; omega
    have square := Nat.mul_le_mul_left 279 (Nat.pow_le_pow_left massBound 2)
    have algebra : 279*(3*FetchSetup.size input)^2+476*(3*FetchSetup.size input)+356=
        2511*(FetchSetup.size input)^2+1428*FetchSetup.size input+356 := by ring
    have commitTime : commitTicks ≤ 2511*(FetchSetup.size input)^2+1428*FetchSetup.size input+356 := by rw [← algebra]; omega
    have timeBound : (sourceTicks+(readTicks+commitTicks))+4 ≤ 2646*(FetchSetup.size input)^2+1727*FetchSetup.size input+543 := by omega
    have space := trace.peak_le
    exact ⟨_,_,trace,timeBound,by change _ ≤ FetchSetup.size input+_ at space; omega⟩
  · have rejected : Option.isNone ((readOutput input state address none).head?)=false := by
      simpa only [readOutput,valid,decide_false] using HeapRead.status (prepared input state address) state (state.reg address) (ready.heap input state bound dst address)
    have guardedTrace := GuardedLink.failure LoadCommit.program none Option.isNone reading rejected
    obtain ⟨cleanPeak,cleaning⟩ := cleanup_execution (readOutput input state address)
    have indexLength : (readOutput input state address (some 3)).length=width := by simp [readOutput,HeapRead.output,valid,prepared,IndirectAddress.output,Encoding.bits_length]
    have valueEmpty : readOutput input state address (some 27)=[] := by simp [readOutput,HeapRead.output,valid,prepared,IndirectAddress.output]
    rw [indexLength,valueEmpty,List.length_nil,Nat.add_zero,failure_output input state dst address valid] at cleaning
    have trace := (sourcing.link guardedTrace).link cleaning
    have timeBound : (sourceTicks+(readTicks+1))+(width+4) ≤ 2646*(FetchSetup.size input)^2+1727*FetchSetup.size input+543 := by omega
    have space := trace.peak_le
    exact ⟨_,_,trace,timeBound,by change _ ≤ FetchSetup.size input+_ at space; omega⟩

theorem guard_card : Fintype.card GuardLabel=878 := by
  have split : Fintype.card GuardLabel=Fintype.card PcAdvance.GetterLabel+(Fintype.card LoadCommit.Label+1) := by
    change Fintype.card (PcAdvance.GetterLabel ⊕ Option LoadCommit.Label)=_
    simp only [Fintype.card_sum,Fintype.card_option]
  rw [PcAdvance.getter_card,LoadCommit.canonical_card] at split
  exact split

theorem canonical_card : Fintype.card Label=1162 := by
  have split : Fintype.card Label=(Fintype.card IndirectAddress.Label+Fintype.card GuardLabel)+(2+2) := by
    change Fintype.card ((IndirectAddress.Label ⊕ GuardLabel) ⊕ (Fin 2 ⊕ Fin 2))=_
    simp only [Fintype.card_sum,Fintype.card_fin]
  rw [IndirectAddress.canonical_card,guard_card] at split
  exact split

theorem resident : (∑ label, statementSize (tmStatement (program.code label))) ≤ 10458 := by
  have bound := finiteTM_resident program
  rw [canonical_card] at bound
  exact bound

end Controller.Complexity.LoadBody
