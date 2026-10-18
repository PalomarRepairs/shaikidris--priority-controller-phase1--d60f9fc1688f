module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.IndirectAddress

public import Mathlib.Tactic.Ring

@[expose] public section

/-! A successful load's returned heap word is moved into replacement27.
The fetched destination is read only after that move, and native register/PC
commit clears all address/value temporaries. -/
namespace Controller.Complexity.LoadCommit
open StackMachine WordReader
open scoped BigOperators

structure Ready (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (dst address : Fin registers) (value : Controller.Cost.Word width) : Prop where
  stored : NativeStore.Stored input state
  payload : input (some 11)=Encoding.wordList width [InstructionCodec.registerWord bound dst,InstructionCodec.registerWord bound address]
  wordStored : input (some 1)=Encoding.bits width value.val
  valueEmpty : input (some 27)=[]
  clear : ∀ port ∈ FieldSet.work, port ≠ some 1 → input port=[]

def moved (input : Port → List Bool) (value : Controller.Cost.Word width) :=
  Function.update (Function.update input (some 1) []) (some 27) (Encoding.bits width value.val)
def loaded (input : Port → List Bool) (bound : registers ≤ 2^width) (dst : Fin registers) (value : Controller.Cost.Word width) :=
  OperandLoad.output (moved input value) false (InstructionCodec.registerWord bound dst)
def output (input : Port → List Bool) (state : Controller.Cost.State width registers) (dst : Fin registers) (value : Controller.Cost.Word width) :=
  RegisterWrite.completeOutput (Function.update input (some 1) []) state dst value

def indexProgram : Program (Fin 31) ConstantBody.OperandLabel := OperandLoad.program 0 false
def commitProgram : Program (Fin 31) CopyBody.CommitLabel := RegisterWrite.completeProgram
def Label : Type := ((Fin 4 ⊕ Fin 4) ⊕ ConstantBody.OperandLabel) ⊕ CopyBody.CommitLabel
instance labelFintype : Fintype Label := inferInstanceAs (Fintype (((Fin 4 ⊕ Fin 4) ⊕ ConstantBody.OperandLabel) ⊕ CopyBody.CommitLabel))
def program : Program (Fin 31) Label := link (link (WordMove.program (some 1) (some 27) (some 2)) indexProgram) commitProgram

theorem moved_stored (input : Port → List Bool) (value : Controller.Cost.Word width) (state : Controller.Cost.State width registers) (stored : NativeStore.Stored input state) :
    NativeStore.Stored (moved input value) state :=
  (stored.update_other input state (some 1) [] (by decide)).update_other (Function.update input (some 1) []) state (some 27) (Encoding.bits width value.val) (by decide)

theorem Ready.moved_clear (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (dst address : Fin registers) (value : Controller.Cost.Word width) (ready : Ready input state bound dst address value) :
    ∀ port ∈ FieldSet.work, moved input value port=[] := by
  intro port member
  have h27 : port ≠ (some 27 : Port) := by intro equal; subst port; simp [FieldSet.work] at member
  by_cases h1 : port=some 1
  · subst port; simp [moved]
  · simpa only [moved,Function.update_of_ne h27,Function.update_of_ne h1] using ready.clear port member h1

theorem Ready.index (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (dst address : Fin registers) (value : Controller.Cost.Word width) (ready : Ready input state bound dst address value) :
    OperandLoad.Ready (moved input value) [InstructionCodec.registerWord bound dst,InstructionCodec.registerWord bound address] where
  payload := by simpa [moved] using ready.payload
  stored := (moved_stored input value state ready.stored).widthStored
  clear := ready.moved_clear input state bound dst address value

theorem Ready.commit (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (dst address : Fin registers) (value : Controller.Cost.Word width) (ready : Ready input state bound dst address value) :
    RegisterWrite.Ready (loaded input bound dst value) state bound dst value where
  stored := OperandLoad.stored_output _ false _ state (moved_stored input value state ready.stored)
  indexStored := by simp [loaded,OperandLoad.output,OperandLoad.destination,InstructionCodec.registerWord]
  valueStored := by simp [loaded,OperandLoad.output,OperandLoad.destination,moved]
  clear := OperandLoad.clear_output _ false _ (ready.moved_clear input state bound dst address value)

theorem commit_output (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (dst : Fin registers) (value : Controller.Cost.Word width) :
    RegisterWrite.completeOutput (loaded input bound dst value) state dst value=output input state dst value := by
  funext port
  by_cases h1 : port=some 1 <;> by_cases h3 : port=some 3 <;> by_cases h27 : port=some 27 <;>
    by_cases h21 : port=some 21 <;> by_cases h25 : port=some 25 <;>
      simp_all [RegisterWrite.completeOutput,RegisterWrite.output,RegisterWrite.cleared,PcAdvance.output,FieldGet.field,
        loaded,OperandLoad.output,OperandLoad.destination,moved,output]

theorem execution (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (dst address : Fin registers) (value : Controller.Cost.Word width) (ready : Ready input state bound dst address value) :
    ∃ ticks peak, Execution program ⟨some program.main,input⟩ ⟨none,output input state dst value⟩ ticks peak ∧
      ticks ≤ 279*(FetchSetup.size input)^2+476*FetchSetup.size input+356 ∧
      peak ≤ 279*(FetchSetup.size input)^2+477*FetchSetup.size input+356 := by
  obtain ⟨movePeak,moving⟩ := WordMove.execution input (some 1) (some 27) (some 2) (by decide) (by decide) (by decide)
    (ready.clear _ (by simp [FieldSet.work]) (by decide))
  simp only [ready.wordStored,ready.valueEmpty,List.append_nil,Encoding.bits_length] at moving
  obtain ⟨indexTicks,indexPeak,indexing,indexBound,_⟩ := OperandLoad.execution (moved input value)
    [InstructionCodec.registerWord bound dst,InstructionCodec.registerWord bound address] 0 false (by simp)
    (ready.index input state bound dst address value)
  obtain ⟨commitTicks,commitPeak,committing,commitBound,_⟩ := RegisterWrite.complete_execution (loaded input bound dst value) state bound dst value
    (ready.commit input state bound dst address value)
  rw [commit_output] at committing
  have trace := (moving.link indexing).link committing
  have cell : (input (some 8)).length ≤ FetchSetup.size input :=
    Finset.single_le_sum (f := fun port : Port => (input port).length) (fun _ _ => Nat.zero_le _) (Finset.mem_univ (some 8))
  have wBound : width ≤ FetchSetup.size input := by simpa only [ready.stored.widthStored,List.length_replicate] using cell
  have a := OperandLoad.update_size_le input (some 1) []
  have b := OperandLoad.update_size_le (Function.update input (some 1) []) (some 27) (Encoding.bits width value.val)
  have c := OperandLoad.update_size_le (moved input value) (some 3) (Encoding.bits width dst.val)
  simp only [List.length_nil,Nat.add_zero,Encoding.bits_length] at a b c
  change FetchSetup.size (moved input value) ≤ FetchSetup.size (Function.update input (some 1) [])+width at b
  change FetchSetup.size (loaded input bound dst value) ≤ FetchSetup.size (moved input value)+width at c
  have movedBound : FetchSetup.size (moved input value) ≤ 2*FetchSetup.size input := by omega
  have loadedBound : FetchSetup.size (loaded input bound dst value) ≤ 3*FetchSetup.size input := by omega
  have product := Nat.mul_le_mul_left 31 (Nat.pow_le_pow_left loadedBound 2)
  have identity : 31*(3*FetchSetup.size input)^2+90*(3*FetchSetup.size input)+92*FetchSetup.size input+293=
      279*(FetchSetup.size input)^2+362*FetchSetup.size input+293 := by ring
  have commitTime : commitTicks ≤ 279*(FetchSetup.size input)^2+362*FetchSetup.size input+293 := by rw [← identity]; omega
  have timeBound : ((4*width+4)+indexTicks)+commitTicks ≤ 279*(FetchSetup.size input)^2+476*FetchSetup.size input+356 := by omega
  have space := trace.peak_le
  change max (max movePeak indexPeak) commitPeak ≤ FetchSetup.size input+(((4*width+4)+indexTicks)+commitTicks) at space
  exact ⟨_,_,trace,timeBound,by omega⟩

theorem canonical_card : Fintype.card Label=705 := by
  have split : Fintype.card Label=((4+4)+Fintype.card ConstantBody.OperandLabel)+Fintype.card CopyBody.CommitLabel := by
    change Fintype.card (((Fin 4 ⊕ Fin 4) ⊕ ConstantBody.OperandLabel) ⊕ CopyBody.CommitLabel)=_
    simp only [Fintype.card_sum,Fintype.card_fin]
  rw [ConstantBody.operand_card,CopyBody.commit_card] at split
  exact split

theorem resident : (∑ label, statementSize (tmStatement (program.code label))) ≤ 6345 := by
  have bound := finiteTM_resident program
  rw [canonical_card] at bound
  exact bound

end Controller.Complexity.LoadCommit
