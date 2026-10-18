module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.ReturnCommit
public import Controller.Complexity.ReleaseBody

public import Mathlib.Tactic.Ring

@[expose] public section

/-! Native pop erases old temporaries, removes the actual first stack word
and commits that returned word through the fetched destination. Empty stacks
reject without changing any native state packet or advancing PC. -/
namespace Controller.Complexity.PopBody
open StackMachine WordReader
open scoped BigOperators

structure Ready (input : Port → List Bool) (state : Controller.Cost.State width registers)
    (bound : registers ≤ 2^width) (dst : Fin registers) : Prop where
  stored : NativeStore.Stored input state
  running : state.halted=false
  payload : input (some 11)=Encoding.wordList width [InstructionCodec.registerWord bound dst]
  clear : ∀ port ∈ FieldSet.work, input port=[]

def prepared (input : Port → List Bool) := RegisterWrite.cleared input
def tailState (state : Controller.Cost.State width registers) (rest : List (Controller.Cost.Word width)) := { state with stack := rest }
def tailInput (input : Port → List Bool) (rest : List (Controller.Cost.Word width)) :=
  Function.update (prepared input) (some 23) (Encoding.encodeWords width rest)
def popped (input : Port → List Bool) (state : Controller.Cost.State width registers) :=
  match state.stack with
  | [] => Function.update (prepared input) none [false]
  | head :: rest => Function.update (tailInput input rest) (some 1) (Encoding.bits width head.val)
def output (input : Port → List Bool) (state : Controller.Cost.State width registers) (dst : Fin registers) :=
  match state.stack with
  | [] => Function.update (prepared input) none [false]
  | head :: rest => RegisterWrite.completeOutput (tailInput input rest) (tailState state rest) dst head

def PopLabel : Type := StateReader.LabelsOf (FieldPop.program 2)
instance popFintype : Fintype PopLabel := inferInstanceAs (Fintype (StateReader.LabelsOf (FieldPop.program 2)))
def popProgram : Program (Fin 31) PopLabel := FieldPop.program 2
def GuardLabel : Type := PopLabel ⊕ Option ReturnCommit.Label
instance guardFintype : Fintype GuardLabel := inferInstanceAs (Fintype (PopLabel ⊕ Option ReturnCommit.Label))
def guarded : Program (Fin 31) GuardLabel := GuardedLink.program popProgram ReturnCommit.program none Option.isNone
def Label : Type := (Fin 2 ⊕ Fin 2) ⊕ GuardLabel
instance labelFintype : Fintype Label := inferInstanceAs (Fintype ((Fin 2 ⊕ Fin 2) ⊕ GuardLabel))
def program : Program (Fin 31) Label := link LoadBody.cleanup guarded

theorem prepared_stored (input : Port → List Bool) (state : Controller.Cost.State width registers) (stored : NativeStore.Stored input state) :
    NativeStore.Stored (prepared input) state :=
  (stored.update_other input state (some 3) [] (by decide)).update_other _ state (some 27) [] (by decide)

theorem prepared_clear (input : Port → List Bool) (clean : ∀ port ∈ FieldSet.work, input port=[]) :
    ∀ port ∈ FieldSet.work, prepared input port=[] := by
  intro port member
  have h3 : port ≠ (some 3 : Port) := by intro equal; subst port; simp [FieldSet.work] at member
  have h27 : port ≠ (some 27 : Port) := by intro equal; subst port; simp [FieldSet.work] at member
  simpa [prepared,RegisterWrite.cleared,h3,h27] using clean port member

theorem pop_ready (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (dst : Fin registers) (ready : Ready input state bound dst) : ShrinkFields.Ready 2 (prepared input) state.stack where
  packet := by simpa [FieldGet.field] using (prepared_stored input state ready.stored).stackStored
  widthStored := (prepared_stored input state ready.stored).widthStored
  clear := prepared_clear input ready.clear

theorem pop_output (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (dst : Fin registers) (ready : Ready input state bound dst) :
    ShrinkFields.pop_output 2 (prepared input) state.stack=popped input state := by
  cases contents : state.stack with
  | nil => simpa only [ShrinkFields.pop_output,popped,contents] using NativeFieldUpdate.rejection (prepared input) (prepared_clear input ready.clear)
  | cons head rest =>
    simp only [ShrinkFields.pop_output,FieldPop.output,popped,contents]
    rw [NativeFieldUpdate.replacement (prepared input) 2 _ (prepared_clear input ready.clear)]
    rfl

theorem tail_stored (input : Port → List Bool) (state : Controller.Cost.State width registers) (rest : List (Controller.Cost.Word width))
    (stored : NativeStore.Stored input state) : NativeStore.Stored (tailInput input rest) (tailState state rest) := by
  have relation := prepared_stored input state stored
  rcases relation with ⟨hw,hr,hreg,hh,hs,ho,hpc,hhalt⟩
  constructor <;> simp_all [tailInput,tailState]

theorem commit_ready (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (dst : Fin registers) (head : Controller.Cost.Word width) (rest : List (Controller.Cost.Word width))
    (ready : Ready input state bound dst) (contents : state.stack=head :: rest) :
    ReturnCommit.Ready (popped input state) (tailState state rest) bound dst [] head where
  stored := by
    simpa only [popped,contents] using (tail_stored input state rest ready.stored).update_other (tailInput input rest) (tailState state rest) (some 1) (Encoding.bits width head.val) (by decide)
  payload := by simpa [popped,contents,tailInput,prepared,RegisterWrite.cleared] using ready.payload
  wordStored := by simp [popped,contents]
  valueEmpty := by simp [popped,contents,tailInput,prepared,RegisterWrite.cleared]
  clear := by
    intro port member other
    have hs : port ≠ (some 23 : Port) := by intro equal; subst port; simp [FieldSet.work] at member
    simpa only [popped,contents,Function.update_of_ne other,tailInput,Function.update_of_ne hs] using prepared_clear input ready.clear port member

theorem commit_output (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (dst : Fin registers) (head : Controller.Cost.Word width) (rest : List (Controller.Cost.Word width))
    (ready : Ready input state bound dst) (contents : state.stack=head :: rest) :
    ReturnCommit.output (popped input state) (tailState state rest) dst head=output input state dst := by
  have clean := ready.clear (some 1) (by simp [FieldSet.work])
  have restored : Function.update (popped input state) (some 1) []=tailInput input rest := by
    funext port
    by_cases h1 : port=some 1 <;> simp_all [popped,tailInput,prepared,RegisterWrite.cleared]
  rw [ReturnCommit.output,restored]
  simp only [output,contents]

theorem status (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (dst : Fin registers) (ready : Ready input state bound dst) :
    (output input state dst none).head?.isNone=(!state.stack.isEmpty) := by
  cases contents : state.stack <;> simp [output,contents,RegisterWrite.completeOutput,RegisterWrite.output,RegisterWrite.cleared,
    PcAdvance.output,FieldGet.field,tailInput,prepared,ready.clear none (by simp [FieldSet.work])]

theorem invalid_stored (input : Port → List Bool) (state : Controller.Cost.State width registers) (dst : Fin registers)
    (stored : NativeStore.Stored input state) (empty : state.stack=[]) : NativeStore.Stored (output input state dst) state := by
  simpa only [output,empty] using (prepared_stored input state stored).update_other (prepared input) state none [false] (by decide)

theorem native_transition (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (dst : Fin registers) (ready : Ready input state bound dst) :
    LoadBody.observation width registers (output input state dst)=Controller.Cost.step (.pop dst) state := by
  unfold LoadBody.observation
  rw [status input state bound dst ready]
  cases contents : state.stack with
  | nil => simp [contents,Controller.Cost.step,ready.running]
  | cons head rest =>
    simp only [contents,List.isEmpty_cons,Bool.not_false,↓reduceIte,output]
    rw [(RegisterWrite.complete_stored (tailInput input rest) (tailState state rest) dst head (tail_stored input state rest ready.stored)).observation]
    simp [Controller.Cost.step,ready.running,contents,tailState,Controller.Cost.State.put,Controller.Cost.State.advance]

theorem execution (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (dst : Fin registers) (ready : Ready input state bound dst) :
    ∃ ticks peak, Execution program ⟨some program.main,input⟩ ⟨none,output input state dst⟩ ticks peak ∧
      ticks ≤ 2511*(FetchSetup.size input)^2+1460*FetchSetup.size input+394 ∧
      peak ≤ 2511*(FetchSetup.size input)^2+1461*FetchSetup.size input+394 := by
  obtain ⟨cleanPeak,cleaning⟩ := LoadBody.cleanup_execution input
  obtain ⟨popTicks,popPeak,popping,popBound,_⟩ := ShrinkFields.pop_total 2 (prepared input) state.stack (pop_ready input state bound dst ready)
  rw [pop_output input state bound dst ready] at popping
  have a := OperandLoad.update_size_le input (some 3) []
  have b := OperandLoad.update_size_le (Function.update input (some 3) []) (some 27) []
  simp only [List.length_nil,Nat.add_zero] at a b
  have massPrepared : FetchSetup.size (prepared input) ≤ FetchSetup.size input := by change FetchSetup.size (prepared input) ≤ _ at b; omega
  change popTicks ≤ 30*FetchSetup.size (prepared input)+34 at popBound
  have cell (port : Port) : (input port).length ≤ FetchSetup.size input :=
    Finset.single_le_sum (f := fun address : Port => (input address).length) (fun _ _ => Nat.zero_le _) (Finset.mem_univ port)
  have wBound : width ≤ FetchSetup.size input := by simpa only [ready.stored.widthStored,List.length_replicate] using cell (some 8)
  have indexBound := cell (some 3)
  have valueBound := cell (some 27)
  cases contents : state.stack with
  | nil =>
    have rejected : Option.isNone ((popped input state none).head?)=false := by simp [popped,contents]
    have guardedTrace := GuardedLink.failure ReturnCommit.program none Option.isNone popping rejected
    have same : popped input state=output input state dst := by simp only [popped,output,contents]
    rw [same] at guardedTrace
    have trace := cleaning.link guardedTrace
    have timeBound : ((input (some 3)).length+(input (some 27)).length+4)+(popTicks+1) ≤ 2511*(FetchSetup.size input)^2+1460*FetchSetup.size input+394 := by omega
    have space := trace.peak_le
    exact ⟨_,_,trace,timeBound,by change _ ≤ FetchSetup.size input+_ at space; omega⟩
  | cons head rest =>
    obtain ⟨commitTicks,commitPeak,committing,commitBound,_⟩ := ReturnCommit.execution (popped input state) (tailState state rest) bound dst [] head (commit_ready input state bound dst head rest ready contents)
    rw [commit_output input state bound dst head rest ready contents] at committing
    have accepted : Option.isNone ((popped input state none).head?)=true := by
      simp [popped,contents,tailInput,prepared,RegisterWrite.cleared,ready.clear none (by simp [FieldSet.work])]
    have trace := cleaning.link (GuardedLink.success none Option.isNone popping committing accepted)
    have packetBound : (Encoding.encodeWords width rest).length ≤ FetchSetup.size input := by
      have stored := cell (some 23)
      rw [ready.stored.stackStored,contents,Encoding.encodeWords_length] at stored
      rw [Encoding.encodeWords_length]
      simp only [List.length_cons,Nat.mul_add,Nat.mul_one] at stored
      omega
    have first := OperandLoad.update_size_le (prepared input) (some 23) (Encoding.encodeWords width rest)
    have second := OperandLoad.update_size_le (tailInput input rest) (some 1) (Encoding.bits width head.val)
    simp only [Encoding.bits_length] at second
    have massPopped : FetchSetup.size (popped input state) ≤ 3*FetchSetup.size input := by
      change FetchSetup.size (tailInput input rest) ≤ _ at first
      simpa only [popped,contents] using (show FetchSetup.size (Function.update (tailInput input rest) (some 1) (Encoding.bits width head.val)) ≤ 3*FetchSetup.size input by omega)
    have product := Nat.mul_le_mul_left 279 (Nat.pow_le_pow_left massPopped 2)
    have identity : 279*(3*FetchSetup.size input)^2+476*(3*FetchSetup.size input)+356=2511*(FetchSetup.size input)^2+1428*FetchSetup.size input+356 := by ring
    have commitTime : commitTicks ≤ 2511*(FetchSetup.size input)^2+1428*FetchSetup.size input+356 := by rw [← identity]; omega
    have timeBound : ((input (some 3)).length+(input (some 27)).length+4)+(popTicks+commitTicks) ≤ 2511*(FetchSetup.size input)^2+1460*FetchSetup.size input+394 := by omega
    have space := trace.peak_le
    exact ⟨_,_,trace,timeBound,by change _ ≤ FetchSetup.size input+_ at space; omega⟩

theorem pop_card : Fintype.card PopLabel=72 := by
  have original : Fintype.card (StateReader.LabelsOf (FieldPop.program (2 : Fin 5)))=72 := by simp only [StateReader.LabelsOf,Fintype.card_sum,Fintype.card_option,Fintype.card_fin,Nat.reduceAdd]
  have same : Fintype.card PopLabel=Fintype.card (StateReader.LabelsOf (FieldPop.program (2 : Fin 5))) := @Fintype.card_congr PopLabel (StateReader.LabelsOf (FieldPop.program (2 : Fin 5))) _ _ (Equiv.refl _)
  exact same.trans original

theorem guard_card : Fintype.card GuardLabel=778 := by
  have split : Fintype.card GuardLabel=Fintype.card PopLabel+(Fintype.card ReturnCommit.Label+1) := by
    change Fintype.card (PopLabel ⊕ Option ReturnCommit.Label)=_
    simp only [Fintype.card_sum,Fintype.card_option]
  rw [pop_card,ReturnCommit.canonical_card] at split
  exact split

theorem canonical_card : Fintype.card Label=782 := by
  have split : Fintype.card Label=(2+2)+Fintype.card GuardLabel := by
    change Fintype.card ((Fin 2 ⊕ Fin 2) ⊕ GuardLabel)=_
    simp only [Fintype.card_sum,Fintype.card_fin]
  rw [guard_card] at split
  exact split

theorem resident : (∑ label, statementSize (tmStatement (program.code label))) ≤ 7038 := by
  have bound := finiteTM_resident program
  rw [canonical_card] at bound
  exact bound

end Controller.Complexity.PopBody
