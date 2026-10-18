module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.AllocateBody
public import Controller.Complexity.ShrinkFields

@[expose] public section

/-! Native release removes the last heap word and advances PC on success.
An empty heap rejects without changing native state. The contract admits
zero registers and nonempty initial heaps larger than word capacity. -/
namespace Controller.Complexity.ReleaseBody
open StackMachine WordReader
open scoped BigOperators

structure Ready (input : Port → List Bool) (state : Controller.Cost.State width registers) : Prop where
  stored : NativeStore.Stored input state
  running : state.halted=false
  clear : ∀ port ∈ FieldSet.work, input port=[]

def shrunk (input : Port → List Bool) (state : Controller.Cost.State width registers) :=
  if state.heap.toList=[] then Function.update input none [false]
  else Function.update input (some 22) (Encoding.encodeWords width state.heap.toList.dropLast)
def cleaned (input : Port → List Bool) (state : Controller.Cost.State width registers) := RegisterWrite.cleared (shrunk input state)
def output (input : Port → List Bool) (state : Controller.Cost.State width registers) :=
  if state.heap.toList=[] then Function.update (RegisterWrite.cleared input) none [false]
  else PcAdvance.output (Function.update (RegisterWrite.cleared input) (some 22) (Encoding.encodeWords width state.heap.toList.dropLast)) state.pc
def updated (state : Controller.Cost.State width registers) := if state.heap.toList=[] then state else { state with heap := state.heap.pop }

def ReleaseLabel : Type := StateReader.LabelsOf HeapRelease.program
instance releaseFintype : Fintype ReleaseLabel := inferInstanceAs (Fintype (StateReader.LabelsOf HeapRelease.program))
def releaseProgram : Program (Fin 31) ReleaseLabel := HeapRelease.program
def WriteLabel : Type := ReleaseLabel ⊕ (Fin 2 ⊕ Fin 2)
instance writeFintype : Fintype WriteLabel := inferInstanceAs (Fintype (ReleaseLabel ⊕ (Fin 2 ⊕ Fin 2)))
def writeProgram : Program (Fin 31) WriteLabel := link releaseProgram LoadBody.cleanup
def Label : Type := WriteLabel ⊕ Option PcAdvance.Label
instance labelFintype : Fintype Label := inferInstanceAs (Fintype (WriteLabel ⊕ Option PcAdvance.Label))
def program : Program (Fin 31) Label := GuardedLink.program writeProgram PcAdvance.program none Option.isNone

theorem release_ready (input : Port → List Bool) (state : Controller.Cost.State width registers) (ready : Ready input state) :
    ShrinkFields.Ready 1 input state.heap.toList where
  packet := by simpa [FieldGet.field] using ready.stored.heapStored
  widthStored := ready.stored.widthStored
  clear := ready.clear

theorem release_output (input : Port → List Bool) (state : Controller.Cost.State width registers) (ready : Ready input state) :
    ShrinkFields.release_output input state.heap.toList=shrunk input state := by
  simp only [ShrinkFields.release_output]
  rw [NativeFieldUpdate.replacement input 1 _ ready.clear,NativeFieldUpdate.rejection input ready.clear]
  rfl

theorem shrunk_stored (input : Port → List Bool) (state : Controller.Cost.State width registers) (stored : NativeStore.Stored input state) :
    NativeStore.Stored (shrunk input state) (updated state) := by
  rcases stored with ⟨hw,hr,hreg,hh,hs,ho,hpc,hhalt⟩
  by_cases empty : state.heap.toList=[] <;>
    simp only [shrunk,updated,empty,↓reduceIte] <;> constructor <;> simp_all

theorem cleaned_shape (input : Port → List Bool) (state : Controller.Cost.State width registers) :
    cleaned input state=if state.heap.toList=[] then Function.update (RegisterWrite.cleared input) none [false]
    else Function.update (RegisterWrite.cleared input) (some 22) (Encoding.encodeWords width state.heap.toList.dropLast) := by
  by_cases empty : state.heap.toList=[] <;> simp only [cleaned,shrunk,empty,↓reduceIte] <;>
    funext port <;> by_cases h3 : port=some 3 <;> by_cases h27 : port=some 27 <;>
      by_cases h22 : port=some 22 <;> by_cases hn : port=none <;> simp_all [RegisterWrite.cleared]

theorem cleaned_stored (input : Port → List Bool) (state : Controller.Cost.State width registers) (stored : NativeStore.Stored input state) :
    NativeStore.Stored (cleaned input state) (updated state) :=
  ((shrunk_stored input state stored).update_other _ _ (some 3) [] (by decide)).update_other _ _ (some 27) [] (by decide)

theorem advance_output (input : Port → List Bool) (state : Controller.Cost.State width registers) (nonempty : state.heap.toList≠[]) :
    PcAdvance.output (cleaned input state) state.pc=output input state := by rw [cleaned_shape]; simp only [output,ite_eq_right nonempty]

theorem success_stored (input : Port → List Bool) (state : Controller.Cost.State width registers) (stored : NativeStore.Stored input state)
    (nonempty : state.heap.toList≠[]) : NativeStore.Stored (output input state) { state.advance with heap := state.heap.pop } := by
  have relation := cleaned_stored input state stored
  simp only [updated,ite_eq_right nonempty] at relation
  have advanced := relation.advance (cleaned input state) { state with heap := state.heap.pop }
  rw [advance_output input state nonempty] at advanced
  exact advanced

theorem invalid_stored (input : Port → List Bool) (state : Controller.Cost.State width registers) (stored : NativeStore.Stored input state)
    (empty : state.heap.toList=[]) : NativeStore.Stored (output input state) state := by
  simpa only [updated,ite_eq_left empty,cleaned_shape,output] using cleaned_stored input state stored

theorem status (input : Port → List Bool) (state : Controller.Cost.State width registers) (ready : Ready input state) :
    (output input state none).head?.isNone=decide (state.heap.toList≠[]) := by
  by_cases empty : state.heap.toList=[] <;>
    simp [output,empty,PcAdvance.output,FieldGet.field,RegisterWrite.cleared,ready.clear none (by simp [FieldSet.work])]

theorem native_transition (input : Port → List Bool) (state : Controller.Cost.State width registers) (ready : Ready input state) :
    LoadBody.observation width registers (output input state)=Controller.Cost.step .release state := by
  unfold LoadBody.observation
  rw [status input state ready]
  by_cases empty : state.heap.toList=[]
  · have flag : state.heap.isEmpty=true := by simpa only [← Array.isEmpty_toList,List.isEmpty_iff] using empty
    simp [empty,Controller.Cost.step,ready.running,flag]
  · have flag : state.heap.isEmpty=false := by simpa only [← Array.isEmpty_toList,List.isEmpty_eq_false_iff] using empty
    rw [(success_stored input state ready.stored empty).observation]
    simp [Controller.Cost.step,ready.running,flag,empty]

theorem pc_ready (input : Port → List Bool) (state : Controller.Cost.State width registers) (ready : Ready input state)
    (nonempty : state.heap.toList≠[]) : PcAdvance.Ready (cleaned input state) state.pc where
  stored := by simpa only [updated,ite_eq_right nonempty] using (cleaned_stored input state ready.stored).widthStored
  pcStored := by simpa [updated,nonempty,FieldGet.field] using (cleaned_stored input state ready.stored).pcStored
  indexEmpty := by simp [cleaned,RegisterWrite.cleared]
  valueEmpty := by simp [cleaned,RegisterWrite.cleared]
  clear := by
    intro port member
    have h3 : port ≠ (some 3 : Port) := by intro equal; subst port; simp [FieldSet.work] at member
    have h27 : port ≠ (some 27 : Port) := by intro equal; subst port; simp [FieldSet.work] at member
    have h22 : port ≠ (some 22 : Port) := by intro equal; subst port; simp [FieldSet.work] at member
    simpa only [cleaned,shrunk,ite_eq_right nonempty,RegisterWrite.cleared,Function.update_of_ne h3,Function.update_of_ne h27,Function.update_of_ne h22] using ready.clear port member

theorem execution (input : Port → List Bool) (state : Controller.Cost.State width registers) (ready : Ready input state) :
    ∃ ticks peak, Execution program ⟨some program.main,input⟩ ⟨none,output input state⟩ ticks peak ∧
      ticks ≤ 16*(FetchSetup.size input)^2+143*FetchSetup.size input+269 ∧
      peak ≤ 16*(FetchSetup.size input)^2+144*FetchSetup.size input+269 := by
  obtain ⟨releaseTicks,releasePeak,releasing,releaseBound,_⟩ := ShrinkFields.release_total input state.heap.toList (release_ready input state ready)
  rw [release_output input state ready] at releasing
  change releaseTicks ≤ 16*(FetchSetup.size input)^2+49*FetchSetup.size input+50 at releaseBound
  obtain ⟨cleanPeak,cleaning⟩ := LoadBody.cleanup_execution (shrunk input state)
  have indexLength : (shrunk input state (some 3)).length=(input (some 3)).length := by by_cases empty : state.heap.toList=[] <;> simp [shrunk,empty]
  have valueLength : (shrunk input state (some 27)).length=(input (some 27)).length := by by_cases empty : state.heap.toList=[] <;> simp [shrunk,empty]
  rw [indexLength,valueLength] at cleaning
  have releasingClean := releasing.link cleaning
  have cell (port : Port) : (input port).length ≤ FetchSetup.size input :=
    Finset.single_le_sum (f := fun address : Port => (input address).length) (fun _ _ => Nat.zero_le _) (Finset.mem_univ port)
  have wBound : width ≤ FetchSetup.size input := by simpa only [ready.stored.widthStored,List.length_replicate] using cell (some 8)
  have indexBound := cell (some 3)
  have valueBound := cell (some 27)
  by_cases empty : state.heap.toList=[]
  · have rejected : Option.isNone ((cleaned input state none).head?)=false := by simp [cleaned_shape,empty]
    have trace := GuardedLink.failure PcAdvance.program none Option.isNone releasingClean rejected
    have same : RegisterWrite.cleared (shrunk input state)=output input state := by
      change cleaned input state=output input state
      simp only [cleaned_shape,output,ite_eq_left empty]
    rw [same] at trace
    have timeBound : (releaseTicks+((input (some 3)).length+(input (some 27)).length+4))+1 ≤ 16*(FetchSetup.size input)^2+143*FetchSetup.size input+269 := by omega
    have space := trace.peak_le
    exact ⟨_,_,trace,timeBound,by change _ ≤ FetchSetup.size input+_ at space; omega⟩
  · obtain ⟨pcTicks,pcPeak,advancing,pcBound,_⟩ := PcAdvance.execution (cleaned input state) state.pc (pc_ready input state ready empty)
    rw [advance_output input state empty] at advancing
    have accepted : Option.isNone ((cleaned input state none).head?)=true := by simp [cleaned_shape,empty,RegisterWrite.cleared,ready.clear none (by simp [FieldSet.work])]
    have trace := GuardedLink.success none Option.isNone releasingClean advancing accepted
    have timeBound : (releaseTicks+((input (some 3)).length+(input (some 27)).length+4))+pcTicks ≤ 16*(FetchSetup.size input)^2+143*FetchSetup.size input+269 := by omega
    have space := trace.peak_le
    exact ⟨_,_,trace,timeBound,by change _ ≤ FetchSetup.size input+_ at space; omega⟩

theorem release_card : Fintype.card ReleaseLabel=116 := by
  have original : Fintype.card (StateReader.LabelsOf HeapRelease.program)=116 := by
    simp only [StateReader.LabelsOf,Fintype.card_sum,Fintype.card_option,Fintype.card_fin,Nat.reduceAdd]
  have same : Fintype.card ReleaseLabel=Fintype.card (StateReader.LabelsOf HeapRelease.program) :=
    @Fintype.card_congr ReleaseLabel (StateReader.LabelsOf HeapRelease.program) _ _ (Equiv.refl _)
  exact same.trans original

theorem canonical_card : Fintype.card Label=520 := by
  have split : Fintype.card Label=(Fintype.card ReleaseLabel+(2+2))+(Fintype.card PcAdvance.Label+1) := by
    change Fintype.card ((ReleaseLabel ⊕ (Fin 2 ⊕ Fin 2)) ⊕ Option PcAdvance.Label)=_
    simp only [Fintype.card_sum,Fintype.card_option,Fintype.card_fin]
  rw [release_card,PcAdvance.canonical_card] at split
  exact split

theorem resident : (∑ label, statementSize (tmStatement (program.code label))) ≤ 4680 := by
  have bound := finiteTM_resident program
  rw [canonical_card] at bound
  exact bound

end Controller.Complexity.ReleaseBody
