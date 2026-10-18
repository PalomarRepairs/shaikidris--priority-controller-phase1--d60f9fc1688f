module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.NativeFieldUpdate
public import Controller.Complexity.LoadBody

@[expose] public section

/-! Native push and emit read an old source register, prepend that word to
the selected physical stack/output packet, clear temporaries and advance PC.
Output is prepended, matching the native machine's literal convention. -/
namespace Controller.Complexity.PrependBody
open StackMachine WordReader
open scoped BigOperators

structure Ready (input : Port → List Bool) (state : Controller.Cost.State width registers)
    (bound : registers ≤ 2^width) (src : Fin registers) : Prop where
  stored : NativeStore.Stored input state
  running : state.halted=false
  payload : input (some 11)=Encoding.wordList width [InstructionCodec.registerWord bound src]
  clear : ∀ port ∈ FieldSet.work, input port=[]

def slot (emit : Bool) : Fin 5 := if emit then 3 else 2
def words (emit : Bool) (state : Controller.Cost.State width registers) := if emit then state.output else state.stack
def updated (emit : Bool) (state : Controller.Cost.State width registers) (value : Controller.Cost.Word width) :=
  if emit then { state with output := value :: state.output } else { state with stack := value :: state.stack }
def nativeInstruction (emit : Bool) (src : Fin registers) : Controller.Cost.Instruction width registers :=
  if emit then .emit src else .push src
def sourceLoaded (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width) (src : Fin registers) :=
  RegisterLoad.output input (InstructionCodec.registerWord bound src) (state.reg src)
def grown (emit : Bool) (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width) (src : Fin registers) :=
  Function.update (sourceLoaded input state bound src) (some (FieldGet.field (slot emit))) (Encoding.encodeWords width (state.reg src :: words emit state))
def cleaned (emit : Bool) (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width) (src : Fin registers) :=
  RegisterWrite.cleared (grown emit input state bound src)
def output (emit : Bool) (input : Port → List Bool) (state : Controller.Cost.State width registers) (src : Fin registers) :=
  PcAdvance.output (Function.update (RegisterWrite.cleared input) (some (FieldGet.field (slot emit))) (Encoding.encodeWords width (state.reg src :: words emit state))) state.pc

def GrowLabel : Type := StateReader.LabelsOf (FieldGrowth.prepend 2)
instance growFintype : Fintype GrowLabel := inferInstanceAs (Fintype (StateReader.LabelsOf (FieldGrowth.prepend 2)))
def sourceProgram : Program (Fin 31) CopyBody.SourceLabel := RegisterLoad.program 0
def growProgram (emit : Bool) : Program (Fin 31) GrowLabel := FieldGrowth.prepend (slot emit)
def Label : Type := ((CopyBody.SourceLabel ⊕ GrowLabel) ⊕ (Fin 2 ⊕ Fin 2)) ⊕ PcAdvance.Label
instance labelFintype : Fintype Label := inferInstanceAs (Fintype (((CopyBody.SourceLabel ⊕ GrowLabel) ⊕ (Fin 2 ⊕ Fin 2)) ⊕ PcAdvance.Label))
def program (emit : Bool) : Program (Fin 31) Label := link (link (link sourceProgram (growProgram emit)) LoadBody.cleanup) PcAdvance.program

theorem Ready.source (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (src : Fin registers) (ready : Ready input state bound src) : RegisterRead.Ready input [InstructionCodec.registerWord bound src] (List.ofFn state.reg) where
  payload := ready.payload
  stored := ready.stored.widthStored
  registersStored := by simpa [FieldGet.field] using ready.stored.registersStored
  clear := ready.clear

theorem Ready.grow (emit : Bool) (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (src : Fin registers) (ready : Ready input state bound src) : DynamicFields.Ready (slot emit) (sourceLoaded input state bound src) (words emit state) (state.reg src) where
  packet := by
    cases emit with
    | false => simpa [slot,words,sourceLoaded,RegisterLoad.output,RegisterRead.addressed,FieldGet.field] using ready.stored.stackStored
    | true => simpa [slot,words,sourceLoaded,RegisterLoad.output,RegisterRead.addressed,FieldGet.field] using ready.stored.outputStored
  widthStored := by simpa [sourceLoaded,RegisterLoad.output,RegisterRead.addressed] using ready.stored.widthStored
  valueStored := by simp [sourceLoaded,RegisterLoad.output]
  clear := RegisterLoad.clear_output input _ _ ready.clear

theorem grown_stored (emit : Bool) (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (src : Fin registers) (stored : NativeStore.Stored input state) : NativeStore.Stored (grown emit input state bound src) (updated emit state (state.reg src)) := by
  have relation := RegisterLoad.stored_output input (InstructionCodec.registerWord bound src) (state.reg src) state stored
  rcases relation with ⟨hw,hr,hreg,hh,hs,ho,hpc,hhalt⟩
  cases emit <;> constructor <;>
    simp_all [grown,slot,words,updated,FieldGet.field,sourceLoaded]

theorem cleaned_shape (emit : Bool) (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (src : Fin registers) : cleaned emit input state bound src=
      Function.update (RegisterWrite.cleared input) (some (FieldGet.field (slot emit))) (Encoding.encodeWords width (state.reg src :: words emit state)) := by
  cases emit <;> funext port <;>
    by_cases h3 : port=some 3 <;> by_cases h27 : port=some 27 <;> by_cases hs : port=some 23 <;> by_cases ho : port=some 24 <;>
      simp_all [cleaned,grown,slot,FieldGet.field,RegisterWrite.cleared,sourceLoaded,RegisterLoad.output,RegisterRead.addressed]

theorem cleaned_stored (emit : Bool) (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (src : Fin registers) (stored : NativeStore.Stored input state) : NativeStore.Stored (cleaned emit input state bound src) (updated emit state (state.reg src)) :=
  ((grown_stored emit input state bound src stored).update_other _ _ (some 3) [] (by decide)).update_other _ _ (some 27) [] (by decide)

theorem advance_output (emit : Bool) (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (src : Fin registers) : PcAdvance.output (cleaned emit input state bound src) state.pc=output emit input state src := by rw [cleaned_shape]; rfl

theorem native_transition (emit : Bool) (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (src : Fin registers) (ready : Ready input state bound src) :
    StateNative.observe width registers (output emit input state src)=Controller.Cost.step (nativeInstruction emit src) state := by
  have relation := cleaned_stored emit input state bound src ready.stored
  have advance := relation.advance (cleaned emit input state bound src) (updated emit state (state.reg src))
  cases emit <;> simp only [updated,Bool.false_eq_true,↓reduceIte] at advance <;>
    rw [advance_output] at advance <;> rw [advance.observation] <;>
      simp [nativeInstruction,Controller.Cost.step,ready.running,Controller.Cost.State.advance]

theorem Ready.pc (emit : Bool) (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (src : Fin registers) (ready : Ready input state bound src) : PcAdvance.Ready (cleaned emit input state bound src) state.pc where
  stored := by
    have relation := (cleaned_stored emit input state bound src ready.stored).widthStored
    cases emit <;> simpa [updated] using relation
  pcStored := by
    have relation := (cleaned_stored emit input state bound src ready.stored).pcStored
    cases emit <;> simpa [updated,FieldGet.field] using relation
  indexEmpty := by simp [cleaned,RegisterWrite.cleared]
  valueEmpty := by simp [cleaned,RegisterWrite.cleared]
  clear := by
    intro port member
    have h3 : port ≠ (some 3 : Port) := by intro equal; subst port; simp [FieldSet.work] at member
    have h27 : port ≠ (some 27 : Port) := by intro equal; subst port; simp [FieldSet.work] at member
    have hf : port ≠ some (FieldGet.field (slot emit)) := by
      intro equal; subst port; cases emit <;> simp [FieldGet.field,slot,FieldSet.work] at member
    simpa only [cleaned,RegisterWrite.cleared,grown,Function.update_of_ne h3,Function.update_of_ne h27,Function.update_of_ne hf,sourceLoaded] using
      RegisterLoad.clear_output input (InstructionCodec.registerWord bound src) (state.reg src) ready.clear port member

theorem execution (emit : Bool) (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (src : Fin registers) (ready : Ready input state bound src) :
    ∃ ticks peak, Execution (program emit) ⟨some (program emit).main,input⟩ ⟨none,output emit input state src⟩ ticks peak ∧
      ticks ≤ 27*(FetchSetup.size input)^2+307*FetchSetup.size input+368 ∧
      peak ≤ 27*(FetchSetup.size input)^2+308*FetchSetup.size input+368 := by
  have valid : ([InstructionCodec.registerWord bound src][(0 : Fin 3).val]).val<(List.ofFn state.reg).length := by simp [InstructionCodec.registerWord]
  obtain ⟨sourceTicks,sourcePeak,sourcing,sourceBound,_⟩ := RegisterLoad.execution input [InstructionCodec.registerWord bound src] (List.ofFn state.reg) 0 (by simp) valid (ready.source input state bound src)
  have value : (List.ofFn state.reg)[(InstructionCodec.registerWord bound src).val]=state.reg src := by simp [InstructionCodec.registerWord,List.getElem_ofFn]
  change Execution (RegisterLoad.program 0) _ ⟨none,RegisterLoad.output input (InstructionCodec.registerWord bound src) ((List.ofFn state.reg)[(InstructionCodec.registerWord bound src).val])⟩ _ _ at sourcing
  rw [value] at sourcing
  obtain ⟨growTicks,growPeak,growing,growBound,_⟩ := DynamicFields.prepend_total (slot emit) (sourceLoaded input state bound src) (words emit state) (state.reg src) (ready.grow emit input state bound src)
  change growTicks ≤ 25*FetchSetup.size (sourceLoaded input state bound src)+28 at growBound
  rw [DynamicFields.prepend_output,NativeFieldUpdate.replacement (sourceLoaded input state bound src) (slot emit)
    (Encoding.encodeWords width (state.reg src :: words emit state)) (ready.grow emit input state bound src).clear] at growing
  obtain ⟨cleanPeak,cleaning⟩ := LoadBody.cleanup_execution (grown emit input state bound src)
  have indexLength : (grown emit input state bound src (some 3)).length=width := by cases emit <;> simp [grown,slot,FieldGet.field,sourceLoaded,RegisterLoad.output,RegisterRead.addressed,Encoding.bits_length]
  have valueLength : (grown emit input state bound src (some 27)).length=width := by cases emit <;> simp [grown,slot,FieldGet.field,sourceLoaded,RegisterLoad.output,Encoding.bits_length]
  rw [indexLength,valueLength] at cleaning
  obtain ⟨pcTicks,pcPeak,advancing,pcBound,_⟩ := PcAdvance.execution (cleaned emit input state bound src) state.pc (ready.pc emit input state bound src)
  rw [advance_output] at advancing
  have trace := ((sourcing.link growing).link cleaning).link advancing
  have cell : (input (some 8)).length ≤ FetchSetup.size input :=
    Finset.single_le_sum (f := fun port : Port => (input port).length) (fun _ _ => Nat.zero_le _) (Finset.mem_univ (some 8))
  have wBound : width ≤ FetchSetup.size input := by simpa only [ready.stored.widthStored,List.length_replicate] using cell
  have mass := RegisterLoad.size_output input (InstructionCodec.registerWord bound src) (state.reg src)
  change FetchSetup.size (sourceLoaded input state bound src) ≤ FetchSetup.size input+2*width at mass
  have timeBound : ((sourceTicks+growTicks)+(width+width+4))+pcTicks ≤ 27*(FetchSetup.size input)^2+307*FetchSetup.size input+368 := by omega
  have space := trace.peak_le
  exact ⟨_,_,trace,timeBound,by change _ ≤ FetchSetup.size input+_ at space; omega⟩

theorem grow_card : Fintype.card GrowLabel=51 := by
  have original : Fintype.card (StateReader.LabelsOf (FieldGrowth.prepend (2 : Fin 5)))=51 := by
    simp only [StateReader.LabelsOf,Fintype.card_sum,Fintype.card_option,Fintype.card_fin,Nat.reduceAdd]
  have same : Fintype.card GrowLabel=Fintype.card (StateReader.LabelsOf (FieldGrowth.prepend (2 : Fin 5))) :=
    @Fintype.card_congr GrowLabel (StateReader.LabelsOf (FieldGrowth.prepend (2 : Fin 5))) _ _ (Equiv.refl _)
  exact same.trans original

theorem canonical_card : Fintype.card Label=724 := by
  have split : Fintype.card Label=((Fintype.card CopyBody.SourceLabel+Fintype.card GrowLabel)+(2+2))+Fintype.card PcAdvance.Label := by
    change Fintype.card (((CopyBody.SourceLabel ⊕ GrowLabel) ⊕ (Fin 2 ⊕ Fin 2)) ⊕ PcAdvance.Label)=_
    simp only [Fintype.card_sum,Fintype.card_fin]
  rw [CopyBody.source_card,grow_card,PcAdvance.canonical_card] at split
  exact split

theorem resident (emit : Bool) : (∑ label, statementSize (tmStatement ((program emit).code label))) ≤ 6516 := by
  have bound := finiteTM_resident (program emit)
  rw [canonical_card] at bound
  exact bound

end Controller.Complexity.PrependBody
