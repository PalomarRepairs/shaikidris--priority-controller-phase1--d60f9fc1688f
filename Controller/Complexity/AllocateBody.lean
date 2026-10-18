module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.PrependBody

public import Mathlib.Tactic.Ring

@[expose] public section

/-! Allocation reads an old register, checks the actual heap count against
word capacity, appends on success and advances PC only after an accepted
physical result. Rejection retains every original native state field. -/
namespace Controller.Complexity.AllocateBody
open StackMachine WordReader
open scoped BigOperators

abbrev Ready := @PrependBody.Ready
def sourceLoaded := @PrependBody.sourceLoaded
def grown (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width) (src : Fin registers) :=
  if state.heap.size<2^width then Function.update (sourceLoaded input state bound src) (some 22)
    (Encoding.encodeWords width (state.heap.toList++[state.reg src]))
  else Function.update (sourceLoaded input state bound src) none [false]
def cleaned (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width) (src : Fin registers) :=
  RegisterWrite.cleared (grown input state bound src)
def output (input : Port → List Bool) (state : Controller.Cost.State width registers) (src : Fin registers) :=
  if state.heap.size<2^width then PcAdvance.output (Function.update (RegisterWrite.cleared input) (some 22)
    (Encoding.encodeWords width (state.heap.toList++[state.reg src]))) state.pc
  else Function.update (RegisterWrite.cleared input) none [false]
def updated (state : Controller.Cost.State width registers) (src : Fin registers) :=
  if state.heap.size<2^width then { state with heap := state.heap.push (state.reg src) } else state

def AllocLabel : Type := StateReader.LabelsOf HeapAllocate.program
instance allocFintype : Fintype AllocLabel := inferInstanceAs (Fintype (StateReader.LabelsOf HeapAllocate.program))
def allocProgram : Program (Fin 31) AllocLabel := HeapAllocate.program
def WriteLabel : Type := AllocLabel ⊕ (Fin 2 ⊕ Fin 2)
instance writeFintype : Fintype WriteLabel := inferInstanceAs (Fintype (AllocLabel ⊕ (Fin 2 ⊕ Fin 2)))
def writeProgram : Program (Fin 31) WriteLabel := link allocProgram LoadBody.cleanup
def GuardLabel : Type := WriteLabel ⊕ Option PcAdvance.Label
instance guardFintype : Fintype GuardLabel := inferInstanceAs (Fintype (WriteLabel ⊕ Option PcAdvance.Label))
def guarded : Program (Fin 31) GuardLabel := GuardedLink.program writeProgram PcAdvance.program none Option.isNone
def Label : Type := CopyBody.SourceLabel ⊕ GuardLabel
instance labelFintype : Fintype Label := inferInstanceAs (Fintype (CopyBody.SourceLabel ⊕ GuardLabel))
def program : Program (Fin 31) Label := link PrependBody.sourceProgram guarded

theorem allocation_ready (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (src : Fin registers) (ready : Ready input state bound src) :
    DynamicFields.Ready 1 (sourceLoaded input state bound src) state.heap.toList (state.reg src) where
  packet := by simpa [sourceLoaded,PrependBody.sourceLoaded,RegisterLoad.output,RegisterRead.addressed,FieldGet.field] using ready.stored.heapStored
  widthStored := by simpa [sourceLoaded,PrependBody.sourceLoaded,RegisterLoad.output,RegisterRead.addressed] using ready.stored.widthStored
  valueStored := by simp [sourceLoaded,PrependBody.sourceLoaded,RegisterLoad.output]
  clear := RegisterLoad.clear_output input _ _ ready.clear

theorem allocation_output (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (src : Fin registers) (ready : Ready input state bound src) :
    DynamicFields.allocate_output (sourceLoaded input state bound src) state.heap.toList (state.reg src)=grown input state bound src := by
  simp only [DynamicFields.allocate_output,Array.length_toList,DynamicFields.append_output]
  rw [NativeFieldUpdate.replacement _ _ _ (allocation_ready input state bound src ready).clear,
    NativeFieldUpdate.rejection _ (allocation_ready input state bound src ready).clear]
  rfl

theorem grown_stored (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (src : Fin registers) (stored : NativeStore.Stored input state) : NativeStore.Stored (grown input state bound src) (updated state src) := by
  have relation := RegisterLoad.stored_output input (InstructionCodec.registerWord bound src) (state.reg src) state stored
  rcases relation with ⟨hw,hr,hreg,hh,hs,ho,hpc,hhalt⟩
  by_cases valid : state.heap.size<2^width <;>
    simp only [grown,updated,valid,↓reduceIte] <;> constructor <;>
      simp_all [sourceLoaded,PrependBody.sourceLoaded]

theorem cleaned_shape (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width) (src : Fin registers) :
    cleaned input state bound src=if state.heap.size<2^width then
      Function.update (RegisterWrite.cleared input) (some 22) (Encoding.encodeWords width (state.heap.toList++[state.reg src]))
    else Function.update (RegisterWrite.cleared input) none [false] := by
  by_cases valid : state.heap.size<2^width <;> simp only [cleaned,grown,valid,↓reduceIte] <;>
    funext port <;> by_cases h3 : port=some 3 <;> by_cases h27 : port=some 27 <;>
      by_cases h22 : port=some 22 <;> by_cases hn : port=none <;>
        simp_all [RegisterWrite.cleared,sourceLoaded,PrependBody.sourceLoaded,RegisterLoad.output,RegisterRead.addressed]

theorem cleaned_stored (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (src : Fin registers) (stored : NativeStore.Stored input state) : NativeStore.Stored (cleaned input state bound src) (updated state src) :=
  ((grown_stored input state bound src stored).update_other _ _ (some 3) [] (by decide)).update_other _ _ (some 27) [] (by decide)

theorem advance_output (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (src : Fin registers) (valid : state.heap.size<2^width) : PcAdvance.output (cleaned input state bound src) state.pc=output input state src := by
  rw [cleaned_shape]
  simp only [output,ite_eq_left valid]

theorem success_stored (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (src : Fin registers) (stored : NativeStore.Stored input state) (valid : state.heap.size<2^width) :
    NativeStore.Stored (output input state src) { state.advance with heap := state.heap.push (state.reg src) } := by
  have relation := cleaned_stored input state bound src stored
  simp only [updated,ite_eq_left valid] at relation
  have advanced := relation.advance (cleaned input state bound src) { state with heap := state.heap.push (state.reg src) }
  rw [advance_output input state bound src valid] at advanced
  exact advanced

theorem invalid_stored (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (src : Fin registers) (stored : NativeStore.Stored input state) (invalid : ¬state.heap.size<2^width) : NativeStore.Stored (output input state src) state := by
  simpa only [updated,ite_eq_right invalid,cleaned_shape,output] using cleaned_stored input state bound src stored

theorem status (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (src : Fin registers) (ready : Ready input state bound src) :
    (output input state src none).head?.isNone=decide (state.heap.size<2^width) := by
  by_cases valid : state.heap.size<2^width <;>
    simp [output,valid,PcAdvance.output,FieldGet.field,RegisterWrite.cleared,ready.clear none (by simp [FieldSet.work])]

theorem native_transition (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (src : Fin registers) (ready : Ready input state bound src) :
    LoadBody.observation width registers (output input state src)=Controller.Cost.step (.allocate src) state := by
  unfold LoadBody.observation
  rw [status input state bound src ready]
  by_cases valid : state.heap.size<2^width
  · simp only [valid,decide_true,↓reduceIte]
    rw [(success_stored input state bound src ready.stored valid).observation]
    simp [Controller.Cost.step,ready.running,valid]
  · simp [valid,Controller.Cost.step,ready.running]

theorem pc_ready (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (src : Fin registers) (ready : Ready input state bound src) (valid : state.heap.size<2^width) :
    PcAdvance.Ready (cleaned input state bound src) state.pc where
  stored := by simpa only [updated,ite_eq_left valid] using (cleaned_stored input state bound src ready.stored).widthStored
  pcStored := by simpa [updated,valid,FieldGet.field] using (cleaned_stored input state bound src ready.stored).pcStored
  indexEmpty := by simp [cleaned,RegisterWrite.cleared]
  valueEmpty := by simp [cleaned,RegisterWrite.cleared]
  clear := by
    intro port member
    have h3 : port ≠ (some 3 : Port) := by intro equal; subst port; simp [FieldSet.work] at member
    have h27 : port ≠ (some 27 : Port) := by intro equal; subst port; simp [FieldSet.work] at member
    have h22 : port ≠ (some 22 : Port) := by intro equal; subst port; simp [FieldSet.work] at member
    simpa only [cleaned,grown,ite_eq_left valid,RegisterWrite.cleared,Function.update_of_ne h3,Function.update_of_ne h27,Function.update_of_ne h22] using
      (allocation_ready input state bound src ready).clear port member

theorem execution (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (src : Fin registers) (ready : Ready input state bound src) :
    ∃ ticks peak, Execution program ⟨some program.main,input⟩ ⟨none,output input state src⟩ ticks peak ∧
      ticks ≤ 63*(FetchSetup.size input)^2+355*FetchSetup.size input+388 ∧
      peak ≤ 63*(FetchSetup.size input)^2+356*FetchSetup.size input+388 := by
  have validIndex : ([InstructionCodec.registerWord bound src][(0 : Fin 3).val]).val<(List.ofFn state.reg).length := by simp [InstructionCodec.registerWord]
  obtain ⟨sourceTicks,sourcePeak,sourcing,sourceBound,_⟩ := RegisterLoad.execution input [InstructionCodec.registerWord bound src] (List.ofFn state.reg) 0 (by simp) validIndex (ready.source input state bound src)
  have value : (List.ofFn state.reg)[(InstructionCodec.registerWord bound src).val]=state.reg src := by simp [InstructionCodec.registerWord,List.getElem_ofFn]
  change Execution (RegisterLoad.program 0) _ ⟨none,RegisterLoad.output input (InstructionCodec.registerWord bound src) ((List.ofFn state.reg)[(InstructionCodec.registerWord bound src).val])⟩ _ _ at sourcing
  rw [value] at sourcing
  obtain ⟨growTicks,growPeak,growing,growBound,_⟩ := DynamicFields.allocate_total (sourceLoaded input state bound src) state.heap.toList (state.reg src) (allocation_ready input state bound src ready)
  rw [allocation_output input state bound src ready] at growing
  change growTicks ≤ 4*(FetchSetup.size (sourceLoaded input state bound src))^2+41*FetchSetup.size (sourceLoaded input state bound src)+48 at growBound
  obtain ⟨cleanPeak,cleaning⟩ := LoadBody.cleanup_execution (grown input state bound src)
  have indexLength : (grown input state bound src (some 3)).length=width := by
    by_cases valid : state.heap.size<2^width <;> simp [grown,valid,sourceLoaded,PrependBody.sourceLoaded,RegisterLoad.output,RegisterRead.addressed,Encoding.bits_length]
  have valueLength : (grown input state bound src (some 27)).length=width := by
    by_cases valid : state.heap.size<2^width <;> simp [grown,valid,sourceLoaded,PrependBody.sourceLoaded,RegisterLoad.output,Encoding.bits_length]
  rw [indexLength,valueLength] at cleaning
  have growingClean := growing.link cleaning
  have cell : (input (some 8)).length ≤ FetchSetup.size input :=
    Finset.single_le_sum (f := fun port : Port => (input port).length) (fun _ _ => Nat.zero_le _) (Finset.mem_univ (some 8))
  have wBound : width ≤ FetchSetup.size input := by simpa only [ready.stored.widthStored,List.length_replicate] using cell
  have mass := RegisterLoad.size_output input (InstructionCodec.registerWord bound src) (state.reg src)
  have massBound : FetchSetup.size (sourceLoaded input state bound src) ≤ 3*FetchSetup.size input := by change FetchSetup.size (sourceLoaded input state bound src) ≤ _ at mass; omega
  have product := Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left massBound 2)
  have identity : 4*(3*FetchSetup.size input)^2+41*(3*FetchSetup.size input)+48=36*(FetchSetup.size input)^2+123*FetchSetup.size input+48 := by ring
  have growTime : growTicks ≤ 36*(FetchSetup.size input)^2+123*FetchSetup.size input+48 := by rw [← identity]; omega
  by_cases valid : state.heap.size<2^width
  · obtain ⟨pcTicks,pcPeak,advancing,pcBound,_⟩ := PcAdvance.execution (cleaned input state bound src) state.pc (pc_ready input state bound src ready valid)
    rw [advance_output input state bound src valid] at advancing
    have accepted : Option.isNone ((cleaned input state bound src none).head?)=true := by
      simp [cleaned_shape,valid,RegisterWrite.cleared,ready.clear none (by simp [FieldSet.work])]
    have trace := sourcing.link (GuardedLink.success none Option.isNone growingClean advancing accepted)
    have timeBound : sourceTicks+((growTicks+(width+width+4))+pcTicks) ≤ 63*(FetchSetup.size input)^2+355*FetchSetup.size input+388 := by omega
    have space := trace.peak_le
    exact ⟨_,_,trace,timeBound,by change _ ≤ FetchSetup.size input+_ at space; omega⟩
  · have rejected : Option.isNone ((cleaned input state bound src none).head?)=false := by simp [cleaned_shape,valid]
    have guardedTrace := GuardedLink.failure PcAdvance.program none Option.isNone growingClean rejected
    have same : RegisterWrite.cleared (grown input state bound src)=output input state src := by
      change cleaned input state bound src=output input state src
      simp only [cleaned_shape,output,ite_eq_right valid]
    rw [same] at guardedTrace
    have trace := sourcing.link guardedTrace
    have timeBound : sourceTicks+((growTicks+(width+width+4))+1) ≤ 63*(FetchSetup.size input)^2+355*FetchSetup.size input+388 := by omega
    have space := trace.peak_le
    exact ⟨_,_,trace,timeBound,by change _ ≤ FetchSetup.size input+_ at space; omega⟩

theorem alloc_card : Fintype.card AllocLabel=95 := by
  have original : Fintype.card (StateReader.LabelsOf HeapAllocate.program)=95 := by
    simp only [StateReader.LabelsOf,Fintype.card_sum,Fintype.card_option,Fintype.card_fin,Nat.reduceAdd]
  have same : Fintype.card AllocLabel=Fintype.card (StateReader.LabelsOf HeapAllocate.program) :=
    @Fintype.card_congr AllocLabel (StateReader.LabelsOf HeapAllocate.program) _ _ (Equiv.refl _)
  exact same.trans original

theorem guard_card : Fintype.card GuardLabel=499 := by
  have split : Fintype.card GuardLabel=(Fintype.card AllocLabel+(2+2))+(Fintype.card PcAdvance.Label+1) := by
    change Fintype.card ((AllocLabel ⊕ (Fin 2 ⊕ Fin 2)) ⊕ Option PcAdvance.Label)=_
    simp only [Fintype.card_sum,Fintype.card_option,Fintype.card_fin]
  rw [alloc_card,PcAdvance.canonical_card] at split
  exact split

theorem canonical_card : Fintype.card Label=769 := by
  have split : Fintype.card Label=Fintype.card CopyBody.SourceLabel+Fintype.card GuardLabel := by
    change Fintype.card (CopyBody.SourceLabel ⊕ GuardLabel)=_
    simp only [Fintype.card_sum]
  rw [CopyBody.source_card,guard_card] at split
  exact split

theorem resident : (∑ label, statementSize (tmStatement (program.code label))) ≤ 6921 := by
  have bound := finiteTM_resident program
  rw [canonical_card] at bound
  exact bound

end Controller.Complexity.AllocateBody
