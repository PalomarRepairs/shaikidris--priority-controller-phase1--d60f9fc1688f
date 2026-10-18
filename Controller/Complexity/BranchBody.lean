module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.PopBody
public import Controller.Complexity.WordZero
public import Controller.Complexity.PcWrite

public import Mathlib.Tactic.Ring

@[expose] public section

/-! The actual old register word controls two guarded paths. A zero source
writes the fetched absolute target; a nonzero source clears the internal
marker and advances the old PC. Both paths preserve all other native fields. -/
namespace Controller.Complexity.BranchBody
open StackMachine WordReader
open scoped BigOperators

structure Ready (input : Port → List Bool) (state : Controller.Cost.State width registers)
    (bound : registers ≤ 2^width) (src : Fin registers) (target : Controller.Cost.Word width) : Prop where
  stored : NativeStore.Stored input state
  running : state.halted=false
  payload : input (some 11)=Encoding.wordList width [InstructionCodec.registerWord bound src,target]
  clear : ∀ port ∈ FieldSet.work, input port=[]

def base (input : Port → List Bool) := RegisterWrite.cleared input
def sourceLoaded := @PrependBody.sourceLoaded
def zeroed (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width) (src : Fin registers) :=
  Function.update (Function.update (sourceLoaded input state bound src) (some 27) []) none (if (state.reg src).val=0 then [] else [false])
def marked (input : Port → List Bool) (state : Controller.Cost.State width registers) (src : Fin registers) :=
  if (state.reg src).val=0 then base input else Function.update (base input) none [false]
def targetLoaded (input : Port → List Bool) (target : Controller.Cost.Word width) := OperandLoad.output (base input) true target
def targetOutput (input : Port → List Bool) (target : Controller.Cost.Word width) := Function.update (base input) (some 25) (Encoding.encodeWords width [target])
def output (input : Port → List Bool) (state : Controller.Cost.State width registers) (src : Fin registers) (target : Controller.Cost.Word width) :=
  if (state.reg src).val=0 then targetOutput input target else PcAdvance.output (base input) state.pc

def PrepareLabel : Type := (CopyBody.SourceLabel ⊕ Fin 4) ⊕ (Fin 2 ⊕ Fin 2)
instance prepareFintype : Fintype PrepareLabel := inferInstanceAs (Fintype ((CopyBody.SourceLabel ⊕ Fin 4) ⊕ (Fin 2 ⊕ Fin 2)))
def prepareProgram : Program (Fin 31) PrepareLabel := link (link PrependBody.sourceProgram WordZero.program) LoadBody.cleanup
def TargetLabel : Type := ConstantBody.OperandLabel ⊕ (PcAdvance.SetterLabel ⊕ Fin 2)
instance targetFintype : Fintype TargetLabel := inferInstanceAs (Fintype (ConstantBody.OperandLabel ⊕ (PcAdvance.SetterLabel ⊕ Fin 2)))
def targetOperand : Program (Fin 31) ConstantBody.OperandLabel := OperandLoad.program 1 true
def targetProgram : Program (Fin 31) TargetLabel := link targetOperand PcWrite.program
def FallLabel : Type := Fin 2 ⊕ PcAdvance.Label
instance fallFintype : Fintype FallLabel := inferInstanceAs (Fintype (Fin 2 ⊕ PcAdvance.Label))
def fallProgram : Program (Fin 31) FallLabel := link (StackClear.program (none : Port)) PcAdvance.program
def ZeroLabel : Type := PrepareLabel ⊕ Option TargetLabel
instance zeroFintype : Fintype ZeroLabel := inferInstanceAs (Fintype (PrepareLabel ⊕ Option TargetLabel))
def zeroProgram : Program (Fin 31) ZeroLabel := GuardedLink.program prepareProgram targetProgram none Option.isNone
def Label : Type := ZeroLabel ⊕ Option FallLabel
instance labelFintype : Fintype Label := inferInstanceAs (Fintype (ZeroLabel ⊕ Option FallLabel))
def program : Program (Fin 31) Label := GuardedLink.program zeroProgram fallProgram none Option.isSome

theorem base_stored (input : Port → List Bool) (state : Controller.Cost.State width registers) (stored : NativeStore.Stored input state) :
    NativeStore.Stored (base input) state := PopBody.prepared_stored input state stored

theorem base_clear (input : Port → List Bool) (clean : ∀ port ∈ FieldSet.work, input port=[]) :
    ∀ port ∈ FieldSet.work, base input port=[] := PopBody.prepared_clear input clean

theorem base_size (input : Port → List Bool) : FetchSetup.size (base input) ≤ FetchSetup.size input := by
  have a := OperandLoad.update_size_le input (some 3) []
  have b := OperandLoad.update_size_le (Function.update input (some 3) []) (some 27) []
  simp only [List.length_nil,Nat.add_zero] at a b
  change FetchSetup.size (base input) ≤ _ at b
  omega

theorem source_ready (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (src : Fin registers) (target : Controller.Cost.Word width) (ready : Ready input state bound src target) :
    RegisterRead.Ready input [InstructionCodec.registerWord bound src,target] (List.ofFn state.reg) where
  payload := ready.payload
  stored := ready.stored.widthStored
  registersStored := by simpa [FieldGet.field] using ready.stored.registersStored
  clear := ready.clear

theorem prepare_output (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (src : Fin registers) (target : Controller.Cost.Word width) (ready : Ready input state bound src target) :
    RegisterWrite.cleared (zeroed input state bound src)=marked input state src := by
  have clean := ready.clear none (by simp [FieldSet.work])
  by_cases zero : (state.reg src).val=0 <;> simp only [zeroed,marked,zero,↓reduceIte] <;>
    funext port <;> by_cases hn : port=none <;> by_cases h3 : port=some 3 <;> by_cases h27 : port=some 27 <;>
      simp_all [base,RegisterWrite.cleared,sourceLoaded,PrependBody.sourceLoaded,RegisterLoad.output,RegisterRead.addressed]

theorem prepare_execution (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (src : Fin registers) (target : Controller.Cost.Word width) (ready : Ready input state bound src target) :
    ∃ ticks peak, Execution prepareProgram ⟨some prepareProgram.main,input⟩ ⟨none,marked input state src⟩ ticks peak ∧
      ticks ≤ 27*(FetchSetup.size input)^2+140*FetchSetup.size input+128 := by
  have valid : ([InstructionCodec.registerWord bound src,target][(0 : Fin 3).val]).val<(List.ofFn state.reg).length := by simp [InstructionCodec.registerWord]
  obtain ⟨sourceTicks,sourcePeak,sourcing,sourceBound,_⟩ := RegisterLoad.execution input [InstructionCodec.registerWord bound src,target] (List.ofFn state.reg) 0 (by simp) valid (source_ready input state bound src target ready)
  have value : (List.ofFn state.reg)[(InstructionCodec.registerWord bound src).val]=state.reg src := by simp [InstructionCodec.registerWord,List.getElem_ofFn]
  change Execution (RegisterLoad.program 0) _ ⟨none,RegisterLoad.output input (InstructionCodec.registerWord bound src) ((List.ofFn state.reg)[(InstructionCodec.registerWord bound src).val])⟩ _ _ at sourcing
  rw [value] at sourcing
  obtain ⟨zeroTicks,zeroPeak,testing,zeroBound,_⟩ := WordZero.encoded_execution (sourceLoaded input state bound src) (state.reg src)
    (by simp [sourceLoaded,PrependBody.sourceLoaded,RegisterLoad.output])
    (by simpa [sourceLoaded,PrependBody.sourceLoaded,RegisterLoad.output,RegisterRead.addressed] using ready.clear none (by simp [FieldSet.work]))
  obtain ⟨cleanPeak,cleaning⟩ := LoadBody.cleanup_execution (zeroed input state bound src)
  have indexLength : (zeroed input state bound src (some 3)).length=width := by simp [zeroed,sourceLoaded,PrependBody.sourceLoaded,RegisterLoad.output,RegisterRead.addressed,Encoding.bits_length]
  have valueEmpty : zeroed input state bound src (some 27)=[] := by simp [zeroed]
  rw [indexLength,valueEmpty,List.length_nil,Nat.add_zero,prepare_output input state bound src target ready] at cleaning
  have trace := (sourcing.link testing).link cleaning
  have cell : (input (some 8)).length ≤ FetchSetup.size input :=
    Finset.single_le_sum (f := fun port : Port => (input port).length) (fun _ _ => Nat.zero_le _) (Finset.mem_univ (some 8))
  have wBound : width ≤ FetchSetup.size input := by simpa only [ready.stored.widthStored,List.length_replicate] using cell
  exact ⟨_,_,trace,by omega⟩

theorem target_ready (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (src : Fin registers) (target : Controller.Cost.Word width) (ready : Ready input state bound src target) :
    OperandLoad.Ready (base input) [InstructionCodec.registerWord bound src,target] where
  payload := by simpa [base,RegisterWrite.cleared] using ready.payload
  stored := (base_stored input state ready.stored).widthStored
  clear := base_clear input ready.clear

theorem target_pc_ready (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (src : Fin registers) (target : Controller.Cost.Word width) (ready : Ready input state bound src target) :
    PcWrite.Ready (targetLoaded input target) state.pc target where
  widthStored := (OperandLoad.stored_output (base input) true target state (base_stored input state ready.stored)).widthStored
  pcStored := (OperandLoad.stored_output (base input) true target state (base_stored input state ready.stored)).pcStored
  indexEmpty := by simp [targetLoaded,OperandLoad.output,OperandLoad.destination,base,RegisterWrite.cleared]
  valueStored := by simp [targetLoaded,OperandLoad.output,OperandLoad.destination]
  clear := OperandLoad.clear_output (base input) true target (base_clear input ready.clear)

theorem target_output (input : Port → List Bool) (target : Controller.Cost.Word width) : PcWrite.output (targetLoaded input target) target=targetOutput input target := by
  funext port
  by_cases hp : port=some 25 <;> by_cases hv : port=some 27 <;>
    simp_all [PcWrite.output,targetLoaded,OperandLoad.output,OperandLoad.destination,targetOutput,base,RegisterWrite.cleared]

theorem target_execution (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (src : Fin registers) (target : Controller.Cost.Word width) (ready : Ready input state bound src target) :
    ∃ ticks peak, Execution targetProgram ⟨some targetProgram.main,base input⟩ ⟨none,targetOutput input target⟩ ticks peak ∧
      ticks ≤ 124*(FetchSetup.size input)^2+233*FetchSetup.size input+135 := by
  obtain ⟨operandTicks,operandPeak,loading,operandBound,_⟩ := OperandLoad.execution (base input) [InstructionCodec.registerWord bound src,target] 1 true (by simp) (target_ready input state bound src target ready)
  obtain ⟨writeTicks,writePeak,writing,writeBound,_⟩ := PcWrite.execution (targetLoaded input target) state.pc target (target_pc_ready input state bound src target ready)
  rw [target_output] at writing
  have trace := loading.link writing
  have baseBound := base_size input
  have cell : (input (some 8)).length ≤ FetchSetup.size input :=
    Finset.single_le_sum (f := fun port : Port => (input port).length) (fun _ _ => Nat.zero_le _) (Finset.mem_univ (some 8))
  have wBound : width ≤ FetchSetup.size input := by simpa only [ready.stored.widthStored,List.length_replicate] using cell
  have mass := OperandLoad.update_size_le (base input) (some 27) (Encoding.bits width target.val)
  simp only [Encoding.bits_length] at mass
  have massBound : FetchSetup.size (targetLoaded input target) ≤ 2*FetchSetup.size input := by change FetchSetup.size (targetLoaded input target) ≤ _ at mass; omega
  have product := Nat.mul_le_mul_left 31 (Nat.pow_le_pow_left massBound 2)
  have identity : 31*(2*FetchSetup.size input)^2+89*(2*FetchSetup.size input)+76=124*(FetchSetup.size input)^2+178*FetchSetup.size input+76 := by ring
  have writeTime : writeTicks ≤ 124*(FetchSetup.size input)^2+178*FetchSetup.size input+76 := by rw [← identity]; omega
  exact ⟨_,_,trace,by omega⟩

theorem fall_pc_ready (input : Port → List Bool) (state : Controller.Cost.State width registers) (stored : NativeStore.Stored input state)
    (clean : ∀ port ∈ FieldSet.work, input port=[]) : PcAdvance.Ready (base input) state.pc where
  stored := (base_stored input state stored).widthStored
  pcStored := by simpa [FieldGet.field] using (base_stored input state stored).pcStored
  indexEmpty := by simp [base,RegisterWrite.cleared]
  valueEmpty := by simp [base,RegisterWrite.cleared]
  clear := base_clear input clean

theorem fall_execution (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (src : Fin registers) (target : Controller.Cost.Word width) (ready : Ready input state bound src target) :
    ∃ ticks peak, Execution fallProgram ⟨some fallProgram.main,Function.update (base input) none [false]⟩
      ⟨none,PcAdvance.output (base input) state.pc⟩ ticks peak ∧ ticks ≤ 92*width+218 := by
  obtain ⟨clearPeak,clearing⟩ := StackClear.ready_execution (Function.update (base input) none [false]) none
  simp only [Function.update_self,List.length_cons,List.length_nil,Nat.reduceAdd] at clearing
  have restored : Function.update (Function.update (base input) none [false]) none []=base input := by
    funext port
    have status := ready.clear none (by simp [FieldSet.work])
    by_cases hn : port=none <;> simp_all [base,RegisterWrite.cleared]
  rw [restored] at clearing
  obtain ⟨pcTicks,pcPeak,advancing,pcBound,_⟩ := PcAdvance.execution (base input) state.pc (fall_pc_ready input state ready.stored ready.clear)
  exact ⟨_,_,clearing.link advancing,by omega⟩

theorem taken_stored (input : Port → List Bool) (state : Controller.Cost.State width registers) (target : Controller.Cost.Word width)
    (stored : NativeStore.Stored input state) : NativeStore.Stored (targetOutput input target) { state with pc := target } := by
  have relation := base_stored input state stored
  rcases relation with ⟨hw,hr,hreg,hh,hs,ho,hpc,hhalt⟩
  constructor <;> simp_all [targetOutput]

theorem native_transition (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (src : Fin registers) (target : Controller.Cost.Word width) (ready : Ready input state bound src target) :
    StateNative.observe width registers (output input state src target)=Controller.Cost.step (.branchZero src target) state := by
  by_cases zero : (state.reg src).val=0
  · rw [output,ite_eq_left zero,(taken_stored input state target ready.stored).observation]
    simp [Controller.Cost.step,ready.running,zero,Controller.Cost.State.advance]
  · rw [output,ite_eq_right zero,((base_stored input state ready.stored).advance (base input) state).observation]
    simp [Controller.Cost.step,ready.running,zero]

theorem execution (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (src : Fin registers) (target : Controller.Cost.Word width) (ready : Ready input state bound src target) :
    ∃ ticks peak, Execution program ⟨some program.main,input⟩ ⟨none,output input state src target⟩ ticks peak ∧
      ticks ≤ 151*(FetchSetup.size input)^2+373*FetchSetup.size input+347 ∧
      peak ≤ 151*(FetchSetup.size input)^2+374*FetchSetup.size input+347 := by
  obtain ⟨prepareTicks,preparePeak,preparing,prepareBound⟩ := prepare_execution input state bound src target ready
  by_cases zero : (state.reg src).val=0
  · simp only [marked,ite_eq_left zero] at preparing
    obtain ⟨targetTicks,targetPeak,targeting,targetBound⟩ := target_execution input state bound src target ready
    have accepted : Option.isNone ((base input none).head?)=true := by simp [base,RegisterWrite.cleared,ready.clear none (by simp [FieldSet.work])]
    have takenTrace := GuardedLink.success none Option.isNone preparing targeting accepted
    have rejected : Option.isSome ((targetOutput input target none).head?)=false := by simp [targetOutput,base,RegisterWrite.cleared,ready.clear none (by simp [FieldSet.work])]
    have trace := GuardedLink.failure fallProgram none Option.isSome takenTrace rejected
    rw [show targetOutput input target=output input state src target by simp only [output,ite_eq_left zero]] at trace
    have timeBound : (prepareTicks+targetTicks)+1 ≤ 151*(FetchSetup.size input)^2+373*FetchSetup.size input+347 := by omega
    have space := trace.peak_le
    exact ⟨_,_,trace,timeBound,by change _ ≤ FetchSetup.size input+_ at space; omega⟩
  · simp only [marked,ite_eq_right zero] at preparing
    have rejected : Option.isNone (((Function.update (base input) none [false]) none).head?)=false := by simp
    have skipped := GuardedLink.failure targetProgram none Option.isNone preparing rejected
    obtain ⟨fallTicks,fallPeak,falling,fallBound⟩ := fall_execution input state bound src target ready
    have accepted : Option.isSome (((Function.update (base input) none [false]) none).head?)=true := by simp
    have trace := GuardedLink.success none Option.isSome skipped falling accepted
    rw [show PcAdvance.output (base input) state.pc=output input state src target by simp only [output,ite_eq_right zero]] at trace
    have cell : (input (some 8)).length ≤ FetchSetup.size input :=
      Finset.single_le_sum (f := fun port : Port => (input port).length) (fun _ _ => Nat.zero_le _) (Finset.mem_univ (some 8))
    have wBound : width ≤ FetchSetup.size input := by simpa only [ready.stored.widthStored,List.length_replicate] using cell
    have timeBound : (prepareTicks+1)+fallTicks ≤ 151*(FetchSetup.size input)^2+373*FetchSetup.size input+347 := by omega
    have space := trace.peak_le
    exact ⟨_,_,trace,timeBound,by change _ ≤ FetchSetup.size input+_ at space; omega⟩

theorem prepare_card : Fintype.card PrepareLabel=278 := by
  have split : Fintype.card PrepareLabel=(Fintype.card CopyBody.SourceLabel+4)+(2+2) := by
    change Fintype.card ((CopyBody.SourceLabel ⊕ Fin 4) ⊕ (Fin 2 ⊕ Fin 2))=_
    simp only [Fintype.card_sum,Fintype.card_fin]
  rw [CopyBody.source_card] at split
  exact split

theorem target_card : Fintype.card TargetLabel=296 := by
  have split : Fintype.card TargetLabel=Fintype.card ConstantBody.OperandLabel+(Fintype.card PcAdvance.SetterLabel+2) := by
    change Fintype.card (ConstantBody.OperandLabel ⊕ (PcAdvance.SetterLabel ⊕ Fin 2))=_
    simp only [Fintype.card_sum,Fintype.card_fin]
  rw [ConstantBody.operand_card,PcAdvance.setter_card] at split
  exact split

theorem fall_card : Fintype.card FallLabel=401 := by
  have split : Fintype.card FallLabel=2+Fintype.card PcAdvance.Label := by
    change Fintype.card (Fin 2 ⊕ PcAdvance.Label)=_
    simp only [Fintype.card_sum,Fintype.card_fin]
  rw [PcAdvance.canonical_card] at split
  exact split

theorem zero_card : Fintype.card ZeroLabel=575 := by
  have split : Fintype.card ZeroLabel=Fintype.card PrepareLabel+(Fintype.card TargetLabel+1) := by
    change Fintype.card (PrepareLabel ⊕ Option TargetLabel)=_
    simp only [Fintype.card_sum,Fintype.card_option]
  rw [prepare_card,target_card] at split
  exact split

theorem canonical_card : Fintype.card Label=977 := by
  have split : Fintype.card Label=Fintype.card ZeroLabel+(Fintype.card FallLabel+1) := by
    change Fintype.card (ZeroLabel ⊕ Option FallLabel)=_
    simp only [Fintype.card_sum,Fintype.card_option]
  rw [zero_card,fall_card] at split
  exact split

theorem resident : (∑ label, statementSize (tmStatement (program.code label))) ≤ 8793 := by
  have bound := finiteTM_resident program
  rw [canonical_card] at bound
  exact bound

end Controller.Complexity.BranchBody
