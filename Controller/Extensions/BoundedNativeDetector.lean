module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Extensions.BoundedNativeCold
public import Controller.Cost.SharedMachineCapacity

@[expose] public section

/-! An unconditional fetched detector for bounded live conjunctions. The
canonical input contains the original DAG and singleton channel vector.
Empty DAGs and disabled drives reject by two fetched instructions; every
other run computes its reference table and executes the two search phases. -/
namespace Controller.Extensions.BoundedNativeDetector
open Controller Controller.Decoder Controller.Decoder.DAG Controller.Cost
open Controller.Native Controller.Native.SourceController Controller.Cost.NativeSourceExecution
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestInputStored
open Controller.Cost.SharedDetectorAssembly Controller.Cost.RawAdapterProgram

def rejectCode (width : Nat) : List (Instruction width 8) := [.constant 4 (word width 0),.halt]

theorem reject_execution (resident : Program width 8) (state : State width 8)
    (position : state.pc = word width 0) (running : state.halted = false) (fits : 2<2^width)
    (present : SharedRootRead.BlockAt resident 0 (rejectCode width)) :
    ∃ final, Execution resident state final 2 state.liveWords ∧ final.halted = true ∧
      final.reg 4 = word width 0 ∧ final.output = state.output := by
  obtain ⟨tagged,tag,tp,tv,th,ts,tout,tr,_⟩ :=
    SharedEvaluationReclaim.constant_execution resident 0 0 4 state position running (by omega)
      (by simpa [rejectCode] using present 0 (by simp [rejectCode]))
  let final := { tagged.advance with halted := true }
  have halt := SharedDetectorSteps.single resident tagged final 1 Instruction.halt tp (by omega)
    (by simpa [rejectCode] using present 1 (by simp [rejectCode])) (by simp [step,tr,final])
  have live : tagged.liveWords = state.liveWords := by simp only [State.liveWords,th,ts,tout]
  have lastLive : final.liveWords = tagged.liveWords := rfl
  exact ⟨final,by simpa only [live,lastLive,Nat.max_self] using tag.append halt,rfl,tv,tout⟩

def code (parameters : Parameters) (width k : Nat) : List (Instruction width 8) :=
  if parameters.drive then
    if nonempty : 0<parameters.decoder.nodeCount then
      BoundedNativeCold.code parameters width (UniformDAGOutputs.rowsOfGraph parameters.decoder)
        (parameters.decoder.roots.map Fin.val) k ⟨0,nonempty⟩
    else rejectCode width
  else rejectCode width

def program (parameters : Parameters) (width k : Nat) : Program width 8 := (code parameters width k).toArray

def width (parameters : Parameters) : Nat :=
  SharedMachineCapacity.wordWidth 0 parameters.decoder.countedSize (selectedSize parameters).total

theorem capacity (parameters : Parameters) :
    131072*(parameters.decoder.countedSize+(selectedSize parameters).total+1)<2^width parameters := by
  simpa only [Nat.zero_add,width] using
    SharedMachineCapacity.capacity 0 parameters.decoder.countedSize (selectedSize parameters).total

theorem code_bound (parameters : Parameters) (k : Nat) :
    (code parameters wordWidth k).length ≤
      3400*(parameters.decoder.countedSize+1)+68*(selectedSize parameters).total := by
  unfold code
  split
  · split
    · exact BoundedNativeCold.code_bound parameters _ _ k _
        (UniformDAGOutputs.rowsOfGraph_match parameters.decoder) rfl
    · simp only [rejectCode,List.length_cons,List.length_nil]; omega
  · simp only [rejectCode,List.length_cons,List.length_nil]; omega

set_option maxHeartbeats 1800000 in
theorem execution (parameters : Parameters) (raw : parameters.layout = .raw)
    (k : Nat) (andBound : parameters.decoder.liveAndCount ≤ k)
    (room : 131072*(parameters.decoder.countedSize+(selectedSize parameters).total+1)<2^wordWidth)
    (state : State wordWidth 8) (suffix : List (Word wordWidth))
    (empty : state.heap = #[])
    (input : state.stack = SharedDetectorCold.inputWords wordWidth (UniformDAGOutputs.rowsOfGraph parameters.decoder)
      (parameters.decoder.roots.map Fin.val) (assignmentOfSet {parameters.bridge.target}) ++ suffix)
    (position : state.pc = word wordWidth 0) (running : state.halted = false) :
    ∃ final ticks peak, Execution (program parameters wordWidth k) state final ticks peak ∧
      final.halted = true ∧ final.reg 4 = word wordWidth
        (if (SupportStream.detectSet parameters.decoder k parameters.buses parameters.bridge.target parameters.drive).isSome then 1 else 0) ∧
      ticks ≤ BoundedNativeCold.timeBound parameters k ∧
      peak ≤ state.liveWords+800*(parameters.decoder.countedSize+1)+3*(selectedSize parameters).total+12 ∧
      programWords (program parameters wordWidth k) ≤
        13600*(parameters.decoder.countedSize+1)+272*(selectedSize parameters).total ∧
      ((SupportStream.detectSet parameters.decoder k parameters.buses parameters.bridge.target parameters.drive).isSome = true →
        Certificate.ModelCheck.check (formula parameters)
          (NativeRealizedChecked.decodeOutput final.output (compile parameters).toState.count) = true) ∧
      (SupportStream.detectSet parameters.decoder k parameters.buses parameters.bridge.target parameters.drive = none →
        final.output = state.output) := by
  have residentWords : programWords (program parameters wordWidth k) ≤
      13600*(parameters.decoder.countedSize+1)+272*(selectedSize parameters).total := by
    have bound := Nat.mul_le_mul_left 4 (code_bound (wordWidth := wordWidth) parameters k)
    simpa only [program,programWords,List.size_toArray,Nat.mul_add,← Nat.mul_assoc,Nat.reduceMul] using bound
  by_cases drive : parameters.drive = true
  · by_cases nonempty : 0<parameters.decoder.nodeCount
    · obtain ⟨final,ticks,peak,trace,halted,decision,time,space,words,checked,unchanged⟩ :=
        BoundedNativeCold.execution parameters raw drive _ _ (UniformDAGOutputs.rowsOfGraph_match parameters.decoder)
          (UniformDAGOutputs.rowsOfGraph_heads parameters.decoder) rfl k andBound ⟨0,nonempty⟩ room
          state suffix empty input position running
      exact ⟨final,ticks,peak,by simpa only [program,code,drive,ite_true,dite_eq_left nonempty] using trace,
        halted,decision,time,space,residentWords,checked,unchanged⟩
    · have roots : parameters.decoder.roots = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro root member
        have bound := root.isLt
        omega
      have rejected : SupportStream.detectSet parameters.decoder k parameters.buses parameters.bridge.target parameters.drive = none := by
        simp [SupportStream.detectSet,drive,roots,firstSuccess]
      have present : SharedRootRead.BlockAt (program parameters wordWidth k) 0 (rejectCode wordWidth) := by
        simp only [program,code,drive,ite_true,dite_eq_right nonempty]
        intro offset below
        simp only [Nat.zero_add,List.getElem?_toArray]
      obtain ⟨final,trace,halted,decision,output⟩ := reject_execution _ state position running (by omega) present
      refine ⟨final,2,state.liveWords,trace,halted,by simpa only [rejected,Option.isSome_none,Bool.false_eq_true,ite_false] using decision,
        ?_,by omega,residentWords,by simp [rejected],by intro _; exact output⟩
      unfold BoundedNativeCold.timeBound
      omega
  · have rejected : SupportStream.detectSet parameters.decoder k parameters.buses parameters.bridge.target parameters.drive = none := by
      simp only [SupportStream.detectSet,drive,Bool.false_eq_true,ite_false]
    have present : SharedRootRead.BlockAt (program parameters wordWidth k) 0 (rejectCode wordWidth) := by
      simp only [program,code,drive,Bool.false_eq_true,ite_false]
      intro offset below
      simp only [Nat.zero_add,List.getElem?_toArray]
    obtain ⟨final,trace,halted,decision,output⟩ := reject_execution _ state position running (by omega) present
    refine ⟨final,2,state.liveWords,trace,halted,by simpa only [rejected,Option.isSome_none,Bool.false_eq_true,ite_false] using decision,
      ?_,by omega,residentWords,by simp [rejected],by intro _; exact output⟩
    unfold BoundedNativeCold.timeBound
    omega

def Detects (parameters : Parameters) : Prop :=
  parameters.drive = true ∧ ∃ root ∈ parameters.decoder.roots, ∃ K,
    Admissible parameters.buses parameters.bridge.target K ∧
    parameters.decoder.eval (assignmentOfSet K) root ≠
      parameters.decoder.eval (assignmentOfSet {parameters.bridge.target}) root

theorem acceptance_iff (parameters : Parameters) (k : Nat) (andBound : parameters.decoder.liveAndCount ≤ k)
    (fits : 1<2^wordWidth) (final : State wordWidth 8)
    (decision : final.reg 4 = word wordWidth
      (if (SupportStream.detectSet parameters.decoder k parameters.buses parameters.bridge.target parameters.drive).isSome then 1 else 0)) :
    final.reg 4 = word wordWidth 1 ↔ Detects parameters := by
  have semantic := SupportStream.detectSet_none_iff parameters.decoder k andBound parameters.buses parameters.bridge.target parameters.drive
  classical
  rw [decision]
  cases answer : SupportStream.detectSet parameters.decoder k parameters.buses parameters.bridge.target parameters.drive with
  | none =>
    have none : ¬Detects parameters := semantic.mp answer
    simp only [answer,Option.isSome_none,Bool.false_eq_true,ite_false]
    constructor
    · intro equal
      have values := congrArg Fin.val equal
      simp only [word,Fin.val_mk,Nat.zero_mod,Nat.mod_eq_of_lt fits] at values
      omega
    · exact False.elim ∘ none
  | some K =>
    have detects : Detects parameters := by
      by_contra absent
      have impossible := semantic.mpr absent
      rw [answer] at impossible
      contradiction
    simp only [answer,Option.isSome_some,ite_true,detects]

end Controller.Extensions.BoundedNativeDetector
