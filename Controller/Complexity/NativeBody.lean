module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.BodyTable

@[expose] public section

/-! The common fetched-state contract supplies the literal premises of every
native body. The selected family executes the actual matching body, with one
uniform original-live budget and exact status-filtered native semantics. -/
namespace Controller.Complexity.NativeBody
open StackMachine WordReader

structure Ready (input : Port → List Bool) (state : Controller.Cost.State width registers)
    (bound : registers ≤ 2^width) (instruction : Controller.Cost.Instruction width registers) : Prop where
  stored : NativeStore.Stored input state
  running : state.halted=false
  payload : input (some 11)=Encoding.wordList width (InstructionCodec.fields bound instruction).2
  indexStored : input (some 3)=Encoding.bits width state.pc.val
  valueEmpty : input (some 27)=[]
  bufferEmpty : input (some 28)=[]
  resultEmpty : input (some 29)=[]
  clear : ∀ port ∈ FieldSet.work, input port=[]

def Condition (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width) :
    Controller.Cost.Instruction width registers → Prop
  | .constant dst value => ConstantBody.Ready input state bound dst value
  | .copy dst src => CopyBody.Ready input state bound dst src
  | .add dst left right => ArithmeticBody.Ready input state bound dst left right
  | .xor dst left right => ArithmeticBody.Ready input state bound dst left right
  | .load dst address => LoadBody.Ready input state bound dst address
  | .store address src => StoreBody.Ready input state bound address src
  | .allocate src => AllocateBody.Ready input state bound src
  | .release => ReleaseBody.Ready input state
  | .push src => PrependBody.Ready input state bound src
  | .pop dst => PopBody.Ready input state bound dst
  | .emit src => PrependBody.Ready input state bound src
  | .branchZero src target => BranchBody.Ready input state bound src target
  | .halt => HaltBody.Ready input state

def output (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width) :
    Controller.Cost.Instruction width registers → Port → List Bool
  | .constant dst value => ConstantBody.output input state bound dst value
  | .copy dst src => CopyBody.output input state bound dst src
  | .add dst left right => ArithmeticBody.output input false state bound dst left right
  | .xor dst left right => ArithmeticBody.output input true state bound dst left right
  | .load dst address => LoadBody.output input state dst address
  | .store address src => StoreBody.output input state address src
  | .allocate src => AllocateBody.output input state src
  | .release => ReleaseBody.output input state
  | .push src => PrependBody.output false input state src
  | .pop dst => PopBody.output input state dst
  | .emit src => PrependBody.output true input state src
  | .branchZero src target => BranchBody.output input state src target
  | .halt => HaltBody.output input state

theorem ready (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (instruction : Controller.Cost.Instruction width registers) (r : Ready input state bound instruction) : Condition input state bound instruction := by
  cases instruction with
  | constant dst value =>
    exact ({ stored := r.stored, running := r.running, clear := r.clear, payload := by simpa [InstructionCodec.fields] using r.payload } : ConstantBody.Ready input state bound dst value)
  | copy dst src =>
    exact ({ stored := r.stored, running := r.running, clear := r.clear, payload := by simpa [InstructionCodec.fields] using r.payload } : CopyBody.Ready input state bound dst src)
  | add dst left right =>
    exact ({ stored := r.stored, running := r.running, clear := r.clear, payload := by simpa [InstructionCodec.fields] using r.payload, bufferEmpty := r.bufferEmpty, resultEmpty := r.resultEmpty } : ArithmeticBody.Ready input state bound dst left right)
  | xor dst left right =>
    exact ({ stored := r.stored, running := r.running, clear := r.clear, payload := by simpa [InstructionCodec.fields] using r.payload, bufferEmpty := r.bufferEmpty, resultEmpty := r.resultEmpty } : ArithmeticBody.Ready input state bound dst left right)
  | load dst address =>
    exact ({ stored := r.stored, running := r.running, clear := r.clear, payload := by simpa [InstructionCodec.fields] using r.payload } : LoadBody.Ready input state bound dst address)
  | store address src =>
    exact ({ stored := r.stored, running := r.running, clear := r.clear, payload := by simpa [InstructionCodec.fields] using r.payload, bufferEmpty := r.bufferEmpty } : StoreBody.Ready input state bound address src)
  | allocate src =>
    exact ({ stored := r.stored, running := r.running, clear := r.clear, payload := by simpa [InstructionCodec.fields] using r.payload } : AllocateBody.Ready input state bound src)
  | release =>
    exact ({ stored := r.stored, running := r.running, clear := r.clear } : ReleaseBody.Ready input state)
  | push src =>
    exact ({ stored := r.stored, running := r.running, clear := r.clear, payload := by simpa [InstructionCodec.fields] using r.payload } : PrependBody.Ready input state bound src)
  | pop dst =>
    exact ({ stored := r.stored, running := r.running, clear := r.clear, payload := by simpa [InstructionCodec.fields] using r.payload } : PopBody.Ready input state bound dst)
  | emit src =>
    exact ({ stored := r.stored, running := r.running, clear := r.clear, payload := by simpa [InstructionCodec.fields] using r.payload } : PrependBody.Ready input state bound src)
  | branchZero src target =>
    exact ({ stored := r.stored, running := r.running, clear := r.clear, payload := by simpa [InstructionCodec.fields] using r.payload } : BranchBody.Ready input state bound src target)
  | halt =>
    exact ({ stored := r.stored, running := r.running, clear := r.clear, indexStored := r.indexStored, valueEmpty := r.valueEmpty } : HaltBody.Ready input state)

theorem execution (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (instruction : Controller.Cost.Instruction width registers) (r : Ready input state bound instruction) :
    ∃ ticks peak, Execution (BodyTable.family (BodyTable.nativeTag bound instruction))
      ⟨some (BodyTable.family (BodyTable.nativeTag bound instruction)).main,input⟩ ⟨none,output input state bound instruction⟩ ticks peak ∧
      ticks ≤ 3000*(FetchSetup.size input)^2+2500*FetchSetup.size input+1000 := by
  have caseReady := ready input state bound instruction r
  have cell : (input (some 8)).length ≤ FetchSetup.size input :=
    Finset.single_le_sum (f := fun port : Port => (input port).length) (fun _ _ => Nat.zero_le _) (Finset.mem_univ (some 8))
  have wBound : width ≤ FetchSetup.size input := by simpa only [r.stored.widthStored,List.length_replicate] using cell
  cases instruction with
  | constant dst value =>
    obtain ⟨ticks,peak,trace,time,_⟩ := ConstantBody.execution input state bound dst value caseReady
    exact ⟨ticks,peak,trace,by omega⟩
  | copy dst src =>
    obtain ⟨ticks,peak,trace,time,_⟩ := CopyBody.execution input state bound dst src caseReady
    exact ⟨ticks,peak,trace,by omega⟩
  | add dst left right =>
    obtain ⟨ticks,peak,trace,time,_⟩ := ArithmeticBody.execution input false state bound dst left right caseReady
    exact ⟨ticks,peak,trace,by omega⟩
  | xor dst left right =>
    obtain ⟨ticks,peak,trace,time,_⟩ := ArithmeticBody.execution input true state bound dst left right caseReady
    exact ⟨ticks,peak,trace,by omega⟩
  | load dst address =>
    obtain ⟨ticks,peak,trace,time,_⟩ := LoadBody.execution input state bound dst address caseReady
    exact ⟨ticks,peak,trace,by omega⟩
  | store address src =>
    obtain ⟨ticks,peak,trace,time,_⟩ := StoreBody.execution input state bound address src caseReady
    exact ⟨ticks,peak,trace,by omega⟩
  | allocate src =>
    obtain ⟨ticks,peak,trace,time,_⟩ := AllocateBody.execution input state bound src caseReady
    exact ⟨ticks,peak,trace,by omega⟩
  | release =>
    obtain ⟨ticks,peak,trace,time,_⟩ := ReleaseBody.execution input state caseReady
    exact ⟨ticks,peak,trace,by omega⟩
  | push src =>
    obtain ⟨ticks,peak,trace,time,_⟩ := PrependBody.execution false input state bound src caseReady
    exact ⟨ticks,peak,trace,by omega⟩
  | pop dst =>
    obtain ⟨ticks,peak,trace,time,_⟩ := PopBody.execution input state bound dst caseReady
    exact ⟨ticks,peak,trace,by omega⟩
  | emit src =>
    obtain ⟨ticks,peak,trace,time,_⟩ := PrependBody.execution true input state bound src caseReady
    exact ⟨ticks,peak,trace,by omega⟩
  | branchZero src target =>
    obtain ⟨ticks,peak,trace,time,_⟩ := BranchBody.execution input state bound src target caseReady
    exact ⟨ticks,peak,trace,by omega⟩
  | halt =>
    obtain ⟨ticks,peak,trace,time,_⟩ := HaltBody.execution input state caseReady
    exact ⟨ticks,peak,trace,by omega⟩

theorem filtered_of_clear (width registers : Nat) (input : Port → List Bool) (clean : input none=[]) :
    LoadBody.observation width registers input=StateNative.observe width registers input := by simp [LoadBody.observation,clean]

theorem semantics (input : Port → List Bool) (state : Controller.Cost.State width registers)
    (bound : registers ≤ 2^width) (instruction : Controller.Cost.Instruction width registers)
    (r : Ready input state bound instruction) :
    LoadBody.observation width registers (output input state bound instruction)=Controller.Cost.step instruction state := by
  have caseReady := ready input state bound instruction r
  have clean := r.clear none (by simp [FieldSet.work])
  cases instruction with
  | constant dst value =>
    have flag := (ConstantBody.Ready.pc input state bound dst value caseReady).clear none (by simp [FieldSet.work])
    have outClear : output input state bound (.constant dst value) none=[] := by
      simpa [output,ConstantBody.output,PcAdvance.output,FieldGet.field] using flag
    rw [filtered_of_clear _ _ _ outClear]
    exact ConstantBody.native_transition input state bound dst value caseReady
  | copy dst src =>
    have flag := (CopyBody.Ready.commit input state bound dst src caseReady).clear none (by simp [FieldSet.work])
    have outClear : output input state bound (.copy dst src) none=[] := by
      simpa [output,CopyBody.output,RegisterWrite.completeOutput,RegisterWrite.output,RegisterWrite.cleared,PcAdvance.output,FieldGet.field] using flag
    rw [filtered_of_clear _ _ _ outClear]
    exact CopyBody.native_transition input state bound dst src caseReady
  | add dst left right =>
    have shape := ArithmeticBody.output_shape input false state bound dst left right caseReady
    have outClear : output input state bound (.add dst left right) none=[] := by
      change ArithmeticBody.output input false state bound dst left right none=[]
      rw [shape]
      simpa [RegisterWrite.completeOutput,RegisterWrite.output,RegisterWrite.cleared,PcAdvance.output,FieldGet.field] using clean
    rw [filtered_of_clear _ _ _ outClear]
    exact ArithmeticBody.native_transition input false state bound dst left right caseReady
  | xor dst left right =>
    have shape := ArithmeticBody.output_shape input true state bound dst left right caseReady
    have outClear : output input state bound (.xor dst left right) none=[] := by
      change ArithmeticBody.output input true state bound dst left right none=[]
      rw [shape]
      simpa [RegisterWrite.completeOutput,RegisterWrite.output,RegisterWrite.cleared,PcAdvance.output,FieldGet.field] using clean
    rw [filtered_of_clear _ _ _ outClear]
    exact ArithmeticBody.native_transition input true state bound dst left right caseReady
  | load dst address => exact LoadBody.native_transition input state bound dst address caseReady
  | store address src => exact StoreBody.native_transition input state bound address src caseReady
  | allocate src => exact AllocateBody.native_transition input state bound src caseReady
  | release => exact ReleaseBody.native_transition input state caseReady
  | push src =>
    have outClear : output input state bound (.push src) none=[] := by
      simpa [output,PrependBody.output,PrependBody.slot,RegisterWrite.cleared,PcAdvance.output,FieldGet.field] using clean
    rw [filtered_of_clear _ _ _ outClear]
    exact PrependBody.native_transition false input state bound src caseReady
  | pop dst => exact PopBody.native_transition input state bound dst caseReady
  | emit src =>
    have outClear : output input state bound (.emit src) none=[] := by
      simpa [output,PrependBody.output,PrependBody.slot,RegisterWrite.cleared,PcAdvance.output,FieldGet.field] using clean
    rw [filtered_of_clear _ _ _ outClear]
    exact PrependBody.native_transition true input state bound src caseReady
  | branchZero src target =>
    have outClear : output input state bound (.branchZero src target) none=[] := by
      by_cases zero : (state.reg src).val=0 <;>
        simpa [output,BranchBody.output,zero,BranchBody.base,BranchBody.targetOutput,RegisterWrite.cleared,PcAdvance.output,FieldGet.field] using clean
    rw [filtered_of_clear _ _ _ outClear]
    exact BranchBody.native_transition input state bound src target caseReady
  | halt =>
    have outClear : output input state bound .halt none=[] := by
      simpa [output,HaltBody.output,HaltBody.cleared,NativeStore.haltedOutput,PcAdvance.output,FieldGet.field] using clean
    rw [filtered_of_clear _ _ _ outClear]
    have native := HaltBody.native_transition input state caseReady
    exact native.2.trans native.1.symm

end Controller.Complexity.NativeBody
