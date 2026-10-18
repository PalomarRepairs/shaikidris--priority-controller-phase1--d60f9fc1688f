module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.NativeReset

@[expose] public section

/-! Native instruction bodies retain exact framed state packets and both
persistent program banks. Successful native transitions therefore supply the
same stored-state relation required after the next executed workspace reset. -/
namespace Controller.Complexity.NativePreserve
open StackMachine WordReader

theorem body_stored (input : Port → List Bool) (state : Controller.Cost.State width registers)
    (bound : registers ≤ 2^width) (instruction : Controller.Cost.Instruction width registers)
    (r : NativeBody.Ready input state bound instruction) :
    ∃ candidate : Controller.Cost.State width registers, NativeStore.Stored (NativeBody.output input state bound instruction) candidate := by
  have ready := NativeBody.ready input state bound instruction r
  cases instruction with
  | constant dst value => exact ⟨_,ConstantBody.stored_output input state bound dst value ready⟩
  | copy dst src =>
    exact ⟨_,RegisterWrite.complete_stored (CopyBody.loaded input state bound dst src) state dst (state.reg src)
      (CopyBody.Ready.commit input state bound dst src ready).stored⟩
  | add dst left right =>
    rw [NativeBody.output,ArithmeticBody.output_shape input false state bound dst left right ready]
    exact ⟨_,RegisterWrite.complete_stored input state dst _ r.stored⟩
  | xor dst left right =>
    rw [NativeBody.output,ArithmeticBody.output_shape input true state bound dst left right ready]
    exact ⟨_,RegisterWrite.complete_stored input state dst _ r.stored⟩
  | load dst address =>
    by_cases valid : (state.reg address).val<state.heap.size
    · rw [NativeBody.output,LoadBody.output,dite_eq_left valid]
      exact ⟨_,RegisterWrite.complete_stored input state dst _ r.stored⟩
    · exact ⟨_,LoadBody.invalid_stored input state dst address r.stored valid⟩
  | store address src =>
    by_cases valid : (state.reg address).val<state.heap.size
    · exact ⟨_,StoreBody.success_stored input state address src r.stored valid⟩
    · exact ⟨_,StoreBody.invalid_stored input state address src r.stored valid⟩
  | allocate src =>
    by_cases valid : state.heap.size<2^width
    · exact ⟨_,AllocateBody.success_stored input state bound src r.stored valid⟩
    · exact ⟨_,AllocateBody.invalid_stored input state bound src r.stored valid⟩
  | release =>
    by_cases empty : state.heap.toList=[]
    · exact ⟨_,ReleaseBody.invalid_stored input state r.stored empty⟩
    · exact ⟨_,ReleaseBody.success_stored input state r.stored empty⟩
  | push src =>
    have stored := (PrependBody.cleaned_stored false input state bound src r.stored).advance
      (PrependBody.cleaned false input state bound src) (PrependBody.updated false state (state.reg src))
    change NativeStore.Stored (PcAdvance.output (PrependBody.cleaned false input state bound src) state.pc) _ at stored
    rw [PrependBody.advance_output] at stored
    exact ⟨_,stored⟩
  | pop dst =>
    cases contents : state.stack with
    | nil => exact ⟨_,PopBody.invalid_stored input state dst r.stored contents⟩
    | cons head rest =>
      rw [NativeBody.output,PopBody.output,contents]
      exact ⟨_,RegisterWrite.complete_stored (PopBody.tailInput input rest) (PopBody.tailState state rest) dst head
        (PopBody.tail_stored input state rest r.stored)⟩
  | emit src =>
    have stored := (PrependBody.cleaned_stored true input state bound src r.stored).advance
      (PrependBody.cleaned true input state bound src) (PrependBody.updated true state (state.reg src))
    change NativeStore.Stored (PcAdvance.output (PrependBody.cleaned true input state bound src) state.pc) _ at stored
    rw [PrependBody.advance_output] at stored
    exact ⟨_,stored⟩
  | branchZero src target =>
    by_cases zero : (state.reg src).val=0
    · rw [NativeBody.output,BranchBody.output,ite_eq_left zero]
      exact ⟨_,BranchBody.taken_stored input state target r.stored⟩
    · rw [NativeBody.output,BranchBody.output,ite_eq_right zero]
      exact ⟨_,(BranchBody.base_stored input state r.stored).advance (BranchBody.base input) state⟩
  | halt => exact ⟨_,HaltBody.stored_output input state ready⟩

theorem stored_of_observation (input : Port → List Bool) (candidate next : Controller.Cost.State width registers)
    (stored : NativeStore.Stored input candidate) (observed : LoadBody.observation width registers input=some next) :
    NativeStore.Stored input next := by
  unfold LoadBody.observation at observed
  split at observed
  · have same : candidate=next := Option.some.inj ((stored.observation input candidate).symm.trans observed)
    exact same ▸ stored
  · contradiction

theorem body_success (input : Port → List Bool) (state next : Controller.Cost.State width registers)
    (bound : registers ≤ 2^width) (instruction : Controller.Cost.Instruction width registers)
    (r : NativeBody.Ready input state bound instruction) (transition : Controller.Cost.step instruction state=some next) :
    NativeStore.Stored (NativeBody.output input state bound instruction) next := by
  obtain ⟨candidate,stored⟩ := body_stored input state bound instruction r
  exact stored_of_observation _ candidate next stored ((NativeBody.semantics input state bound instruction r).trans transition)

theorem body_program (input : Port → List Bool) (state : Controller.Cost.State width registers)
    (bound : registers ≤ 2^width) (instruction : Controller.Cost.Instruction width registers)
    (port : Port) (programPort : port=some 15 ∨ port=some 19) :
    NativeBody.output input state bound instruction port=input port := by
  cases instruction with
  | constant dst value =>
    rcases programPort with rfl | rfl <;>
      simp [NativeBody.output,ConstantBody.output,ConstantBody.written,ConstantBody.loaded,OperandLoad.output,
        OperandLoad.destination,RegisterWrite.output,RegisterWrite.cleared,PcAdvance.output,FieldGet.field]
  | copy dst src =>
    rcases programPort with rfl | rfl <;>
      simp [NativeBody.output,CopyBody.output,CopyBody.loaded,CopyBody.sourceLoaded,RegisterLoad.output,RegisterRead.addressed,
        OperandLoad.output,OperandLoad.destination,RegisterWrite.completeOutput,RegisterWrite.output,RegisterWrite.cleared,PcAdvance.output,FieldGet.field]
  | add dst left right =>
    rcases programPort with rfl | rfl <;>
      simp [NativeBody.output,ArithmeticBody.output,ArithmeticBody.loaded,ArithmeticBody.calculated,ArithmeticKernel.output,
        ArithmeticOperands.output,ArithmeticOperands.parked,ArithmeticOperands.first,RegisterLoad.output,RegisterRead.addressed,
        OperandLoad.output,OperandLoad.destination,RegisterWrite.completeOutput,RegisterWrite.output,RegisterWrite.cleared,PcAdvance.output,FieldGet.field]
  | xor dst left right =>
    rcases programPort with rfl | rfl <;>
      simp [NativeBody.output,ArithmeticBody.output,ArithmeticBody.loaded,ArithmeticBody.calculated,ArithmeticKernel.output,
        ArithmeticOperands.output,ArithmeticOperands.parked,ArithmeticOperands.first,RegisterLoad.output,RegisterRead.addressed,
        OperandLoad.output,OperandLoad.destination,RegisterWrite.completeOutput,RegisterWrite.output,RegisterWrite.cleared,PcAdvance.output,FieldGet.field]
  | load dst address =>
    by_cases valid : (state.reg address).val<state.heap.size <;> rcases programPort with rfl | rfl <;>
      simp [NativeBody.output,LoadBody.output,valid,RegisterWrite.completeOutput,RegisterWrite.output,RegisterWrite.cleared,PcAdvance.output,FieldGet.field]
  | store address src =>
    by_cases valid : (state.reg address).val<state.heap.size <;> rcases programPort with rfl | rfl <;>
      simp [NativeBody.output,StoreBody.output,valid,StoreBody.base,RegisterWrite.cleared,PcAdvance.output,FieldGet.field]
  | allocate src =>
    by_cases valid : state.heap.size<2^width <;> rcases programPort with rfl | rfl <;>
      simp [NativeBody.output,AllocateBody.output,valid,RegisterWrite.cleared,PcAdvance.output,FieldGet.field]
  | release =>
    by_cases empty : state.heap.toList=[] <;> rcases programPort with rfl | rfl <;>
      simp [NativeBody.output,ReleaseBody.output,empty,RegisterWrite.cleared,PcAdvance.output,FieldGet.field]
  | push src =>
    rcases programPort with rfl | rfl <;>
      simp [NativeBody.output,PrependBody.output,PrependBody.slot,RegisterWrite.cleared,PcAdvance.output,FieldGet.field]
  | pop dst =>
    cases contents : state.stack <;> rcases programPort with rfl | rfl <;>
      simp [NativeBody.output,PopBody.output,contents,PopBody.prepared,PopBody.tailInput,RegisterWrite.completeOutput,
        RegisterWrite.output,RegisterWrite.cleared,PcAdvance.output,FieldGet.field]
  | emit src =>
    rcases programPort with rfl | rfl <;>
      simp [NativeBody.output,PrependBody.output,PrependBody.slot,RegisterWrite.cleared,PcAdvance.output,FieldGet.field]
  | branchZero src target =>
    by_cases zero : (state.reg src).val=0 <;> rcases programPort with rfl | rfl <;>
      simp [NativeBody.output,BranchBody.output,zero,BranchBody.targetOutput,BranchBody.base,RegisterWrite.cleared,PcAdvance.output,FieldGet.field]
  | halt =>
    rcases programPort with rfl | rfl <;>
      simp [NativeBody.output,HaltBody.output,HaltBody.cleared,NativeStore.haltedOutput,PcAdvance.output,FieldGet.field]

theorem dispatch_success (input : Port → List Bool) (state next : Controller.Cost.State width registers)
    (bound : registers ≤ 2^width) (instruction : Controller.Cost.Instruction width registers)
    (r : NativeDispatch.Ready input state bound instruction) (transition : Controller.Cost.step instruction state=some next) :
    NativeStore.Stored (NativeDispatch.output input state bound instruction) next := by
  have stored := body_success (NativeDispatch.bodyInput input) state next bound instruction (r.body input state bound instruction) transition
  exact ((stored.update_other _ next (some 11) [] (by decide)).update_other _ next (some 12) [] (by decide)).update_other _ next (some 13) [] (by decide)

theorem dispatch_program (input : Port → List Bool) (state : Controller.Cost.State width registers)
    (bound : registers ≤ 2^width) (instruction : Controller.Cost.Instruction width registers)
    (port : Port) (programPort : port=some 15 ∨ port=some 19) :
    NativeDispatch.output input state bound instruction port=input port := by
  have outside : port ≠ (some 11 : Port) ∧ port ≠ (some 12 : Port) ∧ port ≠ (some 13 : Port) := by
    rcases programPort with rfl | rfl <;> decide
  simp only [NativeDispatch.output,NativeDispatch.cleaned,Function.update_of_ne outside.1,
    Function.update_of_ne outside.2.1,Function.update_of_ne outside.2.2,
    body_program _ _ _ _ port programPort,NativeDispatch.bodyInput]

theorem step_success (input : Port → List Bool) (state next : Controller.Cost.State width registers)
    (bound : registers ≤ 2^width) (instructions : List (Controller.Cost.Instruction width registers))
    (r : NativeStep.Ready input state bound instructions)
    (transition : Controller.Cost.programStep instructions.toArray state=some next) :
    NativeStore.Stored (NativeStep.output input state bound instructions) next := by
  by_cases valid : state.pc.val < instructions.length
  · have native : Controller.Cost.step instructions[state.pc.val] state=some next := by
      simpa [Controller.Cost.programStep,valid] using transition
    rw [NativeStep.output,dite_eq_left valid]
    exact dispatch_success _ state next bound _ (r.body input state bound instructions valid) native
  · simp [Controller.Cost.programStep,valid] at transition

theorem step_program (input : Port → List Bool) (state : Controller.Cost.State width registers)
    (bound : registers ≤ 2^width) (instructions : List (Controller.Cost.Instruction width registers))
    (port : Port) (programPort : port=some 15 ∨ port=some 19) :
    NativeStep.output input state bound instructions port=input port := by
  by_cases valid : state.pc.val < instructions.length
  · rw [NativeStep.output,dite_eq_left valid,dispatch_program _ _ _ _ port programPort,NativeStep.fetched_shape input state bound instructions valid]
    rcases programPort with rfl | rfl <;>
      simp [InstructionFetch.chosen,InstructionShape.fieldsData,WordListReader.data_at,InstructionFields.resultFrame,InstructionFields.tagFrame,PcRead.output]
  · rw [NativeStep.output,dite_eq_right valid]
    rcases programPort with rfl | rfl <;>
      simp [NativeStep.fetched,PcFetch.result,InstructionFetch.result,Encoding.value_bits width state.pc.val state.pc.isLt,
        valid,bank,WordReader.cursorFrame,WordReader.cursorPorts_apply,StackFrames.embedStorage,PcRead.output]

theorem next_ready (input : Port → List Bool) (state next : Controller.Cost.State width registers)
    (bound : registers ≤ 2^width) (instructions : List (Controller.Cost.Instruction width registers))
    (r : NativeStep.Ready input state bound instructions)
    (transition : Controller.Cost.programStep instructions.toArray state=some next) (running : next.halted=false) :
    NativeStep.Ready (NativeReset.output (NativeStep.output input state bound instructions)) next bound instructions := by
  apply NativeReset.ready _ next bound instructions (step_success input state next bound instructions r transition) running
  · rw [step_program input state bound instructions (some 19) (Or.inr rfl)]
    exact r.codeStored
  · rw [step_program input state bound instructions (some 15) (Or.inl rfl)]
    exact r.countStored

end Controller.Complexity.NativePreserve
