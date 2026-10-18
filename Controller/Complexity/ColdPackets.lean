module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.NativeDeliver
public import Controller.Complexity.ImageReader

@[expose] public section

/-! Execution of the cold image reader establishes the interpreter's literal
state, code and count packets. Canonical endpoints are identified by execution
determinism, retaining the existing all-input parser resource bounds. -/
namespace Controller.Complexity.ColdPackets
open StackMachine WordReader

def values (state : Controller.Cost.State width registers) :=
  [List.ofFn state.reg,state.heap.toList,state.stack,state.output,[state.pc]]

def body (bound : registers ≤ 2^width) (instructions : List (Controller.Cost.Instruction width registers))
    (state : Controller.Cost.State width registers) :=
  Encoding.frameCount instructions.length (InstructionCodec.encodeMany bound instructions++MachineBridge.encodeState state)

def image (bound : registers ≤ 2^width) (instructions : List (Controller.Cost.Instruction width registers))
    (state : Controller.Cost.State width registers) : MachineInput.Image :=
  ⟨width,registers,bound,instructions.toArray,state⟩

def output (bound : registers ≤ 2^width) (instructions : List (Controller.Cost.Instruction width registers))
    (state : Controller.Cost.State width registers) :=
  StateReader.store (ImageAssembly.codeBank width registers bound (body bound instructions state) instructions
    (MachineBridge.encodeState state)) width StateReader.fields (values state) state.halted

theorem image_shape (bound : registers ≤ 2^width) (instructions : List (Controller.Cost.Instruction width registers))
    (state : Controller.Cost.State width registers) :
    MachineInput.encode (image bound instructions state)=MachineInput.envelope width registers (body bound instructions state) := by
  simp [image,MachineInput.encode,body,InstructionCodec.encodeProgram,Encoding.frameCount,List.append_assoc]

theorem state_read (state : Controller.Cost.State width registers) :
    StateReader.read width registers StateReader.fields (MachineBridge.encodeState state)=some (values state,state.halted) := by
  simp [StateReader.read,StateReader.fields,StateReader.Field.read,CheckedWordField.readField,
    MachineBridge.encodeState,Encoding.readFramedWords_encoded,StateShape.decodeTail,values]

theorem prefix_read (bound : registers ≤ 2^width) (instructions : List (Controller.Cost.Instruction width registers))
    (state : Controller.Cost.State width registers) :
    ProgramSyntax.readPrefix width registers (body bound instructions state)=some (instructions,MachineBridge.encodeState state) := by
  simp only [ProgramSyntax.readPrefix,body,Encoding.readCount_frame,Bind.bind,Option.bind,InstructionCodec.readMany_encoded]

theorem packets (bound : registers ≤ 2^width) (instructions : List (Controller.Cost.Instruction width registers))
    (state : Controller.Cost.State width registers) : NativeLoop.Packets (output bound instructions state) state bound instructions := by
  constructor
  · constructor <;>
      simp [output,StateReader.store,StateReader.fieldsBank,StateReader.fields,values,StateReader.Field.slot,
        StateShape.tail_at,ImageAssembly.code_at]
  · simp [output,StateReader.store,StateReader.fieldsBank,StateReader.fields,values,StateReader.Field.slot,
      StateShape.tail_at,ImageAssembly.code_at]
  · simp [output,StateReader.store,StateReader.fieldsBank,StateReader.fields,values,StateReader.Field.slot,
      StateShape.tail_at,ImageAssembly.code_at]

theorem body_execution (bound : registers ≤ 2^width) (instructions : List (Controller.Cost.Instruction width registers))
    (state : Controller.Cost.State width registers) :
    ∃ ticks peak, Execution ImageAssembly.program
      ⟨some ImageAssembly.program.main,ImageHeaders.data width registers [] (body bound instructions state)⟩
      ⟨none,output bound instructions state⟩ ticks peak := by
  let source := body bound instructions state
  let frame := ImageAssembly.codeBank width registers bound source instructions (MachineBridge.encodeState state)
  obtain ⟨last,ticks,peak,first,halted,_,observed,_,_⟩ :=
    ProgramTotal.total_decodes (ImageHeaders.data width registers [] source) bound source
      (ImageAssembly.header_workspace width registers source)
      (by simp [ImageHeaders.data_at]) (by simp [ImageHeaders.data_at]) (by simp [ImageHeaders.data_at])
  rw [ImageAssembly.header_entry] at first
  obtain ⟨endpoint,_,_⟩ := observed instructions (MachineBridge.encodeState state) (prefix_read bound instructions state)
  change last.stk=frame at endpoint
  have terminal : last=⟨none,last.stk⟩ := congrArg₂ State.mk halted rfl
  rw [terminal,endpoint] at first
  obtain ⟨stateTicks,statePeak,stored,second,_,_,_,stateObserved⟩ :=
    StateReader.state_total width registers frame (ImageAssembly.code_ready width registers bound source instructions (MachineBridge.encodeState state))
  have sourceStored : frame (some 0)=MachineBridge.encodeState state := by simp [frame,ImageAssembly.code_at]
  have parsed : StateReader.read width registers StateReader.fields (frame (some 0))=some (values state,state.halted) := by
    rw [sourceStored]
    exact state_read state
  have exactStore := stateObserved (values state) state.halted parsed
  rw [exactStore] at second
  have trace := GuardedLink.success none Option.isNone first second (by simp [frame,ImageAssembly.code_at])
  exact ⟨ticks+stateTicks,max peak statePeak,trace⟩

theorem headers_read (bound : registers ≤ 2^width) (instructions : List (Controller.Cost.Instruction width registers))
    (state : Controller.Cost.State width registers) :
    ImageHeaders.readHeaders (MachineInput.encode (image bound instructions state))=some (width,registers,body bound instructions state) := by
  rw [image_shape]
  simp [ImageHeaders.readHeaders,MachineInput.envelope,Encoding.readCount_frame,bound]

theorem endpoint_execution (bound : registers ≤ 2^width) (instructions : List (Controller.Cost.Instruction width registers))
    (state : Controller.Cost.State width registers) :
    ∃ ticks peak, Execution ImageReader.program (initial ImageReader.program (MachineInput.encode (image bound instructions state)))
      ⟨none,output bound instructions state⟩ ticks peak := by
  obtain ⟨headerTicks,headerPeak,first,_,_⟩ := ImageHeaders.success_execution (headers_read bound instructions state)
  obtain ⟨bodyTicks,bodyPeak,second⟩ := body_execution bound instructions state
  rw [ColdInput.initial_bank] at first
  have trace := GuardedLink.success none Option.isNone first second (by simp [ImageHeaders.data_at])
  change Execution ImageReader.program ⟨some ImageReader.program.main,_⟩ _ _ _ at trace
  rw [← ColdInput.initial_bank ImageReader.program] at trace
  exact ⟨headerTicks+bodyTicks,max headerPeak bodyPeak,trace⟩

theorem execution (bound : registers ≤ 2^width) (instructions : List (Controller.Cost.Instruction width registers))
    (state : Controller.Cost.State width registers) :
    ∃ ticks peak, Execution ImageReader.program (initial ImageReader.program (MachineInput.encode (image bound instructions state)))
      ⟨none,output bound instructions state⟩ ticks peak ∧
      ticks ≤ ImageReader.polynomial (MachineInput.encode (image bound instructions state)).length ∧
      peak ≤ ImageReader.polynomial (MachineInput.encode (image bound instructions state)).length+
        (MachineInput.encode (image bound instructions state)).length := by
  obtain ⟨exactTicks,exactPeak,exactRun⟩ := endpoint_execution bound instructions state
  obtain ⟨ticks,peak,stored,run,time,space,_,_⟩ := ImageReader.total_decodes (MachineInput.encode (image bound instructions state))
  have same := InstructionFrontend.terminal_unique run exactRun rfl rfl
  have storage : stored=output bound instructions state := congrArg State.stk same
  rw [storage] at run
  exact ⟨ticks,peak,run,time,space⟩

end Controller.Complexity.ColdPackets
