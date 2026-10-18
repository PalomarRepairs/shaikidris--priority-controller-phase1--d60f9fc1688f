module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.NativeCompilation

@[expose] public section

/-! Successful decoding fixes every byte of the self-describing native image.
The interpreter simulation therefore applies to any successfully decoded input,
without a separate canonical-encoding premise. -/
namespace Controller.Complexity.ImageCanonical
open Encoding

theorem state_inverse (input : List Bool) (state : Controller.Cost.State width registers)
    (decoded : MachineBridge.decodeState width registers input=some state) :
    MachineBridge.encodeState state=input := by
  cases first : readFramedWords width input with
  | none => simp [MachineBridge.decodeState,first] at decoded
  | some pair =>
    rcases pair with ⟨values,a⟩
    cases second : readFramedWords width a with
    | none => simp [MachineBridge.decodeState,first,second] at decoded
    | some pair =>
      rcases pair with ⟨heap,b⟩
      cases third : readFramedWords width b with
      | none => simp [MachineBridge.decodeState,first,second,third] at decoded
      | some pair =>
        rcases pair with ⟨stack,c⟩
        cases fourth : readFramedWords width c with
        | none => simp [MachineBridge.decodeState,first,second,third,fourth] at decoded
        | some pair =>
          rcases pair with ⟨output,d⟩
          cases fifth : readFramedWords width d with
          | none => simp [MachineBridge.decodeState,first,second,third,fourth,fifth] at decoded
          | some pair =>
            rcases pair with ⟨control,tail⟩
            rcases control with _ | ⟨pc,_ | ⟨extra,rest⟩⟩ <;>
              rcases tail with _ | ⟨halt,_ | ⟨extraTail,restTail⟩⟩ <;>
              simp only [MachineBridge.decodeState,first,second,third,fourth,fifth,Bind.bind,Option.bind] at decoded
            all_goals try contradiction
            split at decoded
            next same =>
              cases decoded
              subst registers
              simp only [MachineBridge.encodeState,List.ofFn_getElem]
              rw [InstructionFrontend.framed_sound width input values a first,
                InstructionFrontend.framed_sound width a heap b second,
                InstructionFrontend.framed_sound width b stack c third,
                InstructionFrontend.framed_sound width c output d fourth,
                InstructionFrontend.framed_sound width d [pc] [halt] fifth]
            next wrong => simp at decoded

theorem image_inverse (input : List Bool) (image : MachineInput.Image)
    (decoded : MachineInput.decode input=some image) : MachineInput.encode image=input := by
  cases first : readCount input with
  | none => simp [MachineInput.decode,first] at decoded
  | some pair =>
    rcases pair with ⟨width,a⟩
    cases second : readCount a with
    | none => simp [MachineInput.decode,first,second] at decoded
    | some pair =>
      rcases pair with ⟨registers,b⟩
      by_cases bound : registers ≤ 2^width
      · cases third : readCount b with
        | none => simp [MachineInput.decode,first,second,bound,third] at decoded
        | some pair =>
          rcases pair with ⟨count,c⟩
          cases fourth : InstructionCodec.readMany width registers count c with
          | none => simp [MachineInput.decode,first,second,bound,third,fourth] at decoded
          | some pair =>
            rcases pair with ⟨instructions,d⟩
            cases fifth : MachineBridge.decodeState width registers d with
            | none => simp [MachineInput.decode,first,second,bound,third,fourth,fifth] at decoded
            | some state =>
              simp only [MachineInput.decode,first,second,dite_eq_left bound,third,fourth,fifth,
                Bind.bind,Option.bind,Option.pure_def,Option.some.injEq] at decoded
              subst image
              obtain ⟨length,code⟩ := ProgramSyntax.readMany_inverse bound count c instructions d fourth
              rw [HeaderParser.readCount_sound first,HeaderParser.readCount_sound second,
                HeaderParser.readCount_sound third,code,← state_inverse d state fifth,← length]
              simp [MachineInput.encode,MachineInput.envelope,InstructionCodec.encodeProgram,
                frameCount,List.append_assoc]
      · simp [MachineInput.decode,first,second,bound] at decoded

theorem decoded_execution (input : List Bool) (image : MachineInput.Image)
    (decoded : MachineInput.decode input=some image)
    {final : Controller.Cost.State image.width image.registers} {nativeTicks nativePeak}
    (native : Controller.Cost.Execution image.program image.state final nativeTicks nativePeak)
    (halted : final.halted=true) :
    ∃ ticks peak, StackMachine.Execution ColdInterpreter.program
      (StackMachine.initial ColdInterpreter.program input) (StackMachine.terminal (MachineBridge.encodeState final)) ticks peak ∧
      ticks ≤ NativePolynomial.timePolynomial.eval (input.length+nativeTicks+1) ∧
      peak ≤ NativePolynomial.spacePolynomial.eval (input.length+nativeTicks+1) := by
  have trace := NativeCompilation.image_execution image native halted
  rwa [image_inverse input image decoded] at trace

end Controller.Complexity.ImageCanonical
