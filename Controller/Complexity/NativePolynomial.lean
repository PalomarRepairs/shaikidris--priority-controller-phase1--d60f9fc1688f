module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.ColdInterpreter
public import Controller.Complexity.NativeGrowth
public import Mathlib.Tactic.Linarith

@[expose] public section

/-! The cold interpreter has an actual natural-coefficient polynomial bound
in encoded input length plus source steps. Native peak words and word width
are eliminated using executed storage growth and the input's unary headers. -/
namespace Controller.Complexity.NativePolynomial
open StackMachine WordReader

noncomputable def parserPolynomial : Polynomial Nat := 32*Polynomial.X^4+256*Polynomial.X^3+
  484*Polynomial.X^2+643*Polynomial.X+261
noncomputable def fetchPolynomial : Polynomial Nat := 12*Polynomial.X^3+197*Polynomial.X^2+434*Polynomial.X+104
noncomputable def stepPolynomial : Polynomial Nat := fetchPolynomial+12000*(Polynomial.X+fetchPolynomial)^2+
  10003*(Polynomial.X+fetchPolynomial)+4011
noncomputable def framePolynomial : Polynomial Nat := 2*(Polynomial.X+parserPolynomial+Polynomial.X^2+
  stepPolynomial.comp (Polynomial.X^2))+45
noncomputable def timePolynomial : Polynomial Nat := Polynomial.X+2*parserPolynomial+
  Polynomial.X*(Polynomial.X^2+2*stepPolynomial.comp (Polynomial.X^2)+47)+11*framePolynomial+121
noncomputable def spacePolynomial : Polynomial Nat := 12*framePolynomial+119

/-- Executable bounds coincide with the algebraic polynomial descriptors. -/
def frameBound (size : Nat) := 2*(size+ImageReader.polynomial size+size^2+NativeStep.budget (size^2))+45
def timeBound (size : Nat) := size+2*ImageReader.polynomial size+
  size*(size^2+2*NativeStep.budget (size^2)+47)+11*frameBound size+121
def spaceBound (size : Nat) := 12*frameBound size+119

theorem parser_eval (size : Nat) : parserPolynomial.eval size=ImageReader.polynomial size := by
  simp [parserPolynomial,ImageReader.polynomial]
theorem fetch_eval (size : Nat) : fetchPolynomial.eval size=NativeStep.fetchBudget size := by
  simp [fetchPolynomial,NativeStep.fetchBudget]
theorem step_eval (size : Nat) : stepPolynomial.eval size=NativeStep.budget size := by
  simp [stepPolynomial,fetch_eval,NativeStep.budget]
theorem frame_eval (size : Nat) : framePolynomial.eval size=
    2*(size+ImageReader.polynomial size+size^2+NativeStep.budget (size^2))+45 := by
  simp [framePolynomial,Polynomial.eval_comp,parser_eval,step_eval]

theorem time_eval (size : Nat) : timePolynomial.eval size=timeBound size := by
  simp [timePolynomial,timeBound,Polynomial.eval_comp,parser_eval,step_eval,frame_eval,frameBound]
theorem space_eval (size : Nat) : spacePolynomial.eval size=spaceBound size := by
  simp [spacePolynomial,spaceBound,frame_eval,frameBound]

theorem image_length (bound : registers ≤ 2^width) (instructions : List (Controller.Cost.Instruction width registers))
    (state : Controller.Cost.State width registers) :
    (MachineInput.encode (ColdPackets.image bound instructions state)).length=
      NativeEnvelope.mass width registers instructions.length (InstructionCodec.encodeMany bound instructions).length state.liveWords+3 := by
  rw [ColdPackets.image_shape,MachineInput.envelope_length]
  simp only [ColdPackets.body,Encoding.frameCount,List.length_append,List.length_replicate,List.length_cons,
    MachineBridge.encodeState_length,NativeEnvelope.mass]
  omega

theorem width_le_image (bound : registers ≤ 2^width) (instructions : List (Controller.Cost.Instruction width registers))
    (state : Controller.Cost.State width registers) : width ≤ (MachineInput.encode (ColdPackets.image bound instructions state)).length := by
  rw [image_length]
  unfold NativeEnvelope.mass
  omega

theorem envelope_le (bound : registers ≤ 2^width) (instructions : List (Controller.Cost.Instruction width registers))
    {state final : Controller.Cost.State width registers} {ticks peak}
    (native : Controller.Cost.Execution instructions.toArray state final ticks peak) :
    let size := (MachineInput.encode (ColdPackets.image bound instructions state)).length
    NativeEnvelope.mass width registers instructions.length (InstructionCodec.encodeMany bound instructions).length peak ≤
      size+(size+1)*ticks := by
  intro size
  have growth := Nat.mul_le_mul_left (width+1) (NativeGrowth.peak_le native)
  rw [Nat.mul_add] at growth
  have length := image_length bound instructions state
  have header := width_le_image bound instructions state
  have factor := Nat.mul_le_mul_right ticks (Nat.add_le_add_right header 1)
  unfold NativeEnvelope.mass at *
  dsimp only [size] at *
  omega

theorem space_majorant (size envelope combined : Nat) (inputBound : size ≤ combined) (wordBound : envelope ≤ combined^2) :
    NativeLoop.space (size+ImageReader.polynomial size) envelope ≤ framePolynomial.eval combined := by
  have parserBound := polynomial_eval_mono parserPolynomial inputBound
  change parserPolynomial.eval size ≤ parserPolynomial.eval combined at parserBound
  rw [parser_eval,parser_eval] at parserBound
  have budgetBound := NativeEnvelope.budget_mono wordBound
  rw [frame_eval]
  unfold NativeLoop.space
  have left : size+ImageReader.polynomial size ≤ combined+ImageReader.polynomial combined+combined^2+NativeStep.budget (combined^2) := by omega
  have right : envelope+NativeStep.budget envelope ≤ combined+ImageReader.polynomial combined+combined^2+NativeStep.budget (combined^2) := by omega
  exact Nat.add_le_add_right (Nat.mul_le_mul_left 2 (max_le left right)) 45

theorem polynomial_bounds (size nativeTicks envelope ticks peak : Nat)
    (words : envelope ≤ size+(size+1)*nativeTicks)
    (time : ticks ≤ size+2*ImageReader.polynomial size+nativeTicks*NativeLoop.perStep envelope+
      11*NativeLoop.space (size+ImageReader.polynomial size) envelope+121)
    (space : peak ≤ 12*NativeLoop.space (size+ImageReader.polynomial size) envelope+119) :
    ticks ≤ timePolynomial.eval (size+nativeTicks+1) ∧ peak ≤ spacePolynomial.eval (size+nativeTicks+1) := by
  let combined := size+nativeTicks+1
  have inputBound : size ≤ combined := by dsimp only [combined]; omega
  have nativeBound : nativeTicks ≤ combined := by dsimp only [combined]; omega
  have wordBound : envelope ≤ combined^2 := by dsimp only [combined]; nlinarith
  have parserBound := polynomial_eval_mono parserPolynomial inputBound
  change parserPolynomial.eval size ≤ parserPolynomial.eval combined at parserBound
  rw [parser_eval,parser_eval] at parserBound
  have budgetBound := NativeEnvelope.budget_mono wordBound
  have frameEstimate : NativeLoop.space (size+ImageReader.polynomial size) envelope ≤
      frameBound combined := by
    simpa only [frame_eval,frameBound] using space_majorant size envelope combined inputBound wordBound
  have cycleBound : NativeLoop.perStep envelope ≤ combined^2+2*NativeStep.budget (combined^2)+47 := by
    unfold NativeLoop.perStep
    omega
  have cycles := Nat.mul_le_mul nativeBound cycleBound
  have timeBound : ticks ≤ timePolynomial.eval combined := by
    rw [time_eval]
    unfold NativePolynomial.timeBound
    omega
  have peakBound : peak ≤ spacePolynomial.eval combined := by
    rw [space_eval]
    unfold spaceBound
    omega
  exact ⟨timeBound,peakBound⟩

theorem encoded_execution (bound : registers ≤ 2^width)
    (instructions : List (Controller.Cost.Instruction width registers))
    {state final : Controller.Cost.State width registers} {nativeTicks nativePeak}
    (native : Controller.Cost.Execution instructions.toArray state final nativeTicks nativePeak) (halted : final.halted=true) :
    let input := MachineInput.encode (ColdPackets.image bound instructions state)
    let combined := input.length+nativeTicks+1
    ∃ ticks peak, Execution ColdInterpreter.program (initial ColdInterpreter.program input)
      (StackMachine.terminal (MachineBridge.encodeState final)) ticks peak ∧
      ticks ≤ timePolynomial.eval combined ∧ peak ≤ spacePolynomial.eval combined := by
  intro input combined
  obtain ⟨ticks,peak,trace,time,space⟩ := ColdInterpreter.encoded_execution bound instructions native halted
  have words := envelope_le bound instructions native
  have bounds := polynomial_bounds input.length nativeTicks
    (NativeEnvelope.mass width registers instructions.length (InstructionCodec.encodeMany bound instructions).length nativePeak)
    ticks peak words time space
  exact ⟨ticks,peak,trace,bounds.1,bounds.2⟩

theorem tm_outputs (bound : registers ≤ 2^width)
    (instructions : List (Controller.Cost.Instruction width registers))
    {state final : Controller.Cost.State width registers} {nativeTicks nativePeak}
    (native : Controller.Cost.Execution instructions.toArray state final nativeTicks nativePeak) (halted : final.halted=true) :
    let input := MachineInput.encode (ColdPackets.image bound instructions state)
    Nonempty (Turing.TM2OutputsInTime (finiteTM ColdInterpreter.program) input (some (MachineBridge.encodeState final))
      (timePolynomial.eval (input.length+nativeTicks+1))) := by
  intro input
  obtain ⟨ticks,peak,trace,time,_⟩ := encoded_execution bound instructions native halted
  obtain ⟨execution⟩ := trace.finiteTM_outputs
  exact ⟨⟨execution.toEvalsTo,execution.steps_le_m.trans time⟩⟩

end Controller.Complexity.NativePolynomial
