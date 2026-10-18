module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.NativePolynomial

@[expose] public section

/-! Polynomial simulation of native algorithms through an executed image
constructor. Both phases run on concrete finite binary machines; construction
time, intermediate image length and the complete final state are charged. -/
namespace Controller.Complexity.NativeCompilation
open StackMachine

theorem image_execution (image : MachineInput.Image)
    {final : Controller.Cost.State image.width image.registers} {nativeTicks nativePeak}
    (native : Controller.Cost.Execution image.program image.state final nativeTicks nativePeak)
    (halted : final.halted=true) :
    ∃ ticks peak, Execution ColdInterpreter.program
      (initial ColdInterpreter.program (MachineInput.encode image))
      (terminal (MachineBridge.encodeState final)) ticks peak ∧
      ticks ≤ NativePolynomial.timePolynomial.eval ((MachineInput.encode image).length+nativeTicks+1) ∧
      peak ≤ NativePolynomial.spacePolynomial.eval ((MachineInput.encode image).length+nativeTicks+1) := by
  rcases image with ⟨width,registers,bound,program,state⟩
  have trace := NativePolynomial.encoded_execution bound program.toList
    (by simpa only [Array.toArray_toList] using native) halted
  simpa only [ColdPackets.image,Array.toArray_toList] using trace

/-- An executed constructor and a source-time bound give a polynomial bound
for their actual composed machine, including the encoded intermediate image. -/
theorem computes [Fintype K] [DecidableEq K]
    {constructor : Program K Q} {construction sourceTime : Polynomial Nat}
    (image : List Bool → MachineInput.Image)
    (final : (input : List Bool) → Controller.Cost.State (image input).width (image input).registers)
    (constructed : Computes constructor (MachineInput.encode ∘ image) construction)
    (native : ∀ input, ∃ ticks peak,
      Controller.Cost.Execution (image input).program (image input).state (final input) ticks peak ∧
      ticks ≤ sourceTime.eval input.length)
    (halted : ∀ input, (final input).halted=true) :
    Computes (StackMachine.compose constructor ColdInterpreter.program)
      (fun input => MachineBridge.encodeState (final input))
      (construction+NativePolynomial.timePolynomial.comp (Polynomial.X+construction+sourceTime+1)) := by
  intro input
  obtain ⟨constructionTicks,constructionPeak,building,constructionBound⟩ := constructed input
  obtain ⟨nativeTicks,nativePeak,source,sourceBound⟩ := native input
  obtain ⟨ticks,peak,running,time,_⟩ := image_execution (image input) source (halted input)
  have imageBound := constructed.output_length_le input
  change (MachineInput.encode (image input)).length ≤ input.length+construction.eval input.length at imageBound
  have combinedBound : (MachineInput.encode (image input)).length+nativeTicks+1 ≤
      (Polynomial.X+construction+sourceTime+1).eval input.length := by
    simp only [Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
    omega
  have simulated := time.trans (polynomial_eval_mono NativePolynomial.timePolynomial combinedBound)
  refine ⟨constructionTicks+ticks,max constructionPeak peak,building.compose running,?_⟩
  rw [Polynomial.eval_add,Polynomial.eval_comp]
  exact Nat.add_le_add constructionBound simulated

theorem tm_polytime [Fintype K] [DecidableEq K] [Fintype Q]
    {constructor : Program K Q} {construction sourceTime : Polynomial Nat}
    (image : List Bool → MachineInput.Image)
    (final : (input : List Bool) → Controller.Cost.State (image input).width (image input).registers)
    (constructed : Computes constructor (MachineInput.encode ∘ image) construction)
    (native : ∀ input, ∃ ticks peak,
      Controller.Cost.Execution (image input).program (image input).state (final input) ticks peak ∧
      ticks ≤ sourceTime.eval input.length)
    (halted : ∀ input, (final input).halted=true) :
    Nonempty (Turing.TM2ComputableInPolyTime id id (fun input => MachineBridge.encodeState (final input))) := by
  exact (computes image final constructed native halted).tm_polytime

theorem output_length [Fintype K] [DecidableEq K]
    {constructor : Program K Q} {construction sourceTime : Polynomial Nat}
    (image : List Bool → MachineInput.Image)
    (final : (input : List Bool) → Controller.Cost.State (image input).width (image input).registers)
    (constructed : Computes constructor (MachineInput.encode ∘ image) construction)
    (native : ∀ input, ∃ ticks peak,
      Controller.Cost.Execution (image input).program (image input).state (final input) ticks peak ∧
      ticks ≤ sourceTime.eval input.length)
    (halted : ∀ input, (final input).halted=true) (input : List Bool) :
    (MachineBridge.encodeState (final input)).length ≤ input.length+
      (construction+NativePolynomial.timePolynomial.comp
        (Polynomial.X+construction+sourceTime+1)).eval input.length := by
  exact (computes image final constructed native halted).output_length_le input

end Controller.Complexity.NativeCompilation
