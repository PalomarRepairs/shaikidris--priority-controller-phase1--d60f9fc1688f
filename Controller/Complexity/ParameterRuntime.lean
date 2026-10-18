module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.ParameterBounds
public import Controller.Complexity.Reductions
public import Mathlib.Basic.Finite.Sum

@[expose] public section

/-! Fixed-parameter runtime bounds for one actual finite binary program.
The parameter and its computable majorants bound traces of that same fixed
program; they do not choose a separate program for each parameter value. -/
namespace Controller.Complexity.ParameterRuntime
open StackMachine

def Computes [Fintype K] [DecidableEq K] (program : Program K Q)
    (function : List Bool → List Bool) (parameter : List Bool → Nat)
    (coefficient : Nat → Nat) (degree : Nat) : Prop :=
  Finite Q ∧ Computable coefficient ∧ ∀ input, ∃ ticks peak,
    Execution program (initial program input) (terminal (function input)) ticks peak ∧
      ticks ≤ coefficient (parameter input)*(input.length+1)^degree

theorem Computes.output_length [Fintype K] [DecidableEq K] {program : Program K Q}
    {function parameter coefficient degree} (computed : Computes program function parameter coefficient degree)
    (input : List Bool) :
    (function input).length ≤ input.length+coefficient (parameter input)*(input.length+1)^degree := by
  obtain ⟨ticks,peak,trace,bound⟩ := computed.2.2 input
  exact trace.output_length_le.trans (Nat.add_le_add_left bound _)

theorem Computes.output_size [Fintype K] [DecidableEq K] {program : Program K Q}
    {function parameter coefficient degree} (computed : Computes program function parameter coefficient degree)
    (input : List Bool) :
    (function input).length+1 ≤ (coefficient (parameter input)+1)*(input.length+1)^(degree+1) := by
  obtain ⟨ticks,peak,trace,bound⟩ := computed.2.2 input
  exact (Nat.add_le_add_right trace.output_length_le 1).trans (ParameterBounds.length_bound bound)

theorem Computes.compose [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {first : Program A P} {second : Program B Q} {function target sourceParameter middleParameter}
    {firstCoefficient secondCoefficient parameterBound firstDegree secondDegree}
    (firstComputed : Computes first function sourceParameter firstCoefficient firstDegree)
    (secondComputed : Computes second target middleParameter secondCoefficient secondDegree)
    (parameterComputed : Computable parameterBound)
    (parameter : ∀ input, middleParameter (function input) ≤ parameterBound (sourceParameter input)) :
    Computes (StackMachine.compose first second) (target ∘ function) sourceParameter
      (ParameterBounds.coefficient firstCoefficient secondCoefficient parameterBound secondDegree)
      (ParameterBounds.degree firstDegree secondDegree) := by
  have : Finite P := firstComputed.1
  have : Finite Q := secondComputed.1
  refine ⟨inferInstance,ParameterBounds.computable_coefficient firstComputed.2.1 secondComputed.2.1 parameterComputed secondDegree,?_⟩
  intro input
  obtain ⟨firstTicks,firstPeak,firstRun,firstTime⟩ := firstComputed.2.2 input
  obtain ⟨secondTicks,secondPeak,secondRun,secondTime⟩ := secondComputed.2.2 (function input)
  exact ⟨_,_,firstRun.compose secondRun,
    ParameterBounds.composed firstTime firstRun.output_length_le (parameter input) secondTime⟩

theorem Computes.physical [Fintype K] [DecidableEq K] [Fintype Q] {program : Program K Q}
    {function parameter coefficient degree} (computed : Computes program function parameter coefficient degree)
    (input : List Bool) :
    ∃ ticks peak, Execution program (initial program input) (terminal (function input)) ticks peak ∧
      Nonempty (Turing.TM2OutputsInTime (finiteTM program) input (some (function input)) ticks) ∧
      ticks ≤ coefficient (parameter input)*(input.length+1)^degree ∧
      peak ≤ input.length+coefficient (parameter input)*(input.length+1)^degree := by
  obtain ⟨ticks,peak,trace,time⟩ := computed.2.2 input
  have space := trace.peak_le
  simp only [live_initial] at space
  exact ⟨ticks,peak,trace,trace.finiteTM_outputs,time,space.trans (Nat.add_le_add_left time _)⟩

end Controller.Complexity.ParameterRuntime
