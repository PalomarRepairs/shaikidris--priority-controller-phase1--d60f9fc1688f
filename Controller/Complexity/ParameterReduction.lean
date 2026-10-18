module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.ParameterRuntime

@[expose] public section

/-! Executed fixed-parameter many-one reductions. Runtime, parameter growth
and membership equivalence refer to one fixed computed map. Composition
retains computable bounds without assuming either parameter bound monotone. -/
namespace Controller.Complexity.ParameterReduction
open StackMachine

def Reduces [Fintype K] [DecidableEq K] (program : Program K Q) (function : List Bool → List Bool)
    (source target : Set (List Bool)) (sourceParameter targetParameter : List Bool → Nat)
    (coefficient : Nat → Nat) (degree : Nat) (parameterBound : Nat → Nat) : Prop :=
  ParameterRuntime.Computes program function sourceParameter coefficient degree ∧
    Computable parameterBound ∧ (∀ input, targetParameter (function input) ≤ parameterBound (sourceParameter input)) ∧
    ∀ input, input ∈ source ↔ function input ∈ target

theorem compose [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {first : Program A P} {second : Program B Q} {function target firstLanguage middleLanguage lastLanguage}
    {sourceParameter middleParameter lastParameter firstCoefficient secondCoefficient firstDegree secondDegree firstBound secondBound}
    (firstReduction : Reduces first function firstLanguage middleLanguage sourceParameter middleParameter firstCoefficient firstDegree firstBound)
    (secondReduction : Reduces second target middleLanguage lastLanguage middleParameter lastParameter secondCoefficient secondDegree secondBound) :
    Reduces (StackMachine.compose first second) (target ∘ function) firstLanguage lastLanguage sourceParameter lastParameter
      (ParameterBounds.coefficient firstCoefficient secondCoefficient firstBound secondDegree)
      (ParameterBounds.degree firstDegree secondDegree) (ParameterMajorant.maximum secondBound ∘ firstBound) := by
  refine ⟨firstReduction.1.compose secondReduction.1 firstReduction.2.1 firstReduction.2.2.1,
    (ParameterMajorant.computable secondReduction.2.1).comp firstReduction.2.1,?_,?_⟩
  · intro input
    exact (secondReduction.2.2.1 (function input)).trans
      (ParameterMajorant.bounded secondBound (firstReduction.2.2.1 input))
  · intro input
    exact (firstReduction.2.2.2 input).trans (secondReduction.2.2.2 (function input))

theorem identity (language : Set (List Bool)) (parameter : List Bool → Nat) :
    Reduces StackMachine.identity id language language parameter parameter (fun _ => 1) 0 id := by
  refine ⟨⟨inferInstance,Computable.const _,?_⟩,Computable.id,fun _ => le_rfl,fun _ => Iff.rfl⟩
  intro input
  obtain ⟨ticks,peak,trace,time⟩ := StackMachine.identity_computes input
  exact ⟨ticks,peak,trace,by simpa using time⟩

theorem output_size [Fintype K] [DecidableEq K] {program : Program K Q}
    {function source target sourceParameter targetParameter coefficient degree parameterBound}
    (reduction : Reduces program function source target sourceParameter targetParameter coefficient degree parameterBound)
    (input : List Bool) :
    (function input).length+1 ≤ (coefficient (sourceParameter input)+1)*(input.length+1)^(degree+1) :=
  reduction.1.output_size input

end Controller.Complexity.ParameterReduction
