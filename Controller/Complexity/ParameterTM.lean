module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.ParameterReduction

@[expose] public section

/-! One fixed finite TM2 realizes each executed parameterized computation.
The machine and its alphabets are chosen before the input or parameter.
The witness's finite-control hypothesis supplies the control enumeration. -/
namespace Controller.Complexity.ParameterTM
open StackMachine

theorem realization [Fintype K] [DecidableEq K] {program : Program K Q}
    {function parameter coefficient degree}
    (computed : ParameterRuntime.Computes program function parameter coefficient degree) :
    ∃ (machine : Turing.FinTM2) (inputAlphabet : Bool ≃ machine.Γ machine.k₀)
      (outputAlphabet : Bool ≃ machine.Γ machine.k₁),
      ∀ input, Nonempty (Turing.TM2OutputsInTime machine (input.map inputAlphabet)
        (some ((function input).map outputAlphabet)) (coefficient (parameter input)*(input.length+1)^degree)) := by
  classical
  have : Finite Q := computed.1
  let : Fintype Q := Fintype.ofFinite Q
  refine ⟨finiteTM program,Equiv.refl Bool,Equiv.refl Bool,fun input => ?_⟩
  obtain ⟨ticks,peak,trace,time⟩ := computed.2.2 input
  obtain ⟨actual⟩ := trace.finiteTM_outputs
  change Nonempty (Turing.TM2OutputsInTime (finiteTM program) (input.map id)
    (some ((function input).map id)) (coefficient (parameter input)*(input.length+1)^degree))
  dsimp only [Turing.TM2OutputsInTime,finiteTM] at actual ⊢
  rw [List.map_id,List.map_id]
  exact ⟨⟨actual.toEvalsTo,actual.steps_le_m.trans time⟩⟩

end Controller.Complexity.ParameterTM
