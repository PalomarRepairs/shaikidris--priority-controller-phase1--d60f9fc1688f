module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.SpaceVirtualRun
public import Controller.Complexity.SpaceLogGrowth

public import Mathlib.Tactic.Ring

@[expose] public section

/-! Executed composition of read-only-input/write-only-output logspace
transducers. The second input is recomputed by the fixed virtual-input program;
intermediate output is never allocated as work or external output. -/
namespace Controller.Complexity.SpaceComposition

def constant (firstLabels firstBanks firstConstant secondConstant : Nat) :=
  firstConstant+(secondConstant+2)*SpaceLogGrowth.constant firstLabels firstBanks firstConstant+2

theorem computes [Fintype A] [Fintype B] [Fintype P] [Fintype Q] [DecidableEq A] [DecidableEq B]
    (first : SpaceMachine.Program A P) (second : SpaceMachine.Program B Q)
    (enumeration : Fin n ≃ SpaceLookup.Bank A) {function target firstConstant secondConstant}
    (firstComputes : LogSpaceBounds.Computes first function firstConstant)
    (secondComputes : LogSpaceBounds.Computes second target secondConstant) :
    LogSpaceBounds.Computes (SpaceVirtual.program first second enumeration) (fun input => target (function input))
      (constant (Fintype.card P) (Fintype.card A) firstConstant secondConstant) := by
  refine ⟨inferInstance,fun input => ?_⟩
  obtain ⟨result,ticks,peak,trace,halted,output,space⟩ := SpaceVirtualRun.cold first second enumeration firstComputes secondComputes input
  have intermediate := SpaceLogGrowth.output_bits firstComputes input
  have scaled := Nat.mul_le_mul_left (secondConstant+2) intermediate
  have positive : 2 ≤ 2*LogSpaceBounds.bits input.length := by unfold LogSpaceBounds.bits; omega
  refine ⟨result,ticks,peak,trace,halted,output,?_⟩
  calc
    _ ≤ firstConstant*LogSpaceBounds.bits input.length+(secondConstant+2)*LogSpaceBounds.bits (function input).length+2 := space
    _ ≤ firstConstant*LogSpaceBounds.bits input.length+
        (secondConstant+2)*(SpaceLogGrowth.constant (Fintype.card P) (Fintype.card A) firstConstant*LogSpaceBounds.bits input.length)+
        2*LogSpaceBounds.bits input.length := Nat.add_le_add (Nat.add_le_add_left scaled _) positive
    _ = _ := by unfold constant; ring

theorem output_length [Fintype A] [Fintype B] [Fintype P] [Fintype Q] [DecidableEq A] [DecidableEq B]
    (first : SpaceMachine.Program A P) (second : SpaceMachine.Program B Q)
    (enumeration : Fin n ≃ SpaceLookup.Bank A) {function target firstConstant secondConstant}
    (firstComputes : LogSpaceBounds.Computes first function firstConstant)
    (secondComputes : LogSpaceBounds.Computes second target secondConstant) (input : List Bool) :
    (target (function input)).length ≤ LogSpaceBounds.timeBound (Fintype.card (SpaceVirtual.Label n P Q))
      (Fintype.card (SpaceVirtual.Bank A B))
      (constant (Fintype.card P) (Fintype.card A) firstConstant secondConstant) input.length :=
  (computes first second enumeration firstComputes secondComputes).output_length input

theorem exists_program [Fintype A] [Fintype B] [Fintype P] [Fintype Q] [DecidableEq A] [DecidableEq B]
    (first : SpaceMachine.Program A P) (second : SpaceMachine.Program B Q)
    {function target firstConstant secondConstant}
    (firstComputes : LogSpaceBounds.Computes first function firstConstant)
    (secondComputes : LogSpaceBounds.Computes second target secondConstant) :
    ∃ composite : SpaceMachine.Program (SpaceVirtual.Bank A B)
        (SpaceVirtual.Label (Fintype.card (SpaceLookup.Bank A)) P Q),
      LogSpaceBounds.Computes composite (fun input => target (function input))
        (constant (Fintype.card P) (Fintype.card A) firstConstant secondConstant) := by
  classical
  exact ⟨_,computes first second (Fintype.equivFin (SpaceLookup.Bank A)).symm firstComputes secondComputes⟩

theorem physical_execution [Fintype A] [Fintype B] [Fintype P] [Fintype Q] [DecidableEq A] [DecidableEq B]
    (first : SpaceMachine.Program A P) (second : SpaceMachine.Program B Q)
    (enumeration : Fin n ≃ SpaceLookup.Bank A) {function target firstConstant secondConstant}
    (firstComputes : LogSpaceBounds.Computes first function firstConstant)
    (secondComputes : LogSpaceBounds.Computes second target secondConstant) (input : List Bool) :
    ∃ final ticks peak, SpaceTM.Execution (SpaceVirtual.program first second enumeration)
      (SpaceTM.configuration (SpaceMachine.initial (SpaceVirtual.program first second enumeration) input))
      (SpaceTM.configuration final) ticks peak ∧ final.pc=none ∧ final.output.reverse=target (function input) ∧
      peak ≤ constant (Fintype.card P) (Fintype.card A) firstConstant secondConstant*LogSpaceBounds.bits input.length ∧
      ticks ≤ (LogSpaceBounds.timePolynomial (Fintype.card (SpaceVirtual.Label n P Q))
        (Fintype.card (SpaceVirtual.Bank A B))
        (constant (Fintype.card P) (Fintype.card A) firstConstant secondConstant)).eval input.length :=
  (computes first second enumeration firstComputes secondComputes).executed_time input

end Controller.Complexity.SpaceComposition
