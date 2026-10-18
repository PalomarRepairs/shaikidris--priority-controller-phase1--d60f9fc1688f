module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.SpaceTapeBoot
public import Controller.Complexity.SpaceTapeSimulation
public import Controller.Complexity.SpaceComposition

@[expose] public section

/-! Cold ordinary-multitape realization of the read-only source model.
Work tapes start blank, all bottom markers are written by the machine, and
every visited work position lies in the proved finite interval. -/
namespace Controller.Complexity.SpaceTapeBridge
open SpaceMachine SpaceTapeMachine SpaceTapeRun

theorem cold [Fintype K] [DecidableEq K] (enumeration : Fin n ≃ K)
    {program : SpaceMachine.Program K Q} {input final ticks peak}
    (actual : SpaceMachine.Execution program (SpaceMachine.initial program input) final ticks peak) :
    ∃ tapeTicks, Run enumeration program (peak+2) (SpaceTapeMachine.initial input) (configuration final) tapeTicks ∧
      tapeTicks ≤ n+1+2*ticks := by
  obtain ⟨simulationTicks,simulation,time⟩ := SpaceTapeSimulation.execution enumeration actual
  have boot := (SpaceTapeBoot.execution enumeration program input).mono (show 2 ≤ peak+2 by omega)
  exact ⟨_,boot.append simulation,by omega⟩

theorem halted [DecidableEq K] (enumeration : Fin n ≃ K) (program : SpaceMachine.Program K Q)
    (source : SpaceMachine.State K Q) (halt : source.pc=none) :
    SpaceTapeMachine.step enumeration program (configuration source)=none := by
  simp [SpaceTapeMachine.step,configuration,halt]

theorem computes [Fintype K] [DecidableEq K] [Fintype Q]
    (enumeration : Fin n ≃ K) {program : SpaceMachine.Program K Q} {function constant}
    (computed : LogSpaceBounds.Computes program function constant) (input : List Bool) :
    ∃ final tapeTicks, Run enumeration program ((constant+2)*LogSpaceBounds.bits input.length)
      (SpaceTapeMachine.initial input) (configuration final) tapeTicks ∧
      final.pc=none ∧ final.output.reverse=function input ∧
      tapeTicks ≤ n+1+2*LogSpaceBounds.timeBound (Fintype.card Q) (Fintype.card K) constant input.length := by
  obtain ⟨final,ticks,peak,source,halt,output,bounded⟩ := computed.2 input
  obtain ⟨tapeTicks,tapes,time⟩ := cold enumeration source
  have sourceTime := LogSpaceBounds.running_time source halt
    (by simpa only [SpaceMachine.initial,ReadOnlyInput.word_start] using bounded)
  simp only [SpaceMachine.initial,ReadOnlyInput.word_start] at sourceTime
  have capacity : peak+2 ≤ (constant+2)*LogSpaceBounds.bits input.length := by
    have positive : 2 ≤ 2*LogSpaceBounds.bits input.length := by unfold LogSpaceBounds.bits; omega
    rw [Nat.add_mul]
    omega
  exact ⟨final,tapeTicks,tapes.mono capacity,halt,output,by omega⟩

theorem composed [Fintype A] [Fintype B] [Fintype P] [Fintype Q] [DecidableEq A] [DecidableEq B]
    (first : SpaceMachine.Program A P) (second : SpaceMachine.Program B Q)
    (lookup : Fin n ≃ SpaceLookup.Bank A) (banks : Fin m ≃ SpaceVirtual.Bank A B)
    {function target firstConstant secondConstant}
    (firstComputes : LogSpaceBounds.Computes first function firstConstant)
    (secondComputes : LogSpaceBounds.Computes second target secondConstant) (input : List Bool) :
    ∃ final tapeTicks, Run banks (SpaceVirtual.program first second lookup)
      ((SpaceComposition.constant (Fintype.card P) (Fintype.card A) firstConstant secondConstant+2)*
        LogSpaceBounds.bits input.length)
      (SpaceTapeMachine.initial input) (configuration final) tapeTicks ∧
      final.pc=none ∧ final.output.reverse=target (function input) ∧
      tapeTicks ≤ m+1+2*LogSpaceBounds.timeBound (Fintype.card (SpaceVirtual.Label n P Q))
        (Fintype.card (SpaceVirtual.Bank A B))
        (SpaceComposition.constant (Fintype.card P) (Fintype.card A) firstConstant secondConstant) input.length :=
  computes banks (SpaceComposition.computes first second lookup firstComputes secondComputes) input

end Controller.Complexity.SpaceTapeBridge
