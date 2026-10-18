module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Extensions.ProperBasisDetector

@[expose] public section

/-! Total proper-basis detector, including a disabled drive. -/
namespace Controller.Extensions.ProperBasisComplete
open Controller.Decoder Controller.Cost Controller.Native Controller.Native.SourceController
open Controller.Cost.NativeSourceExecution Controller.Cost.ForestIndexedOperands
open Controller.Cost.UniformDAGSource Controller.Cost.UniformDAGRun Controller.Cost.ForestInputPrefixStored
open Controller.Extensions.ProperBasisDetector Controller.Extensions.GateBasis

def disabled : Machine where
  width := 4
  program := #[.halt]
  initial := ⟨fun _ => word 4 0, #[], [], [], word 4 0, false⟩
  accepted _ := false

def detector (parameters : Parameters) (basis : Basis) (rows : List Row) (roots : List Nat) : Machine :=
  if parameters.drive then machine parameters (select basis) rows roots else disabled

set_option maxHeartbeats 1200000 in
theorem execution (parameters : Parameters) (raw : parameters.layout = .raw)
    (basis : Basis) (uses : Uses parameters.decoder basis) (proper : basis ≠ full)
    (rows : List Row) (roots : List Nat) (matched : RowsMatch parameters.decoder rows)
    (heads : HeadsMatch parameters.decoder rows matched) (rootMatches : RootsMatch parameters.decoder roots) :
    let selected := detector parameters basis rows roots
    ∃ final ticks peak, Execution selected.program selected.initial final ticks peak ∧
      final.halted = true ∧
      ticks ≤ 10000 * ((parameters.channels + parameters.decoder.roots.length + 1) * (parameters.decoder.countedSize + 1)) +
        55 * (selectedSize parameters).total + 1 ∧
      programWords selected.program + peak ≤
        10000 * ((parameters.channels + 1) * (parameters.decoder.countedSize + 1)) + 400 * (selectedSize parameters).total ∧
      (selected.accepted final = true ↔ parameters.drive = true ∧ Feasible parameters) ∧
      (selected.accepted final = true → Certificate.ModelCheck.check (formula parameters)
        (NativeRealizedChecked.decodeOutput final.output (compile parameters).toState.count) = true) := by
  dsimp only [detector]
  cases drive : parameters.drive with
  | true =>
    simpa using
      ProperBasisDetector.execution parameters raw drive basis uses proper rows roots matched heads rootMatches
  | false =>
    obtain ⟨final, trace, halted, heap, stack, output⟩ :=
      EnumerationSteps.halt_execution disabled.program disabled.initial 0 rfl rfl (by decide)
        (by simp [disabled])
    have positive : 0 < (parameters.channels + 1) * (parameters.decoder.countedSize + 1) := Nat.mul_pos (by omega) (by omega)
    simp only [Bool.false_eq_true, ite_false]
    refine ⟨final, 1, disabled.initial.liveWords, trace, halted, by omega, ?_, by simp [disabled], by simp [disabled]⟩
    change 4 + 9 ≤ 10000 * ((parameters.channels + 1) * (parameters.decoder.countedSize + 1)) + 400 * (selectedSize parameters).total
    omega

end Controller.Extensions.ProperBasisComplete
