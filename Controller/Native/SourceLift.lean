module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Native.Lift

@[expose] public section

/-! Evaluation of every actual retained source producer from the allocated input
roots. No existential model selection is used by the assignment constructor. -/
namespace Controller.Native.SourceLift
open Controller Controller.Native.SourceController

def finite (parameters : Parameters)
    (input : Physical.PrimaryInput parameters.channels parameters.buses) :
    Fin (compile parameters).toState.count → Bool :=
  (compile parameters).toState.circuit.evaluate (sourcePhysicalRoots parameters input)

def assignment (parameters : Parameters)
    (input : Physical.PrimaryInput parameters.channels parameters.buses) : ℕ → Bool :=
  sourceFiniteExtension (finite parameters input)

theorem restriction (parameters : Parameters)
    (input : Physical.PrimaryInput parameters.channels parameters.buses) :
    assignment parameters input ∘ SourceObservation.sourceID = finite parameters input := by
  funext index
  exact sourceFiniteExtension_sourceID _ index

theorem equations (parameters : Parameters)
    (input : Physical.PrimaryInput parameters.channels parameters.buses) :
    CNF.Satisfies (assignment parameters input) (equationFormula parameters) := by
  apply (compile_source_model_iff parameters _).mp
  rw [restriction]
  exact (compile parameters).toState.circuit.evaluate_satisfies _

theorem root (parameters : Parameters)
    (input : Physical.PrimaryInput parameters.channels parameters.buses)
    (index : Fin (SourceInitialIDs.rootCount parameters)) :
    assignment parameters input (index.val + 1) = sourcePhysicalRoots parameters input index := by
  have identity : SourceObservation.sourceID ((compile parameters).toState.circuit.rootIndex index) = index.val + 1 := by
    simp only [SourceObservation.sourceID, source_root_index_val]
  rw [← identity]
  change sourceFiniteExtension (finite parameters input) _ = _
  rw [sourceFiniteExtension_sourceID]
  exact (compile parameters).toState.circuit.evaluate_root _ index

theorem loaded (parameters : Parameters)
    (input : Physical.PrimaryInput parameters.channels parameters.buses) :
    sourceInput parameters (assignment parameters input) = input := by
  apply sourceInput_eq_physical_of_roots
  · intro channel
    exact (root parameters input (SourceInitialIDs.rootIndex (.enable channel))).trans
      (sourcePhysicalRoots_at_root parameters input (.enable channel))
  · intro bus channel
    exact (root parameters input (SourceInitialIDs.rootIndex (.request bus channel))).trans
      (sourcePhysicalRoots_at_root parameters input (.request bus channel))

theorem satisfies (parameters : Parameters) (raw : parameters.layout = .raw)
    (input : Physical.PrimaryInput parameters.channels parameters.buses)
    (detects : Physical.BridgeInputDetects parameters.bridge parameters.drive parameters.observations input
      (Physical.bridgeD parameters.bridge input)) :
    CNF.Satisfies (assignment parameters input) (formula parameters) := by
  apply (source_formula_physical_iff parameters _ raw).mpr
  exact ⟨equations parameters input, by simpa only [loaded] using detects⟩

theorem checked (parameters : Parameters) (raw : parameters.layout = .raw)
    (input : Physical.PrimaryInput parameters.channels parameters.buses)
    (detects : Physical.BridgeInputDetects parameters.bridge parameters.drive parameters.observations input
      (Physical.bridgeD parameters.bridge input)) :
    Certificate.ModelCheck.check (formula parameters) (assignment parameters input) = true :=
  (Certificate.ModelCheck.check_iff _ _).mpr (satisfies parameters raw input detects)

end Controller.Native.SourceLift
