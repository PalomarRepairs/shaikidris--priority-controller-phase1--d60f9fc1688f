module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Native.SourceLift

@[expose] public section

/-! Direct eligible-set composition for the complete raw-source model checker. -/
namespace Controller.Native.SourceLift
open Controller

theorem eligible_checked (parameters : Parameters) (raw : parameters.layout = .raw)
    (K : Finset (Channel parameters.channels))
    (eligible : Admissible parameters.buses parameters.bridge.target K)
    (drive : parameters.drive = true)
    (differs : ∃ output, parameters.observations output (assignmentOfSet {parameters.bridge.target}) ≠
      parameters.observations output (assignmentOfSet K)) :
    Certificate.ModelCheck.check (SourceController.formula parameters)
      (assignment parameters (Physical.realizeBridge parameters.bridge parameters.positiveBuses K)) = true := by
  apply checked parameters raw
  have detects := (Physical.realizeBridge_detects_iff parameters.bridge parameters.positiveBuses K eligible
    parameters.observations).mpr differs
  have wire := (Physical.realizeBridge_cofactors parameters.bridge parameters.positiveBuses K).2.1
  simpa only [drive, wire] using detects

end Controller.Native.SourceLift
