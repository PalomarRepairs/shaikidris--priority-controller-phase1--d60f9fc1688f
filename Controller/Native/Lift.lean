module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Native.EncodeCorrect
public import Controller.Certificate.ModelCheck
public import Controller.Physical.DetectCorrect

@[expose] public section

/-! Constructive complete named and binary-expanded native assignments. Physical
roots and every internal coordinate are evaluated by the native gate semantics.
The checker consumes the complete formula, including its assertions. -/
namespace Controller.Native.Lift
open Controller

def named (parameters : Parameters)
    (input : Physical.PrimaryInput parameters.channels parameters.buses) (wire : Bool) :=
  parameters.physicalAssignment input wire

def bounded (parameters : Parameters)
    (input : Physical.PrimaryInput parameters.channels parameters.buses) (wire : Bool) :=
  Bounded.globalAssignment parameters (named parameters input wire)

theorem named_satisfies (parameters : Parameters)
    (input : Physical.PrimaryInput parameters.channels parameters.buses) (wire : Bool)
    (detects : Physical.BridgeInputDetects parameters.bridge parameters.drive parameters.observations input wire) :
    CNF.Satisfies (named parameters input wire) parameters.specificationFormula := by
  apply (CNF.satisfies_append _ _ _).mpr
  exact ⟨parameters.physicalAssignment_satisfies_equations input wire,
    (parameters.physicalAssignment_assertions_iff input wire).mpr detects⟩

theorem bounded_satisfies (parameters : Parameters)
    (input : Physical.PrimaryInput parameters.channels parameters.buses) (wire : Bool)
    (detects : Physical.BridgeInputDetects parameters.bridge parameters.drive parameters.observations input wire) :
    CNF.Satisfies (bounded parameters input wire) (Bounded.globalFormula parameters) :=
  Bounded.globalAssignment_satisfies parameters _ (named_satisfies parameters input wire detects)

theorem named_checked (parameters : Parameters)
    (input : Physical.PrimaryInput parameters.channels parameters.buses) (wire : Bool)
    (detects : Physical.BridgeInputDetects parameters.bridge parameters.drive parameters.observations input wire) :
    Certificate.ModelCheck.check parameters.specificationFormula (named parameters input wire) = true :=
  (Certificate.ModelCheck.check_iff _ _).mpr (named_satisfies parameters input wire detects)

theorem bounded_checked (parameters : Parameters)
    (input : Physical.PrimaryInput parameters.channels parameters.buses) (wire : Bool)
    (detects : Physical.BridgeInputDetects parameters.bridge parameters.drive parameters.observations input wire) :
    Certificate.ModelCheck.check (Bounded.globalFormula parameters) (bounded parameters input wire) = true :=
  (Certificate.ModelCheck.check_iff _ _).mpr (bounded_satisfies parameters input wire detects)

theorem bounded_primary (parameters : Parameters)
    (input : Physical.PrimaryInput parameters.channels parameters.buses) (wire : Bool) (primary) :
    bounded parameters input wire (.original (.primary primary)) =
      Parameters.primaryAssignment input wire primary := rfl

def detectNamed (parameters : Parameters) :=
  (Physical.detectInput parameters.bridge parameters.positiveBuses parameters.drive parameters.decoder).map
    (fun input => named parameters input true)

theorem eligible_checked (parameters : Parameters)
    (K : Finset (Channel parameters.channels))
    (eligible : Admissible parameters.buses parameters.bridge.target K)
    (drive : parameters.drive = true)
    (differs : ∃ output, parameters.observations output (assignmentOfSet {parameters.bridge.target}) ≠
      parameters.observations output (assignmentOfSet K)) :
    Certificate.ModelCheck.check parameters.specificationFormula
      (named parameters (Physical.realizeBridge parameters.bridge parameters.positiveBuses K) true) = true := by
  apply named_checked
  rw [drive]
  exact (Physical.realizeBridge_detects_iff parameters.bridge parameters.positiveBuses K eligible
    parameters.observations).mpr differs

theorem detectNamed_some (parameters : Parameters) (guarded : parameters.decoder.Guarded)
    (assignment : Variable parameters → Bool)
    (returned : detectNamed parameters = some assignment) :
    Certificate.ModelCheck.check parameters.specificationFormula assignment = true := by
  obtain ⟨input, found, equality⟩ := Option.map_eq_some_iff.mp returned
  rw [← equality]
  apply named_checked
  exact Physical.detectInput_some parameters.bridge parameters.positiveBuses parameters.drive
    parameters.decoder guarded input found

end Controller.Native.Lift
