module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Native.SourceTransport

@[expose] public section

/-! Complete controller encoding correspondence. Named and binary-expanded
specifications support both declared prefix layouts. Transport to the concrete
source generator uses its raw layout. Counts remain separate for each encoding;
unused natural-number coordinates are excluded from source uniqueness. -/
namespace Controller.Native.EncodeCorrect
open Controller

/-- Binary expansion introduces only uniquely determined internal coordinates,
so its complete primary-input fibers are exactly the physical detecting fibers. -/
theorem bounded_extension_iff (parameters : Native.Parameters)
    (input : Physical.PrimaryInput parameters.channels parameters.buses) (wire : Bool) :
    (∃ assignment : Native.Bounded.GlobalVariable parameters → Bool,
      (∀ primary, assignment (.original (.primary primary)) = Native.Parameters.primaryAssignment input wire primary) ∧
        CNF.Satisfies assignment (Native.Bounded.globalFormula parameters)) ↔
      Physical.BridgeInputDetects parameters.bridge parameters.drive parameters.observations input wire := by
  constructor
  · rintro ⟨assignment, roots, model⟩
    exact (parameters.specification_extension_iff input wire).mp
      ⟨fun slot => assignment (.original slot), roots,
        Native.Bounded.global_model_projects parameters assignment model⟩
  · intro detects
    obtain ⟨original, roots, model⟩ := (parameters.specification_extension_iff input wire).mpr detects
    exact ⟨Native.Bounded.globalAssignment parameters original, roots,
      Native.Bounded.globalAssignment_satisfies parameters original model⟩

/-- Complete bounded gate extension is unique for every detecting physical input. -/
theorem bounded_unique_extension (parameters : Native.Parameters)
    (input : Physical.PrimaryInput parameters.channels parameters.buses) (wire : Bool)
    (detects : Physical.BridgeInputDetects parameters.bridge parameters.drive parameters.observations input wire) :
    ∃! assignment : Native.Bounded.GlobalVariable parameters → Bool,
      (∀ primary, assignment (.original (.primary primary)) = Native.Parameters.primaryAssignment input wire primary) ∧
        CNF.Satisfies assignment (Native.Bounded.globalFormula parameters) := by
  obtain ⟨original, originalModel, uniqueOriginal⟩ := parameters.specification_unique_extension input wire detects
  refine ⟨Native.Bounded.globalAssignment parameters original,
    ⟨originalModel.1, Native.Bounded.globalAssignment_satisfies parameters original originalModel.2⟩, ?_⟩
  intro assignment model
  have projection := Native.Bounded.global_model_projects parameters assignment model.2
  have equal := uniqueOriginal (fun slot => assignment (.original slot)) ⟨model.1, projection⟩
  rw [Native.Bounded.global_model_eq_assignment parameters assignment model.2, equal]

/-- Both declared named/bounded layouts have exactly the same physical model
space, including the independent wire after its interface assertions. -/
noncomputable def boundedModelsEquivDetecting (parameters : Native.Parameters) :
    Native.SourceController.BoundedIndependentWireModels parameters ≃
      Native.SourceController.SourceDetectingInputs parameters :=
  (Native.SourceController.boundedIndependentWireModelsEquiv parameters).trans
    (Native.SourceController.independentWireModelsEquivDetectingInputs parameters)

theorem bounded_model_count (parameters : Native.Parameters) :
    Nat.card (Native.SourceController.BoundedIndependentWireModels parameters) =
      Nat.card (Native.SourceController.SourceDetectingInputs parameters) :=
  Nat.card_congr (boundedModelsEquivDetecting parameters)

/-- The actual raw source allocation has the same finite complete models as
binary expansion, including arbitrary signed permutations. -/
noncomputable def boundedModelsEquivRawSource (parameters : Native.Parameters)
    (raw : parameters.layout = .raw) (rename : ℕ ≃ ℕ) (phase : ℕ → Bool) :
    Native.SourceController.BoundedIndependentWireModels parameters ≃
      Native.SourceController.SignedSourceFiniteModels parameters rename phase :=
  Native.SourceController.boundedIndependentWireModelsEquivSignedSource parameters raw rename phase

/-- A raw source fiber is inhabited exactly for a detecting input and contains
at most one allocated model. Slot zero and unallocated natural IDs are not roots. -/
theorem raw_source_fiber (parameters : Native.Parameters) (raw : parameters.layout = .raw)
    (input : Physical.PrimaryInput parameters.channels parameters.buses) :
    (Nonempty (Native.SourceController.SourceFiniteModelsFor parameters input) ↔
      Physical.BridgeInputDetects parameters.bridge parameters.drive parameters.observations input
        (Physical.bridgeD parameters.bridge input)) ∧
    Subsingleton (Native.SourceController.SourceFiniteModelsFor parameters input) :=
  ⟨Native.SourceController.sourceFiniteModelsFor_nonempty_iff parameters raw input,
    Native.SourceController.sourceFiniteModelsFor_subsingleton parameters raw input⟩

/-- Exact bounded/private and source/retained-observation counts remain distinct. -/
theorem separate_incidence_counts (parameters : Native.Parameters) :
    (Native.Bounded.globalVariables parameters).length = parameters.variableRoles.length +
      (parameters.roles.map fun owner => Native.Bounded.auxiliaryCount (parameters.gate owner)).sum ∧
    (Native.Bounded.globalFormula parameters).clauses.size =
      (parameters.roles.map fun owner => Native.Bounded.expansionRowCount (parameters.gate owner)).sum + 4 ∧
    Native.Bounded.literalIncidences (Native.Bounded.globalFormula parameters) =
      (parameters.roles.map fun owner => Native.Bounded.expansionLiteralCount (parameters.gate owner)).sum + 4 ∧
    (Native.SourceController.compile parameters).lastID = Native.SourceInitialIDs.rootCount parameters +
      Native.SourceController.sourceCompileProducerCost parameters ∧
    (Native.SourceController.formula parameters).clauses.size = Native.SourceController.sourceCompileRowCost parameters + 4 ∧
    ((Native.SourceController.formula parameters).clauses.toList.map List.length).sum =
      Native.SourceController.sourceCompileLiteralCost parameters + 4 :=
  Native.SourceController.bounded_and_source_exact_counts parameters

end Controller.Native.EncodeCorrect
