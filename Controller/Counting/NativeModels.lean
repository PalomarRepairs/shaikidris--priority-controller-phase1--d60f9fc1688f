module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Reductions.IndependentSet
public import Controller.Native.Encode
public import Controller.Native.BoundedEncode
public import Mathlib.Data.Fintype.BigOperators

@[expose] public section

/-!
# Graph-cover input multiplicities

The one-bus counting domain retains every enable, request and interface wire.
Enabled vertices form a cover, and requests at disabled vertices are free.
Complete declared assignments are counted only for the explicitly named
native specification formula.
-/

namespace Controller.Counting

open Reductions

variable {n m : ℕ}

private theorem vertex_ne_target (v : Fin n) : v.castSucc ≠ coverTarget n := by
  intro equal
  have values := congrArg Fin.val equal
  change v.val = n at values
  omega

private theorem firstBus_one (input : Physical.PrimaryInput n 1) : input.firstBus = 0 :=
  Subsingleton.elim _ _

/-- With a false flag on the sole bus, qualifiers retain every enabled channel. -/
theorem oneBus_qualifiers_false (input : Physical.PrimaryInput n 1) :
    Physical.qualifiersFromFirst input false = input.enable := by
  funext channel
  simp [Physical.qualifiersFromFirst, Physical.qualifiers, Physical.runFromFirst,
    Physical.runMasks]

/-- The source's complete primary-bit pattern, leaving disabled requests free. -/
def CoverInputPattern (input : Physical.PrimaryInput (n + 1) 1) (wire : Bool)
    (C : Finset (Fin n)) : Prop :=
  input.enable (coverTarget n) = true ∧
    input.request 0 (coverTarget n) = true ∧ wire = true ∧
    ∀ v : Fin n, input.enable v.castSucc = decide (v ∈ C) ∧
      (v ∈ C → input.request 0 v.castSucc = false)

theorem coverInputPattern_enable (input : Physical.PrimaryInput (n + 1) 1)
    (wire : Bool) (C : Finset (Fin n)) (pattern : CoverInputPattern input wire C) :
    input.enable = assignmentOfSet (coverSet C) := by
  funext channel
  refine Fin.lastCases ?_ (fun v => ?_) channel
  · change input.enable (coverTarget n) = assignmentOfSet (coverSet C) (coverTarget n)
    simpa [assignmentOfSet, coverSet] using pattern.1
  · simpa only [assignmentOfSet, coverSet_vertex] using (pattern.2.2.2 v).1

theorem coverInputPattern_firstTerms (input : Physical.PrimaryInput (n + 1) 1)
    (wire : Bool) (C : Finset (Fin n)) (pattern : CoverInputPattern input wire C) :
    Physical.firstTerms input = assignmentOfSet {coverTarget n} := by
  funext channel
  refine Fin.lastCases ?_ (fun v => ?_) channel
  · have enables : input.enable (Fin.last n) = true := pattern.1
    have requests : input.request 0 (Fin.last n) = true := pattern.2.1
    simp [Physical.firstTerms, Physical.stageTerms, firstBus_one, enables, requests,
      coverTarget, assignmentOfSet]
  · have row := pattern.2.2.2 v
    by_cases included : v ∈ C
    · simp [Physical.firstTerms, Physical.stageTerms, firstBus_one, row.1, included, row.2 included,
        assignmentOfSet, vertex_ne_target]
    · simp [Physical.firstTerms, Physical.stageTerms, firstBus_one, row.1, included,
        assignmentOfSet, vertex_ne_target]

/-- Every actual detecting input has exactly the displayed target/non-target bits. -/
theorem detecting_coverInputPattern (J : EnumeratedGraph n m) (edge : Fin m)
    (driver : Fin n) (input : Physical.PrimaryInput (n + 1) 1) (wire : Bool)
    (detects : Physical.BridgeInputDetects (coverBridge driver) true
      (coverObservation J) input wire) :
    ∃ C, J.IsCover C ∧ CoverInputPattern input wire C := by
  have changed : Physical.stageFlag input.enable (input.request input.firstBus) ≠
      Physical.bridgeFirstFlag (coverBridge driver) input wire := by
    intro equal
    exact Physical.no_observation_change_of_firstFlag_eq (coverBridge driver) input wire
      (coverObservation J) equal detects.2
  have target := Physical.separated_drive_one_target_enabled (coverBridge driver) input detects.1 changed
  have products := Physical.separated_drive_one_pattern (coverBridge driver) input detects.1 changed
  have healthyFlag := Physical.firstFlag_drive_one (coverBridge driver) input detects.1
  have faultyFlag : Physical.bridgeFirstFlag (coverBridge driver) input wire = false := by
    rw [healthyFlag] at changed
    cases h : Physical.bridgeFirstFlag (coverBridge driver) input wire <;> simp_all
  have qualifiers : Physical.bridgeQualifiers (coverBridge driver) input wire = input.enable := by
    unfold Physical.bridgeQualifiers
    rw [faultyFlag, oneBus_qualifiers_false]
  obtain ⟨C, cover, equation⟩ := cover_physical_detects_only_covers J edge driver input wire detects
  rw [qualifiers] at equation
  have enable : input.enable = assignmentOfSet (coverSet C) := by
    simpa using congrArg assignmentOfSet equation
  refine ⟨C, cover, target.1, target.2, detects.1.2.2, ?_⟩
  intro v
  have vertexEnable : input.enable v.castSucc = decide (v ∈ C) := by
    rw [enable]
    simp only [assignmentOfSet, coverSet_vertex]
  refine ⟨vertexEnable, ?_⟩
  intro included
  have zero := products.2 v.castSucc (vertex_ne_target v)
  simpa [Physical.firstTerms, Physical.stageTerms, firstBus_one, vertexEnable, included] using zero

theorem coverInputPattern_detects (J : EnumeratedGraph n m) (edge : Fin m)
    (driver : Fin n) (input : Physical.PrimaryInput (n + 1) 1) (wire : Bool)
    (C : Finset (Fin n)) (cover : J.IsCover C) (pattern : CoverInputPattern input wire C) :
    Physical.BridgeInputDetects (coverBridge driver) true (coverObservation J) input wire := by
  have products := coverInputPattern_firstTerms input wire C pattern
  have drivers : Physical.bridgeD (coverBridge driver) input = true := by
    simp [Physical.bridgeD, products, coverBridge, assignmentOfSet,
      vertex_ne_target driver]
  have remaining : Physical.bridgeR (coverBridge driver) input = true := by
    simp only [Physical.bridgeR, decide_eq_true_eq]
    intro channel membership
    have different := ((coverBridge driver).mem_remaining channel).mp membership |>.1
    change channel ≠ coverTarget n at different
    rw [products]
    simp [assignmentOfSet, different]
  have absent : Physical.bridgeU (coverBridge driver) input = false := by
    simp [Physical.bridgeU, products, assignmentOfSet, coverBridge]
  have interface : Physical.BridgeInterfaceSatisfied (coverBridge driver) input true wire := by
    exact ⟨by simpa using absent, drivers, pattern.2.2.1⟩
  have faultyFlag : Physical.bridgeFirstFlag (coverBridge driver) input wire = false := by
    simp [Physical.bridgeFirstFlag, drivers, remaining, pattern.2.2.1]
  have healthy : Physical.healthyQualifiers input = assignmentOfSet {coverTarget n} :=
    Physical.healthyQualifiers_eq_singleton_of_firstTerms input (coverTarget n) products
  have faulty : Physical.bridgeQualifiers (coverBridge driver) input wire =
      assignmentOfSet (coverSet C) := by
    unfold Physical.bridgeQualifiers
    rw [faultyFlag, oneBus_qualifiers_false, coverInputPattern_enable input wire C pattern]
  refine ⟨interface, 0, ?_⟩
  rw [healthy, faulty]
  simp only [coverObservation, setOfAssignment_assignmentOfSet]
  have legal : Admissible 1 (coverTarget n) (coverSet C) := by simp
  exact ((cover_detects_iff J edge _ legal).mpr ⟨C, cover, rfl⟩).symm

theorem cover_input_detects_iff (J : EnumeratedGraph n m) (edge : Fin m)
    (driver : Fin n) (input : Physical.PrimaryInput (n + 1) 1) (wire : Bool) :
    Physical.BridgeInputDetects (coverBridge driver) true (coverObservation J) input wire ↔
      ∃ C, J.IsCover C ∧ CoverInputPattern input wire C :=
  ⟨detecting_coverInputPattern J edge driver input wire,
    fun ⟨C, cover, pattern⟩ => coverInputPattern_detects J edge driver input wire C cover pattern⟩

abbrev FreeRequests (C : Finset (Fin n)) := {v : Fin n // v ∉ C} → Bool

theorem freeRequests_card (C : Finset (Fin n)) :
    Fintype.card (FreeRequests C) = 2 ^ (n - C.card) := by
  classical
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_subtype_compl]
  simp [Fintype.card_coe]

abbrev CoverPackets (J : EnumeratedGraph n m) := Σ C : Covers J, FreeRequests C.val

/-- Independent bits retained for each disabled vertex, with no extra assertions. -/
def packetInput (C : Finset (Fin n)) (rho : FreeRequests C) :
    Physical.PrimaryInput (n + 1) 1 where
  positiveBuses := by decide
  enable := assignmentOfSet (coverSet C)
  request := fun _ channel => Fin.lastCases true
    (fun v => if included : v ∈ C then false else rho ⟨v, included⟩) channel

theorem packetInput_pattern (C : Finset (Fin n)) (rho : FreeRequests C) :
    CoverInputPattern (packetInput C rho) true C := by
  refine ⟨by simp [packetInput, assignmentOfSet], ?_, rfl, ?_⟩
  · simp [packetInput, coverTarget]
  · intro v
    refine ⟨by simp only [packetInput, assignmentOfSet, coverSet_vertex], ?_⟩
    intro included
    simp [packetInput, included]

private theorem primaryInput_ext {a b : ℕ} (first second : Physical.PrimaryInput a b)
    (enables : first.enable = second.enable) (requests : first.request = second.request) :
    first = second := by
  cases first
  cases second
  cases enables
  cases requests
  rfl

/-- Proof fields add no counting freedom; a sole-bus input consists of two bit rows. -/
def oneBusInputEquiv (a : ℕ) :
    Physical.PrimaryInput a 1 ≃ Assignment a × Assignment a where
  toFun input := (input.enable, input.request 0)
  invFun rows := { positiveBuses := by decide, enable := rows.1, request := fun _ => rows.2 }
  left_inv input := by
    apply primaryInput_ext
    · rfl
    · funext bus
      have zero : bus = 0 := Subsingleton.elim _ _
      subst bus
      rfl
  right_inv rows := by cases rows; rfl

instance oneBusInputFintype (a : ℕ) : Fintype (Physical.PrimaryInput a 1) :=
  Fintype.ofEquiv (Assignment a × Assignment a) (oneBusInputEquiv a).symm

abbrev DetectingCoverInputs (J : EnumeratedGraph n m) (driver : Fin n) :=
  {pair : Physical.PrimaryInput (n + 1) 1 × Bool //
    Physical.BridgeInputDetects (coverBridge driver) true (coverObservation J) pair.1 pair.2}

noncomputable instance detectingCoverInputsFintype (J : EnumeratedGraph n m) (driver : Fin n) :
    Fintype (DetectingCoverInputs J driver) := Fintype.ofFinite _

def enabledCover (input : Physical.PrimaryInput (n + 1) 1) : Finset (Fin n) :=
  coverVertices (setOfAssignment input.enable)

theorem coverInputPattern_enabledCover (input : Physical.PrimaryInput (n + 1) 1)
    (wire : Bool) (C : Finset (Fin n)) (pattern : CoverInputPattern input wire C) :
    enabledCover input = C := by
  rw [enabledCover, coverInputPattern_enable input wire C pattern]
  simp

def detectedCover (J : EnumeratedGraph n m) (edge : Fin m) (driver : Fin n)
    (input : DetectingCoverInputs J driver) : Covers J :=
  ⟨enabledCover input.val.1, by
    obtain ⟨C, cover, pattern⟩ := detecting_coverInputPattern J edge driver
      input.val.1 input.val.2 input.property
    rwa [coverInputPattern_enabledCover _ _ C pattern]⟩

theorem detectedCover_pattern (J : EnumeratedGraph n m) (edge : Fin m) (driver : Fin n)
    (input : DetectingCoverInputs J driver) :
    CoverInputPattern input.val.1 input.val.2 (detectedCover J edge driver input).val := by
  obtain ⟨C, _, pattern⟩ := detecting_coverInputPattern J edge driver
    input.val.1 input.val.2 input.property
  change CoverInputPattern input.val.1 input.val.2 (enabledCover input.val.1)
  rw [coverInputPattern_enabledCover _ _ C pattern]
  exact pattern

def packetDetection (J : EnumeratedGraph n m) (edge : Fin m) (driver : Fin n)
    (packet : CoverPackets J) : DetectingCoverInputs J driver :=
  ⟨(packetInput packet.1.val packet.2, true),
    coverInputPattern_detects J edge driver _ true packet.1.val packet.1.property
      (packetInput_pattern _ _)⟩

theorem packetDetection_bijective (J : EnumeratedGraph n m) (edge : Fin m) (driver : Fin n) :
    Function.Bijective (packetDetection J edge driver) := by
  constructor
  · rintro ⟨C, rho⟩ ⟨D, sigma⟩ same
    have sets : C.val = D.val := by
      have enabled := congrArg (fun input : DetectingCoverInputs J driver =>
        enabledCover input.val.1) same
      change enabledCover (packetInput C.val rho) = enabledCover (packetInput D.val sigma) at enabled
      rw [coverInputPattern_enabledCover _ _ C.val (packetInput_pattern C.val rho),
        coverInputPattern_enabledCover _ _ D.val (packetInput_pattern D.val sigma)] at enabled
      exact enabled
    have covers : C = D := Subtype.ext sets
    subst D
    have requests : rho = sigma := by
      funext v
      have value := congrArg (fun input : DetectingCoverInputs J driver =>
        input.val.1.request 0 v.val.castSucc) same
      simpa [packetDetection, packetInput, v.property] using value
    subst sigma
    rfl
  · intro input
    let C := detectedCover J edge driver input
    let rho : FreeRequests C.val := fun v => input.val.1.request 0 v.val.castSucc
    let packet : CoverPackets J := ⟨C, rho⟩
    have pattern := detectedCover_pattern J edge driver input
    refine ⟨packet, ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · apply primaryInput_ext
      · exact (coverInputPattern_enable input.val.1 input.val.2 C.val pattern).symm
      · funext bus channel
        have zero : bus = 0 := Subsingleton.elim _ _
        subst bus
        refine Fin.lastCases ?_ (fun v => ?_) channel
        · simpa [packet, packetDetection, packetInput, coverTarget] using pattern.2.1.symm
        · by_cases included : v ∈ C.val
          · simp [packet, packetDetection, packetInput, included, (pattern.2.2.2 v).2 included]
          · simp [packet, packetDetection, packetInput, included, rho]
    · exact pattern.2.2.1.symm

noncomputable def packetDetectionEquiv (J : EnumeratedGraph n m) (edge : Fin m) (driver : Fin n) :
    CoverPackets J ≃ DetectingCoverInputs J driver :=
  Equiv.ofBijective _ (packetDetection_bijective J edge driver)

/-- Disabled request freedoms are counted once, with the interface wire fixed true. -/
theorem detecting_primary_count (J : EnumeratedGraph n m) (edge : Fin m) (driver : Fin n) :
    Fintype.card (DetectingCoverInputs J driver) =
      ∑ C : Covers J, 2 ^ (n - C.val.card) := by
  classical
  rw [← Fintype.card_congr (packetDetectionEquiv J edge driver)]
  simp only [CoverPackets, Fintype.card_sigma, freeRequests_card]

noncomputable def independencePolynomial (J : EnumeratedGraph n m) (z : ℕ) : ℕ :=
  ∑ I : IndependentSets J, z ^ I.val.card

theorem cover_weighted_sum_eq_independence (J : EnumeratedGraph n m) :
    (∑ C : Covers J, 2 ^ (n - C.val.card)) = independencePolynomial J 2 := by
  classical
  apply Fintype.sum_equiv (coverIndependentEquiv J) _ _
  intro C
  change 2 ^ (n - C.val.card) = 2 ^ (Finset.univ \ C.val).card
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  simp

theorem detecting_primary_count_independence (J : EnumeratedGraph n m) (edge : Fin m)
    (driver : Fin n) :
    Fintype.card (DetectingCoverInputs J driver) = independencePolynomial J 2 := by
  rw [detecting_primary_count J edge driver, cover_weighted_sum_eq_independence]

/-- Parameters of the named gate-equation specification, not a source-generator layout. -/
def coverParameters (J : EnumeratedGraph n m) (driver : Fin n)
    (layout : Native.PrefixLayout) : Native.Parameters where
  channels := n + 1
  buses := 1
  positiveBuses := by decide
  bridge := coverBridge driver
  decoder := coverDAG J
  layout := layout
  drive := true

theorem coverParameters_observations (J : EnumeratedGraph n m) (driver : Fin n)
    (layout : Native.PrefixLayout) :
    (coverParameters J driver layout).observations = coverObservation J := by
  change (fun output : Fin 1 => fun assignment : Assignment (n + 1) =>
    (coverDAG J).eval assignment ((coverDAG J).roots.get output)) = coverObservation J
  funext output assignment
  have zero : output = 0 := Subsingleton.elim _ _
  subst output
  change (coverDAG J).eval assignment
    ⟨m + 1, by change m + 1 < m + 2; omega⟩ = coverObservation J 0 assignment
  exact (coverObservation_eq_dag J assignment).symm

theorem coverParameters_detects_iff (J : EnumeratedGraph n m) (driver : Fin n)
    (layout : Native.PrefixLayout) (input : Physical.PrimaryInput (n + 1) 1) (wire : Bool) :
    Physical.BridgeInputDetects (coverParameters J driver layout).bridge
      (coverParameters J driver layout).drive (coverParameters J driver layout).observations
      input wire ↔ Physical.BridgeInputDetects (coverBridge driver) true
        (coverObservation J) input wire := by
  rw [coverParameters_observations]
  rfl

/-- Assignments to exactly the named specification's complete declared variable universe. -/
abbrev SpecificationModels (parameters : Native.Parameters) :=
  {assignment : Native.Variable parameters → Bool //
    CNF.Satisfies assignment parameters.specificationFormula}

noncomputable instance specificationModelsFintype (parameters : Native.Parameters) :
    Fintype (SpecificationModels parameters) := Fintype.ofFinite _

noncomputable def specificationLift (J : EnumeratedGraph n m) (driver : Fin n)
    (layout : Native.PrefixLayout) (input : DetectingCoverInputs J driver) :
    SpecificationModels (coverParameters J driver layout) :=
  let p := coverParameters J driver layout
  let detects := (coverParameters_detects_iff J driver layout input.val.1 input.val.2).mpr input.property
  let extension := p.specification_unique_extension input.val.1 input.val.2 detects
  ⟨Classical.choose extension, (Classical.choose_spec extension).1.2⟩

theorem specificationLift_roots (J : EnumeratedGraph n m) (driver : Fin n)
    (layout : Native.PrefixLayout) (input : DetectingCoverInputs J driver)
    (role : Native.PrimaryRole (n + 1) 1) :
    (specificationLift J driver layout input).val (.primary role) =
      Native.Parameters.primaryAssignment input.val.1 input.val.2 role := by
  exact (Classical.choose_spec
    ((coverParameters J driver layout).specification_unique_extension input.val.1 input.val.2
      ((coverParameters_detects_iff J driver layout input.val.1 input.val.2).mpr input.property))).1.1 role

theorem specificationLift_bijective (J : EnumeratedGraph n m) (driver : Fin n)
    (layout : Native.PrefixLayout) : Function.Bijective (specificationLift J driver layout) := by
  constructor
  · intro first second same
    have roots : Native.Parameters.primaryAssignment first.val.1 first.val.2 =
        Native.Parameters.primaryAssignment second.val.1 second.val.2 := by
      funext role
      exact (specificationLift_roots J driver layout first role).symm.trans
        ((congrArg (fun model : SpecificationModels (coverParameters J driver layout) =>
          model.val (.primary role)) same).trans (specificationLift_roots J driver layout second role))
    apply Subtype.ext
    apply Prod.ext
    · apply primaryInput_ext
      · funext channel
        exact congrArg (fun row => row (.enable channel)) roots
      · funext bus channel
        exact congrArg (fun row => row (.request bus channel)) roots
    · exact congrArg (fun row => row .wire) roots
  · intro model
    let p := coverParameters J driver layout
    let input := p.primaryInput (fun role => model.val (.primary role))
    let wire := model.val (.primary .wire)
    have detection : Physical.BridgeInputDetects (coverBridge driver) true
        (coverObservation J) input wire := by
      exact (coverParameters_detects_iff J driver layout input wire).mp
        (p.specification_model_projects model.val model.property)
    let primary : DetectingCoverInputs J driver := ⟨(input, wire), detection⟩
    refine ⟨primary, ?_⟩
    apply Subtype.ext
    have modelRoots : ∀ role, model.val (.primary role) =
        Native.Parameters.primaryAssignment input wire role := by
      intro role
      cases role <;> rfl
    have unique := (Classical.choose_spec
      (p.specification_unique_extension input wire
        ((coverParameters_detects_iff J driver layout input wire).mpr detection))).2
    exact (unique model.val ⟨modelRoots, model.property⟩).symm

noncomputable def specificationPrimaryEquiv (J : EnumeratedGraph n m) (driver : Fin n)
    (layout : Native.PrefixLayout) :
    DetectingCoverInputs J driver ≃ SpecificationModels (coverParameters J driver layout) :=
  Equiv.ofBijective _ (specificationLift_bijective J driver layout)

/-- The named specification retains exactly a cover and its disabled request bits. -/
noncomputable def specificationPacketEquiv (J : EnumeratedGraph n m) (edge : Fin m)
    (driver : Fin n) (layout : Native.PrefixLayout) :
    CoverPackets J ≃ SpecificationModels (coverParameters J driver layout) :=
  (packetDetectionEquiv J edge driver).trans (specificationPrimaryEquiv J driver layout)

/-- Exact weighted native count for the named specification only. -/
theorem specification_model_count (J : EnumeratedGraph n m) (edge : Fin m) (driver : Fin n)
    (layout : Native.PrefixLayout) :
    Fintype.card (SpecificationModels (coverParameters J driver layout)) =
      ∑ C : Covers J, 2 ^ (n - C.val.card) := by
  rw [← Fintype.card_congr (specificationPrimaryEquiv J driver layout), detecting_primary_count J edge driver]

theorem specification_model_count_independence (J : EnumeratedGraph n m) (edge : Fin m)
    (driver : Fin n) (layout : Native.PrefixLayout) :
    Fintype.card (SpecificationModels (coverParameters J driver layout)) = independencePolynomial J 2 := by
  rw [specification_model_count J edge driver layout, cover_weighted_sum_eq_independence]

/-- Complete assignments of the explicitly named global binary expansion. -/
abbrev BoundedModels (parameters : Native.Parameters) :=
  {assignment : Native.Bounded.GlobalVariable parameters → Bool //
    CNF.Satisfies assignment (Native.Bounded.globalFormula parameters)}

noncomputable instance boundedModelsFintype (parameters : Native.Parameters) :
    Fintype (BoundedModels parameters) := Fintype.ofFinite _

noncomputable def boundedLift (parameters : Native.Parameters)
    (model : SpecificationModels parameters) : BoundedModels parameters :=
  let extension := Native.Bounded.global_unique_extension parameters model.val model.property
  ⟨Classical.choose extension, (Classical.choose_spec extension).1.2⟩

theorem boundedLift_original (parameters : Native.Parameters)
    (model : SpecificationModels parameters) (slot : Native.Variable parameters) :
    (boundedLift parameters model).val (.original slot) = model.val slot := by
  exact (Classical.choose_spec
    (Native.Bounded.global_unique_extension parameters model.val model.property)).1.1 slot

theorem boundedLift_bijective (parameters : Native.Parameters) :
    Function.Bijective (boundedLift parameters) := by
  constructor
  · intro first second same
    apply Subtype.ext
    funext slot
    exact (boundedLift_original parameters first slot).symm.trans
      ((congrArg (fun model : BoundedModels parameters => model.val (.original slot)) same).trans
        (boundedLift_original parameters second slot))
  · intro model
    let original : SpecificationModels parameters :=
      ⟨fun slot => model.val (.original slot),
        Native.Bounded.global_model_projects parameters model.val model.property⟩
    refine ⟨original, ?_⟩
    apply Subtype.ext
    have unique := (Classical.choose_spec
      (Native.Bounded.global_unique_extension parameters original.val original.property)).2
    exact (unique model.val ⟨fun _ => rfl, model.property⟩).symm

/-- Binary prefix variables add no multiplicity to a complete named model. -/
noncomputable def specificationBoundedEquiv (parameters : Native.Parameters) :
    SpecificationModels parameters ≃ BoundedModels parameters :=
  Equiv.ofBijective _ (boundedLift_bijective parameters)

theorem bounded_model_count_eq_specification (parameters : Native.Parameters) :
    Fintype.card (BoundedModels parameters) = Fintype.card (SpecificationModels parameters) :=
  (Fintype.card_congr (specificationBoundedEquiv parameters)).symm

noncomputable def boundedPacketEquiv (J : EnumeratedGraph n m) (edge : Fin m)
    (driver : Fin n) (layout : Native.PrefixLayout) :
    CoverPackets J ≃ BoundedModels (coverParameters J driver layout) :=
  (specificationPacketEquiv J edge driver layout).trans
    (specificationBoundedEquiv (coverParameters J driver layout))

/-- Exact weighted count for the named binary expansion, without added wrappers. -/
theorem bounded_model_count (J : EnumeratedGraph n m) (edge : Fin m) (driver : Fin n)
    (layout : Native.PrefixLayout) :
    Fintype.card (BoundedModels (coverParameters J driver layout)) =
      ∑ C : Covers J, 2 ^ (n - C.val.card) := by
  rw [bounded_model_count_eq_specification, specification_model_count J edge driver layout]

theorem bounded_model_count_independence (J : EnumeratedGraph n m) (edge : Fin m)
    (driver : Fin n) (layout : Native.PrefixLayout) :
    Fintype.card (BoundedModels (coverParameters J driver layout)) = independencePolynomial J 2 := by
  rw [bounded_model_count J edge driver layout, cover_weighted_sum_eq_independence]

end Controller.Counting
