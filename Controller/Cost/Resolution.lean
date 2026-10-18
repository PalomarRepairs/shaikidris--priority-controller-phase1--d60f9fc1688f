module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.Compiler
public import Controller.Resolution.Cases
public import Controller.Decoder.ForestTraversal
public import Mathlib.Data.Fintype.Card
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

public import Mathlib.Tactic.Ring

@[expose] public section

/-! Native ordinary-resolution accounting. Selector schema counts, injective
primary allocation, paid decoder incidences and local case expansion are
separate measures. The complete stored refutation uses a positive-handle
quotient for Horn queries and is bounded before pruning. Derived width and
literal occurrences are proved separately from machine storage and runtime. -/
namespace Controller.Cost.NativeResolution
open Controller Controller.CNF Controller.Resolution Controller.Resolution.Cases
open Controller.Native Controller.Native.SourceController
open Controller.NativeProof
open Controller.NativeProof.SourceStageCongruence Controller.NativeProof.SourceFoldProjection
set_option maxRecDepth 8192

/-- For later stage `j = offset + 2`, there are `j` guard implications
and one suffix clause per channel. Repeated incidences are counted. -/
def selectorLayerCount (laterStages : Nat) : Nat :=
  ((List.range laterStages).map fun offset => offset + 3).sum

theorem selectorLayerCount_double (laterStages : Nat) :
    2 * selectorLayerCount laterStages = laterStages * (laterStages + 5) := by
  induction laterStages with
  | zero => simp [selectorLayerCount]
  | succ stages ih =>
    have next : selectorLayerCount (stages + 1) = selectorLayerCount stages + stages + 3 := by
      simp [selectorLayerCount, List.range_succ, List.map_append, List.sum_append, Nat.add_assoc]
    rw [next]
    nlinarith

theorem selectorLayerCount_le (laterStages : Nat) :
    selectorLayerCount laterStages ≤ laterStages * (laterStages + 2) := by
  have double := selectorLayerCount_double laterStages
  have square := Nat.le_mul_self laterStages
  nlinarith

/-- Appendix B selector macro schema. One bus uses the target-unit case;
multiple buses include two descending flag clauses per stage. This counts
the schema, not the concrete compiler's entire emitted proof. -/
def selectorSchemaCount (channels buses : Nat) : Nat :=
  if buses = 1 then 1 else channels * selectorLayerCount (buses - 1) + 2 * buses

@[simp] theorem selectorSchemaCount_one (channels : Nat) : selectorSchemaCount channels 1 = 1 := by
  simp [selectorSchemaCount]

theorem selectorSchemaCount_many (channels buses : Nat) (many : 1 < buses) :
    selectorSchemaCount channels buses = channels * (buses - 1) * (buses + 4) / 2 + 2 * buses := by
  have double := selectorLayerCount_double (buses - 1)
  have successor : buses - 1 + 5 = buses + 4 := by omega
  rw [successor] at double
  have numerator : channels * (buses - 1) * (buses + 4) =
      (channels * selectorLayerCount (buses - 1)) * 2 := by
    calc
      _ = channels * ((buses - 1) * (buses + 4)) := by ring
      _ = channels * (2 * selectorLayerCount (buses - 1)) := congrArg (channels * ·) double.symm
      _ = _ := by ring
  simp [selectorSchemaCount, show buses ≠ 1 by omega, numerator]

/-- Any injective placement of every enable and request slot charges
`n(b+1)` distinct variables. No clause-occurrence assumption is required. -/
theorem primary_slots_le {channels buses variablesCount : Nat}
    (place : InterfaceAlias.Root channels buses → Fin variablesCount)
    (injective : Function.Injective place) : channels * (buses + 1) ≤ variablesCount := by
  have counted := Fintype.card_le_of_injective
    (place ∘ (SourceInitialIDs.rootIndex (n := channels) (b := buses)).symm)
    (injective.comp (SourceInitialIDs.rootIndex (n := channels) (b := buses)).symm.injective)
  simpa [Nat.mul_add, Nat.mul_one, Nat.add_comm] using counted

theorem source_root_bounded (parameters : Parameters)
    (root : InterfaceAlias.Root parameters.channels parameters.buses) :
    SourceInitialIDs.rootID root ≤ (compile parameters).lastID := by
  have index := (SourceInitialIDs.rootIndex root).isLt
  rw [compile_lastID_source_count]
  unfold SourceInitialIDs.rootID SourceInitialIDs.rootCount
  omega

/-- The actual canonical finite encoding preserves the primary-root injection. -/
theorem canonical_primary_injective (parameters : Parameters) :
    Function.Injective (fun root : InterfaceAlias.Root parameters.channels parameters.buses =>
      NativeProof.Compiler.canonicalRename parameters (SourceInitialIDs.rootID root)) := by
  intro left right equal
  apply SourceInitialIDs.rootID_injective
  have leftValue := NativeProof.Compiler.canonicalRename_allocated (parameters := parameters)
    (SourceInitialIDs.rootID left) (source_root_bounded parameters left)
  have rightValue := NativeProof.Compiler.canonicalRename_allocated (parameters := parameters)
    (SourceInitialIDs.rootID right) (source_root_bounded parameters right)
  simpa only [leftValue, rightValue] using congrArg Fin.val equal

theorem canonical_primary_slots_le (parameters : Parameters) :
    parameters.channels * (parameters.buses + 1) ≤ NativeProof.Compiler.variableCount parameters :=
  primary_slots_le _ (canonical_primary_injective parameters)

theorem selectorSchemaCount_quadratic (channels buses variableCount : Nat)
    (nonzero : 0 < channels) (positive : 0 < buses)
    (allocated : channels * (buses + 1) ≤ variableCount) :
    selectorSchemaCount channels buses ≤ 3 * variableCount ^ 2 := by
  have product : channels * buses ≤ variableCount := by
    nlinarith
  have busProduct : buses ≤ channels * buses := by
    simpa using Nat.mul_le_mul_right buses (show 1 ≤ channels by omega)
  have busBound : buses ≤ variableCount := busProduct.trans product
  have variablePositive : 0 < variableCount := by omega
  have square := Nat.le_mul_self variableCount
  unfold selectorSchemaCount
  split
  · nlinarith
  · have stages : buses - 1 + 1 = buses := by omega
    have layer := selectorLayerCount_le (buses - 1)
    have layerBound : selectorLayerCount (buses - 1) ≤ buses ^ 2 := by nlinarith
    have scaled := Nat.mul_le_mul_left channels layerBound
    have charged := Nat.mul_le_mul product busBound
    have same : channels * buses ^ 2 = (channels * buses) * buses := by ring
    rw [same] at scaled
    nlinarith

theorem canonical_selectorSchemaCount_quadratic (parameters : Parameters) :
    selectorSchemaCount parameters.channels parameters.buses ≤
      3 * (NativeProof.Compiler.variableCount parameters) ^ 2 :=
  selectorSchemaCount_quadratic _ _ _
    (by have := parameters.bridge.two_le; omega) parameters.positiveBuses
    (canonical_primary_slots_le parameters)

/-- Decoder incidences surviving source alias elimination. Input nodes,
unary ORs and empty guards allocate no gate and contribute zero. Repeated
children and repeated guard labels retain their full list multiplicities. -/
def paidNodeIncidences (parameters : Parameters) (node : Fin parameters.decoder.nodeCount) : Nat :=
  match parameters.decoder.node node with
  | .zero | .input _ => 0
  | .disj children => if children.length ≤ 1 then 0 else children.length
  | .guard _ labels => labels.length
  | .liveAnd _ _ => 2

theorem paidNodeIncidences_le (parameters : Parameters) (node : Fin parameters.decoder.nodeCount) :
    paidNodeIncidences parameters node ≤ 2 * sourceDecoderNodeProducerCost parameters node := by
  cases shape : parameters.decoder.node node with
  | zero => simp [paidNodeIncidences, sourceDecoderNodeProducerCost, shape]
  | input channel => simp [paidNodeIncidences, sourceDecoderNodeProducerCost, shape]
  | guard child labels => simp [paidNodeIncidences, sourceDecoderNodeProducerCost, shape]; omega
  | liveAnd left right => simp [paidNodeIncidences, sourceDecoderNodeProducerCost, shape]
  | disj children =>
    simp only [paidNodeIncidences, sourceDecoderNodeProducerCost, shape, sourceFoldProducerCount]
    split <;> split <;> omega

def paidDecoderIncidences (parameters : Parameters) : Nat :=
  ((List.finRange parameters.decoder.nodeCount).map (paidNodeIncidences parameters)).sum

theorem paidDecoderIncidences_producers (parameters : Parameters) :
    paidDecoderIncidences parameters ≤ 2 * sourceDecoderProducerCost parameters := by
  have total (nodes : List (Fin parameters.decoder.nodeCount)) :
      (nodes.map (paidNodeIncidences parameters)).sum ≤
        2 * (nodes.map (sourceDecoderNodeProducerCost parameters)).sum := by
    induction nodes with
    | nil => simp
    | cons node rest ih =>
      have current := paidNodeIncidences_le parameters node
      simp only [List.map_cons, List.sum_cons]
      omega
  exact total _

/-- Both native decoder copies pay for the flattened incidence bank. This
uses the actual source producer count, rather than the number of syntax nodes. -/
theorem paidDecoderIncidences_source (parameters : Parameters) :
    paidDecoderIncidences parameters ≤ sourceCompileProducerCost parameters := by
  have actual := paidDecoderIncidences_producers parameters
  unfold sourceCompileProducerCost
  omega

theorem canonical_paidDecoderIncidences_le (parameters : Parameters) :
    paidDecoderIncidences parameters ≤ NativeProof.Compiler.variableCount parameters := by
  have actual := paidDecoderIncidences_source parameters
  unfold NativeProof.Compiler.variableCount
  rw [compile_lastID_source_count]
  omega

/-- Expand every case tree in order, retaining all emitted inferences. The
next tree starts in the preceding tree's resulting proof state. -/
def caseSchedule (state : State v) : List (CaseTree v) → List (Step v)
  | [] => []
  | tree :: rest =>
    let built := compileTree state tree
    built.steps ++ caseSchedule built.state rest

theorem caseSchedule_count (state : State v) (trees : List (CaseTree v))
    (depth : ∀ tree ∈ trees, DepthBound 5 tree)
    (reasons : ∀ tree ∈ trees, ReasonsBound v tree) :
    (caseSchedule state trees).length ≤ trees.length * (32 * v + 31) := by
  induction trees generalizing state with
  | nil => simp [caseSchedule]
  | cons tree rest ih =>
    have current := compileTree_depth_budget 5 v tree state
      (depth tree (by simp)) (reasons tree (by simp))
    have later := ih (compileTree state tree).state
      (fun next member => depth next (List.mem_cons_of_mem _ member))
      (fun next member => reasons next (List.mem_cons_of_mem _ member))
    simp only [caseSchedule, List.length_append, List.length_cons]
    norm_num only at current
    nlinarith

/-- A quadratic bound on the full stored macro schedule gives a cubic
inference bound. This theorem does not supply the native macro-count premise. -/
theorem caseSchedule_cubic (state : State v) (trees : List (CaseTree v))
    (depth : ∀ tree ∈ trees, DepthBound 5 tree)
    (reasons : ∀ tree ∈ trees, ReasonsBound v tree)
    (size constant : Nat) (positive : 0 < size) (variableBound : v ≤ size)
    (macros : trees.length ≤ constant * size ^ 2) :
    (caseSchedule state trees).length ≤ 63 * constant * size ^ 3 := by
  have localBound : 32 * v + 31 ≤ 63 * size := by omega
  calc
    _ ≤ trees.length * (32 * v + 31) := caseSchedule_count state trees depth reasons
    _ ≤ (constant * size ^ 2) * (63 * size) := Nat.mul_le_mul macros localBound
    _ = 63 * constant * size ^ 3 := by ring

/-- Concrete canonical variable charging for a selector-schema-sized bank.
The full compiler also stores preparation and decoder-summary banks. -/
theorem canonical_selectorCaseSchedule_cubic (parameters : Parameters)
    (state : State (NativeProof.Compiler.variableCount parameters))
    (trees : List (CaseTree (NativeProof.Compiler.variableCount parameters)))
    (depth : ∀ tree ∈ trees, DepthBound 5 tree)
    (reasons : ∀ tree ∈ trees, ReasonsBound (NativeProof.Compiler.variableCount parameters) tree)
    (macros : trees.length ≤ selectorSchemaCount parameters.channels parameters.buses) :
    (caseSchedule state trees).length ≤
      189 * (NativeProof.Compiler.variableCount parameters) ^ 3 := by
  have positive : 0 < NativeProof.Compiler.variableCount parameters := by
    unfold NativeProof.Compiler.variableCount
    omega
  simpa only [Nat.mul_one, Nat.reduceMul] using
    caseSchedule_cubic state trees depth reasons (NativeProof.Compiler.variableCount parameters) 3
      positive (Nat.le_refl _) (macros.trans (canonical_selectorSchemaCount_quadratic parameters))

theorem derived_width_le {state next : State v} {step : Step v}
    (accepted : applyStep state step = some next) : step.clause.length ≤ 2 * v := by
  obtain ⟨left, right, _, _, valid, _⟩ := applyStep_success accepted
  have counted := valid.2.2.2.2.2.1.length_le_card
  simpa only [Literal, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, Nat.mul_comm] using counted

/-- This charges all derived rows in an accepted schedule, including unused
rows. Original clauses, row identifiers and machine-word/byte storage are
separate measures. Tautological derived clauses are allowed by the checker. -/
theorem derived_literal_count {state next : State v} {steps : List (Step v)}
    (accepted : runSteps state steps = some next) :
    (steps.map fun step => step.clause.length).sum ≤ steps.length * (2 * v) := by
  induction steps generalizing state with
  | nil => simp
  | cons step rest ih =>
    simp only [runSteps] at accepted
    cases current : applyStep state step with
    | none => simp [current] at accepted
    | some middle =>
      simp only [current] at accepted
      have width := derived_width_le current
      have later := ih accepted
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      nlinarith

theorem derived_literal_count_quartic {state next : State v} {steps : List (Step v)}
    (accepted : runSteps state steps = some next) (size constant : Nat)
    (variableBound : v ≤ size) (inferences : steps.length ≤ constant * size ^ 3) :
    (steps.map fun step => step.clause.length).sum ≤ 2 * constant * size ^ 4 := by
  calc
    _ ≤ steps.length * (2 * v) := derived_literal_count accepted
    _ ≤ (constant * size ^ 3) * (2 * size) := Nat.mul_le_mul inferences (by omega)
    _ = 2 * constant * size ^ 4 := by ring

section MaskAccounting
open Controller.NativeProof
open Controller.NativeProof.FoldProjection Controller.NativeProof.SourceFoldProjection
open Controller.NativeProof.SourceMismatchSeed Controller.NativeProof.SourceMismatchAdvance
open Controller.NativeProof.SourceHealthyMasks Controller.NativeProof.SourceBusSchedule
open Controller.NativeProof.SourceBusAdvance Controller.NativeProof.SourceStageCongruence
open Controller.NativeProof.SourceRoleFrames Controller.NativeProof.SourceFoldOccurrences
open Controller.NativeProof.SourceFoldOwners
variable {parameters : Parameters} {v : Nat}

theorem sum_map_bound (items : List α) (cost : α → Nat) (bound : Nat)
    (bounded : ∀ item ∈ items, cost item ≤ bound) :
    (items.map cost).sum ≤ items.length * bound := by
  induction items with
  | nil => simp
  | cons item rest ih =>
    have current := bounded item (by simp)
    have later := ih (fun old member => bounded old (List.mem_cons_of_mem _ member))
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    nlinarith

theorem groupInputs_length_le (group : Group) :
    (groupInputs (parameters := parameters) group).length ≤ parameters.channels := by
  cases group with
  | drivers => simpa only [groupInputs, driverInputs, List.length_map, Finset.length_sort, Fintype.card_fin]
      using Finset.card_le_univ parameters.bridge.drivers
  | remaining => simpa only [groupInputs, remainingInputs, List.length_map, Finset.length_sort, Fintype.card_fin]
      using Finset.card_le_univ parameters.bridge.remaining

theorem absenceCost_bound (rename : Nat → Fin v) (channel : Fin parameters.channels) :
    absenceCost (parameters := parameters) rename channel ≤ 2 * parameters.channels + 2 := by
  unfold absenceCost
  split
  · omega
  · have tree := (groupTree (parameters := parameters) rename (otherGroup channel)
        (otherGroup_nonempty channel ‹_›)).nodes_leaves
    have inputs := groupInputs_length_le (parameters := parameters) (otherGroup channel)
    simp only [List.length_map] at tree
    omega

theorem initialMasks_count (rename : Nat → Fin v) (drive : parameters.drive = true) :
    (SourceHealthyMasks.initial rename drive).proofPrefix.steps.length ≤
      2 * parameters.channels ^ 2 + 4 * parameters.channels := by
  have first := (allOtherAbsences (parameters := parameters) rename).count
  have total := sum_map_bound
    ((List.finRange parameters.channels).filter (fun channel => decide (channel ≠ parameters.bridge.target)))
    (absenceCost rename) (2 * parameters.channels + 2) (fun channel _ => absenceCost_bound rename channel)
  have length := List.length_filter_le (fun channel : Fin parameters.channels => decide (channel ≠ parameters.bridge.target))
    (List.finRange parameters.channels)
  simp only [List.length_finRange] at length
  have product := Nat.mul_le_mul_right (2 * parameters.channels + 2) length
  have second := allFirstMasks_count rename drive
  change ((allOtherAbsences rename).steps ++ (allFirstMasks rename drive).steps).length ≤ _
  rw [List.length_append]
  nlinarith

theorem laterTermInputs_length_le (position : Fin (laterBuses (parameters := parameters)).length)
    (channel : Fin parameters.channels) :
    (laterTermInputs (parameters := parameters) .healthy position channel).length ≤ parameters.buses + 2 := by
  have bounded := List.length_filter_le
    (fun earlier : Fin parameters.buses => earlier < (laterBuses (parameters := parameters))[position.val])
    (List.finRange parameters.buses)
  simp only [List.length_finRange] at bounded
  simpa only [laterTermInputs, List.length_append, List.length_cons, List.length_nil, List.length_map] using
    (show 2 + ((List.finRange parameters.buses).filter
      (fun earlier => earlier < (laterBuses (parameters := parameters))[position.val])).length ≤ parameters.buses + 2 by omega)

theorem otherTerm_count (rename : Nat → Fin v)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (table : SourceHealthyMasks.Table (parameters := parameters) rename position.val)
    (channel : Fin parameters.channels) (different : channel ≠ parameters.bridge.target) :
    (otherTerm rename position table channel different).steps.length ≤ 2 * parameters.buses + 5 := by
  have actual := (otherTerm rename position table channel different).count
  have nodes := (laterTermTree (parameters := parameters) rename .healthy position channel).nodes_leaves
  have inputs := laterTermInputs_length_le position channel
  simp only [List.length_map] at nodes
  omega

theorem collectOtherTerms_count (rename : Nat → Fin v)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (table : SourceHealthyMasks.Table (parameters := parameters) rename position.val) (channels : List (Fin parameters.channels)) :
    (collectOtherTerms rename position table channels).steps.length ≤
      channels.length * (2 * parameters.buses + 5) := by
  induction channels generalizing table with
  | nil => simp [collectOtherTerms]
  | cons channel rest ih =>
    by_cases same : channel = parameters.bridge.target
    · simpa only [collectOtherTerms, dite_eq_left same, List.length_cons] using
        (ih table).trans (by nlinarith)
    · have current := otherTerm_count rename position table channel same
      have later := ih (table.afterTrace (otherTerm rename position table channel same).state
        (otherTerm rename position table channel same).steps (otherTerm rename position table channel same).checked)
      simp only [collectOtherTerms, dite_eq_right same, List.length_append, List.length_cons]
      nlinarith

theorem advanceMasks_count (rename : Nat → Fin v)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (table : SourceHealthyMasks.Table (parameters := parameters) rename position.val)
    (drive : parameters.drive = true) :
    (SourceHealthyMasks.advance rename position table drive).proofPrefix.steps.length ≤
      table.proofPrefix.steps.length + 50 * (parameters.channels + 1) * (parameters.buses + 1) := by
  change (table.proofPrefix.steps ++ (currentTargetMask rename position table drive).steps).length ≤ _
  rw [List.length_append]
  exact Nat.add_le_add_left (currentTargetMask rename position table drive).count _

theorem buildMasks_count (rename : Nat → Fin v) (drive : parameters.drive = true)
    (count : Nat) (bound : count ≤ (laterBuses (parameters := parameters)).length) :
    (buildPrefix rename drive count bound).proofPrefix.steps.length ≤
      2 * parameters.channels ^ 2 + 4 * parameters.channels +
        count * (50 * (parameters.channels + 1) * (parameters.buses + 1)) := by
  induction count with
  | zero => simpa only [buildPrefix, Nat.zero_mul, Nat.add_zero] using initialMasks_count rename drive
  | succ count ih =>
    have previous := ih (by omega)
    have current := advanceMasks_count rename ⟨count, by omega⟩
      (buildPrefix rename drive count (by omega)) drive
    change (SourceHealthyMasks.advance rename ⟨count, by omega⟩
      (buildPrefix rename drive count (by omega)) drive).proofPrefix.steps.length ≤ _
    simp only [Nat.add_mul, Nat.one_mul]
    omega

theorem allMasks_count (rename : Nat → Fin v) (drive : parameters.drive = true) :
    (SourceHealthyMasks.allMasks rename drive).proofPrefix.steps.length ≤
      2 * parameters.channels ^ 2 + 4 * parameters.channels +
        parameters.buses * (50 * (parameters.channels + 1) * (parameters.buses + 1)) := by
  have actual := buildMasks_count rename drive (laterBuses (parameters := parameters)).length (Nat.le_refl _)
  have length : (laterBuses (parameters := parameters)).length ≤ parameters.buses := by
    simpa only [laterBuses, List.length_finRange] using
      List.length_filter_le (fun bus : Fin parameters.buses => bus.val != 0) (List.finRange parameters.buses)
  exact actual.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ length) _)

end MaskAccounting

section PreparationAccounting
open Controller.NativeProof Controller.NativeProof.FoldProjection
open Controller.NativeProof.SourceHealthyOne Controller.NativeProof.SourceDecoderTraversal
open Controller.NativeProof.SourceHealthyMasks Controller.NativeProof.SourceHealthyQualifiers
variable {parameters : Parameters} {v : Nat}

def healthyQualifierBudget (parameters : Parameters) : Nat :=
  2 * parameters.channels ^ 2 + 4 * parameters.channels +
    parameters.buses * (50 * (parameters.channels + 1) * (parameters.buses + 1)) +
    parameters.channels * (6 * parameters.buses + 63)

theorem healthyQualifiersSize (rename : Nat → Fin v) (drive : parameters.drive = true) :
    (allQualifiers (parameters := parameters) rename drive).table.proofPrefix.steps.length ≤
      healthyQualifierBudget parameters := by
  unfold allQualifiers
  rw [buildQualifiers_prefix, List.length_append]
  have masks := allMasks_count rename drive
  have added := buildQualifiersSize rename (allMasks rename drive) drive (List.finRange parameters.channels)
  simp only [List.length_finRange] at added
  exact Nat.add_le_add masks added

def mixedBudget (parameters : Parameters) : Nat :=
  parameters.buses * (2 * parameters.channels + parameters.channels *
    (SourceMixedSchedule.qualifierBudget parameters + 1)) + 5 * parameters.buses + 3

def preparationBudget (parameters : Parameters) : Nat :=
  healthyQualifierBudget parameters + 8 * sourceDecoderProducerCost parameters + mixedBudget parameters +
    (3 * parameters.buses + 4)

theorem optionalTargetSize (rename : Nat → Fin v) (start : SourcePrefix (parameters := parameters) rename)
    (drive : parameters.drive = true) :
    (optionalTarget rename start drive).steps.length ≤ 3 * parameters.buses + 4 := by
  unfold optionalTarget
  split
  · dsimp only
    have actual := (oneBusTarget rename start drive (by assumption)).count
    have nodes := qualifierTreeSize rename .faulty parameters.bridge.target
    omega
  · simp

theorem preparationSize (rename : Nat → Fin v) (drive : parameters.drive = true)
    (guarded : parameters.decoder.Guarded) :
    (prepare rename drive guarded).proofPrefix.steps.length ≤ preparationBudget parameters := by
  let healthy := SourceDecoderEvaluation.healthy rename drive guarded
  let forwards := SourceForwardRows.allRows rename .faulty (cofactor (parameters := parameters) rename) guarded healthy.proofPrefix
  let activation := compiledMixedActivation rename drive
  let replay := replayNativeProgram rename forwards.proofPrefix activation.state activation.steps activation.checked
  let target := optionalTarget rename replay.prefix drive
  have qualifiers := healthyQualifiersSize rename drive
  change (SourceDecoderEvaluation.healthySeed rename drive).proofPrefix.steps.length ≤ _ at qualifiers
  have evaluated := SourceDecoderEvaluation.healthySize rename drive guarded
  change healthy.proofPrefix.steps.length ≤ _ at evaluated
  have forward := SourceForwardRows.buildSize rename .faulty (cofactor (parameters := parameters) rename)
    guarded healthy.proofPrefix parameters.decoder.nodeCount (Nat.le_refl _)
  unfold SourceDecoderEvaluation.evaluationPrefixCost at forward
  rw [List.take_of_length_le (by simp)] at forward
  change forwards.proofPrefix.steps.length ≤ healthy.proofPrefix.steps.length +
    4 * sourceDecoderProducerCost parameters at forward
  have activated := activation.count
  have replayCount := replay.added_length
  have targetCount := optionalTargetSize rename replay.prefix drive
  change target.steps.length ≤ _ at targetCount
  change (forwards.proofPrefix.steps ++ replay.added ++ target.steps).length ≤ _
  simp only [List.length_append]
  unfold preparationBudget
  change activation.steps.length ≤ mixedBudget parameters at activated
  omega

def drivenInitialBudget (parameters : Parameters) : Nat :=
  preparationBudget parameters + 28 * sourceDecoderProducerCost parameters +
    SourceQualifierSchedule.qualifierProgramBudget parameters + 2

theorem initialDrivenSize (rename : Nat → Fin v) (drive : parameters.drive = true)
    (guarded : parameters.decoder.Guarded) :
    (Compiler.initialDriven rename drive guarded).summaries.prepared.proofPrefix.steps.length ≤
      drivenInitialBudget parameters := by
  let prepared := prepare rename drive guarded
  let summaries := SourceSupportSummaries.allSummaries rename guarded prepared
  let equal := equalDecoderProgram (parameters := parameters) rename true
  let replay := replayNativeProgram rename summaries.prepared.proofPrefix equal.table.prefixState.state
    equal.table.prefixState.steps equal.table.prefixState.checked
  let extended := summaries.afterTrace replay.next replay.added replay.checked
  let physical := SourceMismatchHandles.healthyFlagUnit rename drive
  let final := replayNativeProgram rename extended.prepared.proofPrefix physical.state physical.steps physical.checked
  have preparedCount := preparationSize rename drive guarded
  change prepared.proofPrefix.steps.length ≤ _ at preparedCount
  have summarized := SourceSupportSummaries.buildSize rename guarded prepared parameters.decoder.nodeCount (Nat.le_refl _)
  unfold SourceDecoderEvaluation.evaluationPrefixCost at summarized
  rw [List.take_of_length_le (by simp)] at summarized
  change summaries.prepared.proofPrefix.steps.length ≤ prepared.proofPrefix.steps.length +
    4 * sourceDecoderProducerCost parameters at summarized
  have equalCount := equalDecoderProgramSize (parameters := parameters) rename true
  change equal.table.prefixState.steps.length ≤ _ at equalCount
  have copied := replay.added_length
  have fixed := final.added_length
  have physicalCount := physical.count
  change (summaries.prepared.proofPrefix.steps ++ replay.added ++ final.added).length ≤ _
  simp only [List.length_append]
  unfold drivenInitialBudget
  omega

end PreparationAccounting

section NativeQuotient
open Controller.NativeProof Controller.NativeProof.FoldProjection
open Controller.NativeProof.HornNativeReplay
variable {u v : Nat}

def positiveHandles : Fin v → Literal (Fin v) := fun index => (index, true)

theorem liftClause_positive_quotient (handles : Fin u → Literal (Fin v))
    (positive : ∀ index, (handles index).2 = true) (row : Clause (Fin u)) :
    liftClause positiveHandles (Rows.mapClause (fun index => (handles index).1) row) =
      liftClause handles row := by
  unfold liftClause Rows.mapClause
  rw [List.map_map]
  apply List.map_congr_left
  intro literal member
  rcases literal with ⟨index, phase⟩
  cases equal : handles index with
  | mk label bit =>
    have same : bit = true := by simpa only [equal] using positive index
    subst bit
    cases phase <;> simp [liftLiteral, positiveHandles, equal]

/-- Quotienting syntactic aliases by their native positive handles preserves
each original-row certificate and each explicitly discharged assumption. -/
def quotientOrigin (handles : Fin u → Literal (Fin v))
    (positive : ∀ index, (handles index).2 = true) (state : State v)
    (target : Clause (Fin v)) (row : Clause (Fin u))
    (origin : HornRowTransport.Origin handles state target row) :
    HornRowTransport.Origin positiveHandles state target
      (Rows.mapClause (fun index => (handles index).1) row) := by
  cases origin with
  | native available =>
    apply HornRowTransport.Origin.native
    rw [liftClause_positive_quotient handles positive]
    exact available
  | identity first second shape same =>
    apply HornRowTransport.Origin.identity (handles first).1 (handles second).1
    · simp [shape, Rows.mapClause]
    · exact congrArg (fun literal => (literal.1, true)) same
  | assumption literal shape negative discharged =>
    apply HornRowTransport.Origin.assumption ((handles literal.1).1, literal.2)
    · simp [shape, Rows.mapClause]
    · exact negative
    · have equal := liftClause_positive_quotient handles positive [literal]
      simp only [Rows.mapClause, liftClause, List.map_cons, List.map_nil, List.cons.injEq] at equal
      rw [equal.1]
      exact discharged

end NativeQuotient

section CompactHealthyQuery
open Controller.NativeProof Controller.NativeProof.FoldProjection
open Controller.NativeProof.SourceHealthyOne Controller.NativeProof.SourceDecoderTraversal
open Controller.NativeProof.SourceDecoderEvaluation Controller.NativeProof.HornNativeReplay
variable {parameters : Parameters} {v : Nat}

theorem healthyHandles_positive (rename : Nat → Fin v)
    (index : Fin (parameters.channels + parameters.decoder.nodeCount)) :
    (SourceHealthyOneQuery.handles (parameters := parameters) rename index).2 = true := by
  unfold SourceHealthyOneQuery.handles SourceForwardRows.handle
  cases parameters.decoder.zeroIndex.symm index with
  | inl channel =>
    have actual := sourceRoleMap_positive parameters (.internal (.qualifier .faulty channel))
    rw [compiled_faulty_qualifier_slot] at actual
    exact actual
  | inr node =>
    have actual := sourceRoleMap_positive parameters (.internal (.decoder .faulty node))
    have equal : mapLiteral rename (sourceRoleMap parameters (.internal (.decoder .faulty node))) =
        outputLiteral rename .faulty node := by
      rw [compiled_decoder_slot, decoderComplete_slot]
      exact stored_eq_output rename .faulty parameters.decoder.nodeCount (Nat.le_refl _) node node.isLt
    exact (congrArg (fun literal => literal.2) equal).symm.trans actual

def healthyNativeFormula (rename : Nat → Fin v) (root : Fin parameters.decoder.nodeCount) : FiniteFormula v :=
  relabel (fun index => (SourceHealthyOneQuery.handles (parameters := parameters) rename index).1)
    (parameters.decoder.finiteZeroSystem parameters.buses parameters.bridge.target root ∅ ∅)

def healthyNativeRows (rename : Nat → Fin v) (prepared : Preparation (parameters := parameters) rename)
    (root : Fin parameters.decoder.nodeCount) :
    ∀ index : Fin (healthyNativeFormula rename root).clauses.size,
      HornRowTransport.Origin positiveHandles prepared.proofPrefix.state
        (cofactor (parameters := parameters) rename ++ [SourceForwardRows.handle rename .faulty (.inr root)])
        (healthyNativeFormula rename root).clauses[index.val] := by
  intro index
  have bound : index.val <
      (parameters.decoder.finiteZeroSystem parameters.buses parameters.bridge.target root ∅ ∅).clauses.size := by
    simpa only [healthyNativeFormula, relabel, Controller.CNF.OrderedFormula.relabel, Array.size_map] using index.isLt
  simpa only [healthyNativeFormula, relabel, Controller.CNF.OrderedFormula.relabel, Array.getElem_map,
    Controller.CNF.OrderedFormula.Clause.relabel, Rows.mapClause] using
    quotientOrigin _ (healthyHandles_positive rename) _ _ _
      (SourceHealthyOneQuery.finiteRows rename prepared root ⟨index.val, bound⟩)

def healthyNativeQuery (rename : Nat → Fin v) (prepared : Preparation (parameters := parameters) rename)
    (guarded : parameters.decoder.Guarded) (selected : Finset (Fin parameters.decoder.roots.length))
    (absent : Decoder.NoDiscrepancy parameters selected)
    (output : Fin parameters.decoder.roots.length) (accepted : output ∈ selected)
    (healthy : parameters.observations output (Controller.assignmentOfSet {parameters.bridge.target}) = true) :
    SubclauseProjection prepared.proofPrefix.state
      (cofactor (parameters := parameters) rename ++ [SourceForwardRows.handle rename .faulty (.inr (parameters.decoder.roots.get output))])
      v := by
  let root := parameters.decoder.roots.get output
  let formula := healthyNativeFormula rename root
  have unsatOriginal : Unsatisfiable
      (parameters.decoder.finiteZeroSystem parameters.buses parameters.bridge.target root ∅ ∅) := by
    apply (unsatisfiable_relabel_iff parameters.decoder.zeroIndex.injective _).mpr
    exact Decoder.healthyOne_zeroSystem_unsatisfiable parameters guarded selected absent output accepted healthy
  have unsat : Unsatisfiable formula := by
    intro ⟨assignment, model⟩
    exact unsatOriginal ⟨_, (satisfies_relabel _ _ _).mp model⟩
  have restricted : Horn.DualHorn formula :=
    Decoder.SparseFormula.relabel_dualHorn _ _
      (parameters.decoder.finiteZeroSystem_dualHorn guarded _ _ _ _ _)
  have complete := HornTrail.produce_complete formula restricted unsat
  exact match returned : HornTrail.produce formula with
  | .none => False.elim (by obtain ⟨conflict, run, _, _⟩ := complete; simp [returned] at run)
  | .some conflict => by
    have certified : HornTrail.Certified formula conflict := by
      obtain ⟨result, run, proof, bound⟩ := complete
      have same : result = conflict := Option.some.inj (run.symm.trans returned)
      exact same ▸ proof
    have bound : conflict.reasons.length ≤ v := by
      obtain ⟨result, run, proof, bound⟩ := complete
      have same : result = conflict := Option.some.inj (run.symm.trans returned)
      exact same ▸ bound
    have positive := HornTrail.scan_conflict_positive formula _ _ _ conflict returned
    let replayed := HornRowTransport.replay formula conflict certified positive positiveHandles
      prepared.proofPrefix.state (cofactor (parameters := parameters) rename ++ [SourceForwardRows.handle rename .faulty (.inr root)])
      (healthyNativeRows rename prepared root)
    exact ⟨replayed.state, replayed.steps, replayed.checked, replayed.result, replayed.count.trans bound⟩

def healthyNativeEquality (rename : Nat → Fin v) (prepared : Preparation (parameters := parameters) rename)
    (guarded : parameters.decoder.Guarded) (selected : Finset (Fin parameters.decoder.roots.length))
    (absent : Decoder.NoDiscrepancy parameters selected)
    (output : Fin parameters.decoder.roots.length) (accepted : output ∈ selected)
    (healthy : parameters.observations output (Controller.assignmentOfSet {parameters.bridge.target}) = true) :
    SourceBusAdvance.PairedProjection prepared.proofPrefix.state (cofactor (parameters := parameters) rename)
      (nativeRootLiteral rename .healthy output) (nativeRootLiteral rename .faulty output) v := by
  let actual := healthyNativeQuery rename prepared guarded selected absent output accepted healthy
  have faulty : AvailableSubclause actual.state (cofactor (parameters := parameters) rename ++
      [nativeRootLiteral rename .faulty output]) := by
    simpa only [SourceHealthyOneQuery.rootHandle, SourceForwardRows.handle, Sum.elim_inr] using actual.result
  have healthyRow : AvailableSubclause actual.state (cofactor (parameters := parameters) rename ++
      [nativeRootLiteral rename .healthy output]) := by
    have bit : parameters.decoder.eval (Controller.assignmentOfSet {parameters.bridge.target})
        (parameters.decoder.roots.get output) = true := healthy
    simpa only [bit, SourceStageXor.valueLiteral, ite_true, SourceHealthyOneQuery.rootHandle] using
      FoldProjection.afterTrace (prepared.healthy (parameters.decoder.roots.get output)) actual.state actual.steps actual.checked
  refine ⟨actual.state, actual.steps, actual.checked, ⟨.derived (retarget faulty ?_), .derived (retarget healthyRow ?_)⟩, actual.count⟩
  · intro literal member
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member ⊢
    aesop
  · intro literal member
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member ⊢
    aesop

end CompactHealthyQuery

section FullPrefix
open Controller.NativeProof Controller.NativeProof.FoldProjection
open Controller.NativeProof.SourceHealthyOne Controller.NativeProof.SourceDecoderTraversal
open Controller.NativeProof.SourceBusSchedule Controller.NativeProof.SourceBusAdvance
open Controller.NativeProof.Compiler
variable {parameters : Parameters} {v : Nat}

/-- The native-variable query is used in every selected healthy-one cofactor.
All emitted steps remain in the stored prefix. -/
def compactMixed (rename : Nat → Fin v) (guarded : parameters.decoder.Guarded)
    (absent : Decoder.NoDiscrepancy parameters Finset.univ)
    (prepared : SourceSupportSummaries.Table (parameters := parameters) rename parameters.decoder.nodeCount)
    (output : Fin parameters.decoder.roots.length) :
    PairedProjection prepared.prepared.proofPrefix.state (cofactor (parameters := parameters) rename)
      (nativeRootLiteral rename .healthy output) (nativeRootLiteral rename .faulty output) v := by
  if healthy : parameters.observations output (Controller.assignmentOfSet {parameters.bridge.target}) = true then
    exact healthyNativeEquality rename prepared.prepared guarded Finset.univ absent output (by simp) healthy
  else
    let actual := SourceSupportSummaries.equality rename prepared guarded Finset.univ absent output (by simp)
      (Bool.eq_false_of_not_eq_true healthy)
    exact ⟨actual.state, actual.steps, actual.checked, actual.pair, actual.count.trans (Nat.zero_le _)⟩

def compactAdvanceDriven (rename : Nat → Fin v) (guarded : parameters.decoder.Guarded)
    (absent : Decoder.NoDiscrepancy parameters Finset.univ) (count : Nat)
    (before : count < parameters.decoder.roots.length)
    (table : DrivenTable (parameters := parameters) rename count) :
    DrivenTable (parameters := parameters) rename (count + 1) := by
  let output : Fin parameters.decoder.roots.length := ⟨count, before⟩
  let mixed := compactMixed rename guarded absent table.summaries output
  let current := table.afterTrace mixed.state mixed.steps mixed.checked
  have one : DirectionPair mixed.state
      [negate (nativeHealthyFirstFlag (parameters := parameters) rename), negate (nativeFaultyFirstFlag (parameters := parameters) rename)]
      (nativeRootLiteral rename .healthy output) (nativeRootLiteral rename .faulty output) := by
    simpa only [current, DrivenTable.afterTrace, SourceSupportSummaries.Table.afterTrace, Preparation.afterTrace, SourcePrefix.extend, equalFlagContext, SourceCongruence.assignmentGuard, ite_true, nativeHealthyFirstFlag, nativeFaultyFirstFlag] using current.equalOne output
  have zero : DirectionPair mixed.state
      [negate (nativeHealthyFirstFlag (parameters := parameters) rename), nativeFaultyFirstFlag (parameters := parameters) rename]
      (nativeRootLiteral rename .healthy output) (nativeRootLiteral rename .faulty output) := mixed.pair
  let final := dischargePair mixed.state _ _ _ _ one zero current.healthyFlag
  let extended := current.afterTrace final.state final.steps final.checked
  refine { extended with pairs := ?_ }
  intro query bound
  if same : query = output then exact same ▸ final.pair
  else
    have earlier : query.val < count := by
      have different : query.val ≠ count := fun h => same (Fin.ext h)
      omega
    exact extended.pairs query earlier

def compactBuildDriven (rename : Nat → Fin v) (drive : parameters.drive = true)
    (guarded : parameters.decoder.Guarded) (absent : Decoder.NoDiscrepancy parameters Finset.univ) :
    (count : Nat) → count ≤ parameters.decoder.roots.length → DrivenTable (parameters := parameters) rename count
  | 0, _ => initialDriven rename drive guarded
  | count + 1, bound => compactAdvanceDriven rename guarded absent count (by omega)
      (compactBuildDriven rename drive guarded absent count (by omega))

theorem compactAdvanceDrivenSize (rename : Nat → Fin v) (guarded : parameters.decoder.Guarded)
    (absent : Decoder.NoDiscrepancy parameters Finset.univ) (count : Nat)
    (before : count < parameters.decoder.roots.length)
    (table : DrivenTable (parameters := parameters) rename count) :
    (compactAdvanceDriven rename guarded absent count before table).summaries.prepared.proofPrefix.steps.length ≤
      table.summaries.prepared.proofPrefix.steps.length + v + 4 := by
  unfold compactAdvanceDriven
  dsimp only
  simp only [DrivenTable.afterTrace, SourceSupportSummaries.Table.afterTrace, Preparation.afterTrace,
    SourcePrefix.extend]
  rw [List.length_append, List.length_append]
  apply (Nat.add_le_add_left (dischargePair _ _ _ _ _ _ _ _).count _).trans
  have actual := (compactMixed rename guarded absent table.summaries ⟨count, before⟩).count
  omega

theorem compactBuildDrivenSize (rename : Nat → Fin v) (drive : parameters.drive = true)
    (guarded : parameters.decoder.Guarded) (absent : Decoder.NoDiscrepancy parameters Finset.univ)
    (count : Nat) (bound : count ≤ parameters.decoder.roots.length) :
    (compactBuildDriven rename drive guarded absent count bound).summaries.prepared.proofPrefix.steps.length ≤
      drivenInitialBudget parameters + count * (v + 4) := by
  induction count with
  | zero => simpa only [compactBuildDriven, Nat.zero_mul, Nat.add_zero] using initialDrivenSize rename drive guarded
  | succ count ih =>
    have previous := ih (by omega)
    have next := compactAdvanceDrivenSize rename guarded absent count (by omega)
      (compactBuildDriven rename drive guarded absent count (by omega))
    change (compactBuildDriven rename drive guarded absent (count + 1) bound).summaries.prepared.proofPrefix.steps.length ≤ _ at next
    change _ ≤ drivenInitialBudget parameters + (count + 1) * (v + 4)
    rw [Nat.add_mul, Nat.one_mul]
    omega

def compactOutputPrefix (rename : Nat → Fin v) (raw : parameters.layout = .raw)
    (guarded : parameters.decoder.Guarded) (unsat : Unsatisfiable (formula parameters)) :
    Compiler.EqualityPrefix (parameters := parameters) rename := by
  if drive : parameters.drive = true then
    let absent := Decoder.source_unsat_noDiscrepancy parameters raw drive unsat Finset.univ
    let table := compactBuildDriven rename drive guarded absent parameters.decoder.roots.length (Nat.le_refl _)
    exact ⟨table.summaries.prepared.proofPrefix, fun output => table.pairs output output.isLt⟩
  else
    have zero : parameters.drive = false := Bool.eq_false_of_not_eq_true drive
    exact ⟨driveZeroOutputPrefix rename zero, driveZeroOutputRoot rename zero⟩

theorem driveZeroPhysicalSize (rename : Nat → Fin v) (drive : parameters.drive = false) :
    (driveZeroPhysicalPrefix rename drive).steps.length ≤
      SourceQualifierSchedule.qualifierProgramBudget parameters + 24 * sourceDecoderProducerCost parameters + 4 := by
  have base := equalDecoderProgramSize (parameters := parameters) rename true
  have healthy : (driveZeroHealthyReplay rename drive).added.length ≤ 2 := by
    rw [(driveZeroHealthyReplay rename drive).added_length]
    simpa only [driveZeroFlagPrefix, SourcePrefix.extend, SourcePrefix.initial, List.nil_append] using
      (driveZeroFlagSource rename drive .healthy).count
  have faulty : (driveZeroFaultyReplay rename drive).added.length ≤ 2 := by
    rw [(driveZeroFaultyReplay rename drive).added_length]
    simpa only [driveZeroFlagPrefix, SourcePrefix.extend, SourcePrefix.initial, List.nil_append] using
      (driveZeroFlagSource rename drive .faulty).count
  simp only [driveZeroPhysicalPrefix, NativeReplay.prefix, SourcePrefix.extend, List.length_append]
  change (driveZeroEqualPrefix (parameters := parameters) rename).steps.length +
      (driveZeroHealthyReplay rename drive).added.length +
      (driveZeroFaultyReplay rename drive).added.length ≤ _
  exact (Nat.add_le_add (Nat.add_le_add base healthy) faulty).trans (by omega)

theorem driveZeroOutputSize (rename : Nat → Fin v) (drive : parameters.drive = false) :
    (driveZeroOutputPrefix rename drive).steps.length ≤
      SourceQualifierSchedule.qualifierProgramBudget parameters + 24 * sourceDecoderProducerCost parameters +
        4 + 4 * parameters.decoder.roots.length := by
  have base := driveZeroPhysicalSize rename drive
  have suffix := buildDriveZeroOutputs_count rename drive parameters.decoder.roots.length (Nat.le_refl _)
  change ((driveZeroPhysicalPrefix rename drive).steps ++ (driveZeroOutputProgram rename drive).steps).length ≤ _
  rw [List.length_append]
  exact Nat.add_le_add base suffix

def outputBudget (parameters : Parameters) (variableCount : Nat) : Nat :=
  drivenInitialBudget parameters + parameters.decoder.roots.length * (variableCount + 4) +
    SourceQualifierSchedule.qualifierProgramBudget parameters + 24 * sourceDecoderProducerCost parameters +
      4 + 4 * parameters.decoder.roots.length

theorem compactOutputSize (rename : Nat → Fin v) (raw : parameters.layout = .raw)
    (guarded : parameters.decoder.Guarded) (unsat : Unsatisfiable (formula parameters)) :
    (compactOutputPrefix rename raw guarded unsat).proofPrefix.steps.length ≤ outputBudget parameters v := by
  unfold compactOutputPrefix
  split
  · dsimp only
    have actual := compactBuildDrivenSize rename (by assumption) guarded
      (Decoder.source_unsat_noDiscrepancy parameters raw (by assumption) unsat Finset.univ)
      parameters.decoder.roots.length (Nat.le_refl _)
    exact actual.trans (by unfold outputBudget; omega)
  · dsimp only
    have actual := driveZeroOutputSize rename (Bool.eq_false_of_not_eq_true (by assumption))
    exact actual.trans (by unfold outputBudget; omega)

def compactRefute (rename : Nat → Fin v) (raw : parameters.layout = .raw)
    (guarded : parameters.decoder.Guarded) (unsat : Unsatisfiable (formula parameters)) :
    Refutation (parameters := parameters) rename := by
  let equalities := compactOutputPrefix rename raw guarded unsat
  let differences := buildDifferences rename equalities parameters.decoder.roots.length (Nat.le_refl _)
  let negative := detectionNegative rename differences
  let current := differences.equalities.proofPrefix.extend negative.state negative.steps negative.checked
  let assertion := afterTrace (ofRow (detectedAssertion (parameters := parameters) rename))
    current.state current.steps current.checked
  let final := longMerge current.state (detectedLiteral (parameters := parameters) rename) [] [] negative.result assertion
  let result := longMerge_result current.state (detectedLiteral (parameters := parameters) rename) [] [] negative.result assertion
  have empty : result.clause = [] := by
    have subset := result.subset
    cases shape : result.clause with
    | nil => rfl
    | cons head tail => exact False.elim (by have bad := subset head (by rw [shape]; simp); simpa using bad)
  have row : Rows.Available final.state [] :=
    ⟨result.row.id, by simpa only [empty] using result.row.present, result.row.bound⟩
  exact ⟨current.extend final.state final.steps (longMerge_run _ _ _ _ _ _), row⟩

theorem eraseDupsLength (items : List (Fin v)) : items.eraseDups.length ≤ items.length := by
  suffices universal : ∀ size, ∀ input : List (Fin v), input.length = size → input.eraseDups.length ≤ input.length by
    exact universal items.length items rfl
  intro size
  induction size using Nat.strong_induction_on with
  | h size ih =>
    intro input equal
    cases input with
    | nil => simp
    | cons item rest =>
      rw [List.eraseDups_cons, List.length_cons, List.length_cons]
      apply Nat.succ_le_succ
      have filtered := List.length_filter_le (fun other => !other == item) rest
      have small : (rest.filter (fun other => !other == item)).length < size := by
        simp only [List.length_cons] at equal
        omega
      exact (ih _ small _ rfl).trans filtered

theorem equalXorSize (state : State v) (a b output : Literal (Fin v))
    (rows : SourceStageXor.XorRows state a b output) (pair : DirectionPair state [] a b) :
    (equalXor state a b output rows pair).steps.length ≤ 65535 := by
  let premises := XorUnits.xorPremises (context := []) rows ++ XorUnits.pairPremises pair
  have flattened : (premises.flatMap fun row => LocalUnitCases.labelsOf row.clause).length ≤ 16 := by
    rcases pair with ⟨forward, backward⟩
    cases forward <;> cases backward <;>
      simp [premises, XorUnits.xorPremises, XorUnits.pairPremises, XorUnits.transferPremises,
        XorUnits.contextual, LocalUnitCases.labelsOf, List.flatMap_append]
  have filtered := List.length_filter_le (fun label => label ≠ (negate output).1)
    (premises.flatMap fun row => LocalUnitCases.labelsOf row.clause).eraseDups
  have unique := eraseDupsLength (premises.flatMap fun row => LocalUnitCases.labelsOf row.clause)
  have length : (LocalUnitCases.allVariables premises (negate output)).length ≤ 16 :=
    filtered.trans (unique.trans flattened)
  have exponent := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : Nat)) length
  norm_num at exponent
  have actual := (equalXor state a b output rows pair).count
  change _ ≤ 2 ^ (LocalUnitCases.allVariables premises (negate output)).length - 1 at actual
  omega

theorem differenceStepSize (rename : Nat → Fin v) (count : Nat)
    (before : count < parameters.decoder.roots.length)
    (table : DifferenceTable (parameters := parameters) rename count) :
    (differenceStep rename count before table).equalities.proofPrefix.steps.length ≤
      table.equalities.proofPrefix.steps.length + 65535 := by
  let output : Fin parameters.decoder.roots.length := ⟨count, before⟩
  let original := SourceStageXor.xorRowsOriginal _ _ _ (observationDifferenceOriginalRows parameters rename output)
  let rows := original.afterTrace table.equalities.proofPrefix.state table.equalities.proofPrefix.steps
    table.equalities.proofPrefix.checked
  have actual := equalXorSize table.equalities.proofPrefix.state _ _ _ rows (table.equalities.pairs output)
  change (table.equalities.proofPrefix.steps ++ _).length ≤ _
  rw [List.length_append]
  exact Nat.add_le_add_left actual _

theorem buildDifferencesSize (rename : Nat → Fin v) (equalities : Compiler.EqualityPrefix (parameters := parameters) rename)
    (count : Nat) (bound : count ≤ parameters.decoder.roots.length) :
    (buildDifferences rename equalities count bound).equalities.proofPrefix.steps.length ≤
      equalities.proofPrefix.steps.length + 65535 * count := by
  induction count with
  | zero => simp [buildDifferences]
  | succ count ih =>
    have previous := ih (by omega)
    have next := differenceStepSize rename count (by omega) (buildDifferences rename equalities count (by omega))
    change (buildDifferences rename equalities (count + 1) bound).equalities.proofPrefix.steps.length ≤ _ at next
    exact next.trans (by
      simpa only [Nat.mul_add, Nat.mul_one, Nat.add_assoc] using Nat.add_le_add_right previous 65535)

def fullPrefixBudget (parameters : Parameters) (variableCount : Nat) : Nat :=
  outputBudget parameters variableCount + 65538 * parameters.decoder.roots.length + 1

theorem compactRefuteSize (rename : Nat → Fin v) (raw : parameters.layout = .raw)
    (guarded : parameters.decoder.Guarded) (unsat : Unsatisfiable (formula parameters)) :
    (compactRefute rename raw guarded unsat).proofPrefix.steps.length ≤ fullPrefixBudget parameters v := by
  let equalities := compactOutputPrefix rename raw guarded unsat
  let differences := buildDifferences rename equalities parameters.decoder.roots.length (Nat.le_refl _)
  let negative := detectionNegative rename differences
  let current := differences.equalities.proofPrefix.extend negative.state negative.steps negative.checked
  let assertion := afterTrace (ofRow (detectedAssertion (parameters := parameters) rename))
    current.state current.steps current.checked
  let final := longMerge current.state (detectedLiteral (parameters := parameters) rename) [] [] negative.result assertion
  have first := compactOutputSize rename raw guarded unsat
  change equalities.proofPrefix.steps.length ≤ _ at first
  have second := buildDifferencesSize rename equalities parameters.decoder.roots.length (Nat.le_refl _)
  change differences.equalities.proofPrefix.steps.length ≤ _ at second
  have third := negative.count
  simp only [detectedInputs, List.length_map, List.length_finRange] at third
  have last := longMerge_count current.state (detectedLiteral (parameters := parameters) rename) [] [] negative.result assertion
  change final.steps.length ≤ 1 at last
  change (differences.equalities.proofPrefix.steps ++ negative.steps ++ final.steps).length ≤ _
  simp only [List.length_append]
  unfold fullPrefixBudget
  omega

end FullPrefix

/-- A universal bound for the complete stored native prefix. The constant
comes from the structural inequalities, including the local case expansion;
no execution sample or pruning reduction is used. -/
theorem fullPrefixBudget_cubic (parameters : Parameters) (variableCount : Nat)
    (allocated : parameters.channels * (parameters.buses + 1) ≤ variableCount)
    (decoder : sourceDecoderProducerCost parameters ≤ variableCount)
    (outputs : parameters.decoder.roots.length ≤ variableCount) :
    fullPrefixBudget parameters variableCount ≤ 100000 * variableCount ^ 3 := by
  have channelsPositive : 1 ≤ parameters.channels := by have := parameters.bridge.two_le; omega
  have busesPositive := parameters.positiveBuses
  have channelBound : parameters.channels ≤ variableCount := by nlinarith only [allocated]
  have product : parameters.channels * parameters.buses ≤ variableCount := by nlinarith only [allocated]
  have busBound : parameters.buses ≤ variableCount :=
    (show parameters.buses ≤ parameters.channels * parameters.buses by nlinarith only [channelsPositive]).trans product
  have positive : 1 ≤ variableCount := channelsPositive.trans channelBound
  have nSquare := Nat.mul_le_mul channelBound channelBound
  have bSquare := Nat.mul_le_mul busBound busBound
  have nbSquare := Nat.mul_le_mul product busBound
  have nbCube := Nat.mul_le_mul nbSquare busBound
  have qv := Nat.mul_le_mul_right variableCount outputs
  have vSquare : variableCount ≤ variableCount ^ 2 := by nlinarith only [positive]
  have vCube : variableCount ^ 2 ≤ variableCount ^ 3 := by
    have actual := Nat.mul_le_mul_right (variableCount * variableCount) positive
    nlinarith only [actual]
  unfold fullPrefixBudget outputBudget drivenInitialBudget preparationBudget healthyQualifierBudget mixedBudget
    SourceQualifierSchedule.qualifierProgramBudget SourceQualifierSchedule.channelQualifierBudget
    SourceMixedSchedule.qualifierBudget
  nlinarith only [channelBound, product, busBound, positive, nSquare, bSquare, nbSquare, nbCube,
    qv, vSquare, vCube, decoder, outputs]

theorem canonical_fullPrefixBudget_cubic (parameters : Parameters) :
    fullPrefixBudget parameters (NativeProof.Compiler.variableCount parameters) ≤
      100000 * (NativeProof.Compiler.variableCount parameters) ^ 3 := by
  have charged : sourceCompileProducerCost parameters ≤ NativeProof.Compiler.variableCount parameters := by
    unfold NativeProof.Compiler.variableCount
    rw [compile_lastID_source_count]
    omega
  apply fullPrefixBudget_cubic parameters _ (canonical_primary_slots_le parameters)
  · unfold sourceCompileProducerCost at charged
    omega
  · unfold sourceCompileProducerCost at charged
    omega

/-- Public native-core cubic theorem for the unpruned stored refutation.
The constructor uses ordinary resolution on the original canonical CNF. -/
theorem canonical_refutation_cubic (parameters : Parameters) (raw : parameters.layout = .raw)
    (guarded : parameters.decoder.Guarded) (unsat : Unsatisfiable (formula parameters)) :
    ∃ result : NativeProof.Compiler.Refutation (parameters := parameters) (NativeProof.Compiler.canonicalRename parameters),
      check (relabel (NativeProof.Compiler.canonicalRename parameters) (formula parameters)) result.trace = true ∧
      result.proofPrefix.steps.length ≤ 100000 * (NativeProof.Compiler.variableCount parameters) ^ 3 := by
  let result := compactRefute (NativeProof.Compiler.canonicalRename parameters) raw guarded unsat
  exact ⟨result, result.checked,
    (compactRefuteSize _ raw guarded unsat).trans (canonical_fullPrefixBudget_cubic parameters)⟩

theorem canonical_derived_literal_storage (parameters : Parameters) (raw : parameters.layout = .raw)
    (guarded : parameters.decoder.Guarded) (unsat : Unsatisfiable (formula parameters)) :
    let result := compactRefute (NativeProof.Compiler.canonicalRename parameters) raw guarded unsat
    (result.proofPrefix.steps.map fun step => step.clause.length).sum ≤
      200000 * (NativeProof.Compiler.variableCount parameters) ^ 4 := by
  dsimp only
  apply derived_literal_count_quartic (compactRefute _ raw guarded unsat).proofPrefix.checked
    (NativeProof.Compiler.variableCount parameters) 100000 (Nat.le_refl _)
  exact (compactRefuteSize _ raw guarded unsat).trans (canonical_fullPrefixBudget_cubic parameters)

/-- Parameter-only frontend for the resource-bounded native construction. -/
def compactNativeCompile (parameters : Parameters) : Option (Trace (NativeProof.Compiler.variableCount parameters)) :=
  if accepted : NativeProof.Compiler.supported parameters = true then
    let hypotheses := NativeProof.Compiler.supported_iff.mp accepted
    if noDetection : parameters.decoder.detectSet parameters.buses parameters.bridge.target parameters.drive = none then
      some (compactRefute (NativeProof.Compiler.canonicalRename parameters) hypotheses.1 hypotheses.2
        (NativeProof.Compiler.unsat_of_detector_none hypotheses.1 hypotheses.2 noDetection)).trace
    else none
  else none

theorem compactNativeCompile_complete (parameters : Parameters) (raw : parameters.layout = .raw)
    (guarded : parameters.decoder.Guarded) (unsat : Unsatisfiable (formula parameters)) :
    ∃ trace, compactNativeCompile parameters = some trace ∧
      check (NativeProof.Compiler.nativeFormula parameters) trace = true ∧
      trace.steps.length ≤ 100000 * (NativeProof.Compiler.variableCount parameters) ^ 3 := by
  have accepted := NativeProof.Compiler.supported_iff.mpr ⟨raw, guarded⟩
  have none := NativeProof.Compiler.detector_none_of_unsat raw guarded unsat
  let result := compactRefute (NativeProof.Compiler.canonicalRename parameters) raw guarded unsat
  refine ⟨result.trace, ?_, result.checked, ?_⟩
  · simp only [compactNativeCompile, accepted, none, ↓reduceDIte]
    rfl
  · exact (compactRefuteSize _ raw guarded unsat).trans (canonical_fullPrefixBudget_cubic parameters)

theorem compactNativeCompile_checked (parameters : Parameters)
    (trace : Trace (NativeProof.Compiler.variableCount parameters))
    (returned : compactNativeCompile parameters = some trace) :
    check (NativeProof.Compiler.nativeFormula parameters) trace = true ∧
      trace.steps.length ≤ 100000 * (NativeProof.Compiler.variableCount parameters) ^ 3 := by
  unfold compactNativeCompile at returned
  split at returned
  · split at returned
    · cases Option.some.inj returned
      exact ⟨NativeProof.Compiler.Refutation.checked _,
        (compactRefuteSize _ _ _ _).trans (canonical_fullPrefixBudget_cubic parameters)⟩
    · simp at returned
  · simp at returned

/-- The paper's combinatorial native size: declared variables plus literal
occurrences, with multiplicities retained in every original clause. -/
def nativeEncodedSize (parameters : Parameters) : Nat :=
  NativeProof.Compiler.variableCount parameters +
    ((NativeProof.Compiler.nativeFormula parameters).clauses.toList.map List.length).sum

theorem native_refutation_encoded_cubic (parameters : Parameters) (raw : parameters.layout = .raw)
    (guarded : parameters.decoder.Guarded) (unsat : Unsatisfiable (formula parameters)) :
    ∃ result : NativeProof.Compiler.Refutation (parameters := parameters) (NativeProof.Compiler.canonicalRename parameters),
      check (NativeProof.Compiler.nativeFormula parameters) result.trace = true ∧
      result.proofPrefix.steps.length ≤ 100000 * nativeEncodedSize parameters ^ 3 := by
  obtain ⟨result, checked, count⟩ := canonical_refutation_cubic parameters raw guarded unsat
  refine ⟨result, checked, count.trans ?_⟩
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_left
  unfold nativeEncodedSize
  omega

end Controller.Cost.NativeResolution
