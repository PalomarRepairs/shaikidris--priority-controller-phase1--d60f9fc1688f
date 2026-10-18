module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.WrapperTreeProvenance

@[expose] public section

/-! Retained controller origins survive row lookup, transfer composition and
cofactor-preserving propagation. -/
namespace Controller.NativeProof.Wrapper.ControllerOrigins
open Controller.CNF Controller.Resolution Controller.Native Controller.Native.SourceController
open Controller.NativeProof.FoldProjection Controller.NativeProof.SourceStageCongruence
open Controller.NativeProof.SourceStagePolarity Controller.NativeProof.SourceBusSchedule
open Controller.NativeProof.SourceBusAdvance Controller.NativeProof.SourceMismatchHandles
open Controller.NativeProof.SourceFoldProvenance
variable {parameters : Parameters} {v : Nat}

theorem projection_indices_mpr_supported (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    {before after : Clause (Fin v)} {beforeBudget afterBudget : Nat}
    (clauseEqual : before = after) (budgetEqual : beforeBudget = afterBudget)
    (typeEqual : SubclauseProjection prefixState.state before beforeBudget =
      SubclauseProjection prefixState.state after afterBudget)
    (value : SubclauseProjection prefixState.state after afterBudget)
    (supported : SourceMixedSchedule.ProjectionOriginalSupport rename prefixState value) :
    SourceMixedSchedule.ProjectionOriginalSupport rename prefixState (Eq.mpr typeEqual value) := by
  subst after
  subst afterBudget
  have same : typeEqual = rfl := Subsingleton.elim _ _
  rw [same]
  exact supported

theorem mappedUnit_origin (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    {α : Type} (items : List α) (handle : α → Literal (Fin v)) (context : Clause (Fin v))
    (rows : ∀ item ∈ items, AvailableSubclause prefixState.state (context ++ [handle item]))
    (origins : ∀ item member, ResultOrigin (formula parameters).clauses.size
      (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      prefixState.steps (rows item member).row.id)
    (input : Literal (Fin v)) (present : input ∈ items.map handle) :
    ResultOrigin (formula parameters).clauses.size
      (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      prefixState.steps (TreeUnits.mappedUnit items handle context rows input present).row.id := by
  induction items with
  | nil => simp at present
  | cons item rest ih =>
    by_cases equal : input = handle item
    · subst input
      simpa only [TreeUnits.mappedUnit, SourceMixedSchedule.subclause_dite_id,
        dite_eq_left rfl, dite_true] using origins item (List.mem_cons_self ..)
    · have member := (List.mem_cons.mp present).resolve_left equal
      simpa only [TreeUnits.mappedUnit, SourceMixedSchedule.subclause_dite_id, dite_eq_right equal] using
        ih (fun old listed => rows old (List.mem_cons_of_mem _ listed))
          (fun old listed => origins old (List.mem_cons_of_mem _ listed)) member

theorem projection_indices_mp_supported (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    {before after : Clause (Fin v)} {beforeBudget afterBudget : Nat}
    (clauseEqual : before = after) (budgetEqual : beforeBudget = afterBudget)
    (typeEqual : SubclauseProjection prefixState.state before beforeBudget =
      SubclauseProjection prefixState.state after afterBudget)
    (value : SubclauseProjection prefixState.state before beforeBudget)
    (supported : SourceMixedSchedule.ProjectionOriginalSupport rename prefixState value) :
    SourceMixedSchedule.ProjectionOriginalSupport rename prefixState (Eq.mp typeEqual value) := by
  subst after
  subst afterBudget
  have same : typeEqual = rfl := Subsingleton.elim _ _
  rw [same]
  exact supported

def TransferProjectionOrigins (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    {context : Clause (Fin v)} {input output : Literal (Fin v)} {budget : Nat}
    (projection : TreeUnits.TransferProjection prefixState.state context input output budget) : Prop :=
  SourceMixedSchedule.PrefixOriginalSupport rename
    (prefixState.extend projection.state projection.steps projection.checked) ∧
  GuardedTransferOrigin rename (prefixState.extend projection.state projection.steps projection.checked)
    projection.result

theorem compose_supported (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (context : Clause (Fin v)) (a b c : Literal (Fin v))
    (first : GuardedTransfer prefixState.state context a b)
    (second : GuardedTransfer prefixState.state context b c)
    (supported : SourceMixedSchedule.PrefixOriginalSupport rename prefixState)
    (firstOrigin : GuardedTransferOrigin rename prefixState first)
    (secondOrigin : GuardedTransferOrigin rename prefixState second) :
    TransferProjectionOrigins rename prefixState (TreeUnits.compose prefixState.state context first second) := by
  cases first with
  | identity same =>
    cases same
    cases second with
    | identity another =>
      simpa only [TransferProjectionOrigins, TreeUnits.compose, SourcePrefix.extend, List.append_nil,
        GuardedTransferOrigin, TransferOrigin, SourceMixedSchedule.PrefixOriginalSupport, and_true] using supported
    | derived two =>
      simpa only [TransferProjectionOrigins, TreeUnits.compose, SourcePrefix.extend, List.append_nil,
        GuardedTransferOrigin, TransferOrigin, SourceMixedSchedule.PrefixOriginalSupport] using
        (show SourceMixedSchedule.PrefixOriginalSupport rename prefixState ∧
          ResultOrigin (formula parameters).clauses.size
            (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
            prefixState.steps two.row.id from ⟨supported, secondOrigin⟩)
  | derived one =>
    cases second with
    | identity same =>
      cases same
      simpa only [TransferProjectionOrigins, TreeUnits.compose, SourcePrefix.extend, List.append_nil,
        GuardedTransferOrigin, TransferOrigin, SourceMixedSchedule.PrefixOriginalSupport] using (show SourceMixedSchedule.PrefixOriginalSupport rename prefixState ∧
          ResultOrigin (formula parameters).clauses.size
            (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
            prefixState.steps one.row.id from ⟨supported, firstOrigin⟩)
    | derived two =>
      have actual := SourceMixedSchedule.guardedChain_supported (formula parameters).clauses.size
        (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
        prefixState.steps prefixState.state context a b c one two supported
        (SourceMixedSchedule.allowed_native_count_le rename)
        (SourceMixedSchedule.prefix_native_count_le rename prefixState) firstOrigin secondOrigin
      simpa only [TransferProjectionOrigins, TreeUnits.compose, SourcePrefix.extend,
        SourceMixedSchedule.PrefixOriginalSupport, GuardedTransferOrigin, TransferOrigin] using actual

theorem composePairs_supported (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (context : Clause (Fin v)) (a b c : Literal (Fin v))
    (first : DirectionPair prefixState.state context a b)
    (second : DirectionPair prefixState.state context b c)
    (supported : SourceMixedSchedule.PrefixOriginalSupport rename prefixState)
    (firstOrigin : DirectionPairOrigin rename prefixState first)
    (secondOrigin : DirectionPairOrigin rename prefixState second) :
    PairedProjectionOriginalSupport rename prefixState
      (TreeUnits.composePairs prefixState.state context first second) := by
  let forward := TreeUnits.compose prefixState.state context first.forward second.forward
  let current := prefixState.extend forward.state forward.steps forward.checked
  have forwardOrigins := compose_supported rename prefixState context a b c
    first.forward second.forward supported firstOrigin.1 secondOrigin.1
  have secondBack := GuardedTransferOrigin.afterTrace rename prefixState second.backward secondOrigin.2
    forward.state forward.steps forward.checked
  have firstBack := GuardedTransferOrigin.afterTrace rename prefixState first.backward firstOrigin.2
    forward.state forward.steps forward.checked
  let backward := TreeUnits.compose forward.state context
    (second.backward.afterTrace forward.state forward.steps forward.checked)
    (first.backward.afterTrace forward.state forward.steps forward.checked)
  have backwardOrigins := compose_supported rename current context c b a
    (second.backward.afterTrace forward.state forward.steps forward.checked)
    (first.backward.afterTrace forward.state forward.steps forward.checked)
    forwardOrigins.1 secondBack firstBack
  have carried := GuardedTransferOrigin.afterTrace rename current forward.result forwardOrigins.2
    backward.state backward.steps backward.checked
  let actual := TreeUnits.composePairs prefixState.state context first second
  let combined := prefixState.extend actual.state actual.steps actual.checked
  have same : (current.extend backward.state backward.steps backward.checked).steps = combined.steps :=
    List.append_assoc ..
  have forwardFinal := GuardedTransferOrigin.same_steps rename backward.state
    (current.extend backward.state backward.steps backward.checked).steps combined.steps same
    (current.extend backward.state backward.steps backward.checked).checked combined.checked
    (forward.result.afterTrace backward.state backward.steps backward.checked) carried
  have backwardFinal := GuardedTransferOrigin.same_steps rename backward.state
    (current.extend backward.state backward.steps backward.checked).steps combined.steps same
    (current.extend backward.state backward.steps backward.checked).checked combined.checked
    backward.result backwardOrigins.2
  refine ⟨?_, forwardFinal, backwardFinal⟩
  simpa only [SourceMixedSchedule.PrefixOriginalSupport, combined, actual,
    TreeUnits.composePairs, current, forward, backward, SourcePrefix.extend, List.append_assoc] using backwardOrigins.1

theorem contextualDirection_origin (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (prior steps : List (Step v)) (same : prefixState.steps = prior ++ steps)
    (context : Clause (Fin v)) (certificate : DirectionalCertificate prefixState.state root input)
    (origin : CertificateOrigin (formula parameters).clauses.size
      (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename) steps certificate) :
    GuardedTransferOrigin rename prefixState (TreeUnits.contextualDirection context certificate) := by
  cases certificate with
  | identity equal => trivial
  | derived available =>
    change ResultOrigin (formula parameters).clauses.size
      (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      prefixState.steps available.row.id
    rw [same]
    exact resultOrigin_append_left _ _ prior steps available.row.id origin

theorem reduceToInput_supported (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (tree : AndTree prefixState.state root inputs) (context : Clause (Fin v))
    (input : Literal (Fin v)) (member : input ∈ inputs)
    (units : ∀ other ∈ inputs, other ≠ input →
      AvailableSubclause prefixState.state (context ++ [other]))
    (supported : SourceMixedSchedule.PrefixOriginalSupport rename prefixState)
    (original : SourceFoldProvenance.TreeOriginals
      (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename) tree)
    (unitOrigins : ∀ other present different, ResultOrigin (formula parameters).clauses.size
      (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      prefixState.steps (units other present different).row.id) :
    PairedProjectionOriginalSupport rename prefixState
      (TreeUnits.reduceToInput tree context input member units) := by
  cases tree with
  | leaf =>
    simpa only [PairedProjectionOriginalSupport, TreeUnits.reduceToInput, DirectionPairOrigin,
      GuardedTransferOrigin, TransferOrigin, SourcePrefix.extend, SourceMixedSchedule.PrefixOriginalSupport,
      List.append_nil, true_and, and_true] using supported
  | @node leftRoot rightRoot leftInputs rightInputs left right root rows =>
    let tree := AndTree.node left right root rows
    let projected := projectTreeLong tree
    have two : 2 ≤ (leftInputs ++ rightInputs).length := by
      have one := left.nodes_leaves
      have other := right.nodes_leaves
      simp only [List.length_append]
      omega
    let row := nonunaryAggregate projected.result two
    let known := fun other present different =>
      afterTrace (units other present different) projected.state projected.steps projected.checked
    let rest := (leftInputs ++ rightInputs).filter fun other => other ≠ input
    let target := context ++ [negate input, root]
    let parent : AvailableSubclause projected.state (rest.map negate ++ target) := retarget row (by
      intro literal present
      rcases List.mem_cons.mp present with same | old
      · exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (by simp [same]))))
      · obtain ⟨other, listed, same⟩ := List.mem_map.mp old
        by_cases equal : other = input
        · subst other
          exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (by simp [same.symm]))))
        · exact List.mem_append.mpr (Or.inl (List.mem_map.mpr
            ⟨other, List.mem_filter.mpr ⟨listed, by simpa using equal⟩, same⟩)))
    let propagation : ∀ other ∈ rest, AvailableSubclause projected.state (target ++ [other]) :=
      fun other listed => retarget
        (known other (List.mem_filter.mp listed).1 (by simpa using (List.mem_filter.mp listed).2)) (by
          intro literal present
          simp only [target, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at present ⊢
          aesop)
    let eliminated := dischargeInputs projected.state rest target parent propagation
    let afterLong := prefixState.extend projected.state projected.steps projected.checked
    have longOrigins := aggregate_long_supported rename prefixState tree two supported original
    have eliminatedOrigins := dischargeInputs_supported rename afterLong rest target parent propagation
      longOrigins.1 longOrigins.2 (fun other listed => resultOrigin_append_right _ _
        prefixState.steps projected.steps _ (unitOrigins other (List.mem_filter.mp listed).1
          (by simpa using (List.mem_filter.mp listed).2)))
    have localRun : runSteps prefixState.state (projected.steps ++ eliminated.steps) = some eliminated.state := by
      rw [runSteps_append, projected.checked]
      exact eliminated.checked
    let current := prefixState.extend eliminated.state (projected.steps ++ eliminated.steps) localRun
    let treeNow := tree.afterTrace eliminated.state (projected.steps ++ eliminated.steps) localRun
    let directions := projectTreeInputs treeNow
    have treeOrigins := SourceFoldProvenance.treeOriginals_afterTrace
      (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename) tree original
      eliminated.state (projected.steps ++ eliminated.steps) localRun
    have directionOrigins := SourceFoldProvenance.projectTreeInputs_supported treeNow
      (formula parameters).clauses.size (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      treeOrigins (SourceMixedSchedule.allowed_native_count_le rename)
      (SourceMixedSchedule.prefix_native_count_le rename current)
    have currentSupport : SourceMixedSchedule.PrefixOriginalSupport rename current := by
      simpa only [current, afterLong, SourcePrefix.extend, SourceMixedSchedule.ProjectionOriginalSupport,
        SourceMixedSchedule.PrefixOriginalSupport, List.append_assoc] using eliminatedOrigins.1
    have finalSupport := SourceMixedSchedule.traceOriginalSupport_append _ _ current.steps directions.steps
      currentSupport directionOrigins.1
    have backwardOrigin := SourceFoldProvenance.resultOrigin_append_right _ _ current.steps directions.steps
      eliminated.result.row.id (by
        simpa only [current, afterLong, SourcePrefix.extend, List.append_assoc] using eliminatedOrigins.2)
    let actual := TreeUnits.reduceToInput tree context input member units
    let final := prefixState.extend actual.state actual.steps actual.checked
    unfold PairedProjectionOriginalSupport TreeUnits.reduceToInput
    dsimp only [id]
    refine ⟨?_, ?_, ?_⟩
    · simpa only [current, treeNow, tree, projected, parent, propagation, eliminated,
        known, rest, target, row, directions, SourcePrefix.extend,
        SourceMixedSchedule.PrefixOriginalSupport, List.append_assoc] using finalSupport
    · have lifted := contextualDirection_origin rename
        (current.extend directions.state directions.steps directions.checked) current.steps directions.steps rfl
        context (directions.results input member) (directionOrigins.2 input member)
      have same : (current.extend directions.state directions.steps directions.checked).steps = final.steps :=
        List.append_assoc ..
      let transfer := TreeUnits.contextualDirection context (directions.results input member)
      have transferred : TransferOrigin (formula parameters).clauses.size
          (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename) final.steps transfer := by
        rw [← same]
        simpa only [GuardedTransferOrigin, transfer, SourcePrefix.extend] using lifted
      simpa only [GuardedTransferOrigin, transfer, final, actual, TreeUnits.reduceToInput, current, treeNow, tree, projected,
        parent, propagation, eliminated, known, rest, target, row, directions, SourcePrefix.extend] using transferred
    · simpa only [GuardedTransferOrigin, TransferOrigin, current, treeNow, tree, projected, parent, propagation,
        eliminated, known, rest, target, row, directions, afterTrace, SourcePrefix.extend,
        List.append_assoc] using backwardOrigin

end Controller.NativeProof.Wrapper.ControllerOrigins
