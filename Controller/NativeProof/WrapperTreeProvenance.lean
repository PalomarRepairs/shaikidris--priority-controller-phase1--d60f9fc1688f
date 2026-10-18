module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.WrapperControllerOrigins

@[expose] public section

/-! Controller-only provenance for native AND propagation. Identity outputs
reuse rows; all nontrivial steps are checked ordinary resolution. -/
namespace Controller.NativeProof.Wrapper.ControllerOrigins
open Controller.CNF Controller.Resolution Controller.Native Controller.Native.SourceController
open Controller.NativeProof.FoldProjection Controller.NativeProof.SourceFoldProjection
open Controller.NativeProof.SourceStageCongruence Controller.NativeProof.SourceBusSchedule
open Controller.NativeProof.SourceStagePolarity
open Controller.NativeProof.SourceBusAdvance
open Controller.NativeProof.SourceFoldProvenance Controller.NativeProof.SourceMismatchHandles
open Controller.NativeProof.SourceFoldAggregateProvenance Controller.NativeProof.SourceDecoderSchedule
open Controller.NativeProof.SourceMixedSchedule
variable {parameters : Parameters} {v : Nat}
theorem dischargeInputs_supported (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (remaining target : Clause (Fin v))
    (conflict : AvailableSubclause prefixState.state (remaining.map negate ++ target))
    (propagation : ∀ input ∈ remaining, AvailableSubclause prefixState.state (target ++ [input]))
    (supported : SourceMixedSchedule.PrefixOriginalSupport rename prefixState)
    (conflictOrigin : ResultOrigin (formula parameters).clauses.size
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      prefixState.steps conflict.row.id)
    (propagationOrigins : ∀ input member, ResultOrigin (formula parameters).clauses.size
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      prefixState.steps (propagation input member).row.id) :
    SourceMixedSchedule.ProjectionOriginalSupport rename prefixState
      (dischargeInputs prefixState.state remaining target conflict propagation) := by
  induction remaining generalizing prefixState with
  | nil =>
      have fields := dischargeInputs_nil_fields prefixState.state target conflict propagation
      unfold SourceMixedSchedule.ProjectionOriginalSupport
      rw [fields.1, fields.2, List.append_nil]
      exact ⟨supported, conflictOrigin⟩
  | cons pivot rest ih =>
      let reason : AvailableSubclause prefixState.state (pivot :: target) :=
        retarget (propagation pivot (by simp)) (by
          intro literal member
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member ⊢
          aesop)
      let adapted : AvailableSubclause prefixState.state
          (negate pivot :: (rest.map negate ++ target)) := by simpa using conflict
      have adaptedId : adapted.row.id = conflict.row.id := by
        dsimp only [adapted]
        apply subclause_cast_id
        simp only [List.map_cons, List.cons_append]
      have adaptedOrigin : ResultOrigin (formula parameters).clauses.size
          (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
          prefixState.steps adapted.row.id := by
        rw [adaptedId]
        exact conflictOrigin
      let joined := longMerge prefixState.state pivot (rest.map negate ++ target) target adapted reason
      have joinedRun := longMerge_run prefixState.state pivot
        (rest.map negate ++ target) target adapted reason
      have joinedSupport := longMerge_supported (formula parameters).clauses.size
        (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
        prefixState.steps prefixState.state pivot (rest.map negate ++ target) target adapted reason
        supported (SourceMixedSchedule.allowed_native_count_le rename) (SourceMixedSchedule.prefix_native_count_le rename prefixState)
        adaptedOrigin (propagationOrigins pivot (by simp))
      let current := prefixState.extend joined.state joined.steps joinedRun
      let merged := longMerge_result prefixState.state pivot (rest.map negate ++ target) target adapted reason
      let nextConflict : AvailableSubclause joined.state (rest.map negate ++ target) :=
        retarget merged (by
          intro literal member
          simp only [List.mem_append] at member ⊢
          aesop)
      let nextPropagation : ∀ input ∈ rest, AvailableSubclause joined.state (target ++ [input]) :=
        fun input member => afterTrace (propagation input (by simp [member]))
          joined.state joined.steps joinedRun
      have nextOrigins : ∀ input member, ResultOrigin (formula parameters).clauses.size
          (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
          current.steps (nextPropagation input member).row.id := by
        intro input member
        exact resultOrigin_append_right (formula parameters).clauses.size
          (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
          prefixState.steps joined.steps (propagation input (by simp [member])).row.id
          (propagationOrigins input (by simp [member]))
      have tailSupport := ih current nextConflict nextPropagation
        joinedSupport.1 joinedSupport.2 nextOrigins
      have fields := dischargeInputs_cons_fields prefixState.state pivot rest target conflict propagation
      unfold SourceMixedSchedule.ProjectionOriginalSupport at tailSupport ⊢
      constructor
      · rw [fields.1]
        simpa only [current, SourcePrefix.extend, List.append_assoc] using tailSupport.1
      · rw [fields.1, fields.2]
        simpa only [current, SourcePrefix.extend, List.append_assoc] using tailSupport.2

theorem aggregate_long_supported {parameters : Parameters}
    (rename : Nat → Fin v) (proofPrefix : SourcePrefix (parameters := parameters) rename)
    (tree : AndTree proofPrefix.state root inputs) (two : 2 ≤ inputs.length)
    (supported : SourceMixedSchedule.PrefixOriginalSupport rename proofPrefix)
    (original : TreeOriginals (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename) tree) :
    TraceOriginalSupport (formula parameters).clauses.size
      (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      (proofPrefix.steps ++ (projectTreeLong tree).steps) ∧
      ResultOrigin (formula parameters).clauses.size
        (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
        (proofPrefix.steps ++ (projectTreeLong tree).steps)
        (nonunaryAggregate (projectTreeLong tree).result two).row.id := by
  have actual := projectTreeLong_supported proofPrefix.state tree (formula parameters).clauses.size
    (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename) proofPrefix.steps
    original supported (SourceMixedSchedule.allowed_native_count_le rename)
    (SourceMixedSchedule.prefix_native_count_le rename proofPrefix)
  exact ⟨actual.1, SourceDecoderSchedule.nonunaryAggregate_origin _ _ _ _ two actual.2⟩

theorem tree_force_supported {parameters : Parameters}
    (rename : Nat → Fin v) (proofPrefix : SourcePrefix (parameters := parameters) rename)
    (tree : AndTree proofPrefix.state root inputs) (context : Clause (Fin v))
    (units : ∀ input ∈ inputs, AvailableSubclause proofPrefix.state (context ++ [input]))
    (supported : SourceMixedSchedule.PrefixOriginalSupport rename proofPrefix)
    (original : TreeOriginals (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename) tree)
    (unitOrigins : ∀ input member, ResultOrigin (formula parameters).clauses.size
      (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename) proofPrefix.steps
      (units input member).row.id) :
    SourceMixedSchedule.ProjectionOriginalSupport rename proofPrefix (TreeUnits.force tree context units) := by
  cases tree with
  | leaf =>
    unfold SourceMixedSchedule.ProjectionOriginalSupport
    simp only [TreeUnits.force, List.append_nil]
    exact ⟨supported, unitOrigins root (by simp)⟩
  | @node leftRoot rightRoot leftInputs rightInputs left right root rows =>
    let tree := AndTree.node left right root rows
    have two : 2 ≤ (leftInputs ++ rightInputs).length := by
      have one := left.nodes_leaves; have other := right.nodes_leaves
      simp only [List.length_append]; omega
    let projected := projectTreeLong tree
    let row := nonunaryAggregate projected.result two
    have projectionSupport := aggregate_long_supported rename proofPrefix tree two supported original
    let current := proofPrefix.extend projected.state projected.steps projected.checked
    let known := fun input member => afterTrace (units input member) projected.state projected.steps projected.checked
    let parent : AvailableSubclause projected.state ((leftInputs ++ rightInputs).map negate ++ (context ++ [root])) :=
      retarget row (by
        intro literal member
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member ⊢
        aesop)
    let propagation : ∀ input ∈ leftInputs ++ rightInputs,
        AvailableSubclause projected.state ((context ++ [root]) ++ [input]) := fun input member => retarget (known input member) (by
      intro literal present
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at present ⊢
      aesop)
    have final := dischargeInputs_supported rename current (leftInputs ++ rightInputs)
      (context ++ [root]) parent propagation projectionSupport.1 projectionSupport.2
      (fun input member => resultOrigin_append_right _ _ proofPrefix.steps projected.steps _ (unitOrigins input member))
    have fields := force_node_fields left right root rows context units
    unfold SourceMixedSchedule.ProjectionOriginalSupport
    rw [fields.1, fields.2]
    simpa only [SourceMixedSchedule.ProjectionOriginalSupport, current, SourcePrefix.extend,
      projected, parent, propagation, known, row, tree, List.append_assoc] using final

theorem tree_deny_supported {parameters : Parameters}
    (rename : Nat → Fin v) (proofPrefix : SourcePrefix (parameters := parameters) rename)
    (tree : AndTree proofPrefix.state root inputs) (context : Clause (Fin v))
    (input : Literal (Fin v)) (member : input ∈ inputs)
    (unit : AvailableSubclause proofPrefix.state (context ++ [negate input]))
    (supported : SourceMixedSchedule.PrefixOriginalSupport rename proofPrefix)
    (original : TreeOriginals (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename) tree)
    (unitOrigin : ResultOrigin (formula parameters).clauses.size
      (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      proofPrefix.steps unit.row.id) :
    SourceMixedSchedule.ProjectionOriginalSupport rename proofPrefix
      (TreeUnits.deny tree context input member unit) := by
  let projected := projectTreeInputs tree
  let unitNow := afterTrace unit projected.state projected.steps projected.checked
  have actual := projectTreeInputs_supported tree (formula parameters).clauses.size
    (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename) original
    (SourceMixedSchedule.allowed_native_count_le rename)
    (SourceMixedSchedule.prefix_native_count_le rename proofPrefix)
  have complete := traceOriginalSupport_append _ _ proofPrefix.steps projected.steps supported actual.1
  have carried := resultOrigin_append_right _ _ proofPrefix.steps projected.steps unit.row.id unitOrigin
  have directionOrigin := actual.2 input member
  unfold TreeUnits.deny
  dsimp only
  split
  · rename_i same direction
    unfold SourceMixedSchedule.ProjectionOriginalSupport
    constructor
    · exact complete
    · subst input
      with_unfolding_all
        simpa only [SourceMixedSchedule.subclause_indices_mpr_id
          (show projected.state = projected.state from rfl)
          (show context ++ [negate root] = context ++ [negate root] from rfl),
          unitNow, afterTrace] using carried
  · rename_i row direction
    let left : AvailableSubclause projected.state (negate input :: context) :=
      retarget unitNow (by
        intro literal present
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at present ⊢
        aesop)
    let right : AvailableSubclause projected.state (input :: [negate root]) :=
      retarget row (by
        intro literal present
        simp only [List.mem_cons, List.not_mem_nil, or_false] at present ⊢
        aesop)
    have rowOrigin : ResultOrigin (formula parameters).clauses.size
        (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
        (proofPrefix.steps ++ projected.steps) row.row.id := by
      apply resultOrigin_append_left
      simpa only [direction, CertificateOrigin] using directionOrigin
    have joined := SourceMixedSchedule.longMerge_supported (formula parameters).clauses.size
      (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      (proofPrefix.steps ++ projected.steps) projected.state input context [negate root] left right
      complete (SourceMixedSchedule.allowed_native_count_le rename)
      (Nat.le_trans (SourceMixedSchedule.prefix_native_count_le rename proofPrefix)
        (runSteps_lastId_le projected.checked)) carried rowOrigin
    simpa only [SourceMixedSchedule.ProjectionOriginalSupport, projected, unitNow,
      left, right, List.append_assoc] using joined

def TransferOrigin (originalCount : Nat) (allowed : Nat → Prop) (steps : List (Step v))
    {state : State v} {context : Clause (Fin v)} {input output : Literal (Fin v)}
    (transfer : GuardedTransfer state context input output) : Prop :=
  match (generalizing := false) transfer with
  | .identity _ => True
  | .derived row => ResultOrigin originalCount allowed steps row.row.id

def GuardedTransferOrigin (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    {context : Clause (Fin v)} {input output : Literal (Fin v)}
    (transfer : GuardedTransfer prefixState.state context input output) : Prop :=
  TransferOrigin (formula parameters).clauses.size
    (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
    prefixState.steps transfer

def DirectionPairOrigin (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    {context : Clause (Fin v)} {input output : Literal (Fin v)}
    (pair : DirectionPair prefixState.state context input output) : Prop :=
  GuardedTransferOrigin rename prefixState pair.forward ∧
    GuardedTransferOrigin rename prefixState pair.backward

theorem GuardedTransferOrigin.afterTrace (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    {context : Clause (Fin v)} {input output : Literal (Fin v)}
    (transfer : GuardedTransfer prefixState.state context input output)
    (original : GuardedTransferOrigin rename prefixState transfer)
    (next : State v) (steps : List (Step v))
    (checked : runSteps prefixState.state steps = some next) :
    GuardedTransferOrigin rename (prefixState.extend next steps checked)
      (transfer.afterTrace next steps checked) := by
  cases transfer with
  | identity same => trivial
  | derived row =>
      change ResultOrigin (formula parameters).clauses.size
        (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
        (prefixState.steps ++ steps) row.row.id
      exact resultOrigin_append_right (formula parameters).clauses.size
        (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
        prefixState.steps steps row.row.id original

theorem DirectionPairOrigin.afterTrace (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    {context : Clause (Fin v)} {input output : Literal (Fin v)}
    (pair : DirectionPair prefixState.state context input output)
    (original : DirectionPairOrigin rename prefixState pair)
    (next : State v) (steps : List (Step v))
    (checked : runSteps prefixState.state steps = some next) :
    DirectionPairOrigin rename (prefixState.extend next steps checked)
      (pair.afterTrace next steps checked) :=
  ⟨GuardedTransferOrigin.afterTrace rename prefixState pair.forward original.1 next steps checked,
   GuardedTransferOrigin.afterTrace rename prefixState pair.backward original.2 next steps checked⟩

theorem GuardedTransferOrigin.dual (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    {context : Clause (Fin v)} {input output : Literal (Fin v)}
    (transfer : GuardedTransfer prefixState.state context input output)
    (original : GuardedTransferOrigin rename prefixState transfer) :
    GuardedTransferOrigin rename prefixState
      (Controller.NativeProof.SourceStagePolarity.GuardedTransfer.dual transfer) := by
  cases transfer with
  | identity same => trivial
  | derived row =>
      simpa only [GuardedTransferOrigin, TransferOrigin,
        Controller.NativeProof.SourceStagePolarity.GuardedTransfer.dual, retarget] using original

def PairedProjectionOriginalSupport (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    {context : Clause (Fin v)} {input output : Literal (Fin v)} {budget : Nat}
    (projection : PairedProjection prefixState.state context input output budget) : Prop :=
  SourceMixedSchedule.PrefixOriginalSupport rename (prefixState.extend projection.state projection.steps projection.checked) ∧
    DirectionPairOrigin rename
      (prefixState.extend projection.state projection.steps projection.checked) projection.pair

theorem GuardedTransferOrigin.same_steps (rename : Nat → Fin v)
    (state : State v) (before after : List (Step v)) (same : before = after)
    (beforeChecked : runSteps (initialState (relabel rename (formula parameters))) before = some state)
    (afterChecked : runSteps (initialState (relabel rename (formula parameters))) after = some state)
    {context : Clause (Fin v)} {input output : Literal (Fin v)}
    (transfer : GuardedTransfer state context input output)
    (original : GuardedTransferOrigin rename ⟨state, before, beforeChecked⟩ transfer) :
    GuardedTransferOrigin rename ⟨state, after, afterChecked⟩ transfer := by
  cases same
  exact original

end Controller.NativeProof.Wrapper.ControllerOrigins
