module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.Resolution
public import Controller.NativeProof.WrapperRuntime

@[expose] public section

/-! Wrapper resource accounting keeps the Horn query universe separate from
the ambient wrapper variables. Reindexing retains native row identifiers and
the classification of native, alias and discharged-assumption rows. -/
namespace Controller.Cost.WrapperResolution
open Controller.CNF Controller.Resolution Controller.Resolution.RUP
open Controller.NativeProof Controller.NativeProof.FoldProjection
open Controller.NativeProof.HornNativeReplay Controller.NativeProof.Wrapper
open Controller.NativeProof.SourceFoldProvenance
open Controller.NativeProof.SourceBusSchedule Controller.NativeProof.SourceMismatchHandles
variable {a u v : Nat}

theorem liftLiteral_reindex (codes : Fin a → Fin u)
    (source : Fin a → Literal (Fin v)) (target : Fin u → Literal (Fin v))
    (compatible : ∀ index, target (codes index) = source index) (literal : Literal (Fin a)) :
    liftLiteral target (codes literal.1, literal.2) = liftLiteral source literal := by
  rcases literal with ⟨index, phase⟩
  cases phase <;> simp [liftLiteral, compatible]

theorem liftClause_reindex (codes : Fin a → Fin u)
    (source : Fin a → Literal (Fin v)) (target : Fin u → Literal (Fin v))
    (compatible : ∀ index, target (codes index) = source index) (clause : Clause (Fin a)) :
    liftClause target (Rows.mapClause codes clause) = liftClause source clause := by
  unfold liftClause Rows.mapClause
  rw [List.map_map]
  apply List.map_congr_left
  intro literal member
  exact liftLiteral_reindex codes source target compatible literal

def reindexNativeRow (codes : Fin a → Fin u)
    (source : Fin a → Literal (Fin v)) (target : Fin u → Literal (Fin v))
    (compatible : ∀ index, target (codes index) = source index)
    (state : State v) (context : Clause (Fin v)) (clause : Clause (Fin a))
    (available : AvailableSubclause state (liftClause source clause ++ context)) :
    AvailableSubclause state (liftClause target (Rows.mapClause codes clause) ++ context) :=
  ⟨available.clause, available.row, by rw [liftClause_reindex codes source target compatible]; exact available.subset⟩

/-- Codes may identify aliases. No injectivity or ambient-size premise is used. -/
def reindexOrigin (codes : Fin a → Fin u)
    (source : Fin a → Literal (Fin v)) (target : Fin u → Literal (Fin v))
    (compatible : ∀ index, target (codes index) = source index)
    (state : State v) (context : Clause (Fin v)) (clause : Clause (Fin a))
    (origin : HornRowTransport.Origin source state context clause) :
    HornRowTransport.Origin target state context (Rows.mapClause codes clause) := by
  cases origin with
  | native available => exact .native (reindexNativeRow codes source target compatible state context clause available)
  | identity first second shape same =>
    exact .identity (codes first) (codes second) (by simp [shape, Rows.mapClause])
      ((compatible first).trans (same.trans (compatible second).symm))
  | assumption literal shape negative discharged =>
    refine .assumption (codes literal.1, literal.2) (by simp [shape, Rows.mapClause]) negative ?_
    rw [liftLiteral_reindex codes source target compatible]
    exact discharged

theorem reindexOrigin_keep (codes : Fin a → Fin u)
    (source : Fin a → Literal (Fin v)) (target : Fin u → Literal (Fin v))
    (compatible : ∀ index, target (codes index) = source index)
    (state : State v) (context : Clause (Fin v)) (clause : Clause (Fin a))
    (origin : HornRowTransport.Origin source state context clause) :
    (reindexOrigin codes source target compatible state context clause origin).keep = origin.keep := by
  cases origin <;> rfl

theorem reindexOrigin_provenance (codes : Fin a → Fin u)
    (source : Fin a → Literal (Fin v)) (target : Fin u → Literal (Fin v))
    (compatible : ∀ index, target (codes index) = source index)
    (state : State v) (context : Clause (Fin v)) (clause : Clause (Fin a))
    (origin : HornRowTransport.Origin source state context clause)
    (originalCount : Nat) (allowed : Nat → Prop) (prior : List (Step v))
    (supported : HornOriginResultOrigin originalCount allowed prior origin) :
    HornOriginResultOrigin originalCount allowed prior
      (reindexOrigin codes source target compatible state context clause origin) := by
  cases origin with
  | native available => exact supported
  | identity first second shape same => trivial
  | assumption literal shape negative discharged => trivial

/-- The retained wrapper replay never emits more steps than the stored source
prefix, including source steps that are unused by the final contradiction. -/
theorem retainedReplay_count
    {sourceCount targetCount : Nat} {original : Nat → Nat} {allowed : Nat → Prop}
    {source target next : State v}
    (matched : RetainedMatch sourceCount targetCount original allowed source target)
    (steps : List (Step v)) (checked : runSteps source steps = some next)
    (supported : TraceOriginalSupport sourceCount allowed steps) :
    (replayRetained matched steps next checked supported).steps.length ≤ steps.length := by
  rw [(replayRetained matched steps next checked supported).emitted, List.length_map]

/-- The query bound depends on its finite native universe, independently of
the ambient wrapper universe in which the certified rows are replayed. -/
def finiteQuery (formula : FiniteFormula u) (restricted : Controller.Horn.DualHorn formula)
    (unsat : Unsatisfiable formula) (handles : Fin u → Literal (Fin v))
    (state : State v) (context : Clause (Fin v))
    (rows : ∀ index : Fin formula.clauses.size,
      HornRowTransport.Origin handles state context formula.clauses[index.val]) :
    SubclauseProjection state context u := by
  have complete := HornTrail.produce_complete formula restricted unsat
  exact match returned : HornTrail.produce formula with
  | none => False.elim (by obtain ⟨conflict, run, _, _⟩ := complete; simp [returned] at run)
  | some conflict => by
    have certified : HornTrail.Certified formula conflict := by
      obtain ⟨result, run, proof, bound⟩ := complete
      have same : result = conflict := Option.some.inj (run.symm.trans returned)
      exact same ▸ proof
    have bound : conflict.reasons.length ≤ u := by
      obtain ⟨result, run, proof, bound⟩ := complete
      have same : result = conflict := Option.some.inj (run.symm.trans returned)
      exact same ▸ bound
    have positive := HornTrail.scan_conflict_positive formula _ _ _ conflict returned
    let replay := HornRowTransport.replay formula conflict certified positive handles state context rows
    exact ⟨replay.state, replay.steps, replay.checked, replay.result, replay.count.trans bound⟩

theorem finiteQuery_provenance (formula : FiniteFormula u) (restricted : Controller.Horn.DualHorn formula)
    (unsat : Unsatisfiable formula) (handles : Fin u → Literal (Fin v))
    (state : State v) (context : Clause (Fin v))
    (rows : ∀ index : Fin formula.clauses.size,
      HornRowTransport.Origin handles state context formula.clauses[index.val])
    (originalCount : Nat) (allowed : Nat → Prop) (prior : List (Step v))
    (supported : TraceOriginalSupport originalCount allowed prior)
    (originalBound : ∀ row, allowed row → row ≤ originalCount) (bound : originalCount ≤ state.lastId)
    (origins : ∀ index, HornOriginResultOrigin originalCount allowed prior (rows index)) :
    let actual := finiteQuery formula restricted unsat handles state context rows
    TraceOriginalSupport originalCount allowed (prior ++ actual.steps) ∧
      ResultOrigin originalCount allowed (prior ++ actual.steps) actual.result.row.id := by
  have complete := HornTrail.produce_complete formula restricted unsat
  unfold finiteQuery
  dsimp only
  split
  · rename_i returned
    obtain ⟨conflict, run, _, _⟩ := complete
    simp [returned] at run
  · rename_i conflict returned
    have certified : HornTrail.Certified formula conflict := by
      obtain ⟨result, run, proof, bound⟩ := complete
      have same : result = conflict := Option.some.inj (run.symm.trans returned)
      exact same ▸ proof
    have positive := HornTrail.scan_conflict_positive formula _ _ _ conflict returned
    exact hornRowReplay_supported formula conflict certified positive handles state context rows
      originalCount allowed prior supported originalBound bound origins

section NativeQuery
open Controller.Native Controller.Native.SourceController
open Controller.NativeProof.SourceFoldProjection Controller.NativeProof.SourceStageCongruence
open Controller.NativeProof.SourceDecoderTraversal Controller.NativeProof.SourceHealthyOne
variable {parameters : Parameters}

/-- The cursor after the paired decoders and before final observations. -/
def coreCursor (parameters : Parameters) : Cursor parameters :=
  attachDecoder parameters .faulty (attachDecoder parameters .healthy
    (originalObservations parameters (controller parameters)))

def coreVariableCount (parameters : Parameters) : Nat := (coreCursor parameters).lastID + 1

def coreRename (parameters : Parameters) (source : Nat) : Fin (coreVariableCount parameters) :=
  ⟨source % coreVariableCount parameters, Nat.mod_lt _ (by unfold coreVariableCount; omega)⟩

theorem coreRename_allocated (source : Nat) (bounded : source ≤ (coreCursor parameters).lastID) :
    (coreRename parameters source).val = source :=
  Nat.mod_eq_of_lt (by unfold coreVariableCount; omega)

theorem coreCursor_ready (parameters : Parameters) : (coreCursor parameters).Ready := by
  apply attachDecoder_ready
  · exact attachDecoder_ready parameters .healthy _ (controller_originalObservations_ready parameters)
      (controller_originalObservations_qualifiers parameters .healthy)
  · exact attachDecoder_qualifiersAvailable parameters .healthy .faulty _
      (controller_originalObservations_qualifiers parameters .faulty)

def queryRole (parameters : Parameters)
    (index : Fin (parameters.channels + parameters.decoder.nodeCount)) : Controller.Native.Variable parameters :=
  match parameters.decoder.zeroIndex.symm index with
  | .inl channel => .internal (.qualifier .faulty channel)
  | .inr node => .internal (.decoder .faulty node)

theorem queryRole_assigned (parameters : Parameters)
    (index : Fin (parameters.channels + parameters.decoder.nodeCount)) :
    queryRole parameters index ∈ (compile parameters).assigned := by
  rw [compile_assigned]
  unfold queryRole
  split
  · simp [assignedRoles, tailRoles, eligibleRoles]
  · simp [assignedRoles]

theorem queryHandles_role (rename : Nat → Fin v)
    (index : Fin (parameters.channels + parameters.decoder.nodeCount)) :
    SourceHealthyOneQuery.handles (parameters := parameters) rename index =
      mapLiteral rename (sourceRoleMap parameters (queryRole parameters index)) := by
  unfold SourceHealthyOneQuery.handles SourceForwardRows.handle queryRole
  cases parameters.decoder.zeroIndex.symm index with
  | inl channel => rw [compiled_faulty_qualifier_slot]; rfl
  | inr node =>
    rw [compiled_decoder_slot, decoderComplete_slot]
    exact (SourceDecoderEvaluation.stored_eq_output rename .faulty parameters.decoder.nodeCount
      (Nat.le_refl _) node node.isLt).symm

def nativeHandles (parameters : Parameters) (rename : Nat → Fin v) :
    Fin (coreVariableCount parameters) → Literal (Fin v) := fun index => (rename index.val, true)

def nativeCodes (parameters : Parameters) :
    Fin (parameters.channels + parameters.decoder.nodeCount) → Fin (coreVariableCount parameters) :=
  fun index => (SourceHealthyOneQuery.handles (parameters := parameters) (coreRename parameters) index).1

theorem nativeHandles_compatible (rename : Nat → Fin v)
    (index : Fin (parameters.channels + parameters.decoder.nodeCount)) :
    nativeHandles parameters rename (nativeCodes parameters index) =
      SourceHealthyOneQuery.handles (parameters := parameters) rename index := by
  have member : queryRole parameters index ∈ (coreCursor parameters).assigned := by
    have assigned := queryRole_assigned parameters index
    change queryRole parameters index ∈ (newObservations parameters (coreCursor parameters)).assigned at assigned
    rw [newObservations_assigned] at assigned
    unfold queryRole at assigned ⊢
    cases shape : parameters.decoder.zeroIndex.symm index <;> simpa [shape] using assigned
  have same : sourceRoleMap parameters (queryRole parameters index) =
      (coreCursor parameters).slots (queryRole parameters index) := by
    unfold sourceRoleMap compile
    apply newObservations_preserves
    · unfold queryRole; split <;> simp
    · intro output; unfold queryRole; split <;> simp
  have bounded := (coreCursor_ready parameters).bounded (queryRole parameters index) member
  have positive := sourceRoleMap_positive parameters (queryRole parameters index)
  have allocated := coreRename_allocated (parameters := parameters)
    (sourceRoleMap parameters (queryRole parameters index)).1 (by rw [same]; exact bounded.2)
  unfold nativeHandles nativeCodes
  rw [queryHandles_role, queryHandles_role]
  change (rename (coreRename parameters (sourceRoleMap parameters (queryRole parameters index)).1).val, true) =
    (rename (sourceRoleMap parameters (queryRole parameters index)).1, (sourceRoleMap parameters (queryRole parameters index)).2)
  rw [allocated]
  exact Prod.ext rfl positive.symm

def nativeRows (rename : Nat → Fin v) (prepared : Preparation (parameters := parameters) rename)
    (root : Fin parameters.decoder.nodeCount) :
    ∀ index : Fin (NativeResolution.healthyNativeFormula (coreRename parameters) root).clauses.size,
      HornRowTransport.Origin (nativeHandles parameters rename) prepared.proofPrefix.state
        (cofactor (parameters := parameters) rename ++ [SourceForwardRows.handle rename .faulty (.inr root)])
        (NativeResolution.healthyNativeFormula (coreRename parameters) root).clauses[index.val] := by
  intro index
  let original := parameters.decoder.finiteZeroSystem parameters.buses parameters.bridge.target root ∅ ∅
  have bound : index.val < original.clauses.size := by
    simpa only [original, NativeResolution.healthyNativeFormula, relabel, Controller.CNF.OrderedFormula.relabel, Array.size_map] using index.isLt
  let clause := original.clauses[index.val]'bound
  have equal : (NativeResolution.healthyNativeFormula (coreRename parameters) root).clauses[index.val] =
      Rows.mapClause (nativeCodes parameters) clause := by
    simp only [NativeResolution.healthyNativeFormula, relabel, Controller.CNF.OrderedFormula.relabel, Array.getElem_map,
      Controller.CNF.OrderedFormula.Clause.relabel, Rows.mapClause, nativeCodes, clause, original]
  exact Eq.mpr (congrArg (HornRowTransport.Origin (nativeHandles parameters rename) prepared.proofPrefix.state
    (cofactor (parameters := parameters) rename ++ [SourceForwardRows.handle rename .faulty (.inr root)])) equal)
    (reindexOrigin (nativeCodes parameters) (SourceHealthyOneQuery.handles (parameters := parameters) rename)
      (nativeHandles parameters rename) (nativeHandles_compatible rename) _ _ clause
      (SourceHealthyOneQuery.finiteRows rename prepared root ⟨index.val, bound⟩))

theorem nativeRows_provenance (rename : Nat → Fin v)
    (prepared : Preparation (parameters := parameters) rename) (origins : PreparationOrigins rename prepared)
    (root : Fin parameters.decoder.nodeCount)
    (index : Fin (NativeResolution.healthyNativeFormula (coreRename parameters) root).clauses.size) :
    QueryOriginProvenance rename prepared.proofPrefix (nativeRows rename prepared root index) := by
  unfold nativeRows
  dsimp only
  apply queryOrigin_indices_mpr_provenance
  · simp only [NativeResolution.healthyNativeFormula, relabel, Controller.CNF.OrderedFormula.relabel, Array.getElem_map,
      Controller.CNF.OrderedFormula.Clause.relabel, Rows.mapClause, nativeCodes]
  · apply reindexOrigin_provenance
    exact queryFiniteRows_origins rename prepared origins root _

/-- A selected native query replays into an arbitrary wrapper universe while
retaining the native variable count as its inference budget. -/
def healthyQuery (rename : Nat → Fin v) (prepared : Preparation (parameters := parameters) rename)
    (guarded : parameters.decoder.Guarded) (selected : Finset (Fin parameters.decoder.roots.length))
    (absent : Controller.NativeProof.Decoder.NoDiscrepancy parameters selected)
    (output : Fin parameters.decoder.roots.length) (accepted : output ∈ selected)
    (healthy : parameters.observations output (Controller.assignmentOfSet {parameters.bridge.target}) = true) :
    SubclauseProjection prepared.proofPrefix.state
      (cofactor (parameters := parameters) rename ++ [SourceForwardRows.handle rename .faulty (.inr (parameters.decoder.roots.get output))])
      (coreVariableCount parameters) := by
  let root := parameters.decoder.roots.get output
  let formula := NativeResolution.healthyNativeFormula (coreRename parameters) root
  have original : Unsatisfiable
      (parameters.decoder.finiteZeroSystem parameters.buses parameters.bridge.target root ∅ ∅) := by
    apply (unsatisfiable_relabel_iff parameters.decoder.zeroIndex.injective _).mpr
    exact Controller.NativeProof.Decoder.healthyOne_zeroSystem_unsatisfiable parameters guarded selected absent output accepted healthy
  have unsat : Unsatisfiable formula := by
    rintro ⟨assignment, model⟩
    exact original ⟨_, (satisfies_relabel _ _ _).mp model⟩
  have restricted : Controller.Horn.DualHorn formula :=
    Controller.Decoder.SparseFormula.relabel_dualHorn _ _
      (parameters.decoder.finiteZeroSystem_dualHorn guarded _ _ _ _ _)
  exact finiteQuery formula restricted unsat (nativeHandles parameters rename)
    prepared.proofPrefix.state
    (cofactor (parameters := parameters) rename ++ [SourceForwardRows.handle rename .faulty (.inr root)])
    (nativeRows rename prepared root)

theorem healthyQuery_provenance (rename : Nat → Fin v)
    (prepared : Preparation (parameters := parameters) rename) (origins : PreparationOrigins rename prepared)
    (guarded : parameters.decoder.Guarded) (selected : Finset (Fin parameters.decoder.roots.length))
    (absent : Controller.NativeProof.Decoder.NoDiscrepancy parameters selected)
    (output : Fin parameters.decoder.roots.length) (accepted : output ∈ selected)
    (healthy : parameters.observations output (Controller.assignmentOfSet {parameters.bridge.target}) = true) :
    SourceDecoderSchedule.ProjectionOriginalSupport rename prepared.proofPrefix
      (healthyQuery rename prepared guarded selected absent output accepted healthy) := by
  unfold healthyQuery
  apply finiteQuery_provenance
  · exact origins.supported
  · exact SourceDecoderSchedule.allowed_native_count_le rename
  · exact SourceMixedSchedule.prefix_native_count_le rename prepared.proofPrefix
  · exact nativeRows_provenance rename prepared origins _

open Controller.NativeProof.SourceBusAdvance Controller.NativeProof.SourceStageXor

def healthyEquality (rename : Nat → Fin v) (prepared : Preparation (parameters := parameters) rename)
    (guarded : parameters.decoder.Guarded) (selected : Finset (Fin parameters.decoder.roots.length))
    (absent : Controller.NativeProof.Decoder.NoDiscrepancy parameters selected)
    (output : Fin parameters.decoder.roots.length) (accepted : output ∈ selected)
    (healthy : parameters.observations output (Controller.assignmentOfSet {parameters.bridge.target}) = true) :
    SourceBusAdvance.PairedProjection prepared.proofPrefix.state (cofactor (parameters := parameters) rename)
      (SourceDecoderTraversal.nativeRootLiteral rename .healthy output)
      (SourceDecoderTraversal.nativeRootLiteral rename .faulty output)
      (coreVariableCount parameters) := by
  let actual := healthyQuery rename prepared guarded selected absent output accepted healthy
  have faulty : AvailableSubclause actual.state (cofactor (parameters := parameters) rename ++
      [SourceDecoderTraversal.nativeRootLiteral rename .faulty output]) := by
    simpa only [SourceHealthyOneQuery.rootHandle, SourceForwardRows.handle, Sum.elim_inr] using actual.result
  have healthyRow : AvailableSubclause actual.state (cofactor (parameters := parameters) rename ++
      [SourceDecoderTraversal.nativeRootLiteral rename .healthy output]) := by
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

theorem healthyEquality_provenance (rename : Nat → Fin v)
    (prepared : SourceHealthyOne.Preparation (parameters := parameters) rename) (origins : PreparationOrigins rename prepared)
    (guarded : parameters.decoder.Guarded) (selected : Finset (Fin parameters.decoder.roots.length))
    (absent : Controller.NativeProof.Decoder.NoDiscrepancy parameters selected) (output : Fin parameters.decoder.roots.length)
    (accepted : output ∈ selected)
    (healthy : parameters.observations output (Controller.assignmentOfSet {parameters.bridge.target}) = true) :
    SourceDecoderSchedule.PairedProjectionOriginalSupport rename prepared.proofPrefix
      (healthyEquality rename prepared guarded selected absent output accepted healthy) := by
  let actual := healthyQuery rename prepared guarded selected absent output accepted healthy
  let faulty : AvailableSubclause actual.state (cofactor (parameters := parameters) rename ++ [nativeRootLiteral rename .faulty output]) := by
    simpa only [SourceHealthyOneQuery.rootHandle, SourceForwardRows.handle, Sum.elim_inr] using actual.result
  let healthyRow : AvailableSubclause actual.state (cofactor (parameters := parameters) rename ++ [nativeRootLiteral rename .healthy output]) := by
    have bit : parameters.decoder.eval (Controller.assignmentOfSet {parameters.bridge.target}) (parameters.decoder.roots.get output) = true := healthy
    simpa only [bit, valueLiteral, ite_true, SourceHealthyOneQuery.rootHandle] using
      FoldProjection.afterTrace (prepared.healthy (parameters.decoder.roots.get output)) actual.state actual.steps actual.checked
  have actualOrigins := healthyQuery_provenance rename prepared origins guarded selected absent output accepted healthy
  have faultyId : faulty.row.id = actual.result.row.id := by
    dsimp only [faulty]
    with_unfolding_all
      apply SourceMixedSchedule.subclause_indices_mpr_id rfl
      simp only [SourceHealthyOneQuery.rootHandle, SourceForwardRows.handle, Sum.elim_inr]
  have healthyId : healthyRow.row.id = (prepared.healthy (parameters.decoder.roots.get output)).row.id := by
    have bit : parameters.decoder.eval (Controller.assignmentOfSet {parameters.bridge.target})
        (parameters.decoder.roots.get output) = true := healthy
    dsimp only [healthyRow]
    with_unfolding_all
      apply Eq.trans (SourceMixedSchedule.subclause_indices_mpr_id rfl
        (by simp only [SourceHealthyOneQuery.rootHandle]) _ _)
      apply SourceMixedSchedule.subclause_indices_cast_id rfl
      simp only [bit, valueLiteral, ite_true]
  unfold SourceDecoderSchedule.PairedProjectionOriginalSupport healthyEquality
  dsimp only [id]
  refine ⟨actualOrigins.1, ?_, ?_⟩
  · change ResultOrigin (SourceController.formula parameters).clauses.size
      (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
      (prepared.proofPrefix.steps ++ actual.steps) faulty.row.id
    rw [faultyId]
    exact actualOrigins.2
  · change ResultOrigin (SourceController.formula parameters).clauses.size
      (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
      (prepared.proofPrefix.steps ++ actual.steps) healthyRow.row.id
    rw [healthyId]
    exact resultOrigin_append_right _ _ prepared.proofPrefix.steps actual.steps _ (origins.healthy _)


def selectedMixed (rename : Nat → Fin v) (guarded : parameters.decoder.Guarded)
    (selected : Finset (Fin parameters.decoder.roots.length)) (absent : Controller.NativeProof.Decoder.NoDiscrepancy parameters selected)
    (table : Compiler.DrivenTable (parameters := parameters) rename 0)
    (output : Fin parameters.decoder.roots.length) (accepted : output ∈ selected) :
    PairedProjection table.summaries.prepared.proofPrefix.state (cofactor (parameters := parameters) rename)
      (nativeRootLiteral rename .healthy output) (nativeRootLiteral rename .faulty output)
      (coreVariableCount parameters) :=
  if healthy : parameters.observations output (Controller.assignmentOfSet {parameters.bridge.target}) = true then
    healthyEquality rename table.summaries.prepared guarded selected absent output accepted healthy
  else
    let actual := SourceSupportSummaries.equality rename table.summaries guarded selected absent output accepted
      (Bool.eq_false_of_not_eq_true healthy)
    ⟨actual.state, actual.steps, actual.checked, actual.pair, actual.count.trans (Nat.zero_le _)⟩

theorem selectedMixed_origins (rename : Nat → Fin v) (guarded : parameters.decoder.Guarded)
    (selected : Finset (Fin parameters.decoder.roots.length)) (absent : Controller.NativeProof.Decoder.NoDiscrepancy parameters selected)
    (table : Compiler.DrivenTable (parameters := parameters) rename 0) (origins : DrivenSeedOrigins rename table)
    (output : Fin parameters.decoder.roots.length) (accepted : output ∈ selected) :
    SourceDecoderSchedule.PairedProjectionOriginalSupport rename table.summaries.prepared.proofPrefix
      (selectedMixed rename guarded selected absent table output accepted) := by
  unfold selectedMixed
  split
  · rename_i healthy
    exact healthyEquality_provenance rename table.summaries.prepared origins.summaries.prepared guarded selected absent output accepted healthy
  · rename_i healthy
    exact healthyZeroEquality_origins rename table.summaries origins.summaries guarded selected absent output accepted
      (Bool.eq_false_of_not_eq_true healthy)

def selectedAdvance (rename : Nat → Fin v) (guarded : parameters.decoder.Guarded)
    (selected : Finset (Fin parameters.decoder.roots.length)) (absent : Controller.NativeProof.Decoder.NoDiscrepancy parameters selected)
    (output : Fin parameters.decoder.roots.length) (accepted : output ∈ selected)
    (table : SelectedDriven (parameters := parameters) rename outputs) :
    SelectedDriven (parameters := parameters) rename (output :: outputs) := by
  let mixed := selectedMixed rename guarded selected absent table.seed output accepted
  have mixedOrigins := selectedMixed_origins rename guarded selected absent table.seed table.origins output accepted
  let current := table.afterTrace mixed.state mixed.steps mixed.checked mixedOrigins.1
  let final := Compiler.dischargePair mixed.state
    (nativeHealthyFirstFlag (parameters := parameters) rename) (nativeFaultyFirstFlag (parameters := parameters) rename)
    (nativeRootLiteral rename .healthy output) (nativeRootLiteral rename .faulty output)
    (current.seed.equalOne output) mixed.pair current.seed.healthyFlag
  have finalOrigins := dischargePair_origins rename current.seed.summaries.prepared.proofPrefix _ _ _ _
    (current.seed.equalOne output) mixed.pair current.seed.healthyFlag current.origins.summaries.prepared.supported
    (current.origins.equalOne output) mixedOrigins.2 current.origins.healthyFlag
  let extended := current.afterTrace final.state final.steps final.checked finalOrigins.1
  refine ⟨extended.seed, extended.origins,
    (fun query member => if same : query = output then same ▸ final.pair else
      extended.pairs query (by simpa only [List.mem_cons, same, false_or] using member)), ?_⟩
  intro query member
  split
  · rename_i same
    subst query
    exact finalOrigins.2
  · exact extended.pairOrigins _ _

def selectedBuild (rename : Nat → Fin v) (drive : parameters.drive = true) (guarded : parameters.decoder.Guarded)
    (selected : Finset (Fin parameters.decoder.roots.length)) (absent : Controller.NativeProof.Decoder.NoDiscrepancy parameters selected) :
    (outputs : List (Fin parameters.decoder.roots.length)) → (∀ output ∈ outputs, output ∈ selected) →
      SelectedDriven (parameters := parameters) rename outputs
  | [], _ => ⟨Compiler.initialDriven rename drive guarded, initialDriven_origins rename drive guarded,
      fun _ member => False.elim (List.not_mem_nil member), fun _ member => False.elim (List.not_mem_nil member)⟩
  | output :: rest, accepted => selectedAdvance rename guarded selected absent output (accepted output (by simp))
      (selectedBuild rename drive guarded selected absent rest (fun query member => accepted query (List.mem_cons_of_mem _ member)))


theorem selectedAdvanceSize (rename : Nat → Fin v) (guarded : parameters.decoder.Guarded)
    (selected : Finset (Fin parameters.decoder.roots.length))
    (absent : Controller.NativeProof.Decoder.NoDiscrepancy parameters selected)
    (output : Fin parameters.decoder.roots.length) (accepted : output ∈ selected)
    (table : SelectedDriven (parameters := parameters) rename outputs) :
    (selectedAdvance rename guarded selected absent output accepted table).seed.summaries.prepared.proofPrefix.steps.length ≤
      table.seed.summaries.prepared.proofPrefix.steps.length + coreVariableCount parameters + 4 := by
  unfold selectedAdvance
  dsimp only
  simp only [SelectedDriven.afterTrace, Compiler.DrivenTable.afterTrace,
    SourceSupportSummaries.Table.afterTrace, Preparation.afterTrace, SourcePrefix.extend]
  rw [List.length_append, List.length_append]
  apply (Nat.add_le_add_left (Compiler.dischargePair _ _ _ _ _ _ _ _).count _).trans
  have actual := (selectedMixed rename guarded selected absent table.seed output accepted).count
  omega

theorem selectedBuildSize (rename : Nat → Fin v) (drive : parameters.drive = true)
    (guarded : parameters.decoder.Guarded) (selected : Finset (Fin parameters.decoder.roots.length))
    (absent : Controller.NativeProof.Decoder.NoDiscrepancy parameters selected)
    (outputs : List (Fin parameters.decoder.roots.length)) (accepted : ∀ output ∈ outputs, output ∈ selected) :
    (selectedBuild rename drive guarded selected absent outputs accepted).seed.summaries.prepared.proofPrefix.steps.length ≤
      NativeResolution.drivenInitialBudget parameters + outputs.length * (coreVariableCount parameters + 4) := by
  induction outputs with
  | nil => simpa only [selectedBuild, List.length_nil, Nat.zero_mul, Nat.add_zero] using
      NativeResolution.initialDrivenSize rename drive guarded
  | cons output rest ih =>
    have previous := ih (fun query member => accepted query (List.mem_cons_of_mem _ member))
    have next := selectedAdvanceSize rename guarded selected absent output (accepted output (by simp))
      (selectedBuild rename drive guarded selected absent rest
        (fun query member => accepted query (List.mem_cons_of_mem _ member)))
    change (selectedBuild rename drive guarded selected absent (output :: rest) accepted).seed.summaries.prepared.proofPrefix.steps.length ≤ _ at next
    simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

end NativeQuery

section RetainedPrefix
open Controller.Native Controller.Native.SourceController Controller.Native.ObservationProjection
open Controller.NativeProof.SourceDecoderTraversal
open Controller.NativeProof.SourceStageCongruence
variable {internalCount : Nat}

structure SelectedZero (parameters : Parameters) (rename : Nat → Fin v)
    (drive : parameters.drive = false) (outputs : List (Fin parameters.decoder.roots.length)) where
  program : DriveZeroOutputAccumulator (parameters := parameters) rename drive 0
  supported : SourceDecoderSchedule.PrefixOriginalSupport rename program.prefix
  pairs : ∀ output ∈ outputs, DirectionPair program.state []
    (nativeRootLiteral rename .healthy output) (nativeRootLiteral rename .faulty output)
  origins : ∀ output member, SourceDecoderSchedule.DirectionPairOrigin rename program.prefix (pairs output member)

def selectedZeroAdvance (parameters : Parameters) (rename : Nat → Fin v) (drive : parameters.drive = false)
    {outputs : List (Fin parameters.decoder.roots.length)}
    (output : Fin parameters.decoder.roots.length) (table : SelectedZero parameters rename drive outputs) :
    SelectedZero parameters rename drive (output :: outputs) := by
  let added := driveZeroOutputPairAt rename drive table.program output
  have origin := driveZeroOutputPairAt_supported rename drive 0 table.program output table.supported
  let next : DriveZeroOutputAccumulator (parameters := parameters) rename drive 0 :=
    ⟨added.state, table.program.steps ++ added.steps, by
      rw [runSteps_append, table.program.checked]; exact added.checked,
      fun index impossible => False.elim (Nat.not_lt_zero _ impossible)⟩
  have sameSteps : (table.program.prefix.extend added.state added.steps added.checked).steps = next.prefix.steps := by
    simp only [next, DriveZeroOutputAccumulator.prefix, SourcePrefix.extend, List.append_assoc]
  have carried := decoderPairOrigin_same_steps rename added.state _ _ sameSteps
    (table.program.prefix.extend added.state added.steps added.checked).checked next.prefix.checked added.pair origin.2
  refine ⟨next, ?_, (fun query member => if same : query = output then same ▸ added.pair else
    (table.pairs query (by simpa only [List.mem_cons, same, false_or] using member)).afterTrace
      added.state added.steps added.checked), ?_⟩
  · unfold SourceDecoderSchedule.PrefixOriginalSupport at origin ⊢
    rw [← sameSteps]
    exact origin.1
  · intro query member
    split
    · rename_i same; subst query; exact carried
    · exact decoderPairOrigin_same_steps rename added.state _ _ sameSteps
        (table.program.prefix.extend added.state added.steps added.checked).checked next.prefix.checked _
        (SourceDecoderSchedule.DirectionPairOrigin.afterTrace rename table.program.prefix _
          (table.origins query _) added.state added.steps added.checked)

def selectedZeroBuild (parameters : Parameters) (rename : Nat → Fin v) (drive : parameters.drive = false) :
    (outputs : List (Fin parameters.decoder.roots.length)) → SelectedZero parameters rename drive outputs
  | [] => ⟨driveZeroOutputInitial rename drive, (driveZeroOutputInitial_originals rename drive).1,
      fun _ member => False.elim (List.not_mem_nil member),
      fun _ member => False.elim (List.not_mem_nil member)⟩
  | output :: rest => selectedZeroAdvance parameters rename drive output (selectedZeroBuild parameters rename drive rest)

theorem selectedZeroBuildSize (parameters : Parameters) (rename : Nat → Fin v) (drive : parameters.drive = false)
    (outputs : List (Fin parameters.decoder.roots.length)) :
    (selectedZeroBuild parameters rename drive outputs).program.prefix.steps.length ≤
      SourceQualifierSchedule.qualifierProgramBudget parameters + 24 * sourceDecoderProducerCost parameters +
        4 + 4 * outputs.length := by
  have bounded : (selectedZeroBuild parameters rename drive outputs).program.steps.length ≤ 4 * outputs.length := by
    induction outputs with
    | nil => simp [selectedZeroBuild, driveZeroOutputInitial]
    | cons output rest ih =>
      have count := (driveZeroOutputPairAt rename drive
        (selectedZeroBuild parameters rename drive rest).program output).count
      change ((selectedZeroBuild parameters rename drive rest).program.steps ++ _).length ≤ _
      rw [List.length_append]
      simp only [List.length_cons]
      omega
  have base := NativeResolution.driveZeroPhysicalSize rename drive
  change ((driveZeroPhysicalPrefix rename drive).steps ++ _).length ≤ _
  rw [List.length_append]
  omega

theorem replaySelectedPrefixSize (parameters : Parameters)
    (rows : List (Clause (WrapperLabel parameters internalCount)))
    (core : ∀ clause ∈ taggedCoreRows parameters, clause ∈ rows)
    (rename : WrapperLabel parameters internalCount → Fin v) (outputs : List (Fin parameters.decoder.roots.length))
    (proofPrefix : SourcePrefix (parameters := parameters) (fun signal => rename (.inl signal)))
    (supported : SourceDecoderSchedule.PrefixOriginalSupport _ proofPrefix)
    (pairs : ∀ output ∈ outputs, DirectionPair proofPrefix.state []
      (nativeRootLiteral (fun signal => rename (.inl signal)) .healthy output)
      (nativeRootLiteral (fun signal => rename (.inl signal)) .faulty output))
    (origins : ∀ output member, SourceDecoderSchedule.DirectionPairOrigin _ proofPrefix (pairs output member)) :
    (replaySelectedPrefix parameters rows core rename outputs proofPrefix supported pairs origins).steps.length ≤
      proofPrefix.steps.length := by
  unfold replaySelectedPrefix
  dsimp only
  exact retainedReplay_count _ _ _ _

/-- Complete stored-prefix budget. Both drive branches charge only requested
pairs, and the query universe ends before final observation allocations. -/
def selectedPrefixBudget (parameters : Parameters) (queries : Nat) : Nat :=
  NativeResolution.drivenInitialBudget parameters + queries * (coreVariableCount parameters + 4) +
    SourceQualifierSchedule.qualifierProgramBudget parameters + 24 * sourceDecoderProducerCost parameters +
      4 + 4 * queries

def nativeSelectedPrefix (parameters : Parameters)
    (rows : List (Clause (WrapperLabel parameters internalCount)))
    (core : ∀ clause ∈ taggedCoreRows parameters, clause ∈ rows)
    (rename : WrapperLabel parameters internalCount → Fin v) (outputs : List (Fin parameters.decoder.roots.length))
    (guarded : parameters.decoder.Guarded)
    (absent : parameters.drive = true → Controller.NativeProof.Decoder.NoDiscrepancy parameters outputs.toFinset) :
    NativeSelectedPrefix parameters rows rename outputs := by
  let signalRename := fun signal => rename (Sum.inl signal)
  if drive : parameters.drive = true then
    let table := selectedBuild signalRename drive guarded outputs.toFinset (absent drive) outputs.dedup
      (fun output member => List.mem_toFinset.mpr (List.mem_dedup.mp member))
    exact replaySelectedPrefix parameters rows core rename outputs table.seed.summaries.prepared.proofPrefix
      table.origins.summaries.prepared.supported
      (fun output member => table.pairs output (List.mem_dedup.mpr member))
      (fun output member => table.pairOrigins output (List.mem_dedup.mpr member))
  else
    have zero := Bool.eq_false_of_not_eq_true drive
    let table := selectedZeroBuild parameters signalRename zero outputs.dedup
    exact replaySelectedPrefix parameters rows core rename outputs table.program.prefix table.supported
      (fun output member => table.pairs output (List.mem_dedup.mpr member))
      (fun output member => table.origins output (List.mem_dedup.mpr member))

theorem nativeSelectedPrefixSize (parameters : Parameters)
    (rows : List (Clause (WrapperLabel parameters internalCount)))
    (core : ∀ clause ∈ taggedCoreRows parameters, clause ∈ rows)
    (rename : WrapperLabel parameters internalCount → Fin v) (outputs : List (Fin parameters.decoder.roots.length))
    (guarded : parameters.decoder.Guarded)
    (absent : parameters.drive = true → Controller.NativeProof.Decoder.NoDiscrepancy parameters outputs.toFinset) :
    (nativeSelectedPrefix parameters rows core rename outputs guarded absent).steps.length ≤
      selectedPrefixBudget parameters outputs.dedup.length := by
  unfold nativeSelectedPrefix
  dsimp only
  split
  · rename_i drive
    apply (replaySelectedPrefixSize _ _ _ _ _ _ _ _ _).trans
    have bound := selectedBuildSize (fun signal => rename (.inl signal)) drive guarded
      outputs.toFinset (absent drive) outputs.dedup
      (fun output member => List.mem_toFinset.mpr (List.mem_dedup.mp member))
    exact bound.trans (by unfold selectedPrefixBudget; omega)
  · rename_i drive
    apply (replaySelectedPrefixSize _ _ _ _ _ _ _ _ _).trans
    have bound := selectedZeroBuildSize parameters (fun signal => rename (.inl signal))
      (Bool.eq_false_of_not_eq_true drive) outputs.dedup
    exact bound.trans (by unfold selectedPrefixBudget; omega)

def selectedRefutationOfAbsence (parameters : Parameters)
    (guarded : parameters.decoder.Guarded)
    (wrapper : OptionalWrapper Nat (Fin internalCount) (Fin parameters.decoder.roots.length))
    (pairs : ∀ output ∈ wrapper.tree.leaves, wrapper.observedPairs output = nativePair parameters output)
    (selected : List (Fin parameters.decoder.roots.length)) (nonempty : selected ≠ [])
    (leaves : ∀ output ∈ selected, output ∈ wrapper.tree.leaves)
    (absent : parameters.drive = true → Controller.NativeProof.Decoder.NoDiscrepancy parameters selected.toFinset)
    (rename : WrapperLabel parameters internalCount → Fin v) : SelectedRefutation parameters wrapper selected rename := by
  let prefixState := nativeSelectedPrefix parameters (selectedInputRows parameters wrapper selected)
    (fun clause member => List.mem_append_left _ (List.mem_append_left _ member)) rename selected guarded
    absent
  have equal : ∀ output ∈ selected, DirectionPair prefixState.state []
      (rename (.inl (wrapper.observedPairs output).1.1), (wrapper.observedPairs output).1.2)
      (rename (.inl (wrapper.observedPairs output).2.1), (wrapper.observedPairs output).2.2) := by
    intro output member
    rw [pairs output (leaves output member)]
    exact prefixState.pairs output member
  let suffix := selectedAfterPrefix parameters wrapper selected nonempty leaves rename prefixState.state
    prefixState.steps prefixState.checked equal
  have empty : suffix.result.clause = [] := by
    cases shape : suffix.result.clause with
    | nil => rfl
    | cons head tail =>
      exact False.elim (by have bad := suffix.result.subset head (by rw [shape]; simp); simpa using bad)
  let trace : Trace v := ⟨(selectedFiniteInput parameters wrapper selected rename).clauses.size,
    prefixState.steps ++ suffix.steps, suffix.result.row.id⟩
  refine ⟨trace, ?_⟩
  have combined : runSteps (initialState (selectedFiniteInput parameters wrapper selected rename)) trace.steps = some suffix.state := by
    rw [runSteps_append]
    change (runSteps (initialState (ofClauses ((selectedInputRows parameters wrapper selected).map (Rows.mapClause rename)) )) prefixState.steps).bind _ = _
    rw [prefixState.checked]
    exact suffix.checked
  have final : suffix.state.rows trace.finalClauseId = some [] :=
    suffix.result.row.present.trans (congrArg some empty)
  unfold Controller.Resolution.check
  rw [ite_eq_left (show trace.originalClauseCount = (selectedFiniteInput parameters wrapper selected rename).clauses.size from rfl), combined]
  simp only [final]
  rfl


theorem selectedRefutationSize (parameters : Parameters)
    (guarded : parameters.decoder.Guarded)
    (wrapper : OptionalWrapper Nat (Fin internalCount) (Fin parameters.decoder.roots.length))
    (pairs : ∀ output ∈ wrapper.tree.leaves, wrapper.observedPairs output = nativePair parameters output)
    (selected : List (Fin parameters.decoder.roots.length)) (nonempty : selected ≠ [])
    (leaves : ∀ output ∈ selected, output ∈ wrapper.tree.leaves)
    (absent : parameters.drive = true → Controller.NativeProof.Decoder.NoDiscrepancy parameters selected.toFinset)
    (rename : WrapperLabel parameters internalCount → Fin v) :
    (selectedRefutationOfAbsence parameters guarded wrapper pairs selected nonempty leaves absent rename).trace.steps.length ≤
      selectedPrefixBudget parameters selected.dedup.length + (5 * selected.length - 1) := by
  unfold selectedRefutationOfAbsence
  dsimp only
  rw [List.length_append]
  apply (Nat.add_le_add_right (nativeSelectedPrefixSize _ _ _ _ _ _ _) _).trans
  exact Nat.add_le_add_left (selectedAfterPrefix _ _ _ _ _ _ _ _ _ _).count _

theorem optionalRefutationFromPrefixSize (parameters : Parameters)
    (wrapper : OptionalWrapper Nat (Fin internalCount) (Fin parameters.decoder.roots.length))
    (rename : WrapperLabel parameters internalCount → Fin v)
    (proofPrefix : OptionalEqualityPrefix parameters wrapper rename) :
    (optionalRefutationFromPrefix parameters wrapper rename proofPrefix).trace.steps.length ≤
      proofPrefix.steps.length + (5 * wrapper.tree.leaves.length - 1) := by
  unfold optionalRefutationFromPrefix
  dsimp only
  rw [List.length_append]
  exact Nat.add_le_add_left (optionalAfterPrefix _ _ _ _ _ _ _ _).count _

def optionalDrivenPrefix (parameters : Parameters) (raw : parameters.layout = .raw)
    (guarded : parameters.decoder.Guarded)
    (wrapper : OptionalWrapper Nat (Fin internalCount) (Fin parameters.decoder.roots.length))
    (pairs : ∀ output ∈ wrapper.tree.leaves, wrapper.observedPairs output = nativePair parameters output)
    (unsat : Unsatisfiable (optionalNativeInput parameters wrapper))
    (rename : WrapperLabel parameters internalCount → Fin v) : OptionalEqualityPrefix parameters wrapper rename := by
  let prefixState := nativeSelectedPrefix parameters (optionalInputRows parameters wrapper)
    (fun clause member => List.mem_append_left _ member) rename wrapper.tree.leaves guarded
    (fun drive => optional_native_absence parameters raw drive wrapper pairs unsat)
  refine ⟨prefixState.state, prefixState.steps, prefixState.checked, ?_⟩
  intro output member
  rw [pairs output member]
  exact prefixState.pairs output member


theorem optionalDrivenPrefixSize (parameters : Parameters) (raw : parameters.layout = .raw)
    (guarded : parameters.decoder.Guarded)
    (wrapper : OptionalWrapper Nat (Fin internalCount) (Fin parameters.decoder.roots.length))
    (pairs : ∀ output ∈ wrapper.tree.leaves, wrapper.observedPairs output = nativePair parameters output)
    (unsat : Unsatisfiable (optionalNativeInput parameters wrapper))
    (rename : WrapperLabel parameters internalCount → Fin v) :
    (optionalDrivenPrefix parameters raw guarded wrapper pairs unsat rename).steps.length ≤
      selectedPrefixBudget parameters wrapper.tree.leaves.dedup.length := by
  unfold optionalDrivenPrefix
  dsimp only
  exact nativeSelectedPrefixSize _ _ _ _ _ _ _

/-- The optional wrapper refutation has an additive counted suffix, with the
native prefix budget independent of the ambient wrapper variable count. -/
theorem optional_refutation_parameter_bound (parameters : Parameters) (raw : parameters.layout = .raw)
    (guarded : parameters.decoder.Guarded)
    (wrapper : OptionalWrapper Nat (Fin internalCount) (Fin parameters.decoder.roots.length))
    (pairs : ∀ output ∈ wrapper.tree.leaves, wrapper.observedPairs output = nativePair parameters output)
    (unsat : Unsatisfiable (optionalNativeInput parameters wrapper))
    (rename : WrapperLabel parameters internalCount → Fin v) :
    ∃ result : OptionalRefutation parameters wrapper rename,
      result.trace.steps.length ≤ selectedPrefixBudget parameters wrapper.tree.leaves.dedup.length +
        (5 * wrapper.tree.leaves.length - 1) := by
  let prefixState := optionalDrivenPrefix parameters raw guarded wrapper pairs unsat rename
  refine ⟨optionalRefutationFromPrefix parameters wrapper rename prefixState, ?_⟩
  exact (optionalRefutationFromPrefixSize parameters wrapper rename prefixState).trans
    (Nat.add_le_add_right (optionalDrivenPrefixSize parameters raw guarded wrapper pairs unsat rename) _)

end RetainedPrefix

section CoreSize
open Controller.Native Controller.Native.SourceController
open Controller.NativeProof.SourceFoldOwners Controller.NativeProof.SourceFoldOccurrences

/-- Declared native primary variables, retained producer outputs, original
core literal occurrences and the two native incidences of each observed pair.
Source allocation holes and private wrapper labels are not counted. -/
def nativeCoreSize (parameters : Parameters) (observed : Nat) : Nat :=
  SourceInitialIDs.rootCount parameters + (nativeCoreEntries parameters).length +
    ((nativeCoreRows parameters).map List.length).sum + 2 * observed

theorem retainedBlockLengthLe (parameters : Parameters) (start count : Nat)
    (bounded : start + count ≤ (compile parameters).entries.length)
    (retained : ∀ index, start ≤ index → index < start + count → retainedIndex parameters index) :
    count ≤ (nativeCoreEntries parameters).length := by
  let place : Fin count → Fin (compile parameters).entries.length :=
    fun index => ⟨start + index.val, by have := index.isLt; omega⟩
  have injective : Function.Injective place := by
    intro first second same
    have values := congrArg Fin.val same
    apply Fin.ext
    change start + first.val = start + second.val at values
    omega
  have small := ((List.nodup_finRange count).map injective).length_le_of_subset
    (l₂ := (List.finRange (compile parameters).entries.length).filter
      (fun index => decide (retainedIndex parameters index.val))) (by
        intro index member
        obtain ⟨original, _, rfl⟩ := List.mem_map.mp member
        apply List.mem_filter.mpr
        exact ⟨List.mem_finRange _, decide_eq_true (retained _ (by simp [place])
          (by dsimp [place]; have := original.isLt; omega))⟩)
  simpa only [nativeCoreEntries, List.length_map, List.length_finRange] using small

theorem retainedControllerCostLe (parameters : Parameters) :
    sourceControllerProducerCost parameters ≤ (nativeCoreEntries parameters).length := by
  obtain ⟨suffix, same⟩ := controller_before_compile (parameters := parameters)
  have bound : (controller parameters).entries.length ≤ (compile parameters).entries.length := by
    rw [same, List.length_append]; omega
  have actual := retainedBlockLengthLe parameters 0 (controller parameters).entries.length (by omega)
    (fun index _ before => Or.inl (by omega))
  change (controller parameters).sourceProducerCount ≤ _ at actual
  rw [(controller_source_counts parameters).1] at actual
  exact actual

theorem retainedDecoderCostLe (parameters : Parameters) :
    sourceDecoderProducerCost parameters ≤ (nativeCoreEntries parameters).length := by
  let start := decoderStart (parameters := parameters) .faulty
  let finish := attachDecoder parameters .faulty start
  have count : finish.entries.length = start.entries.length + sourceDecoderProducerCost parameters :=
    (attachDecoder_source_counts parameters .faulty start).1
  obtain ⟨suffix, same⟩ := decoder_end_before_compile (parameters := parameters) .faulty
  have bound : finish.entries.length ≤ (compile parameters).entries.length := by
    change (compile parameters).entries = finish.entries ++ suffix at same
    rw [same, List.length_append]; omega
  apply retainedBlockLengthLe parameters start.entries.length _ (by omega)
  intro index after before
  exact Or.inr (Or.inr ⟨after, by change index < finish.entries.length; omega⟩)

theorem coreEntriesCount (parameters : Parameters) :
    (coreCursor parameters).entries.length = sourceControllerProducerCost parameters +
      (parameters.buses + parameters.channels) + sourceFoldProducerCount (parameters.buses + parameters.channels) +
      2 * sourceDecoderProducerCost parameters := by
  change (coreCursor parameters).sourceProducerCount = _
  unfold coreCursor
  rw [(attachDecoder_source_counts parameters .faulty _).1,
    (attachDecoder_source_counts parameters .healthy _).1,
    (originalObservations_source_counts parameters _).1, (controller_source_counts parameters).1]
  omega

theorem coreVariableCount_le (parameters : Parameters) (observed : Nat) :
    coreVariableCount parameters ≤ 6 * nativeCoreSize parameters observed := by
  have channels : 2 ≤ parameters.channels := parameters.bridge.two_le
  have buses := parameters.positiveBuses
  have controller := retainedControllerCostLe parameters
  have decoder := retainedDecoderCostLe parameters
  have fold : sourceFoldProducerCount (parameters.buses + parameters.channels) ≤ parameters.buses + parameters.channels := by
    unfold sourceFoldProducerCount
    split <;> omega
  have nb : parameters.buses ≤ parameters.channels * parameters.buses := by nlinarith
  unfold coreVariableCount Cursor.lastID
  rw [coreEntriesCount]
  unfold nativeCoreSize SourceInitialIDs.rootCount
  omega

theorem selectedPrefixBudget_cubic (parameters : Parameters) (queries size : Nat)
    (allocated : parameters.channels * (parameters.buses + 1) ≤ size)
    (decoder : sourceDecoderProducerCost parameters ≤ size)
    (outputs : queries ≤ size) (queryUniverse : coreVariableCount parameters ≤ 6 * size) :
    selectedPrefixBudget parameters queries ≤ 1000000 * size ^ 3 := by
  have channelsPositive : 1 ≤ parameters.channels := by have := parameters.bridge.two_le; omega
  have channelBound : parameters.channels ≤ size := by nlinarith only [allocated]
  have product : parameters.channels * parameters.buses ≤ size := by nlinarith only [allocated]
  have busBound : parameters.buses ≤ size :=
    (show parameters.buses ≤ parameters.channels * parameters.buses by nlinarith only [channelsPositive]).trans product
  have positive : 1 ≤ size := channelsPositive.trans channelBound
  have nSquare := Nat.mul_le_mul channelBound channelBound
  have bSquare := Nat.mul_le_mul busBound busBound
  have nbSquare := Nat.mul_le_mul product busBound
  have nbCube := Nat.mul_le_mul nbSquare busBound
  have qv := Nat.mul_le_mul outputs queryUniverse
  have vSquare : size ≤ size ^ 2 := by nlinarith only [positive]
  have vCube : size ^ 2 ≤ size ^ 3 := by
    have actual := Nat.mul_le_mul_right (size * size) positive
    nlinarith only [actual]
  unfold selectedPrefixBudget NativeResolution.drivenInitialBudget NativeResolution.preparationBudget
    NativeResolution.healthyQualifierBudget NativeResolution.mixedBudget
    SourceQualifierSchedule.qualifierProgramBudget SourceQualifierSchedule.channelQualifierBudget
    SourceMixedSchedule.qualifierBudget
  nlinarith only [channelBound, product, busBound, positive, nSquare, bSquare, nbSquare, nbCube,
    qv, vSquare, vCube, decoder, outputs]

theorem nativeCoreBudget_cubic (parameters : Parameters) (outputs : List (Fin parameters.decoder.roots.length)) :
    selectedPrefixBudget parameters outputs.dedup.length ≤ 1000000 * (nativeCoreSize parameters outputs.length) ^ 3 := by
  apply selectedPrefixBudget_cubic
  · unfold nativeCoreSize SourceInitialIDs.rootCount
    simp only [Nat.mul_add, Nat.mul_one]
    omega
  · exact (retainedDecoderCostLe parameters).trans (by unfold nativeCoreSize; omega)
  · have count := (List.dedup_sublist outputs).length_le
    unfold nativeCoreSize
    omega
  · exact coreVariableCount_le parameters outputs.length

/-- Repeating a selected index increases only its explicit wrapper charge. -/
theorem nativeCoreBudget_distinct_cubic (parameters : Parameters) (outputs : List (Fin parameters.decoder.roots.length)) :
    selectedPrefixBudget parameters outputs.dedup.length ≤
      1000000 * (nativeCoreSize parameters outputs.dedup.length) ^ 3 := by
  simpa only [List.dedup_idem] using nativeCoreBudget_cubic parameters outputs.dedup

end CoreSize

section WrapperSize
open Controller.Native Controller.Native.SourceController Controller.Native.ObservationProjection
variable {internalCount : Nat}

/-- Original wrapper rows and literal occurrences, including unused internal
activity clauses. A selected wrapper also counts its added disjunction. -/
def wrapperSize (parameters : Parameters)
    (wrapper : OptionalWrapper Nat (Fin internalCount) (Fin parameters.decoder.roots.length)) : Nat :=
  (optionalRows wrapper).length + ((optionalRows wrapper).map List.length).sum

def selectedWrapperSize (parameters : Parameters)
    (wrapper : OptionalWrapper Nat (Fin internalCount) (Fin parameters.decoder.roots.length))
    (selected : List (Fin parameters.decoder.roots.length)) : Nat :=
  wrapperSize parameters wrapper + 1 + selected.length

theorem leaves_le_wrapperSize (parameters : Parameters)
    (wrapper : OptionalWrapper Nat (Fin internalCount) (Fin parameters.decoder.roots.length)) :
    wrapper.tree.leaves.length ≤ wrapperSize parameters wrapper := by
  have count : ∀ outputs : List (Fin parameters.decoder.roots.length),
      outputs.length ≤ (outputs.flatMap (fun output => guardRows (.observed output : PrivateActivity (Fin internalCount) _)
        (wrapper.observedPairs output))).length := by
    intro outputs
    induction outputs with
    | nil => simp
    | cons output rest ih =>
      simp only [List.length_cons, List.flatMap_cons, List.length_append]
      change rest.length + 1 ≤ 2 + _
      omega
  have actual := count wrapper.tree.leaves
  unfold wrapperSize optionalRows
  simp only [List.length_append]
  omega

theorem optional_refutation_cubic (parameters : Parameters) (raw : parameters.layout = .raw)
    (guarded : parameters.decoder.Guarded)
    (wrapper : OptionalWrapper Nat (Fin internalCount) (Fin parameters.decoder.roots.length))
    (pairs : ∀ output ∈ wrapper.tree.leaves, wrapper.observedPairs output = nativePair parameters output)
    (unsat : Unsatisfiable (optionalNativeInput parameters wrapper))
    (rename : WrapperLabel parameters internalCount → Fin v) :
    ∃ result : OptionalRefutation parameters wrapper rename,
      result.trace.steps.length ≤ 1000000 * (nativeCoreSize parameters wrapper.tree.leaves.length) ^ 3 +
        5 * wrapperSize parameters wrapper := by
  obtain ⟨result, bound⟩ := optional_refutation_parameter_bound parameters raw guarded wrapper pairs unsat rename
  refine ⟨result, bound.trans ?_⟩
  have core := nativeCoreBudget_cubic parameters wrapper.tree.leaves
  have leaves := leaves_le_wrapperSize parameters wrapper
  omega

theorem selected_refutation_cubic (parameters : Parameters) (raw : parameters.layout = .raw)
    (guarded : parameters.decoder.Guarded)
    (wrapper : OptionalWrapper Nat (Fin internalCount) (Fin parameters.decoder.roots.length))
    (pairs : ∀ output ∈ wrapper.tree.leaves, wrapper.observedPairs output = nativePair parameters output)
    (selected : List (Fin parameters.decoder.roots.length)) (nonempty : selected ≠ [])
    (leaves : ∀ output ∈ selected, output ∈ wrapper.tree.leaves)
    (unsat : Unsatisfiable (selectedNativeInput parameters wrapper selected))
    (rename : WrapperLabel parameters internalCount → Fin v) :
    ∃ result : SelectedRefutation parameters wrapper selected rename,
      result.trace.steps.length ≤ 1000000 * (nativeCoreSize parameters selected.dedup.length) ^ 3 +
        5 * selectedWrapperSize parameters wrapper selected := by
  let absent := fun drive => selected_native_absence parameters raw drive wrapper pairs selected leaves unsat
  refine ⟨selectedRefutationOfAbsence parameters guarded wrapper pairs selected nonempty leaves absent rename, ?_⟩
  have bound := selectedRefutationSize parameters guarded wrapper pairs selected nonempty leaves absent rename
  have core := nativeCoreBudget_distinct_cubic parameters selected
  unfold selectedWrapperSize
  omega

end WrapperSize

section Runtime
open Controller.Native Controller.Native.ObservationProjection
variable {internalCount : Nat}

def optionalRefutationOfAbsence (parameters : Parameters) (guarded : parameters.decoder.Guarded)
    (wrapper : OptionalWrapper Nat (Fin internalCount) (Fin parameters.decoder.roots.length))
    (pairs : ∀ output ∈ wrapper.tree.leaves, wrapper.observedPairs output = nativePair parameters output)
    (absent : parameters.drive = true → Controller.NativeProof.Decoder.NoDiscrepancy parameters wrapper.tree.leaves.toFinset) :
    OptionalRefutation parameters wrapper (canonicalWrapperRename parameters wrapper) := by
  let labels := canonicalWrapperLabels parameters wrapper
  let rename := fun label => canonicalLabelIndex parameters labels label
  let native := nativeSelectedPrefix parameters (optionalInputRows parameters wrapper)
    (fun clause member => List.mem_append_left _ member) rename wrapper.tree.leaves guarded absent
  let prefixState : OptionalEqualityPrefix parameters wrapper rename :=
    ⟨native.state, native.steps, native.checked, fun output member => by
      rw [pairs output member]
      exact native.pairs output member⟩
  exact optionalRefutationFromPrefix parameters wrapper rename prefixState

def runOptional (parameters : Parameters)
    (wrapper : OptionalWrapper Nat (Fin internalCount) (Fin parameters.decoder.roots.length)) :
    Option (Trace (canonicalWrapperCount parameters wrapper)) :=
  if accepted : wrapperSupported parameters wrapper = true then
    if absent : wrapperDetect parameters wrapper.tree.leaves = none then
      some (optionalRefutationOfAbsence parameters (wrapperSupported_native parameters wrapper accepted).2 wrapper
        (wrapperSupported_pairs parameters wrapper accepted)
        ((wrapperDetect_none_iff parameters (wrapperSupported_native parameters wrapper accepted).2 _).mp absent)).trace
    else none
  else none

def runSelected (parameters : Parameters)
    (wrapper : OptionalWrapper Nat (Fin internalCount) (Fin parameters.decoder.roots.length))
    (selected : List (Fin parameters.decoder.roots.length)) : Option (Trace (canonicalWrapperCount parameters wrapper)) :=
  if accepted : wrapperSupported parameters wrapper = true then
    let labels := canonicalWrapperLabels parameters wrapper
    let rename := fun label => canonicalLabelIndex parameters labels label
    if nonempty : selected ≠ [] then
      if leaves : ∀ output ∈ selected, output ∈ wrapper.tree.leaves then
        if absent : wrapperDetect parameters selected = none then
          some (selectedRefutationOfAbsence parameters (wrapperSupported_native parameters wrapper accepted).2 wrapper (wrapperSupported_pairs parameters wrapper accepted)
            selected nonempty leaves
            ((wrapperDetect_none_iff parameters (wrapperSupported_native parameters wrapper accepted).2 _).mp absent)
            rename).trace
        else none
      else none
    else none
  else none

theorem runOptional_checked (parameters : Parameters)
    (wrapper : OptionalWrapper Nat (Fin internalCount) (Fin parameters.decoder.roots.length))
    (trace : Trace (canonicalWrapperCount parameters wrapper)) (returned : runOptional parameters wrapper = some trace) :
    check (canonicalOptionalInput parameters wrapper) trace = true := by
  unfold runOptional at returned
  split at returned
  · split at returned
    · cases Option.some.inj returned
      exact (optionalRefutationOfAbsence parameters _ wrapper _ _).accepted
    · simp at returned
  · simp at returned

theorem runSelected_checked (parameters : Parameters)
    (wrapper : OptionalWrapper Nat (Fin internalCount) (Fin parameters.decoder.roots.length))
    (selected : List (Fin parameters.decoder.roots.length)) (trace : Trace (canonicalWrapperCount parameters wrapper))
    (returned : runSelected parameters wrapper selected = some trace) :
    check (canonicalSelectedInput parameters wrapper selected) trace = true := by
  unfold runSelected at returned
  split at returned
  · dsimp only at returned
    split at returned
    · split at returned
      · split at returned
        · cases Option.some.inj returned
          exact (selectedRefutationOfAbsence parameters _ wrapper _ selected _ _ _ _).accepted
        · simp at returned
      · simp at returned
    · simp at returned
  · simp at returned

theorem runOptional_complete (parameters : Parameters)
    (wrapper : OptionalWrapper Nat (Fin internalCount) (Fin parameters.decoder.roots.length))
    (accepted : wrapperSupported parameters wrapper = true)
    (unsat : Unsatisfiable (canonicalOptionalInput parameters wrapper)) :
    ∃ trace, runOptional parameters wrapper = some trace ∧ check (canonicalOptionalInput parameters wrapper) trace = true := by
  have native := wrapperSupported_native parameters wrapper accepted
  have pairs := wrapperSupported_pairs parameters wrapper accepted
  have original : Unsatisfiable (optionalNativeInput parameters wrapper) := by
    apply unsatisfiable_of_decode _ _ (canonicalWrapperDecode parameters wrapper) _ unsat
    rw [canonicalOptionalInput_roundtrip, optionalInputRows_formula]
  have absent : wrapperDetect parameters wrapper.tree.leaves = none :=
    (wrapperDetect_none_iff parameters native.2 _).mpr
      (fun drive => optional_native_absence parameters native.1 drive wrapper pairs original)
  unfold runOptional
  simp only [accepted, absent, ↓reduceDIte]
  exact ⟨_, rfl, (optionalRefutationOfAbsence parameters _ wrapper _ _).accepted⟩

theorem runSelected_complete (parameters : Parameters)
    (wrapper : OptionalWrapper Nat (Fin internalCount) (Fin parameters.decoder.roots.length))
    (accepted : wrapperSupported parameters wrapper = true)
    (selected : List (Fin parameters.decoder.roots.length)) (nonempty : selected ≠ [])
    (leaves : ∀ output ∈ selected, output ∈ wrapper.tree.leaves)
    (unsat : Unsatisfiable (canonicalSelectedInput parameters wrapper selected)) :
    ∃ trace, runSelected parameters wrapper selected = some trace ∧
      check (canonicalSelectedInput parameters wrapper selected) trace = true := by
  have native := wrapperSupported_native parameters wrapper accepted
  have pairs := wrapperSupported_pairs parameters wrapper accepted
  have original : Unsatisfiable (selectedNativeInput parameters wrapper selected) := by
    apply unsatisfiable_of_decode _ _ (canonicalWrapperDecode parameters wrapper) _ unsat
    rw [canonicalSelectedInput_roundtrip parameters wrapper selected leaves, selectedInputRows_formula]
  have absent : wrapperDetect parameters selected = none :=
    (wrapperDetect_none_iff parameters native.2 _).mpr
      (fun drive => selected_native_absence parameters native.1 drive wrapper pairs selected leaves original)
  unfold runSelected
  rw [dite_eq_left accepted, dite_eq_left nonempty, dite_eq_left leaves, dite_eq_left absent]
  exact ⟨_, rfl, (selectedRefutationOfAbsence parameters _ wrapper _ selected _ _ _ _).accepted⟩


theorem optionalRefutationOfAbsenceSize (parameters : Parameters) (guarded : parameters.decoder.Guarded)
    (wrapper : OptionalWrapper Nat (Fin internalCount) (Fin parameters.decoder.roots.length))
    (pairs : ∀ output ∈ wrapper.tree.leaves, wrapper.observedPairs output = nativePair parameters output)
    (absent : parameters.drive = true → Controller.NativeProof.Decoder.NoDiscrepancy parameters wrapper.tree.leaves.toFinset) :
    (optionalRefutationOfAbsence parameters guarded wrapper pairs absent).trace.steps.length ≤
      1000000 * (nativeCoreSize parameters wrapper.tree.leaves.length) ^ 3 + 5 * wrapperSize parameters wrapper := by
  unfold optionalRefutationOfAbsence
  dsimp only
  apply (optionalRefutationFromPrefixSize _ _ _ _).trans
  have first := nativeSelectedPrefixSize parameters (optionalInputRows parameters wrapper)
    (fun clause member => List.mem_append_left _ member) (canonicalWrapperRename parameters wrapper)
    wrapper.tree.leaves guarded absent
  have core := nativeCoreBudget_cubic parameters wrapper.tree.leaves
  have leaves := leaves_le_wrapperSize parameters wrapper
  exact Nat.add_le_add (first.trans core) (by omega)

theorem runOptional_bound (parameters : Parameters)
    (wrapper : OptionalWrapper Nat (Fin internalCount) (Fin parameters.decoder.roots.length))
    (trace : Trace (canonicalWrapperCount parameters wrapper)) (returned : runOptional parameters wrapper = some trace) :
    trace.steps.length ≤ 1000000 * (nativeCoreSize parameters wrapper.tree.leaves.length) ^ 3 +
      5 * wrapperSize parameters wrapper := by
  unfold runOptional at returned
  split at returned
  · split at returned
    · cases Option.some.inj returned
      exact optionalRefutationOfAbsenceSize _ _ _ _ _
    · simp at returned
  · simp at returned

theorem runSelected_bound (parameters : Parameters)
    (wrapper : OptionalWrapper Nat (Fin internalCount) (Fin parameters.decoder.roots.length))
    (selected : List (Fin parameters.decoder.roots.length)) (trace : Trace (canonicalWrapperCount parameters wrapper))
    (returned : runSelected parameters wrapper selected = some trace) :
    trace.steps.length ≤ 1000000 * (nativeCoreSize parameters selected.dedup.length) ^ 3 +
      5 * selectedWrapperSize parameters wrapper selected := by
  unfold runSelected at returned
  split at returned
  · dsimp only at returned
    split at returned
    · split at returned
      · split at returned
        · cases Option.some.inj returned
          apply (selectedRefutationSize _ _ _ _ _ _ _ _ _).trans
          have core := nativeCoreBudget_distinct_cubic parameters selected
          unfold selectedWrapperSize
          omega
        · simp at returned
      · simp at returned
    · simp at returned
  · simp at returned

/-- Parameter-only optional frontend: every supported UNSAT canonical input
returns a checked ordinary-resolution trace with the B.2 size bound. -/
theorem runOptional_complete_cubic (parameters : Parameters)
    (wrapper : OptionalWrapper Nat (Fin internalCount) (Fin parameters.decoder.roots.length))
    (accepted : wrapperSupported parameters wrapper = true)
    (unsat : Unsatisfiable (canonicalOptionalInput parameters wrapper)) :
    ∃ trace, runOptional parameters wrapper = some trace ∧
      check (canonicalOptionalInput parameters wrapper) trace = true ∧
      trace.steps.length ≤ 1000000 * (nativeCoreSize parameters wrapper.tree.leaves.length) ^ 3 +
        5 * wrapperSize parameters wrapper := by
  obtain ⟨trace, returned, checked⟩ := runOptional_complete parameters wrapper accepted unsat
  exact ⟨trace, returned, checked, runOptional_bound parameters wrapper trace returned⟩

/-- Only the selected outputs must lack discrepancies; unselected outputs
may differ. Repeated selected incidences are charged in the emitted input. -/
theorem runSelected_complete_cubic (parameters : Parameters)
    (wrapper : OptionalWrapper Nat (Fin internalCount) (Fin parameters.decoder.roots.length))
    (accepted : wrapperSupported parameters wrapper = true)
    (selected : List (Fin parameters.decoder.roots.length)) (nonempty : selected ≠ [])
    (leaves : ∀ output ∈ selected, output ∈ wrapper.tree.leaves)
    (unsat : Unsatisfiable (canonicalSelectedInput parameters wrapper selected)) :
    ∃ trace, runSelected parameters wrapper selected = some trace ∧
      check (canonicalSelectedInput parameters wrapper selected) trace = true ∧
      trace.steps.length ≤ 1000000 * (nativeCoreSize parameters selected.dedup.length) ^ 3 +
        5 * selectedWrapperSize parameters wrapper selected := by
  obtain ⟨trace, returned, checked⟩ := runSelected_complete parameters wrapper accepted selected nonempty leaves unsat
  exact ⟨trace, returned, checked, runSelected_bound parameters wrapper selected trace returned⟩

end Runtime


section EssentialRows
open Controller.Native Controller.Native.SourceController Controller.Native.ObservationProjection
open Controller.NativeProof.SourceDecoderTraversal
variable {internalCount : Nat}

structure CountedRefutation (formula : FiniteFormula v) (budget : Nat) where
  trace : Trace v
  accepted : check formula trace = true
  count : trace.steps.length ≤ budget

def finishRefutation (formula : FiniteFormula v) (state : State v) (steps : List (Step v))
    (checked : runSteps (initialState formula) steps = some state)
    (suffix : SubclauseProjection state [] budget) : CountedRefutation formula (steps.length + budget) := by
  have empty : suffix.result.clause = [] := List.eq_nil_iff_forall_not_mem.mpr (by
    intro literal member; simpa using suffix.result.subset literal member)
  let trace : Trace v := ⟨formula.clauses.size, steps ++ suffix.steps, suffix.result.row.id⟩
  have combined : runSteps (initialState formula) trace.steps = some suffix.state := by
    rw [runSteps_append, checked]; exact suffix.checked
  have final : suffix.state.rows trace.finalClauseId = some [] :=
    suffix.result.row.present.trans (congrArg some empty)
  refine ⟨trace, ?_, ?_⟩
  · unfold check
    rw [ite_eq_left (show trace.originalClauseCount = formula.clauses.size from rfl), combined]
    simp only [final]; rfl
  · change (steps ++ suffix.steps).length ≤ _
    rw [List.length_append]
    exact Nat.add_le_add_left suffix.count _

/-- These rows contain no internal activity guards or optional Horn clauses. -/
def essentialOptionalRows (parameters : Parameters)
    (wrapper : OptionalWrapper Nat (Fin internalCount) (Fin parameters.decoder.roots.length)) :
    List (Clause (WrapperLabel parameters internalCount)) :=
  taggedCoreRows parameters ++
    wrapper.tree.leaves.flatMap (fun output => guardRows (.observed output) (wrapper.observedPairs output)) ++
    wrapper.tree.rows [] ++ [[(Sum.inr (wrapper.tree.root []), true)]]

def essentialSelectedRows (parameters : Parameters)
    (wrapper : OptionalWrapper Nat (Fin internalCount) (Fin parameters.decoder.roots.length))
    (selected : List (Fin parameters.decoder.roots.length)) : List (Clause (WrapperLabel parameters internalCount)) :=
  taggedCoreRows parameters ++
    selected.flatMap (fun output => guardRows (.observed output) (wrapper.observedPairs output)) ++
    [selected.map (fun output => (Sum.inr (.observed output), true))]

theorem essentialOptionalRows_subset (parameters : Parameters)
    (wrapper : OptionalWrapper Nat (Fin internalCount) (Fin parameters.decoder.roots.length)) :
    essentialOptionalRows parameters wrapper ⊆ optionalInputRows parameters wrapper := by
  have core : taggedCoreRows parameters ⊆ optionalInputRows parameters wrapper := List.subset_append_left _ _
  have guards : wrapper.tree.leaves.flatMap (fun output => guardRows (.observed output) (wrapper.observedPairs output)) ⊆
      optionalInputRows parameters wrapper := by
    intro clause member
    obtain ⟨output, leaf, guard⟩ := List.mem_flatMap.mp member
    exact List.mem_append_right _ (optionalRows_guard wrapper output leaf clause guard)
  have tree : wrapper.tree.rows [] ⊆ optionalInputRows parameters wrapper := by
    intro clause member; exact List.mem_append_right _ (optionalRows_tree wrapper clause member)
  have root := List.mem_append_right (taggedCoreRows parameters) (optionalRows_root wrapper)
  intro clause member
  simp only [essentialOptionalRows, List.mem_append, List.mem_singleton] at member
  rcases member with ((member | member) | member) | rfl
  · exact core member
  · exact guards member
  · exact tree member
  · exact root

theorem essentialSelectedRows_subset (parameters : Parameters)
    (wrapper : OptionalWrapper Nat (Fin internalCount) (Fin parameters.decoder.roots.length))
    (selected : List (Fin parameters.decoder.roots.length))
    (leaves : ∀ output ∈ selected, output ∈ wrapper.tree.leaves) :
    essentialSelectedRows parameters wrapper selected ⊆ selectedInputRows parameters wrapper selected := by
  have core : taggedCoreRows parameters ⊆ selectedInputRows parameters wrapper selected := by
    intro clause member; exact List.mem_append_left _ (List.mem_append_left _ member)
  have guards : selected.flatMap (fun output => guardRows (.observed output) (wrapper.observedPairs output)) ⊆
      selectedInputRows parameters wrapper selected := by
    intro clause member
    obtain ⟨output, leaf, guard⟩ := List.mem_flatMap.mp member
    exact List.mem_append_left _ (List.mem_append_right _ (optionalRows_guard wrapper output (leaves output leaf) clause guard))
  intro clause member
  simp only [essentialSelectedRows, List.mem_append, List.mem_singleton] at member
  rcases member with (member | member) | rfl
  · exact core member
  · exact guards member
  · simp [selectedInputRows]

/-- A refutation constructed on the strict retained subformula witnesses that
optional internal activities and Horn clauses need not be proof parents. -/
def essentialOptionalRefutation (parameters : Parameters) (guarded : parameters.decoder.Guarded)
    (wrapper : OptionalWrapper Nat (Fin internalCount) (Fin parameters.decoder.roots.length))
    (pairs : ∀ output ∈ wrapper.tree.leaves, wrapper.observedPairs output = nativePair parameters output)
    (absent : parameters.drive = true → Controller.NativeProof.Decoder.NoDiscrepancy parameters wrapper.tree.leaves.toFinset)
    (rename : WrapperLabel parameters internalCount → Fin v) :
    CountedRefutation (ofClauses ((essentialOptionalRows parameters wrapper).map (Rows.mapClause rename)))
      (1000000 * (nativeCoreSize parameters wrapper.tree.leaves.length) ^ 3 + (5 * wrapper.tree.leaves.length - 1)) := by
  let clauses := essentialOptionalRows parameters wrapper
  have core : ∀ clause ∈ taggedCoreRows parameters, clause ∈ clauses := by
    intro clause member
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ member))
  let prefixState := nativeSelectedPrefix parameters clauses core rename wrapper.tree.leaves guarded absent
  have run : runSteps (initialState (relabel rename (ofClauses clauses))) prefixState.steps = some prefixState.state := by
    rw [mapped_formula]; exact prefixState.checked
  let guards := fun output (leaf : output ∈ wrapper.tree.leaves) => guardsFromRows rename clauses wrapper output (by
    intro clause member
    have present : clause ∈ wrapper.tree.leaves.flatMap (fun output => guardRows (.observed output) (wrapper.observedPairs output)) :=
      List.mem_flatMap.mpr ⟨output, leaf, member⟩
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ present)))
  let tree := emittedTree rename clauses wrapper.tree [] (by
    intro clause member; exact List.mem_append_left _ (List.mem_append_right _ member))
  let root : AvailableSubclause (initialState (relabel rename (ofClauses clauses)))
      [(rename (.inr (wrapper.tree.root [])), true)] := by
    simpa [Rows.mapClause] using ofRow (memberRow rename clauses
      [(Sum.inr (wrapper.tree.root []), true)] (by simp [clauses, essentialOptionalRows]))
  have equal : ∀ output ∈ wrapper.tree.leaves, DirectionPair prefixState.state []
      (rename (.inl (wrapper.observedPairs output).1.1), (wrapper.observedPairs output).1.2)
      (rename (.inl (wrapper.observedPairs output).2.1), (wrapper.observedPairs output).2.2) := by
    intro output member; rw [pairs output member]; exact prefixState.pairs output member
  let suffix := optionalSuffix prefixState.state [] (fun activity => (rename (.inr activity), true))
    (fun output => (rename (.inl (wrapper.observedPairs output).1.1), (wrapper.observedPairs output).1.2))
    (fun output => (rename (.inl (wrapper.observedPairs output).2.1), (wrapper.observedPairs output).2.2))
    wrapper.tree (fun output member => (guards output member).afterTrace _ _ run) equal
    (tree.afterTrace _ _ run) (afterTrace root _ _ run)
  let result := finishRefutation _ prefixState.state prefixState.steps prefixState.checked suffix
  refine ⟨result.trace, result.accepted, result.count.trans ?_⟩
  exact Nat.add_le_add_right ((nativeSelectedPrefixSize _ _ _ _ _ _ _).trans
    (nativeCoreBudget_cubic parameters wrapper.tree.leaves)) _

def essentialSelectedRefutation (parameters : Parameters) (guarded : parameters.decoder.Guarded)
    (wrapper : OptionalWrapper Nat (Fin internalCount) (Fin parameters.decoder.roots.length))
    (pairs : ∀ output ∈ wrapper.tree.leaves, wrapper.observedPairs output = nativePair parameters output)
    (selected : List (Fin parameters.decoder.roots.length)) (nonempty : selected ≠ [])
    (leaves : ∀ output ∈ selected, output ∈ wrapper.tree.leaves)
    (absent : parameters.drive = true → Controller.NativeProof.Decoder.NoDiscrepancy parameters selected.toFinset)
    (rename : WrapperLabel parameters internalCount → Fin v) :
    CountedRefutation (ofClauses ((essentialSelectedRows parameters wrapper selected).map (Rows.mapClause rename)))
      (1000000 * (nativeCoreSize parameters selected.dedup.length) ^ 3 + (5 * selected.length - 1)) := by
  let clauses := essentialSelectedRows parameters wrapper selected
  have core : ∀ clause ∈ taggedCoreRows parameters, clause ∈ clauses := by
    intro clause member; exact List.mem_append_left _ (List.mem_append_left _ member)
  let prefixState := nativeSelectedPrefix parameters clauses core rename selected guarded absent
  have run : runSteps (initialState (relabel rename (ofClauses clauses))) prefixState.steps = some prefixState.state := by
    rw [mapped_formula]; exact prefixState.checked
  let guards := fun output (member : output ∈ selected) => guardsFromRows rename clauses wrapper output (by
    intro clause present
    have guard : clause ∈ selected.flatMap (fun output => guardRows (.observed output) (wrapper.observedPairs output)) :=
      List.mem_flatMap.mpr ⟨output, member, present⟩
    exact List.mem_append_left _ (List.mem_append_right _ guard))
  let requirement : AvailableSubclause (initialState (relabel rename (ofClauses clauses)))
      (selected.map (fun output => (rename (.inr (.observed output)), true))) := by
    simpa [Rows.mapClause, List.map_map, Function.comp_def] using ofRow (memberRow rename clauses
      (selected.map (fun output => (Sum.inr (.observed output), true))) (by simp [clauses, essentialSelectedRows]))
  have equal : ∀ output ∈ selected, DirectionPair prefixState.state []
      (rename (.inl (wrapper.observedPairs output).1.1), (wrapper.observedPairs output).1.2)
      (rename (.inl (wrapper.observedPairs output).2.1), (wrapper.observedPairs output).2.2) := by
    intro output member; rw [pairs output (leaves output member)]; exact prefixState.pairs output member
  let suffix := selectedSuffix prefixState.state [] (fun output => (rename (.inr (.observed output)), true))
    (fun output => (rename (.inl (wrapper.observedPairs output).1.1), (wrapper.observedPairs output).1.2))
    (fun output => (rename (.inl (wrapper.observedPairs output).2.1), (wrapper.observedPairs output).2.2))
    selected nonempty (fun output member => (guards output member).afterTrace _ _ run) equal
    (afterTrace requirement _ _ run)
  let result := finishRefutation _ prefixState.state prefixState.steps prefixState.checked suffix
  refine ⟨result.trace, result.accepted, result.count.trans ?_⟩
  exact Nat.add_le_add_right ((nativeSelectedPrefixSize _ _ _ _ _ _ _).trans
    (nativeCoreBudget_distinct_cubic parameters selected)) _

end EssentialRows

end Controller.Cost.WrapperResolution
