module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.SourceHealthyOne

@[expose] public section

/-! Selected healthy-one queries replay the computed finite zero-system trail
against the shared native row table. Discrepancy absence is supplied by the
independent model semantics. -/
namespace Controller.NativeProof.SourceHealthyOneQuery
open Controller.CNF Controller.Resolution Controller.Resolution.RUP
open Controller.Native Controller.Native.SourceController Controller.Decoder.ZeroSystem
open Controller.NativeProof.FoldProjection Controller.NativeProof.SourceFoldProjection
open Controller.NativeProof.SourceHealthyOne Controller.NativeProof.SourceStageCongruence
open Controller.NativeProof.HornNativeReplay
variable {parameters : Parameters} {v : Nat}

def handles (rename : Nat → Fin v) : Fin (parameters.channels + parameters.decoder.nodeCount) → Literal (Fin v) :=
  fun index => SourceForwardRows.handle rename .faulty (parameters.decoder.zeroIndex.symm index)

theorem lifted (rename : Nat → Fin v) (row : Clause parameters.decoder.ZeroVar) :
    liftClause (handles (parameters := parameters) rename) (Rows.mapClause parameters.decoder.zeroIndex row) =
      SourceForwardRows.clause rename .faulty row := by
  unfold liftClause Rows.mapClause SourceForwardRows.clause
  rw [List.map_map]
  apply List.map_congr_left
  intro literal member
  rcases literal with ⟨label, polarity⟩
  cases polarity <;> simp [handles, liftLiteral, SourceForwardRows.literal]

def fromNative (rename : Nat → Fin v) (prepared : Preparation (parameters := parameters) rename)
    (root : Fin parameters.decoder.nodeCount) (row : Clause parameters.decoder.ZeroVar)
    (origin : SourceForwardRows.Origin (parameters := parameters) rename .faulty prepared.proofPrefix.state
      (cofactor (parameters := parameters) rename) row) :
    HornRowTransport.Origin (handles (parameters := parameters) rename) prepared.proofPrefix.state
      (cofactor (parameters := parameters) rename ++ [SourceForwardRows.handle rename .faulty (.inr root)])
      (Rows.mapClause parameters.decoder.zeroIndex row) := by
  cases origin with
  | native available =>
    apply HornRowTransport.Origin.native
    rw [lifted]
    apply retarget available
    intro literal member
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member ⊢
    aesop
  | identity premise conclusion shape same =>
    apply HornRowTransport.Origin.identity (parameters.decoder.zeroIndex premise) (parameters.decoder.zeroIndex conclusion)
    · simpa only [Rows.mapClause, implicationClause, positiveClause, List.map_cons, List.map_nil] using
        congrArg (Rows.mapClause parameters.decoder.zeroIndex) shape
    · simpa only [handles, Equiv.symm_apply_apply] using same

def originalRows (root : Fin parameters.decoder.nodeCount) : List (Clause parameters.decoder.ZeroVar) :=
  (parameters.decoder.forwardClauses ++ parameters.decoder.channelClauses parameters.buses parameters.bridge.target ∅ ∅) ++
    [implicationClause (.inr root) []]

def rowOrigin (rename : Nat → Fin v) (prepared : Preparation (parameters := parameters) rename)
    (root : Fin parameters.decoder.nodeCount) (row : Clause parameters.decoder.ZeroVar)
    (present : row ∈ originalRows (parameters := parameters) root) :
    HornRowTransport.Origin (handles (parameters := parameters) rename) prepared.proofPrefix.state
      (cofactor (parameters := parameters) rename ++ [SourceForwardRows.handle rename .faulty (.inr root)])
      (Rows.mapClause parameters.decoder.zeroIndex row) := by
  letI : DecidablePred (fun row : Clause parameters.decoder.ZeroVar => row ∈ parameters.decoder.forwardClauses) :=
    fun row => SourceForwardRows.memDecidable row parameters.decoder.forwardClauses
  by_cases assumption : row = implicationClause (.inr root) []
  · apply HornRowTransport.Origin.assumption (parameters.decoder.zeroIndex (.inr root), false)
    · simpa only [Rows.mapClause, implicationClause, positiveClause, List.map_cons, List.map_nil] using
        congrArg (Rows.mapClause parameters.decoder.zeroIndex) assumption
    · rfl
    · simp [liftLiteral, handles, negate_negate]
  · by_cases forward : row ∈ parameters.decoder.forwardClauses
    · exact fromNative rename prepared root row (prepared.forward row forward)
    · let allChannels := positiveClause ((List.finRange parameters.channels).map (Sum.inl : Fin parameters.channels → parameters.decoder.ZeroVar))
      let target := positiveClause [(Sum.inl parameters.bridge.target : parameters.decoder.ZeroVar)]
      have classified : row = allChannels ∨ (parameters.buses = 1 ∧ row = target) := by
        have emptyTrue : parameters.decoder.trueUnitClauses ∅ = [] := by simp [Controller.Decoder.DAG.trueUnitClauses]
        have emptyFalse : parameters.decoder.falseUnitClauses ∅ = [] := by simp [Controller.Decoder.DAG.falseUnitClauses]
        by_cases one : parameters.buses = 1 <;>
          simpa [originalRows, Controller.Decoder.DAG.channelClauses, emptyTrue, emptyFalse,
            forward, assumption, one, allChannels, target] using present
      by_cases nonempty : row = allChannels
      · apply HornRowTransport.Origin.native
        rw [lifted]
        have mapped : SourceForwardRows.clause rename .faulty row =
            (List.finRange parameters.channels).map (SourceDecoderEvaluation.qualifierLiteral rename .faulty) := by
          simpa [allChannels, SourceForwardRows.clause, SourceForwardRows.literal, SourceForwardRows.handle,
            positiveClause, List.map_map, Function.comp_def] using congrArg (SourceForwardRows.clause rename .faulty) nonempty
        rw [mapped]
        apply retarget prepared.nonempty
        intro literal member
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member ⊢
        aesop
      · have targetRow := classified.resolve_left nonempty
        apply HornRowTransport.Origin.native
        rw [lifted]
        have mapped : SourceForwardRows.clause rename .faulty row =
            [SourceDecoderEvaluation.qualifierLiteral rename .faulty parameters.bridge.target] := by
          simpa [target, SourceForwardRows.clause, SourceForwardRows.literal, SourceForwardRows.handle,
            positiveClause] using congrArg (SourceForwardRows.clause rename .faulty) targetRow.2
        rw [mapped]
        apply retarget (prepared.targetUnit targetRow.1)
        intro literal member
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member ⊢
        aesop

def finiteRows (rename : Nat → Fin v) (prepared : Preparation (parameters := parameters) rename)
    (root : Fin parameters.decoder.nodeCount) :
    ∀ index : Fin (parameters.decoder.finiteZeroSystem parameters.buses parameters.bridge.target root ∅ ∅).clauses.size,
      HornRowTransport.Origin (handles (parameters := parameters) rename) prepared.proofPrefix.state
        (cofactor (parameters := parameters) rename ++ [SourceForwardRows.handle rename .faulty (.inr root)])
        (parameters.decoder.finiteZeroSystem parameters.buses parameters.bridge.target root ∅ ∅).clauses[index.val] := by
  intro index
  let original := parameters.decoder.zeroSystem parameters.buses parameters.bridge.target root ∅ ∅
  have bound : index.val < original.clauses.size := by
    simpa only [Controller.Decoder.DAG.finiteZeroSystem, relabel, Controller.CNF.OrderedFormula.relabel, Array.size_map] using index.isLt
  let row := original.clauses[index.val]'bound
  have present : row ∈ originalRows (parameters := parameters) root := by
    have member := Array.getElem_mem bound
    simpa only [row, original, Controller.Decoder.DAG.zeroSystem, ofClauses, List.mem_toArray, originalRows] using member
  have equal : (parameters.decoder.finiteZeroSystem parameters.buses parameters.bridge.target root ∅ ∅).clauses[index.val] =
      Rows.mapClause parameters.decoder.zeroIndex row := by
    simp only [Controller.Decoder.DAG.finiteZeroSystem, relabel, Controller.CNF.OrderedFormula.relabel, Array.getElem_map,
      Controller.CNF.OrderedFormula.Clause.relabel, Rows.mapClause, row, original]
  exact Eq.mpr (congrArg (HornRowTransport.Origin (handles (parameters := parameters) rename) prepared.proofPrefix.state
    (cofactor (parameters := parameters) rename ++ [SourceForwardRows.handle rename .faulty (.inr root)])) equal)
    (rowOrigin rename prepared root row present)

def query (rename : Nat → Fin v) (prepared : Preparation (parameters := parameters) rename)
    (guarded : parameters.decoder.Guarded) (selected : Finset (Fin parameters.decoder.roots.length))
    (absent : Decoder.NoDiscrepancy parameters selected)
    (output : Fin parameters.decoder.roots.length) (accepted : output ∈ selected)
    (healthy : parameters.observations output (Controller.assignmentOfSet {parameters.bridge.target}) = true) :
    SubclauseProjection prepared.proofPrefix.state
      (cofactor (parameters := parameters) rename ++ [SourceForwardRows.handle rename .faulty (.inr (parameters.decoder.roots.get output))])
      (parameters.channels + parameters.decoder.nodeCount) := by
  let root := parameters.decoder.roots.get output
  let formula := parameters.decoder.finiteZeroSystem parameters.buses parameters.bridge.target root ∅ ∅
  have unsat : Unsatisfiable formula := by
    apply (unsatisfiable_relabel_iff parameters.decoder.zeroIndex.injective _).mpr
    exact Decoder.healthyOne_zeroSystem_unsatisfiable parameters guarded selected absent output accepted healthy
  have complete := HornTrail.produce_complete formula
    (parameters.decoder.finiteZeroSystem_dualHorn guarded _ _ _ _ _) unsat
  exact match returned : HornTrail.produce formula with
  | .none => False.elim (by obtain ⟨conflict, run, _, _⟩ := complete; simp [returned] at run)
  | .some conflict => by
    have certified : HornTrail.Certified formula conflict := by
      obtain ⟨result, run, proof, bound⟩ := complete
      have same : result = conflict := Option.some.inj (run.symm.trans returned)
      exact same ▸ proof
    have bound : conflict.reasons.length ≤ parameters.channels + parameters.decoder.nodeCount := by
      obtain ⟨result, run, proof, bound⟩ := complete
      have same : result = conflict := Option.some.inj (run.symm.trans returned)
      exact same ▸ bound
    have positive := HornTrail.scan_conflict_positive formula _ _ _ conflict returned
    let replayed := HornRowTransport.replay formula conflict certified positive (handles (parameters := parameters) rename)
      prepared.proofPrefix.state (cofactor (parameters := parameters) rename ++ [SourceForwardRows.handle rename .faulty (.inr root)])
      (finiteRows rename prepared root)
    exact ⟨replayed.state, replayed.steps, replayed.checked, replayed.result, replayed.count.trans bound⟩

theorem rootHandle (rename : Nat → Fin v) (side : Side)
    (output : Fin parameters.decoder.roots.length) :
    SourceDecoderTraversal.nativeRootLiteral rename side output =
      SourceDecoderEvaluation.outputLiteral rename side (parameters.decoder.roots.get output) := by
  let root := parameters.decoder.roots.get output
  have complete : SourceDecoderTraversal.nativeRootLiteral rename side output =
      SourceDecoderTraversal.decoderStoredLiteral rename side parameters.decoder.nodeCount root := by
    simp only [SourceDecoderTraversal.nativeRootLiteral, SourceDecoderTraversal.compiled_decoder_slot,
      SourceDecoderTraversal.decoderComplete_slot, SourceDecoderTraversal.decoderStoredLiteral, root, List.get_eq_getElem]
  exact complete.trans (SourceDecoderEvaluation.stored_eq_output rename side parameters.decoder.nodeCount (Nat.le_refl _) root root.isLt)

def equality (rename : Nat → Fin v) (prepared : Preparation (parameters := parameters) rename)
    (guarded : parameters.decoder.Guarded) (selected : Finset (Fin parameters.decoder.roots.length))
    (absent : Decoder.NoDiscrepancy parameters selected)
    (output : Fin parameters.decoder.roots.length) (accepted : output ∈ selected)
    (healthy : parameters.observations output (Controller.assignmentOfSet {parameters.bridge.target}) = true) :
    SourceBusAdvance.PairedProjection prepared.proofPrefix.state (cofactor (parameters := parameters) rename)
      (SourceDecoderTraversal.nativeRootLiteral rename .healthy output)
      (SourceDecoderTraversal.nativeRootLiteral rename .faulty output)
      (parameters.channels + parameters.decoder.nodeCount) := by
  let actual := query rename prepared guarded selected absent output accepted healthy
  have faulty : AvailableSubclause actual.state (cofactor (parameters := parameters) rename ++
      [SourceDecoderTraversal.nativeRootLiteral rename .faulty output]) := by
    simpa only [rootHandle, SourceForwardRows.handle, Sum.elim_inr] using actual.result
  have healthyRow : AvailableSubclause actual.state (cofactor (parameters := parameters) rename ++
      [SourceDecoderTraversal.nativeRootLiteral rename .healthy output]) := by
    have bit : parameters.decoder.eval (Controller.assignmentOfSet {parameters.bridge.target})
        (parameters.decoder.roots.get output) = true := healthy
    simpa only [bit, SourceStageXor.valueLiteral, ite_true, rootHandle] using
      FoldProjection.afterTrace (prepared.healthy (parameters.decoder.roots.get output)) actual.state actual.steps actual.checked
  refine ⟨actual.state, actual.steps, actual.checked, ⟨.derived (retarget faulty ?_), .derived (retarget healthyRow ?_)⟩, actual.count⟩
  · intro literal member
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member ⊢
    aesop
  · intro literal member
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member ⊢
    aesop

def closedEquality (rename : Nat → Fin v) (drive : parameters.drive = true)
    (guarded : parameters.decoder.Guarded) (selected : Finset (Fin parameters.decoder.roots.length))
    (absent : Decoder.NoDiscrepancy parameters selected)
    (output : Fin parameters.decoder.roots.length) (accepted : output ∈ selected)
    (healthy : parameters.observations output (Controller.assignmentOfSet {parameters.bridge.target}) = true) :=
  equality rename (prepare rename drive guarded) guarded selected absent output accepted healthy

structure EqualityPrefix (rename : Nat → Fin v) (output : Fin parameters.decoder.roots.length) where
  proofPrefix : SourcePrefix (parameters := parameters) rename
  pair : SourceBusSchedule.DirectionPair proofPrefix.state (cofactor (parameters := parameters) rename)
    (SourceDecoderTraversal.nativeRootLiteral rename .healthy output)
    (SourceDecoderTraversal.nativeRootLiteral rename .faulty output)

def addContext (context : Clause (Fin v))
    (transfer : GuardedTransfer state [] first second) : GuardedTransfer state context first second := by
  cases transfer with
  | identity same => exact .identity same
  | derived row => exact .derived (retarget row (fun _ member => List.mem_append_right _ member))

/-- The accepted zero-drive constructor supplies unconditional equality;
the driven case uses the shared healthy-one construction. -/
def uniformEquality (rename : Nat → Fin v) (guarded : parameters.decoder.Guarded)
    (selected : Finset (Fin parameters.decoder.roots.length)) (absent : Decoder.NoDiscrepancy parameters selected)
    (output : Fin parameters.decoder.roots.length) (accepted : output ∈ selected)
    (healthy : parameters.observations output (Controller.assignmentOfSet {parameters.bridge.target}) = true) :
    EqualityPrefix (parameters := parameters) rename output := by
  by_cases drive : parameters.drive = true
  · let prepared := prepare rename drive guarded
    let actual := equality rename prepared guarded selected absent output accepted healthy
    exact ⟨prepared.proofPrefix.extend actual.state actual.steps actual.checked, actual.pair⟩
  · have zero : parameters.drive = false := Bool.eq_false_of_not_eq_true drive
    let actual := SourceDecoderTraversal.driveZeroOutputRoot rename zero output
    exact ⟨SourceDecoderTraversal.driveZeroOutputPrefix rename zero,
      ⟨addContext _ actual.forward, addContext _ actual.backward⟩⟩

end Controller.NativeProof.SourceHealthyOneQuery
