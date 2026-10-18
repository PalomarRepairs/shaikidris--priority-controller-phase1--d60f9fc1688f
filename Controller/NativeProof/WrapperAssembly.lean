module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.WrapperSelectedTraversal
public import Controller.NativeProof.WrapperSelectedEmission

@[expose] public section

/-! Native equality prefixes replay into the exact optional and selected inputs. -/
namespace Controller.NativeProof.Wrapper
open Controller.CNF Controller.Resolution Controller.Native Controller.Native.SourceController
open Controller.NativeProof.FoldProjection Controller.NativeProof.SourceFoldProjection
open Controller.NativeProof.SourceStageCongruence Controller.NativeProof.SourceStagePolarity
open Controller.NativeProof.SourceBusSchedule Controller.NativeProof.SourceBusAdvance
open Controller.NativeProof.SourceMismatchHandles Controller.NativeProof.SourceDecoderTraversal
open Controller.Native.ObservationProjection
variable {parameters : Parameters} {internalCount v : Nat}

theorem native_rows_match (parameters : Parameters)
    (rows : List (Clause (WrapperLabel parameters internalCount)))
    (core : ∀ clause ∈ taggedCoreRows parameters, clause ∈ rows)
    (rename : WrapperLabel parameters internalCount → Fin v) :
    let signalRename := fun signal => rename (Sum.inl signal)
    let source := relabel signalRename (formula parameters)
    let targetRows := rows.map (Rows.mapClause rename)
    RetainedMatch source.clauses.size targetRows.length (originalLookup source targetRows)
      (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) signalRename)
      (initialState source) (initialState (ofClauses targetRows)) := by
  dsimp only
  apply initial_retained_match
  intro rowId allowed
  obtain ⟨clause, member, present⟩ := allowed_core_row parameters (fun signal => rename (Sum.inl signal)) rowId allowed
  refine ⟨Rows.mapClause (fun signal => rename (Sum.inl signal)) clause, ?_, present⟩
  apply List.mem_map.mpr
  refine ⟨clause.map (fun literal => (Sum.inl literal.1, literal.2)), core _ (List.mem_map.mpr ⟨clause, member, rfl⟩), ?_⟩
  simp [Rows.mapClause, List.map_map, Function.comp_def]

structure NativeSelectedPrefix (parameters : Parameters)
    (rows : List (Clause (WrapperLabel parameters internalCount)))
    (rename : WrapperLabel parameters internalCount → Fin v) (outputs : List (Fin parameters.decoder.roots.length)) where
  state : State v
  steps : List (Step v)
  checked : runSteps (initialState (ofClauses (rows.map (Rows.mapClause rename)))) steps = some state
  pairs : ∀ output ∈ outputs, DirectionPair state []
    (nativeRootLiteral (fun signal => rename (.inl signal)) .healthy output)
    (nativeRootLiteral (fun signal => rename (.inl signal)) .faulty output)

def replaySelectedPrefix (parameters : Parameters)
    (rows : List (Clause (WrapperLabel parameters internalCount)))
    (core : ∀ clause ∈ taggedCoreRows parameters, clause ∈ rows)
    (rename : WrapperLabel parameters internalCount → Fin v) (outputs : List (Fin parameters.decoder.roots.length))
    (proofPrefix : SourcePrefix (parameters := parameters) (fun signal => rename (.inl signal)))
    (supported : SourceDecoderSchedule.PrefixOriginalSupport _ proofPrefix)
    (pairs : ∀ output ∈ outputs, DirectionPair proofPrefix.state []
      (nativeRootLiteral (fun signal => rename (.inl signal)) .healthy output)
      (nativeRootLiteral (fun signal => rename (.inl signal)) .faulty output))
    (origins : ∀ output member, SourceDecoderSchedule.DirectionPairOrigin _ proofPrefix (pairs output member)) :
    NativeSelectedPrefix parameters rows rename outputs := by
  let signalRename := fun signal => rename (Sum.inl signal)
  let source := relabel signalRename (formula parameters)
  let targetRows := rows.map (Rows.mapClause rename)
  have matched : RetainedMatch (formula parameters).clauses.size targetRows.length (originalLookup source targetRows)
      (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) signalRename)
      (initialState source) (initialState (ofClauses targetRows)) := by
    simpa only [source, targetRows, signalRename, relabel, Controller.CNF.OrderedFormula.relabel, Array.size_map] using
      native_rows_match parameters rows core rename
  let replay := replayRetained matched proofPrefix.steps proofPrefix.state proofPrefix.checked supported
  exact ⟨replay.state, replay.steps, replay.checked,
    fun output member => retainedPair signalRename proofPrefix replay.matched (pairs output member) (origins output member)⟩

def nativeSelectedPrefix (parameters : Parameters)
    (rows : List (Clause (WrapperLabel parameters internalCount)))
    (core : ∀ clause ∈ taggedCoreRows parameters, clause ∈ rows)
    (rename : WrapperLabel parameters internalCount → Fin v) (outputs : List (Fin parameters.decoder.roots.length))
    (guarded : parameters.decoder.Guarded)
    (absent : parameters.drive = true → Decoder.NoDiscrepancy parameters outputs.toFinset) :
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
    exact replaySelectedPrefix parameters rows core rename outputs (driveZeroOutputPrefix signalRename zero)
      (driveZeroOutputPrefix_supported signalRename zero)
      (fun output _ => driveZeroOutputRoot signalRename zero output)
      (fun output _ => driveZeroOutputRoot_supported signalRename zero output)

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

end Controller.NativeProof.Wrapper
