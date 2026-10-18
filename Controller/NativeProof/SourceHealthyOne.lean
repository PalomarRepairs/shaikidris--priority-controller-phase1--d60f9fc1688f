module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.SourceForwardRows
public import Controller.NativeProof.HornRowTransport

@[expose] public section

/-! Concrete channel premises and shared source preparation for the
healthy-one native Horn branch. -/
namespace Controller.NativeProof.SourceHealthyOne
open Controller.CNF Controller.Resolution Controller.Native Controller.Native.SourceController
open Controller.NativeProof.FoldProjection Controller.NativeProof.SourceFoldProjection
open Controller.NativeProof.SourceStageCongruence Controller.NativeProof.SourceStagePolarity
open Controller.NativeProof.SourceStageXor Controller.NativeProof.SourceFoldOccurrences
open Controller.NativeProof.SourceRoleFrames Controller.NativeProof.SourceBusSchedule
open Controller.NativeProof.SourceBusAdvance Controller.NativeProof.SourceMismatchAdvance
open Controller.NativeProof.SourceMixedSchedule Controller.NativeProof.SourceSuffixSelector
open Controller.NativeProof.SourceQualifierSchedule Controller.NativeProof.SourceDecoderTraversal
variable {parameters : Parameters} {v : Nat}

abbrev cofactor (rename : Nat → Fin v) := mixedContext (parameters := parameters) rename

def oneBusTarget (rename : Nat → Fin v) (start : SourcePrefix (parameters := parameters) rename)
    (drive : parameters.drive = true) (one : parameters.buses = 1) :
    SubclauseProjection start.state (cofactor (parameters := parameters) rename ++
      [SourceDecoderEvaluation.qualifierLiteral rename .faulty parameters.bridge.target])
      (3 + 2 * (qualifierTree rename .faulty parameters.bridge.target).nodes + parameters.buses + 1) := by
  let guard := guardOrFlagAt rename start .faulty parameters.bridge.target parameters.firstBus
  let g := mapLiteral rename (guardHandle .faulty parameters.bridge.target parameters.firstBus)
  have guardUnit : AvailableSubclause guard.state (cofactor (parameters := parameters) rename ++ [g]) := by
    apply retarget guard.result
    intro literal member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with same | same
    · exact List.mem_append_right _ (List.mem_singleton.mpr same)
    · subst literal
      rw [firstFlagInput_eq_sourceRoleMap]
      exact List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  let afterGuard := start.extend guard.state guard.steps guard.checked
  let enabled := targetEnableAt rename afterGuard drive
  let prefixState := afterGuard.extend enabled.state enabled.steps enabled.checked
  let tree := (qualifierTree rename .faulty parameters.bridge.target).afterTrace
    enabled.state prefixState.steps prefixState.checked
  let inputs := (qualifierGuarded .faulty parameters.bridge.target).slots (.primary (.enable parameters.bridge.target)) ::
    (List.finRange parameters.buses).map (fun bus =>
      (qualifierGuarded .faulty parameters.bridge.target).slots (.internal (.qualifierGuard .faulty bus parameters.bridge.target)))
  have units : ∀ leaf ∈ inputs.map (mapLiteral rename),
      AvailableSubclause enabled.state (cofactor (parameters := parameters) rename ++ [leaf]) := by
    intro leaf member
    let e := mapLiteral rename ((qualifierGuarded .faulty parameters.bridge.target).slots (.primary (.enable parameters.bridge.target)))
    have allGuard : ∀ bus : Fin parameters.buses, bus = parameters.firstBus := by
      intro bus
      apply Fin.ext
      have bound := bus.isLt
      simp only [Parameters.firstBus]
      omega
    have possibilities : leaf = e ∨ leaf = g := by
      have expanded : leaf = e ∨ ∃ bus ∈ List.finRange parameters.buses,
          mapLiteral rename ((qualifierGuarded .faulty parameters.bridge.target).slots
            (.internal (.qualifierGuard .faulty bus parameters.bridge.target))) = leaf := by
        simpa only [inputs, List.map_cons, List.mem_cons, List.map_map, List.mem_map, Function.comp_def] using member
      rcases expanded with enable | guarded
      · exact Or.inl enable
      · obtain ⟨bus, listed, equal⟩ := guarded
        exact Or.inr (by simpa only [qualifierGuarded_guard_handle, allGuard, g] using equal.symm)
    by_cases isEnable : leaf = e
    · subst leaf
      apply retarget enabled.result
      intro literal member
      simpa only [e, (qualifierGuarded_roots .faulty parameters.bridge.target).1,
        sourceRoleMap, (compile_rootsExact parameters).1] using List.mem_append_right (cofactor (parameters := parameters) rename) member
    · have same := possibilities.resolve_left isEnable
      exact same ▸ FoldProjection.afterTrace guardUnit enabled.state enabled.steps enabled.checked
  let forced := TreeUnits.force tree (cofactor (parameters := parameters) rename) units
  refine ⟨forced.state, (guard.steps ++ enabled.steps) ++ forced.steps, ?_, ?_, ?_⟩
  · have enabledRun : runSteps guard.state enabled.steps = some enabled.state := enabled.checked
    simp only [runSteps_append, guard.checked, Option.bind_some, enabledRun, forced.checked]
  · simpa only [SourceDecoderEvaluation.qualifierLiteral, ← qualifierOutput_decoderStart, qualifierOutput] using forced.result
  · have first := guard.count
    have second := enabled.count
    have third : forced.steps.length ≤ 2 * (qualifierTree rename .faulty parameters.bridge.target).nodes + parameters.buses + 1 := by
      calc
        forced.steps.length ≤ 2 * tree.nodes + (inputs.map (mapLiteral rename)).length := forced.count
        _ = _ := by
          rw [show tree.nodes = (qualifierTree rename .faulty parameters.bridge.target).nodes from AndTree.afterTrace_nodes _ _ _ _]
          simp only [inputs, List.length_map, List.length_cons, List.length_finRange]
          omega
    simp only [List.length_append]
    omega

structure TargetPrefix (rename : Nat → Fin v) (start : SourcePrefix (parameters := parameters) rename) where
  state : State v
  steps : List (Step v)
  checked : runSteps start.state steps = some state
  targetUnit : parameters.buses = 1 → AvailableSubclause state
    (cofactor (parameters := parameters) rename ++ [SourceDecoderEvaluation.qualifierLiteral rename .faulty parameters.bridge.target])

def optionalTarget (rename : Nat → Fin v) (start : SourcePrefix (parameters := parameters) rename)
    (drive : parameters.drive = true) : TargetPrefix rename start :=
  if one : parameters.buses = 1 then
    let actual := oneBusTarget rename start drive one
    ⟨actual.state, actual.steps, actual.checked, fun _ => actual.result⟩
  else ⟨start.state, [], rfl, fun equality => False.elim (one equality)⟩

structure Preparation (rename : Nat → Fin v) where
  proofPrefix : SourcePrefix (parameters := parameters) rename
  healthy : ∀ node : Fin parameters.decoder.nodeCount, AvailableSubclause proofPrefix.state
    (cofactor (parameters := parameters) rename ++ [valueLiteral (SourceDecoderEvaluation.outputLiteral rename .healthy node)
      (parameters.decoder.eval (Controller.assignmentOfSet {parameters.bridge.target}) node)])
  forward : ∀ row ∈ parameters.decoder.forwardClauses,
    SourceForwardRows.Origin (parameters := parameters) rename .faulty proofPrefix.state (cofactor (parameters := parameters) rename) row
  nonempty : AvailableSubclause proofPrefix.state (cofactor (parameters := parameters) rename ++
    (List.finRange parameters.channels).map (SourceDecoderEvaluation.qualifierLiteral rename .faulty))
  targetUnit : parameters.buses = 1 → AvailableSubclause proofPrefix.state
    (cofactor (parameters := parameters) rename ++ [SourceDecoderEvaluation.qualifierLiteral rename .faulty parameters.bridge.target])

def prepare (rename : Nat → Fin v) (drive : parameters.drive = true) (guarded : parameters.decoder.Guarded) :
    Preparation (parameters := parameters) rename := by
  let healthy := SourceDecoderEvaluation.healthy rename drive guarded
  let forwards := SourceForwardRows.allRows rename .faulty (cofactor (parameters := parameters) rename) guarded healthy.proofPrefix
  have forwardRun : runSteps healthy.proofPrefix.state
      (forwards.proofPrefix.steps.drop healthy.proofPrefix.steps.length) = some forwards.proofPrefix.state :=
    SourceForwardRows.build_relative rename .faulty (cofactor (parameters := parameters) rename) guarded healthy.proofPrefix
      parameters.decoder.nodeCount (Nat.le_refl _)
  let healthyNow := healthy.afterTrace forwards.proofPrefix.state
    (forwards.proofPrefix.steps.drop healthy.proofPrefix.steps.length) forwardRun
  let activation := compiledMixedActivation rename drive
  let replay := replayNativeProgram rename forwards.proofPrefix activation.state activation.steps activation.checked
  let forwardNow := forwards.afterTrace replay.next replay.added replay.checked
  let healthyActivated := healthyNow.afterTrace replay.next replay.added replay.checked
  let target := optionalTarget rename replay.prefix drive
  let prefixState := replay.prefix.extend target.state target.steps target.checked
  refine ⟨prefixState, ?_, ?_, ?_, target.targetUnit⟩
  · intro node
    have row := FoldProjection.afterTrace (healthyActivated.nodes node node.isLt) target.state target.steps target.checked
    simpa only [cofactor, SourceHealthyMasks.context, prefixState, SourcePrefix.extend, SourceDecoderEvaluation.nodeBit,
      SourceDecoderEvaluation.stored_eq_output rename .healthy parameters.decoder.nodeCount (Nat.le_refl _) node node.isLt] using row
  · intro row present
    exact (SourceForwardRows.forwardRow rename .faulty (cofactor (parameters := parameters) rename) forwardNow row present).afterTrace
      target.state target.steps target.checked
  · have original : AvailableSubclause replay.next (cofactor (parameters := parameters) rename ++
        compiledQualifierOutputs (parameters := parameters) rename) :=
      ⟨activation.result.clause, replay.available activation.result.row, activation.result.subset⟩
    have available := FoldProjection.afterTrace original target.state target.steps target.checked
    have outputs : compiledQualifierOutputs (parameters := parameters) rename =
        (List.finRange parameters.channels).map (SourceDecoderEvaluation.qualifierLiteral rename .faulty) := by
      unfold compiledQualifierOutputs
      apply List.map_congr_left
      intro channel listed
      exact congrArg (mapLiteral rename) (compiled_faulty_qualifier_slot channel)
    simpa only [prefixState, SourcePrefix.extend, outputs] using available

def Preparation.afterTrace (prepared : Preparation (parameters := parameters) rename)
    (next : State v) (steps : List (Step v)) (checked : runSteps prepared.proofPrefix.state steps = some next) :
    Preparation (parameters := parameters) rename where
  proofPrefix := prepared.proofPrefix.extend next steps checked
  healthy node := FoldProjection.afterTrace (prepared.healthy node) next steps checked
  forward row present := (prepared.forward row present).afterTrace next steps checked
  nonempty := FoldProjection.afterTrace prepared.nonempty next steps checked
  targetUnit one := FoldProjection.afterTrace (prepared.targetUnit one) next steps checked

end Controller.NativeProof.SourceHealthyOne
