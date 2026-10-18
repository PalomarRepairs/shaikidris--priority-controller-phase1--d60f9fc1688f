module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.SourceDecoderClauses
public import Controller.NativeProof.TreeUnits
public import Controller.NativeProof.XorUnits

@[expose] public section

/-! Healthy-singleton mask construction under the separating first-flag
cofactor. The seed is the actual first-mask bank, and later non-target terms
are killed by their retained first mask. -/
namespace Controller.NativeProof.SourceHealthyMasks
open Controller.CNF Controller.Resolution Controller.Native Controller.Native.SourceController
open Controller.NativeProof.FoldProjection Controller.NativeProof.SourceFoldProjection
open Controller.NativeProof.SourceStageCongruence Controller.NativeProof.SourceStagePolarity
open Controller.NativeProof.SourceStageXor Controller.NativeProof.SourceFoldOccurrences
open Controller.NativeProof.SourceRoleFrames Controller.NativeProof.SourceBusSchedule
open Controller.NativeProof.SourceBusAdvance Controller.NativeProof.SourceMismatchAdvance
open Controller.NativeProof.SourceMixedSchedule Controller.NativeProof.SourceSuffixSelector
variable {parameters : Parameters} {v : Nat}

abbrev context (rename : Nat → Fin v) := mixedContext (parameters := parameters) rename

def targetRequest (rename : Nat → Fin v)
    (position : Fin (laterBuses (parameters := parameters)).length) : Literal (Fin v) :=
  mapLiteral rename ((termBefore .healthy position parameters.bridge.target).slots
    (.primary (.request (laterBuses (parameters := parameters))[position.val] parameters.bridge.target)))

structure Table (rename : Nat → Fin v) (count : Nat) where
  proofPrefix : SourcePrefix (parameters := parameters) rename
  firstZero : ∀ channel, channel ≠ parameters.bridge.target →
    AvailableSubclause proofPrefix.state (context (parameters := parameters) rename ++ [negate (sourceMask rename .healthy parameters.firstBus channel)])
  firstAbsent : ∀ channel, channel ≠ parameters.bridge.target →
    AvailableSubclause proofPrefix.state (context (parameters := parameters) rename ++
      [mapLiteral rename ((firstArrays parameters).slots (.internal (.absent .healthy parameters.firstBus channel)))])
  targetMasks : ∀ bus ∈ parameters.firstBus :: (laterBuses (parameters := parameters)).take count,
    AvailableSubclause proofPrefix.state (context (parameters := parameters) rename ++ [mapLiteral rename
      ((stagesBefore (parameters := parameters) .healthy count).slots
        (.internal (.mask .healthy bus parameters.bridge.target)))])
  flagRequests : ∀ position : Fin (laterBuses (parameters := parameters)).length, position.val < count →
    DirectionPair proofPrefix.state (context (parameters := parameters) rename)
      (laterFlagOutput rename .healthy position) (targetRequest rename position)

def initial (rename : Nat → Fin v) (drive : parameters.drive = true) :
    Table (parameters := parameters) rename 0 := by
  let absences := allOtherAbsences (parameters := parameters) rename
  let masks := allFirstMasks (parameters := parameters) rename drive
  let start : SourcePrefix (parameters := parameters) rename :=
    ⟨masks.state, absences.steps ++ masks.steps, by
      have firstRun : runSteps (initialState (relabel rename (formula parameters))) absences.steps =
          some absences.state := absences.checked
      rw [runSteps_append, firstRun]
      exact masks.checked⟩
  refine ⟨start, ?_, ?_, ?_, ?_⟩
  · intro channel different
    have row := masks.rows .healthy channel (List.mem_finRange _)
    simpa [firstMaskValue, absenceBit, different, valueLiteral, maskOutput_eq_sourceRoleMap,
      sourceMask] using row
  · intro channel different
    exact FoldProjection.afterTrace (allOtherAbsences_complete rename channel different)
      masks.state masks.steps masks.checked
  · intro bus member
    have same : bus = parameters.firstBus := by simpa using member
    subst bus
    have row := masks.rows .healthy parameters.bridge.target (List.mem_finRange _)
    rw [stagesBefore_zero_first_mask]
    simpa [firstMaskValue, absenceBit, valueLiteral, maskOutput_eq_sourceRoleMap, sourceMask] using row
  · intro position before
    exact False.elim (Nat.not_lt_zero _ before)

def Table.afterTrace (table : Table (parameters := parameters) rename count)
    (next : State v) (steps : List (Step v)) (checked : runSteps table.proofPrefix.state steps = some next) :
    Table (parameters := parameters) rename count where
  proofPrefix := table.proofPrefix.extend next steps checked
  firstZero channel different := FoldProjection.afterTrace (table.firstZero channel different) next steps checked
  firstAbsent channel different := FoldProjection.afterTrace (table.firstAbsent channel different) next steps checked
  targetMasks bus member := FoldProjection.afterTrace (table.targetMasks bus member) next steps checked
  flagRequests position before := (table.flagRequests position before).afterTrace next steps checked

theorem later_positive (position : Fin (laterBuses (parameters := parameters)).length) :
    0 < (laterBuses (parameters := parameters))[position.val].val := by
  have present := List.getElem_mem position.isLt
  have nonzero : (laterBuses (parameters := parameters))[position.val].val ≠ 0 := by
    simpa using (List.mem_filter.mp present).2
  omega

def otherTerm (rename : Nat → Fin v)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (table : Table (parameters := parameters) rename position.val)
    (channel : Fin parameters.channels) (different : channel ≠ parameters.bridge.target) :
    SubclauseProjection table.proofPrefix.state
      (context (parameters := parameters) rename ++ [negate (laterTermOutput rename .healthy position channel)])
      (2 * (laterTermTree rename .healthy position channel).nodes + 1) := by
  let tree := (laterTermTree rename .healthy position channel).afterTrace
    table.proofPrefix.state table.proofPrefix.steps table.proofPrefix.checked
  let input := mapLiteral rename ((termBefore .healthy position channel).slots
    (.internal (.mask .healthy parameters.firstBus channel)))
  have member : input ∈ (laterTermInputs .healthy position channel).map (mapLiteral rename) := by
    apply List.mem_map.mpr
    refine ⟨_, ?_, rfl⟩
    unfold laterTermInputs
    apply List.mem_append.mpr
    right
    apply List.mem_map.mpr
    refine ⟨parameters.firstBus, ?_, rfl⟩
    apply List.mem_filter.mpr
    exact ⟨List.mem_finRange _, by simpa [Parameters.firstBus, Fin.lt_def] using later_positive position⟩
  have unit : AvailableSubclause table.proofPrefix.state (context (parameters := parameters) rename ++ [negate input]) := by
    simpa only [input, termBefore_first_mask] using table.firstZero channel different
  simpa only [tree, AndTree.afterTrace_nodes, laterTermOutput] using TreeUnits.deny tree (context (parameters := parameters) rename) input member unit

structure TermZeros (rename : Nat → Fin v)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (start : Table (parameters := parameters) rename position.val) (done : List (Fin parameters.channels)) where
  table : Table (parameters := parameters) rename position.val
  steps : List (Step v)
  checked : runSteps start.proofPrefix.state steps = some table.proofPrefix.state
  rows : ∀ channel ∈ done, channel ≠ parameters.bridge.target →
    AvailableSubclause table.proofPrefix.state
      (context (parameters := parameters) rename ++ [negate (laterTermOutput rename .healthy position channel)])

def collectOtherTerms (rename : Nat → Fin v)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (table : Table (parameters := parameters) rename position.val)
    (channels : List (Fin parameters.channels)) : TermZeros (parameters := parameters) rename position table channels :=
  match channels with
  | [] => ⟨table, [], rfl, by
      intro channel member
      exact False.elim (List.not_mem_nil member)⟩
  | channel :: rest => by
    by_cases same : channel = parameters.bridge.target
    · let tail := collectOtherTerms rename position table rest
      refine ⟨tail.table, tail.steps, tail.checked, ?_⟩
      intro query member different
      by_cases equal : query = channel
      · exact False.elim (different (equal.trans same))
      · exact tail.rows query ((List.mem_cons.mp member).resolve_left equal) different
    · let added := otherTerm rename position table channel same
      let nextTable := table.afterTrace added.state added.steps added.checked
      let tail := collectOtherTerms rename position nextTable rest
      refine ⟨tail.table, added.steps ++ tail.steps, ?_, ?_⟩
      · rw [runSteps_append, added.checked]
        exact tail.checked
      · intro query member different
        by_cases equal : query = channel
        · subst query
          have original : AvailableSubclause nextTable.proofPrefix.state
              (context (parameters := parameters) rename ++ [negate (laterTermOutput rename .healthy position channel)]) := added.result
          exact afterTrace original tail.table.proofPrefix.state tail.steps tail.checked
        · exact tail.rows query ((List.mem_cons.mp member).resolve_left equal) different

def targetTermUnits (rename : Nat → Fin v)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (table : Table (parameters := parameters) rename position.val) (drive : parameters.drive = true) : ∀ other ∈ (laterTermInputs .healthy position parameters.bridge.target).map (mapLiteral rename),
      other ≠ targetRequest rename position →
      AvailableSubclause (targetEnableAt rename table.proofPrefix drive).state (context (parameters := parameters) rename ++ [other]) := by
    let enabled := targetEnableAt rename table.proofPrefix drive
    intro other present different
    have classified : other = mapLiteral rename ((termBefore .healthy position parameters.bridge.target).slots
        (.primary (.enable parameters.bridge.target))) ∨
        ∃ bus, bus ∈ (List.finRange parameters.buses).filter
          (fun earlier => earlier < (laterBuses (parameters := parameters))[position.val]) ∧
          other = mapLiteral rename ((termBefore .healthy position parameters.bridge.target).slots
            (.internal (.mask .healthy bus parameters.bridge.target))) := by
      simpa [laterTermInputs, targetRequest, List.mem_map, eq_comm, targetRequest] using
        ((show other = _ ∨ other = targetRequest rename position ∨ _ from by
          simpa [laterTermInputs, targetRequest, List.mem_map, eq_comm] using present).elim
          Or.inl (fun rest => Or.inr (rest.resolve_left different)))
    by_cases isEnable : other = mapLiteral rename ((termBefore .healthy position parameters.bridge.target).slots
        (.primary (.enable parameters.bridge.target)))
    · subst other
      have roots := (termBefore_rootsExact .healthy position parameters.bridge.target).1 parameters.bridge.target
      have finalRoots := (compile_rootsExact parameters).1 parameters.bridge.target
      apply retarget enabled.result
      intro literal listed
      simpa only [sourceRoleMap, roots, finalRoots] using List.mem_append_right
        (context (parameters := parameters) rename) listed
    · let buses := (List.finRange parameters.buses).filter
        (fun earlier => earlier < (laterBuses (parameters := parameters))[position.val])
      let handle := fun bus => mapLiteral rename ((termBefore .healthy position parameters.bridge.target).slots
        (.internal (.mask .healthy bus parameters.bridge.target)))
      have presentMask : other ∈ buses.map handle := by
        obtain ⟨bus, listed, equal⟩ := classified.resolve_left isEnable
        exact List.mem_map.mpr ⟨bus, listed, equal.symm⟩
      exact TreeUnits.mappedUnit buses handle (context (parameters := parameters) rename) (fun bus listed => by
        have before : bus < (laterBuses (parameters := parameters))[position.val] := by
          simpa using (List.mem_filter.mp listed).2
        have row := FoldProjection.afterTrace (table.targetMasks bus (earlier_bus_covered position bus before))
          (targetEnableAt rename table.proofPrefix drive).state enabled.steps enabled.checked
        simpa only [handle, termBefore_mask, busBefore_eq_stagesBefore] using row) other presentMask

def targetTerm (rename : Nat → Fin v)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (table : Table (parameters := parameters) rename position.val) (drive : parameters.drive = true) :
    PairedProjection table.proofPrefix.state (context (parameters := parameters) rename)
      (laterTermOutput rename .healthy position parameters.bridge.target) (targetRequest rename position)
      (2 + 4 * (laterTermTree rename .healthy position parameters.bridge.target).nodes +
        (laterTermInputs .healthy position parameters.bridge.target).length) := by
  let enabled := targetEnableAt rename table.proofPrefix drive
  let tree := (laterTermTree rename .healthy position parameters.bridge.target).afterTrace
    enabled.state (table.proofPrefix.steps ++ enabled.steps) (by
      rw [runSteps_append, table.proofPrefix.checked]
      exact enabled.checked)
  have member : targetRequest rename position ∈ (laterTermInputs .healthy position parameters.bridge.target).map (mapLiteral rename) := by
    simp [targetRequest, laterTermInputs]
  let units := targetTermUnits rename position table drive
  let reduced := TreeUnits.reduceToInput tree (context (parameters := parameters) rename)
    (targetRequest rename position) member units
  refine ⟨reduced.state, enabled.steps ++ reduced.steps, ?_, reduced.pair, ?_⟩
  · rw [runSteps_append, enabled.checked]
    exact reduced.checked
  · have first := enabled.count
    have second := reduced.count
    simp only [List.length_append]
    simpa only [tree, AndTree.afterTrace_nodes, List.length_map] using
      (show enabled.steps.length + reduced.steps.length ≤
        2 + 4 * tree.nodes + ((laterTermInputs .healthy position parameters.bridge.target).map (mapLiteral rename)).length by omega)

def targetFlagUnits (rename : Nat → Fin v)
    (position : Fin (laterBuses (parameters := parameters)).length)
    {start : Table (parameters := parameters) rename position.val}
    (zeros : TermZeros (parameters := parameters) rename position start (List.finRange parameters.channels)) : ∀ other ∈ (laterFlagInputs .healthy position).map (dualLiteral rename),
      other ≠ negate (laterTermOutput rename .healthy position parameters.bridge.target) →
      AvailableSubclause zeros.table.proofPrefix.state (context (parameters := parameters) rename ++ [other]) := by
  have inputs : (laterFlagInputs .healthy position).map (dualLiteral rename) =
      (List.finRange parameters.channels).map (fun channel => negate (laterTermOutput rename .healthy position channel)) := by
    rw [show (laterFlagInputs .healthy position).map (dualLiteral rename) =
        ((laterFlagInputs .healthy position).map (mapLiteral rename)).map negate from
      List.map_map.symm]
    rw [laterFlagInputs_eq_terms, List.map_map]
    rfl
  intro other listed different
  let channels := (List.finRange parameters.channels).filter (fun channel => channel ≠ parameters.bridge.target)
  have covered : other ∈ channels.map (fun channel => negate (laterTermOutput rename .healthy position channel)) := by
    rw [inputs] at listed
    obtain ⟨channel, present, equal⟩ := List.mem_map.mp listed
    have nonTarget : channel ≠ parameters.bridge.target := by
      intro same
      exact different (equal.symm.trans (congrArg (fun c => negate (laterTermOutput rename .healthy position c)) same))
    exact List.mem_map.mpr ⟨channel, List.mem_filter.mpr ⟨present, by simpa using nonTarget⟩, equal⟩
  exact TreeUnits.mappedUnit channels _ (context (parameters := parameters) rename)
    (fun channel present => zeros.rows channel (List.mem_filter.mp present).1
      (by simpa using (List.mem_filter.mp present).2)) other covered

def targetFlag (rename : Nat → Fin v)
    (position : Fin (laterBuses (parameters := parameters)).length)
    {start : Table (parameters := parameters) rename position.val}
    (zeros : TermZeros (parameters := parameters) rename position start (List.finRange parameters.channels)) :
    PairedProjection zeros.table.proofPrefix.state (context (parameters := parameters) rename)
      (laterFlagOutput rename .healthy position)
      (laterTermOutput rename .healthy position parameters.bridge.target)
      (4 * (laterFlagTree rename .healthy position).nodes + parameters.channels) := by
  let tree := (laterFlagTree rename .healthy position).afterTrace zeros.table.proofPrefix.state
    zeros.table.proofPrefix.steps zeros.table.proofPrefix.checked
  have inputs : (laterFlagInputs .healthy position).map (dualLiteral rename) =
      (List.finRange parameters.channels).map (fun channel => negate (laterTermOutput rename .healthy position channel)) := by
    rw [show (laterFlagInputs .healthy position).map (dualLiteral rename) =
        ((laterFlagInputs .healthy position).map (mapLiteral rename)).map negate from
      List.map_map.symm]
    rw [laterFlagInputs_eq_terms, List.map_map]
    rfl
  have member : negate (laterTermOutput rename .healthy position parameters.bridge.target) ∈
      (laterFlagInputs .healthy position).map (dualLiteral rename) := by
    rw [inputs]
    exact List.mem_map.mpr ⟨parameters.bridge.target, List.mem_finRange _, rfl⟩
  let units := targetFlagUnits rename position zeros
  let reduced := TreeUnits.reduceToInput tree (context (parameters := parameters) rename)
    (negate (laterTermOutput rename .healthy position parameters.bridge.target)) member units
  have pair : DirectionPair reduced.state (context (parameters := parameters) rename)
      (laterFlagOutput rename .healthy position) (laterTermOutput rename .healthy position parameters.bridge.target) := by
    have forwards := dualTransfer reduced.pair.backward
    have backwards := dualTransfer reduced.pair.forward
    simpa only [tree, dualLiteral, laterFlagOutput, negate_negate] using
      (show DirectionPair reduced.state _ _ _ from ⟨forwards, backwards⟩)
  refine ⟨reduced.state, reduced.steps, reduced.checked, pair, ?_⟩
  have length : ((laterFlagInputs .healthy position).map (dualLiteral rename)).length = parameters.channels := by
    simp [laterFlagInputs]
  simpa only [tree, AndTree.afterTrace_nodes, length] using reduced.count

theorem termInputSize (position : Fin (laterBuses (parameters := parameters)).length)
    (channel : Fin parameters.channels) :
    (laterTermInputs (parameters := parameters) .healthy position channel).length ≤ parameters.buses + 2 := by
  have bounded := List.length_filter_le
    (fun earlier : Fin parameters.buses => earlier < (laterBuses (parameters := parameters))[position.val])
    (List.finRange parameters.buses)
  simp only [List.length_finRange] at bounded
  simp only [laterTermInputs, List.length_append, List.length_cons, List.length_nil, List.length_map]
  omega

theorem otherTermSize (rename : Nat → Fin v)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (table : Table (parameters := parameters) rename position.val) (channel : Fin parameters.channels)
    (different : channel ≠ parameters.bridge.target) :
    (otherTerm rename position table channel different).steps.length ≤ 2 * parameters.buses + 5 := by
  have actual := (otherTerm rename position table channel different).count
  have nodes := (laterTermTree (parameters := parameters) rename .healthy position channel).nodes_leaves
  have inputs := termInputSize position channel
  simp only [List.length_map] at nodes
  omega

theorem collectOtherTermsSize (rename : Nat → Fin v)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (table : Table (parameters := parameters) rename position.val) (channels : List (Fin parameters.channels)) :
    (collectOtherTerms rename position table channels).steps.length ≤
      channels.length * (2 * parameters.buses + 5) := by
  induction channels generalizing table with
  | nil => simp [collectOtherTerms]
  | cons channel rest ih =>
    by_cases same : channel = parameters.bridge.target
    · simpa only [collectOtherTerms, dite_eq_left same, List.length_cons] using
        (ih table).trans (by simp only [Nat.add_mul, Nat.one_mul]; omega)
    · have current := otherTermSize rename position table channel same
      have later := ih (table.afterTrace (otherTerm rename position table channel same).state
        (otherTerm rename position table channel same).steps (otherTerm rename position table channel same).checked)
      simp only [collectOtherTerms, dite_eq_right same, List.length_append, List.length_cons]
      simp only [Nat.add_mul, Nat.one_mul]
      omega

theorem targetTermSize (rename : Nat → Fin v)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (table : Table (parameters := parameters) rename position.val) (drive : parameters.drive = true) :
    (targetTerm rename position table drive).steps.length ≤ 5 * parameters.buses + 12 := by
  have actual := (targetTerm rename position table drive).count
  have nodes := (laterTermTree (parameters := parameters) rename .healthy position parameters.bridge.target).nodes_leaves
  have inputs := termInputSize position parameters.bridge.target
  simp only [List.length_map] at nodes
  omega

theorem targetFlagSize (rename : Nat → Fin v)
    (position : Fin (laterBuses (parameters := parameters)).length)
    {start : Table (parameters := parameters) rename position.val}
    (zeros : TermZeros (parameters := parameters) rename position start (List.finRange parameters.channels)) :
    (targetFlag rename position zeros).steps.length ≤ 5 * parameters.channels := by
  have actual := (targetFlag rename position zeros).count
  have nodes := (laterFlagTree (parameters := parameters) rename .healthy position).nodes_leaves
  simp only [laterFlagInputs, List.length_map, List.length_finRange] at nodes
  change (laterFlagTree (parameters := parameters) rename .healthy position).nodes + 1 = parameters.channels at nodes
  generalize (targetFlag rename position zeros).steps.length = emitted at actual ⊢
  generalize (laterFlagTree (parameters := parameters) rename .healthy position).nodes = nodeCount at actual nodes
  omega

structure MaskStep (rename : Nat → Fin v)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (start : Table (parameters := parameters) rename position.val) where
  state : State v
  steps : List (Step v)
  checked : runSteps start.proofPrefix.state steps = some state
  result : AvailableSubclause state (context (parameters := parameters) rename ++
    [laterMaskOutput rename .healthy position parameters.bridge.target])
  pair : DirectionPair state (context (parameters := parameters) rename)
    (laterFlagOutput rename .healthy position) (targetRequest rename position)
  count : steps.length ≤ 50 * (parameters.channels + 1) * (parameters.buses + 1)

def currentTargetMask (rename : Nat → Fin v)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (table : Table (parameters := parameters) rename position.val) (drive : parameters.drive = true) :
    MaskStep (parameters := parameters) rename position table := by
  let term := targetTerm rename position table drive
  let next := table.afterTrace term.state term.steps term.checked
  let zeros := collectOtherTerms rename position next (List.finRange parameters.channels)
  let flag := targetFlag rename position zeros
  have zerosRun : runSteps term.state zeros.steps = some zeros.table.proofPrefix.state := zeros.checked
  let termNow := term.pair.afterTrace flag.state (zeros.steps ++ flag.steps) (by
    rw [runSteps_append, zerosRun]
    exact flag.checked)
  let paired := TreeUnits.composePairs flag.state (context (parameters := parameters) rename) flag.pair termNow
  let prefixState := zeros.table.proofPrefix.extend paired.state (flag.steps ++ paired.steps) (by
    rw [runSteps_append, flag.checked]
    exact paired.checked)
  let xorRows := laterMaskNativeRows rename .healthy position parameters.bridge.target prefixState
  let notRows := laterAbsentNativeRows rename .healthy position parameters.bridge.target prefixState
  have equal : DirectionPair paired.state (context (parameters := parameters) rename)
      (laterMaskFlag rename .healthy position parameters.bridge.target)
      (laterAbsentInput rename .healthy position parameters.bridge.target) := by
    simpa only [laterMaskFlag_eq_flagOutput, laterAbsentInput_eq_termOutput] using
      flag.pair.afterTrace paired.state paired.steps paired.checked
  have negRows : NotRows paired.state
      (laterAbsentInput rename .healthy position parameters.bridge.target)
      (laterMaskAbsent rename .healthy position parameters.bridge.target) := by
    simpa only [laterMaskAbsent_eq_absentOutput, prefixState, SourcePrefix.extend] using notRows
  let mask := XorUnits.complementary paired.state (context (parameters := parameters) rename)
    _ _ _ _ xorRows negRows equal
  refine ⟨mask.state, (((term.steps ++ zeros.steps) ++ flag.steps) ++ paired.steps) ++ mask.steps, ?_,
    mask.result, paired.pair.afterTrace mask.state mask.steps mask.checked, ?_⟩
  · simp only [runSteps_append, term.checked, Option.bind_some, zerosRun, flag.checked,
      paired.checked, mask.checked]
  · have a := targetTermSize rename position table drive
    have b := collectOtherTermsSize rename position next (List.finRange parameters.channels)
    have c := targetFlagSize rename position zeros
    have d := paired.count
    have e := mask.count
    simp only [List.length_finRange] at b
    simp only [List.length_append]
    change term.steps.length + zeros.steps.length + flag.steps.length + paired.steps.length + mask.steps.length ≤ _
    change term.steps.length ≤ _ at a
    change zeros.steps.length ≤ _ at b
    change flag.steps.length ≤ _ at c
    ring_nf at b ⊢
    omega

def advance (rename : Nat → Fin v)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (table : Table (parameters := parameters) rename position.val) (drive : parameters.drive = true) :
    Table (parameters := parameters) rename (position.val + 1) := by
  let mask := currentTargetMask rename position table drive
  let next := table.afterTrace mask.state mask.steps mask.checked
  refine ⟨next.proofPrefix, next.firstZero, next.firstAbsent, ?_, ?_⟩
  · intro bus member
    by_cases same : bus = (laterBuses (parameters := parameters))[position.val]
    · subst bus
      rw [stagesBefore_current_mask]
      exact mask.result
    · have old : bus ∈ parameters.firstBus :: (laterBuses (parameters := parameters)).take position.val := by
        rw [List.take_succ_eq_append_getElem position.isLt] at member
        simp only [List.mem_cons, List.mem_append, List.mem_singleton] at member ⊢
        aesop
      rw [stagesBefore_succ, laterBus_mask_other .healthy .healthy _ bus parameters.bridge.target same]
      exact next.targetMasks bus old
  · intro query before
    by_cases same : query = position
    · subst query
      exact mask.pair
    · exact next.flagRequests query (by
        have ne : query.val ≠ position.val := fun equal => same (Fin.ext equal)
        omega)

def buildPrefix (rename : Nat → Fin v) (drive : parameters.drive = true) :
    (count : Nat) → count ≤ (laterBuses (parameters := parameters)).length →
      Table (parameters := parameters) rename count
  | 0, _ => initial rename drive
  | count + 1, bound =>
    advance rename ⟨count, by omega⟩ (buildPrefix rename drive count (by omega)) drive

def allMasks (rename : Nat → Fin v) (drive : parameters.drive = true) :
    Table (parameters := parameters) rename (laterBuses (parameters := parameters)).length :=
  buildPrefix rename drive _ (Nat.le_refl _)

end Controller.NativeProof.SourceHealthyMasks
