module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.SourceSuffixSelector
public import Controller.NativeProof.SourceMismatchAdvance
public import Controller.NativeProof.SourceBusAdvance

@[expose] public section

/-! Concrete cursor identities for the descending mixed selector traversal.
The masks consumed by a later term retain their actual source occurrence
handles; no supplied role map or available-row premise is used. -/
namespace Controller.NativeProof.SourceMixedSelector
open Controller.CNF Controller.Resolution Controller.Native Controller.Native.SourceController
open Controller.NativeProof.SourceFoldOccurrences Controller.NativeProof.SourceStageCongruence
open Controller.NativeProof.SourceSlotFrames Controller.NativeProof.SourceRoleFrames
open Controller.NativeProof.SourceSuffixSelector
open Controller.NativeProof.FoldProjection Controller.NativeProof.SourceFoldProjection
open Controller.NativeProof.SourceStagePolarity
open Controller.NativeProof.SourceStageXor Controller.NativeProof.SourceBusAdvance
variable {parameters : Parameters} {v : Nat}

/-- Term formation updates its term slot and retains every mask slot. -/
theorem termStep_mask_frame (side : Side) (bus query : Fin parameters.buses)
    (channel input : Fin parameters.channels) (cursor : Cursor parameters) :
    (termStep side bus cursor input).slots (.internal (.mask side query channel)) =
      cursor.slots (.internal (.mask side query channel)) := by
  apply foldNative_other
  simp

theorem termPrefix_mask_frame (side : Side) (bus query : Fin parameters.buses)
    (channel : Fin parameters.channels) (values : List (Fin parameters.channels))
    (cursor : Cursor parameters) :
    (values.foldl (termStep side bus) cursor).slots (.internal (.mask side query channel)) =
      cursor.slots (.internal (.mask side query channel)) := by
  apply foldl_slot
  intro current input
  exact termStep_mask_frame side bus query channel input current

/-- Subsequent distinct buses preserve the previously emitted mask handle. -/
theorem busSuffix_mask_frame (side : Side) (query : Fin parameters.buses)
    (channel : Fin parameters.channels) (values : List (Fin parameters.buses))
    (absent : query ∉ values) (cursor : Cursor parameters) :
    (values.foldl (fun current bus => laterBus parameters side bus current) cursor).slots
      (.internal (.mask side query channel)) = cursor.slots (.internal (.mask side query channel)) := by
  apply foldl_slot_mem
  intro current bus member
  apply laterBus_mask_frame
  intro equal
  exact absent (equal.symm ▸ member)

/-- The current term's channel prefix does not alter an earlier mask input. -/
theorem termBefore_mask_frame (side : Side)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (query : Fin parameters.buses) (channel : Fin parameters.channels) :
    (termBefore side position channel).slots (.internal (.mask side query channel)) =
      (busBefore side position).slots (.internal (.mask side query channel)) := by
  apply termPrefix_mask_frame

/-- The output of the actual stored XOR emission has its positive allocated
phase before any subsequent channel or bus is traversed. -/
def laterMaskHandle (side : Side)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (channel : Fin parameters.channels) : Literal Nat :=
  ((laterMaskBefore side position channel).lastID + 1, true)

theorem laterMask_emit_handle (side : Side)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (channel : Fin parameters.channels) :
    ((laterMaskBefore side position channel).emitNative
      (.internal (.mask side (laterBuses (parameters := parameters))[position.val] channel))
      (.xor ((laterMaskBefore side position channel).slots
        (.internal (.flag side (laterBuses (parameters := parameters))[position.val])))
        ((laterMaskBefore side position channel).slots
          (.internal (.absent side (laterBuses (parameters := parameters))[position.val] channel))))).slots
      (.internal (.mask side (laterBuses (parameters := parameters))[position.val] channel)) =
        laterMaskHandle side position channel := by
  simp [Cursor.emitNative, Cursor.emit, Cursor.assign, laterMaskHandle]

theorem busMaskStep_other_mask (side : Side) (bus : Fin parameters.buses)
    (query input : Fin parameters.channels) (different : query ≠ input)
    (cursor : Cursor parameters) :
    (busMaskStep side bus cursor input).slots (.internal (.mask side bus query)) =
      cursor.slots (.internal (.mask side bus query)) := by
  simp [busMaskStep, Cursor.emitNative, Cursor.emit, Cursor.assign, different]

theorem channelSuffix_mask_frame (side : Side) (bus : Fin parameters.buses)
    (query : Fin parameters.channels) (values : List (Fin parameters.channels))
    (absent : query ∉ values) (cursor : Cursor parameters) :
    (values.foldl (busMaskStep side bus) cursor).slots (.internal (.mask side bus query)) =
      cursor.slots (.internal (.mask side bus query)) := by
  apply foldl_slot_mem
  intro current input member
  apply busMaskStep_other_mask
  intro equal
  exact absent (equal.symm ▸ member)

/-- The represented channel position determines the mask's occurrence. The
remaining channels retain that same output; sharing is not unfolded. -/
theorem laterBus_mask_output (side : Side)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (channel : Fin parameters.channels) :
    (laterBus parameters side (laterBuses (parameters := parameters))[position.val]
      (busBefore side position)).slots
      (.internal (.mask side (laterBuses (parameters := parameters))[position.val] channel)) =
      laterMaskHandle side position channel := by
  let bus := (laterBuses (parameters := parameters))[position.val]
  have bound : channel.val < (List.finRange parameters.channels).length := by
    simpa using channel.isLt
  have decomposition : List.finRange parameters.channels =
      (List.finRange parameters.channels).take channel.val ++ channel ::
        (List.finRange parameters.channels).drop (channel.val + 1) := by
    simpa using positional_decomposition (List.finRange parameters.channels) ⟨channel.val, bound⟩
  have distinct : channel ∉ (List.finRange parameters.channels).drop (channel.val + 1) := by
    have nodup := List.nodup_finRange parameters.channels
    rw [decomposition] at nodup
    exact (List.nodup_cons.mp (List.nodup_append.mp nodup).2.1).1
  change ((List.finRange parameters.channels).foldl (busMaskStep side bus)
    (busFlag side bus (busBefore side position))).slots (.internal (.mask side bus channel)) = _
  rw [decomposition, List.foldl_append]
  simp only [List.foldl_cons]
  rw [channelSuffix_mask_frame side bus channel _ distinct]
  exact laterMask_emit_handle side position channel

theorem tailStages_mask (side : Side)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (channel : Fin parameters.channels) :
    (tailStages (parameters := parameters) side).slots
      (.internal (.mask side (laterBuses (parameters := parameters))[position.val] channel)) =
      laterMaskHandle side position channel := by
  let values := laterBuses (parameters := parameters)
  let bus := values[position.val]
  have decomposition := positional_decomposition values position
  have distinct : bus ∉ values.drop (position.val + 1) := by
    have nodup : values.Nodup := List.Nodup.filter _ (List.nodup_finRange parameters.buses)
    rw [decomposition] at nodup
    exact (List.nodup_cons.mp (List.nodup_append.mp nodup).2.1).1
  change (values.foldl (fun cursor bus => laterBus parameters side bus cursor)
    (initialMasks parameters side (tailStart side))).slots (.internal (.mask side bus channel)) = _
  rw [decomposition, List.foldl_append]
  simp only [List.foldl_cons]
  rw [busSuffix_mask_frame side bus channel _ distinct]
  exact laterBus_mask_output side position channel

/-- Earlier represented masks have the same stored handle in the later term
and in the completed controller tail. The strict order is an index relation
between actual positions, rather than a supplied handle-map premise. -/
theorem earlierMask_term_handle (side : Side)
    (earlier later : Fin (laterBuses (parameters := parameters)).length)
    (order : earlier.val < later.val) (channel : Fin parameters.channels) :
    (termBefore side later channel).slots
      (.internal (.mask side (laterBuses (parameters := parameters))[earlier.val] channel)) =
      laterMaskHandle side earlier channel := by
  let values := laterBuses (parameters := parameters)
  let query := values[earlier.val]
  have member : query ∈ values.take later.val := by
    apply List.mem_take_iff_getElem.mpr
    have bound : earlier.val < values.length := earlier.isLt
    exact ⟨earlier.val, Nat.lt_min.mpr ⟨order, bound⟩, rfl⟩
  have distinct : query ∉ values.drop later.val := by
    have nodup : values.Nodup := List.Nodup.filter _ (List.nodup_finRange parameters.buses)
    have split : values = values.take later.val ++ values.drop later.val :=
      (List.take_append_drop later.val values).symm
    rw [split] at nodup
    intro found
    exact (List.nodup_append.mp nodup).2.2 query member query found rfl
  have retained : (tailStages (parameters := parameters) side).slots
      (.internal (.mask side query channel)) =
      (busBefore side later).slots (.internal (.mask side query channel)) := by
    change (values.foldl (fun cursor bus => laterBus parameters side bus cursor)
      (initialMasks parameters side (tailStart side))).slots (.internal (.mask side query channel)) = _
    rw [← List.take_append_drop later.val values, List.foldl_append]
    exact busSuffix_mask_frame side query channel _ distinct _
  exact (termBefore_mask_frame side later query channel).trans
    (retained.symm.trans (tailStages_mask side earlier channel))

/-- Compose checked projections without reducing their source computations. -/
def appendProjection (first : SubclauseProjection state firstTarget firstBudget)
    (second : SubclauseProjection first.state secondTarget secondBudget) :
    SubclauseProjection state secondTarget (firstBudget + secondBudget) := by
  refine ⟨second.state, first.steps ++ second.steps, ?_, second.result, ?_⟩
  · rw [runSteps_append, first.checked]
    exact second.checked
  · simpa only [List.length_append] using Nat.add_le_add first.count second.count

/-- Three ordinary merges over abstract current rows. The source-facing
constructor below obtains all four premises from their actual occurrences. -/
def maskGuardRows (state : State v) (p z u m g : Literal (Fin v))
    (leftOne : AvailableSubclause state [negate p, negate u, negate m])
    (positiveNot : AvailableSubclause state [u, z])
    (rightOne : AvailableSubclause state [p, g])
    (termGuard : AvailableSubclause state [negate z, g]) :
    SubclauseProjection state [negate m, g] 3 := by
  let joinOne := longMerge state p [negate u, negate m] [g] leftOne rightOne
  have runOne := longMerge_run state p [negate u, negate m] [g] leftOne rightOne
  let leftTwo := FoldProjection.afterTrace termGuard joinOne.state joinOne.steps runOne
  let notRow := FoldProjection.afterTrace positiveNot joinOne.state joinOne.steps runOne
  let rightTwo : AvailableSubclause joinOne.state [z, u] := retarget notRow (by
    intro literal found
    simp only [List.mem_cons, List.not_mem_nil, or_false] at found ⊢
    exact found.elim Or.inr Or.inl)
  let joinTwo := longMerge joinOne.state z [g] [u] leftTwo rightTwo
  have runTwo := longMerge_run joinOne.state z [g] [u] leftTwo rightTwo
  let leftThree := FoldProjection.afterTrace
    (longMerge_result state p [negate u, negate m] [g] leftOne rightOne)
    joinTwo.state joinTwo.steps runTwo
  let rightThree : AvailableSubclause joinTwo.state [u, g] :=
    retarget (longMerge_result joinOne.state z [g] [u] leftTwo rightTwo) (by
      intro literal found
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at found ⊢
      exact found.elim Or.inr Or.inl)
  let joinThree := longMerge joinTwo.state u [negate m, g] [g] leftThree rightThree
  have runThree := longMerge_run joinTwo.state u [negate m, g] [g] leftThree rightThree
  refine ⟨joinThree.state, joinOne.steps ++ (joinTwo.steps ++ joinThree.steps), ?_, ?_, ?_⟩
  · have firstRun : runSteps state joinOne.steps = some joinOne.state := runOne
    have secondRun : runSteps joinOne.state joinTwo.steps = some joinTwo.state := runTwo
    rw [runSteps_append, firstRun]
    simp only [Option.bind_some]
    rw [runSteps_append, secondRun]
    simp only [Option.bind_some]
    exact runThree
  · apply retarget (longMerge_result joinTwo.state u [negate m, g] [g] leftThree rightThree)
    intro literal found
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at found ⊢
    aesop
  · have one := longMerge_count state p [negate u, negate m] [g] leftOne rightOne
    have two := longMerge_count joinOne.state z [g] [u] leftTwo rightTwo
    have three := longMerge_count joinTwo.state u [negate m, g] [g] leftThree rightThree
    change joinOne.steps.length ≤ 1 at one
    change joinTwo.steps.length ≤ 1 at two
    change joinThree.steps.length ≤ 1 at three
    simp only [List.length_append]
    omega

/-- An actual later mask implies its channel guard. The four original
XOR/NOT inputs and the term/request projection are read at the current source
prefix. Missing pivots retain stronger rows; no weakened row is inserted. -/
def maskGuardAt (rename : Nat → Fin v) (prefixState : SourcePrefix (parameters := parameters) rename)
    (side : Side) (position : Fin (laterBuses (parameters := parameters)).length)
    (channel : Fin parameters.channels) :
    SubclauseProjection prefixState.state
      [negate (laterMaskOutput rename side position channel),
       mapLiteral rename (guardHandle side channel (laterBuses (parameters := parameters))[position.val])]
      (2 * (laterTermTree rename side position channel).nodes + 5) := by
  let bus := (laterBuses (parameters := parameters))[position.val]
  let g := mapLiteral rename (guardHandle side channel bus)
  let p := laterFlagOutput rename side position
  let z := laterTermOutput rename side position channel
  let u := laterAbsentOutput rename side position channel
  let m := laterMaskOutput rename side position channel
  let first := guardOrFlagAt rename prefixState side channel bus
  let current := prefixState.extend first.state first.steps first.checked
  let second := sameBusTermGuardAt rename current side position channel
  have secondRun : runSteps first.state second.steps = some second.state := by
    simpa only [current, SourcePrefix.extend] using second.checked
  let next := current.extend second.state second.steps second.checked
  let originalXor := laterMaskNativeRows rename side position channel next
  let originalNot := laterAbsentNativeRows rename side position channel next
  let guardFlag := FoldProjection.afterTrace first.result second.state second.steps second.checked
  have flagAligned : mapLiteral rename (flagInput side bus) = p := by
    rw [flagInput_busFlag side position]
    rfl
  let leftOne : AvailableSubclause second.state [negate p, negate u, negate m] := by
    simpa only [next, SourcePrefix.extend, laterMaskFlag_eq_flagOutput, laterMaskAbsent_eq_absentOutput, p, u, m] using originalXor.oneOne
  let rightOne : AvailableSubclause second.state [p, g] := retarget guardFlag (by
    intro literal found
    have member := found
    simp only [List.mem_cons, List.not_mem_nil, or_false, flagAligned] at member ⊢
    exact member.elim Or.inr Or.inl)
  let positiveNot : AvailableSubclause second.state [u, z] := by
    simpa only [next, SourcePrefix.extend, laterAbsentInput_eq_termOutput, u, z] using originalNot.positive
  let joined := maskGuardRows second.state p z u m g leftOne positiveNot rightOne second.result
  let typedSecond : SubclauseProjection first.state [negate z, g]
      (2 * (laterTermTree rename side position channel).nodes + 1) :=
    ⟨second.state, second.steps, secondRun, second.result, second.count⟩
  let completed := appendProjection (appendProjection first typedSecond) joined
  refine ⟨completed.state, completed.steps, completed.checked, completed.result, ?_⟩
  calc
    completed.steps.length ≤ (1 + (2 * (laterTermTree rename side position channel).nodes + 1)) + 3 :=
      completed.count
    _ ≤ 2 * (laterTermTree rename side position channel).nodes + 5 := by omega

/-- A later term implies every earlier channel guard, through the mask
occurrence actually used by that term and the concrete mask/guard macro. -/
def earlierTermGuardAt (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename) (side : Side)
    (earlier later : Fin (laterBuses (parameters := parameters)).length)
    (order : earlier.val < later.val) (channel : Fin parameters.channels) :
    SubclauseProjection prefixState.state
      [negate (laterTermOutput rename side later channel),
       mapLiteral rename (guardHandle side channel (laterBuses (parameters := parameters))[earlier.val])]
      (2 * (laterTermTree rename side earlier channel).nodes +
       2 * (laterTermTree rename side later channel).nodes + 6) := by
  let first := maskGuardAt rename prefixState side earlier channel
  let current := prefixState.extend first.state first.steps first.checked
  let tree := (laterTermTree rename side later channel).afterTrace
    current.state current.steps current.checked
  have two : 2 ≤ ((laterTermInputs side later channel).map (mapLiteral rename)).length := by
    simp [laterTermInputs]
  let projected := nonunaryTreeInputs tree two
  let mask := laterMaskOutput rename side earlier channel
  let root := laterTermOutput rename side later channel
  let guard := mapLiteral rename (guardHandle side channel (laterBuses (parameters := parameters))[earlier.val])
  have member : mask ∈ ((laterTermInputs side later channel).map (mapLiteral rename)) := by
    apply List.mem_map.mpr
    refine ⟨(termBefore side later channel).slots
      (.internal (.mask side (laterBuses (parameters := parameters))[earlier.val] channel)), ?_, ?_⟩
    · have sorted : (laterBuses (parameters := parameters)).Pairwise (· < ·) :=
        (List.pairwise_lt_finRange parameters.buses).filter _
      have before : (laterBuses (parameters := parameters))[earlier.val] <
          (laterBuses (parameters := parameters))[later.val] :=
        sorted.rel_get_of_lt order
      simp only [laterTermInputs, List.mem_append, List.mem_cons, List.mem_map, List.mem_filter,
        List.mem_finRange, true_and, decide_eq_true_eq, List.not_mem_nil, or_false]
      exact Or.inr ⟨(laterBuses (parameters := parameters))[earlier.val], before, rfl⟩
    · rw [earlierMask_term_handle side earlier later order channel]
      rfl
  have projectedRun : runSteps first.state projected.steps = some projected.state := by
    simpa only [current, SourcePrefix.extend] using projected.checked
  let direction := projected.results mask member
  let guardRow := FoldProjection.afterTrace first.result projected.state projected.steps projected.checked
  let joined := guardedChain projected.state [] root mask guard direction guardRow
  refine ⟨joined.state, first.steps ++ (projected.steps ++ joined.steps), ?_, joined.result, ?_⟩
  · simp only [runSteps_append, first.checked, projectedRun, Option.bind_some]
    exact joined.checked
  · have one := first.count
    have two := projected.count
    have three := joined.count
    have unchanged := AndTree.afterTrace_nodes (laterTermTree rename side later channel)
      current.state current.steps current.checked
    change tree.nodes = (laterTermTree rename side later channel).nodes at unchanged
    simp only [List.length_append]
    omega

end Controller.NativeProof.SourceMixedSelector
