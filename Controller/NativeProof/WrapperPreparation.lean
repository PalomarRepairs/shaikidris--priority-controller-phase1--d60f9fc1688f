module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.WrapperControllerOrigins

@[expose] public section

/-! Retained-original provenance for the native preparation shared by optional
and selected observation refutations. -/
namespace Controller.NativeProof.Wrapper
open Controller.CNF Controller.Resolution Controller.Native Controller.Native.SourceController
open Controller.NativeProof.FoldProjection Controller.NativeProof.SourceFoldProjection
open Controller.NativeProof.SourceStageCongruence Controller.NativeProof.SourceBusSchedule
open Controller.NativeProof.SourceFoldProvenance Controller.NativeProof.SourceMismatchHandles
open Controller.NativeProof.SourceMismatchSeed Controller.NativeProof.SourceMismatchAdvance
open Controller.NativeProof.SourceStageXor
variable {parameters : Parameters} {v : Nat}

def AbsenceBankOrigins (rename : Nat → Fin v)
    (start : SourcePrefix (parameters := parameters) rename)
    {channels : List (Fin parameters.channels)} (bank : AbsenceBank rename start channels) : Prop :=
  TraceOriginalSupport (formula parameters).clauses.size
    (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
    (start.steps ++ bank.steps) ∧
  ∀ channel member, ResultOrigin (formula parameters).clauses.size
    (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
    (start.steps ++ bank.steps) (bank.rows channel member).row.id

theorem buildAbsenceBank_origins (rename : Nat → Fin v)
    (start : SourcePrefix (parameters := parameters) rename)
    (channels : List (Fin parameters.channels))
    (nonTarget : ∀ channel ∈ channels, channel ≠ parameters.bridge.target)
    (supported : SourceMixedSchedule.PrefixOriginalSupport rename start) :
    AbsenceBankOrigins rename start (buildAbsenceBank rename start channels nonTarget) := by
  induction channels generalizing start with
  | nil =>
    constructor
    · simpa only [buildAbsenceBank, buildAbsenceBankStep, List.append_nil,
        SourceMixedSchedule.PrefixOriginalSupport] using supported
    · intro channel member
      simp at member
  | cons channel rest ih =>
    let different := nonTarget channel (by simp)
    let first := otherAbsenceAt rename start channel different
    let nextPrefix := start.extend first.state first.steps first.checked
    let next := buildAbsenceBank rename nextPrefix rest (by
      intro query member
      exact nonTarget query (List.mem_cons_of_mem channel member))
    have one := ControllerOrigins.otherAbsenceAt_supported rename start channel different supported
    have tail := ih nextPrefix (fun query member => nonTarget query (List.mem_cons_of_mem channel member)) one.1
    constructor
    · simpa only [buildAbsenceBank, buildAbsenceBankStep, AbsenceBankOrigins, nextPrefix, SourcePrefix.extend,
        next, first, different, List.append_assoc] using tail.1
    · intro query member
      by_cases same : query = channel
      · subst query
        have origin := resultOrigin_append_right _ _ (start.steps ++ first.steps)
          next.steps first.result.row.id one.2
        simpa only [buildAbsenceBank, buildAbsenceBankStep, SourceMixedSchedule.subclause_dite_id, dite_eq_left rfl, dite_true,
          afterTrace, next, nextPrefix, SourcePrefix.extend, first, different,
          List.append_assoc] using origin
      · have restMember := (List.mem_cons.mp member).resolve_left same
        have origin := tail.2 query restMember
        simpa only [buildAbsenceBank, buildAbsenceBankStep, SourceMixedSchedule.subclause_dite_id, dite_eq_right same,
          next, nextPrefix, SourcePrefix.extend, first, different, List.append_assoc] using origin

theorem allOtherAbsences_origins (rename : Nat → Fin v) :
    AbsenceBankOrigins rename (SourcePrefix.initial rename)
      (allOtherAbsences (parameters := parameters) rename) := by
  apply buildAbsenceBank_origins
  intro step member
  simp only [SourcePrefix.initial, List.not_mem_nil] at member

def MaskSeedOrigins (rename : Nat → Fin v)
    (start : SourcePrefix (parameters := parameters) rename) (seeds : MaskSeedBank rename start) : Prop :=
  ∀ channel, ResultOrigin (formula parameters).clauses.size
    (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
    start.steps (seeds.rows channel).row.id

theorem MaskSeedOrigins.afterTrace (rename : Nat → Fin v)
    (start : SourcePrefix (parameters := parameters) rename) (seeds : MaskSeedBank rename start)
    (next : State v) (steps : List (Step v)) (checked : runSteps start.state steps = some next)
    (origins : MaskSeedOrigins rename start seeds) :
    MaskSeedOrigins rename (start.extend next steps checked) (seeds.afterTrace next steps checked) := by
  intro channel
  exact resultOrigin_append_right _ _ start.steps steps _ (origins channel)

def FirstMaskPairOrigins (rename : Nat → Fin v)
    (start : SourcePrefix (parameters := parameters) rename) {channel : Fin parameters.channels}
    (pair : FirstMaskPair rename start channel) : Prop :=
  TraceOriginalSupport (formula parameters).clauses.size
    (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
    (start.steps ++ pair.steps) ∧
  ∀ side, ResultOrigin (formula parameters).clauses.size
    (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
    (start.steps ++ pair.steps) (pair.rows side).row.id

theorem firstMaskPair_origins (rename : Nat → Fin v)
    (start : SourcePrefix (parameters := parameters) rename) (seeds : MaskSeedBank rename start)
    (channel : Fin parameters.channels)
    (supported : SourceMixedSchedule.PrefixOriginalSupport rename start)
    (origins : MaskSeedOrigins rename start seeds) :
    FirstMaskPairOrigins rename start (firstMaskPair rename start seeds channel) := by
  let healthy := maskValueAt rename start .healthy channel (absenceBit channel) (seeds.rows channel)
  let healthyPrefix := start.extend healthy.state healthy.steps healthy.checked
  let healthySeeds := seeds.afterTrace healthy.state healthy.steps healthy.checked
  let faulty := maskValueAt rename healthyPrefix .faulty channel (absenceBit channel) (healthySeeds.rows channel)
  have one := ControllerOrigins.maskValueAt_supported rename start .healthy channel (absenceBit channel)
    (seeds.rows channel) supported (origins channel)
  have seedOrigin := MaskSeedOrigins.afterTrace rename start seeds healthy.state healthy.steps healthy.checked origins
  have two := ControllerOrigins.maskValueAt_supported rename healthyPrefix .faulty channel (absenceBit channel)
    (healthySeeds.rows channel) one.1 (seedOrigin channel)
  constructor
  · simpa only [firstMaskPair, healthyPrefix, SourcePrefix.extend, healthy, faulty,
      healthySeeds, List.append_assoc] using two.1
  · intro side
    cases side with
    | healthy =>
      have origin := resultOrigin_append_right _ _ (start.steps ++ healthy.steps)
        faulty.steps healthy.result.row.id one.2
      simpa only [firstMaskPair, afterTrace, healthyPrefix, SourcePrefix.extend,
        healthy, faulty, healthySeeds, List.append_assoc] using origin
    | faulty =>
      simpa only [firstMaskPair, healthyPrefix, SourcePrefix.extend, healthy,
        faulty, healthySeeds, List.append_assoc] using two.2

def FirstMaskBankOrigins (rename : Nat → Fin v)
    (start : SourcePrefix (parameters := parameters) rename)
    {channels : List (Fin parameters.channels)} (bank : FirstMaskBank rename start channels) : Prop :=
  TraceOriginalSupport (formula parameters).clauses.size
    (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
    (start.steps ++ bank.steps) ∧
  ∀ side channel member, ResultOrigin (formula parameters).clauses.size
    (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
    (start.steps ++ bank.steps) (bank.rows side channel member).row.id

theorem FirstMaskBank.prepend_origins (rename : Nat → Fin v)
    (start : SourcePrefix (parameters := parameters) rename) (channel : Fin parameters.channels)
    (rest : List (Fin parameters.channels)) (pair : FirstMaskPair rename start channel)
    (next : FirstMaskBank rename (start.extend pair.state pair.steps pair.checked) rest)
    (pairOrigins : FirstMaskPairOrigins rename start pair)
    (nextOrigins : FirstMaskBankOrigins rename (start.extend pair.state pair.steps pair.checked) next) :
    FirstMaskBankOrigins rename start (FirstMaskBank.prepend rename start channel rest pair next) := by
  constructor
  · simpa only [FirstMaskBank.prepend, SourcePrefix.extend, List.append_assoc] using nextOrigins.1
  · intro side query member
    by_cases same : query = channel
    · subst query
      have origin := resultOrigin_append_right _ _ (start.steps ++ pair.steps)
        next.steps (pair.rows side).row.id (pairOrigins.2 side)
      simpa only [FirstMaskBank.prepend, SourceMixedSchedule.subclause_dite_id,
        dite_eq_left rfl, dite_true, afterTrace, List.append_assoc] using origin
    · simpa only [FirstMaskBank.prepend, SourceMixedSchedule.subclause_dite_id,
        dite_eq_right same, SourcePrefix.extend, List.append_assoc] using
        nextOrigins.2 side query ((List.mem_cons.mp member).resolve_left same)

theorem buildFirstMaskBank_origins (rename : Nat → Fin v)
    (start : SourcePrefix (parameters := parameters) rename) (seeds : MaskSeedBank rename start)
    (channels : List (Fin parameters.channels))
    (supported : SourceMixedSchedule.PrefixOriginalSupport rename start)
    (origins : MaskSeedOrigins rename start seeds) :
    FirstMaskBankOrigins rename start (buildFirstMaskBank rename start seeds channels) := by
  induction channels generalizing start with
  | nil =>
    constructor
    · simpa only [buildFirstMaskBank, List.append_nil,
        SourceMixedSchedule.PrefixOriginalSupport] using supported
    · intro side channel member
      simp at member
  | cons channel rest ih =>
    let pair := firstMaskPair rename start seeds channel
    have one := firstMaskPair_origins rename start seeds channel supported origins
    have carried := MaskSeedOrigins.afterTrace rename start seeds pair.state pair.steps pair.checked origins
    have next := ih (start.extend pair.state pair.steps pair.checked)
      (seeds.afterTrace pair.state pair.steps pair.checked) one.1 carried
    exact FirstMaskBank.prepend_origins rename start channel rest pair _ one next

theorem allMaskSeeds_origins (rename : Nat → Fin v) (drive : parameters.drive = true) :
    let bank := allOtherAbsences (parameters := parameters) rename
    let start : SourcePrefix (parameters := parameters) rename := ⟨bank.state, bank.steps, bank.checked⟩
    MaskSeedOrigins rename start (allMaskSeeds rename drive) := by
  dsimp only
  intro channel
  by_cases same : channel = parameters.bridge.target
  · subst channel
    have origin : ResultOrigin (formula parameters).clauses.size
        (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
        (allOtherAbsences (parameters := parameters) rename).steps
        (SourceMismatchBranch.physicalUnitRow (parameters := parameters) rename ⟨0, by decide⟩).id :=
      Or.inl (SourceMismatchBranch.physicalUnit_allowed (parameters := parameters) rename ⟨0, by decide⟩)
    simp only [allMaskSeeds, id, SourceMixedSchedule.subclause_dite_id, dite_eq_left rfl,
      dite_true]
    with_unfolding_all
      rw [SourceMixedSchedule.subclause_indices_mpr_id
        (show (allOtherAbsences (parameters := parameters) rename).state =
          (allOtherAbsences (parameters := parameters) rename).state from rfl)
        (show mixedContext (parameters := parameters) rename ++
          [absenceValue rename parameters.bridge.target (absenceBit parameters.bridge.target)] =
          mixedContext (parameters := parameters) rename ++
          [absenceValue rename parameters.bridge.target false] from by simp [absenceBit])]
    simpa only [ofRow, retarget, afterTrace] using origin
  · have present : channel ∈ (List.finRange parameters.channels).filter
        (fun query => decide (query ≠ parameters.bridge.target)) :=
      List.mem_filter.mpr ⟨List.mem_finRange _, decide_eq_true same⟩
    have origin := (allOtherAbsences_origins (parameters := parameters) rename).2 channel present
    simp only [allMaskSeeds, id, SourceMixedSchedule.subclause_dite_id, dite_eq_right same, dite_false]
    with_unfolding_all
      rw [SourceMixedSchedule.subclause_indices_mpr_id
        (show (allOtherAbsences (parameters := parameters) rename).state =
          (allOtherAbsences (parameters := parameters) rename).state from rfl)
        (show mixedContext (parameters := parameters) rename ++ [absenceValue rename channel (absenceBit channel)] =
          mixedContext (parameters := parameters) rename ++ [mapLiteral rename
            ((firstArrays parameters).slots (.internal (.absent .healthy parameters.firstBus channel)))] from by
          simp [absenceBit, same, absenceValue, valueLiteral])]
    simpa only [SourcePrefix.initial, List.nil_append, allOtherAbsences_complete] using origin

theorem allFirstMasks_origins (rename : Nat → Fin v) (drive : parameters.drive = true) :
    let bank := allOtherAbsences (parameters := parameters) rename
    let start : SourcePrefix (parameters := parameters) rename := ⟨bank.state, bank.steps, bank.checked⟩
    FirstMaskBankOrigins rename start (allFirstMasks rename drive) := by
  dsimp only
  apply buildFirstMaskBank_origins
  · simpa only [SourcePrefix.initial, List.nil_append, SourceMixedSchedule.PrefixOriginalSupport] using
      (allOtherAbsences_origins (parameters := parameters) rename).1
  · exact allMaskSeeds_origins rename drive

end Controller.NativeProof.Wrapper
