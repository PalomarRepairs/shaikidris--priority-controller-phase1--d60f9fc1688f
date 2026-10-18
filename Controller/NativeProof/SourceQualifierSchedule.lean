module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.SourceEqualSchedule
public import Controller.NativeProof.SourceSuffixSelector
public import Controller.NativeProof.SourceDecoderSchedule

@[expose] public section

/-! Source qualifier certificates retain the first-flag cofactor and every
already emitted later flag pair. Private NOT and guard OR occurrences are
read from their actual controller positions. -/
namespace Controller.NativeProof.SourceQualifierSchedule
open Controller.CNF Controller.Resolution Controller.Native Controller.Native.SourceController
open Controller.NativeProof.SourceEqualSchedule Controller.NativeProof.SourceBusSchedule
open Controller.NativeProof.SourceStageCongruence
open Controller.NativeProof.SourceCongruence Controller.NativeProof.SourceFoldProvenance
open Controller.NativeProof.SourceBusAdvance Controller.NativeProof.SourceStagePolarity
open Controller.NativeProof.SourceFoldProjection Controller.NativeProof.FoldProjection
open Controller.NativeProof.SourceFoldOwners Controller.NativeProof.SourceFoldOccurrences
open Controller.NativeProof.SourceSlotFrames Controller.NativeProof.SourceQualifierOccurrences
open Controller.NativeProof.SourceMismatchHandles Controller.NativeProof.SourceMixedSchedule
variable {parameters : Parameters} {v : Nat}

def currentBusFlagPair (rename : Nat → Fin v) (flag : Bool)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (table : BusMaskTable (parameters := parameters) rename flag position.val) :
    DirectionPair (currentBusFromTable rename flag position table).state
      (equalFlagContext (parameters := parameters) rename flag)
      (laterFlagOutput rename .healthy position) (laterFlagOutput rename .faulty position) := by
  let terms := buildTermBank rename flag position table (List.finRange parameters.channels)
  let flags := laterFlagPairFromTerms rename flag position table.checkedPrefix terms
  let inputs : MaskInputs (parameters := parameters) rename flag position :=
    ⟨terms.checkedPrefix.extend flags.state flags.steps flags.checked,
      fun channel => (terms.pairs channel (by simp)).afterTrace flags.state flags.steps flags.checked, flags.pair⟩
  let masks := buildMaskBank rename flag position inputs (List.finRange parameters.channels)
  exact flags.pair.afterTrace masks.state masks.steps masks.checked

theorem currentBusFlagPair_supported (rename : Nat → Fin v) (flag : Bool)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (table : BusMaskTable (parameters := parameters) rename flag position.val)
    (supported : BusMaskTableOriginalSupport rename flag table) :
    DirectionPairOrigin rename
      (table.checkedPrefix.extend (currentBusFromTable rename flag position table).state
        (currentBusFromTable rename flag position table).steps
        (currentBusFromTable rename flag position table).checked)
      (currentBusFlagPair rename flag position table) := by
  let terms := buildTermBank rename flag position table (List.finRange parameters.channels)
  have termSupport := buildTermBank_supported rename flag position table (List.finRange parameters.channels) supported
  let flags := laterFlagPairFromTerms rename flag position table.checkedPrefix terms
  have flagSupport := laterFlagPairFromTerms_supported rename flag position table.checkedPrefix terms termSupport
  let inputs : MaskInputs (parameters := parameters) rename flag position :=
    ⟨terms.checkedPrefix.extend flags.state flags.steps flags.checked,
      fun channel => (terms.pairs channel (by simp)).afterTrace flags.state flags.steps flags.checked, flags.pair⟩
  let masks := buildMaskBank rename flag position inputs (List.finRange parameters.channels)
  have carried := DirectionPairOrigin.afterTrace rename inputs.checkedPrefix flags.pair flagSupport.2
    masks.state masks.steps masks.checked
  let finalPrefix := table.checkedPrefix.extend masks.state ((terms.steps ++ flags.steps) ++ masks.steps) (by
    rw [runSteps_append, runSteps_append, terms.checked]
    simp only [Option.bind_some, flags.checked]
    exact masks.checked)
  have sameSteps : (inputs.checkedPrefix.extend masks.state masks.steps masks.checked).steps =
      finalPrefix.steps := by
    simp only [finalPrefix, inputs, TermBank.checkedPrefix, SourcePrefix.extend, List.append_assoc]
  have actual := DirectionPairOrigin.same_steps rename masks.state
    (inputs.checkedPrefix.extend masks.state masks.steps masks.checked).steps finalPrefix.steps sameSteps
    (inputs.checkedPrefix.extend masks.state masks.steps masks.checked).checked finalPrefix.checked
    (flags.pair.afterTrace masks.state masks.steps masks.checked) carried
  change DirectionPairOrigin rename finalPrefix (flags.pair.afterTrace masks.state masks.steps masks.checked)
  exact actual


theorem laterBus_flag_other (side querySide : Side) (bus queryBus : Fin parameters.buses)
    (cursor : Cursor parameters) (different : queryBus ≠ bus) :
    (laterBus parameters side bus cursor).slots (.internal (.flag querySide queryBus)) =
      cursor.slots (.internal (.flag querySide queryBus)) := by
  unfold laterBus
  rw [foldl_slot _ _ (fun current channel => by
    simp [Cursor.emitNative, Cursor.emit, Cursor.assign])]
  rw [foldNative_other _ _ _ _ _ (by simp [different])]
  exact foldl_slot _ _ (fun current channel => foldNative_other _ _ _ _ _ (by simp)) _ cursor

theorem stagesBefore_current_flag (rename : Nat → Fin v) (side : Side)
    (position : Fin (laterBuses (parameters := parameters)).length) :
    mapLiteral rename ((stagesBefore (parameters := parameters) side (position.val + 1)).slots
      (.internal (.flag side (laterBuses (parameters := parameters))[position.val]))) =
      laterFlagOutput rename side position := by
  rw [stagesBefore_succ, ← busBefore_eq_stagesBefore]
  change mapLiteral rename (((List.finRange parameters.channels).foldl
    (busMaskStep side (laterBuses (parameters := parameters))[position.val])
    (busFlag side (laterBuses (parameters := parameters))[position.val] (busBefore side position))).slots
      (.internal (.flag side (laterBuses (parameters := parameters))[position.val]))) = _
  rw [foldl_slot _ _ (fun current channel => busMaskStep_flag_frame side side _ _ channel current)]
  simp [busFlag, Cursor.foldNative, Cursor.assign, laterFlagOutput, laterFlagInputs]

structure FlagMaskTable (rename : Nat → Fin v) (flag : Bool) (count : Nat) where
  masks : BusMaskTable (parameters := parameters) rename flag count
  laterFlags : ∀ position : Fin (laterBuses (parameters := parameters)).length,
    position.val < count →
    DirectionPair masks.checkedPrefix.state (equalFlagContext (parameters := parameters) rename flag)
      (mapLiteral rename ((stagesBefore (parameters := parameters) .healthy count).slots
        (.internal (.flag .healthy (laterBuses (parameters := parameters))[position.val]))))
      (mapLiteral rename ((stagesBefore (parameters := parameters) .faulty count).slots
        (.internal (.flag .faulty (laterBuses (parameters := parameters))[position.val]))))

def FlagMaskTableOriginalSupport (rename : Nat → Fin v) (flag : Bool) (count : Nat)
    (table : FlagMaskTable (parameters := parameters) rename flag count) : Prop :=
  BusMaskTableOriginalSupport rename flag table.masks ∧
  ∀ position member, DirectionPairOrigin rename table.masks.checkedPrefix (table.laterFlags position member)



/-- The initial flag cache is empty; the actual first-bus mask trace supplies
its controller prefix. -/
def flagMaskTableInitial (rename : Nat → Fin v) (flag : Bool) :
    FlagMaskTable (parameters := parameters) rename flag 0 :=
  ⟨busMaskTableInitial rename flag, fun position impossible => False.elim (by omega)⟩

theorem flagMaskTableInitial_supported (rename : Nat → Fin v) (flag : Bool) :
    FlagMaskTableOriginalSupport (parameters := parameters) rename flag 0
      (flagMaskTableInitial (parameters := parameters) rename flag) := by
  refine ⟨busMaskTableInitial_supported (parameters := parameters) rename flag, ?_⟩
  intro position impossible
  omega

/-- Advancing a different stored bus preserves the exact allocated flag handle. -/
theorem stagesBefore_old_flag (side querySide : Side)
    (position query : Fin (laterBuses (parameters := parameters)).length)
    (different : (laterBuses (parameters := parameters))[query.val] ≠
      (laterBuses (parameters := parameters))[position.val]) :
    (stagesBefore (parameters := parameters) side (position.val + 1)).slots
        (.internal (.flag querySide (laterBuses (parameters := parameters))[query.val])) =
      (stagesBefore (parameters := parameters) side position.val).slots
        (.internal (.flag querySide (laterBuses (parameters := parameters))[query.val])) := by
  rw [stagesBefore_succ]
  exact laterBus_flag_other side querySide _ _ _ different



/-- The flag cache advances with the existing bus trace. It retains the newly
emitted flag certificate and transports each earlier one through that trace. -/
def flagMaskTableAdvance (rename : Nat → Fin v) (flag : Bool)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (table : FlagMaskTable (parameters := parameters) rename flag position.val) :
    FlagMaskTable (parameters := parameters) rename flag (position.val + 1) := by
  let added := currentBusFromTable rename flag position table.masks
  refine ⟨busTableAdvance rename flag position table.masks, ?_⟩
  intro query member
  by_cases same : query = position
  · subst query
    rw [stagesBefore_current_flag rename .healthy position,
      stagesBefore_current_flag rename .faulty position]
    exact currentBusFlagPair rename flag position table.masks
  · have earlier : query.val < position.val := by
      have unequal : query.val ≠ position.val := fun equality => same (Fin.ext equality)
      omega
    have distinct : (laterBuses (parameters := parameters))[query.val] ≠
        (laterBuses (parameters := parameters))[position.val] := by
      intro equality
      have nodup : (laterBuses (parameters := parameters)).Nodup := by
        exact (List.nodup_finRange parameters.buses).filter _
      have indexEqual : query.val = position.val :=
        (List.Nodup.getElem_inj_iff nodup (hi := query.isLt) (hj := position.isLt)).mp equality
      exact same (Fin.ext indexEqual)
    have carried := (table.laterFlags query earlier).afterTrace added.state added.steps added.checked
    rw [stagesBefore_old_flag .healthy .healthy position query distinct,
      stagesBefore_old_flag .faulty .faulty position query distinct]
    exact carried



/-- A primitive traversal retains every actual emitted later flag alongside
its mask table. The proof-row sequence is the existing bus-prefix sequence. -/
def buildFlagMaskPrefix (rename : Nat → Fin v) (flag : Bool) :
    (count : Nat) → count ≤ (laterBuses (parameters := parameters)).length →
      FlagMaskTable (parameters := parameters) rename flag count
  | 0, _ => flagMaskTableInitial rename flag
  | count + 1, bound =>
      let position : Fin (laterBuses (parameters := parameters)).length := ⟨count, by omega⟩
      flagMaskTableAdvance rename flag position (buildFlagMaskPrefix rename flag count (by omega))

def allFlagMasks (rename : Nat → Fin v) (flag : Bool) :
    FlagMaskTable (parameters := parameters) rename flag (laterBuses (parameters := parameters)).length :=
  buildFlagMaskPrefix rename flag _ (Nat.le_refl _)

theorem buildFlagMaskPrefix_masks (rename : Nat → Fin v) (flag : Bool)
    (count : Nat) (bound : count ≤ (laterBuses (parameters := parameters)).length) :
    (buildFlagMaskPrefix rename flag count bound).masks = buildBusPrefix rename flag count bound := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [buildFlagMaskPrefix, buildBusPrefix, flagMaskTableAdvance]
      rw [ih]

theorem allFlagMasks_masks (rename : Nat → Fin v) (flag : Bool) :
    (allFlagMasks (parameters := parameters) rename flag).masks = allBusMasks rename flag :=
  buildFlagMaskPrefix_masks rename flag _ _



def qualifierNotRows (rename : Nat → Fin v) (side : Side) (bus : Fin parameters.buses)
    (prefixState : SourcePrefix (parameters := parameters) rename) :
    NotRows prefixState.state
      (mapLiteral rename ((negateBefore side bus).slots (.internal (.flag side bus))))
      (mapLiteral rename ((negateBefore side bus).lastID + 1, true)) :=
  (notRowsOriginal ((negateBefore side bus).slots (.internal (.flag side bus)))
    ((negateBefore side bus).lastID + 1, true) (negatedFlagRows rename side bus)).afterTrace
    prefixState.state prefixState.steps prefixState.checked


def firstNotPair (state : State v) (context : Clause (Fin v)) (flag : Bool)
    (leftFlag rightFlag leftOut rightOut : Literal (Fin v))
    (left : NotRows state leftFlag leftOut) (right : NotRows state rightFlag rightOut)
    (leftGuard : (if flag then negate leftFlag else leftFlag) ∈ context)
    (rightGuard : (if flag then negate rightFlag else rightFlag) ∈ context) :
    DirectionPair state context leftOut rightOut := by
  cases flag with
  | false =>
      refine ⟨.derived (retarget right.positive ?_), .derived (retarget left.positive ?_)⟩
      · intro literal member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with equal | equal
        · subst literal; exact List.mem_append_right _ (by simp)
        · subst literal; exact List.mem_append_left _ rightGuard
      · intro literal member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with equal | equal
        · subst literal; exact List.mem_append_right _ (by simp)
        · subst literal; exact List.mem_append_left _ leftGuard
  | true =>
      refine ⟨.derived (retarget left.negative ?_), .derived (retarget right.negative ?_)⟩
      · intro literal member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with equal | equal
        · subst literal; exact List.mem_append_right _ (by simp)
        · subst literal; exact List.mem_append_left _ leftGuard
      · intro literal member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with equal | equal
        · subst literal; exact List.mem_append_right _ (by simp)
        · subst literal; exact List.mem_append_left _ rightGuard


theorem firstNotPair_supported (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (context : Clause (Fin v)) (flag : Bool)
    (leftFlag rightFlag leftOut rightOut : Literal (Fin v))
    (left : NotRows prefixState.state leftFlag leftOut)
    (right : NotRows prefixState.state rightFlag rightOut)
    (leftGuard : (if flag then negate leftFlag else leftFlag) ∈ context)
    (rightGuard : (if flag then negate rightFlag else rightFlag) ∈ context)
    (leftOrigin : NotRowsOriginalSupport rename prefixState left)
    (rightOrigin : NotRowsOriginalSupport rename prefixState right) :
    DirectionPairOrigin rename prefixState
      (firstNotPair prefixState.state context flag leftFlag rightFlag leftOut rightOut
        left right leftGuard rightGuard) := by
  cases flag with
  | false =>
      exact ⟨rightOrigin.1, leftOrigin.1⟩
  | true =>
      exact ⟨leftOrigin.2, rightOrigin.2⟩


theorem negateStep_slots (side : Side) (cursor : Cursor parameters)
    (bus : Fin parameters.buses) (query : Controller.Native.Variable parameters) :
    (negateStep side cursor bus).slots query = cursor.slots query := rfl

theorem negateBefore_flag (side : Side) (bus : Fin parameters.buses)
    (querySide : Side) (queryBus : Fin parameters.buses) :
    (negateBefore side bus).slots (.internal (.flag querySide queryBus)) =
      (tailStages (parameters := parameters) side).slots (.internal (.flag querySide queryBus)) := by
  unfold negateBefore occurrenceCursor
  exact foldl_slot _ _ (fun cursor index => negateStep_slots side cursor index _) _ _

theorem guardBefore_flag (side : Side) (channel : Fin parameters.channels)
    (bus : Fin parameters.buses) (querySide : Side) (queryBus : Fin parameters.buses) :
    (guardBefore side channel bus).slots (.internal (.flag querySide queryBus)) =
      (eligibleBefore side channel).slots (.internal (.flag querySide queryBus)) := by
  unfold guardBefore occurrenceCursor
  exact foldl_slot _ _ (fun cursor index => by
    simp [eligibleGuardStep, Cursor.emitNative, Cursor.emit, Cursor.assign]) _ _


theorem tailStages_eq_completed (side : Side) :
    tailStages (parameters := parameters) side =
      stagesBefore (parameters := parameters) side (laterBuses (parameters := parameters)).length := by
  simp only [tailStages, stagesBefore, List.take_length]

theorem cached_flag_at_negateBefore (side : Side) (bus : Fin parameters.buses)
    (querySide : Side) (query : Fin (laterBuses (parameters := parameters)).length) :
    (negateBefore side bus).slots
      (.internal (.flag querySide (laterBuses (parameters := parameters))[query.val])) =
    (stagesBefore (parameters := parameters) side (laterBuses (parameters := parameters)).length).slots
      (.internal (.flag querySide (laterBuses (parameters := parameters))[query.val])) := by
  rw [negateBefore_flag, tailStages_eq_completed]


theorem flagMaskTableAdvance_supported (rename : Nat → Fin v) (flag : Bool)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (table : FlagMaskTable (parameters := parameters) rename flag position.val)
    (supported : FlagMaskTableOriginalSupport rename flag position.val table) :
    FlagMaskTableOriginalSupport rename flag (position.val + 1)
      (flagMaskTableAdvance rename flag position table) := by
  let added := currentBusFromTable rename flag position table.masks
  let nextPrefix := table.masks.checkedPrefix.extend added.state added.steps added.checked
  constructor
  · exact busTableAdvance_supported rename flag position table.masks supported.1
  · intro query member
    by_cases same : query = position
    · subst query
      have actual := currentBusFlagPair_supported rename flag position table.masks supported.1
      dsimp only [flagMaskTableAdvance]
      rw [dite_eq_left rfl]
      apply directionPairOrigin_mpr rename nextPrefix
        (stagesBefore_current_flag rename .healthy position).symm rfl
      apply directionPairOrigin_mpr rename nextPrefix rfl
        (stagesBefore_current_flag rename .faulty position).symm
      exact actual
    · have earlier : query.val < position.val := by
        have unequal : query.val ≠ position.val := fun equality => same (Fin.ext equality)
        omega
      have distinct : (laterBuses (parameters := parameters))[query.val] ≠
          (laterBuses (parameters := parameters))[position.val] := by
        intro equality
        have nodup : (laterBuses (parameters := parameters)).Nodup :=
          (List.nodup_finRange parameters.buses).filter _
        exact same (Fin.ext ((List.Nodup.getElem_inj_iff nodup
          (hi := query.isLt) (hj := position.isLt)).mp equality))
      have actual := DirectionPairOrigin.afterTrace rename table.masks.checkedPrefix
        (table.laterFlags query earlier) (supported.2 query earlier)
        added.state added.steps added.checked
      dsimp only [flagMaskTableAdvance]
      rw [dite_eq_right same]
      apply directionPairOrigin_mpr rename nextPrefix
        (congrArg (mapLiteral rename) (stagesBefore_old_flag .healthy .healthy position query distinct)).symm rfl
      apply directionPairOrigin_mpr rename nextPrefix rfl
        (congrArg (mapLiteral rename) (stagesBefore_old_flag .faulty .faulty position query distinct)).symm
      exact actual

theorem buildFlagMaskPrefix_supported (rename : Nat → Fin v) (flag : Bool)
    (count : Nat) (bound : count ≤ (laterBuses (parameters := parameters)).length) :
    FlagMaskTableOriginalSupport rename flag count (buildFlagMaskPrefix rename flag count bound) := by
  induction count with
  | zero => exact flagMaskTableInitial_supported rename flag
  | succ count ih =>
      exact flagMaskTableAdvance_supported rename flag ⟨count, by omega⟩
        (buildFlagMaskPrefix rename flag count (by omega)) (ih (by omega))

theorem allFlagMasks_supported (rename : Nat → Fin v) (flag : Bool) :
    FlagMaskTableOriginalSupport (parameters := parameters) rename flag _
      (allFlagMasks (parameters := parameters) rename flag) :=
  buildFlagMaskPrefix_supported rename flag _ _


theorem qualifierNotRows_supported (rename : Nat → Fin v) (side : Side) (bus : Fin parameters.buses)
    (prefixState : SourcePrefix (parameters := parameters) rename) :
    NotRowsOriginalSupport rename prefixState (qualifierNotRows rename side bus prefixState) := by
  constructor
  · apply Or.inl
    exact negatedFlagRows_allowed rename side bus ⟨0, by decide⟩
  · apply Or.inl
    exact negatedFlagRows_allowed rename side bus ⟨1, by decide⟩

/-- A cached later flag is retyped to the actual input of its stored private NOT. -/
def laterNotInputPair (rename : Nat → Fin v) (flag : Bool)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (table : FlagMaskTable (parameters := parameters) rename flag (laterBuses (parameters := parameters)).length) :
    DirectionPair table.masks.checkedPrefix.state (equalFlagContext (parameters := parameters) rename flag)
      (mapLiteral rename ((negateBefore .healthy (laterBuses (parameters := parameters))[position.val]).slots
        (.internal (.flag .healthy (laterBuses (parameters := parameters))[position.val]))))
      (mapLiteral rename ((negateBefore .faulty (laterBuses (parameters := parameters))[position.val]).slots
        (.internal (.flag .faulty (laterBuses (parameters := parameters))[position.val])))) := by
  rw [cached_flag_at_negateBefore .healthy _ .healthy position,
    cached_flag_at_negateBefore .faulty _ .faulty position]
  exact table.laterFlags position position.isLt

theorem laterNotInputPair_supported (rename : Nat → Fin v) (flag : Bool)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (table : FlagMaskTable (parameters := parameters) rename flag (laterBuses (parameters := parameters)).length)
    (supported : FlagMaskTableOriginalSupport rename flag _ table) :
    DirectionPairOrigin rename table.masks.checkedPrefix (laterNotInputPair rename flag position table) := by
  dsimp only [laterNotInputPair]
  apply directionPairOrigin_mpr rename table.masks.checkedPrefix
    (congrArg (mapLiteral rename) (cached_flag_at_negateBefore .healthy _ .healthy position)).symm rfl
  apply directionPairOrigin_mpr rename table.masks.checkedPrefix rfl
    (congrArg (mapLiteral rename) (cached_flag_at_negateBefore .faulty _ .faulty position)).symm
  exact supported.2 position position.isLt

/-- A two-direction NOT macro consumes carried certificates and original rows. -/
def pairedPrivateNot (state : State v) (context : Clause (Fin v))
    (leftInput rightInput leftOut rightOut : Literal (Fin v))
    (left : NotRows state leftInput leftOut) (right : NotRows state rightInput rightOut)
    (inputs : DirectionPair state context leftInput rightInput) :
    PairedProjection state context leftOut rightOut 4 := by
  let first := guardedNot state context leftInput rightInput leftOut rightOut left right inputs.backward
  let nextLeft := left.afterTrace first.state first.steps first.checked
  let nextRight := right.afterTrace first.state first.steps first.checked
  let second := guardedNot first.state context rightInput leftInput rightOut leftOut nextRight nextLeft
    (inputs.forward.afterTrace first.state first.steps first.checked)
  refine ⟨second.state, first.steps ++ second.steps, ?_,
    ⟨.derived (FoldProjection.afterTrace first.result second.state second.steps second.checked),
      .derived second.result⟩, ?_⟩
  · rw [runSteps_append, first.checked]
    exact second.checked
  · have one := first.count
    have two := second.count
    simp only [List.length_append]
    omega

theorem pairedPrivateNot_supported (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename) (context : Clause (Fin v))
    (leftInput rightInput leftOut rightOut : Literal (Fin v))
    (left : NotRows prefixState.state leftInput leftOut) (right : NotRows prefixState.state rightInput rightOut)
    (inputs : DirectionPair prefixState.state context leftInput rightInput)
    (prefixOriginal : SourceMixedSchedule.PrefixOriginalSupport rename prefixState)
    (leftOriginal : NotRowsOriginalSupport rename prefixState left)
    (rightOriginal : NotRowsOriginalSupport rename prefixState right)
    (inputsOriginal : DirectionPairOrigin rename prefixState inputs) :
    PairedProjectionOriginalSupport rename prefixState
      (pairedPrivateNot prefixState.state context leftInput rightInput leftOut rightOut left right inputs) := by
  let first := guardedNot prefixState.state context leftInput rightInput leftOut rightOut left right inputs.backward
  have firstSupport := guardedNot_supported rename prefixState context leftInput rightInput leftOut rightOut
    left right inputs.backward prefixOriginal leftOriginal rightOriginal inputsOriginal.2
  let current := prefixState.extend first.state first.steps first.checked
  let nextLeft := left.afterTrace first.state first.steps first.checked
  let nextRight := right.afterTrace first.state first.steps first.checked
  let second := guardedNot first.state context rightInput leftInput rightOut leftOut nextRight nextLeft
    (inputs.forward.afterTrace first.state first.steps first.checked)
  have secondSupport := guardedNot_supported rename current context rightInput leftInput rightOut leftOut
    nextRight nextLeft (inputs.forward.afterTrace first.state first.steps first.checked) firstSupport.1
    (NotRowsOriginalSupport.afterTrace rename prefixState right first.state first.steps first.checked rightOriginal)
    (NotRowsOriginalSupport.afterTrace rename prefixState left first.state first.steps first.checked leftOriginal)
    (GuardedTransferOrigin.afterTrace rename prefixState inputs.forward inputsOriginal.1
      first.state first.steps first.checked)
  have forward := resultOrigin_append_right (formula parameters).clauses.size
    (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
    (prefixState.steps ++ first.steps) second.steps first.result.row.id firstSupport.2
  simpa only [PairedProjectionOriginalSupport, SourceMixedSchedule.PrefixOriginalSupport, pairedPrivateNot,
    first, current, nextLeft, nextRight, second, DirectionPairOrigin, GuardedTransferOrigin,
    SourcePrefix.extend, List.append_assoc, FoldProjection.afterTrace] using
      And.intro secondSupport.1 (And.intro forward secondSupport.2)



theorem tailStages_first_flag_frame (side querySide : Side) :
    (tailStages (parameters := parameters) side).slots (.internal (.flag querySide parameters.firstBus)) =
      (tailStart (parameters := parameters) side).slots (.internal (.flag querySide parameters.firstBus)) := by
  have actual := SourceRoleFrames.tail_first_flag (parameters := parameters) side querySide (tailStart side)
  unfold SourceController.tail at actual
  rw [foldl_slot _ (.internal (.flag querySide parameters.firstBus))
    (fun current channel => SourceRoleFrames.eligible_first_flag side querySide channel current),
    SourceSlotFrames.negateFlags_slot] at actual
  exact actual

theorem firstNotInput_eq_sourceFlag (rename : Nat → Fin v) (side : Side) :
    mapLiteral rename ((negateBefore side parameters.firstBus).slots
      (.internal (.flag side parameters.firstBus))) =
      mapLiteral rename (sourceRoleMap parameters (.internal (.flag side parameters.firstBus))) := by
  rw [negateBefore_flag, tailStages_first_flag_frame]
  unfold sourceRoleMap
  rw [SourceRoleFrames.compiled_first_flag]
  cases side with
  | healthy => rfl
  | faulty =>
      exact congrArg (mapLiteral rename)
        (SourceRoleFrames.tail_first_flag .healthy .faulty (interface parameters))

/-- The first private NOT pair reuses actual original rows under the two
first-flag guards and emits no proof rows. -/
def firstNotFromSource (rename : Nat → Fin v) (flag : Bool)
    (prefixState : SourcePrefix (parameters := parameters) rename) :
    DirectionPair prefixState.state (equalFlagContext (parameters := parameters) rename flag)
      (mapLiteral rename ((negateBefore .healthy parameters.firstBus).lastID + 1, true))
      (mapLiteral rename ((negateBefore .faulty parameters.firstBus).lastID + 1, true)) := by
  let left := qualifierNotRows rename .healthy parameters.firstBus prefixState
  let right := qualifierNotRows rename .faulty parameters.firstBus prefixState
  exact firstNotPair prefixState.state (equalFlagContext (parameters := parameters) rename flag) flag _ _ _ _
    left right
    (by rw [firstNotInput_eq_sourceFlag]; cases flag <;> simp [equalFlagContext, assignmentGuard])
    (by rw [firstNotInput_eq_sourceFlag]; cases flag <;> simp [equalFlagContext, assignmentGuard])

theorem firstNotFromSource_supported (rename : Nat → Fin v) (flag : Bool)
    (prefixState : SourcePrefix (parameters := parameters) rename) :
    DirectionPairOrigin rename prefixState (firstNotFromSource rename flag prefixState) := by
  exact firstNotPair_supported rename prefixState (equalFlagContext (parameters := parameters) rename flag)
    flag _ _ _ _ _ _ _ _
    (qualifierNotRows_supported rename .healthy parameters.firstBus prefixState)
    (qualifierNotRows_supported rename .faulty parameters.firstBus prefixState)



def laterPrivateNotFromCache (rename : Nat → Fin v) (flag : Bool)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (table : FlagMaskTable (parameters := parameters) rename flag (laterBuses (parameters := parameters)).length) :
    PairedProjection table.masks.checkedPrefix.state (equalFlagContext (parameters := parameters) rename flag)
      (mapLiteral rename ((negateBefore .healthy (laterBuses (parameters := parameters))[position.val]).lastID + 1, true))
      (mapLiteral rename ((negateBefore .faulty (laterBuses (parameters := parameters))[position.val]).lastID + 1, true)) 4 :=
  pairedPrivateNot table.masks.checkedPrefix.state (equalFlagContext (parameters := parameters) rename flag)
    (mapLiteral rename ((negateBefore .healthy (laterBuses (parameters := parameters))[position.val]).slots
      (.internal (.flag .healthy (laterBuses (parameters := parameters))[position.val]))))
    (mapLiteral rename ((negateBefore .faulty (laterBuses (parameters := parameters))[position.val]).slots
      (.internal (.flag .faulty (laterBuses (parameters := parameters))[position.val]))))
    (mapLiteral rename ((negateBefore .healthy (laterBuses (parameters := parameters))[position.val]).lastID + 1, true))
    (mapLiteral rename ((negateBefore .faulty (laterBuses (parameters := parameters))[position.val]).lastID + 1, true))
    (qualifierNotRows rename .healthy (laterBuses (parameters := parameters))[position.val] table.masks.checkedPrefix)
    (qualifierNotRows rename .faulty (laterBuses (parameters := parameters))[position.val] table.masks.checkedPrefix)
    (laterNotInputPair rename flag position table)

theorem laterPrivateNotFromCache_supported (rename : Nat → Fin v) (flag : Bool)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (table : FlagMaskTable (parameters := parameters) rename flag (laterBuses (parameters := parameters)).length)
    (supported : FlagMaskTableOriginalSupport rename flag _ table) :
    PairedProjectionOriginalSupport rename table.masks.checkedPrefix
      (laterPrivateNotFromCache rename flag position table) := by
  let bus := (laterBuses (parameters := parameters))[position.val]
  let leftInput := mapLiteral rename ((negateBefore .healthy bus).slots (.internal (.flag .healthy bus)))
  let rightInput := mapLiteral rename ((negateBefore .faulty bus).slots (.internal (.flag .faulty bus)))
  let leftOut := mapLiteral rename ((negateBefore .healthy bus).lastID + 1, true)
  let rightOut := mapLiteral rename ((negateBefore .faulty bus).lastID + 1, true)
  let left := qualifierNotRows rename .healthy bus table.masks.checkedPrefix
  let right := qualifierNotRows rename .faulty bus table.masks.checkedPrefix
  let inputs := laterNotInputPair rename flag position table
  have actual : PairedProjectionOriginalSupport rename table.masks.checkedPrefix
      (pairedPrivateNot table.masks.checkedPrefix.state (equalFlagContext (parameters := parameters) rename flag)
        leftInput rightInput leftOut rightOut left right inputs) :=
    pairedPrivateNot_supported rename table.masks.checkedPrefix (equalFlagContext (parameters := parameters) rename flag)
      leftInput rightInput leftOut rightOut left right inputs supported.1.1
      (qualifierNotRows_supported rename .healthy bus table.masks.checkedPrefix)
      (qualifierNotRows_supported rename .faulty bus table.masks.checkedPrefix)
      (laterNotInputPair_supported rename flag position table supported)
  dsimp only [laterPrivateNotFromCache]
  exact actual


/-- The completed cache is carried across actual accepted proof continuations. -/
def FlagMaskTable.afterTrace {count : Nat}
    (table : FlagMaskTable (parameters := parameters) rename flag count)
    (next : State v) (steps : List (Step v)) (checked : runSteps table.masks.checkedPrefix.state steps = some next) :
    FlagMaskTable (parameters := parameters) rename flag count :=
  ⟨⟨table.masks.checkedPrefix.extend next steps checked,
      fun bus member channel => (table.masks.directions bus member channel).afterTrace next steps checked⟩,
    fun position member => (table.laterFlags position member).afterTrace next steps checked⟩

/-- Every stored private-NOT output is the actual input handle of its guard OR. -/
theorem privateNot_to_guard_input (side : Side) (channel : Fin parameters.channels)
    (bus : Fin parameters.buses) :
    (guardBefore side channel bus).negated side bus =
      ((negateBefore side bus).lastID + 1, true) :=
  SourceSuffixSelector.guardBefore_negated side channel bus

structure PrivateNotBank (rename : Nat → Fin v) (flag : Bool) (count : Nat) where
  cache : FlagMaskTable (parameters := parameters) rename flag (laterBuses (parameters := parameters)).length
  pairs : ∀ bus ∈ parameters.firstBus :: (laterBuses (parameters := parameters)).take count,
    DirectionPair cache.masks.checkedPrefix.state (equalFlagContext (parameters := parameters) rename flag)
      (mapLiteral rename (SourceSuffixSelector.negatedHandle .healthy bus))
      (mapLiteral rename (SourceSuffixSelector.negatedHandle .faulty bus))

def privateNotBankInitial (rename : Nat → Fin v) (flag : Bool)
    (cache : FlagMaskTable (parameters := parameters) rename flag (laterBuses (parameters := parameters)).length) :
    PrivateNotBank (parameters := parameters) rename flag 0 := by
  refine ⟨cache, ?_⟩
  intro bus member
  have same : bus = parameters.firstBus := by simpa only [List.take_zero, List.mem_cons,
    List.not_mem_nil, or_false] using member
  subst bus
  exact firstNotFromSource rename flag cache.masks.checkedPrefix

def privateNotBankAdvance (rename : Nat → Fin v) (flag : Bool)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (bank : PrivateNotBank (parameters := parameters) rename flag position.val) :
    PrivateNotBank (parameters := parameters) rename flag (position.val + 1) := by
  let added := laterPrivateNotFromCache rename flag position bank.cache
  let nextCache := bank.cache.afterTrace added.state added.steps added.checked
  refine ⟨nextCache, ?_⟩
  intro bus member
  by_cases same : bus = (laterBuses (parameters := parameters))[position.val]
  · subst bus
    exact added.pair
  · have previous : bus ∈ parameters.firstBus :: (laterBuses (parameters := parameters)).take position.val := by
      rw [List.take_succ_eq_append_getElem position.isLt] at member
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at member ⊢
      rcases member with first | old | current
      · exact Or.inl first
      · exact Or.inr old
      · exact False.elim (same current)
    exact (bank.pairs bus previous).afterTrace added.state added.steps added.checked

theorem FlagMaskTable.afterTrace_supported (rename : Nat → Fin v) (flag : Bool) {count : Nat}
    (table : FlagMaskTable (parameters := parameters) rename flag count)
    (supported : FlagMaskTableOriginalSupport rename flag count table)
    (next : State v) (steps : List (Step v)) (checked : runSteps table.masks.checkedPrefix.state steps = some next)
    (nextOriginal : SourceMixedSchedule.PrefixOriginalSupport rename
      (table.masks.checkedPrefix.extend next steps checked)) :
    FlagMaskTableOriginalSupport rename flag count (table.afterTrace next steps checked) := by
  refine ⟨⟨nextOriginal, ?_⟩, ?_⟩
  · intro bus member channel
    exact DirectionPairOrigin.afterTrace rename table.masks.checkedPrefix
      (table.masks.directions bus member channel) (supported.1.2 bus member channel) next steps checked
  · intro position member
    exact DirectionPairOrigin.afterTrace rename table.masks.checkedPrefix
      (table.laterFlags position member) (supported.2 position member) next steps checked

def PrivateNotBankOriginalSupport (rename : Nat → Fin v) (flag : Bool) {count : Nat}
    (bank : PrivateNotBank (parameters := parameters) rename flag count) : Prop :=
  FlagMaskTableOriginalSupport rename flag (laterBuses (parameters := parameters)).length bank.cache ∧
    ∀ bus member, DirectionPairOrigin rename bank.cache.masks.checkedPrefix (bank.pairs bus member)

theorem privateNotBankInitial_supported (rename : Nat → Fin v) (flag : Bool)
    (cache : FlagMaskTable (parameters := parameters) rename flag (laterBuses (parameters := parameters)).length)
    (supported : FlagMaskTableOriginalSupport rename flag (laterBuses (parameters := parameters)).length cache) :
    PrivateNotBankOriginalSupport rename flag (privateNotBankInitial rename flag cache) := by
  refine ⟨supported, ?_⟩
  intro bus member
  have same : bus = parameters.firstBus := by simpa only [List.take_zero, List.mem_cons,
    List.not_mem_nil, or_false] using member
  subst bus
  exact firstNotFromSource_supported rename flag cache.masks.checkedPrefix

def buildPrivateNotBank (rename : Nat → Fin v) (flag : Bool)
    (cache : FlagMaskTable (parameters := parameters) rename flag (laterBuses (parameters := parameters)).length)
    (count : Nat) (bounded : count ≤ (laterBuses (parameters := parameters)).length) :
    PrivateNotBank (parameters := parameters) rename flag count :=
  match count with
  | 0 => privateNotBankInitial rename flag cache
  | count + 1 => privateNotBankAdvance rename flag ⟨count, by omega⟩
      (buildPrivateNotBank rename flag cache count (by omega))

def allPrivateNotPairs (rename : Nat → Fin v) (flag : Bool) :
    PrivateNotBank (parameters := parameters) rename flag (laterBuses (parameters := parameters)).length :=
  buildPrivateNotBank rename flag (allFlagMasks rename flag) _ (Nat.le_refl _)

theorem privateNotBankAdvance_supported (rename : Nat → Fin v) (flag : Bool)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (bank : PrivateNotBank (parameters := parameters) rename flag position.val)
    (supported : PrivateNotBankOriginalSupport rename flag bank) :
    PrivateNotBankOriginalSupport rename flag (privateNotBankAdvance rename flag position bank) := by
  let added := laterPrivateNotFromCache rename flag position bank.cache
  have addedOriginal := laterPrivateNotFromCache_supported rename flag position bank.cache supported.1
  refine ⟨FlagMaskTable.afterTrace_supported rename flag bank.cache supported.1
    added.state added.steps added.checked addedOriginal.1, ?_⟩
  intro bus member
  by_cases same : bus = (laterBuses (parameters := parameters))[position.val]
  · subst bus
    dsimp only [privateNotBankAdvance, FlagMaskTable.afterTrace, SourcePrefix.extend,
      SourceSuffixSelector.negatedHandle]
    rw [dite_eq_left rfl]
    exact addedOriginal.2
  · have previous : bus ∈ parameters.firstBus :: (laterBuses (parameters := parameters)).take position.val := by
      rw [List.take_succ_eq_append_getElem position.isLt] at member
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at member ⊢
      rcases member with first | old | current
      · exact Or.inl first
      · exact Or.inr old
      · exact False.elim (same current)
    have original := DirectionPairOrigin.afterTrace rename bank.cache.masks.checkedPrefix
      (bank.pairs bus previous) (supported.2 bus previous) added.state added.steps added.checked
    dsimp only [privateNotBankAdvance, FlagMaskTable.afterTrace, SourcePrefix.extend]
    rw [dite_eq_right same]
    exact original

theorem buildPrivateNotBank_supported (rename : Nat → Fin v) (flag : Bool)
    (cache : FlagMaskTable (parameters := parameters) rename flag (laterBuses (parameters := parameters)).length)
    (supported : FlagMaskTableOriginalSupport rename flag _ cache)
    (count : Nat) (bounded : count ≤ (laterBuses (parameters := parameters)).length) :
    PrivateNotBankOriginalSupport rename flag (buildPrivateNotBank rename flag cache count bounded) := by
  induction count with
  | zero => exact privateNotBankInitial_supported rename flag cache supported
  | succ count ih =>
      exact privateNotBankAdvance_supported rename flag ⟨count, by omega⟩
        (buildPrivateNotBank rename flag cache count (by omega)) (ih (by omega))

theorem allPrivateNotPairs_supported (rename : Nat → Fin v) (flag : Bool) :
    PrivateNotBankOriginalSupport (parameters := parameters) rename flag
      (count := (laterBuses (parameters := parameters)).length)
      (allPrivateNotPairs (parameters := parameters) rename flag) :=
  buildPrivateNotBank_supported rename flag (allFlagMasks (parameters := parameters) rename flag)
    (allFlagMasks_supported (parameters := parameters) rename flag) _ (Nat.le_refl _)

def guardOrTreeOriginal (rename : Nat → Fin v) (side : Side)
    (channel : Fin parameters.channels) (bus : Fin parameters.buses) :
    AndTree (initialState (relabel rename (formula parameters)))
      (dualLiteral rename (SourceSuffixSelector.guardHandle side channel bus))
      [dualLiteral rename ((guardBefore side channel bus).negated side bus),
       dualLiteral rename ((guardBefore side channel bus).slots (.primary (.request bus channel)))] :=
  .node (.leaf _) (.leaf _) _
    (binaryOrRows ((guardBefore side channel bus).negated side bus)
      ((guardBefore side channel bus).slots (.primary (.request bus channel)))
      (SourceSuffixSelector.guardHandle side channel bus) (guardRows rename side channel bus))

theorem guardOrTreeOriginal_supported (rename : Nat → Fin v) (side : Side)
    (channel : Fin parameters.channels) (bus : Fin parameters.buses) :
    TreeOriginals (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      (guardOrTreeOriginal rename side channel bus) := by
  refine ⟨trivial, trivial, ?_⟩
  apply Controller.NativeProof.SourceFoldAggregateProvenance.binaryOrRows_originals
  intro index
  exact guardRows_allowed rename side channel bus ⟨index.val, by change index.val < 3; exact index.isLt⟩

def guardOrTree (rename : Nat → Fin v) (side : Side)
    (channel : Fin parameters.channels) (bus : Fin parameters.buses)
    (prefixState : SourcePrefix (parameters := parameters) rename) :=
  (guardOrTreeOriginal rename side channel bus).afterTrace
    prefixState.state prefixState.steps prefixState.checked

theorem allPrivateNotBank_mem (bus : Fin parameters.buses) :
    bus ∈ parameters.firstBus :: (laterBuses (parameters := parameters)).take (laterBuses (parameters := parameters)).length := by
  rw [List.take_length]
  by_cases first : bus = parameters.firstBus
  · exact List.mem_cons.mpr (Or.inl first)
  · apply List.mem_cons_of_mem
    simp only [laterBuses, List.mem_filter, List.mem_finRange, true_and]
    have nonzero : bus.val ≠ 0 := by
      intro zero
      apply first
      apply Fin.ext
      exact zero
    simpa using nonzero

def guardNotInputPair (rename : Nat → Fin v) (flag : Bool)
    (channel : Fin parameters.channels) (bus : Fin parameters.buses)
    (bank : PrivateNotBank (parameters := parameters) rename flag (laterBuses (parameters := parameters)).length) :
    DirectionPair bank.cache.masks.checkedPrefix.state (equalFlagContext (parameters := parameters) rename flag)
      (mapLiteral rename ((guardBefore .healthy channel bus).negated .healthy bus))
      (mapLiteral rename ((guardBefore .faulty channel bus).negated .faulty bus)) := by
  have typeEqual : DirectionPair bank.cache.masks.checkedPrefix.state (equalFlagContext (parameters := parameters) rename flag)
      (mapLiteral rename ((guardBefore .healthy channel bus).negated .healthy bus))
      (mapLiteral rename ((guardBefore .faulty channel bus).negated .faulty bus)) =
      DirectionPair bank.cache.masks.checkedPrefix.state (equalFlagContext (parameters := parameters) rename flag)
        (mapLiteral rename (SourceSuffixSelector.negatedHandle .healthy bus))
        (mapLiteral rename (SourceSuffixSelector.negatedHandle .faulty bus)) := by
    rw [SourceSuffixSelector.guardBefore_negated, SourceSuffixSelector.guardBefore_negated]
  exact Eq.mpr typeEqual (bank.pairs bus (allPrivateNotBank_mem (parameters := parameters) bus))

def guardRequestPair (rename : Nat → Fin v) (context : Clause (Fin v))
    (channel : Fin parameters.channels) (bus : Fin parameters.buses) (state : State v) :
    DirectionPair state context
      (mapLiteral rename ((guardBefore .healthy channel bus).slots (.primary (.request bus channel))))
      (mapLiteral rename ((guardBefore .faulty channel bus).slots (.primary (.request bus channel)))) := by
  have same := congrArg (mapLiteral rename)
    (((SourceSuffixSelector.guardBefore_roots .healthy channel bus).2 bus channel).trans
      ((SourceSuffixSelector.guardBefore_roots .faulty channel bus).2 bus channel).symm)
  exact ⟨.identity same, .identity same.symm⟩

def chooseTwoGuardPairs (state : State v) (context : Clause (Fin v))
    (first second : Literal (Fin v) × Literal (Fin v))
    (firstPair : DirectionPair state context first.1 first.2)
    (secondPair : DirectionPair state context second.1 second.2)
    (pair : Literal (Fin v) × Literal (Fin v)) (member : pair ∈ [first, second]) :
    DirectionPair state context pair.1 pair.2 := by
  by_cases same : pair = first
  · subst pair
    exact firstPair
  · have last : pair = second := by
      simpa only [List.mem_cons, List.not_mem_nil, or_false, same, false_or] using member
    subst pair
    exact secondPair

def privateGuardPairs (rename : Nat → Fin v) (channel : Fin parameters.channels)
    (bus : Fin parameters.buses) : List (Literal (Fin v) × Literal (Fin v)) :=
  [(mapLiteral rename ((guardBefore .healthy channel bus).negated .healthy bus),
    mapLiteral rename ((guardBefore .faulty channel bus).negated .faulty bus)),
   (mapLiteral rename ((guardBefore .healthy channel bus).slots (.primary (.request bus channel))),
    mapLiteral rename ((guardBefore .faulty channel bus).slots (.primary (.request bus channel))))]

def privateGuardOr (rename : Nat → Fin v) (flag : Bool)
    (channel : Fin parameters.channels) (bus : Fin parameters.buses)
    (bank : PrivateNotBank (parameters := parameters) rename flag (laterBuses (parameters := parameters)).length) :
    PairedProjection bank.cache.masks.checkedPrefix.state (equalFlagContext (parameters := parameters) rename flag)
      (mapLiteral rename (SourceSuffixSelector.guardHandle .healthy channel bus))
      (mapLiteral rename (SourceSuffixSelector.guardHandle .faulty channel bus)) 24 := by
  let prefixState := bank.cache.masks.checkedPrefix
  let context := equalFlagContext (parameters := parameters) rename flag
  let first : Literal (Fin v) × Literal (Fin v) :=
    (mapLiteral rename ((guardBefore .healthy channel bus).negated .healthy bus),
     mapLiteral rename ((guardBefore .faulty channel bus).negated .faulty bus))
  let second : Literal (Fin v) × Literal (Fin v) :=
    (mapLiteral rename ((guardBefore .healthy channel bus).slots (.primary (.request bus channel))),
     mapLiteral rename ((guardBefore .faulty channel bus).slots (.primary (.request bus channel))))
  let leftOut := mapLiteral rename (SourceSuffixSelector.guardHandle .healthy channel bus)
  let rightOut := mapLiteral rename (SourceSuffixSelector.guardHandle .faulty channel bus)
  let leftTree : AndTree prefixState.state (negate leftOut) [negate first.1, negate second.1] := by
    exact guardOrTree rename .healthy channel bus prefixState
  let rightTree : AndTree prefixState.state (negate rightOut) [negate first.2, negate second.2] := by
    exact guardOrTree rename .faulty channel bus prefixState
  exact pairedOr prefixState.state context leftOut rightOut [first, second] (by simp)
    leftTree rightTree
    (fun pair member => chooseTwoGuardPairs prefixState.state context first second
      (guardNotInputPair rename flag channel bus bank)
      (guardRequestPair rename context channel bus prefixState.state) pair member)

theorem guardOrTree_supported (rename : Nat → Fin v) (side : Side)
    (channel : Fin parameters.channels) (bus : Fin parameters.buses)
    (prefixState : SourcePrefix (parameters := parameters) rename) :
    TreeOriginals (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      (guardOrTree rename side channel bus prefixState) :=
  treeOriginals_afterTrace _ (guardOrTreeOriginal rename side channel bus)
    (guardOrTreeOriginal_supported rename side channel bus) prefixState.state prefixState.steps prefixState.checked

theorem guardNotInputPair_supported (rename : Nat → Fin v) (flag : Bool)
    (channel : Fin parameters.channels) (bus : Fin parameters.buses)
    (bank : PrivateNotBank (parameters := parameters) rename flag (laterBuses (parameters := parameters)).length)
    (supported : PrivateNotBankOriginalSupport rename flag bank) :
    DirectionPairOrigin rename bank.cache.masks.checkedPrefix (guardNotInputPair rename flag channel bus bank) := by
  have typeEqual : DirectionPair bank.cache.masks.checkedPrefix.state (equalFlagContext (parameters := parameters) rename flag)
      (mapLiteral rename ((guardBefore .healthy channel bus).negated .healthy bus))
      (mapLiteral rename ((guardBefore .faulty channel bus).negated .faulty bus)) =
      DirectionPair bank.cache.masks.checkedPrefix.state (equalFlagContext (parameters := parameters) rename flag)
        (mapLiteral rename (SourceSuffixSelector.negatedHandle .healthy bus))
        (mapLiteral rename (SourceSuffixSelector.negatedHandle .faulty bus)) := by
    rw [SourceSuffixSelector.guardBefore_negated, SourceSuffixSelector.guardBefore_negated]
  exact directionPairOrigin_mpr rename bank.cache.masks.checkedPrefix
    (congrArg (mapLiteral rename) (SourceSuffixSelector.guardBefore_negated .healthy channel bus)).symm
    (congrArg (mapLiteral rename) (SourceSuffixSelector.guardBefore_negated .faulty channel bus)).symm
    typeEqual (bank.pairs bus (allPrivateNotBank_mem (parameters := parameters) bus)) (supported.2 bus (allPrivateNotBank_mem (parameters := parameters) bus))

theorem guardRequestPair_supported (rename : Nat → Fin v) (context : Clause (Fin v))
    (channel : Fin parameters.channels) (bus : Fin parameters.buses)
    (prefixState : SourcePrefix (parameters := parameters) rename) :
    DirectionPairOrigin rename prefixState (guardRequestPair rename context channel bus prefixState.state) := by
  exact ⟨trivial, trivial⟩

theorem chooseTwoGuardPairs_supported (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (context : Clause (Fin v)) (first second : Literal (Fin v) × Literal (Fin v))
    (firstPair : DirectionPair prefixState.state context first.1 first.2)
    (secondPair : DirectionPair prefixState.state context second.1 second.2)
    (firstOrigin : DirectionPairOrigin rename prefixState firstPair)
    (secondOrigin : DirectionPairOrigin rename prefixState secondPair)
    (pair : Literal (Fin v) × Literal (Fin v)) (member : pair ∈ [first, second]) :
    DirectionPairOrigin rename prefixState
      (chooseTwoGuardPairs prefixState.state context first second firstPair secondPair pair member) := by
  by_cases same : pair = first
  · subst pair
    dsimp only [chooseTwoGuardPairs]
    rw [dite_eq_left rfl]
    exact firstOrigin
  · have last : pair = second := by
      simpa only [List.mem_cons, List.not_mem_nil, or_false, same, false_or] using member
    subst pair
    dsimp only [chooseTwoGuardPairs]
    rw [dite_eq_right same]
    exact secondOrigin

theorem privateGuardOr_supported (rename : Nat → Fin v) (flag : Bool)
    (channel : Fin parameters.channels) (bus : Fin parameters.buses)
    (bank : PrivateNotBank (parameters := parameters) rename flag (laterBuses (parameters := parameters)).length)
    (supported : PrivateNotBankOriginalSupport rename flag bank) :
    PairedProjectionOriginalSupport rename bank.cache.masks.checkedPrefix (privateGuardOr rename flag channel bus bank) := by
  let prefixState := bank.cache.masks.checkedPrefix
  let context := equalFlagContext (parameters := parameters) rename flag
  let first : Literal (Fin v) × Literal (Fin v) :=
    (mapLiteral rename ((guardBefore .healthy channel bus).negated .healthy bus),
     mapLiteral rename ((guardBefore .faulty channel bus).negated .faulty bus))
  let second : Literal (Fin v) × Literal (Fin v) :=
    (mapLiteral rename ((guardBefore .healthy channel bus).slots (.primary (.request bus channel))),
     mapLiteral rename ((guardBefore .faulty channel bus).slots (.primary (.request bus channel))))
  let leftOut := mapLiteral rename (SourceSuffixSelector.guardHandle .healthy channel bus)
  let rightOut := mapLiteral rename (SourceSuffixSelector.guardHandle .faulty channel bus)
  let leftTree : AndTree prefixState.state (negate leftOut) [negate first.1, negate second.1] :=
    guardOrTree rename .healthy channel bus prefixState
  let rightTree : AndTree prefixState.state (negate rightOut) [negate first.2, negate second.2] :=
    guardOrTree rename .faulty channel bus prefixState
  let firstPair := guardNotInputPair rename flag channel bus bank
  let secondPair := guardRequestPair rename context channel bus prefixState.state
  have leftOriginal : TreeOriginals (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename) leftTree :=
    guardOrTree_supported rename .healthy channel bus prefixState
  have rightOriginal : TreeOriginals (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename) rightTree :=
    guardOrTree_supported rename .faulty channel bus prefixState
  have actual : PairedProjectionOriginalSupport rename prefixState
      (pairedOr prefixState.state context leftOut rightOut [first, second] (by simp) leftTree rightTree
        (fun pair member => chooseTwoGuardPairs prefixState.state context first second firstPair secondPair pair member)) :=
    pairedOr_supported rename prefixState context leftOut rightOut [first, second] (by simp) leftTree rightTree
      (fun pair member => chooseTwoGuardPairs prefixState.state context first second firstPair secondPair pair member)
      leftOriginal rightOriginal supported.1.1.1
      (fun pair member => chooseTwoGuardPairs_supported rename prefixState context first second firstPair secondPair
        (guardNotInputPair_supported rename flag channel bus bank supported)
        (guardRequestPair_supported rename context channel bus prefixState) pair member)
  dsimp only [privateGuardOr]
  exact actual

def PrivateNotBank.afterTrace {count : Nat}
    (bank : PrivateNotBank (parameters := parameters) rename flag count)
    (next : State v) (steps : List (Step v)) (checked : runSteps bank.cache.masks.checkedPrefix.state steps = some next) :
    PrivateNotBank (parameters := parameters) rename flag count :=
  ⟨bank.cache.afterTrace next steps checked,
    fun bus member => (bank.pairs bus member).afterTrace next steps checked⟩

theorem PrivateNotBank.afterTrace_supported (rename : Nat → Fin v) (flag : Bool) {count : Nat}
    (bank : PrivateNotBank (parameters := parameters) rename flag count)
    (supported : PrivateNotBankOriginalSupport rename flag bank)
    (next : State v) (steps : List (Step v)) (checked : runSteps bank.cache.masks.checkedPrefix.state steps = some next)
    (nextOriginal : SourceMixedSchedule.PrefixOriginalSupport rename
      (bank.cache.masks.checkedPrefix.extend next steps checked)) :
    PrivateNotBankOriginalSupport rename flag (bank.afterTrace next steps checked) := by
  refine ⟨FlagMaskTable.afterTrace_supported rename flag bank.cache supported.1 next steps checked nextOriginal, ?_⟩
  intro bus member
  exact DirectionPairOrigin.afterTrace rename bank.cache.masks.checkedPrefix
    (bank.pairs bus member) (supported.2 bus member) next steps checked

structure PrivateGuardBank (rename : Nat → Fin v) (flag : Bool)
    (channel : Fin parameters.channels) (count : Nat) where
  nots : PrivateNotBank (parameters := parameters) rename flag (laterBuses (parameters := parameters)).length
  pairs : ∀ bus : Fin parameters.buses, bus.val < count →
    DirectionPair nots.cache.masks.checkedPrefix.state (equalFlagContext (parameters := parameters) rename flag)
      (mapLiteral rename (SourceSuffixSelector.guardHandle .healthy channel bus))
      (mapLiteral rename (SourceSuffixSelector.guardHandle .faulty channel bus))

def privateGuardBankInitial (rename : Nat → Fin v) (flag : Bool) (channel : Fin parameters.channels)
    (nots : PrivateNotBank (parameters := parameters) rename flag (laterBuses (parameters := parameters)).length) :
    PrivateGuardBank (parameters := parameters) rename flag channel 0 :=
  ⟨nots, fun bus before => False.elim (Nat.not_lt_zero bus.val before)⟩

def privateGuardBankAppend (rename : Nat → Fin v) (flag : Bool) (channel : Fin parameters.channels)
    (position : Fin parameters.buses)
    (bank : PrivateGuardBank (parameters := parameters) rename flag channel position.val)
    (added : PairedProjection bank.nots.cache.masks.checkedPrefix.state
      (equalFlagContext (parameters := parameters) rename flag)
      (mapLiteral rename (SourceSuffixSelector.guardHandle .healthy channel position))
      (mapLiteral rename (SourceSuffixSelector.guardHandle .faulty channel position)) 24) :
    PrivateGuardBank (parameters := parameters) rename flag channel (position.val + 1) := by
  let nextNots := bank.nots.afterTrace added.state added.steps added.checked
  refine ⟨nextNots, ?_⟩
  intro bus before
  by_cases same : bus = position
  · subst bus
    exact added.pair
  · have earlier : bus.val < position.val := by
      have different : bus.val ≠ position.val := fun equality => same (Fin.ext equality)
      omega
    exact (bank.pairs bus earlier).afterTrace added.state added.steps added.checked

def privateGuardBankAdvance (rename : Nat → Fin v) (flag : Bool) (channel : Fin parameters.channels)
    (position : Fin parameters.buses)
    (bank : PrivateGuardBank (parameters := parameters) rename flag channel position.val) :
    PrivateGuardBank (parameters := parameters) rename flag channel (position.val + 1) :=
  privateGuardBankAppend rename flag channel position bank (privateGuardOr rename flag channel position bank.nots)

def buildPrivateGuardBank (rename : Nat → Fin v) (flag : Bool) (channel : Fin parameters.channels)
    (nots : PrivateNotBank (parameters := parameters) rename flag (laterBuses (parameters := parameters)).length)
    (count : Nat) (bounded : count ≤ parameters.buses) :
    PrivateGuardBank (parameters := parameters) rename flag channel count :=
  match count with
  | 0 => privateGuardBankInitial rename flag channel nots
  | count + 1 => privateGuardBankAdvance rename flag channel ⟨count, by omega⟩
      (buildPrivateGuardBank rename flag channel nots count (by omega))

def PrivateGuardBankOriginalSupport (rename : Nat → Fin v) (flag : Bool)
    (channel : Fin parameters.channels) {count : Nat}
    (bank : PrivateGuardBank (parameters := parameters) rename flag channel count) : Prop :=
  PrivateNotBankOriginalSupport rename flag bank.nots ∧
    ∀ bus before, DirectionPairOrigin rename bank.nots.cache.masks.checkedPrefix (bank.pairs bus before)

theorem privateGuardBankInitial_supported (rename : Nat → Fin v) (flag : Bool)
    (channel : Fin parameters.channels)
    (nots : PrivateNotBank (parameters := parameters) rename flag (laterBuses (parameters := parameters)).length)
    (supported : PrivateNotBankOriginalSupport rename flag nots) :
    PrivateGuardBankOriginalSupport rename flag channel (privateGuardBankInitial rename flag channel nots) := by
  refine ⟨supported, ?_⟩
  intro bus before
  exact False.elim (Nat.not_lt_zero bus.val before)

theorem privateGuardBankAppend_supported (rename : Nat → Fin v) (flag : Bool)
    (channel : Fin parameters.channels) (position : Fin parameters.buses)
    (bank : PrivateGuardBank (parameters := parameters) rename flag channel position.val)
    (supported : PrivateGuardBankOriginalSupport rename flag channel bank)
    (added : PairedProjection bank.nots.cache.masks.checkedPrefix.state
      (equalFlagContext (parameters := parameters) rename flag)
      (mapLiteral rename (SourceSuffixSelector.guardHandle .healthy channel position))
      (mapLiteral rename (SourceSuffixSelector.guardHandle .faulty channel position)) 24)
    (addedOriginal : PairedProjectionOriginalSupport rename bank.nots.cache.masks.checkedPrefix added) :
    PrivateGuardBankOriginalSupport rename flag channel (privateGuardBankAppend rename flag channel position bank added) := by
  refine ⟨PrivateNotBank.afterTrace_supported rename flag bank.nots supported.1
    added.state added.steps added.checked addedOriginal.1, ?_⟩
  intro bus before
  by_cases same : bus = position
  · subst bus
    dsimp only [privateGuardBankAppend, PrivateNotBank.afterTrace, FlagMaskTable.afterTrace, SourcePrefix.extend]
    rw [dite_eq_left rfl]
    exact addedOriginal.2
  · have earlier : bus.val < position.val := by
      have different : bus.val ≠ position.val := fun equality => same (Fin.ext equality)
      omega
    have original := DirectionPairOrigin.afterTrace rename bank.nots.cache.masks.checkedPrefix
      (bank.pairs bus earlier) (supported.2 bus earlier) added.state added.steps added.checked
    dsimp only [privateGuardBankAppend, PrivateNotBank.afterTrace, FlagMaskTable.afterTrace, SourcePrefix.extend]
    rw [dite_eq_right same]
    exact original


theorem privateGuardBankAdvance_supported (rename : Nat → Fin v) (flag : Bool)
    (channel : Fin parameters.channels) (position : Fin parameters.buses)
    (bank : PrivateGuardBank (parameters := parameters) rename flag channel position.val)
    (supported : PrivateGuardBankOriginalSupport rename flag channel bank) :
    PrivateGuardBankOriginalSupport rename flag channel
      (privateGuardBankAdvance rename flag channel position bank) :=
  privateGuardBankAppend_supported rename flag channel position bank supported
    (privateGuardOr rename flag channel position bank.nots)
    (privateGuardOr_supported rename flag channel position bank.nots supported.1)

theorem buildPrivateGuardBank_supported (rename : Nat → Fin v) (flag : Bool)
    (channel : Fin parameters.channels)
    (nots : PrivateNotBank (parameters := parameters) rename flag (laterBuses (parameters := parameters)).length)
    (supported : PrivateNotBankOriginalSupport rename flag nots)
    (count : Nat) (bounded : count ≤ parameters.buses) :
    PrivateGuardBankOriginalSupport rename flag channel
      (buildPrivateGuardBank rename flag channel nots count bounded) := by
  induction count with
  | zero => exact privateGuardBankInitial_supported rename flag channel nots supported
  | succ count ih =>
      exact privateGuardBankAdvance_supported rename flag channel ⟨count, by omega⟩
        (buildPrivateGuardBank rename flag channel nots count (by omega)) (ih (by omega))

theorem privateNotBankAdvance_steps (rename : Nat → Fin v) (flag : Bool)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (bank : PrivateNotBank (parameters := parameters) rename flag position.val) :
    (privateNotBankAdvance rename flag position bank).cache.masks.checkedPrefix.steps.length ≤
      bank.cache.masks.checkedPrefix.steps.length + 4 := by
  let added := laterPrivateNotFromCache rename flag position bank.cache
  have next := added.count
  have scalar : (privateNotBankAdvance rename flag position bank).cache.masks.checkedPrefix.steps.length =
      bank.cache.masks.checkedPrefix.steps.length + added.steps.length := by
    simp only [privateNotBankAdvance, FlagMaskTable.afterTrace, SourcePrefix.extend, List.length_append, added]
  rw [scalar]
  omega

theorem buildPrivateNotBank_steps (rename : Nat → Fin v) (flag : Bool)
    (cache : FlagMaskTable (parameters := parameters) rename flag (laterBuses (parameters := parameters)).length)
    (count : Nat) (bounded : count ≤ (laterBuses (parameters := parameters)).length) :
    (buildPrivateNotBank rename flag cache count bounded).cache.masks.checkedPrefix.steps.length ≤
      cache.masks.checkedPrefix.steps.length + 4 * count := by
  induction count with
  | zero => exact Nat.le_refl _
  | succ count ih =>
      have next := privateNotBankAdvance_steps rename flag ⟨count, by omega⟩
        (buildPrivateNotBank rename flag cache count (by omega))
      have before := ih (by omega)
      simp only [buildPrivateNotBank]
      omega

theorem privateGuardBankAdvance_steps (rename : Nat → Fin v) (flag : Bool)
    (channel : Fin parameters.channels) (position : Fin parameters.buses)
    (bank : PrivateGuardBank (parameters := parameters) rename flag channel position.val) :
    (privateGuardBankAdvance rename flag channel position bank).nots.cache.masks.checkedPrefix.steps.length ≤
      bank.nots.cache.masks.checkedPrefix.steps.length + 24 := by
  let added := privateGuardOr rename flag channel position bank.nots
  have next := added.count
  have scalar : (privateGuardBankAdvance rename flag channel position bank).nots.cache.masks.checkedPrefix.steps.length =
      bank.nots.cache.masks.checkedPrefix.steps.length + added.steps.length := by
    simp only [privateGuardBankAdvance, privateGuardBankAppend, PrivateNotBank.afterTrace, FlagMaskTable.afterTrace,
      SourcePrefix.extend, List.length_append, added]
  rw [scalar]
  omega

theorem buildPrivateGuardBank_steps (rename : Nat → Fin v) (flag : Bool)
    (channel : Fin parameters.channels)
    (nots : PrivateNotBank (parameters := parameters) rename flag (laterBuses (parameters := parameters)).length)
    (count : Nat) (bounded : count ≤ parameters.buses) :
    (buildPrivateGuardBank rename flag channel nots count bounded).nots.cache.masks.checkedPrefix.steps.length ≤
      nots.cache.masks.checkedPrefix.steps.length + 24 * count := by
  induction count with
  | zero => exact Nat.le_refl _
  | succ count ih =>
      have next := privateGuardBankAdvance_steps rename flag channel ⟨count, by omega⟩
        (buildPrivateGuardBank rename flag channel nots count (by omega))
      have before := ih (by omega)
      simp only [buildPrivateGuardBank]
      omega

def qualifierEnablePair (rename : Nat → Fin v) (context : Clause (Fin v))
    (channel : Fin parameters.channels) (state : State v) :
    DirectionPair state context
      (mapLiteral rename ((qualifierGuarded .healthy channel).slots (.primary (.enable channel))))
      (mapLiteral rename ((qualifierGuarded .faulty channel).slots (.primary (.enable channel)))) := by
  have same := congrArg (mapLiteral rename)
    (((qualifierGuarded_roots .healthy channel).1 channel).trans
      ((qualifierGuarded_roots .faulty channel).1 channel).symm)
  exact ⟨.identity same, .identity same.symm⟩

def qualifierGuardPair (rename : Nat → Fin v) (flag : Bool) (channel : Fin parameters.channels)
    (bank : PrivateGuardBank (parameters := parameters) rename flag channel parameters.buses)
    (bus : Fin parameters.buses) :
    DirectionPair bank.nots.cache.masks.checkedPrefix.state (equalFlagContext (parameters := parameters) rename flag)
      (mapLiteral rename ((qualifierGuarded .healthy channel).slots (.internal (.qualifierGuard .healthy bus channel))))
      (mapLiteral rename ((qualifierGuarded .faulty channel).slots (.internal (.qualifierGuard .faulty bus channel)))) := by
  have typeEqual : DirectionPair bank.nots.cache.masks.checkedPrefix.state (equalFlagContext (parameters := parameters) rename flag)
      (mapLiteral rename ((qualifierGuarded .healthy channel).slots (.internal (.qualifierGuard .healthy bus channel))))
      (mapLiteral rename ((qualifierGuarded .faulty channel).slots (.internal (.qualifierGuard .faulty bus channel)))) =
      DirectionPair bank.nots.cache.masks.checkedPrefix.state (equalFlagContext (parameters := parameters) rename flag)
        (mapLiteral rename (SourceSuffixSelector.guardHandle .healthy channel bus))
        (mapLiteral rename (SourceSuffixSelector.guardHandle .faulty channel bus)) := by
    rw [qualifierGuarded_guard_handle, qualifierGuarded_guard_handle]
  exact Eq.mpr typeEqual (bank.pairs bus bus.isLt)

def qualifierGuardInputs (rename : Nat → Fin v) (channel : Fin parameters.channels) :
    List (Literal (Fin v) × Literal (Fin v)) :=
  (List.finRange parameters.buses).map fun bus =>
    (mapLiteral rename ((qualifierGuarded .healthy channel).slots (.internal (.qualifierGuard .healthy bus channel))),
     mapLiteral rename ((qualifierGuarded .faulty channel).slots (.internal (.qualifierGuard .faulty bus channel))))

def qualifierInputPairs (rename : Nat → Fin v) (channel : Fin parameters.channels) :
    List (Literal (Fin v) × Literal (Fin v)) :=
  (mapLiteral rename ((qualifierGuarded .healthy channel).slots (.primary (.enable channel))),
   mapLiteral rename ((qualifierGuarded .faulty channel).slots (.primary (.enable channel)))) ::
    qualifierGuardInputs rename channel

def qualifierInputDirection (rename : Nat → Fin v) (flag : Bool) (channel : Fin parameters.channels)
    (bank : PrivateGuardBank (parameters := parameters) rename flag channel parameters.buses)
    (pair : Literal (Fin v) × Literal (Fin v)) (member : pair ∈ qualifierInputPairs rename channel) :
    DirectionPair bank.nots.cache.masks.checkedPrefix.state (equalFlagContext (parameters := parameters) rename flag)
      pair.1 pair.2 := by
  let first : Literal (Fin v) × Literal (Fin v) :=
    (mapLiteral rename ((qualifierGuarded .healthy channel).slots (.primary (.enable channel))),
     mapLiteral rename ((qualifierGuarded .faulty channel).slots (.primary (.enable channel))))
  by_cases same : pair = first
  · subst pair
    exact qualifierEnablePair (parameters := parameters) rename (equalFlagContext (parameters := parameters) rename flag) channel bank.nots.cache.masks.checkedPrefix.state
  · have rest : pair ∈ qualifierGuardInputs rename channel := by
      simpa only [qualifierInputPairs, List.mem_cons, first, same, false_or] using member
    let selected := mappedChoice
      (fun bus : Fin parameters.buses =>
        (mapLiteral rename ((qualifierGuarded .healthy channel).slots (.internal (.qualifierGuard .healthy bus channel))),
         mapLiteral rename ((qualifierGuarded .faulty channel).slots (.internal (.qualifierGuard .faulty bus channel)))))
      pair (List.finRange parameters.buses) rest
    have whole := selected.property.2
    have typeEqual : DirectionPair bank.nots.cache.masks.checkedPrefix.state (equalFlagContext (parameters := parameters) rename flag) pair.1 pair.2 =
        DirectionPair bank.nots.cache.masks.checkedPrefix.state (equalFlagContext (parameters := parameters) rename flag)
          (mapLiteral rename ((qualifierGuarded .healthy channel).slots (.internal (.qualifierGuard .healthy selected.val channel))))
          (mapLiteral rename ((qualifierGuarded .faulty channel).slots (.internal (.qualifierGuard .faulty selected.val channel)))) :=
      congrArg (fun next : Literal (Fin v) × Literal (Fin v) => DirectionPair bank.nots.cache.masks.checkedPrefix.state
        (equalFlagContext (parameters := parameters) rename flag) next.1 next.2) whole.symm
    exact Eq.mpr typeEqual (qualifierGuardPair rename flag channel bank selected.val)

def qualifierOutput (rename : Nat → Fin v) (side : Side) (channel : Fin parameters.channels) : Literal (Fin v) :=
  mapLiteral rename (SourceSerialFold.allocate .conjunction (qualifierGuarded side channel).lastID
    ((qualifierGuarded side channel).slots (.primary (.enable channel)) ::
      (List.finRange parameters.buses).map fun bus =>
        (qualifierGuarded side channel).slots (.internal (.qualifierGuard side bus channel)))).output

def qualifierFromGuardBank (rename : Nat → Fin v) (flag : Bool) (channel : Fin parameters.channels)
    (bank : PrivateGuardBank (parameters := parameters) rename flag channel parameters.buses) :
    PairedProjection bank.nots.cache.masks.checkedPrefix.state (equalFlagContext (parameters := parameters) rename flag)
      (qualifierOutput rename .healthy channel) (qualifierOutput rename .faulty channel)
      (12 * (qualifierInputPairs rename channel).length) := by
  let prefixState := bank.nots.cache.masks.checkedPrefix
  let leftTree : AndTree prefixState.state (qualifierOutput rename .healthy channel)
      ((qualifierInputPairs rename channel).map Prod.fst) := by
    simpa only [qualifierInputPairs, qualifierGuardInputs, qualifierOutput, List.map_cons, List.map_map,
      List.map_nil, Function.comp_def] using
      (qualifierTree rename .healthy channel).afterTrace prefixState.state prefixState.steps prefixState.checked
  let rightTree : AndTree prefixState.state (qualifierOutput rename .faulty channel)
      ((qualifierInputPairs rename channel).map Prod.snd) := by
    simpa only [qualifierInputPairs, qualifierGuardInputs, qualifierOutput, List.map_cons, List.map_map,
      List.map_nil, Function.comp_def] using
      (qualifierTree rename .faulty channel).afterTrace prefixState.state prefixState.steps prefixState.checked
  exact pairedAnd prefixState.state (equalFlagContext (parameters := parameters) rename flag) _ _ (qualifierInputPairs rename channel)
    (by simp [qualifierInputPairs]) leftTree rightTree
    (fun pair member => qualifierInputDirection rename flag channel bank pair member)

theorem qualifierFromGuardBank_count (rename : Nat → Fin v) (flag : Bool)
    (channel : Fin parameters.channels)
    (bank : PrivateGuardBank (parameters := parameters) rename flag channel parameters.buses) :
    (qualifierFromGuardBank rename flag channel bank).steps.length ≤ 12 * (parameters.buses + 1) := by
  have actual := (qualifierFromGuardBank rename flag channel bank).count
  have size : (qualifierInputPairs rename channel).length = parameters.buses + 1 := by
    simp only [qualifierInputPairs, qualifierGuardInputs, List.length_cons, List.length_map,
      List.length_finRange, Nat.add_comm]
  calc
    (qualifierFromGuardBank rename flag channel bank).steps.length ≤
        12 * (qualifierInputPairs rename channel).length := actual
    _ = 12 * (parameters.buses + 1) := congrArg (12 * ·) size

structure ChannelQualifierResult (rename : Nat → Fin v) (flag : Bool) (channel : Fin parameters.channels) where
  prefixState : SourcePrefix (parameters := parameters) rename
  pair : DirectionPair prefixState.state (equalFlagContext (parameters := parameters) rename flag)
    (qualifierOutput rename .healthy channel) (qualifierOutput rename .faulty channel)

def channelQualifierFromNotBank (rename : Nat → Fin v) (flag : Bool) (channel : Fin parameters.channels)
    (nots : PrivateNotBank (parameters := parameters) rename flag (laterBuses (parameters := parameters)).length) :
    ChannelQualifierResult (parameters := parameters) rename flag channel := by
  let guards := buildPrivateGuardBank rename flag channel nots parameters.buses (Nat.le_refl _)
  let added := qualifierFromGuardBank rename flag channel guards
  exact ⟨guards.nots.cache.masks.checkedPrefix.extend added.state added.steps added.checked, added.pair⟩

def channelQualifier (rename : Nat → Fin v) (flag : Bool) (channel : Fin parameters.channels) :
    ChannelQualifierResult (parameters := parameters) rename flag channel :=
  channelQualifierFromNotBank rename flag channel (allPrivateNotPairs (parameters := parameters) rename flag)


theorem qualifierEnablePair_supported (rename : Nat → Fin v) (context : Clause (Fin v))
    (channel : Fin parameters.channels) (prefixState : SourcePrefix (parameters := parameters) rename) :
    DirectionPairOrigin rename prefixState (qualifierEnablePair rename context channel prefixState.state) :=
  ⟨trivial, trivial⟩

theorem qualifierGuardPair_supported (rename : Nat → Fin v) (flag : Bool)
    (channel : Fin parameters.channels)
    (bank : PrivateGuardBank (parameters := parameters) rename flag channel parameters.buses)
    (supported : PrivateGuardBankOriginalSupport rename flag channel bank)
    (bus : Fin parameters.buses) :
    DirectionPairOrigin rename bank.nots.cache.masks.checkedPrefix
      (qualifierGuardPair rename flag channel bank bus) := by
  dsimp only [qualifierGuardPair]
  apply directionPairOrigin_mpr rename bank.nots.cache.masks.checkedPrefix
    (congrArg (mapLiteral rename) (qualifierGuarded_guard_handle .healthy channel bus)).symm
    (congrArg (mapLiteral rename) (qualifierGuarded_guard_handle .faulty channel bus)).symm
  exact supported.2 bus bus.isLt

theorem qualifierInputDirection_supported (rename : Nat → Fin v) (flag : Bool)
    (channel : Fin parameters.channels)
    (bank : PrivateGuardBank (parameters := parameters) rename flag channel parameters.buses)
    (supported : PrivateGuardBankOriginalSupport rename flag channel bank)
    (pair : Literal (Fin v) × Literal (Fin v)) (member : pair ∈ qualifierInputPairs rename channel) :
    DirectionPairOrigin rename bank.nots.cache.masks.checkedPrefix
      (qualifierInputDirection rename flag channel bank pair member) := by
  let first : Literal (Fin v) × Literal (Fin v) :=
    (mapLiteral rename ((qualifierGuarded .healthy channel).slots (.primary (.enable channel))),
     mapLiteral rename ((qualifierGuarded .faulty channel).slots (.primary (.enable channel))))
  dsimp only [qualifierInputDirection]
  by_cases same : pair = first
  · rw [dite_eq_left same]
    subst pair
    exact qualifierEnablePair_supported rename (equalFlagContext (parameters := parameters) rename flag)
      channel bank.nots.cache.masks.checkedPrefix
  · rw [dite_eq_right same]
    have rest : pair ∈ qualifierGuardInputs rename channel := by
      simpa only [qualifierInputPairs, List.mem_cons, first, same, false_or] using member
    let selected := mappedChoice
      (fun bus : Fin parameters.buses =>
        (mapLiteral rename ((qualifierGuarded .healthy channel).slots (.internal (.qualifierGuard .healthy bus channel))),
         mapLiteral rename ((qualifierGuarded .faulty channel).slots (.internal (.qualifierGuard .faulty bus channel)))))
      pair (List.finRange parameters.buses) rest
    have whole := selected.property.2
    apply directionPairOrigin_mpr rename bank.nots.cache.masks.checkedPrefix
      (congrArg Prod.fst whole) (congrArg Prod.snd whole)
    exact qualifierGuardPair_supported rename flag channel bank supported selected.val

theorem qualifierFromGuardBank_supported (rename : Nat → Fin v) (flag : Bool)
    (channel : Fin parameters.channels)
    (bank : PrivateGuardBank (parameters := parameters) rename flag channel parameters.buses)
    (supported : PrivateGuardBankOriginalSupport rename flag channel bank) :
    PairedProjectionOriginalSupport rename bank.nots.cache.masks.checkedPrefix
      (qualifierFromGuardBank rename flag channel bank) := by
  let prefixState := bank.nots.cache.masks.checkedPrefix
  let leftTree : AndTree prefixState.state (qualifierOutput rename .healthy channel)
      ((qualifierInputPairs rename channel).map Prod.fst) := by
    simpa only [qualifierInputPairs, qualifierGuardInputs, qualifierOutput, List.map_cons, List.map_map,
      List.map_nil, Function.comp_def] using
      (qualifierTree rename .healthy channel).afterTrace prefixState.state prefixState.steps prefixState.checked
  let rightTree : AndTree prefixState.state (qualifierOutput rename .faulty channel)
      ((qualifierInputPairs rename channel).map Prod.snd) := by
    simpa only [qualifierInputPairs, qualifierGuardInputs, qualifierOutput, List.map_cons, List.map_map,
      List.map_nil, Function.comp_def] using
      (qualifierTree rename .faulty channel).afterTrace prefixState.state prefixState.steps prefixState.checked
  have leftOriginal : TreeOriginals
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename) leftTree := by
    dsimp only [leftTree]
    apply treeOriginals_mpr (by
      simp only [qualifierInputPairs, qualifierGuardInputs, qualifierOutput, List.map_cons,
        List.map_map, List.map_nil, Function.comp_def])
    apply treeOriginals_mp (by
      simp only [qualifierInputPairs, qualifierGuardInputs, qualifierOutput, List.map_cons,
        List.map_map, List.map_nil, Function.comp_def])
    exact treeOriginals_afterTrace _ (qualifierTree rename .healthy channel)
      (qualifierTree_originals rename .healthy channel) prefixState.state prefixState.steps prefixState.checked
  have rightOriginal : TreeOriginals
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename) rightTree := by
    dsimp only [rightTree]
    apply treeOriginals_mpr (by
      simp only [qualifierInputPairs, qualifierGuardInputs, qualifierOutput, List.map_cons,
        List.map_map, List.map_nil, Function.comp_def])
    apply treeOriginals_mp (by
      simp only [qualifierInputPairs, qualifierGuardInputs, qualifierOutput, List.map_cons,
        List.map_map, List.map_nil, Function.comp_def])
    exact treeOriginals_afterTrace _ (qualifierTree rename .faulty channel)
      (qualifierTree_originals rename .faulty channel) prefixState.state prefixState.steps prefixState.checked
  exact pairedAnd_supported rename prefixState (equalFlagContext (parameters := parameters) rename flag)
    _ _ (qualifierInputPairs rename channel) (by simp [qualifierInputPairs]) leftTree rightTree
    (fun pair member => qualifierInputDirection rename flag channel bank pair member)
    leftOriginal rightOriginal supported.1.1.1.1
    (fun pair member => qualifierInputDirection_supported rename flag channel bank supported pair member)

def ChannelQualifierOriginalSupport (rename : Nat → Fin v) (flag : Bool)
    (channel : Fin parameters.channels) (result : ChannelQualifierResult (parameters := parameters) rename flag channel) : Prop :=
  SourceMixedSchedule.PrefixOriginalSupport rename result.prefixState ∧
    DirectionPairOrigin rename result.prefixState result.pair

theorem channelQualifierFromNotBank_supported (rename : Nat → Fin v) (flag : Bool)
    (channel : Fin parameters.channels)
    (nots : PrivateNotBank (parameters := parameters) rename flag (laterBuses (parameters := parameters)).length)
    (supported : PrivateNotBankOriginalSupport rename flag nots) :
    ChannelQualifierOriginalSupport rename flag channel (channelQualifierFromNotBank rename flag channel nots) := by
  let guards := buildPrivateGuardBank rename flag channel nots parameters.buses (Nat.le_refl _)
  have guardOriginal := buildPrivateGuardBank_supported rename flag channel nots supported
    parameters.buses (Nat.le_refl _)
  exact qualifierFromGuardBank_supported rename flag channel guards guardOriginal

theorem channelQualifier_supported (rename : Nat → Fin v) (flag : Bool)
    (channel : Fin parameters.channels) :
    ChannelQualifierOriginalSupport rename flag channel (channelQualifier rename flag channel) :=
  channelQualifierFromNotBank_supported rename flag channel _ (allPrivateNotPairs_supported rename flag)


structure QualifierTable (rename : Nat → Fin v) (flag : Bool) (count : Nat) where
  nots : PrivateNotBank (parameters := parameters) rename flag (laterBuses (parameters := parameters)).length
  pairs : ∀ channel : Fin parameters.channels, channel.val < count →
    DirectionPair nots.cache.masks.checkedPrefix.state (equalFlagContext (parameters := parameters) rename flag)
      (qualifierOutput rename .healthy channel) (qualifierOutput rename .faulty channel)

/-- Earlier channel outputs are retained during every actual guard OR macro. -/
structure ChannelGuardTable (rename : Nat → Fin v) (flag : Bool)
    (channel : Fin parameters.channels) (busCount : Nat) where
  guards : PrivateGuardBank (parameters := parameters) rename flag channel busCount
  earlier : ∀ query : Fin parameters.channels, query.val < channel.val →
    DirectionPair guards.nots.cache.masks.checkedPrefix.state (equalFlagContext (parameters := parameters) rename flag)
      (qualifierOutput rename .healthy query) (qualifierOutput rename .faulty query)

def channelGuardInitial (rename : Nat → Fin v) (flag : Bool) (channel : Fin parameters.channels)
    (table : QualifierTable (parameters := parameters) rename flag channel.val) :
    ChannelGuardTable (parameters := parameters) rename flag channel 0 :=
  ⟨privateGuardBankInitial rename flag channel table.nots, table.pairs⟩

def channelGuardAppend (rename : Nat → Fin v) (flag : Bool) (channel : Fin parameters.channels)
    (position : Fin parameters.buses)
    (table : ChannelGuardTable (parameters := parameters) rename flag channel position.val)
    (added : PairedProjection table.guards.nots.cache.masks.checkedPrefix.state
      (equalFlagContext (parameters := parameters) rename flag)
      (mapLiteral rename (SourceSuffixSelector.guardHandle .healthy channel position))
      (mapLiteral rename (SourceSuffixSelector.guardHandle .faulty channel position)) 24) :
    ChannelGuardTable (parameters := parameters) rename flag channel (position.val + 1) :=
  ⟨privateGuardBankAppend rename flag channel position table.guards added,
    fun query before => (table.earlier query before).afterTrace added.state added.steps added.checked⟩

def channelGuardAdvance (rename : Nat → Fin v) (flag : Bool) (channel : Fin parameters.channels)
    (position : Fin parameters.buses)
    (table : ChannelGuardTable (parameters := parameters) rename flag channel position.val) :=
  channelGuardAppend rename flag channel position table
    (privateGuardOr rename flag channel position table.guards.nots)

def buildChannelGuards (rename : Nat → Fin v) (flag : Bool) (channel : Fin parameters.channels)
    (table : QualifierTable (parameters := parameters) rename flag channel.val)
    (count : Nat) (bounded : count ≤ parameters.buses) :
    ChannelGuardTable (parameters := parameters) rename flag channel count :=
  match count with
  | 0 => channelGuardInitial rename flag channel table
  | count + 1 => channelGuardAdvance rename flag channel ⟨count, by omega⟩
      (buildChannelGuards rename flag channel table count (by omega))

def qualifierTableAppend (rename : Nat → Fin v) (flag : Bool) (channel : Fin parameters.channels)
    (guards : ChannelGuardTable (parameters := parameters) rename flag channel parameters.buses)
    (added : PairedProjection guards.guards.nots.cache.masks.checkedPrefix.state
      (equalFlagContext (parameters := parameters) rename flag)
      (qualifierOutput rename .healthy channel) (qualifierOutput rename .faulty channel)
      (12 * (qualifierInputPairs rename channel).length)) :
    QualifierTable (parameters := parameters) rename flag (channel.val + 1) := by
  refine ⟨guards.guards.nots.afterTrace added.state added.steps added.checked, ?_⟩
  intro query before
  by_cases same : query = channel
  · subst query
    exact added.pair
  · have earlier : query.val < channel.val := by
      have different : query.val ≠ channel.val := fun equality => same (Fin.ext equality)
      omega
    exact (guards.earlier query earlier).afterTrace added.state added.steps added.checked

def qualifierTableAdvance (rename : Nat → Fin v) (flag : Bool) (channel : Fin parameters.channels)
    (table : QualifierTable (parameters := parameters) rename flag channel.val) :
    QualifierTable (parameters := parameters) rename flag (channel.val + 1) :=
  let guards := buildChannelGuards rename flag channel table parameters.buses (Nat.le_refl _)
  qualifierTableAppend rename flag channel guards (qualifierFromGuardBank rename flag channel guards.guards)

def qualifierTableInitial (rename : Nat → Fin v) (flag : Bool) :
    QualifierTable (parameters := parameters) rename flag 0 :=
  ⟨allPrivateNotPairs rename flag, fun query before => False.elim (Nat.not_lt_zero query.val before)⟩

/-- The actual all-channel constructor reuses the one constructed NOT bank. -/
def buildQualifierTable (rename : Nat → Fin v) (flag : Bool) (count : Nat)
    (bounded : count ≤ parameters.channels) : QualifierTable (parameters := parameters) rename flag count :=
  match count with
  | 0 => qualifierTableInitial rename flag
  | count + 1 => qualifierTableAdvance rename flag ⟨count, by omega⟩
      (buildQualifierTable rename flag count (by omega))

def allChannelQualifiers (rename : Nat → Fin v) (flag : Bool) :=
  buildQualifierTable rename flag parameters.channels (Nat.le_refl _)

def QualifierTableOriginalSupport (rename : Nat → Fin v) (flag : Bool) {count : Nat}
    (table : QualifierTable (parameters := parameters) rename flag count) : Prop :=
  PrivateNotBankOriginalSupport rename flag table.nots ∧
    ∀ channel before, DirectionPairOrigin rename table.nots.cache.masks.checkedPrefix (table.pairs channel before)

def ChannelGuardTableOriginalSupport (rename : Nat → Fin v) (flag : Bool)
    (channel : Fin parameters.channels) {count : Nat}
    (table : ChannelGuardTable (parameters := parameters) rename flag channel count) : Prop :=
  PrivateGuardBankOriginalSupport rename flag channel table.guards ∧
    ∀ query before, DirectionPairOrigin rename table.guards.nots.cache.masks.checkedPrefix (table.earlier query before)

theorem channelGuardInitial_supported (rename : Nat → Fin v) (flag : Bool)
    (channel : Fin parameters.channels)
    (table : QualifierTable (parameters := parameters) rename flag channel.val)
    (supported : QualifierTableOriginalSupport rename flag table) :
    ChannelGuardTableOriginalSupport rename flag channel (channelGuardInitial rename flag channel table) :=
  ⟨privateGuardBankInitial_supported rename flag channel table.nots supported.1, supported.2⟩

theorem channelGuardAppend_supported (rename : Nat → Fin v) (flag : Bool)
    (channel : Fin parameters.channels) (position : Fin parameters.buses)
    (table : ChannelGuardTable (parameters := parameters) rename flag channel position.val)
    (supported : ChannelGuardTableOriginalSupport rename flag channel table)
    (added : PairedProjection table.guards.nots.cache.masks.checkedPrefix.state
      (equalFlagContext (parameters := parameters) rename flag)
      (mapLiteral rename (SourceSuffixSelector.guardHandle .healthy channel position))
      (mapLiteral rename (SourceSuffixSelector.guardHandle .faulty channel position)) 24)
    (addedOriginal : PairedProjectionOriginalSupport rename table.guards.nots.cache.masks.checkedPrefix added) :
    ChannelGuardTableOriginalSupport rename flag channel
      (channelGuardAppend rename flag channel position table added) := by
  refine ⟨privateGuardBankAppend_supported rename flag channel position table.guards supported.1 added addedOriginal, ?_⟩
  intro query before
  exact DirectionPairOrigin.afterTrace rename table.guards.nots.cache.masks.checkedPrefix
    (table.earlier query before) (supported.2 query before) added.state added.steps added.checked

theorem buildChannelGuards_supported (rename : Nat → Fin v) (flag : Bool)
    (channel : Fin parameters.channels)
    (table : QualifierTable (parameters := parameters) rename flag channel.val)
    (supported : QualifierTableOriginalSupport rename flag table)
    (count : Nat) (bounded : count ≤ parameters.buses) :
    ChannelGuardTableOriginalSupport rename flag channel (buildChannelGuards rename flag channel table count bounded) := by
  induction count with
  | zero => exact channelGuardInitial_supported rename flag channel table supported
  | succ count ih =>
    let previous := buildChannelGuards rename flag channel table count (by omega)
    have prior := ih (by omega)
    exact channelGuardAppend_supported rename flag channel ⟨count, by omega⟩ previous prior
      (privateGuardOr rename flag channel ⟨count, by omega⟩ previous.guards.nots)
      (privateGuardOr_supported rename flag channel ⟨count, by omega⟩ previous.guards.nots prior.1.1)


theorem qualifierTableAppend_supported (rename : Nat → Fin v) (flag : Bool)
    (channel : Fin parameters.channels)
    (guards : ChannelGuardTable (parameters := parameters) rename flag channel parameters.buses)
    (supported : ChannelGuardTableOriginalSupport rename flag channel guards)
    (added : PairedProjection guards.guards.nots.cache.masks.checkedPrefix.state
      (equalFlagContext (parameters := parameters) rename flag)
      (qualifierOutput rename .healthy channel) (qualifierOutput rename .faulty channel)
      (12 * (qualifierInputPairs rename channel).length))
    (addedOriginal : PairedProjectionOriginalSupport rename guards.guards.nots.cache.masks.checkedPrefix added) :
    QualifierTableOriginalSupport rename flag (qualifierTableAppend rename flag channel guards added) := by
  refine ⟨PrivateNotBank.afterTrace_supported rename flag guards.guards.nots supported.1.1
    added.state added.steps added.checked addedOriginal.1, ?_⟩
  intro query before
  by_cases same : query = channel
  · subst query
    dsimp only [qualifierTableAppend, PrivateNotBank.afterTrace, FlagMaskTable.afterTrace, SourcePrefix.extend]
    rw [dite_eq_left rfl]
    exact addedOriginal.2
  · have earlier : query.val < channel.val := by
      have different : query.val ≠ channel.val := fun equality => same (Fin.ext equality)
      omega
    have old := DirectionPairOrigin.afterTrace rename guards.guards.nots.cache.masks.checkedPrefix
      (guards.earlier query earlier) (supported.2 query earlier) added.state added.steps added.checked
    dsimp only [qualifierTableAppend, PrivateNotBank.afterTrace, FlagMaskTable.afterTrace, SourcePrefix.extend]
    rw [dite_eq_right same]
    exact old

theorem qualifierTableAdvance_supported (rename : Nat → Fin v) (flag : Bool)
    (channel : Fin parameters.channels)
    (table : QualifierTable (parameters := parameters) rename flag channel.val)
    (supported : QualifierTableOriginalSupport rename flag table) :
    QualifierTableOriginalSupport rename flag (qualifierTableAdvance rename flag channel table) := by
  let guards := buildChannelGuards rename flag channel table parameters.buses (Nat.le_refl _)
  have original := buildChannelGuards_supported rename flag channel table supported parameters.buses (Nat.le_refl _)
  exact qualifierTableAppend_supported rename flag channel guards original
    (qualifierFromGuardBank rename flag channel guards.guards)
    (qualifierFromGuardBank_supported rename flag channel guards.guards original.1)

theorem qualifierTableInitial_supported (rename : Nat → Fin v) (flag : Bool) :
    QualifierTableOriginalSupport (parameters := parameters) rename flag
      (qualifierTableInitial (parameters := parameters) rename flag) := by
  refine ⟨allPrivateNotPairs_supported (parameters := parameters) rename flag, ?_⟩
  intro query before
  exact False.elim (Nat.not_lt_zero query.val before)

theorem buildQualifierTable_supported (rename : Nat → Fin v) (flag : Bool)
    (count : Nat) (bounded : count ≤ parameters.channels) :
    QualifierTableOriginalSupport rename flag (buildQualifierTable rename flag count bounded) := by
  induction count with
  | zero => exact qualifierTableInitial_supported rename flag
  | succ count ih =>
    exact qualifierTableAdvance_supported rename flag ⟨count, by omega⟩
      (buildQualifierTable rename flag count (by omega)) (ih (by omega))

theorem allChannelQualifiers_supported (rename : Nat → Fin v) (flag : Bool) :
    QualifierTableOriginalSupport rename flag (allChannelQualifiers (parameters := parameters) rename flag) :=
  buildQualifierTable_supported rename flag parameters.channels (Nat.le_refl _)

def channelQualifierBudget (parameters : Parameters) : Nat := 24 * parameters.buses + 12 * (parameters.buses + 1)

theorem channelGuardAppend_count (rename : Nat → Fin v) (flag : Bool) (channel : Fin parameters.channels)
    (position : Fin parameters.buses)
    (table : ChannelGuardTable (parameters := parameters) rename flag channel position.val)
    (added : PairedProjection table.guards.nots.cache.masks.checkedPrefix.state
      (equalFlagContext (parameters := parameters) rename flag)
      (mapLiteral rename (SourceSuffixSelector.guardHandle .healthy channel position))
      (mapLiteral rename (SourceSuffixSelector.guardHandle .faulty channel position)) 24) :
    (channelGuardAppend rename flag channel position table added).guards.nots.cache.masks.checkedPrefix.steps.length ≤
      table.guards.nots.cache.masks.checkedPrefix.steps.length + 24 := by
  have count := added.count
  change (table.guards.nots.cache.masks.checkedPrefix.steps ++ added.steps).length ≤ _
  rw [List.length_append]
  omega

theorem buildChannelGuards_count (rename : Nat → Fin v) (flag : Bool) (channel : Fin parameters.channels)
    (table : QualifierTable (parameters := parameters) rename flag channel.val)
    (count : Nat) (bounded : count ≤ parameters.buses) :
    (buildChannelGuards rename flag channel table count bounded).guards.nots.cache.masks.checkedPrefix.steps.length ≤
      table.nots.cache.masks.checkedPrefix.steps.length + 24 * count := by
  induction count with
  | zero => exact Nat.le_refl _
  | succ count ih =>
    let previous := buildChannelGuards rename flag channel table count (by omega)
    have prior := ih (by omega)
    have next := channelGuardAppend_count rename flag channel ⟨count, by omega⟩ previous
      (privateGuardOr rename flag channel ⟨count, by omega⟩ previous.guards.nots)
    dsimp only [previous] at next
    simp only [buildChannelGuards, channelGuardAdvance]
    omega

theorem qualifierTableAdvance_count (rename : Nat → Fin v) (flag : Bool) (channel : Fin parameters.channels)
    (table : QualifierTable (parameters := parameters) rename flag channel.val) :
    (qualifierTableAdvance rename flag channel table).nots.cache.masks.checkedPrefix.steps.length ≤
      table.nots.cache.masks.checkedPrefix.steps.length + channelQualifierBudget parameters := by
  let guards := buildChannelGuards rename flag channel table parameters.buses (Nat.le_refl _)
  let added := qualifierFromGuardBank rename flag channel guards.guards
  have prior := buildChannelGuards_count rename flag channel table parameters.buses (Nat.le_refl _)
  have next := qualifierFromGuardBank_count rename flag channel guards.guards
  have scalar : (qualifierTableAdvance rename flag channel table).nots.cache.masks.checkedPrefix.steps.length =
      guards.guards.nots.cache.masks.checkedPrefix.steps.length + added.steps.length := by
    simp only [qualifierTableAdvance, qualifierTableAppend, PrivateNotBank.afterTrace, FlagMaskTable.afterTrace,
      SourcePrefix.extend, List.length_append, guards, added]
  rw [scalar]
  dsimp only [guards, added] at prior next ⊢
  unfold channelQualifierBudget
  omega

theorem buildQualifierTable_count (rename : Nat → Fin v) (flag : Bool)
    (count : Nat) (bounded : count ≤ parameters.channels) :
    (buildQualifierTable rename flag count bounded).nots.cache.masks.checkedPrefix.steps.length ≤
      (allPrivateNotPairs (parameters := parameters) rename flag).cache.masks.checkedPrefix.steps.length +
        channelQualifierBudget parameters * count := by
  induction count with
  | zero => exact Nat.le_refl _
  | succ count ih =>
    have prior := ih (show count ≤ parameters.channels by omega)
    have next := qualifierTableAdvance_count (parameters := parameters) rename flag ⟨count, by omega⟩
      (buildQualifierTable (parameters := parameters) rename flag count (by omega))
    simp only [buildQualifierTable, Nat.mul_add, Nat.mul_one]
    omega


def qualifierProgramBudget (parameters : Parameters) : Nat :=
  2 * parameters.channels +
  parameters.buses * (12 * parameters.channels * (2 + parameters.buses) + 38 * parameters.channels) +
  4 * parameters.buses + channelQualifierBudget parameters * parameters.channels

theorem allPrivateNotPairs_count (rename : Nat → Fin v) (flag : Bool) :
    (allPrivateNotPairs (parameters := parameters) rename flag).cache.masks.checkedPrefix.steps.length ≤
      2 * parameters.channels + parameters.buses *
        (12 * parameters.channels * (2 + parameters.buses) + 38 * parameters.channels) + 4 * parameters.buses := by
  have actual := buildPrivateNotBank_steps (parameters := parameters) rename flag
    (allFlagMasks (parameters := parameters) rename flag)
    (laterBuses (parameters := parameters)).length (Nat.le_refl _)
  have initial : (allFlagMasks (parameters := parameters) rename flag).masks.checkedPrefix.steps.length ≤
      2 * parameters.channels + parameters.buses *
        (12 * parameters.channels * (2 + parameters.buses) + 38 * parameters.channels) := by
    rw [allFlagMasks_masks]
    exact allBusMasks_count (parameters := parameters) rename flag
  have size : (laterBuses (parameters := parameters)).length ≤ parameters.buses := by
    simpa only [laterBuses, List.length_finRange] using
      List.length_filter_le (fun bus : Fin parameters.buses => bus.val != 0) (List.finRange parameters.buses)
  have nots := Nat.mul_le_mul_left 4 size
  change (allPrivateNotPairs (parameters := parameters) rename flag).cache.masks.checkedPrefix.steps.length ≤ _ at actual
  exact actual.trans (Nat.add_le_add initial nots)

theorem allChannelQualifiers_count (rename : Nat → Fin v) (flag : Bool) :
    (allChannelQualifiers (parameters := parameters) rename flag).nots.cache.masks.checkedPrefix.steps.length ≤
      qualifierProgramBudget parameters := by
  have actual := buildQualifierTable_count (parameters := parameters) rename flag
    parameters.channels (Nat.le_refl _)
  have initial := allPrivateNotPairs_count (parameters := parameters) rename flag
  exact actual.trans (Nat.add_le_add_right initial _)



theorem initialMasks_qualifier (side querySide : Side) (channel : Fin parameters.channels)
    (cursor : Cursor parameters) :
    (initialMasks parameters side cursor).slots (.internal (.qualifier querySide channel)) =
      cursor.slots (.internal (.qualifier querySide channel)) := by
  unfold initialMasks
  exact foldl_slot _ _ (fun current index => emitNative_other current _ _ _ (by simp)) _ _

theorem laterBus_qualifier (side querySide : Side) (bus : Fin parameters.buses)
    (channel : Fin parameters.channels) (cursor : Cursor parameters) :
    (laterBus parameters side bus cursor).slots (.internal (.qualifier querySide channel)) =
      cursor.slots (.internal (.qualifier querySide channel)) := by
  unfold laterBus
  rw [foldl_slot _ _ (by
    intro current index
    dsimp only
    rw [emitNative_other _ _ _ _ (by simp), emitNative_other current _ _ _ (by simp)])]
  rw [foldNative_other _ _ _ _ _ (by simp)]
  exact foldl_slot _ _ (fun current index => foldNative_other current _ _ _ _ (by simp)) _ _

theorem negateFlags_qualifier (side querySide : Side) (channel : Fin parameters.channels)
    (cursor : Cursor parameters) :
    (negateFlags parameters side cursor).slots (.internal (.qualifier querySide channel)) =
      cursor.slots (.internal (.qualifier querySide channel)) := by
  unfold negateFlags
  apply foldl_slot
  intro current bus
  rfl

theorem eligible_qualifier_other (side querySide : Side)
    (index channel : Fin parameters.channels) (cursor : Cursor parameters)
    (different : querySide ≠ side ∨ channel ≠ index) :
    (eligible parameters side index cursor).slots (.internal (.qualifier querySide channel)) =
      cursor.slots (.internal (.qualifier querySide channel)) := by
  unfold eligible
  rw [foldNative_other _ _ _ _ _ (by rcases different with h | h <;> simp [h])]
  exact foldl_slot _ _ (fun current bus => emitNative_other current _ _ _ (by simp)) _ _

theorem tail_qualifier_other (side querySide : Side) (channel : Fin parameters.channels)
    (cursor : Cursor parameters) (different : querySide ≠ side) :
    (tail parameters side cursor).slots (.internal (.qualifier querySide channel)) =
      cursor.slots (.internal (.qualifier querySide channel)) := by
  unfold tail
  rw [foldl_slot _ _ (fun current index => eligible_qualifier_other side querySide index channel current (Or.inl different)),
    negateFlags_qualifier]
  rw [foldl_slot _ _ (fun current bus => laterBus_qualifier side querySide bus channel current)]
  exact initialMasks_qualifier side querySide channel cursor

theorem tail_qualifier_output (side : Side) (channel : Fin parameters.channels) :
    (tail parameters side (tailStart side)).slots (.internal (.qualifier side channel)) =
      (eligible parameters side channel (eligibleBefore side channel)).slots (.internal (.qualifier side channel)) := by
  let values := List.finRange parameters.channels
  have bound : channel.val < values.length := by simpa [values] using channel.isLt
  have decomposition : values = values.take channel.val ++ channel :: values.drop (channel.val + 1) := by
    simpa [values] using positional_decomposition values ⟨channel.val, bound⟩
  have unique : (values.take channel.val ++ channel :: values.drop (channel.val + 1)).Nodup := by
    rw [← decomposition]
    exact List.nodup_finRange parameters.channels
  have absent : channel ∉ values.drop (channel.val + 1) :=
    (List.nodup_cons.mp (List.nodup_append.mp unique).2.1).1
  change (values.foldl (fun current index => eligible parameters side index current)
    (negateFlags parameters side (tailStages side))).slots _ = _
  rw [decomposition, List.foldl_append, List.foldl_cons]
  rw [Controller.NativeProof.SourceRoleFrames.foldl_slot_mem _ _ _ (by
    intro current index member
    apply eligible_qualifier_other
    exact Or.inr (fun equal => absent (equal ▸ member)))]
  rfl

theorem controller_qualifier_output (side : Side) (channel : Fin parameters.channels) :
    (controller parameters).slots (.internal (.qualifier side channel)) =
      (eligible parameters side channel (eligibleBefore side channel)).slots (.internal (.qualifier side channel)) := by
  cases side with
  | healthy =>
    unfold controller
    rw [tail_qualifier_other .faulty .healthy channel _ (by decide)]
    exact tail_qualifier_output .healthy channel
  | faulty => exact tail_qualifier_output .faulty channel

theorem qualifierOutput_decoderStart (rename : Nat → Fin v) (side : Side)
    (channel : Fin parameters.channels) :
    qualifierOutput rename side channel = mapLiteral rename
      ((Controller.NativeProof.SourceFoldOccurrences.decoderStart side).slots (.internal (.qualifier side channel))) := by
  unfold qualifierOutput
  rw [← eligible_output_eq_allocator, ← controller_qualifier_output]
  congr 1
  cases side with
  | healthy => exact (Controller.NativeProof.SourceRoleFrames.originalObservations_slot _ _).symm
  | faulty =>
    rw [Controller.NativeProof.SourceFoldOccurrences.decoderStart,
      Controller.NativeProof.SourceDecoderSchedule.attachDecoder_qualifier,
      Controller.NativeProof.SourceRoleFrames.originalObservations_slot]



def constructedDecoderQualifier (rename : Nat → Fin v) (flag : Bool)
    (channel : Fin parameters.channels) :
    DirectionPair (allChannelQualifiers (parameters := parameters) rename flag).nots.cache.masks.checkedPrefix.state
      (equalFlagContext (parameters := parameters) rename flag)
      (mapLiteral rename ((decoderStart .healthy).slots (.internal (.qualifier .healthy channel))))
      (mapLiteral rename ((decoderStart .faulty).slots (.internal (.qualifier .faulty channel)))) :=
  Eq.mpr (congrArg₂ (DirectionPair
    (allChannelQualifiers (parameters := parameters) rename flag).nots.cache.masks.checkedPrefix.state
    (equalFlagContext (parameters := parameters) rename flag))
    (qualifierOutput_decoderStart rename .healthy channel).symm
    (qualifierOutput_decoderStart rename .faulty channel).symm)
    ((allChannelQualifiers (parameters := parameters) rename flag).pairs channel channel.isLt)

theorem constructedDecoderQualifier_supported (rename : Nat → Fin v) (flag : Bool)
    (channel : Fin parameters.channels) :
    DirectionPairOrigin rename
      (allChannelQualifiers (parameters := parameters) rename flag).nots.cache.masks.checkedPrefix
      (constructedDecoderQualifier rename flag channel) :=
  directionPairOrigin_mpr rename
    (allChannelQualifiers (parameters := parameters) rename flag).nots.cache.masks.checkedPrefix
    (qualifierOutput_decoderStart rename .healthy channel)
    (qualifierOutput_decoderStart rename .faulty channel) _
    ((allChannelQualifiers (parameters := parameters) rename flag).pairs channel channel.isLt)
    ((allChannelQualifiers_supported rename flag).2 channel channel.isLt)

end Controller.NativeProof.SourceQualifierSchedule
