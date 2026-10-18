module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.SourceStagePolarity

@[expose] public section

/-! The equal-first-flag schedule starts from actual original mask equations.
The table stores checked stronger directional clauses at one accepted prefix.
Original support is recorded syntactically by source producer occurrences. -/
namespace Controller.NativeProof.SourceBusSchedule
open Controller.Native Controller.Native.SourceController Controller.CNF
open Controller.Resolution Controller.Resolution.Cases
open Controller.NativeProof.FoldProjection Controller.NativeProof.SourceFoldProjection
open Controller.NativeProof.SourceCongruence Controller.NativeProof.SourceSlotFrames
open Controller.NativeProof.SourceFoldOccurrences
open Controller.NativeProof.SourceRoleFrames Controller.NativeProof.SourceStageCongruence
variable {parameters : Parameters} {v : Nat}

def equalFlagContext (rename : Nat → Fin v) (flag : Bool) : Clause (Fin v) :=
  [assignmentGuard (mapLiteral rename (sourceRoleMap parameters (.internal (.flag .healthy parameters.firstBus)))) flag,
   assignmentGuard (mapLiteral rename (sourceRoleMap parameters (.internal (.flag .faulty parameters.firstBus)))) flag]

theorem firstFlagContext_eq (rename : Nat → Fin v) (channel : Fin parameters.channels) (flag : Bool) :
    firstFlagContext rename channel flag = equalFlagContext (parameters := parameters) rename flag := by
  unfold firstFlagContext equalFlagContext
  rw [maskFlag_eq_sourceRoleMap, maskFlag_eq_sourceRoleMap]

def sourceMask (rename : Nat → Fin v) (side : Side) (bus : Fin parameters.buses)
    (channel : Fin parameters.channels) : Literal (Fin v) :=
  mapLiteral rename (sourceRoleMap parameters (.internal (.mask side bus channel)))

/-- A support ID names a concrete original mask producer and one of its four
stored rows. Assertion IDs and observation producers have no constructors. -/
def InitialMaskOriginalSupport (rename : Nat → Fin v) (id : Nat) : Prop :=
  ∃ (side : Side) (channel : Fin parameters.channels) (index : Fin 4),
    id = ((initialMaskOriginalRows rename side channel).row
      ⟨index.val, by change index.val < 4; exact index.isLt⟩).id

def TreeOriginalSupport (allowed : Nat → Prop) : CaseTree v → Prop
  | .leaf certificate => allowed certificate.rowId ∧
      ∀ reason ∈ certificate.reasons, allowed reason.rowId
  | .fork _ left right => TreeOriginalSupport allowed left ∧ TreeOriginalSupport allowed right

theorem maskCofactor_supported (rename : Nat → Fin v) (channel : Fin parameters.channels)
    (flag absent : Bool) : TreeOriginalSupport (InitialMaskOriginalSupport (parameters := parameters) rename)
      (maskCofactorTree rename channel flag absent) := by
  refine ⟨?_, ?_⟩
  · exact ⟨maskCofactorSide flag absent, channel, maskCofactorIndex flag absent, rfl⟩
  · simp [maskCofactorTree]

theorem initialMaskFlagTree_supported (rename : Nat → Fin v) (channel : Fin parameters.channels)
    (flag : Bool) : TreeOriginalSupport (InitialMaskOriginalSupport (parameters := parameters) rename)
      (initialMaskFlagTree rename channel flag) :=
  ⟨maskCofactor_supported rename channel flag true, maskCofactor_supported rename channel flag false⟩

theorem reverseMaskCofactor_supported (rename : Nat → Fin v) (channel : Fin parameters.channels)
    (flag absent : Bool) : TreeOriginalSupport (InitialMaskOriginalSupport (parameters := parameters) rename)
      (reverseMaskCofactorTree rename channel flag absent) := by
  refine ⟨?_, ?_⟩
  · exact ⟨reverseMaskSide flag absent, channel, maskCofactorIndex flag absent, rfl⟩
  · simp [reverseMaskCofactorTree]

theorem reverseMaskFlagTree_supported (rename : Nat → Fin v) (channel : Fin parameters.channels)
    (flag : Bool) : TreeOriginalSupport (InitialMaskOriginalSupport (parameters := parameters) rename)
      (reverseMaskFlagTree rename channel flag) :=
  ⟨reverseMaskCofactor_supported rename channel flag true, reverseMaskCofactor_supported rename channel flag false⟩

/-- An emitted trace may reference an allowed original occurrence or an earlier
emitted row. This condition is syntactic and does not use entailment. -/
def TraceOriginalSupport (originalCount : Nat) (allowed : Nat → Prop) (steps : List (Step v)) : Prop :=
  ∀ step ∈ steps, ∀ parent ∈ [step.left, step.right],
    (parent ≤ originalCount → allowed parent) ∧
    (originalCount < parent → ∃ earlier ∈ steps, earlier.id = parent ∧ earlier.id < step.id)

def AllParentsAllowed (allowed : Nat → Prop) (steps : List (Step v)) : Prop :=
  ∀ step ∈ steps, allowed step.left ∧ allowed step.right

theorem allParentsAllowed_append (allowed : Nat → Prop) (first second : List (Step v))
    (one : AllParentsAllowed allowed first) (two : AllParentsAllowed allowed second) :
    AllParentsAllowed allowed (first ++ second) := by
  intro step member
  rcases List.mem_append.mp member with old | added
  · exact one step old
  · exact two step added

theorem merge_parents_allowed (state : State v) (leftId rightId : Nat)
    (pivot : Literal (Fin v)) (left right : Clause (Fin v)) (allowed : Nat → Prop)
    (leftAllowed : allowed leftId) (rightAllowed : allowed rightId) :
    AllParentsAllowed allowed (merge state leftId rightId pivot left right).steps := by
  unfold merge
  split
  · intro step member; cases member
  · split
    · intro step member; cases member
    · intro step member
      have equal := List.mem_singleton.mp member
      subst step
      exact ⟨leftAllowed, rightAllowed⟩

theorem initialMaskTraceParents (rename : Nat → Fin v) (channel : Fin parameters.channels)
    (flag : Bool) (state : State v) : AllParentsAllowed (InitialMaskOriginalSupport (parameters := parameters) rename)
      (compileTree state (initialMaskFlagTree rename channel flag)).steps := by
  have one : InitialMaskOriginalSupport (parameters := parameters) rename (maskCofactorRow rename channel flag true).id :=
    ⟨maskCofactorSide flag true, channel, maskCofactorIndex flag true, rfl⟩
  have two : InitialMaskOriginalSupport (parameters := parameters) rename (maskCofactorRow rename channel flag false).id :=
    ⟨maskCofactorSide flag false, channel, maskCofactorIndex flag false, rfl⟩
  simpa only [initialMaskFlagTree, maskCofactorTree, compileTree, RUP.compileReasons,
    List.nil_append] using merge_parents_allowed state _ _ (maskAbsent rename .healthy channel)
      (maskCofactorClause rename channel flag true) (maskCofactorClause rename channel flag false)
      (InitialMaskOriginalSupport (parameters := parameters) rename) one two

theorem reverseMaskTraceParents (rename : Nat → Fin v) (channel : Fin parameters.channels)
    (flag : Bool) (state : State v) : AllParentsAllowed (InitialMaskOriginalSupport (parameters := parameters) rename)
      (compileTree state (reverseMaskFlagTree rename channel flag)).steps := by
  have one : InitialMaskOriginalSupport (parameters := parameters) rename (reverseMaskRow rename channel flag true).id :=
    ⟨reverseMaskSide flag true, channel, maskCofactorIndex flag true, rfl⟩
  have two : InitialMaskOriginalSupport (parameters := parameters) rename (reverseMaskRow rename channel flag false).id :=
    ⟨reverseMaskSide flag false, channel, maskCofactorIndex flag false, rfl⟩
  simpa only [reverseMaskFlagTree, reverseMaskCofactorTree, compileTree, RUP.compileReasons,
    List.nil_append] using merge_parents_allowed state _ _ (maskAbsent rename .healthy channel)
      (reverseMaskClause rename channel flag true) (reverseMaskClause rename channel flag false)
      (InitialMaskOriginalSupport (parameters := parameters) rename) one two

theorem initialMaskSupport_bound (rename : Nat → Fin v) (id : Nat)
    (support : InitialMaskOriginalSupport (parameters := parameters) rename id) :
    id ≤ (initialState (relabel rename (SourceController.formula parameters))).lastId := by
  rcases support with ⟨side, channel, index, same⟩
  rw [same]
  exact ((initialMaskOriginalRows rename side channel).row
    ⟨index.val, by change index.val < 4; exact index.isLt⟩).bound

theorem initialMask_trace_support (rename : Nat → Fin v) (steps : List (Step v))
    (parents : AllParentsAllowed (InitialMaskOriginalSupport (parameters := parameters) rename) steps) :
    TraceOriginalSupport (initialState (relabel rename (SourceController.formula parameters))).lastId
      (InitialMaskOriginalSupport (parameters := parameters) rename) steps := by
  intro step member parent parentMem
  have supported : InitialMaskOriginalSupport (parameters := parameters) rename parent := by
    have both := parents step member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at parentMem
    rcases parentMem with same | same
    · exact same.symm ▸ both.1
    · exact same.symm ▸ both.2
  refine ⟨fun _ => supported, ?_⟩
  intro larger
  have bound := initialMaskSupport_bound rename parent supported
  omega

structure DirectionPair (state : State v) (context : Clause (Fin v)) (left right : Literal (Fin v)) where
  forward : GuardedTransfer state context left right
  backward : GuardedTransfer state context right left

def DirectionPair.afterTrace (pair : DirectionPair state context left right) (next : State v)
    (steps : List (Step v)) (checked : runSteps state steps = some next) : DirectionPair next context left right :=
  ⟨pair.forward.afterTrace next steps checked, pair.backward.afterTrace next steps checked⟩

structure InitialMaskProjection (rename : Nat → Fin v) (flag : Bool)
    (channel : Fin parameters.channels) (start : SourcePrefix (parameters := parameters) rename) where
  state : State v
  steps : List (Step v)
  checked : runSteps start.state steps = some state
  pair : DirectionPair state (equalFlagContext (parameters := parameters) rename flag)
    (sourceMask rename .healthy parameters.firstBus channel) (sourceMask rename .faulty parameters.firstBus channel)
  count : steps.length ≤ 2
  parents : AllParentsAllowed (InitialMaskOriginalSupport (parameters := parameters) rename) steps

/-- Both directions are constructed from the actual original mask case trees,
then transported to the same accepted state. No availability is an input. -/
def initialMaskProjection (rename : Nat → Fin v) (flag : Bool) (channel : Fin parameters.channels)
    (start : SourcePrefix (parameters := parameters) rename) : InitialMaskProjection rename flag channel start := by
  let base := initialState (relabel rename (SourceController.formula parameters))
  let firstTree := initialMaskFlagTree rename channel flag
  let first := compileTree start.state firstTree
  have firstRun := compileTree_run firstTree base start.state
    (runSteps_lastId_le start.checked)
    (fun id bound => runSteps_preserves_old_rows start.checked id bound) _
    (initialMaskFlagTree_valid rename channel flag)
  have prefixFirst : runSteps base (start.steps ++ first.steps) = some first.state := by
    rw [runSteps_append, start.checked]
    exact firstRun.1
  let secondTree := reverseMaskFlagTree rename channel flag
  let second := compileTree first.state secondTree
  have secondRun := compileTree_run secondTree base first.state
    (runSteps_lastId_le prefixFirst)
    (fun id bound => runSteps_preserves_old_rows prefixFirst id bound) _
    (reverseMaskFlagTree_valid rename channel flag)
  let forwardRow : AvailableSubclause first.state
      (firstFlagContext rename channel flag ++ [negate (maskOutput rename .healthy channel), maskOutput rename .faulty channel]) :=
    ⟨first.clause, ⟨first.rowId, firstRun.2.1, firstRun.2.2.1⟩, firstRun.2.2.2⟩
  let forward := FoldProjection.afterTrace forwardRow second.state second.steps secondRun.1
  let backward : AvailableSubclause second.state
      (firstFlagContext rename channel flag ++ [maskOutput rename .healthy channel, negate (maskOutput rename .faulty channel)]) :=
    ⟨second.clause, ⟨second.rowId, secondRun.2.1, secondRun.2.2.1⟩, secondRun.2.2.2⟩
  refine ⟨second.state, first.steps ++ second.steps, ?_, ⟨.derived (retarget forward ?_),
    .derived (retarget backward ?_)⟩, ?_, ?_⟩
  · rw [runSteps_append, firstRun.1]
    exact secondRun.1
  · intro literal member
    have old := member
    simpa only [firstFlagContext_eq, maskOutput_eq_sourceRoleMap, sourceMask] using old
  · intro literal member
    have old := member
    simp only [firstFlagContext_eq, maskOutput_eq_sourceRoleMap, sourceMask,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at old ⊢
    aesop
  · have firstCount : first.steps.length ≤ 1 := by
      change (compileTree start.state firstTree).steps.length ≤ 1
      have budget : inferenceBudget firstTree = 1 := rfl
      have actual := compileTree_count_le firstTree start.state
      rw [budget] at actual
      exact actual
    have secondCount : second.steps.length ≤ 1 := by
      change (compileTree first.state secondTree).steps.length ≤ 1
      have budget : inferenceBudget secondTree = 1 := rfl
      have actual := compileTree_count_le secondTree first.state
      rw [budget] at actual
      exact actual
    simp only [List.length_append]
    omega
  · exact allParentsAllowed_append _ _ _ (initialMaskTraceParents rename channel flag start.state)
      (reverseMaskTraceParents rename channel flag first.state)

structure InitialMaskTable (rename : Nat → Fin v) (flag : Bool) (done : List (Fin parameters.channels)) where
  checkedPrefix : SourcePrefix (parameters := parameters) rename
  directions : ∀ channel ∈ done, DirectionPair checkedPrefix.state (equalFlagContext (parameters := parameters) rename flag)
    (sourceMask rename .healthy parameters.firstBus channel) (sourceMask rename .faulty parameters.firstBus channel)
  count : checkedPrefix.steps.length ≤ 2 * done.length
  parents : AllParentsAllowed (InitialMaskOriginalSupport (parameters := parameters) rename) checkedPrefix.steps

def initialMaskTableStep (rename : Nat → Fin v) (flag : Bool) (done : List (Fin parameters.channels))
    (table : InitialMaskTable rename flag done) (channel : Fin parameters.channels) :
    InitialMaskTable rename flag (channel :: done) := by
  let next := initialMaskProjection rename flag channel table.checkedPrefix
  let nextPrefix := table.checkedPrefix.extend next.state next.steps next.checked
  refine ⟨nextPrefix, ?_, ?_, ?_⟩
  · intro query member
    by_cases same : query = channel
    · subst query
      exact next.pair
    · have old : query ∈ done := (List.mem_cons.mp member).resolve_left same
      exact (table.directions query old).afterTrace next.state next.steps next.checked
  · have before := table.count
    have added := next.count
    change (table.checkedPrefix.steps ++ next.steps).length ≤ 2 * (channel :: done).length
    simp only [List.length_append, List.length_cons]
    omega
  · exact allParentsAllowed_append _ _ _ table.parents next.parents

def buildInitialMaskTable (rename : Nat → Fin v) (flag : Bool) :
    (channels : List (Fin parameters.channels)) → InitialMaskTable rename flag channels
  | [] => ⟨SourcePrefix.initial rename,
      (by intro channel member; exact False.elim (List.not_mem_nil member)),
      (by simp [SourcePrefix.initial]),
      (by intro step member; exact False.elim (List.not_mem_nil member))⟩
  | channel :: channels => initialMaskTableStep rename flag channels (buildInitialMaskTable rename flag channels) channel

/-- A complete later stage changes only masks belonging to its own bus.
This frame is independent of the values or sharing of its folded inputs. -/
theorem laterBus_mask_other (side querySide : Side) (bus queryBus : Fin parameters.buses)
    (channel : Fin parameters.channels) (different : queryBus ≠ bus) (cursor : Cursor parameters) :
    (laterBus parameters side bus cursor).slots (.internal (.mask querySide queryBus channel)) =
      cursor.slots (.internal (.mask querySide queryBus channel)) := by
  unfold laterBus
  rw [foldl_slot _ (.internal (.mask querySide queryBus channel))
    (fun current index => by simp [Cursor.emitNative, Cursor.emit, Cursor.assign, different])]
  rw [foldNative_other _ _ _ _ _ (by simp)]
  apply foldl_slot
  intro current index
  apply foldNative_other
  simp

theorem laterBus_mask_otherSide (side querySide : Side) (bus queryBus : Fin parameters.buses)
    (channel : Fin parameters.channels) (different : querySide ≠ side) (cursor : Cursor parameters) :
    (laterBus parameters side bus cursor).slots (.internal (.mask querySide queryBus channel)) =
      cursor.slots (.internal (.mask querySide queryBus channel)) := by
  unfold laterBus
  rw [foldl_slot _ (.internal (.mask querySide queryBus channel))
    (fun current index => by simp [Cursor.emitNative, Cursor.emit, Cursor.assign, different])]
  rw [foldNative_other _ _ _ _ _ (by simp)]
  apply foldl_slot
  intro current index
  apply foldNative_other
  simp

theorem laterBuses_mask_frame (side querySide : Side) (queryBus : Fin parameters.buses)
    (channel : Fin parameters.channels) (values : List (Fin parameters.buses))
    (absent : queryBus ∉ values) (cursor : Cursor parameters) :
    (values.foldl (fun current bus => laterBus parameters side bus current) cursor).slots
      (.internal (.mask querySide queryBus channel)) = cursor.slots (.internal (.mask querySide queryBus channel)) := by
  apply foldl_slot_mem
  intro current bus member
  apply laterBus_mask_other
  intro same
  exact absent (same.symm ▸ member)

/-- Term allocation preserves every earlier mask and every primary input.
Thus the consumer sees exactly the prefix table's physical mask handles. -/
theorem termStep_mask_frame (side querySide : Side) (bus queryBus : Fin parameters.buses)
    (index channel : Fin parameters.channels) (cursor : Cursor parameters) :
    (termStep side bus cursor index).slots (.internal (.mask querySide queryBus channel)) =
      cursor.slots (.internal (.mask querySide queryBus channel)) := by
  apply foldNative_other
  simp

theorem busTerms_mask_frame (side querySide : Side) (bus queryBus : Fin parameters.buses)
    (channel : Fin parameters.channels) (cursor : Cursor parameters) :
    (busTerms side bus cursor).slots (.internal (.mask querySide queryBus channel)) =
      cursor.slots (.internal (.mask querySide queryBus channel)) :=
  foldl_slot _ _ (fun current index => termStep_mask_frame side querySide bus queryBus index channel current) _ cursor

theorem termStep_primary_frame (side : Side) (bus : Fin parameters.buses)
    (channel : Fin parameters.channels) (primary : PrimaryRole parameters.channels parameters.buses)
    (cursor : Cursor parameters) :
    (termStep side bus cursor channel).slots (.primary primary) = cursor.slots (.primary primary) := by
  apply foldNative_other
  simp

/-- The physical cursor at any later-bus occurrence still contains the first
mask handle used to seed the certificate table. -/
theorem busBefore_first_mask (rename : Nat → Fin v) (side : Side)
    (position : Fin (laterBuses (parameters := parameters)).length) (channel : Fin parameters.channels) :
    mapLiteral rename ((busBefore side position).slots (.internal (.mask side parameters.firstBus channel))) =
      sourceMask rename side parameters.firstBus channel := by
  have frame : (busBefore side position).slots (.internal (.mask side parameters.firstBus channel)) =
      (initialMasks parameters side (tailStart side)).slots (.internal (.mask side parameters.firstBus channel)) := by
    unfold busBefore occurrenceCursor
    apply foldl_slot_mem
    intro current bus member
    apply laterBus_mask_other
    have all : bus ∈ laterBuses (parameters := parameters) := List.mem_of_mem_take member
    have nonzero : bus.val ≠ 0 := by simpa [laterBuses] using (List.mem_filter.mp all).2
    intro same
    apply nonzero
    simpa [← same, Parameters.firstBus]
  rw [frame, initialMasks_output]
  simpa only [maskOutput, sourceMask] using maskOutput_eq_sourceRoleMap rename side channel

theorem termBefore_mask (side querySide : Side)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (queryBus : Fin parameters.buses) (index channel : Fin parameters.channels) :
    (termBefore side position index).slots (.internal (.mask querySide queryBus channel)) =
      (busBefore side position).slots (.internal (.mask querySide queryBus channel)) := by
  unfold termBefore occurrenceCursor
  apply foldl_slot
  intro current selected
  exact termStep_mask_frame side querySide _ queryBus selected channel current

theorem termBefore_first_mask (rename : Nat → Fin v) (side : Side)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (index channel : Fin parameters.channels) :
    mapLiteral rename ((termBefore side position index).slots (.internal (.mask side parameters.firstBus channel))) =
      sourceMask rename side parameters.firstBus channel := by
  rw [termBefore_mask]
  exact busBefore_first_mask rename side position channel

/-- The completed seed is constructive for every channel, including arbitrary
positive channel counts supplied by the controller parameters. -/
def firstBusTable (rename : Nat → Fin v) (flag : Bool) :
    InitialMaskTable (parameters := parameters) rename flag (List.finRange parameters.channels) :=
  buildInitialMaskTable rename flag (List.finRange parameters.channels)

theorem firstBusTable_count (rename : Nat → Fin v) (flag : Bool) :
    (firstBusTable (parameters := parameters) rename flag).checkedPrefix.steps.length ≤ 2 * parameters.channels := by
  simpa only [List.length_finRange] using (firstBusTable (parameters := parameters) rename flag).count

theorem firstBusTable_support (rename : Nat → Fin v) (flag : Bool) :
    TraceOriginalSupport (initialState (relabel rename (SourceController.formula parameters))).lastId
      (InitialMaskOriginalSupport (parameters := parameters) rename) (firstBusTable (parameters := parameters) rename flag).checkedPrefix.steps :=
  initialMask_trace_support rename _ (firstBusTable (parameters := parameters) rename flag).parents

/-- A stage boundary is the exact source list prefix for each copy. -/
def stagesBefore (side : Side) (count : Nat) : Cursor parameters :=
  ((laterBuses (parameters := parameters)).take count).foldl
    (fun cursor bus => laterBus parameters side bus cursor)
    (initialMasks parameters side (tailStart side))

theorem busBefore_eq_stagesBefore (side : Side)
    (position : Fin (laterBuses (parameters := parameters)).length) :
    busBefore side position = stagesBefore (parameters := parameters) side position.val := rfl

theorem stagesBefore_succ (side : Side)
    (position : Fin (laterBuses (parameters := parameters)).length) :
    stagesBefore (parameters := parameters) side (position.val + 1) =
      laterBus parameters side (laterBuses (parameters := parameters))[position.val]
        (stagesBefore (parameters := parameters) side position.val) := by
  unfold stagesBefore
  rw [List.take_succ_eq_append_getElem position.isLt, List.foldl_append]
  rfl

/-- The mask emitted for a channel is retained by the remaining channels of
that same bus; its physical handle is the selected original emission output. -/
theorem laterBus_mask_output (side : Side)
    (position : Fin (laterBuses (parameters := parameters)).length) (channel : Fin parameters.channels) :
    (laterBus parameters side (laterBuses (parameters := parameters))[position.val] (busBefore side position)).slots
      (.internal (.mask side (laterBuses (parameters := parameters))[position.val] channel)) =
      ((laterMaskBefore side position channel).lastID + 1, true) := by
  let values := List.finRange parameters.channels
  let bus := (laterBuses (parameters := parameters))[position.val]
  have bound : channel.val < values.length := by simpa [values] using channel.isLt
  have split := positional_decomposition values ⟨channel.val, bound⟩
  have decomposition : values = values.take channel.val ++ channel :: values.drop (channel.val + 1) := by
    simpa [values] using split
  have unique : (values.take channel.val ++ channel :: values.drop (channel.val + 1)).Nodup := by
    rw [← decomposition]
    exact List.nodup_finRange parameters.channels
  have absent : channel ∉ values.drop (channel.val + 1) :=
    (List.nodup_cons.mp (List.nodup_append.mp unique).2.1).1
  change (values.foldl (busMaskStep side bus) (busFlag side bus (busBefore side position))).slots _ = _
  rw [decomposition, List.foldl_append, List.foldl_cons]
  rw [foldl_slot_mem _ (.internal (.mask side bus channel)) _ (by
    intro current index member
    have different : index ≠ channel := by
      intro equal
      exact absent (equal ▸ member)
    simp [busMaskStep, Cursor.emitNative, Cursor.emit, Cursor.assign, different, Ne.symm different])]
  simp [busMaskStep, laterMaskBefore, laterAbsentBefore, occurrenceCursor,
    Cursor.emitNative, Cursor.emit, Cursor.assign, values, bus]

theorem stagesBefore_current_mask (rename : Nat → Fin v) (side : Side)
    (position : Fin (laterBuses (parameters := parameters)).length) (channel : Fin parameters.channels) :
    mapLiteral rename ((stagesBefore (parameters := parameters) side (position.val + 1)).slots
      (.internal (.mask side (laterBuses (parameters := parameters))[position.val] channel))) =
      mapLiteral rename ((laterMaskBefore side position channel).lastID + 1, true) := by
  rw [stagesBefore_succ, ← busBefore_eq_stagesBefore, laterBus_mask_output]

/-- This table's endpoints are physical source-prefix handles. Its final
constructor must derive all fields rather than accept a native availability map. -/
structure BusMaskTable (rename : Nat → Fin v) (flag : Bool) (count : Nat) where
  checkedPrefix : SourcePrefix (parameters := parameters) rename
  directions : ∀ bus ∈ parameters.firstBus :: (laterBuses (parameters := parameters)).take count,
    ∀ channel : Fin parameters.channels,
    DirectionPair checkedPrefix.state (equalFlagContext (parameters := parameters) rename flag)
      (mapLiteral rename ((stagesBefore (parameters := parameters) .healthy count).slots (.internal (.mask .healthy bus channel))))
      (mapLiteral rename ((stagesBefore (parameters := parameters) .faulty count).slots (.internal (.mask .faulty bus channel))))

theorem stagesBefore_zero_first_mask (rename : Nat → Fin v) (side : Side)
    (channel : Fin parameters.channels) :
    mapLiteral rename ((stagesBefore (parameters := parameters) side 0).slots
      (.internal (.mask side parameters.firstBus channel))) = sourceMask rename side parameters.firstBus channel := by
  change mapLiteral rename ((initialMasks parameters side (tailStart side)).slots _) = _
  rw [initialMasks_output]
  simpa only [maskOutput, sourceMask] using maskOutput_eq_sourceRoleMap rename side channel

def busMaskTableInitial (rename : Nat → Fin v) (flag : Bool) : BusMaskTable (parameters := parameters) rename flag 0 := by
  let seed := firstBusTable (parameters := parameters) rename flag
  refine ⟨seed.checkedPrefix, ?_⟩
  intro bus member channel
  have same : bus = parameters.firstBus := by simpa using member
  subst bus
  rw [stagesBefore_zero_first_mask, stagesBefore_zero_first_mask]
  exact seed.directions channel (by simp)

/-- Every earlier bus read by a term already belongs to the actual completed
prefix, including the separately initialized first bus. -/
theorem earlier_bus_covered (position : Fin (laterBuses (parameters := parameters)).length)
    (earlier : Fin parameters.buses)
    (before : earlier < (laterBuses (parameters := parameters))[position.val]) :
    earlier ∈ parameters.firstBus :: (laterBuses (parameters := parameters)).take position.val := by
  by_cases zero : earlier.val = 0
  · have same : earlier = parameters.firstBus := Fin.ext (by simpa [Parameters.firstBus] using zero)
    simp [same]
  · have member : earlier ∈ laterBuses (parameters := parameters) := by simp [laterBuses, zero]
    have split := positional_decomposition (laterBuses (parameters := parameters)) position
    have sorted : (laterBuses (parameters := parameters)).Pairwise (· < ·) :=
      (List.pairwise_lt_finRange parameters.buses).filter _
    rw [split] at member sorted
    rcases List.mem_append.mp member with prior | rest
    · exact List.mem_cons_of_mem _ prior
    · rcases List.mem_cons.mp rest with same | after
      · exact False.elim ((ne_of_lt before) same)
      · have larger := (List.pairwise_cons.mp (List.pairwise_append.mp sorted).2.1).1 earlier after
        exact False.elim (lt_asymm before larger)

theorem tailStart_rootsExact (side : Side) : (tailStart (parameters := parameters) side).RootsExact := by
  cases side with
  | healthy => exact interface_rootsExact parameters
  | faulty => exact tail_rootsExact parameters .healthy _ (interface_rootsExact parameters)

theorem busBefore_rootsExact (side : Side)
    (position : Fin (laterBuses (parameters := parameters)).length) : (busBefore side position).RootsExact := by
  unfold busBefore occurrenceCursor
  apply rootsExact_foldl
  · intro current bus roots
    exact laterBus_rootsExact parameters side bus current roots
  · exact initialMasks_rootsExact parameters side _ (tailStart_rootsExact side)

theorem termBefore_rootsExact (side : Side)
    (position : Fin (laterBuses (parameters := parameters)).length) (channel : Fin parameters.channels) :
    (termBefore side position channel).RootsExact := by
  unfold termBefore occurrenceCursor
  apply rootsExact_foldl
  · intro current index roots
    exact current.rootsExact_foldNative_internal _ _ _ roots
  · exact busBefore_rootsExact side position

inductive TermSource (parameters : Parameters) where
  | enable
  | request
  | mask (bus : Fin parameters.buses)

def termSources (position : Fin (laterBuses (parameters := parameters)).length) : List (TermSource parameters) :=
  [.enable, .request] ++ (((List.finRange parameters.buses).filter
    (fun earlier => earlier < (laterBuses (parameters := parameters))[position.val])).map .mask)

def termSourceLiteral (rename : Nat → Fin v) (side : Side)
    (position : Fin (laterBuses (parameters := parameters)).length) (channel : Fin parameters.channels)
    (source : TermSource parameters) : Literal (Fin v) :=
  let cursor := termBefore side position channel
  mapLiteral rename (match source with
    | .enable => cursor.slots (.primary (.enable channel))
    | .request => cursor.slots (.primary (.request (laterBuses (parameters := parameters))[position.val] channel))
    | .mask bus => cursor.slots (.internal (.mask side bus channel)))

def termSourcePair (rename : Nat → Fin v)
    (position : Fin (laterBuses (parameters := parameters)).length) (channel : Fin parameters.channels)
    (source : TermSource parameters) : Literal (Fin v) × Literal (Fin v) :=
  (termSourceLiteral rename .healthy position channel source,
   termSourceLiteral rename .faulty position channel source)

theorem termSources_inputs (rename : Nat → Fin v) (side : Side)
    (position : Fin (laterBuses (parameters := parameters)).length) (channel : Fin parameters.channels) :
    (termSources position).map (termSourceLiteral rename side position channel) =
      (laterTermInputs side position channel).map (mapLiteral rename) := by
  simp only [termSources, termSourceLiteral, laterTermInputs, List.map_append,
    List.map_cons, List.map_nil, List.map_map, Function.comp_def]

theorem termSources_pairs (rename : Nat → Fin v)
    (position : Fin (laterBuses (parameters := parameters)).length) (channel : Fin parameters.channels) :
    laterTermPairs rename position channel = (termSources position).map (termSourcePair rename position channel) := by
  unfold laterTermPairs
  rw [← termSources_inputs rename .healthy position channel, ← termSources_inputs rename .faulty position channel]
  exact List.zip_map'

/-- Every term input direction is constructed from an actual shared root or
from the completed mask table at the exact source-prefix boundary. -/
def termSourceDirection (rename : Nat → Fin v) (flag : Bool)
    (position : Fin (laterBuses (parameters := parameters)).length) (channel : Fin parameters.channels)
    (table : BusMaskTable (parameters := parameters) rename flag position.val)
    (source : TermSource parameters) (member : source ∈ termSources position) :
    DirectionPair table.checkedPrefix.state (equalFlagContext (parameters := parameters) rename flag)
      (termSourceLiteral rename .healthy position channel source) (termSourceLiteral rename .faulty position channel source) := by
  cases source with
  | enable =>
      have same : termSourceLiteral rename .healthy position channel .enable =
          termSourceLiteral rename .faulty position channel .enable := by
        dsimp only [termSourceLiteral]
        rw [(termBefore_rootsExact .healthy position channel).1 channel,
          (termBefore_rootsExact .faulty position channel).1 channel]
      exact ⟨.identity same, .identity same.symm⟩
  | request =>
      have same : termSourceLiteral rename .healthy position channel .request =
          termSourceLiteral rename .faulty position channel .request := by
        dsimp only [termSourceLiteral]
        rw [(termBefore_rootsExact .healthy position channel).2,
          (termBefore_rootsExact .faulty position channel).2]
      exact ⟨.identity same, .identity same.symm⟩
  | mask bus =>
      have before : bus < (laterBuses (parameters := parameters))[position.val] := by
        simpa [termSources] using member
      have certificate := table.directions bus (earlier_bus_covered position bus before) channel
      simpa only [termSourceLiteral, termBefore_mask, busBefore_eq_stagesBefore] using certificate

def termPairDirection (rename : Nat → Fin v) (flag : Bool)
    (position : Fin (laterBuses (parameters := parameters)).length) (channel : Fin parameters.channels)
    (table : BusMaskTable (parameters := parameters) rename flag position.val)
    (pair : Literal (Fin v) × Literal (Fin v)) (member : pair ∈ laterTermPairs rename position channel) :
    DirectionPair table.checkedPrefix.state (equalFlagContext (parameters := parameters) rename flag) pair.1 pair.2 := by
  have represented : pair ∈ (termSources position).map (termSourcePair rename position channel) := by
    simpa only [← termSources_pairs rename position channel] using member
  let selected := mappedChoice (termSourcePair rename position channel) pair (termSources position) represented
  have certificate := termSourceDirection rename flag position channel table selected.val selected.property.1
  have same := selected.property.2
  simpa only [← same, termSourcePair] using certificate

/-- The forward term trace consumes the constructed table input directions;
all AND rows are selected by the frozen actual source allocator adapter. -/
def laterTermFromTable (rename : Nat → Fin v) (flag : Bool)
    (position : Fin (laterBuses (parameters := parameters)).length) (channel : Fin parameters.channels)
    (table : BusMaskTable (parameters := parameters) rename flag position.val) :
    SubclauseProjection table.checkedPrefix.state
      (equalFlagContext (parameters := parameters) rename flag ++
        [negate (laterTermOutput rename .healthy position channel), laterTermOutput rename .faulty position channel])
      (6 * (laterTermPairs rename position channel).length) :=
  laterTermCongruence rename (equalFlagContext (parameters := parameters) rename flag) position channel table.checkedPrefix
    (fun pair member => (termPairDirection rename flag position channel table pair member).forward)

end Controller.NativeProof.SourceBusSchedule
