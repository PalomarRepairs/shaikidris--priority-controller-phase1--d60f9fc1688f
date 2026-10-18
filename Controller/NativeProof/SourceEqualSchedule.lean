module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.SourceMixedScheduleFoundation

@[expose] public section

/-! Causal original-row support for the actual equal-first-flag source schedule. -/
namespace Controller.NativeProof.SourceEqualSchedule
open Controller.CNF Controller.Resolution Controller.Native Controller.Native.SourceController
open Controller.NativeProof.FoldProjection Controller.NativeProof.SourceFoldProjection
open Controller.NativeProof.SourceCongruence Controller.NativeProof.SourceStageCongruence
open Controller.NativeProof.SourceBusSchedule Controller.NativeProof.SourceBusAdvance
open Controller.NativeProof.SourceFoldOccurrences Controller.NativeProof.SourceFoldOwners
open Controller.NativeProof.SourceQualifierOccurrences Controller.NativeProof.SourceFoldProvenance
open Controller.NativeProof.SourceMismatchHandles Controller.NativeProof.SourceMixedSchedule
open Controller.NativeProof.SourceStagePolarity
open Controller.NativeProof.SourceSlotFrames
variable {parameters : Parameters} {v : Nat}

def GuardedTransferOrigin (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    {context : Clause (Fin v)} {input output : Literal (Fin v)}
    (transfer : GuardedTransfer prefixState.state context input output) : Prop :=
  match transfer with
  | .identity _ => True
  | .derived row => ResultOrigin (formula parameters).clauses.size
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      prefixState.steps row.row.id

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

theorem initial_mask_before_controller (side : Side) (channel : Fin parameters.channels) :
    EntriesBefore (initialMaskStep side (initialMaskBefore side channel) channel)
      (controller parameters) := by
  have bound : channel.val < (List.finRange parameters.channels).length := by
    simpa using channel.isLt
  have split := positional_decomposition (List.finRange parameters.channels) ⟨channel.val, bound⟩
  have decomposition : List.finRange parameters.channels =
      (List.finRange parameters.channels).take channel.val ++ channel ::
        (List.finRange parameters.channels).drop (channel.val + 1) := by simpa using split
  have selected := occurrence_before_of_eq (initialMaskStep side)
    (fun cursor index => emitNative_before cursor _ _) (tailStart side)
    (List.finRange parameters.channels) _ _ channel decomposition
  exact selected.trans ((initialMasks_before_tail side).trans (tail_end_before_controller side))

theorem initialMaskOriginalRows_allowed (rename : Nat → Fin v)
    (side : Side) (channel : Fin parameters.channels) :
    ProducerOriginals
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      (initialMaskOriginalRows rename side channel) := by
  have actual := actualEmitRows_allowed rename (initialMaskBefore side channel)
    (.internal (.mask side parameters.firstBus channel))
    (.xor ((initialMaskBefore side channel).slots (.internal (.flag side parameters.firstBus)))
      ((initialMaskBefore side channel).slots (.internal (.absent side parameters.firstBus channel))))
    (initial_mask_before_controller side channel)
  simpa only [initialMaskOriginalRows, id] using actual

theorem initialMaskOriginalSupport_allowed (rename : Nat → Fin v) (id : Nat)
    (original : InitialMaskOriginalSupport (parameters := parameters) rename id) :
    Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename id := by
  rcases original with ⟨side, channel, index, same⟩
  rw [same]
  exact initialMaskOriginalRows_allowed rename side channel
    ⟨index.val, by change index.val < 4; exact index.isLt⟩

theorem traceOriginalSupport_mono (originalCount : Nat) (one two : Nat → Prop)
    (steps : List (Step v)) (included : ∀ id, one id → two id)
    (supported : TraceOriginalSupport originalCount one steps) :
    TraceOriginalSupport originalCount two steps := by
  intro step member parent parentMember
  have old := supported step member parent parentMember
  exact ⟨fun bound => included parent (old.1 bound), old.2⟩

theorem firstBusTable_trace_supported (rename : Nat → Fin v) (flag : Bool) :
    PrefixOriginalSupport rename (firstBusTable (parameters := parameters) rename flag).checkedPrefix := by
  have old := firstBusTable_support (parameters := parameters) rename flag
  have promoted := traceOriginalSupport_mono _ _ _ _
    (initialMaskOriginalSupport_allowed rename) old
  simpa only [PrefixOriginalSupport, initialState, relabel, Controller.CNF.OrderedFormula.relabel,
    Array.size_map] using promoted


/-- The actual contextual implication merge preserves causal parent identifiers. -/
theorem guardedChain_supported (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (context : Clause (Fin v)) (root middle output : Literal (Fin v))
    (first : AvailableSubclause prefixState.state (context ++ [negate root, middle]))
    (second : AvailableSubclause prefixState.state (context ++ [negate middle, output]))
    (supported : PrefixOriginalSupport rename prefixState)
    (firstOrigin : ResultOrigin (formula parameters).clauses.size
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      prefixState.steps first.row.id)
    (secondOrigin : ResultOrigin (formula parameters).clauses.size
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      prefixState.steps second.row.id) :
    ProjectionOriginalSupport rename prefixState
      (guardedChain prefixState.state context root middle output first second) := by
  constructor
  · exact Controller.NativeProof.SourceFoldAggregateProvenance.appendMerge_origins_supported
      (formula parameters).clauses.size
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      prefixState.steps prefixState.state second.row.id first.row.id middle second.clause first.clause
      supported (allowed_native_count_le rename) secondOrigin firstOrigin second.row.bound first.row.bound
  · exact Controller.NativeProof.SourceFoldAggregateProvenance.merge_origins
      (formula parameters).clauses.size
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      prefixState.steps prefixState.state second.row.id first.row.id middle second.clause first.clause
      secondOrigin firstOrigin (prefix_native_count_le rename prefixState)

/-- An identity transfer reuses the directional row; a derived transfer performs
its actual contextual merge. Neither branch invents an alias premise. -/
theorem guardedFromRow_supported (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (context : Clause (Fin v)) (root input output : Literal (Fin v))
    (direction : AvailableSubclause prefixState.state [negate root, input])
    (transfer : GuardedTransfer prefixState.state context input output)
    (supported : PrefixOriginalSupport rename prefixState)
    (directionOrigin : ResultOrigin (formula parameters).clauses.size
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      prefixState.steps direction.row.id)
    (transferOrigin : GuardedTransferOrigin rename prefixState transfer) :
    ProjectionOriginalSupport rename prefixState
      (guardedFromRow prefixState.state context root input output direction transfer) := by
  cases transfer with
  | identity same =>
      subst output
      constructor
      · simpa only [guardedFromRow, ProjectionOriginalSupport, PrefixOriginalSupport, List.append_nil] using supported
      · simpa only [guardedFromRow, retarget, List.append_nil] using directionOrigin
  | derived row =>
      exact guardedChain_supported rename prefixState context root input output
        (retarget direction (fun literal member => List.mem_append_right _ member)) row
        supported directionOrigin transferOrigin

theorem twoOriginalLeaves_supported (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (pivot : Literal (Fin v)) (left right : Clause (Fin v))
    (leftId rightId : Nat)
    (leftBound : leftId ≤ prefixState.state.lastId)
    (rightBound : rightId ≤ prefixState.state.lastId)
    (supported : PrefixOriginalSupport rename prefixState)
    (one : ResultOrigin (formula parameters).clauses.size
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      prefixState.steps leftId)
    (two : ResultOrigin (formula parameters).clauses.size
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      prefixState.steps rightId) :
    let tree := Controller.Resolution.Cases.CaseTree.fork pivot
      (.leaf ⟨leftId, left, []⟩) (.leaf ⟨rightId, right, []⟩)
    let actual := Controller.Resolution.Cases.compileTree prefixState.state tree
    TraceOriginalSupport (formula parameters).clauses.size
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      (prefixState.steps ++ actual.steps) ∧
    ResultOrigin (formula parameters).clauses.size
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      (prefixState.steps ++ actual.steps) actual.rowId := by
  constructor
  · exact Controller.NativeProof.SourceFoldAggregateProvenance.appendMerge_origins_supported
      (formula parameters).clauses.size
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      prefixState.steps prefixState.state leftId rightId pivot left right
      supported (allowed_native_count_le rename) one two leftBound rightBound
  · exact Controller.NativeProof.SourceFoldAggregateProvenance.merge_origins
      (formula parameters).clauses.size
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      prefixState.steps prefixState.state leftId rightId pivot left right one two
      (prefix_native_count_le rename prefixState)


/-- Both actual forward cofactor leaves are bound to original mask rows. -/
theorem initialMaskFlagTree_origins (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (channel : Fin parameters.channels) (flag : Bool)
    (supported : PrefixOriginalSupport rename prefixState) :
    let actual := Controller.Resolution.Cases.compileTree prefixState.state
      (initialMaskFlagTree rename channel flag)
    TraceOriginalSupport (formula parameters).clauses.size
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      (prefixState.steps ++ actual.steps) ∧
    ResultOrigin (formula parameters).clauses.size
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      (prefixState.steps ++ actual.steps) actual.rowId := by
  have one := initialMaskOriginalSupport_allowed rename _
    (maskCofactor_supported rename channel flag true).1
  have two := initialMaskOriginalSupport_allowed rename _
    (maskCofactor_supported rename channel flag false).1
  have leftBound := Nat.le_trans (maskCofactorRow rename channel flag true).bound
    (runSteps_lastId_le prefixState.checked)
  have rightBound := Nat.le_trans (maskCofactorRow rename channel flag false).bound
    (runSteps_lastId_le prefixState.checked)
  exact twoOriginalLeaves_supported rename prefixState (maskAbsent rename .healthy channel)
    (maskCofactorClause rename channel flag true) (maskCofactorClause rename channel flag false)
    (maskCofactorRow rename channel flag true).id (maskCofactorRow rename channel flag false).id
    leftBound rightBound supported (Or.inl one) (Or.inl two)

/-- The reverse direction uses its own two concrete original cofactor rows. -/
theorem reverseMaskFlagTree_origins (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (channel : Fin parameters.channels) (flag : Bool)
    (supported : PrefixOriginalSupport rename prefixState) :
    let actual := Controller.Resolution.Cases.compileTree prefixState.state
      (reverseMaskFlagTree rename channel flag)
    TraceOriginalSupport (formula parameters).clauses.size
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      (prefixState.steps ++ actual.steps) ∧
    ResultOrigin (formula parameters).clauses.size
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      (prefixState.steps ++ actual.steps) actual.rowId := by
  have one := initialMaskOriginalSupport_allowed rename _
    (reverseMaskCofactor_supported rename channel flag true).1
  have two := initialMaskOriginalSupport_allowed rename _
    (reverseMaskCofactor_supported rename channel flag false).1
  have leftBound := Nat.le_trans (reverseMaskRow rename channel flag true).bound
    (runSteps_lastId_le prefixState.checked)
  have rightBound := Nat.le_trans (reverseMaskRow rename channel flag false).bound
    (runSteps_lastId_le prefixState.checked)
  exact twoOriginalLeaves_supported rename prefixState (maskAbsent rename .healthy channel)
    (reverseMaskClause rename channel flag true) (reverseMaskClause rename channel flag false)
    (reverseMaskRow rename channel flag true).id (reverseMaskRow rename channel flag false).id
    leftBound rightBound supported (Or.inl one) (Or.inl two)

/-- The initial paired mask construction carries both concrete compiled results
through its complete two-direction trace. -/
theorem initialMaskProjection_origins (rename : Nat → Fin v)
    (flag : Bool) (channel : Fin parameters.channels)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (supported : PrefixOriginalSupport rename prefixState) :
    let actual := initialMaskProjection rename flag channel prefixState
    let current := prefixState.extend actual.state actual.steps actual.checked
    PrefixOriginalSupport rename current ∧ DirectionPairOrigin rename current actual.pair := by
  let base := initialState (relabel rename (formula parameters))
  let firstTree := initialMaskFlagTree rename channel flag
  let first := Controller.Resolution.Cases.compileTree prefixState.state firstTree
  have firstRun := Controller.Resolution.Cases.compileTree_run firstTree base prefixState.state
    (runSteps_lastId_le prefixState.checked)
    (fun id bound => runSteps_preserves_old_rows prefixState.checked id bound) _
    (initialMaskFlagTree_valid rename channel flag)
  let firstPrefix := prefixState.extend first.state first.steps firstRun.1
  have firstSupport := initialMaskFlagTree_origins rename prefixState channel flag supported
  have firstPrefixSupport : PrefixOriginalSupport rename firstPrefix := firstSupport.1
  let secondTree := reverseMaskFlagTree rename channel flag
  let second := Controller.Resolution.Cases.compileTree first.state secondTree
  have secondSupport := reverseMaskFlagTree_origins rename firstPrefix channel flag firstPrefixSupport
  have forwardOrigin := resultOrigin_append_right (formula parameters).clauses.size
    (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
    (prefixState.steps ++ first.steps) second.steps first.rowId firstSupport.2
  constructor
  · change TraceOriginalSupport (formula parameters).clauses.size
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      (prefixState.steps ++ (first.steps ++ second.steps))
    simpa only [firstPrefix, SourcePrefix.extend, List.append_assoc] using secondSupport.1
  · constructor
    · change ResultOrigin (formula parameters).clauses.size
        (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
        (prefixState.steps ++ (first.steps ++ second.steps)) first.rowId
      simpa only [List.append_assoc] using forwardOrigin
    · change ResultOrigin (formula parameters).clauses.size
        (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
        (prefixState.steps ++ (first.steps ++ second.steps)) second.rowId
      simpa only [firstPrefix, SourcePrefix.extend, List.append_assoc] using secondSupport.2

theorem dischargeInputs_nil_fields (state : State v) (target : Clause (Fin v))
    (conflict : AvailableSubclause state ([].map negate ++ target))
    (propagation : ∀ input ∈ ([] : List (Literal (Fin v))),
      AvailableSubclause state (target ++ [input])) :
    (dischargeInputs state [] target conflict propagation).steps = [] ∧
      (dischargeInputs state [] target conflict propagation).result.row.id = conflict.row.id := by
  constructor <;> rfl

theorem dischargeInputs_cons_fields (state : State v)
    (pivot : Literal (Fin v)) (rest target : Clause (Fin v))
    (conflict : AvailableSubclause state ((pivot :: rest).map negate ++ target))
    (propagation : ∀ input ∈ pivot :: rest,
      AvailableSubclause state (target ++ [input])) :
    let reason : AvailableSubclause state (pivot :: target) :=
      retarget (propagation pivot (by simp)) (by
        intro literal member
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member ⊢
        aesop)
    let adapted : AvailableSubclause state (negate pivot :: (rest.map negate ++ target)) := by
      simpa using conflict
    let joined := longMerge state pivot (rest.map negate ++ target) target adapted reason
    let merged := longMerge_result state pivot (rest.map negate ++ target) target adapted reason
    let nextConflict : AvailableSubclause joined.state (rest.map negate ++ target) :=
      retarget merged (by
        intro literal member
        simp only [List.mem_append] at member ⊢
        aesop)
    let nextPropagation : ∀ input ∈ rest, AvailableSubclause joined.state (target ++ [input]) :=
      fun input member => afterTrace (propagation input (by simp [member]))
        joined.state joined.steps (longMerge_run state pivot (rest.map negate ++ target) target adapted reason)
    let tail := dischargeInputs joined.state rest target nextConflict nextPropagation
    (dischargeInputs state (pivot :: rest) target conflict propagation).steps =
        joined.steps ++ tail.steps ∧
      (dischargeInputs state (pivot :: rest) target conflict propagation).result.row.id =
        tail.result.row.id := by
  constructor <;> rfl

theorem dischargeInputs_supported (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (remaining target : Clause (Fin v))
    (conflict : AvailableSubclause prefixState.state (remaining.map negate ++ target))
    (propagation : ∀ input ∈ remaining, AvailableSubclause prefixState.state (target ++ [input]))
    (supported : PrefixOriginalSupport rename prefixState)
    (conflictOrigin : ResultOrigin (formula parameters).clauses.size
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      prefixState.steps conflict.row.id)
    (propagationOrigins : ∀ input member, ResultOrigin (formula parameters).clauses.size
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      prefixState.steps (propagation input member).row.id) :
    ProjectionOriginalSupport rename prefixState
      (dischargeInputs prefixState.state remaining target conflict propagation) := by
  induction remaining generalizing prefixState with
  | nil =>
      have fields := dischargeInputs_nil_fields prefixState.state target conflict propagation
      unfold ProjectionOriginalSupport
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
        supported (allowed_native_count_le rename) (prefix_native_count_le rename prefixState)
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
      unfold ProjectionOriginalSupport at tailSupport ⊢
      constructor
      · rw [fields.1]
        simpa only [current, SourcePrefix.extend, List.append_assoc] using tailSupport.1
      · rw [fields.1, fields.2]
        simpa only [current, SourcePrefix.extend, List.append_assoc] using tailSupport.2

def PairPropagationOriginalSupport (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    {context : Clause (Fin v)} {root : Literal (Fin v)}
    {pairs : List (Literal (Fin v) × Literal (Fin v))}
    (actual : PairPropagation prefixState.state context root pairs) : Prop :=
  TraceOriginalSupport (formula parameters).clauses.size
    (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
    (prefixState.steps ++ actual.steps) ∧
  ∀ pair member, ResultOrigin (formula parameters).clauses.size
    (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
    (prefixState.steps ++ actual.steps) (actual.results pair member).row.id


theorem pairPropagationStep_steps {state : State v} {context : Clause (Fin v)}
    {root : Literal (Fin v)} {rest : List (Literal (Fin v) × Literal (Fin v))}
    (head : Literal (Fin v) × Literal (Fin v))
    (first : SubclauseProjection state (context ++ [negate root, head.2]) 1)
    (tail : PairPropagation first.state context root rest) :
    (pairPropagationStep head first tail).steps = first.steps ++ tail.steps := rfl

theorem pairPropagationStep_head_id {state : State v} {context : Clause (Fin v)}
    {root : Literal (Fin v)} {rest : List (Literal (Fin v) × Literal (Fin v))}
    (head : Literal (Fin v) × Literal (Fin v))
    (first : SubclauseProjection state (context ++ [negate root, head.2]) 1)
    (tail : PairPropagation first.state context root rest)
    (member : head ∈ head :: rest) :
    ((pairPropagationStep head first tail).results head member).row.id = first.result.row.id := by
  simp only [pairPropagationStep, subclause_dite_id, dite_eq_left rfl] <;> rfl

theorem pairPropagationStep_tail_id {state : State v} {context : Clause (Fin v)}
    {root : Literal (Fin v)} {rest : List (Literal (Fin v) × Literal (Fin v))}
    (head : Literal (Fin v) × Literal (Fin v))
    (first : SubclauseProjection state (context ++ [negate root, head.2]) 1)
    (tail : PairPropagation first.state context root rest)
    (pair : Literal (Fin v) × Literal (Fin v))
    (member : pair ∈ head :: rest) (different : pair ≠ head) :
    ((pairPropagationStep head first tail).results pair member).row.id =
      (tail.results pair ((List.mem_cons.mp member).resolve_left different)).row.id := by
  simp only [pairPropagationStep, subclause_dite_id, dite_eq_right different] <;> rfl


theorem pairPropagationStep_supported (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    {context : Clause (Fin v)} {root : Literal (Fin v)}
    {rest : List (Literal (Fin v) × Literal (Fin v))}
    (head : Literal (Fin v) × Literal (Fin v))
    (first : SubclauseProjection prefixState.state (context ++ [negate root, head.2]) 1)
    (tail : PairPropagation first.state context root rest)
    (firstSupport : ProjectionOriginalSupport rename prefixState first)
    (tailSupport : PairPropagationOriginalSupport rename
      (prefixState.extend first.state first.steps first.checked) tail) :
    PairPropagationOriginalSupport rename prefixState (pairPropagationStep head first tail) := by
  unfold PairPropagationOriginalSupport at tailSupport ⊢
  constructor
  · rw [pairPropagationStep_steps]
    simpa only [SourcePrefix.extend, List.append_assoc] using tailSupport.1
  · intro pair member
    rw [pairPropagationStep_steps]
    by_cases same : pair = head
    · subst pair
      rw [pairPropagationStep_head_id]
      have carried := resultOrigin_append_right (formula parameters).clauses.size
        (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
        (prefixState.steps ++ first.steps) tail.steps first.result.row.id firstSupport.2
      simpa only [List.append_assoc] using carried
    · rw [pairPropagationStep_tail_id head first tail pair member same]
      simpa only [SourcePrefix.extend, List.append_assoc] using
        tailSupport.2 pair ((List.mem_cons.mp member).resolve_left same)


theorem propagatePairs_supported (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (context : Clause (Fin v)) (root : Literal (Fin v))
    (pairs : List (Literal (Fin v) × Literal (Fin v)))
    (directions : ∀ pair ∈ pairs, AvailableSubclause prefixState.state [negate root, pair.1])
    (transfers : ∀ pair ∈ pairs, GuardedTransfer prefixState.state context pair.1 pair.2)
    (supported : PrefixOriginalSupport rename prefixState)
    (directionOrigins : ∀ pair member, ResultOrigin (formula parameters).clauses.size
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      prefixState.steps (directions pair member).row.id)
    (transferOrigins : ∀ pair member, GuardedTransferOrigin rename prefixState (transfers pair member)) :
    PairPropagationOriginalSupport rename prefixState
      (propagatePairs prefixState.state context root pairs directions transfers) := by
  induction pairs generalizing prefixState with
  | nil =>
      constructor
      · simpa only [propagatePairs, PrefixOriginalSupport, List.append_nil] using supported
      · intro pair impossible
        exact False.elim (List.not_mem_nil impossible)
  | cons head rest ih =>
      let first := guardedFromRow prefixState.state context root head.1 head.2
        (directions head (by simp)) (transfers head (by simp))
      have firstSupport := guardedFromRow_supported rename prefixState context root head.1 head.2
        (directions head (by simp)) (transfers head (by simp)) supported
        (directionOrigins head (by simp)) (transferOrigins head (by simp))
      let current := prefixState.extend first.state first.steps first.checked
      let nextDirections := fun pair (member : pair ∈ rest) => afterTrace
        (directions pair (List.mem_cons_of_mem _ member)) first.state first.steps first.checked
      let nextTransfers := fun pair (member : pair ∈ rest) => GuardedTransfer.afterTrace
        (transfers pair (List.mem_cons_of_mem _ member)) first.state first.steps first.checked
      have nextDirectionOrigins : ∀ pair member, ResultOrigin (formula parameters).clauses.size
          (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
          current.steps (nextDirections pair member).row.id := by
        intro pair member
        exact resultOrigin_append_right (formula parameters).clauses.size
          (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
          prefixState.steps first.steps (directions pair (List.mem_cons_of_mem _ member)).row.id
          (directionOrigins pair (List.mem_cons_of_mem _ member))
      have nextTransferOrigins : ∀ pair member,
          GuardedTransferOrigin rename current (nextTransfers pair member) := by
        intro pair member
        exact GuardedTransferOrigin.afterTrace rename prefixState
          (transfers pair (List.mem_cons_of_mem _ member))
          (transferOrigins pair (List.mem_cons_of_mem _ member)) first.state first.steps first.checked
      let tail := propagatePairs first.state context root rest nextDirections nextTransfers
      have tailSupport := ih current nextDirections nextTransfers firstSupport.1
        nextDirectionOrigins nextTransferOrigins
      exact pairPropagationStep_supported rename prefixState head first tail firstSupport tailSupport


def InitialMaskTableOriginalSupport (rename : Nat → Fin v) (flag : Bool)
    {done : List (Fin parameters.channels)} (table : InitialMaskTable rename flag done) : Prop :=
  PrefixOriginalSupport rename table.checkedPrefix ∧
    ∀ channel member, DirectionPairOrigin rename table.checkedPrefix (table.directions channel member)

theorem initialMaskTableStep_supported (rename : Nat → Fin v) (flag : Bool)
    (done : List (Fin parameters.channels)) (table : InitialMaskTable rename flag done)
    (channel : Fin parameters.channels)
    (supported : InitialMaskTableOriginalSupport rename flag table) :
    InitialMaskTableOriginalSupport rename flag (initialMaskTableStep rename flag done table channel) := by
  let next := initialMaskProjection rename flag channel table.checkedPrefix
  have nextSupport := initialMaskProjection_origins rename flag channel table.checkedPrefix supported.1
  constructor
  · exact nextSupport.1
  · intro query member
    by_cases same : query = channel
    · subst query
      simp only [initialMaskTableStep]
      dsimp only [SourcePrefix.extend]
      rw [dite_eq_left rfl]
      exact nextSupport.2
    · have old : query ∈ done := (List.mem_cons.mp member).resolve_left same
      have carried := DirectionPairOrigin.afterTrace rename table.checkedPrefix
        (table.directions query old) (supported.2 query old) next.state next.steps next.checked
      simp only [initialMaskTableStep]
      dsimp only [SourcePrefix.extend]
      rw [dite_eq_right same]
      exact carried

theorem buildInitialMaskTable_supported (rename : Nat → Fin v) (flag : Bool)
    (channels : List (Fin parameters.channels)) :
    InitialMaskTableOriginalSupport rename flag (buildInitialMaskTable rename flag channels) := by
  induction channels with
  | nil =>
      constructor
      · intro step impossible
        exact False.elim (List.not_mem_nil impossible)
      · intro channel impossible
        exact False.elim (List.not_mem_nil impossible)
  | cons channel channels ih =>
      exact initialMaskTableStep_supported rename flag channels
        (buildInitialMaskTable rename flag channels) channel ih


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
      simpa only [GuardedTransferOrigin,
        Controller.NativeProof.SourceStagePolarity.GuardedTransfer.dual, retarget] using original


def NotRowsOriginalSupport (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    {input output : Literal (Fin v)}
    (rows : Controller.NativeProof.SourceStagePolarity.NotRows prefixState.state input output) : Prop :=
  ResultOrigin (formula parameters).clauses.size
    (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
    prefixState.steps rows.positive.row.id ∧
  ResultOrigin (formula parameters).clauses.size
    (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
    prefixState.steps rows.negative.row.id

theorem guardedNot_supported (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (context : Clause (Fin v)) (leftInput rightInput leftOut rightOut : Literal (Fin v))
    (left : Controller.NativeProof.SourceStagePolarity.NotRows prefixState.state leftInput leftOut)
    (right : Controller.NativeProof.SourceStagePolarity.NotRows prefixState.state rightInput rightOut)
    (transfer : GuardedTransfer prefixState.state context rightInput leftInput)
    (supported : PrefixOriginalSupport rename prefixState)
    (leftSupport : NotRowsOriginalSupport rename prefixState left)
    (rightSupport : NotRowsOriginalSupport rename prefixState right)
    (transferSupport : GuardedTransferOrigin rename prefixState transfer) :
    ProjectionOriginalSupport rename prefixState
      (Controller.NativeProof.SourceStagePolarity.guardedNot prefixState.state context
        leftInput rightInput leftOut rightOut left right transfer) := by
  let dual := Controller.NativeProof.SourceStagePolarity.GuardedTransfer.dual transfer
  let first := guardedFromRow prefixState.state context leftOut (negate leftInput) (negate rightInput)
    left.negative dual
  have firstSupport := guardedFromRow_supported rename prefixState context
    leftOut (negate leftInput) (negate rightInput) left.negative dual supported leftSupport.2
    (GuardedTransferOrigin.dual rename prefixState transfer transferSupport)
  let current := prefixState.extend first.state first.steps first.checked
  let rightRow := afterTrace right.positive first.state first.steps first.checked
  let adapted : AvailableSubclause first.state
      (context ++ [negate (negate rightInput), rightOut]) :=
    retarget rightRow (by
      intro literal member
      simp only [negate_negate, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member ⊢
      aesop)
  have adaptedOrigin : ResultOrigin (formula parameters).clauses.size
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      current.steps adapted.row.id :=
    resultOrigin_append_right (formula parameters).clauses.size
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      prefixState.steps first.steps right.positive.row.id rightSupport.1
  have secondSupport := guardedChain_supported rename current context leftOut (negate rightInput)
    rightOut first.result adapted firstSupport.1 firstSupport.2 adaptedOrigin
  simpa only [ProjectionOriginalSupport, Controller.NativeProof.SourceStagePolarity.guardedNot,
    current, SourcePrefix.extend, first, dual, rightRow, adapted, List.append_assoc] using secondSupport


def InputProjectionOriginalSupport (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    {root : Literal (Fin v)} {inputs : Clause (Fin v)} {budget : Nat}
    (actual : InputProjection prefixState.state root inputs budget) : Prop :=
  TraceOriginalSupport (formula parameters).clauses.size
    (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
    (prefixState.steps ++ actual.steps) ∧
  ∀ input member, ResultOrigin (formula parameters).clauses.size
    (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
    (prefixState.steps ++ actual.steps) (actual.results input member).row.id

theorem nonunaryTreeInputs_prefixed_supported (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    {root : Literal (Fin v)} {inputs : Clause (Fin v)}
    (tree : AndTree prefixState.state root inputs) (two : 2 ≤ inputs.length)
    (original : TreeOriginals
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename) tree)
    (supported : PrefixOriginalSupport rename prefixState) :
    InputProjectionOriginalSupport rename prefixState (nonunaryTreeInputs tree two) := by
  have actual := nonunaryTreeInputs_supported tree two (formula parameters).clauses.size
    (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
    original (allowed_native_count_le rename) (prefix_native_count_le rename prefixState)
  constructor
  · exact traceOriginalSupport_append (formula parameters).clauses.size
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      prefixState.steps (nonunaryTreeInputs tree two).steps supported actual.1
  · intro input member
    exact resultOrigin_append_left (formula parameters).clauses.size
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      prefixState.steps (nonunaryTreeInputs tree two).steps
      ((nonunaryTreeInputs tree two).results input member).row.id (actual.2 input member)

theorem nonunaryAggregate_origin (originalCount : Nat) (allowed : Nat → Prop)
    (steps : List (Step v)) {state : State v} {output : Literal (Fin v)}
    {inputs : Clause (Fin v)} (certificate : AggregateCertificate state output inputs)
    (two : 2 ≤ inputs.length)
    (origin : Controller.NativeProof.SourceFoldAggregateProvenance.AggregateOrigin
      originalCount allowed steps certificate) :
    ResultOrigin originalCount allowed steps (nonunaryAggregate certificate two).row.id := by
  cases certificate with
  | identity => simp at two
  | derived row => exact origin


theorem guardedAnd_supported (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (context : Clause (Fin v)) (leftOut rightOut : Literal (Fin v))
    (pairs : List (Literal (Fin v) × Literal (Fin v))) (two : 2 ≤ pairs.length)
    (leftTree : AndTree prefixState.state leftOut (pairs.map Prod.fst))
    (rightTree : AndTree prefixState.state rightOut (pairs.map Prod.snd))
    (transfers : ∀ pair ∈ pairs, GuardedTransfer prefixState.state context pair.1 pair.2)
    (leftOriginal : TreeOriginals
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename) leftTree)
    (rightOriginal : TreeOriginals
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename) rightTree)
    (supported : PrefixOriginalSupport rename prefixState)
    (transferOrigins : ∀ pair member, GuardedTransferOrigin rename prefixState (transfers pair member)) :
    ProjectionOriginalSupport rename prefixState
      (guardedAnd prefixState.state context leftOut rightOut pairs two leftTree rightTree transfers) := by
  let first := nonunaryTreeInputs leftTree (by simpa using two)
  have firstSupport := nonunaryTreeInputs_prefixed_supported rename prefixState leftTree
    (by simpa using two) leftOriginal supported
  let firstPrefix := prefixState.extend first.state first.steps first.checked
  let reflected := rightTree.afterTrace first.state first.steps first.checked
  let second := projectTreeLong reflected
  have reflectedOriginal := treeOriginals_afterTrace
    (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
    rightTree rightOriginal first.state first.steps first.checked
  have secondSupport := Controller.NativeProof.SourceFoldAggregateProvenance.projectTreeLong_supported
    first.state reflected (formula parameters).clauses.size
    (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
    firstPrefix.steps reflectedOriginal firstSupport.1 (allowed_native_count_le rename)
    (prefix_native_count_le rename firstPrefix)
  let secondPrefix := firstPrefix.extend second.state second.steps second.checked
  let directions := fun pair (member : pair ∈ pairs) => afterTrace
    (first.results pair.1 (List.mem_map_of_mem (f := Prod.fst) member))
    second.state second.steps second.checked
  let currentTransfers := fun pair (member : pair ∈ pairs) =>
    GuardedTransfer.afterTrace
      (GuardedTransfer.afterTrace (transfers pair member) first.state first.steps first.checked)
      second.state second.steps second.checked
  have directionOrigins : ∀ pair member, ResultOrigin (formula parameters).clauses.size
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      secondPrefix.steps (directions pair member).row.id := by
    intro pair member
    exact resultOrigin_append_right (formula parameters).clauses.size
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      firstPrefix.steps second.steps
      (first.results pair.1 (List.mem_map_of_mem (f := Prod.fst) member)).row.id
      (firstSupport.2 pair.1 (List.mem_map_of_mem (f := Prod.fst) member))
  have currentOrigins : ∀ pair member,
      GuardedTransferOrigin rename secondPrefix (currentTransfers pair member) := by
    intro pair member
    have firstOrigin := GuardedTransferOrigin.afterTrace rename prefixState
      (transfers pair member) (transferOrigins pair member) first.state first.steps first.checked
    exact GuardedTransferOrigin.afterTrace rename firstPrefix
      (GuardedTransfer.afterTrace (transfers pair member) first.state first.steps first.checked)
      firstOrigin second.state second.steps second.checked
  let third := propagatePairs second.state context leftOut pairs directions currentTransfers
  have thirdSupport := propagatePairs_supported rename secondPrefix context leftOut pairs directions
    currentTransfers secondSupport.1 directionOrigins currentOrigins
  let thirdPrefix := secondPrefix.extend third.state third.steps third.checked
  let certificate := second.result.afterTrace third.state third.steps third.checked
  have certificateOrigin := Controller.NativeProof.SourceFoldAggregateProvenance.aggregateOrigin_afterTrace
    (formula parameters).clauses.size
    (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
    secondPrefix.steps third.steps second.result third.state third.checked secondSupport.2
  let aggregate := nonunaryAggregate certificate (by simpa using two)
  have aggregateOrigin := nonunaryAggregate_origin (formula parameters).clauses.size
    (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
    thirdPrefix.steps certificate (by simpa using two) certificateOrigin
  let target := context ++ [negate leftOut, rightOut]
  let conflict : AvailableSubclause third.state ((pairs.map Prod.snd).map negate ++ target) :=
    retarget aggregate (by
      intro literal member
      rcases List.mem_cons.mp member with equal | rest
      · subst literal
        simp [target]
      · exact List.mem_append_left _ rest)
  let propagations : ∀ input ∈ pairs.map Prod.snd,
      AvailableSubclause third.state (target ++ [input]) := fun input member =>
    let selected := mappedChoice Prod.snd input pairs member
    let row := third.results selected.val selected.property.1
    retarget row (by
      intro literal included
      have selectedEq := selected.property.2
      simp only [target, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at included ⊢
      aesop)
  have propagationOrigins : ∀ input member, ResultOrigin (formula parameters).clauses.size
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      thirdPrefix.steps (propagations input member).row.id := by
    intro input member
    let selected := mappedChoice Prod.snd input pairs member
    exact thirdSupport.2 selected.val selected.property.1
  have fourthSupport := dischargeInputs_supported rename thirdPrefix (pairs.map Prod.snd)
    target conflict propagations thirdSupport.1 aggregateOrigin propagationOrigins
  simpa only [ProjectionOriginalSupport, guardedAnd, firstPrefix, secondPrefix, thirdPrefix,
    SourcePrefix.extend, first, second, reflected, directions, currentTransfers, third, certificate,
    aggregate, target, conflict, propagations, List.append_assoc] using fourthSupport


/-- A guarded projection records both the exact accumulated checked trace
and the causal origin of its surviving directional certificate. -/
def GuardedProjectionOriginalSupport (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    {context : Clause (Fin v)} {input output : Literal (Fin v)} {budget : Nat}
    (projection : GuardedProjection prefixState.state context input output budget) : Prop :=
  PrefixOriginalSupport rename (prefixState.extend projection.state projection.steps projection.checked) ∧
    GuardedTransferOrigin rename
      (prefixState.extend projection.state projection.steps projection.checked) projection.result

/-- Both directions in the paired projection share the same final causal
prefix; the first direction is carried over the second direction's trace. -/
def PairedProjectionOriginalSupport (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    {context : Clause (Fin v)} {input output : Literal (Fin v)} {budget : Nat}
    (projection : PairedProjection prefixState.state context input output budget) : Prop :=
  PrefixOriginalSupport rename (prefixState.extend projection.state projection.steps projection.checked) ∧
    DirectionPairOrigin rename
      (prefixState.extend projection.state projection.steps projection.checked) projection.pair



def singletonTransfers (state : State v) (context : Clause (Fin v))
    (pair : Literal (Fin v) × Literal (Fin v))
    (transfer : GuardedTransfer state context pair.1 pair.2) :
    ∀ query ∈ [pair], GuardedTransfer state context query.1 query.2 := by
  intro query member
  have same : query = pair := by simpa only [List.mem_cons, List.not_mem_nil, or_false] using member
  subst query
  exact transfer

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

theorem guardedAndPositive_supported (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (context : Clause (Fin v)) (leftOut rightOut : Literal (Fin v))
    (pairs : List (Literal (Fin v) × Literal (Fin v))) (nonempty : pairs ≠ [])
    (leftTree : AndTree prefixState.state leftOut (pairs.map Prod.fst))
    (rightTree : AndTree prefixState.state rightOut (pairs.map Prod.snd))
    (transfers : ∀ pair ∈ pairs, GuardedTransfer prefixState.state context pair.1 pair.2)
    (leftOriginal : TreeOriginals
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename) leftTree)
    (rightOriginal : TreeOriginals
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename) rightTree)
    (supported : PrefixOriginalSupport rename prefixState)
    (transferOrigins : ∀ pair member, GuardedTransferOrigin rename prefixState (transfers pair member)) :
    GuardedProjectionOriginalSupport rename prefixState
      (guardedAndPositive prefixState.state context leftOut rightOut pairs nonempty leftTree rightTree transfers) := by
  cases pairs with
  | nil => exact False.elim (nonempty rfl)
  | cons pair rest =>
      cases rest with
      | nil =>
          have leftEq := treeRoot_singleton (input := pair.1) leftTree (by simp) (by simp)
          have rightEq := treeRoot_singleton (input := pair.2) rightTree (by simp) (by simp)
          let transfer := transfers pair (by simp)
          have origin : GuardedTransferOrigin rename prefixState transfer := transferOrigins pair (by simp)
          have transfersEq : transfers = singletonTransfers prefixState.state context pair transfer := by
            funext query member
            have same : query = pair := by simpa only [List.mem_cons, List.not_mem_nil, or_false] using member
            subst query
            rfl
          rw [transfersEq]
          cases transferEq : transfer with
          | identity same =>
              simpa only [GuardedProjectionOriginalSupport, guardedAndPositive, singletonTransfers,
                SourcePrefix.extend, List.append_nil, GuardedTransferOrigin] using
                (show PrefixOriginalSupport rename prefixState ∧ True from ⟨supported, trivial⟩)
          | derived row =>
              rw [transferEq] at origin
              simpa only [GuardedProjectionOriginalSupport, guardedAndPositive, singletonTransfers,
                SourcePrefix.extend, List.append_nil, GuardedTransferOrigin, retarget] using
                (show PrefixOriginalSupport rename prefixState ∧
                  ResultOrigin (formula parameters).clauses.size
                    (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal
                      (parameters := parameters) rename) prefixState.steps row.row.id from
                  ⟨supported, origin⟩)
      | cons second rest =>
          have actual := guardedAnd_supported rename prefixState context leftOut rightOut
            (pair :: second :: rest) (by simp) leftTree rightTree transfers
            leftOriginal rightOriginal supported transferOrigins
          simpa only [GuardedProjectionOriginalSupport, guardedAndPositive,
            ProjectionOriginalSupport, PrefixOriginalSupport, SourcePrefix.extend,
            GuardedTransferOrigin] using actual



theorem treeOriginals_mpr {state : State v} {output : Literal (Fin v)}
    {before after : List (Literal (Fin v))} (same : before = after)
    (typeEqual : AndTree state output before = AndTree state output after)
    (tree : AndTree state output after) (allowed : Nat → Prop)
    (original : TreeOriginals allowed tree) :
    TreeOriginals allowed (Eq.mpr typeEqual tree) := by
  cases same
  have proofEqual : typeEqual = rfl := Subsingleton.elim _ _
  cases proofEqual
  exact original

theorem guardedTransferOrigin_mpr (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    {context : Clause (Fin v)} {input output nextInput nextOutput : Literal (Fin v)}
    (sameInput : input = nextInput) (sameOutput : output = nextOutput)
    (typeEqual : GuardedTransfer prefixState.state context nextInput nextOutput =
      GuardedTransfer prefixState.state context input output)
    (transfer : GuardedTransfer prefixState.state context input output)
    (original : GuardedTransferOrigin rename prefixState transfer) :
    GuardedTransferOrigin rename prefixState (Eq.mpr typeEqual transfer) := by
  cases sameInput
  cases sameOutput
  have proofEqual : typeEqual = rfl := Subsingleton.elim _ _
  cases proofEqual
  exact original

theorem pairedAnd_supported (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (context : Clause (Fin v)) (leftOut rightOut : Literal (Fin v))
    (pairs : List (Literal (Fin v) × Literal (Fin v))) (nonempty : pairs ≠ [])
    (leftTree : AndTree prefixState.state leftOut (pairs.map Prod.fst))
    (rightTree : AndTree prefixState.state rightOut (pairs.map Prod.snd))
    (transfers : ∀ pair ∈ pairs, DirectionPair prefixState.state context pair.1 pair.2)
    (leftOriginal : TreeOriginals
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename) leftTree)
    (rightOriginal : TreeOriginals
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename) rightTree)
    (supported : PrefixOriginalSupport rename prefixState)
    (transferOrigins : ∀ pair member, DirectionPairOrigin rename prefixState (transfers pair member)) :
    PairedProjectionOriginalSupport rename prefixState
      (pairedAnd prefixState.state context leftOut rightOut pairs nonempty leftTree rightTree transfers) := by
  let first := guardedAndPositive prefixState.state context leftOut rightOut pairs nonempty leftTree rightTree
    (fun pair member => (transfers pair member).forward)
  have firstSupport := guardedAndPositive_supported rename prefixState context leftOut rightOut
    pairs nonempty leftTree rightTree (fun pair member => (transfers pair member).forward)
    leftOriginal rightOriginal supported (fun pair member => (transferOrigins pair member).1)
  let current := prefixState.extend first.state first.steps first.checked
  let reversed := pairs.map Prod.swap
  have reversedNonempty : reversed ≠ [] := by
    intro empty
    exact nonempty (List.map_eq_nil_iff.mp empty)
  let nextLeft : AndTree first.state rightOut (reversed.map Prod.fst) := by
    simpa only [reversed, List.map_map, Function.comp_def, Prod.fst_swap] using
      rightTree.afterTrace first.state first.steps first.checked
  let nextRight : AndTree first.state leftOut (reversed.map Prod.snd) := by
    simpa only [reversed, List.map_map, Function.comp_def, Prod.snd_swap] using
      leftTree.afterTrace first.state first.steps first.checked
  let nextTransfers := fun pair (member : pair ∈ reversed) =>
    let selected := mappedChoice Prod.swap pair pairs member
    let old := (transfers selected.val selected.property.1).backward
    (show GuardedTransfer first.state context pair.1 pair.2 from by
      have same := selected.property.2
      simpa only [← same, Prod.fst_swap, Prod.snd_swap] using
        old.afterTrace first.state first.steps first.checked)
  have nextLeftOriginal : TreeOriginals
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename) nextLeft := by
    dsimp only [nextLeft]
    apply treeOriginals_mpr (by simp only [reversed, List.map_map, Function.comp_def, Prod.fst_swap])
    exact treeOriginals_afterTrace _ rightTree rightOriginal first.state first.steps first.checked
  have nextRightOriginal : TreeOriginals
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename) nextRight := by
    dsimp only [nextRight]
    apply treeOriginals_mpr (by simp only [reversed, List.map_map, Function.comp_def, Prod.snd_swap])
    exact treeOriginals_afterTrace _ leftTree leftOriginal first.state first.steps first.checked
  have nextOrigins : ∀ pair member, GuardedTransferOrigin rename current (nextTransfers pair member) := by
    intro pair member
    let selected := mappedChoice Prod.swap pair pairs member
    have carried := GuardedTransferOrigin.afterTrace rename prefixState
      (transfers selected.val selected.property.1).backward
      (transferOrigins selected.val selected.property.1).2 first.state first.steps first.checked
    have same := selected.property.2
    dsimp only [nextTransfers]
    apply guardedTransferOrigin_mpr rename current
      (by simpa only [Prod.fst_swap] using congrArg Prod.fst same)
      (by simpa only [Prod.snd_swap] using congrArg Prod.snd same)
    exact carried
  let second := guardedAndPositive first.state context rightOut leftOut reversed reversedNonempty
    nextLeft nextRight nextTransfers
  have secondSupport := guardedAndPositive_supported rename current context rightOut leftOut
    reversed reversedNonempty nextLeft nextRight nextTransfers nextLeftOriginal nextRightOriginal
    firstSupport.1 nextOrigins
  have forwardSupport := GuardedTransferOrigin.afterTrace rename current first.result firstSupport.2
    second.state second.steps second.checked
  have both : PrefixOriginalSupport rename (current.extend second.state second.steps second.checked) ∧
      DirectionPairOrigin rename (current.extend second.state second.steps second.checked)
        ⟨first.result.afterTrace second.state second.steps second.checked, second.result⟩ :=
    ⟨secondSupport.1, forwardSupport, secondSupport.2⟩
  let finished := prefixState.extend second.state (first.steps ++ second.steps) (by
    rw [runSteps_append, first.checked]
    exact second.checked)
  change PrefixOriginalSupport rename finished ∧ DirectionPairOrigin rename finished
    ⟨first.result.afterTrace second.state second.steps second.checked, second.result⟩
  constructor
  · simpa only [PrefixOriginalSupport, finished, current, SourcePrefix.extend,
      List.append_assoc] using secondSupport.1
  · constructor
    · exact GuardedTransferOrigin.same_steps rename second.state
        ((prefixState.steps ++ first.steps) ++ second.steps)
        (prefixState.steps ++ (first.steps ++ second.steps)) (List.append_assoc _ _ _)
        _ _ (first.result.afterTrace second.state second.steps second.checked) forwardSupport
    · exact GuardedTransferOrigin.same_steps rename second.state
        ((prefixState.steps ++ first.steps) ++ second.steps)
        (prefixState.steps ++ (first.steps ++ second.steps)) (List.append_assoc _ _ _)
        _ _ second.result secondSupport.2


def reverseNegatedTransfer {state : State v} {context : Clause (Fin v)}
    {left right : Literal (Fin v)}
    (transfer : GuardedTransfer state context (negate right) (negate left)) :
    GuardedTransfer state context left right := by
  cases transfer with
  | identity same => exact .identity (by simpa only [negate_negate] using congrArg negate same.symm)
  | derived row =>
      exact .derived (retarget row (by
        intro literal member
        simp only [negate_negate, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member ⊢
        aesop))

theorem reverseNegatedTransfer_supported (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    {context : Clause (Fin v)} {left right : Literal (Fin v)}
    (transfer : GuardedTransfer prefixState.state context (negate right) (negate left))
    (original : GuardedTransferOrigin rename prefixState transfer) :
    GuardedTransferOrigin rename prefixState (reverseNegatedTransfer transfer) := by
  cases transfer with
  | identity same => trivial
  | derived row => exact original


theorem treeOriginals_mp {state : State v} {output : Literal (Fin v)}
    {before after : List (Literal (Fin v))} (same : before = after)
    (typeEqual : AndTree state output before = AndTree state output after)
    (tree : AndTree state output before) (allowed : Nat → Prop)
    (original : TreeOriginals allowed tree) : TreeOriginals allowed (Eq.mp typeEqual tree) := by
  cases same
  have proofEqual : typeEqual = rfl := Subsingleton.elim _ _
  cases proofEqual
  exact original

theorem guardedOr_supported (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (context : Clause (Fin v)) (leftOut rightOut : Literal (Fin v))
    (pairs : List (Literal (Fin v) × Literal (Fin v))) (nonempty : pairs ≠ [])
    (leftTree : AndTree prefixState.state (negate leftOut) ((pairs.map Prod.fst).map negate))
    (rightTree : AndTree prefixState.state (negate rightOut) ((pairs.map Prod.snd).map negate))
    (transfers : ∀ pair ∈ pairs, GuardedTransfer prefixState.state context pair.1 pair.2)
    (leftOriginal : TreeOriginals
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename) leftTree)
    (rightOriginal : TreeOriginals
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename) rightTree)
    (supported : PrefixOriginalSupport rename prefixState)
    (transferOrigins : ∀ pair member, GuardedTransferOrigin rename prefixState (transfers pair member)) :
    GuardedProjectionOriginalSupport rename prefixState
      (guardedOr prefixState.state context leftOut rightOut pairs nonempty leftTree rightTree transfers) := by
  let reflected := pairs.map dualPair
  let reflectedLeft : AndTree prefixState.state (negate rightOut) (reflected.map Prod.fst) := by
    simpa only [reflected, List.map_map, dualPair, Function.comp_def] using rightTree
  let reflectedRight : AndTree prefixState.state (negate leftOut) (reflected.map Prod.snd) := by
    simpa only [reflected, List.map_map, dualPair, Function.comp_def] using leftTree
  let reflectedTransfers := fun pair (member : pair ∈ reflected) =>
    let selected := mappedChoice dualPair pair pairs member
    let transfer := GuardedTransfer.dual (transfers selected.val selected.property.1)
    (show GuardedTransfer prefixState.state context pair.1 pair.2 from by
      have equal := selected.property.2
      simpa only [← equal, dualPair] using transfer)
  have reflectedLeftOriginal : TreeOriginals
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename) reflectedLeft := by
    dsimp only [reflectedLeft]
    apply treeOriginals_mpr (by simp only [reflected, List.map_map, dualPair, Function.comp_def])
    apply treeOriginals_mp (by simp only [reflected, List.map_map, dualPair, Function.comp_def])
    exact rightOriginal
  have reflectedRightOriginal : TreeOriginals
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename) reflectedRight := by
    dsimp only [reflectedRight]
    apply treeOriginals_mpr (by simp only [reflected, List.map_map, dualPair, Function.comp_def])
    apply treeOriginals_mp (by simp only [reflected, List.map_map, dualPair, Function.comp_def])
    exact leftOriginal
  have reflectedOrigins : ∀ pair member,
      GuardedTransferOrigin rename prefixState (reflectedTransfers pair member) := by
    intro pair member
    let selected := mappedChoice dualPair pair pairs member
    have actual := GuardedTransferOrigin.dual rename prefixState
      (transfers selected.val selected.property.1) (transferOrigins selected.val selected.property.1)
    have equal := selected.property.2
    dsimp only [reflectedTransfers]
    apply guardedTransferOrigin_mpr rename prefixState
      (by simpa only [dualPair] using congrArg Prod.fst equal)
      (by simpa only [dualPair] using congrArg Prod.snd equal)
    exact actual
  let joined := guardedAndPositive prefixState.state context _ _ reflected
    (by intro empty; apply nonempty; exact List.map_eq_nil_iff.mp empty)
    reflectedLeft reflectedRight reflectedTransfers
  have joinedSupport := guardedAndPositive_supported rename prefixState context _ _ reflected
    (by intro empty; apply nonempty; exact List.map_eq_nil_iff.mp empty)
    reflectedLeft reflectedRight reflectedTransfers reflectedLeftOriginal reflectedRightOriginal
    supported reflectedOrigins
  change PrefixOriginalSupport rename
      (prefixState.extend joined.state joined.steps joined.checked) ∧
    GuardedTransferOrigin rename (prefixState.extend joined.state joined.steps joined.checked)
      (reverseNegatedTransfer joined.result)
  exact ⟨joinedSupport.1, reverseNegatedTransfer_supported rename
    (prefixState.extend joined.state joined.steps joined.checked) joined.result joinedSupport.2⟩

theorem pairedOr_supported (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (context : Clause (Fin v)) (leftOut rightOut : Literal (Fin v))
    (pairs : List (Literal (Fin v) × Literal (Fin v))) (nonempty : pairs ≠ [])
    (leftTree : AndTree prefixState.state (negate leftOut) ((pairs.map Prod.fst).map negate))
    (rightTree : AndTree prefixState.state (negate rightOut) ((pairs.map Prod.snd).map negate))
    (transfers : ∀ pair ∈ pairs, DirectionPair prefixState.state context pair.1 pair.2)
    (leftOriginal : TreeOriginals
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename) leftTree)
    (rightOriginal : TreeOriginals
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename) rightTree)
    (supported : PrefixOriginalSupport rename prefixState)
    (transferOrigins : ∀ pair member, DirectionPairOrigin rename prefixState (transfers pair member)) :
    PairedProjectionOriginalSupport rename prefixState
      (pairedOr prefixState.state context leftOut rightOut pairs nonempty leftTree rightTree transfers) := by
  let first := guardedOr prefixState.state context leftOut rightOut pairs nonempty leftTree rightTree
    (fun pair member => (transfers pair member).forward)
  have firstSupport := guardedOr_supported rename prefixState context leftOut rightOut
    pairs nonempty leftTree rightTree (fun pair member => (transfers pair member).forward)
    leftOriginal rightOriginal supported (fun pair member => (transferOrigins pair member).1)
  let current := prefixState.extend first.state first.steps first.checked
  let reversed := pairs.map Prod.swap
  have reversedNonempty : reversed ≠ [] := by
    intro empty
    exact nonempty (List.map_eq_nil_iff.mp empty)
  let nextLeft : AndTree first.state (negate rightOut) ((reversed.map Prod.fst).map negate) := by
    simpa only [reversed, List.map_map, Function.comp_def, Prod.fst_swap] using
      rightTree.afterTrace first.state first.steps first.checked
  let nextRight : AndTree first.state (negate leftOut) ((reversed.map Prod.snd).map negate) := by
    simpa only [reversed, List.map_map, Function.comp_def, Prod.snd_swap] using
      leftTree.afterTrace first.state first.steps first.checked
  let nextTransfers := fun pair (member : pair ∈ reversed) =>
    let selected := mappedChoice Prod.swap pair pairs member
    let old := (transfers selected.val selected.property.1).backward
    (show GuardedTransfer first.state context pair.1 pair.2 from by
      have same := selected.property.2
      simpa only [← same, Prod.fst_swap, Prod.snd_swap] using
        old.afterTrace first.state first.steps first.checked)
  have nextLeftOriginal : TreeOriginals
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename) nextLeft := by
    dsimp only [nextLeft]
    apply treeOriginals_mpr (by simp only [reversed, List.map_map, Function.comp_def, Prod.fst_swap])
    apply treeOriginals_mp (by simp only [reversed, List.map_map, Function.comp_def, Prod.fst_swap])
    exact treeOriginals_afterTrace _ rightTree rightOriginal first.state first.steps first.checked
  have nextRightOriginal : TreeOriginals
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename) nextRight := by
    dsimp only [nextRight]
    apply treeOriginals_mpr (by simp only [reversed, List.map_map, Function.comp_def, Prod.snd_swap])
    apply treeOriginals_mp (by simp only [reversed, List.map_map, Function.comp_def, Prod.snd_swap])
    exact treeOriginals_afterTrace _ leftTree leftOriginal first.state first.steps first.checked
  have nextOrigins : ∀ pair member, GuardedTransferOrigin rename current (nextTransfers pair member) := by
    intro pair member
    let selected := mappedChoice Prod.swap pair pairs member
    have carried := GuardedTransferOrigin.afterTrace rename prefixState
      (transfers selected.val selected.property.1).backward
      (transferOrigins selected.val selected.property.1).2 first.state first.steps first.checked
    have same := selected.property.2
    dsimp only [nextTransfers]
    apply guardedTransferOrigin_mpr rename current
      (by simpa only [Prod.fst_swap] using congrArg Prod.fst same)
      (by simpa only [Prod.snd_swap] using congrArg Prod.snd same)
    exact carried
  let second := guardedOr first.state context rightOut leftOut reversed reversedNonempty
    nextLeft nextRight nextTransfers
  have secondSupport := guardedOr_supported rename current context rightOut leftOut
    reversed reversedNonempty nextLeft nextRight nextTransfers nextLeftOriginal nextRightOriginal
    firstSupport.1 nextOrigins
  have forwardSupport := GuardedTransferOrigin.afterTrace rename current first.result firstSupport.2
    second.state second.steps second.checked
  have both : PrefixOriginalSupport rename (current.extend second.state second.steps second.checked) ∧
      DirectionPairOrigin rename (current.extend second.state second.steps second.checked)
        ⟨first.result.afterTrace second.state second.steps second.checked, second.result⟩ :=
    ⟨secondSupport.1, forwardSupport, secondSupport.2⟩
  let finished := prefixState.extend second.state (first.steps ++ second.steps) (by
    rw [runSteps_append, first.checked]
    exact second.checked)
  change PrefixOriginalSupport rename finished ∧ DirectionPairOrigin rename finished
    ⟨first.result.afterTrace second.state second.steps second.checked, second.result⟩
  constructor
  · simpa only [PrefixOriginalSupport, finished, current, SourcePrefix.extend,
      List.append_assoc] using secondSupport.1
  · constructor
    · exact GuardedTransferOrigin.same_steps rename second.state
        ((prefixState.steps ++ first.steps) ++ second.steps)
        (prefixState.steps ++ (first.steps ++ second.steps)) (List.append_assoc _ _ _)
        _ _ (first.result.afterTrace second.state second.steps second.checked) forwardSupport
    · exact GuardedTransferOrigin.same_steps rename second.state
        ((prefixState.steps ++ first.steps) ++ second.steps)
        (prefixState.steps ++ (first.steps ++ second.steps)) (List.append_assoc _ _ _)
        _ _ second.result secondSupport.2



def BusMaskTableOriginalSupport (rename : Nat → Fin v) (flag : Bool)
    {count : Nat} (table : BusMaskTable (parameters := parameters) rename flag count) : Prop :=
  PrefixOriginalSupport rename table.checkedPrefix ∧
    ∀ bus member channel,
      DirectionPairOrigin rename table.checkedPrefix (table.directions bus member channel)

def TermBankOriginalSupport (rename : Nat → Fin v) (flag : Bool)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (start : SourcePrefix (parameters := parameters) rename)
    {done : List (Fin parameters.channels)} (bank : TermBank rename flag position start done) : Prop :=
  PrefixOriginalSupport rename bank.checkedPrefix ∧
    ∀ channel member, DirectionPairOrigin rename bank.checkedPrefix (bank.pairs channel member)

def MaskInputsOriginalSupport (rename : Nat → Fin v) (flag : Bool)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (inputs : MaskInputs (parameters := parameters) rename flag position) : Prop :=
  PrefixOriginalSupport rename inputs.checkedPrefix ∧
    (∀ channel, DirectionPairOrigin rename inputs.checkedPrefix (inputs.terms channel)) ∧
    DirectionPairOrigin rename inputs.checkedPrefix inputs.flags


open Controller.NativeProof.SourceStageXor

def CofactorReasonOrigin (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    {target : Clause (Fin v)} {input : Literal (Fin v)}
    (reason : CofactorReason prefixState.state target input) : Prop :=
  match reason with
  | .known _ => True
  | .propagated row => ResultOrigin (formula parameters).clauses.size
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      prefixState.steps row.row.id

theorem CofactorReasonOrigin.afterTrace (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    {target : Clause (Fin v)} {input : Literal (Fin v)}
    (reason : CofactorReason prefixState.state target input)
    (original : CofactorReasonOrigin rename prefixState reason)
    (next : State v) (steps : List (Step v)) (checked : runSteps prefixState.state steps = some next) :
    CofactorReasonOrigin rename (prefixState.extend next steps checked)
      (reason.afterTrace next steps checked) := by
  cases reason with
  | known contained => trivial
  | propagated row =>
      exact resultOrigin_append_right (formula parameters).clauses.size
        (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
        prefixState.steps steps row.row.id original

theorem cofactorReason_supported (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    {context target : Clause (Fin v)} {left right : Literal (Fin v)}
    (transfer : GuardedTransfer prefixState.state context left right)
    (included : ClauseSubset context target) (negative : negate left ∈ target)
    (original : GuardedTransferOrigin rename prefixState transfer) :
    CofactorReasonOrigin rename prefixState (cofactorReason transfer included negative) := by
  cases transfer with
  | identity same => trivial
  | derived row => exact original

theorem resolveReason_supported (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (target remaining : Clause (Fin v)) (input : Literal (Fin v))
    (conflict : AvailableSubclause prefixState.state (negate input :: (remaining ++ target)))
    (reason : CofactorReason prefixState.state target input)
    (supported : PrefixOriginalSupport rename prefixState)
    (conflictOrigin : ResultOrigin (formula parameters).clauses.size
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      prefixState.steps conflict.row.id)
    (reasonOrigin : CofactorReasonOrigin rename prefixState reason) :
    ProjectionOriginalSupport rename prefixState
      (resolveReason prefixState.state target remaining input conflict reason) := by
  cases reason with
  | known contained =>
      simpa only [ProjectionOriginalSupport, resolveReason, retarget, List.append_nil] using
        ⟨supported, conflictOrigin⟩
  | propagated row =>
      let adapted : AvailableSubclause prefixState.state (input :: target) := retarget row (by
        intro literal member
        have old := member
        simpa only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, false_or, or_comm] using old)
      have actual := longMerge_supported (formula parameters).clauses.size
        (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
        prefixState.steps prefixState.state input (remaining ++ target) target conflict adapted
        supported (allowed_native_count_le rename) (prefix_native_count_le rename prefixState)
        conflictOrigin reasonOrigin
      simpa only [ProjectionOriginalSupport, resolveReason, adapted, retarget] using actual


theorem directionPairOrigin_mpr (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    {context : Clause (Fin v)} {input output nextInput nextOutput : Literal (Fin v)}
    (sameInput : input = nextInput) (sameOutput : output = nextOutput)
    (typeEqual : DirectionPair prefixState.state context nextInput nextOutput =
      DirectionPair prefixState.state context input output)
    (pair : DirectionPair prefixState.state context input output)
    (original : DirectionPairOrigin rename prefixState pair) :
    DirectionPairOrigin rename prefixState (Eq.mpr typeEqual pair) := by
  cases sameInput
  cases sameOutput
  have proofEqual : typeEqual = rfl := Subsingleton.elim _ _
  cases proofEqual
  exact original

theorem termSourceDirection_supported (rename : Nat → Fin v) (flag : Bool)
    (position : Fin (laterBuses (parameters := parameters)).length) (channel : Fin parameters.channels)
    (table : BusMaskTable (parameters := parameters) rename flag position.val)
    (source : TermSource parameters) (member : source ∈ termSources position)
    (supported : BusMaskTableOriginalSupport rename flag table) :
    DirectionPairOrigin rename table.checkedPrefix
      (termSourceDirection rename flag position channel table source member) := by
  cases source with
  | enable => trivial
  | request => trivial
  | mask bus =>
      have before : bus < (laterBuses (parameters := parameters))[position.val] := by
        simpa [termSources] using member
      dsimp only [termSourceDirection]
      apply directionPairOrigin_mpr rename table.checkedPrefix
        (by simp only [termSourceLiteral, termBefore_mask, busBefore_eq_stagesBefore])
        (by simp only [termSourceLiteral, termBefore_mask, busBefore_eq_stagesBefore])
      exact supported.2 bus (earlier_bus_covered position bus before) channel

theorem termPairDirection_supported (rename : Nat → Fin v) (flag : Bool)
    (position : Fin (laterBuses (parameters := parameters)).length) (channel : Fin parameters.channels)
    (table : BusMaskTable (parameters := parameters) rename flag position.val)
    (pair : Literal (Fin v) × Literal (Fin v))
    (member : pair ∈ laterTermPairs rename position channel)
    (supported : BusMaskTableOriginalSupport rename flag table) :
    DirectionPairOrigin rename table.checkedPrefix
      (termPairDirection rename flag position channel table pair member) := by
  have represented : pair ∈ (termSources position).map (termSourcePair rename position channel) := by
    simpa only [← termSources_pairs rename position channel] using member
  let selected := mappedChoice (termSourcePair rename position channel) pair (termSources position) represented
  have actual := termSourceDirection_supported rename flag position channel table
    selected.val selected.property.1 supported
  have same := selected.property.2
  dsimp only [termPairDirection]
  apply directionPairOrigin_mpr rename table.checkedPrefix
    (by simpa only [termSourcePair] using congrArg Prod.fst same)
    (by simpa only [termSourcePair] using congrArg Prod.snd same)
  exact actual



theorem laterTermPairFromTable_supported (rename : Nat → Fin v) (flag : Bool)
    (position : Fin (laterBuses (parameters := parameters)).length) (channel : Fin parameters.channels)
    (table : BusMaskTable (parameters := parameters) rename flag position.val)
    (supported : BusMaskTableOriginalSupport rename flag table) :
    PairedProjectionOriginalSupport rename table.checkedPrefix
      (laterTermPairFromTable rename flag position channel table) := by
  let pairs := laterTermPairs rename position channel
  let left : AndTree table.checkedPrefix.state (laterTermOutput rename .healthy position channel)
      (pairs.map Prod.fst) := by
    dsimp only [pairs]
    rw [laterTermPairs_fst]
    exact (laterTermTree rename .healthy position channel).afterTrace
      table.checkedPrefix.state table.checkedPrefix.steps table.checkedPrefix.checked
  let right : AndTree table.checkedPrefix.state (laterTermOutput rename .faulty position channel)
      (pairs.map Prod.snd) := by
    dsimp only [pairs]
    rw [laterTermPairs_snd]
    exact (laterTermTree rename .faulty position channel).afterTrace
      table.checkedPrefix.state table.checkedPrefix.steps table.checkedPrefix.checked
  have leftOriginal : TreeOriginals
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename) left := by
    dsimp only [left]
    apply treeOriginals_mpr (laterTermPairs_fst rename position channel)
    exact treeOriginals_afterTrace _
      (laterTermTree rename .healthy position channel) (laterTermTree_originals rename .healthy position channel)
      table.checkedPrefix.state table.checkedPrefix.steps table.checkedPrefix.checked
  have rightOriginal : TreeOriginals
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename) right := by
    dsimp only [right]
    apply treeOriginals_mpr (laterTermPairs_snd rename position channel)
    exact treeOriginals_afterTrace _
      (laterTermTree rename .faulty position channel) (laterTermTree_originals rename .faulty position channel)
      table.checkedPrefix.state table.checkedPrefix.steps table.checkedPrefix.checked
  have nonempty : pairs ≠ [] := by
    have bound := laterTermPairs_two rename position channel
    intro empty
    simp only [pairs, empty, List.length_nil] at bound
    omega
  have actual := pairedAnd_supported rename table.checkedPrefix
    (equalFlagContext (parameters := parameters) rename flag) _ _ pairs nonempty left right
    (fun pair member => termPairDirection rename flag position channel table pair member)
    leftOriginal rightOriginal supported.1
    (fun pair member => termPairDirection_supported rename flag position channel table pair member supported)
  simpa only [PairedProjectionOriginalSupport, PrefixOriginalSupport, laterTermPairFromTable, pairs, left, right] using actual


theorem busMaskTable_afterTrace_supported (rename : Nat → Fin v) (flag : Bool)
    {count : Nat} (table : BusMaskTable (parameters := parameters) rename flag count)
    (next : State v) (steps : List (Step v))
    (checked : runSteps table.checkedPrefix.state steps = some next)
    (supported : BusMaskTableOriginalSupport rename flag table)
    (trace : PrefixOriginalSupport rename (table.checkedPrefix.extend next steps checked)) :
    BusMaskTableOriginalSupport rename flag (BusMaskTable.afterTrace table next steps checked) := by
  refine ⟨trace, ?_⟩
  intro bus member channel
  exact DirectionPairOrigin.afterTrace rename table.checkedPrefix
    (table.directions bus member channel) (supported.2 bus member channel) next steps checked

theorem DirectionPairOrigin.same_steps (rename : Nat → Fin v)
    (state : State v) (before after : List (Step v)) (same : before = after)
    (beforeChecked : runSteps (initialState (relabel rename (formula parameters))) before = some state)
    (afterChecked : runSteps (initialState (relabel rename (formula parameters))) after = some state)
    {context : Clause (Fin v)} {input output : Literal (Fin v)}
    (pair : DirectionPair state context input output)
    (original : DirectionPairOrigin rename ⟨state, before, beforeChecked⟩ pair) :
    DirectionPairOrigin rename ⟨state, after, afterChecked⟩ pair := by
  cases same
  exact original

def termBankStepKernel (rename : Nat → Fin v) (flag : Bool)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (table : BusMaskTable (parameters := parameters) rename flag position.val)
    (done : List (Fin parameters.channels))
    (bank : TermBank rename flag position table.checkedPrefix done)
    (channel : Fin parameters.channels)
    (added : PairedProjection bank.state (equalFlagContext (parameters := parameters) rename flag)
      (laterTermOutput rename .healthy position channel) (laterTermOutput rename .faulty position channel)
      (12 * (laterTermPairs rename position channel).length)) :
    TermBank rename flag position table.checkedPrefix (channel :: done) := by
  refine ⟨added.state, bank.steps ++ added.steps, ?_, ?_, ?_⟩
  · rw [runSteps_append, bank.checked]
    exact added.checked
  · intro query member
    by_cases same : query = channel
    · subst query
      exact added.pair
    · have old : query ∈ done := (List.mem_cons.mp member).resolve_left same
      exact (bank.pairs query old).afterTrace added.state added.steps added.checked
  · have one := bank.count
    have two : added.steps.length ≤ 12 *
        (2 + ((List.finRange parameters.buses).filter
          (fun earlier => earlier < (laterBuses (parameters := parameters))[position.val])).length) := by
      calc
        added.steps.length ≤ 12 * (laterTermPairs rename position channel).length := added.count
        _ = _ := congrArg (fun size => 12 * size) (laterTermPairs_length rename position channel)
    simp only [List.length_append, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

theorem termBankStep_kernel_eq (rename : Nat → Fin v) (flag : Bool)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (table : BusMaskTable (parameters := parameters) rename flag position.val)
    (done : List (Fin parameters.channels))
    (bank : TermBank rename flag position table.checkedPrefix done) (channel : Fin parameters.channels) :
    termBankStep rename flag position table done bank channel =
      termBankStepKernel rename flag position table done bank channel
        (laterTermPairFromTable rename flag position channel
          (BusMaskTable.afterTrace table bank.state bank.steps bank.checked)) := by
  rfl

theorem termBankStepKernel_supported (rename : Nat → Fin v) (flag : Bool)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (table : BusMaskTable (parameters := parameters) rename flag position.val)
    (done : List (Fin parameters.channels))
    (bank : TermBank rename flag position table.checkedPrefix done) (channel : Fin parameters.channels)
    (added : PairedProjection bank.state (equalFlagContext (parameters := parameters) rename flag)
      (laterTermOutput rename .healthy position channel) (laterTermOutput rename .faulty position channel)
      (12 * (laterTermPairs rename position channel).length))
    (bankSupport : TermBankOriginalSupport rename flag position table.checkedPrefix bank)
    (addedSupport : PairedProjectionOriginalSupport rename bank.checkedPrefix added) :
    TermBankOriginalSupport rename flag position table.checkedPrefix
      (termBankStepKernel rename flag position table done bank channel added) := by
  let joined := table.checkedPrefix.extend added.state (bank.steps ++ added.steps) (by
    rw [runSteps_append, bank.checked]
    exact added.checked)
  have joinedSupport : PrefixOriginalSupport rename joined := by
    simpa only [PairedProjectionOriginalSupport, PrefixOriginalSupport, PrefixOriginalSupport, joined,
      TermBank.checkedPrefix, SourcePrefix.extend, List.append_assoc] using addedSupport.1
  refine ⟨?_, ?_⟩
  · simpa only [TermBank.checkedPrefix, termBankStepKernel, PrefixOriginalSupport, joined,
      SourcePrefix.extend] using joinedSupport
  · intro query member
    by_cases same : query = channel
    · subst query
      have stepsEqual : bank.checkedPrefix.steps ++ added.steps = joined.steps := by
        simp only [joined, TermBank.checkedPrefix, SourcePrefix.extend, List.append_assoc]
      have carried := DirectionPairOrigin.same_steps rename added.state
        (bank.checkedPrefix.steps ++ added.steps) joined.steps stepsEqual
        (bank.checkedPrefix.extend added.state added.steps added.checked).checked joined.checked
        added.pair addedSupport.2
      simp only [termBankStepKernel, TermBank.checkedPrefix]
      dsimp only [SourcePrefix.extend]
      rw [dite_eq_left (show True from trivial)]
      change DirectionPairOrigin rename joined added.pair
      exact carried
    · have old : query ∈ done := (List.mem_cons.mp member).resolve_left same
      have origin := DirectionPairOrigin.afterTrace rename bank.checkedPrefix
        (bank.pairs query old) (bankSupport.2 query old) added.state added.steps added.checked
      have stepsEqual : bank.checkedPrefix.steps ++ added.steps = joined.steps := by
        simp only [TermBank.checkedPrefix, joined, SourcePrefix.extend, List.append_assoc]
      have carried := DirectionPairOrigin.same_steps rename added.state
        (bank.checkedPrefix.steps ++ added.steps) joined.steps stepsEqual
        (bank.checkedPrefix.extend added.state added.steps added.checked).checked joined.checked
        ((bank.pairs query old).afterTrace added.state added.steps added.checked) origin
      simp only [termBankStepKernel, TermBank.checkedPrefix]
      dsimp only [SourcePrefix.extend]
      rw [dite_eq_right same]
      change DirectionPairOrigin rename joined
        ((bank.pairs query old).afterTrace added.state added.steps added.checked)
      exact carried

theorem termBankStep_supported (rename : Nat → Fin v) (flag : Bool)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (table : BusMaskTable (parameters := parameters) rename flag position.val)
    (done : List (Fin parameters.channels))
    (bank : TermBank rename flag position table.checkedPrefix done)
    (channel : Fin parameters.channels)
    (tableSupport : BusMaskTableOriginalSupport rename flag table)
    (bankSupport : TermBankOriginalSupport rename flag position table.checkedPrefix bank) :
    TermBankOriginalSupport rename flag position table.checkedPrefix
      (termBankStep rename flag position table done bank channel) := by
  let extended := BusMaskTable.afterTrace table bank.state bank.steps bank.checked
  have extendedSupport := busMaskTable_afterTrace_supported rename flag table
    bank.state bank.steps bank.checked tableSupport bankSupport.1
  let added := laterTermPairFromTable rename flag position channel extended
  have addedSupport := laterTermPairFromTable_supported rename flag position channel extended extendedSupport
  rw [termBankStep_kernel_eq]
  exact termBankStepKernel_supported rename flag position table done bank channel added bankSupport addedSupport

theorem buildTermBank_supported (rename : Nat → Fin v) (flag : Bool)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (table : BusMaskTable (parameters := parameters) rename flag position.val)
    (channels : List (Fin parameters.channels))
    (supported : BusMaskTableOriginalSupport rename flag table) :
    TermBankOriginalSupport rename flag position table.checkedPrefix
      (buildTermBank rename flag position table channels) := by
  induction channels with
  | nil =>
      constructor
      · simpa only [TermBankOriginalSupport, TermBank.checkedPrefix, buildTermBank,
          PrefixOriginalSupport, SourcePrefix.extend, List.append_nil] using supported.1
      · intro channel member
        exact False.elim (List.not_mem_nil member)
  | cons channel channels ih =>
      exact termBankStep_supported rename flag position table channels
        (buildTermBank rename flag position table channels) channel supported ih


theorem flagPairDirection_supported (rename : Nat → Fin v) (flag : Bool)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (start : SourcePrefix (parameters := parameters) rename)
    (bank : TermBank rename flag position start (List.finRange parameters.channels))
    (pair : Literal (Fin v) × Literal (Fin v))
    (member : pair ∈ laterFlagPairs rename position)
    (supported : TermBankOriginalSupport rename flag position start bank) :
    DirectionPairOrigin rename bank.checkedPrefix
      (flagPairDirection rename flag position start bank pair member) := by
  have represented : pair ∈ (List.finRange parameters.channels).map (fun channel =>
      (laterTermOutput rename .healthy position channel, laterTermOutput rename .faulty position channel)) := by
    simpa only [← laterFlagPairs_eq_terms rename position] using member
  let selected := mappedChoice (fun channel =>
      (laterTermOutput rename .healthy position channel, laterTermOutput rename .faulty position channel))
    pair (List.finRange parameters.channels) represented
  have origin := supported.2 selected.val selected.property.1
  have same := selected.property.2
  dsimp only [flagPairDirection]
  apply directionPairOrigin_mpr rename bank.checkedPrefix
    (congrArg Prod.fst same) (congrArg Prod.snd same)
  exact origin


theorem laterFlagPairFromTerms_supported (rename : Nat → Fin v) (flag : Bool)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (start : SourcePrefix (parameters := parameters) rename)
    (bank : TermBank rename flag position start (List.finRange parameters.channels))
    (supported : TermBankOriginalSupport rename flag position start bank) :
    PairedProjectionOriginalSupport rename bank.checkedPrefix
      (laterFlagPairFromTerms rename flag position start bank) := by
  let checkedPrefix := bank.checkedPrefix
  let left : AndTree bank.state (negate (laterFlagOutput rename .healthy position))
      (((laterFlagPairs rename position).map Prod.fst).map negate) := by
    rw [laterFlagPairs_fst]
    have actual : AndTree bank.state (negate (laterFlagOutput rename .healthy position))
        ((laterFlagInputs .healthy position).map (fun literal => negate (mapLiteral rename literal))) :=
      (laterFlagTree rename .healthy position).afterTrace bank.state checkedPrefix.steps checkedPrefix.checked
    simpa only [List.map_map, Function.comp_def] using actual
  let right : AndTree bank.state (negate (laterFlagOutput rename .faulty position))
      (((laterFlagPairs rename position).map Prod.snd).map negate) := by
    rw [laterFlagPairs_snd]
    have actual : AndTree bank.state (negate (laterFlagOutput rename .faulty position))
        ((laterFlagInputs .faulty position).map (fun literal => negate (mapLiteral rename literal))) :=
      (laterFlagTree rename .faulty position).afterTrace bank.state checkedPrefix.steps checkedPrefix.checked
    simpa only [List.map_map, Function.comp_def] using actual
  have leftOriginal : TreeOriginals
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename) left := by
    dsimp only [left]
    apply treeOriginals_mpr (congrArg (List.map negate) (laterFlagPairs_fst rename position))
    apply treeOriginals_mpr (by simp only [List.map_map, Function.comp_def])
    exact treeOriginals_afterTrace _
      (laterFlagTree rename .healthy position) (laterFlagTree_originals rename .healthy position)
      bank.state checkedPrefix.steps checkedPrefix.checked
  have rightOriginal : TreeOriginals
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename) right := by
    dsimp only [right]
    apply treeOriginals_mpr (congrArg (List.map negate) (laterFlagPairs_snd rename position))
    apply treeOriginals_mpr (by simp only [List.map_map, Function.comp_def])
    exact treeOriginals_afterTrace _
      (laterFlagTree rename .faulty position) (laterFlagTree_originals rename .faulty position)
      bank.state checkedPrefix.steps checkedPrefix.checked
  have actual := pairedOr_supported rename checkedPrefix
    (equalFlagContext (parameters := parameters) rename flag)
    (laterFlagOutput rename .healthy position) (laterFlagOutput rename .faulty position)
    (laterFlagPairs rename position) (laterFlagPairs_nonempty rename position) left right
    (fun pair member => flagPairDirection rename flag position start bank pair member)
    leftOriginal rightOriginal supported.1
    (fun pair member => flagPairDirection_supported rename flag position start bank pair member supported)
  simpa only [PairedProjectionOriginalSupport, PrefixOriginalSupport, laterFlagPairFromTerms, checkedPrefix, left, right,
    TermBank.checkedPrefix, SourcePrefix.extend]
    using actual


theorem directionPairOrigin_mp (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    {context : Clause (Fin v)} {input output nextInput nextOutput : Literal (Fin v)}
    (sameInput : input = nextInput) (sameOutput : output = nextOutput)
    (typeEqual : DirectionPair prefixState.state context input output =
      DirectionPair prefixState.state context nextInput nextOutput)
    (pair : DirectionPair prefixState.state context input output)
    (original : DirectionPairOrigin rename prefixState pair) :
    DirectionPairOrigin rename prefixState (Eq.mp typeEqual pair) := by
  cases sameInput
  cases sameOutput
  have proofEqual : typeEqual = rfl := Subsingleton.elim _ _
  cases proofEqual
  exact original


theorem NotRowsOriginalSupport.afterTrace (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    {input output : Literal (Fin v)} (rows : NotRows prefixState.state input output)
    (next : State v) (steps : List (Step v))
    (checked : runSteps prefixState.state steps = some next)
    (original : NotRowsOriginalSupport rename prefixState rows) :
    NotRowsOriginalSupport rename (prefixState.extend next steps checked)
      (rows.afterTrace next steps checked) := by
  constructor
  · exact resultOrigin_append_right (formula parameters).clauses.size
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      prefixState.steps steps rows.positive.row.id original.1
  · exact resultOrigin_append_right (formula parameters).clauses.size
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      prefixState.steps steps rows.negative.row.id original.2

theorem laterAbsentNativeRows_supported (rename : Nat → Fin v) (side : Side)
    (position : Fin (laterBuses (parameters := parameters)).length) (channel : Fin parameters.channels)
    (prefixState : SourcePrefix (parameters := parameters) rename) :
    NotRowsOriginalSupport rename prefixState
      (laterAbsentNativeRows rename side position channel prefixState) := by
  constructor
  · apply Or.inl
    exact laterAbsentRows_allowed rename side position channel ⟨0, by change 0 < 2; decide⟩
  · apply Or.inl
    exact laterAbsentRows_allowed rename side position channel ⟨1, by change 1 < 2; decide⟩


theorem laterAbsentPairFromTerm_supported (rename : Nat → Fin v) (context : Clause (Fin v))
    (position : Fin (laterBuses (parameters := parameters)).length) (channel : Fin parameters.channels)
    (start : SourcePrefix (parameters := parameters) rename)
    (terms : DirectionPair start.state context (laterTermOutput rename .healthy position channel)
      (laterTermOutput rename .faulty position channel))
    (supported : PrefixOriginalSupport rename start)
    (termsOriginal : DirectionPairOrigin rename start terms) :
    PairedProjectionOriginalSupport rename start
      (laterAbsentPairFromTerm rename context position channel start terms) := by
  let inputs : DirectionPair start.state context (laterAbsentInput rename .healthy position channel)
      (laterAbsentInput rename .faulty position channel) := by
    simpa only [laterAbsentInput_eq_termOutput] using terms
  have inputsOriginal : DirectionPairOrigin rename start inputs := by
    dsimp only [inputs]
    apply directionPairOrigin_mpr rename start
      (laterAbsentInput_eq_termOutput rename .healthy position channel).symm
      (laterAbsentInput_eq_termOutput rename .faulty position channel).symm
    exact termsOriginal
  let left := laterAbsentNativeRows rename .healthy position channel start
  let right := laterAbsentNativeRows rename .faulty position channel start
  have leftOriginal := laterAbsentNativeRows_supported rename .healthy position channel start
  have rightOriginal := laterAbsentNativeRows_supported rename .faulty position channel start
  let first := guardedNot start.state context _ _ _ _ left right inputs.backward
  have firstSupport := guardedNot_supported rename start context _ _ _ _ left right inputs.backward
    supported leftOriginal rightOriginal inputsOriginal.2
  let current := start.extend first.state first.steps first.checked
  let nextLeft := left.afterTrace first.state first.steps first.checked
  let nextRight := right.afterTrace first.state first.steps first.checked
  let second := guardedNot first.state context _ _ _ _ nextRight nextLeft
    (inputs.forward.afterTrace first.state first.steps first.checked)
  have secondSupport := guardedNot_supported rename current context _ _ _ _ nextRight nextLeft
    (inputs.forward.afterTrace first.state first.steps first.checked) firstSupport.1
    (NotRowsOriginalSupport.afterTrace rename start right first.state first.steps first.checked rightOriginal)
    (NotRowsOriginalSupport.afterTrace rename start left first.state first.steps first.checked leftOriginal)
    (GuardedTransferOrigin.afterTrace rename start inputs.forward inputsOriginal.1 first.state first.steps first.checked)
  have forward := resultOrigin_append_right (formula parameters).clauses.size
    (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
    (start.steps ++ first.steps) second.steps first.result.row.id firstSupport.2
  simpa only [PairedProjectionOriginalSupport, PrefixOriginalSupport, laterAbsentPairFromTerm, inputs, left, right,
    first, current, nextLeft, nextRight, second, DirectionPairOrigin, GuardedTransferOrigin,
    SourcePrefix.extend, List.append_assoc, FoldProjection.afterTrace] using
      And.intro secondSupport.1 (And.intro forward secondSupport.2)


open Controller.NativeProof.SourceStageXor Controller.Resolution.Cases

theorem oddCofactor_supported (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (target : Clause (Fin v)) (a b output : Literal (Fin v)) (outputMem : output ∈ target)
    (row : AvailableSubclause prefixState.state [negate a, negate b, output])
    (firstReason : CofactorReason prefixState.state target a)
    (secondReason : CofactorReason prefixState.state target b)
    (supported : PrefixOriginalSupport rename prefixState)
    (rowOrigin : ResultOrigin (formula parameters).clauses.size
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      prefixState.steps row.row.id)
    (firstOrigin : CofactorReasonOrigin rename prefixState firstReason)
    (secondOrigin : CofactorReasonOrigin rename prefixState secondReason) :
    ProjectionOriginalSupport rename prefixState
      (oddCofactor prefixState.state target a b output outputMem row firstReason secondReason) := by
  let adapted : AvailableSubclause prefixState.state (negate a :: ([negate b] ++ target)) :=
    retarget row (by
      intro literal member
      have old := member
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at old ⊢
      aesop)
  let first := resolveReason prefixState.state target [negate b] a adapted firstReason
  have firstSupport := resolveReason_supported rename prefixState target [negate b] a
    adapted firstReason supported rowOrigin firstOrigin
  let current := prefixState.extend first.state first.steps first.checked
  let secondConflict : AvailableSubclause first.state (negate b :: ([] ++ target)) :=
    retarget first.result (by intro literal member; simpa using member)
  have carried := CofactorReasonOrigin.afterTrace rename prefixState secondReason secondOrigin
    first.state first.steps first.checked
  let second := resolveReason first.state target [] b secondConflict
    (secondReason.afterTrace first.state first.steps first.checked)
  have secondSupport := resolveReason_supported rename current target [] b secondConflict
    (secondReason.afterTrace first.state first.steps first.checked) firstSupport.1
    firstSupport.2 carried
  simpa only [ProjectionOriginalSupport, PrefixOriginalSupport, oddCofactor,
    adapted, first, current, secondConflict, second, SourcePrefix.extend,
    List.append_assoc, retarget] using secondSupport


def XorRowsOriginalSupport (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    {a b output : Literal (Fin v)} (rows : XorRows prefixState.state a b output) : Prop :=
  ResultOrigin (formula parameters).clauses.size
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      prefixState.steps rows.zeroZero.row.id ∧
  ResultOrigin (formula parameters).clauses.size
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      prefixState.steps rows.oneOne.row.id ∧
  ResultOrigin (formula parameters).clauses.size
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      prefixState.steps rows.zeroOne.row.id ∧
  ResultOrigin (formula parameters).clauses.size
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      prefixState.steps rows.oneZero.row.id

theorem XorRowsOriginalSupport.afterTrace (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    {a b output : Literal (Fin v)} (rows : XorRows prefixState.state a b output)
    (next : State v) (steps : List (Step v)) (checked : runSteps prefixState.state steps = some next)
    (original : XorRowsOriginalSupport rename prefixState rows) :
    XorRowsOriginalSupport rename (prefixState.extend next steps checked)
      (rows.afterTrace next steps checked) := by
  exact ⟨resultOrigin_append_right _ _ _ _ _ original.1,
    resultOrigin_append_right _ _ _ _ _ original.2.1,
    resultOrigin_append_right _ _ _ _ _ original.2.2.1,
    resultOrigin_append_right _ _ _ _ _ original.2.2.2⟩

theorem inputReason_supported (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (context target : Clause (Fin v)) (left right : Literal (Fin v)) (bit : Bool)
    (forward : GuardedTransfer prefixState.state context left right)
    (backward : GuardedTransfer prefixState.state context right left)
    (included : ClauseSubset context target)
    (guardMem : negate (valueLiteral left bit) ∈ target)
    (forwardOriginal : GuardedTransferOrigin rename prefixState forward)
    (backwardOriginal : GuardedTransferOrigin rename prefixState backward) :
    CofactorReasonOrigin rename prefixState
      (inputReason prefixState.state context target left right bit forward backward included guardMem) := by
  cases bit with
  | false =>
      exact cofactorReason_supported rename prefixState (dualTransfer backward)
        included guardMem (GuardedTransferOrigin.dual rename prefixState backward backwardOriginal)
  | true =>
      exact cofactorReason_supported rename prefixState forward included guardMem forwardOriginal


theorem xorCofactor_supported (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (context : Clause (Fin v)) (a b c d leftOut rightOut : Literal (Fin v))
    (left : XorRows prefixState.state a b leftOut)
    (right : XorRows prefixState.state c d rightOut)
    (aForward : GuardedTransfer prefixState.state context a c)
    (aBackward : GuardedTransfer prefixState.state context c a)
    (bForward : GuardedTransfer prefixState.state context b d)
    (bBackward : GuardedTransfer prefixState.state context d b)
    (x y : Bool) (supported : PrefixOriginalSupport rename prefixState)
    (leftOriginal : XorRowsOriginalSupport rename prefixState left)
    (rightOriginal : XorRowsOriginalSupport rename prefixState right)
    (af : GuardedTransferOrigin rename prefixState aForward)
    (ab : GuardedTransferOrigin rename prefixState aBackward)
    (bf : GuardedTransferOrigin rename prefixState bForward)
    (bb : GuardedTransferOrigin rename prefixState bBackward) :
    ProjectionOriginalSupport rename prefixState
      (xorCofactor prefixState.state context a b c d leftOut rightOut left right
        aForward aBackward bForward bBackward x y) := by
  let target := branchTarget (context ++ [negate leftOut, rightOut]) a b x y
  have included : ClauseSubset context target := by
    intro literal member
    simp only [target, branchTarget, List.mem_append]
    exact Or.inl (Or.inl (Or.inl member))
  have aMem : negate (valueLiteral a x) ∈ target := by simp [target, branchTarget]
  have bMem : negate (valueLiteral b y) ∈ target := by simp [target, branchTarget]
  let firstReason := inputReason prefixState.state context target a c x aForward aBackward included aMem
  let secondReason := inputReason prefixState.state context target b d y bForward bBackward included bMem
  have firstOrigin := inputReason_supported rename prefixState context target a c x
    aForward aBackward included aMem af ab
  have secondOrigin := inputReason_supported rename prefixState context target b d y
    bForward bBackward included bMem bf bb
  have outputMem : rightOut ∈ target := by simp [target, branchTarget]
  cases x <;> cases y
  · simpa only [ProjectionOriginalSupport, xorCofactor, PrefixOriginalSupport, SourcePrefix.extend,
      List.append_nil, retarget] using And.intro supported leftOriginal.1
  · let row : AvailableSubclause prefixState.state
        [negate (valueLiteral c false), negate (valueLiteral d true), rightOut] :=
      retarget right.zeroOne (by intro literal member; simpa [valueLiteral] using member)
    have actual := oddCofactor_supported rename prefixState target _ _ rightOut outputMem row
      firstReason secondReason supported rightOriginal.2.2.1 firstOrigin secondOrigin
    simpa only [ProjectionOriginalSupport, xorCofactor, target, firstReason, secondReason, row]
      using actual
  · let row : AvailableSubclause prefixState.state
        [negate (valueLiteral c true), negate (valueLiteral d false), rightOut] :=
      retarget right.oneZero (by intro literal member; simpa [valueLiteral] using member)
    have actual := oddCofactor_supported rename prefixState target _ _ rightOut outputMem row
      firstReason secondReason supported rightOriginal.2.2.2 firstOrigin secondOrigin
    simpa only [ProjectionOriginalSupport, xorCofactor, target, firstReason, secondReason, row]
      using actual
  · simpa only [ProjectionOriginalSupport, xorCofactor, PrefixOriginalSupport, SourcePrefix.extend,
      List.append_nil, retarget] using And.intro supported leftOriginal.2.1


open Controller.Resolution.Cases

def EmptyReasonTreeOrigins (rename : Nat → Fin v) (steps : List (Step v)) :
    CaseTree v → Prop
  | .leaf certificate => certificate.reasons = [] ∧
      ResultOrigin (formula parameters).clauses.size
        (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
        steps certificate.rowId
  | .fork _ left right => EmptyReasonTreeOrigins rename steps left ∧
      EmptyReasonTreeOrigins rename steps right

theorem EmptyReasonTreeOrigins.append (rename : Nat → Fin v)
    (before after : List (Step v)) (tree : CaseTree v)
    (original : EmptyReasonTreeOrigins (parameters := parameters) rename before tree) :
    EmptyReasonTreeOrigins (parameters := parameters) rename (before ++ after) tree := by
  induction tree with
  | leaf certificate =>
      exact ⟨original.1, resultOrigin_append_right _ _ before after certificate.rowId original.2⟩
  | fork pivot left right leftIH rightIH => exact ⟨leftIH original.1, rightIH original.2⟩

theorem compileEmptyReasonTree_supported (rename : Nat → Fin v)
    (tree : CaseTree v) (base : State v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (target : Clause (Fin v)) (valid : ValidTree base target tree)
    (baseBound : base.lastId ≤ prefixState.state.lastId)
    (baseRows : ∀ id, id ≤ base.lastId → prefixState.state.rows id = base.rows id)
    (supported : PrefixOriginalSupport rename prefixState)
    (original : EmptyReasonTreeOrigins (parameters := parameters) rename prefixState.steps tree) :
    TraceOriginalSupport (formula parameters).clauses.size
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      (prefixState.steps ++ (compileTree prefixState.state tree).steps) ∧
    ResultOrigin (formula parameters).clauses.size
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      (prefixState.steps ++ (compileTree prefixState.state tree).steps)
      (compileTree prefixState.state tree).rowId := by
  induction tree generalizing prefixState target with
  | leaf certificate =>
      rcases original with ⟨empty, origin⟩
      simpa only [PrefixOriginalSupport, compileTree, empty, Controller.Resolution.RUP.compileReasons, List.append_nil] using
        And.intro supported origin
  | fork pivot left right leftIH rightIH =>
      let first := compileTree prefixState.state left
      have firstRun := compileTree_run left base prefixState.state baseBound baseRows
        (target ++ [negate pivot]) valid.1
      have firstSupport := leftIH prefixState (target ++ [negate pivot]) valid.1
        baseBound baseRows supported original.1
      let current := prefixState.extend first.state first.steps firstRun.1
      have nextBound : base.lastId ≤ current.state.lastId :=
        Nat.le_trans baseBound (runSteps_lastId_le firstRun.1)
      have nextRows : ∀ id, id ≤ base.lastId → current.state.rows id = base.rows id := by
        intro id bound
        exact (runSteps_preserves_old_rows firstRun.1 id (Nat.le_trans bound baseBound)).trans
          (baseRows id bound)
      have secondOriginal := EmptyReasonTreeOrigins.append (parameters := parameters) rename prefixState.steps first.steps right original.2
      let second := compileTree first.state right
      have secondRun := compileTree_run right base current.state nextBound nextRows
        (target ++ [pivot]) valid.2
      have secondSupport := rightIH current (target ++ [pivot]) valid.2 nextBound nextRows
        firstSupport.1 secondOriginal
      let finalPrefix := current.extend second.state second.steps secondRun.1
      have one := resultOrigin_append_right (formula parameters).clauses.size
        (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
        (prefixState.steps ++ first.steps) second.steps first.rowId firstSupport.2
      have leftBound : first.rowId ≤ second.state.lastId :=
        Nat.le_trans firstRun.2.2.1 (runSteps_lastId_le secondRun.1)
      have joinedSupport := Controller.NativeProof.SourceFoldAggregateProvenance.appendMerge_origins_supported
        (formula parameters).clauses.size
        (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
        finalPrefix.steps second.state first.rowId second.rowId pivot first.clause second.clause
        secondSupport.1 (allowed_native_count_le rename) one secondSupport.2 leftBound secondRun.2.2.1
      have joinedOrigin := Controller.NativeProof.SourceFoldAggregateProvenance.merge_origins
        (formula parameters).clauses.size
        (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
        finalPrefix.steps second.state first.rowId second.rowId pivot first.clause second.clause
        one secondSupport.2 (prefix_native_count_le rename finalPrefix)
      simpa only [compileTree, first, second, current, finalPrefix, SourcePrefix.extend,
        List.append_assoc] using And.intro joinedSupport joinedOrigin


theorem joinCofactors_supported (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (target : Clause (Fin v)) (a b : Literal (Fin v))
    (tt : AvailableSubclause prefixState.state (branchTarget target a b true true))
    (tf : AvailableSubclause prefixState.state (branchTarget target a b true false))
    (ft : AvailableSubclause prefixState.state (branchTarget target a b false true))
    (ff : AvailableSubclause prefixState.state (branchTarget target a b false false))
    (supported : PrefixOriginalSupport rename prefixState)
    (ttOrigin : ResultOrigin (formula parameters).clauses.size
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename) prefixState.steps tt.row.id)
    (tfOrigin : ResultOrigin (formula parameters).clauses.size
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename) prefixState.steps tf.row.id)
    (ftOrigin : ResultOrigin (formula parameters).clauses.size
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename) prefixState.steps ft.row.id)
    (ffOrigin : ResultOrigin (formula parameters).clauses.size
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename) prefixState.steps ff.row.id) :
    ProjectionOriginalSupport rename prefixState
      (joinCofactors prefixState.state target a b tt tf ft ff) := by
  have origins : EmptyReasonTreeOrigins (parameters := parameters) rename prefixState.steps
      (xorCaseTree prefixState.state target a b tt tf ft ff) :=
    ⟨⟨⟨rfl, ttOrigin⟩, ⟨rfl, tfOrigin⟩⟩, ⟨⟨rfl, ftOrigin⟩, ⟨rfl, ffOrigin⟩⟩⟩
  have actual := compileEmptyReasonTree_supported rename
    (xorCaseTree prefixState.state target a b tt tf ft ff) prefixState.state prefixState target
    (xorCaseTree_valid prefixState.state target a b tt tf ft ff) (Nat.le_refl _)
    (fun _ _ => rfl) supported origins
  simpa only [ProjectionOriginalSupport, joinCofactors] using actual


theorem guardedXor_supported (rename : Nat → Fin v)
    (start : SourcePrefix (parameters := parameters) rename)
    (context : Clause (Fin v)) (a b c d leftOut rightOut : Literal (Fin v))
    (left : XorRows start.state a b leftOut) (right : XorRows start.state c d rightOut)
    (aForward : GuardedTransfer start.state context a c)
    (aBackward : GuardedTransfer start.state context c a)
    (bForward : GuardedTransfer start.state context b d)
    (bBackward : GuardedTransfer start.state context d b)
    (supported : PrefixOriginalSupport rename start)
    (leftOriginal : XorRowsOriginalSupport rename start left)
    (rightOriginal : XorRowsOriginalSupport rename start right)
    (af : GuardedTransferOrigin rename start aForward)
    (ab : GuardedTransferOrigin rename start aBackward)
    (bf : GuardedTransferOrigin rename start bForward)
    (bb : GuardedTransferOrigin rename start bBackward) :
    ProjectionOriginalSupport rename start
      (guardedXor start.state context a b c d leftOut rightOut left right
        aForward aBackward bForward bBackward) := by
  let runBranch := fun (next : State v) (steps : List (Step v))
      (checked : runSteps start.state steps = some next) (x y : Bool) =>
    xorCofactor next context a b c d leftOut rightOut
      (left.afterTrace next steps checked) (right.afterTrace next steps checked)
      (aForward.afterTrace next steps checked) (aBackward.afterTrace next steps checked)
      (bForward.afterTrace next steps checked) (bBackward.afterTrace next steps checked) x y
  have branchSupport := fun next steps checked x y
      (trace : PrefixOriginalSupport rename (start.extend next steps checked)) =>
    xorCofactor_supported rename (start.extend next steps checked) context a b c d leftOut rightOut
      (left.afterTrace next steps checked) (right.afterTrace next steps checked)
      (aForward.afterTrace next steps checked) (aBackward.afterTrace next steps checked)
      (bForward.afterTrace next steps checked) (bBackward.afterTrace next steps checked) x y trace
      (XorRowsOriginalSupport.afterTrace rename start left next steps checked leftOriginal)
      (XorRowsOriginalSupport.afterTrace rename start right next steps checked rightOriginal)
      (GuardedTransferOrigin.afterTrace rename start aForward af next steps checked)
      (GuardedTransferOrigin.afterTrace rename start aBackward ab next steps checked)
      (GuardedTransferOrigin.afterTrace rename start bForward bf next steps checked)
      (GuardedTransferOrigin.afterTrace rename start bBackward bb next steps checked)
  let first := runBranch start.state [] rfl true true
  have one := branchSupport start.state [] rfl true true (by
    simpa only [PrefixOriginalSupport, SourcePrefix.extend, List.append_nil] using supported)
  let second := runBranch first.state first.steps first.checked true false
  have two := branchSupport first.state first.steps first.checked true false (by
    simpa only [ProjectionOriginalSupport, PrefixOriginalSupport, SourcePrefix.extend,
      List.append_nil, first, runBranch] using one.1)
  have firstTwo : runSteps start.state (first.steps ++ second.steps) = some second.state := by
    rw [runSteps_append, first.checked]; exact second.checked
  let third := runBranch second.state (first.steps ++ second.steps) firstTwo false true
  have three := branchSupport second.state (first.steps ++ second.steps) firstTwo false true (by
    simpa only [PrefixOriginalSupport, SourcePrefix.extend, List.append_assoc] using two.1)
  have firstThree : runSteps start.state ((first.steps ++ second.steps) ++ third.steps) = some third.state := by
    rw [runSteps_append, firstTwo]; exact third.checked
  let fourth := runBranch third.state ((first.steps ++ second.steps) ++ third.steps) firstThree false false
  have four := branchSupport third.state ((first.steps ++ second.steps) ++ third.steps)
    firstThree false false (by
      simpa only [PrefixOriginalSupport, SourcePrefix.extend, List.append_assoc] using three.1)
  have tailRun : runSteps second.state (third.steps ++ fourth.steps) = some fourth.state := by
    rw [runSteps_append, third.checked]; exact fourth.checked
  have firstTail : runSteps first.state (second.steps ++ (third.steps ++ fourth.steps)) = some fourth.state := by
    rw [runSteps_append, second.checked]; exact tailRun
  let tt := FoldProjection.afterTrace first.result fourth.state (second.steps ++ (third.steps ++ fourth.steps)) firstTail
  let tf := FoldProjection.afterTrace second.result fourth.state (third.steps ++ fourth.steps) tailRun
  let ft := FoldProjection.afterTrace third.result fourth.state fourth.steps fourth.checked
  let branchPrefix := (start.extend third.state ((first.steps ++ second.steps) ++ third.steps) firstThree).extend
    fourth.state fourth.steps fourth.checked
  have ttOrigin := resultOrigin_append_right _ _ _ (second.steps ++ (third.steps ++ fourth.steps))
    first.result.row.id one.2
  have tfOrigin := resultOrigin_append_right _ _ _ (third.steps ++ fourth.steps) second.result.row.id two.2
  have ftOrigin := resultOrigin_append_right _ _ _ fourth.steps third.result.row.id three.2
  have joinedSupport := joinCofactors_supported rename branchPrefix (context ++ [negate leftOut, rightOut])
    a b tt tf ft fourth.result four.1
    (by simpa only [branchPrefix, SourcePrefix.extend, List.append_assoc, List.nil_append, first, runBranch, tt, FoldProjection.afterTrace] using ttOrigin)
    (by simpa only [branchPrefix, SourcePrefix.extend, List.append_assoc, second, runBranch, tf, FoldProjection.afterTrace] using tfOrigin)
    (by simpa only [branchPrefix, SourcePrefix.extend, List.append_assoc, third, runBranch, ft, FoldProjection.afterTrace] using ftOrigin)
    four.2
  simpa only [ProjectionOriginalSupport, guardedXor, runBranch, first, second, third, fourth,
    branchPrefix, tt, tf, ft, SourcePrefix.extend, List.append_assoc] using joinedSupport


theorem laterMaskNativeRows_supported (rename : Nat → Fin v) (side : Side)
    (position : Fin (laterBuses (parameters := parameters)).length) (channel : Fin parameters.channels)
    (prefixState : SourcePrefix (parameters := parameters) rename) :
    XorRowsOriginalSupport rename prefixState (laterMaskNativeRows rename side position channel prefixState) := by
  exact ⟨Or.inl (laterMaskRows_allowed rename side position channel ⟨0, by change 0 < 4; decide⟩),
    Or.inl (laterMaskRows_allowed rename side position channel ⟨1, by change 1 < 4; decide⟩),
    Or.inl (laterMaskRows_allowed rename side position channel ⟨2, by change 2 < 4; decide⟩),
    Or.inl (laterMaskRows_allowed rename side position channel ⟨3, by change 3 < 4; decide⟩)⟩

theorem laterMaskPairFromStages_supported (rename : Nat → Fin v) (context : Clause (Fin v))
    (position : Fin (laterBuses (parameters := parameters)).length) (channel : Fin parameters.channels)
    (start : SourcePrefix (parameters := parameters) rename)
    (flags : DirectionPair start.state context (laterFlagOutput rename .healthy position)
      (laterFlagOutput rename .faulty position))
    (absent : DirectionPair start.state context (laterAbsentOutput rename .healthy position channel)
      (laterAbsentOutput rename .faulty position channel))
    (supported : PrefixOriginalSupport rename start)
    (flagsOriginal : DirectionPairOrigin rename start flags)
    (absentOriginal : DirectionPairOrigin rename start absent) :
    PairedProjectionOriginalSupport rename start
      (laterMaskPairFromStages rename context position channel start flags absent) := by
  let flagInputs : DirectionPair start.state context (laterMaskFlag rename .healthy position channel)
      (laterMaskFlag rename .faulty position channel) := by
    simpa only [laterMaskFlag_eq_flagOutput] using flags
  let absentInputs : DirectionPair start.state context (laterMaskAbsent rename .healthy position channel)
      (laterMaskAbsent rename .faulty position channel) := by
    simpa only [laterMaskAbsent_eq_absentOutput] using absent
  have flagOrigin : DirectionPairOrigin rename start flagInputs := by
    dsimp only [flagInputs]
    apply directionPairOrigin_mpr rename start
      (laterMaskFlag_eq_flagOutput rename .healthy position channel).symm
      (laterMaskFlag_eq_flagOutput rename .faulty position channel).symm
    exact flagsOriginal
  have absentOrigin : DirectionPairOrigin rename start absentInputs := by
    dsimp only [absentInputs]
    apply directionPairOrigin_mpr rename start
      (laterMaskAbsent_eq_absentOutput rename .healthy position channel).symm
      (laterMaskAbsent_eq_absentOutput rename .faulty position channel).symm
    exact absentOriginal
  let left := laterMaskNativeRows rename .healthy position channel start
  let right := laterMaskNativeRows rename .faulty position channel start
  have leftOrigin := laterMaskNativeRows_supported rename .healthy position channel start
  have rightOrigin := laterMaskNativeRows_supported rename .faulty position channel start
  let first := guardedXor start.state context _ _ _ _ _ _ left right
    flagInputs.forward flagInputs.backward absentInputs.forward absentInputs.backward
  have firstSupport := guardedXor_supported rename start context _ _ _ _ _ _ left right
    flagInputs.forward flagInputs.backward absentInputs.forward absentInputs.backward
    supported leftOrigin rightOrigin flagOrigin.1 flagOrigin.2 absentOrigin.1 absentOrigin.2
  let current := start.extend first.state first.steps first.checked
  let nextFlags := flagInputs.afterTrace first.state first.steps first.checked
  let nextAbsent := absentInputs.afterTrace first.state first.steps first.checked
  have nextFlagOrigin := DirectionPairOrigin.afterTrace rename start flagInputs flagOrigin
    first.state first.steps first.checked
  have nextAbsentOrigin := DirectionPairOrigin.afterTrace rename start absentInputs absentOrigin
    first.state first.steps first.checked
  let second := guardedXor first.state context _ _ _ _ _ _
    (right.afterTrace first.state first.steps first.checked)
    (left.afterTrace first.state first.steps first.checked)
    nextFlags.backward nextFlags.forward nextAbsent.backward nextAbsent.forward
  have secondSupport := guardedXor_supported rename current context _ _ _ _ _ _
    (right.afterTrace first.state first.steps first.checked)
    (left.afterTrace first.state first.steps first.checked)
    nextFlags.backward nextFlags.forward nextAbsent.backward nextAbsent.forward firstSupport.1
    (XorRowsOriginalSupport.afterTrace rename start right first.state first.steps first.checked rightOrigin)
    (XorRowsOriginalSupport.afterTrace rename start left first.state first.steps first.checked leftOrigin)
    nextFlagOrigin.2 nextFlagOrigin.1 nextAbsentOrigin.2 nextAbsentOrigin.1
  have forward := resultOrigin_append_right (formula parameters).clauses.size
    (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
    (start.steps ++ first.steps) second.steps first.result.row.id firstSupport.2
  simpa only [PairedProjectionOriginalSupport, PrefixOriginalSupport, laterMaskPairFromStages, flagInputs, absentInputs,
    left, right, first, current, nextFlags, nextAbsent, second, DirectionPairOrigin,
    GuardedTransferOrigin, SourcePrefix.extend, List.append_assoc, FoldProjection.afterTrace] using
    And.intro secondSupport.1 (And.intro forward secondSupport.2)


theorem laterMaskChannelFromBanks_supported (rename : Nat → Fin v)
    (context : Clause (Fin v))
    (position : Fin (laterBuses (parameters := parameters)).length) (channel : Fin parameters.channels)
    (start : SourcePrefix (parameters := parameters) rename)
    (terms : DirectionPair start.state context (laterTermOutput rename .healthy position channel)
      (laterTermOutput rename .faulty position channel))
    (flags : DirectionPair start.state context (laterFlagOutput rename .healthy position)
      (laterFlagOutput rename .faulty position))
    (supported : PrefixOriginalSupport rename start)
    (termsOriginal : DirectionPairOrigin rename start terms)
    (flagsOriginal : DirectionPairOrigin rename start flags) :
    PairedProjectionOriginalSupport rename start
      (laterMaskChannelFromBanks rename context position channel start terms flags) := by
  let first := laterAbsentPairFromTerm rename context position channel start terms
  have firstSupport := laterAbsentPairFromTerm_supported rename context position channel start terms
    supported termsOriginal
  let nextPrefix := start.extend first.state first.steps first.checked
  let second := laterMaskPairFromStages rename context position channel nextPrefix
    (flags.afterTrace first.state first.steps first.checked) first.pair
  have secondSupport := laterMaskPairFromStages_supported rename context position channel nextPrefix
    (flags.afterTrace first.state first.steps first.checked) first.pair firstSupport.1
    (DirectionPairOrigin.afterTrace rename start flags flagsOriginal first.state first.steps first.checked)
    firstSupport.2
  let joined := start.extend second.state (first.steps ++ second.steps) (by
    rw [runSteps_append, first.checked]
    exact second.checked)
  have sameSteps : nextPrefix.steps ++ second.steps = joined.steps := by
    simp only [nextPrefix, joined, SourcePrefix.extend, List.append_assoc]
  have origin := DirectionPairOrigin.same_steps rename second.state
    (nextPrefix.steps ++ second.steps) joined.steps sameSteps
    (nextPrefix.extend second.state second.steps second.checked).checked joined.checked second.pair secondSupport.2
  change PrefixOriginalSupport rename joined ∧ DirectionPairOrigin rename joined second.pair
  refine ⟨?_, origin⟩
  simpa only [PrefixOriginalSupport, joined, nextPrefix, second, SourcePrefix.extend, List.append_assoc]
    using secondSupport.1

def maskBankPrefix (bank : MaskBank (parameters := parameters) rename flag position inputs done) :
    SourcePrefix (parameters := parameters) rename :=
  inputs.checkedPrefix.extend bank.state bank.steps bank.checked

def MaskBankOriginalSupport (rename : Nat → Fin v) (flag : Bool)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (inputs : MaskInputs (parameters := parameters) rename flag position)
    {done : List (Fin parameters.channels)} (bank : MaskBank rename flag position inputs done) : Prop :=
  PrefixOriginalSupport rename (maskBankPrefix bank) ∧
    ∀ channel member, DirectionPairOrigin rename (maskBankPrefix bank) (bank.pairs channel member)

theorem MaskInputsOriginalSupport.afterTrace (rename : Nat → Fin v) (flag : Bool)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (inputs : MaskInputs (parameters := parameters) rename flag position)
    (next : State v) (steps : List (Step v))
    (checked : runSteps inputs.checkedPrefix.state steps = some next)
    (original : MaskInputsOriginalSupport rename flag position inputs)
    (supported : PrefixOriginalSupport rename (inputs.checkedPrefix.extend next steps checked)) :
    MaskInputsOriginalSupport rename flag position (inputs.afterTrace next steps checked) := by
  refine ⟨supported, ?_, ?_⟩
  · intro channel
    exact DirectionPairOrigin.afterTrace rename inputs.checkedPrefix
      (inputs.terms channel) (original.2.1 channel) next steps checked
  · exact DirectionPairOrigin.afterTrace rename inputs.checkedPrefix
      inputs.flags original.2.2 next steps checked


def maskBankStepKernel (rename : Nat → Fin v) (flag : Bool)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (inputs : MaskInputs (parameters := parameters) rename flag position)
    (done : List (Fin parameters.channels)) (bank : MaskBank rename flag position inputs done)
    (channel : Fin parameters.channels)
    (added : PairedProjection bank.state (equalFlagContext (parameters := parameters) rename flag)
      (laterMaskOutput rename .healthy position channel)
      (laterMaskOutput rename .faulty position channel) 26) :
    MaskBank rename flag position inputs (channel :: done) := by
  refine ⟨added.state, bank.steps ++ added.steps, ?_, ?_, ?_⟩
  · rw [runSteps_append, bank.checked]
    exact added.checked
  · intro query member
    by_cases same : query = channel
    · subst query
      exact added.pair
    · have old : query ∈ done := (List.mem_cons.mp member).resolve_left same
      exact (bank.pairs query old).afterTrace added.state added.steps added.checked
  · have one := bank.count
    have two := added.count
    simp only [List.length_append, List.length_cons]
    omega

theorem maskBankStep_kernel_eq (rename : Nat → Fin v) (flag : Bool)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (inputs : MaskInputs (parameters := parameters) rename flag position)
    (done : List (Fin parameters.channels)) (bank : MaskBank rename flag position inputs done)
    (channel : Fin parameters.channels) :
    maskBankStep rename flag position inputs done bank channel =
      maskBankStepKernel rename flag position inputs done bank channel
        (laterMaskChannelFromBanks rename (equalFlagContext (parameters := parameters) rename flag)
          position channel (inputs.afterTrace bank.state bank.steps bank.checked).checkedPrefix
          ((inputs.afterTrace bank.state bank.steps bank.checked).terms channel)
          (inputs.afterTrace bank.state bank.steps bank.checked).flags) := rfl

theorem maskBankStepKernel_supported (rename : Nat → Fin v) (flag : Bool)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (inputs : MaskInputs (parameters := parameters) rename flag position)
    (done : List (Fin parameters.channels))
    (bank : MaskBank rename flag position inputs done) (channel : Fin parameters.channels)
    (added : PairedProjection bank.state (equalFlagContext (parameters := parameters) rename flag)
      (laterMaskOutput rename .healthy position channel) (laterMaskOutput rename .faulty position channel)
      26)
    (bankSupport : MaskBankOriginalSupport rename flag position inputs bank)
    (addedSupport : PairedProjectionOriginalSupport rename (maskBankPrefix bank) added) :
    MaskBankOriginalSupport rename flag position inputs
      (maskBankStepKernel rename flag position inputs done bank channel added) := by
  let joined := inputs.checkedPrefix.extend added.state (bank.steps ++ added.steps) (by
    rw [runSteps_append, bank.checked]
    exact added.checked)
  have joinedSupport : PrefixOriginalSupport rename joined := by
    simpa only [PairedProjectionOriginalSupport, PrefixOriginalSupport, PrefixOriginalSupport, joined,
      maskBankPrefix, SourcePrefix.extend, List.append_assoc] using addedSupport.1
  refine ⟨?_, ?_⟩
  · simpa only [maskBankPrefix, maskBankStepKernel, PrefixOriginalSupport, joined,
      SourcePrefix.extend] using joinedSupport
  · intro query member
    by_cases same : query = channel
    · subst query
      have stepsEqual : (maskBankPrefix bank).steps ++ added.steps = joined.steps := by
        simp only [joined, maskBankPrefix, SourcePrefix.extend, List.append_assoc]
      have carried := DirectionPairOrigin.same_steps rename added.state
        ((maskBankPrefix bank).steps ++ added.steps) joined.steps stepsEqual
        ((maskBankPrefix bank).extend added.state added.steps added.checked).checked joined.checked
        added.pair addedSupport.2
      simp only [maskBankStepKernel, maskBankPrefix]
      dsimp only [SourcePrefix.extend]
      rw [dite_eq_left (show True from trivial)]
      change DirectionPairOrigin rename joined added.pair
      exact carried
    · have old : query ∈ done := (List.mem_cons.mp member).resolve_left same
      have origin := DirectionPairOrigin.afterTrace rename (maskBankPrefix bank)
        (bank.pairs query old) (bankSupport.2 query old) added.state added.steps added.checked
      have stepsEqual : (maskBankPrefix bank).steps ++ added.steps = joined.steps := by
        simp only [maskBankPrefix, joined, SourcePrefix.extend, List.append_assoc]
      have carried := DirectionPairOrigin.same_steps rename added.state
        ((maskBankPrefix bank).steps ++ added.steps) joined.steps stepsEqual
        ((maskBankPrefix bank).extend added.state added.steps added.checked).checked joined.checked
        ((bank.pairs query old).afterTrace added.state added.steps added.checked) origin
      simp only [maskBankStepKernel, maskBankPrefix]
      dsimp only [SourcePrefix.extend]
      rw [dite_eq_right same]
      change DirectionPairOrigin rename joined
        ((bank.pairs query old).afterTrace added.state added.steps added.checked)
      exact carried


theorem maskBankStep_supported (rename : Nat → Fin v) (flag : Bool)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (inputs : MaskInputs (parameters := parameters) rename flag position)
    (done : List (Fin parameters.channels)) (bank : MaskBank rename flag position inputs done)
    (channel : Fin parameters.channels)
    (inputsSupport : MaskInputsOriginalSupport rename flag position inputs)
    (bankSupport : MaskBankOriginalSupport rename flag position inputs bank) :
    MaskBankOriginalSupport rename flag position inputs
      (maskBankStep rename flag position inputs done bank channel) := by
  let extended := inputs.afterTrace bank.state bank.steps bank.checked
  have extendedSupport := MaskInputsOriginalSupport.afterTrace rename flag position inputs
    bank.state bank.steps bank.checked inputsSupport bankSupport.1
  let added := laterMaskChannelFromBanks rename (equalFlagContext (parameters := parameters) rename flag)
    position channel extended.checkedPrefix (extended.terms channel) extended.flags
  have addedSupport := laterMaskChannelFromBanks_supported rename _ position channel extended.checkedPrefix
    (extended.terms channel) extended.flags extendedSupport.1
    (extendedSupport.2.1 channel) extendedSupport.2.2
  rw [maskBankStep_kernel_eq]
  exact maskBankStepKernel_supported rename flag position inputs done bank channel added bankSupport addedSupport

theorem buildMaskBank_supported (rename : Nat → Fin v) (flag : Bool)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (inputs : MaskInputs (parameters := parameters) rename flag position)
    (channels : List (Fin parameters.channels))
    (supported : MaskInputsOriginalSupport rename flag position inputs) :
    MaskBankOriginalSupport rename flag position inputs
      (buildMaskBank rename flag position inputs channels) := by
  induction channels with
  | nil =>
      unfold MaskBankOriginalSupport
      constructor
      · simpa only [MaskBankOriginalSupport, maskBankPrefix, buildMaskBank,
          PrefixOriginalSupport, SourcePrefix.extend, List.append_nil] using supported.1
      · intro channel member
        exact False.elim (List.not_mem_nil member)
  | cons channel channels ih =>
      exact maskBankStep_supported rename flag position inputs channels
        (buildMaskBank rename flag position inputs channels) channel supported ih


def CurrentBusProjectionOriginalSupport (rename : Nat → Fin v) (flag : Bool)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (table : BusMaskTable (parameters := parameters) rename flag position.val)
    (projection : CurrentBusProjection rename flag position table) : Prop :=
  PrefixOriginalSupport rename
    (table.checkedPrefix.extend projection.state projection.steps projection.checked) ∧
  ∀ channel, DirectionPairOrigin rename
    (table.checkedPrefix.extend projection.state projection.steps projection.checked)
    (projection.pairs channel)

theorem currentBusFromTable_supported (rename : Nat → Fin v) (flag : Bool)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (table : BusMaskTable (parameters := parameters) rename flag position.val)
    (supported : BusMaskTableOriginalSupport rename flag table) :
    CurrentBusProjectionOriginalSupport rename flag position table
      (currentBusFromTable rename flag position table) := by
  let terms := buildTermBank rename flag position table (List.finRange parameters.channels)
  have termSupport := buildTermBank_supported rename flag position table (List.finRange parameters.channels) supported
  let flags := laterFlagPairFromTerms rename flag position table.checkedPrefix terms
  have flagSupport := laterFlagPairFromTerms_supported rename flag position table.checkedPrefix terms termSupport
  let inputs : MaskInputs (parameters := parameters) rename flag position :=
    ⟨terms.checkedPrefix.extend flags.state flags.steps flags.checked,
      fun channel => (terms.pairs channel (by simp)).afterTrace flags.state flags.steps flags.checked, flags.pair⟩
  have inputsSupport : MaskInputsOriginalSupport rename flag position inputs := by
    refine ⟨flagSupport.1, ?_, flagSupport.2⟩
    intro channel
    exact DirectionPairOrigin.afterTrace rename terms.checkedPrefix
      (terms.pairs channel (by simp)) (termSupport.2 channel (by simp))
      flags.state flags.steps flags.checked
  let masks := buildMaskBank rename flag position inputs (List.finRange parameters.channels)
  have maskSupport := buildMaskBank_supported rename flag position inputs (List.finRange parameters.channels) inputsSupport
  let joined := table.checkedPrefix.extend masks.state ((terms.steps ++ flags.steps) ++ masks.steps) (by
    rw [runSteps_append, runSteps_append, terms.checked]
    simp only [Option.bind_some, flags.checked]
    exact masks.checked)
  have sameSteps : (maskBankPrefix masks).steps = joined.steps := by
    simp only [maskBankPrefix, joined, inputs, TermBank.checkedPrefix, SourcePrefix.extend, List.append_assoc]
  constructor
  · simpa only [CurrentBusProjectionOriginalSupport, currentBusFromTable,
      terms, flags, inputs, masks, maskBankPrefix, TermBank.checkedPrefix,
      SourcePrefix.extend, PrefixOriginalSupport, List.append_assoc] using maskSupport.1
  · intro channel
    have origin := DirectionPairOrigin.same_steps rename masks.state
      (maskBankPrefix masks).steps joined.steps sameSteps (maskBankPrefix masks).checked joined.checked
      (masks.pairs channel (by simp)) (maskSupport.2 channel (by simp))
    -- Map the exact completed mask handle to its stagesBefore successor slot.
    have inputEq : laterMaskOutput rename .healthy position channel =
        mapLiteral rename ((stagesBefore (parameters := parameters) .healthy (position.val + 1)).slots
          (.internal (.mask .healthy (laterBuses (parameters := parameters))[position.val] channel))) := by
      simp only [stagesBefore_current_mask, laterMaskOutput]
    have outputEq : laterMaskOutput rename .faulty position channel =
        mapLiteral rename ((stagesBefore (parameters := parameters) .faulty (position.val + 1)).slots
          (.internal (.mask .faulty (laterBuses (parameters := parameters))[position.val] channel))) := by
      simp only [stagesBefore_current_mask, laterMaskOutput]
    -- Scalar branchPrefix and handle transports preserve the actual certificate IDs.
    dsimp only [currentBusFromTable]
    apply directionPairOrigin_mpr rename _ inputEq outputEq
    change DirectionPairOrigin rename joined (masks.pairs channel (by simp))
    exact origin


theorem busMaskTableInitial_supported (rename : Nat → Fin v) (flag : Bool) :
    BusMaskTableOriginalSupport rename flag (busMaskTableInitial (parameters := parameters) rename flag) := by
  let seed := firstBusTable (parameters := parameters) rename flag
  have seedSupport := buildInitialMaskTable_supported rename flag (List.finRange parameters.channels)
  constructor
  · exact seedSupport.1
  · intro bus member channel
    have same : bus = parameters.firstBus := by simpa using member
    subst bus
    dsimp only [busMaskTableInitial]
    apply directionPairOrigin_mpr rename seed.checkedPrefix
      (stagesBefore_zero_first_mask rename .healthy channel).symm rfl
    apply directionPairOrigin_mpr rename seed.checkedPrefix rfl
      (stagesBefore_zero_first_mask rename .faulty channel).symm
    exact seedSupport.2 channel (by simp)

theorem busTableAdvance_supported (rename : Nat → Fin v) (flag : Bool)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (table : BusMaskTable (parameters := parameters) rename flag position.val)
    (supported : BusMaskTableOriginalSupport rename flag table) :
    BusMaskTableOriginalSupport rename flag (busTableAdvance rename flag position table) := by
  let added := currentBusFromTable rename flag position table
  have addedSupport := currentBusFromTable_supported rename flag position table supported
  let nextPrefix := table.checkedPrefix.extend added.state added.steps added.checked
  constructor
  · exact addedSupport.1
  · intro query member channel
    by_cases same : query = (laterBuses (parameters := parameters))[position.val]
    · subst query
      dsimp only [busTableAdvance]
      dsimp only [SourcePrefix.extend]
      rw [dite_eq_left rfl]
      exact addedSupport.2 channel
    · have oldMem : query ∈ parameters.firstBus :: (laterBuses (parameters := parameters)).take position.val := by
        rw [List.take_succ_eq_append_getElem position.isLt] at member
        simp only [List.mem_cons, List.mem_append, List.mem_singleton] at member ⊢
        aesop
      have carried := DirectionPairOrigin.afterTrace rename table.checkedPrefix
        (table.directions query oldMem channel) (supported.2 query oldMem channel)
        added.state added.steps added.checked
      dsimp only [busTableAdvance, SourcePrefix.extend]
      rw [dite_eq_right same]
      apply directionPairOrigin_mpr rename nextPrefix (by rw [stagesBefore_succ]) rfl
      apply directionPairOrigin_mpr rename nextPrefix rfl (by rw [stagesBefore_succ])
      apply directionPairOrigin_mpr rename nextPrefix
        (by rw [laterBus_mask_other .healthy .healthy _ query channel same]) rfl
      apply directionPairOrigin_mpr rename nextPrefix rfl
        (by rw [laterBus_mask_other .faulty .faulty _ query channel same])
      exact carried

theorem buildBusPrefix_supported (rename : Nat → Fin v) (flag : Bool)
    (count : Nat) (bound : count ≤ (laterBuses (parameters := parameters)).length) :
    BusMaskTableOriginalSupport rename flag (buildBusPrefix (parameters := parameters) rename flag count bound) := by
  induction count with
  | zero => exact busMaskTableInitial_supported rename flag
  | succ count ih =>
      exact busTableAdvance_supported rename flag ⟨count, by omega⟩
        (buildBusPrefix rename flag count (by omega)) (ih (by omega))

theorem allBusMasks_supported (rename : Nat → Fin v) (flag : Bool) :
    BusMaskTableOriginalSupport rename flag (allBusMasks (parameters := parameters) rename flag) :=
  buildBusPrefix_supported rename flag _ (Nat.le_refl _)


end Controller.NativeProof.SourceEqualSchedule
