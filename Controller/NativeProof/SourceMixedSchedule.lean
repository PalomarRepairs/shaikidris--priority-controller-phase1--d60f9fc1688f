module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.SourceMixedScheduleFoundation

@[expose] public section

/-! Causal suffix-bank and descending selector schedule proofs. -/
namespace Controller.NativeProof.SourceMixedSchedule
open Controller.CNF Controller.Resolution Controller.Native Controller.Native.SourceController
open Controller.NativeProof.SourceFoldOccurrences Controller.NativeProof.SourceStageCongruence
open Controller.NativeProof.SourceSlotFrames Controller.NativeProof.SourceRoleFrames
open Controller.NativeProof.SourceSuffixSelector Controller.NativeProof.SourceMixedSelector
open Controller.NativeProof.FoldProjection Controller.NativeProof.SourceFoldProjection
open Controller.NativeProof.SourceStagePolarity Controller.NativeProof.SourceStageXor
open Controller.NativeProof.SourceBusAdvance Controller.NativeProof.SourceMismatchAdvance
open Controller.NativeProof.SourceFoldProvenance
variable {parameters : Parameters} {v : Nat}
open Controller.NativeProof.SourceFoldOwners Controller.NativeProof.SourceQualifierOccurrences
open Controller.NativeProof.SourceFoldProvenance Controller.NativeProof.SourceMismatchHandles
def suffixBankAfter (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (remaining : Nat) (position : Fin (laterBuses (parameters := parameters)).length)
    (positionValue : position.val = remaining - 1) (outputs : Clause (Fin v)) (budget : Nat)
    (closed : SubclauseProjection prefixState.state
      (mixedContext (parameters := parameters) rename ++
        negate (laterFlagOutput rename .faulty position) :: outputs) budget)
    (bank : ∀ later : Fin (laterBuses (parameters := parameters)).length,
      remaining ≤ later.val → AvailableSubclause prefixState.state
        (mixedContext (parameters := parameters) rename ++
          negate (laterFlagOutput rename .faulty later) :: outputs)) :
    ∀ later : Fin (laterBuses (parameters := parameters)).length,
      remaining - 1 ≤ later.val → AvailableSubclause closed.state
        (mixedContext (parameters := parameters) rename ++
          negate (laterFlagOutput rename .faulty later) :: outputs) := by
  intro later order
  if same : later.val = position.val then
    have equal : later = position := Fin.ext same
    exact equal.symm ▸ closed.result
  else
    have previous : remaining ≤ later.val := by omega
    exact FoldProjection.afterTrace (bank later previous)
      closed.state closed.steps closed.checked

theorem suffixBankAfter_origins (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (remaining : Nat) (position : Fin (laterBuses (parameters := parameters)).length)
    (positionValue : position.val = remaining - 1) (outputs : Clause (Fin v)) (budget : Nat)
    (closed : SubclauseProjection prefixState.state
      (mixedContext (parameters := parameters) rename ++
        negate (laterFlagOutput rename .faulty position) :: outputs) budget)
    (bank : ∀ later : Fin (laterBuses (parameters := parameters)).length,
      remaining ≤ later.val → AvailableSubclause prefixState.state
        (mixedContext (parameters := parameters) rename ++
          negate (laterFlagOutput rename .faulty later) :: outputs))
    (closedOrigin : Controller.NativeProof.SourceMismatchHandles.ResultOrigin
      (formula parameters).clauses.size
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      (prefixState.steps ++ closed.steps) closed.result.row.id)
    (bankOrigin : ∀ later order, Controller.NativeProof.SourceMismatchHandles.ResultOrigin
      (formula parameters).clauses.size
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      prefixState.steps (bank later order).row.id) :
    ∀ later order, Controller.NativeProof.SourceMismatchHandles.ResultOrigin
      (formula parameters).clauses.size
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      (prefixState.steps ++ closed.steps)
      (suffixBankAfter rename prefixState remaining position positionValue outputs budget closed bank later order).row.id := by
  intro later order
  by_cases same : later.val = position.val
  · have equal : later = position := Fin.ext same
    subst later
    have idEqual :
        (suffixBankAfter rename prefixState remaining position positionValue outputs budget
          closed bank position order).row.id = closed.result.row.id := by
      simp only [suffixBankAfter, subclause_dite_id]
      exact dite_eq_left trivial
    rw [idEqual]
    exact closedOrigin
  · have previous : remaining ≤ later.val := by omega
    have origin := resultOrigin_append_right (formula parameters).clauses.size
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      prefixState.steps closed.steps (bank later previous).row.id (bankOrigin later previous)
    have idEqual :
        (suffixBankAfter rename prefixState remaining position positionValue outputs budget
          closed bank later order).row.id = (bank later previous).row.id := by
      simp only [suffixBankAfter, subclause_dite_id]
      rw [dite_eq_right same]
      rfl
    rw [idEqual]
    exact origin


theorem descendingFlags_zero_steps (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (bounded : 0 ≤ (laterBuses (parameters := parameters)).length)
    (bank : ∀ later : Fin (laterBuses (parameters := parameters)).length,
      0 ≤ later.val → AvailableSubclause prefixState.state
        (mixedContext (parameters := parameters) rename ++
          negate (laterFlagOutput rename .faulty later) ::
            qualifierOutputs (parameters := parameters) rename)) :
    (descendingFlags rename prefixState 0 bounded bank).steps = [] := by
  rw [descendingFlags.eq_def, dite_eq_left rfl]

theorem descendingFlags_zero_bank_id (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (bounded : 0 ≤ (laterBuses (parameters := parameters)).length)
    (bank : ∀ later : Fin (laterBuses (parameters := parameters)).length,
      0 ≤ later.val → AvailableSubclause prefixState.state
        (mixedContext (parameters := parameters) rename ++
          negate (laterFlagOutput rename .faulty later) ::
            qualifierOutputs (parameters := parameters) rename))
    (later : Fin (laterBuses (parameters := parameters)).length) :
    ((descendingFlags rename prefixState 0 bounded bank).bank later).row.id =
      (bank later (Nat.zero_le later.val)).row.id := by
  rw [descendingFlags.eq_def, dite_eq_left rfl]

theorem descendingFlags_step_fields (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (remaining : Nat) (bounded : remaining ≤ (laterBuses (parameters := parameters)).length)
    (bank : ∀ later : Fin (laterBuses (parameters := parameters)).length,
      remaining ≤ later.val → AvailableSubclause prefixState.state
        (mixedContext (parameters := parameters) rename ++
          negate (laterFlagOutput rename .faulty later) ::
            qualifierOutputs (parameters := parameters) rename))
    (nonzero : remaining ≠ 0) :
    let position : Fin (laterBuses (parameters := parameters)).length :=
      ⟨remaining - 1, by omega⟩
    let localBank : ClosedFlags rename prefixState position
        (qualifierOutputs (parameters := parameters) rename) :=
      fun later order => bank later (by dsimp only [position] at order; omega)
    let closed := closeFlagAt rename prefixState position localBank
    let current := prefixState.extend closed.state closed.steps closed.checked
    let nextBank := suffixBankAfter rename prefixState remaining position rfl
      (qualifierOutputs (parameters := parameters) rename)
      (2 * (laterFlagTree rename .faulty position).nodes +
        parameters.channels * (qualifierBudget parameters + 1)) closed bank
    let tail := descendingFlags rename current (remaining - 1) (by omega) nextBank
    (descendingFlags rename prefixState remaining bounded bank).steps =
        closed.steps ++ tail.steps ∧
      ∀ later, ((descendingFlags rename prefixState remaining bounded bank).bank later).row.id =
        (tail.bank later).row.id := by
  -- Reduce only the bank alias before comparing the recursive call fields.
  -- Its proof arguments are irrelevant; its two data branches match the runtime bank.
  constructor
  · rw [descendingFlags.eq_def, dite_eq_right nonzero]
    delta suffixBankAfter
    rfl
  · intro later
    rw [descendingFlags.eq_def, dite_eq_right nonzero]
    delta suffixBankAfter
    rfl

theorem descendingFlags_supported (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (remaining : Nat) (bounded : remaining ≤ (laterBuses (parameters := parameters)).length)
    (bank : ∀ later : Fin (laterBuses (parameters := parameters)).length,
      remaining ≤ later.val → AvailableSubclause prefixState.state
        (mixedContext (parameters := parameters) rename ++
          negate (laterFlagOutput rename .faulty later) ::
            qualifierOutputs (parameters := parameters) rename))
    (supported : PrefixOriginalSupport rename prefixState)
    (bankSupported : ∀ later order,
      Controller.NativeProof.SourceMismatchHandles.ResultOrigin
        (formula parameters).clauses.size
        (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
        prefixState.steps (bank later order).row.id) :
    FlagClosureOriginalSupport rename prefixState remaining
      (descendingFlags rename prefixState remaining bounded bank) := by
  induction remaining using Nat.strong_induction_on generalizing prefixState with
  | h remaining ih =>
    by_cases zero : remaining = 0
    · subst remaining
      unfold FlagClosureOriginalSupport
      constructor
      · rw [descendingFlags_zero_steps, List.append_nil]
        exact supported
      · intro later
        rw [descendingFlags_zero_steps, descendingFlags_zero_bank_id, List.append_nil]
        exact bankSupported later (Nat.zero_le later.val)
    · let position : Fin (laterBuses (parameters := parameters)).length :=
        ⟨remaining - 1, by omega⟩
      let localBank : ClosedFlags rename prefixState position
          (qualifierOutputs (parameters := parameters) rename) :=
        fun later order => bank later (by dsimp only [position] at order; omega)
      have localBankSupport : ClosedFlagsOriginalSupport rename prefixState position
          (qualifierOutputs (parameters := parameters) rename) localBank := by
        intro later order
        exact bankSupported later (by dsimp only [position] at order; omega)
      let closed := closeFlagAt rename prefixState position localBank
      have closedSupport := closeFlagAt_supported rename prefixState position localBank
        supported localBankSupport
      let current := prefixState.extend closed.state closed.steps closed.checked
      let nextBank := suffixBankAfter rename prefixState remaining position rfl
        (qualifierOutputs (parameters := parameters) rename)
        (2 * (laterFlagTree rename .faulty position).nodes +
          parameters.channels * (qualifierBudget parameters + 1)) closed bank
      have nextBankSupport := suffixBankAfter_origins rename prefixState remaining position rfl
        (qualifierOutputs (parameters := parameters) rename)
        (2 * (laterFlagTree rename .faulty position).nodes +
          parameters.channels * (qualifierBudget parameters + 1)) closed bank
        closedSupport.2 bankSupported
      have tailSupport := ih (remaining - 1) (by omega) current (by omega) nextBank
        closedSupport.1 nextBankSupport
      let tail := descendingFlags rename current (remaining - 1) (by omega) nextBank
      have fields := descendingFlags_step_fields rename prefixState remaining bounded bank zero
      have stepsEqual :
          (descendingFlags rename prefixState remaining bounded bank).steps =
            closed.steps ++ tail.steps := fields.1
      have bankIdEqual : ∀ later,
          ((descendingFlags rename prefixState remaining bounded bank).bank later).row.id =
            (tail.bank later).row.id := fields.2
      unfold FlagClosureOriginalSupport at tailSupport ⊢
      constructor
      · rw [stepsEqual]
        simpa only [current, SourcePrefix.extend, List.append_assoc, tail] using tailSupport.1
      · intro later
        rw [stepsEqual, bankIdEqual]
        simpa only [current, SourcePrefix.extend, List.append_assoc, tail] using tailSupport.2 later


theorem subclause_indices_cast_id {beforeState afterState : State v}
    {beforeClause afterClause : Clause (Fin v)}
    (stateEqual : beforeState = afterState) (clauseEqual : beforeClause = afterClause)
    (typeEqual : AvailableSubclause beforeState beforeClause =
      AvailableSubclause afterState afterClause)
    (value : AvailableSubclause beforeState beforeClause) :
    (Eq.mp typeEqual value).row.id = value.row.id := by
  subst afterState
  subst afterClause
  have same : typeEqual = rfl := Subsingleton.elim _ _
  rw [same]
  rfl

theorem subclause_indices_mpr_id {beforeState afterState : State v}
    {beforeClause afterClause : Clause (Fin v)}
    (stateEqual : beforeState = afterState) (clauseEqual : beforeClause = afterClause)
    (typeEqual : AvailableSubclause beforeState beforeClause =
      AvailableSubclause afterState afterClause)
    (value : AvailableSubclause afterState afterClause) :
    (Eq.mpr typeEqual value).row.id = value.row.id := by
  subst afterState
  subst afterClause
  have same : typeEqual = rfl := Subsingleton.elim _ _
  rw [same]
  rfl

def AllClosedFlagsOriginalSupport (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename) (outputs : Clause (Fin v))
    (bank : AllClosedFlags rename prefixState outputs) : Prop :=
  ∀ later, Controller.NativeProof.SourceMismatchHandles.ResultOrigin
    (formula parameters).clauses.size
    (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
    prefixState.steps (bank later).row.id


theorem AllClosedFlagsOriginalSupport.afterTrace
    (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (outputs : Clause (Fin v))
    (bank : AllClosedFlags rename prefixState outputs)
    (original : AllClosedFlagsOriginalSupport rename prefixState outputs bank)
    (next : State v) (steps : List (Step v))
    (checked : runSteps prefixState.state steps = some next) :
    AllClosedFlagsOriginalSupport rename (prefixState.extend next steps checked)
      outputs (bank.afterTrace next steps checked) := by
  intro later
  have carried := resultOrigin_append_right (formula parameters).clauses.size
    (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
    prefixState.steps steps (bank later).row.id (original later)
  change Controller.NativeProof.SourceMismatchHandles.ResultOrigin
    (formula parameters).clauses.size
    (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
    (prefixState.steps ++ steps) (bank later).row.id
  exact carried


theorem eliminateAllFlagLeaves_supported (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (outputs : Clause (Fin v))
    (bank : AllClosedFlags rename prefixState outputs)
    (context : Clause (Fin v)) (output : Literal (Fin v))
    (inputs : List (Literal (Fin v))) (budget : Nat)
    (parent : AvailableSubclause prefixState.state (context ++ output :: inputs.map negate))
    (reason : ∀ (current : SourcePrefix (parameters := parameters) rename)
      (currentBank : AllClosedFlags rename current outputs) (index : Fin inputs.length),
      SubclauseProjection current.state (inputs[index.val] :: context) budget)
    (supported : PrefixOriginalSupport rename prefixState)
    (bankSupported : AllClosedFlagsOriginalSupport rename prefixState outputs bank)
    (parentOrigin : Controller.NativeProof.SourceMismatchHandles.ResultOrigin
      (formula parameters).clauses.size
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      prefixState.steps parent.row.id)
    (reasonSupported : ∀ current currentBank index,
      PrefixOriginalSupport rename current →
      AllClosedFlagsOriginalSupport rename current outputs currentBank →
      ProjectionOriginalSupport rename current (reason current currentBank index)) :
    ProjectionOriginalSupport rename prefixState
      (eliminateAllFlagLeaves rename prefixState outputs bank context output inputs budget parent reason) := by
  induction inputs generalizing prefixState with
  | nil =>
    have stepsEqual :
        (eliminateAllFlagLeaves rename prefixState outputs bank context output [] budget parent reason).steps = [] := by
      simp only [eliminateAllFlagLeaves]
    have idEqual :
        (eliminateAllFlagLeaves rename prefixState outputs bank context output [] budget parent reason).result.row.id =
          parent.row.id := by
      rw [eliminateAllFlagLeaves.eq_def]
    unfold ProjectionOriginalSupport
    rw [stepsEqual, idEqual, List.append_nil]
    exact ⟨supported, parentOrigin⟩
  | cons input rest ih =>
    let direction := reason prefixState bank ⟨0, by simp⟩
    have directedSupport := reasonSupported prefixState bank ⟨0, by simp⟩ supported bankSupported
    let kept := FoldProjection.afterTrace parent direction.state direction.steps direction.checked
    let left : AvailableSubclause direction.state
        (negate input :: (context ++ output :: rest.map negate)) := retarget kept (by
      intro literal member
      simp only [List.map_cons, List.mem_append, List.mem_cons] at member ⊢
      aesop)
    let joined := longMerge direction.state input
      (context ++ output :: rest.map negate) context left direction.result
    have joinedRun := longMerge_run direction.state input
      (context ++ output :: rest.map negate) context left direction.result
    let remaining : AvailableSubclause joined.state (context ++ output :: rest.map negate) :=
      retarget (longMerge_result direction.state input
        (context ++ output :: rest.map negate) context left direction.result) (by
      intro literal member
      simp only [List.mem_append] at member ⊢
      aesop)
    let directed := prefixState.extend direction.state direction.steps direction.checked
    have joinedTyped : runSteps directed.state joined.steps = some joined.state := joinedRun
    let current := directed.extend joined.state joined.steps joinedTyped
    let directedBank := bank.afterTrace direction.state direction.steps direction.checked
    let currentBank := directedBank.afterTrace joined.state joined.steps joinedTyped
    have keptOrigin := resultOrigin_append_right (formula parameters).clauses.size
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      prefixState.steps direction.steps parent.row.id parentOrigin
    have bound := Nat.le_trans (prefix_native_count_le rename prefixState)
      (runSteps_lastId_le direction.checked)
    have joinedSupport := longMerge_supported (formula parameters).clauses.size
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      directed.steps direction.state input (context ++ output :: rest.map negate) context
      left direction.result directedSupport.1 (allowed_native_count_le rename) bound
      keptOrigin directedSupport.2
    have currentBankSupported : AllClosedFlagsOriginalSupport rename current outputs currentBank := by
      intro later
      have one := resultOrigin_append_right (formula parameters).clauses.size
        (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
        prefixState.steps direction.steps (bank later).row.id (bankSupported later)
      exact resultOrigin_append_right (formula parameters).clauses.size
        (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
        directed.steps joined.steps (bank later).row.id one
    let tailReason : ∀ (now : SourcePrefix (parameters := parameters) rename)
      (nowBank : AllClosedFlags rename now outputs) (index : Fin rest.length),
      SubclauseProjection now.state (rest[index.val] :: context) budget :=
      fun now nowBank index => by
        simpa only [Fin.val_succ, List.getElem_cons_succ] using reason now nowBank index.succ
    have tailReasonSupported : ∀ now nowBank index,
        PrefixOriginalSupport rename now →
        AllClosedFlagsOriginalSupport rename now outputs nowBank →
        ProjectionOriginalSupport rename now (tailReason now nowBank index) := by
      intro now nowBank index nowSupported nowBankSupported
      simpa only [tailReason, Fin.val_succ, List.getElem_cons_succ] using
        reasonSupported now nowBank index.succ nowSupported nowBankSupported
    have tailSupport := ih (prefixState := current) (bank := currentBank)
      (parent := remaining) (reason := tailReason) joinedSupport.1
      currentBankSupported joinedSupport.2 tailReasonSupported
    let tail := eliminateAllFlagLeaves rename current outputs currentBank
      context output rest budget remaining tailReason
    have stepsEqual :
        (eliminateAllFlagLeaves rename prefixState outputs bank context output
          (input :: rest) budget parent reason).steps =
        direction.steps ++ (joined.steps ++ tail.steps) := by
      rw [eliminateAllFlagLeaves.eq_def]
      rfl
    have idEqual :
        (eliminateAllFlagLeaves rename prefixState outputs bank context output
          (input :: rest) budget parent reason).result.row.id = tail.result.row.id := by
      rw [eliminateAllFlagLeaves.eq_def]
      rfl
    unfold ProjectionOriginalSupport at tailSupport ⊢
    rw [stepsEqual, idEqual]
    simpa only [current, directed, SourcePrefix.extend, List.append_assoc, tail] using tailSupport

theorem targetEnableAt_supported (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (drive : parameters.drive = true) (supported : PrefixOriginalSupport rename prefixState) :
    ProjectionOriginalSupport rename prefixState (targetEnableAt rename prefixState drive) := by
  let channel := parameters.bridge.target
  let absent := mapLiteral rename
    ((Controller.NativeProof.SourceMismatchSeed.absentBefore (parameters := parameters) channel).lastID + 1, true)
  let term := mapLiteral rename
    ((Controller.NativeProof.SourceMismatchSeed.termBefore (parameters := parameters) channel).lastID + 1, true)
  let input := mapLiteral rename
    ((Controller.NativeProof.SourceMismatchSeed.termBefore (parameters := parameters) channel).slots
      (.primary (.enable channel)))
  let physical := Controller.NativeProof.SourceMismatchBranch.physicalUnitRow
    (parameters := parameters) rename ⟨0, by decide⟩
  let originalUnit : Rows.Available (initialState (relabel rename (formula parameters))) [negate absent] :=
    ⟨physical.id,
      (by simpa only [Controller.NativeProof.SourceMismatchSeed.targetUnit_at_occurrence rename drive]
        using physical.present), physical.bound⟩
  let unit := FoldProjection.afterTrace (ofRow originalUnit)
    prefixState.state prefixState.steps prefixState.checked
  let originalNot : AvailableSubclause (initialState (relabel rename (formula parameters))) [absent, term] := by
    have row := ofRow ((Controller.NativeProof.SourceMismatchSeed.absentRows rename channel).row
      ⟨0, by change 0 < 2; decide⟩)
    simpa only [Bounded.Producer.rows, Gate.clauses, List.getElem_cons_zero,
      Rows.mapClause, List.map_cons, List.map_nil,
      Controller.NativeProof.SourceMismatchSeed.absentBefore_term_handle,
      absent, term, mapLiteral] using row
  let notRow := FoldProjection.afterTrace originalNot prefixState.state prefixState.steps prefixState.checked
  let first := longMerge prefixState.state absent [] [term] unit notRow
  have firstRun := longMerge_run prefixState.state absent [] [term] unit notRow
  let firstResult := longMerge_result prefixState.state absent [] [term] unit notRow
  let originalAnd : AvailableSubclause (initialState (relabel rename (formula parameters))) [negate term, input] := by
    have row := ofRow ((Controller.NativeProof.SourceMismatchSeed.termRows rename channel).row
      ⟨0, by change 0 < 3; decide⟩)
    simpa [Bounded.Producer.rows, Gate.clauses, List.getElem_cons_zero,
      Rows.mapClause, List.map_cons, List.map_nil, mapLiteral, term, input,
      negate, Std.Sat.Literal.negate] using row
  let kept := FoldProjection.afterTrace originalAnd prefixState.state prefixState.steps prefixState.checked
  let andRow := FoldProjection.afterTrace kept first.state first.steps firstRun
  let second := longMerge first.state term [input] [] andRow firstResult
  have notId : originalNot.row.id =
      ((Controller.NativeProof.SourceMismatchSeed.absentRows rename channel).row
        ⟨0, by change 0 < 2; decide⟩).id := by
    dsimp only [originalNot]
    apply subclause_cast_id
    simp only [Bounded.Producer.rows, Gate.clauses, List.getElem_cons_zero,
      Rows.mapClause, List.map_cons, List.map_nil,
      Controller.NativeProof.SourceMismatchSeed.absentBefore_term_handle,
      absent, term, mapLiteral]
  have andId : originalAnd.row.id =
      ((Controller.NativeProof.SourceMismatchSeed.termRows rename channel).row
        ⟨0, by change 0 < 3; decide⟩).id := by
    dsimp only [originalAnd]
    refine (subclause_indices_mpr_id ?_ ?_ _ _).trans ?_
    · rfl
    · simp [Bounded.Producer.rows, Gate.clauses, List.getElem_cons_zero,
        Rows.mapClause, List.map_cons, List.map_nil, mapLiteral, term, input,
        negate, Std.Sat.Literal.negate]
    · apply subclause_indices_cast_id
      · rfl
      · simp [Bounded.Producer.rows, Gate.clauses, List.getElem_cons_zero,
        Rows.mapClause, List.map_cons, List.map_nil, mapLiteral, term, input,
        negate, Std.Sat.Literal.negate]
  have unitOrigin : Controller.NativeProof.SourceMismatchHandles.ResultOrigin
      (formula parameters).clauses.size
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      prefixState.steps unit.row.id :=
    Or.inl (Controller.NativeProof.SourceMismatchBranch.physicalUnit_allowed rename ⟨0, by decide⟩)
  have notOrigin : Controller.NativeProof.SourceMismatchHandles.ResultOrigin
      (formula parameters).clauses.size
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      prefixState.steps notRow.row.id := by
    change Controller.NativeProof.SourceMismatchHandles.ResultOrigin _ _ _ originalNot.row.id
    rw [notId]
    exact Or.inl (Controller.NativeProof.SourceMismatchSeed.absentRows_allowed rename channel
      ⟨0, by change 0 < 2; decide⟩)
  have firstSupport := longMerge_supported (formula parameters).clauses.size
    (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
    prefixState.steps prefixState.state absent [] [term] unit notRow supported
    (allowed_native_count_le rename) (prefix_native_count_le rename prefixState) unitOrigin notOrigin
  have andOrigin : Controller.NativeProof.SourceMismatchHandles.ResultOrigin
      (formula parameters).clauses.size
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      (prefixState.steps ++ first.steps) andRow.row.id := by
    change Controller.NativeProof.SourceMismatchHandles.ResultOrigin _ _ _ originalAnd.row.id
    rw [andId]
    exact Or.inl (Controller.NativeProof.SourceMismatchSeed.termRows_allowed rename channel
      ⟨0, by change 0 < 3; decide⟩)
  have firstBound := Nat.le_trans (prefix_native_count_le rename prefixState)
    (runSteps_lastId_le firstRun)
  have secondSupport := longMerge_supported (formula parameters).clauses.size
    (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
    (prefixState.steps ++ first.steps) first.state term [input] [] andRow firstResult
    firstSupport.1 (allowed_native_count_le rename) firstBound andOrigin firstSupport.2
  simpa only [ProjectionOriginalSupport, targetEnableAt, List.append_assoc, retarget,
    channel, absent, term, input, physical, originalUnit, unit, originalNot, notRow,
    first, firstRun, firstResult, originalAnd, kept, andRow, second] using secondSupport


theorem allFutureGuardAt_supported (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (later : Fin (laterBuses (parameters := parameters)).length)
    (channel : Fin parameters.channels) (outputs : Clause (Fin v))
    (bank : AllClosedFlags rename prefixState outputs)
    (supported : PrefixOriginalSupport rename prefixState)
    (bankSupported : AllClosedFlagsOriginalSupport rename prefixState outputs bank) :
    ProjectionOriginalSupport rename prefixState
      (allFutureGuardAt rename prefixState later channel outputs bank) := by
  let bus := (laterBuses (parameters := parameters))[later.val]
  let flag := laterFlagOutput rename .faulty later
  let guard := mapLiteral rename (guardHandle .faulty channel bus)
  let context := mixedContext (parameters := parameters) rename
  let first := guardOrFlagAt rename prefixState .faulty channel bus
  have firstSupported := guardOrFlagAt_supported rename prefixState .faulty channel bus supported
  have sameFlag : mapLiteral rename (flagInput .faulty bus) = flag := by
    rw [flagInput_busFlag]
    rfl
  let right : AvailableSubclause first.state [flag, guard] :=
    retarget first.result (by
      intro literal member
      rw [sameFlag] at member
      simp only [guard, List.mem_cons, List.not_mem_nil, or_false] at member ⊢
      exact member.elim Or.inr Or.inl)
  let kept := FoldProjection.afterTrace (bank later) first.state first.steps first.checked
  let left : AvailableSubclause first.state (negate flag :: (context ++ outputs)) :=
    retarget kept (by
      intro literal member
      simp only [context, flag, List.mem_append, List.mem_cons] at member ⊢
      aesop)
  have leftOrigin := resultOrigin_append_right (formula parameters).clauses.size
    (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
    prefixState.steps first.steps (bank later).row.id (bankSupported later)
  have rightOrigin := firstSupported.2
  have currentBound := Nat.le_trans (prefix_native_count_le rename prefixState)
    (runSteps_lastId_le first.checked)
  have joinedSupport := longMerge_supported (formula parameters).clauses.size
    (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
    (prefixState.steps ++ first.steps) first.state flag (context ++ outputs) [guard]
    left right firstSupported.1 (allowed_native_count_le rename) currentBound leftOrigin rightOrigin
  simpa only [ProjectionOriginalSupport, allFutureGuardAt, List.append_assoc, retarget,
    bus, flag, guard, context, first, kept, left, right] using joinedSupport

theorem finalGuardAt_supported (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (channel : Fin parameters.channels) (outputs : Clause (Fin v))
    (bank : AllClosedFlags rename prefixState outputs) (bus : Fin parameters.buses)
    (supported : PrefixOriginalSupport rename prefixState)
    (bankSupported : AllClosedFlagsOriginalSupport rename prefixState outputs bank) :
    ProjectionOriginalSupport rename prefixState
      (finalGuardAt rename prefixState channel outputs bank bus) := by
  unfold finalGuardAt
  split
  · have actual := guardOrFlagAt_supported rename prefixState .faulty channel parameters.firstBus supported
    simpa only [ProjectionOriginalSupport, retarget] using actual
  · rename_i nonzero
    dsimp only
    have actual := allFutureGuardAt_supported rename prefixState (laterPosition bus nonzero)
      channel outputs bank supported bankSupported
    exact projection_cast_supported rename prefixState
      (by rw [laterPosition_bus bus nonzero]) _ _ actual


theorem activationLeafReason_supported (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (drive : parameters.drive = true)
    (bank : AllClosedFlags rename prefixState (qualifierOutputs (parameters := parameters) rename))
    (index : Fin (1 + parameters.buses))
    (supported : PrefixOriginalSupport rename prefixState)
    (bankSupported : AllClosedFlagsOriginalSupport rename prefixState
      (qualifierOutputs (parameters := parameters) rename) bank) :
    ProjectionOriginalSupport rename prefixState
      (activationLeafReason rename prefixState drive bank index) := by
  unfold activationLeafReason
  split
  · have actual := targetEnableAt_supported rename prefixState drive supported
    simpa only [ProjectionOriginalSupport, retarget] using actual
  · rename_i nonzero
    dsimp only
    let bus : Fin parameters.buses := ⟨index.val - 1, by omega⟩
    have actual := finalGuardAt_supported rename prefixState parameters.bridge.target
      (qualifierOutputs (parameters := parameters) rename) bank bus supported bankSupported
    refine projection_cast_supported rename prefixState ?_ _ _ actual
    congr 1
    symm
    let inputs := (mapLiteral rename ((qualifierGuarded .faulty parameters.bridge.target).slots
      (.primary (.enable parameters.bridge.target)))) ::
      (List.finRange parameters.buses).map (fun query =>
        mapLiteral rename ((qualifierGuarded .faulty parameters.bridge.target).slots
          (.internal (.qualifierGuard .faulty query parameters.bridge.target))))
    have indexBound : index.val < inputs.length := by
      simp only [inputs, List.length_cons, List.length_map, List.length_finRange]
      omega
    have busBound : bus.val + 1 < inputs.length := by
      simp only [inputs, List.length_cons, List.length_map, List.length_finRange]
      omega
    change inputs[index.val]'indexBound =
      mapLiteral rename (guardHandle .faulty parameters.bridge.target bus)
    have successor : index.val = bus.val + 1 := by dsimp only [bus]; omega
    have lookup := congrArg (fun coordinate => inputs[coordinate]?) successor
    rw [List.getElem?_eq_getElem indexBound, List.getElem?_eq_getElem busBound] at lookup
    calc
      inputs[index.val]'indexBound = inputs[bus.val + 1]'busBound := Option.some.inj lookup
      _ = mapLiteral rename (guardHandle .faulty parameters.bridge.target bus) := by
        simp only [inputs, List.getElem_cons_succ, List.getElem_map,
          List.getElem_finRange, qualifierGuarded_guard_handle]
        congr 2


theorem qualifierActivationAt_supported (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (drive : parameters.drive = true)
    (bank : AllClosedFlags rename prefixState (qualifierOutputs (parameters := parameters) rename))
    (supported : PrefixOriginalSupport rename prefixState)
    (bankSupported : AllClosedFlagsOriginalSupport rename prefixState
      (qualifierOutputs (parameters := parameters) rename) bank) :
    ProjectionOriginalSupport rename prefixState
      (qualifierActivationAt rename prefixState drive bank) := by
  let channel := parameters.bridge.target
  let rawInputs := (qualifierGuarded .faulty channel).slots (.primary (.enable channel)) ::
    (List.finRange parameters.buses).map fun bus =>
      (qualifierGuarded .faulty channel).slots (.internal (.qualifierGuard .faulty bus channel))
  let inputs := rawInputs.map (mapLiteral rename)
  let output := mapLiteral rename (SourceSerialFold.allocate .conjunction
    (qualifierGuarded .faulty channel).lastID rawInputs).output
  let tree := (qualifierTree rename .faulty channel).afterTrace
    prefixState.state prefixState.steps prefixState.checked
  let projected := projectTreeLong tree
  have size : 2 ≤ inputs.length := by
    simp only [inputs, rawInputs, List.length_map, List.length_cons, List.length_finRange]
    have positive := parameters.positiveBuses
    omega
  let actual := nonunaryAggregateRow projected.result size
  let context := mixedContext (parameters := parameters) rename ++
    qualifierOutputs (parameters := parameters) rename
  let current := prefixState.extend projected.state projected.steps projected.checked
  let currentBank := bank.afterTrace projected.state projected.steps projected.checked
  let parent : AvailableSubclause current.state (context ++ output :: inputs.map negate) :=
    retarget actual (fun _ member => List.mem_append_right _ member)
  have aggregateSupported := qualifierAggregate_supported rename prefixState .faulty channel supported
  have parentOrigin := nonunaryAggregateRow_origin (formula parameters).clauses.size
    (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
    (prefixState.steps ++ projected.steps) projected.result size aggregateSupported.2
  have currentBankSupported : AllClosedFlagsOriginalSupport rename current
      (qualifierOutputs (parameters := parameters) rename) currentBank := by
    intro later
    exact resultOrigin_append_right (formula parameters).clauses.size
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      prefixState.steps projected.steps (bank later).row.id (bankSupported later)
  let reason : ∀ (now : SourcePrefix (parameters := parameters) rename)
    (nowBank : AllClosedFlags rename now (qualifierOutputs (parameters := parameters) rename))
    (index : Fin inputs.length), SubclauseProjection now.state
      (inputs[index.val] :: context) 2 :=
    fun now nowBank index => by
      let originalIndex : Fin (1 + parameters.buses) := ⟨index.val, by
        simpa only [inputs, rawInputs, List.length_map, List.length_cons,
          List.length_finRange, Nat.add_comm] using index.isLt⟩
      simpa only [inputs, rawInputs, context, List.map_cons, List.map_map,
        Function.comp_def, originalIndex] using
        activationLeafReason rename now drive nowBank originalIndex
  have reasonSupported : ∀ now nowBank index,
      PrefixOriginalSupport rename now →
      AllClosedFlagsOriginalSupport rename now
        (qualifierOutputs (parameters := parameters) rename) nowBank →
      ProjectionOriginalSupport rename now (reason now nowBank index) := by
    intro now nowBank index nowSupported nowBankSupported
    let originalIndex : Fin (1 + parameters.buses) := ⟨index.val, by
      simpa only [inputs, rawInputs, List.length_map, List.length_cons,
        List.length_finRange, Nat.add_comm] using index.isLt⟩
    have actualSupport := activationLeafReason_supported rename now drive nowBank originalIndex
      nowSupported nowBankSupported
    -- The actual callback's literal cast is transported without changing its trace or ID.
    dsimp only [reason]
    exact projection_cast_supported rename now
      (by simp only [inputs, rawInputs, context, channel, List.map_cons, List.map_map,
        Function.comp_def, originalIndex]) _ _ actualSupport
  have consumedSupport := eliminateAllFlagLeaves_supported rename current
    (qualifierOutputs (parameters := parameters) rename) currentBank context output inputs
    2 parent reason aggregateSupported.1 currentBankSupported
    parentOrigin reasonSupported
  simpa only [ProjectionOriginalSupport, qualifierActivationAt, SourcePrefix.extend,
    List.append_assoc, retarget, rawInputs, inputs, output, tree, projected,
    actual, channel, context, current, currentBank, parent, reason] using consumedSupport


theorem mixedActivation_supported (rename : Nat → Fin v) (drive : parameters.drive = true) :
    let initialPrefix := SourcePrefix.initial (parameters := parameters) rename
    ProjectionOriginalSupport rename initialPrefix (mixedActivation rename drive) := by
  let initialPrefix := SourcePrefix.initial (parameters := parameters) rename
  let emptyBank : ∀ later : Fin (laterBuses (parameters := parameters)).length,
      (laterBuses (parameters := parameters)).length ≤ later.val →
      AvailableSubclause initialPrefix.state
        (mixedContext (parameters := parameters) rename ++
          negate (laterFlagOutput rename .faulty later) ::
            qualifierOutputs (parameters := parameters) rename) :=
    fun later impossible => False.elim (Nat.not_le_of_gt later.isLt impossible)
  have emptySupport : PrefixOriginalSupport rename initialPrefix := by
    intro step impossible
    exact False.elim (List.not_mem_nil impossible)
  have emptyBankSupport : ∀ later order,
      Controller.NativeProof.SourceMismatchHandles.ResultOrigin
        (formula parameters).clauses.size
        (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
        initialPrefix.steps (emptyBank later order).row.id := by
    intro later impossible
    exact False.elim (Nat.not_le_of_gt later.isLt impossible)
  let flags := descendingFlags rename initialPrefix (laterBuses (parameters := parameters)).length
    (Nat.le_refl _) emptyBank
  have flagsSupport := descendingFlags_supported rename initialPrefix
    (laterBuses (parameters := parameters)).length (Nat.le_refl _) emptyBank
    emptySupport emptyBankSupport
  let current := initialPrefix.extend flags.state flags.steps flags.checked
  let allBank : AllClosedFlags rename current (qualifierOutputs (parameters := parameters) rename) := flags.bank
  have allBankSupport : AllClosedFlagsOriginalSupport rename current
      (qualifierOutputs (parameters := parameters) rename) allBank := flagsSupport.2
  have finalSupport := qualifierActivationAt_supported rename current drive allBank
    flagsSupport.1 allBankSupport
  simpa only [ProjectionOriginalSupport, mixedActivation, SourcePrefix.extend,
    List.append_assoc, initialPrefix, emptyBank, flags, current, allBank] using finalSupport

end Controller.NativeProof.SourceMixedSchedule
