module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.SourceMixedSelector
public import Controller.NativeProof.SourceFoldAggregateProvenance

@[expose] public section

/-! Source constructors for the descending mixed selector schedule. -/
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
theorem firstFlagInput_eq_sourceRoleMap (side : Side) :
    flagInput side parameters.firstBus =
      sourceRoleMap parameters (.internal (.flag side parameters.firstBus)) := by
  unfold flagInput
  rw [negateBefore_slots]
  change (tailStages side).slots (.internal (.flag side parameters.firstBus)) =
    (compile parameters).slots (.internal (.flag side parameters.firstBus))
  rw [compiled_first_flag]
  unfold tailStages
  rw [foldl_slot_mem _ (.internal (.flag side parameters.firstBus)) _ (by
    intro cursor bus member
    apply laterBus_first_flag
    have nonzero : bus.val ≠ 0 := by
      simpa [laterBuses] using (List.mem_filter.mp member).2
    intro equal
    apply nonzero
    rw [equal]
    rfl)]
  unfold initialMasks
  change ((List.finRange parameters.channels).foldl
    (Controller.NativeProof.SourceCongruence.initialMaskStep side) (tailStart side)).slots
      (.internal (.flag side parameters.firstBus)) = _
  rw [masks_first_flag]
  cases side with
  | healthy => rfl
  | faulty => exact tail_first_flag .healthy .faulty (interface parameters)

def firstTermGuardMixedAt (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (channel : Fin parameters.channels) :
    SubclauseProjection prefixState.state
      (Controller.NativeProof.SourceMismatchAdvance.mixedContext (parameters := parameters) rename ++
       [negate (laterTermOutput rename .faulty position channel),
        mapLiteral rename (guardHandle .faulty channel parameters.firstBus)]) 1 := by
  let first := guardOrFlagAt rename prefixState .faulty channel parameters.firstBus
  refine ⟨first.state, first.steps, first.checked, retarget first.result ?_, first.count⟩
  intro literal member
  rw [firstFlagInput_eq_sourceRoleMap] at member
  simp only [Controller.NativeProof.SourceMismatchAdvance.mixedContext,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member ⊢
  aesop

theorem eligibleGuardStep_other (side : Side) (channel : Fin parameters.channels)
    (query bus : Fin parameters.buses) (different : query ≠ bus) (cursor : Cursor parameters) :
    (eligibleGuardStep parameters side channel cursor bus).slots
      (.internal (.qualifierGuard side query channel)) =
      cursor.slots (.internal (.qualifierGuard side query channel)) := by
  apply emitNative_other
  simp [different]

theorem qualifierGuarded_guard_handle (side : Side) (channel : Fin parameters.channels)
    (bus : Fin parameters.buses) :
    (qualifierGuarded side channel).slots (.internal (.qualifierGuard side bus channel)) =
      guardHandle side channel bus := by
  have bound : bus.val < (List.finRange parameters.buses).length := by simpa using bus.isLt
  have decomposition : List.finRange parameters.buses =
      (List.finRange parameters.buses).take bus.val ++ bus ::
        (List.finRange parameters.buses).drop (bus.val + 1) := by
    simpa using positional_decomposition (List.finRange parameters.buses) ⟨bus.val, bound⟩
  have distinct : bus ∉ (List.finRange parameters.buses).drop (bus.val + 1) := by
    have nodup := List.nodup_finRange parameters.buses
    rw [decomposition] at nodup
    exact (List.nodup_cons.mp (List.nodup_append.mp nodup).2.1).1
  change ((List.finRange parameters.buses).foldl (eligibleGuardStep parameters side channel)
    (eligibleBefore side channel)).slots (.internal (.qualifierGuard side bus channel)) = _
  rw [decomposition, List.foldl_append]
  simp only [List.foldl_cons]
  rw [foldl_slot_mem _ (.internal (.qualifierGuard side bus channel)) _ (by
    intro cursor query member
    apply eligibleGuardStep_other
    intro equal
    exact distinct (equal.symm ▸ member))]
  simp only [eligibleGuardStep, Cursor.emitNative, Cursor.emit, Cursor.assign, Function.update_self]
  rfl

def qualifierTree (rename : Nat → Fin v) (side : Side) (channel : Fin parameters.channels) :=
  allocateForest (initialForest (state := initialState (relabel rename (formula parameters))) rename
    ((qualifierGuarded side channel).slots (.primary (.enable channel)) ::
      (List.finRange parameters.buses).map fun bus =>
        (qualifierGuarded side channel).slots (.internal (.qualifierGuard side bus channel))))
    (qualifierGuarded side channel).lastID (by simp)
    (foldRowsExact rename (qualifierGuarded side channel)
      (.internal (.qualifier side channel)) .conjunction
      ((qualifierGuarded side channel).slots (.primary (.enable channel)) ::
        (List.finRange parameters.buses).map fun bus =>
          (qualifierGuarded side channel).slots (.internal (.qualifierGuard side bus channel)))
      ((Controller.NativeProof.SourceQualifierOccurrences.eligible_occurrence_before_controller
        side channel).trans Controller.NativeProof.SourceFoldOwners.controller_before_compile))

/-- The qualifier aggregate is computed from the actual balanced allocator
rows, including the enable input and every stored guard occurrence. -/
def qualifierAggregate (rename : Nat → Fin v) (side : Side)
    (channel : Fin parameters.channels) :=
  projectTreeLong (qualifierTree rename side channel)

theorem qualifierAggregate_count (rename : Nat → Fin v) (side : Side)
    (channel : Fin parameters.channels) :
    (qualifierAggregate rename side channel).steps.length ≤
      2 * (qualifierTree rename side channel).nodes :=
  (qualifierAggregate rename side channel).count

theorem eligible_output_eq_allocator (side : Side) (channel : Fin parameters.channels) :
    (eligible parameters side channel (eligibleBefore side channel)).slots
      (.internal (.qualifier side channel)) =
    (SourceSerialFold.allocate .conjunction (qualifierGuarded side channel).lastID
      ((qualifierGuarded side channel).slots (.primary (.enable channel)) ::
        (List.finRange parameters.buses).map fun bus =>
          (qualifierGuarded side channel).slots (.internal (.qualifierGuard side bus channel)))).output := by
  simp only [eligible, qualifierGuarded, Cursor.foldNative, Cursor.assign, Function.update_self]

theorem qualifierGuarded_roots (side : Side) (channel : Fin parameters.channels) :
    (qualifierGuarded side channel).RootsExact := by
  unfold qualifierGuarded
  exact rootsExact_foldl _ _
    (fun cursor bus roots => cursor.rootsExact_emitNative_internal _ _ roots) _
    (eligibleBefore_roots side channel)

theorem qualifier_enable_eq_term (side : Side)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (channel : Fin parameters.channels) :
    (qualifierGuarded side channel).slots (.primary (.enable channel)) =
      (termBefore side position channel).slots (.primary (.enable channel)) :=
  ((qualifierGuarded_roots side channel).1 channel).trans
    ((termBefore_roots side position channel).1 channel).symm

/-- Original term-tree directions supply the enable leaf required by B. -/
def termEnableAt (rename : Nat → Fin v) (prefixState : SourcePrefix (parameters := parameters) rename)
    (side : Side) (position : Fin (laterBuses (parameters := parameters)).length)
    (channel : Fin parameters.channels) :
    SubclauseProjection prefixState.state
      [negate (laterTermOutput rename side position channel),
        mapLiteral rename ((qualifierGuarded side channel).slots (.primary (.enable channel)))]
      (2 * (laterTermTree rename side position channel).nodes) := by
  let tree := (laterTermTree rename side position channel).afterTrace
    prefixState.state prefixState.steps prefixState.checked
  have two : 2 ≤ ((laterTermInputs side position channel).map (mapLiteral rename)).length := by
    simp [laterTermInputs]
  let projected := nonunaryTreeInputs tree two
  have member : mapLiteral rename ((qualifierGuarded side channel).slots (.primary (.enable channel))) ∈
      (laterTermInputs side position channel).map (mapLiteral rename) := by
    rw [qualifier_enable_eq_term side position channel]
    apply List.mem_map.mpr
    exact ⟨_, by simp [laterTermInputs], rfl⟩
  refine ⟨projected.state, projected.steps, projected.checked, projected.results _ member, ?_⟩
  simpa only [tree, AndTree.afterTrace_nodes] using projected.count

/-- Assemble one checked leaf-elimination cell outside its recursive equations. -/
def eliminateLeavesStep (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (context : Clause (Fin v)) (output : Literal (Fin v))
    (input : Literal (Fin v)) (rest : List (Literal (Fin v))) (budget : Nat)
    (parent : AvailableSubclause prefixState.state
      (context ++ output :: (input :: rest).map negate))
    (reason : ∀ (current : SourcePrefix (parameters := parameters) rename)
      (index : Fin (input :: rest).length),
      SubclauseProjection current.state ((input :: rest)[index.val] :: context) budget)
    (recurse : ∀ (current : SourcePrefix (parameters := parameters) rename),
      AvailableSubclause current.state (context ++ output :: rest.map negate) →
      (∀ (now : SourcePrefix (parameters := parameters) rename) (index : Fin rest.length),
        SubclauseProjection now.state (rest[index.val] :: context) budget) →
      SubclauseProjection current.state (context ++ [output]) (rest.length * (budget + 1))) :
    SubclauseProjection prefixState.state (context ++ [output])
      ((input :: rest).length * (budget + 1)) := by
  let direction := reason prefixState ⟨0, by simp⟩
  let kept := FoldProjection.afterTrace parent direction.state direction.steps direction.checked
  let left : AvailableSubclause direction.state
      (negate input :: (context ++ output :: rest.map negate)) :=
    retarget kept (by
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
  let tail := recurse current remaining
    (fun now index => by
      simpa only [Fin.val_succ, List.getElem_cons_succ] using reason now index.succ)
  refine ⟨tail.state, direction.steps ++ (joined.steps ++ tail.steps), ?_, tail.result, ?_⟩
  · have tailRun : runSteps joined.state tail.steps = some tail.state := tail.checked
    rw [runSteps_append, direction.checked]
    simp only [Option.bind_some]
    rw [runSteps_append, joinedRun]
    simp only [Option.bind_some]
    exact tailRun
  · have one := direction.count
    have two := longMerge_count direction.state input
      (context ++ output :: rest.map negate) context left direction.result
    have three := tail.count
    change joined.steps.length ≤ 1 at two
    simp only [List.length_append, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- Sequential checked leaf elimination. The source consumer supplies a
constructor which recomputes each directional reason at the current prefix. -/
def eliminateLeaves (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (context : Clause (Fin v)) (output : Literal (Fin v))
    (inputs : List (Literal (Fin v))) (budget : Nat)
    (parent : AvailableSubclause prefixState.state
      (context ++ output :: inputs.map negate))
    (reason : ∀ (current : SourcePrefix (parameters := parameters) rename)
      (index : Fin inputs.length),
      SubclauseProjection current.state (inputs[index.val] :: context) budget) :
    SubclauseProjection prefixState.state (context ++ [output])
      (inputs.length * (budget + 1)) := by
  match inputs with
  | [] => exact ⟨prefixState.state, [], rfl, parent, by simp⟩
  | input :: rest =>
    exact eliminateLeavesStep rename prefixState context output input rest budget parent reason
      (fun current remaining tailReason =>
        eliminateLeaves rename current context output rest budget remaining tailReason)
termination_by inputs.length

def laterPosition (bus : Fin parameters.buses) (nonzero : bus.val ≠ 0) :
    Fin (laterBuses (parameters := parameters)).length :=
  ⟨(laterBuses (parameters := parameters)).idxOf bus,
    List.idxOf_lt_length_of_mem (by simp [laterBuses, nonzero])⟩

theorem laterPosition_bus (bus : Fin parameters.buses) (nonzero : bus.val ≠ 0) :
    (laterBuses (parameters := parameters))[(laterPosition bus nonzero).val] = bus :=
  List.getElem_idxOf (laterPosition bus nonzero).isLt

theorem laterTermTree_nodes_le (rename : Nat → Fin v) (side : Side)
    (position : Fin (laterBuses (parameters := parameters)).length) (channel : Fin parameters.channels) :
    (laterTermTree rename side position channel).nodes ≤ parameters.buses + 1 := by
  have size : (laterTermTree rename side position channel).nodes + 1 =
      ((laterTermInputs side position channel).map (mapLiteral rename)).length :=
    AndTree.nodes_leaves _
  have filtered := List.length_filter_le (fun earlier : Fin parameters.buses =>
    earlier < (laterBuses (parameters := parameters))[position.val]) (List.finRange parameters.buses)
  have inputLength : ((laterTermInputs side position channel).map (mapLiteral rename)).length =
      2 + ((List.finRange parameters.buses).filter
        (fun earlier => earlier < (laterBuses (parameters := parameters))[position.val])).length := by
    simp only [laterTermInputs, List.length_map, List.length_append, List.length_cons,
      List.length_nil]
  rw [inputLength] at size
  simp only [List.length_finRange] at filtered
  omega

def rebudget {state : State v} {target : Clause (Fin v)} {before after : Nat}
    (projection : SubclauseProjection state target before) (bound : before ≤ after) :
    SubclauseProjection state target after :=
  ⟨projection.state, projection.steps, projection.checked, projection.result, projection.count.trans bound⟩

def ClosedFlags (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (position : Fin (laterBuses (parameters := parameters)).length) (outputs : Clause (Fin v)) : Type :=
  ∀ later : Fin (laterBuses (parameters := parameters)).length, position.val < later.val →
    AvailableSubclause prefixState.state
      (mixedContext (parameters := parameters) rename ++
        negate (laterFlagOutput rename .faulty later) :: outputs)

def ClosedFlags.afterTrace (bank : ClosedFlags rename prefixState position outputs)
    (next : State v) (steps : List (Step v)) (checked : runSteps prefixState.state steps = some next) :
    ClosedFlags rename (prefixState.extend next steps checked) position outputs :=
  fun later order => FoldProjection.afterTrace (bank later order) next steps checked

def contextualize {state : State v} {target : Clause (Fin v)} {budget : Nat}
    (projection : SubclauseProjection state target budget) (context : Clause (Fin v)) :
    SubclauseProjection state (context ++ target) budget :=
  ⟨projection.state, projection.steps, projection.checked,
    retarget projection.result (fun _ member => List.mem_append_right _ member), projection.count⟩

def earlierGuardAt (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (channel : Fin parameters.channels) (bus : Fin parameters.buses)
    (before : bus ≤ (laterBuses (parameters := parameters))[position.val]) :
    SubclauseProjection prefixState.state
      (mixedContext (parameters := parameters) rename ++
        [negate (laterTermOutput rename .faulty position channel),
          mapLiteral rename (guardHandle .faulty channel bus)])
      (4 * parameters.buses + 10) := by
  have rootBound := laterTermTree_nodes_le rename .faulty position channel
  if zero : bus.val = 0 then
    have same : bus = parameters.firstBus := Fin.ext zero
    simpa only [same] using
      rebudget (firstTermGuardMixedAt rename prefixState position channel) (by omega)
  else
    let earlier := laterPosition bus zero
    have selected : (laterBuses (parameters := parameters))[earlier.val] = bus :=
      laterPosition_bus bus zero
    have bounded : earlier.val ≤ position.val := by
      by_contra reversed
      have sorted : (laterBuses (parameters := parameters)).Pairwise (· < ·) :=
        (List.pairwise_lt_finRange parameters.buses).filter _
      have strict := sorted.rel_get_of_lt (Nat.lt_of_not_ge reversed)
      simp only [List.get_eq_getElem] at strict
      rw [selected] at strict
      exact (not_lt_of_ge before) strict
    if same : earlier = position then
      have sameBus : bus = (laterBuses (parameters := parameters))[position.val] := by
        simpa only [same] using selected.symm
      let projected := contextualize
        (sameBusTermGuardAt rename prefixState .faulty position channel)
        (mixedContext (parameters := parameters) rename)
      simpa only [sameBus] using rebudget projected (by omega)
    else
      have order : earlier.val < position.val := by
        have different : earlier.val ≠ position.val := fun equal => same (Fin.ext equal)
        omega
      have earlierBound := laterTermTree_nodes_le rename .faulty earlier channel
      let projected := contextualize
        (earlierTermGuardAt rename prefixState .faulty earlier position order channel)
        (mixedContext (parameters := parameters) rename)
      simpa only [selected] using rebudget projected (by omega)

def futureGuardAt (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (position later : Fin (laterBuses (parameters := parameters)).length)
    (channel : Fin parameters.channels) (outputs : Clause (Fin v))
    (bank : ClosedFlags rename prefixState position outputs) (order : position.val < later.val) :
    SubclauseProjection prefixState.state
      (mapLiteral rename (guardHandle .faulty channel
        (laterBuses (parameters := parameters))[later.val]) ::
        (mixedContext (parameters := parameters) rename ++ outputs)) 2 := by
  let bus := (laterBuses (parameters := parameters))[later.val]
  let flag := laterFlagOutput rename .faulty later
  let guard := mapLiteral rename (guardHandle .faulty channel bus)
  let context := mixedContext (parameters := parameters) rename
  let first := guardOrFlagAt rename prefixState .faulty channel bus
  have sameFlag : mapLiteral rename (flagInput .faulty bus) = flag := by
    rw [flagInput_busFlag]
    rfl
  let right : AvailableSubclause first.state [flag, guard] :=
    retarget first.result (by
      intro literal member
      rw [sameFlag] at member
      simp only [guard, List.mem_cons, List.not_mem_nil, or_false] at member ⊢
      exact member.elim Or.inr Or.inl)
  let kept := FoldProjection.afterTrace (bank later order) first.state first.steps first.checked
  let left : AvailableSubclause first.state (negate flag :: (context ++ outputs)) :=
    retarget kept (by
      intro literal member
      simp only [context, flag, List.mem_append, List.mem_cons] at member ⊢
      aesop)
  let joined := longMerge first.state flag (context ++ outputs) [guard] left right
  have joinedRun := longMerge_run first.state flag (context ++ outputs) [guard] left right
  refine ⟨joined.state, first.steps ++ joined.steps, ?_, ?_, ?_⟩
  · rw [runSteps_append, first.checked]
    exact joinedRun
  · apply retarget (longMerge_result first.state flag (context ++ outputs) [guard] left right)
    intro literal member
    simp only [guard, context, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member ⊢
    aesop
  · have one := first.count
    have two := longMerge_count first.state flag (context ++ outputs) [guard] left right
    change joined.steps.length ≤ 1 at two
    simp only [List.length_append]
    omega

/-- Assemble one checked leaf-elimination cell outside its recursive equations. -/
def eliminateBankLeavesStep (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (outputs : Clause (Fin v))
    (bank : ClosedFlags rename prefixState position outputs)
    (context : Clause (Fin v)) (output : Literal (Fin v))
    (input : Literal (Fin v)) (rest : List (Literal (Fin v))) (budget : Nat)
    (parent : AvailableSubclause prefixState.state
      (context ++ output :: (input :: rest).map negate))
    (reason : ∀ (current : SourcePrefix (parameters := parameters) rename)
      (currentBank : ClosedFlags rename current position outputs)
      (index : Fin (input :: rest).length),
      SubclauseProjection current.state ((input :: rest)[index.val] :: context) budget)
    (recurse : ∀ (current : SourcePrefix (parameters := parameters) rename) (currentBank : ClosedFlags rename current position outputs),
      AvailableSubclause current.state (context ++ output :: rest.map negate) →
      (∀ (now : SourcePrefix (parameters := parameters) rename) (nowBank : ClosedFlags rename now position outputs) (index : Fin rest.length),
        SubclauseProjection now.state (rest[index.val] :: context) budget) →
      SubclauseProjection current.state (context ++ [output]) (rest.length * (budget + 1))) :
    SubclauseProjection prefixState.state (context ++ [output])
      ((input :: rest).length * (budget + 1)) := by
  let direction := reason prefixState bank ⟨0, by simp⟩
  let kept := FoldProjection.afterTrace parent direction.state direction.steps direction.checked
  let left : AvailableSubclause direction.state
      (negate input :: (context ++ output :: rest.map negate)) :=
    retarget kept (by
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
  let tail := recurse current currentBank remaining
    (fun now nowBank index => by
      simpa only [Fin.val_succ, List.getElem_cons_succ] using reason now nowBank index.succ)
  refine ⟨tail.state, direction.steps ++ (joined.steps ++ tail.steps), ?_, tail.result, ?_⟩
  · have tailRun : runSteps joined.state tail.steps = some tail.state := tail.checked
    rw [runSteps_append, direction.checked]
    simp only [Option.bind_some]
    rw [runSteps_append, joinedRun]
    simp only [Option.bind_some]
    exact tailRun
  · have one := direction.count
    have two := longMerge_count direction.state input
      (context ++ output :: rest.map negate) context left direction.result
    have three := tail.count
    change joined.steps.length ≤ 1 at two
    simp only [List.length_append, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- Leaf elimination carries the actual already-derived suffix bank through
each checked extension. A callback never receives a bank from an unrelated prefix. -/
def eliminateBankLeaves (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (outputs : Clause (Fin v))
    (bank : ClosedFlags rename prefixState position outputs)
    (context : Clause (Fin v)) (output : Literal (Fin v))
    (inputs : List (Literal (Fin v))) (budget : Nat)
    (parent : AvailableSubclause prefixState.state
      (context ++ output :: inputs.map negate))
    (reason : ∀ (current : SourcePrefix (parameters := parameters) rename)
      (currentBank : ClosedFlags rename current position outputs)
      (index : Fin inputs.length),
      SubclauseProjection current.state (inputs[index.val] :: context) budget) :
    SubclauseProjection prefixState.state (context ++ [output])
      (inputs.length * (budget + 1)) := by
  match inputs with
  | [] => exact ⟨prefixState.state, [], rfl, parent, by simp⟩
  | input :: rest =>
    exact eliminateBankLeavesStep rename prefixState position outputs bank
      context output input rest budget parent reason
      (fun current currentBank remaining tailReason =>
        eliminateBankLeaves rename current position outputs currentBank
          context output rest budget remaining tailReason)
termination_by inputs.length
/-- Actual qualifier leaf directions for B, including the original enable
leaf and the guard at every represented bus. -/
theorem guardReasonSubset (context : Clause (Fin v)) (term guard : Literal (Fin v))
    (outputs : Clause (Fin v)) :
    context ++ [term, guard] ⊆ guard :: (context ++ term :: outputs) := by
  intro literal member
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member ⊢
  aesop

theorem futureReasonSubset (context : Clause (Fin v)) (term guard : Literal (Fin v))
    (outputs : Clause (Fin v)) :
    guard :: (context ++ outputs) ⊆ guard :: (context ++ term :: outputs) := by
  intro literal member
  simp only [List.mem_append, List.mem_cons] at member ⊢
  aesop

def qualifierLeafReason (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (channel : Fin parameters.channels) (outputs : Clause (Fin v))
    (bank : ClosedFlags rename prefixState position outputs)
    (index : Fin (1 + parameters.buses)) :
    SubclauseProjection prefixState.state
      (((mapLiteral rename ((qualifierGuarded .faulty channel).slots (.primary (.enable channel)))) ::
        (List.finRange parameters.buses).map (fun bus =>
          mapLiteral rename ((qualifierGuarded .faulty channel).slots
            (.internal (.qualifierGuard .faulty bus channel)))))[index.val] ::
        (mixedContext (parameters := parameters) rename ++
          negate (laterTermOutput rename .faulty position channel) :: outputs))
      (4 * parameters.buses + 10) := by
  if zero : index.val = 0 then
    let one := termEnableAt rename prefixState .faulty position channel
    have bounded := laterTermTree_nodes_le rename .faulty position channel
    refine ⟨one.state, one.steps, one.checked, retarget one.result ?_,
      one.count.trans (by omega)⟩
    intro literal member
    simp only [zero, List.getElem_cons_zero]
    simp only [List.mem_cons, List.not_mem_nil, or_false, List.mem_append] at member ⊢
    aesop
  else
    let bus : Fin parameters.buses := ⟨index.val - 1, by omega⟩
    have succIndex : index.val = bus.val + 1 := by dsimp only [bus]; omega
    have leaf : ((mapLiteral rename ((qualifierGuarded .faulty channel).slots
        (.primary (.enable channel)))) ::
        (List.finRange parameters.buses).map (fun query =>
          mapLiteral rename ((qualifierGuarded .faulty channel).slots
            (.internal (.qualifierGuard .faulty query channel)))))[index.val] =
        mapLiteral rename (guardHandle .faulty channel bus) := by
      simp only [succIndex, List.getElem_cons_succ, List.getElem_map,
        List.getElem_finRange, qualifierGuarded_guard_handle]
      congr 2
    if before : bus ≤ (laterBuses (parameters := parameters))[position.val] then
      let one := earlierGuardAt rename prefixState position channel bus before
      refine ⟨one.state, one.steps, one.checked, retarget one.result ?_, one.count⟩
      rw [leaf]
      exact guardReasonSubset _ _ _ _
    else
      have nonzero : bus.val ≠ 0 := by
        have strict : (laterBuses (parameters := parameters))[position.val] < bus :=
          lt_of_not_ge before
        intro zero
        have impossible := strict
        change (laterBuses (parameters := parameters))[position.val].val < bus.val at impossible
        omega
      let later := laterPosition bus nonzero
      have selected := laterPosition_bus bus nonzero
      have order : position.val < later.val := by
        by_contra reversed
        have bounded : later.val ≤ position.val := Nat.le_of_not_gt reversed
        have sorted : (laterBuses (parameters := parameters)).Pairwise (· < ·) :=
          (List.pairwise_lt_finRange parameters.buses).filter _
        have boundBus : bus ≤ (laterBuses (parameters := parameters))[position.val] := by
          rcases Nat.lt_or_eq_of_le bounded with strict | equal
          · have ordered := sorted.rel_get_of_lt strict
            simp only [List.get_eq_getElem] at ordered
            rw [selected] at ordered
            exact le_of_lt ordered
          · have same : later = position := Fin.ext equal
            have chosen : (laterBuses (parameters := parameters))[later.val] = bus := selected
            simpa only [same] using chosen.symm.le
        exact before boundBus
      let one := futureGuardAt rename prefixState position later channel outputs bank order
      refine ⟨one.state, one.steps, one.checked, retarget one.result ?_,
        one.count.trans (by omega)⟩
      rw [leaf, selected]
      exact futureReasonSubset _ _ _ _

def nonunaryAggregateRow {state : State v} {output : Literal (Fin v)}
    {inputs : List (Literal (Fin v))}
    (certificate : AggregateCertificate state output inputs) (size : 2 ≤ inputs.length) :
    AvailableSubclause state (output :: inputs.map negate) := by
  cases certificate with
  | identity => simp at size
  | derived row => exact row

/-- Qualifiers are indexed by all represented channels, retaining shared handles. -/
def qualifierOutputs (rename : Nat → Fin v) : Clause (Fin v) :=
  (List.finRange parameters.channels).map fun channel =>
    mapLiteral rename (SourceSerialFold.allocate .conjunction
      (qualifierGuarded .faulty channel).lastID
      ((qualifierGuarded .faulty channel).slots (.primary (.enable channel)) ::
        (List.finRange parameters.buses).map fun bus =>
          (qualifierGuarded .faulty channel).slots (.internal (.qualifierGuard .faulty bus channel)))).output

def qualifierTermAt (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (channel : Fin parameters.channels)
    (bank : ClosedFlags rename prefixState position (qualifierOutputs (parameters := parameters) rename)) :
    SubclauseProjection prefixState.state
      (mixedContext (parameters := parameters) rename ++
        negate (laterTermOutput rename .faulty position channel) :: qualifierOutputs (parameters := parameters) rename)
      (2 * (qualifierTree rename .faulty channel).nodes +
        (1 + parameters.buses) * (4 * parameters.buses + 11)) := by
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
    negate (laterTermOutput rename .faulty position channel) :: qualifierOutputs (parameters := parameters) rename
  let current := prefixState.extend projected.state projected.steps projected.checked
  let currentBank := bank.afterTrace projected.state projected.steps projected.checked
  let parent : AvailableSubclause current.state (context ++ output :: inputs.map negate) :=
    retarget actual (fun _ member => List.mem_append_right _ member)
  let eliminated := eliminateBankLeaves rename current position (qualifierOutputs (parameters := parameters) rename)
    currentBank context output inputs (4 * parameters.buses + 10) parent
    (fun now nowBank index => by
      let originalIndex : Fin (1 + parameters.buses) :=
        ⟨index.val, by simpa only [tree, qualifierTree, 
          inputs, rawInputs, List.length_map, List.length_cons, List.length_finRange, Nat.add_comm] using index.isLt⟩
      simpa only [inputs, rawInputs, context, List.map_cons, List.map_map, Function.comp_def,
        originalIndex] using
        qualifierLeafReason rename now position channel (qualifierOutputs (parameters := parameters) rename)
          nowBank originalIndex)
  refine ⟨eliminated.state, projected.steps ++ eliminated.steps, ?_, ?_, ?_⟩
  · rw [runSteps_append, projected.checked]
    exact eliminated.checked
  · apply retarget eliminated.result
    intro literal member
    have outputMember : output ∈ qualifierOutputs (parameters := parameters) rename := by
      apply List.mem_map.mpr
      exact ⟨channel, List.mem_finRange _, rfl⟩
    change literal ∈ context
    have included : literal ∈ context ∨ literal = output := by
      simpa only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] using member
    rcases included with member | equal
    · exact member
    · subst literal
      exact List.mem_append_right _ (List.mem_cons_of_mem _ outputMember)
  · have one : projected.steps.length ≤ 2 * (qualifierTree rename .faulty channel).nodes := by
      simpa only [tree, AndTree.afterTrace_nodes] using projected.count
    have two : eliminated.steps.length ≤ inputs.length * (4 * parameters.buses + 10 + 1) :=
      eliminated.count
    have inputLength : inputs.length = 1 + parameters.buses := by
      simp only [inputs, rawInputs, List.length_map, List.length_cons, List.length_finRange]
      omega
    have budgetEqual : 4 * parameters.buses + 10 + 1 = 4 * parameters.buses + 11 := by omega
    simp only [List.length_append]
    calc
      projected.steps.length + eliminated.steps.length ≤
          2 * (qualifierTree rename .faulty channel).nodes +
            inputs.length * (4 * parameters.buses + 10 + 1) := Nat.add_le_add one two
      _ = _ := by rw [inputLength, budgetEqual]

/-- Consume an actual aggregate certificate using the current suffix bank.
The identity branch is the raw unary gate and adds no fabricated gate row. -/
def consumeAggregateBank (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (outputs context : Clause (Fin v))
    (bank : ClosedFlags rename prefixState position outputs)
    (output : Literal (Fin v)) (inputs : List (Literal (Fin v)))
    (aggregateBudget reasonBudget : Nat)
    (projection : AggregateProjection prefixState.state output inputs aggregateBudget)
    (reason : ∀ (current : SourcePrefix (parameters := parameters) rename)
      (currentBank : ClosedFlags rename current position outputs) (index : Fin inputs.length),
      SubclauseProjection current.state (inputs[index.val] :: context) reasonBudget) :
    SubclauseProjection prefixState.state (context ++ [output])
      (aggregateBudget + inputs.length * (reasonBudget + 1)) := by
  rcases projection with ⟨next, steps, checked, certificate, count⟩
  let current := prefixState.extend next steps checked
  let carried := bank.afterTrace next steps checked
  cases certificate with
  | identity =>
    let directed := reason current carried ⟨0, by simp⟩
    refine ⟨directed.state, steps ++ directed.steps, ?_, retarget directed.result ?_, ?_⟩
    · rw [runSteps_append, checked]
      exact directed.checked
    · intro literal member
      simp only [List.getElem_cons_zero, List.mem_cons] at member
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
      aesop
    · have bound := directed.count
      simp only [List.length_append, List.length_cons, List.length_nil, Nat.one_mul]
      omega
  | derived row =>
    let parent : AvailableSubclause current.state (context ++ output :: inputs.map negate) :=
      retarget row (fun _ member => List.mem_append_right _ member)
    let consumed := eliminateBankLeaves rename current position outputs carried
      context output inputs reasonBudget parent reason
    refine ⟨consumed.state, steps ++ consumed.steps, ?_, consumed.result, ?_⟩
    · rw [runSteps_append, checked]
      exact consumed.checked
    · exact (by
        simpa only [List.length_append] using Nat.add_le_add count consumed.count)

def qualifierBudget (parameters : Parameters) : Nat :=
  2 * parameters.buses + (1 + parameters.buses) * (4 * parameters.buses + 11)

theorem qualifierTree_nodes_le (rename : Nat → Fin v) (channel : Fin parameters.channels) :
    (qualifierTree rename .faulty channel).nodes ≤ parameters.buses := by
  have exactSize := AndTree.nodes_leaves (qualifierTree rename .faulty channel)
  have lengthInputs : (List.map (mapLiteral rename)
      ((qualifierGuarded .faulty channel).slots (.primary (.enable channel)) ::
        (List.finRange parameters.buses).map (fun bus =>
          (qualifierGuarded .faulty channel).slots (.internal (.qualifierGuard .faulty bus channel))))).length = 1 + parameters.buses := by
    simp only [List.length_map, List.length_cons, List.length_finRange]
    omega
  rw [lengthInputs] at exactSize
  omega

def closeFlagAt (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (bank : ClosedFlags rename prefixState position (qualifierOutputs (parameters := parameters) rename)) :
    SubclauseProjection prefixState.state
      (mixedContext (parameters := parameters) rename ++
        negate (laterFlagOutput rename .faulty position) :: qualifierOutputs (parameters := parameters) rename)
      (2 * (laterFlagTree rename .faulty position).nodes +
        parameters.channels * (qualifierBudget parameters + 1)) := by
  let inputs := (List.finRange parameters.channels).map
    (fun channel => negate (laterTermOutput rename .faulty position channel))
  let output := negate (laterFlagOutput rename .faulty position)
  let context := mixedContext (parameters := parameters) rename ++ qualifierOutputs (parameters := parameters) rename
  let tree : AndTree prefixState.state output inputs := by
    have actual := (laterFlagTree rename .faulty position).afterTrace
      prefixState.state prefixState.steps prefixState.checked
    have reflected := congrArg (List.map negate) (laterFlagInputs_eq_terms rename .faulty position)
    simp only [List.map_map, Function.comp_def] at reflected
    change AndTree prefixState.state (negate (laterFlagOutput rename .faulty position))
      ((List.finRange parameters.channels).map
        (fun channel => negate (laterTermOutput rename .faulty position channel)))
    rw [← reflected]
    exact actual
  let aggregate := projectTreeLong tree
  let consumed := consumeAggregateBank rename prefixState position (qualifierOutputs (parameters := parameters) rename)
    context bank output inputs (2 * tree.nodes) (qualifierBudget parameters) aggregate
    (fun current currentBank index => by
      let channel : Fin parameters.channels := ⟨index.val, by
        simpa only [inputs, List.length_map, List.length_finRange] using index.isLt⟩
      let one := qualifierTermAt rename current position channel currentBank
      have bound := qualifierTree_nodes_le rename channel
      refine ⟨one.state, one.steps, one.checked, retarget one.result ?_,
        one.count.trans (by dsimp only [qualifierBudget]; omega)⟩
      intro literal member
      simp only [inputs, List.getElem_map, List.getElem_finRange, channel]
      simp only [context, List.mem_append, List.mem_cons] at member ⊢
      aesop)
  refine ⟨consumed.state, consumed.steps, consumed.checked, retarget consumed.result ?_, ?_⟩
  · intro literal member
    simp only [context, output, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at member ⊢
    aesop
  · have oldSize : (laterFlagTree rename .faulty position).nodes + 1 = parameters.channels := by
      calc
        (laterFlagTree rename .faulty position).nodes + 1 =
            ((laterFlagInputs .faulty position).map (dualLiteral rename)).length :=
          AndTree.nodes_leaves _
        _ = parameters.channels := by
          simp only [List.length_map, laterFlagInputs, List.length_finRange]
    have newSize : tree.nodes + 1 = parameters.channels := by
      calc
        tree.nodes + 1 = inputs.length := AndTree.nodes_leaves _
        _ = parameters.channels := by
          simp only [inputs, List.length_map, List.length_finRange]
    have sameNodes : tree.nodes = (laterFlagTree rename .faulty position).nodes := by omega
    have count := consumed.count
    simpa only [sameNodes, inputs, List.length_map, List.length_finRange] using count

structure FlagClosure (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename) (remaining : Nat) where
  state : State v
  steps : List (Step v)
  checked : runSteps prefixState.state steps = some state
  bank : ∀ later : Fin (laterBuses (parameters := parameters)).length,
    AvailableSubclause state (mixedContext (parameters := parameters) rename ++
      negate (laterFlagOutput rename .faulty later) ::
        qualifierOutputs (parameters := parameters) rename)
  count : steps.length ≤ remaining *
    (2 * parameters.channels + parameters.channels * (qualifierBudget parameters + 1))

/-- The remaining counter is the length of the unclosed source prefix.
Every recursive step closes its greatest represented bus and lifts the
existing suffix rows through the actual checked extension. -/
def descendingFlags (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (remaining : Nat) (bounded : remaining ≤ (laterBuses (parameters := parameters)).length)
    (bank : ∀ later : Fin (laterBuses (parameters := parameters)).length,
      remaining ≤ later.val →
      AvailableSubclause prefixState.state
        (mixedContext (parameters := parameters) rename ++
          negate (laterFlagOutput rename .faulty later) ::
            qualifierOutputs (parameters := parameters) rename)) :
    FlagClosure rename prefixState remaining := by
  if zero : remaining = 0 then
    exact ⟨prefixState.state, [], rfl, fun later => bank later (by omega), by simp⟩
  else
    let position : Fin (laterBuses (parameters := parameters)).length :=
      ⟨remaining - 1, by omega⟩
    let localBank : ClosedFlags rename prefixState position
        (qualifierOutputs (parameters := parameters) rename) :=
      fun later order => bank later (by dsimp only [position] at order; omega)
    let closed := closeFlagAt rename prefixState position localBank
    let current := prefixState.extend closed.state closed.steps closed.checked
    let nextBank : ∀ later : Fin (laterBuses (parameters := parameters)).length,
        remaining - 1 ≤ later.val →
        AvailableSubclause current.state
          (mixedContext (parameters := parameters) rename ++
            negate (laterFlagOutput rename .faulty later) ::
              qualifierOutputs (parameters := parameters) rename) := by
      intro later order
      if same : later.val = position.val then
        have equal : later = position := Fin.ext same
        exact equal.symm ▸ closed.result
      else
        have previous : remaining ≤ later.val := by
          dsimp only [position] at same
          omega
        exact FoldProjection.afterTrace (bank later previous)
          closed.state closed.steps closed.checked
    let tail := descendingFlags rename current (remaining - 1) (by omega) nextBank
    refine ⟨tail.state, closed.steps ++ tail.steps, ?_, tail.bank, ?_⟩
    · rw [runSteps_append, closed.checked]
      exact tail.checked
    · have first := closed.count
      have second := tail.count
      have flagNodes : (laterFlagTree rename .faulty position).nodes ≤ parameters.channels := by
        have nodes : (laterFlagTree rename .faulty position).nodes + 1 = parameters.channels := by
          calc
            (laterFlagTree rename .faulty position).nodes + 1 =
                ((laterFlagInputs .faulty position).map (dualLiteral rename)).length :=
              AndTree.nodes_leaves _
            _ = parameters.channels := by
              simp only [List.length_map, laterFlagInputs, List.length_finRange]
        omega
      have localCount : closed.steps.length ≤
          2 * parameters.channels + parameters.channels * (qualifierBudget parameters + 1) :=
        first.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 2 flagNodes) _)
      simp only [List.length_append]
      have sumBound := Nat.add_le_add localCount second
      have successor : remaining = (remaining - 1) + 1 := by omega
      calc
        closed.steps.length + tail.steps.length ≤
            (2 * parameters.channels + parameters.channels * (qualifierBudget parameters + 1)) +
              (remaining - 1) * (2 * parameters.channels + parameters.channels * (qualifierBudget parameters + 1)) :=
          sumBound
        _ = ((remaining - 1) + 1) * (2 * parameters.channels + parameters.channels * (qualifierBudget parameters + 1)) := by
          rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
        _ = remaining * (2 * parameters.channels + parameters.channels * (qualifierBudget parameters + 1)) :=
          congrArg (fun count => count * (2 * parameters.channels + parameters.channels * (qualifierBudget parameters + 1))) successor.symm
termination_by remaining

def PrefixOriginalSupport (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename) : Prop :=
  Controller.NativeProof.SourceBusSchedule.TraceOriginalSupport
    (formula parameters).clauses.size
    (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename) prefixState.steps

def ClosedFlagsOriginalSupport (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (outputs : Clause (Fin v)) (bank : ClosedFlags rename prefixState position outputs) : Prop :=
  ∀ later order,
    Controller.NativeProof.SourceMismatchHandles.ResultOrigin
      (formula parameters).clauses.size
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      prefixState.steps (bank later order).row.id

theorem qualifierTree_originals (rename : Nat → Fin v) (side : Side)
    (channel : Fin parameters.channels) :
    TreeOriginals (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      (qualifierTree rename side channel) := by
  unfold qualifierTree
  apply allocateForest_originals
  · exact initialForest_originals _ _ _
  · exact foldRowsExact_allowed rename (qualifierGuarded side channel)
      (.internal (.qualifier side channel)) .conjunction _
      (Controller.NativeProof.SourceQualifierOccurrences.eligible_occurrence_before_controller side channel)

theorem qualifierAggregate_supported (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (side : Side) (channel : Fin parameters.channels)
    (supported : PrefixOriginalSupport rename prefixState) :
    let tree := (qualifierTree rename side channel).afterTrace
      prefixState.state prefixState.steps prefixState.checked
    let actual := projectTreeLong tree
    Controller.NativeProof.SourceBusSchedule.TraceOriginalSupport
      (formula parameters).clauses.size
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      (prefixState.steps ++ actual.steps) ∧
    Controller.NativeProof.SourceFoldAggregateProvenance.AggregateOrigin
      (formula parameters).clauses.size
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      (prefixState.steps ++ actual.steps) actual.result := by
  apply Controller.NativeProof.SourceFoldAggregateProvenance.projectTreeLong_supported
  · exact treeOriginals_afterTrace _
      (qualifierTree rename side channel) (qualifierTree_originals rename side channel)
      prefixState.state prefixState.steps prefixState.checked
  · exact supported
  · intro id allowed
    have bound := Controller.NativeProof.SourceMismatchBranch.allowedOriginal_bound rename id allowed
    have inputSize : (formula parameters).clauses.size =
        (Controller.NativeProof.SourceMismatchBranch.equationRows (parameters := parameters)).length + 4 := by
      rw [Controller.NativeProof.SourceRows.formula_as_rows]
      simp only [ofClauses, List.size_toArray, List.length_append, List.length_map,
        assertions, List.length_cons, List.length_nil]
      rfl
    rw [inputSize]
    omega
  · have monotone := runSteps_lastId_le prefixState.checked
    simpa only [initialState, relabel, Controller.CNF.OrderedFormula.relabel, Array.size_map] using monotone

/-- The physical drive unit is reread at the current prefix. Fresh resolution
IDs are allocated from that prefix, so replay never appends an initial-state trace. -/
def targetEnableAt (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (drive : parameters.drive = true) :
    SubclauseProjection prefixState.state
      [mapLiteral rename (sourceRoleMap parameters
        (.primary (.enable parameters.bridge.target)))] 2 := by
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
  have originalNot : AvailableSubclause (initialState (relabel rename (formula parameters))) [absent, term] := by
    have row := ofRow ((Controller.NativeProof.SourceMismatchSeed.absentRows rename channel).row
      ⟨0, by change 0 < 2; decide⟩)
    simpa only [Bounded.Producer.rows, Gate.clauses, List.getElem_cons_zero,
      Rows.mapClause, List.map_cons, List.map_nil,
      Controller.NativeProof.SourceMismatchSeed.absentBefore_term_handle,
      absent, term, mapLiteral] using row
  let notRow := FoldProjection.afterTrace originalNot prefixState.state prefixState.steps prefixState.checked
  let first := longMerge prefixState.state absent [] [term] unit notRow
  have firstRun := longMerge_run prefixState.state absent [] [term] unit notRow
  have firstResult := longMerge_result prefixState.state absent [] [term] unit notRow
  have originalAnd : AvailableSubclause (initialState (relabel rename (formula parameters))) [negate term, input] := by
    have row := ofRow ((Controller.NativeProof.SourceMismatchSeed.termRows rename channel).row
      ⟨0, by change 0 < 3; decide⟩)
    simpa [Bounded.Producer.rows, Gate.clauses, List.getElem_cons_zero,
      Rows.mapClause, List.map_cons, List.map_nil, mapLiteral, term, input,
      negate, Std.Sat.Literal.negate] using row
  let kept := FoldProjection.afterTrace originalAnd prefixState.state prefixState.steps prefixState.checked
  let andRow := FoldProjection.afterTrace kept first.state first.steps firstRun
  let second := longMerge first.state term [input] [] andRow firstResult
  refine ⟨second.state, first.steps ++ second.steps, ?_, ?_, ?_⟩
  · rw [runSteps_append, firstRun]
    exact longMerge_run _ _ _ _ _ _
  · apply retarget (longMerge_result first.state term [input] [] andRow firstResult)
    intro literal member
    simpa only [input, channel, Controller.NativeProof.SourceMismatchSeed.termBefore_enable,
      List.append_nil] using member
  · have one : first.steps.length ≤ 1 :=
      longMerge_count prefixState.state absent [] [term] unit notRow
    have two : second.steps.length ≤ 1 :=
      longMerge_count first.state term [input] [] andRow firstResult
    simp only [List.length_append]
    omega

def AllClosedFlags (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename) (outputs : Clause (Fin v)) : Type :=
  ∀ later : Fin (laterBuses (parameters := parameters)).length,
    AvailableSubclause prefixState.state
      (mixedContext (parameters := parameters) rename ++
        negate (laterFlagOutput rename .faulty later) :: outputs)

def AllClosedFlags.afterTrace (bank : AllClosedFlags rename prefixState outputs)
    (next : State v) (steps : List (Step v)) (checked : runSteps prefixState.state steps = some next) :
    AllClosedFlags rename (prefixState.extend next steps checked) outputs :=
  fun later => FoldProjection.afterTrace (bank later) next steps checked

/-- Assemble one checked leaf-elimination cell outside its recursive equations. -/
def eliminateAllFlagLeavesStep (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (outputs : Clause (Fin v))
    (bank : AllClosedFlags rename prefixState outputs)
    (context : Clause (Fin v)) (output : Literal (Fin v))
    (input : Literal (Fin v)) (rest : List (Literal (Fin v))) (budget : Nat)
    (parent : AvailableSubclause prefixState.state
      (context ++ output :: (input :: rest).map negate))
    (reason : ∀ (current : SourcePrefix (parameters := parameters) rename)
      (currentBank : AllClosedFlags rename current outputs)
      (index : Fin (input :: rest).length),
      SubclauseProjection current.state ((input :: rest)[index.val] :: context) budget)
    (recurse : ∀ (current : SourcePrefix (parameters := parameters) rename) (currentBank : AllClosedFlags rename current outputs),
      AvailableSubclause current.state (context ++ output :: rest.map negate) →
      (∀ (now : SourcePrefix (parameters := parameters) rename) (nowBank : AllClosedFlags rename now outputs) (index : Fin rest.length),
        SubclauseProjection now.state (rest[index.val] :: context) budget) →
      SubclauseProjection current.state (context ++ [output]) (rest.length * (budget + 1))) :
    SubclauseProjection prefixState.state (context ++ [output])
      ((input :: rest).length * (budget + 1)) := by
  let direction := reason prefixState bank ⟨0, by simp⟩
  let kept := FoldProjection.afterTrace parent direction.state direction.steps direction.checked
  let left : AvailableSubclause direction.state
      (negate input :: (context ++ output :: rest.map negate)) :=
    retarget kept (by
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
  let tail := recurse current currentBank remaining
    (fun now nowBank index => by
      simpa only [Fin.val_succ, List.getElem_cons_succ] using reason now nowBank index.succ)
  refine ⟨tail.state, direction.steps ++ (joined.steps ++ tail.steps), ?_, tail.result, ?_⟩
  · have tailRun : runSteps joined.state tail.steps = some tail.state := tail.checked
    rw [runSteps_append, direction.checked]
    simp only [Option.bind_some]
    rw [runSteps_append, joinedRun]
    simp only [Option.bind_some]
    exact tailRun
  · have one := direction.count
    have two := longMerge_count direction.state input
      (context ++ output :: rest.map negate) context left direction.result
    have three := tail.count
    change joined.steps.length ≤ 1 at two
    simp only [List.length_append, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

def eliminateAllFlagLeaves (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (outputs : Clause (Fin v))
    (bank : AllClosedFlags rename prefixState outputs)
    (context : Clause (Fin v)) (output : Literal (Fin v))
    (inputs : List (Literal (Fin v))) (budget : Nat)
    (parent : AvailableSubclause prefixState.state
      (context ++ output :: inputs.map negate))
    (reason : ∀ (current : SourcePrefix (parameters := parameters) rename)
      (currentBank : AllClosedFlags rename current outputs)
      (index : Fin inputs.length),
      SubclauseProjection current.state (inputs[index.val] :: context) budget) :
    SubclauseProjection prefixState.state (context ++ [output])
      (inputs.length * (budget + 1)) := by
  match inputs with
  | [] => exact ⟨prefixState.state, [], rfl, parent, by simp⟩
  | input :: rest =>
    exact eliminateAllFlagLeavesStep rename prefixState outputs bank
      context output input rest budget parent reason
      (fun current currentBank remaining tailReason =>
        eliminateAllFlagLeaves rename current outputs currentBank
          context output rest budget remaining tailReason)
termination_by inputs.length
def allFutureGuardAt (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (later : Fin (laterBuses (parameters := parameters)).length)
    (channel : Fin parameters.channels) (outputs : Clause (Fin v))
    (bank : AllClosedFlags rename prefixState outputs) :
    SubclauseProjection prefixState.state
      (mapLiteral rename (guardHandle .faulty channel
        (laterBuses (parameters := parameters))[later.val]) ::
        (mixedContext (parameters := parameters) rename ++ outputs)) 2 := by
  let bus := (laterBuses (parameters := parameters))[later.val]
  let flag := laterFlagOutput rename .faulty later
  let guard := mapLiteral rename (guardHandle .faulty channel bus)
  let context := mixedContext (parameters := parameters) rename
  let first := guardOrFlagAt rename prefixState .faulty channel bus
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
  let joined := longMerge first.state flag (context ++ outputs) [guard] left right
  have joinedRun := longMerge_run first.state flag (context ++ outputs) [guard] left right
  refine ⟨joined.state, first.steps ++ joined.steps, ?_, ?_, ?_⟩
  · rw [runSteps_append, first.checked]
    exact joinedRun
  · apply retarget (longMerge_result first.state flag (context ++ outputs) [guard] left right)
    intro literal member
    simp only [guard, context, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member ⊢
    aesop
  · have one := first.count
    have two := longMerge_count first.state flag (context ++ outputs) [guard] left right
    change joined.steps.length ≤ 1 at two
    simp only [List.length_append]
    omega

def finalGuardAt (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (channel : Fin parameters.channels) (outputs : Clause (Fin v))
    (bank : AllClosedFlags rename prefixState outputs) (bus : Fin parameters.buses) :
    SubclauseProjection prefixState.state
      (mapLiteral rename (guardHandle .faulty channel bus) ::
        (mixedContext (parameters := parameters) rename ++ outputs)) 2 := by
  if zero : bus.val = 0 then
    have same : bus = parameters.firstBus := Fin.ext zero
    let original := guardOrFlagAt rename prefixState .faulty channel parameters.firstBus
    refine ⟨original.state, original.steps, original.checked, retarget original.result ?_,
      original.count.trans (by omega)⟩
    intro literal member
    rw [firstFlagInput_eq_sourceRoleMap] at member
    rw [same]
    simp only [mixedContext, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at member ⊢
    aesop
  else
    let later := laterPosition bus zero
    have selected : (laterBuses (parameters := parameters))[later.val] = bus :=
      laterPosition_bus bus zero
    simpa only [selected] using allFutureGuardAt rename prefixState later channel outputs bank

def activationLeafReason (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (drive : parameters.drive = true)
    (bank : AllClosedFlags rename prefixState (qualifierOutputs (parameters := parameters) rename))
    (index : Fin (1 + parameters.buses)) :
    SubclauseProjection prefixState.state
      (((mapLiteral rename ((qualifierGuarded .faulty parameters.bridge.target).slots
        (.primary (.enable parameters.bridge.target)))) ::
        (List.finRange parameters.buses).map (fun bus =>
          mapLiteral rename ((qualifierGuarded .faulty parameters.bridge.target).slots
            (.internal (.qualifierGuard .faulty bus parameters.bridge.target)))))[index.val] ::
        (mixedContext (parameters := parameters) rename ++
          qualifierOutputs (parameters := parameters) rename)) 2 := by
  if zero : index.val = 0 then
    let one := targetEnableAt rename prefixState drive
    have sourceEnable : (qualifierGuarded .faulty parameters.bridge.target).slots
        (.primary (.enable parameters.bridge.target)) =
        sourceRoleMap parameters (.primary (.enable parameters.bridge.target)) :=
      ((qualifierGuarded_roots .faulty parameters.bridge.target).1 parameters.bridge.target).trans
        ((compile_rootsExact parameters).1 parameters.bridge.target).symm
    refine ⟨one.state, one.steps, one.checked, retarget one.result ?_, one.count⟩
    intro literal member
    simp only [zero, List.getElem_cons_zero, sourceEnable]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    exact List.mem_cons.mpr (Or.inl member)
  else
    let bus : Fin parameters.buses := ⟨index.val - 1, by omega⟩
    have succIndex : index.val = bus.val + 1 := by dsimp only [bus]; omega
    have leaf : ((mapLiteral rename ((qualifierGuarded .faulty parameters.bridge.target).slots
        (.primary (.enable parameters.bridge.target)))) ::
        (List.finRange parameters.buses).map (fun query =>
          mapLiteral rename ((qualifierGuarded .faulty parameters.bridge.target).slots
            (.internal (.qualifierGuard .faulty query parameters.bridge.target)))))[index.val] =
        mapLiteral rename (guardHandle .faulty parameters.bridge.target bus) := by
      simp only [succIndex, List.getElem_cons_succ, List.getElem_map,
        List.getElem_finRange, qualifierGuarded_guard_handle]
      congr 2
    rw [leaf]
    exact finalGuardAt rename prefixState parameters.bridge.target
      (qualifierOutputs (parameters := parameters) rename) bank bus

def qualifierActivationAt (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (drive : parameters.drive = true)
    (bank : AllClosedFlags rename prefixState (qualifierOutputs (parameters := parameters) rename)) :
    SubclauseProjection prefixState.state
      (mixedContext (parameters := parameters) rename ++ qualifierOutputs (parameters := parameters) rename)
      (2 * (qualifierTree rename .faulty parameters.bridge.target).nodes +
        (1 + parameters.buses) * 3) := by
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
  have inputLength : inputs.length = 1 + parameters.buses := by
    simp only [inputs, rawInputs, List.length_map, List.length_cons, List.length_finRange]
    omega
  have size : 2 ≤ inputs.length := by
    rw [inputLength]
    have positive := parameters.positiveBuses
    omega
  let actual := nonunaryAggregateRow projected.result size
  let context := mixedContext (parameters := parameters) rename ++ qualifierOutputs (parameters := parameters) rename
  let current := prefixState.extend projected.state projected.steps projected.checked
  let currentBank := bank.afterTrace projected.state projected.steps projected.checked
  let parent : AvailableSubclause current.state (context ++ output :: inputs.map negate) :=
    retarget actual (fun _ member => List.mem_append_right _ member)
  let eliminated := eliminateAllFlagLeaves rename current (qualifierOutputs (parameters := parameters) rename)
    currentBank context output inputs 2 parent
    (fun now nowBank index => by
      let originalIndex : Fin (1 + parameters.buses) := ⟨index.val, by
        simpa only [inputLength] using index.isLt⟩
      simpa only [inputs, rawInputs, context, channel, List.map_cons, List.map_map,
        Function.comp_def, originalIndex] using activationLeafReason rename now drive nowBank originalIndex)
  refine ⟨eliminated.state, projected.steps ++ eliminated.steps, ?_, ?_, ?_⟩
  · rw [runSteps_append, projected.checked]
    exact eliminated.checked
  · apply retarget eliminated.result
    intro literal member
    have outputMember : output ∈ qualifierOutputs (parameters := parameters) rename := by
      apply List.mem_map.mpr
      exact ⟨channel, List.mem_finRange _, rfl⟩
    change literal ∈ context
    have included : literal ∈ context ∨ literal = output := by
      simpa only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] using member
    exact included.elim id (fun equal => equal.symm ▸ List.mem_append_right _ outputMember)
  · have one : projected.steps.length ≤ 2 * (qualifierTree rename .faulty channel).nodes := by
      simpa only [tree, AndTree.afterTrace_nodes] using projected.count
    have two : eliminated.steps.length ≤ inputs.length * 3 := eliminated.count
    simp only [List.length_append]
    calc
      projected.steps.length + eliminated.steps.length ≤
          2 * (qualifierTree rename .faulty channel).nodes + inputs.length * 3 :=
        Nat.add_le_add one two
      _ = _ := by rw [inputLength]

/-- The mixed first-flag activation is constructed from the empty native
prefix, every represented later bus, and the actual physical target unit. -/
def mixedActivation (rename : Nat → Fin v) (drive : parameters.drive = true) :
    SubclauseProjection (initialState (relabel rename (formula parameters)))
      (mixedContext (parameters := parameters) rename ++ qualifierOutputs (parameters := parameters) rename)
      (parameters.buses *
        (2 * parameters.channels + parameters.channels * (qualifierBudget parameters + 1)) +
          5 * parameters.buses + 3) := by
  let initialPrefix := SourcePrefix.initial (parameters := parameters) rename
  let emptyBank : ∀ later : Fin (laterBuses (parameters := parameters)).length,
      (laterBuses (parameters := parameters)).length ≤ later.val →
      AvailableSubclause initialPrefix.state
        (mixedContext (parameters := parameters) rename ++
          negate (laterFlagOutput rename .faulty later) ::
            qualifierOutputs (parameters := parameters) rename) :=
    fun later impossible => False.elim (Nat.not_le_of_gt later.isLt impossible)
  let flags := descendingFlags rename initialPrefix (laterBuses (parameters := parameters)).length
    (Nat.le_refl _) emptyBank
  let current := initialPrefix.extend flags.state flags.steps flags.checked
  let allBank : AllClosedFlags rename current (qualifierOutputs (parameters := parameters) rename) := flags.bank
  let activated := qualifierActivationAt rename current drive allBank
  refine ⟨activated.state, flags.steps ++ activated.steps, ?_, activated.result, ?_⟩
  · have flagRun : runSteps (initialState (relabel rename (formula parameters)))
        flags.steps = some flags.state := flags.checked
    rw [runSteps_append, flagRun]
    exact activated.checked
  · have flagCount := flags.count
    have treeBound := qualifierTree_nodes_le rename parameters.bridge.target
    have lengthBound : (laterBuses (parameters := parameters)).length ≤ parameters.buses := by
      have bound := List.length_filter_le (fun bus : Fin parameters.buses => bus.val != 0)
        (List.finRange parameters.buses)
      simpa only [laterBuses, List.length_finRange] using bound
    have flagsBound : flags.steps.length ≤ parameters.buses *
        (2 * parameters.channels + parameters.channels * (qualifierBudget parameters + 1)) :=
      flagCount.trans (Nat.mul_le_mul_right _ lengthBound)
    have finalBound := activated.count
    have short : activated.steps.length ≤ 5 * parameters.buses + 3 := by omega
    simp only [List.length_append]
    have total := Nat.add_le_add flagsBound short
    simpa only [Nat.add_assoc] using total

theorem longMerge_supported (originalCount : Nat) (allowed : Nat → Prop)
    (priorSteps : List (Step v)) (current : State v)
    (pivot : Literal (Fin v)) (leftRest rightRest : Clause (Fin v))
    (left : AvailableSubclause current (negate pivot :: leftRest))
    (right : AvailableSubclause current (pivot :: rightRest))
    (supported : Controller.NativeProof.SourceBusSchedule.TraceOriginalSupport originalCount allowed priorSteps)
    (originalBound : ∀ id, allowed id → id ≤ originalCount)
    (currentBound : originalCount ≤ current.lastId)
    (leftOrigin : Controller.NativeProof.SourceMismatchHandles.ResultOrigin
      originalCount allowed priorSteps left.row.id)
    (rightOrigin : Controller.NativeProof.SourceMismatchHandles.ResultOrigin
      originalCount allowed priorSteps right.row.id) :
    let actual := longMerge current pivot leftRest rightRest left right
    Controller.NativeProof.SourceBusSchedule.TraceOriginalSupport originalCount allowed
      (priorSteps ++ actual.steps) ∧
      Controller.NativeProof.SourceMismatchHandles.ResultOrigin originalCount allowed
        (priorSteps ++ actual.steps)
        (longMerge_result current pivot leftRest rightRest left right).row.id := by
  constructor
  · exact Controller.NativeProof.SourceFoldAggregateProvenance.appendMerge_origins_supported
      originalCount allowed priorSteps current left.row.id right.row.id pivot left.clause right.clause
      supported originalBound leftOrigin rightOrigin left.row.bound right.row.bound
  · exact Controller.NativeProof.SourceFoldAggregateProvenance.merge_origins
      originalCount allowed priorSteps current left.row.id right.row.id pivot left.clause right.clause
      leftOrigin rightOrigin currentBound

def ProjectionOriginalSupport (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    {target : Clause (Fin v)} {budget : Nat}
    (projection : SubclauseProjection prefixState.state target budget) : Prop :=
  Controller.NativeProof.SourceBusSchedule.TraceOriginalSupport
    (formula parameters).clauses.size
    (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
    (prefixState.steps ++ projection.steps) ∧
  Controller.NativeProof.SourceMismatchHandles.ResultOrigin
    (formula parameters).clauses.size
    (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
    (prefixState.steps ++ projection.steps) projection.result.row.id

theorem subclause_cast_id {before after : Clause (Fin v)}
    (equal : before = after)
    (typeEqual : AvailableSubclause state before = AvailableSubclause state after)
    (value : AvailableSubclause state before) :
    (Eq.mp typeEqual value).row.id = value.row.id := by
  subst after
  have same : typeEqual = rfl := Subsingleton.elim _ _
  rw [same]
  rfl

theorem guardNegatedRow_allowed (rename : Nat → Fin v) (side : Side)
    (channel : Fin parameters.channels) (bus : Fin parameters.buses) :
    Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename
      (guardNegatedRow rename side channel bus).row.id := by
  have original := Controller.NativeProof.SourceQualifierOccurrences.guardRows_allowed
    rename side channel bus ⟨0, by decide⟩
  have sameId : (guardNegatedRow rename side channel bus).row.id =
      ((Controller.NativeProof.SourceQualifierOccurrences.guardRows rename side channel bus).row
        ⟨0, by change 0 < 3; decide⟩).id := by
    unfold guardNegatedRow
    dsimp only [retarget, ofRow]
    apply subclause_cast_id
    simp only [Bounded.Producer.rows, Gate.clauses, List.cons_append, List.nil_append,
      List.getElem_cons_succ, List.getElem_cons_zero, Rows.mapClause, List.map_cons,
      List.map_nil, guardHandle, guardBefore_negated, mapLiteral, negate, Std.Sat.Literal.negate]
  rw [sameId]
  exact original

theorem privateFlagRow_allowed (rename : Nat → Fin v) (side : Side)
    (bus : Fin parameters.buses) :
    Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename
      (privateFlagRow rename side bus).row.id := by
  have original := Controller.NativeProof.SourceQualifierOccurrences.negatedFlagRows_allowed
    rename side bus ⟨0, by decide⟩
  have sameId : (privateFlagRow rename side bus).row.id =
      ((Controller.NativeProof.SourceQualifierOccurrences.negatedFlagRows rename side bus).row
        ⟨0, by change 0 < 2; decide⟩).id := by
    unfold privateFlagRow
    dsimp only [ofRow]
    apply subclause_cast_id
    simp only [Bounded.Producer.rows, Gate.clauses, List.cons_append, List.nil_append,
      List.getElem_cons_succ, List.getElem_cons_zero, Rows.mapClause, List.map_cons,
      List.map_nil, negatedHandle, flagInput, mapLiteral]
  rw [sameId]
  exact original

open Controller.NativeProof.SourceFoldOwners Controller.NativeProof.SourceQualifierOccurrences
open Controller.NativeProof.SourceFoldProvenance Controller.NativeProof.SourceMismatchHandles

theorem family_cast_eq_mp {α : Sort _} {family : α → Sort _}
    {before after : α} (equal : before = after) (value : family before) :
    Eq.rec (motive := fun index _ => family index) value equal =
      Eq.mp (congrArg family equal) value := by
  cases equal
  rfl

theorem available_state_mpr_id {before after : State v} {clause : Clause (Fin v)}
    (same : before = after)
    (typeEqual : Rows.Available before clause = Rows.Available after clause)
    (row : Rows.Available after clause) : (Eq.mpr typeEqual row).id = row.id := by
  subst after
  rfl

theorem available_indices_mpr_id {beforeState afterState : State v}
    {beforeClause afterClause : Clause (Fin v)}
    (stateEqual : beforeState = afterState) (clauseEqual : beforeClause = afterClause)
    (typeEqual : Rows.Available beforeState beforeClause = Rows.Available afterState afterClause)
    (row : Rows.Available afterState afterClause) : (Eq.mpr typeEqual row).id = row.id := by
  subst afterState
  subst afterClause
  rfl

theorem available_indices_mp_id {beforeState afterState : State v}
    {beforeClause afterClause : Clause (Fin v)}
    (stateEqual : beforeState = afterState) (clauseEqual : beforeClause = afterClause)
    (typeEqual : Rows.Available beforeState beforeClause = Rows.Available afterState afterClause)
    (row : Rows.Available beforeState beforeClause) : (Eq.mp typeEqual row).id = row.id := by
  subst afterState
  subst afterClause
  rfl

theorem subclause_dite_id {state : State v} {target : Clause (Fin v)}
    (condition : Prop) [Decidable condition]
    (yes : condition → AvailableSubclause state target)
    (no : ¬condition → AvailableSubclause state target) :
    (dite condition yes no).row.id =
      dite condition (fun proof => (yes proof).row.id) (fun proof => (no proof).row.id) := by
  by_cases proof : condition
  · calc
      _ = (yes proof).row.id := congrArg
        (fun row : AvailableSubclause state target => row.row.id) (dite_eq_left proof)
      _ = _ := by
        have scalar : dite condition (fun evidence => (yes evidence).row.id)
            (fun evidence => (no evidence).row.id) = (yes proof).row.id := dite_eq_left proof
        exact scalar.symm
  · calc
      _ = (no proof).row.id := congrArg
        (fun row : AvailableSubclause state target => row.row.id) (dite_eq_right proof)
      _ = _ := by
        have scalar : dite condition (fun evidence => (yes evidence).row.id)
            (fun evidence => (no evidence).row.id) = (no proof).row.id := dite_eq_right proof
        exact scalar.symm

theorem sourceOriginalRows_allowed (rename : Nat → Fin v)
    (owner : Fin (compile parameters).entries.length)
    (bound : owner.val < (controller parameters).entries.length) :
    ProducerOriginals (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      (sourceOriginalRows parameters rename owner) := by
  intro index
  refine Or.inl ⟨owner, bound, index, ?_⟩
  simp only [sourceOriginalRows, SourceRows.fullProducerRow, Rows.framedRow,
    Controller.NativeProof.SourceMismatchBranch.ownedRow]
  repeat' rw [available_indices_mpr_id
    (by simp only [SourceRows.formula_as_rows,
      SourceRows.sourceClauses_split parameters owner, List.append_assoc])
    (by simp [SourceRows.formula_as_rows, SourceRows.sourceClauses_split parameters owner,
      Rows.mapClause, ofClauses, List.getElem_append, index.isLt])]
  rfl

theorem sourceSupply_allowed (rename : Nat → Fin v)
    (producers : List (Bounded.Producer Nat))
    (owners : Fin producers.length → Fin (compile parameters).entries.length)
    (stored : ∀ index, (compile parameters).entries[(owners index).val].producer = producers[index.val])
    (bound : ∀ index, (owners index).val < (controller parameters).entries.length) :
    SupplyOriginals (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      (sourceSupply parameters rename producers owners stored) := by
  intro index
  have moved := producerOriginals_transport
    (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename) rename (stored index)
    (sourceOriginalRows parameters rename (owners index))
    (sourceOriginalRows_allowed rename (owners index) (bound index))
  have same : (sourceSupply parameters rename producers owners stored) index =
      Eq.mp (congrArg (OriginalRows _ rename) (stored index))
        (sourceOriginalRows parameters rename (owners index)) := by
    unfold sourceSupply
    exact family_cast_eq_mp (family := OriginalRows _ rename) (stored index) _
  rw [same]
  exact moved

theorem actualFoldRows_allowed (rename : Nat → Fin v) (cursor : Cursor parameters)
    (slot : Controller.Native.Variable parameters) (junction : Bounded.Junction)
    (inputs : List (Literal Nat))
    (retained : EntriesBefore (cursor.foldNative slot junction inputs) (controller parameters)) :
    SupplyOriginals (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      (foldRows rename cursor slot junction inputs (retained.trans controller_before_compile)) := by
  apply sourceSupply_allowed
  intro index
  rcases retained with ⟨suffix, equality⟩
  simp only [equality, Cursor.foldNative, Cursor.assign, List.length_append,
    List.length_map, List.length_zipIdx, SourceFoldOwners.foldOwner]
  have indexBound := index.isLt
  omega

theorem bus_occurrence_before_controller (side : Side)
    (position : Fin (laterBuses (parameters := parameters)).length) :
    EntriesBefore
      (laterBus parameters side (laterBuses (parameters := parameters))[position.val] (busBefore side position))
      (controller parameters) := by
  have selected := occurrence_before_of_eq
    (fun cursor bus => laterBus parameters side bus cursor)
    (fun cursor bus => laterBus_before side bus cursor)
    (initialMasks parameters side (tailStart side)) (laterBuses (parameters := parameters))
    ((laterBuses (parameters := parameters)).take position.val)
    ((laterBuses (parameters := parameters)).drop (position.val + 1))
    ((laterBuses (parameters := parameters))[position.val])
    (positional_decomposition _ position)
  let stages := (laterBuses (parameters := parameters)).foldl
    (fun cursor bus => laterBus parameters side bus cursor)
    (initialMasks parameters side (tailStart side))
  have continuation : EntriesBefore stages (SourceController.tail parameters side (tailStart side)) :=
    (negateFlags_before side stages).trans
      (foldl_before (fun cursor channel => eligible parameters side channel cursor)
        (fun cursor channel => eligible_before side channel cursor)
        (List.finRange parameters.channels) (negateFlags parameters side stages))
  exact selected.trans (continuation.trans (Controller.NativeProof.SourceQualifierOccurrences.tail_end_before_controller side))

theorem term_occurrence_before_controller (side : Side)
    (position : Fin (laterBuses (parameters := parameters)).length) (channel : Fin parameters.channels) :
    EntriesBefore
      (termStep side ((laterBuses (parameters := parameters))[position.val])
        (termBefore side position channel) channel) (controller parameters) := by
  have bound : channel.val < (List.finRange parameters.channels).length := by simpa using channel.isLt
  have split := positional_decomposition (List.finRange parameters.channels) ⟨channel.val, bound⟩
  have decomposition : List.finRange parameters.channels =
      (List.finRange parameters.channels).take channel.val ++ channel ::
        (List.finRange parameters.channels).drop (channel.val + 1) := by simpa using split
  have selected := occurrence_before_of_eq
    (termStep side ((laterBuses (parameters := parameters))[position.val]))
    (fun cursor index => foldNative_before cursor _ _ _)
    (busBefore side position) (List.finRange parameters.channels) _ _ channel decomposition
  exact selected.trans ((foldNative_before _ _ _ _).trans
    ((flag_before_laterBus side _ _).trans (bus_occurrence_before_controller side position)))


theorem laterFlagRows_allowed (rename : Nat → Fin v) (side : Side)
    (position : Fin (laterBuses (parameters := parameters)).length) :
    SupplyOriginals (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      (laterFlagRows rename side position) := by
  unfold laterFlagRows
  dsimp only
  apply actualFoldRows_allowed
  exact (flag_before_laterBus side _ _).trans (bus_occurrence_before_controller side position)

theorem laterTermRows_allowed (rename : Nat → Fin v) (side : Side)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (channel : Fin parameters.channels) :
    SupplyOriginals (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      (laterTermRows rename side position channel) := by
  unfold laterTermRows
  dsimp only
  apply actualFoldRows_allowed
  exact term_occurrence_before_controller side position channel

theorem laterTermTree_originals (rename : Nat → Fin v) (side : Side)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (channel : Fin parameters.channels) :
    TreeOriginals (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      (laterTermTree rename side position channel) := by
  unfold laterTermTree
  apply allocateForest_originals
  · exact initialForest_originals _ _ _
  · exact laterTermRows_allowed rename side position channel

theorem laterFlagTree_originals (rename : Nat → Fin v) (side : Side)
    (position : Fin (laterBuses (parameters := parameters)).length) :
    TreeOriginals (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      (laterFlagTree rename side position) := by
  change TreeOriginals _ (allocateOrForest
    (initialOrForest rename (laterFlagInputs side position))
    (busTerms side ((laterBuses (parameters := parameters))[position.val])
      (busBefore side position)).lastID
    (laterFlagInputs_nonempty side position) (laterFlagRows rename side position))
  apply Controller.NativeProof.SourceFoldAggregateProvenance.allocateOrForest_originals
  · exact Controller.NativeProof.SourceFoldAggregateProvenance.initialOrForest_originals _ _ _
  · exact laterFlagRows_allowed rename side position

theorem prefix_native_count_le (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename) :
    (formula parameters).clauses.size ≤ prefixState.state.lastId := by
  have bound := runSteps_lastId_le prefixState.checked
  simpa only [initialState, relabel, Controller.CNF.OrderedFormula.relabel, Array.size_map] using bound

theorem allowed_native_count_le (rename : Nat → Fin v) (id : Nat)
    (allowed : Controller.NativeProof.SourceMismatchBranch.AllowedOriginal
      (parameters := parameters) rename id) : id ≤ (formula parameters).clauses.size := by
  have bound := Controller.NativeProof.SourceMismatchHandles.allowedOriginal_initial_bound rename id allowed
  simpa only [initialState, relabel, Controller.CNF.OrderedFormula.relabel, Array.size_map] using bound

theorem guardOrFlagAt_supported (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (side : Side) (channel : Fin parameters.channels) (bus : Fin parameters.buses)
    (supported : PrefixOriginalSupport rename prefixState) :
    ProjectionOriginalSupport rename prefixState (guardOrFlagAt rename prefixState side channel bus) := by
  let q := mapLiteral rename (negatedHandle side bus)
  let g := mapLiteral rename (guardHandle side channel bus)
  let p := mapLiteral rename (flagInput side bus)
  let left := FoldProjection.afterTrace (guardNegatedRow rename side channel bus)
    prefixState.state prefixState.steps prefixState.checked
  let right := FoldProjection.afterTrace (privateFlagRow rename side bus)
    prefixState.state prefixState.steps prefixState.checked
  have one : Controller.NativeProof.SourceMismatchHandles.ResultOrigin
      (formula parameters).clauses.size
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      prefixState.steps left.row.id :=
    Or.inl (guardNegatedRow_allowed rename side channel bus)
  have two : Controller.NativeProof.SourceMismatchHandles.ResultOrigin
      (formula parameters).clauses.size
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      prefixState.steps right.row.id :=
    Or.inl (privateFlagRow_allowed rename side bus)
  have result := longMerge_supported (formula parameters).clauses.size
    (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
    prefixState.steps prefixState.state q [g] [p] left right supported
    (allowed_native_count_le rename) (prefix_native_count_le rename prefixState) one two
  exact result

theorem firstTermGuardMixedAt_supported (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (channel : Fin parameters.channels) (supported : PrefixOriginalSupport rename prefixState) :
    ProjectionOriginalSupport rename prefixState
      (firstTermGuardMixedAt rename prefixState position channel) :=
  guardOrFlagAt_supported rename prefixState .faulty channel parameters.firstBus supported

theorem traceOriginalSupport_append (originalCount : Nat) (allowed : Nat → Prop)
    (before after : List (Step v))
    (one : Controller.NativeProof.SourceBusSchedule.TraceOriginalSupport originalCount allowed before)
    (two : Controller.NativeProof.SourceBusSchedule.TraceOriginalSupport originalCount allowed after) :
    Controller.NativeProof.SourceBusSchedule.TraceOriginalSupport originalCount allowed (before ++ after) := by
  intro step member parent parentMember
  rcases List.mem_append.mp member with member | member
  · have previous := one step member parent parentMember
    refine ⟨previous.1, ?_⟩
    intro later
    rcases previous.2 later with ⟨earlier, contained, same, bound⟩
    exact ⟨earlier, List.mem_append_left _ contained, same, bound⟩
  · have previous := two step member parent parentMember
    refine ⟨previous.1, ?_⟩
    intro later
    rcases previous.2 later with ⟨earlier, contained, same, bound⟩
    exact ⟨earlier, List.mem_append_right _ contained, same, bound⟩

theorem nonunaryTreeInputs_supported (tree : AndTree state root inputs) (two : 2 ≤ inputs.length)
    (originalCount : Nat) (allowed : Nat → Prop)
    (original : TreeOriginals allowed tree)
    (originalBound : ∀ id, allowed id → id ≤ originalCount)
    (bound : originalCount ≤ state.lastId) :
    let actual := nonunaryTreeInputs tree two
    Controller.NativeProof.SourceBusSchedule.TraceOriginalSupport originalCount allowed actual.steps ∧
      ∀ input member, Controller.NativeProof.SourceMismatchHandles.ResultOrigin
        originalCount allowed actual.steps (actual.results input member).row.id := by
  have result := projectTreeInputs_supported tree originalCount allowed original originalBound bound
  cases tree with
  | leaf input => simp at two
  | @node left right leftInputs rightInputs leftTree rightTree output rows =>
    constructor
    · exact result.1
    · intro input member
      have origin := result.2 input member
      by_cases leftMem : input ∈ leftInputs
      · convert origin using 1 <;>
          simp only [nonunaryTreeInputs, projectTreeInputs, CertificateOrigin,
            FoldProjection.afterTrace, getter_transport, getter_transport_apply,
            getter_transport_apply_two, dite_apply, ite_apply, apply_dite, apply_ite]
        all_goals rw [subclause_dite_id, dite_eq_left leftMem]
        all_goals simp only [dite_eq_left leftMem, CertificateOrigin]
      · convert origin using 1 <;>
          simp only [nonunaryTreeInputs, projectTreeInputs, CertificateOrigin,
            FoldProjection.afterTrace, getter_transport, getter_transport_apply,
            getter_transport_apply_two, dite_apply, ite_apply, apply_dite, apply_ite]
        all_goals rw [subclause_dite_id, dite_eq_right leftMem]
        all_goals simp only [dite_eq_right leftMem, CertificateOrigin]


theorem guardRequestRow_allowed (rename : Nat → Fin v) (side : Side)
    (channel : Fin parameters.channels) (bus : Fin parameters.buses) :
    Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename
      (guardRequestRow rename side channel bus).row.id := by
  have original := Controller.NativeProof.SourceQualifierOccurrences.guardRows_allowed
    rename side channel bus ⟨1, by change 1 < 3; decide⟩
  have sameId : (guardRequestRow rename side channel bus).row.id =
      ((guardRows rename side channel bus).row ⟨1, by change 1 < 3; decide⟩).id := by
    unfold guardRequestRow
    dsimp only [retarget, ofRow]
    apply subclause_cast_id
    simp only [Bounded.Producer.rows, Gate.clauses, List.cons_append, List.nil_append,
      List.getElem_cons_succ, List.getElem_cons_zero, Rows.mapClause, List.map_cons,
      List.map_nil, guardHandle, (guardBefore_roots side channel bus).2 bus channel,
      requestHandle, mapLiteral, negate, Std.Sat.Literal.negate]
  rw [sameId]
  exact original

theorem sameBusTermGuardAt_supported (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename) (side : Side)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (channel : Fin parameters.channels) (supported : PrefixOriginalSupport rename prefixState) :
    ProjectionOriginalSupport rename prefixState
      (sameBusTermGuardAt rename prefixState side position channel) := by
  let bus := (laterBuses (parameters := parameters))[position.val]
  let request := mapLiteral rename (requestHandle bus channel)
  let root := laterTermOutput rename side position channel
  let guard := mapLiteral rename (guardHandle side channel bus)
  let tree := (laterTermTree rename side position channel).afterTrace
    prefixState.state prefixState.steps prefixState.checked
  have two : 2 ≤ ((laterTermInputs side position channel).map (mapLiteral rename)).length := by
    simp [laterTermInputs]
  let projected := nonunaryTreeInputs tree two
  have member : request ∈ ((laterTermInputs side position channel).map (mapLiteral rename)) := by
    apply List.mem_map.mpr
    refine ⟨(termBefore side position channel).slots (.primary (.request bus channel)), ?_, ?_⟩
    · simp [laterTermInputs, bus]
    · rw [(termBefore_roots side position channel).2 bus channel]
      rfl
  have originals := treeOriginals_afterTrace
    (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
    (laterTermTree rename side position channel)
    (laterTermTree_originals rename side position channel)
    prefixState.state prefixState.steps prefixState.checked
  have projectedSupport := nonunaryTreeInputs_supported tree two
    (formula parameters).clauses.size
    (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
    originals (allowed_native_count_le rename) (prefix_native_count_le rename prefixState)
  have complete := traceOriginalSupport_append _ _ prefixState.steps projected.steps
    supported projectedSupport.1
  let direction := projected.results request member
  let kept := FoldProjection.afterTrace (guardRequestRow rename side channel bus)
    prefixState.state prefixState.steps prefixState.checked
  let guardRow := FoldProjection.afterTrace kept projected.state projected.steps projected.checked
  let left : AvailableSubclause projected.state [negate request, guard] := guardRow
  let right : AvailableSubclause projected.state [request, negate root] := retarget direction (by
    intro literal found
    simp only [List.mem_cons, List.not_mem_nil, or_false] at found ⊢
    exact found.elim Or.inr Or.inl)
  have leftOrigin : Controller.NativeProof.SourceMismatchHandles.ResultOrigin
      (formula parameters).clauses.size
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      (prefixState.steps ++ projected.steps) left.row.id :=
    Or.inl (guardRequestRow_allowed rename side channel bus)
  have rightOrigin := resultOrigin_append_left (formula parameters).clauses.size
    (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
    prefixState.steps projected.steps direction.row.id (projectedSupport.2 request member)
  have currentBound := Nat.le_trans (prefix_native_count_le rename prefixState)
    (runSteps_lastId_le projected.checked)
  have joinedSupport := longMerge_supported (formula parameters).clauses.size
    (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
    (prefixState.steps ++ projected.steps) projected.state request [guard] [negate root]
    left right complete (allowed_native_count_le rename) currentBound leftOrigin rightOrigin
  simpa only [ProjectionOriginalSupport, sameBusTermGuardAt, List.append_assoc, retarget,
    bus, request, root, guard, tree, projected, direction, kept, guardRow, left, right]
    using joinedSupport

theorem futureGuardAt_supported (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (position later : Fin (laterBuses (parameters := parameters)).length)
    (channel : Fin parameters.channels) (outputs : Clause (Fin v))
    (bank : ClosedFlags rename prefixState position outputs) (order : position.val < later.val)
    (supported : PrefixOriginalSupport rename prefixState)
    (bankSupported : ClosedFlagsOriginalSupport rename prefixState position outputs bank) :
    ProjectionOriginalSupport rename prefixState
      (futureGuardAt rename prefixState position later channel outputs bank order) := by
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
  let kept := FoldProjection.afterTrace (bank later order) first.state first.steps first.checked
  let left : AvailableSubclause first.state (negate flag :: (context ++ outputs)) :=
    retarget kept (by
      intro literal member
      simp only [context, flag, List.mem_append, List.mem_cons] at member ⊢
      aesop)
  have leftOrigin := resultOrigin_append_right (formula parameters).clauses.size
    (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
    prefixState.steps first.steps (bank later order).row.id (bankSupported later order)
  have rightOrigin := firstSupported.2
  have currentBound := Nat.le_trans (prefix_native_count_le rename prefixState)
    (runSteps_lastId_le first.checked)
  have joinedSupport := longMerge_supported (formula parameters).clauses.size
    (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
    (prefixState.steps ++ first.steps) first.state flag (context ++ outputs) [guard]
    left right firstSupported.1 (allowed_native_count_le rename) currentBound leftOrigin rightOrigin
  simpa only [ProjectionOriginalSupport, futureGuardAt, List.append_assoc, retarget,
    bus, flag, guard, context, first, kept, left, right] using joinedSupport

theorem actualEmitRows_allowed (rename : Nat → Fin v) (cursor : Cursor parameters)
    (slot : Controller.Native.Variable parameters) (gate : Gate Nat)
    (retained : EntriesBefore (cursor.emitNative slot gate) (controller parameters)) :
    ProducerOriginals
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      (Controller.NativeProof.SourceCongruence.emitRows rename cursor slot gate
        (retained.trans controller_before_compile)) := by
  let retainedCompile := retained.trans controller_before_compile
  let owner := Controller.NativeProof.SourceCongruence.emitOwner cursor slot gate retainedCompile
  have ownerBound : owner.val < (controller parameters).entries.length := by
    rcases retained with ⟨suffix, equality⟩
    simp only [equality, Cursor.emitNative, Cursor.emit, Cursor.assign,
      List.length_append, List.length_cons, List.length_nil, owner,
      Controller.NativeProof.SourceCongruence.emitOwner]
    omega
  have equality := Controller.NativeProof.SourceCongruence.emitOwner_producer
    cursor slot gate retainedCompile
  intro index
  have bound : index.val < (compile parameters).entries[owner.val].producer.rows.length := by
    rw [equality]
    exact index.isLt
  have original := sourceOriginalRows_allowed rename owner ownerBound ⟨index.val, bound⟩
  simp only [Controller.NativeProof.SourceCongruence.emitRows]
  rw [available_indices_mp_id rfl (by simp only [equality])]
  exact original

theorem appendProjection_supported (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (first : SubclauseProjection prefixState.state firstTarget firstBudget)
    (second : SubclauseProjection first.state secondTarget secondBudget)
    (supported : ProjectionOriginalSupport rename
      (prefixState.extend first.state first.steps first.checked) second) :
    ProjectionOriginalSupport rename prefixState (appendProjection first second) := by
  simpa only [ProjectionOriginalSupport, SourcePrefix.extend, appendProjection,
    List.append_assoc] using supported

theorem rebudget_supported (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (projection : SubclauseProjection prefixState.state target before)
    (bound : before ≤ after) (supported : ProjectionOriginalSupport rename prefixState projection) :
    ProjectionOriginalSupport rename prefixState (rebudget projection bound) := supported

theorem contextualize_supported (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (projection : SubclauseProjection prefixState.state target budget)
    (context : Clause (Fin v)) (supported : ProjectionOriginalSupport rename prefixState projection) :
    ProjectionOriginalSupport rename prefixState (contextualize projection context) := supported

theorem bus_mask_before_controller (side : Side)
    (position : Fin (laterBuses (parameters := parameters)).length) (channel : Fin parameters.channels) :
    EntriesBefore (busMaskStep side ((laterBuses (parameters := parameters))[position.val])
      (laterAbsentBefore side position channel) channel) (controller parameters) := by
  have bound : channel.val < (List.finRange parameters.channels).length := by simpa using channel.isLt
  have split := positional_decomposition (List.finRange parameters.channels) ⟨channel.val, bound⟩
  have decomposition : List.finRange parameters.channels =
      (List.finRange parameters.channels).take channel.val ++ channel ::
        (List.finRange parameters.channels).drop (channel.val + 1) := by simpa using split
  have selected := occurrence_before_of_eq
    (busMaskStep side ((laterBuses (parameters := parameters))[position.val]))
    (fun cursor index => (emitNative_before cursor _ _).trans (emitNative_before _ _ _))
    (busFlag side ((laterBuses (parameters := parameters))[position.val]) (busBefore side position))
    (List.finRange parameters.channels) _ _ channel decomposition
  exact selected.trans (bus_occurrence_before_controller side position)

theorem laterAbsentRows_allowed (rename : Nat → Fin v) (side : Side)
    (position : Fin (laterBuses (parameters := parameters)).length) (channel : Fin parameters.channels) :
    ProducerOriginals
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      (laterAbsentRows rename side position channel) := by
  unfold laterAbsentRows
  dsimp only
  apply actualEmitRows_allowed
  exact (emitNative_before _ _ _).trans (bus_mask_before_controller side position channel)

theorem laterMaskRows_allowed (rename : Nat → Fin v) (side : Side)
    (position : Fin (laterBuses (parameters := parameters)).length) (channel : Fin parameters.channels) :
    ProducerOriginals
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      (laterMaskRows rename side position channel) := by
  unfold laterMaskRows
  dsimp only
  apply actualEmitRows_allowed
  exact bus_mask_before_controller side position channel

theorem laterAbsentPositive_allowed (rename : Nat → Fin v) (side : Side)
    (position : Fin (laterBuses (parameters := parameters)).length) (channel : Fin parameters.channels)
    (prefixState : SourcePrefix (parameters := parameters) rename) :
    Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename
      (laterAbsentNativeRows rename side position channel prefixState).positive.row.id := by
  exact laterAbsentRows_allowed rename side position channel ⟨0, by change 0 < 2; decide⟩

theorem laterMaskOneOne_allowed (rename : Nat → Fin v) (side : Side)
    (position : Fin (laterBuses (parameters := parameters)).length) (channel : Fin parameters.channels)
    (prefixState : SourcePrefix (parameters := parameters) rename) :
    Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename
      (laterMaskNativeRows rename side position channel prefixState).oneOne.row.id := by
  exact laterMaskRows_allowed rename side position channel ⟨1, by change 1 < 4; decide⟩

theorem guardedChain_supported (originalCount : Nat) (allowed : Nat → Prop)
    (priorSteps : List (Step v)) (state : State v) (context : Clause (Fin v))
    (root middle output : Literal (Fin v))
    (first : AvailableSubclause state (context ++ [negate root, middle]))
    (second : AvailableSubclause state (context ++ [negate middle, output]))
    (supported : Controller.NativeProof.SourceBusSchedule.TraceOriginalSupport originalCount allowed priorSteps)
    (originalBound : ∀ id, allowed id → id ≤ originalCount)
    (bound : originalCount ≤ state.lastId)
    (firstOrigin : Controller.NativeProof.SourceMismatchHandles.ResultOrigin originalCount allowed priorSteps first.row.id)
    (secondOrigin : Controller.NativeProof.SourceMismatchHandles.ResultOrigin originalCount allowed priorSteps second.row.id) :
    let actual := guardedChain state context root middle output first second
    Controller.NativeProof.SourceBusSchedule.TraceOriginalSupport originalCount allowed (priorSteps ++ actual.steps) ∧
      Controller.NativeProof.SourceMismatchHandles.ResultOrigin originalCount allowed
        (priorSteps ++ actual.steps) actual.result.row.id := by
  constructor
  · exact Controller.NativeProof.SourceFoldAggregateProvenance.appendMerge_origins_supported
      originalCount allowed priorSteps state second.row.id first.row.id middle
      second.clause first.clause supported originalBound secondOrigin firstOrigin
      second.row.bound first.row.bound
  · exact Controller.NativeProof.SourceFoldAggregateProvenance.merge_origins
      originalCount allowed priorSteps state second.row.id first.row.id middle
      second.clause first.clause secondOrigin firstOrigin bound

theorem maskGuardRows_supported (originalCount : Nat) (allowed : Nat → Prop)
    (priorSteps : List (Step v)) (state : State v) (p z u m g : Literal (Fin v))
    (leftOne : AvailableSubclause state [negate p, negate u, negate m])
    (positiveNot : AvailableSubclause state [u, z])
    (rightOne : AvailableSubclause state [p, g])
    (termGuard : AvailableSubclause state [negate z, g])
    (supported : Controller.NativeProof.SourceBusSchedule.TraceOriginalSupport originalCount allowed priorSteps)
    (originalBound : ∀ id, allowed id → id ≤ originalCount)
    (bound : originalCount ≤ state.lastId)
    (leftOrigin : Controller.NativeProof.SourceMismatchHandles.ResultOrigin originalCount allowed priorSteps leftOne.row.id)
    (notOrigin : Controller.NativeProof.SourceMismatchHandles.ResultOrigin originalCount allowed priorSteps positiveNot.row.id)
    (rightOrigin : Controller.NativeProof.SourceMismatchHandles.ResultOrigin originalCount allowed priorSteps rightOne.row.id)
    (termOrigin : Controller.NativeProof.SourceMismatchHandles.ResultOrigin originalCount allowed priorSteps termGuard.row.id) :
    let actual := maskGuardRows state p z u m g leftOne positiveNot rightOne termGuard
    Controller.NativeProof.SourceBusSchedule.TraceOriginalSupport originalCount allowed (priorSteps ++ actual.steps) ∧
      Controller.NativeProof.SourceMismatchHandles.ResultOrigin originalCount allowed
        (priorSteps ++ actual.steps) actual.result.row.id := by
  let joinOne := longMerge state p [negate u, negate m] [g] leftOne rightOne
  have runOne := longMerge_run state p [negate u, negate m] [g] leftOne rightOne
  have supportOne := longMerge_supported originalCount allowed priorSteps state p
    [negate u, negate m] [g] leftOne rightOne supported originalBound bound leftOrigin rightOrigin
  let leftTwo := FoldProjection.afterTrace termGuard joinOne.state joinOne.steps runOne
  let notRow := FoldProjection.afterTrace positiveNot joinOne.state joinOne.steps runOne
  let rightTwo : AvailableSubclause joinOne.state [z, u] := retarget notRow (by
    intro literal found
    simp only [List.mem_cons, List.not_mem_nil, or_false] at found ⊢
    exact found.elim Or.inr Or.inl)
  let joinTwo := longMerge joinOne.state z [g] [u] leftTwo rightTwo
  have runTwo := longMerge_run joinOne.state z [g] [u] leftTwo rightTwo
  have termKept := resultOrigin_append_right originalCount allowed priorSteps joinOne.steps
    termGuard.row.id termOrigin
  have notKept := resultOrigin_append_right originalCount allowed priorSteps joinOne.steps
    positiveNot.row.id notOrigin
  have boundOne := Nat.le_trans bound (runSteps_lastId_le runOne)
  have supportTwo := longMerge_supported originalCount allowed (priorSteps ++ joinOne.steps)
    joinOne.state z [g] [u] leftTwo rightTwo supportOne.1 originalBound boundOne termKept notKept
  let leftThree := FoldProjection.afterTrace
    (longMerge_result state p [negate u, negate m] [g] leftOne rightOne)
    joinTwo.state joinTwo.steps runTwo
  let rightThree : AvailableSubclause joinTwo.state [u, g] :=
    retarget (longMerge_result joinOne.state z [g] [u] leftTwo rightTwo) (by
      intro literal found
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at found ⊢
      exact found.elim Or.inr Or.inl)
  have oneKept := resultOrigin_append_right originalCount allowed
    (priorSteps ++ joinOne.steps) joinTwo.steps
    (longMerge_result state p [negate u, negate m] [g] leftOne rightOne).row.id supportOne.2
  have boundTwo := Nat.le_trans boundOne (runSteps_lastId_le runTwo)
  have supportThree := longMerge_supported originalCount allowed
    ((priorSteps ++ joinOne.steps) ++ joinTwo.steps) joinTwo.state u [negate m, g] [g]
    leftThree rightThree supportTwo.1 originalBound boundTwo oneKept supportTwo.2
  simpa only [maskGuardRows, List.append_assoc, retarget,
    joinOne, leftTwo, notRow, rightTwo, joinTwo, leftThree, rightThree]
    using supportThree

theorem maskGuardAt_supported (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename) (side : Side)
    (position : Fin (laterBuses (parameters := parameters)).length) (channel : Fin parameters.channels)
    (supported : PrefixOriginalSupport rename prefixState) :
    ProjectionOriginalSupport rename prefixState (maskGuardAt rename prefixState side position channel) := by
  let bus := (laterBuses (parameters := parameters))[position.val]
  let g := mapLiteral rename (guardHandle side channel bus)
  let p := laterFlagOutput rename side position
  let z := laterTermOutput rename side position channel
  let u := laterAbsentOutput rename side position channel
  let m := laterMaskOutput rename side position channel
  let first := guardOrFlagAt rename prefixState side channel bus
  have firstSupport := guardOrFlagAt_supported rename prefixState side channel bus supported
  let current := prefixState.extend first.state first.steps first.checked
  let second := sameBusTermGuardAt rename current side position channel
  have secondSupport := sameBusTermGuardAt_supported rename current side position channel firstSupport.1
  let next := current.extend second.state second.steps second.checked
  let originalXor := laterMaskNativeRows rename side position channel next
  let originalNot := laterAbsentNativeRows rename side position channel next
  let guardFlag := FoldProjection.afterTrace first.result second.state second.steps second.checked
  have flagAligned : mapLiteral rename (flagInput side bus) = p := by
    rw [flagInput_busFlag side position]
    rfl
  let leftOne : AvailableSubclause second.state [negate p, negate u, negate m] := by
    simpa only [next, SourcePrefix.extend, laterMaskFlag_eq_flagOutput,
      laterMaskAbsent_eq_absentOutput, p, u, m] using originalXor.oneOne
  let rightOne : AvailableSubclause second.state [p, g] := retarget guardFlag (by
    intro literal found
    have member := found
    simp only [List.mem_cons, List.not_mem_nil, or_false, flagAligned] at member ⊢
    exact member.elim Or.inr Or.inl)
  let positiveNot : AvailableSubclause second.state [u, z] := by
    simpa only [next, SourcePrefix.extend, laterAbsentInput_eq_termOutput, u, z]
      using originalNot.positive
  have leftId : leftOne.row.id = originalXor.oneOne.row.id := by
    dsimp only [leftOne]
    apply subclause_cast_id
    simp only [next, SourcePrefix.extend, laterMaskFlag_eq_flagOutput,
      laterMaskAbsent_eq_absentOutput, p, u, m]
  have notId : positiveNot.row.id = originalNot.positive.row.id := by
    dsimp only [positiveNot]
    apply subclause_cast_id
    simp only [next, SourcePrefix.extend, laterAbsentInput_eq_termOutput, u, z]
  have leftOrigin : Controller.NativeProof.SourceMismatchHandles.ResultOrigin
      (formula parameters).clauses.size
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      next.steps leftOne.row.id := by
    rw [leftId]
    exact Or.inl (laterMaskOneOne_allowed rename side position channel next)
  have notOrigin : Controller.NativeProof.SourceMismatchHandles.ResultOrigin
      (formula parameters).clauses.size
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      next.steps positiveNot.row.id := by
    rw [notId]
    exact Or.inl (laterAbsentPositive_allowed rename side position channel next)
  have rightOrigin := resultOrigin_append_right (formula parameters).clauses.size
    (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
    (prefixState.steps ++ first.steps) second.steps first.result.row.id firstSupport.2
  have joinedSupport := maskGuardRows_supported (formula parameters).clauses.size
    (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
    next.steps second.state p z u m g leftOne positiveNot rightOne second.result
    secondSupport.1 (allowed_native_count_le rename) (prefix_native_count_le rename next)
    leftOrigin notOrigin rightOrigin secondSupport.2
  simpa only [ProjectionOriginalSupport, maskGuardAt, appendProjection, SourcePrefix.extend,
    List.append_assoc, retarget, bus, g, p, z, u, m, first, current, second, next,
    originalXor, originalNot, guardFlag, leftOne, rightOne, positiveNot]
    using joinedSupport

theorem earlierTermGuardAt_supported (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename) (side : Side)
    (earlier later : Fin (laterBuses (parameters := parameters)).length)
    (order : earlier.val < later.val) (channel : Fin parameters.channels)
    (supported : PrefixOriginalSupport rename prefixState) :
    ProjectionOriginalSupport rename prefixState
      (earlierTermGuardAt rename prefixState side earlier later order channel) := by
  let first := maskGuardAt rename prefixState side earlier channel
  have firstSupport := maskGuardAt_supported rename prefixState side earlier channel supported
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
  have original := treeOriginals_afterTrace
    (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
    (laterTermTree rename side later channel) (laterTermTree_originals rename side later channel)
    current.state current.steps current.checked
  have projectedSupport := nonunaryTreeInputs_supported tree two
    (formula parameters).clauses.size
    (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
    original (allowed_native_count_le rename) (prefix_native_count_le rename current)
  have complete := traceOriginalSupport_append _ _ current.steps projected.steps
    firstSupport.1 projectedSupport.1
  let direction := projected.results mask member
  let guardRow := FoldProjection.afterTrace first.result projected.state projected.steps projected.checked
  have directionOrigin := resultOrigin_append_left (formula parameters).clauses.size
    (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
    current.steps projected.steps direction.row.id (projectedSupport.2 mask member)
  have guardOrigin := resultOrigin_append_right (formula parameters).clauses.size
    (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
    current.steps projected.steps first.result.row.id firstSupport.2
  have bound := Nat.le_trans (prefix_native_count_le rename current)
    (runSteps_lastId_le projected.checked)
  have joinedSupport := guardedChain_supported (formula parameters).clauses.size
    (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
    (current.steps ++ projected.steps) projected.state [] root mask guard direction guardRow
    complete (allowed_native_count_le rename) bound directionOrigin guardOrigin
  simpa only [ProjectionOriginalSupport, earlierTermGuardAt, SourcePrefix.extend, List.append_assoc,
    first, current, tree, projected, mask, root, guard, direction, guardRow] using joinedSupport

theorem data_getter_transport {ι : Sort _} {family : ι → Sort _} {β : Sort _}
    (getter : ∀ index, family index → β) {before after : ι} (equal : before = after)
    (value : family before) : getter after (equal ▸ value) = getter before value := by
  subst after
  rfl

theorem projection_cast_steps {before after : Clause (Fin v)} {budget : Nat}
    (equal : before = after)
    (typeEqual : SubclauseProjection state before budget = SubclauseProjection state after budget)
    (value : SubclauseProjection state before budget) :
    (Eq.mp typeEqual value).steps = value.steps := by
  subst after
  have same : typeEqual = rfl := Subsingleton.elim _ _
  rw [same]
  rfl

theorem projection_cast_id {before after : Clause (Fin v)} {budget : Nat}
    (equal : before = after)
    (typeEqual : SubclauseProjection state before budget = SubclauseProjection state after budget)
    (value : SubclauseProjection state before budget) :
    (Eq.mp typeEqual value).result.row.id = value.result.row.id := by
  subst after
  have same : typeEqual = rfl := Subsingleton.elim _ _
  rw [same]
  rfl

theorem earlierGuardAt_supported (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (channel : Fin parameters.channels) (bus : Fin parameters.buses)
    (before : bus ≤ (laterBuses (parameters := parameters))[position.val])
    (supported : PrefixOriginalSupport rename prefixState) :
    ProjectionOriginalSupport rename prefixState
      (earlierGuardAt rename prefixState position channel bus before) := by
  by_cases zero : bus.val = 0
  · have same : bus = parameters.firstBus := Fin.ext zero
    have actual := firstTermGuardMixedAt_supported rename prefixState position channel supported
    have stepsEqual : (earlierGuardAt rename prefixState position channel bus before).steps =
        (firstTermGuardMixedAt rename prefixState position channel).steps := by
      unfold earlierGuardAt
      rw [dite_eq_left zero]
      exact projection_cast_steps (by simp only [same]) _ _
    have idEqual : (earlierGuardAt rename prefixState position channel bus before).result.row.id =
        (firstTermGuardMixedAt rename prefixState position channel).result.row.id := by
      unfold earlierGuardAt
      rw [dite_eq_left zero]
      exact projection_cast_id (by simp only [same]) _ _
    unfold ProjectionOriginalSupport at actual ⊢
    rw [stepsEqual, idEqual]
    exact actual
  · let earlier := laterPosition bus zero
    have selected : (laterBuses (parameters := parameters))[earlier.val] = bus := laterPosition_bus bus zero
    have bounded : earlier.val ≤ position.val := by
      by_contra reversed
      have sorted : (laterBuses (parameters := parameters)).Pairwise (· < ·) :=
        (List.pairwise_lt_finRange parameters.buses).filter _
      have strict := sorted.rel_get_of_lt (Nat.lt_of_not_ge reversed)
      simp only [List.get_eq_getElem] at strict
      rw [selected] at strict
      exact (not_lt_of_ge before) strict
    by_cases same : earlier = position
    · have sameBus : bus = (laterBuses (parameters := parameters))[position.val] := by
        simpa only [same] using selected.symm
      have actual := sameBusTermGuardAt_supported rename prefixState .faulty position channel supported
      have stepsEqual : (earlierGuardAt rename prefixState position channel bus before).steps =
          (sameBusTermGuardAt rename prefixState .faulty position channel).steps := by
        unfold earlierGuardAt
        rw [dite_eq_right zero, dite_eq_left same]
        exact projection_cast_steps (by simp only [sameBus]) _ _
      have idEqual : (earlierGuardAt rename prefixState position channel bus before).result.row.id =
          (sameBusTermGuardAt rename prefixState .faulty position channel).result.row.id := by
        unfold earlierGuardAt
        rw [dite_eq_right zero, dite_eq_left same]
        exact projection_cast_id (by simp only [sameBus]) _ _
      unfold ProjectionOriginalSupport at actual ⊢
      rw [stepsEqual, idEqual]
      exact actual
    · have order : earlier.val < position.val := by
        have different : earlier.val ≠ position.val := fun equal => same (Fin.ext equal)
        omega
      have actual := earlierTermGuardAt_supported rename prefixState .faulty earlier position order channel supported
      have stepsEqual : (earlierGuardAt rename prefixState position channel bus before).steps =
          (earlierTermGuardAt rename prefixState .faulty earlier position order channel).steps := by
        unfold earlierGuardAt
        rw [dite_eq_right zero, dite_eq_right same]
        exact projection_cast_steps (by rw [laterPosition_bus bus zero]) _ _
      have idEqual : (earlierGuardAt rename prefixState position channel bus before).result.row.id =
          (earlierTermGuardAt rename prefixState .faulty earlier position order channel).result.row.id := by
        unfold earlierGuardAt
        rw [dite_eq_right zero, dite_eq_right same]
        exact projection_cast_id (by rw [laterPosition_bus bus zero]) _ _
      unfold ProjectionOriginalSupport at actual ⊢
      rw [stepsEqual, idEqual]
      exact actual

theorem termEnableAt_supported (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename) (side : Side)
    (position : Fin (laterBuses (parameters := parameters)).length) (channel : Fin parameters.channels)
    (supported : PrefixOriginalSupport rename prefixState) :
    ProjectionOriginalSupport rename prefixState (termEnableAt rename prefixState side position channel) := by
  let tree := (laterTermTree rename side position channel).afterTrace
    prefixState.state prefixState.steps prefixState.checked
  have two : 2 ≤ ((laterTermInputs side position channel).map (mapLiteral rename)).length := by
    simp [laterTermInputs]
  let projected := nonunaryTreeInputs tree two
  have member : mapLiteral rename ((qualifierGuarded side channel).slots (.primary (.enable channel))) ∈
      (laterTermInputs side position channel).map (mapLiteral rename) := by
    rw [qualifier_enable_eq_term side position channel]
    apply List.mem_map.mpr
    exact ⟨_, by simp [laterTermInputs], rfl⟩
  have original := treeOriginals_afterTrace
    (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
    (laterTermTree rename side position channel) (laterTermTree_originals rename side position channel)
    prefixState.state prefixState.steps prefixState.checked
  have projectedSupport := nonunaryTreeInputs_supported tree two
    (formula parameters).clauses.size
    (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
    original (allowed_native_count_le rename) (prefix_native_count_le rename prefixState)
  have complete := traceOriginalSupport_append _ _ prefixState.steps projected.steps supported projectedSupport.1
  have origin := resultOrigin_append_left (formula parameters).clauses.size
    (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
    prefixState.steps projected.steps _ (projectedSupport.2 _ member)
  simpa only [ProjectionOriginalSupport, termEnableAt, tree, projected] using And.intro complete origin

theorem eliminateBankLeaves_supported (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (position : Fin (laterBuses (parameters := parameters)).length) (outputs : Clause (Fin v))
    (bank : ClosedFlags rename prefixState position outputs)
    (context : Clause (Fin v)) (output : Literal (Fin v))
    (inputs : List (Literal (Fin v))) (budget : Nat)
    (parent : AvailableSubclause prefixState.state (context ++ output :: inputs.map negate))
    (reason : ∀ (current : SourcePrefix (parameters := parameters) rename)
      (currentBank : ClosedFlags rename current position outputs) (index : Fin inputs.length),
      SubclauseProjection current.state (inputs[index.val] :: context) budget)
    (supported : PrefixOriginalSupport rename prefixState)
    (bankSupported : ClosedFlagsOriginalSupport rename prefixState position outputs bank)
    (parentOrigin : Controller.NativeProof.SourceMismatchHandles.ResultOrigin
      (formula parameters).clauses.size
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      prefixState.steps parent.row.id)
    (reasonSupported : ∀ current currentBank index,
      PrefixOriginalSupport rename current →
      ClosedFlagsOriginalSupport rename current position outputs currentBank →
      ProjectionOriginalSupport rename current (reason current currentBank index)) :
    ProjectionOriginalSupport rename prefixState
      (eliminateBankLeaves rename prefixState position outputs bank context output inputs budget parent reason) := by
  induction inputs generalizing prefixState with
  | nil =>
    have stepsEqual :
        (eliminateBankLeaves rename prefixState position outputs bank context output [] budget parent reason).steps = [] := by
      simp only [eliminateBankLeaves]
    have idEqual :
        (eliminateBankLeaves rename prefixState position outputs bank context output [] budget parent reason).result.row.id =
          parent.row.id := by
      rw [eliminateBankLeaves.eq_def]
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
    have currentBankSupported : ClosedFlagsOriginalSupport rename current position outputs currentBank := by
      intro later order
      have one := resultOrigin_append_right (formula parameters).clauses.size
        (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
        prefixState.steps direction.steps (bank later order).row.id (bankSupported later order)
      exact resultOrigin_append_right (formula parameters).clauses.size
        (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
        directed.steps joined.steps (bank later order).row.id one
    let tailReason : ∀ (now : SourcePrefix (parameters := parameters) rename)
      (nowBank : ClosedFlags rename now position outputs) (index : Fin rest.length),
      SubclauseProjection now.state (rest[index.val] :: context) budget :=
      fun now nowBank index => by
        simpa only [Fin.val_succ, List.getElem_cons_succ] using reason now nowBank index.succ
    have tailReasonSupported : ∀ now nowBank index,
        PrefixOriginalSupport rename now →
        ClosedFlagsOriginalSupport rename now position outputs nowBank →
        ProjectionOriginalSupport rename now (tailReason now nowBank index) := by
      intro now nowBank index nowSupported nowBankSupported
      simpa only [tailReason, Fin.val_succ, List.getElem_cons_succ] using
        reasonSupported now nowBank index.succ nowSupported nowBankSupported
    have tailSupport := ih (prefixState := current) (bank := currentBank)
      (parent := remaining) (reason := tailReason) joinedSupport.1
      currentBankSupported joinedSupport.2 tailReasonSupported
    let tail := eliminateBankLeaves rename current position outputs currentBank
      context output rest budget remaining tailReason
    have stepsEqual :
        (eliminateBankLeaves rename prefixState position outputs bank context output
          (input :: rest) budget parent reason).steps =
        direction.steps ++ (joined.steps ++ tail.steps) := by
      rw [eliminateBankLeaves.eq_def]
      rfl
    have idEqual :
        (eliminateBankLeaves rename prefixState position outputs bank context output
          (input :: rest) budget parent reason).result.row.id = tail.result.row.id := by
      rw [eliminateBankLeaves.eq_def]
      rfl
    unfold ProjectionOriginalSupport at tailSupport ⊢
    rw [stepsEqual, idEqual]
    simpa only [current, directed, SourcePrefix.extend, List.append_assoc, tail] using tailSupport

theorem projection_cast_supported (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    {before after : Clause (Fin v)} {budget : Nat}
    (equal : before = after)
    (typeEqual : SubclauseProjection prefixState.state before budget =
      SubclauseProjection prefixState.state after budget)
    (value : SubclauseProjection prefixState.state before budget)
    (supported : ProjectionOriginalSupport rename prefixState value) :
    ProjectionOriginalSupport rename prefixState (Eq.mp typeEqual value) := by
  unfold ProjectionOriginalSupport at supported ⊢
  rw [projection_cast_steps equal typeEqual value, projection_cast_id equal typeEqual value]
  exact supported


theorem nonunaryAggregateRow_origin
    (originalCount : Nat) (allowed : Nat → Prop) (steps : List (Step v))
    {state : State v} {output : Literal (Fin v)} {inputs : List (Literal (Fin v))}
    (certificate : AggregateCertificate state output inputs) (size : 2 ≤ inputs.length)
    (origin : Controller.NativeProof.SourceFoldAggregateProvenance.AggregateOrigin
      originalCount allowed steps certificate) :
    Controller.NativeProof.SourceMismatchHandles.ResultOrigin originalCount allowed steps
      (nonunaryAggregateRow certificate size).row.id := by
  cases certificate with
  | identity => simp at size
  | derived row => exact origin


theorem qualifierLeafReason_supported (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (channel : Fin parameters.channels) (outputs : Clause (Fin v))
    (bank : ClosedFlags rename prefixState position outputs)
    (index : Fin (1 + parameters.buses))
    (supported : PrefixOriginalSupport rename prefixState)
    (bankSupported : ClosedFlagsOriginalSupport rename prefixState position outputs bank) :
    ProjectionOriginalSupport rename prefixState
      (qualifierLeafReason rename prefixState position channel outputs bank index) := by
  unfold qualifierLeafReason
  split
  · have actual := termEnableAt_supported rename prefixState .faulty position channel supported
    simpa only [ProjectionOriginalSupport, retarget] using actual
  · rename_i nonzero
    dsimp only
    split
    · have actual := earlierGuardAt_supported rename prefixState position channel
        ⟨index.val - 1, by omega⟩ ‹_› supported
      simpa only [ProjectionOriginalSupport, retarget] using actual
    · rename_i after
      let bus : Fin parameters.buses := ⟨index.val - 1, by omega⟩
      have busNonzero : bus.val ≠ 0 := by
        have strict : (laterBuses (parameters := parameters))[position.val] < bus :=
          lt_of_not_ge after
        intro zero
        change (laterBuses (parameters := parameters))[position.val].val < bus.val at strict
        omega
      let later := laterPosition bus busNonzero
      have selected := laterPosition_bus bus busNonzero
      have order : position.val < later.val := by
        by_contra reversed
        have bounded : later.val ≤ position.val := Nat.le_of_not_gt reversed
        have sorted : (laterBuses (parameters := parameters)).Pairwise (· < ·) :=
          (List.pairwise_lt_finRange parameters.buses).filter _
        have before : bus ≤ (laterBuses (parameters := parameters))[position.val] := by
          rcases Nat.lt_or_eq_of_le bounded with strict | equal
          · have ordered := sorted.rel_get_of_lt strict
            simp only [List.get_eq_getElem] at ordered
            rw [selected] at ordered
            exact le_of_lt ordered
          · have same : later = position := Fin.ext equal
            have selectedGet : (laterBuses (parameters := parameters)).get later = bus := by
              simpa only [List.get_eq_getElem] using selected
            have indexEqual := congrArg
              (fun query : Fin (laterBuses (parameters := parameters)).length =>
                (laterBuses (parameters := parameters)).get query) same
            have atPosition : bus = (laterBuses (parameters := parameters)).get position :=
              selectedGet.symm.trans indexEqual
            exact le_of_eq (by simpa only [List.get_eq_getElem] using atPosition)
        exact after before
      have actual := futureGuardAt_supported rename prefixState position later channel outputs bank order
        supported bankSupported
      simpa only [ProjectionOriginalSupport, retarget, data_getter_transport,
        getter_transport, apply_dite, dite_apply] using actual


theorem qualifierTermAt_supported (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (channel : Fin parameters.channels)
    (bank : ClosedFlags rename prefixState position (qualifierOutputs (parameters := parameters) rename))
    (supported : PrefixOriginalSupport rename prefixState)
    (bankSupported : ClosedFlagsOriginalSupport rename prefixState position
      (qualifierOutputs (parameters := parameters) rename) bank) :
    ProjectionOriginalSupport rename prefixState
      (qualifierTermAt rename prefixState position channel bank) := by
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
    negate (laterTermOutput rename .faulty position channel) ::
      qualifierOutputs (parameters := parameters) rename
  let current := prefixState.extend projected.state projected.steps projected.checked
  let currentBank := bank.afterTrace projected.state projected.steps projected.checked
  let parent : AvailableSubclause current.state (context ++ output :: inputs.map negate) :=
    retarget actual (fun _ member => List.mem_append_right _ member)
  have aggregateSupported := qualifierAggregate_supported rename prefixState .faulty channel supported
  have parentOrigin := nonunaryAggregateRow_origin (formula parameters).clauses.size
    (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
    (prefixState.steps ++ projected.steps) projected.result size aggregateSupported.2
  have currentBankSupported : ClosedFlagsOriginalSupport rename current position
      (qualifierOutputs (parameters := parameters) rename) currentBank := by
    intro later order
    exact resultOrigin_append_right (formula parameters).clauses.size
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      prefixState.steps projected.steps (bank later order).row.id (bankSupported later order)
  let reason : ∀ (now : SourcePrefix (parameters := parameters) rename)
    (nowBank : ClosedFlags rename now position (qualifierOutputs (parameters := parameters) rename))
    (index : Fin inputs.length), SubclauseProjection now.state
      (inputs[index.val] :: context) (4 * parameters.buses + 10) :=
    fun now nowBank index => by
      let originalIndex : Fin (1 + parameters.buses) := ⟨index.val, by
        simpa only [inputs, rawInputs, List.length_map, List.length_cons,
          List.length_finRange, Nat.add_comm] using index.isLt⟩
      simpa only [inputs, rawInputs, context, List.map_cons, List.map_map,
        Function.comp_def, originalIndex] using
        qualifierLeafReason rename now position channel
          (qualifierOutputs (parameters := parameters) rename) nowBank originalIndex
  have reasonSupported : ∀ now nowBank index,
      PrefixOriginalSupport rename now →
      ClosedFlagsOriginalSupport rename now position
        (qualifierOutputs (parameters := parameters) rename) nowBank →
      ProjectionOriginalSupport rename now (reason now nowBank index) := by
    intro now nowBank index nowSupported nowBankSupported
    let originalIndex : Fin (1 + parameters.buses) := ⟨index.val, by
      simpa only [inputs, rawInputs, List.length_map, List.length_cons,
        List.length_finRange, Nat.add_comm] using index.isLt⟩
    have actualSupport := qualifierLeafReason_supported rename now position channel
      (qualifierOutputs (parameters := parameters) rename) nowBank originalIndex
      nowSupported nowBankSupported
    -- The actual callback's literal cast is transported without changing its trace or ID.
    dsimp only [reason]
    exact projection_cast_supported rename now
      (by simp only [inputs, rawInputs, context, List.map_cons, List.map_map,
        Function.comp_def, originalIndex]) _ _ actualSupport
  have consumedSupport := eliminateBankLeaves_supported rename current position
    (qualifierOutputs (parameters := parameters) rename) currentBank context output inputs
    (4 * parameters.buses + 10) parent reason aggregateSupported.1 currentBankSupported
    parentOrigin reasonSupported
  simpa only [ProjectionOriginalSupport, qualifierTermAt, SourcePrefix.extend,
    List.append_assoc, retarget, rawInputs, inputs, output, tree, projected,
    actual, context, current, currentBank, parent, reason] using consumedSupport


theorem consumeAggregateBank_supported (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (outputs context : Clause (Fin v))
    (bank : ClosedFlags rename prefixState position outputs)
    (output : Literal (Fin v)) (inputs : List (Literal (Fin v)))
    (aggregateBudget reasonBudget : Nat)
    (projection : AggregateProjection prefixState.state output inputs aggregateBudget)
    (reason : ∀ (current : SourcePrefix (parameters := parameters) rename)
      (currentBank : ClosedFlags rename current position outputs) (index : Fin inputs.length),
      SubclauseProjection current.state (inputs[index.val] :: context) reasonBudget)
    (supported : PrefixOriginalSupport rename prefixState)
    (bankSupported : ClosedFlagsOriginalSupport rename prefixState position outputs bank)
    (aggregateSupport : Controller.NativeProof.SourceBusSchedule.TraceOriginalSupport
      (formula parameters).clauses.size
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      (prefixState.steps ++ projection.steps))
    (aggregateOrigin : Controller.NativeProof.SourceFoldAggregateProvenance.AggregateOrigin
      (formula parameters).clauses.size
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      (prefixState.steps ++ projection.steps) projection.result)
    (reasonSupported : ∀ current currentBank index,
      PrefixOriginalSupport rename current →
      ClosedFlagsOriginalSupport rename current position outputs currentBank →
      ProjectionOriginalSupport rename current (reason current currentBank index)) :
    ProjectionOriginalSupport rename prefixState
      (consumeAggregateBank rename prefixState position outputs context bank output inputs
        aggregateBudget reasonBudget projection reason) := by
  rcases projection with ⟨next, steps, checked, certificate, count⟩
  let current := prefixState.extend next steps checked
  let carried := bank.afterTrace next steps checked
  have carriedSupport : ClosedFlagsOriginalSupport rename current position outputs carried := by
    intro later order
    exact resultOrigin_append_right (formula parameters).clauses.size
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      prefixState.steps steps (bank later order).row.id (bankSupported later order)
  cases certificate with
  | identity =>
    let directed := reason current carried ⟨0, by simp⟩
    have actual := reasonSupported current carried ⟨0, by simp⟩ aggregateSupport carriedSupport
    have stepsEqual :
        (consumeAggregateBank rename prefixState position outputs context bank output [output]
          aggregateBudget reasonBudget ⟨next, steps, checked, .identity, count⟩ reason).steps =
        steps ++ directed.steps := by
      rfl
    have idEqual :
        (consumeAggregateBank rename prefixState position outputs context bank output [output]
          aggregateBudget reasonBudget ⟨next, steps, checked, .identity, count⟩ reason).result.row.id =
        directed.result.row.id := by
      rfl
    unfold ProjectionOriginalSupport at actual ⊢
    rw [stepsEqual, idEqual]
    simpa only [current, SourcePrefix.extend, List.append_assoc, directed] using actual
  | derived row =>
    let parent : AvailableSubclause current.state (context ++ output :: inputs.map negate) :=
      retarget row (fun _ member => List.mem_append_right _ member)
    let consumed := eliminateBankLeaves rename current position outputs carried context
      output inputs reasonBudget parent reason
    have actual := eliminateBankLeaves_supported rename current position outputs carried context
      output inputs reasonBudget parent reason aggregateSupport carriedSupport aggregateOrigin reasonSupported
    have stepsEqual :
        (consumeAggregateBank rename prefixState position outputs context bank output inputs
          aggregateBudget reasonBudget ⟨next, steps, checked, .derived row, count⟩ reason).steps =
        steps ++ consumed.steps := by
      rfl
    have idEqual :
        (consumeAggregateBank rename prefixState position outputs context bank output inputs
          aggregateBudget reasonBudget ⟨next, steps, checked, .derived row, count⟩ reason).result.row.id =
        consumed.result.row.id := by
      rfl
    unfold ProjectionOriginalSupport at actual ⊢
    rw [stepsEqual, idEqual]
    simpa only [current, SourcePrefix.extend, List.append_assoc, consumed] using actual


theorem closeFlagAt_supported (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (bank : ClosedFlags rename prefixState position (qualifierOutputs (parameters := parameters) rename))
    (supported : PrefixOriginalSupport rename prefixState)
    (bankSupported : ClosedFlagsOriginalSupport rename prefixState position
      (qualifierOutputs (parameters := parameters) rename) bank) :
    ProjectionOriginalSupport rename prefixState (closeFlagAt rename prefixState position bank) := by
  let inputs := (List.finRange parameters.channels).map
    (fun channel => negate (laterTermOutput rename .faulty position channel))
  let output := negate (laterFlagOutput rename .faulty position)
  let context := mixedContext (parameters := parameters) rename ++
    qualifierOutputs (parameters := parameters) rename
  let tree : AndTree prefixState.state output inputs := by
    have actual := (laterFlagTree rename .faulty position).afterTrace
      prefixState.state prefixState.steps prefixState.checked
    have reflected := congrArg (List.map negate) (laterFlagInputs_eq_terms rename .faulty position)
    simp only [List.map_map, Function.comp_def] at reflected
    change AndTree prefixState.state (negate (laterFlagOutput rename .faulty position))
      ((List.finRange parameters.channels).map
        (fun channel => negate (laterTermOutput rename .faulty position channel)))
    rw [← reflected]
    exact actual
  have treeOriginal : TreeOriginals
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename) tree := by
    have original := treeOriginals_afterTrace
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      (laterFlagTree rename .faulty position) (laterFlagTree_originals rename .faulty position)
      prefixState.state prefixState.steps prefixState.checked
    have reflected := congrArg (List.map negate) (laterFlagInputs_eq_terms rename .faulty position)
    have dualFunction : dualLiteral rename = (fun literal => negate (mapLiteral rename literal)) := rfl
    have inputEqual : inputs = (laterFlagInputs .faulty position).map (dualLiteral rename) := by
      simpa only [inputs, dualFunction, List.map_map, Function.comp_def] using reflected.symm
    dsimp only [tree, id_eq]
    apply (treeOriginals_mpr_indices
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      (show output = negate (laterFlagOutput rename .faulty position) from rfl)
      inputEqual _ _).mpr
    exact original
  let aggregate := projectTreeLong tree
  have aggregateSupported := Controller.NativeProof.SourceFoldAggregateProvenance.projectTreeLong_supported
    prefixState.state tree (formula parameters).clauses.size
    (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
    prefixState.steps treeOriginal supported (allowed_native_count_le rename)
    (prefix_native_count_le rename prefixState)
  let reason : ∀ (current : SourcePrefix (parameters := parameters) rename)
      (currentBank : ClosedFlags rename current position (qualifierOutputs (parameters := parameters) rename))
      (index : Fin inputs.length),
      SubclauseProjection current.state (inputs[index.val] :: context) (qualifierBudget parameters) :=
    fun current currentBank index => by
      let channel : Fin parameters.channels := ⟨index.val, by
        simpa only [inputs, List.length_map, List.length_finRange] using index.isLt⟩
      let one := qualifierTermAt rename current position channel currentBank
      have bound := qualifierTree_nodes_le rename channel
      refine ⟨one.state, one.steps, one.checked, retarget one.result ?_,
        one.count.trans (by dsimp only [qualifierBudget]; omega)⟩
      intro literal member
      simp only [inputs, List.getElem_map, List.getElem_finRange, channel]
      simp only [context, List.mem_append, List.mem_cons] at member ⊢
      aesop
  have reasonSupported : ∀ current currentBank index,
      PrefixOriginalSupport rename current →
      ClosedFlagsOriginalSupport rename current position
        (qualifierOutputs (parameters := parameters) rename) currentBank →
      ProjectionOriginalSupport rename current (reason current currentBank index) := by
    intro current currentBank index currentSupported currentBankSupported
    let channel : Fin parameters.channels := ⟨index.val, by
      simpa only [inputs, List.length_map, List.length_finRange] using index.isLt⟩
    have actual := qualifierTermAt_supported rename current position channel currentBank
      currentSupported currentBankSupported
    simpa only [ProjectionOriginalSupport, reason, channel, retarget] using actual
  have consumedSupport := consumeAggregateBank_supported rename prefixState position
    (qualifierOutputs (parameters := parameters) rename) context bank output inputs
    (2 * tree.nodes) (qualifierBudget parameters) aggregate reason supported bankSupported
    aggregateSupported.1 aggregateSupported.2 reasonSupported
  simpa only [ProjectionOriginalSupport, closeFlagAt, inputs, output, context, tree,
    aggregate, reason, retarget] using consumedSupport


def FlagClosureOriginalSupport (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename) (remaining : Nat)
    (closed : FlagClosure rename prefixState remaining) : Prop :=
  Controller.NativeProof.SourceBusSchedule.TraceOriginalSupport
    (formula parameters).clauses.size
    (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
    (prefixState.steps ++ closed.steps) ∧
  ∀ later, Controller.NativeProof.SourceMismatchHandles.ResultOrigin
    (formula parameters).clauses.size
    (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
    (prefixState.steps ++ closed.steps) (closed.bank later).row.id



end Controller.NativeProof.SourceMixedSchedule
