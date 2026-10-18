module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.SourceQualifierOccurrences
public import Controller.Native.SourceTransport

@[expose] public section

/-! The suffix selector uses the concrete private-NOT and qualifier-guard
occurrences. Cursor frames identify their shared source handles. -/
namespace Controller.NativeProof.SourceSuffixSelector
open Controller.CNF Controller.Native Controller.Native.SourceController
open Controller.Resolution Controller.Resolution.Cases
open Controller.NativeProof.FoldProjection Controller.NativeProof.SourceFoldProjection
open Controller.NativeProof.SourceFoldOccurrences Controller.NativeProof.SourceFoldOwners
open Controller.NativeProof.SourceQualifierOccurrences Controller.NativeProof.SourceSlotFrames
open Controller.NativeProof.SourceStageCongruence Controller.NativeProof.SourceRoleFrames
variable {parameters : Parameters} {v : Nat}

def negatedHandle (side : Side) (bus : Fin parameters.buses) : Literal Nat :=
  ((negateBefore side bus).lastID + 1, true)

theorem negateStep_slots (side : Side) (cursor : Cursor parameters) (bus : Fin parameters.buses)
    (query : Controller.Native.Variable parameters) :
    (negateStep side cursor bus).slots query = cursor.slots query := rfl

theorem negateBefore_slots (side : Side) (bus : Fin parameters.buses)
    (query : Controller.Native.Variable parameters) :
    (negateBefore side bus).slots query = (tailStages side).slots query := by
  apply foldl_slot
  intro cursor index
  rfl

theorem negateStep_same (side : Side) (cursor : Cursor parameters) (bus : Fin parameters.buses) :
    (negateStep side cursor bus).negated side bus = (cursor.lastID + 1, true) := by
  simp [negateStep, Cursor.emit]

theorem negateStep_other (side : Side) (cursor : Cursor parameters)
    (bus query : Fin parameters.buses) (different : query ≠ bus) :
    (negateStep side cursor bus).negated side query = cursor.negated side query := by
  simp [negateStep, Cursor.emit, different]

theorem negateSuffix_preserves (side : Side) (query : Fin parameters.buses)
    (values : List (Fin parameters.buses)) (absent : query ∉ values) (cursor : Cursor parameters) :
    (values.foldl (negateStep side) cursor).negated side query = cursor.negated side query := by
  induction values generalizing cursor with
  | nil => rfl
  | cons bus rest ih =>
      have different : query ≠ bus := by intro equal; apply absent; simp [equal]
      have absentRest : query ∉ rest := fun member => absent (List.mem_cons_of_mem bus member)
      exact (ih absentRest _).trans (negateStep_other side cursor bus query different)

theorem negateFlags_handle (side : Side) (bus : Fin parameters.buses) :
    (negateFlags parameters side (tailStages side)).negated side bus = negatedHandle side bus := by
  have bound : bus.val < (List.finRange parameters.buses).length := by simpa using bus.isLt
  have decomposition : List.finRange parameters.buses =
      (List.finRange parameters.buses).take bus.val ++ bus ::
        (List.finRange parameters.buses).drop (bus.val + 1) := by
    simpa using positional_decomposition (List.finRange parameters.buses) ⟨bus.val, bound⟩
  have distinct : bus ∉ (List.finRange parameters.buses).drop (bus.val + 1) := by
    have nodup := List.nodup_finRange parameters.buses
    rw [decomposition] at nodup
    exact (List.nodup_cons.mp (List.nodup_append.mp nodup).2.1).1
  rw [← negate_traversal, decomposition, List.foldl_append]
  simp only [List.foldl_cons]
  rw [negateSuffix_preserves side bus _ distinct, negateStep_same]
  rfl

theorem eligiblePrefix_negated (side : Side) (bus : Fin parameters.buses)
    (values : List (Fin parameters.channels)) (cursor : Cursor parameters) :
    (values.foldl (fun cursor channel => eligible parameters side channel cursor) cursor).negated side bus =
      cursor.negated side bus := by
  induction values generalizing cursor with
  | nil => rfl
  | cons channel rest ih =>
      exact (ih _).trans (congrArg (fun table => table side bus) (eligible_negated parameters side channel cursor))

theorem eligibleBefore_negated (side : Side) (channel : Fin parameters.channels)
    (bus : Fin parameters.buses) :
    (eligibleBefore side channel).negated side bus = negatedHandle side bus := by
  change (((List.finRange parameters.channels).take channel.val).foldl
    (fun cursor index => eligible parameters side index cursor)
    (negateFlags parameters side (tailStages side))).negated side bus = _
  rw [eligiblePrefix_negated, negateFlags_handle]

theorem guardPrefix_negated (side : Side) (channel : Fin parameters.channels)
    (bus : Fin parameters.buses) (values : List (Fin parameters.buses)) (cursor : Cursor parameters) :
    (values.foldl (eligibleGuardStep parameters side channel) cursor).negated side bus = cursor.negated side bus := by
  induction values generalizing cursor with
  | nil => rfl
  | cons index rest ih => exact ih _

theorem guardBefore_negated (side : Side) (channel : Fin parameters.channels)
    (bus : Fin parameters.buses) :
    (guardBefore side channel bus).negated side bus = negatedHandle side bus := by
  unfold guardBefore occurrenceCursor
  rw [guardPrefix_negated, eligibleBefore_negated]

def guardHandle (side : Side) (channel : Fin parameters.channels) (bus : Fin parameters.buses) : Literal Nat :=
  ((guardBefore side channel bus).lastID + 1, true)

def flagInput (side : Side) (bus : Fin parameters.buses) : Literal Nat :=
  (negateBefore side bus).slots (.internal (.flag side bus))

/-- The guard's negative-NOT input row is an original OR occurrence. -/
def guardNegatedRow (rename : Nat → Fin v) (side : Side) (channel : Fin parameters.channels)
    (bus : Fin parameters.buses) :
    AvailableSubclause (initialState (relabel rename (formula parameters)))
      [negate (mapLiteral rename (negatedHandle side bus)), mapLiteral rename (guardHandle side channel bus)] := by
  let original := ofRow ((guardRows rename side channel bus).row ⟨0, by change 0 < 3; decide⟩)
  have row : AvailableSubclause (initialState (relabel rename (formula parameters)))
      [mapLiteral rename (guardHandle side channel bus), negate (mapLiteral rename (negatedHandle side bus))] := by
    simpa only [Bounded.Producer.rows, Gate.clauses, List.cons_append, List.nil_append, List.getElem_cons_succ, Rows.mapClause, List.map_cons, List.map_nil,
      List.getElem_cons_zero, guardHandle, guardBefore_negated, mapLiteral, negate, Std.Sat.Literal.negate] using original
  exact retarget row (by
    intro literal member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢
    exact member.elim Or.inr Or.inl)

/-- The private NOT has the actual flag input and the shared negated output. -/
def privateFlagRow (rename : Nat → Fin v) (side : Side) (bus : Fin parameters.buses) :
    AvailableSubclause (initialState (relabel rename (formula parameters)))
      [mapLiteral rename (negatedHandle side bus), mapLiteral rename (flagInput side bus)] := by
  let original := ofRow ((negatedFlagRows rename side bus).row ⟨0, by change 0 < 2; decide⟩)
  simpa only [Bounded.Producer.rows, Gate.clauses, List.cons_append, List.nil_append, List.getElem_cons_succ, Rows.mapClause, List.map_cons, List.map_nil,
    List.getElem_cons_zero, negatedHandle, flagInput, mapLiteral] using original

/-- One checked source resolution derives `guard OR flag` at the current
accepted prefix. No available row or owner map is supplied by the caller. -/
def guardOrFlagAt (rename : Nat → Fin v)
    (prefixState : Controller.NativeProof.SourceStageCongruence.SourcePrefix (parameters := parameters) rename)
    (side : Side) (channel : Fin parameters.channels) (bus : Fin parameters.buses) :
    SubclauseProjection prefixState.state
      [mapLiteral rename (guardHandle side channel bus), mapLiteral rename (flagInput side bus)] 1 := by
  let q := mapLiteral rename (negatedHandle side bus)
  let g := mapLiteral rename (guardHandle side channel bus)
  let p := mapLiteral rename (flagInput side bus)
  let left := FoldProjection.afterTrace (guardNegatedRow rename side channel bus)
    prefixState.state prefixState.steps prefixState.checked
  let right := FoldProjection.afterTrace (privateFlagRow rename side bus)
    prefixState.state prefixState.steps prefixState.checked
  let joined := longMerge prefixState.state q [g] [p] left right
  refine ⟨joined.state, joined.steps, longMerge_run _ _ _ _ _ _,
    retarget (longMerge_result _ _ _ _ _ _) ?_, longMerge_count _ _ _ _ _ _⟩
  intro literal member
  simpa only [List.cons_append, List.nil_append] using member

theorem tailStart_roots (side : Side) : (tailStart (parameters := parameters) side).RootsExact := by
  cases side with
  | healthy => exact interface_rootsExact parameters
  | faulty => exact tail_rootsExact parameters .healthy _ (interface_rootsExact parameters)

theorem tailStages_roots (side : Side) : (tailStages (parameters := parameters) side).RootsExact :=
  rootsExact_foldl _ _ (fun cursor bus roots => laterBus_rootsExact parameters side bus cursor roots) _
    (initialMasks_rootsExact parameters side _ (tailStart_roots side))

theorem eligibleBefore_roots (side : Side) (channel : Fin parameters.channels) :
    (eligibleBefore side channel).RootsExact :=
  rootsExact_foldl _ _ (fun cursor index roots => eligible_rootsExact parameters side index cursor roots) _
    (negateFlags_rootsExact parameters side _ (tailStages_roots side))

theorem guardBefore_roots (side : Side) (channel : Fin parameters.channels) (bus : Fin parameters.buses) :
    (guardBefore side channel bus).RootsExact :=
  rootsExact_foldl _ _ (fun cursor index roots => cursor.rootsExact_emitNative_internal _ _ roots) _
    (eligibleBefore_roots side channel)

theorem busBefore_roots (side : Side) (position : Fin (laterBuses (parameters := parameters)).length) :
    (busBefore side position).RootsExact :=
  rootsExact_foldl _ _ (fun cursor bus roots => laterBus_rootsExact parameters side bus cursor roots) _
    (initialMasks_rootsExact parameters side _ (tailStart_roots side))

theorem termBefore_roots (side : Side) (position : Fin (laterBuses (parameters := parameters)).length)
    (channel : Fin parameters.channels) : (termBefore side position channel).RootsExact :=
  rootsExact_foldl _ _ (fun cursor index roots => cursor.rootsExact_foldNative_internal _ _ _ roots) _
    (busBefore_roots side position)

/-- A distinct represented bus cannot overwrite an earlier flag handle. -/
theorem laterBus_flag_frame (side : Side) (bus query : Fin parameters.buses)
    (different : query ≠ bus) (cursor : Cursor parameters) :
    (laterBus parameters side bus cursor).slots (.internal (.flag side query)) =
      cursor.slots (.internal (.flag side query)) := by
  unfold laterBus
  rw [foldl_slot _ (.internal (.flag side query)) (fun current index => by
    simp [Cursor.emitNative, Cursor.emit, Cursor.assign])]
  rw [foldNative_other _ _ _ _ _ (by simp [different])]
  apply foldl_slot
  intro current index
  apply foldNative_other
  simp

/-- The same concrete cursor frame applies to each earlier channel mask. -/
theorem laterBus_mask_frame (side : Side) (bus query : Fin parameters.buses)
    (channel : Fin parameters.channels) (different : query ≠ bus) (cursor : Cursor parameters) :
    (laterBus parameters side bus cursor).slots (.internal (.mask side query channel)) =
      cursor.slots (.internal (.mask side query channel)) := by
  unfold laterBus
  rw [foldl_slot _ (.internal (.mask side query channel)) (fun current index => by
    simp [Cursor.emitNative, Cursor.emit, Cursor.assign, different, Ne.symm different])]
  rw [foldNative_other _ _ _ _ _ (by simp)]
  apply foldl_slot
  intro current index
  apply foldNative_other
  simp

theorem laterBus_term_frame (side : Side) (bus query : Fin parameters.buses)
    (channel : Fin parameters.channels) (different : query ≠ bus) (cursor : Cursor parameters) :
    (laterBus parameters side bus cursor).slots (.internal (.term side query channel)) =
      cursor.slots (.internal (.term side query channel)) := by
  unfold laterBus
  rw [foldl_slot _ (.internal (.term side query channel)) (fun current index => by
    simp [Cursor.emitNative, Cursor.emit, Cursor.assign])]
  rw [foldNative_other _ _ _ _ _ (by simp)]
  apply foldl_slot
  intro current index
  apply foldNative_other
  simp [different, Ne.symm different]

theorem laterBus_absent_frame (side : Side) (bus query : Fin parameters.buses)
    (channel : Fin parameters.channels) (different : query ≠ bus) (cursor : Cursor parameters) :
    (laterBus parameters side bus cursor).slots (.internal (.absent side query channel)) =
      cursor.slots (.internal (.absent side query channel)) := by
  unfold laterBus
  rw [foldl_slot _ (.internal (.absent side query channel)) (fun current index => by
    simp [Cursor.emitNative, Cursor.emit, Cursor.assign, different, Ne.symm different])]
  rw [foldNative_other _ _ _ _ _ (by simp)]
  apply foldl_slot
  intro current index
  apply foldNative_other
  simp

def busFlagHandle (side : Side) (position : Fin (laterBuses (parameters := parameters)).length) : Literal Nat :=
  (SourceSerialFold.allocate .disjunction
    (busTerms side (laterBuses (parameters := parameters))[position.val] (busBefore side position)).lastID
    (laterFlagInputs side position)).output

theorem laterBus_flag_output (side : Side) (position : Fin (laterBuses (parameters := parameters)).length) :
    (laterBus parameters side (laterBuses (parameters := parameters))[position.val] (busBefore side position)).slots
      (.internal (.flag side (laterBuses (parameters := parameters))[position.val])) = busFlagHandle side position := by
  unfold laterBus
  rw [foldl_slot _ (.internal (.flag side (laterBuses (parameters := parameters))[position.val]))
    (fun cursor channel => by simp [Cursor.emitNative, Cursor.emit, Cursor.assign])]
  simp only [Cursor.foldNative, Cursor.assign, Function.update_self]
  rfl

theorem tailStages_flag (side : Side) (position : Fin (laterBuses (parameters := parameters)).length) :
    (tailStages (parameters := parameters) side).slots
      (.internal (.flag side (laterBuses (parameters := parameters))[position.val])) = busFlagHandle side position := by
  let values := laterBuses (parameters := parameters)
  let bus := values[position.val]
  have decomposition := positional_decomposition values position
  have distinct : bus ∉ values.drop (position.val + 1) := by
    have nodup : values.Nodup := List.Nodup.filter _ (List.nodup_finRange parameters.buses)
    rw [decomposition] at nodup
    exact (List.nodup_cons.mp (List.nodup_append.mp nodup).2.1).1
  change (values.foldl (fun cursor bus => laterBus parameters side bus cursor)
    (initialMasks parameters side (tailStart side))).slots (.internal (.flag side bus)) = _
  rw [decomposition, List.foldl_append]
  simp only [List.foldl_cons]
  rw [foldl_slot_mem _ (.internal (.flag side bus)) _ (by
    intro cursor query member
    apply laterBus_flag_frame
    intro equal
    exact distinct (equal.symm ▸ member))]
  exact laterBus_flag_output side position

theorem flagInput_busFlag (side : Side) (position : Fin (laterBuses (parameters := parameters)).length) :
    flagInput side (laterBuses (parameters := parameters))[position.val] = busFlagHandle side position := by
  unfold flagInput
  rw [negateBefore_slots, tailStages_flag]

def requestHandle (bus : Fin parameters.buses) (channel : Fin parameters.channels) : Literal Nat :=
  (SourceInitialIDs.rootID (.request bus channel), true)

def guardRequestRow (rename : Nat → Fin v) (side : Side) (channel : Fin parameters.channels)
    (bus : Fin parameters.buses) :
    AvailableSubclause (initialState (relabel rename (formula parameters)))
      [negate (mapLiteral rename (requestHandle bus channel)), mapLiteral rename (guardHandle side channel bus)] := by
  let original := ofRow ((guardRows rename side channel bus).row ⟨1, by change 1 < 3; decide⟩)
  have row : AvailableSubclause (initialState (relabel rename (formula parameters)))
      [mapLiteral rename (guardHandle side channel bus), negate (mapLiteral rename (requestHandle bus channel))] := by
    simpa only [Bounded.Producer.rows, Gate.clauses, List.cons_append, List.nil_append, List.getElem_cons_succ, Rows.mapClause, List.map_cons, List.map_nil,
      List.getElem_cons_succ, List.getElem_cons_zero, guardHandle, (guardBefore_roots side channel bus).2 bus channel,
      requestHandle, mapLiteral, negate, Std.Sat.Literal.negate] using original
  exact retarget row (by
    intro literal member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢
    exact member.elim Or.inr Or.inl)

/-- The same-bus A clause is a concrete term-tree request implication followed
by its original guard row. All fresh IDs use the supplied accepted prefix. -/
def sameBusTermGuardAt (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename) (side : Side)
    (position : Fin (laterBuses (parameters := parameters)).length) (channel : Fin parameters.channels) :
    SubclauseProjection prefixState.state
      [negate (laterTermOutput rename side position channel),
       mapLiteral rename (guardHandle side channel (laterBuses (parameters := parameters))[position.val])]
      (2 * (laterTermTree rename side position channel).nodes + 1) := by
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
  let direction := projected.results request member
  let original := guardRequestRow rename side channel bus
  let kept := FoldProjection.afterTrace original prefixState.state prefixState.steps prefixState.checked
  let guardRow := FoldProjection.afterTrace kept projected.state projected.steps projected.checked
  let left : AvailableSubclause projected.state [negate request, guard] := guardRow
  let right : AvailableSubclause projected.state [request, negate root] := retarget direction (by
    intro literal found
    simp only [List.mem_cons, List.not_mem_nil, or_false] at found ⊢
    exact found.elim Or.inr Or.inl)
  let joined := longMerge projected.state request [guard] [negate root] left right
  refine ⟨joined.state, projected.steps ++ joined.steps, ?_, ?_, ?_⟩
  · rw [runSteps_append, projected.checked]
    exact longMerge_run _ _ _ _ _ _
  · apply retarget (longMerge_result _ _ _ _ _ _)
    intro literal found
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at found ⊢
    exact found.elim Or.inr Or.inl
  · have one := projected.count
    have two := longMerge_count projected.state request [guard] [negate root] left right
    change joined.steps.length ≤ 1 at two
    have unchanged := AndTree.afterTrace_nodes (laterTermTree rename side position channel)
      prefixState.state prefixState.steps prefixState.checked
    change tree.nodes = (laterTermTree rename side position channel).nodes at unchanged
    simp only [List.length_append]
    omega

end Controller.NativeProof.SourceSuffixSelector
