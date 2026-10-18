module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.SourceMismatchHandles

@[expose] public section

/-! First-array seed clauses use concrete original AND/NOT occurrences and
physical input units. -/
namespace Controller.NativeProof.SourceMismatchSeed
open Controller.Native Controller.Native.SourceController Controller.CNF
open Controller.Resolution Controller.Resolution.Cases
open Controller.NativeProof.SourceFoldOwners Controller.NativeProof.SourceFoldOccurrences
open Controller.NativeProof.SourceCongruence Controller.NativeProof.SourceSlotFrames
open Controller.NativeProof.SourceRoleFrames Controller.NativeProof.SourceMismatchBranch
open Controller.NativeProof.SourceMismatchHandles
open Controller.NativeProof.SourceFoldProjection Controller.NativeProof.FoldProjection
variable {parameters : Parameters} {v : Nat}

def termBefore (channel : Fin parameters.channels) : Cursor parameters :=
  occurrenceCursor (firstTermStep parameters) (initial parameters)
    ((List.finRange parameters.channels).take channel.val)

def absentBefore (channel : Fin parameters.channels) : Cursor parameters :=
  occurrenceCursor (firstAbsentStep parameters) (firstTerms parameters)
    ((List.finRange parameters.channels).take channel.val)

theorem termStep_before (cursor : Cursor parameters) (channel : Fin parameters.channels) :
    EntriesBefore cursor (firstTermStep parameters cursor channel) :=
  (emitNative_before _ _ _).trans (assign_before _ _ _)

theorem absentStep_before (cursor : Cursor parameters) (channel : Fin parameters.channels) :
    EntriesBefore cursor (firstAbsentStep parameters cursor channel) :=
  (emitNative_before _ _ _).trans (assign_before _ _ _)

theorem firstArrays_before_controller : EntriesBefore (firstArrays parameters) (controller parameters) :=
  (foldNative_before _ _ _ _).trans ((foldNative_before _ _ _ _).trans
    (remaining_before_interface.trans interface_before_controller))

theorem firstTerms_before_controller : EntriesBefore (firstTerms parameters) (controller parameters) := by
  have beforeSteps := foldl_before (firstAbsentStep parameters) absentStep_before
    (List.finRange parameters.channels) (firstTerms parameters)
  exact beforeSteps.trans firstArrays_before_controller

theorem channel_decomposition (channel : Fin parameters.channels) :
    List.finRange parameters.channels = (List.finRange parameters.channels).take channel.val ++
      channel :: (List.finRange parameters.channels).drop (channel.val + 1) := by
  have bound : channel.val < (List.finRange parameters.channels).length := by simpa using channel.isLt
  simpa using positional_decomposition (List.finRange parameters.channels) ⟨channel.val, bound⟩

theorem term_occurrence_before_controller (channel : Fin parameters.channels) :
    EntriesBefore (firstTermStep parameters (termBefore (parameters := parameters) channel) channel)
      (controller parameters) :=
  (occurrence_before_of_eq (firstTermStep parameters) termStep_before (initial parameters)
    (List.finRange parameters.channels) _ _ channel (channel_decomposition channel)).trans
    firstTerms_before_controller

theorem absent_occurrence_before_controller (channel : Fin parameters.channels) :
    EntriesBefore (firstAbsentStep parameters (absentBefore (parameters := parameters) channel) channel)
      (controller parameters) :=
  (occurrence_before_of_eq (firstAbsentStep parameters) absentStep_before (firstTerms parameters)
    (List.finRange parameters.channels) _ _ channel (channel_decomposition channel)).trans
    firstArrays_before_controller

theorem term_emit_before_controller (channel : Fin parameters.channels) :
    EntriesBefore ((termBefore (parameters := parameters) channel).emitNative
      (.internal (.term .healthy parameters.firstBus channel))
      (.and [(termBefore (parameters := parameters) channel).slots (.primary (.enable channel)),
        (termBefore (parameters := parameters) channel).slots (.primary (.request parameters.firstBus channel))]))
      (controller parameters) :=
  (assign_before _ _ _).trans (term_occurrence_before_controller channel)

theorem absent_emit_before_controller (channel : Fin parameters.channels) :
    EntriesBefore ((absentBefore (parameters := parameters) channel).emitNative
      (.internal (.absent .healthy parameters.firstBus channel))
      (.not ((absentBefore (parameters := parameters) channel).slots
        (.internal (.term .healthy parameters.firstBus channel))))) (controller parameters) :=
  (assign_before _ _ _).trans (absent_occurrence_before_controller channel)

def termRows (rename : Nat → Fin v) (channel : Fin parameters.channels) :=
  emitRowsExact rename (termBefore (parameters := parameters) channel)
    (.internal (.term .healthy parameters.firstBus channel))
    (.and [(termBefore (parameters := parameters) channel).slots (.primary (.enable channel)),
      (termBefore (parameters := parameters) channel).slots (.primary (.request parameters.firstBus channel))])
    ((term_emit_before_controller channel).trans controller_before_compile)

def absentRows (rename : Nat → Fin v) (channel : Fin parameters.channels) :=
  emitRowsExact rename (absentBefore (parameters := parameters) channel)
    (.internal (.absent .healthy parameters.firstBus channel))
    (.not ((absentBefore (parameters := parameters) channel).slots
      (.internal (.term .healthy parameters.firstBus channel))))
    ((absent_emit_before_controller channel).trans controller_before_compile)

theorem termRows_allowed (rename : Nat → Fin v) (channel : Fin parameters.channels) (index : Fin 3) :
    AllowedOriginal (parameters := parameters) rename
      ((termRows rename channel).row ⟨index.val, by change index.val < 3; exact index.isLt⟩).id := by
  exact emitRow_allowed rename (termBefore (parameters := parameters) channel)
    (.internal (.term .healthy parameters.firstBus channel))
    (.and [(termBefore (parameters := parameters) channel).slots (.primary (.enable channel)),
      (termBefore (parameters := parameters) channel).slots (.primary (.request parameters.firstBus channel))])
    (term_emit_before_controller channel) ⟨index.val, by change index.val < 3; exact index.isLt⟩

theorem absentRows_allowed (rename : Nat → Fin v) (channel : Fin parameters.channels) (index : Fin 2) :
    AllowedOriginal (parameters := parameters) rename
      ((absentRows rename channel).row ⟨index.val, by change index.val < 2; exact index.isLt⟩).id := by
  exact emitRow_allowed rename (absentBefore (parameters := parameters) channel)
    (.internal (.absent .healthy parameters.firstBus channel))
    (.not ((absentBefore (parameters := parameters) channel).slots
      (.internal (.term .healthy parameters.firstBus channel))))
    (absent_emit_before_controller channel) ⟨index.val, by change index.val < 2; exact index.isLt⟩


theorem channel_not_suffix (channel : Fin parameters.channels) :
    channel ∉ (List.finRange parameters.channels).drop (channel.val + 1) := by
  have nodup := List.nodup_finRange parameters.channels
  rw [channel_decomposition channel] at nodup
  exact (List.nodup_cons.mp (List.nodup_append'.mp nodup).2.1).1

theorem firstTermStep_other (cursor : Cursor parameters) (side : Side)
    (query channel : Fin parameters.channels) (different : channel ≠ query) :
    (firstTermStep parameters cursor channel).slots (.internal (.term side parameters.firstBus query)) =
      cursor.slots (.internal (.term side parameters.firstBus query)) := by
  cases side <;> simp [firstTermStep, Cursor.emitNative, Cursor.emit, Cursor.assign,
    different, Ne.symm different]

theorem firstTerms_term_handle (side : Side) (channel : Fin parameters.channels) :
    (firstTerms parameters).slots (.internal (.term side parameters.firstBus channel)) =
      ((termBefore (parameters := parameters) channel).lastID + 1, true) := by
  unfold firstTerms
  rw [channel_decomposition channel, List.foldl_append, List.foldl_cons]
  rw [foldl_slot_mem _ (.internal (.term side parameters.firstBus channel)) _ (by
    intro cursor query member
    apply firstTermStep_other
    intro same
    exact channel_not_suffix channel (same ▸ member))]
  cases side <;> simp [firstTermStep, termBefore, occurrenceCursor,
    Cursor.emitNative, Cursor.emit, Cursor.assign]

theorem firstAbsentStep_term (cursor : Cursor parameters) (side : Side)
    (query channel : Fin parameters.channels) :
    (firstAbsentStep parameters cursor channel).slots (.internal (.term side parameters.firstBus query)) =
      cursor.slots (.internal (.term side parameters.firstBus query)) := by
  simp [firstAbsentStep, Cursor.emitNative, Cursor.emit, Cursor.assign]

theorem absentBefore_term_handle (side : Side) (channel : Fin parameters.channels) :
    (absentBefore (parameters := parameters) channel).slots (.internal (.term side parameters.firstBus channel)) =
      ((termBefore (parameters := parameters) channel).lastID + 1, true) := by
  unfold absentBefore occurrenceCursor
  rw [foldl_slot _ _ (fun cursor query => firstAbsentStep_term cursor side channel query)]
  exact firstTerms_term_handle side channel

theorem firstArrays_absent_handle (side : Side) (channel : Fin parameters.channels) :
    (firstArrays parameters).slots (.internal (.absent side parameters.firstBus channel)) =
      ((absentBefore (parameters := parameters) channel).lastID + 1, true) := by
  change ((List.finRange parameters.channels).foldl (firstAbsentStep parameters)
    (firstTerms parameters)).slots (.internal (.absent side parameters.firstBus channel)) = _
  rw [channel_decomposition channel, List.foldl_append, List.foldl_cons]
  rw [foldl_slot_mem (firstAbsentStep parameters) (.internal (.absent side parameters.firstBus channel)) _ (by
    intro cursor query member
    apply firstAbsentStep_other
    intro same
    exact channel_not_suffix channel (same ▸ member))]
  cases side <;> simp [firstAbsentStep, absentBefore, occurrenceCursor,
    Cursor.emitNative, Cursor.emit, Cursor.assign]

theorem termBefore_rootsExact (channel : Fin parameters.channels) :
    (termBefore (parameters := parameters) channel).RootsExact :=
  rootsExact_foldl _ _ (firstTermStep_rootsExact parameters) _ (initial_rootsExact parameters)

theorem termBefore_enable (channel query : Fin parameters.channels) :
    (termBefore (parameters := parameters) channel).slots (.primary (.enable query)) =
      sourceRoleMap parameters (.primary (.enable query)) :=
  ((termBefore_rootsExact channel).1 query).trans ((compile_rootsExact parameters).1 query).symm

theorem termBefore_request (channel query : Fin parameters.channels) (bus : Fin parameters.buses) :
    (termBefore (parameters := parameters) channel).slots (.primary (.request bus query)) =
      sourceRoleMap parameters (.primary (.request bus query)) :=
  ((termBefore_rootsExact channel).2 bus query).trans ((compile_rootsExact parameters).2 bus query).symm

theorem targetUnit_at_occurrence (rename : Nat → Fin v) (drive : parameters.drive = true) :
    mapLiteral rename (physicalUnit (parameters := parameters) ⟨0, by decide⟩) =
      negate (mapLiteral rename ((absentBefore (parameters := parameters) parameters.bridge.target).lastID + 1, true)) := by
  rw [targetPhysicalUnit rename drive, wireCursor_first_absent, firstArrays_absent_handle]

/-- U=0 propagates x_t=1 through the actual first-absence NOT occurrence. -/
def targetTermFromPhysicalUnit (rename : Nat → Fin v) (drive : parameters.drive = true) :
    SubclauseProjection (initialState (relabel rename (formula parameters)))
      [mapLiteral rename ((termBefore (parameters := parameters) parameters.bridge.target).lastID + 1, true)] 1 := by
  let channel := parameters.bridge.target
  let absent := mapLiteral rename ((absentBefore (parameters := parameters) channel).lastID + 1, true)
  let term := mapLiteral rename ((termBefore (parameters := parameters) channel).lastID + 1, true)
  let physical := physicalUnitRow (parameters := parameters) rename ⟨0, by decide⟩
  let unit : Rows.Available (initialState (relabel rename (formula parameters))) [negate absent] :=
    ⟨physical.id, (by simpa only [targetUnit_at_occurrence rename drive] using physical.present), physical.bound⟩
  let reason : AvailableSubclause (initialState (relabel rename (formula parameters))) [absent, term] := by
    have row := ofRow ((absentRows rename channel).row ⟨0, by change 0 < 2; decide⟩)
    simpa only [Bounded.Producer.rows, Gate.clauses, List.getElem_cons_zero,
      Rows.mapClause, List.map_cons, List.map_nil, absentBefore_term_handle, absent, term, mapLiteral] using row
  let joined := longMerge (initialState (relabel rename (formula parameters))) absent [] [term] (ofRow unit) reason
  exact ⟨joined.state, joined.steps, longMerge_run _ _ _ _ _ _,
    longMerge_result _ _ _ _ _ _, longMerge_count _ _ _ _ _ _⟩


def targetInputs : List (Literal Nat) :=
  [(termBefore (parameters := parameters) parameters.bridge.target).slots (.primary (.enable parameters.bridge.target)),
   (termBefore (parameters := parameters) parameters.bridge.target).slots
     (.primary (.request parameters.firstBus parameters.bridge.target))]

/-- The target enable and first request follow the original first-term AND.
The physical-unit NOT propagation and the AND projection cost at most two. -/
def targetInputFromPhysicalUnit (rename : Nat → Fin v) (drive : parameters.drive = true) (index : Fin 2) :
    SubclauseProjection (initialState (relabel rename (formula parameters)))
      [mapLiteral rename ((targetInputs (parameters := parameters))[index.val]'(by
        simpa [targetInputs] using index.isLt))] 2 := by
  let first := targetTermFromPhysicalUnit rename drive
  let term := mapLiteral rename ((termBefore (parameters := parameters) parameters.bridge.target).lastID + 1, true)
  let input := mapLiteral rename ((targetInputs (parameters := parameters))[index.val]'(by
    simpa [targetInputs] using index.isLt))
  have original : AvailableSubclause (initialState (relabel rename (formula parameters))) [negate term, input] := by
    have row := ofRow ((termRows rename parameters.bridge.target).row
      ⟨index.val, by change index.val < 3; omega⟩)
    have bound : index.val < (targetInputs (parameters := parameters)).length := by
      simpa [targetInputs] using index.isLt
    by_cases zero : index.val = 0
    · simpa [Bounded.Producer.rows, Gate.clauses, zero, targetInputs, Rows.mapClause,
        mapLiteral, term, input, negate, Std.Sat.Literal.negate] using row
    · have one : index.val = 1 := by omega
      simpa [Bounded.Producer.rows, Gate.clauses, one, targetInputs, Rows.mapClause,
        mapLiteral, term, input, negate, Std.Sat.Literal.negate] using row
  let left := FoldProjection.afterTrace original first.state first.steps first.checked
  let joined := longMerge first.state term [input] [] left first.result
  refine ⟨joined.state, first.steps ++ joined.steps, ?_, ?_, ?_⟩
  · rw [runSteps_append, first.checked]
    exact longMerge_run _ _ _ _ _ _
  · exact longMerge_result _ _ _ _ _ _
  · have one := first.count
    have two : joined.steps.length ≤ 1 := longMerge_count first.state term [input] [] left first.result
    simp only [List.length_append]
    omega

def targetEnable (rename : Nat → Fin v) (drive : parameters.drive = true) :
    SubclauseProjection (initialState (relabel rename (formula parameters)))
      [mapLiteral rename (sourceRoleMap parameters (.primary (.enable parameters.bridge.target)))] 2 := by
  let actual := targetInputFromPhysicalUnit rename drive ⟨0, by decide⟩
  refine ⟨actual.state, actual.steps, actual.checked, retarget actual.result ?_, actual.count⟩
  intro literal member
  simpa only [targetInputs, List.getElem_cons_zero, termBefore_enable] using member

def targetFirstRequest (rename : Nat → Fin v) (drive : parameters.drive = true) :
    SubclauseProjection (initialState (relabel rename (formula parameters)))
      [mapLiteral rename (sourceRoleMap parameters (.primary (.request parameters.firstBus parameters.bridge.target)))] 2 := by
  let actual := targetInputFromPhysicalUnit rename drive ⟨1, by decide⟩
  refine ⟨actual.state, actual.steps, actual.checked, retarget actual.result ?_, actual.count⟩
  intro literal member
  simpa only [targetInputs, List.getElem_cons_succ, List.getElem_cons_zero, termBefore_request] using member


inductive Group where
  | drivers | remaining
  deriving DecidableEq

def groupInputs (group : Group) : List (Literal Nat) :=
  match group with
  | .drivers => driverInputs parameters
  | .remaining => remainingInputs parameters

def groupLastID (group : Group) : Nat :=
  match group with
  | .drivers => (firstArrays parameters).lastID
  | .remaining => (driverCursor parameters).lastID

def groupOutput (group : Group) : Literal Nat :=
  (SourceSerialFold.allocate .conjunction (groupLastID (parameters := parameters) group)
    (groupInputs (parameters := parameters) group)).output

def groupTree (rename : Nat → Fin v) (group : Group)
    (nonempty : groupInputs (parameters := parameters) group ≠ []) :
    AndTree (initialState (relabel rename (formula parameters)))
      (mapLiteral rename (groupOutput (parameters := parameters) group))
      ((groupInputs (parameters := parameters) group).map (mapLiteral rename)) := by
  cases group with
  | drivers =>
    exact allocateForest (initialForest rename (driverInputs parameters))
      (firstArrays parameters).lastID nonempty (driverRows parameters rename)
  | remaining =>
    exact allocateForest (initialForest rename (remainingInputs parameters))
      (driverCursor parameters).lastID nonempty (remainingRows parameters rename)

def groupIndex (group : Group) : Fin 3 :=
  match group with
  | .drivers => ⟨1, by decide⟩
  | .remaining => ⟨2, by decide⟩

theorem groupOutput_interface (group : Group) :
    (faultyProductInputs (parameters := parameters))[(groupIndex group).val]'(by
      simpa [faultyProductInputs] using (groupIndex group).isLt) =
      groupOutput (parameters := parameters) group := by
  cases group <;> simp [faultyProductInputs, groupIndex, groupOutput, groupLastID, groupInputs,
    healthyFlagCursor, healthyProductCursor, wireCursor, remainingCursor, driverCursor,
    Cursor.emitNative, Cursor.emit, Cursor.assign, Cursor.foldNative]

def otherGroup (channel : Fin parameters.channels) : Group :=
  if channel ∈ parameters.bridge.drivers then .drivers else .remaining

theorem driverCursor_first_absent (side : Side) (channel : Fin parameters.channels) :
    (driverCursor parameters).slots (.internal (.absent side parameters.firstBus channel)) =
      (firstArrays parameters).slots (.internal (.absent side parameters.firstBus channel)) := by
  simp [driverCursor, Cursor.foldNative, Cursor.assign]

theorem otherGroup_member (channel : Fin parameters.channels) (different : channel ≠ parameters.bridge.target) :
    (firstArrays parameters).slots (.internal (.absent .healthy parameters.firstBus channel)) ∈
      groupInputs (parameters := parameters) (otherGroup (parameters := parameters) channel) := by
  unfold otherGroup
  split
  · rename_i member
    exact List.mem_map.mpr ⟨channel, by simpa using member, rfl⟩
  · rename_i absent
    have member : channel ∈ parameters.bridge.remaining :=
      (parameters.bridge.mem_remaining channel).mpr ⟨different, absent⟩
    exact List.mem_map.mpr ⟨channel, by simpa using member, driverCursor_first_absent .healthy channel⟩

theorem otherGroup_nonempty (channel : Fin parameters.channels) (different : channel ≠ parameters.bridge.target) :
    groupInputs (parameters := parameters) (otherGroup (parameters := parameters) channel) ≠ [] := by
  intro empty
  have member := otherGroup_member channel different
  rw [empty] at member
  exact List.not_mem_nil member

/-- The actual faulty-zero cofactor yields a driver/remaining root clause. -/
def groupCofactor (rename : Nat → Fin v) (group : Group) :
    SubclauseProjection (initialState (relabel rename (formula parameters)))
      [mapLiteral rename ((faultyProductCursor (parameters := parameters)).lastID + 1, true),
       mapLiteral rename (groupOutput (parameters := parameters) group)] 1 := by
  let actual := faultyZeroInput (parameters := parameters) rename (groupIndex group)
  refine ⟨actual.state, actual.steps, actual.checked, retarget actual.result ?_, actual.count⟩
  intro literal member
  simpa only [groupOutput_interface] using member

/-- Root-to-leaf projection reuses the balanced actual input tree. Each
represented binary node is processed once; a unary group uses identity. -/
def otherAbsentFromFaultyZero (rename : Nat → Fin v) (channel : Fin parameters.channels)
    (different : channel ≠ parameters.bridge.target) :
    SubclauseProjection (initialState (relabel rename (formula parameters)))
      [mapLiteral rename ((faultyProductCursor (parameters := parameters)).lastID + 1, true),
       mapLiteral rename ((firstArrays parameters).slots (.internal (.absent .healthy parameters.firstBus channel)))]
      (2 * (groupTree rename (otherGroup (parameters := parameters) channel) (otherGroup_nonempty channel different)).nodes + 2) := by
  let group := otherGroup (parameters := parameters) channel
  let first := groupCofactor (parameters := parameters) rename group
  let root := mapLiteral rename (groupOutput (parameters := parameters) group)
  let flag := mapLiteral rename ((faultyProductCursor (parameters := parameters)).lastID + 1, true)
  let input := mapLiteral rename ((firstArrays parameters).slots (.internal (.absent .healthy parameters.firstBus channel)))
  let originalTree := groupTree rename group (otherGroup_nonempty channel different)
  let tree := AndTree.afterTrace originalTree first.state first.steps first.checked
  let projected := projectTreeInputs tree
  have inputMember : input ∈ (groupInputs (parameters := parameters) group).map (mapLiteral rename) :=
    List.mem_map.mpr ⟨_, otherGroup_member channel different, rfl⟩
  let rootClause := FoldProjection.afterTrace first.result projected.state projected.steps projected.checked
  have combined : runSteps (initialState (relabel rename (formula parameters)))
      (first.steps ++ projected.steps) = some projected.state := by
    rw [runSteps_append, first.checked]
    exact projected.checked
  have treeCount : projected.steps.length ≤ 2 * originalTree.nodes := by
    calc
      projected.steps.length ≤ 2 * tree.nodes := projected.count
      _ = _ := congrArg (fun nodes => 2 * nodes)
        (AndTree.afterTrace_nodes originalTree first.state first.steps first.checked)
  dsimp only [originalTree, group] at treeCount
  cases projected.results input inputMember with
  | identity same =>
      refine ⟨projected.state, first.steps ++ projected.steps, combined,
        retarget rootClause ?_, ?_⟩
      · intro literal member
        simpa only [same] using member
      · have one := first.count
        simp only [List.length_append]
        omega
  | derived implication =>
      let right : AvailableSubclause projected.state [root, flag] := retarget rootClause (by
        intro literal member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢
        aesop)
      let joined := longMerge projected.state root [input] [flag] implication right
      refine ⟨joined.state, (first.steps ++ projected.steps) ++ joined.steps, ?_, ?_, ?_⟩
      · rw [runSteps_append, combined]
        exact longMerge_run _ _ _ _ _ _
      · apply retarget (longMerge_result _ _ _ _ _ _)
        intro literal member
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member ⊢
        aesop
      · have one := first.count
        have two : joined.steps.length ≤ 1 :=
          longMerge_count projected.state root [input] [flag] implication right
        simp only [List.length_append]
        omega


/-- Conditional U_i=1 propagates x_i=0 through the actual NOT row. -/
def otherTermFromFaultyZero (rename : Nat → Fin v) (channel : Fin parameters.channels)
    (different : channel ≠ parameters.bridge.target) :
    SubclauseProjection (initialState (relabel rename (formula parameters)))
      [mapLiteral rename ((faultyProductCursor (parameters := parameters)).lastID + 1, true),
       negate (mapLiteral rename ((termBefore (parameters := parameters) channel).lastID + 1, true))]
      (2 * (groupTree rename (otherGroup (parameters := parameters) channel) (otherGroup_nonempty channel different)).nodes + 3) := by
  let first := otherAbsentFromFaultyZero rename channel different
  let absent := mapLiteral rename ((absentBefore (parameters := parameters) channel).lastID + 1, true)
  let term := mapLiteral rename ((termBefore (parameters := parameters) channel).lastID + 1, true)
  let flag := mapLiteral rename ((faultyProductCursor (parameters := parameters)).lastID + 1, true)
  have original : AvailableSubclause (initialState (relabel rename (formula parameters))) [negate absent, negate term] := by
    have row := ofRow ((absentRows rename channel).row ⟨1, by change 1 < 2; decide⟩)
    simpa [Bounded.Producer.rows, Gate.clauses, Rows.mapClause, mapLiteral,
      absentBefore_term_handle, absent, term, negate, Std.Sat.Literal.negate] using row
  let left := FoldProjection.afterTrace original first.state first.steps first.checked
  let right : AvailableSubclause first.state [absent, flag] := retarget first.result (by
    intro literal member
    rw [firstArrays_absent_handle] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢
    aesop)
  let joined := longMerge first.state absent [negate term] [flag] left right
  refine ⟨joined.state, first.steps ++ joined.steps, ?_, ?_, ?_⟩
  · rw [runSteps_append, first.checked]
    exact longMerge_run _ _ _ _ _ _
  · apply retarget (longMerge_result _ _ _ _ _ _)
    intro literal member
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member ⊢
    aesop
  · have one := first.count
    have two := longMerge_count first.state absent [negate term] [flag] left right
    simp only [List.length_append, joined]
    omega

theorem faultyFlag_handle :
    sourceRoleMap parameters (.internal (.flag .faulty parameters.firstBus)) =
      ((faultyProductCursor (parameters := parameters)).lastID + 1, true) := by
  unfold sourceRoleMap
  rw [compiled_first_flag]
  change ((faultyProductCursor (parameters := parameters)).emitNative
    (.internal (.flag .faulty parameters.firstBus))
    (.not ((faultyProductCursor (parameters := parameters)).slots (.internal (.firstProduct .faulty))))).slots
    (.internal (.flag .faulty parameters.firstBus)) = _
  simp [Cursor.emitNative, Cursor.emit, Cursor.assign]

end Controller.NativeProof.SourceMismatchSeed
