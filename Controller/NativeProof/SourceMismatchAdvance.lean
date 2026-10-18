module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.SourceMismatchSeed
public import Controller.NativeProof.SourceStageXor

@[expose] public section

/-! Constructive mixed-first-flag advancement uses the source controller's
actual mask emissions and physical mismatch seed. -/
namespace Controller.NativeProof.SourceMismatchAdvance
open Controller.CNF Controller.Resolution Controller.Resolution.Cases
open Controller.Native Controller.Native.SourceController
open Controller.NativeProof.FoldProjection Controller.NativeProof.SourceFoldProjection
open Controller.NativeProof.SourceCongruence Controller.NativeProof.SourceRoleFrames
open Controller.NativeProof.SourceSlotFrames Controller.NativeProof.SourceMismatchBranch
open Controller.NativeProof.SourceStageCongruence Controller.NativeProof.SourceStageXor
open Controller.NativeProof.SourceMismatchSeed Controller.NativeProof.SourceFoldOwners
open Controller.NativeProof.SourceFoldOccurrences Controller.NativeProof.SourceMismatchHandles
variable {parameters : Parameters} {v : Nat}

def mixedContext (rename : Nat → Fin v) : Clause (Fin v) :=
  [negate (mapLiteral rename (sourceRoleMap parameters (.internal (.flag .healthy parameters.firstBus)))),
   mapLiteral rename (sourceRoleMap parameters (.internal (.flag .faulty parameters.firstBus)))]

theorem mixedContext_eq (rename : Nat → Fin v) (channel : Fin parameters.channels) :
    mixedContext (parameters := parameters) rename =
      [negate (maskFlag rename .healthy channel), maskFlag rename .faulty channel] := by
  simp only [mixedContext, maskFlag_eq_sourceRoleMap]

/-- Both directions are retained original XOR occurrences. On the healthy
side mask equals negated absence; on the faulty side it equals absence. -/
def maskSource (rename : Nat → Fin v) (side : Side) (channel : Fin parameters.channels) : Literal (Fin v) :=
  match side with
  | .healthy => negate (maskAbsent rename side channel)
  | .faulty => maskAbsent rename side channel

def initialMaskRowsExact (rename : Nat → Fin v) (side : Side) (channel : Fin parameters.channels) :
    let cursor := initialMaskBefore side channel
    OriginalRows (initialState (relabel rename (formula parameters))) rename
      (⟨(cursor.lastID + 1, true), .xor (cursor.slots (.internal (.flag side parameters.firstBus)))
        (cursor.slots (.internal (.absent side parameters.firstBus channel)))⟩ : Bounded.Producer Nat) := by
  dsimp only
  exact emitRowsExact rename _ _ _ (initial_mask_before_compile side channel)

/-- The forward mixed-context implication is an actual original row with a
larger proof target; no weakening instruction is emitted. -/
def initialMaskForward (rename : Nat → Fin v) (side : Side) (channel : Fin parameters.channels) :
    AvailableSubclause (initialState (relabel rename (formula parameters)))
      (mixedContext (parameters := parameters) rename ++ [negate (maskSource rename side channel), maskOutput rename side channel]) := by
  cases side with
  | healthy =>
      let original := ofRow ((initialMaskRowsExact rename .healthy channel).row ⟨3, by change 3 < 4; decide⟩)
      have row : AvailableSubclause (initialState (relabel rename (formula parameters)))
          [negate (maskFlag rename .healthy channel), maskAbsent rename .healthy channel,
           maskOutput rename .healthy channel] := by
        simpa only [Bounded.Producer.rows, Gate.clauses, Rows.mapClause, List.map_cons,
          List.map_nil, List.getElem_cons_succ, List.getElem_cons_zero, maskFlag, maskAbsent,
          maskOutput, mapLiteral, negate, Std.Sat.Literal.negate] using original
      exact retarget row (by
        rw [mixedContext_eq rename channel]
        simp only [maskSource, negate_negate]
        intro literal member
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member ⊢
        aesop)
  | faulty =>
      let original := ofRow ((initialMaskRowsExact rename .faulty channel).row ⟨2, by change 2 < 4; decide⟩)
      have row : AvailableSubclause (initialState (relabel rename (formula parameters)))
          [maskFlag rename .faulty channel, negate (maskAbsent rename .faulty channel),
           maskOutput rename .faulty channel] := by
        simpa only [Bounded.Producer.rows, Gate.clauses, Rows.mapClause, List.map_cons,
          List.map_nil, List.getElem_cons_succ, List.getElem_cons_zero, maskFlag, maskAbsent,
          maskOutput, mapLiteral, negate, Std.Sat.Literal.negate] using original
      exact retarget row (by
        rw [mixedContext_eq rename channel]
        intro literal member
        simp only [maskSource, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member ⊢
        aesop)

/-- The reverse direction also uses an original XOR row and no split. -/
def initialMaskBackward (rename : Nat → Fin v) (side : Side) (channel : Fin parameters.channels) :
    AvailableSubclause (initialState (relabel rename (formula parameters)))
      (mixedContext (parameters := parameters) rename ++ [negate (maskOutput rename side channel), maskSource rename side channel]) := by
  cases side with
  | healthy =>
      let original := ofRow ((initialMaskRowsExact rename .healthy channel).row ⟨1, by change 1 < 4; decide⟩)
      have row : AvailableSubclause (initialState (relabel rename (formula parameters)))
          [negate (maskFlag rename .healthy channel), negate (maskAbsent rename .healthy channel),
           negate (maskOutput rename .healthy channel)] := by
        simpa only [Bounded.Producer.rows, Gate.clauses, Rows.mapClause, List.map_cons,
          List.map_nil, List.getElem_cons_succ, List.getElem_cons_zero, maskFlag, maskAbsent,
          maskOutput, mapLiteral, negate, Std.Sat.Literal.negate] using original
      exact retarget row (by
        rw [mixedContext_eq rename channel]
        intro literal member
        simp only [maskSource, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member ⊢
        aesop)
  | faulty =>
      let original := ofRow ((initialMaskRowsExact rename .faulty channel).row ⟨0, by change 0 < 4; decide⟩)
      have row : AvailableSubclause (initialState (relabel rename (formula parameters)))
          [maskFlag rename .faulty channel, maskAbsent rename .faulty channel,
           negate (maskOutput rename .faulty channel)] := by
        simpa only [Bounded.Producer.rows, Gate.clauses, Rows.mapClause, List.map_cons,
          List.map_nil, List.getElem_cons_zero, maskFlag, maskAbsent,
          maskOutput, mapLiteral, negate, Std.Sat.Literal.negate] using original
      exact retarget row (by
        rw [mixedContext_eq rename channel]
        intro literal member
        simp only [maskSource, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member ⊢
        aesop)

/-- The balanced physical seed already carries the final faulty first-flag
literal. Retargeting into the mixed context retains its actual trace and ID. -/
def otherAbsenceMixed (rename : Nat → Fin v) (channel : Fin parameters.channels)
    (different : channel ≠ parameters.bridge.target) :
    SubclauseProjection (initialState (relabel rename (formula parameters)))
      (mixedContext (parameters := parameters) rename ++
        [mapLiteral rename ((firstArrays parameters).slots
          (.internal (.absent .healthy parameters.firstBus channel)))])
      (2 * (groupTree rename (otherGroup (parameters := parameters) channel)
        (otherGroup_nonempty channel different)).nodes + 2) := by
  let first := otherAbsentFromFaultyZero rename channel different
  refine ⟨first.state, first.steps, first.checked, retarget first.result ?_, first.count⟩
  intro literal member
  rw [← faultyFlag_handle] at member
  simp only [mixedContext, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member ⊢
  aesop

/-- Recompute the physical interface cofactor at the current accepted prefix.
Fresh IDs are allocated from that state, so channel iterations do not collide. -/
def faultyZeroInputAt (rename : Nat → Fin v) (prefixState : SourcePrefix (parameters := parameters) rename)
    (index : Fin 3) : SubclauseProjection prefixState.state
      [mapLiteral rename ((faultyProductCursor (parameters := parameters)).lastID + 1, true),
       mapLiteral rename ((faultyProductInputs (parameters := parameters))[index.val]'(by
         simpa [faultyProductInputs] using index.isLt))] 1 := by
  let base := initialState (relabel rename (formula parameters))
  let product := mapLiteral rename ((healthyFlagCursor (parameters := parameters)).lastID + 1, true)
  let flag := mapLiteral rename ((faultyProductCursor (parameters := parameters)).lastID + 1, true)
  let input := mapLiteral rename ((faultyProductInputs (parameters := parameters))[index.val]'(by
    simpa [faultyProductInputs] using index.isLt))
  have originalLeft : AvailableSubclause base [negate product, input] := by
    have row := ofRow ((faultyProductRows (parameters := parameters) rename).row
      ⟨index.val, by change index.val < 4; omega⟩)
    have bound : index.val < (faultyProductInputs (parameters := parameters)).length := by
      simpa [faultyProductInputs] using index.isLt
    simpa [Bounded.Producer.rows, Gate.clauses, List.getElem_append, bound,
      Rows.mapClause, mapLiteral, product, input, base, negate, Std.Sat.Literal.negate] using row
  let originalRight : AvailableSubclause base [product, flag] :=
    retarget (ofRow ((faultyFlagRows (parameters := parameters) rename).row
      ⟨0, by change 0 < 2; decide⟩)) (by
        intro literal member
        simp [faultyProductCursor, Cursor.emitNative, Cursor.emit, Cursor.assign,
          Bounded.Producer.rows, Gate.clauses, Rows.mapClause, mapLiteral, product, flag,
          List.mem_cons, List.not_mem_nil] at member ⊢ <;> aesop)
  let left := FoldProjection.afterTrace originalLeft prefixState.state prefixState.steps prefixState.checked
  let right := FoldProjection.afterTrace originalRight prefixState.state prefixState.steps prefixState.checked
  let joined := longMerge prefixState.state product [input] [flag] left right
  refine ⟨joined.state, joined.steps, longMerge_run _ _ _ _ _ _,
    retarget (longMerge_result _ _ _ _ _ _) ?_, longMerge_count _ _ _ _ _ _⟩
  intro literal member
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member ⊢
  aesop

def groupCofactorAt (rename : Nat → Fin v) (prefixState : SourcePrefix (parameters := parameters) rename)
    (group : Group) : SubclauseProjection prefixState.state
      [mapLiteral rename ((faultyProductCursor (parameters := parameters)).lastID + 1, true),
       mapLiteral rename (groupOutput (parameters := parameters) group)] 1 := by
  let actual := faultyZeroInputAt rename prefixState (groupIndex group)
  refine ⟨actual.state, actual.steps, actual.checked, retarget actual.result ?_, actual.count⟩
  intro literal member
  simpa only [groupOutput_interface] using member

/-- The current-state balanced seed is executable at every channel iteration.
Its root implication and tree projections share the same accepted prefix. -/
def otherAbsenceAt (rename : Nat → Fin v) (prefixState : SourcePrefix (parameters := parameters) rename)
    (channel : Fin parameters.channels) (different : channel ≠ parameters.bridge.target) :
    SubclauseProjection prefixState.state
      (mixedContext (parameters := parameters) rename ++ [mapLiteral rename ((firstArrays parameters).slots
        (.internal (.absent .healthy parameters.firstBus channel)))])
      (2 * (groupTree rename (otherGroup (parameters := parameters) channel)
        (otherGroup_nonempty channel different)).nodes + 2) := by
  let group := otherGroup (parameters := parameters) channel
  let first := groupCofactorAt rename prefixState group
  let root := mapLiteral rename (groupOutput (parameters := parameters) group)
  let flag := mapLiteral rename ((faultyProductCursor (parameters := parameters)).lastID + 1, true)
  let input := mapLiteral rename ((firstArrays parameters).slots
    (.internal (.absent .healthy parameters.firstBus channel)))
  let originalTree := groupTree rename group (otherGroup_nonempty channel different)
  have combinedPrefix : runSteps (initialState (relabel rename (formula parameters)))
      (prefixState.steps ++ first.steps) = some first.state := by
    rw [runSteps_append, prefixState.checked]
    exact first.checked
  let tree := originalTree.afterTrace first.state (prefixState.steps ++ first.steps) combinedPrefix
  let projected := projectTreeInputs tree
  have inputMember : input ∈ (groupInputs (parameters := parameters) group).map (mapLiteral rename) :=
    List.mem_map.mpr ⟨_, otherGroup_member channel different, rfl⟩
  let rootClause : AvailableSubclause projected.state [flag, root] :=
    FoldProjection.afterTrace first.result projected.state projected.steps projected.checked
  have combined : runSteps prefixState.state (first.steps ++ projected.steps) = some projected.state := by
    rw [runSteps_append, first.checked]
    exact projected.checked
  have treeCount : projected.steps.length ≤ 2 * originalTree.nodes := by
    calc
      projected.steps.length ≤ 2 * tree.nodes := projected.count
      _ = _ := congrArg (fun nodes => 2 * nodes)
        (AndTree.afterTrace_nodes originalTree first.state (prefixState.steps ++ first.steps) combinedPrefix)
  change projected.steps.length ≤ 2 * (groupTree rename
    (otherGroup (parameters := parameters) channel) (otherGroup_nonempty channel different)).nodes at treeCount
  match projected.results input inputMember with
  | .identity same =>
      refine ⟨projected.state, first.steps ++ projected.steps, combined, retarget rootClause ?_, ?_⟩
      · intro literal member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with one | two
        · subst literal
          exact List.mem_append_left _ (by
            change mapLiteral rename ((faultyProductCursor (parameters := parameters)).lastID + 1, true) ∈ mixedContext (parameters := parameters) rename
            rw [← faultyFlag_handle]
            exact List.mem_cons_of_mem _ (List.mem_cons_self ..))
        · exact List.mem_append_right _ (by
            exact List.mem_singleton.mpr (two.trans same))
      · have one := first.count
        simp only [List.length_append]
        omega
  | .derived implication =>
      let right : AvailableSubclause projected.state [root, flag] := retarget rootClause (by
        intro literal member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢
        exact member.elim (fun equal => Or.inr equal) (fun equal => Or.inl equal))
      let joined := longMerge projected.state root [input] [flag] implication right
      refine ⟨joined.state, (first.steps ++ projected.steps) ++ joined.steps, ?_, ?_, ?_⟩
      · rw [runSteps_append, combined]
        exact longMerge_run _ _ _ _ _ _
      · apply retarget (longMerge_result _ _ _ _ _ _)
        intro literal member
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with one | two
        · exact List.mem_append_right _ (List.mem_singleton.mpr one)
        · subst literal
          exact List.mem_append_left _ (by
            change mapLiteral rename ((faultyProductCursor (parameters := parameters)).lastID + 1, true) ∈ mixedContext (parameters := parameters) rename
            rw [← faultyFlag_handle]
            exact List.mem_cons_of_mem _ (List.mem_cons_self ..))
      · have one := first.count
        have two : joined.steps.length ≤ 1 := longMerge_count projected.state root [input] [flag] implication right
        simp only [List.length_append]
        omega

def absenceCost (rename : Nat → Fin v) (channel : Fin parameters.channels) : Nat :=
  if same : channel = parameters.bridge.target then 0
  else 2 * (groupTree rename (otherGroup (parameters := parameters) channel)
    (otherGroup_nonempty channel same)).nodes + 2

structure AbsenceBank (rename : Nat → Fin v)
    (start : SourcePrefix (parameters := parameters) rename)
    (channels : List (Fin parameters.channels)) where
  state : State v
  steps : List (Step v)
  checked : runSteps start.state steps = some state
  rows : ∀ channel ∈ channels, AvailableSubclause state
    (mixedContext (parameters := parameters) rename ++ [mapLiteral rename ((firstArrays parameters).slots
      (.internal (.absent .healthy parameters.firstBus channel)))])
  count : steps.length ≤ (channels.map (absenceCost rename)).sum

/-- Assemble one absence-bank cell outside the structural recursive equations. -/
def buildAbsenceBankStep (rename : Nat → Fin v)
    (start : SourcePrefix (parameters := parameters) rename)
    (channel : Fin parameters.channels) (rest : List (Fin parameters.channels))
    (nonTarget : ∀ query ∈ channel :: rest, query ≠ parameters.bridge.target)
    (recurse : ∀ (next : SourcePrefix (parameters := parameters) rename),
      (∀ query ∈ rest, query ≠ parameters.bridge.target) → AbsenceBank rename next rest) :
    AbsenceBank rename start (channel :: rest) := by
  let different := nonTarget channel (by simp)
  let first := otherAbsenceAt rename start channel different
  let nextPrefix := start.extend first.state first.steps first.checked
  let next := recurse nextPrefix (by
    intro query member
    exact nonTarget query (List.mem_cons_of_mem channel member))
  refine ⟨next.state, first.steps ++ next.steps, ?_, ?_, ?_⟩
  · rw [runSteps_append, first.checked]
    exact next.checked
  · intro query member
    if same : query = channel then
      subst query
      exact FoldProjection.afterTrace first.result next.state next.steps next.checked
    else
      exact next.rows query ((List.mem_cons.mp member).resolve_left same)
  · have firstCount : first.steps.length ≤ absenceCost rename channel := by
      simpa only [absenceCost, dite_eq_right different] using first.count
    have nextCount := next.count
    simp only [List.length_append, List.map_cons, List.sum_cons]
    omega


/-- Structural list traversal recomputes every seed at the actual current
state. Every retained result is transported through the subsequent trace. -/
def buildAbsenceBank (rename : Nat → Fin v)
    (start : SourcePrefix (parameters := parameters) rename)
    (channels : List (Fin parameters.channels))
    (nonTarget : ∀ channel ∈ channels, channel ≠ parameters.bridge.target) :
    AbsenceBank rename start channels := by
  match channels with
  | [] =>
      exact ⟨start.state, [], rfl, by intro channel member; simp at member, by simp⟩
  | channel :: rest =>
      exact buildAbsenceBankStep rename start channel rest nonTarget
        (fun next tailNonTarget => buildAbsenceBank rename next rest tailNonTarget)

/-- The computed bank covers every non-target channel in the declared finite
universe; no caller supplies native availability or precomputed derivations. -/
def allOtherAbsences (rename : Nat → Fin v) :
    AbsenceBank rename (SourcePrefix.initial rename)
      ((List.finRange parameters.channels).filter (fun channel => decide (channel ≠ parameters.bridge.target))) :=
  buildAbsenceBank rename (SourcePrefix.initial rename) _ (by
    intro channel member
    exact of_decide_eq_true (List.mem_filter.mp member).2)

def allOtherAbsences_complete (rename : Nat → Fin v) (channel : Fin parameters.channels)
    (different : channel ≠ parameters.bridge.target) :
    AvailableSubclause (allOtherAbsences (parameters := parameters) rename).state
      (mixedContext (parameters := parameters) rename ++ [mapLiteral rename ((firstArrays parameters).slots
        (.internal (.absent .healthy parameters.firstBus channel)))]) :=
  (allOtherAbsences rename).rows channel (List.mem_filter.mpr ⟨by simp, decide_eq_true different⟩)

theorem maskAbsent_source (rename : Nat → Fin v) (side : Side) (channel : Fin parameters.channels) :
    maskAbsent rename side channel = mapLiteral rename ((firstArrays parameters).slots
      (.internal (.absent .healthy parameters.firstBus channel))) := by
  unfold maskAbsent initialMaskBefore occurrenceCursor
  rw [initialMasks_absent side side]
  cases side with
  | healthy =>
      change mapLiteral rename ((interface parameters).slots
        (.internal (.absent .healthy parameters.firstBus channel))) = _
      rw [interface_absent]
  | faulty =>
      change mapLiteral rename ((SourceController.tail parameters .healthy (interface parameters)).slots
        (.internal (.absent .faulty parameters.firstBus channel))) = _
      rw [healthy_tail_faulty_absent, interface_absent, ← firstArrays_absent_equal]

def absenceValue (rename : Nat → Fin v) (channel : Fin parameters.channels) (bit : Bool) : Literal (Fin v) :=
  valueLiteral (mapLiteral rename ((firstArrays parameters).slots
    (.internal (.absent .healthy parameters.firstBus channel)))) bit

def firstMaskValue (rename : Nat → Fin v) (side : Side) (channel : Fin parameters.channels)
    (absence : Bool) : Literal (Fin v) :=
  valueLiteral (maskOutput rename side channel)
    (match side with | .healthy => !absence | .faulty => absence)

/-- Fixing first flags leaves one XOR equation sufficient for each requested
mask value. The only reason is the concrete source absence seed. -/
def maskValueOriginal (rename : Nat → Fin v) (side : Side) (channel : Fin parameters.channels)
    (absence : Bool) : AvailableSubclause (initialState (relabel rename (formula parameters)))
      (mixedContext (parameters := parameters) rename ++ [negate (absenceValue rename channel absence),
        firstMaskValue rename side channel absence]) := by
  cases side <;> cases absence
  · exact retarget (initialMaskForward rename .healthy channel) (by
      intro literal member
      simpa only [maskSource, maskAbsent_source, absenceValue, firstMaskValue,
        valueLiteral, Bool.not_false, Bool.false_eq_true, ite_false, ite_true, negate_negate] using member)
  · exact retarget (initialMaskBackward rename .healthy channel) (by
      intro literal member
      simp only [maskSource, maskAbsent_source, absenceValue, firstMaskValue,
        valueLiteral, Bool.not_true, Bool.false_eq_true, ite_false, ite_true, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member ⊢
      rcases member with old | output | input
      · exact Or.inl old
      · exact Or.inr (Or.inr output)
      · exact Or.inr (Or.inl input))
  · exact retarget (initialMaskBackward rename .faulty channel) (by
      intro literal member
      simp only [maskSource, maskAbsent_source, absenceValue, firstMaskValue,
        valueLiteral, Bool.false_eq_true, ite_false, ite_true, negate_negate, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at member ⊢
      rcases member with old | output | input
      · exact Or.inl old
      · exact Or.inr (Or.inr output)
      · exact Or.inr (Or.inl input))
  · exact retarget (initialMaskForward rename .faulty channel) (by
      intro literal member
      simpa only [maskSource, maskAbsent_source, absenceValue, firstMaskValue, valueLiteral, Bool.false_eq_true, ite_false, ite_true] using member)

def maskValueAt (rename : Nat → Fin v) (prefixState : SourcePrefix (parameters := parameters) rename)
    (side : Side) (channel : Fin parameters.channels) (absence : Bool)
    (seed : AvailableSubclause prefixState.state (mixedContext (parameters := parameters) rename ++ [absenceValue rename channel absence])) :
    SubclauseProjection prefixState.state (mixedContext (parameters := parameters) rename ++ [firstMaskValue rename side channel absence]) 1 := by
  let input := absenceValue rename channel absence
  let output := firstMaskValue rename side channel absence
  let context := mixedContext (parameters := parameters) rename
  let original := maskValueOriginal rename side channel absence
  let row := FoldProjection.afterTrace original prefixState.state prefixState.steps prefixState.checked
  let left : AvailableSubclause prefixState.state (negate input :: (context ++ [output])) := retarget row (by
    intro literal member
    simp only [input, output, context, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member ⊢
    rcases member with old | pivot | final
    · exact Or.inr (Or.inl old)
    · exact Or.inl pivot
    · exact Or.inr (Or.inr final))
  let right : AvailableSubclause prefixState.state (input :: context) := retarget seed (by
    intro literal member
    simp only [input, context, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member ⊢
    exact member.elim Or.inr Or.inl)
  let joined := longMerge prefixState.state input (context ++ [output]) context left right
  refine ⟨joined.state, joined.steps, longMerge_run _ _ _ _ _ _,
    retarget (longMerge_result _ _ _ _ _ _) ?_, longMerge_count _ _ _ _ _ _⟩
  intro literal member
  simp only [context, output, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member ⊢
  rcases member with (old | final) | old
  · exact Or.inl old
  · exact Or.inr final
  · exact Or.inl old

def absenceBit (channel : Fin parameters.channels) : Bool := decide (channel ≠ parameters.bridge.target)

structure MaskSeedBank (rename : Nat → Fin v) (prefixState : SourcePrefix (parameters := parameters) rename) where
  rows : ∀ channel : Fin parameters.channels, AvailableSubclause prefixState.state
    (mixedContext (parameters := parameters) rename ++ [absenceValue rename channel (absenceBit channel)])

def MaskSeedBank.afterTrace (seed : MaskSeedBank (parameters := parameters) rename prefixState)
    (next : State v) (steps : List (Step v)) (checked : runSteps prefixState.state steps = some next) :
    MaskSeedBank rename (prefixState.extend next steps checked) where
  rows channel := FoldProjection.afterTrace (seed.rows channel) next steps checked

structure FirstMaskBank (rename : Nat → Fin v)
    (start : SourcePrefix (parameters := parameters) rename) (channels : List (Fin parameters.channels)) where
  state : State v
  steps : List (Step v)
  checked : runSteps start.state steps = some state
  rows : ∀ side channel, channel ∈ channels → AvailableSubclause state
    (mixedContext (parameters := parameters) rename ++ [firstMaskValue rename side channel (absenceBit channel)])
  count : steps.length ≤ 2 * channels.length

structure FirstMaskPair (rename : Nat → Fin v)
    (start : SourcePrefix (parameters := parameters) rename) (channel : Fin parameters.channels) where
  state : State v
  steps : List (Step v)
  checked : runSteps start.state steps = some state
  rows : ∀ side, AvailableSubclause state
    (mixedContext (parameters := parameters) rename ++ [firstMaskValue rename side channel (absenceBit channel)])
  count : steps.length ≤ 2

/-- Both side computations allocate from the actual accepted mutable prefix. -/
def firstMaskPair (rename : Nat → Fin v) (start : SourcePrefix (parameters := parameters) rename)
    (seeds : MaskSeedBank rename start) (channel : Fin parameters.channels) :
    FirstMaskPair rename start channel := by
  let healthy := maskValueAt rename start .healthy channel (absenceBit channel) (seeds.rows channel)
  let healthyPrefix := start.extend healthy.state healthy.steps healthy.checked
  let healthySeeds := seeds.afterTrace healthy.state healthy.steps healthy.checked
  let faulty := maskValueAt rename healthyPrefix .faulty channel (absenceBit channel) (healthySeeds.rows channel)
  refine ⟨faulty.state, healthy.steps ++ faulty.steps, ?_, ?_, ?_⟩
  · rw [runSteps_append, healthy.checked]
    exact faulty.checked
  · intro side
    cases side with
    | healthy => exact FoldProjection.afterTrace healthy.result faulty.state faulty.steps faulty.checked
    | faulty => exact faulty.result
  · have one := healthy.count
    have two := faulty.count
    simp only [List.length_append]
    omega

/-- The proof constructor composes one pair and a previously computed suffix. -/
def FirstMaskBank.prepend (rename : Nat → Fin v)
    (start : SourcePrefix (parameters := parameters) rename) (channel : Fin parameters.channels)
    (rest : List (Fin parameters.channels)) (pair : FirstMaskPair rename start channel)
    (next : FirstMaskBank rename (start.extend pair.state pair.steps pair.checked) rest) :
    FirstMaskBank rename start (channel :: rest) := by
  refine ⟨next.state, pair.steps ++ next.steps, ?_, ?_, ?_⟩
  · rw [runSteps_append, pair.checked]
    exact next.checked
  · intro side query member
    if same : query = channel then
      subst query
      exact FoldProjection.afterTrace (pair.rows side) next.state next.steps next.checked
    else exact next.rows side query ((List.mem_cons.mp member).resolve_left same)
  · have one := pair.count
    have two := next.count
    simp only [List.length_append, List.length_cons]
    omega

/-- Structural traversal retains only the current prefix and one recursive
suffix computation; composition proofs are checked outside the recursion. -/
def buildFirstMaskBank (rename : Nat → Fin v)
    (start : SourcePrefix (parameters := parameters) rename) (seeds : MaskSeedBank rename start)
    (channels : List (Fin parameters.channels)) : FirstMaskBank rename start channels :=
  match channels with
  | [] => ⟨start.state, [], rfl, by intro side channel member; simp at member, by simp⟩
  | channel :: rest =>
      let pair := firstMaskPair rename start seeds channel
      let nextPrefix := start.extend pair.state pair.steps pair.checked
      let nextSeeds := seeds.afterTrace pair.state pair.steps pair.checked
      FirstMaskBank.prepend rename start channel rest pair
        (buildFirstMaskBank rename nextPrefix nextSeeds rest)

/-- All non-target seeds are computed by the balanced physical derivation;
the target seed is the actual drive-one input unit. -/
def allMaskSeeds (rename : Nat → Fin v) (drive : parameters.drive = true) :
    let bank := allOtherAbsences (parameters := parameters) rename
    let prefixState : SourcePrefix (parameters := parameters) rename := ⟨bank.state, bank.steps, bank.checked⟩
    MaskSeedBank rename prefixState := by
  dsimp only
  refine ⟨?_⟩
  intro channel
  by_cases same : channel = parameters.bridge.target
  · subst channel
    let unit := physicalUnitRow (parameters := parameters) rename ⟨0, by decide⟩
    have original : AvailableSubclause (initialState (relabel rename (formula parameters)))
        (mixedContext (parameters := parameters) rename ++ [absenceValue rename parameters.bridge.target false]) := by
      apply retarget (ofRow unit)
      intro literal member
      have unitEq := targetPhysicalUnit rename drive
      rw [wireCursor_first_absent] at unitEq
      simp only [ofRow, Rows.mapClause, List.map_cons, List.map_nil,
        List.mem_cons, List.not_mem_nil, or_false] at member
      rw [unitEq] at member
      exact List.mem_append_right _ (by simpa [absenceValue, valueLiteral, Bool.false_eq_true, ite_false, ite_true] using member)
    simpa only [absenceBit, ne_eq, not_true_eq_false, decide_false] using
      FoldProjection.afterTrace original (allOtherAbsences rename).state
        (allOtherAbsences rename).steps (allOtherAbsences rename).checked
  · simpa only [absenceBit, decide_eq_true_eq, same, not_false_eq_true, decide_true,
      absenceValue, valueLiteral, ite_eq_left same] using allOtherAbsences_complete rename channel same

/-- This endpoint computes the complete first-mask bank from source input.
It requires no available native clauses or caller-generated certificate bank. -/
def allFirstMasks (rename : Nat → Fin v) (drive : parameters.drive = true) :
    FirstMaskBank rename
      (⟨(allOtherAbsences (parameters := parameters) rename).state,
        (allOtherAbsences rename).steps, (allOtherAbsences rename).checked⟩ : SourcePrefix (parameters := parameters) rename)
      (List.finRange parameters.channels) :=
  buildFirstMaskBank rename _ (allMaskSeeds rename drive) _

theorem allFirstMasks_count (rename : Nat → Fin v) (drive : parameters.drive = true) :
    (allFirstMasks (parameters := parameters) rename drive).steps.length ≤ 2 * parameters.channels := by
  simpa only [List.length_finRange] using (allFirstMasks rename drive).count

end Controller.NativeProof.SourceMismatchAdvance
