module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.SourceStageCongruence

@[expose] public section

/-! Checked XOR cofactors use actual source producer rows and earlier guarded
subclauses. A missing pivot reuses an existing row. -/
namespace Controller.NativeProof.SourceStageXor
open Controller.Native Controller.Native.SourceController Controller.CNF
open Controller.Resolution Controller.Resolution.Cases
open Controller.NativeProof.FoldProjection Controller.NativeProof.SourceFoldProjection
open Controller.NativeProof.SourceStageCongruence Controller.NativeProof.SourceFoldOccurrences
variable {v : Nat} {parameters : Parameters}

structure XorRows (state : State v) (a b output : Literal (Fin v)) where
  zeroZero : AvailableSubclause state [a, b, negate output]
  oneOne : AvailableSubclause state [negate a, negate b, negate output]
  zeroOne : AvailableSubclause state [a, negate b, output]
  oneZero : AvailableSubclause state [negate a, b, output]

def xorRowsOriginal {rename : Nat → Fin v} (a b output : Literal Nat)
    (rows : OriginalRows state rename ⟨output, .xor a b⟩) :
    XorRows state (mapLiteral rename a) (mapLiteral rename b) (mapLiteral rename output) where
  zeroZero := ofRow (rows.row ⟨0, by change 0 < 4; decide⟩)
  oneOne := ofRow (rows.row ⟨1, by change 1 < 4; decide⟩)
  zeroOne := ofRow (rows.row ⟨2, by change 2 < 4; decide⟩)
  oneZero := ofRow (rows.row ⟨3, by change 3 < 4; decide⟩)

def XorRows.afterTrace (rows : XorRows state a b output) (next : State v)
    (steps : List (Step v)) (checked : runSteps state steps = some next) : XorRows next a b output where
  zeroZero := FoldProjection.afterTrace rows.zeroZero next steps checked
  oneOne := FoldProjection.afterTrace rows.oneOne next steps checked
  zeroOne := FoldProjection.afterTrace rows.zeroOne next steps checked
  oneZero := FoldProjection.afterTrace rows.oneZero next steps checked

/-- Identity data avoids creating a fictitious tautological reason row. -/
inductive CofactorReason (state : State v) (target : Clause (Fin v)) (input : Literal (Fin v)) : Type
  | known (contained : negate input ∈ target)
  | propagated (row : AvailableSubclause state (target ++ [input]))

def CofactorReason.afterTrace (reason : CofactorReason state target input) (next : State v)
    (steps : List (Step v)) (checked : runSteps state steps = some next) :
    CofactorReason next target input :=
  match reason with
  | .known contained => .known contained
  | .propagated row => .propagated (FoldProjection.afterTrace row next steps checked)

def cofactorReason (transfer : GuardedTransfer state context left right)
    (included : ClauseSubset context target) (negative : negate left ∈ target) :
    CofactorReason state target right := by
  cases transfer with
  | identity same => exact .known (by simpa only [← same] using negative)
  | derived row =>
      exact .propagated (retarget row (by
        intro literal member
        have contained := member
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at contained ⊢
        rcases contained with old | equal | equal
        · exact Or.inl (included literal old)
        · exact Or.inl (equal.symm ▸ negative)
        · exact Or.inr equal))

/-- One actual merge eliminates the input; known branch guards require no step. -/
def resolveReason (state : State v) (target remaining : Clause (Fin v))
    (input : Literal (Fin v))
    (conflict : AvailableSubclause state (negate input :: (remaining ++ target)))
    (reason : CofactorReason state target input) :
    SubclauseProjection state (remaining ++ target) 1 := by
  cases reason with
  | known contained =>
      refine ⟨state, [], rfl, retarget conflict ?_, by simp⟩
      intro literal member
      have old := member
      rcases List.mem_cons.mp old with same | rest
      · exact List.mem_append_right remaining (same.symm ▸ contained)
      · exact rest
  | propagated row =>
      let adapted : AvailableSubclause state (input :: target) := retarget row (by
        intro literal member
        have old := member
        simpa only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, false_or, or_comm] using old)
      let joined := longMerge state input (remaining ++ target) target conflict adapted
      let result := longMerge_result state input (remaining ++ target) target conflict adapted
      refine ⟨joined.state, joined.steps,
        longMerge_run state input (remaining ++ target) target conflict adapted,
        retarget result ?_, longMerge_count state input (remaining ++ target) target conflict adapted⟩
      intro literal member
      have old := member
      simp only [List.mem_append] at old ⊢
      aesop

/-- Odd-parity branches eliminate two right-input guards from a real XOR row. -/
def oddCofactor (state : State v) (target : Clause (Fin v))
    (a b output : Literal (Fin v)) (outputMem : output ∈ target)
    (row : AvailableSubclause state [negate a, negate b, output])
    (firstReason : CofactorReason state target a)
    (secondReason : CofactorReason state target b) : SubclauseProjection state target 2 := by
  let adapted : AvailableSubclause state (negate a :: ([negate b] ++ target)) := retarget row (by
    intro literal member
    have old := member
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at old ⊢
    aesop)
  let first := resolveReason state target [negate b] a adapted firstReason
  let secondConflict : AvailableSubclause first.state (negate b :: ([] ++ target)) :=
    retarget first.result (by intro literal member; simpa using member)
  let second := resolveReason first.state target [] b secondConflict
    (secondReason.afterTrace first.state first.steps first.checked)
  refine ⟨second.state, first.steps ++ second.steps, ?_, ?_, ?_⟩
  · rw [runSteps_append, first.checked]
    exact second.checked
  · exact retarget second.result (by intro literal member; simpa using member)
  · have one := first.count
    have two := second.count
    simp only [List.length_append]
    omega

def valueLiteral (literal : Literal (Fin v)) (bit : Bool) : Literal (Fin v) :=
  if bit then literal else negate literal

def branchTarget (target : Clause (Fin v)) (a b : Literal (Fin v)) (x y : Bool) : Clause (Fin v) :=
  (target ++ [negate (valueLiteral a x)]) ++ [negate (valueLiteral b y)]

def dualTransfer (transfer : GuardedTransfer state context input output) :
    GuardedTransfer state context (negate output) (negate input) := by
  cases transfer with
  | identity same => exact .identity (congrArg negate same.symm)
  | derived row => exact .derived (retarget row (by
      intro literal member
      have old := member
      simp only [negate_negate, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at old ⊢
      aesop))

def inputReason (state : State v) (context target : Clause (Fin v))
    (left right : Literal (Fin v)) (bit : Bool)
    (forward : GuardedTransfer state context left right)
    (backward : GuardedTransfer state context right left)
    (included : ClauseSubset context target)
    (guardMem : negate (valueLiteral left bit) ∈ target) :
    CofactorReason state target (valueLiteral right bit) := by
  cases bit with
  | false => exact cofactorReason (dualTransfer backward) included guardMem
  | true => exact cofactorReason forward included guardMem

/-- The branch chooses concrete gate rows by Boolean data, never by a semantic
entailment oracle. Even branches use a left row; odd branches resolve a right row. -/
def xorCofactor (state : State v) (context : Clause (Fin v))
    (a b c d leftOut rightOut : Literal (Fin v))
    (left : XorRows state a b leftOut) (right : XorRows state c d rightOut)
    (aForward : GuardedTransfer state context a c) (aBackward : GuardedTransfer state context c a)
    (bForward : GuardedTransfer state context b d) (bBackward : GuardedTransfer state context d b)
    (x y : Bool) :
    SubclauseProjection state (branchTarget (context ++ [negate leftOut, rightOut]) a b x y) 2 := by
  let target := branchTarget (context ++ [negate leftOut, rightOut]) a b x y
  have included : ClauseSubset context target := by
    intro literal member
    simp only [target, branchTarget, List.mem_append]
    exact Or.inl (Or.inl (Or.inl member))
  have aMem : negate (valueLiteral a x) ∈ target := by simp [target, branchTarget]
  have bMem : negate (valueLiteral b y) ∈ target := by simp [target, branchTarget]
  let firstReason := inputReason state context target a c x aForward aBackward included aMem
  let secondReason := inputReason state context target b d y bForward bBackward included bMem
  have outputMem : rightOut ∈ target := by simp [target, branchTarget]
  cases x <;> cases y
  · refine ⟨state, [], rfl, retarget left.zeroZero ?_, by simp⟩
    intro literal member
    have old := member
    simp only [target, branchTarget, valueLiteral, Bool.false_eq_true, ite_false, negate_negate,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at old ⊢
    aesop
  · let row : AvailableSubclause state [negate (valueLiteral c false), negate (valueLiteral d true), rightOut] :=
      retarget right.zeroOne (by intro literal member; simpa [valueLiteral] using member)
    exact oddCofactor state target _ _ rightOut outputMem row firstReason secondReason
  · let row : AvailableSubclause state [negate (valueLiteral c true), negate (valueLiteral d false), rightOut] :=
      retarget right.oneZero (by intro literal member; simpa [valueLiteral] using member)
    exact oddCofactor state target _ _ rightOut outputMem row firstReason secondReason
  · refine ⟨state, [], rfl, retarget left.oneOne ?_, by simp⟩
    intro literal member
    have old := member
    simp only [target, branchTarget, valueLiteral, ite_true,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at old ⊢
    aesop

def rowLeaf {state : State v} {target : Clause (Fin v)} (row : AvailableSubclause state target) : CaseTree v :=
  .leaf ⟨row.row.id, row.clause, []⟩

theorem rowLeaf_valid {state : State v} {target : Clause (Fin v)} (row : AvailableSubclause state target) : ValidTree state target (rowLeaf row) := by
  refine ⟨row.row.present, row.row.bound, ?_, ?_, ?_⟩
  · simp [RUP.KnownReasons]
  · simp [RUP.ValidReasons]
  · simpa [RUP.negations] using row.subset

/-- Two split literals are shared by all four leaves. The rows are the actual
stronger results of the four checked cofactor traces. -/
def xorCaseTree (state : State v) (target : Clause (Fin v)) (a b : Literal (Fin v))
    (tt : AvailableSubclause state (branchTarget target a b true true))
    (tf : AvailableSubclause state (branchTarget target a b true false))
    (ft : AvailableSubclause state (branchTarget target a b false true))
    (ff : AvailableSubclause state (branchTarget target a b false false)) : CaseTree v :=
  .fork a (.fork b (rowLeaf tt) (rowLeaf tf)) (.fork b (rowLeaf ft) (rowLeaf ff))

theorem xorCaseTree_valid (state : State v) (target : Clause (Fin v)) (a b : Literal (Fin v))
    (tt : AvailableSubclause state (branchTarget target a b true true))
    (tf : AvailableSubclause state (branchTarget target a b true false))
    (ft : AvailableSubclause state (branchTarget target a b false true))
    (ff : AvailableSubclause state (branchTarget target a b false false)) :
    ValidTree state target (xorCaseTree state target a b tt tf ft ff) := by
  exact ⟨⟨by simpa [branchTarget, valueLiteral] using rowLeaf_valid tt,
    by simpa [branchTarget, valueLiteral] using rowLeaf_valid tf⟩,
    ⟨by simpa [branchTarget, valueLiteral] using rowLeaf_valid ft,
    by simpa [branchTarget, valueLiteral] using rowLeaf_valid ff⟩⟩

theorem xorCaseTree_depth (state : State v) (target : Clause (Fin v)) (a b : Literal (Fin v))
    (tt : AvailableSubclause state (branchTarget target a b true true))
    (tf : AvailableSubclause state (branchTarget target a b true false))
    (ft : AvailableSubclause state (branchTarget target a b false true))
    (ff : AvailableSubclause state (branchTarget target a b false false)) :
    DepthBound 2 (xorCaseTree state target a b tt tf ft ff) := by
  simp [xorCaseTree, rowLeaf, DepthBound]

def joinCofactors (state : State v) (target : Clause (Fin v)) (a b : Literal (Fin v))
    (tt : AvailableSubclause state (branchTarget target a b true true))
    (tf : AvailableSubclause state (branchTarget target a b true false))
    (ft : AvailableSubclause state (branchTarget target a b false true))
    (ff : AvailableSubclause state (branchTarget target a b false false)) : SubclauseProjection state target 3 := by
  let tree := xorCaseTree state target a b tt tf ft ff
  let joined := compileTree state tree
  have checked := compileTree_run tree state state (Nat.le_refl _) (fun _ _ => rfl) target
    (xorCaseTree_valid state target a b tt tf ft ff)
  refine ⟨joined.state, joined.steps, checked.1,
    ⟨joined.clause, ⟨joined.rowId, checked.2.1, checked.2.2.1⟩, checked.2.2.2⟩, ?_⟩
  change (compileTree state tree).steps.length ≤ 3
  have budget : inferenceBudget tree = 3 := rfl
  have count := compileTree_count_le tree state
  rw [budget] at count
  exact count

/-- Four checked cofactor traces are emitted once, followed by the actual case
compiler. Runtime state contains rows and proof steps, with no semantic oracle. -/
def guardedXor (state : State v) (context : Clause (Fin v))
    (a b c d leftOut rightOut : Literal (Fin v))
    (left : XorRows state a b leftOut) (right : XorRows state c d rightOut)
    (aForward : GuardedTransfer state context a c) (aBackward : GuardedTransfer state context c a)
    (bForward : GuardedTransfer state context b d) (bBackward : GuardedTransfer state context d b) :
    SubclauseProjection state (context ++ [negate leftOut, rightOut]) 11 := by
  let runBranch := fun (next : State v) (steps : List (Step v))
      (checked : runSteps state steps = some next) (x y : Bool) =>
    xorCofactor next context a b c d leftOut rightOut
      (left.afterTrace next steps checked) (right.afterTrace next steps checked)
      (aForward.afterTrace next steps checked) (aBackward.afterTrace next steps checked)
      (bForward.afterTrace next steps checked) (bBackward.afterTrace next steps checked) x y
  let first := runBranch state [] rfl true true
  let second := runBranch first.state first.steps first.checked true false
  have firstTwo : runSteps state (first.steps ++ second.steps) = some second.state := by
    rw [runSteps_append, first.checked]
    exact second.checked
  let third := runBranch second.state (first.steps ++ second.steps) firstTwo false true
  have firstThree : runSteps state ((first.steps ++ second.steps) ++ third.steps) = some third.state := by
    rw [runSteps_append, firstTwo]
    exact third.checked
  let fourth := runBranch third.state ((first.steps ++ second.steps) ++ third.steps) firstThree false false
  have tailRun : runSteps second.state (third.steps ++ fourth.steps) = some fourth.state := by
    rw [runSteps_append, third.checked]
    exact fourth.checked
  have firstTail : runSteps first.state (second.steps ++ (third.steps ++ fourth.steps)) = some fourth.state := by
    rw [runSteps_append, second.checked]
    exact tailRun
  let tt := FoldProjection.afterTrace first.result fourth.state
    (second.steps ++ (third.steps ++ fourth.steps)) firstTail
  let tf := FoldProjection.afterTrace second.result fourth.state (third.steps ++ fourth.steps) tailRun
  let ft := FoldProjection.afterTrace third.result fourth.state fourth.steps fourth.checked
  let joined := joinCofactors fourth.state (context ++ [negate leftOut, rightOut]) a b tt tf ft fourth.result
  refine ⟨joined.state, (((first.steps ++ second.steps) ++ third.steps) ++ fourth.steps) ++ joined.steps,
    ?_, joined.result, ?_⟩
  · rw [runSteps_append, runSteps_append, firstThree]
    simp only [Option.bind_some, fourth.checked]
    exact joined.checked
  · have one := first.count
    have two := second.count
    have three := third.count
    have four := fourth.count
    have five := joined.count
    simp only [List.length_append]
    omega

def laterMaskFlag (rename : Nat → Fin v) (side : Side)
    (position : Fin (laterBuses (parameters := parameters)).length) (channel : Fin parameters.channels) : Literal (Fin v) :=
  mapLiteral rename ((laterMaskBefore side position channel).slots
    (.internal (.flag side (laterBuses (parameters := parameters))[position.val])))

def laterMaskAbsent (rename : Nat → Fin v) (side : Side)
    (position : Fin (laterBuses (parameters := parameters)).length) (channel : Fin parameters.channels) : Literal (Fin v) :=
  mapLiteral rename ((laterMaskBefore side position channel).slots
    (.internal (.absent side (laterBuses (parameters := parameters))[position.val] channel)))

def laterMaskOutput (rename : Nat → Fin v) (side : Side)
    (position : Fin (laterBuses (parameters := parameters)).length) (channel : Fin parameters.channels) : Literal (Fin v) :=
  mapLiteral rename ((laterMaskBefore side position channel).lastID + 1, true)

def laterMaskNativeRows (rename : Nat → Fin v) (side : Side)
    (position : Fin (laterBuses (parameters := parameters)).length) (channel : Fin parameters.channels)
    (checkedPrefix : SourcePrefix (parameters := parameters) rename) :
    XorRows checkedPrefix.state (laterMaskFlag rename side position channel)
      (laterMaskAbsent rename side position channel) (laterMaskOutput rename side position channel) :=
  (xorRowsOriginal _ _ _ (laterMaskRows rename side position channel)).afterTrace
    checkedPrefix.state checkedPrefix.steps checkedPrefix.checked

/-- All XOR gate premises are bound to original source occurrences. Input
transfers must already belong to the same checked source prefix. -/
def laterMaskCongruence (rename : Nat → Fin v) (context : Clause (Fin v))
    (position : Fin (laterBuses (parameters := parameters)).length) (channel : Fin parameters.channels)
    (checkedPrefix : SourcePrefix (parameters := parameters) rename)
    (flagForward : GuardedTransfer checkedPrefix.state context
      (laterMaskFlag rename .healthy position channel) (laterMaskFlag rename .faulty position channel))
    (flagBackward : GuardedTransfer checkedPrefix.state context
      (laterMaskFlag rename .faulty position channel) (laterMaskFlag rename .healthy position channel))
    (absentForward : GuardedTransfer checkedPrefix.state context
      (laterMaskAbsent rename .healthy position channel) (laterMaskAbsent rename .faulty position channel))
    (absentBackward : GuardedTransfer checkedPrefix.state context
      (laterMaskAbsent rename .faulty position channel) (laterMaskAbsent rename .healthy position channel)) :
    SubclauseProjection checkedPrefix.state
      (context ++ [negate (laterMaskOutput rename .healthy position channel),
        laterMaskOutput rename .faulty position channel]) 11 :=
  guardedXor checkedPrefix.state context _ _ _ _ _ _
    (laterMaskNativeRows rename .healthy position channel checkedPrefix)
    (laterMaskNativeRows rename .faulty position channel checkedPrefix)
    flagForward flagBackward absentForward absentBackward

end Controller.NativeProof.SourceStageXor
