module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.SourceStageCongruence

@[expose] public section

/-! Polarity consumers join actual source rows and checked earlier directional
clauses. Identity certificates and absent pivots reuse existing rows without
inserting weakened conclusions. -/
namespace Controller.NativeProof.SourceStagePolarity
open Controller.Native Controller.Native.SourceController Controller.CNF
open Controller.Resolution Controller.Resolution.Cases
open Controller.NativeProof.FoldProjection Controller.NativeProof.SourceFoldProjection
open Controller.NativeProof.SourceFoldOccurrences Controller.NativeProof.SourceStageCongruence

variable {parameters : Parameters} {v : Nat}

/-- Negating a guarded direction reverses its endpoints. -/
def GuardedTransfer.dual (transfer : GuardedTransfer state context input output) :
    GuardedTransfer state context (negate output) (negate input) := by
  cases transfer with
  | identity same => exact .identity (congrArg negate same.symm)
  | derived row =>
      exact .derived (retarget row (by
        intro literal member
        simp only [negate_negate, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member ⊢
        aesop))

structure NotRows (state : State v) (input output : Literal (Fin v)) where
  positive : AvailableSubclause state [output, input]
  negative : AvailableSubclause state [negate output, negate input]

def notRowsOriginal {rename : Nat → Fin v} (input output : Literal Nat)
    (rows : OriginalRows state rename ⟨output, .not input⟩) :
    NotRows state (mapLiteral rename input) (mapLiteral rename output) where
  positive := ofRow (rows.row ⟨0, by change 0 < 2; decide⟩)
  negative := ofRow (rows.row ⟨1, by change 1 < 2; decide⟩)

def NotRows.afterTrace (rows : NotRows state input output) (next : State v)
    (steps : List (Step v)) (checked : runSteps state steps = some next) : NotRows next input output where
  positive := FoldProjection.afterTrace rows.positive next steps checked
  negative := FoldProjection.afterTrace rows.negative next steps checked

/-- The transfer is contravariant: right input implies left input. -/
def guardedNot (state : State v) (context : Clause (Fin v))
    (leftInput rightInput leftOut rightOut : Literal (Fin v))
    (left : NotRows state leftInput leftOut) (right : NotRows state rightInput rightOut)
    (transfer : GuardedTransfer state context rightInput leftInput) :
    SubclauseProjection state (context ++ [negate leftOut, rightOut]) 2 := by
  let first := guardedFromRow state context leftOut (negate leftInput) (negate rightInput)
    left.negative (GuardedTransfer.dual transfer)
  let rightRow := FoldProjection.afterTrace right.positive first.state first.steps first.checked
  let adapted : AvailableSubclause first.state (context ++ [negate (negate rightInput), rightOut]) :=
    retarget rightRow (by
      intro literal member
      simp only [negate_negate, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member ⊢
      aesop)
  let second := guardedChain first.state context leftOut (negate rightInput) rightOut first.result adapted
  refine ⟨second.state, first.steps ++ second.steps, ?_, second.result, ?_⟩
  · rw [runSteps_append, first.checked]
    exact second.checked
  · have firstCount := first.count
    have secondCount := second.count
    simp only [List.length_append]
    omega

def laterAbsentInput (rename : Nat → Fin v) (side : Side)
    (position : Fin (laterBuses (parameters := parameters)).length) (channel : Fin parameters.channels) : Literal (Fin v) :=
  mapLiteral rename ((laterAbsentBefore side position channel).slots
    (.internal (.term side (laterBuses (parameters := parameters))[position.val] channel)))

def laterAbsentOutput (rename : Nat → Fin v) (side : Side)
    (position : Fin (laterBuses (parameters := parameters)).length) (channel : Fin parameters.channels) : Literal (Fin v) :=
  mapLiteral rename ((laterAbsentBefore side position channel).lastID + 1, true)

/-- Both actual stored absent equations are transported through the accepted
source prefix; neither directional NOT clause is supplied as an assumption. -/
def laterAbsentNativeRows (rename : Nat → Fin v) (side : Side)
    (position : Fin (laterBuses (parameters := parameters)).length) (channel : Fin parameters.channels)
    (checkedPrefix : SourcePrefix (parameters := parameters) rename) :
    NotRows checkedPrefix.state (laterAbsentInput rename side position channel)
      (laterAbsentOutput rename side position channel) :=
  (notRowsOriginal _ _ (laterAbsentRows rename side position channel)).afterTrace
    checkedPrefix.state checkedPrefix.steps checkedPrefix.checked

def laterAbsentCongruence (rename : Nat → Fin v) (context : Clause (Fin v))
    (position : Fin (laterBuses (parameters := parameters)).length) (channel : Fin parameters.channels)
    (checkedPrefix : SourcePrefix (parameters := parameters) rename)
    (transfer : GuardedTransfer checkedPrefix.state context
      (laterAbsentInput rename .faulty position channel) (laterAbsentInput rename .healthy position channel)) :
    SubclauseProjection checkedPrefix.state
      (context ++ [negate (laterAbsentOutput rename .healthy position channel),
        laterAbsentOutput rename .faulty position channel]) 2 :=
  guardedNot checkedPrefix.state context _ _ _ _
    (laterAbsentNativeRows rename .healthy position channel checkedPrefix)
    (laterAbsentNativeRows rename .faulty position channel checkedPrefix) transfer

structure GuardedProjection (initial : State v) (context : Clause (Fin v))
    (input output : Literal (Fin v)) (budget : Nat) where
  state : State v
  steps : List (Step v)
  checked : runSteps initial steps = some state
  result : GuardedTransfer state context input output
  count : steps.length ≤ budget

theorem treeRoot_singleton (tree : AndTree state root inputs) (one : inputs.length = 1)
    (member : input ∈ inputs) : root = input := by
  cases tree with
  | leaf value => simpa using (List.mem_singleton.mp member).symm
  | @node left right leftInputs rightInputs leftTree rightTree output rows =>
      have leftSize := leftTree.nodes_leaves
      have rightSize := rightTree.nodes_leaves
      simp only [List.length_append] at one
      omega

/-- Unary source aliases reuse the earlier transfer certificate. Binary and
larger represented folds use the actual counted projection/merge traversal. -/
def guardedAndPositive (state : State v) (context : Clause (Fin v))
    (leftOut rightOut : Literal (Fin v)) (pairs : List (Literal (Fin v) × Literal (Fin v)))
    (nonempty : pairs ≠ [])
    (leftTree : AndTree state leftOut (pairs.map Prod.fst))
    (rightTree : AndTree state rightOut (pairs.map Prod.snd))
    (transfers : ∀ pair ∈ pairs, GuardedTransfer state context pair.1 pair.2) :
    GuardedProjection state context leftOut rightOut (6 * pairs.length) := by
  match pairs with
  | [] => exact False.elim (nonempty rfl)
  | [pair] =>
      have leftEq := treeRoot_singleton (input := pair.1) leftTree (by simp) (by simp)
      have rightEq := treeRoot_singleton (input := pair.2) rightTree (by simp) (by simp)
      let transfer := transfers pair (by simp)
      cases transfer with
      | identity same =>
          exact ⟨state, [], rfl, .identity (leftEq.trans (same.trans rightEq.symm)), by simp⟩
      | derived row =>
          refine ⟨state, [], rfl, .derived (retarget row ?_), by simp⟩
          intro literal member
          simpa only [leftEq, rightEq] using member
  | first :: second :: rest =>
      let joined := guardedAnd state context leftOut rightOut (first :: second :: rest) (by simp)
        leftTree rightTree transfers
      refine ⟨joined.state, joined.steps, joined.checked, .derived joined.result, ?_⟩
      have count := joined.count
      have leftSize := leftTree.nodes_leaves
      have rightSize := rightTree.nodes_leaves
      simp only [List.length_map] at leftSize rightSize
      omega

def dualPair (pair : Literal (Fin v) × Literal (Fin v)) : Literal (Fin v) × Literal (Fin v) :=
  (negate pair.2, negate pair.1)

/-- OR congruence is the actual polarity dual of guarded AND. The reflected
pair is selected by decidable list membership, including repeated inputs. -/
def guardedOr (state : State v) (context : Clause (Fin v))
    (leftOut rightOut : Literal (Fin v)) (pairs : List (Literal (Fin v) × Literal (Fin v)))
    (nonempty : pairs ≠ [])
    (leftTree : AndTree state (negate leftOut) ((pairs.map Prod.fst).map negate))
    (rightTree : AndTree state (negate rightOut) ((pairs.map Prod.snd).map negate))
    (transfers : ∀ pair ∈ pairs, GuardedTransfer state context pair.1 pair.2) :
    GuardedProjection state context leftOut rightOut (6 * pairs.length) := by
  let reflected := pairs.map dualPair
  let reflectedLeft : AndTree state (negate rightOut) (reflected.map Prod.fst) := by
    simpa only [reflected, List.map_map, dualPair, Function.comp_def] using rightTree
  let reflectedRight : AndTree state (negate leftOut) (reflected.map Prod.snd) := by
    simpa only [reflected, List.map_map, dualPair, Function.comp_def] using leftTree
  let reflectedTransfers := fun pair (member : pair ∈ reflected) =>
    let selected := mappedChoice dualPair pair pairs member
    let transfer := GuardedTransfer.dual (transfers selected.val selected.property.1)
    (show GuardedTransfer state context pair.1 pair.2 from by
      have equal := selected.property.2
      simpa only [← equal, dualPair] using transfer)
  let joined := guardedAndPositive state context _ _ reflected
    (by intro empty; apply nonempty; exact List.map_eq_nil_iff.mp empty)
    reflectedLeft reflectedRight reflectedTransfers
  refine ⟨joined.state, joined.steps, joined.checked, ?_, ?_⟩
  · cases joined.result with
    | identity same => exact .identity (by simpa only [negate_negate] using congrArg negate same.symm)
    | derived row =>
        exact .derived (retarget row (by
          intro literal member
          simp only [negate_negate, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member ⊢
          aesop))
  · simpa only [reflected, List.length_map] using joined.count

def laterFlagPairs (rename : Nat → Fin v)
    (position : Fin (laterBuses (parameters := parameters)).length) :
    List (Literal (Fin v) × Literal (Fin v)) :=
  ((laterFlagInputs .healthy position).map (mapLiteral rename)).zip
    ((laterFlagInputs .faulty position).map (mapLiteral rename))

theorem laterFlagPairs_fst (rename : Nat → Fin v)
    (position : Fin (laterBuses (parameters := parameters)).length) :
    (laterFlagPairs rename position).map Prod.fst = (laterFlagInputs .healthy position).map (mapLiteral rename) := by
  apply List.map_fst_zip
  simp [laterFlagInputs]

theorem laterFlagPairs_snd (rename : Nat → Fin v)
    (position : Fin (laterBuses (parameters := parameters)).length) :
    (laterFlagPairs rename position).map Prod.snd = (laterFlagInputs .faulty position).map (mapLiteral rename) := by
  apply List.map_snd_zip
  simp [laterFlagInputs]

theorem laterFlagPairs_nonempty (rename : Nat → Fin v)
    (position : Fin (laterBuses (parameters := parameters)).length) : laterFlagPairs rename position ≠ [] := by
  intro empty
  have equality := laterFlagPairs_fst rename position
  rw [empty] at equality
  have impossible : laterFlagInputs .healthy position = [] := by
    simpa using equality.symm
  exact laterFlagInputs_nonempty .healthy position impossible

def laterFlagOutput (rename : Nat → Fin v) (side : Side)
    (position : Fin (laterBuses (parameters := parameters)).length) : Literal (Fin v) :=
  let bus := (laterBuses (parameters := parameters))[position.val]
  let terms := busTerms side bus (busBefore side position)
  mapLiteral rename (SourceSerialFold.allocate .disjunction terms.lastID (laterFlagInputs side position)).output

/-- The complete OR flag stage consumes actual earlier term certificates.
A single channel reuses its term handle; larger buses project their represented
binary source allocators and emit only checked counted mergers. -/
def laterFlagCongruence (rename : Nat → Fin v) (context : Clause (Fin v))
    (position : Fin (laterBuses (parameters := parameters)).length)
    (checkedPrefix : SourcePrefix (parameters := parameters) rename)
    (transfers : ∀ pair ∈ laterFlagPairs rename position,
      GuardedTransfer checkedPrefix.state context pair.1 pair.2) :
    GuardedProjection checkedPrefix.state context (laterFlagOutput rename .healthy position)
      (laterFlagOutput rename .faulty position) (6 * (laterFlagPairs rename position).length) := by
  let left : AndTree checkedPrefix.state (negate (laterFlagOutput rename .healthy position))
      (((laterFlagPairs rename position).map Prod.fst).map negate) := by
    rw [laterFlagPairs_fst]
    have actual : AndTree checkedPrefix.state (negate (laterFlagOutput rename .healthy position))
        ((laterFlagInputs .healthy position).map (fun literal => negate (mapLiteral rename literal))) :=
      (laterFlagTree rename .healthy position).afterTrace checkedPrefix.state checkedPrefix.steps checkedPrefix.checked
    simpa only [List.map_map, Function.comp_def] using actual
  let right : AndTree checkedPrefix.state (negate (laterFlagOutput rename .faulty position))
      (((laterFlagPairs rename position).map Prod.snd).map negate) := by
    rw [laterFlagPairs_snd]
    have actual : AndTree checkedPrefix.state (negate (laterFlagOutput rename .faulty position))
        ((laterFlagInputs .faulty position).map (fun literal => negate (mapLiteral rename literal))) :=
      (laterFlagTree rename .faulty position).afterTrace checkedPrefix.state checkedPrefix.steps checkedPrefix.checked
    simpa only [List.map_map, Function.comp_def] using actual
  exact guardedOr checkedPrefix.state context _ _ _ (laterFlagPairs_nonempty rename position) left right transfers

def unaryTransfers (state : State v) (context : Clause (Fin v))
    (pair : Literal (Fin v) × Literal (Fin v))
    (transfer : GuardedTransfer state context pair.1 pair.2) :
    ∀ query ∈ [pair], GuardedTransfer state context query.1 query.2 := by
  intro query member
  have same : query = pair := by simpa using member
  subst query
  exact transfer

@[simp] theorem guardedAndPositive_unary (state : State v) (context : Clause (Fin v))
    (leftOut rightOut : Literal (Fin v)) (pairs : List (Literal (Fin v) × Literal (Fin v)))
    (nonempty : pairs ≠ [])
    (leftTree : AndTree state leftOut (pairs.map Prod.fst))
    (rightTree : AndTree state rightOut (pairs.map Prod.snd))
    (transfers : ∀ pair ∈ pairs, GuardedTransfer state context pair.1 pair.2)
    (one : pairs.length = 1) :
    (guardedAndPositive state context leftOut rightOut pairs nonempty leftTree rightTree transfers).steps.length = 0 := by
  cases pairs with
  | nil => simp at one
  | cons pair rest =>
    have empty : rest = [] := List.length_eq_zero_iff.mp (by simpa using one)
    subst rest
    let transfer := transfers pair (by simp)
    have equal : transfers = unaryTransfers state context pair transfer := by
      funext query member
      have same : query = pair := by simpa using member
      subst query
      rfl
    rw [equal]
    cases transferEq : transfer <;> simp only [guardedAndPositive, unaryTransfers, transferEq, List.length_nil]

@[simp] theorem guardedOr_unary (state : State v) (context : Clause (Fin v))
    (leftOut rightOut : Literal (Fin v)) (pairs : List (Literal (Fin v) × Literal (Fin v)))
    (nonempty : pairs ≠ [])
    (leftTree : AndTree state (negate leftOut) ((pairs.map Prod.fst).map negate))
    (rightTree : AndTree state (negate rightOut) ((pairs.map Prod.snd).map negate))
    (transfers : ∀ pair ∈ pairs, GuardedTransfer state context pair.1 pair.2)
    (one : pairs.length = 1) :
    (guardedOr state context leftOut rightOut pairs nonempty leftTree rightTree transfers).steps.length = 0 := by
  unfold guardedOr
  dsimp only
  apply guardedAndPositive_unary
  simpa only [List.length_map] using one

end Controller.NativeProof.SourceStagePolarity
