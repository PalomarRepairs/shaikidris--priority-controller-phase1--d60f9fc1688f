module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.SourceRoleFrames

@[expose] public section

/-! Native stage proofs carry actual accepted source-input prefixes and stronger
clauses. Pivot-aware mergers reuse a stronger existing row when a requested
pivot has disappeared during normalization. -/
namespace Controller.NativeProof.SourceStageCongruence
open Controller.Native Controller.Native.SourceController Controller.CNF
open Controller.Resolution Controller.Resolution.Cases
open Controller.NativeProof.FoldProjection Controller.NativeProof.SourceFoldProjection
open Controller.NativeProof.SourceFoldOccurrences Controller.NativeProof.SourceCongruence
open Controller.NativeProof.SourceFoldOwners

variable {parameters : Parameters} {v : Nat}

structure SourcePrefix (rename : Nat → Fin v) where
  state : State v
  steps : List (Step v)
  checked : runSteps (initialState (relabel rename (SourceController.formula parameters))) steps = some state

def SourcePrefix.initial (rename : Nat → Fin v) : SourcePrefix (parameters := parameters) rename :=
  ⟨initialState (relabel rename (SourceController.formula parameters)), [], rfl⟩

def SourcePrefix.extend (checkedPrefix : SourcePrefix (parameters := parameters) rename)
    (next : State v) (steps : List (Step v)) (checked : runSteps checkedPrefix.state steps = some next) :
    SourcePrefix (parameters := parameters) rename :=
  ⟨next, checkedPrefix.steps ++ steps, by rw [runSteps_append, checkedPrefix.checked]; exact checked⟩

/-- Both input implication rows retain the actual cofactor context. -/
def guardedChain (state : State v) (context : Clause (Fin v)) (root middle output : Literal (Fin v))
    (first : AvailableSubclause state (context ++ [negate root, middle]))
    (second : AvailableSubclause state (context ++ [negate middle, output])) :
    SubclauseProjection state (context ++ [negate root, output]) 1 := by
  let joined := merge state second.row.id first.row.id middle second.clause first.clause
  have checked := merge_run state second.row.id first.row.id middle second.clause first.clause
    second.row.present first.row.present second.row.bound first.row.bound
  refine ⟨joined.state, joined.steps, checked.1, ⟨joined.clause,
    ⟨joined.rowId, checked.2.1, checked.2.2⟩, ?_⟩, ?_⟩
  · apply merge_subset
    · intro literal member
      have included := second.subset literal member
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at included ⊢
      aesop
    · intro literal member
      have included := first.subset literal member
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at included ⊢
      aesop
  · exact merge_count_le_one state second.row.id first.row.id middle second.clause first.clause

/-- Identity directional certificates carry no fabricated source alias row. -/
def guardedFromDirection (state : State v) (context : Clause (Fin v)) (root input output : Literal (Fin v))
    (direction : DirectionalCertificate state root input)
    (transfer : AvailableSubclause state (context ++ [negate input, output])) :
    SubclauseProjection state (context ++ [negate root, output]) 1 := by
  cases direction with
  | identity same =>
      subst input
      exact ⟨state, [], rfl, transfer, by simp⟩
  | derived row =>
      exact guardedChain state context root input output
        (retarget row (by
          intro literal member
          exact List.mem_append_right _ member)) transfer

def laterTermInputs (side : Side) (position : Fin (laterBuses (parameters := parameters)).length)
    (channel : Fin parameters.channels) : List (Literal Nat) :=
  let bus := (laterBuses (parameters := parameters))[position.val]
  let cursor := termBefore side position channel
  [cursor.slots (.primary (.enable channel)), cursor.slots (.primary (.request bus channel))] ++
    ((List.finRange parameters.buses).filter (fun earlier => earlier < bus)).map fun earlier =>
      cursor.slots (.internal (.mask side earlier channel))

theorem laterTermInputs_nonempty (side : Side) (position : Fin (laterBuses (parameters := parameters)).length)
    (channel : Fin parameters.channels) : laterTermInputs side position channel ≠ [] := by
  simp [laterTermInputs]

/-- The complete source input supplies every private binary AND node in the
actual balanced term allocator. -/
def laterTermTree (rename : Nat → Fin v) (side : Side)
    (position : Fin (laterBuses (parameters := parameters)).length) (channel : Fin parameters.channels) :
    AndTree (initialState (relabel rename (SourceController.formula parameters)))
      (mapLiteral rename (SourceSerialFold.allocate .conjunction (termBefore side position channel).lastID
        (laterTermInputs side position channel)).output)
      ((laterTermInputs side position channel).map (mapLiteral rename)) :=
  allocateForest (initialForest rename (laterTermInputs side position channel))
    (termBefore side position channel).lastID (laterTermInputs_nonempty side position channel)
    (laterTermRows rename side position channel)

def laterTermDirections (rename : Nat → Fin v) (side : Side)
    (position : Fin (laterBuses (parameters := parameters)).length) (channel : Fin parameters.channels)
    (checkedPrefix : SourcePrefix (parameters := parameters) rename) :=
  projectTreeInputs ((laterTermTree rename side position channel).afterTrace checkedPrefix.state checkedPrefix.steps checkedPrefix.checked)

def laterTermAggregate (rename : Nat → Fin v) (side : Side)
    (position : Fin (laterBuses (parameters := parameters)).length) (channel : Fin parameters.channels)
    (checkedPrefix : SourcePrefix (parameters := parameters) rename) :=
  projectTreeLong ((laterTermTree rename side position channel).afterTrace checkedPrefix.state checkedPrefix.steps checkedPrefix.checked)

def laterFlagInputs (side : Side) (position : Fin (laterBuses (parameters := parameters)).length) : List (Literal Nat) :=
  let bus := (laterBuses (parameters := parameters))[position.val]
  let terms := busTerms side bus (busBefore side position)
  (List.finRange parameters.channels).map fun channel => terms.slots (.internal (.term side bus channel))

theorem laterFlagInputs_nonempty (side : Side) (position : Fin (laterBuses (parameters := parameters)).length) :
    laterFlagInputs side position ≠ [] := by
  have target := parameters.bridge.target.isLt
  intro empty
  have length := congrArg List.length empty
  simp [laterFlagInputs] at length
  omega

/-- The OR projection uses the exact polarity-dual tree of the stored allocator. -/
def laterFlagTree (rename : Nat → Fin v) (side : Side)
    (position : Fin (laterBuses (parameters := parameters)).length) :
    let bus := (laterBuses (parameters := parameters))[position.val]
    let terms := busTerms side bus (busBefore side position)
    AndTree (initialState (relabel rename (SourceController.formula parameters)))
      (dualLiteral rename (SourceSerialFold.allocate .disjunction terms.lastID (laterFlagInputs side position)).output)
      ((laterFlagInputs side position).map (dualLiteral rename)) :=
  allocateOrForest (initialOrForest rename (laterFlagInputs side position))
    (busTerms side ((laterBuses (parameters := parameters))[position.val]) (busBefore side position)).lastID
    (laterFlagInputs_nonempty side position) (laterFlagRows rename side position)

def laterFlagDirections (rename : Nat → Fin v) (side : Side)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (checkedPrefix : SourcePrefix (parameters := parameters) rename) :=
  projectTreeInputs ((laterFlagTree rename side position).afterTrace checkedPrefix.state checkedPrefix.steps checkedPrefix.checked)

def laterFlagAggregate (rename : Nat → Fin v) (side : Side)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (checkedPrefix : SourcePrefix (parameters := parameters) rename) :=
  projectTreeLong ((laterFlagTree rename side position).afterTrace checkedPrefix.state checkedPrefix.steps checkedPrefix.checked)

def busMaskStep (side : Side) (bus : Fin parameters.buses) (cursor : Cursor parameters)
    (channel : Fin parameters.channels) : Cursor parameters :=
  let absent := cursor.emitNative (.internal (.absent side bus channel))
    (.not (cursor.slots (.internal (.term side bus channel))))
  absent.emitNative (.internal (.mask side bus channel))
    (.xor (absent.slots (.internal (.flag side bus))) (absent.slots (.internal (.absent side bus channel))))

def laterAbsentBefore (side : Side) (position : Fin (laterBuses (parameters := parameters)).length)
    (channel : Fin parameters.channels) : Cursor parameters :=
  occurrenceCursor (busMaskStep side ((laterBuses (parameters := parameters))[position.val]))
    (busFlag side ((laterBuses (parameters := parameters))[position.val]) (busBefore side position))
    ((List.finRange parameters.channels).take channel.val)

def laterMaskBefore (side : Side) (position : Fin (laterBuses (parameters := parameters)).length)
    (channel : Fin parameters.channels) : Cursor parameters :=
  let bus := (laterBuses (parameters := parameters))[position.val]
  let cursor := laterAbsentBefore side position channel
  cursor.emitNative (.internal (.absent side bus channel)) (.not (cursor.slots (.internal (.term side bus channel))))

theorem bus_mask_occurrence_before_compile (side : Side)
    (position : Fin (laterBuses (parameters := parameters)).length) (channel : Fin parameters.channels) :
    EntriesBefore
      (busMaskStep side ((laterBuses (parameters := parameters))[position.val])
        (laterAbsentBefore side position channel) channel) (compile parameters) := by
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
  exact selected.trans (bus_occurrence_before_compile side position)

theorem later_absent_before_compile (side : Side)
    (position : Fin (laterBuses (parameters := parameters)).length) (channel : Fin parameters.channels) :
    EntriesBefore (laterMaskBefore side position channel) (compile parameters) :=
  (emitNative_before _ _ _).trans (bus_mask_occurrence_before_compile side position channel)

/-- Both NOT rows are original equations at the actual absent emission. -/
def laterAbsentRows (rename : Nat → Fin v) (side : Side)
    (position : Fin (laterBuses (parameters := parameters)).length) (channel : Fin parameters.channels) :
    let bus := (laterBuses (parameters := parameters))[position.val]
    let cursor := laterAbsentBefore side position channel
    OriginalRows (initialState (relabel rename (SourceController.formula parameters))) rename
      (⟨(cursor.lastID + 1, true), .not (cursor.slots (.internal (.term side bus channel)))⟩ : Bounded.Producer Nat) := by
  dsimp only
  apply emitRows
  exact later_absent_before_compile side position channel

/-- All four mask XOR rows come from their concrete original source owner. -/
def laterMaskRows (rename : Nat → Fin v) (side : Side)
    (position : Fin (laterBuses (parameters := parameters)).length) (channel : Fin parameters.channels) :
    let bus := (laterBuses (parameters := parameters))[position.val]
    let cursor := laterMaskBefore side position channel
    OriginalRows (initialState (relabel rename (SourceController.formula parameters))) rename
      (⟨(cursor.lastID + 1, true), .xor (cursor.slots (.internal (.flag side bus)))
        (cursor.slots (.internal (.absent side bus channel)))⟩ : Bounded.Producer Nat) := by
  dsimp only
  apply emitRows
  exact bus_mask_occurrence_before_compile side position channel

def directionAfterTrace (certificate : DirectionalCertificate state root input) (next : State v)
    (steps : List (Step v)) (checked : runSteps state steps = some next) : DirectionalCertificate next root input := by
  cases certificate with
  | identity same => exact .identity same
  | derived row => exact .derived (afterTrace row next steps checked)

inductive GuardedTransfer (state : State v) (context : Clause (Fin v))
    (input output : Literal (Fin v)) : Type
  | identity (same : input = output)
  | derived (row : AvailableSubclause state (context ++ [negate input, output]))

def GuardedTransfer.afterTrace (transfer : GuardedTransfer state context input output)
    (next : State v) (steps : List (Step v)) (checked : runSteps state steps = some next) :
    GuardedTransfer next context input output := by
  cases transfer with
  | identity same => exact .identity same
  | derived row => exact .derived (FoldProjection.afterTrace row next steps checked)

/-- Shared source primary inputs are literal identities, carrying no invented
available implication row. A real root-to-input row already propagates them. -/
def guardedFromRow (state : State v) (context : Clause (Fin v)) (root input output : Literal (Fin v))
    (direction : AvailableSubclause state [negate root, input])
    (transfer : GuardedTransfer state context input output) :
    SubclauseProjection state (context ++ [negate root, output]) 1 := by
  cases transfer with
  | identity same =>
      subst output
      exact ⟨state, [], rfl, retarget direction (fun literal member => List.mem_append_right _ member), by simp⟩
  | derived row =>
      exact guardedChain state context root input output
        (retarget direction (fun literal member => List.mem_append_right _ member)) row

/-- A represented nonunary tree's top original implications provide actual
rows for every root-to-leaf direction. Each shared subtree is visited once. -/
def nonunaryTreeInputs (tree : AndTree state root inputs) (two : 2 ≤ inputs.length) :
    InputProjection state root inputs (2 * tree.nodes) := by
  cases tree with
  | leaf input => simp at two
  | @node left right leftInputs rightInputs leftTree rightTree output rows =>
      let first := projectTreeInputsBelow leftTree state [] rfl root (ofRow rows.leftRow)
      let rightPrefix := FoldProjection.afterTrace (ofRow rows.rightRow) first.state first.steps first.checked
      let second := projectTreeInputsBelow rightTree first.state first.steps first.checked root rightPrefix
      refine ⟨second.state, first.steps ++ second.steps, ?_, ?_, ?_⟩
      · rw [runSteps_append, first.checked]
        exact second.checked
      · intro input member
        if leftMem : input ∈ leftInputs then
          exact FoldProjection.afterTrace (first.results input leftMem) second.state second.steps second.checked
        else
          exact second.results input ((List.mem_append.mp member).resolve_left leftMem)
      · have firstCount := first.count
        have secondCount := second.count
        simp only [List.length_append, AndTree.nodes]
        omega

structure PairPropagation (initial : State v) (context : Clause (Fin v)) (root : Literal (Fin v))
    (pairs : List (Literal (Fin v) × Literal (Fin v))) where
  state : State v
  steps : List (Step v)
  checked : runSteps initial steps = some state
  results : ∀ pair ∈ pairs, AvailableSubclause state (context ++ [negate root, pair.2])
  count : steps.length ≤ pairs.length

def pairPropagationStep {startState : State v} {context : Clause (Fin v)} {root : Literal (Fin v)}
    {rest : List (Literal (Fin v) × Literal (Fin v))} (head : Literal (Fin v) × Literal (Fin v))
    (first : SubclauseProjection startState (context ++ [negate root, head.2]) 1)
    (remaining : PairPropagation first.state context root rest) :
    PairPropagation startState context root (head :: rest) := by
  refine ⟨remaining.state, first.steps ++ remaining.steps, ?_, ?_, ?_⟩
  · rw [runSteps_append, first.checked]
    exact remaining.checked
  · intro pair member
    if same : pair = head then
      subst pair
      exact afterTrace first.result remaining.state remaining.steps remaining.checked
    else
      have tailMem : pair ∈ rest := (List.mem_cons.mp member).resolve_left same
      exact remaining.results pair tailMem
  · have firstCount := first.count
    have tailCount := remaining.count
    simp only [List.length_append, List.length_cons]
    omega

/-- The traversal forms one real merge per paired input at most. Existing
input implications and previous stage clauses retain their actual identifiers. -/
def propagatePairs (state : State v) (context : Clause (Fin v)) (root : Literal (Fin v))
    (pairs : List (Literal (Fin v) × Literal (Fin v)))
    (directions : ∀ pair ∈ pairs, AvailableSubclause state [negate root, pair.1])
    (transfers : ∀ pair ∈ pairs, GuardedTransfer state context pair.1 pair.2) :
    PairPropagation state context root pairs := by
  induction pairs generalizing state with
  | nil => exact ⟨state, [], rfl, by intro pair member; simp at member, by simp⟩
  | cons head rest ih =>
      let first := guardedFromRow state context root head.1 head.2
        (directions head (by simp)) (transfers head (by simp))
      let nextDirections := fun pair (member : pair ∈ rest) => FoldProjection.afterTrace
        (directions pair (List.mem_cons_of_mem _ member)) first.state first.steps first.checked
      let nextTransfers := fun pair (member : pair ∈ rest) => GuardedTransfer.afterTrace
        (transfers pair (List.mem_cons_of_mem _ member)) first.state first.steps first.checked
      let remaining := ih first.state nextDirections nextTransfers
      exact pairPropagationStep head first remaining

/-- A nonunary aggregate has a real projected row. The unary identity case
cannot be converted into a fabricated available clause. -/
def nonunaryAggregate (certificate : AggregateCertificate state output inputs)
    (two : 2 ≤ inputs.length) : AvailableSubclause state (output :: inputs.map negate) := by
  cases certificate with
  | identity => simp at two
  | derived row => exact row

def guardedAnd (state : State v) (context : Clause (Fin v))
    (leftOut rightOut : Literal (Fin v)) (pairs : List (Literal (Fin v) × Literal (Fin v)))
    (two : 2 ≤ pairs.length)
    (leftTree : AndTree state leftOut (pairs.map Prod.fst))
    (rightTree : AndTree state rightOut (pairs.map Prod.snd))
    (transfers : ∀ pair ∈ pairs, GuardedTransfer state context pair.1 pair.2) :
    SubclauseProjection state (context ++ [negate leftOut, rightOut])
      (2 * leftTree.nodes + 2 * rightTree.nodes + 2 * pairs.length) := by
  let first := nonunaryTreeInputs leftTree (by simpa using two)
  let second := projectTreeLong (rightTree.afterTrace first.state first.steps first.checked)
  let directions := fun pair (member : pair ∈ pairs) => FoldProjection.afterTrace
    (first.results pair.1 (List.mem_map_of_mem (f := Prod.fst) member)) second.state second.steps second.checked
  let currentTransfers := fun pair (member : pair ∈ pairs) =>
    GuardedTransfer.afterTrace (GuardedTransfer.afterTrace (transfers pair member) first.state first.steps first.checked)
      second.state second.steps second.checked
  let third := propagatePairs second.state context leftOut pairs directions currentTransfers
  let aggregate := nonunaryAggregate
    (second.result.afterTrace third.state third.steps third.checked) (by simpa using two)
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
  let fourth := dischargeInputs third.state (pairs.map Prod.snd) target conflict propagations
  refine ⟨fourth.state, ((first.steps ++ second.steps) ++ third.steps) ++ fourth.steps, ?_, fourth.result, ?_⟩
  · simp only [runSteps_append, first.checked, second.checked, third.checked, Option.bind_some]
    exact fourth.checked
  · have firstCount := first.count
    have secondCount : second.steps.length ≤ 2 * rightTree.nodes := by
      simpa only [second, AndTree.afterTrace_nodes] using second.count
    have thirdCount := third.count
    have fourthCount := fourth.count
    simp only [List.length_append, List.length_map] at *
    omega

def laterTermPairs (rename : Nat → Fin v)
    (position : Fin (laterBuses (parameters := parameters)).length) (channel : Fin parameters.channels) :
    List (Literal (Fin v) × Literal (Fin v)) :=
  ((laterTermInputs .healthy position channel).map (mapLiteral rename)).zip
    ((laterTermInputs .faulty position channel).map (mapLiteral rename))

theorem laterTermPairs_fst (rename : Nat → Fin v)
    (position : Fin (laterBuses (parameters := parameters)).length) (channel : Fin parameters.channels) :
    (laterTermPairs rename position channel).map Prod.fst =
      (laterTermInputs .healthy position channel).map (mapLiteral rename) := by
  apply List.map_fst_zip
  simp [laterTermInputs]

theorem laterTermPairs_snd (rename : Nat → Fin v)
    (position : Fin (laterBuses (parameters := parameters)).length) (channel : Fin parameters.channels) :
    (laterTermPairs rename position channel).map Prod.snd =
      (laterTermInputs .faulty position channel).map (mapLiteral rename) := by
  apply List.map_snd_zip
  simp [laterTermInputs]

theorem laterTermPairs_two (rename : Nat → Fin v)
    (position : Fin (laterBuses (parameters := parameters)).length) (channel : Fin parameters.channels) :
    2 ≤ (laterTermPairs rename position channel).length := by
  have same := congrArg List.length (laterTermPairs_fst rename position channel)
  simp [laterTermInputs] at same
  omega

def laterTermOutput (rename : Nat → Fin v) (side : Side)
    (position : Fin (laterBuses (parameters := parameters)).length) (channel : Fin parameters.channels) : Literal (Fin v) :=
  mapLiteral rename (SourceSerialFold.allocate .conjunction (termBefore side position channel).lastID
    (laterTermInputs side position channel)).output

/-- An actual later-bus term stage consumes earlier guarded direction
certificates in the checked checkedPrefix. Identity certificates cover shared primary
inputs. All new gate rows come from the concrete original source traversal. -/
def laterTermCongruence (rename : Nat → Fin v) (context : Clause (Fin v))
    (position : Fin (laterBuses (parameters := parameters)).length) (channel : Fin parameters.channels)
    (checkedPrefix : SourcePrefix (parameters := parameters) rename)
    (transfers : ∀ pair ∈ laterTermPairs rename position channel,
      GuardedTransfer checkedPrefix.state context pair.1 pair.2) :
    SubclauseProjection checkedPrefix.state
      (context ++ [negate (laterTermOutput rename .healthy position channel),
        laterTermOutput rename .faulty position channel])
      (6 * (laterTermPairs rename position channel).length) := by
  let pairs := laterTermPairs rename position channel
  let left : AndTree checkedPrefix.state (laterTermOutput rename .healthy position channel) (pairs.map Prod.fst) := by
    dsimp only [pairs]
    rw [laterTermPairs_fst]
    exact (laterTermTree rename .healthy position channel).afterTrace checkedPrefix.state checkedPrefix.steps checkedPrefix.checked
  let right : AndTree checkedPrefix.state (laterTermOutput rename .faulty position channel) (pairs.map Prod.snd) := by
    dsimp only [pairs]
    rw [laterTermPairs_snd]
    exact (laterTermTree rename .faulty position channel).afterTrace checkedPrefix.state checkedPrefix.steps checkedPrefix.checked
  let result := guardedAnd checkedPrefix.state context _ _ pairs
    (laterTermPairs_two rename position channel) left right transfers
  refine ⟨result.state, result.steps, result.checked, result.result, ?_⟩
  have count := result.count
  have leftSize := left.nodes_leaves
  have rightSize := right.nodes_leaves
  simp only [List.length_map] at leftSize rightSize
  change result.steps.length ≤ 6 * pairs.length
  omega

end Controller.NativeProof.SourceStageCongruence
