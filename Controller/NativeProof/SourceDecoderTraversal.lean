module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.SourceDecoderSchedule
public import Controller.NativeProof.SourceQualifierSchedule
public import Controller.NativeProof.SourceMixedSchedule
public import Controller.Resolution.Rebase
public import Controller.NativeProof.SourceDriveZero

public import Mathlib.Tactic.Ring

@[expose] public section

/-! Topological decoder certificates use actual guard and fold producers.
Guard chains retain their stored label order and original clause IDs. -/
namespace Controller.NativeProof.SourceDecoderTraversal
open Controller.CNF Controller.Resolution Controller.Native Controller.Native.SourceController
open Controller.NativeProof.FoldProjection Controller.NativeProof.SourceFoldProjection
open Controller.NativeProof.SourceFoldProvenance Controller.NativeProof.SourceDecoderSchedule
open Controller.NativeProof.SourceStageCongruence Controller.NativeProof.SourceBusAdvance
open Controller.NativeProof.SourceBusSchedule Controller.NativeProof.SourceFoldOccurrences
variable {parameters : Parameters} {v : Nat}

def guardLeft (side : Side) (node : Fin parameters.decoder.nodeCount)
    (child : Fin node.val) (labels : List (Fin parameters.channels)) (index : Fin labels.length) : Literal Nat :=
  (decoderGuardBefore side node child labels index).1

def guardRight (side : Side) (node : Fin parameters.decoder.nodeCount)
    (child : Fin node.val) (labels : List (Fin parameters.channels)) (index : Fin labels.length) : Literal Nat :=
  negate ((decoderGuardBefore side node child labels index).2.slots
    (.internal (.qualifier side labels[index.val])))

def guardOutput (side : Side) (node : Fin parameters.decoder.nodeCount)
    (child : Fin node.val) (labels : List (Fin parameters.channels)) (index : Fin labels.length) : Literal Nat :=
  ((decoderGuardBefore side node child labels index).2.lastID + 1, true)

/-- Both leaves stop at the actual current handles; no preceding graph is unfolded. -/
def guardTreeOriginal (rename : Nat → Fin v) (side : Side)
    (node : Fin parameters.decoder.nodeCount) (child : Fin node.val)
    (labels : List (Fin parameters.channels)) (shape : parameters.decoder.node node = .guard child labels)
    (index : Fin labels.length) :
    AndTree (initialState (relabel rename (formula parameters)))
      (mapLiteral rename (guardOutput side node child labels index))
      [mapLiteral rename (guardLeft side node child labels index),
       mapLiteral rename (guardRight side node child labels index)] :=
  .node (.leaf _) (.leaf _) _
    (binaryRows (guardLeft side node child labels index) (guardRight side node child labels index)
      (guardOutput side node child labels index) (decoderGuardRows rename side node child labels shape index))

theorem guardTreeOriginal_supported (rename : Nat → Fin v) (side : Side)
    (node : Fin parameters.decoder.nodeCount) (child : Fin node.val)
    (labels : List (Fin parameters.channels)) (shape : parameters.decoder.node node = .guard child labels)
    (index : Fin labels.length) :
    TreeOriginals (AllowedOriginal (parameters := parameters) rename)
      (guardTreeOriginal rename side node child labels shape index) := by
  refine ⟨trivial, trivial, ?_⟩
  apply binaryRows_originals
  intro rowIndex
  exact decoderGuardRows_allowed rename side node child labels shape index
    ⟨rowIndex.val, by change rowIndex.val < 3; exact rowIndex.isLt⟩

def guardTree (rename : Nat → Fin v) (side : Side)
    (node : Fin parameters.decoder.nodeCount) (child : Fin node.val)
    (labels : List (Fin parameters.channels)) (shape : parameters.decoder.node node = .guard child labels)
    (index : Fin labels.length) (prefixState : SourcePrefix (parameters := parameters) rename) :
    AndTree prefixState.state (mapLiteral rename (guardOutput side node child labels index))
      [mapLiteral rename (guardLeft side node child labels index),
       mapLiteral rename (guardRight side node child labels index)] :=
  (guardTreeOriginal rename side node child labels shape index).afterTrace
    prefixState.state prefixState.steps prefixState.checked

theorem guardTree_supported (rename : Nat → Fin v) (side : Side)
    (node : Fin parameters.decoder.nodeCount) (child : Fin node.val)
    (labels : List (Fin parameters.channels)) (shape : parameters.decoder.node node = .guard child labels)
    (index : Fin labels.length) (prefixState : SourcePrefix (parameters := parameters) rename) :
    TreeOriginals (AllowedOriginal (parameters := parameters) rename)
      (guardTree rename side node child labels shape index prefixState) :=
  treeOriginals_afterTrace _ (guardTreeOriginal rename side node child labels shape index)
    (guardTreeOriginal_supported rename side node child labels shape index)
    prefixState.state prefixState.steps prefixState.checked


def guardPairs (rename : Nat → Fin v) (node : Fin parameters.decoder.nodeCount)
    (child : Fin node.val) (labels : List (Fin parameters.channels)) (index : Fin labels.length) :
    List (Literal (Fin v) × Literal (Fin v)) :=
  [(mapLiteral rename (guardLeft .healthy node child labels index),
    mapLiteral rename (guardLeft .faulty node child labels index)),
   (mapLiteral rename (guardRight .healthy node child labels index),
    mapLiteral rename (guardRight .faulty node child labels index))]

def guardInputDirection (state : State v) (context : Clause (Fin v))
    (first second : Literal (Fin v) × Literal (Fin v))
    (firstPair : DirectionPair state context first.1 first.2)
    (secondPair : DirectionPair state context second.1 second.2)
    (pair : Literal (Fin v) × Literal (Fin v)) (member : pair ∈ [first, second]) :
    DirectionPair state context pair.1 pair.2 := by
  by_cases same : pair = first
  · subst pair
    exact firstPair
  · have last : pair = second := by simpa only [List.mem_cons, List.not_mem_nil, or_false, same, false_or] using member
    subst pair
    exact secondPair

/-- The binary runtime kernel keeps source cursor proofs outside the paired
AND computation. It emits exactly the existing two-input paired macro. -/
def pairedGuardKernel (state : State v) (context : Clause (Fin v))
    (first second : Literal (Fin v) × Literal (Fin v)) (leftOut rightOut : Literal (Fin v))
    (leftTree : AndTree state leftOut [first.1, second.1])
    (rightTree : AndTree state rightOut [first.2, second.2])
    (previous : DirectionPair state context first.1 first.2)
    (qualifier : DirectionPair state context second.1 second.2) :
    PairedProjection state context leftOut rightOut 24 :=
  pairedAnd state context leftOut rightOut [first, second] (by simp) leftTree rightTree
    (fun pair member => guardInputDirection state context first second previous qualifier pair member)

theorem pairedGuardKernel_eq (state : State v) (context : Clause (Fin v))
    (first second : Literal (Fin v) × Literal (Fin v)) (leftOut rightOut : Literal (Fin v))
    (leftTree : AndTree state leftOut [first.1, second.1])
    (rightTree : AndTree state rightOut [first.2, second.2])
    (previous : DirectionPair state context first.1 first.2)
    (qualifier : DirectionPair state context second.1 second.2) :
    pairedGuardKernel state context first second leftOut rightOut leftTree rightTree previous qualifier =
      pairedAnd state context leftOut rightOut [first, second] (by simp) leftTree rightTree
        (fun pair member => guardInputDirection state context first second previous qualifier pair member) := rfl

/-- One stored guard producer is compared using its actual original binary rows. -/
def pairedGuard (rename : Nat → Fin v) (context : Clause (Fin v))
    (node : Fin parameters.decoder.nodeCount) (child : Fin node.val)
    (labels : List (Fin parameters.channels)) (shape : parameters.decoder.node node = .guard child labels)
    (index : Fin labels.length) (prefixState : SourcePrefix (parameters := parameters) rename)
    (previous : DirectionPair prefixState.state context
      (mapLiteral rename (guardLeft .healthy node child labels index))
      (mapLiteral rename (guardLeft .faulty node child labels index)))
    (qualifier : DirectionPair prefixState.state context
      (mapLiteral rename (guardRight .healthy node child labels index))
      (mapLiteral rename (guardRight .faulty node child labels index))) :
    PairedProjection prefixState.state context
      (mapLiteral rename (guardOutput .healthy node child labels index))
      (mapLiteral rename (guardOutput .faulty node child labels index)) 24 := by
  exact pairedGuardKernel prefixState.state context
    (mapLiteral rename (guardLeft .healthy node child labels index),
     mapLiteral rename (guardLeft .faulty node child labels index))
    (mapLiteral rename (guardRight .healthy node child labels index),
     mapLiteral rename (guardRight .faulty node child labels index)) _ _
    (guardTree rename .healthy node child labels shape index prefixState)
    (guardTree rename .faulty node child labels shape index prefixState) previous qualifier


theorem guardInputDirection_supported (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (context : Clause (Fin v)) (first second : Literal (Fin v) × Literal (Fin v))
    (firstPair : DirectionPair prefixState.state context first.1 first.2)
    (secondPair : DirectionPair prefixState.state context second.1 second.2)
    (firstOrigin : DirectionPairOrigin rename prefixState firstPair)
    (secondOrigin : DirectionPairOrigin rename prefixState secondPair)
    (pair : Literal (Fin v) × Literal (Fin v)) (member : pair ∈ [first, second]) :
    DirectionPairOrigin rename prefixState
      (guardInputDirection prefixState.state context first second firstPair secondPair pair member) := by
  by_cases same : pair = first
  · subst pair
    dsimp only [guardInputDirection]
    rw [dite_eq_left rfl]
    exact firstOrigin
  · have last : pair = second := by
      simpa only [List.mem_cons, List.not_mem_nil, or_false, same, false_or] using member
    subst pair
    dsimp only [guardInputDirection]
    rw [dite_eq_right same]
    exact secondOrigin

theorem pairedGuardKernel_supported (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (context : Clause (Fin v)) (first second : Literal (Fin v) × Literal (Fin v))
    (leftOut rightOut : Literal (Fin v))
    (leftTree : AndTree prefixState.state leftOut [first.1, second.1])
    (rightTree : AndTree prefixState.state rightOut [first.2, second.2])
    (previous : DirectionPair prefixState.state context first.1 first.2)
    (qualifier : DirectionPair prefixState.state context second.1 second.2)
    (leftOriginal : TreeOriginals (AllowedOriginal (parameters := parameters) rename) leftTree)
    (rightOriginal : TreeOriginals (AllowedOriginal (parameters := parameters) rename) rightTree)
    (prefixOriginal : PrefixOriginalSupport rename prefixState)
    (previousOriginal : DirectionPairOrigin rename prefixState previous)
    (qualifierOriginal : DirectionPairOrigin rename prefixState qualifier) :
    PairedProjectionOriginalSupport rename prefixState
      (pairedGuardKernel prefixState.state context first second leftOut rightOut
        leftTree rightTree previous qualifier) :=
  pairedAnd_supported rename prefixState context leftOut rightOut [first, second] (by simp)
    leftTree rightTree
    (fun pair member => guardInputDirection prefixState.state context first second previous qualifier pair member)
    leftOriginal rightOriginal prefixOriginal
    (fun pair member => guardInputDirection_supported rename prefixState context first second previous qualifier
      previousOriginal qualifierOriginal pair member)

theorem pairedGuard_supported (rename : Nat → Fin v) (context : Clause (Fin v))
    (node : Fin parameters.decoder.nodeCount) (child : Fin node.val)
    (labels : List (Fin parameters.channels)) (shape : parameters.decoder.node node = .guard child labels)
    (index : Fin labels.length) (prefixState : SourcePrefix (parameters := parameters) rename)
    (previous : DirectionPair prefixState.state context
      (mapLiteral rename (guardLeft .healthy node child labels index))
      (mapLiteral rename (guardLeft .faulty node child labels index)))
    (qualifier : DirectionPair prefixState.state context
      (mapLiteral rename (guardRight .healthy node child labels index))
      (mapLiteral rename (guardRight .faulty node child labels index)))
    (prefixOrigin : PrefixOriginalSupport rename prefixState)
    (previousOrigin : DirectionPairOrigin rename prefixState previous)
    (qualifierOrigin : DirectionPairOrigin rename prefixState qualifier) :
    PairedProjectionOriginalSupport rename prefixState
      (pairedGuard rename context node child labels shape index prefixState previous qualifier) := by
  let first : Literal (Fin v) × Literal (Fin v) :=
    (mapLiteral rename (guardLeft .healthy node child labels index),
     mapLiteral rename (guardLeft .faulty node child labels index))
  let second : Literal (Fin v) × Literal (Fin v) :=
    (mapLiteral rename (guardRight .healthy node child labels index),
     mapLiteral rename (guardRight .faulty node child labels index))
  let leftOut := mapLiteral rename (guardOutput .healthy node child labels index)
  let rightOut := mapLiteral rename (guardOutput .faulty node child labels index)
  let leftTree : AndTree prefixState.state leftOut [first.1, second.1] :=
    guardTree rename .healthy node child labels shape index prefixState
  let rightTree : AndTree prefixState.state rightOut [first.2, second.2] :=
    guardTree rename .faulty node child labels shape index prefixState
  have leftOriginal : TreeOriginals (AllowedOriginal (parameters := parameters) rename) leftTree :=
    guardTree_supported rename .healthy node child labels shape index prefixState
  have rightOriginal : TreeOriginals (AllowedOriginal (parameters := parameters) rename) rightTree :=
    guardTree_supported rename .faulty node child labels shape index prefixState
  have actual : PairedProjectionOriginalSupport rename prefixState
      (pairedGuardKernel prefixState.state context first second leftOut rightOut
        leftTree rightTree previous qualifier) :=
    pairedGuardKernel_supported rename prefixState context first second leftOut rightOut
      leftTree rightTree previous qualifier leftOriginal rightOriginal prefixOrigin previousOrigin qualifierOrigin
  dsimp only [pairedGuard]
  exact actual



theorem guardFold_slots (side : Side) (node : Fin parameters.decoder.nodeCount)
    (pairs : List (Fin parameters.channels × Nat)) (state : Literal Nat × Cursor parameters)
    (query : Controller.Native.Variable parameters) :
    (pairs.foldl (decoderGuardStep side node) state).2.slots query = state.2.slots query := by
  induction pairs generalizing state with
  | nil => rfl
  | cons head rest ih =>
      rw [List.foldl_cons, ih]
      rfl

theorem guardCursor_qualifier (side : Side) (node : Fin parameters.decoder.nodeCount)
    (child : Fin node.val) (labels : List (Fin parameters.channels)) (index : Fin labels.length)
    (querySide : Side) (channel : Fin parameters.channels) :
    (decoderGuardBefore side node child labels index).2.slots (.internal (.qualifier querySide channel)) =
      (decoderPositionBefore side node).slots (.internal (.qualifier querySide channel)) := by
  exact guardFold_slots side node _ _ _


/-- The current child handle and cursor follow the stored label prefix exactly. -/
def guardCursorAt (side : Side) (node : Fin parameters.decoder.nodeCount)
    (child : Fin node.val) (labels : List (Fin parameters.channels)) (count : Nat) :
    Literal Nat × Cursor parameters :=
  (labels.zipIdx.take count).foldl (decoderGuardStep side node)
    ((decoderPositionBefore side node).slots
      (.internal (.decoder side (parameters.decoder.childIndex node child))), decoderPositionBefore side node)

theorem guardCursorAt_before (side : Side) (node : Fin parameters.decoder.nodeCount)
    (child : Fin node.val) (labels : List (Fin parameters.channels)) (index : Fin labels.length) :
    guardCursorAt side node child labels index.val = decoderGuardBefore side node child labels index := rfl

theorem guardCursorAt_succ (side : Side) (node : Fin parameters.decoder.nodeCount)
    (child : Fin node.val) (labels : List (Fin parameters.channels)) (index : Fin labels.length) :
    guardCursorAt side node child labels (index.val + 1) =
      decoderGuardStep side node (guardCursorAt side node child labels index.val) (labels[index.val], index.val) := by
  unfold guardCursorAt
  rw [List.take_succ_eq_append_getElem (by simpa only [List.length_zipIdx] using index.isLt),
    List.foldl_append, List.foldl_cons, List.foldl_nil]
  simp only [List.getElem_zipIdx, Nat.zero_add]

theorem guardCursorAt_end (side : Side) (node : Fin parameters.decoder.nodeCount)
    (child : Fin node.val) (labels : List (Fin parameters.channels)) :
    guardCursorAt side node child labels labels.length =
      guardChain parameters side node
        ((decoderPositionBefore side node).slots
          (.internal (.decoder side (parameters.decoder.childIndex node child))))
        labels (decoderPositionBefore side node) := by
  have takeFull : labels.zipIdx.take labels.length = labels.zipIdx := by
    rw [← List.length_zipIdx, List.take_length]
  simp only [guardCursorAt, guardChain, takeFull]
  rfl

theorem guardNode_output (side : Side) (node : Fin parameters.decoder.nodeCount)
    (child : Fin node.val) (labels : List (Fin parameters.channels))
    (shape : parameters.decoder.node node = .guard child labels) :
    (decoderNode parameters side node (decoderPositionBefore side node)).slots (.internal (.decoder side node)) =
      (guardCursorAt side node child labels labels.length).1 := by
  rw [guardCursorAt_end]
  simp [decoderNode, shape, Cursor.assign]


/-- Guard requests use the two directional qualifier certificates with polarity reversed. -/
def negativeQualifierPair {state : State v} {context : Clause (Fin v)}
    {left right : Literal (Fin v)} (pair : DirectionPair state context left right) :
    DirectionPair state context (negate left) (negate right) :=
  ⟨Controller.NativeProof.SourceStagePolarity.GuardedTransfer.dual pair.backward,
    Controller.NativeProof.SourceStagePolarity.GuardedTransfer.dual pair.forward⟩

theorem negativeQualifierPair_supported (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    {context : Clause (Fin v)} {left right : Literal (Fin v)}
    (pair : DirectionPair prefixState.state context left right)
    (original : DirectionPairOrigin rename prefixState pair) :
    DirectionPairOrigin rename prefixState (negativeQualifierPair pair) :=
  ⟨GuardedTransferOrigin.dual rename prefixState pair.backward original.2,
    GuardedTransferOrigin.dual rename prefixState pair.forward original.1⟩

/-- A label prefix stores a checked continuation and its current child pair. -/
structure GuardChainProjection (rename : Nat → Fin v) (context : Clause (Fin v))
    (node : Fin parameters.decoder.nodeCount) (child : Fin node.val)
    (labels : List (Fin parameters.channels)) (start : State v) (count : Nat) where
  state : State v
  steps : List (Step v)
  checked : runSteps start steps = some state
  pair : DirectionPair state context
    (mapLiteral rename (guardCursorAt .healthy node child labels count).1)
    (mapLiteral rename (guardCursorAt .faulty node child labels count).1)
  bounded : count ≤ labels.length
  cost : steps.length ≤ 24 * count

/-- The empty label prefix reuses the actual earlier decoder-child certificate. -/
def guardChainInitial (rename : Nat → Fin v) (context : Clause (Fin v))
    (node : Fin parameters.decoder.nodeCount) (child : Fin node.val)
    (labels : List (Fin parameters.channels))
    (table : DecoderPairTable (parameters := parameters) rename context node.val) :
    GuardChainProjection rename context node child labels table.prefixState.state 0 := by
  let previous := table.pairs (parameters.decoder.childIndex node child) child.isLt
  refine ⟨table.prefixState.state, [], rfl, ?_, Nat.zero_le _, by simp⟩
  exact previous

theorem guardCursorAt_output_succ (side : Side) (node : Fin parameters.decoder.nodeCount)
    (child : Fin node.val) (labels : List (Fin parameters.channels)) (index : Fin labels.length) :
    (guardCursorAt side node child labels (index.val + 1)).1 =
      guardOutput side node child labels index := by
  rw [guardCursorAt_succ]
  rfl

/-- Continuation assembly depends only on the checked kernel result and its scalar cost. -/
def guardChainAppend (rename : Nat → Fin v) (context : Clause (Fin v))
    (node : Fin parameters.decoder.nodeCount) (child : Fin node.val)
    (labels : List (Fin parameters.channels)) (start : State v) (index : Fin labels.length)
    (chain : GuardChainProjection rename context node child labels start index.val)
    (added : PairedProjection chain.state context
      (mapLiteral rename (guardOutput .healthy node child labels index))
      (mapLiteral rename (guardOutput .faulty node child labels index)) 24) :
    GuardChainProjection rename context node child labels start (index.val + 1) := by
  refine ⟨added.state, chain.steps ++ added.steps, ?_, ?_, by omega, ?_⟩
  · rw [runSteps_append, chain.checked]
    exact added.checked
  · have typeEqual : DirectionPair added.state context
        (mapLiteral rename (guardCursorAt .healthy node child labels (index.val + 1)).1)
        (mapLiteral rename (guardCursorAt .faulty node child labels (index.val + 1)).1) =
        DirectionPair added.state context
          (mapLiteral rename (guardOutput .healthy node child labels index))
          (mapLiteral rename (guardOutput .faulty node child labels index)) := by
      rw [guardCursorAt_output_succ, guardCursorAt_output_succ]
    exact Eq.mpr typeEqual added.pair
  · have before := chain.cost
    have next := added.count
    simp only [List.length_append]
    omega

/-- One stored guard occurrence extends the continuation by its actual paired AND kernel. -/
def guardChainAdvance (rename : Nat → Fin v) (context : Clause (Fin v))
    (node : Fin parameters.decoder.nodeCount) (child : Fin node.val)
    (labels : List (Fin parameters.channels)) (shape : parameters.decoder.node node = .guard child labels)
    (prefixState : SourcePrefix (parameters := parameters) rename) (index : Fin labels.length)
    (chain : GuardChainProjection rename context node child labels prefixState.state index.val)
    (qualifier : DirectionPair chain.state context
      (mapLiteral rename (guardRight .healthy node child labels index))
      (mapLiteral rename (guardRight .faulty node child labels index))) :
    GuardChainProjection rename context node child labels prefixState.state (index.val + 1) := by
  let current := prefixState.extend chain.state chain.steps chain.checked
  let previous : DirectionPair current.state context
      (mapLiteral rename (guardLeft .healthy node child labels index))
      (mapLiteral rename (guardLeft .faulty node child labels index)) := chain.pair
  let added := pairedGuard rename context node child labels shape index current previous qualifier
  exact guardChainAppend rename context node child labels prefixState.state index chain added

def GuardChainOriginalSupport (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    {context : Clause (Fin v)} {node : Fin parameters.decoder.nodeCount}
    {child : Fin node.val} {labels : List (Fin parameters.channels)} {count : Nat}
    (chain : GuardChainProjection rename context node child labels prefixState.state count) : Prop :=
  PrefixOriginalSupport rename (prefixState.extend chain.state chain.steps chain.checked) ∧
    DirectionPairOrigin rename (prefixState.extend chain.state chain.steps chain.checked) chain.pair

theorem decoderPairOrigin_same_steps (rename : Nat → Fin v)
    (state : State v) (before after : List (Step v)) (same : before = after)
    (beforeChecked : runSteps (initialState (relabel rename (formula parameters))) before = some state)
    (afterChecked : runSteps (initialState (relabel rename (formula parameters))) after = some state)
    {context : Clause (Fin v)} {input output : Literal (Fin v)}
    (pair : DirectionPair state context input output)
    (original : DirectionPairOrigin rename ⟨state, before, beforeChecked⟩ pair) :
    DirectionPairOrigin rename ⟨state, after, afterChecked⟩ pair := by
  cases same
  exact original

theorem guardChainAppend_supported (rename : Nat → Fin v) (context : Clause (Fin v))
    (node : Fin parameters.decoder.nodeCount) (child : Fin node.val)
    (labels : List (Fin parameters.channels))
    (prefixState : SourcePrefix (parameters := parameters) rename) (index : Fin labels.length)
    (chain : GuardChainProjection rename context node child labels prefixState.state index.val)
    (added : PairedProjection chain.state context
      (mapLiteral rename (guardOutput .healthy node child labels index))
      (mapLiteral rename (guardOutput .faulty node child labels index)) 24)
    (supported : PairedProjectionOriginalSupport rename
      (prefixState.extend chain.state chain.steps chain.checked) added) :
    GuardChainOriginalSupport rename prefixState
      (guardChainAppend rename context node child labels prefixState.state index chain added) := by
  refine ⟨?_, ?_⟩
  · simpa only [PrefixOriginalSupport, guardChainAppend, SourcePrefix.extend,
      List.append_assoc] using supported.1
  · let finalPrefix := prefixState.extend added.state (chain.steps ++ added.steps)
      (by rw [runSteps_append, chain.checked]; exact added.checked)
    have original : DirectionPairOrigin rename finalPrefix added.pair :=
      decoderPairOrigin_same_steps rename added.state
        ((prefixState.steps ++ chain.steps) ++ added.steps)
        (prefixState.steps ++ (chain.steps ++ added.steps))
        (List.append_assoc _ _ _)
        ((prefixState.extend chain.state chain.steps chain.checked).extend
          added.state added.steps added.checked).checked finalPrefix.checked added.pair supported.2
    have typeEqual : DirectionPair added.state context
        (mapLiteral rename (guardCursorAt .healthy node child labels (index.val + 1)).1)
        (mapLiteral rename (guardCursorAt .faulty node child labels (index.val + 1)).1) =
        DirectionPair added.state context
          (mapLiteral rename (guardOutput .healthy node child labels index))
          (mapLiteral rename (guardOutput .faulty node child labels index)) := by
      rw [guardCursorAt_output_succ, guardCursorAt_output_succ]
    have transported := directionPairOrigin_mpr rename finalPrefix
      (congrArg (mapLiteral rename) (guardCursorAt_output_succ .healthy node child labels index)).symm
      (congrArg (mapLiteral rename) (guardCursorAt_output_succ .faulty node child labels index)).symm
      typeEqual added.pair original
    exact transported


theorem guardChainAdvance_supported (rename : Nat → Fin v) (context : Clause (Fin v))
    (node : Fin parameters.decoder.nodeCount) (child : Fin node.val)
    (labels : List (Fin parameters.channels)) (shape : parameters.decoder.node node = .guard child labels)
    (prefixState : SourcePrefix (parameters := parameters) rename) (index : Fin labels.length)
    (chain : GuardChainProjection rename context node child labels prefixState.state index.val)
    (qualifier : DirectionPair chain.state context
      (mapLiteral rename (guardRight .healthy node child labels index))
      (mapLiteral rename (guardRight .faulty node child labels index)))
    (chainOriginal : GuardChainOriginalSupport rename prefixState chain)
    (qualifierOriginal : DirectionPairOrigin rename
      (prefixState.extend chain.state chain.steps chain.checked) qualifier) :
    GuardChainOriginalSupport rename prefixState
      (guardChainAdvance rename context node child labels shape prefixState index chain qualifier) := by
  let current := prefixState.extend chain.state chain.steps chain.checked
  let previous : DirectionPair current.state context
      (mapLiteral rename (guardLeft .healthy node child labels index))
      (mapLiteral rename (guardLeft .faulty node child labels index)) := chain.pair
  have previousOriginal : DirectionPairOrigin rename current previous := by
    simpa only [previous, current, guardLeft, guardCursorAt, decoderGuardBefore, occurrenceCursor] using chainOriginal.2
  have actual := pairedGuard_supported rename context node child labels shape index current
    previous qualifier chainOriginal.1 previousOriginal qualifierOriginal
  have combined := guardChainAppend_supported rename context node child labels prefixState index chain
    (pairedGuard rename context node child labels shape index current previous qualifier) actual
  simpa only [guardChainAdvance, current, previous] using combined

/-- Qualifier certificates are indexed by the actual decoder-entry source slots. -/
def GuardQualifierPairs (rename : Nat → Fin v) (context : Clause (Fin v))
    (node : Fin parameters.decoder.nodeCount) (state : State v) :=
  ∀ channel : Fin parameters.channels,
    DirectionPair state context
      (mapLiteral rename ((decoderPositionBefore .healthy node).slots (.internal (.qualifier .healthy channel))))
      (mapLiteral rename ((decoderPositionBefore .faulty node).slots (.internal (.qualifier .faulty channel))))

def guardQualifierAt (rename : Nat → Fin v) (context : Clause (Fin v))
    (node : Fin parameters.decoder.nodeCount) (child : Fin node.val)
    (labels : List (Fin parameters.channels)) (index : Fin labels.length)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (qualifiers : GuardQualifierPairs rename context node prefixState.state)
    (chain : GuardChainProjection rename context node child labels prefixState.state index.val) :
    DirectionPair chain.state context
      (mapLiteral rename (guardRight .healthy node child labels index))
      (mapLiteral rename (guardRight .faulty node child labels index)) := by
  let carried := (qualifiers labels[index.val]).afterTrace chain.state chain.steps chain.checked
  let negative := negativeQualifierPair carried
  have typeEqual : DirectionPair chain.state context
      (mapLiteral rename (guardRight .healthy node child labels index))
      (mapLiteral rename (guardRight .faulty node child labels index)) =
      DirectionPair chain.state context
        (negate (mapLiteral rename ((decoderPositionBefore .healthy node).slots
          (.internal (.qualifier .healthy labels[index.val])))))
        (negate (mapLiteral rename ((decoderPositionBefore .faulty node).slots
          (.internal (.qualifier .faulty labels[index.val]))))) := by
    simp only [guardRight, guardCursor_qualifier, mapLiteral, negate, Std.Sat.Literal.negate]
  exact Eq.mpr typeEqual negative

def buildGuardChain (rename : Nat → Fin v) (context : Clause (Fin v))
    (node : Fin parameters.decoder.nodeCount) (child : Fin node.val)
    (labels : List (Fin parameters.channels)) (shape : parameters.decoder.node node = .guard child labels)
    (table : DecoderPairTable (parameters := parameters) rename context node.val)
    (qualifiers : GuardQualifierPairs rename context node table.prefixState.state)
    (count : Nat) (bounded : count ≤ labels.length) :
    GuardChainProjection rename context node child labels table.prefixState.state count :=
  match count with
  | 0 => guardChainInitial rename context node child labels table
  | count + 1 =>
      let index : Fin labels.length := ⟨count, by omega⟩
      let before := buildGuardChain rename context node child labels shape table qualifiers count (by omega)
      guardChainAdvance rename context node child labels shape table.prefixState index before
        (guardQualifierAt rename context node child labels index table.prefixState qualifiers before)

def completeGuardChain (rename : Nat → Fin v) (context : Clause (Fin v))
    (node : Fin parameters.decoder.nodeCount) (child : Fin node.val)
    (labels : List (Fin parameters.channels)) (shape : parameters.decoder.node node = .guard child labels)
    (table : DecoderPairTable (parameters := parameters) rename context node.val)
    (qualifiers : GuardQualifierPairs rename context node table.prefixState.state) :
    GuardChainProjection rename context node child labels table.prefixState.state labels.length :=
  buildGuardChain rename context node child labels shape table qualifiers labels.length (Nat.le_refl _)

def GuardQualifierPairsOriginalSupport (rename : Nat → Fin v) (context : Clause (Fin v))
    (node : Fin parameters.decoder.nodeCount)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (qualifiers : GuardQualifierPairs rename context node prefixState.state) : Prop :=
  ∀ channel, DirectionPairOrigin rename prefixState (qualifiers channel)

theorem guardQualifierAt_supported (rename : Nat → Fin v) (context : Clause (Fin v))
    (node : Fin parameters.decoder.nodeCount) (child : Fin node.val)
    (labels : List (Fin parameters.channels)) (index : Fin labels.length)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (qualifiers : GuardQualifierPairs rename context node prefixState.state)
    (originals : GuardQualifierPairsOriginalSupport rename context node prefixState qualifiers)
    (chain : GuardChainProjection rename context node child labels prefixState.state index.val) :
    DirectionPairOrigin rename (prefixState.extend chain.state chain.steps chain.checked)
      (guardQualifierAt rename context node child labels index prefixState qualifiers chain) := by
  let current := prefixState.extend chain.state chain.steps chain.checked
  let carried := (qualifiers labels[index.val]).afterTrace chain.state chain.steps chain.checked
  have carriedOriginal := DirectionPairOrigin.afterTrace rename prefixState
    (qualifiers labels[index.val]) (originals labels[index.val]) chain.state chain.steps chain.checked
  let negative := negativeQualifierPair carried
  have negativeOriginal := negativeQualifierPair_supported rename current carried carriedOriginal
  have typeEqual : DirectionPair chain.state context
      (mapLiteral rename (guardRight .healthy node child labels index))
      (mapLiteral rename (guardRight .faulty node child labels index)) =
      DirectionPair chain.state context
        (negate (mapLiteral rename ((decoderPositionBefore .healthy node).slots
          (.internal (.qualifier .healthy labels[index.val])))))
        (negate (mapLiteral rename ((decoderPositionBefore .faulty node).slots
          (.internal (.qualifier .faulty labels[index.val]))))) := by
    simp only [guardRight, guardCursor_qualifier, mapLiteral, negate, Std.Sat.Literal.negate]
  have leftEqual : negate (mapLiteral rename ((decoderPositionBefore .healthy node).slots
      (.internal (.qualifier .healthy labels[index.val])))) =
      mapLiteral rename (guardRight .healthy node child labels index) := by
    simp only [guardRight, guardCursor_qualifier, mapLiteral, negate, Std.Sat.Literal.negate]
  have rightEqual : negate (mapLiteral rename ((decoderPositionBefore .faulty node).slots
      (.internal (.qualifier .faulty labels[index.val])))) =
      mapLiteral rename (guardRight .faulty node child labels index) := by
    simp only [guardRight, guardCursor_qualifier, mapLiteral, negate, Std.Sat.Literal.negate]
  exact directionPairOrigin_mpr rename current leftEqual rightEqual typeEqual negative negativeOriginal

theorem guardChainInitial_supported (rename : Nat → Fin v) (context : Clause (Fin v))
    (node : Fin parameters.decoder.nodeCount) (child : Fin node.val)
    (labels : List (Fin parameters.channels))
    (table : DecoderPairTable (parameters := parameters) rename context node.val)
    (supported : DecoderPairTableOriginalSupport rename context node.val table) :
    GuardChainOriginalSupport rename table.prefixState (guardChainInitial rename context node child labels table) := by
  refine ⟨?_, ?_⟩
  · simpa only [guardChainInitial, SourcePrefix.extend, List.append_nil] using supported.1
  · have actual := decoderPairOrigin_same_steps rename table.prefixState.state
      table.prefixState.steps (table.prefixState.steps ++ []) (List.append_nil _).symm
      table.prefixState.checked (table.prefixState.extend table.prefixState.state [] rfl).checked
      (table.pairs (parameters.decoder.childIndex node child) child.isLt)
      (supported.2 (parameters.decoder.childIndex node child) child.isLt)
    simpa only [guardChainInitial, guardCursorAt, List.take_zero, List.foldl_nil,
      decoderPositionBefore, decoderBefore, occurrenceCursor, SourcePrefix.extend] using actual

theorem buildGuardChain_supported (rename : Nat → Fin v) (context : Clause (Fin v))
    (node : Fin parameters.decoder.nodeCount) (child : Fin node.val)
    (labels : List (Fin parameters.channels)) (shape : parameters.decoder.node node = .guard child labels)
    (table : DecoderPairTable (parameters := parameters) rename context node.val)
    (qualifiers : GuardQualifierPairs rename context node table.prefixState.state)
    (tableOriginal : DecoderPairTableOriginalSupport rename context node.val table)
    (qualifierOriginal : GuardQualifierPairsOriginalSupport rename context node table.prefixState qualifiers)
    (count : Nat) (bounded : count ≤ labels.length) :
    GuardChainOriginalSupport rename table.prefixState
      (buildGuardChain rename context node child labels shape table qualifiers count bounded) := by
  induction count with
  | zero => exact guardChainInitial_supported rename context node child labels table tableOriginal
  | succ count ih =>
      let index : Fin labels.length := ⟨count, by omega⟩
      let before := buildGuardChain rename context node child labels shape table qualifiers count (by omega)
      exact guardChainAdvance_supported rename context node child labels shape table.prefixState index before
        (guardQualifierAt rename context node child labels index table.prefixState qualifiers before)
        (ih (by omega))
        (guardQualifierAt_supported rename context node child labels index table.prefixState
          qualifiers qualifierOriginal before)

theorem completeGuardChain_supported (rename : Nat → Fin v) (context : Clause (Fin v))
    (node : Fin parameters.decoder.nodeCount) (child : Fin node.val)
    (labels : List (Fin parameters.channels)) (shape : parameters.decoder.node node = .guard child labels)
    (table : DecoderPairTable (parameters := parameters) rename context node.val)
    (qualifiers : GuardQualifierPairs rename context node table.prefixState.state)
    (tableOriginal : DecoderPairTableOriginalSupport rename context node.val table)
    (qualifierOriginal : GuardQualifierPairsOriginalSupport rename context node table.prefixState qualifiers) :
    GuardChainOriginalSupport rename table.prefixState
      (completeGuardChain rename context node child labels shape table qualifiers) :=
  buildGuardChain_supported rename context node child labels shape table qualifiers tableOriginal
    qualifierOriginal labels.length (Nat.le_refl _)

/-- The complete guard occurrence returns its actual assigned decoder-node output. -/
def completeGuardNode (rename : Nat → Fin v) (context : Clause (Fin v))
    (node : Fin parameters.decoder.nodeCount) (child : Fin node.val)
    (labels : List (Fin parameters.channels)) (shape : parameters.decoder.node node = .guard child labels)
    (table : DecoderPairTable (parameters := parameters) rename context node.val)
    (qualifiers : GuardQualifierPairs rename context node table.prefixState.state) :
    PairedProjection table.prefixState.state context
      (mapLiteral rename ((decoderNode parameters .healthy node (decoderPositionBefore .healthy node)).slots
        (.internal (.decoder .healthy node))))
      (mapLiteral rename ((decoderNode parameters .faulty node (decoderPositionBefore .faulty node)).slots
        (.internal (.decoder .faulty node)))) (24 * labels.length) := by
  let chain := completeGuardChain rename context node child labels shape table qualifiers
  refine ⟨chain.state, chain.steps, chain.checked, ?_, chain.cost⟩
  have typeEqual : DirectionPair chain.state context
      (mapLiteral rename ((decoderNode parameters .healthy node (decoderPositionBefore .healthy node)).slots
        (.internal (.decoder .healthy node))))
      (mapLiteral rename ((decoderNode parameters .faulty node (decoderPositionBefore .faulty node)).slots
        (.internal (.decoder .faulty node)))) =
      DirectionPair chain.state context
        (mapLiteral rename (guardCursorAt .healthy node child labels labels.length).1)
        (mapLiteral rename (guardCursorAt .faulty node child labels labels.length).1) := by
    rw [guardNode_output .healthy node child labels shape, guardNode_output .faulty node child labels shape]
  exact Eq.mpr typeEqual chain.pair

def decoderCursorAt (side : Side) (count : Nat) : Cursor parameters :=
  ((List.finRange parameters.decoder.nodeCount).take count).foldl
    (fun cursor node => decoderNode parameters side node cursor) (decoderStart side)

theorem decoderCursorAt_before (side : Side) (node : Fin parameters.decoder.nodeCount) :
    decoderCursorAt side node.val = decoderPositionBefore side node := rfl

theorem decoderCursorAt_succ (side : Side) (node : Fin parameters.decoder.nodeCount) :
    decoderCursorAt side (node.val + 1) = decoderNode parameters side node (decoderCursorAt side node.val) := by
  unfold decoderCursorAt
  rw [List.take_succ_eq_append_getElem (by simpa only [List.length_finRange] using node.isLt),
    List.foldl_append, List.foldl_cons, List.foldl_nil]
  simp only [List.getElem_finRange]
  congr 1

theorem decoderCursorAt_old_node (side : Side) (node query : Fin parameters.decoder.nodeCount)
    (earlier : query.val < node.val) :
    (decoderCursorAt side (node.val + 1)).slots (.internal (.decoder side query)) =
      (decoderCursorAt side node.val).slots (.internal (.decoder side query)) := by
  rw [decoderCursorAt_succ]
  apply decoderNode_other
  intro equal
  have same : query = node := by simpa using equal
  have values := congrArg Fin.val same
  omega

def decoderLiveAndOutput (side : Side) (node : Fin parameters.decoder.nodeCount) : Literal Nat :=
  ((decoderPositionBefore side node).lastID + 1, true)

def decoderLiveAndTreeOriginal (rename : Nat → Fin v) (side : Side)
    (node : Fin parameters.decoder.nodeCount) (left right : Fin node.val)
    (shape : parameters.decoder.node node = .liveAnd left right) :
    AndTree (initialState (relabel rename (formula parameters)))
      (mapLiteral rename (decoderLiveAndOutput side node))
      [mapLiteral rename ((decoderPositionBefore side node).slots
        (.internal (.decoder side (parameters.decoder.childIndex node left)))),
       mapLiteral rename ((decoderPositionBefore side node).slots
        (.internal (.decoder side (parameters.decoder.childIndex node right))))] :=
  .node (.leaf _) (.leaf _) _
    (binaryRows _ _ (decoderLiveAndOutput side node) (decoderLiveAndRows rename side node left right shape))

theorem decoderLiveAndTreeOriginal_supported (rename : Nat → Fin v) (side : Side)
    (node : Fin parameters.decoder.nodeCount) (left right : Fin node.val)
    (shape : parameters.decoder.node node = .liveAnd left right) :
    TreeOriginals (AllowedOriginal (parameters := parameters) rename)
      (decoderLiveAndTreeOriginal rename side node left right shape) := by
  refine ⟨trivial, trivial, ?_⟩
  apply binaryRows_originals
  intro index
  exact decoderLiveAndRows_allowed rename side node left right shape ⟨index.val, by change index.val < 3; exact index.isLt⟩

def decoderLiveAndTree (rename : Nat → Fin v) (side : Side)
    (node : Fin parameters.decoder.nodeCount) (left right : Fin node.val)
    (shape : parameters.decoder.node node = .liveAnd left right)
    (prefixState : SourcePrefix (parameters := parameters) rename) :=
  (decoderLiveAndTreeOriginal rename side node left right shape).afterTrace
    prefixState.state prefixState.steps prefixState.checked

def pairedDecoderLiveAnd (rename : Nat → Fin v) (context : Clause (Fin v))
    (node : Fin parameters.decoder.nodeCount) (left right : Fin node.val)
    (shape : parameters.decoder.node node = .liveAnd left right)
    (table : DecoderPairTable (parameters := parameters) rename context node.val) :
    PairedProjection table.prefixState.state context
      (mapLiteral rename (decoderLiveAndOutput .healthy node))
      (mapLiteral rename (decoderLiveAndOutput .faulty node)) 24 := by
  let pairs := decoderChildPairs rename node [left, right]
  let leftTree : AndTree table.prefixState.state (mapLiteral rename (decoderLiveAndOutput .healthy node))
      (pairs.map Prod.fst) := by
    exact decoderLiveAndTree rename .healthy node left right shape table.prefixState
  let rightTree : AndTree table.prefixState.state (mapLiteral rename (decoderLiveAndOutput .faulty node))
      (pairs.map Prod.snd) := by
    exact decoderLiveAndTree rename .faulty node left right shape table.prefixState
  exact pairedAnd table.prefixState.state context _ _ pairs (by simp [pairs, decoderChildPairs])
    leftTree rightTree (fun pair member => decoderChildPairDirection rename context node [left, right] table pair member)


theorem decoderLiveAndTree_supported (rename : Nat → Fin v) (side : Side)
    (node : Fin parameters.decoder.nodeCount) (left right : Fin node.val)
    (shape : parameters.decoder.node node = .liveAnd left right)
    (prefixState : SourcePrefix (parameters := parameters) rename) :
    TreeOriginals (AllowedOriginal (parameters := parameters) rename)
      (decoderLiveAndTree rename side node left right shape prefixState) :=
  treeOriginals_afterTrace _ (decoderLiveAndTreeOriginal rename side node left right shape)
    (decoderLiveAndTreeOriginal_supported rename side node left right shape)
    prefixState.state prefixState.steps prefixState.checked

theorem pairedDecoderLiveAnd_supported (rename : Nat → Fin v) (context : Clause (Fin v))
    (node : Fin parameters.decoder.nodeCount) (left right : Fin node.val)
    (shape : parameters.decoder.node node = .liveAnd left right)
    (table : DecoderPairTable (parameters := parameters) rename context node.val)
    (supported : DecoderPairTableOriginalSupport rename context node.val table) :
    PairedProjectionOriginalSupport rename table.prefixState
      (pairedDecoderLiveAnd rename context node left right shape table) := by
  let pairs := decoderChildPairs rename node [left, right]
  let leftTree : AndTree table.prefixState.state (mapLiteral rename (decoderLiveAndOutput .healthy node))
      (pairs.map Prod.fst) := by
    exact decoderLiveAndTree rename .healthy node left right shape table.prefixState
  let rightTree : AndTree table.prefixState.state (mapLiteral rename (decoderLiveAndOutput .faulty node))
      (pairs.map Prod.snd) := by
    exact decoderLiveAndTree rename .faulty node left right shape table.prefixState
  have leftOriginal : TreeOriginals (AllowedOriginal (parameters := parameters) rename) leftTree := by
    exact decoderLiveAndTree_supported rename .healthy node left right shape table.prefixState
  have rightOriginal : TreeOriginals (AllowedOriginal (parameters := parameters) rename) rightTree := by
    exact decoderLiveAndTree_supported rename .faulty node left right shape table.prefixState
  have actual := pairedAnd_supported rename table.prefixState context
    (mapLiteral rename (decoderLiveAndOutput .healthy node))
    (mapLiteral rename (decoderLiveAndOutput .faulty node)) pairs (by simp [pairs, decoderChildPairs])
    leftTree rightTree
    (fun pair member => decoderChildPairDirection rename context node [left, right] table pair member)
    leftOriginal rightOriginal supported.1
    (fun pair member => decoderChildPairDirection_supported rename context node [left, right] table pair member supported)
  exact actual


/-- Retyping changes only the two endpoint literals and preserves the actual trace. -/
def decoderProjectionRetarget {state : State v} {context : Clause (Fin v)}
    {left right nextLeft nextRight : Literal (Fin v)} {budget : Nat}
    (projection : PairedProjection state context left right budget)
    (leftEqual : nextLeft = left) (rightEqual : nextRight = right) :
    PairedProjection state context nextLeft nextRight budget := by
  cases leftEqual
  cases rightEqual
  exact projection

theorem decoderProjectionRetarget_supported (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    {context : Clause (Fin v)} {left right nextLeft nextRight : Literal (Fin v)} {budget : Nat}
    (projection : PairedProjection prefixState.state context left right budget)
    (leftEqual : nextLeft = left) (rightEqual : nextRight = right)
    (supported : PairedProjectionOriginalSupport rename prefixState projection) :
    PairedProjectionOriginalSupport rename prefixState
      (decoderProjectionRetarget projection leftEqual rightEqual) := by
  cases leftEqual
  cases rightEqual
  exact supported

theorem decoderLiveAnd_output (side : Side) (node : Fin parameters.decoder.nodeCount)
    (left right : Fin node.val) (shape : parameters.decoder.node node = .liveAnd left right) :
    (decoderNode parameters side node (decoderPositionBefore side node)).slots
      (.internal (.decoder side node)) = decoderLiveAndOutput side node := by
  simp [decoderNode, shape, Cursor.emitNative, Cursor.emit, Cursor.assign, decoderLiveAndOutput]

def completeLiveAndNode (rename : Nat → Fin v) (context : Clause (Fin v))
    (node : Fin parameters.decoder.nodeCount) (left right : Fin node.val)
    (shape : parameters.decoder.node node = .liveAnd left right)
    (table : DecoderPairTable (parameters := parameters) rename context node.val) :=
  decoderProjectionRetarget (pairedDecoderLiveAnd rename context node left right shape table)
    (congrArg (mapLiteral rename) (decoderLiveAnd_output .healthy node left right shape))
    (congrArg (mapLiteral rename) (decoderLiveAnd_output .faulty node left right shape))

theorem completeLiveAndNode_supported (rename : Nat → Fin v) (context : Clause (Fin v))
    (node : Fin parameters.decoder.nodeCount) (left right : Fin node.val)
    (shape : parameters.decoder.node node = .liveAnd left right)
    (table : DecoderPairTable (parameters := parameters) rename context node.val)
    (supported : DecoderPairTableOriginalSupport rename context node.val table) :
    PairedProjectionOriginalSupport rename table.prefixState
      (completeLiveAndNode rename context node left right shape table) :=
  decoderProjectionRetarget_supported rename table.prefixState _ _ _
    (pairedDecoderLiveAnd_supported rename context node left right shape table supported)

def completeDisjunctionNode (rename : Nat → Fin v) (context : Clause (Fin v))
    (node : Fin parameters.decoder.nodeCount) (children : List (Fin node.val))
    (shape : parameters.decoder.node node = .disj children) (nonempty : children ≠ [])
    (table : DecoderPairTable (parameters := parameters) rename context node.val) :=
  decoderProjectionRetarget (pairedDecoderDisjunction rename context node children shape nonempty table)
    (congrArg (mapLiteral rename) (decoderDisjunction_output .healthy node children shape))
    (congrArg (mapLiteral rename) (decoderDisjunction_output .faulty node children shape))

theorem completeDisjunctionNode_supported (rename : Nat → Fin v) (context : Clause (Fin v))
    (node : Fin parameters.decoder.nodeCount) (children : List (Fin node.val))
    (shape : parameters.decoder.node node = .disj children) (nonempty : children ≠ [])
    (table : DecoderPairTable (parameters := parameters) rename context node.val)
    (supported : DecoderPairTableOriginalSupport rename context node.val table) :
    PairedProjectionOriginalSupport rename table.prefixState
      (completeDisjunctionNode rename context node children shape nonempty table) :=
  decoderProjectionRetarget_supported rename table.prefixState _ _ _
    (pairedDecoderDisjunction_supported rename context node children shape nonempty table supported)

def decoderStoredLiteral (rename : Nat → Fin v) (side : Side) (count : Nat)
    (query : Fin parameters.decoder.nodeCount) : Literal (Fin v) :=
  mapLiteral rename ((decoderCursorAt side count).slots (.internal (.decoder side query)))

theorem decoderStoredLiteral_self (rename : Nat → Fin v) (side : Side)
    (node : Fin parameters.decoder.nodeCount) :
    decoderStoredLiteral rename side (node.val + 1) node =
      mapLiteral rename ((decoderNode parameters side node (decoderPositionBefore side node)).slots
        (.internal (.decoder side node))) := by
  unfold decoderStoredLiteral
  rw [decoderCursorAt_succ, decoderCursorAt_before]

theorem decoderStoredLiteral_old (rename : Nat → Fin v) (side : Side)
    (node query : Fin parameters.decoder.nodeCount) (earlier : query.val < node.val) :
    decoderStoredLiteral rename side (node.val + 1) query = decoderStoredLiteral rename side node.val query :=
  congrArg (mapLiteral rename) (decoderCursorAt_old_node side node query earlier)

def decoderDirectionRetarget {state : State v} {context : Clause (Fin v)}
    {left right nextLeft nextRight : Literal (Fin v)}
    (pair : DirectionPair state context left right)
    (leftEqual : nextLeft = left) (rightEqual : nextRight = right) :
    DirectionPair state context nextLeft nextRight :=
  Eq.mpr (congrArg₂ (DirectionPair state context) leftEqual rightEqual) pair

theorem decoderDirectionRetarget_supported (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    {context : Clause (Fin v)} {left right nextLeft nextRight : Literal (Fin v)}
    (pair : DirectionPair prefixState.state context left right)
    (leftEqual : nextLeft = left) (rightEqual : nextRight = right)
    (original : DirectionPairOrigin rename prefixState pair) :
    DirectionPairOrigin rename prefixState (decoderDirectionRetarget pair leftEqual rightEqual) :=
  directionPairOrigin_mpr rename prefixState leftEqual.symm rightEqual.symm _ pair original

/-- An opaque node certificate advances the actual two stored source cursors once. -/
def decoderTableAppend (rename : Nat → Fin v) (context : Clause (Fin v))
    (node : Fin parameters.decoder.nodeCount)
    (table : DecoderPairTable (parameters := parameters) rename context node.val) {budget : Nat}
    (added : PairedProjection table.prefixState.state context
      (mapLiteral rename ((decoderNode parameters .healthy node (decoderPositionBefore .healthy node)).slots
        (.internal (.decoder .healthy node))))
      (mapLiteral rename ((decoderNode parameters .faulty node (decoderPositionBefore .faulty node)).slots
        (.internal (.decoder .faulty node)))) budget) :
    DecoderPairTable (parameters := parameters) rename context (node.val + 1) := by
  refine ⟨table.prefixState.extend added.state added.steps added.checked, ?_⟩
  intro query before
  by_cases same : query = node
  · subst query
    exact decoderDirectionRetarget added.pair
      (decoderStoredLiteral_self rename .healthy node)
      (decoderStoredLiteral_self rename .faulty node)
  · have earlier : query.val < node.val := by
      have different : query.val ≠ node.val := fun equality => same (Fin.ext equality)
      omega
    have old := (table.pairs query earlier).afterTrace added.state added.steps added.checked
    exact decoderDirectionRetarget old
      (decoderStoredLiteral_old rename .healthy node query earlier)
      (decoderStoredLiteral_old rename .faulty node query earlier)


theorem decoderTableAppend_supported (rename : Nat → Fin v) (context : Clause (Fin v))
    (node : Fin parameters.decoder.nodeCount)
    (table : DecoderPairTable (parameters := parameters) rename context node.val)
    (supported : DecoderPairTableOriginalSupport rename context node.val table) {budget : Nat}
    (added : PairedProjection table.prefixState.state context
      (mapLiteral rename ((decoderNode parameters .healthy node (decoderPositionBefore .healthy node)).slots
        (.internal (.decoder .healthy node))))
      (mapLiteral rename ((decoderNode parameters .faulty node (decoderPositionBefore .faulty node)).slots
        (.internal (.decoder .faulty node)))) budget)
    (addedOriginal : PairedProjectionOriginalSupport rename table.prefixState added) :
    DecoderPairTableOriginalSupport rename context (node.val + 1)
      (decoderTableAppend rename context node table added) := by
  refine ⟨addedOriginal.1, ?_⟩
  intro query before
  by_cases same : query = node
  · subst query
    dsimp only [decoderTableAppend, SourcePrefix.extend]
    rw [dite_eq_left rfl]
    exact decoderDirectionRetarget_supported rename
      (table.prefixState.extend added.state added.steps added.checked) added.pair
      (decoderStoredLiteral_self rename .healthy node)
      (decoderStoredLiteral_self rename .faulty node) addedOriginal.2
  · have earlier : query.val < node.val := by
      have different : query.val ≠ node.val := fun equality => same (Fin.ext equality)
      omega
    have old := DirectionPairOrigin.afterTrace rename table.prefixState (table.pairs query earlier)
      (supported.2 query earlier) added.state added.steps added.checked
    dsimp only [decoderTableAppend, SourcePrefix.extend]
    rw [dite_eq_right same]
    exact decoderDirectionRetarget_supported rename
      (table.prefixState.extend added.state added.steps added.checked)
      ((table.pairs query earlier).afterTrace added.state added.steps added.checked)
      (decoderStoredLiteral_old rename .healthy node query earlier)
      (decoderStoredLiteral_old rename .faulty node query earlier) old

theorem decoderTableAppend_count (rename : Nat → Fin v) (context : Clause (Fin v))
    (node : Fin parameters.decoder.nodeCount)
    (table : DecoderPairTable (parameters := parameters) rename context node.val) {budget : Nat}
    (added : PairedProjection table.prefixState.state context
      (mapLiteral rename ((decoderNode parameters .healthy node (decoderPositionBefore .healthy node)).slots
        (.internal (.decoder .healthy node))))
      (mapLiteral rename ((decoderNode parameters .faulty node (decoderPositionBefore .faulty node)).slots
        (.internal (.decoder .faulty node)))) budget) :
    (decoderTableAppend rename context node table added).prefixState.steps.length ≤
      table.prefixState.steps.length + budget := by
  have count := added.count
  change (table.prefixState.steps ++ added.steps).length ≤ _
  rw [List.length_append]
  omega


theorem completeGuardNode_supported (rename : Nat → Fin v) (context : Clause (Fin v))
    (node : Fin parameters.decoder.nodeCount) (child : Fin node.val)
    (labels : List (Fin parameters.channels)) (shape : parameters.decoder.node node = .guard child labels)
    (table : DecoderPairTable (parameters := parameters) rename context node.val)
    (qualifiers : GuardQualifierPairs rename context node table.prefixState.state)
    (tableOriginal : DecoderPairTableOriginalSupport rename context node.val table)
    (qualifierOriginal : GuardQualifierPairsOriginalSupport rename context node table.prefixState qualifiers) :
    PairedProjectionOriginalSupport rename table.prefixState
      (completeGuardNode rename context node child labels shape table qualifiers) := by
  let chain := completeGuardChain rename context node child labels shape table qualifiers
  have original := completeGuardChain_supported rename context node child labels shape table qualifiers
    tableOriginal qualifierOriginal
  refine ⟨original.1, ?_⟩
  dsimp only [completeGuardNode]
  apply directionPairOrigin_mpr rename (table.prefixState.extend chain.state chain.steps chain.checked)
    (congrArg (mapLiteral rename) (guardNode_output .healthy node child labels shape)).symm
    (congrArg (mapLiteral rename) (guardNode_output .faulty node child labels shape)).symm
  exact original.2

/-- The initialized table contains no decoder outputs and retains its actual proof prefix. -/
def decoderTableInitial (rename : Nat → Fin v) (context : Clause (Fin v))
    (prefixState : SourcePrefix (parameters := parameters) rename) :
    DecoderPairTable (parameters := parameters) rename context 0 :=
  ⟨prefixState, fun node before => False.elim (Nat.not_lt_zero node.val before)⟩

theorem decoderTableInitial_supported (rename : Nat → Fin v) (context : Clause (Fin v))
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (supported : PrefixOriginalSupport rename prefixState) :
    DecoderPairTableOriginalSupport rename context 0 (decoderTableInitial rename context prefixState) := by
  refine ⟨supported, ?_⟩
  intro node before
  exact False.elim (Nat.not_lt_zero node.val before)

/-- Source-node bounds charge stored incidences, including repeated children and labels. -/
def decoderNodeBudget (node : Fin parameters.decoder.nodeCount) : Nat :=
  match parameters.decoder.node node with
  | .zero => 0
  | .input _ => 0
  | .disj children => 12 * children.length
  | .guard _ labels => 24 * labels.length
  | .liveAnd _ _ => 24


def originalUnitAfterTrace (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename) {output : Literal (Fin v)}
    (row : Rows.Available (initialState (relabel rename (formula parameters))) [negate output]) :
    AvailableSubclause prefixState.state [negate output] :=
  FoldProjection.afterTrace (ofRow row) prefixState.state prefixState.steps prefixState.checked

def emptyOriginalUnit (rename : Nat → Fin v) (output : Literal Nat)
    (rows : OriginalRows (initialState (relabel rename (formula parameters))) rename ⟨output, .or []⟩) :
    Rows.Available (initialState (relabel rename (formula parameters))) [negate (mapLiteral rename output)] :=
  rows.row ⟨0, by change 0 < 1; omega⟩

def decoderZeroUnit (rename : Nat → Fin v) (side : Side)
    (node : Fin parameters.decoder.nodeCount) (shape : parameters.decoder.node node = .zero)
    (prefixState : SourcePrefix (parameters := parameters) rename) :
    AvailableSubclause prefixState.state [negate (mapLiteral rename (decoderLiveAndOutput side node))] :=
  originalUnitAfterTrace rename prefixState
    (emptyOriginalUnit rename (decoderLiveAndOutput side node) (decoderZeroRows rename side node shape))

def pairedEmptyDecoder (state : State v) (context : Clause (Fin v))
    (left right : Literal (Fin v))
    (leftUnit : AvailableSubclause state [negate left])
    (rightUnit : AvailableSubclause state [negate right]) :
    PairedProjection state context left right 0 := by
  refine ⟨state, [], rfl, ?_, by simp⟩
  refine ⟨.derived (retarget leftUnit ?_), .derived (retarget rightUnit ?_)⟩
  · intro literal member
    exact List.mem_append_right context (List.mem_cons.mpr (Or.inl (by simpa using member)))
  · intro literal member
    exact List.mem_append_right context (List.mem_cons.mpr (Or.inl (by simpa using member)))

def completeZeroNode (rename : Nat → Fin v) (context : Clause (Fin v))
    (node : Fin parameters.decoder.nodeCount) (shape : parameters.decoder.node node = .zero)
    (table : DecoderPairTable (parameters := parameters) rename context node.val) :=
  decoderProjectionRetarget
    (pairedEmptyDecoder table.prefixState.state context
      (mapLiteral rename (decoderLiveAndOutput .healthy node))
      (mapLiteral rename (decoderLiveAndOutput .faulty node))
      (decoderZeroUnit rename .healthy node shape table.prefixState)
      (decoderZeroUnit rename .faulty node shape table.prefixState))
    (congrArg (mapLiteral rename) (decoderZero_output .healthy node (decoderPositionBefore .healthy node) shape))
    (congrArg (mapLiteral rename) (decoderZero_output .faulty node (decoderPositionBefore .faulty node) shape))

def decoderPairProjection {state : State v} {context : Clause (Fin v)}
    {left right : Literal (Fin v)} (pair : DirectionPair state context left right) :
    PairedProjection state context left right 0 := ⟨state, [], rfl, pair, by simp⟩

def completeInputNode (rename : Nat → Fin v) (context : Clause (Fin v))
    (node : Fin parameters.decoder.nodeCount) (channel : Fin parameters.channels)
    (shape : parameters.decoder.node node = .input channel)
    (table : DecoderPairTable (parameters := parameters) rename context node.val)
    (qualifier : DirectionPair table.prefixState.state context
      (mapLiteral rename ((decoderPositionBefore .healthy node).slots (.internal (.qualifier .healthy channel))))
      (mapLiteral rename ((decoderPositionBefore .faulty node).slots (.internal (.qualifier .faulty channel))))) :
    PairedProjection table.prefixState.state context
      (mapLiteral rename ((decoderNode parameters .healthy node (decoderPositionBefore .healthy node)).slots
        (.internal (.decoder .healthy node))))
      (mapLiteral rename ((decoderNode parameters .faulty node (decoderPositionBefore .faulty node)).slots
        (.internal (.decoder .faulty node)))) 0 :=
  decoderProjectionRetarget (decoderPairProjection qualifier)
    (congrArg (mapLiteral rename) (decoderInput_output .healthy node channel (decoderPositionBefore .healthy node) shape))
    (congrArg (mapLiteral rename) (decoderInput_output .faulty node channel (decoderPositionBefore .faulty node) shape))


def decoderEmptyDisjunctionSupply (rename : Nat → Fin v) (side : Side)
    (node : Fin parameters.decoder.nodeCount) (shape : parameters.decoder.node node = .disj []) :
    RowSupply (initialState (relabel rename (formula parameters))) rename
      [⟨decoderLiveAndOutput side node, .or []⟩] :=
  let equal : (SourceSerialFold.allocate .disjunction (decoderPositionBefore side node).lastID
      ([].map fun child : Fin node.val => (decoderPositionBefore side node).slots
        (.internal (.decoder side (parameters.decoder.childIndex node child))))).producers =
        [⟨decoderLiveAndOutput side node, .or []⟩] := by
    simp only [List.map_nil, SourceSerialFold.allocate, Bounded.Junction.gate, decoderLiveAndOutput]
  Eq.mp (congrArg (RowSupply (initialState (relabel rename (formula parameters))) rename) equal)
    (decoderDisjunctionRowsExact rename side node [] shape)

def decoderEmptyDisjunctionRows (rename : Nat → Fin v) (side : Side)
    (node : Fin parameters.decoder.nodeCount) (shape : parameters.decoder.node node = .disj []) :
    OriginalRows (initialState (relabel rename (formula parameters))) rename
      ⟨decoderLiveAndOutput side node, .or []⟩ :=
  decoderEmptyDisjunctionSupply rename side node shape ⟨0, by simp⟩

def decoderEmptyDisjunctionUnit (rename : Nat → Fin v) (side : Side)
    (node : Fin parameters.decoder.nodeCount) (shape : parameters.decoder.node node = .disj [])
    (prefixState : SourcePrefix (parameters := parameters) rename) :
    AvailableSubclause prefixState.state [negate (mapLiteral rename (decoderLiveAndOutput side node))] :=
  originalUnitAfterTrace rename prefixState
    (emptyOriginalUnit rename (decoderLiveAndOutput side node) (decoderEmptyDisjunctionRows rename side node shape))

def completeEmptyDisjunctionNode (rename : Nat → Fin v) (context : Clause (Fin v))
    (node : Fin parameters.decoder.nodeCount) (shape : parameters.decoder.node node = .disj [])
    (table : DecoderPairTable (parameters := parameters) rename context node.val) :=
  decoderProjectionRetarget
    (pairedEmptyDecoder table.prefixState.state context
      (mapLiteral rename (decoderLiveAndOutput .healthy node))
      (mapLiteral rename (decoderLiveAndOutput .faulty node))
      (decoderEmptyDisjunctionUnit rename .healthy node shape table.prefixState)
      (decoderEmptyDisjunctionUnit rename .faulty node shape table.prefixState))
    (show mapLiteral rename ((decoderNode parameters .healthy node (decoderPositionBefore .healthy node)).slots
       (.internal (.decoder .healthy node))) = mapLiteral rename (decoderLiveAndOutput .healthy node) by
      rw [decoderDisjunction_output .healthy node [] shape]
      simp only [decoderDisjunctionOutput, SourceSerialFold.allocate, List.map_nil, decoderLiveAndOutput])
    (show mapLiteral rename ((decoderNode parameters .faulty node (decoderPositionBefore .faulty node)).slots
       (.internal (.decoder .faulty node))) = mapLiteral rename (decoderLiveAndOutput .faulty node) by
      rw [decoderDisjunction_output .faulty node [] shape]
      simp only [decoderDisjunctionOutput, SourceSerialFold.allocate, List.map_nil, decoderLiveAndOutput])

/-- Local cursor-indexed qualifier pairs are populated by the constructed qualifier cache. -/
def DecoderQualifiersAt (rename : Nat → Fin v) (context : Clause (Fin v))
    (node : Fin parameters.decoder.nodeCount) (state : State v) :=
  ∀ channel : Fin parameters.channels, DirectionPair state context
    (mapLiteral rename ((decoderPositionBefore .healthy node).slots (.internal (.qualifier .healthy channel))))
    (mapLiteral rename ((decoderPositionBefore .faulty node).slots (.internal (.qualifier .faulty channel))))

def decoderProjectionBudget {state : State v} {context : Clause (Fin v)}
    {left right : Literal (Fin v)} {before after : Nat}
    (projection : PairedProjection state context left right before) (equal : before = after) :
    PairedProjection state context left right after :=
  Eq.mp (congrArg (PairedProjection state context left right) equal) projection

/-- Dispatches the actual stored node form, with no generated program or clause oracle. -/
def decoderNodeProjection (rename : Nat → Fin v) (context : Clause (Fin v))
    (node : Fin parameters.decoder.nodeCount)
    (table : DecoderPairTable (parameters := parameters) rename context node.val)
    (qualifiers : DecoderQualifiersAt rename context node table.prefixState.state) :
    PairedProjection table.prefixState.state context
      (mapLiteral rename ((decoderNode parameters .healthy node (decoderPositionBefore .healthy node)).slots
        (.internal (.decoder .healthy node))))
      (mapLiteral rename ((decoderNode parameters .faulty node (decoderPositionBefore .faulty node)).slots
        (.internal (.decoder .faulty node)))) (decoderNodeBudget node) := by
  match shape : parameters.decoder.node node with
  | .zero =>
    exact decoderProjectionBudget (completeZeroNode rename context node shape table)
      (by simp only [decoderNodeBudget, shape])
  | .input channel =>
    exact decoderProjectionBudget
      (completeInputNode rename context node channel shape table (qualifiers channel))
      (by simp only [decoderNodeBudget, shape])
  | .disj children =>
    match children with
    | [] =>
      exact decoderProjectionBudget (completeEmptyDisjunctionNode rename context node shape table)
        (by simp only [decoderNodeBudget, shape, List.length_nil, Nat.mul_zero])
    | first :: rest =>
      exact decoderProjectionBudget
        (completeDisjunctionNode rename context node (first :: rest) shape (by simp) table)
        (by simp only [decoderNodeBudget, shape, decoderChildPairs, List.length_map])
  | .guard child labels =>
    exact decoderProjectionBudget
      (completeGuardNode rename context node child labels shape table qualifiers)
      (by simp only [decoderNodeBudget, shape])
  | .liveAnd left right =>
    exact decoderProjectionBudget
      (completeLiveAndNode rename context node left right shape table)
      (by simp only [decoderNodeBudget, shape])

/-- One source node is fetched once by the finite topological table traversal. -/
def decoderTableAdvance (rename : Nat → Fin v) (context : Clause (Fin v))
    (node : Fin parameters.decoder.nodeCount)
    (table : DecoderPairTable (parameters := parameters) rename context node.val)
    (qualifiers : DecoderQualifiersAt rename context node table.prefixState.state) :
    DecoderPairTable (parameters := parameters) rename context (node.val + 1) :=
  decoderTableAppend rename context node table (decoderNodeProjection rename context node table qualifiers)


theorem decoderCursorAt_qualifier (side querySide : Side) (channel : Fin parameters.channels)
    (count : Nat) :
    (decoderCursorAt side count).slots (.internal (.qualifier querySide channel)) =
      (decoderStart side).slots (.internal (.qualifier querySide channel)) := by
  unfold decoderCursorAt
  exact Controller.NativeProof.SourceSlotFrames.foldl_slot _ _
    (fun cursor node => decoderNode_qualifier side querySide node channel cursor) _ _

/-- Stored qualifier outputs are carried through decoder proof traces unchanged. -/
def DecoderQualifierCache (rename : Nat → Fin v) (context : Clause (Fin v)) (state : State v) :=
  ∀ channel : Fin parameters.channels, DirectionPair state context
    (mapLiteral rename ((decoderStart .healthy).slots (.internal (.qualifier .healthy channel))))
    (mapLiteral rename ((decoderStart .faulty).slots (.internal (.qualifier .faulty channel))))

def decoderQualifiersAt (rename : Nat → Fin v) (context : Clause (Fin v))
    (node : Fin parameters.decoder.nodeCount) (state : State v)
    (cache : DecoderQualifierCache (parameters := parameters) rename context state) : DecoderQualifiersAt rename context node state := by
  intro channel
  exact decoderDirectionRetarget (cache channel)
    (by rw [← decoderCursorAt_before, decoderCursorAt_qualifier])
    (by rw [← decoderCursorAt_before, decoderCursorAt_qualifier])

structure QualifiedDecoderTable (rename : Nat → Fin v) (context : Clause (Fin v)) (count : Nat) where
  table : DecoderPairTable (parameters := parameters) rename context count
  qualifiers : DecoderQualifierCache (parameters := parameters) rename context table.prefixState.state

def qualifiedDecoderInitial (rename : Nat → Fin v) (context : Clause (Fin v))
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (cache : DecoderQualifierCache (parameters := parameters) rename context prefixState.state) :
    QualifiedDecoderTable (parameters := parameters) rename context 0 :=
  ⟨decoderTableInitial rename context prefixState, cache⟩

def qualifiedDecoderAdvance (rename : Nat → Fin v) (context : Clause (Fin v))
    (node : Fin parameters.decoder.nodeCount)
    (current : QualifiedDecoderTable (parameters := parameters) rename context node.val) :
    QualifiedDecoderTable (parameters := parameters) rename context (node.val + 1) := by
  let added := decoderNodeProjection rename context node current.table
    (decoderQualifiersAt rename context node current.table.prefixState.state current.qualifiers)
  refine ⟨decoderTableAppend rename context node current.table added, ?_⟩
  intro channel
  exact (current.qualifiers channel).afterTrace added.state added.steps added.checked

/-- The constructor traverses each stored decoder index once in its actual order. -/
def buildQualifiedDecoder (rename : Nat → Fin v) (context : Clause (Fin v))
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (cache : DecoderQualifierCache (parameters := parameters) rename context prefixState.state)
    (count : Nat) (bounded : count ≤ parameters.decoder.nodeCount) :
    QualifiedDecoderTable (parameters := parameters) rename context count :=
  match count with
  | 0 => qualifiedDecoderInitial rename context prefixState cache
  | count + 1 => qualifiedDecoderAdvance rename context ⟨count, by omega⟩
      (buildQualifiedDecoder rename context prefixState cache count (by omega))

def decoderPrefixBudget (count : Nat) : Nat :=
  (((List.finRange parameters.decoder.nodeCount).take count).map
    (decoderNodeBudget (parameters := parameters))).sum

theorem decoderPrefixBudget_succ (node : Fin parameters.decoder.nodeCount) :
    decoderPrefixBudget (parameters := parameters) (node.val + 1) =
      decoderPrefixBudget (parameters := parameters) node.val + decoderNodeBudget node := by
  unfold decoderPrefixBudget
  rw [List.take_succ_eq_append_getElem (by simpa only [List.length_finRange] using node.isLt), List.map_append,
    List.sum_append]
  simp only [List.getElem_finRange, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
  congr 1

theorem qualifiedDecoderAdvance_count (rename : Nat → Fin v) (context : Clause (Fin v))
    (node : Fin parameters.decoder.nodeCount)
    (current : QualifiedDecoderTable (parameters := parameters) rename context node.val) :
    (qualifiedDecoderAdvance rename context node current).table.prefixState.steps.length ≤
      current.table.prefixState.steps.length + decoderNodeBudget node :=
  decoderTableAppend_count rename context node current.table _

theorem buildQualifiedDecoder_count (rename : Nat → Fin v) (context : Clause (Fin v))
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (cache : DecoderQualifierCache (parameters := parameters) rename context prefixState.state)
    (count : Nat) (bounded : count ≤ parameters.decoder.nodeCount) :
    (buildQualifiedDecoder (parameters := parameters) rename context prefixState cache count bounded).table.prefixState.steps.length ≤
      prefixState.steps.length + decoderPrefixBudget (parameters := parameters) count := by
  induction count with
  | zero =>
    simp only [buildQualifiedDecoder, qualifiedDecoderInitial, decoderTableInitial,
      decoderPrefixBudget, List.take_zero, List.map_nil, List.sum_nil, Nat.add_zero]
    exact Nat.le_refl _
  | succ count ih =>
    have next := qualifiedDecoderAdvance_count (parameters := parameters) rename context ⟨count, by omega⟩
      (buildQualifiedDecoder (parameters := parameters) rename context prefixState cache count (by omega))
    have previous := ih (by omega)
    simp only [buildQualifiedDecoder]
    have scalar : decoderPrefixBudget (parameters := parameters) (count + 1) =
        decoderPrefixBudget (parameters := parameters) count + decoderNodeBudget (parameters := parameters) ⟨count, by omega⟩ :=
      decoderPrefixBudget_succ (parameters := parameters) ⟨count, by omega⟩
    calc
      _ ≤ (buildQualifiedDecoder (parameters := parameters) rename context prefixState cache count (by omega)).table.prefixState.steps.length +
          decoderNodeBudget (parameters := parameters) ⟨count, by omega⟩ := next
      _ ≤ (prefixState.steps.length + decoderPrefixBudget (parameters := parameters) count) +
          decoderNodeBudget (parameters := parameters) ⟨count, by omega⟩ := Nat.add_le_add_right previous _
      _ = prefixState.steps.length + decoderPrefixBudget (parameters := parameters) (count + 1) := by
        rw [scalar, Nat.add_assoc]

def completeQualifiedDecoder (rename : Nat → Fin v) (context : Clause (Fin v))
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (cache : DecoderQualifierCache (parameters := parameters) rename context prefixState.state) :=
  buildQualifiedDecoder rename context prefixState cache parameters.decoder.nodeCount (Nat.le_refl _)


/-- Exported directional pairs stop at stored decoder roots before observation producers. -/
def completeDecoderRoots (rename : Nat → Fin v) (context : Clause (Fin v))
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (cache : DecoderQualifierCache (parameters := parameters) rename context prefixState.state)
    (index : Fin parameters.decoder.roots.length) :
    DirectionPair (completeQualifiedDecoder rename context prefixState cache).table.prefixState.state context
      (mapLiteral rename ((attachDecoder parameters .healthy (decoderStart .healthy)).slots
        (.internal (.decoder .healthy parameters.decoder.roots[index.val]))))
      (mapLiteral rename ((attachDecoder parameters .faulty (decoderStart .faulty)).slots
        (.internal (.decoder .faulty parameters.decoder.roots[index.val])))) := by
  let completed := completeQualifiedDecoder rename context prefixState cache
  have actual := completed.table.pairs parameters.decoder.roots[index.val]
    parameters.decoder.roots[index.val].isLt
  have whole : (List.finRange parameters.decoder.nodeCount).take parameters.decoder.nodeCount =
      List.finRange parameters.decoder.nodeCount := List.take_of_length_le (by simp)
  simpa only [whole, attachDecoder] using actual


theorem decoderZeroUnit_allowed (rename : Nat → Fin v) (side : Side)
    (node : Fin parameters.decoder.nodeCount) (shape : parameters.decoder.node node = .zero)
    (prefixState : SourcePrefix (parameters := parameters) rename) :
    AllowedOriginal (parameters := parameters) rename (decoderZeroUnit rename side node shape prefixState).row.id :=
  decoderZeroRows_allowed rename side node shape ⟨0, by simp⟩

theorem decoderEmptyDisjunctionSupply_supported (rename : Nat → Fin v) (side : Side)
    (node : Fin parameters.decoder.nodeCount) (shape : parameters.decoder.node node = .disj []) :
    SupplyOriginals (AllowedOriginal (parameters := parameters) rename)
      (decoderEmptyDisjunctionSupply rename side node shape) := by
  dsimp only [decoderEmptyDisjunctionSupply]
  exact supplyOriginals_transport (AllowedOriginal (parameters := parameters) rename) rename
    (by simp only [List.map_nil, SourceSerialFold.allocate, Bounded.Junction.gate, decoderLiveAndOutput])
    (decoderDisjunctionRowsExact rename side node [] shape)
    (decoderDisjunctionRowsExact_allowed rename side node [] shape)

theorem decoderEmptyDisjunctionUnit_allowed (rename : Nat → Fin v) (side : Side)
    (node : Fin parameters.decoder.nodeCount) (shape : parameters.decoder.node node = .disj [])
    (prefixState : SourcePrefix (parameters := parameters) rename) :
    AllowedOriginal (parameters := parameters) rename
      (decoderEmptyDisjunctionUnit rename side node shape prefixState).row.id :=
  decoderEmptyDisjunctionSupply_supported rename side node shape ⟨0, by simp⟩ ⟨0, by change 0 < 1; omega⟩

theorem pairedEmptyDecoder_supported (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (context : Clause (Fin v)) (left right : Literal (Fin v))
    (leftUnit : AvailableSubclause prefixState.state [negate left])
    (rightUnit : AvailableSubclause prefixState.state [negate right])
    (supported : PrefixOriginalSupport rename prefixState)
    (leftOrigin : Controller.NativeProof.SourceMismatchHandles.ResultOrigin (formula parameters).clauses.size
      (AllowedOriginal (parameters := parameters) rename) prefixState.steps leftUnit.row.id)
    (rightOrigin : Controller.NativeProof.SourceMismatchHandles.ResultOrigin (formula parameters).clauses.size
      (AllowedOriginal (parameters := parameters) rename) prefixState.steps rightUnit.row.id) :
    PairedProjectionOriginalSupport rename prefixState
      (pairedEmptyDecoder prefixState.state context left right leftUnit rightUnit) := by
  constructor
  · simpa only [pairedEmptyDecoder, PrefixOriginalSupport, SourcePrefix.extend, List.append_nil] using supported
  · change Controller.NativeProof.SourceMismatchHandles.ResultOrigin (formula parameters).clauses.size
        (AllowedOriginal (parameters := parameters) rename) (prefixState.steps ++ []) leftUnit.row.id ∧
      Controller.NativeProof.SourceMismatchHandles.ResultOrigin (formula parameters).clauses.size
        (AllowedOriginal (parameters := parameters) rename) (prefixState.steps ++ []) rightUnit.row.id
    simpa only [List.append_nil] using And.intro leftOrigin rightOrigin

theorem completeZeroNode_supported (rename : Nat → Fin v) (context : Clause (Fin v))
    (node : Fin parameters.decoder.nodeCount) (shape : parameters.decoder.node node = .zero)
    (table : DecoderPairTable (parameters := parameters) rename context node.val)
    (supported : DecoderPairTableOriginalSupport rename context node.val table) :
    PairedProjectionOriginalSupport rename table.prefixState (completeZeroNode rename context node shape table) :=
  decoderProjectionRetarget_supported rename table.prefixState _ _ _
    (pairedEmptyDecoder_supported rename table.prefixState context _ _ _ _ supported.1
      (Or.inl (decoderZeroUnit_allowed rename .healthy node shape table.prefixState))
      (Or.inl (decoderZeroUnit_allowed rename .faulty node shape table.prefixState)))

theorem completeEmptyDisjunctionNode_supported (rename : Nat → Fin v) (context : Clause (Fin v))
    (node : Fin parameters.decoder.nodeCount) (shape : parameters.decoder.node node = .disj [])
    (table : DecoderPairTable (parameters := parameters) rename context node.val)
    (supported : DecoderPairTableOriginalSupport rename context node.val table) :
    PairedProjectionOriginalSupport rename table.prefixState
      (completeEmptyDisjunctionNode rename context node shape table) :=
  decoderProjectionRetarget_supported rename table.prefixState _ _ _
    (pairedEmptyDecoder_supported rename table.prefixState context _ _ _ _ supported.1
      (Or.inl (decoderEmptyDisjunctionUnit_allowed rename .healthy node shape table.prefixState))
      (Or.inl (decoderEmptyDisjunctionUnit_allowed rename .faulty node shape table.prefixState)))


theorem decoderPairProjection_supported (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    {context : Clause (Fin v)} {left right : Literal (Fin v)}
    (pair : DirectionPair prefixState.state context left right)
    (supported : PrefixOriginalSupport rename prefixState)
    (origin : DirectionPairOrigin rename prefixState pair) :
    PairedProjectionOriginalSupport rename prefixState (decoderPairProjection pair) := by
  constructor
  · simpa only [decoderPairProjection, PrefixOriginalSupport, SourcePrefix.extend, List.append_nil] using supported
  · exact decoderPairOrigin_same_steps rename prefixState.state prefixState.steps (prefixState.steps ++ [])
      (by simp) prefixState.checked (prefixState.extend prefixState.state [] rfl).checked pair origin

theorem completeInputNode_supported (rename : Nat → Fin v) (context : Clause (Fin v))
    (node : Fin parameters.decoder.nodeCount) (channel : Fin parameters.channels)
    (shape : parameters.decoder.node node = .input channel)
    (table : DecoderPairTable (parameters := parameters) rename context node.val)
    (qualifier : DirectionPair table.prefixState.state context
      (mapLiteral rename ((decoderPositionBefore .healthy node).slots (.internal (.qualifier .healthy channel))))
      (mapLiteral rename ((decoderPositionBefore .faulty node).slots (.internal (.qualifier .faulty channel)))))
    (supported : DecoderPairTableOriginalSupport rename context node.val table)
    (origin : DirectionPairOrigin rename table.prefixState qualifier) :
    PairedProjectionOriginalSupport rename table.prefixState
      (completeInputNode rename context node channel shape table qualifier) :=
  decoderProjectionRetarget_supported rename table.prefixState _ _ _
    (decoderPairProjection_supported rename table.prefixState qualifier supported.1 origin)


theorem decoderProjectionBudget_supported (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    {context : Clause (Fin v)} {left right : Literal (Fin v)} {before after : Nat}
    (projection : PairedProjection prefixState.state context left right before) (equal : before = after)
    (supported : PairedProjectionOriginalSupport rename prefixState projection) :
    PairedProjectionOriginalSupport rename prefixState (decoderProjectionBudget projection equal) := by
  cases equal
  exact supported

def DecoderQualifiersAtOriginalSupport (rename : Nat → Fin v) (context : Clause (Fin v))
    (node : Fin parameters.decoder.nodeCount) (prefixState : SourcePrefix (parameters := parameters) rename)
    (qualifiers : DecoderQualifiersAt rename context node prefixState.state) : Prop :=
  ∀ channel, DirectionPairOrigin rename prefixState (qualifiers channel)

theorem decoderNodeProjection_supported (rename : Nat → Fin v) (context : Clause (Fin v))
    (node : Fin parameters.decoder.nodeCount)
    (table : DecoderPairTable (parameters := parameters) rename context node.val)
    (qualifiers : DecoderQualifiersAt rename context node table.prefixState.state)
    (supported : DecoderPairTableOriginalSupport rename context node.val table)
    (qualifierOrigins : DecoderQualifiersAtOriginalSupport rename context node table.prefixState qualifiers) :
    PairedProjectionOriginalSupport rename table.prefixState (decoderNodeProjection rename context node table qualifiers) := by
  unfold decoderNodeProjection
  split
  · exact decoderProjectionBudget_supported rename table.prefixState _ _
      (completeZeroNode_supported rename context node (by assumption) table supported)
  · exact decoderProjectionBudget_supported rename table.prefixState _ _
      (completeInputNode_supported rename context node _ (by assumption) table _ supported
        (qualifierOrigins _))
  · split
    · exact decoderProjectionBudget_supported rename table.prefixState _ _
        (completeEmptyDisjunctionNode_supported rename context node (by assumption) table supported)
    · exact decoderProjectionBudget_supported rename table.prefixState _ _
        (completeDisjunctionNode_supported rename context node _ (by assumption) (by simp) table supported)
  · exact decoderProjectionBudget_supported rename table.prefixState _ _
      (completeGuardNode_supported rename context node _ _ (by assumption) table _ supported qualifierOrigins)
  · exact decoderProjectionBudget_supported rename table.prefixState _ _
      (completeLiveAndNode_supported rename context node _ _ (by assumption) table supported)


def DecoderQualifierCacheOriginalSupport (rename : Nat → Fin v) (context : Clause (Fin v))
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (cache : DecoderQualifierCache (parameters := parameters) rename context prefixState.state) : Prop :=
  ∀ channel, DirectionPairOrigin rename prefixState (cache channel)

theorem decoderQualifiersAt_supported (rename : Nat → Fin v) (context : Clause (Fin v))
    (node : Fin parameters.decoder.nodeCount)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (cache : DecoderQualifierCache (parameters := parameters) rename context prefixState.state)
    (original : DecoderQualifierCacheOriginalSupport rename context prefixState cache) :
    DecoderQualifiersAtOriginalSupport rename context node prefixState
      (decoderQualifiersAt rename context node prefixState.state cache) := by
  intro channel
  exact decoderDirectionRetarget_supported rename prefixState (cache channel) _ _ (original channel)

def QualifiedDecoderTableOriginalSupport (rename : Nat → Fin v) (context : Clause (Fin v))
    (count : Nat) (table : QualifiedDecoderTable (parameters := parameters) rename context count) : Prop :=
  DecoderPairTableOriginalSupport rename context count table.table ∧
    DecoderQualifierCacheOriginalSupport rename context table.table.prefixState table.qualifiers

theorem qualifiedDecoderInitial_supported (rename : Nat → Fin v) (context : Clause (Fin v))
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (cache : DecoderQualifierCache (parameters := parameters) rename context prefixState.state)
    (supported : PrefixOriginalSupport rename prefixState)
    (original : DecoderQualifierCacheOriginalSupport rename context prefixState cache) :
    QualifiedDecoderTableOriginalSupport rename context 0
      (qualifiedDecoderInitial rename context prefixState cache) :=
  ⟨decoderTableInitial_supported rename context prefixState supported, original⟩

theorem qualifiedDecoderAdvance_supported (rename : Nat → Fin v) (context : Clause (Fin v))
    (node : Fin parameters.decoder.nodeCount)
    (current : QualifiedDecoderTable (parameters := parameters) rename context node.val)
    (original : QualifiedDecoderTableOriginalSupport rename context node.val current) :
    QualifiedDecoderTableOriginalSupport rename context (node.val + 1)
      (qualifiedDecoderAdvance rename context node current) := by
  let added := decoderNodeProjection rename context node current.table
    (decoderQualifiersAt rename context node current.table.prefixState.state current.qualifiers)
  have addedOriginal : PairedProjectionOriginalSupport rename current.table.prefixState added :=
    decoderNodeProjection_supported rename context node current.table _ original.1
      (decoderQualifiersAt_supported rename context node current.table.prefixState current.qualifiers original.2)
  refine ⟨decoderTableAppend_supported rename context node current.table original.1 added addedOriginal, ?_⟩
  intro channel
  exact DirectionPairOrigin.afterTrace rename current.table.prefixState (current.qualifiers channel)
    (original.2 channel) added.state added.steps added.checked

theorem buildQualifiedDecoder_supported (rename : Nat → Fin v) (context : Clause (Fin v))
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (cache : DecoderQualifierCache (parameters := parameters) rename context prefixState.state)
    (supported : PrefixOriginalSupport rename prefixState)
    (original : DecoderQualifierCacheOriginalSupport rename context prefixState cache)
    (count : Nat) (bounded : count ≤ parameters.decoder.nodeCount) :
    QualifiedDecoderTableOriginalSupport rename context count
      (buildQualifiedDecoder rename context prefixState cache count bounded) := by
  induction count with
  | zero => exact qualifiedDecoderInitial_supported rename context prefixState cache supported original
  | succ count ih =>
    exact qualifiedDecoderAdvance_supported rename context ⟨count, by omega⟩
      (buildQualifiedDecoder rename context prefixState cache count (by omega)) (ih (by omega))

theorem completeQualifiedDecoder_supported (rename : Nat → Fin v) (context : Clause (Fin v))
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (cache : DecoderQualifierCache (parameters := parameters) rename context prefixState.state)
    (supported : PrefixOriginalSupport rename prefixState)
    (original : DecoderQualifierCacheOriginalSupport rename context prefixState cache) :
    QualifiedDecoderTableOriginalSupport rename context parameters.decoder.nodeCount
      (completeQualifiedDecoder rename context prefixState cache) :=
  buildQualifiedDecoder_supported rename context prefixState cache supported original
    parameters.decoder.nodeCount (Nat.le_refl _)


theorem resultOrigin_controller_to_decoder (rename : Nat → Fin v)
    (steps : List (Step v)) (id : Nat)
    (origin : Controller.NativeProof.SourceMismatchHandles.ResultOrigin (formula parameters).clauses.size
      (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename) steps id) :
    Controller.NativeProof.SourceMismatchHandles.ResultOrigin (formula parameters).clauses.size
      (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) steps id := by
  rcases origin with original | earlier
  · exact Or.inl (SourceDecoderSchedule.controller_original_allowed rename id original)
  · exact Or.inr earlier

theorem prefix_controller_to_decoder (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (origin : SourceMixedSchedule.PrefixOriginalSupport rename prefixState) :
    SourceDecoderSchedule.PrefixOriginalSupport rename prefixState := by
  intro step member parent parentMember
  have previous := origin step member parent parentMember
  exact ⟨fun bounded => SourceDecoderSchedule.controller_original_allowed rename parent
    (previous.1 bounded), previous.2⟩

theorem guardedTransfer_controller_to_decoder (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    {context : Clause (Fin v)} {input output : Literal (Fin v)}
    (transfer : GuardedTransfer prefixState.state context input output)
    (origin : SourceEqualSchedule.GuardedTransferOrigin rename prefixState transfer) :
    SourceDecoderSchedule.GuardedTransferOrigin rename prefixState transfer := by
  cases transfer with
  | identity same => trivial
  | derived row => exact resultOrigin_controller_to_decoder rename prefixState.steps row.row.id origin

theorem directionPair_controller_to_decoder (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    {context : Clause (Fin v)} {input output : Literal (Fin v)}
    (pair : DirectionPair prefixState.state context input output)
    (origin : SourceEqualSchedule.DirectionPairOrigin rename prefixState pair) :
    SourceDecoderSchedule.DirectionPairOrigin rename prefixState pair :=
  ⟨guardedTransfer_controller_to_decoder rename prefixState pair.forward origin.1,
   guardedTransfer_controller_to_decoder rename prefixState pair.backward origin.2⟩


theorem decoderComplete_slot (side : Side) (node : Fin parameters.decoder.nodeCount) :
    (attachDecoder parameters side (decoderStart side)).slots (.internal (.decoder side node)) =
      (decoderCursorAt side parameters.decoder.nodeCount).slots (.internal (.decoder side node)) := by
  unfold decoderCursorAt attachDecoder
  rw [List.take_of_length_le (by simp)]

def completeDecoderRootPair (rename : Nat → Fin v) (context : Clause (Fin v))
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (cache : DecoderQualifierCache (parameters := parameters) rename context prefixState.state)
    (index : Fin parameters.decoder.roots.length) :
    DirectionPair (completeQualifiedDecoder rename context prefixState cache).table.prefixState.state context
      (mapLiteral rename ((attachDecoder parameters .healthy (decoderStart .healthy)).slots
        (.internal (.decoder .healthy parameters.decoder.roots[index.val]))))
      (mapLiteral rename ((attachDecoder parameters .faulty (decoderStart .faulty)).slots
        (.internal (.decoder .faulty parameters.decoder.roots[index.val])))) :=
  let completed := completeQualifiedDecoder rename context prefixState cache
  let node := parameters.decoder.roots[index.val]
  decoderDirectionRetarget (completed.table.pairs node node.isLt)
    (congrArg (mapLiteral rename) (decoderComplete_slot .healthy node))
    (congrArg (mapLiteral rename) (decoderComplete_slot .faulty node))

theorem completeDecoderRootPair_supported (rename : Nat → Fin v) (context : Clause (Fin v))
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (cache : DecoderQualifierCache (parameters := parameters) rename context prefixState.state)
    (supported : PrefixOriginalSupport rename prefixState)
    (original : DecoderQualifierCacheOriginalSupport rename context prefixState cache)
    (index : Fin parameters.decoder.roots.length) :
    DirectionPairOrigin rename (completeQualifiedDecoder rename context prefixState cache).table.prefixState
      (completeDecoderRootPair rename context prefixState cache index) := by
  let completed := completeQualifiedDecoder rename context prefixState cache
  let node := parameters.decoder.roots[index.val]
  have origins := completeQualifiedDecoder_supported rename context prefixState cache supported original
  exact decoderDirectionRetarget_supported rename completed.table.prefixState
    (completed.table.pairs node node.isLt)
    (congrArg (mapLiteral rename) (decoderComplete_slot .healthy node))
    (congrArg (mapLiteral rename) (decoderComplete_slot .faulty node))
    (origins.1.2 node node.isLt)


def equalDecoderPrefix (rename : Nat → Fin v) (flag : Bool) :
    SourcePrefix (parameters := parameters) rename :=
  (SourceQualifierSchedule.allChannelQualifiers (parameters := parameters) rename flag).nots.cache.masks.checkedPrefix

def constructedQualifierCache (rename : Nat → Fin v) (flag : Bool) :
    DecoderQualifierCache (parameters := parameters) rename
      (SourceBusSchedule.equalFlagContext (parameters := parameters) rename flag)
      (equalDecoderPrefix (parameters := parameters) rename flag).state :=
  fun channel => SourceQualifierSchedule.constructedDecoderQualifier rename flag channel

theorem constructedQualifierCache_supported (rename : Nat → Fin v) (flag : Bool) :
    DecoderQualifierCacheOriginalSupport rename
      (SourceBusSchedule.equalFlagContext (parameters := parameters) rename flag)
      (equalDecoderPrefix rename flag) (constructedQualifierCache rename flag) := by
  intro channel
  exact directionPair_controller_to_decoder rename (equalDecoderPrefix rename flag) _
    (SourceQualifierSchedule.constructedDecoderQualifier_supported rename flag channel)

def equalDecoderProgram (rename : Nat → Fin v) (flag : Bool) :=
  completeQualifiedDecoder rename
    (SourceBusSchedule.equalFlagContext (parameters := parameters) rename flag)
    (equalDecoderPrefix rename flag) (constructedQualifierCache rename flag)

theorem equalDecoderProgram_supported (rename : Nat → Fin v) (flag : Bool) :
    QualifiedDecoderTableOriginalSupport rename
      (SourceBusSchedule.equalFlagContext (parameters := parameters) rename flag)
      parameters.decoder.nodeCount (equalDecoderProgram rename flag) :=
  completeQualifiedDecoder_supported rename _ _ _
    (prefix_controller_to_decoder rename _
      (SourceQualifierSchedule.allChannelQualifiers_supported rename flag).1.1.1.1)
    (constructedQualifierCache_supported rename flag)


def equalDecoderProgramBudget (parameters : Parameters) : Nat :=
  SourceQualifierSchedule.qualifierProgramBudget parameters +
    decoderPrefixBudget (parameters := parameters) parameters.decoder.nodeCount

theorem equalDecoderProgram_count (rename : Nat → Fin v) (flag : Bool) :
    (equalDecoderProgram (parameters := parameters) rename flag).table.prefixState.steps.length ≤
      equalDecoderProgramBudget parameters := by
  have actual := buildQualifiedDecoder_count (parameters := parameters) rename
    (equalFlagContext (parameters := parameters) rename flag)
    (equalDecoderPrefix (parameters := parameters) rename flag)
    (constructedQualifierCache (parameters := parameters) rename flag)
    parameters.decoder.nodeCount (Nat.le_refl _)
  have initial := SourceQualifierSchedule.allChannelQualifiers_count (parameters := parameters) rename flag
  exact actual.trans (Nat.add_le_add_right initial _)

def equalDecoderRoot (rename : Nat → Fin v) (flag : Bool)
    (index : Fin parameters.decoder.roots.length) :=
  completeDecoderRootPair rename (equalFlagContext (parameters := parameters) rename flag)
    (equalDecoderPrefix (parameters := parameters) rename flag)
    (constructedQualifierCache (parameters := parameters) rename flag) index

theorem equalDecoderRoot_supported (rename : Nat → Fin v) (flag : Bool)
    (index : Fin parameters.decoder.roots.length) :
    DirectionPairOrigin rename
      (equalDecoderProgram (parameters := parameters) rename flag).table.prefixState
      (equalDecoderRoot (parameters := parameters) rename flag index) :=
  completeDecoderRootPair_supported rename _ _ _
    (prefix_controller_to_decoder rename _
      (SourceQualifierSchedule.allChannelQualifiers_supported (parameters := parameters) rename flag).1.1.1.1)
    (constructedQualifierCache_supported rename flag) index


/-- Native paired-gate sites are indexed by their stored controller or decoder positions. -/
inductive NativeGateSite (parameters : Parameters) where
  | firstMask (channel : Fin parameters.channels)
  | laterTerm (position : Fin (laterBuses (parameters := parameters)).length) (channel : Fin parameters.channels)
  | laterFlag (position : Fin (laterBuses (parameters := parameters)).length)
  | laterAbsent (position : Fin (laterBuses (parameters := parameters)).length) (channel : Fin parameters.channels)
  | laterMask (position : Fin (laterBuses (parameters := parameters)).length) (channel : Fin parameters.channels)
  | privateNot (bus : Fin parameters.buses)
  | qualifierGuard (channel : Fin parameters.channels) (bus : Fin parameters.buses)
  | qualifierAnd (channel : Fin parameters.channels)
  | decoderNode (node : Fin parameters.decoder.nodeCount)
  deriving DecidableEq

def nativeGateSites (parameters : Parameters) : List (NativeGateSite parameters) :=
  (List.finRange parameters.channels).map NativeGateSite.firstMask ++
  (List.finRange (laterBuses (parameters := parameters)).length).flatMap (fun position =>
    (List.finRange parameters.channels).map (NativeGateSite.laterTerm position)) ++
  (List.finRange (laterBuses (parameters := parameters)).length).map NativeGateSite.laterFlag ++
  (List.finRange (laterBuses (parameters := parameters)).length).flatMap (fun position =>
    (List.finRange parameters.channels).map (NativeGateSite.laterAbsent position)) ++
  (List.finRange (laterBuses (parameters := parameters)).length).flatMap (fun position =>
    (List.finRange parameters.channels).map (NativeGateSite.laterMask position)) ++
  (List.finRange parameters.buses).map NativeGateSite.privateNot ++
  (List.finRange parameters.channels).flatMap (fun channel =>
    (List.finRange parameters.buses).map (NativeGateSite.qualifierGuard channel)) ++
  (List.finRange parameters.channels).map NativeGateSite.qualifierAnd ++
  (List.finRange parameters.decoder.nodeCount).map NativeGateSite.decoderNode

theorem nativeGateSites_complete (site : NativeGateSite parameters) :
    site ∈ nativeGateSites parameters := by
  cases site <;> simp [nativeGateSites, List.mem_flatMap, List.mem_map, List.mem_finRange]

theorem nativeGateSites_length (parameters : Parameters) :
    (nativeGateSites parameters).length =
      2 * parameters.channels +
        3 * ((laterBuses (parameters := parameters)).length * parameters.channels) +
        (laterBuses (parameters := parameters)).length + parameters.buses +
        parameters.channels * parameters.buses + parameters.decoder.nodeCount := by
  simp only [nativeGateSites, List.length_append, List.length_map, List.length_flatMap,
    List.length_finRange]
  simp only [List.map_const', List.sum_replicate, Nat.nsmul_eq_mul, List.length_finRange]
  omega

/-- Both first-flag equal cofactors and both directional clauses have separate sites. -/
def directionalGateSites (parameters : Parameters) : List (Bool × Bool × NativeGateSite parameters) :=
  [false, true].flatMap fun flag => [false, true].flatMap fun backward =>
    (nativeGateSites parameters).map fun site => (flag, backward, site)

theorem directionalGateSites_complete (flag backward : Bool) (site : NativeGateSite parameters) :
    (flag, backward, site) ∈ directionalGateSites parameters := by
  cases flag <;> cases backward <;>
    simp [directionalGateSites, nativeGateSites_complete site]

theorem directionalGateSites_length (parameters : Parameters) :
    (directionalGateSites parameters).length = 4 * (nativeGateSites parameters).length := by
  simp only [directionalGateSites, List.flatMap_cons, List.flatMap_nil, List.length_append,
    List.length_map, List.append_nil]
  omega

/-- Mixed selector sites follow the actual C-bank, B-term and A-leaf callback domains. -/
inductive MixedSelectorSite (parameters : Parameters) where
  | leaf (position : Fin (laterBuses (parameters := parameters)).length)
      (channel : Fin parameters.channels) (index : Fin (1 + parameters.buses))
  | term (position : Fin (laterBuses (parameters := parameters)).length) (channel : Fin parameters.channels)
  | flag (position : Fin (laterBuses (parameters := parameters)).length)
  | activationLeaf (index : Fin (1 + parameters.buses))
  deriving DecidableEq

def mixedSelectorSites (parameters : Parameters) : List (MixedSelectorSite parameters) :=
  (List.finRange (laterBuses (parameters := parameters)).length).flatMap (fun position =>
    (List.finRange parameters.channels).flatMap fun channel =>
      (List.finRange (1 + parameters.buses)).map (MixedSelectorSite.leaf position channel)) ++
  (List.finRange (laterBuses (parameters := parameters)).length).flatMap (fun position =>
    (List.finRange parameters.channels).map (MixedSelectorSite.term position)) ++
  (List.finRange (laterBuses (parameters := parameters)).length).map MixedSelectorSite.flag ++
  (List.finRange (1 + parameters.buses)).map MixedSelectorSite.activationLeaf

theorem mixedSelectorSites_complete (site : MixedSelectorSite parameters) :
    site ∈ mixedSelectorSites parameters := by
  cases site <;> simp [mixedSelectorSites, List.mem_flatMap, List.mem_map, List.mem_finRange]

theorem mixedSelectorSites_length (parameters : Parameters) :
    (mixedSelectorSites parameters).length =
      (laterBuses (parameters := parameters)).length * parameters.channels * (1 + parameters.buses) +
      (laterBuses (parameters := parameters)).length * parameters.channels +
      (laterBuses (parameters := parameters)).length + (1 + parameters.buses) := by
  simp only [mixedSelectorSites, List.length_append, List.length_map, List.length_flatMap, List.length_finRange]
  simp only [List.map_const', List.sum_replicate, Nat.nsmul_eq_mul, List.length_finRange]
  ring

def nativeScheduledMacroCount (parameters : Parameters) : Nat :=
  (directionalGateSites parameters).length + (mixedSelectorSites parameters).length

def nativeMacroBound (n b : Nat) : Nat :=
  4 * (2 * n + 3 * (b * n) + b + b + n * b + n) +
    b * n * (1 + b) + b * n + b + (1 + b)

theorem nativeScheduledMacroCount_bound (parameters : Parameters) :
    nativeScheduledMacroCount parameters ≤
      nativeMacroBound (parameters.channels + parameters.decoder.nodeCount) parameters.buses := by
  have later : (laterBuses (parameters := parameters)).length ≤ parameters.buses := by
    simpa only [laterBuses, List.length_finRange] using
      List.length_filter_le (fun bus : Fin parameters.buses => bus.val != 0) (List.finRange parameters.buses)
  let n := parameters.channels + parameters.decoder.nodeCount
  have channels : parameters.channels ≤ n := by dsimp only [n]; omega
  have nodes : parameters.decoder.nodeCount ≤ n := by dsimp only [n]; omega
  have terms : (laterBuses (parameters := parameters)).length * parameters.channels ≤ parameters.buses * n :=
    (Nat.mul_le_mul_right parameters.channels later).trans (Nat.mul_le_mul_left parameters.buses channels)
  have guards : parameters.channels * parameters.buses ≤ n * parameters.buses :=
    Nat.mul_le_mul_right parameters.buses channels
  have leaves := Nat.mul_le_mul_right (1 + parameters.buses) terms
  unfold nativeScheduledMacroCount nativeMacroBound
  rw [directionalGateSites_length, nativeGateSites_length, mixedSelectorSites_length]
  change _ ≤ 4 * (2 * n + 3 * (parameters.buses * n) + parameters.buses + parameters.buses +
    n * parameters.buses + n) + parameters.buses * n * (1 + parameters.buses) +
    parameters.buses * n + parameters.buses + (1 + parameters.buses)
  omega

/-- Only actual fork pivots are split variables; leaf propagation reasons add none. -/
def splitVariables : Controller.Resolution.Cases.CaseTree v → Finset (Fin v)
  | .leaf _ => ∅
  | .fork pivot left right => insert pivot.1 (splitVariables left ∪ splitVariables right)

theorem xorCaseTree_splitVariables (state : State v) (target : Clause (Fin v))
    (a b : Literal (Fin v))
    (tt : AvailableSubclause state (SourceStageXor.branchTarget target a b true true))
    (tf : AvailableSubclause state (SourceStageXor.branchTarget target a b true false))
    (ft : AvailableSubclause state (SourceStageXor.branchTarget target a b false true))
    (ff : AvailableSubclause state (SourceStageXor.branchTarget target a b false false)) :
    splitVariables (SourceStageXor.xorCaseTree state target a b tt tf ft ff) = {a.1, b.1} := by
  simp [SourceStageXor.xorCaseTree, SourceStageXor.rowLeaf, splitVariables]

theorem xorCaseTree_splitVariables_card (state : State v) (target : Clause (Fin v))
    (a b : Literal (Fin v))
    (tt : AvailableSubclause state (SourceStageXor.branchTarget target a b true true))
    (tf : AvailableSubclause state (SourceStageXor.branchTarget target a b true false))
    (ft : AvailableSubclause state (SourceStageXor.branchTarget target a b false true))
    (ff : AvailableSubclause state (SourceStageXor.branchTarget target a b false false)) :
    (splitVariables (SourceStageXor.xorCaseTree state target a b tt tf ft ff)).card ≤ 2 := by
  rw [xorCaseTree_splitVariables]
  exact Finset.card_le_two

theorem contextualXor_splitVariables_le_five (state : State v) (target : Clause (Fin v))
    (firstFlag secondFlag a b : Literal (Fin v))
    (tt : AvailableSubclause state (SourceStageXor.branchTarget target a b true true))
    (tf : AvailableSubclause state (SourceStageXor.branchTarget target a b true false))
    (ft : AvailableSubclause state (SourceStageXor.branchTarget target a b false true))
    (ff : AvailableSubclause state (SourceStageXor.branchTarget target a b false false)) :
    ({firstFlag.1, secondFlag.1} ∪
      splitVariables (SourceStageXor.xorCaseTree state target a b tt tf ft ff)).card ≤ 5 := by
  have union := Finset.card_union_le {firstFlag.1, secondFlag.1}
    (splitVariables (SourceStageXor.xorCaseTree state target a b tt tf ft ff))
  have flags : ({firstFlag.1, secondFlag.1} : Finset (Fin v)).card ≤ 2 := Finset.card_le_two
  have pivots := xorCaseTree_splitVariables_card state target a b tt tf ft ff
  omega


/-- The selector conclusion uses the actual native qualifier handles before decoder emission. -/
def nativeQualifierOutputs (rename : Nat → Fin v) : Clause (Fin v) :=
  (List.finRange parameters.channels).map fun channel => mapLiteral rename
    ((decoderStart (parameters := parameters) .faulty).slots
      (.internal (.qualifier .faulty channel)))

theorem qualifierOutputs_native (rename : Nat → Fin v) :
    SourceMixedSchedule.qualifierOutputs (parameters := parameters) rename =
      nativeQualifierOutputs (parameters := parameters) rename := by
  unfold SourceMixedSchedule.qualifierOutputs nativeQualifierOutputs
  apply List.map_congr_left
  intro channel member
  exact SourceQualifierSchedule.qualifierOutput_decoderStart rename .faulty channel

/-- Retargeting preserves the actual trace and parent IDs; it inserts no inference. -/
def nativeMixedActivation (rename : Nat → Fin v) (drive : parameters.drive = true) :
    SubclauseProjection (initialState (relabel rename (formula parameters)))
      (SourceMismatchAdvance.mixedContext (parameters := parameters) rename ++
        nativeQualifierOutputs (parameters := parameters) rename)
      (parameters.buses *
        (2 * parameters.channels + parameters.channels *
          (SourceMixedSchedule.qualifierBudget parameters + 1)) + 5 * parameters.buses + 3) :=
  let actual := SourceMixedSchedule.mixedActivation rename drive
  { state := actual.state
    steps := actual.steps
    checked := actual.checked
    result := retarget actual.result (by
      intro literal member
      simpa only [qualifierOutputs_native rename] using member)
    count := actual.count }

theorem nativeMixedActivation_steps (rename : Nat → Fin v) (drive : parameters.drive = true) :
    (nativeMixedActivation rename drive).steps =
      (SourceMixedSchedule.mixedActivation rename drive).steps := rfl

theorem nativeMixedActivation_result_id (rename : Nat → Fin v) (drive : parameters.drive = true) :
    (nativeMixedActivation rename drive).result.row.id =
      (SourceMixedSchedule.mixedActivation rename drive).result.row.id := rfl

/-- Controller parents remain original parents in the larger decoder-allowed domain.
Earlier derived parents retain their exact IDs and strict chronological witnesses. -/
theorem trace_controller_to_decoder (rename : Nat → Fin v) (steps : List (Step v))
    (supported : TraceOriginalSupport (formula parameters).clauses.size
      (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename) steps) :
    TraceOriginalSupport (formula parameters).clauses.size
      (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) steps := by
  intro step member parent parentMember
  have previous := supported step member parent parentMember
  exact ⟨fun bounded => SourceDecoderSchedule.controller_original_allowed rename parent
    (previous.1 bounded), previous.2⟩

theorem nativeMixedActivation_supported (rename : Nat → Fin v) (drive : parameters.drive = true) :
    SourceDecoderSchedule.ProjectionOriginalSupport rename
      (SourcePrefix.initial (parameters := parameters) rename)
      (nativeMixedActivation rename drive) := by
  have supported := SourceMixedSchedule.mixedActivation_supported rename drive
  constructor
  · exact trace_controller_to_decoder rename _ supported.1
  · exact resultOrigin_controller_to_decoder rename _ _ supported.2


theorem newObservations_preserves (query : Controller.Native.Variable parameters)
    (cursor : Cursor parameters)
    (detected : query ≠ .internal .detected)
    (different : ∀ output : Fin parameters.decoder.roots.length,
      query ≠ .internal (.difference output)) :
    (newObservations parameters cursor).slots query = cursor.slots query := by
  unfold newObservations
  rw [SourceSlotFrames.foldNative_other _ _ _ _ _ detected]
  apply SourceSlotFrames.foldl_slot
  intro current output
  exact SourceSlotFrames.emitNative_other _ _ _ _ (different output)

theorem compiled_decoder_slot (side : Side) (node : Fin parameters.decoder.nodeCount) :
    sourceRoleMap parameters (.internal (.decoder side node)) =
      (attachDecoder parameters side (decoderStart side)).slots (.internal (.decoder side node)) := by
  unfold sourceRoleMap compile
  rw [newObservations_preserves _ _ (by simp) (fun _ => by simp)]
  cases side with
  | healthy =>
    exact attachDecoder_other .faulty _ _ (fun _ => by simp)
  | faulty => rfl

theorem compiled_faulty_qualifier_slot (channel : Fin parameters.channels) :
    sourceRoleMap parameters (.internal (.qualifier .faulty channel)) =
      (decoderStart .faulty).slots (.internal (.qualifier .faulty channel)) := by
  unfold sourceRoleMap compile
  rw [newObservations_preserves _ _ (by simp) (fun _ => by simp)]
  exact attachDecoder_qualifier .faulty .faulty channel _

def compiledQualifierOutputs (rename : Nat → Fin v) : Clause (Fin v) :=
  (List.finRange parameters.channels).map fun channel =>
    mapLiteral rename (sourceRoleMap parameters (.internal (.qualifier .faulty channel)))

theorem compiledQualifierOutputs_native (rename : Nat → Fin v) :
    compiledQualifierOutputs (parameters := parameters) rename =
      nativeQualifierOutputs (parameters := parameters) rename := by
  unfold compiledQualifierOutputs nativeQualifierOutputs
  apply List.map_congr_left
  intro channel member
  exact congrArg (mapLiteral rename) (compiled_faulty_qualifier_slot channel)

def actualEqualTraces (rename : Nat → Fin v) : List (List (Step v)) :=
  [ (equalDecoderProgram (parameters := parameters) rename false).table.prefixState.steps,
    (equalDecoderProgram (parameters := parameters) rename true).table.prefixState.steps ]

def actualSelectorTraces (rename : Nat → Fin v) (drive : parameters.drive = true) :
    List (List (Step v)) :=
  actualEqualTraces (parameters := parameters) rename ++ [(nativeMixedActivation rename drive).steps]

def actualSelectorResolutionBudget (parameters : Parameters) : Nat :=
  2 * equalDecoderProgramBudget parameters +
    parameters.buses * (2 * parameters.channels +
      parameters.channels * (SourceMixedSchedule.qualifierBudget parameters + 1)) +
    5 * parameters.buses + 3

theorem actualSelectorTraces_count (rename : Nat → Fin v) (drive : parameters.drive = true) :
    ((actualSelectorTraces rename drive).map List.length).sum ≤
      actualSelectorResolutionBudget parameters := by
  have zero := equalDecoderProgram_count (parameters := parameters) rename false
  have one := equalDecoderProgram_count (parameters := parameters) rename true
  have mixed := (nativeMixedActivation (parameters := parameters) rename drive).count
  simp only [actualSelectorTraces, actualEqualTraces, List.cons_append, List.nil_append,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    actualSelectorResolutionBudget]
  omega

theorem decoderNodeBudget_incidence (node : Fin parameters.decoder.nodeCount) :
    decoderNodeBudget node ≤ 24 *
      (1 + (parameters.decoder.node node).children.length +
        (parameters.decoder.node node).guardLabels.length) := by
  cases shape : parameters.decoder.node node <;>
    simp only [decoderNodeBudget, shape, Decoder.Gate.children,
      Decoder.Gate.guardLabels, List.length_cons, List.length_nil]
  all_goals omega

theorem decoderBudget_list_incidence (nodes : List (Fin parameters.decoder.nodeCount)) :
    (nodes.map (decoderNodeBudget (parameters := parameters))).sum ≤
      24 * (nodes.length +
        (nodes.map fun node => (parameters.decoder.node node).children.length).sum +
        (nodes.map fun node => (parameters.decoder.node node).guardLabels.length).sum) := by
  induction nodes with
  | nil => simp
  | cons node rest ih =>
    have current := decoderNodeBudget_incidence (parameters := parameters) node
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    omega

theorem decoderPrefixBudget_incidence :
    decoderPrefixBudget (parameters := parameters) parameters.decoder.nodeCount ≤
      24 * (parameters.decoder.nodeCount + parameters.decoder.childIncidences +
        parameters.decoder.guardIncidences) := by
  unfold decoderPrefixBudget
  rw [List.take_of_length_le (by simp)]
  have actual := decoderBudget_list_incidence (parameters := parameters)
    (List.finRange parameters.decoder.nodeCount)
  simpa only [List.length_finRange,
    Decoder.DAG.childIncidences, Decoder.DAG.guardIncidences, List.ofFn_eq_map] using actual

def compiledEqualDecoderRoot (rename : Nat → Fin v) (flag : Bool)
    (index : Fin parameters.decoder.roots.length) :
    DirectionPair (equalDecoderProgram (parameters := parameters) rename flag).table.prefixState.state
      (equalFlagContext (parameters := parameters) rename flag)
      (mapLiteral rename (sourceRoleMap parameters (.internal (.decoder .healthy parameters.decoder.roots[index.val]))))
      (mapLiteral rename (sourceRoleMap parameters (.internal (.decoder .faulty parameters.decoder.roots[index.val])))) :=
  decoderDirectionRetarget (equalDecoderRoot rename flag index)
    (congrArg (mapLiteral rename) (compiled_decoder_slot .healthy parameters.decoder.roots[index.val]))
    (congrArg (mapLiteral rename) (compiled_decoder_slot .faulty parameters.decoder.roots[index.val]))

theorem compiledEqualDecoderRoot_supported (rename : Nat → Fin v) (flag : Bool)
    (index : Fin parameters.decoder.roots.length) :
    DirectionPairOrigin rename (equalDecoderProgram (parameters := parameters) rename flag).table.prefixState
      (compiledEqualDecoderRoot rename flag index) :=
  decoderDirectionRetarget_supported rename _
    (equalDecoderRoot rename flag index)
    (congrArg (mapLiteral rename) (compiled_decoder_slot .healthy parameters.decoder.roots[index.val]))
    (congrArg (mapLiteral rename) (compiled_decoder_slot .faulty parameters.decoder.roots[index.val]))
    (equalDecoderRoot_supported rename flag index)


def compiledMixedActivation (rename : Nat → Fin v) (drive : parameters.drive = true) :
    SubclauseProjection (initialState (relabel rename (formula parameters)))
      (SourceMismatchAdvance.mixedContext (parameters := parameters) rename ++
        compiledQualifierOutputs (parameters := parameters) rename)
      (parameters.buses * (2 * parameters.channels + parameters.channels *
        (SourceMixedSchedule.qualifierBudget parameters + 1)) + 5 * parameters.buses + 3) :=
  let actual := nativeMixedActivation rename drive
  { state := actual.state
    steps := actual.steps
    checked := actual.checked
    result := retarget actual.result (by
      intro literal member
      simpa only [compiledQualifierOutputs_native rename] using member)
    count := actual.count }

theorem compiledMixedActivation_supported (rename : Nat → Fin v)
    (drive : parameters.drive = true) :
    SourceDecoderSchedule.ProjectionOriginalSupport rename
      (SourcePrefix.initial (parameters := parameters) rename)
      (compiledMixedActivation rename drive) := by
  exact nativeMixedActivation_supported rename drive

def nativeSelectorSizeBudget (n b : Nat) : Nat :=
  2 * (2 * n + b * (12 * n * (2 + b) + 38 * n) + 4 * b +
    (24 * b + 12 * (b + 1)) * n + 24 * n) +
  b * (2 * n + n * (2 * b + (1 + b) * (4 * b + 11) + 1)) + 5 * b + 3

theorem actualSelectorResolutionBudget_countedSize (parameters : Parameters) :
    actualSelectorResolutionBudget parameters ≤
      nativeSelectorSizeBudget parameters.decoder.countedSize parameters.buses := by
  let n := parameters.decoder.countedSize
  have channels : parameters.channels ≤ n := by
    dsimp only [n]
    rw [Decoder.DAG.countedSize_eq]
    omega
  have incidences : parameters.decoder.nodeCount + parameters.decoder.childIncidences +
      parameters.decoder.guardIncidences ≤ n := by
    dsimp only [n]
    rw [Decoder.DAG.countedSize_eq]
    omega
  have decoder : decoderPrefixBudget (parameters := parameters) parameters.decoder.nodeCount ≤ 24 * n :=
    decoderPrefixBudget_incidence.trans (Nat.mul_le_mul_left 24 incidences)
  have qualifier : SourceQualifierSchedule.qualifierProgramBudget parameters ≤
      2 * n + parameters.buses * (12 * n * (2 + parameters.buses) + 38 * n) +
      4 * parameters.buses + (24 * parameters.buses + 12 * (parameters.buses + 1)) * n := by
    unfold SourceQualifierSchedule.qualifierProgramBudget SourceQualifierSchedule.channelQualifierBudget
    gcongr <;> exact channels
  have equal := Nat.mul_le_mul_left 2 (Nat.add_le_add qualifier decoder)
  have mixed := Nat.mul_le_mul_left parameters.buses
    (Nat.add_le_add (Nat.mul_le_mul_left 2 channels)
      (Nat.mul_le_mul_right (SourceMixedSchedule.qualifierBudget parameters + 1) channels))
  unfold actualSelectorResolutionBudget equalDecoderProgramBudget nativeSelectorSizeBudget
  simp only [SourceMixedSchedule.qualifierBudget] at mixed ⊢
  change _ ≤ 2 * (2 * n + parameters.buses * (12 * n * (2 + parameters.buses) + 38 * n) +
    4 * parameters.buses + (24 * parameters.buses + 12 * (parameters.buses + 1)) * n + 24 * n) +
    parameters.buses * (2 * n + n * (2 * parameters.buses +
      (1 + parameters.buses) * (4 * parameters.buses + 11) + 1)) + 5 * parameters.buses + 3
  omega

theorem actualSelectorTraces_countedSize (rename : Nat → Fin v)
    (drive : parameters.drive = true) :
    ((actualSelectorTraces (parameters := parameters) rename drive).map List.length).sum ≤
      nativeSelectorSizeBudget parameters.decoder.countedSize parameters.buses :=
  (actualSelectorTraces_count rename drive).trans
    (actualSelectorResolutionBudget_countedSize parameters)


/-- Replay data is selected by the actual checker result, with proof-only row correspondence. -/
structure NativeReplay (rename : Nat → Fin v)
    (before : SourcePrefix (parameters := parameters) rename)
    (source : State v) (steps : List (Step v)) where
  next : State v
  checked : runSteps before.state (steps.map (Controller.Resolution.Rebase.rebaseStep
    (formula parameters).clauses.size (before.state.lastId - (formula parameters).clauses.size))) = some next
  rowMatch : Controller.Resolution.Rebase.Matches (formula parameters).clauses.size
    (before.state.lastId - (formula parameters).clauses.size) source next

def replayNativeProgram (rename : Nat → Fin v)
    (before : SourcePrefix (parameters := parameters) rename)
    (source : State v) (steps : List (Step v))
    (checked : runSteps (initialState (relabel rename (formula parameters))) steps = some source) :
    NativeReplay (parameters := parameters) rename before source steps := by
  let replay := runSteps before.state (steps.map (Controller.Resolution.Rebase.rebaseStep
    (formula parameters).clauses.size (before.state.lastId - (formula parameters).clauses.size)))
  have size : (relabel rename (formula parameters)).clauses.size =
      (formula parameters).clauses.size := by
    simp only [relabel, Controller.CNF.OrderedFormula.relabel, Array.size_map]
  have nonempty : replay.isSome := by
    obtain ⟨next, run, matched⟩ := Controller.Resolution.Rebase.replay_initial_into_prefix before.checked checked
    rw [size] at run
    change replay = some next at run
    rw [run]
    rfl
  let next := replay.get nonempty
  have run : replay = some next := (Option.some_get nonempty).symm
  have matched : Controller.Resolution.Rebase.Matches (formula parameters).clauses.size
      (before.state.lastId - (formula parameters).clauses.size) source next := by
    obtain ⟨chosen, chosenRun, chosenMatch⟩ :=
      Controller.Resolution.Rebase.replay_initial_into_prefix before.checked checked
    rw [size] at chosenRun chosenMatch
    have same : next = chosen := Option.some.inj (run.symm.trans chosenRun)
    exact same.symm ▸ chosenMatch
  exact ⟨next, run, matched⟩

variable {rename : Nat → Fin v}
  {before : SourcePrefix (parameters := parameters) rename}
  {source : State v} {steps : List (Step v)}

def NativeReplay.added (replay : NativeReplay (parameters := parameters) rename before source steps) : List (Step v) :=
  steps.map (Controller.Resolution.Rebase.rebaseStep (formula parameters).clauses.size
    (before.state.lastId - (formula parameters).clauses.size))

def NativeReplay.prefix (replay : NativeReplay (parameters := parameters) rename before source steps) : SourcePrefix (parameters := parameters) rename :=
  before.extend replay.next replay.added replay.checked

theorem NativeReplay.added_length (replay : NativeReplay (parameters := parameters) rename before source steps) :
    replay.added.length = steps.length := by
  exact List.length_map _

def NativeReplay.available (replay : NativeReplay (parameters := parameters) rename before source steps)
    (row : Rows.Available source clause) : Rows.Available replay.next clause where
  id := Controller.Resolution.Rebase.rebaseId (formula parameters).clauses.size
    (before.state.lastId - (formula parameters).clauses.size) row.id
  present := (replay.rowMatch.row_available row.present row.bound).1
  bound := (replay.rowMatch.row_available row.present row.bound).2

def NativeReplay.transfer (replay : NativeReplay (parameters := parameters) rename before source steps)
    (transfer : GuardedTransfer source context input output) :
    GuardedTransfer replay.next context input output :=
  match transfer with
  | .identity equal => .identity equal
  | .derived row => .derived ⟨row.clause, replay.available row.row, row.subset⟩

def NativeReplay.pair (replay : NativeReplay (parameters := parameters) rename before source steps)
    (pair : DirectionPair source context left right) : DirectionPair replay.next context left right :=
  ⟨replay.transfer pair.forward, replay.transfer pair.backward⟩

/-- Both equal cofactors and the mixed activation are replayed in one strictly growing ID space. -/
structure NativeCofactorReplay (rename : Nat → Fin v) (drive : parameters.drive = true) where
  equalFalse : NativeReplay (parameters := parameters) rename (SourcePrefix.initial (parameters := parameters) rename)
    (equalDecoderProgram (parameters := parameters) rename false).table.prefixState.state
    (equalDecoderProgram (parameters := parameters) rename false).table.prefixState.steps
  equalTrue : NativeReplay (parameters := parameters) rename equalFalse.prefix
    (equalDecoderProgram (parameters := parameters) rename true).table.prefixState.state
    (equalDecoderProgram (parameters := parameters) rename true).table.prefixState.steps
  mixed : NativeReplay (parameters := parameters) rename equalTrue.prefix
    (compiledMixedActivation rename drive).state (compiledMixedActivation rename drive).steps

def nativeCofactorReplay (rename : Nat → Fin v) (drive : parameters.drive = true) :
    NativeCofactorReplay (parameters := parameters) rename drive := by
  let first := replayNativeProgram rename (SourcePrefix.initial (parameters := parameters) rename)
    (equalDecoderProgram (parameters := parameters) rename false).table.prefixState.state
    (equalDecoderProgram (parameters := parameters) rename false).table.prefixState.steps
    (equalDecoderProgram (parameters := parameters) rename false).table.prefixState.checked
  let second := replayNativeProgram rename first.prefix
    (equalDecoderProgram (parameters := parameters) rename true).table.prefixState.state
    (equalDecoderProgram (parameters := parameters) rename true).table.prefixState.steps
    (equalDecoderProgram (parameters := parameters) rename true).table.prefixState.checked
  let third := replayNativeProgram rename second.prefix
    (compiledMixedActivation rename drive).state (compiledMixedActivation rename drive).steps
    (compiledMixedActivation rename drive).checked
  exact ⟨first, second, third⟩

def nativeCofactorPrefix (rename : Nat → Fin v) (drive : parameters.drive = true) : SourcePrefix (parameters := parameters) rename :=
  (nativeCofactorReplay rename drive).mixed.prefix

theorem nativeCofactorPrefix_count (rename : Nat → Fin v) (drive : parameters.drive = true) :
    (nativeCofactorPrefix rename drive).steps.length ≤ actualSelectorResolutionBudget parameters := by
  let program := nativeCofactorReplay rename drive
  have one := equalDecoderProgram_count (parameters := parameters) rename false
  have two := equalDecoderProgram_count (parameters := parameters) rename true
  have three := (compiledMixedActivation rename drive).count
  have firstLength : program.equalFalse.added.length =
      (equalDecoderProgram (parameters := parameters) rename false).table.prefixState.steps.length :=
    program.equalFalse.added_length
  have secondLength : program.equalTrue.added.length =
      (equalDecoderProgram (parameters := parameters) rename true).table.prefixState.steps.length :=
    program.equalTrue.added_length
  have mixedLength : program.mixed.added.length =
      (compiledMixedActivation rename drive).steps.length := program.mixed.added_length
  have firstPrefix : program.equalFalse.prefix.steps.length = program.equalFalse.added.length := by
    change ([] ++ program.equalFalse.added).length = program.equalFalse.added.length
    exact congrArg List.length (List.nil_append _)
  have secondPrefix : program.equalTrue.prefix.steps.length =
      program.equalFalse.prefix.steps.length + program.equalTrue.added.length :=
    List.length_append
  have mixedPrefix : program.mixed.prefix.steps.length =
      program.equalTrue.prefix.steps.length + program.mixed.added.length :=
    List.length_append
  change program.mixed.prefix.steps.length ≤ _
  unfold actualSelectorResolutionBudget
  omega


variable {drive : parameters.drive = true}

theorem NativeCofactorReplay.tail_checked (program : NativeCofactorReplay (parameters := parameters) rename drive) :
    runSteps program.equalFalse.next (program.equalTrue.added ++ program.mixed.added) = some program.mixed.next := by
  have second : runSteps program.equalFalse.next program.equalTrue.added =
      some program.equalTrue.next := program.equalTrue.checked
  have third : runSteps program.equalTrue.next program.mixed.added =
      some program.mixed.next := program.mixed.checked
  rw [runSteps_append, second]
  exact third

def NativeCofactorReplay.root (program : NativeCofactorReplay (parameters := parameters) rename drive)
    (flag : Bool) (index : Fin parameters.decoder.roots.length) :
    DirectionPair program.mixed.next
      (equalFlagContext (parameters := parameters) rename flag)
      (mapLiteral rename (sourceRoleMap parameters (.internal (.decoder .healthy parameters.decoder.roots[index.val]))))
      (mapLiteral rename (sourceRoleMap parameters (.internal (.decoder .faulty parameters.decoder.roots[index.val])))) :=
  match flag with
  | false => ((program.equalFalse.pair (compiledEqualDecoderRoot rename false index)).afterTrace
      program.equalTrue.next program.equalTrue.added program.equalTrue.checked).afterTrace
      program.mixed.next program.mixed.added program.mixed.checked
  | true => (program.equalTrue.pair (compiledEqualDecoderRoot rename true index)).afterTrace
      program.mixed.next program.mixed.added program.mixed.checked

def NativeCofactorReplay.mixedRow (program : NativeCofactorReplay (parameters := parameters) rename drive) :
    AvailableSubclause program.mixed.next
      (SourceMismatchAdvance.mixedContext (parameters := parameters) rename ++
        compiledQualifierOutputs (parameters := parameters) rename) :=
  let actual := compiledMixedActivation rename drive
  { clause := actual.result.clause
    row := program.mixed.available actual.result.row
    subset := actual.result.subset }

/-- Rebasing preserves original-owner exclusions and shifts actual chronological witnesses. -/
theorem rebase_parent_support (n offset : Nat) (allowed : Nat → Prop) (steps : List (Step v))
    (supported : TraceOriginalSupport n allowed steps) (step : Step v) (member : step ∈ steps)
    (parent : Nat) (parentMember : parent ∈ [step.left, step.right]) :
    (Controller.Resolution.Rebase.rebaseId n offset parent ≤ n →
      allowed (Controller.Resolution.Rebase.rebaseId n offset parent)) ∧
    (n < Controller.Resolution.Rebase.rebaseId n offset parent →
      ∃ earlier ∈ steps.map (Controller.Resolution.Rebase.rebaseStep n offset),
        earlier.id = Controller.Resolution.Rebase.rebaseId n offset parent ∧
        earlier.id < (Controller.Resolution.Rebase.rebaseStep n offset step).id) := by
  have old := supported step member parent parentMember
  constructor
  · intro bounded
    by_cases original : parent ≤ n
    · simpa only [Controller.Resolution.Rebase.rebaseId_original original] using old.1 original
    · have derived : n < parent := by omega
      rw [Controller.Resolution.Rebase.rebaseId_derived derived] at bounded
      omega
  · intro high
    have derived : n < parent := by
      by_contra absent
      have original : parent ≤ n := by omega
      rw [Controller.Resolution.Rebase.rebaseId_original original] at high
      omega
    obtain ⟨earlier, earlierMember, same, before⟩ := old.2 derived
    refine ⟨Controller.Resolution.Rebase.rebaseStep n offset earlier,
      List.mem_map.mpr ⟨earlier, earlierMember, rfl⟩, ?_, ?_⟩
    · exact congrArg (Controller.Resolution.Rebase.rebaseId n offset) same
    · exact Controller.Resolution.Rebase.rebaseId_strictMono n offset before

theorem rebase_trace_supported (n offset : Nat) (allowed : Nat → Prop) (steps : List (Step v))
    (supported : TraceOriginalSupport n allowed steps) :
    TraceOriginalSupport n allowed (steps.map (Controller.Resolution.Rebase.rebaseStep n offset)) := by
  intro emitted member parent parentMember
  obtain ⟨step, stepMember, rfl⟩ := List.mem_map.mp member
  have shape : parent = Controller.Resolution.Rebase.rebaseId n offset step.left ∨
      parent = Controller.Resolution.Rebase.rebaseId n offset step.right := by
    simpa only [Controller.Resolution.Rebase.rebaseStep, List.mem_cons, List.not_mem_nil, or_false] using parentMember
  rcases shape with left | right
  · subst parent
    exact rebase_parent_support n offset allowed steps supported step stepMember step.left (by simp)
  · subst parent
    exact rebase_parent_support n offset allowed steps supported step stepMember step.right (by simp)

theorem independent_trace_append_supported (n : Nat) (allowed : Nat → Prop)
    (first second : List (Step v)) (one : TraceOriginalSupport n allowed first)
    (two : TraceOriginalSupport n allowed second) : TraceOriginalSupport n allowed (first ++ second) := by
  intro step member parent parentMember
  rcases List.mem_append.mp member with left | right
  · have original := one step left parent parentMember
    refine ⟨original.1, ?_⟩
    intro high
    obtain ⟨earlier, mem, same, before⟩ := original.2 high
    exact ⟨earlier, List.mem_append.mpr (Or.inl mem), same, before⟩
  · have original := two step right parent parentMember
    refine ⟨original.1, ?_⟩
    intro high
    obtain ⟨earlier, mem, same, before⟩ := original.2 high
    exact ⟨earlier, List.mem_append.mpr (Or.inr mem), same, before⟩

theorem NativeReplay.prefix_supported (rename : Nat → Fin v)
    (before source : SourcePrefix (parameters := parameters) rename)
    (replay : NativeReplay (parameters := parameters) rename before source.state source.steps)
    (beforeSupport : SourceDecoderSchedule.PrefixOriginalSupport rename before)
    (sourceSupport : SourceDecoderSchedule.PrefixOriginalSupport rename source) :
    SourceDecoderSchedule.PrefixOriginalSupport rename replay.prefix :=
  independent_trace_append_supported _ _ _ _ beforeSupport
    (rebase_trace_supported _ _ _ _ sourceSupport)

theorem nativeCofactorPrefix_supported (rename : Nat → Fin v) (drive : parameters.drive = true) :
    SourceDecoderSchedule.PrefixOriginalSupport rename (nativeCofactorPrefix rename drive) := by
  let program := nativeCofactorReplay rename drive
  have empty : SourceDecoderSchedule.PrefixOriginalSupport rename
      (SourcePrefix.initial (parameters := parameters) rename) := by
    intro step member
    exact False.elim (by simpa only [SourcePrefix.initial, List.not_mem_nil] using member)
  have first := NativeReplay.prefix_supported rename (SourcePrefix.initial (parameters := parameters) rename)
    (equalDecoderProgram (parameters := parameters) rename false).table.prefixState program.equalFalse empty
    (equalDecoderProgram_supported (parameters := parameters) rename false).1.1
  have second := NativeReplay.prefix_supported rename program.equalFalse.prefix
    (equalDecoderProgram (parameters := parameters) rename true).table.prefixState program.equalTrue first
    (equalDecoderProgram_supported (parameters := parameters) rename true).1.1
  have mixed := compiledMixedActivation_supported rename drive
  exact independent_trace_append_supported _ _ _ _ second
    (rebase_trace_supported _ _ _ _ mixed.1)


theorem rebase_native_result_origin (rename : Nat → Fin v) (offset : Nat)
    (steps : List (Step v)) (id : Nat)
    (origin : Controller.NativeProof.SourceMismatchHandles.ResultOrigin (formula parameters).clauses.size
      (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) steps id) :
    Controller.NativeProof.SourceMismatchHandles.ResultOrigin (formula parameters).clauses.size
      (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
      (steps.map (Controller.Resolution.Rebase.rebaseStep (formula parameters).clauses.size offset))
      (Controller.Resolution.Rebase.rebaseId (formula parameters).clauses.size offset id) := by
  rcases origin with original | ⟨earlier, member, same, high⟩
  · have bounded := SourceDecoderSchedule.allowed_native_count_le rename id original
    rw [Controller.Resolution.Rebase.rebaseId_original bounded]
    exact Or.inl original
  · refine Or.inr ⟨Controller.Resolution.Rebase.rebaseStep _ offset earlier,
      List.mem_map.mpr ⟨earlier, member, rfl⟩, ?_, ?_⟩
    · exact congrArg (Controller.Resolution.Rebase.rebaseId _ offset) same
    · rw [Controller.Resolution.Rebase.rebaseId_derived high]
      omega

theorem NativeReplay.transfer_supported (rename : Nat → Fin v)
    (before source : SourcePrefix (parameters := parameters) rename)
    (replay : NativeReplay (parameters := parameters) rename before source.state source.steps)
    (transfer : GuardedTransfer source.state context input output)
    (original : SourceDecoderSchedule.GuardedTransferOrigin rename source transfer) :
    SourceDecoderSchedule.GuardedTransferOrigin rename replay.prefix (replay.transfer transfer) := by
  cases transfer with
  | identity equal => trivial
  | derived row =>
    have mapped := rebase_native_result_origin rename
      (before.state.lastId - (formula parameters).clauses.size) source.steps row.row.id original
    exact resultOrigin_append_left _ _ before.steps replay.added _ mapped

theorem NativeReplay.pair_supported (rename : Nat → Fin v)
    (before source : SourcePrefix (parameters := parameters) rename)
    (replay : NativeReplay (parameters := parameters) rename before source.state source.steps)
    (pair : DirectionPair source.state context left right)
    (original : DirectionPairOrigin rename source pair) :
    DirectionPairOrigin rename replay.prefix (replay.pair pair) :=
  ⟨replay.transfer_supported rename before source pair.forward original.1,
   replay.transfer_supported rename before source pair.backward original.2⟩

theorem NativeCofactorReplay.root_supported (program : NativeCofactorReplay (parameters := parameters) rename drive)
    (flag : Bool) (index : Fin parameters.decoder.roots.length) :
    DirectionPairOrigin rename program.mixed.prefix (program.root flag index) := by
  cases flag with
  | false =>
    have first := NativeReplay.pair_supported rename (SourcePrefix.initial (parameters := parameters) rename)
      (equalDecoderProgram (parameters := parameters) rename false).table.prefixState program.equalFalse
      (compiledEqualDecoderRoot rename false index) (compiledEqualDecoderRoot_supported rename false index)
    have second := DirectionPairOrigin.afterTrace rename program.equalFalse.prefix
      (program.equalFalse.pair (compiledEqualDecoderRoot rename false index)) first
      program.equalTrue.next program.equalTrue.added program.equalTrue.checked
    exact DirectionPairOrigin.afterTrace rename program.equalTrue.prefix _ second
      program.mixed.next program.mixed.added program.mixed.checked
  | true =>
    have second := NativeReplay.pair_supported rename program.equalFalse.prefix
      (equalDecoderProgram (parameters := parameters) rename true).table.prefixState program.equalTrue
      (compiledEqualDecoderRoot rename true index) (compiledEqualDecoderRoot_supported rename true index)
    exact DirectionPairOrigin.afterTrace rename program.equalTrue.prefix _ second
      program.mixed.next program.mixed.added program.mixed.checked

theorem NativeCofactorReplay.mixedRow_supported (program : NativeCofactorReplay (parameters := parameters) rename drive) :
    Controller.NativeProof.SourceMismatchHandles.ResultOrigin (formula parameters).clauses.size
      (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
      program.mixed.prefix.steps program.mixedRow.row.id := by
  have original := (compiledMixedActivation_supported rename drive).2
  have mapped := rebase_native_result_origin rename
    (program.equalTrue.prefix.state.lastId - (formula parameters).clauses.size)
    (compiledMixedActivation rename drive).steps (compiledMixedActivation rename drive).result.row.id original
  exact resultOrigin_append_left _ _ program.equalTrue.prefix.steps program.mixed.added _ mapped

def nativeCofactorRoot (rename : Nat → Fin v) (drive : parameters.drive = true)
    (flag : Bool) (index : Fin parameters.decoder.roots.length) :=
  (nativeCofactorReplay rename drive).root flag index

def nativeCofactorMixed (rename : Nat → Fin v) (drive : parameters.drive = true) :=
  (nativeCofactorReplay rename drive).mixedRow

theorem nativeCofactorRoot_supported (rename : Nat → Fin v) (drive : parameters.drive = true)
    (flag : Bool) (index : Fin parameters.decoder.roots.length) :
    DirectionPairOrigin rename (nativeCofactorPrefix rename drive)
      (nativeCofactorRoot rename drive flag index) :=
  (nativeCofactorReplay rename drive).root_supported flag index

theorem nativeCofactorMixed_supported (rename : Nat → Fin v) (drive : parameters.drive = true) :
    Controller.NativeProof.SourceMismatchHandles.ResultOrigin (formula parameters).clauses.size
      (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
      (nativeCofactorPrefix rename drive).steps (nativeCofactorMixed rename drive).row.id :=
  (nativeCofactorReplay rename drive).mixedRow_supported

theorem nativeCofactorPrefix_countedSize (rename : Nat → Fin v) (drive : parameters.drive = true) :
    (nativeCofactorPrefix rename drive).steps.length ≤
      nativeSelectorSizeBudget parameters.decoder.countedSize parameters.buses :=
  (nativeCofactorPrefix_count rename drive).trans (actualSelectorResolutionBudget_countedSize parameters)


def rebaseRowReason (n offset : Nat) (reason : Controller.Resolution.RUP.RowReason v) :
    Controller.Resolution.RUP.RowReason v :=
  { reason with rowId := Controller.Resolution.Rebase.rebaseId n offset reason.rowId }

def rebaseLeafCertificate (n offset : Nat)
    (certificate : Controller.Resolution.Cases.LeafCertificate v) :
    Controller.Resolution.Cases.LeafCertificate v :=
  ⟨Controller.Resolution.Rebase.rebaseId n offset certificate.rowId,
    certificate.clause, certificate.reasons.map (rebaseRowReason n offset)⟩

def rebaseCaseTree (n offset : Nat) :
    Controller.Resolution.Cases.CaseTree v → Controller.Resolution.Cases.CaseTree v
  | .leaf certificate => .leaf (rebaseLeafCertificate n offset certificate)
  | .fork pivot left right => .fork pivot (rebaseCaseTree n offset left)
      (rebaseCaseTree n offset right)

theorem rebase_reasons_entries (n offset : Nat)
    (reasons : List (Controller.Resolution.RUP.RowReason v)) :
    ((reasons.map (rebaseRowReason n offset)).map Controller.Resolution.RUP.RowReason.entry) =
      reasons.map Controller.Resolution.RUP.RowReason.entry := by
  simp only [List.map_map]
  rfl

theorem rebase_knownReasons {source target : State v}
    (n offset : Nat) (correspondence : Controller.Resolution.Rebase.Matches n offset source target)
    (reasons : List (Controller.Resolution.RUP.RowReason v))
    (known : Controller.Resolution.RUP.KnownReasons source reasons) :
    Controller.Resolution.RUP.KnownReasons target
      (reasons.map (rebaseRowReason n offset)) := by
  intro mapped member
  obtain ⟨reason, sourceMember, rfl⟩ := List.mem_map.mp member
  have old := known reason sourceMember
  have row := correspondence.row_available old.1 old.2.1
  exact ⟨row.1, row.2, old.2.2⟩

theorem rebase_validTree {source target : State v}
    (n offset : Nat) (correspondence : Controller.Resolution.Rebase.Matches n offset source target)
    (tree : Controller.Resolution.Cases.CaseTree v) (clause : Clause (Fin v))
    (valid : Controller.Resolution.Cases.ValidTree source clause tree) :
    Controller.Resolution.Cases.ValidTree target clause (rebaseCaseTree n offset tree) := by
  induction tree generalizing clause with
  | leaf certificate =>
    obtain ⟨present, bound, known, reasons, subset⟩ := valid
    have row := correspondence.row_available present bound
    refine ⟨row.1, row.2, rebase_knownReasons n offset correspondence _ known, ?_, ?_⟩
    · simpa only [rebaseCaseTree, rebaseLeafCertificate, rebase_reasons_entries] using reasons
    · simpa only [rebaseCaseTree, rebaseLeafCertificate, rebase_reasons_entries] using subset
  | fork pivot left right leftIH rightIH =>
    exact ⟨leftIH _ valid.1, rightIH _ valid.2⟩

theorem rebaseCaseTree_inferenceBudget (n offset : Nat)
    (tree : Controller.Resolution.Cases.CaseTree v) :
    Controller.Resolution.Cases.inferenceBudget (rebaseCaseTree n offset tree) =
      Controller.Resolution.Cases.inferenceBudget tree := by
  induction tree with
  | leaf certificate =>
    simp only [rebaseCaseTree, rebaseLeafCertificate,
      Controller.Resolution.Cases.inferenceBudget, List.length_map]
  | fork pivot left right leftIH rightIH =>
    simp only [rebaseCaseTree, Controller.Resolution.Cases.inferenceBudget, leftIH, rightIH]

theorem rebaseCaseTree_splitVariables (n offset : Nat)
    (tree : Controller.Resolution.Cases.CaseTree v) :
    splitVariables (rebaseCaseTree n offset tree) = splitVariables tree := by
  induction tree with
  | leaf certificate => rfl
  | fork pivot left right leftIH rightIH =>
    simp only [rebaseCaseTree, splitVariables, leftIH, rightIH]

theorem NativeReplay.caseTree_valid
    {rename : Nat → Fin v} {before : SourcePrefix (parameters := parameters) rename}
    {source : State v} {steps : List (Step v)}
    (replay : NativeReplay (parameters := parameters) rename before source steps)
    (tree : Controller.Resolution.Cases.CaseTree v) (target : Clause (Fin v))
    (valid : Controller.Resolution.Cases.ValidTree source target tree) :
    Controller.Resolution.Cases.ValidTree replay.next target
      (rebaseCaseTree (formula parameters).clauses.size
        (before.state.lastId - (formula parameters).clauses.size) tree) :=
  rebase_validTree _ _ replay.rowMatch tree target valid

theorem NativeReplay.caseTree_run
    {rename : Nat → Fin v} {before : SourcePrefix (parameters := parameters) rename}
    {source : State v} {steps : List (Step v)}
    (replay : NativeReplay (parameters := parameters) rename before source steps)
    (tree : Controller.Resolution.Cases.CaseTree v) (target : Clause (Fin v))
    (valid : Controller.Resolution.Cases.ValidTree source target tree) :
    let mapped := rebaseCaseTree (formula parameters).clauses.size
      (before.state.lastId - (formula parameters).clauses.size) tree
    let emitted := Controller.Resolution.Cases.compileTree replay.next mapped
    runSteps replay.next emitted.steps = some emitted.state ∧
      emitted.state.rows emitted.rowId = some emitted.clause ∧
      emitted.rowId ≤ emitted.state.lastId ∧ ClauseSubset emitted.clause target :=
  Controller.Resolution.Cases.compileTree_run _ replay.next replay.next
    (Nat.le_refl _) (fun _ _ => rfl) target (replay.caseTree_valid tree target valid)

theorem rebaseCaseTree_local_bound (n offset : Nat)
    (tree : Controller.Resolution.Cases.CaseTree v) (limit : Nat)
    (bound : (splitVariables tree).card ≤ limit) :
    (splitVariables (rebaseCaseTree n offset tree)).card ≤ limit := by
  rw [rebaseCaseTree_splitVariables]
  exact bound

theorem NativeReplay.caseTree_count
    {rename : Nat → Fin v} {before : SourcePrefix (parameters := parameters) rename}
    {source : State v} {steps : List (Step v)}
    (replay : NativeReplay (parameters := parameters) rename before source steps)
    (tree : Controller.Resolution.Cases.CaseTree v) :
    (Controller.Resolution.Cases.compileTree replay.next
      (rebaseCaseTree (formula parameters).clauses.size
        (before.state.lastId - (formula parameters).clauses.size) tree)).steps.length ≤
      Controller.Resolution.Cases.inferenceBudget tree := by
  have bound := Controller.Resolution.Cases.compileTree_count_le
    (rebaseCaseTree (formula parameters).clauses.size
      (before.state.lastId - (formula parameters).clauses.size) tree) replay.next
  simpa only [rebaseCaseTree_inferenceBudget] using bound

theorem NativeReplay.xorCaseTree_valid
    (replay : NativeReplay (parameters := parameters) rename before source steps)
    (target : Clause (Fin v)) (a b : Literal (Fin v))
    (tt : AvailableSubclause source (SourceStageXor.branchTarget target a b true true))
    (tf : AvailableSubclause source (SourceStageXor.branchTarget target a b true false))
    (ft : AvailableSubclause source (SourceStageXor.branchTarget target a b false true))
    (ff : AvailableSubclause source (SourceStageXor.branchTarget target a b false false)) :
    Controller.Resolution.Cases.ValidTree replay.next target
      (rebaseCaseTree (formula parameters).clauses.size
        (before.state.lastId - (formula parameters).clauses.size)
        (SourceStageXor.xorCaseTree source target a b tt tf ft ff)) :=
  replay.caseTree_valid _ target
    (SourceStageXor.xorCaseTree_valid source target a b tt tf ft ff)

theorem NativeReplay.xorCaseTree_splitVariables
    (replay : NativeReplay (parameters := parameters) rename before source steps)
    (target : Clause (Fin v)) (a b : Literal (Fin v))
    (tt : AvailableSubclause source (SourceStageXor.branchTarget target a b true true))
    (tf : AvailableSubclause source (SourceStageXor.branchTarget target a b true false))
    (ft : AvailableSubclause source (SourceStageXor.branchTarget target a b false true))
    (ff : AvailableSubclause source (SourceStageXor.branchTarget target a b false false)) :
    splitVariables (rebaseCaseTree (formula parameters).clauses.size
      (before.state.lastId - (formula parameters).clauses.size)
      (SourceStageXor.xorCaseTree source target a b tt tf ft ff)) = {a.1, b.1} := by
  rw [rebaseCaseTree_splitVariables]
  exact Controller.NativeProof.SourceDecoderTraversal.xorCaseTree_splitVariables
    source target a b tt tf ft ff


theorem joinCofactors_actualTree
    (state : State v) (target : Clause (Fin v)) (a b : Literal (Fin v))
    (tt : AvailableSubclause state (SourceStageXor.branchTarget target a b true true))
    (tf : AvailableSubclause state (SourceStageXor.branchTarget target a b true false))
    (ft : AvailableSubclause state (SourceStageXor.branchTarget target a b false true))
    (ff : AvailableSubclause state (SourceStageXor.branchTarget target a b false false)) :
    let tree := SourceStageXor.xorCaseTree state target a b tt tf ft ff
    let actual := SourceStageXor.joinCofactors state target a b tt tf ft ff
    actual.steps = (Controller.Resolution.Cases.compileTree state tree).steps ∧
      actual.state = (Controller.Resolution.Cases.compileTree state tree).state ∧
      actual.result.row.id = (Controller.Resolution.Cases.compileTree state tree).rowId ∧
      Controller.Resolution.Cases.ValidTree state target tree ∧
      (splitVariables tree).card ≤ 2 ∧
      Controller.Resolution.Cases.inferenceBudget tree = 3 := by
  refine ⟨rfl, rfl, rfl, SourceStageXor.xorCaseTree_valid state target a b tt tf ft ff, ?_, rfl⟩
  exact xorCaseTree_splitVariables_card state target a b tt tf ft ff

theorem initialMaskFlagTree_splitVariables (rename : Nat → Fin v)
    (channel : Fin parameters.channels) (flag : Bool) :
    splitVariables (SourceSlotFrames.initialMaskFlagTree (parameters := parameters) rename channel flag) =
      {(SourceCongruence.maskAbsent (parameters := parameters) rename .healthy channel).1} := by
  simp only [SourceSlotFrames.initialMaskFlagTree, SourceCongruence.maskCofactorTree, splitVariables,
    Finset.union_empty, Finset.insert_empty]

theorem reverseMaskFlagTree_splitVariables (rename : Nat → Fin v)
    (channel : Fin parameters.channels) (flag : Bool) :
    splitVariables (SourceSlotFrames.reverseMaskFlagTree (parameters := parameters) rename channel flag) =
      {(SourceCongruence.maskAbsent (parameters := parameters) rename .healthy channel).1} := by
  simp only [SourceSlotFrames.reverseMaskFlagTree, SourceSlotFrames.reverseMaskCofactorTree, splitVariables,
    Finset.union_empty, Finset.insert_empty]

theorem initialMaskProjection_actualTrees (rename : Nat → Fin v) (flag : Bool)
    (channel : Fin parameters.channels) (start : SourcePrefix (parameters := parameters) rename) :
    let firstTree := SourceSlotFrames.initialMaskFlagTree (parameters := parameters) rename channel flag
    let first := Controller.Resolution.Cases.compileTree start.state firstTree
    let secondTree := SourceSlotFrames.reverseMaskFlagTree (parameters := parameters) rename channel flag
    let second := Controller.Resolution.Cases.compileTree first.state secondTree
    let actual := SourceBusSchedule.initialMaskProjection rename flag channel start
    actual.steps = first.steps ++ second.steps ∧ actual.state = second.state ∧
      Controller.Resolution.Cases.inferenceBudget firstTree = 1 ∧
      Controller.Resolution.Cases.inferenceBudget secondTree = 1 := by
  exact ⟨rfl, rfl, rfl, rfl⟩

def maskTreeSteps (invocation : State v × Controller.Resolution.Cases.CaseTree v) : List (Step v) :=
  (Controller.Resolution.Cases.compileTree invocation.1 invocation.2).steps

def initialMaskTreeSchedule (rename : Nat → Fin v) (flag : Bool) :
    List (Fin parameters.channels) → List (State v × Controller.Resolution.Cases.CaseTree v)
  | [] => []
  | channel :: channels =>
    let before := (SourceBusSchedule.buildInitialMaskTable rename flag channels).checkedPrefix
    let firstTree := SourceSlotFrames.initialMaskFlagTree (parameters := parameters) rename channel flag
    let first := Controller.Resolution.Cases.compileTree before.state firstTree
    let secondTree := SourceSlotFrames.reverseMaskFlagTree (parameters := parameters) rename channel flag
    initialMaskTreeSchedule rename flag channels ++ [(before.state, firstTree), (first.state, secondTree)]

theorem initialMaskTreeSchedule_length (rename : Nat → Fin v) (flag : Bool)
    (channels : List (Fin parameters.channels)) :
    (initialMaskTreeSchedule rename flag channels).length = 2 * channels.length := by
  induction channels with
  | nil => rfl
  | cons channel channels ih =>
    simp only [initialMaskTreeSchedule, List.length_append, List.length_cons, List.length_nil]
    omega

theorem initialMaskTreeSchedule_actualTrace (rename : Nat → Fin v) (flag : Bool)
    (channels : List (Fin parameters.channels)) :
    ((initialMaskTreeSchedule rename flag channels).flatMap maskTreeSteps) =
      (SourceBusSchedule.buildInitialMaskTable rename flag channels).checkedPrefix.steps := by
  induction channels with
  | nil => rfl
  | cons channel channels ih =>
    let before := (SourceBusSchedule.buildInitialMaskTable rename flag channels).checkedPrefix
    have actual := initialMaskProjection_actualTrees rename flag channel before
    change ((initialMaskTreeSchedule rename flag channels ++
      [(before.state, SourceSlotFrames.initialMaskFlagTree (parameters := parameters) rename channel flag),
       ((Controller.Resolution.Cases.compileTree before.state
          (SourceSlotFrames.initialMaskFlagTree (parameters := parameters) rename channel flag)).state,
        SourceSlotFrames.reverseMaskFlagTree (parameters := parameters) rename channel flag)]).flatMap maskTreeSteps) =
      before.steps ++ (SourceBusSchedule.initialMaskProjection rename flag channel before).steps
    rw [List.flatMap_append, ih]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, maskTreeSteps]
    exact congrArg (fun tail => before.steps ++ tail) actual.1.symm


def CaseTreeOriginals (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename) :
    Controller.Resolution.Cases.CaseTree v → Prop
  | .leaf certificate =>
    SourceMismatchHandles.ResultOrigin (formula parameters).clauses.size
      (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
      prefixState.steps certificate.rowId ∧
    ∀ reason ∈ certificate.reasons,
      SourceMismatchHandles.ResultOrigin (formula parameters).clauses.size
        (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
        prefixState.steps reason.rowId
  | .fork _ left right => CaseTreeOriginals rename prefixState left ∧
      CaseTreeOriginals rename prefixState right

theorem NativeReplay.caseTree_originals (rename : Nat → Fin v)
    (before source : SourcePrefix (parameters := parameters) rename)
    (replay : NativeReplay (parameters := parameters) rename before source.state source.steps)
    (tree : Controller.Resolution.Cases.CaseTree v)
    (original : CaseTreeOriginals rename source tree) :
    CaseTreeOriginals rename replay.prefix
      (rebaseCaseTree (formula parameters).clauses.size
        (before.state.lastId - (formula parameters).clauses.size) tree) := by
  induction tree with
  | leaf certificate =>
    constructor
    · exact resultOrigin_append_left _ _ before.steps replay.added _
        (rebase_native_result_origin rename _ source.steps certificate.rowId original.1)
    · intro mapped member
      obtain ⟨reason, sourceMember, rfl⟩ := List.mem_map.mp member
      exact resultOrigin_append_left _ _ before.steps replay.added _
        (rebase_native_result_origin rename _ source.steps reason.rowId (original.2 reason sourceMember))
  | fork pivot left right leftIH rightIH =>
    exact ⟨leftIH original.1, rightIH original.2⟩

theorem guardedXor_actualInvocation
    (state : State v) (context : Clause (Fin v))
    (a b c d leftOut rightOut : Literal (Fin v))
    (left : SourceStageXor.XorRows state a b leftOut)
    (right : SourceStageXor.XorRows state c d rightOut)
    (aForward : GuardedTransfer state context a c) (aBackward : GuardedTransfer state context c a)
    (bForward : GuardedTransfer state context b d) (bBackward : GuardedTransfer state context d b) :
    let actual := SourceStageXor.guardedXor state context a b c d leftOut rightOut
      left right aForward aBackward bForward bBackward
    ∃ base tree prefixSteps,
      actual.steps = prefixSteps ++ (Controller.Resolution.Cases.compileTree base tree).steps ∧
      actual.state = (Controller.Resolution.Cases.compileTree base tree).state ∧
      actual.result.row.id = (Controller.Resolution.Cases.compileTree base tree).rowId ∧
      Controller.Resolution.Cases.ValidTree base (context ++ [negate leftOut, rightOut]) tree ∧
      splitVariables tree = {a.1, b.1} ∧
      Controller.Resolution.Cases.inferenceBudget tree = 3 ∧
      prefixSteps.length ≤ 8 := by
  let runBranch := fun (next : State v) (steps : List (Step v))
      (checked : runSteps state steps = some next) (x y : Bool) =>
    SourceStageXor.xorCofactor next context a b c d leftOut rightOut
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
  let tree := SourceStageXor.xorCaseTree fourth.state
    (context ++ [negate leftOut, rightOut]) a b tt tf ft fourth.result
  refine ⟨fourth.state, tree, ((first.steps ++ second.steps) ++ third.steps) ++ fourth.steps,
    rfl, rfl, rfl, SourceStageXor.xorCaseTree_valid _ _ _ _ _ _ _ _, ?_, rfl, ?_⟩
  · exact Controller.NativeProof.SourceDecoderTraversal.xorCaseTree_splitVariables
      fourth.state _ a b tt tf ft fourth.result
  · have one := first.count
    have two := second.count
    have three := third.count
    have four := fourth.count
    simp only [List.length_append]
    omega

theorem NativeReplay.xorCaseTree_contextualSplit_le_five
    (replay : NativeReplay (parameters := parameters) rename before source steps)
    (target : Clause (Fin v)) (a b : Literal (Fin v)) (oldFlag newFlag : Literal (Fin v))
    (tt : AvailableSubclause source (SourceStageXor.branchTarget target a b true true))
    (tf : AvailableSubclause source (SourceStageXor.branchTarget target a b true false))
    (ft : AvailableSubclause source (SourceStageXor.branchTarget target a b false true))
    (ff : AvailableSubclause source (SourceStageXor.branchTarget target a b false false)) :
    ({oldFlag.1, newFlag.1} ∪ splitVariables
      (rebaseCaseTree (formula parameters).clauses.size
        (before.state.lastId - (formula parameters).clauses.size)
        (SourceStageXor.xorCaseTree source target a b tt tf ft ff))).card ≤ 5 := by
  rw [rebaseCaseTree_splitVariables]
  exact contextualXor_splitVariables_le_five source target oldFlag newFlag a b tt tf ft ff


theorem laterMaskPair_actualInvocations (rename : Nat → Fin v) (context : Clause (Fin v))
    (position : Fin (laterBuses (parameters := parameters)).length) (channel : Fin parameters.channels)
    (start : SourcePrefix (parameters := parameters) rename)
    (flags : DirectionPair start.state context (SourceStagePolarity.laterFlagOutput rename .healthy position)
      (SourceStagePolarity.laterFlagOutput rename .faulty position))
    (absent : DirectionPair start.state context (SourceStagePolarity.laterAbsentOutput rename .healthy position channel)
      (SourceStagePolarity.laterAbsentOutput rename .faulty position channel)) :
    let actual := SourceBusAdvance.laterMaskPairFromStages rename context position channel start flags absent
    ∃ baseOne treeOne prefixOne baseTwo treeTwo prefixTwo,
      actual.steps = (prefixOne ++ (Controller.Resolution.Cases.compileTree baseOne treeOne).steps) ++
        (prefixTwo ++ (Controller.Resolution.Cases.compileTree baseTwo treeTwo).steps) ∧
      actual.state = (Controller.Resolution.Cases.compileTree baseTwo treeTwo).state ∧
      Controller.Resolution.Cases.ValidTree baseOne
        (context ++ [negate (SourceStageXor.laterMaskOutput rename .healthy position channel),
          SourceStageXor.laterMaskOutput rename .faulty position channel]) treeOne ∧
      Controller.Resolution.Cases.ValidTree baseTwo
        (context ++ [negate (SourceStageXor.laterMaskOutput rename .faulty position channel),
          SourceStageXor.laterMaskOutput rename .healthy position channel]) treeTwo ∧
      (splitVariables treeOne).card ≤ 2 ∧ (splitVariables treeTwo).card ≤ 2 ∧
      prefixOne.length ≤ 8 ∧ prefixTwo.length ≤ 8 := by
  let flagInputs : DirectionPair start.state context
      (SourceStageXor.laterMaskFlag rename .healthy position channel)
      (SourceStageXor.laterMaskFlag rename .faulty position channel) := by
    simpa only [SourceBusAdvance.laterMaskFlag_eq_flagOutput] using flags
  let absentInputs : DirectionPair start.state context
      (SourceStageXor.laterMaskAbsent rename .healthy position channel)
      (SourceStageXor.laterMaskAbsent rename .faulty position channel) := by
    simpa only [SourceBusAdvance.laterMaskAbsent_eq_absentOutput] using absent
  let left := SourceStageXor.laterMaskNativeRows rename .healthy position channel start
  let right := SourceStageXor.laterMaskNativeRows rename .faulty position channel start
  let first := SourceStageXor.guardedXor start.state context _ _ _ _ _ _ left right
    flagInputs.forward flagInputs.backward absentInputs.forward absentInputs.backward
  let nextFlags := flagInputs.afterTrace first.state first.steps first.checked
  let nextAbsent := absentInputs.afterTrace first.state first.steps first.checked
  let second := SourceStageXor.guardedXor first.state context _ _ _ _ _ _
    (right.afterTrace first.state first.steps first.checked) (left.afterTrace first.state first.steps first.checked)
    nextFlags.backward nextFlags.forward nextAbsent.backward nextAbsent.forward
  have actualSteps :
      (SourceBusAdvance.laterMaskPairFromStages rename context position channel start flags absent).steps =
        first.steps ++ second.steps := rfl
  have actualState :
      (SourceBusAdvance.laterMaskPairFromStages rename context position channel start flags absent).state =
        second.state := rfl
  obtain ⟨baseOne, treeOne, prefixOne, traceOne, stateOne, idOne, validOne, pivotsOne, budgetOne, countOne⟩ :=
    guardedXor_actualInvocation start.state context _ _ _ _ _ _ left right
      flagInputs.forward flagInputs.backward absentInputs.forward absentInputs.backward
  obtain ⟨baseTwo, treeTwo, prefixTwo, traceTwo, stateTwo, idTwo, validTwo, pivotsTwo, budgetTwo, countTwo⟩ :=
    guardedXor_actualInvocation first.state context _ _ _ _ _ _
      (right.afterTrace first.state first.steps first.checked) (left.afterTrace first.state first.steps first.checked)
      nextFlags.backward nextFlags.forward nextAbsent.backward nextAbsent.forward
  refine ⟨baseOne, treeOne, prefixOne, baseTwo, treeTwo, prefixTwo,
    actualSteps.trans (congrArg₂ List.append traceOne traceTwo),
    actualState.trans stateTwo, validOne, validTwo, ?_, ?_, countOne, countTwo⟩
  · rw [pivotsOne]
    exact Finset.card_le_two
  · rw [pivotsTwo]
    exact Finset.card_le_two

def resolutionRupTree (pivot : Literal (Fin v)) (leftClause rightClause : Clause (Fin v))
    (leftId rightId : Nat) : Controller.Resolution.Cases.CaseTree v :=
  .leaf ⟨leftId, leftClause, [⟨rightId, ⟨pivot, rightClause⟩⟩]⟩

theorem resolutionRupTree_valid (state : State v) (pivot : Literal (Fin v))
    (leftClause rightClause target : Clause (Fin v))
    (left : Rows.Available state leftClause) (right : Rows.Available state rightClause)
    (rule : ExactRule pivot leftClause rightClause target) :
    Controller.Resolution.Cases.ValidTree state target
      (resolutionRupTree pivot leftClause rightClause left.id right.id) := by
  have included (literal : Literal (Fin v))
      (member : literal ∈ resolvent pivot leftClause rightClause) : literal ∈ target :=
    (exactRule_sameLiterals rule literal).mpr member
  refine ⟨left.present, left.bound, ?_, ?_, ?_⟩
  · intro reason member
    have same : reason = (⟨right.id, ⟨pivot, rightClause⟩⟩ : Controller.Resolution.RUP.RowReason v) := by
      simpa only [List.mem_cons, List.not_mem_nil, or_false] using member
    subst reason
    exact ⟨right.present, right.bound, rule.2.1⟩
  · change Controller.Resolution.RUP.ReasonEarlier pivot rightClause target ∧ True
    refine ⟨⟨rule.2.1, ?_⟩, trivial⟩
    intro literal member different
    exact included literal ((mem_resolvent pivot literal leftClause rightClause).mpr
      (Or.inr ⟨member, different⟩))
  · change ClauseSubset leftClause ([negate pivot] ++ target)
    intro literal member
    by_cases same : literal = negate pivot
    · exact List.mem_append.mpr (Or.inl (by simpa only [List.mem_cons, List.not_mem_nil, or_false] using same))
    · exact List.mem_append.mpr (Or.inr (included literal
        ((mem_resolvent pivot literal leftClause rightClause).mpr (Or.inl ⟨member, same⟩))))

theorem resolutionRupTree_splitVariables (pivot : Literal (Fin v))
    (leftClause rightClause : Clause (Fin v)) (leftId rightId : Nat) :
    splitVariables (resolutionRupTree pivot leftClause rightClause leftId rightId) = ∅ := rfl

theorem resolutionRupTree_inferenceBudget (pivot : Literal (Fin v))
    (leftClause rightClause : Clause (Fin v)) (leftId rightId : Nat) :
    Controller.Resolution.Cases.inferenceBudget
      (resolutionRupTree pivot leftClause rightClause leftId rightId) = 1 := rfl

structure ResolutionRupInvocation (v : Nat) where
  base : State v
  step : Step v
  target : Clause (Fin v)
  tree : Controller.Resolution.Cases.CaseTree v

def resolutionRupSchedule (state : State v) :
    List (Step v) → Option (List (ResolutionRupInvocation v))
  | [] => some []
  | step :: steps =>
    match state.rows step.left with
    | none => none
    | some left =>
      match state.rows step.right with
      | none => none
      | some right =>
        match applyStep state step with
        | none => none
        | some next =>
          match resolutionRupSchedule next steps with
          | none => none
          | some tail => some
            ((⟨state, step, step.clause,
              resolutionRupTree step.pivot left right step.left step.right⟩ :
                ResolutionRupInvocation v) :: tail)

theorem row_bound_of_bounded (state : State v)
    (bounded : Controller.Resolution.Rebase.RowsBounded state)
    (id : Nat) (clause : Clause (Fin v)) (present : state.rows id = some clause) :
    id ≤ state.lastId := by
  by_contra high
  have beyond : state.lastId < id := by omega
  have absent := bounded id beyond
  rw [present] at absent
  cases absent

def ResolutionRupInvocation.Sound (invocation : ResolutionRupInvocation v) : Prop :=
  Controller.Resolution.Cases.ValidTree invocation.base invocation.target invocation.tree ∧
  splitVariables invocation.tree = ∅ ∧
  Controller.Resolution.Cases.inferenceBudget invocation.tree = 1

theorem resolutionRupSchedule_sound (state next : State v) (steps : List (Step v))
    (bounded : Controller.Resolution.Rebase.RowsBounded state)
    (checked : runSteps state steps = some next) :
    ∃ records, resolutionRupSchedule state steps = some records ∧
      records.length = steps.length ∧
      ∀ record ∈ records, record.Sound := by
  induction steps generalizing state with
  | nil =>
    exact ⟨[], rfl, rfl, by intro record member; exact False.elim (List.not_mem_nil member)⟩
  | cons step steps ih =>
    cases applied : applyStep state step with
    | none =>
      simp only [runSteps, applied, Option.bind_none] at checked
      cases checked
    | some middle =>
      have tailChecked : runSteps middle steps = some next := by
        simpa only [runSteps, applied, Option.bind_some] using checked
      obtain ⟨left, right, leftRow, rightRow, stepRule, middleEqual⟩ := applyStep_success applied
      obtain ⟨tail, tailRun, tailLength, tailSound⟩ :=
        ih middle (Controller.Resolution.Rebase.applyStep_bounded bounded applied) tailChecked
      let record : ResolutionRupInvocation v :=
        ⟨state, step, step.clause, resolutionRupTree step.pivot left right step.left step.right⟩
      have sound : record.Sound := by
        refine ⟨resolutionRupTree_valid state step.pivot left right step.clause
          ⟨step.left, leftRow, row_bound_of_bounded state bounded _ _ leftRow⟩
          ⟨step.right, rightRow, row_bound_of_bounded state bounded _ _ rightRow⟩
          stepRule.2.2.2, rfl, rfl⟩
      refine ⟨record :: tail, ?_, ?_, ?_⟩
      · simp only [resolutionRupSchedule, leftRow, rightRow, applied, tailRun, record]
      · simpa only [List.length_cons] using congrArg Nat.succ tailLength
      · intro item member
        rcases List.mem_cons.mp member with same | member
        · subst item
          exact sound
        · exact tailSound item member

theorem SourcePrefix.resolutionRupSchedule_sound (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename) :
    ∃ records,
      resolutionRupSchedule (initialState (relabel rename (formula parameters))) prefixState.steps = some records ∧
      records.length = prefixState.steps.length ∧
      ∀ record ∈ records, record.Sound :=
  Controller.NativeProof.SourceDecoderTraversal.resolutionRupSchedule_sound _ _ _
    (Controller.Resolution.Rebase.initialState_bounded _) prefixState.checked

theorem nativeCofactorPrefix_resolutionRupSchedule_sound
    (rename : Nat → Fin v) (drive : parameters.drive = true) :
    ∃ records,
      resolutionRupSchedule (initialState (relabel rename (formula parameters)))
        (nativeCofactorPrefix rename drive).steps = some records ∧
      records.length ≤ actualSelectorResolutionBudget parameters ∧
      ∀ record ∈ records, record.Sound := by
  obtain ⟨records, run, count, sound⟩ :=
    SourcePrefix.resolutionRupSchedule_sound rename (nativeCofactorPrefix rename drive)
  exact ⟨records, run, count.le.trans (nativeCofactorPrefix_count rename drive), sound⟩

def treeParentIds : Controller.Resolution.Cases.CaseTree v → List Nat
  | .leaf certificate => certificate.rowId :: certificate.reasons.map Controller.Resolution.RUP.RowReason.rowId
  | .fork _ left right => treeParentIds left ++ treeParentIds right

theorem resolutionRupSchedule_steps
    (state : State v) (steps : List (Step v)) (records : List (ResolutionRupInvocation v))
    (run : resolutionRupSchedule state steps = some records) :
    records.map ResolutionRupInvocation.step = steps ∧
    ∀ record ∈ records, treeParentIds record.tree = [record.step.left, record.step.right] := by
  induction steps generalizing state records with
  | nil =>
    have same : [] = records := Option.some.inj run
    subst records
    exact ⟨rfl, by intro record member; exact False.elim (List.not_mem_nil member)⟩
  | cons step steps ih =>
    cases leftRow : state.rows step.left with
    | none => simp only [resolutionRupSchedule, leftRow, Option.bind_none] at run; cases run
    | some left =>
      cases rightRow : state.rows step.right with
      | none => simp only [resolutionRupSchedule, leftRow, rightRow, Option.bind_some, Option.bind_none] at run; cases run
      | some right =>
        cases applied : applyStep state step with
        | none => simp only [resolutionRupSchedule, leftRow, rightRow, applied, Option.bind_some, Option.bind_none] at run; cases run
        | some middle =>
          cases tailRun : resolutionRupSchedule middle steps with
          | none => simp only [resolutionRupSchedule, leftRow, rightRow, applied, tailRun, Option.bind_some, Option.bind_none] at run; cases run
          | some tail =>
            let head : ResolutionRupInvocation v :=
              ⟨state, step, step.clause, resolutionRupTree step.pivot left right step.left step.right⟩
            have same : head :: tail = records := Option.some.inj (by
              simpa only [resolutionRupSchedule, leftRow, rightRow, applied, tailRun, Option.bind_some] using run)
            subst records
            have previous := ih middle tail tailRun
            constructor
            · exact congrArg (List.cons step) previous.1
            · intro record member
              rcases List.mem_cons.mp member with same | member
              · subst record
                rfl
              · exact previous.2 record member

theorem resolutionRupSchedule_parentSupport
    (n : Nat) (allowed : Nat → Prop) (state : State v) (steps : List (Step v))
    (records : List (ResolutionRupInvocation v))
    (run : resolutionRupSchedule state steps = some records)
    (supported : TraceOriginalSupport n allowed steps) :
    ∀ record ∈ records, ∀ parent ∈ treeParentIds record.tree,
      (parent ≤ n → allowed parent) ∧
      (n < parent → ∃ earlier ∈ steps, earlier.id = parent ∧ earlier.id < record.step.id) := by
  have actual := resolutionRupSchedule_steps state steps records run
  intro record member parent parentMember
  have stepMember : record.step ∈ steps := by
    rw [← actual.1]
    exact List.mem_map.mpr ⟨record, member, rfl⟩
  rw [actual.2 record member] at parentMember
  exact supported record.step stepMember parent parentMember

theorem nativeCofactorPrefix_resolutionRupParents
    (rename : Nat → Fin v) (drive : parameters.drive = true) :
    ∃ records,
      resolutionRupSchedule (initialState (relabel rename (formula parameters)))
        (nativeCofactorPrefix rename drive).steps = some records ∧
      records.length ≤ actualSelectorResolutionBudget parameters ∧
      ∀ record ∈ records, record.Sound ∧
        ∀ parent ∈ treeParentIds record.tree,
          (parent ≤ (formula parameters).clauses.size →
            SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename parent) ∧
          ((formula parameters).clauses.size < parent →
            ∃ earlier ∈ (nativeCofactorPrefix rename drive).steps,
              earlier.id = parent ∧ earlier.id < record.step.id) := by
  obtain ⟨records, run, count, sound⟩ :=
    nativeCofactorPrefix_resolutionRupSchedule_sound rename drive
  have supported : TraceOriginalSupport (formula parameters).clauses.size
      (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
      (nativeCofactorPrefix rename drive).steps :=
    nativeCofactorPrefix_supported rename drive
  have parents := resolutionRupSchedule_parentSupport _ _
    (initialState (relabel rename (formula parameters)))
    (nativeCofactorPrefix rename drive).steps records run supported
  exact ⟨records, run, count, fun record member => ⟨sound record member, parents record member⟩⟩


def maskBankInvocationChunks (rename : Nat → Fin v) (flag : Bool)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (inputs : SourceBusAdvance.MaskInputs (parameters := parameters) rename flag position) :
    List (Fin parameters.channels) → List (List (Step v))
  | [] => []
  | channel :: channels =>
    let prior := SourceBusAdvance.buildMaskBank rename flag position inputs channels
    let extended := inputs.afterTrace prior.state prior.steps prior.checked
    let added := SourceBusAdvance.laterMaskChannelFromBanks rename
      (equalFlagContext (parameters := parameters) rename flag) position channel
      extended.checkedPrefix (extended.terms channel) extended.flags
    maskBankInvocationChunks rename flag position inputs channels ++ [added.steps]

theorem maskBankInvocationChunks_length (rename : Nat → Fin v) (flag : Bool)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (inputs : SourceBusAdvance.MaskInputs (parameters := parameters) rename flag position)
    (channels : List (Fin parameters.channels)) :
    (maskBankInvocationChunks rename flag position inputs channels).length = channels.length := by
  induction channels with
  | nil => rfl
  | cons channel channels ih =>
    simp only [maskBankInvocationChunks, List.length_append, List.length_cons,
      List.length_nil, ih]


theorem maskBankInvocationChunks_flatten (rename : Nat → Fin v) (flag : Bool)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (inputs : SourceBusAdvance.MaskInputs (parameters := parameters) rename flag position)
    (channels : List (Fin parameters.channels)) :
    (maskBankInvocationChunks rename flag position inputs channels).flatMap id =
      (SourceBusAdvance.buildMaskBank rename flag position inputs channels).steps := by
  induction channels with
  | nil => rfl
  | cons channel channels ih =>
    let prior := SourceBusAdvance.buildMaskBank rename flag position inputs channels
    let extended := inputs.afterTrace prior.state prior.steps prior.checked
    let added := SourceBusAdvance.laterMaskChannelFromBanks rename
      (equalFlagContext (parameters := parameters) rename flag) position channel
      extended.checkedPrefix (extended.terms channel) extended.flags
    have scalar :
        (SourceBusAdvance.maskBankStep rename flag position inputs channels prior channel).steps =
          prior.steps ++ added.steps := by
      have projected := congrArg
        (fun next : SourceBusAdvance.MaskBank rename flag position inputs (channel :: channels) =>
          next.steps)
        (SourceEqualSchedule.maskBankStep_kernel_eq rename flag position inputs channels prior channel)
      exact projected
    change
      ((maskBankInvocationChunks rename flag position inputs channels) ++ [added.steps]).flatMap id =
        (SourceBusAdvance.maskBankStep rename flag position inputs channels prior channel).steps
    rw [List.flatMap_append]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, ih]
    exact scalar.symm


theorem maskBankInvocationChunks_bounded (rename : Nat → Fin v) (flag : Bool)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (inputs : SourceBusAdvance.MaskInputs (parameters := parameters) rename flag position)
    (channels : List (Fin parameters.channels)) :
    ∀ chunk ∈ maskBankInvocationChunks rename flag position inputs channels,
      chunk.length ≤ 26 := by
  induction channels with
  | nil => intro chunk member; exact False.elim (List.not_mem_nil member)
  | cons channel channels ih =>
    let prior := SourceBusAdvance.buildMaskBank rename flag position inputs channels
    let extended := inputs.afterTrace prior.state prior.steps prior.checked
    let added := SourceBusAdvance.laterMaskChannelFromBanks rename
      (equalFlagContext (parameters := parameters) rename flag) position channel
      extended.checkedPrefix (extended.terms channel) extended.flags
    intro chunk member
    change chunk ∈ maskBankInvocationChunks rename flag position inputs channels ++ [added.steps] at member
    rcases List.mem_append.mp member with old | latest
    · exact ih chunk old
    · have same : chunk = added.steps := by
        simpa only [List.mem_cons, List.not_mem_nil, or_false] using latest
      subst chunk
      exact added.count

theorem maskBankInvocationChunks_expandedCount (rename : Nat → Fin v) (flag : Bool)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (inputs : SourceBusAdvance.MaskInputs (parameters := parameters) rename flag position)
    (channels : List (Fin parameters.channels)) :
    ((maskBankInvocationChunks rename flag position inputs channels).flatMap id).length ≤
      26 * channels.length := by
  rw [maskBankInvocationChunks_flatten]
  exact (SourceBusAdvance.buildMaskBank rename flag position inputs channels).count


theorem laterMaskChannel_actualInvocations (rename : Nat → Fin v) (context : Clause (Fin v))
    (position : Fin (laterBuses (parameters := parameters)).length) (channel : Fin parameters.channels)
    (start : SourcePrefix (parameters := parameters) rename)
    (terms : DirectionPair start.state context
      (SourceStageCongruence.laterTermOutput rename .healthy position channel)
      (SourceStageCongruence.laterTermOutput rename .faulty position channel))
    (flags : DirectionPair start.state context
      (SourceStagePolarity.laterFlagOutput rename .healthy position)
      (SourceStagePolarity.laterFlagOutput rename .faulty position)) :
    let actual := SourceBusAdvance.laterMaskChannelFromBanks rename context position channel start terms flags
    ∃ notSteps baseOne treeOne prefixOne baseTwo treeTwo prefixTwo,
      actual.steps = notSteps ++
        ((prefixOne ++ (Controller.Resolution.Cases.compileTree baseOne treeOne).steps) ++
         (prefixTwo ++ (Controller.Resolution.Cases.compileTree baseTwo treeTwo).steps)) ∧
      actual.state = (Controller.Resolution.Cases.compileTree baseTwo treeTwo).state ∧
      notSteps.length ≤ 4 ∧
      Controller.Resolution.Cases.ValidTree baseOne
        (context ++ [negate (SourceStageXor.laterMaskOutput rename .healthy position channel),
          SourceStageXor.laterMaskOutput rename .faulty position channel]) treeOne ∧
      Controller.Resolution.Cases.ValidTree baseTwo
        (context ++ [negate (SourceStageXor.laterMaskOutput rename .faulty position channel),
          SourceStageXor.laterMaskOutput rename .healthy position channel]) treeTwo ∧
      (splitVariables treeOne).card ≤ 2 ∧ (splitVariables treeTwo).card ≤ 2 ∧
      prefixOne.length ≤ 8 ∧ prefixTwo.length ≤ 8 := by
  let first := SourceBusAdvance.laterAbsentPairFromTerm rename context position channel start terms
  let nextPrefix := start.extend first.state first.steps first.checked
  let nextFlags := flags.afterTrace first.state first.steps first.checked
  let second := SourceBusAdvance.laterMaskPairFromStages rename context position channel
    nextPrefix nextFlags first.pair
  obtain ⟨baseOne,treeOne,prefixOne,baseTwo,treeTwo,prefixTwo,
    stepsEqual,stateEqual,validOne,validTwo,pivotsOne,pivotsTwo,countOne,countTwo⟩ :=
      laterMaskPair_actualInvocations rename context position channel nextPrefix nextFlags first.pair
  have actualSteps :
      (SourceBusAdvance.laterMaskChannelFromBanks rename context position channel start terms flags).steps =
        first.steps ++ second.steps := rfl
  have actualState :
      (SourceBusAdvance.laterMaskChannelFromBanks rename context position channel start terms flags).state =
        second.state := rfl
  exact ⟨first.steps,baseOne,treeOne,prefixOne,baseTwo,treeTwo,prefixTwo,
    actualSteps.trans (congrArg (List.append first.steps) stepsEqual),
    actualState.trans stateEqual,first.count,validOne,validTwo,pivotsOne,pivotsTwo,countOne,countTwo⟩

def MaskBankChunkOrigin (rename : Nat → Fin v) (flag : Bool)
    (position : Fin (laterBuses (parameters := parameters)).length) (chunk : List (Step v)) : Prop :=
  ∃ channel : Fin parameters.channels,
    ∃ start : SourcePrefix (parameters := parameters) rename,
    ∃ terms : DirectionPair start.state (equalFlagContext (parameters := parameters) rename flag)
      (SourceStageCongruence.laterTermOutput rename .healthy position channel)
      (SourceStageCongruence.laterTermOutput rename .faulty position channel),
    ∃ flags : DirectionPair start.state (equalFlagContext (parameters := parameters) rename flag)
      (SourceStagePolarity.laterFlagOutput rename .healthy position)
      (SourceStagePolarity.laterFlagOutput rename .faulty position),
      chunk = (SourceBusAdvance.laterMaskChannelFromBanks rename
        (equalFlagContext (parameters := parameters) rename flag) position channel start terms flags).steps

theorem maskBankInvocationChunks_actualCallbacks (rename : Nat → Fin v) (flag : Bool)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (inputs : SourceBusAdvance.MaskInputs (parameters := parameters) rename flag position)
    (channels : List (Fin parameters.channels)) :
    ∀ chunk ∈ maskBankInvocationChunks rename flag position inputs channels,
      MaskBankChunkOrigin rename flag position chunk := by
  induction channels with
  | nil => intro chunk member; exact False.elim (List.not_mem_nil member)
  | cons channel channels ih =>
    let prior := SourceBusAdvance.buildMaskBank rename flag position inputs channels
    let extended := inputs.afterTrace prior.state prior.steps prior.checked
    let added := SourceBusAdvance.laterMaskChannelFromBanks rename
      (equalFlagContext (parameters := parameters) rename flag) position channel
      extended.checkedPrefix (extended.terms channel) extended.flags
    intro chunk member
    change chunk ∈ maskBankInvocationChunks rename flag position inputs channels ++ [added.steps] at member
    rcases List.mem_append.mp member with old | latest
    · exact ih chunk old
    · have same : chunk = added.steps := by
        simpa only [List.mem_cons, List.not_mem_nil, or_false] using latest
      exact ⟨channel,extended.checkedPrefix,extended.terms channel,extended.flags,same⟩


theorem resolutionRupSchedule_append
    (state middle : State v) (first second : List (Step v))
    (one two : List (ResolutionRupInvocation v))
    (checked : runSteps state first = some middle)
    (firstAnnotated : resolutionRupSchedule state first = some one)
    (secondAnnotated : resolutionRupSchedule middle second = some two) :
    resolutionRupSchedule state (first ++ second) = some (one ++ two) := by
  induction first generalizing state one with
  | nil =>
    have stateEqual : state = middle := Option.some.inj checked
    subst middle
    have recordsEqual : [] = one := Option.some.inj firstAnnotated
    subst one
    exact secondAnnotated
  | cons step first ih =>
    cases applied : applyStep state step with
    | none =>
      simp only [runSteps, applied] at checked
      cases checked
    | some next =>
      have checkedTail : runSteps next first = some middle := by
        simpa only [runSteps, applied] using checked
      obtain ⟨left,right,leftRow,rightRow,rule,nextEqual⟩ := applyStep_success applied
      cases annotatedTail : resolutionRupSchedule next first with
      | none =>
        simp only [resolutionRupSchedule,leftRow,rightRow,applied,annotatedTail] at firstAnnotated
        cases firstAnnotated
      | some tail =>
        let head : ResolutionRupInvocation v :=
          ⟨state,step,step.clause,resolutionRupTree step.pivot left right step.left step.right⟩
        have recordsEqual : head :: tail = one := Option.some.inj (by
          simpa only [resolutionRupSchedule,leftRow,rightRow,applied,annotatedTail,head]
            using firstAnnotated)
        subst one
        have remaining := ih next tail checkedTail annotatedTail
        simp only [List.cons_append,resolutionRupSchedule,leftRow,rightRow,applied,remaining,head]


theorem emptyReasonTreeOrigins_decoderPort (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (tree : Controller.Resolution.Cases.CaseTree v)
    (original : SourceEqualSchedule.EmptyReasonTreeOrigins
      (parameters := parameters) rename prefixState.steps tree) :
    CaseTreeOriginals rename prefixState tree := by
  induction tree with
  | leaf certificate =>
    refine ⟨?_, ?_⟩
    · rcases original.2 with native | derived
      · exact Or.inl (SourceDecoderSchedule.controller_original_allowed rename _ native)
      · exact Or.inr derived
    · intro reason member
      rw [original.1] at member
      exact False.elim (List.not_mem_nil member)
  | fork pivot left right leftIH rightIH =>
    exact ⟨leftIH original.1, rightIH original.2⟩

theorem guardedXor_actualCaseOrigins (rename : Nat → Fin v)
    (start : SourcePrefix (parameters := parameters) rename)
    (context : Clause (Fin v)) (a b c d leftOut rightOut : Literal (Fin v))
    (left : SourceStageXor.XorRows start.state a b leftOut) (right : SourceStageXor.XorRows start.state c d rightOut)
    (aForward : GuardedTransfer start.state context a c)
    (aBackward : GuardedTransfer start.state context c a)
    (bForward : GuardedTransfer start.state context b d)
    (bBackward : GuardedTransfer start.state context d b)
    (supported : SourceMixedSchedule.PrefixOriginalSupport rename start)
    (leftOriginal : SourceEqualSchedule.XorRowsOriginalSupport rename start left)
    (rightOriginal : SourceEqualSchedule.XorRowsOriginalSupport rename start right)
    (af : SourceEqualSchedule.GuardedTransferOrigin rename start aForward)
    (ab : SourceEqualSchedule.GuardedTransferOrigin rename start aBackward)
    (bf : SourceEqualSchedule.GuardedTransferOrigin rename start bForward)
    (bb : SourceEqualSchedule.GuardedTransferOrigin rename start bBackward) :

    ∃ branchPrefix : SourcePrefix (parameters := parameters) rename,
      ∃ tree : Controller.Resolution.Cases.CaseTree v, ∃ branchSteps : List (Step v),
        branchPrefix.steps = start.steps ++ branchSteps ∧
        (SourceStageXor.guardedXor start.state context a b c d leftOut rightOut left right
          aForward aBackward bForward bBackward).steps =
            branchSteps ++ (Controller.Resolution.Cases.compileTree branchPrefix.state tree).steps ∧
        (SourceStageXor.guardedXor start.state context a b c d leftOut rightOut left right
          aForward aBackward bForward bBackward).state =
            (Controller.Resolution.Cases.compileTree branchPrefix.state tree).state ∧
        CaseTreeOriginals rename branchPrefix tree ∧
        Controller.Resolution.Cases.ValidTree branchPrefix.state
          (context ++ [negate leftOut,rightOut]) tree ∧
        (splitVariables tree).card ≤ 2 ∧ branchSteps.length ≤ 8 := by
  let runBranch := fun (next : State v) (steps : List (Step v))
      (checked : runSteps start.state steps = some next) (x y : Bool) =>
    SourceStageXor.xorCofactor next context a b c d leftOut rightOut
      (left.afterTrace next steps checked) (right.afterTrace next steps checked)
      (aForward.afterTrace next steps checked) (aBackward.afterTrace next steps checked)
      (bForward.afterTrace next steps checked) (bBackward.afterTrace next steps checked) x y
  have branchSupport := fun next steps checked x y
      (trace : SourceMixedSchedule.PrefixOriginalSupport rename (start.extend next steps checked)) =>
    SourceEqualSchedule.xorCofactor_supported rename (start.extend next steps checked) context a b c d leftOut rightOut
      (left.afterTrace next steps checked) (right.afterTrace next steps checked)
      (aForward.afterTrace next steps checked) (aBackward.afterTrace next steps checked)
      (bForward.afterTrace next steps checked) (bBackward.afterTrace next steps checked) x y trace
      (SourceEqualSchedule.XorRowsOriginalSupport.afterTrace rename start left next steps checked leftOriginal)
      (SourceEqualSchedule.XorRowsOriginalSupport.afterTrace rename start right next steps checked rightOriginal)
      (SourceEqualSchedule.GuardedTransferOrigin.afterTrace rename start aForward af next steps checked)
      (SourceEqualSchedule.GuardedTransferOrigin.afterTrace rename start aBackward ab next steps checked)
      (SourceEqualSchedule.GuardedTransferOrigin.afterTrace rename start bForward bf next steps checked)
      (SourceEqualSchedule.GuardedTransferOrigin.afterTrace rename start bBackward bb next steps checked)
  let first := runBranch start.state [] rfl true true
  have one := branchSupport start.state [] rfl true true (by
    simpa only [SourceMixedSchedule.PrefixOriginalSupport, SourcePrefix.extend, List.append_nil] using supported)
  let second := runBranch first.state first.steps first.checked true false
  have two := branchSupport first.state first.steps first.checked true false (by
    simpa only [SourceMixedSchedule.ProjectionOriginalSupport, SourceMixedSchedule.PrefixOriginalSupport, SourcePrefix.extend,
      List.append_nil, first, runBranch] using one.1)
  have firstTwo : runSteps start.state (first.steps ++ second.steps) = some second.state := by
    rw [runSteps_append, first.checked]; exact second.checked
  let third := runBranch second.state (first.steps ++ second.steps) firstTwo false true
  have three := branchSupport second.state (first.steps ++ second.steps) firstTwo false true (by
    simpa only [SourceMixedSchedule.PrefixOriginalSupport, SourcePrefix.extend, List.append_assoc] using two.1)
  have firstThree : runSteps start.state ((first.steps ++ second.steps) ++ third.steps) = some third.state := by
    rw [runSteps_append, firstTwo]; exact third.checked
  let fourth := runBranch third.state ((first.steps ++ second.steps) ++ third.steps) firstThree false false
  have four := branchSupport third.state ((first.steps ++ second.steps) ++ third.steps)
    firstThree false false (by
      simpa only [SourceMixedSchedule.PrefixOriginalSupport, SourcePrefix.extend, List.append_assoc] using three.1)
  have tailRun : runSteps second.state (third.steps ++ fourth.steps) = some fourth.state := by
    rw [runSteps_append, third.checked]; exact fourth.checked
  have firstTail : runSteps first.state (second.steps ++ (third.steps ++ fourth.steps)) = some fourth.state := by
    rw [runSteps_append, second.checked]; exact tailRun
  let tt := FoldProjection.afterTrace first.result fourth.state (second.steps ++ (third.steps ++ fourth.steps)) firstTail
  let tf := FoldProjection.afterTrace second.result fourth.state (third.steps ++ fourth.steps) tailRun
  let ft := FoldProjection.afterTrace third.result fourth.state fourth.steps fourth.checked
  let branchPrefix := (start.extend third.state ((first.steps ++ second.steps) ++ third.steps) firstThree).extend
    fourth.state fourth.steps fourth.checked
  have ttOrigin := SourceFoldProvenance.resultOrigin_append_right _ _ _ (second.steps ++ (third.steps ++ fourth.steps))
    first.result.row.id one.2
  have tfOrigin := SourceFoldProvenance.resultOrigin_append_right _ _ _ (third.steps ++ fourth.steps) second.result.row.id two.2
  have ftOrigin := SourceFoldProvenance.resultOrigin_append_right _ _ _ fourth.steps third.result.row.id three.2

  let tree := SourceStageXor.xorCaseTree branchPrefix.state
    (context ++ [negate leftOut,rightOut]) a b tt tf ft fourth.result
  have origins : SourceEqualSchedule.EmptyReasonTreeOrigins (parameters := parameters)
      rename branchPrefix.steps tree := by
    refine ⟨⟨⟨rfl, ?_⟩, ⟨rfl, ?_⟩⟩, ⟨⟨rfl, ?_⟩, ⟨rfl, ?_⟩⟩⟩
    · simpa only [branchPrefix, SourcePrefix.extend, List.append_assoc, List.nil_append,
        first, runBranch, tt, FoldProjection.afterTrace] using ttOrigin
    · simpa only [branchPrefix, SourcePrefix.extend, List.append_assoc,
        second, runBranch, tf, FoldProjection.afterTrace] using tfOrigin
    · simpa only [branchPrefix, SourcePrefix.extend, List.append_assoc,
        third, runBranch, ft, FoldProjection.afterTrace] using ftOrigin
    · exact four.2
  let branchSteps := ((first.steps ++ second.steps) ++ third.steps) ++ fourth.steps
  refine ⟨branchPrefix,tree,branchSteps,?_,?_,?_,
    emptyReasonTreeOrigins_decoderPort rename branchPrefix tree origins,?_,?_,?_⟩
  · simp only [branchPrefix,branchSteps,SourcePrefix.extend,List.append_assoc]
  · rfl
  · rfl
  · exact SourceStageXor.xorCaseTree_valid branchPrefix.state
      (context ++ [negate leftOut,rightOut]) a b tt tf ft fourth.result
  · exact Controller.NativeProof.SourceDecoderTraversal.xorCaseTree_splitVariables_card
      fourth.state (context ++ [negate leftOut,rightOut]) a b tt tf ft fourth.result
  · have oneCount := first.count
    have twoCount := second.count
    have threeCount := third.count
    have fourCount := fourth.count
    dsimp only [branchSteps]
    simp only [List.length_append]
    omega


theorem caseTree_valid_afterTrace (state next : State v)
    (steps : List (Step v)) (checked : runSteps state steps = some next)
    (target : Clause (Fin v)) (tree : Controller.Resolution.Cases.CaseTree v)
    (valid : Controller.Resolution.Cases.ValidTree state target tree) :
    Controller.Resolution.Cases.ValidTree next target tree := by
  induction tree generalizing target with
  | leaf certificate =>
    refine ⟨(runSteps_preserves_old_rows checked certificate.rowId valid.2.1).trans valid.1,
      Nat.le_trans valid.2.1 (runSteps_lastId_le checked), ?_, valid.2.2.2.1, valid.2.2.2.2⟩
    intro reason member
    have old := valid.2.2.1 reason member
    exact ⟨(runSteps_preserves_old_rows checked reason.rowId old.2.1).trans old.1,
      Nat.le_trans old.2.1 (runSteps_lastId_le checked), old.2.2⟩
  | fork pivot left right leftIH rightIH =>
    exact ⟨leftIH _ valid.1, rightIH _ valid.2⟩

theorem CaseTreeOriginals.afterTrace (rename : Nat → Fin v)
    (start : SourcePrefix (parameters := parameters) rename)
    (tree : Controller.Resolution.Cases.CaseTree v)
    (original : CaseTreeOriginals rename start tree)
    (next : State v) (steps : List (Step v))
    (checked : runSteps start.state steps = some next) :
    CaseTreeOriginals rename (start.extend next steps checked) tree := by
  induction tree with
  | leaf certificate =>
    refine ⟨SourceFoldProvenance.resultOrigin_append_right _ _ start.steps steps
      certificate.rowId original.1, ?_⟩
    intro reason member
    exact SourceFoldProvenance.resultOrigin_append_right _ _ start.steps steps
      reason.rowId (original.2 reason member)
  | fork pivot left right leftIH rightIH =>
    exact ⟨leftIH original.1, rightIH original.2⟩


theorem laterMaskPair_actualCaseOrigins (rename : Nat → Fin v) (context : Clause (Fin v))
    (position : Fin (laterBuses (parameters := parameters)).length) (channel : Fin parameters.channels)
    (start : SourcePrefix (parameters := parameters) rename)
    (flags : DirectionPair start.state context (SourceStagePolarity.laterFlagOutput rename .healthy position)
      (SourceStagePolarity.laterFlagOutput rename .faulty position))
    (absent : DirectionPair start.state context (SourceStagePolarity.laterAbsentOutput rename .healthy position channel)
      (SourceStagePolarity.laterAbsentOutput rename .faulty position channel))
    (supported : SourceMixedSchedule.PrefixOriginalSupport rename start)
    (flagsOriginal : SourceEqualSchedule.DirectionPairOrigin rename start flags)
    (absentOriginal : SourceEqualSchedule.DirectionPairOrigin rename start absent) :

    ∃ sourceOne : SourcePrefix (parameters := parameters) rename,
      ∃ treeOne : Controller.Resolution.Cases.CaseTree v, ∃ branchOne : List (Step v),
      ∃ sourceTwo : SourcePrefix (parameters := parameters) rename,
      ∃ treeTwo : Controller.Resolution.Cases.CaseTree v, ∃ branchTwo : List (Step v),
        (SourceBusAdvance.laterMaskPairFromStages rename context position channel start flags absent).steps =
          (branchOne ++ (Controller.Resolution.Cases.compileTree sourceOne.state treeOne).steps) ++
          (branchTwo ++ (Controller.Resolution.Cases.compileTree sourceTwo.state treeTwo).steps) ∧
        (SourceBusAdvance.laterMaskPairFromStages rename context position channel start flags absent).state =
          (Controller.Resolution.Cases.compileTree sourceTwo.state treeTwo).state ∧
        sourceOne.steps = start.steps ++ branchOne ∧
        sourceTwo.steps =
          (start.steps ++ (branchOne ++ (Controller.Resolution.Cases.compileTree sourceOne.state treeOne).steps)) ++ branchTwo ∧
        CaseTreeOriginals rename sourceOne treeOne ∧ CaseTreeOriginals rename sourceTwo treeTwo ∧
        Controller.Resolution.Cases.ValidTree sourceOne.state
          (context ++ [negate (SourceStageXor.laterMaskOutput rename .healthy position channel),
            SourceStageXor.laterMaskOutput rename .faulty position channel]) treeOne ∧
        Controller.Resolution.Cases.ValidTree sourceTwo.state
          (context ++ [negate (SourceStageXor.laterMaskOutput rename .faulty position channel),
            SourceStageXor.laterMaskOutput rename .healthy position channel]) treeTwo ∧
        (splitVariables treeOne).card ≤ 2 ∧ (splitVariables treeTwo).card ≤ 2 ∧
        branchOne.length ≤ 8 ∧ branchTwo.length ≤ 8 := by
  let flagInputs : DirectionPair start.state context (SourceStageXor.laterMaskFlag rename .healthy position channel)
      (SourceStageXor.laterMaskFlag rename .faulty position channel) := by
    simpa only [SourceBusAdvance.laterMaskFlag_eq_flagOutput] using flags
  let absentInputs : DirectionPair start.state context (SourceStageXor.laterMaskAbsent rename .healthy position channel)
      (SourceStageXor.laterMaskAbsent rename .faulty position channel) := by
    simpa only [SourceBusAdvance.laterMaskAbsent_eq_absentOutput] using absent
  have flagOrigin : SourceEqualSchedule.DirectionPairOrigin rename start flagInputs := by
    dsimp only [flagInputs]
    apply SourceEqualSchedule.directionPairOrigin_mpr rename start
      (SourceBusAdvance.laterMaskFlag_eq_flagOutput rename .healthy position channel).symm
      (SourceBusAdvance.laterMaskFlag_eq_flagOutput rename .faulty position channel).symm
    exact flagsOriginal
  have absentOrigin : SourceEqualSchedule.DirectionPairOrigin rename start absentInputs := by
    dsimp only [absentInputs]
    apply SourceEqualSchedule.directionPairOrigin_mpr rename start
      (SourceBusAdvance.laterMaskAbsent_eq_absentOutput rename .healthy position channel).symm
      (SourceBusAdvance.laterMaskAbsent_eq_absentOutput rename .faulty position channel).symm
    exact absentOriginal
  let left := SourceStageXor.laterMaskNativeRows rename .healthy position channel start
  let right := SourceStageXor.laterMaskNativeRows rename .faulty position channel start
  have leftOrigin := SourceEqualSchedule.laterMaskNativeRows_supported rename .healthy position channel start
  have rightOrigin := SourceEqualSchedule.laterMaskNativeRows_supported rename .faulty position channel start
  let first := SourceStageXor.guardedXor start.state context _ _ _ _ _ _ left right
    flagInputs.forward flagInputs.backward absentInputs.forward absentInputs.backward
  have firstSupport := SourceEqualSchedule.guardedXor_supported rename start context _ _ _ _ _ _ left right
    flagInputs.forward flagInputs.backward absentInputs.forward absentInputs.backward
    supported leftOrigin rightOrigin flagOrigin.1 flagOrigin.2 absentOrigin.1 absentOrigin.2
  let current := start.extend first.state first.steps first.checked
  let nextFlags := flagInputs.afterTrace first.state first.steps first.checked
  let nextAbsent := absentInputs.afterTrace first.state first.steps first.checked
  have nextFlagOrigin := SourceEqualSchedule.DirectionPairOrigin.afterTrace rename start flagInputs flagOrigin
    first.state first.steps first.checked
  have nextAbsentOrigin := SourceEqualSchedule.DirectionPairOrigin.afterTrace rename start absentInputs absentOrigin
    first.state first.steps first.checked
  let second := SourceStageXor.guardedXor first.state context _ _ _ _ _ _
    (right.afterTrace first.state first.steps first.checked)
    (left.afterTrace first.state first.steps first.checked)
    nextFlags.backward nextFlags.forward nextAbsent.backward nextAbsent.forward


  obtain ⟨sourceOne,treeOne,branchOne,onePrefix,oneSteps,oneState,oneOrigin,oneValid,onePivots,oneCount⟩ :=
    guardedXor_actualCaseOrigins rename start context _ _ _ _ _ _ left right
      flagInputs.forward flagInputs.backward absentInputs.forward absentInputs.backward
      supported leftOrigin rightOrigin flagOrigin.1 flagOrigin.2 absentOrigin.1 absentOrigin.2
  obtain ⟨sourceTwo,treeTwo,branchTwo,twoPrefix,twoSteps,twoState,twoOrigin,twoValid,twoPivots,twoCount⟩ :=
    guardedXor_actualCaseOrigins rename current context _ _ _ _ _ _
      (right.afterTrace first.state first.steps first.checked)
      (left.afterTrace first.state first.steps first.checked)
      nextFlags.backward nextFlags.forward nextAbsent.backward nextAbsent.forward firstSupport.1
      (SourceEqualSchedule.XorRowsOriginalSupport.afterTrace rename start right
        first.state first.steps first.checked rightOrigin)
      (SourceEqualSchedule.XorRowsOriginalSupport.afterTrace rename start left
        first.state first.steps first.checked leftOrigin)
      nextFlagOrigin.2 nextFlagOrigin.1 nextAbsentOrigin.2 nextAbsentOrigin.1
  have actualSteps :
      (SourceBusAdvance.laterMaskPairFromStages rename context position channel start flags absent).steps =
        first.steps ++ second.steps := rfl
  have actualState :
      (SourceBusAdvance.laterMaskPairFromStages rename context position channel start flags absent).state =
        second.state := rfl
  refine ⟨sourceOne,treeOne,branchOne,sourceTwo,treeTwo,branchTwo,
    actualSteps.trans (congrArg₂ List.append oneSteps twoSteps),
    actualState.trans twoState,onePrefix,?_,oneOrigin,twoOrigin,oneValid,twoValid,
    onePivots,twoPivots,oneCount,twoCount⟩
  calc
    sourceTwo.steps = current.steps ++ branchTwo := twoPrefix
    _ = (start.steps ++ first.steps) ++ branchTwo := rfl
    _ = (start.steps ++
        (branchOne ++ (Controller.Resolution.Cases.compileTree sourceOne.state treeOne).steps)) ++ branchTwo :=
      congrArg (fun steps => (start.steps ++ steps) ++ branchTwo) oneSteps



def nativeHealthyFirstFlag (rename : Nat → Fin v) : Literal (Fin v) :=
  mapLiteral rename (sourceRoleMap parameters (.internal (.flag .healthy parameters.firstBus)))

def nativeFaultyFirstFlag (rename : Nat → Fin v) : Literal (Fin v) :=
  mapLiteral rename (sourceRoleMap parameters (.internal (.flag .faulty parameters.firstBus)))

def nativeOutputContext (rename : Nat → Fin v) : Clause (Fin v) :=
  [negate (nativeHealthyFirstFlag (parameters := parameters) rename)] ++
    compiledQualifierOutputs (parameters := parameters) rename

def outputDischargeTree {state : State v} {context activationTarget : Clause (Fin v)}
    {input output : Literal (Fin v)} (pivot : Literal (Fin v))
    (transfer : GuardedTransfer state context input output)
    (activation : AvailableSubclause state activationTarget) :
    Option (Controller.Resolution.Cases.CaseTree v) :=
  match transfer with
  | .identity _ => none
  | .derived row =>
    some (.fork pivot (SourceStageXor.rowLeaf row) (SourceStageXor.rowLeaf activation))

def nativeOutputDischargeTree (rename : Nat → Fin v)
    (drive : parameters.drive = true) (index : Fin parameters.decoder.roots.length)
    (reverse : Bool) : Option (Controller.Resolution.Cases.CaseTree v) :=
  let pair := nativeCofactorRoot rename drive true index
  if reverse then
    outputDischargeTree (nativeFaultyFirstFlag (parameters := parameters) rename)
      pair.backward (nativeCofactorMixed rename drive)
  else
    outputDischargeTree (nativeFaultyFirstFlag (parameters := parameters) rename)
      pair.forward (nativeCofactorMixed rename drive)

/- The runtime tree keeps actual stored clauses unchanged. Its branch target
   validity is proved by monotonicity of ClauseSubset, directly for the two
   actual leaves; no weakening row is added. Direction is selected as actual
   forward/backward data. Identity emits no macro because target contains a
   complementary pair. -/


theorem outputDischargeTree_valid (state : State v) (healthy faulty input output : Literal (Fin v))
    (qualifiers : Clause (Fin v))
    (transfer : GuardedTransfer state [negate healthy, negate faulty] input output)
    (activation : AvailableSubclause state ([negate healthy, faulty] ++ qualifiers))
    (tree : Controller.Resolution.Cases.CaseTree v)
    (emitted : outputDischargeTree faulty transfer activation = some tree) :
    Controller.Resolution.Cases.ValidTree state
      (([negate healthy] ++ qualifiers) ++ [negate input, output]) tree := by
  cases transfer with
  | identity same => simp [outputDischargeTree] at emitted
  | derived row =>
    cases Option.some.inj emitted
    refine ⟨?_, ?_⟩
    · exact SourceStageXor.rowLeaf_valid (retarget row (by
        intro literal member
        simp only [List.mem_append, List.mem_cons, List.mem_singleton] at member ⊢
        aesop))
    · exact SourceStageXor.rowLeaf_valid (retarget activation (by
        intro literal member
        simp only [List.mem_append, List.mem_cons, List.mem_singleton] at member ⊢
        aesop))

theorem outputDischargeTree_budget {state : State v} {context activationTarget : Clause (Fin v)}
    {input output : Literal (Fin v)} (transfer : GuardedTransfer state context input output)
    (activation : AvailableSubclause state activationTarget) (faulty : Literal (Fin v))
    (tree : Controller.Resolution.Cases.CaseTree v)
    (emitted : outputDischargeTree faulty transfer activation = some tree) :
    Controller.Resolution.Cases.inferenceBudget tree = 1 ∧
      splitVariables tree = {faulty.1} := by
  cases transfer with
  | identity same => simp [outputDischargeTree] at emitted
  | derived row =>
    cases Option.some.inj emitted
    simp [SourceStageXor.rowLeaf, Controller.Resolution.Cases.inferenceBudget, splitVariables]

theorem outputDischargeTree_originals (rename : Nat → Fin v)
    (start : SourcePrefix (parameters := parameters) rename)
    (transfer : GuardedTransfer start.state context input output)
    (activation : AvailableSubclause start.state activationTarget)
    (transferOriginal : SourceDecoderSchedule.GuardedTransferOrigin rename start transfer)
    (activationOriginal : SourceMismatchHandles.ResultOrigin (formula parameters).clauses.size
      (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
      start.steps activation.row.id)
    (faulty : Literal (Fin v)) (tree : Controller.Resolution.Cases.CaseTree v)
    (emitted : outputDischargeTree faulty transfer activation = some tree) :
    CaseTreeOriginals rename start tree := by
  cases transfer with
  | identity same => simp [outputDischargeTree] at emitted
  | derived row =>
    cases Option.some.inj emitted
    exact ⟨⟨transferOriginal, fun reason member => False.elim (List.not_mem_nil member)⟩,
      ⟨activationOriginal, fun reason member => False.elim (List.not_mem_nil member)⟩⟩


def nativeRootLiteral (rename : Nat → Fin v) (side : Side)
    (index : Fin parameters.decoder.roots.length) : Literal (Fin v) :=
  mapLiteral rename (sourceRoleMap parameters
    (.internal (.decoder side parameters.decoder.roots[index.val])))

def nativeOutputTarget (rename : Nat → Fin v)
    (index : Fin parameters.decoder.roots.length) (reverse : Bool) : Clause (Fin v) :=
  nativeOutputContext (parameters := parameters) rename ++
    if reverse then [negate (nativeRootLiteral rename .faulty index), nativeRootLiteral rename .healthy index]
    else [negate (nativeRootLiteral rename .healthy index), nativeRootLiteral rename .faulty index]

theorem nativeOutputDischargeTree_valid (rename : Nat → Fin v)
    (drive : parameters.drive = true) (index : Fin parameters.decoder.roots.length)
    (reverse : Bool) (tree : Controller.Resolution.Cases.CaseTree v)
    (emitted : nativeOutputDischargeTree rename drive index reverse = some tree) :
    Controller.Resolution.Cases.ValidTree (nativeCofactorPrefix rename drive).state
      (nativeOutputTarget rename index reverse) tree := by
  cases reverse with
  | false =>
    exact outputDischargeTree_valid (nativeCofactorPrefix rename drive).state
      (nativeHealthyFirstFlag (parameters := parameters) rename) (nativeFaultyFirstFlag (parameters := parameters) rename) _ _
      (compiledQualifierOutputs (parameters := parameters) rename) (nativeCofactorRoot rename drive true index).forward
      (nativeCofactorMixed rename drive) tree emitted
  | true =>
    exact outputDischargeTree_valid (nativeCofactorPrefix rename drive).state
      (nativeHealthyFirstFlag (parameters := parameters) rename) (nativeFaultyFirstFlag (parameters := parameters) rename) _ _
      (compiledQualifierOutputs (parameters := parameters) rename) (nativeCofactorRoot rename drive true index).backward
      (nativeCofactorMixed rename drive) tree emitted

theorem nativeOutputDischargeTree_originals (rename : Nat → Fin v)
    (drive : parameters.drive = true) (index : Fin parameters.decoder.roots.length)
    (reverse : Bool) (tree : Controller.Resolution.Cases.CaseTree v)
    (emitted : nativeOutputDischargeTree rename drive index reverse = some tree) :
    CaseTreeOriginals rename (nativeCofactorPrefix rename drive) tree := by
  cases reverse with
  | false =>
    exact outputDischargeTree_originals rename (nativeCofactorPrefix rename drive)
      (nativeCofactorRoot rename drive true index).forward (nativeCofactorMixed rename drive)
      (nativeCofactorRoot_supported rename drive true index).1
      (nativeCofactorMixed_supported rename drive) (nativeFaultyFirstFlag (parameters := parameters) rename) tree emitted
  | true =>
    exact outputDischargeTree_originals rename (nativeCofactorPrefix rename drive)
      (nativeCofactorRoot rename drive true index).backward (nativeCofactorMixed rename drive)
      (nativeCofactorRoot_supported rename drive true index).2
      (nativeCofactorMixed_supported rename drive) (nativeFaultyFirstFlag (parameters := parameters) rename) tree emitted

theorem nativeOutputDischargeTree_budget (rename : Nat → Fin v)
    (drive : parameters.drive = true) (index : Fin parameters.decoder.roots.length)
    (reverse : Bool) (tree : Controller.Resolution.Cases.CaseTree v)
    (emitted : nativeOutputDischargeTree rename drive index reverse = some tree) :
    Controller.Resolution.Cases.inferenceBudget tree = 1 ∧
      splitVariables tree = {(nativeFaultyFirstFlag (parameters := parameters) rename).1} := by
  cases reverse with
  | false =>
    exact outputDischargeTree_budget (nativeCofactorRoot rename drive true index).forward
      (nativeCofactorMixed rename drive) (nativeFaultyFirstFlag (parameters := parameters) rename) tree emitted
  | true =>
    exact outputDischargeTree_budget (nativeCofactorRoot rename drive true index).backward
      (nativeCofactorMixed rename drive) (nativeFaultyFirstFlag (parameters := parameters) rename) tree emitted

theorem nativeOutputDischargeTree_run (rename : Nat → Fin v)
    (drive : parameters.drive = true) (index : Fin parameters.decoder.roots.length)
    (reverse : Bool) (tree : Controller.Resolution.Cases.CaseTree v)
    (emitted : nativeOutputDischargeTree rename drive index reverse = some tree) :
    runSteps (nativeCofactorPrefix rename drive).state
      (Controller.Resolution.Cases.compileTree (nativeCofactorPrefix rename drive).state tree).steps =
      some (Controller.Resolution.Cases.compileTree (nativeCofactorPrefix rename drive).state tree).state ∧
    (Controller.Resolution.Cases.compileTree (nativeCofactorPrefix rename drive).state tree).state.rows
      (Controller.Resolution.Cases.compileTree (nativeCofactorPrefix rename drive).state tree).rowId =
      some (Controller.Resolution.Cases.compileTree (nativeCofactorPrefix rename drive).state tree).clause ∧
    (Controller.Resolution.Cases.compileTree (nativeCofactorPrefix rename drive).state tree).rowId ≤
      (Controller.Resolution.Cases.compileTree (nativeCofactorPrefix rename drive).state tree).state.lastId ∧
    ClauseSubset (Controller.Resolution.Cases.compileTree (nativeCofactorPrefix rename drive).state tree).clause
      (nativeOutputTarget rename index reverse) :=
  Controller.Resolution.Cases.compileTree_run tree _ _ (Nat.le_refl _) (fun _ _ => rfl) _
    (nativeOutputDischargeTree_valid rename drive index reverse tree emitted)


theorem outputDischargeTree_identity {state : State v} {context activationTarget : Clause (Fin v)}
    {input output : Literal (Fin v)} (pivot : Literal (Fin v)) (same : input = output)
    (activation : AvailableSubclause state activationTarget) :
    outputDischargeTree pivot (GuardedTransfer.identity same : GuardedTransfer state context input output)
      activation = none := rfl

theorem identity_output_tautological (context : Clause (Fin v))
    (input output : Literal (Fin v)) (same : input = output) :
    ∃ literal ∈ context ++ [negate input, output],
      negate literal ∈ context ++ [negate input, output] := by
  subst output
  exact ⟨input, by simp, by simp⟩



def outputDischargeProjection (state : State v)
    (healthy faulty input output : Literal (Fin v)) (qualifiers : Clause (Fin v))
    (transfer : GuardedTransfer state [negate healthy, negate faulty] input output)
    (activation : AvailableSubclause state ([negate healthy, faulty] ++ qualifiers)) :
    SourceStagePolarity.GuardedProjection state ([negate healthy] ++ qualifiers) input output 1 := by
  cases transfer with
  | identity same =>
    exact ⟨state, [], rfl, .identity same, Nat.zero_le _⟩
  | derived row =>
    let tree : Controller.Resolution.Cases.CaseTree v :=
      .fork faulty (SourceStageXor.rowLeaf row) (SourceStageXor.rowLeaf activation)
    let compiled := Controller.Resolution.Cases.compileTree state tree
    have emitted : outputDischargeTree faulty
        (GuardedTransfer.derived row) activation = some tree := rfl
    have valid := outputDischargeTree_valid state healthy faulty input output qualifiers
      (.derived row) activation tree emitted
    have run := Controller.Resolution.Cases.compileTree_run tree state state
      (Nat.le_refl _) (fun _ _ => rfl) _ valid
    have budget := (outputDischargeTree_budget (.derived row) activation faulty tree emitted).1
    refine ⟨compiled.state, compiled.steps, run.1,
      .derived ⟨compiled.clause, ⟨compiled.rowId, run.2.1, run.2.2.1⟩, run.2.2.2⟩, ?_⟩
    exact (Controller.Resolution.Cases.compileTree_count_le tree state).trans budget.le



def pairedOutputDischarge (state : State v) (healthy faulty left right : Literal (Fin v))
    (qualifiers : Clause (Fin v))
    (pair : DirectionPair state [negate healthy, negate faulty] left right)
    (activation : AvailableSubclause state ([negate healthy, faulty] ++ qualifiers)) :
    PairedProjection state ([negate healthy] ++ qualifiers) left right 2 := by
  let first := outputDischargeProjection state healthy faulty left right qualifiers pair.forward activation
  let reverse := pair.backward.afterTrace first.state first.steps first.checked
  let nextActivation := FoldProjection.afterTrace activation first.state first.steps first.checked
  let second := outputDischargeProjection first.state healthy faulty right left qualifiers
    reverse nextActivation
  refine ⟨second.state, first.steps ++ second.steps, ?_,
    ⟨first.result.afterTrace second.state second.steps second.checked, second.result⟩, ?_⟩
  · rw [runSteps_append, first.checked]
    exact second.checked
  · have one := first.count
    have two := second.count
    simp only [List.length_append]
    omega



theorem outputDischargeTree_supported (rename : Nat → Fin v)
    (start : SourcePrefix (parameters := parameters) rename)
    (transfer : GuardedTransfer start.state context input output)
    (activation : AvailableSubclause start.state activationTarget)
    (supported : SourceDecoderSchedule.PrefixOriginalSupport rename start)
    (transferOriginal : SourceDecoderSchedule.GuardedTransferOrigin rename start transfer)
    (activationOriginal : SourceMismatchHandles.ResultOrigin (formula parameters).clauses.size
      (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
      start.steps activation.row.id)
    (faulty : Literal (Fin v)) (tree : Controller.Resolution.Cases.CaseTree v)
    (emitted : outputDischargeTree faulty transfer activation = some tree) :
    SourceBusSchedule.TraceOriginalSupport (formula parameters).clauses.size
      (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
      (start.steps ++ (Controller.Resolution.Cases.compileTree start.state tree).steps) ∧
    SourceMismatchHandles.ResultOrigin (formula parameters).clauses.size
      (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
      (start.steps ++ (Controller.Resolution.Cases.compileTree start.state tree).steps)
      (Controller.Resolution.Cases.compileTree start.state tree).rowId := by
  cases transfer with
  | identity same => simp [outputDischargeTree] at emitted
  | derived row =>
    cases Option.some.inj emitted
    have parents := Controller.NativeProof.SourceFoldAggregateProvenance.appendMerge_origins_supported
      (formula parameters).clauses.size
      (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
      start.steps start.state row.row.id activation.row.id faulty row.clause activation.clause
      supported (SourceDecoderSchedule.allowed_native_count_le rename)
      transferOriginal activationOriginal row.row.bound activation.row.bound
    have result := Controller.NativeProof.SourceFoldAggregateProvenance.merge_origins
      (formula parameters).clauses.size
      (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
      start.steps start.state row.row.id activation.row.id faulty row.clause activation.clause
      transferOriginal activationOriginal (SourceMixedSchedule.prefix_native_count_le rename start)
    simpa only [Controller.Resolution.Cases.compileTree, SourceStageXor.rowLeaf,
      Controller.Resolution.RUP.compileReasons, List.nil_append] using And.intro parents result



theorem outputDischargeProjection_supported (rename : Nat → Fin v)
    (start : SourcePrefix (parameters := parameters) rename)
    (healthy faulty input output : Literal (Fin v)) (qualifiers : Clause (Fin v))
    (transfer : GuardedTransfer start.state [negate healthy, negate faulty] input output)
    (activation : AvailableSubclause start.state ([negate healthy, faulty] ++ qualifiers))
    (supported : SourceDecoderSchedule.PrefixOriginalSupport rename start)
    (transferOriginal : SourceDecoderSchedule.GuardedTransferOrigin rename start transfer)
    (activationOriginal : SourceMismatchHandles.ResultOrigin (formula parameters).clauses.size
      (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
      start.steps activation.row.id) :
    let actual := outputDischargeProjection start.state healthy faulty input output qualifiers transfer activation
    SourceDecoderSchedule.PrefixOriginalSupport rename
      (start.extend actual.state actual.steps actual.checked) ∧
    SourceDecoderSchedule.GuardedTransferOrigin rename
      (start.extend actual.state actual.steps actual.checked) actual.result := by
  cases transfer with
  | identity same =>
    exact ⟨by simpa only [outputDischargeProjection, SourceDecoderSchedule.PrefixOriginalSupport,
      SourcePrefix.extend, List.append_nil] using supported, trivial⟩
  | derived row =>
    let tree : Controller.Resolution.Cases.CaseTree v :=
      .fork faulty (SourceStageXor.rowLeaf row) (SourceStageXor.rowLeaf activation)
    have actual := outputDischargeTree_supported rename start (.derived row) activation
      supported transferOriginal activationOriginal faulty tree rfl
    simpa only [outputDischargeProjection, SourceDecoderSchedule.PrefixOriginalSupport,
      SourceDecoderSchedule.GuardedTransferOrigin, SourcePrefix.extend, tree] using actual



structure NativeOutputAccumulator (rename : Nat → Fin v) (drive : parameters.drive = true)
    (count : Nat) where
  state : State v
  steps : List (Step v)
  checked : runSteps (nativeCofactorPrefix rename drive).state steps = some state
  pairs : ∀ index : Fin parameters.decoder.roots.length, index.val < count →
    DirectionPair state (nativeOutputContext (parameters := parameters) rename)
      (nativeRootLiteral rename .healthy index) (nativeRootLiteral rename .faulty index)

def NativeOutputAccumulator.prefix (program : NativeOutputAccumulator (parameters := parameters)
    rename drive count) : SourcePrefix (parameters := parameters) rename :=
  (nativeCofactorPrefix rename drive).extend program.state program.steps program.checked

def nativeOutputInitial (rename : Nat → Fin v) (drive : parameters.drive = true) :
    NativeOutputAccumulator (parameters := parameters) rename drive 0 :=
  ⟨(nativeCofactorPrefix rename drive).state, [], rfl,
    fun index impossible => False.elim (Nat.not_lt_zero index.val impossible)⟩

def nativeOutputPairAt (rename : Nat → Fin v) (drive : parameters.drive = true)
    (prior : NativeOutputAccumulator (parameters := parameters) rename drive count)
    (index : Fin parameters.decoder.roots.length) :
    PairedProjection prior.state (nativeOutputContext (parameters := parameters) rename)
      (nativeRootLiteral rename .healthy index) (nativeRootLiteral rename .faulty index) 2 :=
  let rootPair := (nativeCofactorRoot rename drive true index).afterTrace
    prior.state prior.steps prior.checked
  let activation := FoldProjection.afterTrace (nativeCofactorMixed rename drive)
    prior.state prior.steps prior.checked
  pairedOutputDischarge prior.state
    (nativeHealthyFirstFlag (parameters := parameters) rename)
    (nativeFaultyFirstFlag (parameters := parameters) rename) _ _
    (compiledQualifierOutputs (parameters := parameters) rename) rootPair activation



def nativeOutputAdvance (rename : Nat → Fin v) (drive : parameters.drive = true)
    (count : Nat) (before : count < parameters.decoder.roots.length)
    (prior : NativeOutputAccumulator (parameters := parameters) rename drive count) :
    NativeOutputAccumulator (parameters := parameters) rename drive (count + 1) := by
  let selected : Fin parameters.decoder.roots.length := ⟨count, before⟩
  let added := nativeOutputPairAt rename drive prior selected
  refine ⟨added.state, prior.steps ++ added.steps, ?_, ?_⟩
  · rw [runSteps_append, prior.checked]
    exact added.checked
  · intro query below
    by_cases same : query = selected
    · subst query
      exact added.pair
    · have earlier : query.val < count := by
        have different : query.val ≠ count := by
          intro equal
          apply same
          apply Fin.ext
          exact equal
        omega
      exact (prior.pairs query earlier).afterTrace added.state added.steps added.checked

def buildNativeOutputs (rename : Nat → Fin v) (drive : parameters.drive = true) :
    (count : Nat) → count ≤ parameters.decoder.roots.length →
      NativeOutputAccumulator (parameters := parameters) rename drive count
  | 0, _ => nativeOutputInitial rename drive
  | count + 1, bound => nativeOutputAdvance rename drive count (by omega)
      (buildNativeOutputs rename drive count (by omega))

theorem buildNativeOutputs_count (rename : Nat → Fin v) (drive : parameters.drive = true)
    (count : Nat) (bound : count ≤ parameters.decoder.roots.length) :
    (buildNativeOutputs rename drive count bound).steps.length ≤ 2 * count := by
  induction count with
  | zero => exact Nat.le_refl _
  | succ count ih =>
    have prior := ih (by omega)
    have added := (nativeOutputPairAt rename drive
      (buildNativeOutputs rename drive count (by omega)) ⟨count, by omega⟩).count
    change ((buildNativeOutputs rename drive count (by omega)).steps ++
      (nativeOutputPairAt rename drive
        (buildNativeOutputs rename drive count (by omega)) ⟨count, by omega⟩).steps).length ≤ 2 * (count + 1)
    simp only [List.length_append, Nat.mul_add, Nat.mul_one]
    omega



def nativeOutputProgram (rename : Nat → Fin v) (drive : parameters.drive = true) :=
  buildNativeOutputs rename drive parameters.decoder.roots.length (Nat.le_refl _)

def nativeOutputPrefix (rename : Nat → Fin v) (drive : parameters.drive = true) :
    SourcePrefix (parameters := parameters) rename :=
  (nativeOutputProgram rename drive).prefix

def nativeOutputRoot (rename : Nat → Fin v) (drive : parameters.drive = true)
    (index : Fin parameters.decoder.roots.length) :
    DirectionPair (nativeOutputProgram rename drive).state
      (nativeOutputContext (parameters := parameters) rename)
      (nativeRootLiteral rename .healthy index) (nativeRootLiteral rename .faulty index) :=
  (nativeOutputProgram rename drive).pairs index index.isLt

theorem nativeOutputProgram_checked (rename : Nat → Fin v) (drive : parameters.drive = true) :
    runSteps (nativeCofactorPrefix rename drive).state (nativeOutputProgram rename drive).steps =
      some (nativeOutputProgram rename drive).state :=
  (nativeOutputProgram rename drive).checked

theorem nativeOutputProgram_count (rename : Nat → Fin v) (drive : parameters.drive = true) :
    (nativeOutputProgram rename drive).steps.length ≤ 2 * parameters.decoder.roots.length :=
  buildNativeOutputs_count rename drive parameters.decoder.roots.length (Nat.le_refl _)



theorem pairedOutputDischarge_supported (rename : Nat → Fin v)
    (start : SourcePrefix (parameters := parameters) rename)
    (healthy faulty left right : Literal (Fin v)) (qualifiers : Clause (Fin v))
    (pair : DirectionPair start.state [negate healthy, negate faulty] left right)
    (activation : AvailableSubclause start.state ([negate healthy, faulty] ++ qualifiers))
    (supported : SourceDecoderSchedule.PrefixOriginalSupport rename start)
    (pairOriginal : SourceDecoderSchedule.DirectionPairOrigin rename start pair)
    (activationOriginal : SourceMismatchHandles.ResultOrigin (formula parameters).clauses.size
      (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
      start.steps activation.row.id) :
    let actual := pairedOutputDischarge start.state healthy faulty left right qualifiers pair activation
    SourceDecoderSchedule.PrefixOriginalSupport rename
      (start.extend actual.state actual.steps actual.checked) ∧
    SourceDecoderSchedule.DirectionPairOrigin rename
      (start.extend actual.state actual.steps actual.checked) actual.pair := by
  let first := outputDischargeProjection start.state healthy faulty left right qualifiers pair.forward activation
  have firstSupport := outputDischargeProjection_supported rename start healthy faulty left right qualifiers
    pair.forward activation supported pairOriginal.1 activationOriginal
  let current := start.extend first.state first.steps first.checked
  let reverse := pair.backward.afterTrace first.state first.steps first.checked
  let nextActivation := FoldProjection.afterTrace activation first.state first.steps first.checked
  have reverseOriginal := SourceDecoderSchedule.GuardedTransferOrigin.afterTrace rename start
    pair.backward pairOriginal.2 first.state first.steps first.checked
  have nextActivationOriginal :
      SourceMismatchHandles.ResultOrigin (formula parameters).clauses.size
        (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
        current.steps nextActivation.row.id :=
    SourceFoldProvenance.resultOrigin_append_right _ _ start.steps first.steps
      activation.row.id activationOriginal
  let second := outputDischargeProjection first.state healthy faulty right left qualifiers reverse nextActivation
  have secondSupport := outputDischargeProjection_supported rename current healthy faulty right left qualifiers
    reverse nextActivation firstSupport.1 reverseOriginal nextActivationOriginal
  have forwardSupport := SourceDecoderSchedule.GuardedTransferOrigin.afterTrace rename current
    first.result firstSupport.2 second.state second.steps second.checked
  let finished := start.extend second.state (first.steps ++ second.steps) (by
    rw [runSteps_append, first.checked]
    exact second.checked)
  change SourceDecoderSchedule.PrefixOriginalSupport rename finished ∧
    SourceDecoderSchedule.DirectionPairOrigin rename finished
      ⟨first.result.afterTrace second.state second.steps second.checked, second.result⟩
  constructor
  · simpa only [SourceDecoderSchedule.PrefixOriginalSupport, finished, current,
      SourcePrefix.extend, List.append_assoc] using secondSupport.1
  · constructor
    · exact SourceDecoderSchedule.GuardedTransferOrigin.same_steps rename second.state
        ((start.steps ++ first.steps) ++ second.steps)
        (start.steps ++ (first.steps ++ second.steps)) (List.append_assoc _ _ _)
        _ _ (first.result.afterTrace second.state second.steps second.checked) forwardSupport
    · exact SourceDecoderSchedule.GuardedTransferOrigin.same_steps rename second.state
        ((start.steps ++ first.steps) ++ second.steps)
        (start.steps ++ (first.steps ++ second.steps)) (List.append_assoc _ _ _)
        _ _ second.result secondSupport.2



def nativeOutputAdvanceKernel (rename : Nat → Fin v) (drive : parameters.drive = true)
    (count : Nat) (before : count < parameters.decoder.roots.length)
    (prior : NativeOutputAccumulator (parameters := parameters) rename drive count)
    (added : PairedProjection prior.state (nativeOutputContext (parameters := parameters) rename)
      (nativeRootLiteral rename .healthy ⟨count, before⟩)
      (nativeRootLiteral rename .faulty ⟨count, before⟩) 2) :
    NativeOutputAccumulator (parameters := parameters) rename drive (count + 1) := by
  let selected : Fin parameters.decoder.roots.length := ⟨count, before⟩
  refine ⟨added.state, prior.steps ++ added.steps, ?_, ?_⟩
  · rw [runSteps_append, prior.checked]
    exact added.checked
  · intro query below
    by_cases same : query = selected
    · subst query
      exact added.pair
    · have earlier : query.val < count := by
        have different : query.val ≠ count := by
          intro equal
          apply same
          apply Fin.ext
          exact equal
        omega
      exact (prior.pairs query earlier).afterTrace added.state added.steps added.checked

theorem nativeOutputAdvance_kernel_eq (rename : Nat → Fin v) (drive : parameters.drive = true)
    (count : Nat) (before : count < parameters.decoder.roots.length)
    (prior : NativeOutputAccumulator (parameters := parameters) rename drive count) :
    nativeOutputAdvance rename drive count before prior =
      nativeOutputAdvanceKernel rename drive count before prior
        (nativeOutputPairAt rename drive prior ⟨count, before⟩) := rfl



def NativeOutputAccumulatorOriginals (rename : Nat → Fin v) (drive : parameters.drive = true)
    (count : Nat) (program : NativeOutputAccumulator (parameters := parameters) rename drive count) : Prop :=
  SourceDecoderSchedule.PrefixOriginalSupport rename program.prefix ∧
  ∀ index : Fin parameters.decoder.roots.length, ∀ before : index.val < count,
    SourceDecoderSchedule.DirectionPairOrigin rename program.prefix (program.pairs index before)

theorem nativeOutputPairAt_supported (rename : Nat → Fin v) (drive : parameters.drive = true)
    (count : Nat) (prior : NativeOutputAccumulator (parameters := parameters) rename drive count)
    (index : Fin parameters.decoder.roots.length)
    (supported : SourceDecoderSchedule.PrefixOriginalSupport rename prior.prefix) :
    let added := nativeOutputPairAt rename drive prior index
    SourceDecoderSchedule.PrefixOriginalSupport rename
      (prior.prefix.extend added.state added.steps added.checked) ∧
    SourceDecoderSchedule.DirectionPairOrigin rename
      (prior.prefix.extend added.state added.steps added.checked) added.pair := by
  let rootPair := (nativeCofactorRoot rename drive true index).afterTrace
    prior.state prior.steps prior.checked
  let activation := FoldProjection.afterTrace (nativeCofactorMixed rename drive)
    prior.state prior.steps prior.checked
  have rootOrigin := SourceDecoderSchedule.DirectionPairOrigin.afterTrace rename
    (nativeCofactorPrefix rename drive) (nativeCofactorRoot rename drive true index)
    (nativeCofactorRoot_supported rename drive true index) prior.state prior.steps prior.checked
  have activationOrigin :
      SourceMismatchHandles.ResultOrigin (formula parameters).clauses.size
        (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
        prior.prefix.steps activation.row.id :=
    SourceFoldProvenance.resultOrigin_append_right _ _ (nativeCofactorPrefix rename drive).steps
      prior.steps (nativeCofactorMixed rename drive).row.id
      (nativeCofactorMixed_supported rename drive)
  exact pairedOutputDischarge_supported rename prior.prefix
    (nativeHealthyFirstFlag (parameters := parameters) rename)
    (nativeFaultyFirstFlag (parameters := parameters) rename) _ _
    (compiledQualifierOutputs (parameters := parameters) rename)
    rootPair activation supported rootOrigin activationOrigin

theorem nativeOutputInitial_originals (rename : Nat → Fin v) (drive : parameters.drive = true) :
    NativeOutputAccumulatorOriginals rename drive 0 (nativeOutputInitial rename drive) := by
  constructor
  · simpa only [nativeOutputInitial, NativeOutputAccumulator.prefix, SourcePrefix.extend,
      SourceDecoderSchedule.PrefixOriginalSupport, List.append_nil] using
      nativeCofactorPrefix_supported rename drive
  · intro index impossible
    exact False.elim (Nat.not_lt_zero index.val impossible)



theorem nativeOutputAdvanceKernel_supported (rename : Nat → Fin v) (drive : parameters.drive = true)
    (count : Nat) (before : count < parameters.decoder.roots.length)
    (prior : NativeOutputAccumulator (parameters := parameters) rename drive count)
    (added : PairedProjection prior.state (nativeOutputContext (parameters := parameters) rename)
      (nativeRootLiteral rename .healthy ⟨count, before⟩)
      (nativeRootLiteral rename .faulty ⟨count, before⟩) 2)
    (priorOriginal : NativeOutputAccumulatorOriginals rename drive count prior)
    (addedOriginal : SourceDecoderSchedule.PrefixOriginalSupport rename
        (prior.prefix.extend added.state added.steps added.checked) ∧
      SourceDecoderSchedule.DirectionPairOrigin rename
        (prior.prefix.extend added.state added.steps added.checked) added.pair) :
    NativeOutputAccumulatorOriginals rename drive (count + 1)
      (nativeOutputAdvanceKernel rename drive count before prior added) := by
  let finished := (nativeCofactorPrefix rename drive).extend added.state
    (prior.steps ++ added.steps) (by
      rw [runSteps_append, prior.checked]
      exact added.checked)
  have stepsEqual : prior.prefix.steps ++ added.steps = finished.steps := by
    simp only [NativeOutputAccumulator.prefix, finished, SourcePrefix.extend, List.append_assoc]
  constructor
  · simpa only [SourceDecoderSchedule.PrefixOriginalSupport, nativeOutputAdvanceKernel,
      NativeOutputAccumulator.prefix, SourcePrefix.extend, List.append_assoc] using addedOriginal.1
  · intro query below
    let selected : Fin parameters.decoder.roots.length := ⟨count, before⟩
    by_cases same : query = selected
    · subst query
      have carried := decoderPairOrigin_same_steps rename added.state
        (prior.prefix.steps ++ added.steps) finished.steps stepsEqual
        (prior.prefix.extend added.state added.steps added.checked).checked finished.checked
        added.pair addedOriginal.2
      simp only [nativeOutputAdvanceKernel, NativeOutputAccumulator.prefix]
      dsimp only [SourcePrefix.extend]
      rw [dite_eq_left (show (⟨count, before⟩ : Fin parameters.decoder.roots.length) =
          ⟨count, before⟩ from rfl)]
      change SourceDecoderSchedule.DirectionPairOrigin rename finished added.pair
      exact carried
    · have earlier : query.val < count := by
        have different : query.val ≠ count := by
          intro equal
          apply same
          apply Fin.ext
          exact equal
        omega
      have origin := SourceDecoderSchedule.DirectionPairOrigin.afterTrace rename prior.prefix
        (prior.pairs query earlier) (priorOriginal.2 query earlier)
        added.state added.steps added.checked
      have carried := decoderPairOrigin_same_steps rename added.state
        (prior.prefix.steps ++ added.steps) finished.steps stepsEqual
        (prior.prefix.extend added.state added.steps added.checked).checked finished.checked
        ((prior.pairs query earlier).afterTrace added.state added.steps added.checked) origin
      simp only [nativeOutputAdvanceKernel, NativeOutputAccumulator.prefix]
      dsimp only [SourcePrefix.extend]
      rw [dite_eq_right same]
      change SourceDecoderSchedule.DirectionPairOrigin rename finished
        ((prior.pairs query earlier).afterTrace added.state added.steps added.checked)
      exact carried

theorem nativeOutputAdvance_originals (rename : Nat → Fin v) (drive : parameters.drive = true)
    (count : Nat) (before : count < parameters.decoder.roots.length)
    (prior : NativeOutputAccumulator (parameters := parameters) rename drive count)
    (original : NativeOutputAccumulatorOriginals rename drive count prior) :
    NativeOutputAccumulatorOriginals rename drive (count + 1)
      (nativeOutputAdvance rename drive count before prior) := by
  rw [nativeOutputAdvance_kernel_eq]
  exact nativeOutputAdvanceKernel_supported rename drive count before prior
    (nativeOutputPairAt rename drive prior ⟨count, before⟩) original
    (nativeOutputPairAt_supported rename drive count prior ⟨count, before⟩ original.1)

theorem buildNativeOutputs_originals (rename : Nat → Fin v) (drive : parameters.drive = true)
    (count : Nat) (bound : count ≤ parameters.decoder.roots.length) :
    NativeOutputAccumulatorOriginals rename drive count
      (buildNativeOutputs rename drive count bound) := by
  induction count with
  | zero => exact nativeOutputInitial_originals rename drive
  | succ count ih =>
    exact nativeOutputAdvance_originals rename drive count (by omega)
      (buildNativeOutputs rename drive count (by omega)) (ih (by omega))

theorem nativeOutputPrefix_supported (rename : Nat → Fin v) (drive : parameters.drive = true) :
    SourceDecoderSchedule.PrefixOriginalSupport rename (nativeOutputPrefix rename drive) :=
  (buildNativeOutputs_originals rename drive parameters.decoder.roots.length (Nat.le_refl _)).1

theorem nativeOutputRoot_supported (rename : Nat → Fin v) (drive : parameters.drive = true)
    (index : Fin parameters.decoder.roots.length) :
    SourceDecoderSchedule.DirectionPairOrigin rename (nativeOutputPrefix rename drive)
      (nativeOutputRoot rename drive index) :=
  (buildNativeOutputs_originals rename drive parameters.decoder.roots.length (Nat.le_refl _)).2 index index.isLt



theorem nativeOutputPrefix_checked (rename : Nat → Fin v) (drive : parameters.drive = true) :
    runSteps (initialState (relabel rename (formula parameters)))
      (nativeOutputPrefix rename drive).steps = some (nativeOutputPrefix rename drive).state :=
  (nativeOutputPrefix rename drive).checked

theorem nativeOutputPrefix_countedSize (rename : Nat → Fin v) (drive : parameters.drive = true) :
    (nativeOutputPrefix rename drive).steps.length ≤
      nativeSelectorSizeBudget parameters.decoder.countedSize parameters.buses +
        2 * parameters.decoder.roots.length := by
  have prior := nativeCofactorPrefix_countedSize rename drive
  have added := nativeOutputProgram_count rename drive
  change ((nativeCofactorPrefix rename drive).steps ++ (nativeOutputProgram rename drive).steps).length ≤ _
  simp only [List.length_append]
  omega



theorem resolutionRupSchedule_targets (state : State v)
    (steps : List (Step v)) (records : List (ResolutionRupInvocation v))
    (run : resolutionRupSchedule state steps = some records) :
    ∀ record ∈ records, record.target = record.step.clause := by
  induction steps generalizing state records with
  | nil =>
    have same : [] = records := Option.some.inj run
    subst records
    intro record member
    exact False.elim (List.not_mem_nil member)
  | cons step steps ih =>
    cases leftRow : state.rows step.left with
    | none =>
      simp only [resolutionRupSchedule, leftRow, Option.bind_none] at run
      cases run
    | some left =>
      cases rightRow : state.rows step.right with
      | none =>
        simp only [resolutionRupSchedule, leftRow, rightRow, Option.bind_some, Option.bind_none] at run
        cases run
      | some right =>
        cases applied : applyStep state step with
        | none =>
          simp only [resolutionRupSchedule, leftRow, rightRow, applied, Option.bind_some, Option.bind_none] at run
          cases run
        | some middle =>
          cases tailRun : resolutionRupSchedule middle steps with
          | none =>
            simp only [resolutionRupSchedule, leftRow, rightRow, applied, tailRun,
              Option.bind_some, Option.bind_none] at run
            cases run
          | some tail =>
            let head : ResolutionRupInvocation v :=
              ⟨state, step, step.clause, resolutionRupTree step.pivot left right step.left step.right⟩
            have same : head :: tail = records := Option.some.inj (by
              simpa only [resolutionRupSchedule, leftRow, rightRow, applied, tailRun,
                Option.bind_some] using run)
            subst records
            intro record member
            rcases List.mem_cons.mp member with same | member
            · subst record
              rfl
            · exact ih middle tail tailRun record member



theorem nativeOutputPrefix_resolutionRupCertificate (rename : Nat → Fin v)
    (drive : parameters.drive = true) :
    ∃ records,
      resolutionRupSchedule (initialState (relabel rename (formula parameters)))
        (nativeOutputPrefix rename drive).steps = some records ∧
      records.map ResolutionRupInvocation.step = (nativeOutputPrefix rename drive).steps ∧
      records.length ≤ nativeSelectorSizeBudget parameters.decoder.countedSize parameters.buses +
        2 * parameters.decoder.roots.length ∧
      ∀ record ∈ records,
        Controller.Resolution.Cases.ValidTree record.base record.step.clause record.tree ∧
        splitVariables record.tree = ∅ ∧
        Controller.Resolution.Cases.inferenceBudget record.tree = 1 ∧
        ∀ parent ∈ treeParentIds record.tree,
          (parent ≤ (formula parameters).clauses.size →
            SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename parent) ∧
          ((formula parameters).clauses.size < parent →
            ∃ earlier ∈ (nativeOutputPrefix rename drive).steps,
              earlier.id = parent ∧ earlier.id < record.step.id) := by
  obtain ⟨records, run, count, sound⟩ :=
    SourcePrefix.resolutionRupSchedule_sound rename (nativeOutputPrefix rename drive)
  have exactSteps := (resolutionRupSchedule_steps _ _ records run).1
  have exactTargets := resolutionRupSchedule_targets _ _ records run
  have parents := resolutionRupSchedule_parentSupport _ _
    (initialState (relabel rename (formula parameters)))
    (nativeOutputPrefix rename drive).steps records run (nativeOutputPrefix_supported rename drive)
  refine ⟨records, run, exactSteps,
    count.le.trans (nativeOutputPrefix_countedSize rename drive), ?_⟩
  intro record member
  have valid : Controller.Resolution.Cases.ValidTree record.base record.step.clause record.tree := by
    rw [← exactTargets record member]
    exact (sound record member).1
  exact ⟨valid, (sound record member).2.1, (sound record member).2.2, parents record member⟩



def nativeOutputMacroBudget (n b : Nat) : Nat := nativeSelectorSizeBudget n b + 2 * n

theorem nativeOutputPrefix_macro_count (rename : Nat → Fin v) (drive : parameters.drive = true) :
    (nativeOutputPrefix rename drive).steps.length ≤
      nativeOutputMacroBudget parameters.decoder.countedSize parameters.buses := by
  have roots : parameters.decoder.roots.length ≤ parameters.decoder.countedSize := by
    rw [Decoder.DAG.countedSize_eq]
    omega
  exact (nativeOutputPrefix_countedSize rename drive).trans
    (Nat.add_le_add_left (Nat.mul_le_mul_left 2 roots) _)

theorem nativeOutputPrefix_localCaseCatalogue (rename : Nat → Fin v)
    (drive : parameters.drive = true) :
    ∃ records,
      resolutionRupSchedule (initialState (relabel rename (formula parameters)))
        (nativeOutputPrefix rename drive).steps = some records ∧
      records.map ResolutionRupInvocation.step = (nativeOutputPrefix rename drive).steps ∧
      records.length ≤ nativeOutputMacroBudget parameters.decoder.countedSize parameters.buses ∧
      ∀ record ∈ records,
        Controller.Resolution.Cases.ValidTree record.base record.step.clause record.tree ∧
        (splitVariables record.tree).card ≤ 5 ∧
        ∀ parent ∈ treeParentIds record.tree,
          (parent ≤ (formula parameters).clauses.size →
            SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename parent) ∧
          ((formula parameters).clauses.size < parent →
            ∃ earlier ∈ (nativeOutputPrefix rename drive).steps,
              earlier.id = parent ∧ earlier.id < record.step.id) := by
  obtain ⟨records, run, exactSteps, count, certified⟩ :=
    nativeOutputPrefix_resolutionRupCertificate rename drive
  have sameLength : records.length = (nativeOutputPrefix rename drive).steps.length := by
    have same := congrArg List.length exactSteps
    simpa only [List.length_map] using same
  refine ⟨records, run, exactSteps, sameLength.le.trans (nativeOutputPrefix_macro_count rename drive), ?_⟩
  intro record member
  have evidence := certified record member
  refine ⟨evidence.1, ?_, evidence.2.2.2⟩
  rw [evidence.2.1]
  simp


/-- Eliminate an actual asserted healthy flag from a stored stronger directional row. -/
def physicalGuardDischarge (state : State v) (healthy input output : Literal (Fin v))
    (qualifiers : Clause (Fin v)) (unit : AvailableSubclause state [healthy])
    (transfer : GuardedTransfer state ([negate healthy] ++ qualifiers) input output) :
    SourceStagePolarity.GuardedProjection state qualifiers input output 1 := by
  cases transfer with
  | identity same => exact ⟨state, [], rfl, .identity same, Nat.zero_le _⟩
  | derived row =>
    let left : AvailableSubclause state [negate (negate healthy)] :=
      retarget unit (by
        intro literal member
        simpa only [negate_negate] using member)
    let right : AvailableSubclause state
        (negate healthy :: (qualifiers ++ [negate input, output])) :=
      retarget row (by
        intro literal member
        simpa only [List.singleton_append, List.cons_append, List.nil_append] using member)
    let joined := longMerge state (negate healthy) [] (qualifiers ++ [negate input, output]) left right
    refine ⟨joined.state, joined.steps, longMerge_run _ _ _ _ _ _, .derived ?_,
      longMerge_count _ _ _ _ _ _⟩
    simpa only [List.nil_append] using
      longMerge_result state (negate healthy) [] (qualifiers ++ [negate input, output]) left right

def pairedPhysicalGuardDischarge (state : State v) (healthy left right : Literal (Fin v))
    (qualifiers : Clause (Fin v)) (unit : AvailableSubclause state [healthy])
    (pair : DirectionPair state ([negate healthy] ++ qualifiers) left right) :
    PairedProjection state qualifiers left right 2 := by
  let first := physicalGuardDischarge state healthy left right qualifiers unit pair.forward
  let second := physicalGuardDischarge first.state healthy right left qualifiers
    (FoldProjection.afterTrace unit first.state first.steps first.checked)
    (pair.backward.afterTrace first.state first.steps first.checked)
  refine ⟨second.state, first.steps ++ second.steps, ?_,
    ⟨first.result.afterTrace second.state second.steps second.checked, second.result⟩, ?_⟩
  · rw [runSteps_append, first.checked]
    exact second.checked
  · have one := first.count
    have two := second.count
    simp only [List.length_append]
    omega

def healthyPhysicalSource (rename : Nat → Fin v) (drive : parameters.drive = true) :
    SourcePrefix (parameters := parameters) rename :=
  (SourcePrefix.initial (parameters := parameters) rename).extend
    (SourceMismatchHandles.healthyFlagUnit rename drive).state
    (SourceMismatchHandles.healthyFlagUnit rename drive).steps
    (SourceMismatchHandles.healthyFlagUnit rename drive).checked

theorem healthyPhysicalSource_supported (rename : Nat → Fin v) (drive : parameters.drive = true) :
    SourceDecoderSchedule.PrefixOriginalSupport rename (healthyPhysicalSource rename drive) := by
  have actual := SourceMismatchHandles.healthyPhysical_trace_supported rename drive
  intro step member parent parentMember
  have contained : step ∈ (SourceMismatchHandles.healthyFlagFromPhysicalUnit rename drive).steps := by
    simpa only [healthyPhysicalSource, SourcePrefix.extend, SourcePrefix.initial,
      SourceMismatchHandles.healthyFlagUnit, List.nil_append] using member
  have source := actual step contained parent parentMember
  refine ⟨fun bound => SourceDecoderSchedule.controller_original_allowed rename parent (source.1 ?_), ?_⟩
  · simpa only [initialState, relabel, Controller.CNF.OrderedFormula.relabel, Array.size_map] using bound
  · intro high
    have high' : (initialState (relabel rename (formula parameters))).lastId < parent := by
      simpa only [initialState, relabel, Controller.CNF.OrderedFormula.relabel, Array.size_map] using high
    obtain ⟨earlier, mem, same, before⟩ := source.2 high'
    refine ⟨earlier, ?_, same, before⟩
    simpa only [healthyPhysicalSource, SourcePrefix.extend, SourcePrefix.initial,
      SourceMismatchHandles.healthyFlagUnit, List.nil_append] using mem

def nativeHealthyUnitReplay (rename : Nat → Fin v) (drive : parameters.drive = true) :
    NativeReplay (parameters := parameters) rename (nativeOutputPrefix rename drive)
      (healthyPhysicalSource rename drive).state (healthyPhysicalSource rename drive).steps :=
  replayNativeProgram rename (nativeOutputPrefix rename drive)
    (healthyPhysicalSource rename drive).state (healthyPhysicalSource rename drive).steps
    (healthyPhysicalSource rename drive).checked

def nativeHealthyPhysicalPrefix (rename : Nat → Fin v) (drive : parameters.drive = true) :
    SourcePrefix (parameters := parameters) rename :=
  (nativeHealthyUnitReplay rename drive).prefix

def nativeHealthyPhysicalUnit (rename : Nat → Fin v) (drive : parameters.drive = true) :
    AvailableSubclause (nativeHealthyPhysicalPrefix rename drive).state
      [nativeHealthyFirstFlag (parameters := parameters) rename] :=
  let source := SourceMismatchHandles.healthyFlagUnit rename drive
  ⟨source.result.clause, (nativeHealthyUnitReplay rename drive).available source.result.row,
    source.result.subset⟩

theorem nativeHealthyPhysicalPrefix_supported (rename : Nat → Fin v)
    (drive : parameters.drive = true) :
    SourceDecoderSchedule.PrefixOriginalSupport rename (nativeHealthyPhysicalPrefix rename drive) :=
  NativeReplay.prefix_supported rename (nativeOutputPrefix rename drive)
    (healthyPhysicalSource rename drive) (nativeHealthyUnitReplay rename drive)
    (nativeOutputPrefix_supported rename drive) (healthyPhysicalSource_supported rename drive)

def nativePhysicalOutputPair (rename : Nat → Fin v) (drive : parameters.drive = true)
    (index : Fin parameters.decoder.roots.length) :
    PairedProjection (nativeHealthyPhysicalPrefix rename drive).state
      (compiledQualifierOutputs (parameters := parameters) rename)
      (nativeRootLiteral rename .healthy index) (nativeRootLiteral rename .faulty index) 2 :=
  pairedPhysicalGuardDischarge (nativeHealthyPhysicalPrefix rename drive).state
    (nativeHealthyFirstFlag (parameters := parameters) rename) _ _
    (compiledQualifierOutputs (parameters := parameters) rename)
    (nativeHealthyPhysicalUnit rename drive)
    ((nativeOutputRoot rename drive index).afterTrace
      (nativeHealthyUnitReplay rename drive).next (nativeHealthyUnitReplay rename drive).added
      (nativeHealthyUnitReplay rename drive).checked)

theorem nativePhysicalOutputPair_checked (rename : Nat → Fin v) (drive : parameters.drive = true)
    (index : Fin parameters.decoder.roots.length) :
    runSteps (nativeHealthyPhysicalPrefix rename drive).state
      (nativePhysicalOutputPair rename drive index).steps =
      some (nativePhysicalOutputPair rename drive index).state :=
  (nativePhysicalOutputPair rename drive index).checked

theorem nativePhysicalOutputPair_count (rename : Nat → Fin v) (drive : parameters.drive = true)
    (index : Fin parameters.decoder.roots.length) :
    (nativePhysicalOutputPair rename drive index).steps.length ≤ 2 :=
  (nativePhysicalOutputPair rename drive index).count


theorem healthyPhysicalSource_unit_origin (rename : Nat → Fin v) (drive : parameters.drive = true) :
    SourceMismatchHandles.ResultOrigin (formula parameters).clauses.size
      (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
      (healthyPhysicalSource rename drive).steps
      (SourceMismatchHandles.healthyFlagUnit rename drive).result.row.id := by
  let first := SourceMismatchBranch.healthyFlagFromTargetAbsent (parameters := parameters) rename
  let absent := mapLiteral rename ((SourceMismatchBranch.wireCursor (parameters := parameters)).slots
    (.internal (.absent .healthy parameters.firstBus parameters.bridge.target)))
  let flag := mapLiteral rename ((SourceMismatchBranch.healthyProductCursor (parameters := parameters)).lastID + 1, true)
  let physical := SourceMismatchBranch.physicalUnitRow (parameters := parameters) rename ⟨0, by decide⟩
  let original : Rows.Available (initialState (relabel rename (formula parameters))) [negate absent] :=
    ⟨physical.id, (by simpa only [absent, SourceMismatchHandles.targetPhysicalUnit rename drive] using physical.present),
      physical.bound⟩
  let left := FoldProjection.afterTrace (ofRow original) first.state first.steps first.checked
  have leftOrigin : SourceMismatchHandles.ResultOrigin (formula parameters).clauses.size
      (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
      first.steps left.row.id :=
    Or.inl (SourceDecoderSchedule.controller_original_allowed rename physical.id
      (SourceMismatchBranch.physicalUnit_allowed rename ⟨0, by decide⟩))
  have rightOrigin : SourceMismatchHandles.ResultOrigin (formula parameters).clauses.size
      (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
      first.steps first.result.row.id := by
    apply resultOrigin_controller_to_decoder rename
    simpa only [initialState, relabel, Controller.CNF.OrderedFormula.relabel, Array.size_map] using
      SourceMismatchHandles.healthyInterface_result_origin rename
  have bound : (formula parameters).clauses.size ≤ first.state.lastId := by
    have actual := runSteps_lastId_le first.checked
    simpa only [initialState, relabel, Controller.CNF.OrderedFormula.relabel, Array.size_map] using actual
  have actual := SourceFoldAggregateProvenance.merge_origins (formula parameters).clauses.size
    (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
    first.steps first.state left.row.id first.result.row.id absent left.clause first.result.clause
    leftOrigin rightOrigin bound
  simpa only [healthyPhysicalSource, SourcePrefix.extend, SourcePrefix.initial,
    SourceMismatchHandles.healthyFlagUnit, SourceMismatchHandles.healthyFlagFromPhysicalUnit,
    List.nil_append, longMerge, longMerge_result, retarget, first, left, original,
    physical, absent, flag] using actual

theorem nativeHealthyPhysicalUnit_origin (rename : Nat → Fin v) (drive : parameters.drive = true) :
    SourceMismatchHandles.ResultOrigin (formula parameters).clauses.size
      (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
      (nativeHealthyPhysicalPrefix rename drive).steps
      (nativeHealthyPhysicalUnit rename drive).row.id := by
  have source := healthyPhysicalSource_unit_origin rename drive
  have mapped := rebase_native_result_origin rename
    ((nativeOutputPrefix rename drive).state.lastId - (formula parameters).clauses.size)
    (healthyPhysicalSource rename drive).steps
    (SourceMismatchHandles.healthyFlagUnit rename drive).result.row.id source
  exact resultOrigin_append_left _ _ (nativeOutputPrefix rename drive).steps
    (nativeHealthyUnitReplay rename drive).added _ mapped

theorem physicalGuardDischarge_supported (rename : Nat → Fin v)
    (start : SourcePrefix (parameters := parameters) rename)
    (healthy input output : Literal (Fin v)) (qualifiers : Clause (Fin v))
    (unit : AvailableSubclause start.state [healthy])
    (transfer : GuardedTransfer start.state ([negate healthy] ++ qualifiers) input output)
    (supported : SourceDecoderSchedule.PrefixOriginalSupport rename start)
    (unitOrigin : SourceMismatchHandles.ResultOrigin (formula parameters).clauses.size
      (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) start.steps unit.row.id)
    (transferOrigin : SourceDecoderSchedule.GuardedTransferOrigin rename start transfer) :
    let actual := physicalGuardDischarge start.state healthy input output qualifiers unit transfer
    SourceDecoderSchedule.PrefixOriginalSupport rename
      (start.extend actual.state actual.steps actual.checked) ∧
    SourceDecoderSchedule.GuardedTransferOrigin rename
      (start.extend actual.state actual.steps actual.checked) actual.result := by
  cases transfer with
  | identity same =>
    exact ⟨by simpa only [physicalGuardDischarge, SourceDecoderSchedule.PrefixOriginalSupport,
      SourcePrefix.extend, List.append_nil] using supported, trivial⟩
  | derived row =>
    have parents := SourceFoldAggregateProvenance.appendMerge_origins_supported
      (formula parameters).clauses.size
      (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
      start.steps start.state unit.row.id row.row.id (negate healthy) unit.clause row.clause
      supported (SourceDecoderSchedule.allowed_native_count_le rename) unitOrigin transferOrigin
      unit.row.bound row.row.bound
    have result := SourceFoldAggregateProvenance.merge_origins
      (formula parameters).clauses.size
      (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
      start.steps start.state unit.row.id row.row.id (negate healthy) unit.clause row.clause
      unitOrigin transferOrigin (SourceMixedSchedule.prefix_native_count_le rename start)
    simpa only [physicalGuardDischarge, longMerge, longMerge_result, retarget,
      SourceDecoderSchedule.PrefixOriginalSupport, SourceDecoderSchedule.GuardedTransferOrigin,
      SourcePrefix.extend] using And.intro parents result

theorem pairedPhysicalGuardDischarge_supported (rename : Nat → Fin v)
    (start : SourcePrefix (parameters := parameters) rename)
    (healthy left right : Literal (Fin v)) (qualifiers : Clause (Fin v))
    (unit : AvailableSubclause start.state [healthy])
    (pair : DirectionPair start.state ([negate healthy] ++ qualifiers) left right)
    (supported : SourceDecoderSchedule.PrefixOriginalSupport rename start)
    (unitOrigin : SourceMismatchHandles.ResultOrigin (formula parameters).clauses.size
      (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) start.steps unit.row.id)
    (pairOrigin : SourceDecoderSchedule.DirectionPairOrigin rename start pair) :
    let actual := pairedPhysicalGuardDischarge start.state healthy left right qualifiers unit pair
    SourceDecoderSchedule.PrefixOriginalSupport rename
      (start.extend actual.state actual.steps actual.checked) ∧
    SourceDecoderSchedule.DirectionPairOrigin rename
      (start.extend actual.state actual.steps actual.checked) actual.pair := by
  let first := physicalGuardDischarge start.state healthy left right qualifiers unit pair.forward
  let current := start.extend first.state first.steps first.checked
  have one := physicalGuardDischarge_supported rename start healthy left right qualifiers unit pair.forward
    supported unitOrigin pairOrigin.1
  let nextUnit := FoldProjection.afterTrace unit first.state first.steps first.checked
  let reverse := pair.backward.afterTrace first.state first.steps first.checked
  have nextUnitOrigin := resultOrigin_append_right (formula parameters).clauses.size
    (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
    start.steps first.steps unit.row.id unitOrigin
  have nextReverseOrigin := SourceDecoderSchedule.GuardedTransferOrigin.afterTrace rename start pair.backward
    pairOrigin.2 first.state first.steps first.checked
  let second := physicalGuardDischarge first.state healthy right left qualifiers nextUnit reverse
  have two := physicalGuardDischarge_supported rename current healthy right left qualifiers nextUnit reverse
    one.1 nextUnitOrigin nextReverseOrigin
  have nextForwardOrigin := SourceDecoderSchedule.GuardedTransferOrigin.afterTrace rename current first.result
    one.2 second.state second.steps second.checked
  let finished := start.extend second.state (first.steps ++ second.steps) (by
    rw [runSteps_append, first.checked]
    exact second.checked)
  have stepsEqual : current.steps ++ second.steps = finished.steps := by
    simp only [current, finished, SourcePrefix.extend, List.append_assoc]
  let finalPair : DirectionPair second.state qualifiers left right :=
    ⟨first.result.afterTrace second.state second.steps second.checked, second.result⟩
  have carried := decoderPairOrigin_same_steps rename second.state
    (current.steps ++ second.steps) finished.steps stepsEqual
    (current.extend second.state second.steps second.checked).checked finished.checked
    finalPair (And.intro nextForwardOrigin two.2)
  change SourceDecoderSchedule.PrefixOriginalSupport rename finished ∧
    SourceDecoderSchedule.DirectionPairOrigin rename finished finalPair
  refine ⟨?_, carried⟩
  simpa only [SourceDecoderSchedule.PrefixOriginalSupport, current, finished,
    SourcePrefix.extend, List.append_assoc] using two.1

theorem nativePhysicalOutputPair_supported (rename : Nat → Fin v) (drive : parameters.drive = true)
    (index : Fin parameters.decoder.roots.length) :
    let actual := nativePhysicalOutputPair rename drive index
    SourceDecoderSchedule.PrefixOriginalSupport rename
      ((nativeHealthyPhysicalPrefix rename drive).extend actual.state actual.steps actual.checked) ∧
    SourceDecoderSchedule.DirectionPairOrigin rename
      ((nativeHealthyPhysicalPrefix rename drive).extend actual.state actual.steps actual.checked) actual.pair := by
  have rootOrigin := SourceDecoderSchedule.DirectionPairOrigin.afterTrace rename
    (nativeOutputPrefix rename drive) (nativeOutputRoot rename drive index)
    (nativeOutputRoot_supported rename drive index)
    (nativeHealthyUnitReplay rename drive).next (nativeHealthyUnitReplay rename drive).added
    (nativeHealthyUnitReplay rename drive).checked
  exact pairedPhysicalGuardDischarge_supported rename (nativeHealthyPhysicalPrefix rename drive)
    (nativeHealthyFirstFlag (parameters := parameters) rename) _ _
    (compiledQualifierOutputs (parameters := parameters) rename)
    (nativeHealthyPhysicalUnit rename drive) _ (nativeHealthyPhysicalPrefix_supported rename drive)
    (nativeHealthyPhysicalUnit_origin rename drive) rootOrigin

theorem guardedTransfer_actual_conclusion {state : State v} {context : Clause (Fin v)}
    {input output : Literal (Fin v)} (transfer : GuardedTransfer state context input output) :
    input = output ∨ ∃ id clause,
      state.rows id = some clause ∧ id ≤ state.lastId ∧
      ClauseSubset clause (context ++ [negate input, output]) := by
  cases transfer with
  | identity same => exact Or.inl same
  | derived row => exact Or.inr ⟨row.row.id, row.clause, row.row.present, row.row.bound, row.subset⟩

theorem nativePhysicalOutputPair_actual_conclusions (rename : Nat → Fin v)
    (drive : parameters.drive = true) (index : Fin parameters.decoder.roots.length) :
    let actual := nativePhysicalOutputPair rename drive index
    (nativeRootLiteral rename .healthy index = nativeRootLiteral rename .faulty index ∨
      ∃ id clause, actual.state.rows id = some clause ∧ id ≤ actual.state.lastId ∧
        ClauseSubset clause (compiledQualifierOutputs (parameters := parameters) rename ++
          [negate (nativeRootLiteral rename .healthy index), nativeRootLiteral rename .faulty index])) ∧
    (nativeRootLiteral rename .faulty index = nativeRootLiteral rename .healthy index ∨
      ∃ id clause, actual.state.rows id = some clause ∧ id ≤ actual.state.lastId ∧
        ClauseSubset clause (compiledQualifierOutputs (parameters := parameters) rename ++
          [negate (nativeRootLiteral rename .faulty index), nativeRootLiteral rename .healthy index])) :=
  ⟨guardedTransfer_actual_conclusion (nativePhysicalOutputPair rename drive index).pair.forward,
    guardedTransfer_actual_conclusion (nativePhysicalOutputPair rename drive index).pair.backward⟩

theorem nativeHealthyPhysicalPrefix_count (rename : Nat → Fin v) (drive : parameters.drive = true) :
    (nativeHealthyPhysicalPrefix rename drive).steps.length ≤
      nativeOutputMacroBudget parameters.decoder.countedSize parameters.buses + 2 := by
  have prior := nativeOutputPrefix_macro_count rename drive
  have appended := (nativeHealthyUnitReplay rename drive).added_length
  have unitCount := (SourceMismatchHandles.healthyFlagUnit rename drive).count
  have sourceLength : (healthyPhysicalSource rename drive).steps.length =
      (SourceMismatchHandles.healthyFlagUnit rename drive).steps.length := by
    simp only [healthyPhysicalSource, SourcePrefix.initial, SourcePrefix.extend, List.nil_append]
  have addedCount : (nativeHealthyUnitReplay rename drive).added.length ≤ 2 :=
    appended.le.trans (sourceLength.le.trans unitCount)
  change ((nativeOutputPrefix rename drive).steps ++ (nativeHealthyUnitReplay rename drive).added).length ≤ _
  simp only [List.length_append]
  omega


def nativeHealthyPhysicalRoot (rename : Nat → Fin v) (drive : parameters.drive = true)
    (index : Fin parameters.decoder.roots.length) :
    DirectionPair (nativeHealthyPhysicalPrefix rename drive).state
      (nativeOutputContext (parameters := parameters) rename)
      (nativeRootLiteral rename .healthy index) (nativeRootLiteral rename .faulty index) :=
  (nativeOutputRoot rename drive index).afterTrace
    (nativeHealthyUnitReplay rename drive).next (nativeHealthyUnitReplay rename drive).added
    (nativeHealthyUnitReplay rename drive).checked

structure PhysicalOutputAccumulator (rename : Nat → Fin v) (drive : parameters.drive = true)
    (count : Nat) where
  state : State v
  steps : List (Step v)
  checked : runSteps (nativeHealthyPhysicalPrefix rename drive).state steps = some state
  pairs : ∀ index : Fin parameters.decoder.roots.length, index.val < count →
    DirectionPair state (compiledQualifierOutputs (parameters := parameters) rename)
      (nativeRootLiteral rename .healthy index) (nativeRootLiteral rename .faulty index)

def PhysicalOutputAccumulator.prefix (program : PhysicalOutputAccumulator (parameters := parameters)
    rename drive count) : SourcePrefix (parameters := parameters) rename :=
  (nativeHealthyPhysicalPrefix rename drive).extend program.state program.steps program.checked

def physicalOutputInitial (rename : Nat → Fin v) (drive : parameters.drive = true) :
    PhysicalOutputAccumulator (parameters := parameters) rename drive 0 :=
  ⟨(nativeHealthyPhysicalPrefix rename drive).state, [], rfl,
    fun index impossible => False.elim (Nat.not_lt_zero index.val impossible)⟩

def physicalOutputPairAt (rename : Nat → Fin v) (drive : parameters.drive = true)
    (prior : PhysicalOutputAccumulator (parameters := parameters) rename drive count)
    (index : Fin parameters.decoder.roots.length) :
    PairedProjection prior.state (compiledQualifierOutputs (parameters := parameters) rename)
      (nativeRootLiteral rename .healthy index) (nativeRootLiteral rename .faulty index) 2 :=
  pairedPhysicalGuardDischarge prior.state (nativeHealthyFirstFlag (parameters := parameters) rename) _ _
    (compiledQualifierOutputs (parameters := parameters) rename)
    (FoldProjection.afterTrace (nativeHealthyPhysicalUnit rename drive)
      prior.state prior.steps prior.checked)
    ((nativeHealthyPhysicalRoot rename drive index).afterTrace prior.state prior.steps prior.checked)

def physicalOutputAdvanceKernel (rename : Nat → Fin v) (drive : parameters.drive = true)
    (count : Nat) (before : count < parameters.decoder.roots.length)
    (prior : PhysicalOutputAccumulator (parameters := parameters) rename drive count)
    (added : PairedProjection prior.state (compiledQualifierOutputs (parameters := parameters) rename)
      (nativeRootLiteral rename .healthy ⟨count, before⟩)
      (nativeRootLiteral rename .faulty ⟨count, before⟩) 2) :
    PhysicalOutputAccumulator (parameters := parameters) rename drive (count + 1) := by
  let selected : Fin parameters.decoder.roots.length := ⟨count, before⟩
  refine ⟨added.state, prior.steps ++ added.steps, ?_, ?_⟩
  · rw [runSteps_append, prior.checked]
    exact added.checked
  · intro query below
    by_cases same : query = selected
    · subst query
      exact added.pair
    · have earlier : query.val < count := by
        have different : query.val ≠ count := by
          intro equal
          apply same
          apply Fin.ext
          exact equal
        omega
      exact (prior.pairs query earlier).afterTrace added.state added.steps added.checked

def physicalOutputAdvance (rename : Nat → Fin v) (drive : parameters.drive = true)
    (count : Nat) (before : count < parameters.decoder.roots.length)
    (prior : PhysicalOutputAccumulator (parameters := parameters) rename drive count) :
    PhysicalOutputAccumulator (parameters := parameters) rename drive (count + 1) :=
  physicalOutputAdvanceKernel rename drive count before prior
    (physicalOutputPairAt rename drive prior ⟨count, before⟩)

def buildPhysicalOutputs (rename : Nat → Fin v) (drive : parameters.drive = true)
    (count : Nat) (bound : count ≤ parameters.decoder.roots.length) :
    PhysicalOutputAccumulator (parameters := parameters) rename drive count :=
  match count with
  | 0 => physicalOutputInitial rename drive
  | count + 1 => physicalOutputAdvance rename drive count (by omega)
      (buildPhysicalOutputs rename drive count (by omega))

theorem buildPhysicalOutputs_count (rename : Nat → Fin v) (drive : parameters.drive = true)
    (count : Nat) (bound : count ≤ parameters.decoder.roots.length) :
    (buildPhysicalOutputs rename drive count bound).steps.length ≤ 2 * count := by
  induction count with
  | zero => exact Nat.zero_le _
  | succ count ih =>
    have prior := ih (by omega)
    have added := (physicalOutputPairAt rename drive
      (buildPhysicalOutputs rename drive count (by omega)) ⟨count, by omega⟩).count
    change ((buildPhysicalOutputs rename drive count (by omega)).steps ++
      (physicalOutputPairAt rename drive
        (buildPhysicalOutputs rename drive count (by omega)) ⟨count, by omega⟩).steps).length ≤ _
    simp only [List.length_append]
    omega

def physicalOutputProgram (rename : Nat → Fin v) (drive : parameters.drive = true) :
    PhysicalOutputAccumulator (parameters := parameters) rename drive parameters.decoder.roots.length :=
  buildPhysicalOutputs rename drive parameters.decoder.roots.length (Nat.le_refl _)

def physicalOutputPrefix (rename : Nat → Fin v) (drive : parameters.drive = true) :
    SourcePrefix (parameters := parameters) rename :=
  (physicalOutputProgram rename drive).prefix

def physicalOutputRoot (rename : Nat → Fin v) (drive : parameters.drive = true)
    (index : Fin parameters.decoder.roots.length) :
    DirectionPair (physicalOutputPrefix rename drive).state
      (compiledQualifierOutputs (parameters := parameters) rename)
      (nativeRootLiteral rename .healthy index) (nativeRootLiteral rename .faulty index) :=
  (physicalOutputProgram rename drive).pairs index index.isLt

theorem physicalOutputPrefix_count (rename : Nat → Fin v) (drive : parameters.drive = true) :
    (physicalOutputPrefix rename drive).steps.length ≤
      nativeOutputMacroBudget parameters.decoder.countedSize parameters.buses + 2 +
        2 * parameters.decoder.roots.length := by
  have prior := nativeHealthyPhysicalPrefix_count rename drive
  have added : (physicalOutputProgram rename drive).steps.length ≤ 2 * parameters.decoder.roots.length :=
    buildPhysicalOutputs_count rename drive parameters.decoder.roots.length (Nat.le_refl _)
  change ((nativeHealthyPhysicalPrefix rename drive).steps ++
    (physicalOutputProgram rename drive).steps).length ≤ _
  simp only [List.length_append]
  omega


theorem nativeHealthyPhysicalRoot_supported (rename : Nat → Fin v) (drive : parameters.drive = true)
    (index : Fin parameters.decoder.roots.length) :
    SourceDecoderSchedule.DirectionPairOrigin rename (nativeHealthyPhysicalPrefix rename drive)
      (nativeHealthyPhysicalRoot rename drive index) :=
  SourceDecoderSchedule.DirectionPairOrigin.afterTrace rename
    (nativeOutputPrefix rename drive) (nativeOutputRoot rename drive index)
    (nativeOutputRoot_supported rename drive index) (nativeHealthyUnitReplay rename drive).next
    (nativeHealthyUnitReplay rename drive).added (nativeHealthyUnitReplay rename drive).checked

def PhysicalOutputAccumulatorOriginals (rename : Nat → Fin v) (drive : parameters.drive = true)
    (count : Nat) (program : PhysicalOutputAccumulator (parameters := parameters) rename drive count) : Prop :=
  SourceDecoderSchedule.PrefixOriginalSupport rename program.prefix ∧
    ∀ index : Fin parameters.decoder.roots.length, ∀ before : index.val < count,
      SourceDecoderSchedule.DirectionPairOrigin rename program.prefix (program.pairs index before)

theorem physicalOutputInitial_originals (rename : Nat → Fin v) (drive : parameters.drive = true) :
    PhysicalOutputAccumulatorOriginals rename drive 0 (physicalOutputInitial rename drive) := by
  constructor
  · simpa only [physicalOutputInitial, PhysicalOutputAccumulator.prefix, SourcePrefix.extend,
      SourceDecoderSchedule.PrefixOriginalSupport, List.append_nil] using
      nativeHealthyPhysicalPrefix_supported rename drive
  · intro index impossible
    exact False.elim (Nat.not_lt_zero index.val impossible)

theorem physicalOutputPairAt_supported (rename : Nat → Fin v) (drive : parameters.drive = true)
    (count : Nat) (prior : PhysicalOutputAccumulator (parameters := parameters) rename drive count)
    (index : Fin parameters.decoder.roots.length)
    (supported : SourceDecoderSchedule.PrefixOriginalSupport rename prior.prefix) :
    let added := physicalOutputPairAt rename drive prior index
    SourceDecoderSchedule.PrefixOriginalSupport rename
      (prior.prefix.extend added.state added.steps added.checked) ∧
    SourceDecoderSchedule.DirectionPairOrigin rename
      (prior.prefix.extend added.state added.steps added.checked) added.pair := by
  let unit := FoldProjection.afterTrace (nativeHealthyPhysicalUnit rename drive)
    prior.state prior.steps prior.checked
  let pair := (nativeHealthyPhysicalRoot rename drive index).afterTrace prior.state prior.steps prior.checked
  have unitOrigin := resultOrigin_append_right (formula parameters).clauses.size
    (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
    (nativeHealthyPhysicalPrefix rename drive).steps prior.steps
    (nativeHealthyPhysicalUnit rename drive).row.id (nativeHealthyPhysicalUnit_origin rename drive)
  have pairOrigin := SourceDecoderSchedule.DirectionPairOrigin.afterTrace rename
    (nativeHealthyPhysicalPrefix rename drive) (nativeHealthyPhysicalRoot rename drive index)
    (nativeHealthyPhysicalRoot_supported rename drive index) prior.state prior.steps prior.checked
  exact pairedPhysicalGuardDischarge_supported rename prior.prefix
    (nativeHealthyFirstFlag (parameters := parameters) rename) _ _
    (compiledQualifierOutputs (parameters := parameters) rename)
    unit pair supported unitOrigin pairOrigin

theorem physicalOutputAdvanceKernel_supported (rename : Nat → Fin v) (drive : parameters.drive = true)
    (count : Nat) (before : count < parameters.decoder.roots.length)
    (prior : PhysicalOutputAccumulator (parameters := parameters) rename drive count)
    (added : PairedProjection prior.state (compiledQualifierOutputs (parameters := parameters) rename)
      (nativeRootLiteral rename .healthy ⟨count, before⟩)
      (nativeRootLiteral rename .faulty ⟨count, before⟩) 2)
    (priorOriginal : PhysicalOutputAccumulatorOriginals rename drive count prior)
    (addedOriginal : SourceDecoderSchedule.PrefixOriginalSupport rename
        (prior.prefix.extend added.state added.steps added.checked) ∧
      SourceDecoderSchedule.DirectionPairOrigin rename
        (prior.prefix.extend added.state added.steps added.checked) added.pair) :
    PhysicalOutputAccumulatorOriginals rename drive (count + 1)
      (physicalOutputAdvanceKernel rename drive count before prior added) := by
  let finished := (nativeHealthyPhysicalPrefix rename drive).extend added.state
    (prior.steps ++ added.steps) (by rw [runSteps_append, prior.checked]; exact added.checked)
  have stepsEqual : prior.prefix.steps ++ added.steps = finished.steps := by
    simp only [PhysicalOutputAccumulator.prefix, finished, SourcePrefix.extend, List.append_assoc]
  constructor
  · simpa only [SourceDecoderSchedule.PrefixOriginalSupport, physicalOutputAdvanceKernel,
      PhysicalOutputAccumulator.prefix, SourcePrefix.extend, List.append_assoc] using addedOriginal.1
  · intro query below
    let selected : Fin parameters.decoder.roots.length := ⟨count, before⟩
    by_cases same : query = selected
    · subst query
      have carried := decoderPairOrigin_same_steps rename added.state
        (prior.prefix.steps ++ added.steps) finished.steps stepsEqual
        (prior.prefix.extend added.state added.steps added.checked).checked finished.checked
        added.pair addedOriginal.2
      simp only [physicalOutputAdvanceKernel, PhysicalOutputAccumulator.prefix]
      dsimp only [SourcePrefix.extend]
      rw [dite_eq_left (show (⟨count, before⟩ : Fin parameters.decoder.roots.length) =
          ⟨count, before⟩ from rfl)]
      change SourceDecoderSchedule.DirectionPairOrigin rename finished added.pair
      exact carried
    · have earlier : query.val < count := by
        have different : query.val ≠ count := by
          intro equal
          apply same
          apply Fin.ext
          exact equal
        omega
      have origin := SourceDecoderSchedule.DirectionPairOrigin.afterTrace rename prior.prefix
        (prior.pairs query earlier) (priorOriginal.2 query earlier)
        added.state added.steps added.checked
      have carried := decoderPairOrigin_same_steps rename added.state
        (prior.prefix.steps ++ added.steps) finished.steps stepsEqual
        (prior.prefix.extend added.state added.steps added.checked).checked finished.checked
        ((prior.pairs query earlier).afterTrace added.state added.steps added.checked) origin
      simp only [physicalOutputAdvanceKernel, PhysicalOutputAccumulator.prefix]
      dsimp only [SourcePrefix.extend]
      rw [dite_eq_right same]
      change SourceDecoderSchedule.DirectionPairOrigin rename finished
        ((prior.pairs query earlier).afterTrace added.state added.steps added.checked)
      exact carried

theorem physicalOutputAdvance_originals (rename : Nat → Fin v) (drive : parameters.drive = true)
    (count : Nat) (before : count < parameters.decoder.roots.length)
    (prior : PhysicalOutputAccumulator (parameters := parameters) rename drive count)
    (original : PhysicalOutputAccumulatorOriginals rename drive count prior) :
    PhysicalOutputAccumulatorOriginals rename drive (count + 1)
      (physicalOutputAdvance rename drive count before prior) :=
  physicalOutputAdvanceKernel_supported rename drive count before prior
    (physicalOutputPairAt rename drive prior ⟨count, before⟩) original
    (physicalOutputPairAt_supported rename drive count prior ⟨count, before⟩ original.1)

theorem buildPhysicalOutputs_originals (rename : Nat → Fin v) (drive : parameters.drive = true)
    (count : Nat) (bound : count ≤ parameters.decoder.roots.length) :
    PhysicalOutputAccumulatorOriginals rename drive count
      (buildPhysicalOutputs rename drive count bound) := by
  induction count with
  | zero => exact physicalOutputInitial_originals rename drive
  | succ count ih =>
    exact physicalOutputAdvance_originals rename drive count (by omega)
      (buildPhysicalOutputs rename drive count (by omega)) (ih (by omega))

theorem physicalOutputPrefix_supported (rename : Nat → Fin v) (drive : parameters.drive = true) :
    SourceDecoderSchedule.PrefixOriginalSupport rename (physicalOutputPrefix rename drive) :=
  (buildPhysicalOutputs_originals rename drive parameters.decoder.roots.length (Nat.le_refl _)).1

theorem physicalOutputRoot_supported (rename : Nat → Fin v) (drive : parameters.drive = true)
    (index : Fin parameters.decoder.roots.length) :
    SourceDecoderSchedule.DirectionPairOrigin rename (physicalOutputPrefix rename drive)
      (physicalOutputRoot rename drive index) :=
  (buildPhysicalOutputs_originals rename drive parameters.decoder.roots.length (Nat.le_refl _)).2 index index.isLt

theorem physicalOutputRoot_actual_conclusions (rename : Nat → Fin v)
    (drive : parameters.drive = true) (index : Fin parameters.decoder.roots.length) :
    (nativeRootLiteral rename .healthy index = nativeRootLiteral rename .faulty index ∨
      ∃ id clause, (physicalOutputPrefix rename drive).state.rows id = some clause ∧
        id ≤ (physicalOutputPrefix rename drive).state.lastId ∧
        ClauseSubset clause (compiledQualifierOutputs (parameters := parameters) rename ++
          [negate (nativeRootLiteral rename .healthy index), nativeRootLiteral rename .faulty index])) ∧
    (nativeRootLiteral rename .faulty index = nativeRootLiteral rename .healthy index ∨
      ∃ id clause, (physicalOutputPrefix rename drive).state.rows id = some clause ∧
        id ≤ (physicalOutputPrefix rename drive).state.lastId ∧
        ClauseSubset clause (compiledQualifierOutputs (parameters := parameters) rename ++
          [negate (nativeRootLiteral rename .faulty index), nativeRootLiteral rename .healthy index])) :=
  ⟨guardedTransfer_actual_conclusion (physicalOutputRoot rename drive index).forward,
    guardedTransfer_actual_conclusion (physicalOutputRoot rename drive index).backward⟩


def physicalOutputMacroBudget (n b : Nat) : Nat := nativeOutputMacroBudget n b + 2 + 2 * n

theorem physicalOutputPrefix_macro_count (rename : Nat → Fin v) (drive : parameters.drive = true) :
    (physicalOutputPrefix rename drive).steps.length ≤
      physicalOutputMacroBudget parameters.decoder.countedSize parameters.buses := by
  have roots : parameters.decoder.roots.length ≤ parameters.decoder.countedSize := by
    rw [Decoder.DAG.countedSize_eq]
    omega
  exact (physicalOutputPrefix_count rename drive).trans
    (Nat.add_le_add_left (Nat.mul_le_mul_left 2 roots) _)

theorem physicalOutputPrefix_checked (rename : Nat → Fin v) (drive : parameters.drive = true) :
    runSteps (initialState (relabel rename (formula parameters))) (physicalOutputPrefix rename drive).steps =
      some (physicalOutputPrefix rename drive).state :=
  (physicalOutputPrefix rename drive).checked

theorem physicalOutputPrefix_localCaseCatalogue (rename : Nat → Fin v)
    (drive : parameters.drive = true) :
    ∃ records,
      resolutionRupSchedule (initialState (relabel rename (formula parameters)))
        (physicalOutputPrefix rename drive).steps = some records ∧
      records.map ResolutionRupInvocation.step = (physicalOutputPrefix rename drive).steps ∧
      records.length ≤ physicalOutputMacroBudget parameters.decoder.countedSize parameters.buses ∧
      ∀ record ∈ records,
        Controller.Resolution.Cases.ValidTree record.base record.step.clause record.tree ∧
        (splitVariables record.tree).card ≤ 5 ∧
        ∀ parent ∈ treeParentIds record.tree,
          (parent ≤ (formula parameters).clauses.size →
            SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename parent) ∧
          ((formula parameters).clauses.size < parent →
            ∃ earlier ∈ (physicalOutputPrefix rename drive).steps,
              earlier.id = parent ∧ earlier.id < record.step.id) := by
  obtain ⟨records, run, count, sound⟩ :=
    SourcePrefix.resolutionRupSchedule_sound rename (physicalOutputPrefix rename drive)
  have exactSteps := (resolutionRupSchedule_steps _ _ records run).1
  have exactTargets := resolutionRupSchedule_targets _ _ records run
  have parents := resolutionRupSchedule_parentSupport _ _
    (initialState (relabel rename (formula parameters)))
    (physicalOutputPrefix rename drive).steps records run (physicalOutputPrefix_supported rename drive)
  refine ⟨records, run, exactSteps,
    count.le.trans (physicalOutputPrefix_macro_count rename drive), ?_⟩
  intro record member
  have valid : Controller.Resolution.Cases.ValidTree record.base record.step.clause record.tree := by
    rw [← exactTargets record member]
    exact (sound record member).1
  refine ⟨valid, ?_, parents record member⟩
  rw [(sound record member).2.1]
  simp


/-- This join removes only the proved healthy flag literal, retaining the faulty cofactor guard. -/
def physicalUnitClauseDischarge (state : State v) (healthy : Literal (Fin v))
    (target : Clause (Fin v)) (unit : AvailableSubclause state [healthy])
    (guarded : AvailableSubclause state (negate healthy :: target)) :
    SubclauseProjection state target 1 := by
  let left : AvailableSubclause state [negate (negate healthy)] := retarget unit (by
    intro literal member
    simpa only [negate_negate] using member)
  let joined := longMerge state (negate healthy) [] target left guarded
  refine ⟨joined.state, joined.steps, longMerge_run _ _ _ _ _ _, ?_, longMerge_count _ _ _ _ _ _⟩
  simpa only [List.nil_append] using longMerge_result state (negate healthy) [] target left guarded

theorem physicalUnitClauseDischarge_supported (rename : Nat → Fin v)
    (start : SourcePrefix (parameters := parameters) rename) (healthy : Literal (Fin v))
    (target : Clause (Fin v)) (unit : AvailableSubclause start.state [healthy])
    (guarded : AvailableSubclause start.state (negate healthy :: target))
    (supported : SourceDecoderSchedule.PrefixOriginalSupport rename start)
    (unitOrigin : SourceMismatchHandles.ResultOrigin (formula parameters).clauses.size
      (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) start.steps unit.row.id)
    (guardOrigin : SourceMismatchHandles.ResultOrigin (formula parameters).clauses.size
      (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) start.steps guarded.row.id) :
    SourceDecoderSchedule.ProjectionOriginalSupport rename start
      (physicalUnitClauseDischarge start.state healthy target unit guarded) := by
  have parents := SourceFoldAggregateProvenance.appendMerge_origins_supported
    (formula parameters).clauses.size
    (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
    start.steps start.state unit.row.id guarded.row.id (negate healthy) unit.clause guarded.clause
    supported (SourceDecoderSchedule.allowed_native_count_le rename) unitOrigin guardOrigin
    unit.row.bound guarded.row.bound
  have result := SourceFoldAggregateProvenance.merge_origins
    (formula parameters).clauses.size
    (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
    start.steps start.state unit.row.id guarded.row.id (negate healthy) unit.clause guarded.clause
    unitOrigin guardOrigin (SourceMixedSchedule.prefix_native_count_le rename start)
  simpa only [physicalUnitClauseDischarge, SourceDecoderSchedule.ProjectionOriginalSupport,
    longMerge, longMerge_result, retarget] using And.intro parents result

def nativeHealthyEqualRoot (rename : Nat → Fin v) (drive : parameters.drive = true)
    (index : Fin parameters.decoder.roots.length) :
    DirectionPair (nativeHealthyPhysicalPrefix rename drive).state
      [negate (nativeHealthyFirstFlag (parameters := parameters) rename),
        negate (nativeFaultyFirstFlag (parameters := parameters) rename)]
      (nativeRootLiteral rename .healthy index) (nativeRootLiteral rename .faulty index) :=
  ((nativeCofactorRoot rename drive true index).afterTrace
    (nativeOutputProgram rename drive).state (nativeOutputProgram rename drive).steps
    (nativeOutputProgram rename drive).checked).afterTrace
      (nativeHealthyUnitReplay rename drive).next (nativeHealthyUnitReplay rename drive).added
      (nativeHealthyUnitReplay rename drive).checked

theorem nativeHealthyEqualRoot_supported (rename : Nat → Fin v) (drive : parameters.drive = true)
    (index : Fin parameters.decoder.roots.length) :
    SourceDecoderSchedule.DirectionPairOrigin rename (nativeHealthyPhysicalPrefix rename drive)
      (nativeHealthyEqualRoot rename drive index) := by
  have first := SourceDecoderSchedule.DirectionPairOrigin.afterTrace rename
    (nativeCofactorPrefix rename drive) (nativeCofactorRoot rename drive true index)
    (nativeCofactorRoot_supported rename drive true index)
    (nativeOutputProgram rename drive).state (nativeOutputProgram rename drive).steps
    (nativeOutputProgram rename drive).checked
  exact SourceDecoderSchedule.DirectionPairOrigin.afterTrace rename (nativeOutputPrefix rename drive)
    ((nativeCofactorRoot rename drive true index).afterTrace
      (nativeOutputProgram rename drive).state (nativeOutputProgram rename drive).steps
      (nativeOutputProgram rename drive).checked) first
    (nativeHealthyUnitReplay rename drive).next (nativeHealthyUnitReplay rename drive).added
    (nativeHealthyUnitReplay rename drive).checked

def nativeHealthyMixedRow (rename : Nat → Fin v) (drive : parameters.drive = true) :
    AvailableSubclause (nativeHealthyPhysicalPrefix rename drive).state
      ([negate (nativeHealthyFirstFlag (parameters := parameters) rename),
        nativeFaultyFirstFlag (parameters := parameters) rename] ++
        compiledQualifierOutputs (parameters := parameters) rename) :=
  FoldProjection.afterTrace
    (FoldProjection.afterTrace (nativeCofactorMixed rename drive)
      (nativeOutputProgram rename drive).state (nativeOutputProgram rename drive).steps
      (nativeOutputProgram rename drive).checked)
    (nativeHealthyUnitReplay rename drive).next (nativeHealthyUnitReplay rename drive).added
    (nativeHealthyUnitReplay rename drive).checked

theorem nativeHealthyMixedRow_origin (rename : Nat → Fin v) (drive : parameters.drive = true) :
    SourceMismatchHandles.ResultOrigin (formula parameters).clauses.size
      (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
      (nativeHealthyPhysicalPrefix rename drive).steps (nativeHealthyMixedRow rename drive).row.id := by
  have first := resultOrigin_append_right (formula parameters).clauses.size
    (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
    (nativeCofactorPrefix rename drive).steps (nativeOutputProgram rename drive).steps
    (nativeCofactorMixed rename drive).row.id (nativeCofactorMixed_supported rename drive)
  exact resultOrigin_append_right (formula parameters).clauses.size
    (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
    (nativeOutputPrefix rename drive).steps (nativeHealthyUnitReplay rename drive).added
    (nativeCofactorMixed rename drive).row.id first

def nativePhysicalSelectorActivation (rename : Nat → Fin v) (drive : parameters.drive = true) :
    SubclauseProjection (nativeHealthyPhysicalPrefix rename drive).state
      (nativeFaultyFirstFlag (parameters := parameters) rename ::
        compiledQualifierOutputs (parameters := parameters) rename) 1 :=
  physicalUnitClauseDischarge (nativeHealthyPhysicalPrefix rename drive).state
    (nativeHealthyFirstFlag (parameters := parameters) rename) _
    (nativeHealthyPhysicalUnit rename drive)
    (retarget (nativeHealthyMixedRow rename drive) (by
      intro literal member
      simpa only [List.cons_append, List.nil_append] using member))

theorem nativePhysicalSelectorActivation_supported (rename : Nat → Fin v)
    (drive : parameters.drive = true) :
    SourceDecoderSchedule.ProjectionOriginalSupport rename (nativeHealthyPhysicalPrefix rename drive)
      (nativePhysicalSelectorActivation rename drive) :=
  physicalUnitClauseDischarge_supported rename (nativeHealthyPhysicalPrefix rename drive)
    (nativeHealthyFirstFlag (parameters := parameters) rename) _ (nativeHealthyPhysicalUnit rename drive)
    _ (nativeHealthyPhysicalPrefix_supported rename drive) (nativeHealthyPhysicalUnit_origin rename drive)
    (nativeHealthyMixedRow_origin rename drive)

def nativePhysicalEqualRootPair (rename : Nat → Fin v) (drive : parameters.drive = true)
    (index : Fin parameters.decoder.roots.length) :
    PairedProjection (nativeHealthyPhysicalPrefix rename drive).state
      [negate (nativeFaultyFirstFlag (parameters := parameters) rename)]
      (nativeRootLiteral rename .healthy index) (nativeRootLiteral rename .faulty index) 2 :=
  pairedPhysicalGuardDischarge (nativeHealthyPhysicalPrefix rename drive).state
    (nativeHealthyFirstFlag (parameters := parameters) rename) _ _
    [negate (nativeFaultyFirstFlag (parameters := parameters) rename)]
    (nativeHealthyPhysicalUnit rename drive) (nativeHealthyEqualRoot rename drive index)

theorem nativePhysicalEqualRootPair_supported (rename : Nat → Fin v)
    (drive : parameters.drive = true) (index : Fin parameters.decoder.roots.length) :
    let actual := nativePhysicalEqualRootPair rename drive index
    SourceDecoderSchedule.PrefixOriginalSupport rename
      ((nativeHealthyPhysicalPrefix rename drive).extend actual.state actual.steps actual.checked) ∧
    SourceDecoderSchedule.DirectionPairOrigin rename
      ((nativeHealthyPhysicalPrefix rename drive).extend actual.state actual.steps actual.checked) actual.pair :=
  pairedPhysicalGuardDischarge_supported rename (nativeHealthyPhysicalPrefix rename drive)
    (nativeHealthyFirstFlag (parameters := parameters) rename) _ _
    [negate (nativeFaultyFirstFlag (parameters := parameters) rename)]
    (nativeHealthyPhysicalUnit rename drive) (nativeHealthyEqualRoot rename drive index)
    (nativeHealthyPhysicalPrefix_supported rename drive) (nativeHealthyPhysicalUnit_origin rename drive)
    (nativeHealthyEqualRoot_supported rename drive index)

theorem nativePhysicalSelectorActivation_actual_conclusion (rename : Nat → Fin v)
    (drive : parameters.drive = true) :
    let actual := nativePhysicalSelectorActivation rename drive
    actual.state.rows actual.result.row.id = some actual.result.clause ∧
    actual.result.row.id ≤ actual.state.lastId ∧
    ClauseSubset actual.result.clause
      (nativeFaultyFirstFlag (parameters := parameters) rename ::
        compiledQualifierOutputs (parameters := parameters) rename) :=
  ⟨(nativePhysicalSelectorActivation rename drive).result.row.present,
    (nativePhysicalSelectorActivation rename drive).result.row.bound,
    (nativePhysicalSelectorActivation rename drive).result.subset⟩

theorem nativePhysicalEqualRootPair_actual_conclusions (rename : Nat → Fin v)
    (drive : parameters.drive = true) (index : Fin parameters.decoder.roots.length) :
    let actual := nativePhysicalEqualRootPair rename drive index
    (nativeRootLiteral rename .healthy index = nativeRootLiteral rename .faulty index ∨
      ∃ id clause, actual.state.rows id = some clause ∧ id ≤ actual.state.lastId ∧
        ClauseSubset clause ([negate (nativeFaultyFirstFlag (parameters := parameters) rename)] ++
          [negate (nativeRootLiteral rename .healthy index), nativeRootLiteral rename .faulty index])) ∧
    (nativeRootLiteral rename .faulty index = nativeRootLiteral rename .healthy index ∨
      ∃ id clause, actual.state.rows id = some clause ∧ id ≤ actual.state.lastId ∧
        ClauseSubset clause ([negate (nativeFaultyFirstFlag (parameters := parameters) rename)] ++
          [negate (nativeRootLiteral rename .faulty index), nativeRootLiteral rename .healthy index])) :=
  ⟨guardedTransfer_actual_conclusion (nativePhysicalEqualRootPair rename drive index).pair.forward,
    guardedTransfer_actual_conclusion (nativePhysicalEqualRootPair rename drive index).pair.backward⟩


/-- A single schedule retains the activation row and both families of root
comparisons. All projections consume earlier rows in the same state. -/
structure SelectorOutputAccumulator (rename : Nat → Fin v) (drive : parameters.drive = true)
    (count : Nat) where
  state : State v
  steps : List (Step v)
  checked : runSteps (nativeHealthyPhysicalPrefix rename drive).state steps = some state
  activation : AvailableSubclause state
    (nativeFaultyFirstFlag (parameters := parameters) rename ::
      compiledQualifierOutputs (parameters := parameters) rename)
  equalPairs : ∀ index : Fin parameters.decoder.roots.length, index.val < count →
    DirectionPair state [negate (nativeFaultyFirstFlag (parameters := parameters) rename)]
      (nativeRootLiteral rename .healthy index) (nativeRootLiteral rename .faulty index)
  outputPairs : ∀ index : Fin parameters.decoder.roots.length, index.val < count →
    DirectionPair state (compiledQualifierOutputs (parameters := parameters) rename)
      (nativeRootLiteral rename .healthy index) (nativeRootLiteral rename .faulty index)

def SelectorOutputAccumulator.prefix (program : SelectorOutputAccumulator (parameters := parameters)
    rename drive count) : SourcePrefix (parameters := parameters) rename :=
  (nativeHealthyPhysicalPrefix rename drive).extend program.state program.steps program.checked

def selectorOutputInitial (rename : Nat → Fin v) (drive : parameters.drive = true) :
    SelectorOutputAccumulator (parameters := parameters) rename drive 0 :=
  let actual := nativePhysicalSelectorActivation rename drive
  ⟨actual.state, actual.steps, actual.checked, actual.result,
    fun index impossible => False.elim (Nat.not_lt_zero index.val impossible),
    fun index impossible => False.elim (Nat.not_lt_zero index.val impossible)⟩

def selectorEqualPairAt (rename : Nat → Fin v) (drive : parameters.drive = true)
    (prior : SelectorOutputAccumulator (parameters := parameters) rename drive count)
    (index : Fin parameters.decoder.roots.length) :
    PairedProjection prior.state [negate (nativeFaultyFirstFlag (parameters := parameters) rename)]
      (nativeRootLiteral rename .healthy index) (nativeRootLiteral rename .faulty index) 2 :=
  pairedPhysicalGuardDischarge prior.state (nativeHealthyFirstFlag (parameters := parameters) rename) _ _
    [negate (nativeFaultyFirstFlag (parameters := parameters) rename)]
    (FoldProjection.afterTrace (nativeHealthyPhysicalUnit rename drive) prior.state prior.steps prior.checked)
    ((nativeHealthyEqualRoot rename drive index).afterTrace prior.state prior.steps prior.checked)

def selectorOutputAdvance (rename : Nat → Fin v) (drive : parameters.drive = true)
    (count : Nat) (before : count < parameters.decoder.roots.length)
    (prior : SelectorOutputAccumulator (parameters := parameters) rename drive count) :
    SelectorOutputAccumulator (parameters := parameters) rename drive (count + 1) := by
  let selected : Fin parameters.decoder.roots.length := ⟨count, before⟩
  let equal := selectorEqualPairAt rename drive prior selected
  let firstSteps := prior.steps ++ equal.steps
  have firstChecked : runSteps (nativeHealthyPhysicalPrefix rename drive).state firstSteps =
      some equal.state := by rw [runSteps_append, prior.checked]; exact equal.checked
  let output := pairedPhysicalGuardDischarge equal.state
    (nativeHealthyFirstFlag (parameters := parameters) rename) _ _
    (compiledQualifierOutputs (parameters := parameters) rename)
    (FoldProjection.afterTrace (nativeHealthyPhysicalUnit rename drive) equal.state firstSteps firstChecked)
    ((nativeHealthyPhysicalRoot rename drive selected).afterTrace equal.state firstSteps firstChecked)
  refine ⟨output.state, firstSteps ++ output.steps, ?_,
    FoldProjection.afterTrace (FoldProjection.afterTrace prior.activation equal.state equal.steps equal.checked)
      output.state output.steps output.checked, ?_, ?_⟩
  · rw [runSteps_append, firstChecked]; exact output.checked
  · intro query below
    by_cases same : query = selected
    · subst query
      exact equal.pair.afterTrace output.state output.steps output.checked
    · have earlier : query.val < count := by
        have different : query.val ≠ count := by
          intro h; apply same; exact Fin.ext h
        omega
      exact ((prior.equalPairs query earlier).afterTrace equal.state equal.steps equal.checked).afterTrace
        output.state output.steps output.checked
  · intro query below
    by_cases same : query = selected
    · subst query; exact output.pair
    · have earlier : query.val < count := by
        have different : query.val ≠ count := by
          intro h; apply same; exact Fin.ext h
        omega
      exact ((prior.outputPairs query earlier).afterTrace equal.state equal.steps equal.checked).afterTrace
        output.state output.steps output.checked

def buildSelectorOutputs (rename : Nat → Fin v) (drive : parameters.drive = true)
    (count : Nat) (bound : count ≤ parameters.decoder.roots.length) :
    SelectorOutputAccumulator (parameters := parameters) rename drive count :=
  match count with
  | 0 => selectorOutputInitial rename drive
  | count + 1 => selectorOutputAdvance rename drive count (by omega)
      (buildSelectorOutputs rename drive count (by omega))

def selectorOutputProgram (rename : Nat → Fin v) (drive : parameters.drive = true) :
    SelectorOutputAccumulator (parameters := parameters) rename drive parameters.decoder.roots.length :=
  buildSelectorOutputs rename drive parameters.decoder.roots.length (Nat.le_refl _)

/-- Replay starts at the original native formula; the activation projection is
emitted only by the initial accumulator and is retained through each root. -/
theorem selectorOutputProgram_checked (rename : Nat → Fin v) (drive : parameters.drive = true) :
    runSteps (initialState (relabel rename (formula parameters)))
      (selectorOutputProgram rename drive).prefix.steps =
      some (selectorOutputProgram rename drive).state :=
  (selectorOutputProgram rename drive).prefix.checked


theorem selectorOutputAdvance_count (rename : Nat → Fin v) (drive : parameters.drive = true)
    (count : Nat) (before : count < parameters.decoder.roots.length)
    (prior : SelectorOutputAccumulator (parameters := parameters) rename drive count) :
    (selectorOutputAdvance rename drive count before prior).steps.length ≤ prior.steps.length + 4 := by
  let selected : Fin parameters.decoder.roots.length := ⟨count, before⟩
  let equal := selectorEqualPairAt rename drive prior selected
  let firstSteps := prior.steps ++ equal.steps
  have firstChecked : runSteps (nativeHealthyPhysicalPrefix rename drive).state firstSteps =
      some equal.state := by rw [runSteps_append, prior.checked]; exact equal.checked
  let output := pairedPhysicalGuardDischarge equal.state
    (nativeHealthyFirstFlag (parameters := parameters) rename) _ _
    (compiledQualifierOutputs (parameters := parameters) rename)
    (FoldProjection.afterTrace (nativeHealthyPhysicalUnit rename drive) equal.state firstSteps firstChecked)
    ((nativeHealthyPhysicalRoot rename drive selected).afterTrace equal.state firstSteps firstChecked)
  have one := equal.count
  have two := output.count
  change (firstSteps ++ output.steps).length ≤ prior.steps.length + 4
  dsimp only [firstSteps]
  simp only [List.length_append]
  omega

theorem buildSelectorOutputs_count (rename : Nat → Fin v) (drive : parameters.drive = true)
    (count : Nat) (bound : count ≤ parameters.decoder.roots.length) :
    (buildSelectorOutputs rename drive count bound).steps.length ≤ 1 + 4 * count := by
  induction count with
  | zero =>
      exact (nativePhysicalSelectorActivation rename drive).count
  | succ count ih =>
      exact (selectorOutputAdvance_count rename drive count (by omega)
        (buildSelectorOutputs rename drive count (by omega))).trans (by
          have prior := ih (by omega)
          omega)

theorem selectorEqualPairAt_supported (rename : Nat → Fin v) (drive : parameters.drive = true)
    (prior : SelectorOutputAccumulator (parameters := parameters) rename drive count)
    (index : Fin parameters.decoder.roots.length)
    (supported : SourceDecoderSchedule.PrefixOriginalSupport rename prior.prefix) :
    let actual := selectorEqualPairAt rename drive prior index
    SourceDecoderSchedule.PrefixOriginalSupport rename
      (prior.prefix.extend actual.state actual.steps actual.checked) ∧
    SourceDecoderSchedule.DirectionPairOrigin rename
      (prior.prefix.extend actual.state actual.steps actual.checked) actual.pair := by
  have unitOrigin := resultOrigin_append_right (formula parameters).clauses.size
    (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
    (nativeHealthyPhysicalPrefix rename drive).steps prior.steps
    (nativeHealthyPhysicalUnit rename drive).row.id (nativeHealthyPhysicalUnit_origin rename drive)
  have pairOrigin := SourceDecoderSchedule.DirectionPairOrigin.afterTrace rename
    (nativeHealthyPhysicalPrefix rename drive) (nativeHealthyEqualRoot rename drive index)
    (nativeHealthyEqualRoot_supported rename drive index) prior.state prior.steps prior.checked
  exact pairedPhysicalGuardDischarge_supported rename prior.prefix
    (nativeHealthyFirstFlag (parameters := parameters) rename) _ _
    [negate (nativeFaultyFirstFlag (parameters := parameters) rename)] _ _
    supported unitOrigin pairOrigin


theorem selectorOutputInitial_supported (rename : Nat → Fin v) (drive : parameters.drive = true) :
    SourceDecoderSchedule.PrefixOriginalSupport rename (selectorOutputInitial rename drive).prefix := by
  exact (nativePhysicalSelectorActivation_supported rename drive).1

theorem selectorOutputAdvance_supported (rename : Nat → Fin v) (drive : parameters.drive = true)
    (count : Nat) (before : count < parameters.decoder.roots.length)
    (prior : SelectorOutputAccumulator (parameters := parameters) rename drive count)
    (supported : SourceDecoderSchedule.PrefixOriginalSupport rename prior.prefix) :
    SourceDecoderSchedule.PrefixOriginalSupport rename
      (selectorOutputAdvance rename drive count before prior).prefix := by
  let selected : Fin parameters.decoder.roots.length := ⟨count, before⟩
  let equal := selectorEqualPairAt rename drive prior selected
  let firstSteps := prior.steps ++ equal.steps
  have firstChecked : runSteps (nativeHealthyPhysicalPrefix rename drive).state firstSteps =
      some equal.state := by rw [runSteps_append, prior.checked]; exact equal.checked
  let current := (nativeHealthyPhysicalPrefix rename drive).extend equal.state firstSteps firstChecked
  have currentSupported : SourceDecoderSchedule.PrefixOriginalSupport rename current := by
    simpa only [current, firstSteps, SelectorOutputAccumulator.prefix, SourcePrefix.extend,
      SourceDecoderSchedule.PrefixOriginalSupport, List.append_assoc] using
      (selectorEqualPairAt_supported rename drive prior selected supported).1
  have unitOrigin := resultOrigin_append_right (formula parameters).clauses.size
    (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
    (nativeHealthyPhysicalPrefix rename drive).steps firstSteps
    (nativeHealthyPhysicalUnit rename drive).row.id (nativeHealthyPhysicalUnit_origin rename drive)
  have pairOrigin := SourceDecoderSchedule.DirectionPairOrigin.afterTrace rename
    (nativeHealthyPhysicalPrefix rename drive) (nativeHealthyPhysicalRoot rename drive selected)
    (nativeHealthyPhysicalRoot_supported rename drive selected) equal.state firstSteps firstChecked
  have outputSupported := pairedPhysicalGuardDischarge_supported rename current
    (nativeHealthyFirstFlag (parameters := parameters) rename) _ _
    (compiledQualifierOutputs (parameters := parameters) rename)
    (FoldProjection.afterTrace (nativeHealthyPhysicalUnit rename drive) equal.state firstSteps firstChecked)
    ((nativeHealthyPhysicalRoot rename drive selected).afterTrace equal.state firstSteps firstChecked)
    currentSupported unitOrigin pairOrigin
  simpa only [selectorOutputAdvance, SelectorOutputAccumulator.prefix, current, firstSteps,
    selected, equal, SourcePrefix.extend, SourceDecoderSchedule.PrefixOriginalSupport,
    List.append_assoc] using outputSupported.1

theorem buildSelectorOutputs_supported (rename : Nat → Fin v) (drive : parameters.drive = true)
    (count : Nat) (bound : count ≤ parameters.decoder.roots.length) :
    SourceDecoderSchedule.PrefixOriginalSupport rename
      (buildSelectorOutputs rename drive count bound).prefix := by
  induction count with
  | zero => exact selectorOutputInitial_supported rename drive
  | succ count ih =>
      change SourceDecoderSchedule.PrefixOriginalSupport rename
        (selectorOutputAdvance rename drive count (by omega)
          (buildSelectorOutputs rename drive count (by omega))).prefix
      exact selectorOutputAdvance_supported rename drive count (by omega)
        (buildSelectorOutputs rename drive count (by omega)) (ih (by omega))

theorem selectorOutputProgram_supported (rename : Nat → Fin v) (drive : parameters.drive = true) :
    SourceDecoderSchedule.PrefixOriginalSupport rename (selectorOutputProgram rename drive).prefix :=
  buildSelectorOutputs_supported rename drive parameters.decoder.roots.length (Nat.le_refl _)


theorem selectorOutputProgram_count (rename : Nat → Fin v) (drive : parameters.drive = true) :
    (selectorOutputProgram rename drive).prefix.steps.length ≤
      nativeOutputMacroBudget parameters.decoder.countedSize parameters.buses + 3 +
        4 * parameters.decoder.roots.length := by
  have base := nativeHealthyPhysicalPrefix_count rename drive
  have suffix : (selectorOutputProgram rename drive).steps.length ≤
      1 + 4 * parameters.decoder.roots.length :=
    buildSelectorOutputs_count rename drive parameters.decoder.roots.length (Nat.le_refl _)
  change ((nativeHealthyPhysicalPrefix rename drive).steps ++
    (selectorOutputProgram rename drive).steps).length ≤ _
  simp only [List.length_append]
  omega

/-- Every step of the physical selector/output schedule has an ordered local
RUP tree using original rows or strictly earlier steps of the same schedule. -/
theorem selectorOutputProgram_localCaseCatalogue (rename : Nat → Fin v)
    (drive : parameters.drive = true) :
    ∃ records,
      resolutionRupSchedule (initialState (relabel rename (formula parameters)))
        (selectorOutputProgram rename drive).prefix.steps = some records ∧
      records.map ResolutionRupInvocation.step = (selectorOutputProgram rename drive).prefix.steps ∧
      records.length ≤ nativeOutputMacroBudget parameters.decoder.countedSize parameters.buses + 3 +
        4 * parameters.decoder.roots.length ∧
      ∀ record ∈ records,
        Controller.Resolution.Cases.ValidTree record.base record.step.clause record.tree ∧
        (splitVariables record.tree).card ≤ 5 ∧
        ∀ parent ∈ treeParentIds record.tree,
          (parent ≤ (formula parameters).clauses.size →
            SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename parent) ∧
          ((formula parameters).clauses.size < parent →
            ∃ earlier ∈ (selectorOutputProgram rename drive).prefix.steps,
              earlier.id = parent ∧ earlier.id < record.step.id) := by
  obtain ⟨records, run, count, sound⟩ :=
    SourcePrefix.resolutionRupSchedule_sound rename (selectorOutputProgram rename drive).prefix
  have exactSteps := (resolutionRupSchedule_steps _ _ records run).1
  have exactTargets := resolutionRupSchedule_targets _ _ records run
  have parents := resolutionRupSchedule_parentSupport _ _
    (initialState (relabel rename (formula parameters)))
    (selectorOutputProgram rename drive).prefix.steps records run (selectorOutputProgram_supported rename drive)
  refine ⟨records, run, exactSteps,
    count.le.trans (selectorOutputProgram_count rename drive), ?_⟩
  intro record member
  have valid : Controller.Resolution.Cases.ValidTree record.base record.step.clause record.tree := by
    rw [← exactTargets record member]
    exact (sound record member).1
  refine ⟨valid, ?_, parents record member⟩
  rw [(sound record member).2.1]
  simp


/-- The false-drive physical equations force both NOT-product first flags true. -/
def driveZeroFlagSource (rename : Nat → Fin v) (drive : parameters.drive = false) (side : Side) :
    SubclauseProjection (initialState (relabel rename (formula parameters)))
      [mapLiteral rename (sourceRoleMap parameters (.internal (.flag side parameters.firstBus)))] 2 := by
  cases side with
  | healthy =>
      let actual := SourceDriveZero.healthyFlagFromDriveZero (parameters := parameters) rename drive
      refine ⟨actual.state, actual.steps, actual.checked, retarget actual.result ?_, actual.count⟩
      intro literal member
      simpa only [SourceMismatchHandles.healthyFlag_handle] using member
  | faulty =>
      let actual := SourceDriveZero.faultyFlagFromDriveZero (parameters := parameters) rename drive
      refine ⟨actual.state, actual.steps, actual.checked, retarget actual.result ?_, actual.count⟩
      intro literal member
      simpa only [SourceMismatchSeed.faultyFlag_handle] using member

def driveZeroFlagPrefix (rename : Nat → Fin v) (drive : parameters.drive = false) (side : Side) :
    SourcePrefix (parameters := parameters) rename :=
  (SourcePrefix.initial (parameters := parameters) rename).extend
    (driveZeroFlagSource rename drive side).state (driveZeroFlagSource rename drive side).steps
    (driveZeroFlagSource rename drive side).checked

theorem driveZeroFlagSource_supported (rename : Nat → Fin v) (drive : parameters.drive = false)
    (side : Side) :
    SourceDecoderSchedule.ProjectionOriginalSupport rename (SourcePrefix.initial (parameters := parameters) rename)
      (driveZeroFlagSource rename drive side) := by
  cases side with
  | healthy =>
      have actual := SourceDriveZero.healthyFlagFromDriveZero_supported (parameters := parameters) rename drive
      constructor
      · exact prefix_controller_to_decoder rename (driveZeroFlagPrefix rename drive .healthy) actual.1
      · exact resultOrigin_controller_to_decoder rename _ _ actual.2
  | faulty =>
      have actual := SourceDriveZero.faultyFlagFromDriveZero_supported (parameters := parameters) rename drive
      constructor
      · exact prefix_controller_to_decoder rename (driveZeroFlagPrefix rename drive .faulty) actual.1
      · exact resultOrigin_controller_to_decoder rename _ _ actual.2

def driveZeroEqualPrefix (rename : Nat → Fin v) : SourcePrefix (parameters := parameters) rename :=
  (equalDecoderProgram (parameters := parameters) rename true).table.prefixState

def driveZeroHealthyReplay (rename : Nat → Fin v) (drive : parameters.drive = false) :
    NativeReplay (parameters := parameters) rename (driveZeroEqualPrefix rename)
      (driveZeroFlagPrefix rename drive .healthy).state (driveZeroFlagPrefix rename drive .healthy).steps :=
  replayNativeProgram rename (driveZeroEqualPrefix rename)
    (driveZeroFlagPrefix rename drive .healthy).state (driveZeroFlagPrefix rename drive .healthy).steps
    (driveZeroFlagPrefix rename drive .healthy).checked

def driveZeroFaultyReplay (rename : Nat → Fin v) (drive : parameters.drive = false) :
    NativeReplay (parameters := parameters) rename (driveZeroHealthyReplay rename drive).prefix
      (driveZeroFlagPrefix rename drive .faulty).state (driveZeroFlagPrefix rename drive .faulty).steps :=
  replayNativeProgram rename (driveZeroHealthyReplay rename drive).prefix
    (driveZeroFlagPrefix rename drive .faulty).state (driveZeroFlagPrefix rename drive .faulty).steps
    (driveZeroFlagPrefix rename drive .faulty).checked

def driveZeroPhysicalPrefix (rename : Nat → Fin v) (drive : parameters.drive = false) :
    SourcePrefix (parameters := parameters) rename := (driveZeroFaultyReplay rename drive).prefix

def driveZeroHealthyUnit (rename : Nat → Fin v) (drive : parameters.drive = false) :
    AvailableSubclause (driveZeroPhysicalPrefix rename drive).state
      [nativeHealthyFirstFlag (parameters := parameters) rename] :=
  FoldProjection.afterTrace
    ⟨(driveZeroFlagSource rename drive .healthy).result.clause,
      (driveZeroHealthyReplay rename drive).available (driveZeroFlagSource rename drive .healthy).result.row,
      (driveZeroFlagSource rename drive .healthy).result.subset⟩
    (driveZeroFaultyReplay rename drive).next (driveZeroFaultyReplay rename drive).added
    (driveZeroFaultyReplay rename drive).checked

def driveZeroFaultyUnit (rename : Nat → Fin v) (drive : parameters.drive = false) :
    AvailableSubclause (driveZeroPhysicalPrefix rename drive).state
      [nativeFaultyFirstFlag (parameters := parameters) rename] :=
  ⟨(driveZeroFlagSource rename drive .faulty).result.clause,
    (driveZeroFaultyReplay rename drive).available (driveZeroFlagSource rename drive .faulty).result.row,
    (driveZeroFlagSource rename drive .faulty).result.subset⟩

theorem driveZeroPhysicalPrefix_supported (rename : Nat → Fin v) (drive : parameters.drive = false) :
    SourceDecoderSchedule.PrefixOriginalSupport rename (driveZeroPhysicalPrefix rename drive) := by
  have healthySource : SourceDecoderSchedule.PrefixOriginalSupport rename
      (driveZeroFlagPrefix rename drive .healthy) := by
    exact (driveZeroFlagSource_supported rename drive .healthy).1
  have faultySource : SourceDecoderSchedule.PrefixOriginalSupport rename
      (driveZeroFlagPrefix rename drive .faulty) := by
    exact (driveZeroFlagSource_supported rename drive .faulty).1
  have first := NativeReplay.prefix_supported rename (driveZeroEqualPrefix rename)
    (driveZeroFlagPrefix rename drive .healthy) (driveZeroHealthyReplay rename drive)
    (equalDecoderProgram_supported (parameters := parameters) rename true).1.1 healthySource
  exact NativeReplay.prefix_supported rename (driveZeroHealthyReplay rename drive).prefix
    (driveZeroFlagPrefix rename drive .faulty) (driveZeroFaultyReplay rename drive) first faultySource

def driveZeroGuardedRoot (rename : Nat → Fin v) (drive : parameters.drive = false)
    (index : Fin parameters.decoder.roots.length) :
    DirectionPair (driveZeroPhysicalPrefix rename drive).state
      [negate (nativeHealthyFirstFlag (parameters := parameters) rename),
       negate (nativeFaultyFirstFlag (parameters := parameters) rename)]
      (nativeRootLiteral rename .healthy index) (nativeRootLiteral rename .faulty index) :=
  ((compiledEqualDecoderRoot rename true index).afterTrace
    (driveZeroHealthyReplay rename drive).next (driveZeroHealthyReplay rename drive).added
    (driveZeroHealthyReplay rename drive).checked).afterTrace
    (driveZeroFaultyReplay rename drive).next (driveZeroFaultyReplay rename drive).added
    (driveZeroFaultyReplay rename drive).checked


theorem driveZeroPhysicalPrefix_count (rename : Nat → Fin v) (drive : parameters.drive = false) :
    (driveZeroPhysicalPrefix rename drive).steps.length ≤ equalDecoderProgramBudget parameters + 4 := by
  have base := equalDecoderProgram_count (parameters := parameters) rename true
  have healthy : (driveZeroHealthyReplay rename drive).added.length ≤ 2 := by
    rw [(driveZeroHealthyReplay rename drive).added_length]
    simpa only [driveZeroFlagPrefix, SourcePrefix.extend, SourcePrefix.initial, List.nil_append] using
      (driveZeroFlagSource rename drive .healthy).count
  have faulty : (driveZeroFaultyReplay rename drive).added.length ≤ 2 := by
    rw [(driveZeroFaultyReplay rename drive).added_length]
    simpa only [driveZeroFlagPrefix, SourcePrefix.extend, SourcePrefix.initial, List.nil_append] using
      (driveZeroFlagSource rename drive .faulty).count
  simp only [driveZeroPhysicalPrefix, NativeReplay.prefix, SourcePrefix.extend, List.length_append]
  change (driveZeroEqualPrefix (parameters := parameters) rename).steps.length +
      (driveZeroHealthyReplay rename drive).added.length +
      (driveZeroFaultyReplay rename drive).added.length ≤ _
  dsimp only [driveZeroEqualPrefix] at ⊢
  exact (Nat.add_le_add (Nat.add_le_add base healthy) faulty).trans (by omega)

structure DriveZeroOutputAccumulator (rename : Nat → Fin v) (drive : parameters.drive = false)
    (count : Nat) where
  state : State v
  steps : List (Step v)
  checked : runSteps (driveZeroPhysicalPrefix rename drive).state steps = some state
  pairs : ∀ index : Fin parameters.decoder.roots.length, index.val < count →
    DirectionPair state []
      (nativeRootLiteral rename .healthy index) (nativeRootLiteral rename .faulty index)

def DriveZeroOutputAccumulator.prefix {drive : parameters.drive = false}
    (program : DriveZeroOutputAccumulator (parameters := parameters)
    rename drive count) : SourcePrefix (parameters := parameters) rename :=
  (driveZeroPhysicalPrefix rename drive).extend program.state program.steps program.checked

def driveZeroOutputInitial (rename : Nat → Fin v) (drive : parameters.drive = false) :
    DriveZeroOutputAccumulator (parameters := parameters) rename drive 0 :=
  ⟨(driveZeroPhysicalPrefix rename drive).state, [], rfl,
    fun index impossible => False.elim (Nat.not_lt_zero index.val impossible)⟩

def driveZeroOutputPairAt (rename : Nat → Fin v) (drive : parameters.drive = false)
    (prior : DriveZeroOutputAccumulator (parameters := parameters) rename drive count)
    (index : Fin parameters.decoder.roots.length) :
    PairedProjection prior.state []
      (nativeRootLiteral rename .healthy index) (nativeRootLiteral rename .faulty index) 4 := by
  let first := pairedPhysicalGuardDischarge prior.state
    (nativeHealthyFirstFlag (parameters := parameters) rename) _ _
    [negate (nativeFaultyFirstFlag (parameters := parameters) rename)]
    (FoldProjection.afterTrace (driveZeroHealthyUnit rename drive) prior.state prior.steps prior.checked)
    ((driveZeroGuardedRoot rename drive index).afterTrace prior.state prior.steps prior.checked)
  let second := pairedPhysicalGuardDischarge first.state
    (nativeFaultyFirstFlag (parameters := parameters) rename) _ _ []
    (FoldProjection.afterTrace
      (FoldProjection.afterTrace (driveZeroFaultyUnit rename drive) prior.state prior.steps prior.checked)
      first.state first.steps first.checked) first.pair
  refine ⟨second.state, first.steps ++ second.steps, ?_, second.pair, ?_⟩
  · rw [runSteps_append, first.checked]; exact second.checked
  · have one := first.count
    have two := second.count
    simp only [List.length_append]
    omega
def driveZeroOutputAdvanceKernel (rename : Nat → Fin v) (drive : parameters.drive = false)
    (count : Nat) (before : count < parameters.decoder.roots.length)
    (prior : DriveZeroOutputAccumulator (parameters := parameters) rename drive count)
    (added : PairedProjection prior.state []
      (nativeRootLiteral rename .healthy ⟨count, before⟩)
      (nativeRootLiteral rename .faulty ⟨count, before⟩) 4) :
    DriveZeroOutputAccumulator (parameters := parameters) rename drive (count + 1) := by
  let selected : Fin parameters.decoder.roots.length := ⟨count, before⟩
  refine ⟨added.state, prior.steps ++ added.steps, ?_, ?_⟩
  · rw [runSteps_append, prior.checked]
    exact added.checked
  · intro query below
    by_cases same : query = selected
    · subst query
      exact added.pair
    · have earlier : query.val < count := by
        have different : query.val ≠ count := by
          intro equal
          apply same
          apply Fin.ext
          exact equal
        omega
      exact (prior.pairs query earlier).afterTrace added.state added.steps added.checked

def driveZeroOutputAdvance (rename : Nat → Fin v) (drive : parameters.drive = false)
    (count : Nat) (before : count < parameters.decoder.roots.length)
    (prior : DriveZeroOutputAccumulator (parameters := parameters) rename drive count) :
    DriveZeroOutputAccumulator (parameters := parameters) rename drive (count + 1) :=
  driveZeroOutputAdvanceKernel rename drive count before prior
    (driveZeroOutputPairAt rename drive prior ⟨count, before⟩)

def buildDriveZeroOutputs (rename : Nat → Fin v) (drive : parameters.drive = false)
    (count : Nat) (bound : count ≤ parameters.decoder.roots.length) :
    DriveZeroOutputAccumulator (parameters := parameters) rename drive count :=
  match count with
  | 0 => driveZeroOutputInitial rename drive
  | count + 1 => driveZeroOutputAdvance rename drive count (by omega)
      (buildDriveZeroOutputs rename drive count (by omega))

theorem buildDriveZeroOutputs_count (rename : Nat → Fin v) (drive : parameters.drive = false)
    (count : Nat) (bound : count ≤ parameters.decoder.roots.length) :
    (buildDriveZeroOutputs rename drive count bound).steps.length ≤ 4 * count := by
  induction count with
  | zero => exact Nat.zero_le _
  | succ count ih =>
    have prior := ih (by omega)
    have added := (driveZeroOutputPairAt rename drive
      (buildDriveZeroOutputs rename drive count (by omega)) ⟨count, by omega⟩).count
    change ((buildDriveZeroOutputs rename drive count (by omega)).steps ++
      (driveZeroOutputPairAt rename drive
        (buildDriveZeroOutputs rename drive count (by omega)) ⟨count, by omega⟩).steps).length ≤ _
    simp only [List.length_append]
    omega

def driveZeroOutputProgram (rename : Nat → Fin v) (drive : parameters.drive = false) :
    DriveZeroOutputAccumulator (parameters := parameters) rename drive parameters.decoder.roots.length :=
  buildDriveZeroOutputs rename drive parameters.decoder.roots.length (Nat.le_refl _)

def driveZeroOutputPrefix (rename : Nat → Fin v) (drive : parameters.drive = false) :
    SourcePrefix (parameters := parameters) rename :=
  (driveZeroOutputProgram rename drive).prefix

def driveZeroOutputRoot (rename : Nat → Fin v) (drive : parameters.drive = false)
    (index : Fin parameters.decoder.roots.length) :
    DirectionPair (driveZeroOutputPrefix rename drive).state
      []
      (nativeRootLiteral rename .healthy index) (nativeRootLiteral rename .faulty index) :=
  (driveZeroOutputProgram rename drive).pairs index index.isLt



theorem driveZeroHealthyUnit_origin (rename : Nat → Fin v) (drive : parameters.drive = false) :
    SourceMismatchHandles.ResultOrigin (formula parameters).clauses.size
      (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
      (driveZeroPhysicalPrefix rename drive).steps (driveZeroHealthyUnit rename drive).row.id := by
  have original := (driveZeroFlagSource_supported rename drive .healthy).2
  have mapped := rebase_native_result_origin rename
    ((driveZeroEqualPrefix (parameters := parameters) rename).state.lastId - (formula parameters).clauses.size)
    (driveZeroFlagPrefix rename drive .healthy).steps
    (driveZeroFlagSource rename drive .healthy).result.row.id original
  have first := resultOrigin_append_left _ _ (driveZeroEqualPrefix (parameters := parameters) rename).steps
    (driveZeroHealthyReplay rename drive).added _ mapped
  exact resultOrigin_append_right _ _ (driveZeroHealthyReplay rename drive).prefix.steps
    (driveZeroFaultyReplay rename drive).added _ first

theorem driveZeroFaultyUnit_origin (rename : Nat → Fin v) (drive : parameters.drive = false) :
    SourceMismatchHandles.ResultOrigin (formula parameters).clauses.size
      (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
      (driveZeroPhysicalPrefix rename drive).steps (driveZeroFaultyUnit rename drive).row.id := by
  have original := (driveZeroFlagSource_supported rename drive .faulty).2
  have mapped := rebase_native_result_origin rename
    ((driveZeroHealthyReplay rename drive).prefix.state.lastId - (formula parameters).clauses.size)
    (driveZeroFlagPrefix rename drive .faulty).steps
    (driveZeroFlagSource rename drive .faulty).result.row.id original
  exact resultOrigin_append_left _ _ (driveZeroHealthyReplay rename drive).prefix.steps
    (driveZeroFaultyReplay rename drive).added _ mapped

theorem driveZeroGuardedRoot_supported (rename : Nat → Fin v) (drive : parameters.drive = false)
    (index : Fin parameters.decoder.roots.length) :
    SourceDecoderSchedule.DirectionPairOrigin rename (driveZeroPhysicalPrefix rename drive)
      (driveZeroGuardedRoot rename drive index) := by
  have first := SourceDecoderSchedule.DirectionPairOrigin.afterTrace rename
    (driveZeroEqualPrefix (parameters := parameters) rename) (compiledEqualDecoderRoot rename true index)
    (compiledEqualDecoderRoot_supported rename true index)
    (driveZeroHealthyReplay rename drive).next (driveZeroHealthyReplay rename drive).added
    (driveZeroHealthyReplay rename drive).checked
  exact SourceDecoderSchedule.DirectionPairOrigin.afterTrace rename
    (driveZeroHealthyReplay rename drive).prefix _ first
    (driveZeroFaultyReplay rename drive).next (driveZeroFaultyReplay rename drive).added
    (driveZeroFaultyReplay rename drive).checked

def DriveZeroOutputAccumulatorOriginals (rename : Nat → Fin v) (drive : parameters.drive = false)
    (count : Nat) (program : DriveZeroOutputAccumulator (parameters := parameters) rename drive count) : Prop :=
  SourceDecoderSchedule.PrefixOriginalSupport rename program.prefix ∧
    ∀ index : Fin parameters.decoder.roots.length, ∀ before : index.val < count,
      SourceDecoderSchedule.DirectionPairOrigin rename program.prefix (program.pairs index before)

theorem driveZeroOutputInitial_originals (rename : Nat → Fin v) (drive : parameters.drive = false) :
    DriveZeroOutputAccumulatorOriginals rename drive 0 (driveZeroOutputInitial rename drive) := by
  constructor
  · simpa only [driveZeroOutputInitial, DriveZeroOutputAccumulator.prefix, SourcePrefix.extend,
      SourceDecoderSchedule.PrefixOriginalSupport, List.append_nil] using
      driveZeroPhysicalPrefix_supported rename drive
  · intro index impossible
    exact False.elim (Nat.not_lt_zero index.val impossible)

theorem driveZeroOutputPairAt_supported (rename : Nat → Fin v) (drive : parameters.drive = false)
    (count : Nat) (prior : DriveZeroOutputAccumulator (parameters := parameters) rename drive count)
    (index : Fin parameters.decoder.roots.length)
    (supported : SourceDecoderSchedule.PrefixOriginalSupport rename prior.prefix) :
    let added := driveZeroOutputPairAt rename drive prior index
    SourceDecoderSchedule.PrefixOriginalSupport rename
      (prior.prefix.extend added.state added.steps added.checked) ∧
    SourceDecoderSchedule.DirectionPairOrigin rename
      (prior.prefix.extend added.state added.steps added.checked) added.pair := by
  let healthy := FoldProjection.afterTrace (driveZeroHealthyUnit rename drive) prior.state prior.steps prior.checked
  let faulty := FoldProjection.afterTrace (driveZeroFaultyUnit rename drive) prior.state prior.steps prior.checked
  let root := (driveZeroGuardedRoot rename drive index).afterTrace prior.state prior.steps prior.checked
  have healthyOrigin := resultOrigin_append_right _ _
    (driveZeroPhysicalPrefix rename drive).steps prior.steps _ (driveZeroHealthyUnit_origin rename drive)
  have faultyOrigin := resultOrigin_append_right _ _
    (driveZeroPhysicalPrefix rename drive).steps prior.steps _ (driveZeroFaultyUnit_origin rename drive)
  have rootOrigin := SourceDecoderSchedule.DirectionPairOrigin.afterTrace rename
    (driveZeroPhysicalPrefix rename drive) (driveZeroGuardedRoot rename drive index)
    (driveZeroGuardedRoot_supported rename drive index) prior.state prior.steps prior.checked
  let first := pairedPhysicalGuardDischarge prior.state
    (nativeHealthyFirstFlag (parameters := parameters) rename) _ _
    [negate (nativeFaultyFirstFlag (parameters := parameters) rename)] healthy root
  have one := pairedPhysicalGuardDischarge_supported rename prior.prefix
    (nativeHealthyFirstFlag (parameters := parameters) rename) _ _
    [negate (nativeFaultyFirstFlag (parameters := parameters) rename)] healthy root
    supported healthyOrigin rootOrigin
  let current := prior.prefix.extend first.state first.steps first.checked
  let nextFaulty := FoldProjection.afterTrace faulty first.state first.steps first.checked
  have nextFaultyOrigin := resultOrigin_append_right _ _ prior.prefix.steps first.steps _ faultyOrigin
  let second := pairedPhysicalGuardDischarge first.state
    (nativeFaultyFirstFlag (parameters := parameters) rename) _ _ [] nextFaulty first.pair
  have two := pairedPhysicalGuardDischarge_supported rename current
    (nativeFaultyFirstFlag (parameters := parameters) rename) _ _ [] nextFaulty first.pair
    one.1 nextFaultyOrigin one.2
  let finished := prior.prefix.extend second.state (first.steps ++ second.steps) (by
    change runSteps prior.state (first.steps ++ second.steps) = some second.state
    rw [runSteps_append, first.checked]; exact second.checked)
  have stepsEqual : current.steps ++ second.steps = finished.steps := by
    simp only [current, finished, SourcePrefix.extend, List.append_assoc]
  have carried := decoderPairOrigin_same_steps rename second.state
    (current.steps ++ second.steps) finished.steps stepsEqual
    (current.extend second.state second.steps second.checked).checked finished.checked second.pair two.2
  change SourceDecoderSchedule.PrefixOriginalSupport rename finished ∧
    SourceDecoderSchedule.DirectionPairOrigin rename finished second.pair
  refine ⟨?_, carried⟩
  simpa only [SourceDecoderSchedule.PrefixOriginalSupport, current, finished,
    SourcePrefix.extend, List.append_assoc] using two.1
theorem driveZeroOutputAdvanceKernel_supported (rename : Nat → Fin v) (drive : parameters.drive = false)
    (count : Nat) (before : count < parameters.decoder.roots.length)
    (prior : DriveZeroOutputAccumulator (parameters := parameters) rename drive count)
    (added : PairedProjection prior.state []
      (nativeRootLiteral rename .healthy ⟨count, before⟩)
      (nativeRootLiteral rename .faulty ⟨count, before⟩) 4)
    (priorOriginal : DriveZeroOutputAccumulatorOriginals rename drive count prior)
    (addedOriginal : SourceDecoderSchedule.PrefixOriginalSupport rename
        (prior.prefix.extend added.state added.steps added.checked) ∧
      SourceDecoderSchedule.DirectionPairOrigin rename
        (prior.prefix.extend added.state added.steps added.checked) added.pair) :
    DriveZeroOutputAccumulatorOriginals rename drive (count + 1)
      (driveZeroOutputAdvanceKernel rename drive count before prior added) := by
  let finished := (driveZeroPhysicalPrefix rename drive).extend added.state
    (prior.steps ++ added.steps) (by rw [runSteps_append, prior.checked]; exact added.checked)
  have stepsEqual : prior.prefix.steps ++ added.steps = finished.steps := by
    simp only [DriveZeroOutputAccumulator.prefix, finished, SourcePrefix.extend, List.append_assoc]
  constructor
  · simpa only [SourceDecoderSchedule.PrefixOriginalSupport, driveZeroOutputAdvanceKernel,
      DriveZeroOutputAccumulator.prefix, SourcePrefix.extend, List.append_assoc] using addedOriginal.1
  · intro query below
    let selected : Fin parameters.decoder.roots.length := ⟨count, before⟩
    by_cases same : query = selected
    · subst query
      have carried := decoderPairOrigin_same_steps rename added.state
        (prior.prefix.steps ++ added.steps) finished.steps stepsEqual
        (prior.prefix.extend added.state added.steps added.checked).checked finished.checked
        added.pair addedOriginal.2
      simp only [driveZeroOutputAdvanceKernel, DriveZeroOutputAccumulator.prefix]
      dsimp only [SourcePrefix.extend]
      rw [dite_eq_left (show (⟨count, before⟩ : Fin parameters.decoder.roots.length) =
          ⟨count, before⟩ from rfl)]
      change SourceDecoderSchedule.DirectionPairOrigin rename finished added.pair
      exact carried
    · have earlier : query.val < count := by
        have different : query.val ≠ count := by
          intro equal
          apply same
          apply Fin.ext
          exact equal
        omega
      have origin := SourceDecoderSchedule.DirectionPairOrigin.afterTrace rename prior.prefix
        (prior.pairs query earlier) (priorOriginal.2 query earlier)
        added.state added.steps added.checked
      have carried := decoderPairOrigin_same_steps rename added.state
        (prior.prefix.steps ++ added.steps) finished.steps stepsEqual
        (prior.prefix.extend added.state added.steps added.checked).checked finished.checked
        ((prior.pairs query earlier).afterTrace added.state added.steps added.checked) origin
      simp only [driveZeroOutputAdvanceKernel, DriveZeroOutputAccumulator.prefix]
      dsimp only [SourcePrefix.extend]
      rw [dite_eq_right same]
      change SourceDecoderSchedule.DirectionPairOrigin rename finished
        ((prior.pairs query earlier).afterTrace added.state added.steps added.checked)
      exact carried

theorem driveZeroOutputAdvance_originals (rename : Nat → Fin v) (drive : parameters.drive = false)
    (count : Nat) (before : count < parameters.decoder.roots.length)
    (prior : DriveZeroOutputAccumulator (parameters := parameters) rename drive count)
    (original : DriveZeroOutputAccumulatorOriginals rename drive count prior) :
    DriveZeroOutputAccumulatorOriginals rename drive (count + 1)
      (driveZeroOutputAdvance rename drive count before prior) :=
  driveZeroOutputAdvanceKernel_supported rename drive count before prior
    (driveZeroOutputPairAt rename drive prior ⟨count, before⟩) original
    (driveZeroOutputPairAt_supported rename drive count prior ⟨count, before⟩ original.1)

theorem buildDriveZeroOutputs_originals (rename : Nat → Fin v) (drive : parameters.drive = false)
    (count : Nat) (bound : count ≤ parameters.decoder.roots.length) :
    DriveZeroOutputAccumulatorOriginals rename drive count
      (buildDriveZeroOutputs rename drive count bound) := by
  induction count with
  | zero => exact driveZeroOutputInitial_originals rename drive
  | succ count ih =>
    exact driveZeroOutputAdvance_originals rename drive count (by omega)
      (buildDriveZeroOutputs rename drive count (by omega)) (ih (by omega))

theorem driveZeroOutputPrefix_supported (rename : Nat → Fin v) (drive : parameters.drive = false) :
    SourceDecoderSchedule.PrefixOriginalSupport rename (driveZeroOutputPrefix rename drive) :=
  (buildDriveZeroOutputs_originals rename drive parameters.decoder.roots.length (Nat.le_refl _)).1

theorem driveZeroOutputRoot_supported (rename : Nat → Fin v) (drive : parameters.drive = false)
    (index : Fin parameters.decoder.roots.length) :
    SourceDecoderSchedule.DirectionPairOrigin rename (driveZeroOutputPrefix rename drive)
      (driveZeroOutputRoot rename drive index) :=
  (buildDriveZeroOutputs_originals rename drive parameters.decoder.roots.length (Nat.le_refl _)).2 index index.isLt



theorem driveZeroOutputPrefix_checked (rename : Nat → Fin v) (drive : parameters.drive = false) :
    runSteps (initialState (relabel rename (formula parameters)))
      (driveZeroOutputPrefix rename drive).steps = some (driveZeroOutputPrefix rename drive).state :=
  (driveZeroOutputPrefix rename drive).checked

theorem driveZeroOutputPrefix_count (rename : Nat → Fin v) (drive : parameters.drive = false) :
    (driveZeroOutputPrefix rename drive).steps.length ≤
      equalDecoderProgramBudget parameters + 4 + 4 * parameters.decoder.roots.length := by
  have base := driveZeroPhysicalPrefix_count rename drive
  have suffix := buildDriveZeroOutputs_count rename drive parameters.decoder.roots.length (Nat.le_refl _)
  change ((driveZeroPhysicalPrefix rename drive).steps ++
    (driveZeroOutputProgram rename drive).steps).length ≤ _
  simp only [List.length_append]
  exact Nat.add_le_add base suffix

theorem driveZeroOutputRoot_actual_conclusions (rename : Nat → Fin v) (drive : parameters.drive = false)
    (index : Fin parameters.decoder.roots.length) :
    let actual := driveZeroOutputRoot rename drive index
    (nativeRootLiteral rename .healthy index = nativeRootLiteral rename .faulty index ∨
      ∃ id clause, (driveZeroOutputPrefix rename drive).state.rows id = some clause ∧
        id ≤ (driveZeroOutputPrefix rename drive).state.lastId ∧
        ClauseSubset clause [negate (nativeRootLiteral rename .healthy index), nativeRootLiteral rename .faulty index]) ∧
    (nativeRootLiteral rename .faulty index = nativeRootLiteral rename .healthy index ∨
      ∃ id clause, (driveZeroOutputPrefix rename drive).state.rows id = some clause ∧
        id ≤ (driveZeroOutputPrefix rename drive).state.lastId ∧
        ClauseSubset clause [negate (nativeRootLiteral rename .faulty index), nativeRootLiteral rename .healthy index]) :=
  ⟨guardedTransfer_actual_conclusion (driveZeroOutputRoot rename drive index).forward,
    guardedTransfer_actual_conclusion (driveZeroOutputRoot rename drive index).backward⟩


theorem driveZeroOutputPrefix_localCaseCatalogue (rename : Nat → Fin v)
    (drive : parameters.drive = false) :
    ∃ records,
      resolutionRupSchedule (initialState (relabel rename (formula parameters)))
        (driveZeroOutputPrefix rename drive).steps = some records ∧
      records.map ResolutionRupInvocation.step = (driveZeroOutputPrefix rename drive).steps ∧
      records.length ≤ equalDecoderProgramBudget parameters + 4 + 4 * parameters.decoder.roots.length ∧
      ∀ record ∈ records,
        Controller.Resolution.Cases.ValidTree record.base record.step.clause record.tree ∧
        (splitVariables record.tree).card ≤ 5 ∧
        ∀ parent ∈ treeParentIds record.tree,
          (parent ≤ (formula parameters).clauses.size →
            SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename parent) ∧
          ((formula parameters).clauses.size < parent →
            ∃ earlier ∈ (driveZeroOutputPrefix rename drive).steps,
              earlier.id = parent ∧ earlier.id < record.step.id) := by
  obtain ⟨records, run, count, sound⟩ :=
    SourcePrefix.resolutionRupSchedule_sound rename (driveZeroOutputPrefix rename drive)
  have exactSteps := (resolutionRupSchedule_steps _ _ records run).1
  have exactTargets := resolutionRupSchedule_targets _ _ records run
  have parents := resolutionRupSchedule_parentSupport _ _
    (initialState (relabel rename (formula parameters)))
    (driveZeroOutputPrefix rename drive).steps records run (driveZeroOutputPrefix_supported rename drive)
  refine ⟨records, run, exactSteps,
    count.le.trans (driveZeroOutputPrefix_count rename drive), ?_⟩
  intro record member
  have valid : Controller.Resolution.Cases.ValidTree record.base record.step.clause record.tree := by
    rw [← exactTargets record member]
    exact (sound record member).1
  refine ⟨valid, ?_, parents record member⟩
  rw [(sound record member).2.1]
  simp

/-! The Boolean drive value selects one complete schedule and one uniform
catalogue bound; neither branch assumes an observation clause as a parent. -/

omit drive in
def selectorOutputPrefix (rename : Nat → Fin v) : SourcePrefix (parameters := parameters) rename :=
  if drive : parameters.drive = true then
    (selectorOutputProgram rename drive).prefix
  else
    driveZeroOutputPrefix rename (by
      cases equal : parameters.drive with
      | false => rfl
      | true => exact False.elim (drive equal))

def selectorOutputCatalogueBudget (parameters : Parameters) : Nat :=
  max (nativeOutputMacroBudget parameters.decoder.countedSize parameters.buses + 3)
    (equalDecoderProgramBudget parameters + 4) + 4 * parameters.decoder.roots.length

omit drive in
theorem selectorOutputCatalogueBudget_countedSize (parameters : Parameters) :
    selectorOutputCatalogueBudget parameters ≤
      nativeSelectorSizeBudget parameters.decoder.countedSize parameters.buses +
        6 * parameters.decoder.countedSize + 4 := by
  have roots : parameters.decoder.roots.length ≤ parameters.decoder.countedSize := by
    rw [Decoder.DAG.countedSize_eq]
    omega
  have equalBudget : equalDecoderProgramBudget parameters ≤
      actualSelectorResolutionBudget parameters := by
    unfold actualSelectorResolutionBudget
    omega
  have equalSize : equalDecoderProgramBudget parameters ≤
      nativeSelectorSizeBudget parameters.decoder.countedSize parameters.buses :=
    equalBudget.trans (actualSelectorResolutionBudget_countedSize parameters)
  have firstBound :
      nativeOutputMacroBudget parameters.decoder.countedSize parameters.buses + 3 ≤
        nativeSelectorSizeBudget parameters.decoder.countedSize parameters.buses +
          2 * parameters.decoder.countedSize + 4 := by
    unfold nativeOutputMacroBudget
    omega
  have secondBound : equalDecoderProgramBudget parameters + 4 ≤
      nativeSelectorSizeBudget parameters.decoder.countedSize parameters.buses +
        2 * parameters.decoder.countedSize + 4 := by
    omega
  have maxBound := max_le firstBound secondBound
  have rootBound : 4 * parameters.decoder.roots.length ≤
      4 * parameters.decoder.countedSize := by omega
  unfold selectorOutputCatalogueBudget
  calc
    max (nativeOutputMacroBudget parameters.decoder.countedSize parameters.buses + 3)
        (equalDecoderProgramBudget parameters + 4) + 4 * parameters.decoder.roots.length
        ≤ nativeSelectorSizeBudget parameters.decoder.countedSize parameters.buses +
            2 * parameters.decoder.countedSize + 4 + 4 * parameters.decoder.roots.length := by
              exact Nat.add_le_add_right maxBound _
    _ ≤ nativeSelectorSizeBudget parameters.decoder.countedSize parameters.buses +
          6 * parameters.decoder.countedSize + 4 := by omega

omit drive in
theorem selectorOutputPrefix_supported (rename : Nat → Fin v) :
    SourceDecoderSchedule.PrefixOriginalSupport rename (selectorOutputPrefix (parameters := parameters) rename) := by
  unfold selectorOutputPrefix
  split
  next drive => exact selectorOutputProgram_supported rename drive
  next notDrive =>
    have drive : parameters.drive = false := by
      cases equal : parameters.drive with
      | false => rfl
      | true => exact False.elim (notDrive equal)
    exact driveZeroOutputPrefix_supported rename drive

omit drive in
theorem selectorOutputPrefix_count (rename : Nat → Fin v) :
    (selectorOutputPrefix (parameters := parameters) rename).steps.length ≤ selectorOutputCatalogueBudget parameters := by
  unfold selectorOutputPrefix
  split
  next drive =>
    have bound := selectorOutputProgram_count rename drive
    have shared := Nat.le_max_left
      (nativeOutputMacroBudget parameters.decoder.countedSize parameters.buses + 3)
      (equalDecoderProgramBudget parameters + 4)
    unfold selectorOutputCatalogueBudget
    omega
  next notDrive =>
    have drive : parameters.drive = false := by
      cases equal : parameters.drive with
      | false => rfl
      | true => exact False.elim (notDrive equal)
    have bound := driveZeroOutputPrefix_count rename drive
    have shared := Nat.le_max_right
      (nativeOutputMacroBudget parameters.decoder.countedSize parameters.buses + 3)
      (equalDecoderProgramBudget parameters + 4)
    unfold selectorOutputCatalogueBudget
    omega

omit drive in
theorem selectorOutputPrefix_countedSize (rename : Nat → Fin v) :
    (selectorOutputPrefix (parameters := parameters) rename).steps.length ≤
      nativeSelectorSizeBudget parameters.decoder.countedSize parameters.buses +
        6 * parameters.decoder.countedSize + 4 :=
  (selectorOutputPrefix_count (parameters := parameters) rename).trans
    (selectorOutputCatalogueBudget_countedSize parameters)

omit drive in
/-- The exact selected schedule is covered for both drive polarities, including
strict parent causality, bounded local splitting and the common size bound. -/
theorem selectorOutputPrefix_localCaseCatalogue (rename : Nat → Fin v) :
    ∃ records,
      resolutionRupSchedule (initialState (relabel rename (formula parameters)))
        (selectorOutputPrefix (parameters := parameters) rename).steps = some records ∧
      records.map ResolutionRupInvocation.step = (selectorOutputPrefix (parameters := parameters) rename).steps ∧
      records.length ≤ selectorOutputCatalogueBudget parameters ∧
      ∀ record ∈ records,
        Controller.Resolution.Cases.ValidTree record.base record.step.clause record.tree ∧
        (splitVariables record.tree).card ≤ 5 ∧
        ∀ parent ∈ treeParentIds record.tree,
          (parent ≤ (formula parameters).clauses.size →
            SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename parent) ∧
          ((formula parameters).clauses.size < parent →
            ∃ earlier ∈ (selectorOutputPrefix (parameters := parameters) rename).steps,
              earlier.id = parent ∧ earlier.id < record.step.id) := by
  obtain ⟨records, run, count, sound⟩ :=
    SourcePrefix.resolutionRupSchedule_sound rename (selectorOutputPrefix (parameters := parameters) rename)
  have exactSteps := (resolutionRupSchedule_steps _ _ records run).1
  have exactTargets := resolutionRupSchedule_targets _ _ records run
  have parents := resolutionRupSchedule_parentSupport _ _
    (initialState (relabel rename (formula parameters)))
    (selectorOutputPrefix (parameters := parameters) rename).steps records run
      (selectorOutputPrefix_supported (parameters := parameters) rename)
  refine ⟨records, run, exactSteps,
    count.le.trans (selectorOutputPrefix_count (parameters := parameters) rename), ?_⟩
  intro record member
  have valid : Controller.Resolution.Cases.ValidTree record.base record.step.clause record.tree := by
    rw [← exactTargets record member]
    exact (sound record member).1
  refine ⟨valid, ?_, parents record member⟩
  rw [(sound record member).2.1]
  simp

@[simp] theorem decoderProjectionRetarget_steps {state : State v} {context : Clause (Fin v)}
    {left right nextLeft nextRight : Literal (Fin v)} {budget : Nat}
    (projection : PairedProjection state context left right budget)
    (leftEqual : nextLeft = left) (rightEqual : nextRight = right) :
    (decoderProjectionRetarget projection leftEqual rightEqual).steps = projection.steps := by
  cases leftEqual
  cases rightEqual
  rfl

@[simp] theorem decoderProjectionBudget_steps {state : State v} {context : Clause (Fin v)}
    {left right : Literal (Fin v)} {before after : Nat}
    (projection : PairedProjection state context left right before) (equal : before = after) :
    (decoderProjectionBudget projection equal).steps = projection.steps := by
  cases equal
  rfl

/-- Source aliases emit no equality inference; represented gates are charged
to their actual allocated producers, retaining repeated input incidences. -/
theorem decoderNodeProjectionSize (rename : Nat → Fin v) (context : Clause (Fin v))
    (node : Fin parameters.decoder.nodeCount)
    (table : DecoderPairTable (parameters := parameters) rename context node.val)
    (qualifiers : DecoderQualifiersAt rename context node table.prefixState.state) :
    (decoderNodeProjection rename context node table qualifiers).steps.length ≤
      24 * sourceDecoderNodeProducerCost parameters node := by
  by_cases unary : ∃ child, parameters.decoder.node node = .disj [child]
  · obtain ⟨child, shape⟩ := unary
    unfold decoderNodeProjection
    split
    · next equal => simp [equal] at shape
    · next channel equal => simp [equal] at shape
    · next children equal =>
      have same : children = [child] := by simpa only [equal, Decoder.Gate.disj.injEq] using shape
      subst children
      dsimp only
      simp only [decoderProjectionBudget_steps, completeDisjunctionNode,
        decoderProjectionRetarget_steps, pairedDecoderDisjunction]
      have one : (decoderChildPairs rename node [child]).length = 1 := by simp [decoderChildPairs]
      rw [pairedOr_unary _ _ _ _ _ _ _ _ _ one]
      exact Nat.zero_le _
    · next child labels equal => simp [equal] at shape
    · next left right equal => simp [equal] at shape
  · apply (decoderNodeProjection rename context node table qualifiers).count.trans
    cases shape : parameters.decoder.node node with
    | zero => simp [decoderNodeBudget, sourceDecoderNodeProducerCost, shape]
    | input channel => simp [decoderNodeBudget, sourceDecoderNodeProducerCost, shape]
    | guard child labels => simp [decoderNodeBudget, sourceDecoderNodeProducerCost, shape]
    | liveAnd left right => simp [decoderNodeBudget, sourceDecoderNodeProducerCost, shape]
    | disj children =>
      have different : children.length ≠ 1 := by
        intro one
        obtain ⟨child, equal⟩ := List.length_eq_one_iff.mp one
        exact unary ⟨child, equal ▸ shape⟩
      simp only [decoderNodeBudget, sourceDecoderNodeProducerCost, shape, sourceFoldProducerCount]
      split <;> omega

def decoderProducerPrefixCost (count : Nat) : Nat :=
  (((List.finRange parameters.decoder.nodeCount).take count).map
    (sourceDecoderNodeProducerCost parameters)).sum

theorem decoderProducerPrefixCost_succ (node : Fin parameters.decoder.nodeCount) :
    decoderProducerPrefixCost (parameters := parameters) (node.val + 1) =
      decoderProducerPrefixCost (parameters := parameters) node.val + sourceDecoderNodeProducerCost parameters node := by
  unfold decoderProducerPrefixCost
  rw [List.take_succ_eq_append_getElem (by simpa using node.isLt)]
  simp

theorem qualifiedDecoderAdvanceSize (rename : Nat → Fin v) (context : Clause (Fin v))
    (node : Fin parameters.decoder.nodeCount)
    (current : QualifiedDecoderTable (parameters := parameters) rename context node.val) :
    (qualifiedDecoderAdvance rename context node current).table.prefixState.steps.length ≤
      current.table.prefixState.steps.length + 24 * sourceDecoderNodeProducerCost parameters node := by
  have actual := decoderNodeProjectionSize rename context node current.table
    (decoderQualifiersAt rename context node current.table.prefixState.state current.qualifiers)
  change (current.table.prefixState.steps ++ _).length ≤ _
  rw [List.length_append]
  exact Nat.add_le_add_left actual _

theorem buildQualifiedDecoderSize (rename : Nat → Fin v) (context : Clause (Fin v))
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (cache : DecoderQualifierCache (parameters := parameters) rename context prefixState.state)
    (count : Nat) (bounded : count ≤ parameters.decoder.nodeCount) :
    (buildQualifiedDecoder rename context prefixState cache count bounded).table.prefixState.steps.length ≤
      prefixState.steps.length + 24 * decoderProducerPrefixCost (parameters := parameters) count := by
  induction count with
  | zero => simp [buildQualifiedDecoder, qualifiedDecoderInitial, decoderTableInitial, decoderProducerPrefixCost]
  | succ count ih =>
    let node : Fin parameters.decoder.nodeCount := ⟨count, by omega⟩
    let previous := buildQualifiedDecoder rename context prefixState cache count (by omega)
    have old := ih (by omega)
    change previous.table.prefixState.steps.length ≤ prefixState.steps.length +
      24 * decoderProducerPrefixCost (parameters := parameters) count at old
    have current := qualifiedDecoderAdvanceSize rename context node previous
    have next := decoderProducerPrefixCost_succ (parameters := parameters) node
    change decoderProducerPrefixCost (parameters := parameters) (count + 1) =
      decoderProducerPrefixCost (parameters := parameters) count + sourceDecoderNodeProducerCost parameters node at next
    exact current.trans (by omega)

theorem equalDecoderProgramSize (rename : Nat → Fin v) (flag : Bool) :
    (equalDecoderProgram (parameters := parameters) rename flag).table.prefixState.steps.length ≤
      SourceQualifierSchedule.qualifierProgramBudget parameters + 24 * sourceDecoderProducerCost parameters := by
  have actual := buildQualifiedDecoderSize rename
    (equalFlagContext (parameters := parameters) rename flag) (equalDecoderPrefix rename flag)
    (constructedQualifierCache rename flag) parameters.decoder.nodeCount (Nat.le_refl _)
  have initial := SourceQualifierSchedule.allChannelQualifiers_count (parameters := parameters) rename flag
  unfold decoderProducerPrefixCost at actual
  rw [List.take_of_length_le (by simp)] at actual
  exact actual.trans (Nat.add_le_add_right initial _)

end Controller.NativeProof.SourceDecoderTraversal
