module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.SourceDecoderTraversal

@[expose] public section

/-! Native guard-chain clauses retain the actual source handles and original
occurrences. A multi-guard node is flattened by ordinary resolution through
its stored AND chain, with no duplicated decoder child or observation row. -/
namespace Controller.NativeProof.SourceDecoderClauses
open Controller.CNF Controller.Resolution Controller.Native Controller.Native.SourceController
open Controller.NativeProof.SourceDecoderTraversal Controller.NativeProof.SourceDecoderSchedule
open Controller.NativeProof.FoldProjection Controller.NativeProof.SourceFoldProjection
open Controller.NativeProof.SourceFoldOwners Controller.NativeProof.SourceFoldAggregateProvenance
open Controller.NativeProof.SourceFoldProvenance
open Controller.NativeProof.SourceCongruence
open Controller.NativeProof.SourceFoldOccurrences
variable {parameters : Parameters} {v : Nat}

def guardInputs (rename : Nat → Fin v) (side : Side)
    (node : Fin parameters.decoder.nodeCount) (child : Fin node.val)
    (labels : List (Fin parameters.channels)) (count : Nat) : List (Literal (Fin v)) :=
  [mapLiteral rename ((decoderPositionBefore side node).slots
    (.internal (.decoder side (parameters.decoder.childIndex node child))))] ++
  (labels.take count).map fun channel => negate (mapLiteral rename
    ((decoderPositionBefore side node).slots (.internal (.qualifier side channel))))

structure GuardTreeBundle (rename : Nat → Fin v)
    (output : Literal (Fin v)) (inputs : List (Literal (Fin v))) where
  tree : AndTree (initialState (relabel rename (formula parameters))) output inputs
  originals : TreeOriginals (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) tree

structure BinaryRowsBundle (rename : Nat → Fin v)
    (left right output : Literal (Fin v)) where
  rows : BinaryAndRows (initialState (relabel rename (formula parameters))) left right output
  originals : BinaryOriginals (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) rows

def guardChainBundle (rename : Nat → Fin v) (side : Side)
    (node : Fin parameters.decoder.nodeCount) (child : Fin node.val)
    (labels : List (Fin parameters.channels))
    (shape : parameters.decoder.node node = .guard child labels) :
    (count : Nat) → count ≤ labels.length →
    GuardTreeBundle (parameters := parameters) rename
      (mapLiteral rename (guardCursorAt side node child labels count).1)
      (guardInputs rename side node child labels count)
  | 0, _ => by
      let tree := AndTree.leaf (state := initialState (relabel rename (formula parameters)))
        (mapLiteral rename ((decoderPositionBefore side node).slots
          (.internal (.decoder side (parameters.decoder.childIndex node child)))))
      simpa only [guardInputs, List.take_zero, List.map_nil, List.append_nil,
        guardCursorAt, List.take_zero, List.foldl_nil] using
        (⟨tree, trivial⟩ : GuardTreeBundle (parameters := parameters) rename _ _)
  | count + 1, bound => by
      let index : Fin labels.length := ⟨count, by omega⟩
      let previous := guardChainBundle rename side node child labels shape count (by omega)
      let rows := binaryRows (guardLeft side node child labels index)
        (guardRight side node child labels index) (guardOutput side node child labels index)
        (decoderGuardRows rename side node child labels shape index)
      have rightEq : mapLiteral rename (guardRight side node child labels index) =
          negate (mapLiteral rename ((decoderPositionBefore side node).slots
            (.internal (.qualifier side labels[count])))) := by
        simp only [guardRight, guardCursor_qualifier]
        rfl
      have leftEq : mapLiteral rename (guardLeft side node child labels index) =
          mapLiteral rename (guardCursorAt side node child labels count).1 := rfl
      have outputEq := guardCursorAt_output_succ (parameters := parameters) side node child labels index
      have rowsOrigins : BinaryOriginals
          (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) rows := by
        apply binaryRows_originals
        intro rowIndex
        exact decoderGuardRows_allowed rename side node child labels shape index
          ⟨rowIndex.val, rowIndex.isLt⟩
      let actualBundle : BinaryRowsBundle (parameters := parameters) rename
          (mapLiteral rename (guardCursorAt side node child labels count).1)
          (negate (mapLiteral rename ((decoderPositionBefore side node).slots
            (.internal (.qualifier side labels[count])))))
          (mapLiteral rename (guardOutput side node child labels index)) := by
        simpa only [leftEq, rightEq] using
          (⟨rows, rowsOrigins⟩ : BinaryRowsBundle (parameters := parameters) rename _ _ _)
      let tree := AndTree.node previous.tree
        (.leaf (negate (mapLiteral rename ((decoderPositionBefore side node).slots
          (.internal (.qualifier side labels[count]))))))
        (mapLiteral rename (guardOutput side node child labels index))
        actualBundle.rows
      have origins : TreeOriginals
          (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) tree := by
        dsimp only [tree, TreeOriginals]
        exact ⟨previous.originals, trivial, actualBundle.originals⟩
      have takeEq := List.take_succ_eq_append_getElem (l := labels) index.isLt
      simpa only [index, guardInputs, outputEq, takeEq, List.map_append,
        List.map_cons, List.map_nil, List.append_assoc] using
        (⟨tree, origins⟩ : GuardTreeBundle (parameters := parameters) rename _ _)

def nativeGuardTree (rename : Nat → Fin v) (side : Side)
    (node : Fin parameters.decoder.nodeCount) (child : Fin node.val)
    (labels : List (Fin parameters.channels))
    (shape : parameters.decoder.node node = .guard child labels) :=
  (guardChainBundle rename side node child labels shape labels.length (Nat.le_refl _)).tree

theorem nativeGuardTree_originals (rename : Nat → Fin v) (side : Side)
    (node : Fin parameters.decoder.nodeCount) (child : Fin node.val)
    (labels : List (Fin parameters.channels))
    (shape : parameters.decoder.node node = .guard child labels) :
    TreeOriginals (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
      (nativeGuardTree rename side node child labels shape) :=
  (guardChainBundle rename side node child labels shape labels.length (Nat.le_refl _)).originals

theorem nativeGuardTree_linear (rename : Nat → Fin v) (side : Side)
    (node : Fin parameters.decoder.nodeCount) (child : Fin node.val)
    (labels : List (Fin parameters.channels))
    (shape : parameters.decoder.node node = .guard child labels) :
    (projectTreeLong (nativeGuardTree rename side node child labels shape)).steps.length ≤
      2 * labels.length := by
  have bound := projectTreeLong_linear (nativeGuardTree rename side node child labels shape)
  simpa [nativeGuardTree, guardInputs] using bound

/-- Native forward clause: output or negated child or the positive guard
qualifiers. Empty guard lists are literal-identity skips. -/
def guardForward (rename : Nat → Fin v) (side : Side)
    (node : Fin parameters.decoder.nodeCount) (child : Fin node.val)
    (labels : List (Fin parameters.channels))
    (shape : parameters.decoder.node node = .guard child labels) :=
  projectTreeLong (nativeGuardTree rename side node child labels shape)

theorem guardForward_supported (rename : Nat → Fin v) (side : Side)
    (node : Fin parameters.decoder.nodeCount) (child : Fin node.val)
    (labels : List (Fin parameters.channels))
    (shape : parameters.decoder.node node = .guard child labels) :
    let actual := guardForward rename side node child labels shape
    Controller.NativeProof.SourceBusSchedule.TraceOriginalSupport
      (formula parameters).clauses.size
      (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) actual.steps ∧
    AggregateOrigin (formula parameters).clauses.size
      (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
      actual.steps actual.result := by
  simpa only [guardForward, List.nil_append] using projectTreeLong_supported
    (initialState (relabel rename (formula parameters)))
    (nativeGuardTree rename side node child labels shape)
    (formula parameters).clauses.size
    (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) []
    (nativeGuardTree_originals rename side node child labels shape)
    (by simp [Controller.NativeProof.SourceBusSchedule.TraceOriginalSupport])
    (SourceDecoderSchedule.allowed_native_count_le rename)
    (by simp [initialState, relabel, Controller.CNF.OrderedFormula.relabel])

/-- All child-to-parent OR implications are derived in one shared traversal.
Unary ORs carry an existing literal-identity certificate. -/
def disjunctionForward (rename : Nat → Fin v) (side : Side)
    (node : Fin parameters.decoder.nodeCount) (children : List (Fin node.val))
    (shape : parameters.decoder.node node = .disj children) (nonempty : children ≠ []) :=
  projectTreeInputs (decoderDisjunctionTree rename side node children shape nonempty)

theorem disjunctionForward_linear (rename : Nat → Fin v) (side : Side)
    (node : Fin parameters.decoder.nodeCount) (children : List (Fin node.val))
    (shape : parameters.decoder.node node = .disj children) (nonempty : children ≠ []) :
    (disjunctionForward rename side node children shape nonempty).steps.length ≤
      2 * (children.length - 1) := by
  simpa [disjunctionForward, decoderDisjunctionTree] using
    projectTreeInputs_linear (decoderDisjunctionTree rename side node children shape nonempty)

/-- Native output-to-children OR clause, used by support-summary elimination. -/
def disjunctionReverse (rename : Nat → Fin v) (side : Side)
    (node : Fin parameters.decoder.nodeCount) (children : List (Fin node.val))
    (shape : parameters.decoder.node node = .disj children) (nonempty : children ≠ []) :=
  projectTreeLong (decoderDisjunctionTree rename side node children shape nonempty)

theorem disjunctionReverse_supported (rename : Nat → Fin v) (side : Side)
    (node : Fin parameters.decoder.nodeCount) (children : List (Fin node.val))
    (shape : parameters.decoder.node node = .disj children) (nonempty : children ≠ []) :
    let actual := disjunctionReverse rename side node children shape nonempty
    Controller.NativeProof.SourceBusSchedule.TraceOriginalSupport
      (formula parameters).clauses.size
      (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) actual.steps ∧
    AggregateOrigin (formula parameters).clauses.size
      (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
      actual.steps actual.result := by
  simpa only [disjunctionReverse, List.nil_append] using projectTreeLong_supported
    (initialState (relabel rename (formula parameters)))
    (decoderDisjunctionTree rename side node children shape nonempty)
    (formula parameters).clauses.size
    (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) []
    (decoderDisjunctionTree_originals rename side node children shape nonempty)
    (by simp [Controller.NativeProof.SourceBusSchedule.TraceOriginalSupport])
    (SourceDecoderSchedule.allowed_native_count_le rename)
    (by simp [initialState, relabel, Controller.CNF.OrderedFormula.relabel])

end Controller.NativeProof.SourceDecoderClauses
