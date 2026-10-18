module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.EnumerationUniformRootQuery
public import Controller.Cost.EnumerationLoop

@[expose] public section

/-! One fixed returning output-scan block for every prefix and queried root. -/
namespace Controller.Cost.EnumerationUniformLoop
open Controller.Cost.EnumerationLoop Controller.Cost.GateProgram Controller.Cost.RawTransferLoops
variable {trueBase falseBase : Nat}

section Layout
open Controller.Cost.ForestZeroDictionary Controller.Native Controller.Native.SourceController Controller.Decoder

def returnPoint (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels)) (heapSize coordinateBase slot entry : Nat)
    (root : Fin graph.nodeCount) (width : Nat) : Nat :=
  EnumerationUniformRootQuery.returnEntry (trueBase := trueBase) (falseBase := falseBase) width parameters graph T F heapSize coordinateBase slot (entry + 49) root

/-- One resident copy of the returning output scan; `ret` is the caller's return address. -/
def code (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels)) (heap : Array (Word width))
    (layout : Layout (parameters.channels + graph.nodeCount) heap.size)
    (coordinateBase slot offset entry ret : Nat) (root : Fin graph.nodeCount) : List (Instruction width 8) :=
  (SharedRootTaggedCursor.code width parameters.channels entry
    (returnPoint (trueBase := trueBase) (falseBase := falseBase) parameters graph T F heap.size coordinateBase slot entry root width + 5)
    (entry + 37) (entry + 31)).toList ++
  (acceptCode width entry ret ++
  ((SharedRootResumeEntry.skipCode width layout.tableBase layout.inverseBase entry).toList ++
  ((SharedRootHealthyEntry.code width layout.tableBase layout.inverseBase offset slot).toList ++
  (EnumerationUniformRootQuery.code (trueBase := trueBase) (falseBase := falseBase) parameters graph T F heap layout coordinateBase slot (entry + 49) root ++
  (dispatchCode width entry ++ exhaustedCode width ret)))))

theorem returnEntry_point (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels)) (heapSize coordinateBase slot entry width : Nat)
    (root currentRoot : Fin graph.nodeCount) :
    EnumerationUniformRootQuery.returnEntry (trueBase := trueBase) (falseBase := falseBase) width parameters graph T F heapSize coordinateBase slot (entry + 49) root =
      returnPoint (trueBase := trueBase) (falseBase := falseBase) parameters graph T F heapSize coordinateBase slot entry currentRoot width := by
  unfold returnPoint EnumerationUniformRootQuery.returnEntry
  exact EnumerationFixedRootQuery.return_root_irrel parameters graph root currentRoot

theorem query_end (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels)) (heap : Array (Word width))
    (layout : Layout (parameters.channels + graph.nodeCount) heap.size)
    (coordinateBase slot entry : Nat) (root : Fin graph.nodeCount) :
    entry + 49 + (EnumerationUniformRootQuery.code (trueBase := trueBase) (falseBase := falseBase) parameters graph T F heap layout coordinateBase slot (entry + 49) root).length =
      returnPoint (trueBase := trueBase) (falseBase := falseBase) parameters graph T F heap.size coordinateBase slot entry root width :=
  EnumerationUniformRootQuery.returnEntry_eq (trueBase := trueBase) (falseBase := falseBase) parameters graph T F heap layout coordinateBase slot (entry + 49) root

theorem code_length (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels)) (heap : Array (Word width))
    (layout : Layout (parameters.channels + graph.nodeCount) heap.size)
    (coordinateBase slot offset entry ret : Nat) (root : Fin graph.nodeCount) :
    entry + (code (trueBase := trueBase) (falseBase := falseBase) parameters graph T F heap layout coordinateBase slot offset entry ret root).length =
      returnPoint (trueBase := trueBase) (falseBase := falseBase) parameters graph T F heap.size coordinateBase slot entry root width + 8 := by
  have query := query_end (trueBase := trueBase) (falseBase := falseBase) parameters graph T F heap layout coordinateBase slot entry root
  simp only [code, List.length_append, Array.length_toList, SharedRootTaggedCursor.code_size, acceptCode_length,
    SharedRootResumeEntry.skipCode_size, SharedRootHealthyEntry.code_size, dispatchCode_length, exhaustedCode_length]
  omega

theorem code_length_bound (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels)) (heap : Array (Word width))
    (layout : Layout (parameters.channels + graph.nodeCount) heap.size)
    (coordinateBase slot offset entry ret : Nat) (root : Fin graph.nodeCount) :
    (code (trueBase := trueBase) (falseBase := falseBase) parameters graph T F heap layout coordinateBase slot offset entry ret root).length ≤
      403 * (graph.countedSize + 1) + 604 := by
  have bound := EnumerationUniformRootQuery.code_length_bound (trueBase := trueBase) (falseBase := falseBase) parameters graph T F heap layout coordinateBase slot (entry + 49) root
  simp only [code, List.length_append, Array.length_toList, SharedRootTaggedCursor.code_size, acceptCode_length,
    SharedRootResumeEntry.skipCode_size, SharedRootHealthyEntry.code_size, dispatchCode_length, exhaustedCode_length]
  omega

theorem shared (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels)) (before after : Array (Word width))
    (leftLayout : Layout (parameters.channels + graph.nodeCount) before.size)
    (rightLayout : Layout (parameters.channels + graph.nodeCount) after.size)
    (coordinateBase slot offset entry ret : Nat) (left right : Fin graph.nodeCount)
    (sameSize : before.size = after.size) (sameTable : leftLayout.tableBase = rightLayout.tableBase)
    (sameInverse : leftLayout.inverseBase = rightLayout.inverseBase) :
    code (trueBase := trueBase) (falseBase := falseBase) parameters graph T F before leftLayout coordinateBase slot offset entry ret left =
      code (trueBase := trueBase) (falseBase := falseBase) parameters graph T F after rightLayout coordinateBase slot offset entry ret right := by
  have sameQuery := EnumerationUniformRootQuery.shared (trueBase := trueBase) (falseBase := falseBase) parameters graph T F before after leftLayout rightLayout
    coordinateBase slot (entry + 49) left right sameSize
  have samePoint : returnPoint (trueBase := trueBase) (falseBase := falseBase) parameters graph T F before.size coordinateBase slot entry left width =
      returnPoint (trueBase := trueBase) (falseBase := falseBase) parameters graph T F after.size coordinateBase slot entry right width := by
    unfold returnPoint EnumerationUniformRootQuery.returnEntry
    rw [sameSize, EnumerationFixedRootQuery.return_root_irrel parameters graph left right]
  unfold code
  rw [sameQuery, samePoint, sameTable, sameInverse]

private theorem head_at (program : Program width 8) (entry : Nat) (left right : List (Instruction width 8))
    (present : SharedRootRead.BlockAt program entry (left ++ right)) : SharedRootRead.BlockAt program entry left := by
  intro offset below
  have found := present offset (by simp only [List.length_append]; omega)
  rwa [List.getElem?_append_left below] at found

private theorem tail_at (program : Program width 8) (entry : Nat) (left right : List (Instruction width 8))
    (present : SharedRootRead.BlockAt program entry (left ++ right)) :
    SharedRootRead.BlockAt program (entry + left.length) right := by
  intro offset below
  have found := present (left.length + offset) (by simp only [List.length_append]; omega)
  rw [List.getElem?_append_right (by omega)] at found
  simpa only [Nat.add_sub_cancel_left, Nat.add_assoc] using found

private theorem array_at (program : Program width 8) (entry : Nat) (instructions : Program width 8)
    (present : SharedRootRead.BlockAt program entry instructions.toList) : CodeAt program entry instructions := by
  intro phase
  simpa only [Array.getElem?_toList] using present phase.val (by simpa only [Array.length_toList] using phase.isLt)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem blocks_at (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels)) (heap : Array (Word width))
    (layout : Layout (parameters.channels + graph.nodeCount) heap.size)
    (coordinateBase slot offset entry ret : Nat) (root : Fin graph.nodeCount)
    (program : Program width 8)
    (present : SharedRootRead.BlockAt program entry
      (code (trueBase := trueBase) (falseBase := falseBase) parameters graph T F heap layout coordinateBase slot offset entry ret root)) :
    CodeAt program entry (SharedRootTaggedCursor.code width parameters.channels entry
      (returnPoint (trueBase := trueBase) (falseBase := falseBase) parameters graph T F heap.size coordinateBase slot entry root width + 5) (entry + 37) (entry + 31)) ∧
    SharedRootRead.BlockAt program (entry + 22) (acceptCode width entry ret) ∧
    CodeAt program (entry + 31) (SharedRootResumeEntry.skipCode width layout.tableBase layout.inverseBase entry) ∧
    CodeAt program (entry + 37) (SharedRootHealthyEntry.code width layout.tableBase layout.inverseBase offset slot) ∧
    SharedRootRead.BlockAt program (entry + 49)
      (EnumerationUniformRootQuery.code (trueBase := trueBase) (falseBase := falseBase) parameters graph T F heap layout coordinateBase slot (entry + 49) root) ∧
    SharedRootRead.BlockAt program (returnPoint (trueBase := trueBase) (falseBase := falseBase) parameters graph T F heap.size coordinateBase slot entry root width)
      (dispatchCode width entry) ∧
    SharedRootRead.BlockAt program (returnPoint (trueBase := trueBase) (falseBase := falseBase) parameters graph T F heap.size coordinateBase slot entry root width + 5)
      (exhaustedCode width ret) := by
  unfold code at present
  have cursorBlock := head_at program entry _ _ present
  have first := tail_at program entry _ _ present
  simp only [Array.length_toList, SharedRootTaggedCursor.code_size] at first
  have acceptBlock := head_at program (entry + 22) _ _ first
  have second := tail_at program (entry + 22) _ _ first
  simp only [acceptCode_length, Nat.add_assoc, Nat.reduceAdd] at second
  have skipBlock := head_at program _ _ _ second
  have third := tail_at program _ _ _ second
  simp only [Array.length_toList, SharedRootResumeEntry.skipCode_size, Nat.add_assoc, Nat.reduceAdd] at third
  have healthyBlock := head_at program _ _ _ third
  have fourth := tail_at program _ _ _ third
  simp only [Array.length_toList, SharedRootHealthyEntry.code_size, Nat.add_assoc, Nat.reduceAdd] at fourth
  have queryBlock := head_at program _ _ _ fourth
  have fifth := tail_at program _ _ _ fourth
  have queryEnd := query_end (trueBase := trueBase) (falseBase := falseBase) parameters graph T F heap layout coordinateBase slot entry root
  rw [queryEnd] at fifth
  have dispatchBlock := head_at program _ _ _ fifth
  have last := tail_at program _ _ _ fifth
  simp only [dispatchCode_length] at last
  exact ⟨array_at _ _ _ cursorBlock, acceptBlock, array_at _ _ _ skipBlock, array_at _ _ _ healthyBlock,
    by simpa only [Nat.add_assoc] using queryBlock, dispatchBlock, last⟩

end Layout


end Controller.Cost.EnumerationUniformLoop
