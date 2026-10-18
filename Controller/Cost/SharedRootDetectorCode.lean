module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedRootHealthyQuery
public import Controller.Cost.SharedRootTaggedSkip

@[expose] public section

namespace Controller.Cost.SharedRootDetectorCode
open Controller.Cost.GateProgram Controller.Cost.RawTransferLoops
open Controller.Cost.ForestZeroDictionary Controller.Native Controller.Native.SourceController Controller.Decoder

def skipEntry (entry : Nat) (trueCode : List (Instruction width 8)) : Nat := entry + 22 + trueCode.length
def healthyEntry (entry : Nat) (trueCode : List (Instruction width 8)) : Nat := skipEntry entry trueCode + 6
def queryEntry (entry : Nat) (trueCode : List (Instruction width 8)) : Nat := healthyEntry entry trueCode + 12

def query (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels)) (heap : Array (Word width))
    (layout : Layout (parameters.channels + graph.nodeCount) heap.size)
    (coordinateBase slot entry : Nat) (trueCode : List (Instruction width 8)) (root : Fin graph.nodeCount) :=
  SharedQueryReuseCode.code parameters graph T F heap layout coordinateBase slot (queryEntry entry trueCode) entry root

def exhausted (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels)) (heap : Array (Word width))
    (layout : Layout (parameters.channels + graph.nodeCount) heap.size)
    (coordinateBase slot entry : Nat) (trueCode : List (Instruction width 8)) (root : Fin graph.nodeCount) : Nat :=
  queryEntry entry trueCode + (query parameters graph T F heap layout coordinateBase slot entry trueCode root).length

@[irreducible] def code (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels)) (heap : Array (Word width))
    (layout : Layout (parameters.channels + graph.nodeCount) heap.size)
    (coordinateBase slot offset entry : Nat) (trueCode : List (Instruction width 8)) (root : Fin graph.nodeCount) : List (Instruction width 8) :=
  (SharedRootTaggedCursor.code width parameters.channels entry
    (exhausted parameters graph T F heap layout coordinateBase slot entry trueCode root)
    (healthyEntry entry trueCode) (skipEntry entry trueCode)).toList ++
  (trueCode ++
  ((SharedRootResumeEntry.skipCode width layout.tableBase layout.inverseBase entry).toList ++
  ((SharedRootHealthyEntry.code width layout.tableBase layout.inverseBase offset slot).toList ++
  (query parameters graph T F heap layout coordinateBase slot entry trueCode root ++
    (ForestZeroRootLoop.exhaustedCode width).toList))))

set_option maxHeartbeats 2000000 in
theorem shared (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels)) (before after : Array (Word width))
    (leftLayout : Layout (parameters.channels + graph.nodeCount) before.size)
    (rightLayout : Layout (parameters.channels + graph.nodeCount) after.size)
    (coordinateBase slot offset entry : Nat) (trueCode : List (Instruction width 8))
    (left right : Fin graph.nodeCount) (sameSize : before.size = after.size)
    (sameTable : leftLayout.tableBase = rightLayout.tableBase)
    (sameInverse : leftLayout.inverseBase = rightLayout.inverseBase) :
    code parameters graph T F before leftLayout coordinateBase slot offset entry trueCode left =
      code parameters graph T F after rightLayout coordinateBase slot offset entry trueCode right := by
  have sameQuery : query parameters graph T F before leftLayout coordinateBase slot entry trueCode left =
      query parameters graph T F after rightLayout coordinateBase slot entry trueCode right :=
    SharedQueryReuseCode.shared parameters graph T F before after leftLayout rightLayout coordinateBase slot
      (queryEntry entry trueCode) entry left right sameSize
  have sameEnd : exhausted parameters graph T F before leftLayout coordinateBase slot entry trueCode left =
      exhausted parameters graph T F after rightLayout coordinateBase slot entry trueCode right := by
    unfold exhausted
    rw [sameQuery]
  unfold code
  rw [sameEnd, sameTable, sameInverse, sameQuery]

set_option maxHeartbeats 2000000 in
theorem code_length_bound (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels)) (heap : Array (Word width))
    (layout : Layout (parameters.channels + graph.nodeCount) heap.size)
    (coordinateBase slot offset entry : Nat) (trueCode : List (Instruction width 8)) (root : Fin graph.nodeCount) :
    (code parameters graph T F heap layout coordinateBase slot offset entry trueCode root).length ≤
      trueCode.length + 410 * (graph.countedSize + 1) + 34 * (NativeSourceExecution.selectedSize parameters).total + 554 := by
  have bound : (query parameters graph T F heap layout coordinateBase slot entry trueCode root).length ≤
      410 * (graph.countedSize + 1) + 34 * (NativeSourceExecution.selectedSize parameters).total + 512 := by
    unfold query SharedQueryReuseCode.code
    dsimp only
    exact SharedQueryHeapCapacity.code_length_bound parameters graph T F root width (queryEntry entry trueCode) heap.size _ _ _ entry
  unfold code
  simp only [List.length_append, Array.length_toList, SharedRootTaggedCursor.code_size,
    SharedRootResumeEntry.skipCode_size, SharedRootHealthyEntry.code_size,
    ForestZeroRootLoop.exhaustedCode, List.length_cons, List.length_nil]
  omega


private theorem head_at (program : Program width 8) (entry : Nat) (left right : List (Instruction width 8))
    (present : SharedRootRead.BlockAt program entry (left ++ right)) : SharedRootRead.BlockAt program entry left := by
  intro offset below
  have found := present offset (by simp only [List.length_append]; omega)
  rw [List.getElem?_append_left below] at found
  exact found

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
    (coordinateBase slot offset entry : Nat) (trueCode : List (Instruction width 8)) (root : Fin graph.nodeCount)
    (program : Program width 8)
    (present : SharedRootRead.BlockAt program entry
      (code parameters graph T F heap layout coordinateBase slot offset entry trueCode root)) :
    CodeAt program entry (SharedRootTaggedCursor.code width parameters.channels entry
      (exhausted parameters graph T F heap layout coordinateBase slot entry trueCode root)
      (healthyEntry entry trueCode) (skipEntry entry trueCode)) ∧
    SharedRootRead.BlockAt program (entry + 22) trueCode ∧
    CodeAt program (skipEntry entry trueCode) (SharedRootResumeEntry.skipCode width layout.tableBase layout.inverseBase entry) ∧
    CodeAt program (healthyEntry entry trueCode) (SharedRootHealthyEntry.code width layout.tableBase layout.inverseBase offset slot) ∧
    SharedRootRead.BlockAt program (queryEntry entry trueCode)
      (query parameters graph T F heap layout coordinateBase slot entry trueCode root) ∧
    CodeAt program (exhausted parameters graph T F heap layout coordinateBase slot entry trueCode root)
      (ForestZeroRootLoop.exhaustedCode width) := by
  unfold code at present
  have cursorBlock := head_at program entry _ _ present
  have first := tail_at program entry _ _ present
  simp only [Array.length_toList, SharedRootTaggedCursor.code_size] at first
  have trueBlock := head_at program (entry + 22) _ _ first
  have second := tail_at program (entry + 22) _ _ first
  change SharedRootRead.BlockAt program (skipEntry entry trueCode) _ at second
  have skipBlock := head_at program (skipEntry entry trueCode) _ _ second
  have third := tail_at program (skipEntry entry trueCode) _ _ second
  simp only [Array.length_toList, SharedRootResumeEntry.skipCode_size] at third
  change SharedRootRead.BlockAt program (healthyEntry entry trueCode) _ at third
  have healthyBlock := head_at program (healthyEntry entry trueCode) _ _ third
  have fourth := tail_at program (healthyEntry entry trueCode) _ _ third
  simp only [Array.length_toList, SharedRootHealthyEntry.code_size] at fourth
  change SharedRootRead.BlockAt program (queryEntry entry trueCode) _ at fourth
  have queryBlock := head_at program (queryEntry entry trueCode) _ _ fourth
  have last := tail_at program (queryEntry entry trueCode) _ _ fourth
  change SharedRootRead.BlockAt program (exhausted parameters graph T F heap layout coordinateBase slot entry trueCode root) _ at last
  exact ⟨array_at _ _ _ cursorBlock, trueBlock, array_at _ _ _ skipBlock,
    array_at _ _ _ healthyBlock, queryBlock, array_at _ _ _ last⟩


theorem code_end (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels)) (heap : Array (Word width))
    (layout : Layout (parameters.channels + graph.nodeCount) heap.size)
    (coordinateBase slot offset entry : Nat) (trueCode : List (Instruction width 8)) (root : Fin graph.nodeCount) :
    exhausted parameters graph T F heap layout coordinateBase slot entry trueCode root + 2 =
      entry + (code parameters graph T F heap layout coordinateBase slot offset entry trueCode root).length := by
  unfold code exhausted queryEntry healthyEntry skipEntry
  simp only [List.length_append, Array.length_toList, SharedRootTaggedCursor.code_size,
    SharedRootResumeEntry.skipCode_size, SharedRootHealthyEntry.code_size,
    ForestZeroRootLoop.exhaustedCode, List.length_cons, List.length_nil]
  omega

theorem code_capacity (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels))
    (heap : Array (Word (SharedMachineCapacity.wordWidth retained graph.countedSize (NativeSourceExecution.selectedSize parameters).total)))
    (layout : Layout (parameters.channels + graph.nodeCount) heap.size)
    (coordinateBase slot offset entry : Nat)
    (trueCode : List (Instruction (SharedMachineCapacity.wordWidth retained graph.countedSize (NativeSourceExecution.selectedSize parameters).total) 8))
    (root : Fin graph.nodeCount) (entryBound : entry ≤ retained) (trueBound : trueCode.length ≤ retained) :
    entry + (code parameters graph T F heap layout coordinateBase slot offset entry trueCode root).length <
      2 ^ SharedMachineCapacity.wordWidth retained graph.countedSize (NativeSourceExecution.selectedSize parameters).total := by
  have bound := code_length_bound parameters graph T F heap layout coordinateBase slot offset entry trueCode root
  have capacity := SharedMachineCapacity.capacity retained graph.countedSize (NativeSourceExecution.selectedSize parameters).total
  omega

end Controller.Cost.SharedRootDetectorCode
