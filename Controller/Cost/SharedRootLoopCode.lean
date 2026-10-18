module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedRootIteration

@[expose] public section

namespace Controller.Cost.SharedRootLoopCode
open Controller.Cost.GateProgram Controller.Cost.RawTransferLoops
open Controller.Cost.ForestZeroAdmissibleCaller
open Controller.Cost.ForestZeroDictionary Controller.Native Controller.Native.SourceController Controller.Decoder

def exhausted (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels)) (heap : Array (Word width))
    (layout : Layout (parameters.channels + graph.nodeCount) heap.size)
    (coordinateBase slot entry : Nat) (root : Fin graph.nodeCount) : Nat :=
  entry + 15 + (SharedQueryReuseCode.code parameters graph T F heap layout coordinateBase slot (entry + 15) entry root).length

@[irreducible] def code (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels)) (heap : Array (Word width))
    (layout : Layout (parameters.channels + graph.nodeCount) heap.size)
    (coordinateBase slot entry : Nat) (root : Fin graph.nodeCount) : List (Instruction width 8) :=
  SharedRootIteration.code parameters graph T F heap layout coordinateBase slot entry
    (exhausted parameters graph T F heap layout coordinateBase slot entry root) root ++
  (ForestZeroRootLoop.exhaustedCode width).toList

theorem body_at (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels)) (heap : Array (Word width))
    (layout : Layout (parameters.channels + graph.nodeCount) heap.size)
    (coordinateBase slot entry : Nat) (root : Fin graph.nodeCount) (program : Program width 8)
    (present : SharedRootRead.BlockAt program entry (code parameters graph T F heap layout coordinateBase slot entry root)) :
    SharedRootRead.BlockAt program entry (SharedRootIteration.code parameters graph T F heap layout
      coordinateBase slot entry (exhausted parameters graph T F heap layout coordinateBase slot entry root) root) := by
  unfold code at present
  intro offset below
  have found := present offset (by simp only [List.length_append]; omega)
  rw [List.getElem?_append_left below] at found
  exact found

theorem exhausted_at (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels)) (heap : Array (Word width))
    (layout : Layout (parameters.channels + graph.nodeCount) heap.size)
    (coordinateBase slot entry : Nat) (root : Fin graph.nodeCount) (program : Program width 8)
    (present : SharedRootRead.BlockAt program entry (code parameters graph T F heap layout coordinateBase slot entry root)) :
    ∀ phase : Fin 2, program[exhausted parameters graph T F heap layout coordinateBase slot entry root + phase.val]? =
      (ForestZeroRootLoop.exhaustedCode width)[phase.val]? := by
  have joined : SharedRootRead.BlockAt program entry
      (SharedRootIteration.code parameters graph T F heap layout coordinateBase slot entry
        (exhausted parameters graph T F heap layout coordinateBase slot entry root) root ++
        (ForestZeroRootLoop.exhaustedCode width).toList ++ []) := by
    simpa only [code, List.append_nil] using present
  have found := SharedNativeSuccessCode.segment program entry _ _ _ joined
  have length : entry + (SharedRootIteration.code parameters graph T F heap layout coordinateBase slot entry
      (exhausted parameters graph T F heap layout coordinateBase slot entry root) root).length =
      exhausted parameters graph T F heap layout coordinateBase slot entry root := by
    unfold SharedRootIteration.code exhausted
    simp only [List.length_append, Array.length_toList, SharedRootCursorEntry.code_size]
    omega
  rw [length] at found
  intro phase
  simpa only [Array.getElem?_toList] using found phase.val (by simpa [ForestZeroRootLoop.exhaustedCode] using phase.isLt)

theorem shared (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels)) (before after : Array (Word width))
    (beforeLayout : Layout (parameters.channels + graph.nodeCount) before.size)
    (afterLayout : Layout (parameters.channels + graph.nodeCount) after.size)
    (coordinateBase slot entry : Nat) (left right : Fin graph.nodeCount)
    (sameSize : before.size = after.size) (sameTable : beforeLayout.tableBase = afterLayout.tableBase) :
    code parameters graph T F before beforeLayout coordinateBase slot entry left =
      code parameters graph T F after afterLayout coordinateBase slot entry right := by
  have sameQuery := SharedQueryReuseCode.shared parameters graph T F before after beforeLayout afterLayout
    coordinateBase slot (entry + 15) entry left right sameSize
  have sameExhausted : exhausted parameters graph T F before beforeLayout coordinateBase slot entry left =
      exhausted parameters graph T F after afterLayout coordinateBase slot entry right := by
    unfold exhausted
    rw [sameQuery]
  unfold code
  rw [sameExhausted, SharedRootIteration.code_shared parameters graph T F before after beforeLayout afterLayout
    coordinateBase slot entry _ left right sameSize sameTable]

open Controller.Cost.NativeSourceExecution

theorem code_length_bound (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels)) (heap : Array (Word width))
    (layout : Layout (parameters.channels + graph.nodeCount) heap.size)
    (coordinateBase slot entry : Nat) (root : Fin graph.nodeCount) :
    (code parameters graph T F heap layout coordinateBase slot entry root).length ≤
      410 * (graph.countedSize + 1) + 34 * (selectedSize parameters).total + 529 := by
  have queryBound : (SharedQueryReuseCode.code parameters graph T F heap layout coordinateBase slot
      (entry + 15) entry root).length ≤ 410 * (graph.countedSize + 1) + 34 * (selectedSize parameters).total + 512 := by
    unfold SharedQueryReuseCode.code
    dsimp only
    exact SharedQueryHeapCapacity.code_length_bound parameters graph T F root width (entry + 15) heap.size _ _ _ entry
  unfold code SharedRootIteration.code
  simp only [List.length_append, Array.length_toList, SharedRootCursorEntry.code_size,
    ForestZeroRootLoop.exhaustedCode, List.length_cons, List.length_nil]
  omega

theorem code_end (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels)) (heap : Array (Word width))
    (layout : Layout (parameters.channels + graph.nodeCount) heap.size)
    (coordinateBase slot entry : Nat) (root : Fin graph.nodeCount) :
    exhausted parameters graph T F heap layout coordinateBase slot entry root + 2 =
      entry + (code parameters graph T F heap layout coordinateBase slot entry root).length := by
  unfold exhausted code SharedRootIteration.code
  simp only [List.length_append, Array.length_toList, SharedRootCursorEntry.code_size,
    ForestZeroRootLoop.exhaustedCode, List.length_cons, List.length_nil]
  omega

theorem cursor_at (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels)) (heap : Array (Word width))
    (layout : Layout (parameters.channels + graph.nodeCount) heap.size)
    (coordinateBase slot entry : Nat) (root : Fin graph.nodeCount) (program : Program width 8)
    (present : SharedRootRead.BlockAt program entry (code parameters graph T F heap layout coordinateBase slot entry root)) :
    CodeAt program entry (SharedRootCursor.code width (exhausted parameters graph T F heap layout coordinateBase slot entry root)) := by
  have body := body_at parameters graph T F heap layout coordinateBase slot entry root program present
  unfold SharedRootIteration.code at body
  intro phase
  have below : phase.val < 10 := by simpa using phase.isLt
  have found := body phase.val (by simp only [List.length_append, Array.length_toList, SharedRootCursorEntry.code_size]; omega)
  rw [List.getElem?_append_left (by simp only [Array.length_toList, SharedRootCursorEntry.code_size]; omega)] at found
  simp only [Array.getElem?_toList, SharedRootCursorEntry.code, Array.getElem?_append,
    SharedRootCursor.code_size] at found
  exact found.trans (ite_eq_left below)

theorem code_capacity (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels))
    (heap : Array (Word (SharedMachineCapacity.wordWidth retained graph.countedSize (selectedSize parameters).total)))
    (layout : Layout (parameters.channels + graph.nodeCount) heap.size)
    (coordinateBase slot entry : Nat) (root : Fin graph.nodeCount) (entryBound : entry ≤ retained) :
    entry + (code parameters graph T F heap layout coordinateBase slot entry root).length <
      2 ^ SharedMachineCapacity.wordWidth retained graph.countedSize (selectedSize parameters).total := by
  have length := code_length_bound parameters graph T F heap layout coordinateBase slot entry root
  have capacity := SharedMachineCapacity.capacity retained graph.countedSize (selectedSize parameters).total
  omega


theorem empty_execution (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels))
    (program : Program (SharedMachineCapacity.wordWidth retained graph.countedSize (selectedSize parameters).total) 8)
    (state : State (SharedMachineCapacity.wordWidth retained graph.countedSize (selectedSize parameters).total) 8)
    (sourceHeap : Array (Word (SharedMachineCapacity.wordWidth retained graph.countedSize (selectedSize parameters).total)))
    (layout : Layout (parameters.channels + graph.nodeCount) state.heap.size)
    (coordinateBase slot entry source : Nat) (root : Fin graph.nodeCount)
    (rest : List (Word (SharedMachineCapacity.wordWidth retained graph.countedSize (selectedSize parameters).total)))
    (ready : QueryReady (ambient := parameters.channels + graph.nodeCount) sourceHeap
      layout.tableBase layout.inverseBase entry
      (word (SharedMachineCapacity.wordWidth retained graph.countedSize (selectedSize parameters).total) source ::
       word (SharedMachineCapacity.wordWidth retained graph.countedSize (selectedSize parameters).total) 0 :: rest) state)
    (entryBound : entry ≤ retained)
    (present : SharedRootRead.BlockAt program entry
      (code parameters graph T F state.heap layout coordinateBase slot entry root)) :
    ∃ final, Execution program state final 5 state.liveWords ∧
      final.halted = true ∧
      final.reg 4 = word (SharedMachineCapacity.wordWidth retained graph.countedSize (selectedSize parameters).total) 0 ∧
      final.heap = state.heap ∧ final.stack = rest ∧ final.output = state.output := by
  have capacity := code_capacity parameters graph T F state.heap layout coordinateBase slot entry root entryBound
  have ending := code_end parameters graph T F state.heap layout coordinateBase slot entry root
  have cursorRoom : entry + 10 <
      2 ^ SharedMachineCapacity.wordWidth retained graph.countedSize (selectedSize parameters).total := by
    unfold code SharedRootIteration.code at capacity
    simp only [List.length_append, Array.length_toList, SharedRootCursorEntry.code_size] at capacity
    omega
  exact SharedRootCursor.zero_halts program state sourceHeap layout.tableBase layout.inverseBase entry
    (exhausted parameters graph T F state.heap layout coordinateBase slot entry root) source rest ready
    cursorRoom (cursor_at parameters graph T F state.heap layout coordinateBase slot entry root program present)
    (by omega) (exhausted_at parameters graph T F state.heap layout coordinateBase slot entry root program present)

end Controller.Cost.SharedRootLoopCode
