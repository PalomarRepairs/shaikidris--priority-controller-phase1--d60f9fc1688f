module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedRootCursor

@[expose] public section

namespace Controller.Cost.SharedRootCursorEntry
open Controller.Cost.GateProgram Controller.Cost.RawTransferLoops
open Controller.Cost.ForestZeroAdmissibleCaller

def code (width exhausted slot tableBase : Nat) : Program width 8 :=
  SharedRootCursor.code width exhausted ++ SharedRootQueryEntry.code width slot tableBase

@[simp] theorem code_size : (code width exhausted slot tableBase).size = 15 := rfl

set_option maxHeartbeats 2000000 in
theorem successor_execution (program : Program width 8) (state : State width 8)
    (sourceHeap : Array (Word width)) (tableBase inverseBase entry exhausted source count slot : Nat)
    (root : Word width) (rest : List (Word width))
    (ready : QueryReady (ambient := ambient) sourceHeap tableBase inverseBase entry
      (word width source :: word width (count + 1) :: rest) state)
    (room : entry + 15 < 2 ^ width) (countFits : count + 1 < 2 ^ width)
    (sourceFits : source < 2 ^ width) (slotFits : slot < 2 ^ width)
    (sourceValid : source < state.heap.size) (slotBefore : slot < tableBase)
    (stored : state.heap[source]? = some root)
    (physical : CodeAt program entry (code width exhausted slot tableBase)) :
    ∃ final, Execution program state final 15 state.liveWords ∧
      final.heap = state.heap.set slot root (by have := ready.sourceFrame.2.1; omega) ∧
      final.output = state.output ∧
      QueryReady (ambient := ambient)
        (sourceHeap.set slot root (by have := ready.sourceFrame.1; omega))
        tableBase inverseBase (entry + 15)
        (word width (source + 1) :: word width count :: rest) final := by
  have all := physical
  unfold code at all
  have cursorAt := RawSharedOrdered.takePrefix program entry _ _ all
  have selectAt := RawSharedOrdered.takeSuffix program entry _ _ all
  obtain ⟨cursor, cursorTrace, cursorHeap, cursorOutput, cursorPointer, cursorReady⟩ :=
    SharedRootCursor.successor_ready program state sourceHeap tableBase inverseBase entry exhausted source count rest
      ready (by omega) countFits sourceFits cursorAt
  obtain ⟨final, selectTrace, finalHeap, finalOutput, finalReady⟩ :=
    SharedRootQueryEntry.execution program cursor sourceHeap tableBase inverseBase (entry + 10) source slot root
      (word width (source + 1) :: word width count :: rest) cursorReady (by omega)
      sourceFits slotFits (by simpa only [cursorHeap] using sourceValid) slotBefore cursorPointer
      (by simpa only [cursorHeap] using stored) (by simpa using selectAt)
  have cursorLive : cursor.liveWords = state.liveWords := by
    simp only [State.liveWords, cursorHeap, cursorOutput, cursorReady.stack, ready.stack, List.length_cons]
  refine ⟨final, ?_, ?_, finalOutput.trans cursorOutput, ?_⟩
  · simpa only [cursorLive, Nat.max_self, Nat.reduceAdd] using cursorTrace.append selectTrace
  · simpa only [cursorHeap] using finalHeap
  · simpa only [Nat.add_assoc, Nat.reduceAdd] using finalReady

open Controller.Native Controller.Native.SourceController Controller.Decoder

set_option maxRecDepth 4096 in
theorem bounded_successor_execution (parameters : Parameters) (graph : DAG parameters.channels)
    (program : Program (SharedMachineCapacity.wordWidth retained graph.countedSize (NativeSourceExecution.selectedSize parameters).total) 8) (state : State (SharedMachineCapacity.wordWidth retained graph.countedSize (NativeSourceExecution.selectedSize parameters).total) 8)
    (sourceHeap : Array (Word (SharedMachineCapacity.wordWidth retained graph.countedSize (NativeSourceExecution.selectedSize parameters).total))) (tableBase inverseBase entry exhausted source count slot : Nat)
    (root : Word (SharedMachineCapacity.wordWidth retained graph.countedSize (NativeSourceExecution.selectedSize parameters).total)) (rest : List (Word (SharedMachineCapacity.wordWidth retained graph.countedSize (NativeSourceExecution.selectedSize parameters).total)))
    (ready : QueryReady (ambient := parameters.channels + graph.nodeCount) sourceHeap tableBase inverseBase entry
      (word (SharedMachineCapacity.wordWidth retained graph.countedSize (NativeSourceExecution.selectedSize parameters).total) source :: word (SharedMachineCapacity.wordWidth retained graph.countedSize (NativeSourceExecution.selectedSize parameters).total) (count + 1) :: rest) state)
    (heapBound : state.heap.size ≤ retained) (entryBound : entry ≤ retained)
    (countBound : count + 1 ≤ graph.roots.length)
    (sourceValid : source < state.heap.size) (slotBefore : slot < tableBase)
    (stored : state.heap[source]? = some root)
    (physical : CodeAt program entry (code (SharedMachineCapacity.wordWidth retained graph.countedSize (NativeSourceExecution.selectedSize parameters).total) exhausted slot tableBase)) :
    ∃ final, Execution program state final 15 state.liveWords ∧
      final.heap = state.heap.set slot root (by have := ready.sourceFrame.2.1; omega) ∧
      final.output = state.output ∧
      QueryReady (ambient := parameters.channels + graph.nodeCount)
        (sourceHeap.set slot root (by have := ready.sourceFrame.1; omega))
        tableBase inverseBase (entry + 15)
        (word (SharedMachineCapacity.wordWidth retained graph.countedSize (NativeSourceExecution.selectedSize parameters).total) (source + 1) :: word (SharedMachineCapacity.wordWidth retained graph.countedSize (NativeSourceExecution.selectedSize parameters).total) count :: rest) final := by
  have room := SharedMachineCapacity.capacity retained graph.countedSize
    (NativeSourceExecution.selectedSize parameters).total
  have graphSize := graph.countedSize_eq
  have tableBound := ready.sourceFrame.2.1
  exact successor_execution program state sourceHeap tableBase inverseBase entry exhausted source count slot
    root rest ready (by omega) (by omega) (by omega) (by omega) sourceValid slotBefore stored physical

end Controller.Cost.SharedRootCursorEntry
