module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedRootCursorEntry

@[expose] public section

namespace Controller.Cost.SharedRootQueryRetarget
open Controller.Cost.GateProgram Controller.Cost.ForestZeroDictionary
open Controller.Cost.ForestZeroAdmissibleCaller Controller.Cost.ForestZeroEmit
open Controller.Native Controller.Native.SourceController Controller.Decoder
open Controller.Cost.SharedZeroResidentConditions Controller.Cost.SharedQuerySourceFrame

theorem source_conditions (parameters : Parameters) (graph : DAG parameters.channels)
    (guarded : graph.Guarded) (T F : Finset (Fin parameters.channels))
    (oldRoot root : Fin graph.nodeCount) (before after : State width 8)
    (original : Layout (parameters.channels + graph.nodeCount) before.heap.size)
    (coordinateBase slot sourceEnd : Nat)
    (source : SourceConditions parameters before original
      (SharedZeroSource.references graph parameters.buses parameters.bridge.target T F coordinateBase slot oldRoot)
      sourceEnd graph.nodeCount)
    (slotBound : slot < sourceEnd) (headerBefore : 1 < slot)
    (tableBefore : coordinateBase + (parameters.channels + graph.nodeCount) ≤ slot)
    (sameSize : after.heap.size = before.heap.size)
    (heap : after.heap = before.heap.set slot (word width root.val) (by have := source.sourceBound; omega)) :
    SourceConditions parameters after (SharedQuerySourceFrame.layout before after original sameSize)
      (SharedZeroSource.references graph parameters.buses parameters.bridge.target T F coordinateBase slot root)
      sourceEnd graph.nodeCount := by
  have valid : slot < before.heap.size := by have := source.sourceBound; omega
  refine {
    sourceReferences := ?_
    sourceBeforeTable := source.sourceBeforeTable
    sourceBeforeInverse := source.sourceBeforeInverse
    sourceBound := by rw [sameSize]; exact source.sourceBound
    sourcePositive := source.sourcePositive
    sourceChannel := ?_
    sourceNodes := ?_
    ambientEq := source.ambientEq
    adjacent := source.adjacent
    tablePositive := source.tablePositive
    sourceHeaderRoom := source.sourceHeaderRoom
    sourceDual := SharedQuerySourceFrame.zero_dualHorn graph guarded parameters.buses parameters.bridge.target T F
      root coordinateBase slot
    sourceEndpoint := by
      change after.heap.size = original.inverseBase + (parameters.channels + graph.nodeCount)
      rw [sameSize]
      exact source.sourceEndpoint
  }
  · simpa only [heap] using SharedQuerySourceFrame.references_after_root graph parameters.buses
      parameters.bridge.target T F oldRoot root before.heap coordinateBase slot sourceEnd
      source.sourceBound slotBound (by omega) source.sourceChannel source.sourceReferences tableBefore
  · rw [heap, Array.getElem?_set_ne valid (by omega)]
    exact source.sourceChannel
  · rw [heap, Array.getElem?_set_ne valid (by omega)]
    exact source.sourceNodes

end Controller.Cost.SharedRootQueryRetarget
