module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedRootTaggedCursor
public import Controller.Cost.SharedTrueHandler

@[expose] public section

namespace Controller.Cost.SharedRootTaggedTrue
open Controller.Cost.GateProgram Controller.Cost.RawTransferLoops
open Controller.Cost.ForestZeroAdmissibleCaller
open Controller.Native Controller.Native.SourceController Controller.Decoder
open Controller.Cost.NativeSourceExecution

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4096 in
theorem execution (parameters : Parameters) (raw : parameters.layout = .raw) (drive : parameters.drive = true)
    (graph : DAG parameters.channels) (T F : Finset (Fin parameters.channels))
    (index : Fin graph.roots.length) (observation : Fin parameters.decoder.roots.length)
    (observationEq : ∀ K, parameters.observations observation (assignmentOfSet K) = graph.eval (assignmentOfSet K) graph.roots[index.val])
    (consistent : FixedConsistent (extensionBase parameters.buses parameters.bridge.target T) F)
    (healthyFalse : graph.eval (assignmentOfSet {parameters.bridge.target}) graph.roots[index.val] = false)
    (program : Program width 8) (state : State width 8) (sourceHeap : Array (Word width))
    (tableBase inverseBase maskBase entry exhausted zeroQuery skipEntry source count : Nat)
    (rest : List (Word width))
    (found : SharedWitnessDecode.tag graph (extensionBase parameters.buses parameters.bridge.target T) F width index ≠ word width (parameters.channels + 1))
    (ready : QueryReady (ambient := ambient) sourceHeap tableBase inverseBase entry
      (word width source :: word width (count + 1) :: word width (parameters.channels + 1) :: rest) state)
    (capacity : 256 * (graph.countedSize + 1) < 2 ^ width)
    (countFits : count + 1 < 2 ^ width) (sourceFits : source < 2 ^ width)
    (sourceValid : source < state.heap.size)
    (candidateStored : state.heap[source]? = some
      (SharedWitnessDecode.tag graph (extensionBase parameters.buses parameters.bridge.target T) F width index))
    (handlerRoom : entry + 22 + (SharedTrueHandler.code parameters width state.heap.size maskBase (entry + 22)).length < 2 ^ width)
    (addressRoom : maskBase + parameters.channels < 2 ^ width)
    (maskBound : maskBase + parameters.channels ≤ state.heap.size)
    (nativeRoom : state.heap.size + parameters.channels + (compile parameters).toState.count < 2 ^ width)
    (maskStored : ∀ channel : Fin parameters.channels, state.heap[maskBase + channel.val]? =
      some (word width (if assignmentOfSet (extensionBase parameters.buses parameters.bridge.target T) channel then 1 else 0)))
    (cursorAt : CodeAt program entry (SharedRootTaggedCursor.code width parameters.channels entry exhausted zeroQuery skipEntry))
    (handlerAt : SharedRootRead.BlockAt program (entry + 22)
      (SharedTrueHandler.code parameters width state.heap.size maskBase (entry + 22))) :
    ∃ final ticks peak, Execution program state final ticks peak ∧
      ticks ≤ 14 * parameters.channels + 16 * SourceInitialIDs.rootCount parameters + 13 * (selectedSize parameters).total +
        7 * (compile parameters).toState.count + 26 ∧
      peak ≤ state.liveWords + parameters.channels + 2 * (compile parameters).toState.count ∧
      final.halted = true ∧ final.reg 4 = word width 1 ∧ final.heap = state.heap ∧ final.stack = rest ∧
      Certificate.ModelCheck.check (formula parameters)
        (NativeRealizedChecked.decodeOutput final.output (compile parameters).toState.count) = true := by
  have size := graph.countedSize_eq
  obtain ⟨inspected, cursorTicks, cursorTrace, cursorTime, heap, stack, output, pc, active, sourceHeld, nextHeld, countHeld, candidateHeld⟩ :=
    SharedRootTaggedCursor.successor_execution program state parameters.channels entry exhausted zeroQuery skipEntry source count
      parameters.bridge.target false
      (SharedWitnessDecode.tag graph (extensionBase parameters.buses parameters.bridge.target T) F width index) rest
      ready.position ready.running (by omega) (by omega) countFits sourceFits sourceValid candidateStored
      (by simpa using ready.stack) cursorAt
  have handlerPC : inspected.pc = word width (entry + 22) := by
    simpa only [Bool.false_eq_true, ↓reduceIte, ite_eq_right found] using pc
  obtain ⟨final, handlerTicks, handlerTrace, handlerTime, halted, decision, finalHeap, finalStack, finalOutput, checked⟩ :=
    SharedTrueHandler.execution parameters program inspected (extensionBase parameters.buses parameters.bridge.target T)
      (SharedWitnessDecode.tag graph (extensionBase parameters.buses parameters.bridge.target T) F width index) maskBase (entry + 22)
      handlerPC active (by rw [heap]; exact handlerRoom) (by omega) addressRoom
      (by rw [heap]; exact maskBound) (by rw [heap]; exact nativeRoom) candidateHeld
      (by intro channel; rw [heap]; exact maskStored channel) (by rw [heap]; exact handlerAt)
  have inspectedLive : inspected.liveWords + 3 = state.liveWords := by
    simp only [State.liveWords, heap, stack, output, ready.stack, List.length_cons]
    omega
  have meaning := SharedWitnessDecode.decoded_extension graph parameters.buses parameters.bridge.target T F width index consistent capacity found
  obtain ⟨eligible, fixed, truth⟩ := meaning
  have differs : ∃ observation, parameters.observations observation (assignmentOfSet {parameters.bridge.target}) ≠
      parameters.observations observation (assignmentOfSet
        (SharedWitnessDecode.decode (extensionBase parameters.buses parameters.bridge.target T)
          (SharedWitnessDecode.tag graph (extensionBase parameters.buses parameters.bridge.target T) F width index))) := by
    refine ⟨observation, ?_⟩
    rw [observationEq, observationEq, healthyFalse, truth]
    decide
  refine ⟨final, cursorTicks + handlerTicks,
    max state.liveWords (inspected.liveWords + parameters.channels + 2 * (compile parameters).toState.count),
    cursorTrace.append handlerTrace, by omega, ?_, halted, decision, finalHeap.trans heap, finalStack.trans stack,
    checked raw drive eligible differs⟩
  apply max_le <;> omega

end Controller.Cost.SharedRootTaggedTrue
