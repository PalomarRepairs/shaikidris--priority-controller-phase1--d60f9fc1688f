module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Extensions.ResolvedSourcePrepare
public import Controller.Extensions.ResolvedNativeChecked
public import Controller.Extensions.ResolvedRootSource

@[expose] public section

/-! The successful selector continuation starts with the original retained
source and mask, constructs its selected query packet, extracts the solver's
actual channel witness, emits a checked native model and halts. -/
namespace Controller.Extensions.ResolvedNativeSource
open Controller Controller.Decoder Controller.Decoder.DAG Controller.Cost
open Controller.Native Controller.Native.SourceController Controller.Cost.NativeSourceExecution
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestInputStored
open Controller.Cost.SharedDetectorAssembly

def code (parameters : Parameters) (width : Nat) (packet : Array (Word width)) (rows : List Row) (roots : List Nat)
    (reference : Fin parameters.decoder.nodeCount) (rootSlot entry sourceCount : Nat) : List (Instruction width 8) :=
  let graph := parameters.decoder
  let p := ResolvedSourcePrepare.positions width graph packet rows roots parameters.buses parameters.bridge.target reference rootSlot entry
  let keep := (ResolvedResident.sourceHeap width parameters.channels graph.nodeCount
    (ResolvedResident.rows graph ∅ parameters.buses parameters.bridge.target reference)).size
  ResolvedSourcePrepare.code width graph packet rows roots parameters.buses parameters.bridge.target reference rootSlot entry sourceCount ++
    ResolvedNativeResident.code parameters graph parameters.buses parameters.bridge.target reference width p.solver keep 0

theorem code_bound (parameters : Parameters) (packet : Array (Word width)) (rows : List Row) (roots : List Nat)
    (reference : Fin parameters.decoder.nodeCount) :
    (code parameters width packet rows roots reference rootSlot entry sourceCount).length ≤
      1200*(parameters.decoder.countedSize+1)+34*(selectedSize parameters).total := by
  have prefixBound := ResolvedSourcePrepare.code_bound (width := width) (rootSlot := rootSlot) (entry := entry)
    (sourceCount := sourceCount) parameters.decoder packet rows roots parameters.buses parameters.bridge.target reference
  have nativeBound := ResolvedNativeResident.code_bound (width := width) (entry :=
      (ResolvedSourcePrepare.positions width parameters.decoder packet rows roots parameters.buses parameters.bridge.target reference rootSlot entry).solver)
    (keep := (ResolvedResident.sourceHeap width parameters.channels parameters.decoder.nodeCount
      (ResolvedResident.rows parameters.decoder ∅ parameters.buses parameters.bridge.target reference)).size)
    (next := 0) parameters parameters.decoder parameters.buses parameters.bridge.target reference
  simp only [code,List.length_append]
  omega

theorem code_uniform (parameters : Parameters) (left right : Array (Word width)) (rows : List Row) (roots : List Nat)
    (sameSize : left.size = right.size) (reference : Fin parameters.decoder.nodeCount)
    (rootSlot entry sourceCount : Nat) :
    code parameters width left rows roots reference rootSlot entry sourceCount =
      code parameters width right rows roots reference rootSlot entry sourceCount := by
  have plan := ResolvedRootSource.plan_uniform parameters.decoder left right rows roots sameSize
    parameters.buses parameters.bridge.target rootSlot
  simp only [code,ResolvedSourcePrepare.code,ResolvedSourcePrepare.positions,ResolvedSourceCallback.emitCode,plan,
    cacheHeap_size,sameSize]

set_option maxHeartbeats 1800000 in
theorem execution (parameters : Parameters) (raw : parameters.layout = .raw) (drive : parameters.drive = true)
    (resident : Program width 8) (state : State width 8) (packet : Array (Word width)) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch parameters.decoder rows) (right : Finset (Fin parameters.decoder.nodeCount))
    (reference root : Fin parameters.decoder.nodeCount) (rootSlot entry : Nat)
    (member : root ∈ parameters.decoder.roots)
    (healthy : parameters.decoder.eval (assignmentOfSet {parameters.bridge.target}) root = true)
    (heapStored : state.heap = withValues (cacheHeap width packet rows roots)
      (ResolvedSourcePlan.selectorValues parameters.decoder right))
    (rootStored : state.heap[rootSlot]? = some (word width root.val))
    (channelStored : state.heap[0]? = some (word width parameters.channels))
    (nodeStored : state.heap[1]? = some (word width parameters.decoder.nodeCount))
    (positive : 0<state.heap.size) (position : state.pc = word width entry) (running : state.halted = false)
    (entryBound : entry ≤ 128*(parameters.decoder.countedSize+1))
    (sourceBound : state.heap.size ≤ 40*(parameters.decoder.countedSize+1))
    (capacity : 4096*(parameters.decoder.countedSize+(selectedSize parameters).total+1)<2^width)
    (existsZero : ∃ K, Admissible parameters.buses parameters.bridge.target K ∧
      (BoundedAnd.resolved parameters.decoder right).eval (assignmentOfSet K) root = false)
    (present : SharedRootRead.BlockAt resident entry
      (code parameters width packet rows roots reference rootSlot entry state.heap.size)) :
    ∃ final ticks peak, Execution resident state final ticks peak ∧ final.halted = true ∧
      final.reg 4 = word width 1 ∧ ticks ≤ 6000*(parameters.decoder.countedSize+1)+55*(selectedSize parameters).total ∧
      peak ≤ state.liveWords+300*(parameters.decoder.countedSize+1)+3*(selectedSize parameters).total ∧
      Certificate.ModelCheck.check (formula parameters)
        (NativeRealizedChecked.decodeOutput final.output (compile parameters).toState.count) = true := by
  let graph := parameters.decoder
  let p := ResolvedSourcePrepare.positions width graph packet rows roots parameters.buses parameters.bridge.target reference rootSlot entry
  have baseCapacity : 4096*(graph.countedSize+1)<2^width := by dsimp only [graph]; omega
  have prepareAt := block_left resident entry _ _ present
  have nativeAt := block_right resident entry _ _ present
  rw [ResolvedSourcePrepare.code_end] at nativeAt
  obtain ⟨prepared,pt,pp,prepare,ptime,pspace,_,entryFits,ready⟩ :=
    ResolvedSourcePrepare.execution resident state packet graph rows roots matched right parameters.buses parameters.bridge.target
      reference root rootSlot entry heapStored rootStored channelStored nodeStored positive position running entryBound sourceBound
      baseCapacity prepareAt
  have localEntry : p.solver ≤ 512*(parameters.decoder.countedSize+1) := entryFits
  have prefixTime : pt ≤ 1000*(parameters.decoder.countedSize+1) := ptime
  have prefixSpace : pp ≤ state.liveWords+30*(parameters.decoder.countedSize+1) := pspace
  have preparedSize : prepared.heap.size = (ResolvedResident.sourceHeap width parameters.channels graph.nodeCount
      (ResolvedResident.rows graph ∅ parameters.buses parameters.bridge.target reference)).size :=
    ready.heapSize.trans (ResolvedResident.source_size_uniform graph right ∅ parameters.buses parameters.bridge.target root reference)
  obtain ⟨final,nt,np,native,halted,decision,ntime,nspace,checked⟩ :=
    ResolvedNativeChecked.execution parameters raw drive right reference root member healthy resident p.solver 0 state.stack
      prepared ready (by omega) capacity existsZero (by simpa only [preparedSize] using nativeAt)
  have preparedLive : prepared.liveWords ≤ state.liveWords+30*(parameters.decoder.countedSize+1) :=
    (Execution.final_storage_le prepare).trans prefixSpace
  exact ⟨final,pt+nt,max pp np,prepare.append native,halted,decision,by omega,by omega,checked⟩

end Controller.Extensions.ResolvedNativeSource
