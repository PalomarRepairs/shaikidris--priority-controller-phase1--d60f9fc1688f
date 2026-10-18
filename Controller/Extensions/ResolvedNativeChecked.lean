module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Extensions.ResolvedNativeProfile
public import Controller.Extensions.ResolvedNativeResident
public import Controller.Cost.SharedZeroNativeQuery

@[expose] public section

/-! The native query's actual terminal FIFO supplies an admissible changing
channel set. Its emitted canonical physical/source lift passes the native
model checker for the original decoder. -/
namespace Controller.Extensions.ResolvedNativeChecked
open Controller Controller.Decoder Controller.Decoder.DAG Controller.CNF Controller.Cost
open Controller.Native Controller.Native.SourceController Controller.Cost.NativeSourceExecution
open Controller.Cost.ForestZeroCompile Controller.Cost.ForestZeroAdmissibleCaller
open Controller.Extensions.BoundedAnd

private def atIndex (graph : DAG n) (assignment : Assignment n) (index : Nat) : Bool :=
  if below : index<graph.nodeCount then graph.eval assignment ⟨index,below⟩ else false

theorem resolved_zero (graph : DAG n) (right : Finset (Fin graph.nodeCount))
    (K : Finset (Channel n)) (root : Fin graph.nodeCount)
    (zero : (resolved graph right).eval (assignmentOfSet K) root = false) :
    graph.eval (assignmentOfSet K) root = false := by
  have transported := congrArg (fun g => atIndex g (assignmentOfSet K) root.val) (resolved_eq_expansion graph right)
  have evaluation : (resolved graph right).eval (assignmentOfSet K) root =
      (graph.expansion Finset.univ (fun i => decide (i.val ∈ right))).eval (assignmentOfSet K) root := by
    dsimp only [atIndex,resolved,DAG.expansion] at transported
    simpa only [dite_eq_left root.isLt] using transported
  rw [evaluation] at zero
  cases value : graph.eval (assignmentOfSet K) root with
  | false => rfl
  | true =>
    have truth := graph.true_implies_expansion_true Finset.univ (fun i => decide (i.val ∈ right)) _ root value
    rw [zero] at truth
    contradiction

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1800000 in
theorem checked (parameters : Parameters) (raw : parameters.layout = .raw) (drive : parameters.drive = true)
    (right : Finset (Fin parameters.decoder.nodeCount)) (root : Fin parameters.decoder.nodeCount)
    (member : root ∈ parameters.decoder.roots)
    (healthy : parameters.decoder.eval (assignmentOfSet {parameters.bridge.target}) root = true)
    (heap : Array (Word width)) (layout : ForestZeroDictionary.Layout
      (parameters.channels+parameters.decoder.nodeCount) heap.size)
    (observed : List (Word width)) (fits : 1<2^width)
    (witness : SharedZeroNativeQuery.QueryNativeWitness parameters heap layout
      (ResolvedResident.refs 2 (ResolvedResident.rows parameters.decoder right parameters.buses parameters.bridge.target root))
      (by omega) observed) :
    Certificate.ModelCheck.check (formula parameters)
      (NativeRealizedChecked.decodeOutput observed (compile parameters).toState.count) = true := by
  let graph := parameters.decoder
  let refs := ResolvedResident.refs 2 (ResolvedResident.rows graph right parameters.buses parameters.bridge.target root)
  let dictionary := constructorDictionary heap layout (empty _) refs
  obtain ⟨queue,previous,localModel,_,output⟩ := witness
  have coherent : Coherent dictionary := (rows_dictionary (empty _) (empty_coherent _)
    (ForestZeroAssembly.originalRows (reservedReferences refs))).1
  let assignment := ForestZeroModelLift.lift dictionary true (extendNat (Horn.WorklistOutcome.offAssignment queue))
  have nonempty : ∀ values, Satisfies values (ofClauses (ForestZeroAssembly.originalRows refs)) →
      ∃ channel : Channel parameters.channels, values ⟨channel.val,by have := channel.isLt; omega⟩ = true := by
    intro values model
    apply SharedZeroMeaning.source_nonempty (base := 0) (slot := 0) (resolved graph right)
      parameters.buses parameters.bridge.target ∅ ∅ root values
    rw [SharedZeroSource.originalRows_eq]
    simpa only [refs,ResolvedResident.original_rows,ResolvedResident.rows] using model
  have original := (SharedZeroModel.constructor_lift_model heap layout (empty _) (empty_coherent _) refs
    parameters.channels (by omega) nonempty _).mp localModel
  have template : Satisfies assignment (SharedZeroTemplate.formula (resolved graph right)
      parameters.buses parameters.bridge.target root ∅ ∅) := by
    simpa only [refs,ResolvedResident.original_rows,ResolvedResident.rows,ofClauses,Array.toArray_toList,
      assignment,dictionary] using original
  have projected := SharedZeroOutput.finite_model_projection (resolved graph right) (resolved_guarded graph right)
    parameters.buses parameters.bridge.target ∅ ∅ root assignment
    ((SharedZeroTemplate.satisfies_iff (resolved graph right) parameters.buses parameters.bridge.target root ∅ ∅ assignment).mp template)
  let K := setOfAssignment (SharedZeroNative.channels parameters dictionary queue (by omega))
  have sameChannels : K = (resolved graph right).zeroChannelSet (assignment ∘ (resolved graph right).zeroIndex) := by
    unfold K DAG.zeroChannelSet
    apply congrArg setOfAssignment
    funext channel
    change ForestZeroModelLift.lift dictionary true (ForestZeroChannelPush.localValues queue)
      ⟨channel.val,by have := channel.isLt; omega⟩ = assignment ((resolved graph right).zeroIndex (.inl channel))
    rw [show ForestZeroChannelPush.localValues queue = ForestZeroChannelEmit.localValues queue from rfl,
      SharedZeroOutput.queue_lift dictionary coherent queue]
    rfl
  rw [← sameChannels] at projected
  have zero := resolved_zero graph right K root projected.2.2
  have differs : ∃ output, parameters.observations output (assignmentOfSet {parameters.bridge.target}) ≠
      parameters.observations output (assignmentOfSet K) := by
    obtain ⟨index,equal⟩ := List.mem_iff_get.mp member
    refine ⟨index,?_⟩
    change graph.eval (assignmentOfSet {parameters.bridge.target}) graph.roots[index.val] ≠
      graph.eval (assignmentOfSet K) graph.roots[index.val]
    change graph.roots[index.val] = root at equal
    rw [equal,healthy,zero]
    decide
  rw [output,NativeRealizedChecked.output_decodes _ _ fits]
  exact SourceLift.eligible_checked parameters raw K projected.1 drive differs

theorem execution (parameters : Parameters) (raw : parameters.layout = .raw) (drive : parameters.drive = true)
    (right : Finset (Fin parameters.decoder.nodeCount)) (reference root : Fin parameters.decoder.nodeCount)
    (member : root ∈ parameters.decoder.roots)
    (healthy : parameters.decoder.eval (assignmentOfSet {parameters.bridge.target}) root = true)
    (resident : Program width 8) (entry next : Nat) (rest : List (Word width)) (state : State width 8)
    (ready : ResolvedResident.Ready parameters.decoder right parameters.buses parameters.bridge.target root entry rest state)
    (entryBound : entry ≤ 1024*(parameters.decoder.countedSize+1))
    (capacity : 4096*(parameters.decoder.countedSize+(selectedSize parameters).total+1)<2^width)
    (existsZero : ∃ K, Admissible parameters.buses parameters.bridge.target K ∧
      (resolved parameters.decoder right).eval (assignmentOfSet K) root = false)
    (present : SharedRootRead.BlockAt resident entry
      (ResolvedNativeResident.code parameters parameters.decoder parameters.buses parameters.bridge.target reference
        width entry state.heap.size next)) :
    ∃ final ticks peak, Execution resident state final ticks peak ∧ final.halted = true ∧
      final.reg 4 = word width 1 ∧ ticks ≤ 5000*(parameters.decoder.countedSize+1)+55*(selectedSize parameters).total ∧
      peak ≤ state.liveWords+200*(parameters.decoder.countedSize+1)+3*(selectedSize parameters).total ∧
      Certificate.ModelCheck.check (formula parameters)
        (NativeRealizedChecked.decodeOutput final.output (compile parameters).toState.count) = true := by
  obtain ⟨final,ticks,peak,trace,halted,decision,time,space,witness⟩ :=
    ResolvedNativeResident.execution parameters parameters.decoder right parameters.buses parameters.bridge.target
      reference root resident entry next rest state ready entryBound capacity existsZero present
  exact ⟨final,ticks,peak,trace,halted,decision,time,space,
    checked parameters raw drive right root member healthy state.heap _ final.output (by omega) witness⟩

end Controller.Extensions.ResolvedNativeChecked
