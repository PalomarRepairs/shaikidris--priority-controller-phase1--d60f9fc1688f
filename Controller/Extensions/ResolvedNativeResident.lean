module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Extensions.ResolvedNativeProfile
public import Controller.Extensions.BasisNativeFinish

@[expose] public section

/-! One native-emitting zero query is used only after the decision traversal
has selected a successful expansion. Its source constructor is shared with
the quiet query; the native code is charged once on the successful path. -/
namespace Controller.Extensions.ResolvedNativeResident
open Controller Controller.Decoder Controller.Decoder.DAG Controller.CNF Controller.Cost
open Controller.Native Controller.Native.SourceController
open Controller.Cost.NativeSourceExecution
open Controller.Cost.ForestZeroCompile Controller.Cost.ForestZeroAdmissibleCaller

def templateBase (graph : DAG n) (b : Nat) (target : Channel n) (reference : Fin graph.nodeCount) (width : Nat) : Nat :=
  let state := ResolvedResident.initial graph ∅ b target reference width [] []
  SharedZeroNativeQuery.nativeBase state.heap
    (ResolvedResident.readyLayout graph ∅ b target reference state (ResolvedResident.initial_ready graph ∅ b target reference [] []))
    (ResolvedResident.refs 2 (ResolvedResident.rows graph ∅ b target reference)) n (by omega)

def code (parameters : Parameters) (graph : DAG parameters.channels) (b : Nat)
    (target : Channel parameters.channels) (reference : Fin graph.nodeCount) (width entry keep next : Nat) :
    List (Instruction width 8) :=
  SharedQueryDispatch.code parameters width entry keep (parameters.channels+graph.nodeCount)
    (ResolvedResident.scratchSize keep parameters.channels (parameters.channels+graph.nodeCount)
      (ResolvedResident.rows graph ∅ b target reference))
    (templateBase graph b target reference width)
    (ResolvedResident.refs 2 (ResolvedResident.rows graph ∅ b target reference)) next

theorem dispatch_bound (parameters : Parameters) (graph : DAG parameters.channels)
    (right : Finset (Fin graph.nodeCount)) (b : Nat) (target : Channel parameters.channels) (root : Fin graph.nodeCount)
    (width entry keep base nativeBase next : Nat) :
    (SharedQueryDispatch.code parameters width entry keep (parameters.channels+graph.nodeCount) base nativeBase
      (ResolvedResident.refs 2 (ResolvedResident.rows graph right b target root)) next).length ≤
      900*(graph.countedSize+1)+34*(selectedSize parameters).total+67 := by
  let refs := ResolvedResident.refs 2 (ResolvedResident.rows graph right b target root)
  let solver := SharedQuerySourceCode.solverEntry width entry keep refs
  have quietEnd := EnumerationResident.code_end width entry keep (parameters.channels+graph.nodeCount) base refs
  have nativeEnd := SharedQueryResidentCode.code_end parameters width entry keep (parameters.channels+graph.nodeCount) base nativeBase refs
  have quietBound := ResolvedResident.query_code_bound (width := width) (entry := entry) (keep := keep)
    graph right b target root
  have quietLength : (EnumerationResident.code width entry keep (parameters.channels+graph.nodeCount) base refs).length =
      (ResolvedResident.queryCode graph right b target root width entry keep).length := by
    simp only [ResolvedResident.queryCode,EnumerationResident.code,EnumerationResident.solverCode_length,List.length_append]
    rfl
  rw [quietLength] at quietEnd
  have native := BasisNativeFinish.code_bound parameters width nativeBase (solver+438)
  rw [BasisNativeFinish.code_length] at native
  change entry+(SharedQueryResidentCode.code parameters width entry keep (parameters.channels+graph.nodeCount)
    base nativeBase refs).length = _ at nativeEnd
  simp only [SharedQueryTailCode.cleanup,SharedQueryTailCode.projection,SharedNativeSuccessCode.nativeEntry,
    Nat.add_assoc,Nat.reduceAdd] at nativeEnd
  change entry+(ResolvedResident.queryCode graph right b target root width entry keep).length = solver+430 at quietEnd
  dsimp only [solver,refs] at native
  unfold SharedQueryDispatch.code
  simp only [List.length_append,ForestZeroRootLoop.dispatchCode,List.length_cons,List.length_nil,Nat.reduceAdd]
  dsimp only [solver,refs] at quietEnd nativeEnd quietLength ⊢
  omega

theorem code_bound (parameters : Parameters) (graph : DAG parameters.channels) (b : Nat)
    (target : Channel parameters.channels) (reference : Fin graph.nodeCount) :
    (code parameters graph b target reference width entry keep next).length ≤
      900*(graph.countedSize+1)+34*(selectedSize parameters).total+67 :=
  dispatch_bound parameters graph ∅ b target reference width entry keep _ _ next

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2200000 in
theorem execution (parameters : Parameters) (graph : DAG parameters.channels)
    (right : Finset (Fin graph.nodeCount)) (b : Nat) (target : Channel parameters.channels)
    (reference root : Fin graph.nodeCount) (resident : Program width 8) (entry next : Nat)
    (rest : List (Word width)) (state : State width 8)
    (ready : ResolvedResident.Ready graph right b target root entry rest state)
    (entryBound : entry ≤ 1024*(graph.countedSize+1))
    (capacity : 4096*(graph.countedSize+(selectedSize parameters).total+1)<2^width)
    (existsZero : ∃ K, Admissible b target K ∧ (BoundedAnd.resolved graph right).eval (assignmentOfSet K) root = false)
    (present : SharedRootRead.BlockAt resident entry
      (code parameters graph b target reference width entry state.heap.size next)) :
    let layout := ResolvedResident.readyLayout graph right b target root state ready
    ∃ final ticks peak, Execution resident state final ticks peak ∧ final.halted = true ∧
      final.reg 4 = word width 1 ∧ ticks ≤ 5000*(graph.countedSize+1)+55*(selectedSize parameters).total ∧
      peak ≤ state.liveWords+200*(graph.countedSize+1)+3*(selectedSize parameters).total ∧
      SharedZeroNativeQuery.QueryNativeWitness parameters state.heap layout
        (ResolvedResident.refs 2 (ResolvedResident.rows graph right b target root)) (by omega) final.output := by
  let layout := ResolvedResident.readyLayout graph right b target root state ready
  let refs := ResolvedResident.refs 2 (ResolvedResident.rows graph right b target root)
  let base := SharedZeroNativeQuery.nativeBase state.heap layout refs parameters.channels (by omega)
  have baseCapacity : 4096*(graph.countedSize+1)<2^width := by omega
  have graphSize := graph.countedSize_eq
  have quiet := ResolvedResident.ready_conditions graph right b target root resident entry rest state ready entryBound baseCapacity
  have sameSize : state.heap.size = (ResolvedResident.initial graph ∅ b target reference width [] []).heap.size :=
    ready.heapSize.trans (ResolvedResident.source_size_uniform graph right ∅ b target root reference)
  have nativeBaseEq : base = templateBase graph b target reference width :=
    ResolvedNativeProfile.native_base_uniform graph right ∅ b target root reference state.heap
      (ResolvedResident.initial graph ∅ b target reference width [] []).heap layout
      (ResolvedResident.readyLayout graph ∅ b target reference _ (ResolvedResident.initial_ready graph ∅ b target reference [] [])) sameSize
  have physical : SharedRootRead.BlockAt resident entry
      (SharedQueryDispatch.code parameters width entry state.heap.size
        (constructorDictionary state.heap layout (empty _) refs).coordinates.size
        (constructorHeap state.heap layout (empty _) refs parameters.channels).size base refs next) := by
    rw [ResolvedResident.dictionary_size,ResolvedResident.constructor_size,nativeBaseEq,
      ResolvedResident.scratch_congr _ _ (ResolvedResident.rows_signs graph right ∅ b target root reference)]
    unfold code at present
    unfold SharedQueryDispatch.code SharedQueryResidentCode.code at present ⊢
    rw [ResolvedResident.source_code_congr _ _ (ResolvedResident.rows_wire _ _
        (ResolvedResident.rows_signs graph right ∅ b target root reference)),
      ResolvedResident.source_entry_congr _ _ (ResolvedResident.rows_wire _ _
        (ResolvedResident.rows_signs graph right ∅ b target root reference))]
    exact present
  have nativeBaseBound := ResolvedNativeProfile.native_base_bound graph right b target root state.heap layout
  have sourceSize : state.heap.size ≤ 15*(graph.countedSize+1) := by
    have count := ResolvedResident.rows_bound graph right b target root
    have size := graph.countedSize_eq
    have stored := ready.heapSize
    simp only [ResolvedResident.sourceHeap_size] at stored
    omega
  have countNative : (compile parameters).toState.count ≤ (selectedSize parameters).total := by
    simp only [selectedSize,NativeSize.total]; omega
  have codeSize := dispatch_bound parameters graph right b target root width entry state.heap.size
    (constructorHeap state.heap layout (empty _) refs parameters.channels).size base next
  have conditions : SharedQueryDispatch.Conditions parameters resident state layout refs
      (ResolvedResident.endSource graph right b target root) graph.nodeCount entry rest (by omega) next := {
    sourceReferences := quiet.sourceReferences
    sourceBeforeTable := quiet.sourceBeforeTable
    sourceBeforeInverse := quiet.sourceBeforeInverse
    sourceBound := quiet.sourceBound
    sourcePositive := quiet.sourcePositive
    sourceChannel := quiet.sourceChannel
    sourceNodes := quiet.sourceNodes
    ambientEq := quiet.ambientEq
    adjacent := quiet.adjacent
    tablePositive := quiet.tablePositive
    sourceHeaderRoom := quiet.sourceHeaderRoom
    sourceDual := quiet.sourceDual
    sourceEndpoint := quiet.sourceEndpoint
    constructorRoom := quiet.constructorRoom
    room := quiet.room
    nativeHeap := by
      dsimp only [refs] at nativeBaseBound ⊢
      omega
    capacity := by
      rw [ResolvedResident.dictionary_size]
      dsimp only [base,refs] at codeSize ⊢
      omega }
  obtain ⟨answer,final,ticks,peak,trace,halted,pc,time,space,meaning,witness,_,_,decision⟩ :=
    SharedQueryDispatch.execution parameters resident state _ layout refs (ResolvedResident.endSource graph right b target root)
      graph.nodeCount entry rest (by omega) next conditions physical ready
  have accepted : answer = true := meaning.mpr
    ((ResolvedResident.constructor_meaning (base := 2) graph right b target root state.heap layout).mpr existsZero)
  have count := ResolvedResident.rows_bound graph right b target root
  have size := graph.countedSize_eq
  simp only [refs,ResolvedResident.refs_length,ResolvedResident.refs_literals,accepted,ite_true] at time space decision
  exact ⟨final,ticks,peak,trace,halted.trans accepted,decision,by omega,by omega,witness accepted⟩

end Controller.Extensions.ResolvedNativeResident
