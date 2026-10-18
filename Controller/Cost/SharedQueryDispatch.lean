module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedQueryResidentPlan

@[expose] public section

namespace Controller.Cost.SharedQueryDispatch
open Controller.Cost.ForestZeroTouch Controller.Cost.GateProgram Controller.Cost.ForestZeroCompile
open Controller.Cost.ForestZeroDictionary Controller.Cost.ForestZeroAdmissibleCaller
open Controller.Cost.ForestZeroEmit Controller.CNF Controller.Native Controller.Native.SourceController
open Controller.Decoder Controller.Cost.NativeCircuitExecution Controller.Cost.NativeSourceExecution
open Controller.Cost.SharedZeroNativeComplete Controller.Cost.SharedZeroNativeQuery

@[irreducible] def code (parameters : Parameters) (width entry keep n base nativeBase : Nat)
    (references : List (List (Reference ambient))) (next : Nat) : List (Instruction width 8) :=
  SharedQueryResidentCode.code parameters width entry keep n base nativeBase references ++
    (ForestZeroRootLoop.dispatchCode width next).toList

structure Conditions {width ambient : Nat}
    (parameters : Parameters) (program : Program width 8) (initial : State width 8)
    (sharedLayout : Layout ambient initial.heap.size)
    (references : List (List (Reference ambient))) (sourceEnd nodes sourceEntry : Nat)
    (rest : List (Word width)) (within : parameters.channels ≤ ambient) (nextEntry : Nat) : Prop where
  sourceReferences : ∀ reference ∈ references.flatten,
          Controller.Cost.ForestZeroEmit.StoredReference (initial.heap) parameters.channels sourceEnd reference
  sourceBeforeTable : sourceEnd ≤ (sharedLayout).tableBase
  sourceBeforeInverse : sourceEnd ≤ (sharedLayout).inverseBase
  sourceBound : sourceEnd ≤ (initial.heap).size
  sourcePositive : 0 < sourceEnd
  sourceChannel : (initial.heap)[0]? = some (word width parameters.channels)
  sourceNodes : (initial.heap)[1]? = some (word width nodes)
  ambientEq : ambient = parameters.channels + nodes
  adjacent : (sharedLayout).inverseBase = (sharedLayout).tableBase + ambient
  tablePositive : 0 < (sharedLayout).tableBase
  sourceHeaderRoom : 1 < sourceEnd
  sourceDual : Controller.Horn.DualHorn
          (ofClauses (ForestZeroAssembly.originalRows (reservedReferences references)))
  sourceEndpoint : (initial.heap).size = (sharedLayout).inverseBase + ambient
  constructorRoom : (initial.heap).size + 5 + 2 * (references.length + 1) +
          2 * references.flatten.length + 2 * ambient < 2 ^ width
  room : (constructorState initial.heap sharedLayout (ForestZeroCompile.empty ambient) references parameters.channels (SharedQuerySourceCode.solverEntry width sourceEntry initial.heap.size references) (word width initial.heap.size :: rest) initial.output initial.reg).heap.size + 5 * (constructorDictionary initial.heap sharedLayout (ForestZeroCompile.empty ambient) references).coordinates.size + 4 +
          3 * (constructorFormula initial.heap sharedLayout (ForestZeroCompile.empty ambient) (ForestZeroCompile.empty_coherent ambient) references parameters.channels within).clauses.toList.length + ((constructorFormula initial.heap sharedLayout (ForestZeroCompile.empty ambient) (ForestZeroCompile.empty_coherent ambient) references parameters.channels within).clauses.toList.map List.length).sum +
          2 * (Controller.Horn.IndexScan.occurrences (constructorFormula initial.heap sharedLayout (ForestZeroCompile.empty ambient) (ForestZeroCompile.empty_coherent ambient) references parameters.channels within).clauses.toList ((constructorHeap initial.heap sharedLayout (ForestZeroCompile.empty ambient) references parameters.channels).size + 5 * (constructorDictionary initial.heap sharedLayout (ForestZeroCompile.empty ambient) references).coordinates.size + 4)).length < 2 ^ width
  nativeHeap : (nativeBase initial.heap sharedLayout references parameters.channels within) + parameters.channels + (compile parameters).toState.count < 2 ^ width
  capacity : sourceEntry + (code parameters width sourceEntry initial.heap.size (constructorDictionary initial.heap sharedLayout (ForestZeroCompile.empty ambient) references).coordinates.size (constructorHeap initial.heap sharedLayout (ForestZeroCompile.empty ambient) references parameters.channels).size (nativeBase initial.heap sharedLayout references parameters.channels within) references nextEntry).length < 2 ^ width

set_option maxRecDepth 4096 in
def plan {width ambient : Nat}
    (parameters : Parameters) (program : Program width 8) (initial : State width 8)
    (sharedLayout : Layout ambient initial.heap.size)
    (references : List (List (Reference ambient))) (sourceEnd nodes sourceEntry : Nat)
    (rest : List (Word width)) (within : parameters.channels ≤ ambient) (nextEntry : Nat)
    (conditions : Conditions parameters program initial sharedLayout references sourceEnd nodes sourceEntry rest within nextEntry)
    (present : SharedRootRead.BlockAt program sourceEntry (code parameters width sourceEntry initial.heap.size (constructorDictionary initial.heap sharedLayout (ForestZeroCompile.empty ambient) references).coordinates.size (constructorHeap initial.heap sharedLayout (ForestZeroCompile.empty ambient) references parameters.channels).size (nativeBase initial.heap sharedLayout references parameters.channels within) references nextEntry)) :
    SourceQueryPlan parameters program initial sharedLayout references sourceEnd nodes sourceEntry rest within (SharedQueryTailCode.cleanup parameters width (nativeBase initial.heap sharedLayout references parameters.channels within) ((SharedQuerySourceCode.solverEntry width sourceEntry initial.heap.size references) + 261) + 35) nextEntry := by
  have coreBlock : SharedRootRead.BlockAt program sourceEntry (SharedQueryResidentCode.code parameters width sourceEntry initial.heap.size (constructorDictionary initial.heap sharedLayout (ForestZeroCompile.empty ambient) references).coordinates.size (constructorHeap initial.heap sharedLayout (ForestZeroCompile.empty ambient) references parameters.channels).size (nativeBase initial.heap sharedLayout references parameters.channels within) references) := by
    unfold code at present
    intro offset bound
    have fetched := present offset (by simp only [List.length_append]; omega)
    rw [List.getElem?_append_left bound] at fetched
    exact fetched
  have endpoint := SharedQueryResidentCode.code_end parameters width sourceEntry initial.heap.size
    (constructorDictionary initial.heap sharedLayout (ForestZeroCompile.empty ambient) references).coordinates.size (constructorHeap initial.heap sharedLayout (ForestZeroCompile.empty ambient) references parameters.channels).size (nativeBase initial.heap sharedLayout references parameters.channels within) references
  have cap := conditions.capacity
  simp only [code, List.length_append, Array.length_toList, ForestZeroRootLoop.dispatchCode,
    List.length_cons, List.length_nil] at cap
  have dispatchBlock : SharedRootRead.BlockAt program (SharedQueryTailCode.cleanup parameters width (nativeBase initial.heap sharedLayout references parameters.channels within) ((SharedQuerySourceCode.solverEntry width sourceEntry initial.heap.size references) + 261) + 35) (ForestZeroRootLoop.dispatchCode width nextEntry).toList := by
    have joined : SharedRootRead.BlockAt program sourceEntry
        ((SharedQueryResidentCode.code parameters width sourceEntry initial.heap.size (constructorDictionary initial.heap sharedLayout (ForestZeroCompile.empty ambient) references).coordinates.size (constructorHeap initial.heap sharedLayout (ForestZeroCompile.empty ambient) references parameters.channels).size (nativeBase initial.heap sharedLayout references parameters.channels within) references) ++ (ForestZeroRootLoop.dispatchCode width nextEntry).toList ++ []) := by
      simpa only [code, List.append_nil] using present
    have found := SharedNativeSuccessCode.segment program sourceEntry _ _ _ joined
    rw [endpoint] at found
    exact found
  apply SharedQueryResidentPlan.of_resident parameters program initial sharedLayout references sourceEnd nodes
    sourceEntry rest within (SharedQueryTailCode.cleanup parameters width (nativeBase initial.heap sharedLayout references parameters.channels within) ((SharedQuerySourceCode.solverEntry width sourceEntry initial.heap.size references) + 261) + 35) nextEntry ?_ coreBlock
  refine {
    sourceReferences := conditions.sourceReferences
    sourceBeforeTable := conditions.sourceBeforeTable
    sourceBeforeInverse := conditions.sourceBeforeInverse
    sourceBound := conditions.sourceBound
    sourcePositive := conditions.sourcePositive
    sourceChannel := conditions.sourceChannel
    sourceNodes := conditions.sourceNodes
    ambientEq := conditions.ambientEq
    adjacent := conditions.adjacent
    tablePositive := conditions.tablePositive
    sourceHeaderRoom := conditions.sourceHeaderRoom
    sourceDual := conditions.sourceDual
    sourceEndpoint := conditions.sourceEndpoint
    constructorRoom := conditions.constructorRoom
    room := conditions.room
    nativeHeap := conditions.nativeHeap
    dispatchEq := by omega
    dispatchCapacity := by omega
    dispatchAt := by
      intro phase
      simpa only [Array.getElem?_toList] using dispatchBlock phase.val (by simpa [ForestZeroRootLoop.dispatchCode] using phase.isLt)
    residentCapacity := by omega
  }

set_option maxRecDepth 4096 in
theorem execution {width ambient : Nat}
    (parameters : Parameters) (program : Program width 8) (initial : State width 8)
    (sourceHeap : Array (Word width)) (sharedLayout : Layout ambient initial.heap.size)
    (references : List (List (Reference ambient))) (sourceEnd nodes sourceEntry : Nat)
    (rest : List (Word width)) (within : parameters.channels ≤ ambient) (nextEntry : Nat)
    (conditions : Conditions parameters program initial sharedLayout references sourceEnd nodes sourceEntry rest within nextEntry)
    (present : SharedRootRead.BlockAt program sourceEntry (code parameters width sourceEntry initial.heap.size (constructorDictionary initial.heap sharedLayout (ForestZeroCompile.empty ambient) references).coordinates.size (constructorHeap initial.heap sharedLayout (ForestZeroCompile.empty ambient) references parameters.channels).size (nativeBase initial.heap sharedLayout references parameters.channels within) references nextEntry))
    (initialReady : QueryReady (ambient := ambient) sourceHeap sharedLayout.tableBase sharedLayout.inverseBase
      sourceEntry rest initial) :
    ∃ answer : Bool, ∃ final ticks peak,
      Execution program initial final ticks peak ∧
      final.halted = answer ∧
      final.pc = word width (if answer then (SharedQueryTailCode.cleanup parameters width (nativeBase initial.heap sharedLayout references parameters.channels within) ((SharedQuerySourceCode.solverEntry width sourceEntry initial.heap.size references) + 261) + 35) + 2 else nextEntry) ∧
      ticks ≤ 150 * references.length + 387 * references.flatten.length + 485 +
        (if answer then 55 * (selectedSize parameters).total else 0) ∧
      peak ≤ initial.liveWords + 5 * references.length + 15 * references.flatten.length +
        parameters.channels + 3 * (selectedSize parameters).total + 28 ∧
      (answer = true ↔ Controller.CNF.Satisfiable
        (constructorFormula initial.heap sharedLayout (ForestZeroCompile.empty ambient)
          (ForestZeroCompile.empty_coherent ambient) references parameters.channels within)) ∧
      (answer = true → QueryNativeWitness parameters initial.heap sharedLayout references within final.output) ∧
      (answer = false → QueryReady (ambient := ambient) sourceHeap sharedLayout.tableBase
        sharedLayout.inverseBase nextEntry rest final) ∧
      final.liveWords ≤ initial.liveWords + 1 + (if answer then (compile parameters).toState.count else 0) ∧
      final.reg 4 = word width (if answer then 1 else 0) := by
  obtain ⟨answer, final, ticks, peak, trace, pc, running, decision, timeBound, spaceBound,
      liveBound, meaning, certificate, nextReady, dispatchCapacity, dispatchAt⟩ :=
    SourceQueryPlan.execute parameters program initial sourceHeap sharedLayout references sourceEnd nodes
      sourceEntry rest within (SharedQueryTailCode.cleanup parameters width (nativeBase initial.heap sharedLayout references parameters.channels within) ((SharedQuerySourceCode.solverEntry width sourceEntry initial.heap.size references) + 261) + 35) nextEntry
      (plan parameters program initial sharedLayout references sourceEnd nodes sourceEntry rest within
        nextEntry conditions present) initialReady
  have dispatch := ForestZeroRootLoop.dispatch_execution program final (SharedQueryTailCode.cleanup parameters width (nativeBase initial.heap sharedLayout references parameters.channels within) ((SharedQuerySourceCode.solverEntry width sourceEntry initial.heap.size references) + 261) + 35) nextEntry answer
    pc running decision dispatchCapacity dispatchAt
  refine ⟨answer, ForestZeroRootLoop.dispatchState final (SharedQueryTailCode.cleanup parameters width (nativeBase initial.heap sharedLayout references parameters.channels within) ((SharedQuerySourceCode.solverEntry width sourceEntry initial.heap.size references) + 261) + 35) nextEntry answer,
    ticks + (if answer then 2 else 1), peak, ?_, rfl, rfl, ?_, spaceBound, meaning, ?_, ?_, ?_, decision⟩
  · simpa only [Nat.max_eq_left trace.final_storage_le] using trace.append dispatch
  · cases answer <;> simp only [Bool.false_eq_true, ite_false, ite_true] at timeBound ⊢ <;> omega
  · exact certificate
  · intro rejected
    simpa only [rejected] using nextReady rejected
  · cases answer <;> simpa [ForestZeroRootLoop.dispatchState, State.liveWords, State.put, State.advance] using liveBound

end Controller.Cost.SharedQueryDispatch
