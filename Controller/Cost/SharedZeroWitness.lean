module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedZeroOutput

@[expose] public section

/-! The actual successful query emits a channel prefix whose decoded set is an admissible fixed false-root witness. -/
namespace Controller.Cost.SharedZeroWitness
open Controller.Cost.GateProgram Controller.Cost.ForestZeroAdmissibleCaller
open Controller.Decoder Controller.Decoder.DAG

theorem execution (graph : DAG n) (guarded : graph.Guarded) (b : Nat) (target : Fin n) (T F : Finset (Fin n))
    (root : Fin graph.nodeCount) (base slot : Nat)
    (program : Program width 8) (initial : State width 8) (sourceHeap : Array (Word width))
    (layout : ForestZeroDictionary.Layout (n + graph.nodeCount) initial.heap.size)
    (sourceEnd sourceEntry : Nat) (rest : List (Word width)) (dispatchEntry nextEntry : Nat)
    (plan : SourceQueryPlan (channels := n) program initial layout
      (SharedZeroSource.references graph b target T F base slot root) sourceEnd graph.nodeCount sourceEntry
      rest (by omega) dispatchEntry nextEntry)
    (ready : QueryReady (ambient := n + graph.nodeCount) sourceHeap layout.tableBase layout.inverseBase
      sourceEntry rest initial) :
    ∃ answer : Bool, ∃ final ticks peak,
      Execution program initial final ticks peak ∧
      final.pc = word width dispatchEntry ∧ final.halted = false ∧
      final.reg 4 = word width (if answer then 1 else 0) ∧
      ticks ≤ 4711 * (graph.countedSize + 1) ∧
      peak ≤ initial.liveWords + 186 * (graph.countedSize + 1) ∧
      final.liveWords ≤ initial.liveWords + 1 + (if answer then n else 0) ∧
      (answer = true ↔ ∃ K, Admissible b target K ∧ ExtendsFixed T F K ∧
        graph.eval (assignmentOfSet K) root = false) ∧
      (answer = true → Admissible b target (SharedZeroOutput.decode final.output n) ∧
        ExtendsFixed T F (SharedZeroOutput.decode final.output n) ∧
        graph.eval (assignmentOfSet (SharedZeroOutput.decode final.output n)) root = false) ∧
      (answer = false → QueryReady (ambient := n + graph.nodeCount) sourceHeap layout.tableBase layout.inverseBase
        nextEntry rest (ForestZeroRootLoop.dispatchState final dispatchEntry nextEntry false)) := by
  obtain ⟨answer, final, ticks, peak, trace, finalPC, running, decision, timeBound, spaceBound, live,
    meaning, witness, reset⟩ := SharedZeroChecked.execution graph guarded b target T F root base slot program initial
      sourceHeap layout sourceEnd sourceEntry rest dispatchEntry nextEntry plan ready
  have fits : 1 < 2 ^ width := by have := plan.ambientFits; omega
  refine ⟨answer, final, ticks, peak, trace, finalPC, running, decision, timeBound, spaceBound, live,
    meaning, ?_, reset⟩
  intro accepted
  exact SharedZeroOutput.decoded_witness graph guarded b target T F root initial.heap layout final.output fits
    (witness accepted)

end Controller.Cost.SharedZeroWitness
