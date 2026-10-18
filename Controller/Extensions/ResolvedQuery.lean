module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Extensions.SupportStream
public import Controller.Cost.GuardedZeroSize
public import Controller.Horn.WorklistAccept
public import Controller.Cost.WordWidth

public import Mathlib.Tactic.Ring

@[expose] public section

/-! Each consistently resolved guarded decoder has a concrete cold zero-query
execution. Its worklist input, code and scratch bounds are uniform over the
selector. Constructing and reusing that input belongs to the outer driver. -/
namespace Controller.Extensions.ResolvedQuery
open Controller.Decoder Controller.Decoder.DAG Controller.Extensions.BoundedAnd
open Controller.Cost

variable {n : ℕ}

theorem resolved_children (graph : DAG n) (right : Finset (Fin graph.nodeCount))
    (i : Fin graph.nodeCount) :
    ((resolved graph right).node i).children.length ≤ (graph.node i).children.length := by
  change ((graph.node i).resolve _).children.length ≤ _
  cases graph.node i <;> simp [Gate.resolve,Gate.children]

theorem resolved_guards (graph : DAG n) (right : Finset (Fin graph.nodeCount))
    (i : Fin graph.nodeCount) :
    ((resolved graph right).node i).guardLabels = (graph.node i).guardLabels := by
  change ((graph.node i).resolve _).guardLabels = _
  cases graph.node i <;> simp [Gate.resolve,Gate.guardLabels]

theorem resolved_size (graph : DAG n) (right : Finset (Fin graph.nodeCount)) :
    (resolved graph right).countedSize ≤ graph.countedSize := by
  have children : (resolved graph right).childIncidences ≤ graph.childIncidences := by
    simp only [DAG.childIncidences,List.sum_ofFn]
    exact Finset.sum_le_sum fun i _ => resolved_children graph right i
  have guards : (resolved graph right).guardIncidences = graph.guardIncidences := by
    simp only [DAG.guardIncidences,List.sum_ofFn]
    apply Finset.sum_congr rfl
    intro i _
    rw [resolved_guards]
  simp only [DAG.countedSize_eq,resolved] at children guards ⊢
  omega

abbrev formula (graph : DAG n) (right : Finset (Fin graph.nodeCount)) (b : ℕ)
    (target : Channel n) (root : Fin graph.nodeCount) :=
  (resolved graph right).finiteZeroSystem b target root ∅ ∅

theorem formula_size (graph : DAG n) (right : Finset (Fin graph.nodeCount)) (b : ℕ)
    (target : Channel n) (root : Fin graph.nodeCount) :
    Controller.Cost.Horn.inputSize (formula graph right b target root) ≤ 8*(graph.countedSize+1) := by
  have bound := GuardedZeroSize.finite_input_size (resolved graph right) b target root ∅ ∅
  have size := resolved_size graph right
  apply bound.trans
  apply Nat.mul_le_mul_left
  calc
    _ ≤ (resolved graph right).countedSize + 1 := by rw [DAG.countedSize_eq]; omega
    _ ≤ graph.countedSize+1 := Nat.add_le_add_right size 1

def wordWidth (graph : DAG n) : ℕ := Nat.log 2 (graph.countedSize+1)+13

theorem capacity (graph : DAG n) : 4096*(graph.countedSize+1) < 2^wordWidth graph := by
  have base := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (graph.countedSize+1)
  have scale := Nat.mul_lt_mul_of_pos_left base (by decide : 0 < 4096)
  have eq : 4096*2^(Nat.log 2 (graph.countedSize+1)+1) = 2^wordWidth graph := by
    simp only [wordWidth,Nat.pow_add,Nat.pow_one,Nat.reducePow]
    ring
  rw [eq] at scale
  exact scale

def initial (graph : DAG n) (right : Finset (Fin graph.nodeCount)) (b : ℕ)
    (target : Channel n) (root : Fin graph.nodeCount) : State (wordWidth graph) 8 where
  reg _ := word _ 0
  heap := #[]
  stack := (Controller.Horn.SourceSerialize.heap (width := wordWidth graph)
    (formula graph right b target root).clauses.toList).toList
  output := []
  pc := word _ 0
  halted := false

/-- No code-placement, capacity, or solver-correctness premise remains. The
query consumes the serialized original rows and emits the exact solver result. -/
theorem execution (graph : DAG n) (right : Finset (Fin graph.nodeCount)) (b : ℕ)
    (target : Channel n) (root : Fin graph.nodeCount) :
    ∃ final ticks peak,
      Execution (Controller.Horn.WorklistAccept.program (wordWidth graph)
        (formula graph right b target root).clauses.toList)
        (initial graph right b target root) final ticks peak ∧
      final.halted = true ∧ final.stack = [] ∧
      final.output = Controller.Horn.WorklistAccept.resultWords (wordWidth graph)
        (Controller.Horn.Worklist.solveFormula (formula graph right b target root)) ∧
      ticks ≤ 1048*(graph.countedSize+1) ∧
      programWords (Controller.Horn.WorklistAccept.program (wordWidth graph)
        (formula graph right b target root).clauses.toList) + peak ≤
        (initial graph right b target root).liveWords + 11368*(graph.countedSize+1) := by
  have size := formula_size graph right b target root
  have cap := capacity graph
  have wordBound : 400*Controller.Cost.Horn.inputSize (formula graph right b target root) <
      2^wordWidth graph := by omega
  obtain ⟨final,ticks,peak,trace,halted,stack,output,time,space⟩ :=
    Controller.Cost.Horn.solveFormula_indexed_word_linear (formula graph right b target root)
      ((resolved graph right).finiteZeroSystem_dualHorn (resolved_guarded graph right) b target root ∅ ∅)
      (initial graph right b target root) [] rfl (by simp [initial]) rfl rfl wordBound
  exact ⟨final,ticks,peak,trace,halted,stack,by simpa [initial] using output,
    by omega,by omega⟩

/-- The fetched query's negative tag means absence of an admissible zero in
this expansion, including the global nonemptiness restriction. -/
theorem result_none_iff (graph : DAG n) (right : Finset (Fin graph.nodeCount)) (b : ℕ)
    (target : Channel n) (root : Fin graph.nodeCount) :
    Controller.Horn.Worklist.solveFormula (formula graph right b target root) = none ↔
      ¬ ∃ K, Admissible b target K ∧ (resolved graph right).eval (assignmentOfSet K) root = false := by
  have eq : resolvedZeroQuery graph b target root right = none ↔
      Controller.Horn.Worklist.solveFormula (formula graph right b target root) = none := by
    simp only [resolvedZeroQuery,DAG.solveZero,Option.map_eq_none_iff]
  rw [← eq]
  simpa [resolvedZeroQuery,ExtendsFixed] using
    (resolved graph right).solveZero_none_iff (resolved_guarded graph right) b target root ∅ ∅

end Controller.Extensions.ResolvedQuery
