module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Extensions.ResolvedQuery

@[expose] public section

/-! Resolved zero queries share an instruction array. Selector bits and the
queried root affect serialized literal labels, while clause counts and source
word counts stay fixed. -/
namespace Controller.Extensions.ResolvedProgram
open Controller.Decoder Controller.Decoder.DAG Controller.Extensions.BoundedAnd
open Controller.Cost Controller.Horn

set_option maxRecDepth 4096 in
/-- The cold solver's instructions depend on source row and occurrence counts,
not on the values of its original literals. -/
theorem program_congr (width : ℕ) (left right : List (Controller.CNF.Clause (Fin v)))
    (rows : left.length = right.length)
    (occurrences : (left.map List.length).sum = (right.map List.length).sum) :
    WorklistAccept.program width left = WorklistAccept.program width right := by
  have words : NormalizeCold.words (width := width) left = NormalizeCold.words (width := width) right := by
    simp only [NormalizeCold.words_eq, rows, occurrences]
  have base : SourceSerialize.base left = SourceSerialize.base right := by
    simp only [SourceSerialize.base, SourceSerialize.source, rows, occurrences]
  have loaded : NormalizeCold.loadedPrefix width left = NormalizeCold.loadedPrefix width right := by
    simp only [NormalizeCold.loadedPrefix, words]
  have initialized : NormalizeCold.initializedPrefix width left = NormalizeCold.initializedPrefix width right := by
    simp only [NormalizeCold.initializedPrefix, loaded, base]
  have normalized : NormalizeCold.program width left = NormalizeCold.program width right := by
    simp only [NormalizeCold.program, initialized, base]
  have indexed : IndexScanCold.program width left = IndexScanCold.program width right := by
    simp only [IndexScanCold.program, IndexScanCold.recordStart, IndexScanCold.entry,
      normalized, words, base]
  have seedEnd : WorklistAccept.seedEnd width left = WorklistAccept.seedEnd width right := by
    simp only [WorklistAccept.seedEnd, IndexScanCold.entry, normalized]
  have conflict : WorklistAccept.conflictEntry width left = WorklistAccept.conflictEntry width right := by
    simp only [WorklistAccept.conflictEntry, seedEnd]
  have cold : WorklistAccept.coldPrefix width left = WorklistAccept.coldPrefix width right := by
    unfold WorklistAccept.coldPrefix WorklistSeedRun.program
    rw [indexed, base, conflict]
    simp only [IndexScanCold.recordStart, words]
  simp only [WorklistAccept.program, cold, base, seedEnd, conflict]

theorem node_shape (graph : DAG n) (left right : Finset (Fin graph.nodeCount))
    (i : Fin graph.nodeCount) :
    (((resolved graph left).nodeClauses i).map List.length) =
      (((resolved graph right).nodeClauses i).map List.length) := by
  unfold DAG.nodeClauses
  simp only [resolved]

  cases h : graph.node i <;>
    simp [Gate.resolve, Controller.Decoder.ZeroSystem.implicationClause,
      Controller.Decoder.ZeroSystem.positiveClause, List.map_map, Function.comp_def]

theorem forward_shape (graph : DAG n) (left right : Finset (Fin graph.nodeCount)) :
    ((resolved graph left).forwardClauses.map List.length) =
      ((resolved graph right).forwardClauses.map List.length) := by
  simp only [DAG.forwardClauses, List.map_flatMap]
  congr 1
  funext i
  exact node_shape graph left right i

theorem formula_shape (graph : DAG n) (left right : Finset (Fin graph.nodeCount))
    (b : ℕ) (target : Channel n) (first second : Fin graph.nodeCount) :
    ((ResolvedQuery.formula graph left b target first).clauses.toList.map List.length) =
      ((ResolvedQuery.formula graph right b target second).clauses.toList.map List.length) := by
  simp only [ResolvedQuery.formula, DAG.finiteZeroSystem, Controller.CNF.relabel,
    Controller.CNF.OrderedFormula.relabel, Array.toList_map, List.map_map, Controller.CNF.OrderedFormula.Clause.relabel,
    Function.comp_def, List.length_map, DAG.zeroSystem, Controller.CNF.ofClauses,
    List.map_append]
  rw [forward_shape graph left right]
  simp [DAG.channelClauses, DAG.trueUnitClauses, DAG.falseUnitClauses,
    Controller.Decoder.ZeroSystem.implicationClause,
    Controller.Decoder.ZeroSystem.positiveClause]

/-- The same fetched cold solver serves every selector and root. -/
theorem selector_root_program (graph : DAG n) (left right : Finset (Fin graph.nodeCount))
    (b : ℕ) (target : Channel n) (first second : Fin graph.nodeCount) :
    WorklistAccept.program (ResolvedQuery.wordWidth graph)
      (ResolvedQuery.formula graph left b target first).clauses.toList =
    WorklistAccept.program (ResolvedQuery.wordWidth graph)
      (ResolvedQuery.formula graph right b target second).clauses.toList := by
  have shape := formula_shape graph left right b target first second
  apply program_congr
  · simpa only [List.length_map] using congrArg List.length shape
  · exact congrArg List.sum shape

/-- A resident cold query program chosen once for a nonempty root family. -/
def program (graph : DAG n) (b : ℕ) (target : Channel n) (reference : Fin graph.nodeCount) :
    Program (ResolvedQuery.wordWidth graph) 8 :=
  WorklistAccept.program (ResolvedQuery.wordWidth graph)
    (ResolvedQuery.formula graph ∅ b target reference).clauses.toList

theorem source_words (graph : DAG n) (right : Finset (Fin graph.nodeCount))
    (b : ℕ) (target : Channel n) (root : Fin graph.nodeCount) :
    (SourceSerialize.heap (width := ResolvedQuery.wordWidth graph)
      (ResolvedQuery.formula graph right b target root).clauses.toList).size ≤
        16*(graph.countedSize+1)+3 := by
  have size := ResolvedQuery.formula_size graph right b target root
  simp only [SourceSerialize.heap_size, SourceSerialize.base, SourceSerialize.source]
  unfold Controller.Cost.Horn.inputSize at size
  simp only [Array.length_toList]
  omega

/-- The fixed cold solver preserves arbitrary retained stack and output frames.
The resident bound charges the serialized query input as well as its scratch.
Source-to-query serialization and returning control remain outer-driver duties. -/
theorem execution_framed (graph : DAG n) (b : ℕ) (target : Channel n)
    (reference root : Fin graph.nodeCount) (right : Finset (Fin graph.nodeCount))
    (suffix output : List (Word (ResolvedQuery.wordWidth graph))) :
    ∃ final ticks peak,
      Execution (program graph b target reference)
        { ResolvedQuery.initial graph right b target root with
          stack := (ResolvedQuery.initial graph right b target root).stack ++ suffix,
          output := output } final ticks peak ∧
      final.halted = true ∧ final.stack = suffix ∧
      final.output = WorklistAccept.resultWords (ResolvedQuery.wordWidth graph)
        (Worklist.solveFormula (ResolvedQuery.formula graph right b target root)) ++ output ∧
      ticks ≤ 1048*(graph.countedSize+1) ∧
      programWords (program graph b target reference) + peak ≤
        11396*(graph.countedSize+1) + suffix.length + output.length := by
  let state : State (ResolvedQuery.wordWidth graph) 8 :=
    { ResolvedQuery.initial graph right b target root with
      stack := (ResolvedQuery.initial graph right b target root).stack ++ suffix,
      output := output }
  have size := ResolvedQuery.formula_size graph right b target root
  have cap := ResolvedQuery.capacity graph
  obtain ⟨final,ticks,peak,trace,halted,stack,result,time,space⟩ :=
    Controller.Cost.Horn.solveFormula_indexed_word_linear
      (ResolvedQuery.formula graph right b target root)
      ((resolved graph right).finiteZeroSystem_dualHorn (resolved_guarded graph right) b target root ∅ ∅)
      state suffix rfl rfl rfl rfl (by omega)
  have uniform := selector_root_program graph right ∅ b target root reference
  change WorklistAccept.program _ _ = program graph b target reference at uniform
  rw [uniform] at trace space
  have words := source_words graph right b target root
  have live : state.liveWords ≤ 16*(graph.countedSize+1)+12+suffix.length+output.length := by
    simp only [state, State.liveWords, ResolvedQuery.initial, Array.size_empty,
      List.length_append, Array.length_toList]
    omega
  refine ⟨final,ticks,peak,trace,halted,stack,result,by omega,?_⟩
  have charged := Nat.add_le_add_left (Nat.mul_le_mul_left 1421 size) state.liveWords
  have bound := space.trans charged
  omega

end Controller.Extensions.ResolvedProgram
