module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.EnumerationDriverBounds

@[expose] public section

/-! The fetched prefix oracle in the immutable driver, with the runtime prefix
invariant and its exact D08 answer. All calls use the same resident array. -/
namespace Controller.Cost.EnumerationDriverQuery
open Controller.Decoder Controller.Decoder.Enumeration Controller.Native
open Controller.Cost.GateProgram Controller.Cost.EnumerationDriverPrefix

structure Context (parameters : Parameters) (graph : DAG parameters.channels)
    (retained entry : Nat) (rows : List ForestIndexedOperands.Row) (roots : List Nat)
    (program : Program (EnumerationPrefixOracle.Width parameters graph retained) 8) : Prop where
  guarded : graph.Guarded
  matched : ForestIndexedOperands.RowsMatch graph rows
  heads : UniformDAGSource.HeadsMatch graph rows matched
  rootMatches : ForestIndexedOperands.RootsMatch graph roots
  present : SharedRootRead.BlockAt program entry
    (EnumerationDriverCode.code parameters graph (EnumerationPrefixOracle.Width parameters graph retained) entry rows roots)
  room : entry + (EnumerationDriverCode.code parameters graph
    (EnumerationPrefixOracle.Width parameters graph retained) entry rows roots).length <
    2 ^ EnumerationPrefixOracle.Width parameters graph retained
  oracleRoom : (EnumerationDriverCode.labels parameters graph (EnumerationPrefixOracle.Width parameters graph retained) entry).oracle +
    (EnumerationPrefixOracle.oracleCode parameters graph (EnumerationPrefixOracle.Width parameters graph retained) rows roots
      (EnumerationDriverCode.labels parameters graph (EnumerationPrefixOracle.Width parameters graph retained) entry).oracle
      (EnumerationDriverCode.labels parameters graph (EnumerationPrefixOracle.Width parameters graph retained) entry).restore).length +
    EnumerationUniformPrepared.preparedSize graph ≤ retained
  heapFits : (EnumerationPrefixOracle.packet parameters (EnumerationPrefixOracle.Width parameters graph retained) rows roots).size +
    2 * parameters.channels < 2 ^ EnumerationPrefixOracle.Width parameters graph retained

abbrev budget (parameters : Parameters) (graph : DAG parameters.channels) : Nat :=
  24 * parameters.channels + 16 + (parameters.channels + graph.roots.length + 1) * (8000 * (graph.countedSize + 1))

abbrev scratch (parameters : Parameters) (graph : DAG parameters.channels) : Nat :=
  244 * (graph.countedSize + 1)

theorem ready_live_eq (parameters : Parameters) (packet : Array (Word width))
    (first second : State width 8) (d c e k : Nat) (P Q : Finset (Fin parameters.channels))
    (before : Ready parameters packet d c P first) (after : Ready parameters packet e k Q second)
    (output : second.output = first.output) : second.liveWords = first.liveWords := by
  simp only [State.liveWords, before.heap, after.heap, before.stack, after.stack, output,
    Array.size_append, List.size_toArray, EnumerationMasks.maskList_length]

theorem heap_fits (parameters : Parameters) (graph : DAG parameters.channels)
    (retained entry : Nat) (rows : List ForestIndexedOperands.Row) (roots : List Nat)
    (program : Program (EnumerationPrefixOracle.Width parameters graph retained) 8)
    (context : Context parameters graph retained entry rows roots program)
    (state : State (EnumerationPrefixOracle.Width parameters graph retained) 8)
    (depth cursor : Nat) (partialSet : Finset (Fin parameters.channels))
    (ready : Ready parameters (EnumerationPrefixOracle.packet parameters _ rows roots) depth cursor partialSet state) :
    state.heap.size < 2 ^ EnumerationPrefixOracle.Width parameters graph retained := by
  simpa only [ready.heap, Array.size_append, List.size_toArray, EnumerationMasks.maskList_length] using context.heapFits

theorem channels_fit (parameters : Parameters) (graph : DAG parameters.channels)
    (retained entry : Nat) (rows : List ForestIndexedOperands.Row) (roots : List Nat)
    (program : Program (EnumerationPrefixOracle.Width parameters graph retained) 8)
    (context : Context parameters graph retained entry rows roots program) :
    parameters.channels < 2 ^ EnumerationPrefixOracle.Width parameters graph retained := by
  have := context.heapFits
  omega

theorem query_execution (parameters : Parameters) (graph : DAG parameters.channels)
    (retained entry : Nat) (rows : List ForestIndexedOperands.Row) (roots : List Nat)
    (program : Program (EnumerationPrefixOracle.Width parameters graph retained) 8)
    (context : Context parameters graph retained entry rows roots program)
    (depth cursor mode : Nat) (partialSet : Finset (Fin parameters.channels))
    (state : State (EnumerationPrefixOracle.Width parameters graph retained) 8)
    (ready : Ready parameters (EnumerationPrefixOracle.packet parameters _ rows roots) depth cursor partialSet state)
    (consistent : FixedConsistent (extensionBase parameters.buses parameters.bridge.target (fixedTrue depth partialSet))
      (fixedFalse depth partialSet))
    (position : state.pc = word _ (EnumerationDriverCode.labels parameters graph (EnumerationPrefixOracle.Width parameters graph retained) entry).call)
    (held : state.reg 5 = word _ mode) :
    ∃ final ticks peak, Execution program state final ticks peak ∧
      ticks ≤ budget parameters graph ∧ peak ≤ state.liveWords + scratch parameters graph ∧
      Ready parameters (EnumerationPrefixOracle.packet parameters _ rows roots) depth cursor partialSet final ∧
      final.pc = word _ (EnumerationDriverCode.labels parameters graph (EnumerationPrefixOracle.Width parameters graph retained) entry).dispatch ∧
      final.reg 5 = word _ mode ∧
      final.reg 4 = boolWord _ (query graph parameters.buses parameters.bridge.target true depth partialSet) ∧
      final.output = state.output := by
  have callRoom := EnumerationDriverBounds.block_room parameters graph (EnumerationPrefixOracle.Width parameters graph retained) entry rows roots context.room 1 (by decide)
  have returnRoom := EnumerationDriverBounds.block_room parameters graph (EnumerationPrefixOracle.Width parameters graph retained) entry rows roots context.room 2 (by decide)
  simp only [EnumerationDriverLayout.entries, EnumerationDriverCode.chunks, List.getElem_cons_succ,
    List.getElem_cons_zero, EnumerationPrefixOracle.callCode, EnumerationPrefixCall.code_length] at callRoom
  simp only [EnumerationDriverLayout.entries, EnumerationDriverCode.chunks, List.getElem_cons_succ,
    List.getElem_cons_zero, EnumerationPrefixReturn.code_length] at returnRoom
  obtain ⟨answer, final, ticks, peak, trace, time, space, heap, stack, output, pc, running, counter, modeValue, flag, meaning⟩ :=
    EnumerationPrefixOracle.execution parameters graph context.guarded (fixedTrue depth partialSet) (fixedFalse depth partialSet)
      consistent retained (EnumerationDriverCode.labels parameters graph (EnumerationPrefixOracle.Width parameters graph retained) entry).call
      (EnumerationDriverCode.labels parameters graph (EnumerationPrefixOracle.Width parameters graph retained) entry).oracle
      (EnumerationDriverCode.labels parameters graph (EnumerationPrefixOracle.Width parameters graph retained) entry).restore
      program rows roots context.matched context.heads context.rootMatches state position ready.running ready.heap
      callRoom (by omega) context.heapFits context.oracleRoom
      (EnumerationDriverLayout.call_at parameters graph (EnumerationPrefixOracle.Width parameters graph retained) entry rows roots program context.present)
      (EnumerationDriverLayout.oracle_at parameters graph (EnumerationPrefixOracle.Width parameters graph retained) entry rows roots program context.present)
      (EnumerationDriverLayout.restore_at parameters graph (EnumerationPrefixOracle.Width parameters graph retained) entry rows roots program context.present)
  have answerEq : answer = query graph parameters.buses parameters.bridge.target true depth partialSet := by
    have iff := EnumerationPrefixOracle.answer_iff_query parameters graph context.guarded depth partialSet answer meaning
    cases answer <;> cases value : query graph parameters.buses parameters.bridge.target true depth partialSet <;> simp_all
  refine ⟨final, ticks, peak, trace, time, space,
    ⟨heap.trans ready.heap, counter.trans ready.counter, stack.trans ready.stack, running⟩,
    ?_, modeValue.trans held, ?_, output⟩
  · exact pc
  · simpa only [answerEq, boolWord] using flag

end Controller.Cost.EnumerationDriverQuery
