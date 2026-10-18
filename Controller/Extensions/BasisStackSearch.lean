module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Extensions.MonotoneDetector
public import Controller.Extensions.WitnessStack

@[expose] public section

/-! Concrete output searches returning the selected channel vector on the
caller stack. The native constructor can consume it without an external
state conversion or a precomputed witness. -/
namespace Controller.Extensions.BasisStackSearch
open Controller.Decoder Controller.Decoder.DAG Controller.Cost
open Controller.Extensions.WitnessStack

variable {n width : Nat}

def SafeCode (code : List (Instruction width 8)) : Prop := ∀ i ∈ code, Safe i

theorem emit_safe (ops : List LiteralWitnessEmit.Operand) (entry : Nat) :
    SafeCode (LiteralWitnessEmit.code (width := width) entry ops) := by
  induction ops generalizing entry with
  | nil => simp [SafeCode, LiteralWitnessEmit.code]
  | cons op rest ih =>
    simp only [LiteralWitnessEmit.code, SafeCode, List.mem_append, or_imp, forall_and]
    refine ⟨?_, ih _⟩
    cases op <;> simp [LiteralWitnessEmit.operandCode, LiteralWitnessEmit.constantCode,
      LiteralWitnessEmit.storedCode, LiteralWitnessEmit.selectedCode, SharedTagCompare.code, Safe]

set_option maxHeartbeats 2000000 in
theorem literal_safe (b : Nat) (target : Channel n) (nodes base found absent count entry cursor : Nat) :
    SafeCode (LiteralOutputSearch.code (width := width) b target nodes base found absent count entry cursor) := by
  have rootSafe : ∀ entry absent, SafeCode
      (LiteralWitnessReturn.code (width := width) b target nodes base entry absent) := by
    intro entry absent
    simp only [LiteralWitnessReturn.code, SafeCode, List.mem_append, or_imp, forall_and]
    refine ⟨?_, emit_safe _ _, ?_, emit_safe _ _⟩
    · unfold LiteralRootRun.code LiteralRootRun.tailCode
      split_ifs <;> simp [LiteralRootRun.readCode, LiteralRoot.callCode, LiteralScan.code,
        LiteralTests.positiveTest, LiteralTests.negativeTest, LiteralTests.conflictTest,
        LiteralTests.freeTest, LiteralScan.head, LiteralScan.advance, Safe]
    · simp [LiteralWitnessReturn.jump, Safe]
  induction count generalizing entry cursor with
  | zero => simp [LiteralOutputSearch.code, LiteralWitnessReturn.jump, SafeCode, Safe]
  | succ count ih =>
    simp only [LiteralOutputSearch.code, SafeCode, List.mem_append, or_imp, forall_and]
    exact ⟨by simp [LiteralOutputSearch.readCode, Safe], rootSafe _ _,
      by simp [LiteralWitnessReturn.jump, Safe], ih _ _⟩

theorem monotone_safe (b : Nat) (target : Channel n) (nodes base found absent count entry cursor : Nat) :
    SafeCode (MonotoneOutputSearch.code (width := width) b target nodes base found absent count entry cursor) := by
  have rootSafe : ∀ entry absent, SafeCode
      (MonotoneReturn.code (width := width) b target nodes base entry absent) := by
    intro entry absent
    simp only [MonotoneReturn.code, SafeCode, List.mem_append, or_imp, forall_and]
    refine ⟨?_, emit_safe _ _, ?_, emit_safe _ _⟩
    · unfold MonotoneRoot.code
      split_ifs <;> simp [LiteralRootRun.readCode, MonotoneScan.code, LiteralScan.code,
        LiteralWitnessReturn.jump, LiteralScan.head, LiteralScan.advance, Safe]
    · simp [LiteralWitnessReturn.jump, Safe]
  induction count generalizing entry cursor with
  | zero => simp [MonotoneOutputSearch.code, LiteralWitnessReturn.jump, SafeCode, Safe]
  | succ count ih =>
    simp only [MonotoneOutputSearch.code, SafeCode, List.mem_append, or_imp, forall_and]
    exact ⟨by simp [LiteralOutputSearch.readCode, Safe], rootSafe _ _,
      by simp [LiteralWitnessReturn.jump, Safe], ih _ _⟩

def Result (absent found : Nat) (before after : State width 8) : Option (Finset (Channel n)) → Prop
  | none => after.pc = word width absent ∧ after.stack = before.stack
  | some K => after.pc = word width found ∧ after.stack = LiteralWitnessReturn.words width K ++ before.stack

theorem literal_execution (program : Program width 8) (graph : DAG n) (noOr : GateBasis.NoDisjunction graph)
    (b : Nat) (target : Channel n) (base found absent entry cursor : Nat) (state : State width 8)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : base + (2 * n + 1) * graph.nodeCount + entry + graph.roots.length * LiteralOutputSearch.stride b target graph.nodeCount base + 18 * n + 404 < 2 ^ width)
    (heapFits : state.heap.size < 2 ^ width) (matrix : LiteralRoot.MatrixAt state.heap base graph)
    (roots : LiteralOutputSearch.Stored state.heap cursor graph.roots)
    (present : SharedRootRead.BlockAt program entry
      ((LiteralOutputSearch.code b target graph.nodeCount base found absent graph.roots.length entry cursor).map redirect)) :
    ∃ final ticks peak, Execution program state final ticks peak ∧
      ticks ≤ graph.roots.length * (73 * n + 70) + 2 ∧ peak ≤ state.liveWords + n ∧
      final.heap = state.heap ∧ final.output = state.output ∧ final.halted = false ∧
      Result absent found state final (LiteralWitness.search graph b target) := by
  have block := view_block program entry _ (literal_safe b target _ _ _ _ _ _ _) (by
    intro i h; simpa only [List.length_map, List.getElem?_map] using present i (by simpa using h))
  obtain ⟨final, ticks, peak, trace, time, space, heap, stack, active, result⟩ :=
    LiteralOutputSearch.execution (view program) graph noOr b target base found absent graph.roots entry cursor
      (swap state) position running room heapFits matrix roots block
  refine ⟨swap final, ticks, peak, ?_, time, by simpa only [swap_live] using space, heap, stack, active, ?_⟩
  · simpa only [swap_swap] using WitnessStack.execution program _ _ _ _ trace active
  · change LiteralOutputSearch.Result absent found (swap state) final (LiteralWitness.search graph b target) at result
    cases answer : LiteralWitness.search graph b target <;>
      simpa only [Result, swap, LiteralOutputSearch.Result, answer] using result

theorem monotone_execution (program : Program width 8) (graph : DAG n)
    (b : Nat) (target : Channel n) (base found absent entry cursor : Nat) (state : State width 8)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : base + (n + 1) * graph.nodeCount + entry + graph.roots.length * MonotoneOutputSearch.stride b n + 18 * n + 132 < 2 ^ width)
    (heapFits : state.heap.size < 2 ^ width) (matrix : MonotoneRoot.MatrixAt state.heap base graph)
    (roots : LiteralOutputSearch.Stored state.heap cursor graph.roots)
    (present : SharedRootRead.BlockAt program entry
      ((MonotoneOutputSearch.code b target graph.nodeCount base found absent graph.roots.length entry cursor).map redirect)) :
    ∃ final ticks peak, Execution program state final ticks peak ∧
      ticks ≤ graph.roots.length * (22 * n + 22) + 2 ∧ peak ≤ state.liveWords + n ∧
      final.heap = state.heap ∧ final.output = state.output ∧ final.halted = false ∧
      Result absent found state final (MonotoneDecision.search graph b target) := by
  have block := view_block program entry _ (monotone_safe b target _ _ _ _ _ _ _) (by
    intro i h; simpa only [List.length_map, List.getElem?_map] using present i (by simpa using h))
  obtain ⟨final, ticks, peak, trace, time, space, heap, stack, active, result⟩ :=
    MonotoneOutputSearch.execution (view program) graph b target base found absent graph.roots entry cursor
      (swap state) position running room heapFits matrix roots block
  refine ⟨swap final, ticks, peak, ?_, time, by simpa only [swap_live] using space, heap, stack, active, ?_⟩
  · simpa only [swap_swap] using WitnessStack.execution program _ _ _ _ trace active
  · change LiteralOutputSearch.Result absent found (swap state) final (MonotoneDecision.search graph b target) at result
    cases answer : MonotoneDecision.search graph b target <;>
      simpa only [Result, swap, LiteralOutputSearch.Result, answer] using result

end Controller.Extensions.BasisStackSearch
