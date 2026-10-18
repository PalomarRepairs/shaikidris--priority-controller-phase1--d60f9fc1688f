module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Extensions.MonotoneReturn

@[expose] public section

/-! All declared outputs share the one full/singleton matrix. Root identifiers
are fetched from the source packet, and only the first witness is emitted. -/
namespace Controller.Extensions.MonotoneOutputSearch
open Controller.Decoder Controller.Decoder.DAG Controller.Cost Controller.Cost.EnumerationSteps
open Controller.Extensions.MonotoneDecision Controller.Extensions.MonotoneRoot
open Controller.Extensions.LiteralWitnessReturn (words jump)
open Controller.Extensions.LiteralOutputSearch (readCode read_execution Result Stored)

variable {n width : Nat}

def stride (b n : Nat) : Nat := MonotoneReturn.rootSize b +
  LiteralWitnessEmit.size (MonotoneReturn.operands true n) + 2 +
  LiteralWitnessEmit.size (MonotoneReturn.operands false n) + 4

theorem stride_bound (b n : Nat) : stride b n ≤ 39 + 18 * n := by
  have root : MonotoneReturn.rootSize b ≤ 33 := by unfold MonotoneReturn.rootSize; split <;> omega
  have p := LiteralWitnessEmit.size_bound (MonotoneReturn.operands true n)
  have q := LiteralWitnessEmit.size_bound (MonotoneReturn.operands false n)
  simp only [MonotoneReturn.operands_length] at p q
  unfold stride; omega

theorem return_finish (b n entry : Nat) :
    MonotoneReturn.finish b n (entry + 2) + 2 = entry + stride b n := by
  unfold MonotoneReturn.finish MonotoneReturn.singleEntry MonotoneReturn.fullEntry stride; omega

def code (b : Nat) (target : Channel n) (nodes base found absent : Nat) : Nat → Nat → Nat → List (Instruction width 8)
  | 0, _, _ => jump absent
  | count + 1, entry, cursor => readCode cursor ++
      (MonotoneReturn.code b target nodes base (entry + 2) (entry + stride b n) ++
        (jump found ++ code b target nodes base found absent count (entry + stride b n) (cursor + 1)))

@[simp] theorem code_length (b : Nat) (target : Channel n) (nodes base found absent count entry cursor : Nat) :
    (code (width := width) b target nodes base found absent count entry cursor).length = count * stride b n + 2 := by
  induction count generalizing entry cursor with
  | zero => simp [code, jump]
  | succ count ih =>
    have size := MonotoneReturn.code_length (width := width) b target nodes base (entry + 2) (entry + stride b n)
    have endAt := return_finish b n entry
    simp only [code, List.length_append, readCode, jump, List.length_cons, List.length_nil, ih]
    rw [Nat.succ_mul]; omega

set_option maxHeartbeats 1000000 in
theorem execution (program : Program width 8) (graph : DAG n)
    (b : Nat) (target : Channel n) (base found absent : Nat) (roots : List (Fin graph.nodeCount)) :
    ∀ (entry cursor : Nat) (state : State width 8),
      state.pc = word width entry → state.halted = false →
      base + (n + 1) * graph.nodeCount + entry + roots.length * stride b n + 18 * n + 132 < 2 ^ width →
      state.heap.size < 2 ^ width → MatrixAt state.heap base graph → Stored state.heap cursor roots →
      SharedRootRead.BlockAt program entry (code b target graph.nodeCount base found absent roots.length entry cursor) →
      ∃ final ticks peak, Execution program state final ticks peak ∧
        ticks ≤ roots.length * (22 * n + 22) + 2 ∧ peak ≤ state.liveWords + n ∧
        final.heap = state.heap ∧ final.stack = state.stack ∧ final.halted = false ∧
        Result absent found state final
          (firstSuccess (fun root => (decision graph b target root).map Descriptor.set) roots) := by
  induction roots with
  | nil =>
    intro entry cursor state position running room heapFits matrix stored present
    obtain ⟨final, trace, pc, heap, stack, output, active, _⟩ :=
      jump_execution program state entry absent position running (by omega)
        (by simpa [code, jump] using present 0 (by simp [code, jump]))
        (by simpa [code, jump] using present 1 (by simp [code, jump]))
    exact ⟨final, 2, state.liveWords, trace, by simp, by omega, heap, stack, active, pc, output⟩
  | cons root roots ih =>
    intro entry cursor state position running room heapFits matrix stored present
    have cell : state.heap[cursor]? = some (word width root.val) := stored 0 (by simp)
    have cursorFits : cursor < 2 ^ width := (Array.getElem?_eq_some_iff.mp cell).1.trans heapFits
    have readAt := SharedDetectorAssembly.block_left program entry _ _ present
    have restAt := SharedDetectorAssembly.block_right program entry _ _ present
    simp only [readCode, List.length_cons, List.length_nil] at restAt
    have rootAt := SharedDetectorAssembly.block_left program (entry + 2) _ _ restAt
    have tailAt := SharedDetectorAssembly.block_right program (entry + 2) _ _ restAt
    rw [MonotoneReturn.code_length] at tailAt
    have jumpAt := SharedDetectorAssembly.block_left program _ _ _ tailAt
    have nextAt := SharedDetectorAssembly.block_right program _ _ _ tailAt
    simp only [jump, List.length_cons, List.length_nil, Nat.reduceAdd, return_finish] at nextAt
    have counts : (root :: roots).length = roots.length + 1 := rfl
    simp only [counts, Nat.add_mul, Nat.one_mul] at room
    obtain ⟨loaded, loadTrace, loadPC, rootReg, loadHeap, loadStack, loadOutput, loadRun⟩ :=
      read_execution program state entry cursor root.val position running (by omega) cursorFits cell readAt
    have loadLive : loaded.liveWords = state.liveWords := by simp only [State.liveWords, loadHeap, loadStack, loadOutput]
    obtain ⟨queried, qt, qp, queryTrace, queryTime, querySpace, queryHeap, queryStack, queryRun, result⟩ :=
      MonotoneReturn.execution program loaded graph b target base (entry + 2) (entry + stride b n) root loadPC loadRun
        (by simp only [Nat.add_mul, Nat.one_mul]; omega)
        (by rw [loadHeap]; exact heapFits) rootReg (by rw [loadHeap]; exact matrix) rootAt
    have qh : queried.heap = state.heap := queryHeap.trans loadHeap
    have qs : queried.stack = state.stack := queryStack.trans loadStack
    cases answer : decision graph b target root with
    | none =>
      have res : queried.pc = word width (entry + stride b n) ∧ queried.output = loaded.output := by
        simpa only [answer, MonotoneReturn.Result] using result
      have qo : queried.output = state.output := res.2.trans loadOutput
      have ql : queried.liveWords = state.liveWords := by simp only [State.liveWords, qh, qs, qo]
      have remaining : Stored queried.heap (cursor + 1) roots := by
        intro i h
        have cell := stored (i + 1) (by simpa using Nat.succ_lt_succ h)
        simpa only [qh, List.getElem_cons_succ, Nat.add_assoc, Nat.add_comm 1 i] using cell
      obtain ⟨final, ft, fp, trace, time, space, heap, stack, active, outcome⟩ :=
        ih (entry + stride b n) (cursor + 1) queried res.1 queryRun
          (by simp only [Nat.add_mul, Nat.one_mul]; omega) (by rw [qh]; exact heapFits) (by rw [qh]; exact matrix) remaining nextAt
      refine ⟨final, 2 + qt + ft, max (max state.liveWords qp) fp,
        (loadTrace.append queryTrace).append trace, ?_, ?_, heap.trans qh, stack.trans qs, active, ?_⟩
      · simp only [counts, Nat.add_mul, Nat.one_mul]; omega
      · rw [loadLive] at querySpace
        rw [ql] at space
        exact max_le (max_le (by omega) querySpace) space
      · simpa only [firstSuccess, answer, Option.map_none, Result, qo] using outcome
    | some descriptor =>
      have res : queried.pc = word width (MonotoneReturn.finish b n (entry + 2)) ∧
          queried.output = words width descriptor.set ++ loaded.output := by
        simpa only [answer, MonotoneReturn.Result] using result
      have ql : queried.liveWords = state.liveWords + n := by
        simp only [State.liveWords, qh, qs, res.2, loadOutput, List.length_append, LiteralWitnessReturn.words_length]; omega
      obtain ⟨final, trace, pc, heap, stack, output, active, _⟩ :=
        jump_execution program queried (MonotoneReturn.finish b n (entry + 2)) found res.1 queryRun
          (by rw [return_finish]; omega)
          (by simpa [jump] using jumpAt 0 (by simp [jump]))
          (by simpa [jump] using jumpAt 1 (by simp [jump]))
      refine ⟨final, 2 + qt + 2, max (max state.liveWords qp) queried.liveWords,
        (loadTrace.append queryTrace).append trace, ?_, ?_, heap.trans qh, stack.trans qs, active, ?_⟩
      · simp only [counts, Nat.add_mul, Nat.one_mul]; omega
      · rw [loadLive] at querySpace
        rw [ql]
        exact max_le (max_le (by omega) querySpace) le_rfl
      · simp only [firstSuccess, answer, Option.map_some, Result]
        exact ⟨pc, by rw [output, res.2, loadOutput]⟩

end Controller.Extensions.MonotoneOutputSearch
