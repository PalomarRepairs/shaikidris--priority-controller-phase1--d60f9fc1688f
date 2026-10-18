module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Extensions.LiteralWitnessReturn

@[expose] public section

/-! A source-read traversal of all declared outputs. The schedule is unrolled
by output count; no root identifier or literal value occurs in its instruction
data. Its code and execution both have size O(nq). Each failed query preserves
the source and matrix; the first successful query emits one channel vector. -/
namespace Controller.Extensions.LiteralOutputSearch
open Controller.Decoder Controller.Decoder.DAG Controller.Cost Controller.Cost.EnumerationSteps
open Controller.Extensions.LiteralDecision Controller.Extensions.LiteralRoot
open Controller.Extensions.LiteralWitnessReturn (words jump)
open Controller.Extensions.LiteralScan (word_val)

variable {n width : Nat}

def stride (b : Nat) (target : Channel n) (nodes base : Nat) : Nat :=
  LiteralWitnessReturn.rootSize b +
    LiteralWitnessEmit.size (LiteralWitnessReturn.operands true b target nodes base) + 2 +
    LiteralWitnessEmit.size (LiteralWitnessReturn.operands false b target nodes base) + 4

theorem stride_bound (b : Nat) (target : Channel n) (nodes base : Nat) :
    stride b target nodes base ≤ 154 + 18 * n := by
  have root : LiteralWitnessReturn.rootSize b ≤ 148 := by
    unfold LiteralWitnessReturn.rootSize; split <;> omega
  have p := LiteralWitnessEmit.size_bound (LiteralWitnessReturn.operands true b target nodes base)
  have q := LiteralWitnessEmit.size_bound (LiteralWitnessReturn.operands false b target nodes base)
  simp only [LiteralWitnessReturn.operands_length] at p q
  unfold stride; omega

theorem return_finish (b : Nat) (target : Channel n) (nodes base entry : Nat) :
    LiteralWitnessReturn.finish b target nodes base (entry + 2) + 2 =
      entry + stride b target nodes base := by
  unfold LiteralWitnessReturn.finish LiteralWitnessReturn.singleEntry LiteralWitnessReturn.keepEntry stride
  omega

def readCode (cursor : Nat) : List (Instruction width 8) :=
  [.constant 3 (word width cursor), .load 4 3]

theorem read_execution (program : Program width 8) (state : State width 8) (entry cursor root : Nat)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 2 < 2 ^ width) (cursorFits : cursor < 2 ^ width)
    (cell : state.heap[cursor]? = some (word width root))
    (present : SharedRootRead.BlockAt program entry (readCode cursor)) :
    ∃ final, Execution program state final 2 state.liveWords ∧
      final.pc = word width (entry + 2) ∧ final.reg 4 = word width root ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧ final.halted = false := by
  obtain ⟨middle, tr, pc, reg, heap, stack, output, active, _⟩ :=
    SharedEvaluationReclaim.constant_execution program entry cursor 3 state position running (by omega)
      (by simpa [readCode] using present 0 (by simp [readCode]))
  have address : (middle.reg 3).val = cursor := by rw [reg, word_val cursor cursorFits]
  have inside : (middle.reg 3).val < middle.heap.size := by
    rw [address, heap]; exact (Array.getElem?_eq_some_iff.mp cell).1
  obtain ⟨final, tr', pc', reg', heap', stack', output', active', _⟩ :=
    load_execution program middle (entry + 1) 4 3 pc active (by omega) inside
      (by simpa [readCode] using present 1 (by simp [readCode]))
  have live : middle.liveWords = state.liveWords := by simp only [State.liveWords, heap, stack, output]
  refine ⟨final, by simpa only [live, Nat.max_self] using tr.append tr', by simpa only [Nat.add_assoc] using pc',
    ?_, heap'.trans heap, stack'.trans stack, output'.trans output, active'⟩
  rw [reg']
  have c := cell
  rw [← heap, ← address, Array.getElem?_eq_getElem inside] at c
  exact Option.some.inj c

def code (b : Nat) (target : Channel n) (nodes base found absent : Nat) : Nat → Nat → Nat → List (Instruction width 8)
  | 0, _, _ => jump absent
  | count + 1, entry, cursor =>
    readCode cursor ++
      (LiteralWitnessReturn.code b target nodes base (entry + 2) (entry + stride b target nodes base) ++
        (jump found ++ code b target nodes base found absent count (entry + stride b target nodes base) (cursor + 1)))

@[simp] theorem code_length (b : Nat) (target : Channel n) (nodes base found absent count entry cursor : Nat) :
    (code (width := width) b target nodes base found absent count entry cursor).length =
      count * stride b target nodes base + 2 := by
  induction count generalizing entry cursor with
  | zero => simp [code, jump]
  | succ count ih =>
    have size := LiteralWitnessReturn.code_length (width := width) b target nodes base (entry + 2)
      (entry + stride b target nodes base)
    have endAt := return_finish b target nodes base entry
    simp only [code, List.length_append, readCode, jump, List.length_cons, List.length_nil, ih]
    rw [Nat.succ_mul]; omega

def Result (absent found : Nat) (before after : State width 8) : Option (Finset (Channel n)) → Prop
  | none => after.pc = word width absent ∧ after.output = before.output
  | some K => after.pc = word width found ∧ after.output = words width K ++ before.output

def Stored (heap : Array (Word width)) (cursor : Nat) {nodes : Nat} (roots : List (Fin nodes)) : Prop :=
  ∀ i, (h : i < roots.length) → heap[cursor + i]? = some (word width (roots[i]'h).val)

set_option maxHeartbeats 1000000 in
theorem execution (program : Program width 8) (graph : DAG n) (noOr : GateBasis.NoDisjunction graph)
    (b : Nat) (target : Channel n) (base found absent : Nat) (roots : List (Fin graph.nodeCount)) :
    ∀ (entry cursor : Nat) (state : State width 8),
      state.pc = word width entry → state.halted = false →
      base + (2 * n + 1) * graph.nodeCount + entry +
        roots.length * stride b target graph.nodeCount base + 18 * n + 404 < 2 ^ width →
      state.heap.size < 2 ^ width →
      MatrixAt state.heap base graph → Stored state.heap cursor roots →
      SharedRootRead.BlockAt program entry
        (code b target graph.nodeCount base found absent roots.length entry cursor) →
      ∃ final ticks peak, Execution program state final ticks peak ∧
        ticks ≤ roots.length * (73 * n + 70) + 2 ∧ peak ≤ state.liveWords + n ∧
        final.heap = state.heap ∧ final.stack = state.stack ∧ final.halted = false ∧
        Result absent found state final
          (firstSuccess (fun root => LiteralWitness.rootWitness b target (LiteralMachine.summary graph root)) roots) := by
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
    rw [LiteralWitnessReturn.code_length] at tailAt
    have jumpAt := SharedDetectorAssembly.block_left program _ _ _ tailAt
    have nextAt := SharedDetectorAssembly.block_right program _ _ _ tailAt
    simp only [jump, List.length_cons, List.length_nil, Nat.reduceAdd, return_finish] at nextAt
    have counts : (root :: roots).length = roots.length + 1 := rfl
    simp only [counts, Nat.add_mul, Nat.one_mul] at room
    obtain ⟨loaded, loadTrace, loadPC, rootReg, loadHeap, loadStack, loadOutput, loadRun⟩ :=
      read_execution program state entry cursor root.val position running (by omega) cursorFits cell readAt
    have loadLive : loaded.liveWords = state.liveWords := by simp only [State.liveWords, loadHeap, loadStack, loadOutput]
    obtain ⟨queried, qt, qp, queryTrace, queryTime, querySpace, queryHeap, queryStack, queryRun, result⟩ :=
      LiteralWitnessReturn.execution program loaded graph noOr b target base (entry + 2)
        (entry + stride b target graph.nodeCount base) root loadPC loadRun (by simp only [Nat.add_mul, Nat.one_mul]; omega)
        (by rw [loadHeap]; exact heapFits) rootReg (by rw [loadHeap]; exact matrix) rootAt
    have qh : queried.heap = state.heap := queryHeap.trans loadHeap
    have qs : queried.stack = state.stack := queryStack.trans loadStack
    have choice := decision_set b target (LiteralMachine.summary graph root)
    cases answer : decision b target (LiteralMachine.summary graph root) with
    | none =>
      have missing : LiteralWitness.rootWitness b target (LiteralMachine.summary graph root) = none := by
        simpa only [answer, Option.map_none] using choice.symm
      have res : queried.pc = word width (entry + stride b target graph.nodeCount base) ∧
          queried.output = loaded.output := by simpa only [answer, LiteralWitnessReturn.Result] using result
      have qo : queried.output = state.output := res.2.trans loadOutput
      have ql : queried.liveWords = state.liveWords := by simp only [State.liveWords, qh, qs, qo]
      have remaining : Stored queried.heap (cursor + 1) roots := by
        intro i h
        have cell := stored (i + 1) (by simpa using Nat.succ_lt_succ h)
        simpa only [qh, List.getElem_cons_succ, Nat.add_assoc, Nat.add_comm 1 i] using cell
      obtain ⟨final, ft, fp, trace, time, space, heap, stack, active, outcome⟩ :=
        ih (entry + stride b target graph.nodeCount base) (cursor + 1) queried res.1 queryRun
          (by simp only [Nat.add_mul, Nat.one_mul]; omega) (by rw [qh]; exact heapFits) (by rw [qh]; exact matrix) remaining nextAt
      refine ⟨final, 2 + qt + ft, max (max state.liveWords qp) fp,
        (loadTrace.append queryTrace).append trace, ?_, ?_, heap.trans qh, stack.trans qs, active, ?_⟩
      · simp only [counts, Nat.add_mul, Nat.one_mul]; omega
      · rw [loadLive] at querySpace
        rw [ql] at space
        exact max_le (max_le (by omega) querySpace) space
      · simpa only [firstSuccess, missing, Result, qo] using outcome
    | some descriptor =>
      have foundRoot : LiteralWitness.rootWitness b target (LiteralMachine.summary graph root) =
          some (descriptor.set b target (LiteralMachine.summary graph root)) := by
        simpa only [answer, Option.map_some] using choice.symm
      have res : queried.pc = word width (LiteralWitnessReturn.finish b target graph.nodeCount base (entry + 2)) ∧
          queried.output = words width (descriptor.set b target (LiteralMachine.summary graph root)) ++ loaded.output := by
        simpa only [answer, LiteralWitnessReturn.Result] using result
      have ql : queried.liveWords = state.liveWords + n := by
        simp only [State.liveWords, qh, qs, res.2, loadOutput, List.length_append, LiteralWitnessReturn.words_length]
        omega
      obtain ⟨final, trace, pc, heap, stack, output, active, _⟩ :=
        jump_execution program queried (LiteralWitnessReturn.finish b target graph.nodeCount base (entry + 2))
          found res.1 queryRun (by rw [return_finish]; omega)
          (by simpa [jump] using jumpAt 0 (by simp [jump]))
          (by simpa [jump] using jumpAt 1 (by simp [jump]))
      refine ⟨final, 2 + qt + 2, max (max state.liveWords qp) queried.liveWords,
        (loadTrace.append queryTrace).append trace, ?_, ?_, heap.trans qh, stack.trans qs, active, ?_⟩
      · simp only [counts, Nat.add_mul, Nat.one_mul]; omega
      · rw [loadLive] at querySpace
        rw [ql]
        exact max_le (max_le (by omega) querySpace) le_rfl
      · simp only [firstSuccess, foundRoot, Result]
        exact ⟨pc, by rw [output, res.2, loadOutput]⟩

end Controller.Extensions.LiteralOutputSearch
