module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Extensions.MonotoneTableConstruction
public import Controller.Extensions.MonotoneDecision
public import Controller.Extensions.MonotoneScan

public import Mathlib.Tactic.Ring

@[expose] public section

/-! A runtime monotone root query consumes the shared full/singleton table. -/
namespace Controller.Extensions.MonotoneRoot
open Controller.Decoder Controller.Decoder.DAG Controller.Cost
open Controller.Extensions.MonotoneDecision Controller.Extensions.LiteralScan
open Controller.Extensions.MonotoneTableConstruction

variable {n width : Nat}

def MatrixAt (heap : Array (Word width)) (base : Nat) (graph : DAG n) : Prop :=
  ∀ i, i < (matrix graph width).length → heap[base + i]? = (matrix graph width)[i]?

theorem single_assignment (c : Channel n) : SharedTableBatch.single c = assignmentOfSet {c} := by
  funext d
  simp [SharedTableBatch.single, SharedCandidateProbe.enabled, assignmentOfSet]

theorem full_cell (graph : DAG n) (heap : Array (Word width)) (base : Nat) (root : Fin graph.nodeCount)
    (stored : MatrixAt heap base graph) : heap[base + root.val]? =
      some (boolWord width (graph.eval (assignmentOfSet Finset.univ) root)) := by
  have inside : root.val < (matrix graph width).length := by
    rw [matrix_length]; have := root.isLt; have mult := Nat.le_mul_of_pos_left graph.nodeCount (show 0 < n + 1 by omega); omega
  rw [stored _ inside]
  unfold matrix
  rw [List.getElem?_append_left (by simpa only [SharedTableProbe.words_length] using root.isLt)]
  have full : (fun _ : Channel n => true) = assignmentOfSet Finset.univ := by funext c; simp [assignmentOfSet]
  simp only [SharedTableProbe.words, List.getElem?_ofFn, dite_eq_left root.isLt, DAG.evalTable_eq_eval, full]

theorem singleton_cell (graph : DAG n) (heap : Array (Word width)) (base : Nat) (root : Fin graph.nodeCount)
    (stored : MatrixAt heap base graph) (c : Channel n) :
    heap[base + (n - c.val) * graph.nodeCount + root.val]? =
      some (boolWord width (singletonBit graph root c.val)) := by
  have shift : n - c.val = n - 1 - c.val + 1 := by have := c.isLt; omega
  have inside : (n - c.val) * graph.nodeCount + root.val < (matrix graph width).length := by
    rw [matrix_length]
    have mult := Nat.mul_le_mul_right graph.nodeCount (show n - c.val ≤ n by omega)
    have := root.isLt
    simp only [Nat.add_mul, Nat.one_mul]; omega
  rw [show base + (n - c.val) * graph.nodeCount + root.val = base + ((n - c.val) * graph.nodeCount + root.val) by omega,
    stored _ inside]
  have columnBound : n - 1 - c.val < (List.finRange n).reverse.length := by have := c.isLt; simp; omega
  have selected : (List.finRange n).reverse[n - 1 - c.val] = c := by
    apply Fin.ext
    simp only [List.getElem_reverse, List.length_finRange, List.getElem_finRange]
    change n - 1 - (n - 1 - c.val) = c.val
    have := c.isLt; omega
  have cell := LiteralColumns.flatMap_cell (List.finRange n).reverse
    (fun channel => SharedTableProbe.words graph (SharedTableBatch.single channel) width) graph.nodeCount
    (fun _ _ => SharedTableProbe.words_length _ _) ⟨n - 1 - c.val, columnBound⟩ root.val root.isLt
  rw [selected] at cell
  unfold matrix
  rw [List.getElem?_append_right (by rw [SharedTableProbe.words_length, shift, Nat.add_mul, Nat.one_mul]; omega)]
  have address : (n - c.val) * graph.nodeCount + root.val - (SharedTableProbe.words graph (fun _ => true) width).length =
      (n - 1 - c.val) * graph.nodeCount + root.val := by
    rw [SharedTableProbe.words_length, shift, Nat.add_mul, Nat.one_mul]; omega
  rw [address]
  change (SharedTableBatch.columns graph (List.finRange n) width)[_]? = _
  rw [SharedTableBatch.columns, cell]
  simp only [SharedTableProbe.words, List.getElem?_ofFn, dite_eq_left root.isLt, DAG.evalTable_eq_eval,
    single_assignment, singletonBit_channel]

def code (b : Nat) (target : Channel n) (nodes base entry absent full single : Nat) : List (Instruction width 8) :=
  LiteralRootRun.readCode (base + (n - target.val) * nodes) (entry + 7) (entry + 14) 0 ++
    (LiteralRootRun.readCode base absent full 0 ++
      (if b = 1 then LiteralWitnessReturn.jump absent else MonotoneScan.code n nodes base (entry + 14) single absent))

@[simp] theorem code_length (b : Nat) (target : Channel n) (nodes base entry absent full single : Nat) :
    (code (width := width) b target nodes base entry absent full single).length = 14 + if b = 1 then 2 else 19 := by
  simp only [code, List.length_append, LiteralRootRun.readCode_length]
  split <;> simp [LiteralWitnessReturn.jump]

def Lands (absent full single : Nat) (state : State width 8) : Option (Descriptor n) → Prop
  | none => state.pc = word width absent
  | some .full => state.pc = word width full
  | some (.single c) => state.pc = word width single ∧ state.reg 1 = word width c.val

set_option maxHeartbeats 1500000 in
theorem execution (program : Program width 8) (graph : DAG n) (b : Nat) (target : Channel n)
    (base entry absent full single : Nat) (root : Fin graph.nodeCount) (state : State width 8)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : base + (n + 1) * graph.nodeCount + entry + 64 < 2 ^ width)
    (held : state.reg 4 = word width root.val) (stored : MatrixAt state.heap base graph)
    (present : SharedRootRead.BlockAt program entry (code b target graph.nodeCount base entry absent full single)) :
    ∃ final, LiteralRootRun.Quiet program state final (13 * n + 16) ∧
      Lands absent full single final (decision graph b target root) := by
  have size : (n + 1) * graph.nodeCount = n * graph.nodeCount + graph.nodeCount := by ring
  rw [size] at room
  have targetBound := Nat.mul_le_mul_right graph.nodeCount (show n - target.val ≤ n by omega)
  have rootBound := root.isLt
  have headAt := SharedDetectorAssembly.block_left program entry _ _ present
  have restAt := SharedDetectorAssembly.block_right program entry _ _ present
  simp only [LiteralRootRun.readCode_length] at restAt
  have fullAt := SharedDetectorAssembly.block_left program _ _ _ restAt
  have tailAt := SharedDetectorAssembly.block_right program _ _ _ restAt
  simp only [LiteralRootRun.readCode_length, Nat.add_assoc, Nat.reduceAdd] at tailAt
  obtain ⟨middle, mt, trace, time, active, heap, stack, output, frame, landed⟩ :=
    LiteralRootRun.read_execution program state entry (base + (n - target.val) * graph.nodeCount)
      (entry + 7) (entry + 14) 0 root.val (singletonBit graph root target.val)
      position running (by omega) held (singleton_cell graph state.heap base root stored target) headAt
  have live : middle.liveWords = state.liveWords := by simp only [State.liveWords, heap, stack, output]
  cases healthy : singletonBit graph root target.val with
  | false =>
    have pc : middle.pc = word width (entry + 7) := by simpa only [healthy, Bool.false_eq_true, ite_false] using landed
    obtain ⟨final, ft, tr, bound, run, hf, sf, of, ff, result⟩ :=
      LiteralRootRun.read_execution program middle (entry + 7) base absent full 0 root.val
        (graph.eval (assignmentOfSet Finset.univ) root) pc active (by omega) (frame.trans held)
        (by rw [heap]; exact full_cell graph state.heap base root stored) fullAt
    refine ⟨final, ⟨mt + ft, ?_, by omega, run, hf.trans heap, sf.trans stack, of.trans output, ff.trans frame⟩, ?_⟩
    · simpa only [live, Nat.max_self] using trace.append tr
    · cases value : graph.eval (assignmentOfSet Finset.univ) root with
      | false => simpa [decision, healthy, value, Lands] using result
      | true =>
        have yes : final.pc = word width full ∧ final.reg 1 = word width 0 := by simpa only [value, ite_true] using result
        simpa [decision, healthy, value, Lands] using yes.1
  | true =>
    have pc : middle.pc = word width (entry + 14) := (by simpa only [healthy, ite_true] using landed :
      middle.pc = word width (entry + 14) ∧ middle.reg 1 = word width 0).1
    by_cases one : b = 1
    · have block : SharedRootRead.BlockAt program (entry + 14) (LiteralWitnessReturn.jump absent) := by
        simpa only [one, ite_true] using tailAt
      obtain ⟨final, tr, pos, hf, sf, of, run, ff⟩ := EnumerationSteps.jump_execution program middle (entry + 14) absent
        pc active (by omega) (by simpa [LiteralWitnessReturn.jump] using block 0 (by simp [LiteralWitnessReturn.jump]))
        (by simpa [LiteralWitnessReturn.jump] using block 1 (by simp [LiteralWitnessReturn.jump]))
      refine ⟨final, ⟨mt + 2, ?_, by omega, run, hf.trans heap, sf.trans stack, of.trans output,
        (ff 4 (by decide)).trans frame⟩, ?_⟩
      · simpa only [live, Nat.max_self] using trace.append tr
      · simpa only [decision, healthy, one, ite_true, Lands] using pos
    · obtain ⟨final, ft, tr, bound, run, hf, sf, of, ff, result⟩ :=
        MonotoneScan.execution program middle n graph.nodeCount base (entry + 14) single absent root.val
          (singletonBit graph root) rootBound pc active (by rw [size]; omega) (frame.trans held)
          (by intro c h; rw [heap]; exact singleton_cell graph state.heap base root stored ⟨c, h⟩)
          (by simpa only [one, ite_false] using tailAt)
      refine ⟨final, ⟨mt + ft, ?_, by omega, run, hf.trans heap, sf.trans stack, of.trans output, ff.trans frame⟩, ?_⟩
      · simpa only [live, Nat.max_self] using trace.append tr
      · cases hit : firstHit (fun c => !singletonBit graph root c) 0 n with
        | none => simpa [decision, healthy, one, hit, LiteralDecision.toChannel, Lands] using result
        | some c =>
          have small : c < n := by simpa using LiteralDecision.firstHit_bound _ 0 n c hit
          simpa [decision, healthy, one, hit, LiteralDecision.toChannel, small, Lands] using result

end Controller.Extensions.MonotoneRoot
