module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedTableBatch
public import Controller.Cost.SharedChannelRewrite
public import Controller.Extensions.LiteralDetector

public import Mathlib.Tactic.Ring

@[expose] public section

/-! Shared evaluations for monotone detection: all singleton assignments and
the full assignment are each evaluated once. The evaluation heap is reclaimed
between probes; the resulting columns are retained for all output queries. -/
namespace Controller.Extensions.MonotoneTableConstruction
open Controller.Decoder Controller.Decoder.DAG Controller.Cost Controller.Cost.GateProgram
open Controller.Cost.ForestIndexedOperands Controller.Cost.UniformDAGSource
open Controller.Cost.UniformDAGRun Controller.Cost.ForestInputPrefixStored
open Controller.Cost.ForestInputStored Controller.Cost.RawTransferLoops

variable {n width : Nat}

def matrix (graph : DAG n) (width : Nat) : List (Word width) :=
  SharedTableProbe.words graph (fun _ => true) width ++
    SharedTableBatch.columns graph (List.finRange n) width

@[simp] theorem matrix_length (graph : DAG n) : (matrix graph width).length = (n + 1) * graph.nodeCount := by
  simp only [matrix, List.length_append, SharedTableProbe.words_length, SharedTableBatch.columns_length,
    List.length_finRange, Nat.add_mul, Nat.one_mul]; omega

def rewriteCode (width n : Nat) (rows : List Row) (roots : List Nat) (value : Bool) : List (Instruction width 8) :=
  SharedWitnessSeed.code width (boolWord width value) n ++
    SharedChannelRewrite.code width (cacheHeap width (packetHeaderHeap width n rows roots) rows roots).size (List.finRange n)

@[simp] theorem rewriteCode_length (width n : Nat) (rows : List Row) (roots : List Nat) (value : Bool) :
    (rewriteCode width n rows roots value).length = 5 * n := by simp [rewriteCode]; omega

/-- Change every input bit, preserving any previously computed columns. -/
theorem rewrite_execution (resident : Program width 8) (state : State width 8)
    (rows : List Row) (roots : List Nat) (values : Assignment n) (value : Bool) (entry : Nat)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 5 * n < 2 ^ width)
    (heapFits : (channelHeap (packetHeaderHeap width n rows roots) rows roots values).size < 2 ^ width)
    (stored : state.heap = channelHeap (packetHeaderHeap width n rows roots) rows roots values)
    (present : SharedRootRead.BlockAt resident entry (rewriteCode width n rows roots value)) :
    ∃ final, Execution resident state final (5 * n) (state.liveWords + n) ∧
      final.heap = channelHeap (packetHeaderHeap width n rows roots) rows roots (fun _ : Fin n => value) ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry + 5 * n) ∧ final.halted = false := by
  have seedAt := SharedDetectorAssembly.block_left resident entry _ _ present
  have writeAt := SharedDetectorAssembly.block_right resident entry _ _ present
  simp only [SharedWitnessSeed.code_length] at writeAt
  obtain ⟨seeded, seedTrace, seedHeap, seedStack, seedOutput, seedPC, seedRun, _⟩ :=
    SharedWitnessSeed.execution resident state (boolWord width value) n entry position running (by omega) seedAt
  have input : seeded.stack = (List.finRange n).map (fun _ => boolWord width value) ++ state.stack := by
    simpa only [List.map_const', List.length_finRange] using seedStack
  obtain ⟨final, trace, heap, stack, output, pc, active, _⟩ :=
    SharedChannelRewrite.execution resident seeded
      (cacheHeap width (packetHeaderHeap width n rows roots) rows roots) #[] values (fun _ => value)
      (List.finRange n) state.stack (entry + 2 * n) seedPC seedRun (by simp; omega)
      (by simpa only [channelHeap_size] using heapFits)
      (by simpa only [Array.append_empty, channelHeap] using seedHeap.trans stored) input writeAt
  have live : seeded.liveWords = state.liveWords + n := by
    simp only [State.liveWords, seedHeap, seedStack, seedOutput, List.length_append, List.length_replicate]; omega
  refine ⟨final, ?_, by simpa only [SharedChannelRewrite.replace_all, Array.append_empty, channelHeap] using heap,
    stack, output.trans seedOutput, ?_, active⟩
  · have joined := seedTrace.append trace
    rw [live, Nat.max_self] at joined
    convert joined using 1 <;> simp only [List.length_finRange] <;> omega
  · simpa only [List.length_finRange, show entry + 2 * n + 3 * n = entry + 5 * n by omega] using pc

def code (graph : DAG n) (width : Nat) (rows : List Row) (roots : List Nat) (entry : Nat) : Program width 8 :=
  SharedTableBatch.code width n rows roots entry (List.finRange n) ++
    ((rewriteCode width n rows roots true).toArray ++
      (SharedTableProbe.code width n rows roots (entry + 157 * n) (entry + 157 * n + 143) ++
        ((rewriteCode width n rows roots false).toArray ++
          (SharedWitnessPark.code width (matrix graph width).length).toArray)))

@[simp] theorem code_size (graph : DAG n) (width : Nat) (rows : List Row) (roots : List Nat) (entry : Nat) :
    (code graph width rows roots entry).size = 162 * n + 143 + 2 * (n + 1) * graph.nodeCount := by
  simp only [code, Array.size_append, SharedTableBatch.code_size, List.length_finRange, List.size_toArray,
    rewriteCode_length, SharedTableProbe.code_size, SharedWitnessPark.code_length, matrix_length]
  ring

set_option maxHeartbeats 1000000 in
theorem execution (resident : Program width 8) (state : State width 8) (graph : DAG n)
    (rows : List Row) (roots : List Nat) (matched : RowsMatch graph rows)
    (heads : HeadsMatch graph rows matched) (rootMatches : RootsMatch graph roots) (entry : Nat)
    (capacity : 4096 * (graph.countedSize + 1) < 2 ^ width)
    (room : entry + 162 * n + 143 + 2 * (n + 1) * graph.nodeCount < 2 ^ width)
    (heapRoom : state.heap.size + (matrix graph width).length < 2 ^ width)
    (position : state.pc = word width entry) (running : state.halted = false)
    (stored : state.heap = channelHeap (packetHeaderHeap width n rows roots) rows roots (fun _ : Fin n => false))
    (present : CodeAt resident entry (code graph width rows roots entry)) :
    ∃ final ticks peak, Execution resident state final ticks peak ∧
      ticks ≤ 128 * ((n + 1) * (graph.countedSize + 1)) ∧
      peak ≤ state.liveWords + 8 * ((n + 1) * (graph.countedSize + 1)) ∧
      final.heap = state.heap ++ (matrix graph width).toArray ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry + 162 * n + 143 + 2 * (n + 1) * graph.nodeCount) ∧
      final.halted = false := by
  have all := present
  unfold code at all
  have batchAt := RawSharedOrdered.takePrefix resident entry _ _ all
  have restAt := RawSharedOrdered.takeSuffix resident entry _ _ all
  simp only [SharedTableBatch.code_size, List.length_finRange] at restAt
  have fullAt := RawSharedOrdered.takePrefix resident _ _ _ restAt
  have tailAt := RawSharedOrdered.takeSuffix resident _ _ _ restAt
  simp only [List.size_toArray, rewriteCode_length] at tailAt
  have probeAt := RawSharedOrdered.takePrefix resident _ _ _ tailAt
  have lastAt := RawSharedOrdered.takeSuffix resident _ _ _ tailAt
  simp only [SharedTableProbe.code_size] at lastAt
  have resetAt := RawSharedOrdered.takePrefix resident _ _ _ lastAt
  have parkAt := RawSharedOrdered.takeSuffix resident _ _ _ lastAt
  simp only [List.size_toArray, rewriteCode_length] at parkAt
  have at157 : entry + 152 * n + 5 * n = entry + 157 * n := by omega
  have at162 : entry + 152 * n + 5 * n + 143 + 5 * n = entry + 162 * n + 143 := by omega
  have size := graph.countedSize_eq
  have sourceFits : ∀ values : Assignment n,
      (channelHeap (packetHeaderHeap width n rows roots) rows roots values).size < 2 ^ width := by
    intro values
    obtain ⟨children, guards⟩ := matched_incidence_lengths graph rows matched
    have rootsLength : roots.length = graph.roots.length := by rw [rootMatches]; simp
    simp only [channelHeap_size, cacheHeap_size, packetHeaderHeap_size, matched.length_eq, children, guards, rootsLength]
    omega
  have toBlock (address : Nat) (instructions : List (Instruction width 8))
      (placed : CodeAt resident address instructions.toArray) : SharedRootRead.BlockAt resident address instructions := by
    intro i h; simpa only [List.getElem?_toArray] using placed ⟨i, by simpa using h⟩
  obtain ⟨batched, bt, bp, btrace, btime, bspace, bh, bs, bo, bc, br⟩ :=
    SharedTableBatch.execution resident graph rows roots matched heads rootMatches (List.finRange n) entry state
      (by omega) batchAt (by simp; omega) position running stored
  obtain ⟨enabled, etrace, eh, es, eo, ec, er⟩ :=
    rewrite_execution resident batched rows roots (fun _ => false) true (entry + 152 * n)
      (by simpa only [List.length_finRange] using bc) br (by omega) (sourceFits _) (bh.trans stored)
      (toBlock _ _ fullAt)
  obtain ⟨sampled, st, sp, strace, stime, sspace, sh, ss, so, sc, sr, _⟩ :=
    SharedTableProbe.execution resident enabled graph rows roots matched heads rootMatches (fun _ => true)
      (entry + 157 * n) (entry + 157 * n + 143) (by omega)
      (by simpa only [at157] using probeAt) (by omega) (by simpa only [at157] using ec) er eh
  obtain ⟨reset, rtrace, rh, rs, ro, rc, rr⟩ :=
    rewrite_execution resident sampled rows roots (fun _ => true) false (entry + 157 * n + 143)
      sc sr (by omega) (sourceFits _) (sh.trans eh)
      (toBlock _ _ (by simpa only [at157] using resetAt))
  have resetHeap : reset.heap = state.heap := rh.trans stored.symm
  have resetStack : reset.stack = matrix graph width ++ state.stack := by
    rw [rs, ss, es, bs]; simp only [matrix, List.append_assoc]
  obtain ⟨final, ptrace, ph, ps, po, pc, pr, _⟩ :=
    SharedWitnessPark.execution resident reset (matrix graph width) state.stack (entry + 162 * n + 143)
      (by convert rc using 1 <;> congr 1 <;> omega) rr
      (by simpa only [matrix_length, Nat.mul_assoc] using room) (by rw [resetHeap]; exact heapRoom) resetStack
      (toBlock _ _ (by simpa only [at162] using parkAt))
  have bl : batched.liveWords = state.liveWords + n * graph.nodeCount := by
    simp only [State.liveWords, bh, bs, bo, SharedTableBatch.columns_length, List.length_finRange, List.length_append]; omega
  have el : enabled.liveWords = batched.liveWords := by
    simp only [State.liveWords, eh, bh, stored, channelHeap_size, es, eo]
  have sl : sampled.liveWords = state.liveWords + (matrix graph width).length := by
    have growth : sampled.liveWords = enabled.liveWords + graph.nodeCount := by
      simp only [State.liveWords, sh, ss, so, SharedTableProbe.words_length, List.length_append]; omega
    rw [growth, el, bl, matrix_length]; ring
  have rl : reset.liveWords = sampled.liveWords := by
    simp only [State.liveWords, rh, sh, eh, channelHeap_size, rs, ro]
  have totalPositive : 0 < (n + 1) * (graph.countedSize + 1) := Nat.mul_pos (by omega) (by omega)
  have nodeBound : graph.nodeCount ≤ graph.countedSize + 1 := by omega
  have tableBound := Nat.mul_le_mul_left (n + 1) nodeBound
  have extraBound := Nat.mul_le_mul_left (n + 2) nodeBound
  have timeNodes := Nat.mul_le_mul_left n nodeBound
  have joined := (btrace.append etrace).append (strace.append (rtrace.append ptrace))
  refine ⟨final, bt + 5 * n + (st + (5 * n + 2 * (matrix graph width).length)),
    max (max bp (batched.liveWords + n)) (max sp (max (sampled.liveWords + n) reset.liveWords)),
    joined, ?_, ?_, ph.trans (by rw [resetHeap]), ps, po.trans (ro.trans (so.trans (eo.trans bo))), ?_, pr⟩
  · simp only [List.length_finRange] at btime
    rw [matrix_length]
    nlinarith only [btime, stime, tableBound, size]
  · simp only [List.length_finRange] at bspace
    rw [el, bl] at sspace
    rw [bl, sl, rl, sl, matrix_length]
    simp only [max_le_iff]
    constructor
    · constructor <;> nlinarith only [bspace, tableBound, extraBound, size, totalPositive]
    · constructor
      · nlinarith only [sspace, tableBound, extraBound, size, totalPositive]
      · constructor <;> nlinarith only [tableBound, extraBound, size, totalPositive]
  · simpa only [matrix_length, Nat.mul_assoc] using pc

end Controller.Extensions.MonotoneTableConstruction
