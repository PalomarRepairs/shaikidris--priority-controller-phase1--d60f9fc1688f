module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Extensions.LiteralDecision
public import Controller.Extensions.LiteralTests
public import Controller.Extensions.LiteralSourceConstruction

@[expose] public section

/-! Positioned scans over the physical literal matrix of one root. The
matrix starts at heap address `base`; register 4 holds the root's node id
throughout. -/
namespace Controller.Extensions.LiteralRoot
open Controller.Decoder Controller.Cost Controller.Cost.EnumerationSteps
open Controller.Extensions.LiteralScan Controller.Extensions.LiteralDecision
open Controller.Extensions.LiteralSourceConstruction

variable {n width : Nat}

/-- The constructed matrix is stored at `base`. -/
def MatrixAt (heap : Array (Word width)) (base : Nat) (graph : DAG n) : Prop :=
  ∀ i, i < (matrix graph width).length → heap[base + i]? = (matrix graph width)[i]?

theorem pos_cell (graph : DAG n) (noOr : GateBasis.NoDisjunction graph) (heap : Array (Word width)) (base : Nat)
    (stored : MatrixAt heap base graph) (x : Channel n) (root : Fin graph.nodeCount) :
    heap[base + n * graph.nodeCount + (n - x.val) * graph.nodeCount + root.val]? =
      some (boolWord width (posBit (LiteralMachine.summary graph root) x.val)) := by
  have cell := sign_cell (width := width) graph noOr x root false
  have address : base + n * graph.nodeCount + (n - x.val) * graph.nodeCount + root.val =
      base + signAddress graph x root false := by
    have split : n - x.val = (n - 1 - x.val) + 1 := by have := x.isLt; omega
    rw [split, Nat.add_mul, Nat.one_mul]
    simp only [signAddress, Bool.false_eq_true, ite_false]
    omega
  rw [address, stored _ (signAddress_bound graph x root false), cell, posBit_channel]
  rfl

theorem neg_cell (graph : DAG n) (noOr : GateBasis.NoDisjunction graph) (heap : Array (Word width)) (base : Nat)
    (stored : MatrixAt heap base graph) (x : Channel n) (root : Fin graph.nodeCount) :
    heap[base + (n - x.val) * graph.nodeCount + root.val]? =
      some (boolWord width (negBit (LiteralMachine.summary graph root) x.val)) := by
  have cell := sign_cell (width := width) graph noOr x root true
  have address : base + (n - x.val) * graph.nodeCount + root.val = base + signAddress graph x root true := by
    have split : n - x.val = (n - 1 - x.val) + 1 := by have := x.isLt; omega
    rw [split, Nat.add_mul, Nat.one_mul]
    simp only [signAddress, ite_true]
    omega
  rw [address, stored _ (signAddress_bound graph x root true), cell, negBit_channel]
  rfl

theorem zero_cell_at (graph : DAG n) (noOr : GateBasis.NoDisjunction graph) (heap : Array (Word width)) (base : Nat)
    (stored : MatrixAt heap base graph) (root : Fin graph.nodeCount) :
    heap[base + root.val]? = some (boolWord width (LiteralMachine.summary graph root).zero) := by
  have inside : root.val < (matrix graph width).length := by
    rw [matrix_length]; have := root.isLt; nlinarith
  rw [stored _ inside, zero_cell graph noOr]

/-- Set the cursors for channels `[first, first + count)` and run a scan. -/
def callCode (test : List (Instruction width 8)) (n nodes base first count entry found missing : Nat) :
    List (Instruction width 8) :=
  [.constant 1 (word width first), .constant 2 (word width count),
    .constant 5 (word width (base + n * nodes + (n - first) * nodes)), .add 5 5 4,
    .constant 6 (word width (base + (n - first) * nodes)), .add 6 6 4] ++
  LiteralScan.code test nodes (entry + 6) found missing

@[simp] theorem callCode_length (test : List (Instruction width 8)) (n nodes base first count entry found missing : Nat) :
    (callCode test n nodes base first count entry found missing).length = test.length + 19 := by
  simp only [callCode, List.length_append, List.length_cons, List.length_nil, LiteralScan.code_length]
  omega

set_option maxHeartbeats 2000000 in
theorem call_execution (graph : DAG n) (noOr : GateBasis.NoDisjunction graph) (program : Program width 8)
    (test : List (Instruction width 8)) (bound : Nat) (hit : Nat → Bool → Bool → Bool) (spec : TestSpec test bound hit)
    (base first count entry found missing : Nat) (root : Fin graph.nodeCount) (state : State width 8)
    (position : state.pc = word width entry) (running : state.halted = false)
    (range : first + count ≤ n)
    (room : base + (2 * n + 1) * graph.nodeCount + entry + test.length + 19 < 2 ^ width)
    (rootReg : state.reg 4 = word width root.val)
    (stored : MatrixAt state.heap base graph)
    (present : SharedRootRead.BlockAt program entry (callCode test n graph.nodeCount base first count entry found missing)) :
    ∃ final ticks, Execution program state final ticks state.liveWords ∧
      ticks ≤ count * (bound + 13) + 7 ∧ final.halted = false ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.reg 4 = state.reg 4 ∧
      (match firstHit (fun d => hit d (posBit (LiteralMachine.summary graph root) d)
          (negBit (LiteralMachine.summary graph root) d)) first count with
        | some d => final.pc = word width found ∧ final.reg 1 = word width d
        | none => final.pc = word width missing) := by
  have rootBound := root.isLt
  have big : (2 * n + 1) * graph.nodeCount = 2 * n * graph.nodeCount + graph.nodeCount := by rw [Nat.add_mul, Nat.one_mul]
  have nN : 2 * n * graph.nodeCount = n * graph.nodeCount + n * graph.nodeCount := by rw [Nat.two_mul, Nat.add_mul]
  have firstLe : (n - first) * graph.nodeCount ≤ n * graph.nodeCount := Nat.mul_le_mul_right _ (by omega)
  have fetch : ∀ i (small : i < 6), program[entry + i]? =
      ([.constant 1 (word width first), .constant 2 (word width count),
        .constant 5 (word width (base + n * graph.nodeCount + (n - first) * graph.nodeCount)), .add 5 5 4,
        .constant 6 (word width (base + (n - first) * graph.nodeCount)), .add 6 6 4] : List (Instruction width 8))[i]? := by
    intro i small
    rw [present i (by simp; omega)]
    simp only [callCode]
    rw [List.getElem?_append_left (by simpa using small)]
  obtain ⟨s1, t1, pc1, v1, h1, st1, o1, r1, f1⟩ :=
    SharedEvaluationReclaim.constant_execution program entry first 1 state position running (by omega)
      (by simpa using fetch 0 (by decide))
  obtain ⟨s2, t2, pc2, v2, h2, st2, o2, r2, f2⟩ :=
    SharedEvaluationReclaim.constant_execution program (entry + 1) count 2 s1 pc1 r1 (by omega)
      (by simpa using fetch 1 (by decide))
  obtain ⟨s3, t3, pc3, v3, h3, st3, o3, r3, f3⟩ :=
    SharedEvaluationReclaim.constant_execution program (entry + 1 + 1) (base + n * graph.nodeCount + (n - first) * graph.nodeCount) 5 s2 pc2 r2
      (by omega) (by simpa using fetch 2 (by decide))
  obtain ⟨s4, t4, pc4, v4, h4, st4, o4, r4, f4⟩ :=
    add_execution program s3 (entry + 1 + 1 + 1) 5 5 4 pc3 r3 (by omega) (by simpa using fetch 3 (by decide))
  obtain ⟨s5, t5, pc5, v5, h5, st5, o5, r5, f5⟩ :=
    SharedEvaluationReclaim.constant_execution program (entry + 1 + 1 + 1 + 1) (base + (n - first) * graph.nodeCount) 6 s4 pc4 r4
      (by omega) (by simpa using fetch 4 (by decide))
  obtain ⟨s6, t6, pc6, v6, h6, st6, o6, r6, f6⟩ :=
    add_execution program s5 (entry + 1 + 1 + 1 + 1 + 1) 6 6 4 pc5 r5 (by omega) (by simpa using fetch 5 (by decide))
  have heap6 : s6.heap = state.heap := by rw [h6, h5, h4, h3, h2, h1]
  have reg4 : s6.reg 4 = state.reg 4 := by
    rw [f6 4 (by decide), f5 4 (by decide), f4 4 (by decide), f3 4 (by decide), f2 4 (by decide), f1 4 (by decide)]
  have rootVal : (state.reg 4).val = root.val := by rw [rootReg]; exact word_val _ (by omega)
  have posStart : s6.reg 5 = word width ((base + n * graph.nodeCount + (n - first - count) * graph.nodeCount + root.val) + count * graph.nodeCount) := by
    rw [f6 5 (by decide), f5 5 (by decide), v4, v3, f3 4 (by decide), f2 4 (by decide), f1 4 (by decide), rootVal,
      word_val _ (by omega)]
    congr 1
    have : (n - first) * graph.nodeCount = (n - first - count) * graph.nodeCount + count * graph.nodeCount := by
      rw [← Nat.add_mul]; congr 1; omega
    omega
  have negStart : s6.reg 6 = word width ((base + (n - first - count) * graph.nodeCount + root.val) + count * graph.nodeCount) := by
    rw [v6, v5, f5 4 (by decide), f4 4 (by decide), f3 4 (by decide), f2 4 (by decide), f1 4 (by decide), rootVal,
      word_val _ (by omega)]
    congr 1
    have : (n - first) * graph.nodeCount = (n - first - count) * graph.nodeCount + count * graph.nodeCount := by
      rw [← Nat.add_mul]; congr 1; omega
    omega
  have cReg : s6.reg 1 = word width first := by
    rw [f6 1 (by decide), f5 1 (by decide), f4 1 (by decide), f3 1 (by decide), f2 1 (by decide), v1]
  have kReg : s6.reg 2 = word width count := by
    rw [f6 2 (by decide), f5 2 (by decide), f4 2 (by decide), f3 2 (by decide), v2]
  have scanAt : SharedRootRead.BlockAt program (entry + 6) (LiteralScan.code test graph.nodeCount (entry + 6) found missing) := by
    intro offset small
    have := present (6 + offset) (by simp at small ⊢; omega)
    rw [show entry + 6 + offset = entry + (6 + offset) by omega, this]
    simp only [callCode]
    rw [List.getElem?_append_right (by simp)]
    simp
  have nLe : n ≤ n * graph.nodeCount := Nat.le_mul_of_pos_right _ (by omega)
  have shift : ∀ j, j < count → (n - first - count) * graph.nodeCount + (j + 1) * graph.nodeCount = (n - (first + count - 1 - j)) * graph.nodeCount := by
    intro j small
    rw [← Nat.add_mul]; congr 1; omega
  obtain ⟨final, ticks, trace, time, run, heapF, stackF, outF, reg4F, result⟩ :=
    LiteralScan.execution program test bound hit spec graph.nodeCount (base + n * graph.nodeCount + (n - first - count) * graph.nodeCount + root.val)
      (base + (n - first - count) * graph.nodeCount + root.val) (entry + 6) found missing
      (posBit (LiteralMachine.summary graph root)) (negBit (LiteralMachine.summary graph root)) scanAt
      (by omega) (by omega) count first s6 (by simpa using pc6) r6 (by omega)
      (by have := Nat.mul_le_mul_right graph.nodeCount (show n - first - count + count ≤ n by omega); rw [Nat.add_mul] at this; omega)
      (by have := Nat.mul_le_mul_right graph.nodeCount (show n - first - count + count ≤ n by omega); rw [Nat.add_mul] at this; omega)
      cReg kReg posStart negStart
      (by
        intro j small
        rw [heap6, show base + n * graph.nodeCount + (n - first - count) * graph.nodeCount + root.val + (j + 1) * graph.nodeCount =
          base + n * graph.nodeCount + (n - (first + count - 1 - j)) * graph.nodeCount + root.val by have := shift j small; omega]
        exact pos_cell graph noOr state.heap base stored ⟨first + count - 1 - j, by omega⟩ root)
      (by
        intro j small
        rw [heap6, show base + (n - first - count) * graph.nodeCount + root.val + (j + 1) * graph.nodeCount =
          base + (n - (first + count - 1 - j)) * graph.nodeCount + root.val by have := shift j small; omega]
        exact neg_cell graph noOr state.heap base stored ⟨first + count - 1 - j, by omega⟩ root)
  have live : ∀ s : State width 8, s.heap = state.heap → s.stack = state.stack → s.output = state.output →
      s.liveWords = state.liveWords := by
    intro s h st o; simp only [State.liveWords, h, st, o]
  have joined := t1.append (t2.append (t3.append (t4.append (t5.append (t6.append trace)))))
  rw [live s1 h1 st1 o1, live s2 (h2.trans h1) (st2.trans st1) (o2.trans o1),
    live s3 (by rw [h3, h2, h1]) (by rw [st3, st2, st1]) (by rw [o3, o2, o1]),
    live s4 (by rw [h4, h3, h2, h1]) (by rw [st4, st3, st2, st1]) (by rw [o4, o3, o2, o1]),
    live s5 (by rw [h5, h4, h3, h2, h1]) (by rw [st5, st4, st3, st2, st1]) (by rw [o5, o4, o3, o2, o1]),
    live s6 heap6 (by rw [st6, st5, st4, st3, st2, st1]) (by rw [o6, o5, o4, o3, o2, o1])] at joined
  simp only [Nat.max_self] at joined
  refine ⟨final, _, joined, by omega, run, heapF.trans heap6, ?_, ?_, reg4F.trans reg4, result⟩
  · rw [stackF, st6, st5, st4, st3, st2, st1]
  · rw [outF, o6, o5, o4, o3, o2, o1]

end Controller.Extensions.LiteralRoot
