module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Extensions.LiteralRootRun

public import Mathlib.Tactic.Ring

@[expose] public section

/-! A fetched first-zero scan through the shared singleton columns of one
output. Both read cursors name the same column; the empty test block uses
the value already loaded into register 3. -/
namespace Controller.Extensions.MonotoneScan
open Controller.Cost Controller.Cost.EnumerationSteps Controller.Extensions.LiteralScan

variable {width : Nat}

theorem zero_spec (oneFits : 1 < 2 ^ width) : TestSpec (width := width) [] 0 (fun _ p _ => !p) := by
  intro program state entry c p q _ position running _ _ _ pReg _
  refine ⟨state, 0, Execution.refl state, le_rfl, by simpa only [List.length_nil, Nat.add_zero] using position,
    running, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  rw [pReg]
  cases p <;> simp [boolWord, word, Nat.mod_eq_of_lt oneFits]

def code (n nodes base entry found absent : Nat) : List (Instruction width 8) :=
  [.constant 1 (word width 0), .constant 2 (word width n),
    .constant 5 (word width (base + n * nodes)), .add 5 5 4,
    .constant 6 (word width (base + n * nodes)), .add 6 6 4] ++
    LiteralScan.code [] nodes (entry + 6) found absent

@[simp] theorem code_length (n nodes base entry found absent : Nat) :
    (code (width := width) n nodes base entry found absent).length = 19 := by
  simp [code]

set_option maxHeartbeats 1000000 in
theorem execution (program : Program width 8) (state : State width 8)
    (n nodes base entry found absent root : Nat) (bits : Nat → Bool)
    (rootBound : root < nodes) (position : state.pc = word width entry) (running : state.halted = false)
    (room : base + (n + 1) * nodes + entry + 32 < 2 ^ width)
    (rootReg : state.reg 4 = word width root)
    (cells : ∀ c, c < n → state.heap[base + (n - c) * nodes + root]? = some (boolWord width (bits c)))
    (present : SharedRootRead.BlockAt program entry (code n nodes base entry found absent)) :
    ∃ final ticks, Execution program state final ticks state.liveWords ∧ ticks ≤ 13 * n + 7 ∧
      final.halted = false ∧ final.heap = state.heap ∧ final.stack = state.stack ∧
      final.output = state.output ∧ final.reg 4 = state.reg 4 ∧
      (match firstHit (fun c => !bits c) 0 n with
        | some c => final.pc = word width found ∧ final.reg 1 = word width c
        | none => final.pc = word width absent) := by
  have expanded : (n + 1) * nodes = n * nodes + nodes := by ring
  rw [expanded] at room
  have nLe : n ≤ n * nodes := Nat.le_mul_of_pos_right _ (by omega)
  have front : ∀ i, i < 6 → program[entry + i]? =
      ([.constant 1 (word width 0), .constant 2 (word width n),
        .constant 5 (word width (base + n * nodes)), .add 5 5 4,
        .constant 6 (word width (base + n * nodes)), .add 6 6 4] : List (Instruction width 8))[i]? := by
    intro i h
    rw [present i (by simp; omega)]
    exact List.getElem?_append_left (by simpa using h)
  have tail := SharedDetectorAssembly.block_right program entry _ _ present
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd] at tail
  obtain ⟨s1, t1, pc1, v1, h1, st1, o1, r1, f1⟩ :=
    SharedEvaluationReclaim.constant_execution program entry 0 1 state position running (by omega)
      (by simpa using front 0 (by decide))
  obtain ⟨s2, t2, pc2, v2, h2, st2, o2, r2, f2⟩ :=
    SharedEvaluationReclaim.constant_execution program (entry + 1) n 2 s1 pc1 r1 (by omega)
      (by simpa using front 1 (by decide))
  obtain ⟨s3, t3, pc3, v3, h3, st3, o3, r3, f3⟩ :=
    SharedEvaluationReclaim.constant_execution program (entry + 1 + 1) (base + n * nodes) 5 s2 pc2 r2 (by omega)
      (by simpa using front 2 (by decide))
  obtain ⟨s4, t4, pc4, v4, h4, st4, o4, r4, f4⟩ :=
    add_execution program s3 (entry + 1 + 1 + 1) 5 5 4 pc3 r3 (by omega) (by simpa using front 3 (by decide))
  obtain ⟨s5, t5, pc5, v5, h5, st5, o5, r5, f5⟩ :=
    SharedEvaluationReclaim.constant_execution program (entry + 1 + 1 + 1 + 1) (base + n * nodes) 6 s4 pc4 r4 (by omega)
      (by simpa using front 4 (by decide))
  obtain ⟨s6, t6, pc6, v6, h6, st6, o6, r6, f6⟩ :=
    add_execution program s5 (entry + 1 + 1 + 1 + 1 + 1) 6 6 4 pc5 r5 (by omega) (by simpa using front 5 (by decide))
  have heap6 : s6.heap = state.heap := by rw [h6, h5, h4, h3, h2, h1]
  have stack6 : s6.stack = state.stack := by rw [st6, st5, st4, st3, st2, st1]
  have out6 : s6.output = state.output := by rw [o6, o5, o4, o3, o2, o1]
  have reg4 : s6.reg 4 = state.reg 4 := by
    rw [f6 4 (by decide), f5 4 (by decide), f4 4 (by decide), f3 4 (by decide), f2 4 (by decide), f1 4 (by decide)]
  have cReg : s6.reg 1 = word width 0 := by
    rw [f6 1 (by decide), f5 1 (by decide), f4 1 (by decide), f3 1 (by decide), f2 1 (by decide), v1]
  have kReg : s6.reg 2 = word width n := by
    rw [f6 2 (by decide), f5 2 (by decide), f4 2 (by decide), f3 2 (by decide), v2]
  have posReg : s6.reg 5 = word width (base + root + n * nodes) := by
    rw [f6 5 (by decide), f5 5 (by decide), v4, v3, f3 4 (by decide), f2 4 (by decide),
      f1 4 (by decide), rootReg, word_val _ (by omega), word_val _ (by omega)]
    congr 1; omega
  have negReg : s6.reg 6 = word width (base + root + n * nodes) := by
    rw [v6, v5, f5 4 (by decide), f4 4 (by decide), f3 4 (by decide), f2 4 (by decide),
      f1 4 (by decide), rootReg, word_val _ (by omega), word_val _ (by omega)]
    congr 1; omega
  have physical : ∀ j, j < n → s6.heap[base + root + (j + 1) * nodes]? =
      some (boolWord width (bits (0 + n - 1 - j))) := by
    intro j h
    have shift : n - (0 + n - 1 - j) = j + 1 := by omega
    have cell := cells (0 + n - 1 - j) (by omega)
    rw [shift] at cell
    simpa only [heap6, Nat.add_right_comm] using cell
  obtain ⟨final, ticks, trace, time, active, heap, stack, output, frame, result⟩ :=
    LiteralScan.execution program [] 0 (fun _ p _ => !p) (zero_spec (by omega)) nodes (base + root) (base + root)
      (entry + 6) found absent bits bits tail (by simp; omega) (by omega) n 0 s6
      (by simpa only [Nat.add_assoc, Nat.reduceAdd] using pc6) r6 (by omega) (by omega) (by omega)
      cReg kReg posReg negReg physical physical
  have live : ∀ s : State width 8, s.heap = state.heap → s.stack = state.stack → s.output = state.output →
      s.liveWords = state.liveWords := by intro s h st o; simp only [State.liveWords, h, st, o]
  have joined := t1.append (t2.append (t3.append (t4.append (t5.append (t6.append trace)))))
  rw [live s1 h1 st1 o1, live s2 (h2.trans h1) (st2.trans st1) (o2.trans o1),
    live s3 (by rw [h3, h2, h1]) (by rw [st3, st2, st1]) (by rw [o3, o2, o1]),
    live s4 (by rw [h4, h3, h2, h1]) (by rw [st4, st3, st2, st1]) (by rw [o4, o3, o2, o1]),
    live s5 (by rw [h5, h4, h3, h2, h1]) (by rw [st5, st4, st3, st2, st1]) (by rw [o5, o4, o3, o2, o1]),
    live s6 heap6 stack6 out6, Nat.max_self, Nat.max_self, Nat.max_self, Nat.max_self, Nat.max_self, Nat.max_self] at joined
  exact ⟨final, _, joined, by omega, active, heap.trans heap6, stack.trans stack6, output.trans out6,
    frame.trans reg4, result⟩

end Controller.Extensions.MonotoneScan
