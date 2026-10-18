module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.EnumerationSteps
public import Controller.Cost.SharedDetectorAssembly

@[expose] public section

/-! A fetched scan over the literal columns of one root. Channel `c` reads its
positive bit at `pos - (n-c)` strides and its negative bit at `neg - (n-c)`
strides; both cursors move by one stride per channel. A caller-supplied test
block decides each channel from the two bits and the channel index. The scan
stops at the first hit or after `n` channels. -/
namespace Controller.Extensions.LiteralScan
open Controller.Cost Controller.Cost.EnumerationSteps Controller.Cost.RawTransferLoops

variable {width : Nat}

/-- The two bits of channel `c` are in registers 3 (positive) and 7 (negative);
the test leaves zero in register 3 exactly on a hit. -/
def TestSpec (test : List (Instruction width 8)) (bound : Nat) (hit : Nat → Bool → Bool → Bool) : Prop :=
  ∀ (program : Program width 8) (state : State width 8) (entry c : Nat) (p q : Bool),
    SharedRootRead.BlockAt program entry test → state.pc = word width entry → state.halted = false →
    entry + test.length < 2 ^ width → state.reg 1 = word width c → c < 2 ^ width →
    state.reg 3 = boolWord width p → state.reg 7 = boolWord width q →
    ∃ final ticks, Execution program state final ticks state.liveWords ∧ ticks ≤ bound ∧
      final.pc = word width (entry + test.length) ∧ final.halted = false ∧
      ((final.reg 3).val = 0 ↔ hit c p q = true) ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.reg 1 = state.reg 1 ∧ final.reg 2 = state.reg 2 ∧ final.reg 4 = state.reg 4 ∧
      final.reg 5 = state.reg 5 ∧ final.reg 6 = state.reg 6

def head (missing : Nat) : List (Instruction width 8) :=
  [.branchZero 2 (word width missing), .load 3 5, .load 7 6]

def advance (stride entry found : Nat) : List (Instruction width 8) :=
  [.branchZero 3 (word width found), .constant 3 (word width (2 ^ width - stride)), .add 5 5 3, .add 6 6 3,
    .constant 3 (word width 1), .add 1 1 3, .constant 3 (word width (2 ^ width - 1)), .add 2 2 3,
    .constant 0 (word width 0), .branchZero 0 (word width entry)]

def code (test : List (Instruction width 8)) (stride entry found missing : Nat) : List (Instruction width 8) :=
  head missing ++ (test ++ advance stride entry found)

@[simp] theorem code_length (test : List (Instruction width 8)) (stride entry found missing : Nat) :
    (code test stride entry found missing).length = test.length + 13 := by
  simp only [code, head, advance, List.length_append, List.length_cons, List.length_nil]
  omega

theorem code_head (test : List (Instruction width 8)) (stride entry found missing i : Nat) (small : i < 3) :
    (code test stride entry found missing)[i]? = (head missing : List (Instruction width 8))[i]? := by
  unfold code
  rw [List.getElem?_append_left (by simp [head]; omega)]

theorem code_test (test : List (Instruction width 8)) (stride entry found missing i : Nat) (small : i < test.length) :
    (code test stride entry found missing)[3 + i]? = test[i]? := by
  unfold code
  rw [List.getElem?_append_right (by simp [head]), List.getElem?_append_left (by simp [head]; omega)]
  congr 1; simp [head]

theorem code_tail (test : List (Instruction width 8)) (stride entry found missing i : Nat) :
    (code test stride entry found missing)[3 + test.length + i]? = (advance stride entry found : List (Instruction width 8))[i]? := by
  unfold code
  rw [List.getElem?_append_right (by simp [head]; omega), List.getElem?_append_right (by simp [head]; omega)]
  congr 1; simp [head]; omega

/-- First hit at or after channel `c` among `k` channels. -/
def firstHit (hit : Nat → Bool) (c : Nat) : Nat → Option Nat
  | 0 => none
  | k + 1 => if hit c then some c else firstHit hit (c + 1) k

theorem firstHit_some (hit : Nat → Bool) : ∀ (k c d : Nat), firstHit hit c k = some d →
    c ≤ d ∧ d < c + k ∧ hit d = true ∧ ∀ e, c ≤ e → e < d → hit e = false := by
  intro k
  induction k with
  | zero => intro c d h; simp [firstHit] at h
  | succ k ih =>
    intro c d h
    unfold firstHit at h
    split at h
    next yes =>
      cases h
      exact ⟨le_rfl, by omega, yes, fun e low high => absurd high (by omega)⟩
    next no =>
      obtain ⟨low, high, value, before⟩ := ih (c + 1) d h
      refine ⟨by omega, by omega, value, fun e l h' => ?_⟩
      rcases Nat.lt_or_ge e (c + 1) with small | big
      · have : e = c := by omega
        subst this; simpa using no
      · exact before e big h'

theorem firstHit_none (hit : Nat → Bool) : ∀ (k c : Nat), firstHit hit c k = none →
    ∀ e, c ≤ e → e < c + k → hit e = false := by
  intro k
  induction k with
  | zero => intro c _ e l h; omega
  | succ k ih =>
    intro c h e l h'
    unfold firstHit at h
    split at h
    · simp at h
    next no =>
      rcases Nat.lt_or_ge e (c + 1) with small | big
      · have : e = c := by omega
        subst this; simpa using no
      · exact ih (c + 1) h e big (by omega)

theorem sub_word (value stride : Nat) (fits : value < 2 ^ width) (small : stride ≤ value)
    (positive : 0 < stride) :
    word width ((word width value).val + (word width (2 ^ width - stride)).val) = word width (value - stride) := by
  have strideFits : stride ≤ 2 ^ width := by omega
  have v : (word width value).val = value := Nat.mod_eq_of_lt fits
  have s : (word width (2 ^ width - stride)).val = 2 ^ width - stride := Nat.mod_eq_of_lt (by omega)
  rw [v, s]
  apply Fin.ext
  simp only [word]
  have arithmetic : value + (2 ^ width - stride) = (value - stride) + 2 ^ width := by omega
  rw [arithmetic, Nat.add_mod_right]

theorem word_val (value : Nat) (fits : value < 2 ^ width) : (word width value).val = value :=
  Nat.mod_eq_of_lt fits

set_option maxHeartbeats 4000000 in
/-- The scan. `k` channels remain, starting at channel `c`. -/
theorem execution (program : Program width 8) (test : List (Instruction width 8)) (bound : Nat)
    (hit : Nat → Bool → Bool → Bool) (spec : TestSpec test bound hit)
    (stride posEnd negEnd entry found missing : Nat) (pos neg : Nat → Bool)
    (present : SharedRootRead.BlockAt program entry (code test stride entry found missing))
    (codeRoom : entry + test.length + 13 < 2 ^ width) (positive : 0 < stride) :
    ∀ (k c : Nat) (state : State width 8),
      state.pc = word width entry → state.halted = false →
      c + k < 2 ^ width →
      posEnd + k * stride < 2 ^ width → negEnd + k * stride < 2 ^ width →
      state.reg 1 = word width c → state.reg 2 = word width k →
      state.reg 5 = word width (posEnd + k * stride) → state.reg 6 = word width (negEnd + k * stride) →
      (∀ j, j < k → state.heap[posEnd + (j + 1) * stride]? = some (boolWord width (pos (c + k - 1 - j)))) →
      (∀ j, j < k → state.heap[negEnd + (j + 1) * stride]? = some (boolWord width (neg (c + k - 1 - j)))) →
      ∃ final ticks, Execution program state final ticks state.liveWords ∧
        ticks ≤ k * (bound + 13) + 1 ∧ final.halted = false ∧
        final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
        final.reg 4 = state.reg 4 ∧
        (match firstHit (fun d => hit d (pos d) (neg d)) c k with
          | some d => final.pc = word width found ∧ final.reg 1 = word width d
          | none => final.pc = word width missing) := by
  have fetch : ∀ offset (valid : offset < test.length + 13),
      program[entry + offset]? = (code test stride entry found missing)[offset]? :=
    fun offset valid => present offset (by simpa using valid)
  have tail : ∀ i (valid : i < 10), program[entry + 3 + test.length + i]? =
      (advance stride entry found : List (Instruction width 8))[i]? := by
    intro i valid
    have := fetch (3 + test.length + i) (by omega)
    rw [show entry + 3 + test.length + i = entry + (3 + test.length + i) by omega, this, code_tail]
  have front : ∀ i (valid : i < 3), program[entry + i]? = (head missing : List (Instruction width 8))[i]? := by
    intro i valid
    rw [fetch i (by omega), code_head _ _ _ _ _ _ valid]
  intro k
  induction k with
  | zero =>
    intro c state position running _ _ _ _ countReg _ _ _ _
    obtain ⟨final, trace, pc, heap, stack, output, run, frame⟩ :=
      branch_taken program state entry missing 2 position running (by omega)
        (by rw [countReg]; simp [word]) (by simpa [head] using front 0 (by omega))
    refine ⟨final, 1, trace, by omega, run, heap, stack, output, frame 4, ?_⟩
    simpa [firstHit] using pc
  | succ k ih =>
    intro c state position running cFits posFits negFits cReg countReg posReg negReg posCells negCells
    have kFits : k + 1 < 2 ^ width := by omega
    -- Count test.
    obtain ⟨s1, t1, pc1, heap1, stack1, out1, run1, frame1⟩ :=
      branch_skipped program state entry missing 2 position running (by omega)
        (by rw [countReg, word_val _ kFits]; omega) (by simpa [head] using front 0 (by omega))
    -- Loads.
    have posInside : (s1.reg 5).val < s1.heap.size := by
      rw [frame1, posReg, heap1, word_val _ posFits]
      have := posCells k (by omega)
      have := (Array.getElem?_eq_some_iff.mp this).1
      simpa [Nat.add_mul] using this
    obtain ⟨s2, t2, pc2, val2, heap2, stack2, out2, run2, frame2⟩ :=
      load_execution program s1 (entry + 1) 3 5 pc1 run1 (by omega) posInside
        (by simpa [head] using front 1 (by omega))
    have negInside : (s2.reg 6).val < s2.heap.size := by
      rw [frame2 6 (by decide), frame1, negReg, heap2, heap1, word_val _ negFits]
      have := negCells k (by omega)
      have := (Array.getElem?_eq_some_iff.mp this).1
      simpa [Nat.add_mul] using this
    obtain ⟨s3, t3, pc3, val3, heap3, stack3, out3, run3, frame3⟩ :=
      load_execution program s2 (entry + 1 + 1) 7 6 pc2 run2 (by omega) negInside
        (by simpa [head] using front 2 (by omega))
    have posValue : s3.reg 3 = boolWord width (pos c) := by
      rw [frame3 3 (by decide), val2]
      have cell := posCells k (by omega)
      have index : (s1.reg 5).val = posEnd + (k + 1) * stride := by
        rw [frame1, posReg, word_val _ posFits]
      simp only [index, heap1]
      rw [show c + (k + 1) - 1 - k = c by omega] at cell
      rw [Array.getElem?_eq_getElem (by simpa [index, heap1] using posInside)] at cell
      exact Option.some.inj cell
    have negValue : s3.reg 7 = boolWord width (neg c) := by
      rw [val3]
      have cell := negCells k (by omega)
      have index : (s2.reg 6).val = negEnd + (k + 1) * stride := by
        rw [frame2 6 (by decide), frame1, negReg, word_val _ negFits]
      simp only [index, heap2, heap1]
      rw [show c + (k + 1) - 1 - k = c by omega] at cell
      rw [Array.getElem?_eq_getElem (by simpa [index, heap2, heap1] using negInside)] at cell
      exact Option.some.inj cell
    have cValue : s3.reg 1 = word width c := by
      rw [frame3 1 (by decide), frame2 1 (by decide), frame1, cReg]
    -- Test block.
    have testAt : SharedRootRead.BlockAt program (entry + 3) test := by
      intro offset valid
      have := fetch (3 + offset) (by omega)
      rw [show entry + 3 + offset = entry + (3 + offset) by omega, this, code_test _ _ _ _ _ _ valid]
    obtain ⟨s4, t4, trace4, time4, pc4, run4, val4, heap4, stack4, out4, f1, f2, f4, f5, f6⟩ :=
      spec program s3 (entry + 3) c (pos c) (neg c) testAt (by simpa using pc3) run3 (by omega) cValue
        (by omega) posValue negValue
    have live1 : s1.liveWords = state.liveWords := by simp only [State.liveWords, heap1, stack1, out1]
    have live2 : s2.liveWords = state.liveWords := by simp only [State.liveWords, heap2, stack2, out2] at live1 ⊢; exact live1
    have live3 : s3.liveWords = state.liveWords := by simp only [State.liveWords, heap3, stack3, out3] at live2 ⊢; exact live2
    by_cases decided : hit c (pos c) (neg c) = true
    · -- Hit: branch to `found`.
      obtain ⟨s5, t5, pc5, heap5, stack5, out5, run5, frame5⟩ :=
        branch_taken program s4 (entry + 3 + test.length) found 3 pc4 run4 (by omega)
          (val4.mpr decided) (by simpa [advance] using tail 0 (by omega))
      have live4 : s4.liveWords = state.liveWords := by
        simp only [State.liveWords, heap4, stack4, out4] at live3 ⊢; exact live3
      have joined := t1.append (t2.append (t3.append (trace4.append t5)))
      rw [live1, live2, live3, live4] at joined
      simp only [Nat.max_self] at joined
      refine ⟨s5, _, joined, ?_, run5, ?_, ?_, ?_, ?_, ?_⟩
      · have := Nat.le_mul_of_pos_left (bound + 13) (show 0 < k + 1 by omega)
        omega
      · rw [heap5, heap4, heap3, heap2, heap1]
      · rw [stack5, stack4, stack3, stack2, stack1]
      · rw [out5, out4, out3, out2, out1]
      · rw [frame5, f4, frame3 4 (by decide), frame2 4 (by decide), frame1]
      · simp only [firstHit, decided, ite_true]
        exact ⟨pc5, by rw [frame5, f1, cValue]⟩
    · have miss : hit c (pos c) (neg c) = false := by simpa using decided
      obtain ⟨s5, t5, pc5, heap5, stack5, out5, run5, frame5⟩ :=
        branch_skipped program s4 (entry + 3 + test.length) found 3 pc4 run4 (by omega)
          (fun h => by have := val4.mp h; rw [miss] at this; exact absurd this (by decide))
          (by simpa [advance] using tail 0 (by omega))
      obtain ⟨s6, t6, pc6, val6, heap6, stack6, out6, run6, frame6⟩ :=
        SharedEvaluationReclaim.constant_execution program (entry + 3 + test.length + 1) (2 ^ width - stride) 3 s5
          pc5 run5 (by omega) (by simpa [advance] using tail 1 (by omega))
      obtain ⟨s7, t7, pc7, val7, heap7, stack7, out7, run7, frame7⟩ :=
        add_execution program s6 (entry + 3 + test.length + 1 + 1) 5 5 3 pc6 run6 (by omega)
          (by simpa [advance, Nat.add_assoc] using tail 2 (by omega))
      obtain ⟨s8, t8, pc8, val8, heap8, stack8, out8, run8, frame8⟩ :=
        add_execution program s7 (entry + 3 + test.length + 1 + 1 + 1) 6 6 3 pc7 run7 (by omega)
          (by simpa [advance, Nat.add_assoc] using tail 3 (by omega))
      obtain ⟨s9, t9, pc9, val9, heap9, stack9, out9, run9, frame9⟩ :=
        SharedEvaluationReclaim.constant_execution program (entry + 3 + test.length + 1 + 1 + 1 + 1) 1 3 s8
          pc8 run8 (by omega) (by simpa [advance, Nat.add_assoc] using tail 4 (by omega))
      obtain ⟨s10, t10, pc10, val10, heap10, stack10, out10, run10, frame10⟩ :=
        add_execution program s9 (entry + 3 + test.length + 1 + 1 + 1 + 1 + 1) 1 1 3 pc9 run9 (by omega)
          (by simpa [advance, Nat.add_assoc] using tail 5 (by omega))
      obtain ⟨s11, t11, pc11, val11, heap11, stack11, out11, run11, frame11⟩ :=
        SharedEvaluationReclaim.constant_execution program (entry + 3 + test.length + 1 + 1 + 1 + 1 + 1 + 1)
          (2 ^ width - 1) 3 s10 pc10 run10 (by omega) (by simpa [advance, Nat.add_assoc] using tail 6 (by omega))
      obtain ⟨s12, t12, pc12, val12, heap12, stack12, out12, run12, frame12⟩ :=
        add_execution program s11 (entry + 3 + test.length + 1 + 1 + 1 + 1 + 1 + 1 + 1) 2 2 3 pc11 run11 (by omega)
          (by simpa [advance, Nat.add_assoc] using tail 7 (by omega))
      obtain ⟨s13, t13, pc13, heap13, stack13, out13, run13, frame13⟩ :=
        jump_execution program s12 (entry + 3 + test.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) entry pc12 run12
          (by omega) (by simpa [advance, Nat.add_assoc] using tail 8 (by omega))
          (by simpa [advance, Nat.add_assoc] using tail 9 (by omega))
      -- Register values for the next iteration.
      have r5 : s4.reg 5 = word width (posEnd + (k + 1) * stride) := by
        rw [f5, frame3 5 (by decide), frame2 5 (by decide), frame1, posReg]
      have r6 : s4.reg 6 = word width (negEnd + (k + 1) * stride) := by
        rw [f6, frame3 6 (by decide), frame2 6 (by decide), frame1, negReg]
      have r2 : s4.reg 2 = word width (k + 1) := by
        rw [f2, frame3 2 (by decide), frame2 2 (by decide), frame1, countReg]
      have r1 : s4.reg 1 = word width c := by rw [f1, cValue]
      have strideValue : s6.reg 3 = word width (2 ^ width - stride) := val6
      have nextPos : s13.reg 1 = word width (c + 1) ∧ s13.reg 2 = word width k ∧
          s13.reg 5 = word width (posEnd + k * stride) ∧ s13.reg 6 = word width (negEnd + k * stride) := by
        have e5 : s7.reg 5 = word width (posEnd + k * stride) := by
          rw [val7, frame6 5 (by decide), frame5, r5, strideValue,
            sub_word _ _ posFits (by rw [Nat.add_mul]; omega) positive]
          congr 1; rw [Nat.add_mul]; omega
        have e6 : s8.reg 6 = word width (negEnd + k * stride) := by
          rw [val8, frame7 6 (by decide), frame6 6 (by decide), frame5, r6, frame7 3 (by decide), strideValue,
            sub_word _ _ negFits (by rw [Nat.add_mul]; omega) positive]
          congr 1; rw [Nat.add_mul]; omega
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [frame13 1 (by decide), frame12 1 (by decide), frame11 1 (by decide), val10,
            frame9 1 (by decide), frame8 1 (by decide), frame7 1 (by decide), frame6 1 (by decide), frame5, r1, val9]
          apply Fin.ext
          simp only [word, Nat.mod_eq_of_lt (show c < 2 ^ width by omega),
            Nat.mod_eq_of_lt (show 1 < 2 ^ width by omega)]
        · rw [frame13 2 (by decide), val12, frame11 2 (by decide), frame10 2 (by decide), frame9 2 (by decide),
            frame8 2 (by decide), frame7 2 (by decide), frame6 2 (by decide), frame5, r2, val11]
          have := decrement_word width k
          rw [← this]
          congr 1
          rw [word_val _ kFits, word_val _ (by omega)]
        · rw [frame13 5 (by decide), frame12 5 (by decide), frame11 5 (by decide), frame10 5 (by decide),
            frame9 5 (by decide), frame8 5 (by decide), e5]
        · rw [frame13 6 (by decide), frame12 6 (by decide), frame11 6 (by decide), frame10 6 (by decide),
            frame9 6 (by decide), e6]
      have sameHeap : s13.heap = state.heap := by
        rw [heap13, heap12, heap11, heap10, heap9, heap8, heap7, heap6, heap5, heap4, heap3, heap2, heap1]
      have succStride : (k + 1) * stride = k * stride + stride := Nat.succ_mul k stride
      obtain ⟨final, ticks, trace, time, run, heapF, stackF, outF, reg4F, result⟩ :=
        ih (c + 1) s13 pc13 run13 (by omega) (by omega) (by omega) nextPos.1 nextPos.2.1 nextPos.2.2.1
          nextPos.2.2.2
          (by intro j small; rw [sameHeap, show c + 1 + k - 1 - j = c + (k + 1) - 1 - j by omega]
              exact posCells j (by omega))
          (by intro j small; rw [sameHeap, show c + 1 + k - 1 - j = c + (k + 1) - 1 - j by omega]
              exact negCells j (by omega))
      have live13 : s13.liveWords = state.liveWords := by
        simp only [State.liveWords, sameHeap, stack13, stack12, stack11, stack10, stack9, stack8, stack7, stack6,
          stack5, stack4, stack3, stack2, stack1, out13, out12, out11, out10, out9, out8, out7, out6, out5, out4,
          out3, out2, out1]
      have liveAll : ∀ s : State width 8, s.heap = state.heap → s.stack = state.stack → s.output = state.output →
          s.liveWords = state.liveWords := by
        intro s h st o; simp only [State.liveWords, h, st, o]
      have l4 := liveAll s4 (by rw [heap4, heap3, heap2, heap1]) (by rw [stack4, stack3, stack2, stack1])
        (by rw [out4, out3, out2, out1])
      have l5 := liveAll s5 (by rw [heap5, heap4, heap3, heap2, heap1]) (by rw [stack5, stack4, stack3, stack2, stack1])
        (by rw [out5, out4, out3, out2, out1])
      have l6 := liveAll s6 (by rw [heap6, heap5, heap4, heap3, heap2, heap1])
        (by rw [stack6, stack5, stack4, stack3, stack2, stack1]) (by rw [out6, out5, out4, out3, out2, out1])
      have l7 := liveAll s7 (by rw [heap7, heap6, heap5, heap4, heap3, heap2, heap1])
        (by rw [stack7, stack6, stack5, stack4, stack3, stack2, stack1]) (by rw [out7, out6, out5, out4, out3, out2, out1])
      have l8 := liveAll s8 (by rw [heap8, heap7, heap6, heap5, heap4, heap3, heap2, heap1])
        (by rw [stack8, stack7, stack6, stack5, stack4, stack3, stack2, stack1])
        (by rw [out8, out7, out6, out5, out4, out3, out2, out1])
      have l9 := liveAll s9 (by rw [heap9, heap8, heap7, heap6, heap5, heap4, heap3, heap2, heap1])
        (by rw [stack9, stack8, stack7, stack6, stack5, stack4, stack3, stack2, stack1])
        (by rw [out9, out8, out7, out6, out5, out4, out3, out2, out1])
      have l10 := liveAll s10 (by rw [heap10, heap9, heap8, heap7, heap6, heap5, heap4, heap3, heap2, heap1])
        (by rw [stack10, stack9, stack8, stack7, stack6, stack5, stack4, stack3, stack2, stack1])
        (by rw [out10, out9, out8, out7, out6, out5, out4, out3, out2, out1])
      have l11 := liveAll s11 (by rw [heap11, heap10, heap9, heap8, heap7, heap6, heap5, heap4, heap3, heap2, heap1])
        (by rw [stack11, stack10, stack9, stack8, stack7, stack6, stack5, stack4, stack3, stack2, stack1])
        (by rw [out11, out10, out9, out8, out7, out6, out5, out4, out3, out2, out1])
      have l12 := liveAll s12 (by rw [heap12, heap11, heap10, heap9, heap8, heap7, heap6, heap5, heap4, heap3, heap2, heap1])
        (by rw [stack12, stack11, stack10, stack9, stack8, stack7, stack6, stack5, stack4, stack3, stack2, stack1])
        (by rw [out12, out11, out10, out9, out8, out7, out6, out5, out4, out3, out2, out1])
      have joined := t1.append (t2.append (t3.append (trace4.append (t5.append (t6.append (t7.append (t8.append
        (t9.append (t10.append (t11.append (t12.append (t13.append trace))))))))))))
      rw [live1, live2, live3, l4, l5, l6, l7, l8, l9, l10, l11, l12, live13] at joined
      simp only [Nat.max_self] at joined
      refine ⟨final, _, joined, ?_, run, heapF.trans sameHeap, ?_, ?_, ?_, ?_⟩
      · rw [Nat.succ_mul]; omega
      · rw [stackF, stack13, stack12, stack11, stack10, stack9, stack8, stack7, stack6, stack5, stack4, stack3,
          stack2, stack1]
      · rw [outF, out13, out12, out11, out10, out9, out8, out7, out6, out5, out4, out3, out2, out1]
      · rw [reg4F, frame13 4 (by decide), frame12 4 (by decide), frame11 4 (by decide), frame10 4 (by decide),
          frame9 4 (by decide), frame8 4 (by decide), frame7 4 (by decide), frame6 4 (by decide), frame5, f4,
          frame3 4 (by decide), frame2 4 (by decide), frame1]
      · simp only [firstHit, miss, Bool.false_eq_true, ite_false]
        exact result

end Controller.Extensions.LiteralScan
