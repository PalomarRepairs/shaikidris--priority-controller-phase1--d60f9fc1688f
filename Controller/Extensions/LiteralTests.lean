module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Extensions.LiteralScan

@[expose] public section

/-! Branch-free channel tests for the literal scan. Register 3 holds the
positive bit and register 7 the negative bit; each test leaves zero in
register 3 exactly on a hit and changes only registers 0 and 3. -/
namespace Controller.Extensions.LiteralTests
open Controller.Cost Controller.Cost.EnumerationSteps Controller.Extensions.LiteralScan

variable {width : Nat}

def positiveTest : List (Instruction width 8) := [.constant 0 (word width 1), .xor 3 3 0]
def negativeTest : List (Instruction width 8) := [.constant 0 (word width 1), .xor 3 7 0]
def freeTest : List (Instruction width 8) := [.constant 0 (word width 0), .add 3 7 0]
def conflictTest : List (Instruction width 8) := [.add 3 3 7, .constant 0 (word width 2), .xor 3 3 0]

theorem bool_val (room : 4 < 2 ^ width) (p : Bool) : (boolWord width p).val = if p then 1 else 0 := by
  cases p <;> simp [boolWord, word, Nat.mod_eq_of_lt (show 1 < 2 ^ width by omega)]

theorem small_val (room : 4 < 2 ^ width) (v : Nat) (small : v ≤ 4) : (word width v).val = v :=
  Nat.mod_eq_of_lt (by omega)

/-- Two straight-line instructions: a constant into register 0, then a binary
operation writing register 3. -/
theorem pair_execution (program : Program width 8) (state : State width 8) (entry v : Nat)
    (second : Instruction width 8) (result : Word width)
    (position : state.pc = word width entry) (running : state.halted = false) (room : entry + 2 < 2 ^ width)
    (first : program[entry]? = some (.constant 0 (word width v)))
    (present : program[entry + 1]? = some second)
    (computes : ∀ s : State width 8, s.reg 0 = word width v → (∀ i : Fin 8, i ≠ 0 → s.reg i = state.reg i) →
      s.halted = false → s.pc = word width (entry + 1) → program[entry + 1]? = some second →
      ∃ final, Execution program s final 1 s.liveWords ∧ final.pc = word width (entry + 2) ∧
        final.reg 3 = result ∧ final.heap = s.heap ∧ final.stack = s.stack ∧ final.output = s.output ∧
        final.halted = false ∧ (∀ i : Fin 8, i ≠ 3 → final.reg i = s.reg i)) :
    ∃ final ticks, Execution program state final ticks state.liveWords ∧ ticks ≤ 2 ∧
      final.pc = word width (entry + 2) ∧ final.halted = false ∧ final.reg 3 = result ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      (∀ i : Fin 8, i ≠ 0 → i ≠ 3 → final.reg i = state.reg i) := by
  obtain ⟨s1, t1, pc1, val1, heap1, stack1, out1, run1, frame1⟩ :=
    SharedEvaluationReclaim.constant_execution program entry v 0 state position running (by omega) first
  obtain ⟨s2, t2, pc2, val2, heap2, stack2, out2, run2, frame2⟩ := computes s1 val1 frame1 run1 pc1 present
  have live : s1.liveWords = state.liveWords := by simp only [State.liveWords, heap1, stack1, out1]
  have joined := t1.append t2
  rw [live, Nat.max_self] at joined
  refine ⟨s2, 2, joined, le_rfl, pc2, run2, val2, heap2.trans heap1, stack2.trans stack1, out2.trans out1, ?_⟩
  intro i n0 n3
  rw [frame2 i n3, frame1 i n0]

theorem fetch2 (program : Program width 8) (entry : Nat) (block : List (Instruction width 8))
    (present : SharedRootRead.BlockAt program entry block) (i : Nat) (small : i < block.length) :
    program[entry + i]? = block[i]? := present i small

theorem positive_spec (room : 4 < 2 ^ width) :
    TestSpec (positiveTest (width := width)) 2 (fun _ p _ => p) := by
  intro program state entry c p q present position running fits cReg _ pReg _
  obtain ⟨final, ticks, trace, time, pc, run, val, heap, stack, out, frame⟩ :=
    pair_execution program state entry 1 (.xor 3 3 0) (word width (if p then 0 else 1)) position running
      (by simpa [positiveTest] using fits) (by simpa [positiveTest] using fetch2 program entry _ present 0 (by simp [positiveTest, negativeTest, freeTest, conflictTest]))
      (by simpa [positiveTest] using fetch2 program entry _ present 1 (by simp [positiveTest, negativeTest, freeTest, conflictTest]))
      (by
        intro s zero same run spc fetched
        obtain ⟨f, tr, fpc, fval, fh, fs, fo, frun, fframe⟩ :=
          xor_execution program s (entry + 1) 3 3 0 spc run (by simp [positiveTest] at fits; omega)
            fetched
        refine ⟨f, tr, by simpa using fpc, ?_, fh, fs, fo, frun, fframe⟩
        rw [fval, same 3 (by decide), pReg, zero, bool_val room, small_val room 1 (by omega)]
        cases p <;> rfl)
  refine ⟨final, ticks, trace, time, by simpa [positiveTest] using pc, run, by rw [val]; cases p <;> simp [word, Nat.mod_eq_of_lt (show 1 < 2 ^ width by omega)], heap, stack, out,
    frame 1 (by decide) (by decide), frame 2 (by decide) (by decide), frame 4 (by decide) (by decide),
    frame 5 (by decide) (by decide), frame 6 (by decide) (by decide)⟩

theorem negative_spec (room : 4 < 2 ^ width) :
    TestSpec (negativeTest (width := width)) 2 (fun _ _ q => q) := by
  intro program state entry c p q present position running fits cReg _ _ qReg
  obtain ⟨final, ticks, trace, time, pc, run, val, heap, stack, out, frame⟩ :=
    pair_execution program state entry 1 (.xor 3 7 0) (word width (if q then 0 else 1)) position running
      (by simpa [negativeTest] using fits) (by simpa [negativeTest] using fetch2 program entry _ present 0 (by simp [positiveTest, negativeTest, freeTest, conflictTest]))
      (by simpa [negativeTest] using fetch2 program entry _ present 1 (by simp [positiveTest, negativeTest, freeTest, conflictTest]))
      (by
        intro s zero same run spc fetched
        obtain ⟨f, tr, fpc, fval, fh, fs, fo, frun, fframe⟩ :=
          xor_execution program s (entry + 1) 3 7 0 spc run (by simp [negativeTest] at fits; omega)
            fetched
        refine ⟨f, tr, by simpa using fpc, ?_, fh, fs, fo, frun, fframe⟩
        rw [fval, same 7 (by decide), qReg, zero, bool_val room, small_val room 1 (by omega)]
        cases q <;> rfl)
  refine ⟨final, ticks, trace, time, by simpa [negativeTest] using pc, run, by rw [val]; cases q <;> simp [word, Nat.mod_eq_of_lt (show 1 < 2 ^ width by omega)], heap, stack, out,
    frame 1 (by decide) (by decide), frame 2 (by decide) (by decide), frame 4 (by decide) (by decide),
    frame 5 (by decide) (by decide), frame 6 (by decide) (by decide)⟩

theorem free_spec (room : 4 < 2 ^ width) :
    TestSpec (freeTest (width := width)) 2 (fun _ _ q => !q) := by
  intro program state entry c p q present position running fits cReg _ _ qReg
  obtain ⟨final, ticks, trace, time, pc, run, val, heap, stack, out, frame⟩ :=
    pair_execution program state entry 0 (.add 3 7 0) (word width (if !q then 0 else 1)) position running
      (by simpa [freeTest] using fits) (by simpa [freeTest] using fetch2 program entry _ present 0 (by simp [positiveTest, negativeTest, freeTest, conflictTest]))
      (by simpa [freeTest] using fetch2 program entry _ present 1 (by simp [positiveTest, negativeTest, freeTest, conflictTest]))
      (by
        intro s zero same run spc fetched
        obtain ⟨f, tr, fpc, fval, fh, fs, fo, frun, fframe⟩ :=
          add_execution program s (entry + 1) 3 7 0 spc run (by simp [freeTest] at fits; omega)
            fetched
        refine ⟨f, tr, by simpa using fpc, ?_, fh, fs, fo, frun, fframe⟩
        rw [fval, same 7 (by decide), qReg, zero, bool_val room, small_val room 0 (by omega)]
        cases q <;> rfl)
  refine ⟨final, ticks, trace, time, by simpa [freeTest] using pc, run, by rw [val]; cases q <;> simp [word, Nat.mod_eq_of_lt (show 1 < 2 ^ width by omega)], heap, stack, out,
    frame 1 (by decide) (by decide), frame 2 (by decide) (by decide), frame 4 (by decide) (by decide),
    frame 5 (by decide) (by decide), frame 6 (by decide) (by decide)⟩

theorem conflict_spec (room : 4 < 2 ^ width) :
    TestSpec (conflictTest (width := width)) 3 (fun _ p q => p && q) := by
  intro program state entry c p q present position running fits cReg _ pReg qReg
  have f0 := fetch2 program entry _ present 0 (by simp [positiveTest, negativeTest, freeTest, conflictTest])
  have f1 := fetch2 program entry _ present 1 (by simp [positiveTest, negativeTest, freeTest, conflictTest])
  have f2 := fetch2 program entry _ present 2 (by simp [conflictTest])
  simp only [conflictTest, List.length_cons, List.length_nil] at fits f0 f1 f2
  obtain ⟨s1, t1, pc1, val1, heap1, stack1, out1, run1, frame1⟩ :=
    add_execution program state entry 3 3 7 position running (by omega) (by simpa using f0)
  obtain ⟨s2, t2, pc2, val2, heap2, stack2, out2, run2, frame2⟩ :=
    SharedEvaluationReclaim.constant_execution program (entry + 1) 2 0 s1 pc1 run1 (by omega) (by simpa using f1)
  obtain ⟨s3, t3, pc3, val3, heap3, stack3, out3, run3, frame3⟩ :=
    xor_execution program s2 (entry + 1 + 1) 3 3 0 pc2 run2 (by omega) (by simpa using f2)
  have l1 : s1.liveWords = state.liveWords := by simp only [State.liveWords, heap1, stack1, out1]
  have l2 : s2.liveWords = state.liveWords := by simp only [State.liveWords, heap2, stack2, out2] at l1 ⊢; exact l1
  have joined := t1.append (t2.append t3)
  rw [l1, l2, Nat.max_self, Nat.max_self] at joined
  refine ⟨s3, 3, joined, le_rfl, by simpa [conflictTest] using pc3, run3, ?_, heap3.trans (heap2.trans heap1),
    stack3.trans (stack2.trans stack1), out3.trans (out2.trans out1), ?_, ?_, ?_, ?_, ?_⟩
  · rw [val3, frame2 3 (by decide), val1, pReg, qReg, val2, bool_val room, bool_val room]
    cases p <;> cases q <;> simp [word, Nat.mod_eq_of_lt (show 2 < 2 ^ width by omega), Nat.mod_eq_of_lt room,
      Nat.mod_eq_of_lt (show 1 < 2 ^ width by omega), Nat.mod_eq_of_lt (show 3 < 2 ^ width by omega)]
  all_goals first
    | (rw [frame3 _ (by decide), frame2 _ (by decide), frame1 _ (by decide)])
end Controller.Extensions.LiteralTests
