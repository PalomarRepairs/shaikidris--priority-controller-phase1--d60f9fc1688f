module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.UniformDAGTypedNode
public import Controller.Decoder.Eval

@[expose] public section

/-! Fixed topological interpreter. The node count is fetched from the loaded
packet. The FIFO-like stack frame holds the remaining count and current row
offset across the common node executor; the caller's suffix is retained. -/
namespace Controller.Cost.UniformDAGLoop
open Controller.Cost.GateProgram

/-- Fetch the declared count and begin at source-row offset zero. -/
def initializeCode (width countAddress : ℕ) : Code width :=
  [.constant 0 (word width countAddress), .load 0 0, .push 0,
    .constant 3 (word width 0)]

/-- A zero remaining count returns to the caller; otherwise save both words. -/
def enterCode (width exit : ℕ) : Code width :=
  [.pop 0, .branchZero 0 (word width exit), .push 0, .push 3]

/-- Restore the row offset, advance it by two, decrement the saved remaining
count, and return to the actual fetched loop test. -/
def advanceCode (width entry : ℕ) : Code width :=
  [.pop 3, .constant 0 (word width 2), .add 3 3 0,
    .pop 0, .constant 2 (word width (2 ^ width - 1)), .add 0 0 2,
    .push 0, .constant 0 (word width 0), .branchZero 0 (word width entry)]

/-- No source-node count, tag, arity or child identifier is compiled into this
program. They are loaded by the interpreter and its fixed node block. -/
def code (width base countAddress : ℕ) (layout : UniformDAGNode.Layout) : Code width :=
  initializeCode width countAddress ++
    (enterCode width (base + 126) ++
      (UniformDAGNode.code width (base + 8) layout ++ advanceCode width (base + 4)))

@[simp] theorem initializeCode_length : (initializeCode width countAddress).length = 4 := rfl
@[simp] theorem enterCode_length : (enterCode width exit).length = 4 := rfl
@[simp] theorem advanceCode_length : (advanceCode width entry).length = 9 := rfl
@[simp] theorem code_length : (code width base countAddress layout).length = 126 := by
  simp [code]

/-- The common node executor is the actual contiguous middle of the fixed loop. -/
theorem node_block (program : Program width 4) (base countAddress : ℕ)
    (layout : UniformDAGNode.Layout)
    (block : BlockAt program base (code width base countAddress layout)) :
    BlockAt program (base + 8) (UniformDAGNode.code width (base + 8) layout) := by
  have afterInit := BlockAt.suffix program base (initializeCode width countAddress)
    (enterCode width (base + 126) ++
      (UniformDAGNode.code width (base + 8) layout ++ advanceCode width (base + 4))) block
  have afterEnter := BlockAt.suffix program (base + 4) (enterCode width (base + 126))
    (UniformDAGNode.code width (base + 8) layout ++ advanceCode width (base + 4))
    (by simpa only [initializeCode_length] using afterInit)
  exact BlockAt.prefix program (base + 8) (UniformDAGNode.code width (base + 8) layout)
    (advanceCode width (base + 4)) (by simpa only [enterCode_length, Nat.add_assoc] using afterEnter)

private theorem fetched (program : Program width 4) (state : State width 4)
    (address : ℕ) (instruction : Instruction width 4)
    (pc : state.pc = word width address) (fits : address < 2 ^ width)
    (entry : program[address]? = some instruction) :
    programStep program state = step instruction state := by
  unfold programStep
  rw [pc, show (word width address).val = address from Nat.mod_eq_of_lt fits, entry]
  rfl

/-- Each nonempty iteration physically saves count and row offset for the node. -/
theorem enter_execution (program : Program width 4) (state : State width 4)
    (base exit remaining : ℕ) (suffix : List (Word width))
    (positive : 0 < remaining) (countFits : remaining < 2 ^ width)
    (stack : state.stack = word width remaining :: suffix)
    (pc : state.pc = word width base) (running : state.halted = false)
    (fits : base + 4 < 2 ^ width) (block : BlockAt program base (enterCode width exit)) :
    ∃ ready peak, Execution program state ready 4 peak ∧ peak ≤ state.liveWords + 1 ∧
      ready.heap = state.heap ∧ ready.output = state.output ∧
      ready.stack = state.reg 3 :: word width remaining :: suffix ∧
      ready.reg 3 = state.reg 3 ∧ ready.pc = word width (base + 4) ∧ ready.halted = false := by
  let s1 := { state.advance.put 0 (word width remaining) with stack := suffix }
  let s2 := s1.advance
  let s3 := { s2.advance with stack := s2.reg 0 :: s2.stack }
  let s4 := { s3.advance with stack := s3.reg 3 :: s3.stack }
  have pv : state.pc.val = base := by rw [pc]; exact Nat.mod_eq_of_lt (by omega)
  have countVal : (word width remaining).val = remaining := Nat.mod_eq_of_lt countFits
  have p1 : s1.pc = word width (base + 1) := by simp [s1, State.advance, State.put, pv]
  have v1 : s1.pc.val = base + 1 := by rw [p1]; exact Nat.mod_eq_of_lt (by omega)
  have p2 : s2.pc = word width (base + 2) := by simp [s2, State.advance, v1, Nat.add_assoc]
  have v2 : s2.pc.val = base + 2 := by rw [p2]; exact Nat.mod_eq_of_lt (by omega)
  have p3 : s3.pc = word width (base + 3) := by simp [s3, State.advance, v2, Nat.add_assoc]
  have v3 : s3.pc.val = base + 3 := by rw [p3]; exact Nat.mod_eq_of_lt (by omega)
  have first : programStep program state = some s1 := by
    rw [fetched program state base (.pop 0) pc (by omega)
      (by simpa [enterCode] using block 0 (by simp [enterCode]))]
    simp [step, s1, running, stack]
  have second : programStep program s1 = some s2 := by
    rw [fetched program s1 (base + 1) (.branchZero 0 (word width exit)) p1 (by omega)
      (by simpa [enterCode] using block 1 (by simp [enterCode]))]
    simp [step, s1, s2, State.advance, State.put, running, countVal, Nat.ne_of_gt positive]
  have third : programStep program s2 = some s3 := by
    rw [fetched program s2 (base + 2) (.push 0) p2 (by omega)
      (by simpa [enterCode] using block 2 (by simp [enterCode]))]
    simp [step, s1, s2, s3, State.advance, State.put, running]
  have fourth : programStep program s3 = some s4 := by
    rw [fetched program s3 (base + 3) (.push 3) p3 (by omega)
      (by simpa [enterCode] using block 3 (by simp [enterCode]))]
    simp [step, s1, s2, s3, s4, State.advance, State.put, running]
  have trace := Execution.cons first (Execution.cons second
    (Execution.cons third (Execution.cons fourth (Execution.refl s4))))
  refine ⟨s4, _, by simpa using trace, ?_, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · simp only [max_le_iff]
    simp [s1, s2, s3, s4, State.liveWords, State.advance, State.put, stack]
    omega
  · simp [s1, s2, s3, s4, State.advance, State.put]
  · simp [s1, s2, s3, s4, State.advance, State.put]
  · simp [s4, State.advance, v3, Nat.add_assoc]
  · simp [s1, s2, s3, s4, State.advance, State.put, running]

/-- The final zero-count test consumes its frame and returns to the caller. -/
theorem exit_execution (program : Program width 4) (state : State width 4)
    (base exit : ℕ) (suffix : List (Word width))
    (stack : state.stack = word width 0 :: suffix)
    (pc : state.pc = word width base) (running : state.halted = false)
    (fits : base + 2 < 2 ^ width) (block : BlockAt program base (enterCode width exit)) :
    ∃ final peak, Execution program state final 2 peak ∧ peak ≤ state.liveWords ∧
      final.heap = state.heap ∧ final.output = state.output ∧ final.stack = suffix ∧
      final.pc = word width exit ∧ final.halted = false := by
  let s1 := { state.advance.put 0 (word width 0) with stack := suffix }
  let final := { s1.advance with pc := word width exit }
  have pv : state.pc.val = base := by rw [pc]; exact Nat.mod_eq_of_lt (by omega)
  have p1 : s1.pc = word width (base + 1) := by simp [s1, State.advance, State.put, pv]
  have first : programStep program state = some s1 := by
    rw [fetched program state base (.pop 0) pc (by omega)
      (by simpa [enterCode] using block 0 (by simp [enterCode]))]
    simp [step, s1, running, stack]
  have second : programStep program s1 = some final := by
    rw [fetched program s1 (base + 1) (.branchZero 0 (word width exit)) p1 (by omega)
      (by simpa [enterCode] using block 1 (by simp [enterCode]))]
    simp [step, s1, final, State.advance, State.put, running, word]
  have trace := Execution.cons first (Execution.cons second (Execution.refl final))
  refine ⟨final, _, by simpa using trace, ?_, rfl, rfl, rfl, rfl, ?_⟩
  · simp only [max_le_iff]
    simp [s1, final, State.liveWords, State.advance, State.put, stack]
  · simp [s1, final, State.advance, State.put, running]

private theorem decrement_word (width remaining : ℕ) (positive : 0 < remaining)
    (fits : remaining < 2 ^ width) :
    word width ((word width remaining).val + (word width (2 ^ width - 1)).val) =
      word width (remaining - 1) := by
  apply Fin.ext
  have capPositive := Nat.two_pow_pos width
  have remVal : (word width remaining).val = remaining := Nat.mod_eq_of_lt fits
  have predVal : (word width (2 ^ width - 1)).val = 2 ^ width - 1 :=
    Nat.mod_eq_of_lt (by omega)
  change ((word width remaining).val + (word width (2 ^ width - 1)).val) % (2 ^ width) =
    (remaining - 1) % (2 ^ width)
  rw [remVal, predVal, show remaining + (2 ^ width - 1) = 2 ^ width + (remaining - 1) by omega]
  simp [Nat.add_mod]

/-- The fetched tail restores the saved offset, advances to the next source
row, decrements the saved count and returns to the actual loop test. -/
theorem advance_execution (program : Program width 4) (state : State width 4)
    (base entry offset remaining : ℕ) (suffix : List (Word width))
    (positive : 0 < remaining) (countFits : remaining < 2 ^ width)
    (offsetFits : offset + 2 < 2 ^ width)
    (stack : state.stack = word width offset :: word width remaining :: suffix)
    (pc : state.pc = word width base) (running : state.halted = false)
    (fits : base + 9 < 2 ^ width) (block : BlockAt program base (advanceCode width entry)) :
    ∃ ready peak, Execution program state ready 9 peak ∧ peak ≤ state.liveWords ∧
      ready.heap = state.heap ∧ ready.output = state.output ∧
      ready.stack = word width (remaining - 1) :: suffix ∧
      ready.reg 3 = word width (offset + 2) ∧ ready.pc = word width entry ∧ ready.halted = false := by
  let s1 := { state.advance.put 3 (word width offset) with stack := word width remaining :: suffix }
  let s2 := s1.advance.put 0 (word width 2)
  let s3 := s2.advance.put 3 (word width ((s2.reg 3).val + (s2.reg 0).val))
  let s4 := { s3.advance.put 0 (word width remaining) with stack := suffix }
  let s5 := s4.advance.put 2 (word width (2 ^ width - 1))
  let s6 := s5.advance.put 0 (word width ((s5.reg 0).val + (s5.reg 2).val))
  let s7 := { s6.advance with stack := s6.reg 0 :: s6.stack }
  let s8 := s7.advance.put 0 (word width 0)
  let s9 := { s8.advance with pc := word width entry }
  have pv : state.pc.val = base := by rw [pc]; exact Nat.mod_eq_of_lt (by omega)
  have offVal : (word width offset).val = offset := Nat.mod_eq_of_lt (by omega)
  have twoVal : (word width 2).val = 2 := Nat.mod_eq_of_lt (by omega)
  have decrement := decrement_word width remaining positive countFits
  have p1 : s1.pc = word width (base + 1) := by simp [s1, State.advance, State.put, pv, Nat.add_assoc]
  have v1 : s1.pc.val = base + 1 := by rw [p1]; exact Nat.mod_eq_of_lt (by omega)
  have p2 : s2.pc = word width (base + 2) := by simp [s2, State.advance, State.put, v1, Nat.add_assoc]
  have v2 : s2.pc.val = base + 2 := by rw [p2]; exact Nat.mod_eq_of_lt (by omega)
  have p3 : s3.pc = word width (base + 3) := by simp [s3, State.advance, State.put, v2, Nat.add_assoc]
  have v3 : s3.pc.val = base + 3 := by rw [p3]; exact Nat.mod_eq_of_lt (by omega)
  have p4 : s4.pc = word width (base + 4) := by simp [s4, State.advance, State.put, v3, Nat.add_assoc]
  have v4 : s4.pc.val = base + 4 := by rw [p4]; exact Nat.mod_eq_of_lt (by omega)
  have p5 : s5.pc = word width (base + 5) := by simp [s5, State.advance, State.put, v4, Nat.add_assoc]
  have v5 : s5.pc.val = base + 5 := by rw [p5]; exact Nat.mod_eq_of_lt (by omega)
  have p6 : s6.pc = word width (base + 6) := by simp [s6, State.advance, State.put, v5, Nat.add_assoc]
  have v6 : s6.pc.val = base + 6 := by rw [p6]; exact Nat.mod_eq_of_lt (by omega)
  have p7 : s7.pc = word width (base + 7) := by simp [s7, State.advance, State.put, v6, Nat.add_assoc]
  have v7 : s7.pc.val = base + 7 := by rw [p7]; exact Nat.mod_eq_of_lt (by omega)
  have p8 : s8.pc = word width (base + 8) := by simp [s8, State.advance, State.put, v7, Nat.add_assoc]
  have v8 : s8.pc.val = base + 8 := by rw [p8]; exact Nat.mod_eq_of_lt (by omega)
  have t1 : programStep program state = some s1 := by
    rw [fetched program state base (.pop 3) pc (by omega)
      (by simpa [advanceCode] using block 0 (by simp [advanceCode]))]
    simp [step, s1, State.advance, State.put, running, stack, word]
  have t2 : programStep program s1 = some s2 := by
    rw [fetched program s1 (base + 1) (.constant 0 (word width 2)) p1 (by omega)
      (by simpa [advanceCode] using block 1 (by simp [advanceCode]))]
    simp [step, s1, s2, State.advance, State.put, running, stack, word]
  have t3 : programStep program s2 = some s3 := by
    rw [fetched program s2 (base + 2) (.add 3 3 0) p2 (by omega)
      (by simpa [advanceCode] using block 2 (by simp [advanceCode]))]
    simp [step, s1, s2, s3, State.advance, State.put, running, stack, word]
  have t4 : programStep program s3 = some s4 := by
    rw [fetched program s3 (base + 3) (.pop 0) p3 (by omega)
      (by simpa [advanceCode] using block 3 (by simp [advanceCode]))]
    simp [step, s1, s2, s3, s4, State.advance, State.put, running, stack, word]
  have t5 : programStep program s4 = some s5 := by
    rw [fetched program s4 (base + 4) (.constant 2 (word width (2 ^ width - 1))) p4 (by omega)
      (by simpa [advanceCode] using block 4 (by simp [advanceCode]))]
    simp [step, s1, s2, s3, s4, s5, State.advance, State.put, running, stack, word]
  have t6 : programStep program s5 = some s6 := by
    rw [fetched program s5 (base + 5) (.add 0 0 2) p5 (by omega)
      (by simpa [advanceCode] using block 5 (by simp [advanceCode]))]
    simp [step, s1, s2, s3, s4, s5, s6, State.advance, State.put, running, stack, word]
  have t7 : programStep program s6 = some s7 := by
    rw [fetched program s6 (base + 6) (.push 0) p6 (by omega)
      (by simpa [advanceCode] using block 6 (by simp [advanceCode]))]
    simp [step, s1, s2, s3, s4, s5, s6, s7, State.advance, State.put, running, stack, word]
  have t8 : programStep program s7 = some s8 := by
    rw [fetched program s7 (base + 7) (.constant 0 (word width 0)) p7 (by omega)
      (by simpa [advanceCode] using block 7 (by simp [advanceCode]))]
    simp [step, s1, s2, s3, s4, s5, s6, s7, s8, State.advance, State.put, running, stack, word]
  have t9 : programStep program s8 = some s9 := by
    rw [fetched program s8 (base + 8) (.branchZero 0 (word width entry)) p8 (by omega)
      (by simpa [advanceCode] using block 8 (by simp [advanceCode]))]
    simp [step, s1, s2, s3, s4, s5, s6, s7, s8, s9, State.advance, State.put, running, stack, word]
  have trace := Execution.cons t1 (Execution.cons t2 (Execution.cons t3 (Execution.cons t4 (Execution.cons t5 (Execution.cons t6 (Execution.cons t7 (Execution.cons t8 (Execution.cons t9 (Execution.refl s9)))))))))
  refine ⟨s9, _, by simpa using trace, ?_, rfl, rfl, ?_, ?_, rfl, ?_⟩
  · simp only [max_le_iff]
    simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, State.liveWords, State.advance, State.put, stack]
    omega
  · simpa only [s1, s2, s3, s4, s5, s6, s7, s8, s9, State.advance, State.put,
      ite_true, ite_false, Fin.reduceEq] using
      congrArg (fun value => value :: suffix) decrement
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, State.advance, State.put, offVal, twoVal]
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, State.advance, State.put, running]

end Controller.Cost.UniformDAGLoop
