module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Extensions.LiteralRootRun
public import Controller.Cost.SharedTagCompare
public import Controller.Cost.EnumerationStreamEmit

@[expose] public section

/-! Emit the characteristic vector of a literal witness descriptor. The
instruction sequence uses channel indices and the public matrix dimensions;
the selected channel and root remain runtime values in registers 1 and 4.
Output words are prepended by the machine, so coordinates are visited in
reverse order. Only the output grows; the matrix and caller stack are retained. -/
namespace Controller.Extensions.LiteralWitnessEmit
open Controller.Decoder Controller.Cost Controller.Cost.EnumerationSteps
open Controller.Extensions.LiteralDecision Controller.Extensions.LiteralRoot
open Controller.Extensions.LiteralScan (word_val)

variable {n width : Nat}

def Emits (program : Program width 8) (start final : State width 8)
    (bound : Nat) (words : List (Word width)) : Prop :=
  ∃ ticks, Execution program start final ticks (start.liveWords + words.length) ∧ ticks ≤ bound ∧
    final.heap = start.heap ∧ final.stack = start.stack ∧ final.output = words ++ start.output ∧
    final.halted = false ∧ final.reg 1 = start.reg 1 ∧ final.reg 4 = start.reg 4

theorem Emits.live {program : Program width 8} {start final : State width 8} {bound words}
    (h : Emits program start final bound words) : final.liveWords = start.liveWords + words.length := by
  obtain ⟨_, _, _, heap, stack, output, _⟩ := h
  simp only [State.liveWords, heap, stack, output, List.length_append]
  omega

theorem Emits.trans {program : Program width 8} {start middle final : State width 8}
    {a b : Nat} {xs ys : List (Word width)}
    (first : Emits program start middle a xs) (second : Emits program middle final b ys) :
    Emits program start final (a + b) (ys ++ xs) := by
  have live := first.live
  obtain ⟨t, tr, tb, h, s, o, _, r1, r4⟩ := first
  obtain ⟨u, ur, ub, hh, ss, oo, run, rr1, rr4⟩ := second
  have joined := tr.append ur
  rw [live, Nat.max_eq_right (by omega)] at joined
  refine ⟨t + u, ?_, by omega, hh.trans h, ss.trans s, ?_, run, rr1.trans r1, rr4.trans r4⟩
  · simpa only [List.length_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using joined
  · rw [oo, o, List.append_assoc]

def constantCode (value : Bool) : List (Instruction width 8) :=
  [.constant 3 (boolWord width value), .emit 3]

theorem constant_execution (program : Program width 8) (state : State width 8)
    (entry : Nat) (value : Bool) (position : state.pc = word width entry)
    (running : state.halted = false) (room : entry + 2 < 2 ^ width)
    (present : SharedRootRead.BlockAt program entry (constantCode value)) :
    ∃ final, Emits program state final 2 [boolWord width value] ∧
      final.pc = word width (entry + 2) := by
  obtain ⟨s, tr, pc, val, heap, stack, output, run, frame⟩ :=
    SharedEvaluationReclaim.constant_execution program entry (if value then 1 else 0) 3 state
      position running (by omega) (by simpa [constantCode, boolWord] using present 0 (by simp [constantCode]))
  obtain ⟨f, tf, pcf, hf, sf, of, rf, ff, _⟩ :=
    emit_execution program s (entry + 1) 3 pc run (by omega)
      (by simpa [constantCode] using present 1 (by simp [constantCode]))
  have live : s.liveWords = state.liveWords := by simp only [State.liveWords, heap, stack, output]
  refine ⟨f, ⟨2, ?_, le_rfl, hf.trans heap, sf.trans stack, ?_, rf,
    by rw [ff, frame 1 (by decide)], by rw [ff, frame 4 (by decide)]⟩, by simpa [Nat.add_assoc] using pcf⟩
  · simpa only [live, List.length_singleton, Nat.max_eq_right (Nat.le_succ _)] using tr.append tf
  · rw [of, val, output]; rfl

def storedCode (offset : Nat) : List (Instruction width 8) :=
  [.constant 5 (word width offset), .add 5 5 4, .load 3 5, .emit 3]

theorem stored_execution (program : Program width 8) (state : State width 8)
    (entry offset root : Nat) (value : Word width) (position : state.pc = word width entry)
    (running : state.halted = false) (room : entry + 4 < 2 ^ width)
    (addressFits : offset + root < 2 ^ width) (held : state.reg 4 = word width root)
    (cell : state.heap[offset + root]? = some value)
    (present : SharedRootRead.BlockAt program entry (storedCode offset)) :
    ∃ final, Emits program state final 4 [value] ∧ final.pc = word width (entry + 4) := by
  obtain ⟨s1, t1, pc1, v1, h1, st1, o1, r1, f1⟩ :=
    SharedEvaluationReclaim.constant_execution program entry offset 5 state position running (by omega)
      (by simpa [storedCode] using present 0 (by simp [storedCode]))
  obtain ⟨s2, t2, pc2, v2, h2, st2, o2, r2, f2⟩ :=
    add_execution program s1 (entry + 1) 5 5 4 pc1 r1 (by omega)
      (by simpa [storedCode] using present 1 (by simp [storedCode]))
  have address : (s2.reg 5).val = offset + root := by
    rw [v2, v1, f1 4 (by decide), held, word_val offset (by omega), word_val root (by omega), word_val _ addressFits]
  have inside : (s2.reg 5).val < s2.heap.size := by
    rw [address, h2, h1]; exact (Array.getElem?_eq_some_iff.mp cell).1
  obtain ⟨s3, t3, pc3, v3, h3, st3, o3, r3, f3⟩ :=
    load_execution program s2 (entry + 1 + 1) 3 5 pc2 r2 (by omega) inside
      (by simpa [storedCode] using present 2 (by simp [storedCode]))
  have loaded : s3.reg 3 = value := by
    rw [v3]
    have same := cell
    rw [← h1, ← h2, ← address, Array.getElem?_eq_getElem inside] at same
    exact Option.some.inj same
  obtain ⟨f, tf, pcf, hf, sf, of, rf, ff, _⟩ :=
    emit_execution program s3 (entry + 1 + 1 + 1) 3 pc3 r3 (by omega)
      (by simpa [storedCode] using present 3 (by simp [storedCode]))
  have l1 : s1.liveWords = state.liveWords := by simp only [State.liveWords, h1, st1, o1]
  have l2 : s2.liveWords = state.liveWords := by simp only [State.liveWords, h2, st2, o2, h1, st1, o1]
  have l3 : s3.liveWords = state.liveWords := by simp only [State.liveWords, h3, st3, o3, h2, st2, o2, h1, st1, o1]
  refine ⟨f, ⟨4, ?_, le_rfl, by rw [hf, h3, h2, h1], by rw [sf, st3, st2, st1],
    by rw [of, loaded, o3, o2, o1]; rfl, rf,
    by rw [ff, f3 1 (by decide), f2 1 (by decide), f1 1 (by decide)],
    by rw [ff, f3 4 (by decide), f2 4 (by decide), f1 4 (by decide)]⟩,
    by simpa [Nat.add_assoc] using pcf⟩
  simpa only [l1, l2, l3, List.length_singleton, Nat.max_eq_right (Nat.le_succ _)] using
    t1.append (t2.append (t3.append tf))

def selectedCode (entry channel : Nat) : List (Instruction width 8) :=
  (SharedTagCompare.code width (entry + 7) channel 1).toList ++
    constantCode false ++ [.constant 0 (word width 0), .branchZero 0 (word width (entry + 9))] ++ constantCode true

theorem selected_execution (program : Program width 8) (state : State width 8)
    (entry channel selected : Nat) (position : state.pc = word width entry)
    (running : state.halted = false) (room : entry + 9 < 2 ^ width)
    (channelFits : channel < 2 ^ width) (selectedFits : selected < 2 ^ width)
    (held : state.reg 1 = word width selected)
    (present : SharedRootRead.BlockAt program entry (selectedCode entry channel)) :
    ∃ final, Emits program state final 7 [boolWord width (decide (selected = channel))] ∧
      final.pc = word width (entry + 9) := by
  have compare : RawTransferLoops.CodeAt program entry (SharedTagCompare.code width (entry + 7) channel 1) := by
    intro i
    have h := present i.val (by simp [selectedCode, constantCode]; have := i.isLt; simp at this; omega)
    have small : i.val < 3 := by simpa using i.isLt
    interval_cases hi : i.val <;> simpa [hi, selectedCode, SharedTagCompare.code, constantCode] using h
  have noAt : SharedRootRead.BlockAt program (entry + 3) (constantCode (width := width) false) := by
    intro i small
    have upper : i < 2 := by simpa [constantCode] using small
    have h := present (3 + i) (by simp [selectedCode, constantCode] at *; omega)
    interval_cases i <;> simpa [selectedCode, SharedTagCompare.code, constantCode, Nat.add_assoc] using h
  have yesAt : SharedRootRead.BlockAt program (entry + 7) (constantCode (width := width) true) := by
    intro i small
    have upper : i < 2 := by simpa [constantCode] using small
    have h := present (7 + i) (by simp [selectedCode, constantCode] at *; omega)
    interval_cases i <;> simpa [selectedCode, SharedTagCompare.code, constantCode, Nat.add_assoc] using h
  obtain ⟨s, tr, heap, stack, output, pc, run, frame⟩ :=
    SharedTagCompare.execution program state entry (entry + 7) channel selected 1 (by decide)
      position running (by omega) channelFits selectedFits held compare
  have live : s.liveWords = state.liveWords := by simp only [State.liveWords, heap, stack, output]
  by_cases same : selected = channel
  · obtain ⟨f, ⟨ticks, tf, time, hf, sf, of, rf, f1, f4⟩, pcf⟩ :=
      constant_execution program s (entry + 7) true (by simpa [same] using pc) run (by omega) yesAt
    refine ⟨f, ⟨3 + ticks, ?_, by omega, hf.trans heap, sf.trans stack, ?_, rf,
      f1.trans (frame 1 (by decide)), f4.trans (frame 4 (by decide))⟩, by simpa [Nat.add_assoc] using pcf⟩
    · simpa only [live, List.length_singleton, Nat.max_eq_right (Nat.le_succ _)] using tr.append tf
    · simpa [same, output] using of
  · obtain ⟨f, emit, pcf⟩ := constant_execution program s (entry + 3) false
      (by simpa [same] using pc) run (by omega) noAt
    have flive := emit.live
    obtain ⟨ticks, tf, time, hf, sf, of, rf, f1, f4⟩ := emit
    obtain ⟨g, tg, pcg, hg, sg, og, rg, fg⟩ := jump_execution program f (entry + 5) (entry + 9)
      (by simpa [Nat.add_assoc] using pcf) rf (by omega)
      (by simpa [selectedCode, SharedTagCompare.code, constantCode] using present 5 (by simp [selectedCode, constantCode]))
      (by simpa [selectedCode, SharedTagCompare.code, constantCode, Nat.add_assoc] using present 6 (by simp [selectedCode, constantCode]))
    refine ⟨g, ⟨3 + ticks + 2, ?_, by omega, hg.trans (hf.trans heap), sg.trans (sf.trans stack), ?_, rg,
      by rw [fg 1 (by decide), f1, frame 1 (by decide)],
      by rw [fg 4 (by decide), f4, frame 4 (by decide)]⟩, pcg⟩
    · have joined := (tr.append tf).append tg
      simpa only [live, flive, List.length_singleton, Nat.max_eq_right (Nat.le_succ _), Nat.max_self] using joined
    · simpa [same, output, of] using og

inductive Operand where
  | one
  | stored (offset : Nat)
  | selected (channel : Nat)

def operandCode (entry : Nat) : Operand → List (Instruction width 8)
  | .one => constantCode true
  | .stored offset => storedCode offset
  | .selected channel => selectedCode entry channel

def operandSize : Operand → Nat
  | .one => 2 | .stored _ => 4 | .selected _ => 9

@[simp] theorem operandCode_length (entry : Nat) (op : Operand) :
    (operandCode (width := width) entry op).length = operandSize op := by
  cases op <;> simp [operandCode, operandSize, constantCode, storedCode, selectedCode]

def operandValue (heap : Array (Word width)) (root selected : Nat) : Operand → Word width
  | .one => boolWord width true
  | .stored offset => EnumerationStreamEmit.heapValue heap (offset + root)
  | .selected channel => boolWord width (decide (selected = channel))

def Valid (heap : Array (Word width)) (root : Nat) : Operand → Prop
  | .stored offset => offset + root < heap.size
  | .selected channel => channel < 2 ^ width
  | .one => True

theorem operand_execution (program : Program width 8) (state : State width 8)
    (entry root selected : Nat) (op : Operand) (position : state.pc = word width entry)
    (running : state.halted = false) (room : entry + operandSize op < 2 ^ width)
    (heapFits : state.heap.size < 2 ^ width) (selectedFits : selected < 2 ^ width)
    (rootReg : state.reg 4 = word width root) (selectedReg : state.reg 1 = word width selected)
    (valid : Valid state.heap root op) (present : SharedRootRead.BlockAt program entry (operandCode entry op)) :
    ∃ final, Emits program state final 9 [operandValue state.heap root selected op] ∧
      final.pc = word width (entry + operandSize op) := by
  have widen {s : State width 8} {bound : Nat} {ws : List (Word width)}
      (h : Emits program state s bound ws) (le : bound ≤ 9) : Emits program state s 9 ws := by
    obtain ⟨ticks, tr, time, rest⟩ := h
    exact ⟨ticks, tr, time.trans le, rest⟩
  cases op with
  | one =>
    obtain ⟨final, trace, pc⟩ := constant_execution program state entry true position running room present
    exact ⟨final, widen trace (by omega), pc⟩
  | stored offset =>
    obtain ⟨final, trace, pc⟩ := stored_execution program state entry offset root
      (operandValue state.heap root selected (.stored offset)) position running room (by exact valid.trans heapFits) rootReg
      (by rw [Array.getElem?_eq_getElem valid]; simp [operandValue, EnumerationStreamEmit.heapValue_eq _ _ valid]) present
    exact ⟨final, widen trace (by omega), pc⟩
  | selected channel =>
    obtain ⟨final, trace, pc⟩ := selected_execution program state entry channel selected position running room
      valid selectedFits selectedReg present
    exact ⟨final, widen trace (by omega), pc⟩

def code (entry : Nat) : List Operand → List (Instruction width 8)
  | [] => []
  | op :: rest => operandCode entry op ++ code (entry + operandSize op) rest

def size (ops : List Operand) : Nat := (ops.map operandSize).sum

@[simp] theorem code_length (entry : Nat) (ops : List Operand) :
    (code (width := width) entry ops).length = size ops := by
  induction ops generalizing entry with
  | nil => rfl
  | cons op rest ih => simp [code, size, ih]

theorem size_bound (ops : List Operand) : size ops ≤ 9 * ops.length := by
  induction ops with
  | nil => simp [size]
  | cons op rest ih =>
    have bound : operandSize op ≤ 9 := by cases op <;> simp [operandSize]
    simp only [size, List.map_cons, List.sum_cons, List.length_cons] at *
    omega

theorem execution (program : Program width 8) (ops : List Operand) (root selected : Nat) :
    ∀ (entry : Nat) (state : State width 8), state.pc = word width entry → state.halted = false →
      entry + size ops < 2 ^ width → state.heap.size < 2 ^ width → selected < 2 ^ width →
      state.reg 4 = word width root → state.reg 1 = word width selected →
      (∀ op ∈ ops, Valid state.heap root op) → SharedRootRead.BlockAt program entry (code entry ops) →
      ∃ final, Emits program state final (9 * ops.length) ((ops.map (operandValue state.heap root selected)).reverse) ∧
        final.pc = word width (entry + size ops) := by
  induction ops with
  | nil =>
    intro entry state pc run _ _ _ _ _ _ _
    exact ⟨state, ⟨0, by simpa using Execution.refl state, le_rfl, rfl, rfl, rfl, run, rfl, rfl⟩,
      by simpa [size] using pc⟩
  | cons op rest ih =>
    intro entry state pc run room heapFits selectedFits r4 r1 valid present
    have room' : entry + operandSize op + size rest < 2 ^ width := by simpa [size, Nat.add_assoc] using room
    have headAt := SharedDetectorAssembly.block_left program entry _ _ present
    have tailAt := SharedDetectorAssembly.block_right program entry _ _ present
    rw [operandCode_length] at tailAt
    obtain ⟨middle, first, midPC⟩ := operand_execution program state entry root selected op pc run
      (by omega) heapFits selectedFits r4 r1 (valid op (by simp)) headAt
    obtain ⟨_, _, _, heap, stack, output, active, reg1, reg4⟩ := id first
    obtain ⟨final, tail, endPC⟩ := ih (entry + operandSize op) middle midPC active room'
      (by rw [heap]; exact heapFits) selectedFits (reg4.trans r4) (reg1.trans r1)
      (by intro o mem; rw [heap]; exact valid o (by simp [mem])) tailAt
    refine ⟨final, ?_, ?_⟩
    · have joined := first.trans tail
      simpa only [heap, List.map_cons, List.reverse_cons, List.length_cons, Nat.mul_add, Nat.mul_one, Nat.add_comm] using joined
    · simpa [size, Nat.add_assoc] using endPC

end Controller.Extensions.LiteralWitnessEmit
