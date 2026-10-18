module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.EnumerationCounter

@[expose] public section

/-! Two-word recursion frames for the bounded-subset traversal. Register three
holds the cursor and register five holds the remaining capacity. The parent
mask cell identifies the active child, so no stage word is stored. -/
namespace Controller.Extensions.SupportFrame
open Controller.Cost Controller.Cost.RawTransferLoops

def saveCode (width : Nat) : List (Instruction width 8) := [.push 5, .push 3]

def restoreCode (width : Nat) : List (Instruction width 8) := [.pop 3, .pop 5]

@[simp] theorem saveCode_length : (saveCode width).length = 2 := rfl
@[simp] theorem restoreCode_length : (restoreCode width).length = 2 := rfl

theorem save_execution (program : Program width 8) (state : State width 8)
    (entry : Nat) (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 2 < 2 ^ width)
    (present : SharedRootRead.BlockAt program entry (saveCode width)) :
    ∃ final, Execution program state final 2 (state.liveWords + 2) ∧
      final.heap = state.heap ∧ final.stack = state.reg 3 :: state.reg 5 :: state.stack ∧
      final.output = state.output ∧ final.pc = word width (entry + 2) ∧
      final.halted = false ∧ (∀ i, final.reg i = state.reg i) ∧
      final.liveWords = state.liveWords + 2 := by
  obtain ⟨first, t1, p1, h1, s1, o1, r1, f1, l1⟩ :=
    EnumerationSteps.push_execution program state entry 5 position running (by omega)
      (by simpa [saveCode] using present 0 (by simp))
  obtain ⟨final, t2, p2, h2, s2, o2, r2, f2, l2⟩ :=
    EnumerationSteps.push_execution program first (entry + 1) 3 p1 r1 (by omega)
      (by simpa [saveCode] using present 1 (by simp))
  refine ⟨final, ?_, h2.trans h1, ?_, o2.trans o1, ?_, r2,
    fun i => (f2 i).trans (f1 i), by omega⟩
  · simpa only [l1, Nat.add_assoc, Nat.reduceAdd, Nat.max_eq_right (by omega :
      state.liveWords + 1 ≤ state.liveWords + 2)] using t1.append t2
  · rw [s2, s1, f1]
  · simpa only [Nat.add_assoc, Nat.reduceAdd] using p2

theorem restore_execution (program : Program width 8) (state : State width 8)
    (entry cursor capacity : Nat) (rest : List (Word width))
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 2 < 2 ^ width)
    (saved : state.stack = word width cursor :: word width capacity :: rest)
    (present : SharedRootRead.BlockAt program entry (restoreCode width)) :
    ∃ final, Execution program state final 2 state.liveWords ∧
      final.heap = state.heap ∧ final.stack = rest ∧ final.output = state.output ∧
      final.pc = word width (entry + 2) ∧ final.halted = false ∧
      final.reg 3 = word width cursor ∧ final.reg 5 = word width capacity ∧
      (∀ i : Fin 8, i ≠ 3 → i ≠ 5 → final.reg i = state.reg i) ∧
      final.liveWords + 2 = state.liveWords := by
  obtain ⟨first, t1, p1, v1, h1, s1, o1, r1, f1⟩ :=
    EnumerationSteps.pop_execution program state entry 3 (word width cursor)
      (word width capacity :: rest) position running (by omega) saved
      (by simpa [restoreCode] using present 0 (by simp))
  obtain ⟨final, t2, p2, v2, h2, s2, o2, r2, f2⟩ :=
    EnumerationSteps.pop_execution program first (entry + 1) 5 (word width capacity)
      rest p1 r1 (by omega) s1
      (by simpa [restoreCode] using present 1 (by simp))
  have l1 : first.liveWords + 1 = state.liveWords := by
    simp only [State.liveWords, h1, s1, o1, saved, List.length_cons]; omega
  refine ⟨final, ?_, h2.trans h1, s2, o2.trans o1, ?_, r2,
    (f2 3 (by decide)).trans v1, v2, ?_, ?_⟩
  · simpa only [Nat.max_eq_left (by omega : first.liveWords ≤ state.liveWords),
      Nat.reduceAdd] using t1.append t2
  · simpa only [Nat.add_assoc, Nat.reduceAdd] using p2
  · intro i h3 h5; rw [f2 i h5, f1 i h3]
  · simp only [State.liveWords, h2, h1, s2, o2, o1, saved, List.length_cons]; omega

def decrementCode (width : Nat) : List (Instruction width 8) :=
  [.constant 0 (word width (2 ^ width - 1)), .add 5 5 0]

@[simp] theorem decrementCode_length : (decrementCode width).length = 2 := rfl

/-- Decrement is used only at an internal node with positive remaining capacity. -/
theorem decrement_execution (program : Program width 8) (state : State width 8)
    (entry capacity : Nat) (position : state.pc = word width entry)
    (running : state.halted = false) (held : state.reg 5 = word width (capacity + 1))
    (fits : capacity + 1 < 2 ^ width) (room : entry + 2 < 2 ^ width)
    (present : SharedRootRead.BlockAt program entry (decrementCode width)) :
    ∃ final, Execution program state final 2 state.liveWords ∧
      final.reg 5 = word width capacity ∧ final.heap = state.heap ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry + 2) ∧ final.halted = false ∧
      (∀ i : Fin 8, i ≠ 0 → i ≠ 5 → final.reg i = state.reg i) := by
  obtain ⟨first, t1, p1, v1, h1, s1, o1, r1, f1⟩ :=
    SharedEvaluationReclaim.constant_execution program entry (2 ^ width - 1) 0 state
      position running (by omega) (by simpa [decrementCode] using present 0 (by simp))
  obtain ⟨final, t2, p2, v2, h2, s2, o2, r2, f2⟩ :=
    EnumerationSteps.add_execution program first (entry + 1) 5 5 0 p1 r1 (by omega)
      (by simpa [decrementCode] using present 1 (by simp))
  have l1 : first.liveWords = state.liveWords := by simp only [State.liveWords, h1, s1, o1]
  refine ⟨final, ?_, ?_, h2.trans h1, s2.trans s1, o2.trans o1, ?_, r2, ?_⟩
  · simpa only [l1, Nat.max_self, Nat.reduceAdd] using t1.append t2
  · rw [v2, v1, f1 5 (by decide), held,
      show (word width (capacity + 1)).val = capacity + 1 from Nat.mod_eq_of_lt fits,
      show (word width (2 ^ width - 1)).val = 2 ^ width - 1 from
        Nat.mod_eq_of_lt (by have := Nat.two_pow_pos width; omega)]
    exact decrement_word width capacity
  · simpa only [Nat.add_assoc, Nat.reduceAdd] using p2
  · intro i h0 h5; rw [f2 i h5, f1 i h0]

end Controller.Extensions.SupportFrame
