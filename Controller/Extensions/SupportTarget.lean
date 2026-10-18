module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedChannelStore
public import Controller.Cost.EnumerationSteps

public import Mathlib.Tactic.FinCases

@[expose] public section

/-! A temporary target-channel update saves the original word on the caller's
stack. Restoring it after candidate evaluation recovers the original mask,
including when the target was already selected. -/
namespace Controller.Extensions.SupportTarget
open Controller.Cost Controller.Cost.RawTransferLoops

def saveCode (width address : Nat) : List (Instruction width 8) :=
  [.constant 0 (word width address), .load 1 0, .push 1,
    .constant 1 (boolWord width true), .store 0 1]

def restoreCode (width address : Nat) : List (Instruction width 8) :=
  [.pop 1, .constant 0 (word width address), .store 0 1]

@[simp] theorem saveCode_length : (saveCode width address).length = 5 := rfl
@[simp] theorem restoreCode_length : (restoreCode width address).length = 3 := rfl

theorem save_execution (program : Program width 8) (state : State width 8)
    (entry address : Nat) (old : Word width)
    (stored : state.heap[address]? = some old)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 5 < 2 ^ width) (heapFits : state.heap.size < 2 ^ width)
    (present : SharedRootRead.BlockAt program entry (saveCode width address)) :
    ∃ final, Execution program state final 5 (state.liveWords + 1) ∧
      final.heap = state.heap.set address (boolWord width true)
        (Array.getElem?_eq_some_iff.mp stored).1 ∧
      final.stack = old :: state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry + 5) ∧ final.halted = false ∧
      (∀ i : Fin 8, i ≠ 0 → i ≠ 1 → final.reg i = state.reg i) := by
  have valid := (Array.getElem?_eq_some_iff.mp stored).1
  have cell := (Array.getElem?_eq_some_iff.mp stored).2
  have addressFits : address < 2 ^ width := by omega
  have addressVal : (word width address).val = address := Nat.mod_eq_of_lt addressFits
  obtain ⟨s1, t1, p1, v1, h1, st1, o1, r1, f1⟩ :=
    SharedEvaluationReclaim.constant_execution program entry address 0 state position running (by omega)
      (by simpa [saveCode] using present 0 (by simp))
  obtain ⟨s2, t2, p2, v2, h2, st2, o2, r2, f2⟩ :=
    EnumerationSteps.load_execution program s1 (entry + 1) 1 0 p1 r1 (by omega)
      (by simpa only [v1, addressVal, h1] using valid)
      (by simpa [saveCode] using present 1 (by simp))
  have oldHeld : s2.reg 1 = old := by
    calc
      s2.reg 1 = state.heap[address] := by simpa only [v1, addressVal, h1] using v2
      _ = old := cell
  obtain ⟨s3, t3, p3, h3, st3, o3, r3, f3, l3⟩ :=
    EnumerationSteps.push_execution program s2 (entry + 2) 1
      (by simpa [Nat.add_assoc] using p2) r2 (by omega)
      (by simpa [saveCode] using present 2 (by simp))
  obtain ⟨s4, t4, p4, v4, h4, st4, o4, r4, f4⟩ :=
    SharedEvaluationReclaim.constant_execution program (entry + 3) 1 1 s3 p3 r3 (by omega)
      (by simpa [saveCode, boolWord] using present 3 (by simp))
  obtain ⟨final, t5, h5, st5, o5, p5, r5, f5⟩ :=
    SharedChannelStore.execution program s4 (entry + 4) address (boolWord width true)
      (by simpa [Nat.add_assoc] using p4) r4 (by omega) addressFits
      (by simpa [h4, h3, h2, h1] using valid)
      (by rw [f4 0 (by decide), f3, f2 0 (by decide), v1])
      (by simpa [boolWord] using v4)
      (by intro i; fin_cases i; simpa [SharedChannelStore.code, saveCode] using present 4 (by simp))
  have l1 : s1.liveWords = state.liveWords := by simp only [State.liveWords, h1, st1, o1]
  have l2 : s2.liveWords = state.liveWords := by simp only [State.liveWords, h2, st2, o2, h1, st1, o1]
  have l4 : s4.liveWords = state.liveWords + 1 := by
    simp only [State.liveWords, h4, st4, o4, h3, st3, o3, oldHeld,
      h2, st2, o2, h1, st1, o1, List.length_cons]
    omega
  refine ⟨final, ?_, ?_, ?_, o5.trans (o4.trans (o3.trans (o2.trans o1))), ?_, r5, ?_⟩
  · simpa only [l1, l2, l3, l4, Nat.max_self, Nat.max_eq_right (Nat.le_succ _)] using
      t1.append (t2.append (t3.append (t4.append t5)))
  · simpa only [h4, h3, h2, h1] using h5
  · rw [st5, st4, st3, st2, st1, oldHeld]
  · simpa only [Nat.add_assoc, Nat.reduceAdd] using p5
  · intro i a b
    rw [f5, f4 i b, f3, f2 i b, f1 i a]

theorem restore_execution (program : Program width 8) (state : State width 8)
    (entry address : Nat) (original : Array (Word width)) (old : Word width)
    (rest : List (Word width)) (valid : address < original.size)
    (oldStored : original[address] = old)
    (heapStored : state.heap = original.set address (boolWord width true) valid)
    (saved : state.stack = old :: rest)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 3 < 2 ^ width) (heapFits : original.size < 2 ^ width)
    (present : SharedRootRead.BlockAt program entry (restoreCode width address)) :
    ∃ final, Execution program state final 3 state.liveWords ∧
      final.heap = original ∧ final.stack = rest ∧ final.output = state.output ∧
      final.pc = word width (entry + 3) ∧ final.halted = false ∧
      (∀ i : Fin 8, i ≠ 0 → i ≠ 1 → final.reg i = state.reg i) := by
  obtain ⟨s1, t1, p1, v1, h1, st1, o1, r1, f1⟩ :=
    EnumerationSteps.pop_execution program state entry 1 old rest position running (by omega) saved
      (by simpa [restoreCode] using present 0 (by simp))
  obtain ⟨s2, t2, p2, v2, h2, st2, o2, r2, f2⟩ :=
    SharedEvaluationReclaim.constant_execution program (entry + 1) address 0 s1 p1 r1 (by omega)
      (by simpa [restoreCode] using present 1 (by simp))
  obtain ⟨final, t3, h3, st3, o3, p3, r3, f3⟩ :=
    SharedChannelStore.execution program s2 (entry + 2) address old
      (by simpa [Nat.add_assoc] using p2) r2 (by omega) (by omega)
      (by simpa [h2, h1, heapStored] using valid) v2 ((f2 1 (by decide)).trans v1)
      (by intro i; fin_cases i; simpa [SharedChannelStore.code, restoreCode] using present 2 (by simp))
  have l1 : s1.liveWords + 1 = state.liveWords := by
    simp only [State.liveWords, h1, st1, o1, saved, List.length_cons]; omega
  have l2 : s2.liveWords = s1.liveWords := by simp only [State.liveWords, h2, st2, o2]
  refine ⟨final, ?_, ?_, st3.trans (st2.trans st1), o3.trans (o2.trans o1), ?_, r3, ?_⟩
  · simpa only [l2, Nat.max_self, Nat.max_eq_left (by omega : s1.liveWords ≤ state.liveWords)] using
      t1.append (t2.append t3)
  · have unchanged : original.set address old valid = original := by
      apply Array.ext
      · simp
      · intro i left right
        by_cases same : i = address
        · subst i; simpa using oldStored.symm
        · simp [Array.getElem_set, Ne.symm same]
    simpa only [h2, h1, heapStored, Array.set_set, unchanged] using h3
  · simpa only [Nat.add_assoc, Nat.reduceAdd] using p3
  · intro i a b
    rw [f3, f2 i a, f1 i b]

end Controller.Extensions.SupportTarget
