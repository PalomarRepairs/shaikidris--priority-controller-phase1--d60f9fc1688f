module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Extensions.SupportBranch

@[expose] public section

/-! A fixed instruction array traverses a bounded subset tree. Runtime masks
record the active children, and a two-word sentinel frame detects exhaustion.
The callback enters at the supplied address and returns to `backtrack` after
an unsuccessful query. A successful callback may leave the traversal directly. -/
namespace Controller.Extensions.SupportTraversal
open Controller.Cost Controller.Cost.RawTransferLoops Controller.Cost.SharedDetectorAssembly

def readCode (width base backtrack : Nat) : List (Instruction width 8) :=
  [.constant 0 (word width base), .add 0 0 3, .load 1 0, .branchZero 1 (word width backtrack)]

@[simp] theorem readCode_length : (readCode width base backtrack).length = 4 := rfl

theorem read_execution (program : Program width 8) (state : State width 8)
    (entry base backtrack cursor : Nat) (selected : Bool)
    (position : state.pc = word width entry) (running : state.halted = false)
    (cursorReg : state.reg 3 = word width cursor)
    (valid : base + cursor < state.heap.size) (heapFits : state.heap.size < 2 ^ width)
    (stored : state.heap[base + cursor] = boolWord width selected)
    (room : entry + 4 < 2 ^ width)
    (present : SharedRootRead.BlockAt program entry (readCode width base backtrack)) :
    ∃ final, Execution program state final 4 state.liveWords ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (if selected then entry + 4 else backtrack) ∧ final.halted = false ∧
      (∀ i : Fin 8, i ≠ 0 → i ≠ 1 → final.reg i = state.reg i) := by
  obtain ⟨s1, t1, p1, v1, h1, st1, o1, r1, f1⟩ :=
    SharedEvaluationReclaim.constant_execution program entry base 0 state position running (by omega)
      (by simpa [readCode] using present 0 (by simp))
  obtain ⟨s2, t2, p2, v2, h2, st2, o2, r2, f2⟩ :=
    EnumerationSteps.add_execution program s1 (entry + 1) 0 0 3 p1 r1 (by omega)
      (by simpa [readCode] using present 1 (by simp))
  have address : (s2.reg 0).val = base + cursor := by
    rw [v2, v1, f1 3 (by decide), cursorReg]
    simp only [word, Nat.mod_eq_of_lt (by omega : base < 2 ^ width),
      Nat.mod_eq_of_lt (by omega : cursor < 2 ^ width), Nat.mod_eq_of_lt (by omega : base + cursor < 2 ^ width)]
  obtain ⟨s3, t3, p3, v3, h3, st3, o3, r3, f3⟩ :=
    EnumerationSteps.load_execution program s2 (entry + 1 + 1) 1 0 p2 r2 (by omega)
      (by rw [address, h2, h1]; exact valid)
      (by simpa [readCode] using present 2 (by simp))
  have bit : (s3.reg 1).val = if selected then 1 else 0 := by
    rw [v3]
    have inside : (s2.reg 0).val < s2.heap.size := by rw [address, h2, h1]; exact valid
    have cell : s2.heap[(s2.reg 0).val]'inside = boolWord width selected := by
      simpa only [address, h2, h1] using stored
    rw [cell]
    cases selected <;> simp [boolWord, word, Nat.mod_eq_of_lt (by omega : 1 < 2 ^ width)]
  have branchAt : program[entry + 1 + 1 + 1]? = some (.branchZero 1 (word width backtrack)) := by
    simpa [readCode] using present 3 (by simp)
  have branch : ∃ final, Execution program s3 final 1 s3.liveWords ∧
      final.pc = word width (if selected then entry + 4 else backtrack) ∧
      final.heap = s3.heap ∧ final.stack = s3.stack ∧ final.output = s3.output ∧
      final.halted = false ∧ (∀ i, final.reg i = s3.reg i) := by
    cases selected with
    | false =>
        exact EnumerationSteps.branch_taken program s3 (entry + 1 + 1 + 1) backtrack 1 p3 r3
          (by omega) bit branchAt
    | true =>
        simpa only [ite_eq_left rfl, ite_true, Nat.add_assoc, Nat.reduceAdd] using
          EnumerationSteps.branch_skipped program s3 (entry + 1 + 1 + 1) backtrack 1 p3 r3
            (by omega) (by rw [bit]; decide) branchAt
  obtain ⟨final, t4, p4, h4, st4, o4, r4, f4⟩ := branch
  have l1 : s1.liveWords = state.liveWords := by simp only [State.liveWords, h1, st1, o1]
  have l2 : s2.liveWords = state.liveWords := by simp only [State.liveWords, h2, st2, o2, h1, st1, o1]
  have l3 : s3.liveWords = state.liveWords := by simp only [State.liveWords, h3, st3, o3, h2, st2, o2, h1, st1, o1]
  refine ⟨final, ?_, h4.trans (h3.trans (h2.trans h1)), st4.trans (st3.trans (st2.trans st1)),
    o4.trans (o3.trans (o2.trans o1)), p4, r4, ?_⟩
  · simpa only [l1, l2, l3, Nat.max_self, Nat.reduceAdd] using t1.append (t2.append (t3.append t4))
  · intro i h0 h1; rw [f4, f3 i h1, f2 i h0, f1 i h0]

def returnCode (width limit base backtrack done : Nat) : List (Instruction width 8) :=
  SupportFrame.restoreCode width ++
    ((SharedTagCompare.code width done limit 3).toList ++ readCode width base backtrack)

@[simp] theorem returnCode_length : (returnCode width limit base backtrack done).length = 9 := rfl

/-- Returning from an internal node releases its frame and reads the parent's
mask cell. A zero cell continues backtracking; a one cell selects the sibling. -/
theorem return_execution (program : Program width 8) (state : State width 8)
    (entry limit base backtrack done cursor capacity : Nat) (rest : List (Word width)) (selected : Bool)
    (position : state.pc = word width entry) (running : state.halted = false)
    (saved : state.stack = word width cursor :: word width capacity :: rest)
    (lower : cursor < limit) (limitFits : limit < 2 ^ width)
    (valid : base + cursor < state.heap.size) (heapFits : state.heap.size < 2 ^ width)
    (stored : state.heap[base + cursor] = boolWord width selected)
    (room : entry + 9 < 2 ^ width)
    (present : SharedRootRead.BlockAt program entry (returnCode width limit base backtrack done)) :
    ∃ final, Execution program state final 9 state.liveWords ∧
      final.heap = state.heap ∧ final.stack = rest ∧ final.output = state.output ∧
      final.pc = word width (if selected then entry + 9 else backtrack) ∧ final.halted = false ∧
      final.reg 3 = word width cursor ∧ final.reg 5 = word width capacity ∧
      (∀ i : Fin 8, i ≠ 0 → i ≠ 1 → i ≠ 3 → i ≠ 5 → final.reg i = state.reg i) ∧
      final.liveWords + 2 = state.liveWords := by
  have restoreAt := block_left program entry _ _ present
  have afterAt := block_right program entry _ _ present
  change SharedRootRead.BlockAt program (entry + 2)
    ((SharedTagCompare.code width done limit 3).toList ++ readCode width base backtrack) at afterAt
  have compareAt := block_left program (entry + 2) _ _ afterAt
  have readAt := block_right program (entry + 2) _ _ afterAt
  obtain ⟨s1, t1, h1, st1, o1, p1, r1, c1, b1, f1, l1⟩ :=
    SupportFrame.restore_execution program state entry cursor capacity rest position running (by omega) saved restoreAt
  obtain ⟨s2, t2, h2, st2, o2, p2, r2, f2⟩ :=
    SharedTagCompare.execution program s1 (entry + 2) done limit cursor 3 (by decide) p1 r1 (by omega)
      limitFits (by omega) c1 (block_code _ _ _ compareAt)
  have pc2 : s2.pc = word width (entry + 2 + 3) := by simpa only [ite_eq_right (by omega : cursor ≠ limit)] using p2
  obtain ⟨final, t3, h3, st3, o3, p3, r3, f3⟩ :=
    read_execution program s2 (entry + 2 + 3) base backtrack cursor selected pc2 r2
      ((f2 3 (by decide)).trans c1) (by simpa only [h2, h1] using valid)
      (by simpa only [h2, h1] using heapFits) (by simpa only [h2, h1] using stored) (by omega) readAt
  have l2 : s2.liveWords = s1.liveWords := by simp only [State.liveWords, h2, st2, o2]
  refine ⟨final, ?_, h3.trans (h2.trans h1), st3.trans (st2.trans st1), o3.trans (o2.trans o1),
    ?_, r3, ?_, ?_, ?_, ?_⟩
  · simpa only [l2, Nat.max_self, Nat.max_eq_left (by omega : s1.liveWords ≤ state.liveWords),
      Nat.reduceAdd] using t1.append (t2.append t3)
  · simpa only [Nat.add_assoc, Nat.reduceAdd] using p3
  · rw [f3 3 (by decide) (by decide), f2 3 (by decide), c1]
  · rw [f3 5 (by decide) (by decide), f2 5 (by decide), b1]
  · intro i h0 h1 h3 h5; rw [f3 i h0 h1, f2 i h0, f1 i h3 h5]
  · simpa only [State.liveWords, h3, st3, o3, h2, st2, o2] using l1

/-- The sentinel is tested before any mask access, including for an empty ID
list. Exhaustion consumes precisely the sentinel frame and preserves the caller. -/
theorem exhausted_execution (program : Program width 8) (state : State width 8)
    (entry limit base backtrack done : Nat) (rest : List (Word width))
    (position : state.pc = word width entry) (running : state.halted = false)
    (saved : state.stack = word width limit :: word width 0 :: rest)
    (limitFits : limit < 2 ^ width) (room : entry + 5 < 2 ^ width)
    (present : SharedRootRead.BlockAt program entry (returnCode width limit base backtrack done)) :
    ∃ final, Execution program state final 5 state.liveWords ∧
      final.heap = state.heap ∧ final.stack = rest ∧ final.output = state.output ∧
      final.pc = word width done ∧ final.halted = false ∧ final.liveWords + 2 = state.liveWords := by
  have restoreAt := block_left program entry _ _ present
  have afterAt := block_right program entry _ _ present
  have compareAt := block_left program (entry + 2) _ _ afterAt
  obtain ⟨s1, t1, h1, st1, o1, p1, r1, c1, _, _, l1⟩ :=
    SupportFrame.restore_execution program state entry limit 0 rest position running (by omega) saved restoreAt
  obtain ⟨final, t2, h2, st2, o2, p2, r2, _⟩ :=
    SharedTagCompare.execution program s1 (entry + 2) done limit limit 3 (by decide) p1 r1 (by omega)
      limitFits limitFits c1 (block_code _ _ _ compareAt)
  refine ⟨final, ?_, h2.trans h1, st2.trans st1, o2.trans o1, by simpa using p2, r2, ?_⟩
  · simpa only [Nat.max_eq_left (by omega : s1.liveWords ≤ state.liveWords), Nat.reduceAdd] using t1.append t2
  · simpa only [State.liveWords, h2, st2, o2] using l1

def backtrack (entry : Nat) : Nat := entry + 16
def done (entry : Nat) : Nat := entry + 35

/-- Thirty-six instructions, independent of the number of visited subsets. -/
def code (width entry limit base query : Nat) : List (Instruction width 8) :=
  SupportBranch.dispatchCode width limit query ++
    (SupportBranch.childCode width base entry true ++
      (returnCode width limit base (backtrack entry) (done entry) ++
        (SupportBranch.childCode width base entry false ++ [.halt])))

@[simp] theorem code_length : (code width entry limit base query).length = 36 := by
  simp [code]

@[simp] theorem code_words : programWords (code width entry limit base query).toArray = 144 := by
  simp [programWords]

theorem blocks (program : Program width 8) (entry limit base query : Nat)
    (present : SharedRootRead.BlockAt program entry (code width entry limit base query)) :
    SharedRootRead.BlockAt program entry (SupportBranch.dispatchCode width limit query) ∧
    SharedRootRead.BlockAt program (entry + 4) (SupportBranch.childCode width base entry true) ∧
    SharedRootRead.BlockAt program (backtrack entry)
      (returnCode width limit base (backtrack entry) (done entry)) ∧
    SharedRootRead.BlockAt program (entry + 25) (SupportBranch.childCode width base entry false) ∧
    program[done entry]? = some .halt := by
  have first := block_left program entry _ _ present
  have rest := block_right program entry _ _ present
  simp only [SupportBranch.dispatchCode_length] at rest
  have second := block_left program (entry + 4) _ _ rest
  have rest := block_right program (entry + 4) _ _ rest
  simp only [SupportBranch.childCode_length, Nat.add_assoc] at rest
  have third := block_left program (entry + 16) _ _ rest
  have rest := block_right program (entry + 16) _ _ rest
  simp only [returnCode_length, Nat.add_assoc, Nat.reduceAdd] at rest
  have fourth := block_left program (entry + 25) _ _ rest
  have last := block_right program (entry + 25) _ _ rest
  simp only [SupportBranch.childCode_length, Bool.false_eq_true, ite_false, Nat.zero_add,
    Nat.add_assoc, Nat.reduceAdd] at last
  refine ⟨first, second, third, fourth, ?_⟩
  have found := last 0 (by simp)
  change program[entry + 35 + 0]? = some .halt at found
  simpa only [done, Nat.add_zero] using found

/-- The same core may return to a caller instead of halting on exhaustion. -/
def endingCode (width entry limit base query : Nat) (ending : Instruction width 8) : List (Instruction width 8) :=
  SupportBranch.dispatchCode width limit query ++
    (SupportBranch.childCode width base entry true ++
      (returnCode width limit base (backtrack entry) (done entry) ++
        (SupportBranch.childCode width base entry false ++ [ending])))

@[simp] theorem endingCode_length : (endingCode width entry limit base query ending).length = 36 := by
  simp [endingCode]

theorem ending_blocks (program : Program width 8) (entry limit base query : Nat) (ending : Instruction width 8)
    (present : SharedRootRead.BlockAt program entry (endingCode width entry limit base query ending)) :
    SharedRootRead.BlockAt program entry (SupportBranch.dispatchCode width limit query) ∧
    SharedRootRead.BlockAt program (entry+4) (SupportBranch.childCode width base entry true) ∧
    SharedRootRead.BlockAt program (backtrack entry) (returnCode width limit base (backtrack entry) (done entry)) ∧
    SharedRootRead.BlockAt program (entry+25) (SupportBranch.childCode width base entry false) ∧
    program[done entry]? = some ending := by
  unfold endingCode at present
  have first := block_left program entry _ _ present
  have rest := block_right program entry _ _ present
  simp only [SupportBranch.dispatchCode_length] at rest
  have second := block_left program (entry+4) _ _ rest
  have rest := block_right program (entry+4) _ _ rest
  simp only [SupportBranch.childCode_length, Nat.add_assoc] at rest
  have third := block_left program (entry+16) _ _ rest
  have rest := block_right program (entry+16) _ _ rest
  simp only [returnCode_length, Nat.add_assoc, Nat.reduceAdd] at rest
  have fourth := block_left program (entry+25) _ _ rest
  have last := block_right program (entry+25) _ _ rest
  simp only [SupportBranch.childCode_length, Bool.false_eq_true, ite_false, Nat.zero_add,
    Nat.add_assoc, Nat.reduceAdd] at last
  exact ⟨first, second, third, fourth, by simpa [done] using last 0 (by simp)⟩

end Controller.Extensions.SupportTraversal
