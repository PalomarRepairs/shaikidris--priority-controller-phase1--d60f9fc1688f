module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Extensions.SupportFrame
public import Controller.Cost.EnumerationMaskWrite
public import Controller.Cost.SharedDetectorAssembly

@[expose] public section

/-! Fetched branch control for bounded-subset search. Both children share the
same source and mask array. The included child spends one capacity unit; the
excluded child retains its parent's capacity. Each descent saves two words. -/
namespace Controller.Extensions.SupportBranch
open Controller.Cost Controller.Cost.RawTransferLoops Controller.Cost.SharedDetectorAssembly

def jump (width target : Nat) : List (Instruction width 8) :=
  [.constant 0 (word width 0), .branchZero 0 (word width target)]

def spendCode (width : Nat) (selected : Bool) : List (Instruction width 8) :=
  if selected then SupportFrame.decrementCode width else []

@[simp] theorem spendCode_length :
    (spendCode width selected).length = if selected then 2 else 0 := by
  cases selected <;> rfl

private theorem spend_execution (program : Program width 8) (state : State width 8)
    (entry capacity : Nat) (selected : Bool) (position : state.pc = word width entry)
    (running : state.halted = false)
    (held : state.reg 5 = word width (capacity + if selected then 1 else 0))
    (fits : capacity + (if selected then 1 else 0) < 2 ^ width)
    (room : entry + (spendCode width selected).length < 2 ^ width)
    (present : SharedRootRead.BlockAt program entry (spendCode width selected)) :
    ∃ final, Execution program state final (spendCode width selected).length state.liveWords ∧
      final.reg 5 = word width capacity ∧ final.heap = state.heap ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry + (spendCode width selected).length) ∧ final.halted = false ∧
      (∀ i : Fin 8, i ≠ 0 → i ≠ 5 → final.reg i = state.reg i) := by
  cases selected with
  | false => exact ⟨state, Execution.refl _, by simpa using held, rfl, rfl, rfl,
      by simpa [spendCode] using position, running, fun _ _ _ => rfl⟩
  | true =>
      exact SupportFrame.decrement_execution program state entry capacity position running
        held fits room present

def advanceCode (width next : Nat) (selected : Bool) : List (Instruction width 8) :=
  spendCode width selected ++ (EnumerationCounter.code width 1 ++ jump width next)

@[simp] theorem advanceCode_length :
    (advanceCode width next selected).length = (if selected then 2 else 0) + 4 := by
  simp [advanceCode, jump]

theorem advance_execution (program : Program width 8) (state : State width 8)
    (entry next cursor capacity : Nat) (selected : Bool)
    (position : state.pc = word width entry) (running : state.halted = false)
    (cursorReg : state.reg 3 = word width cursor)
    (capacityReg : state.reg 5 = word width (capacity + if selected then 1 else 0))
    (cursorFits : cursor + 1 < 2 ^ width)
    (capacityFits : capacity + (if selected then 1 else 0) < 2 ^ width)
    (room : entry + (advanceCode width next selected).length < 2 ^ width)
    (present : SharedRootRead.BlockAt program entry (advanceCode width next selected)) :
    ∃ final, Execution program state final (advanceCode width next selected).length state.liveWords ∧
      final.reg 3 = word width (cursor + 1) ∧ final.reg 5 = word width capacity ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width next ∧ final.halted = false ∧
      (∀ i : Fin 8, i ≠ 0 → i ≠ 3 → i ≠ 5 → final.reg i = state.reg i) := by
  let spent := (spendCode width selected).length
  have spendAt := block_left program entry _ _ present
  have afterAt := block_right program entry _ _ present
  change SharedRootRead.BlockAt program (entry + spent)
    (EnumerationCounter.code width 1 ++ jump width next) at afterAt
  have incrementAt := block_left program (entry + spent) _ _ afterAt
  have jumpAt := block_right program (entry + spent) _ _ afterAt
  have length : (advanceCode width next selected).length = spent + 4 := by
    simp [advanceCode, spent, jump]
  obtain ⟨s1, t1, c1, h1, st1, o1, p1, r1, f1⟩ :=
    spend_execution program state entry capacity selected position running capacityReg capacityFits
      (by omega) spendAt
  obtain ⟨s2, t2, c2, h2, st2, o2, p2, r2, f2⟩ :=
    EnumerationCounter.increment_execution program s1 (entry + spent) cursor p1 r1
      ((f1 3 (by decide) (by decide)).trans cursorReg) cursorFits (by omega) incrementAt
  obtain ⟨final, t3, p3, h3, st3, o3, r3, f3⟩ :=
    EnumerationSteps.jump_execution program s2 (entry + spent + 2) next p2 r2 (by omega)
      (by simpa [jump] using jumpAt 0 (by simp [jump]))
      (by simpa [jump] using jumpAt 1 (by simp [jump]))
  have l1 : s1.liveWords = state.liveWords := by simp only [State.liveWords, h1, st1, o1]
  have l2 : s2.liveWords = state.liveWords := by simp only [State.liveWords, h2, st2, o2, h1, st1, o1]
  refine ⟨final, ?_, (f3 3 (by decide)).trans c2,
    (f3 5 (by decide)).trans ((f2 5 (by decide) (by decide)).trans c1),
    h3.trans (h2.trans h1), st3.trans (st2.trans st1), o3.trans (o2.trans o1), p3, r3, ?_⟩
  · simpa only [length, l1, l2, Nat.max_self, Nat.add_assoc, Nat.reduceAdd] using
      t1.append (t2.append t3)
  · intro i h0 h3 h5; rw [f3 i h0, f2 i h0 h3, f1 i h0 h5]

def childCode (width base next : Nat) (selected : Bool) : List (Instruction width 8) :=
  EnumerationMaskWrite.code width base selected ++
    (SupportFrame.saveCode width ++ advanceCode width next selected)

@[simp] theorem childCode_length :
    (childCode width base next selected).length = (if selected then 2 else 0) + 10 := by
  simp [childCode]; omega

/-- A genuine fetched descent updates one mask cell, saves the parent cursor
and budget, and enters the child. The source frame and previous output survive. -/
theorem child_execution (program : Program width 8) (state : State width 8)
    (entry base next cursor capacity : Nat) (selected : Bool)
    (position : state.pc = word width entry) (running : state.halted = false)
    (cursorReg : state.reg 3 = word width cursor)
    (capacityReg : state.reg 5 = word width (capacity + if selected then 1 else 0))
    (cursorFits : cursor + 1 < 2 ^ width)
    (capacityFits : capacity + (if selected then 1 else 0) < 2 ^ width)
    (valid : base + cursor < state.heap.size) (heapFits : state.heap.size < 2 ^ width)
    (room : entry + (childCode width base next selected).length < 2 ^ width)
    (present : SharedRootRead.BlockAt program entry (childCode width base next selected)) :
    ∃ final, Execution program state final (childCode width base next selected).length (state.liveWords + 2) ∧
      final.heap = state.heap.set (base + cursor) (boolWord width selected) valid ∧
      final.stack = word width cursor ::
        word width (capacity + if selected then 1 else 0) :: state.stack ∧
      final.output = state.output ∧ final.pc = word width next ∧ final.halted = false ∧
      final.reg 3 = word width (cursor + 1) ∧ final.reg 5 = word width capacity ∧
      (∀ i : Fin 8, i ≠ 0 → i ≠ 1 → i ≠ 3 → i ≠ 5 → final.reg i = state.reg i) ∧
      final.liveWords = state.liveWords + 2 := by
  have writeAt := block_left program entry _ _ present
  have afterAt := block_right program entry _ _ present
  change SharedRootRead.BlockAt program (entry + 4)
    (SupportFrame.saveCode width ++ advanceCode width next selected) at afterAt
  have saveAt := block_left program (entry + 4) _ _ afterAt
  have advanceAt := block_right program (entry + 4) _ _ afterAt
  have length : (childCode width base next selected).length =
      6 + (advanceCode width next selected).length := by simp [childCode]; omega
  obtain ⟨s1, t1, h1, st1, o1, p1, r1, f1⟩ :=
    EnumerationMaskWrite.execution program state entry base cursor selected position running cursorReg valid
      heapFits (by rw [childCode_length] at room; split at room <;> omega) writeAt
  have c1 : s1.reg 3 = word width cursor := (f1 3 (by decide) (by decide)).trans cursorReg
  have b1 : s1.reg 5 = word width (capacity + if selected then 1 else 0) :=
    (f1 5 (by decide) (by decide)).trans capacityReg
  obtain ⟨s2, t2, h2, st2, o2, p2, r2, f2, l2⟩ :=
    SupportFrame.save_execution program s1 (entry + 4) p1 r1 (by omega) saveAt
  obtain ⟨final, t3, c3, b3, h3, st3, o3, p3, r3, f3⟩ :=
    advance_execution program s2 (entry + 4 + 2) next cursor capacity selected p2 r2
      ((f2 3).trans c1) ((f2 5).trans b1) cursorFits capacityFits (by omega) advanceAt
  have l1 : s1.liveWords = state.liveWords := by simp only [State.liveWords, h1, st1, o1, Array.size_set]
  refine ⟨final, ?_, h3.trans (h2.trans h1), ?_, o3.trans (o2.trans o1), p3, r3, c3, b3, ?_, ?_⟩
  · simpa only [length, l2, l1, Nat.max_self, Nat.max_eq_right (by omega :
      state.liveWords ≤ state.liveWords + 2), ← Nat.add_assoc, Nat.reduceAdd] using t1.append (t2.append t3)
  · rw [st3, st2, c1, b1, st1]
  · intro i h0 h1 h3 h5; rw [f3 i h0 h3 h5, f2, f1 i h0 h1]
  · simp only [State.liveWords, h3, h2, h1, st3, st2, st1, o3, o2, o1,
      Array.size_set, List.length_cons]; omega

def dispatchCode (width limit query : Nat) : List (Instruction width 8) :=
  [.branchZero 5 (word width query)] ++ (SharedTagCompare.code width query limit 3).toList

@[simp] theorem dispatchCode_length : (dispatchCode width limit query).length = 4 := rfl

/-- Zero remaining capacity and exhaustion of the ID list both enter the same
callback. Otherwise control falls through to the included-child block. -/
theorem dispatch_execution (program : Program width 8) (state : State width 8)
    (entry limit query cursor capacity : Nat)
    (position : state.pc = word width entry) (running : state.halted = false)
    (cursorReg : state.reg 3 = word width cursor) (capacityReg : state.reg 5 = word width capacity)
    (cursorFits : cursor < 2 ^ width) (capacityFits : capacity < 2 ^ width)
    (limitFits : limit < 2 ^ width) (room : entry + 4 < 2 ^ width)
    (present : SharedRootRead.BlockAt program entry (dispatchCode width limit query)) :
    ∃ final ticks, Execution program state final ticks state.liveWords ∧ ticks ≤ 4 ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (if capacity = 0 ∨ cursor = limit then query else entry + 4) ∧
      final.halted = false ∧ (∀ i : Fin 8, i ≠ 0 → final.reg i = state.reg i) := by
  have firstAt : program[entry]? = some (.branchZero 5 (word width query)) := by
    have found := present 0 (by simp)
    change program[entry + 0]? = some (.branchZero 5 (word width query)) at found
    simpa only [Nat.add_zero] using found
  by_cases empty : capacity = 0
  · obtain ⟨final, trace, pc, heap, stack, output, active, frame⟩ :=
      EnumerationSteps.branch_taken program state entry query 5 position running (by omega)
        (by rw [capacityReg, empty]; simp [word]) firstAt
    exact ⟨final, 1, trace, by decide, heap, stack, output, by simpa [empty] using pc,
      active, fun i _ => frame i⟩
  · obtain ⟨s1, t1, p1, h1, st1, o1, r1, f1⟩ :=
      EnumerationSteps.branch_skipped program state entry query 5 position running (by omega)
        (by rw [capacityReg, show (word width capacity).val = capacity from Nat.mod_eq_of_lt capacityFits]; exact empty)
        firstAt
    have afterAt := block_right program entry _ _ present
    change SharedRootRead.BlockAt program (entry + 1) (SharedTagCompare.code width query limit 3).toList at afterAt
    obtain ⟨final, t2, h2, st2, o2, p2, r2, f2⟩ :=
      SharedTagCompare.execution program s1 (entry + 1) query limit cursor 3 (by decide) p1 r1 (by omega)
        limitFits cursorFits ((f1 3).trans cursorReg) (block_code _ _ _ afterAt)
    have l1 : s1.liveWords = state.liveWords := by simp only [State.liveWords, h1, st1, o1]
    refine ⟨final, 4, ?_, by decide, h2.trans h1, st2.trans st1, o2.trans o1, ?_, r2, ?_⟩
    · simpa only [l1, Nat.max_self, Nat.reduceAdd] using t1.append t2
    · simpa only [empty, false_or, Nat.add_assoc, Nat.reduceAdd] using p2
    · intro i h0; rw [f2 i h0, f1]

end Controller.Extensions.SupportBranch
