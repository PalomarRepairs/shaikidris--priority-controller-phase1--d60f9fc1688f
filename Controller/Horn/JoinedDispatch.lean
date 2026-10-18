module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Horn.RuleDispatch

@[expose] public section

/-!
# Same-program selection of normalized rule records

The selector stages preserve the caller's heap, output, stack and common
registers. The supported-row premise retains the dual-Horn boundary, while
separate record tags distinguish an inert rule, a headless rule and head zero.
-/
namespace Controller.Horn.JoinedDispatch

open Controller.Cost Controller.Horn.Worklist.IndexedNormalize
open Controller.Horn.RuleDispatch

/-- Concrete selector frames; no storage or control field is assumed free. -/
structure Common (before after : State width 8) : Prop where
  heap : after.heap = before.heap
  stack : after.stack = before.stack
  output : after.output = before.output
  zero : after.reg 2 = before.reg 2
  one : after.reg 5 = before.reg 5
  decrement : after.reg 6 = before.reg 6
  recordAddress : after.reg 7 = before.reg 7
  running : after.halted = before.halted

theorem Common.trans {first middle last : State width 8}
    (left : Common first middle) (right : Common middle last) : Common first last :=
  ⟨right.heap.trans left.heap, right.stack.trans left.stack, right.output.trans left.output,
    right.zero.trans left.zero, right.one.trans left.one, right.decrement.trans left.decrement,
    right.recordAddress.trans left.recordAddress, right.running.trans left.running⟩

theorem Common.liveWords {before after : State width 8} (frame : Common before after) :
    after.liveWords = before.liveWords := by
  simp only [State.liveWords, frame.heap, frame.stack, frame.output]

theorem flag_common (state : State width 8) (base : Nat) (flag : Bool) :
    Common state (flagFinished (n := n) state base flag) := by
  constructor <;> simp [flagFinished, State.put, State.advance]

theorem negative_common (state : State width 8) (base cursor : Nat) :
    Common state (negativeFinished (n := n) state base cursor) := by
  constructor <;> simp [negativeFinished, State.put, State.advance]

theorem compare_common (state : State width 8) (cursor limit : Nat) :
    Common state (Controller.Horn.RuleCopy.bodyTest state cursor limit) := by
  constructor <;> simp [Controller.Horn.RuleCopy.bodyTest, State.put, State.advance]

theorem branch_common (state : State width 8) (register : Fin 8) (target : Nat) :
    Common state (branchFinished state register target) := by
  unfold branchFinished
  split <;> constructor <;> rfl

theorem inert_common (state : State width 8) (exit : Nat) :
    Common state (tailFinished state exit 1 3 (word width 0) (word width 0)) := by
  constructor <;> simp [tailFinished, State.put, State.advance]

theorem positive_common (state : State width 8) (exit : Nat) :
    Common state (tailFinished state exit 3 1 (word width 0) (word width 1)) := by
  constructor <;> simp [tailFinished, State.put, State.advance]

theorem head_common (state : State width 8) (exit : Nat) (label : Fin n) :
    Common state (headFinished state exit label) := by
  constructor <;> simp [headFinished, State.put, State.advance]


/-- A physical tautology flag takes the six-instruction inert selector path.
Its scratch positive buffer may be nonempty; the selected rule has no body. -/
theorem inert_execution (program : Program width 8) (entry base exit pcur ncur tcur : Nat)
    (present : CodeAt program entry base exit n) (state : State width 8) (row : Row n)
    (stored : Controller.Horn.LiteralDispatch.RowStored row base pcur ncur tcur state.heap)
    (_supported : Supported row) (inert : row.tautology = true)
    (position : state.pc = word width entry) (zero : state.reg 2 = word width 0)
    (running : state.halted = false) (capacity : entry + 17 < 2 ^ width)
    (heapFits : state.heap.size < 2 ^ width) :
    ∃ final : State width 8,
      Execution program state final 6 state.liveWords ∧ Common state final ∧
      final.pc = word width exit ∧
      final.reg 1 = word width (Controller.Horn.RuleCopy.tag row.rule) ∧
      final.reg 3 = Controller.Horn.RuleCopy.headWord width row.rule := by
  let f := flagFinished (n := n) state base row.tautology
  let g := branchFinished f 1 (entry + 6)
  let final := tailFinished g exit 1 3 (word width 0) (word width 0)
  have fframe : Common state f := flag_common (n := n) state base row.tautology
  have gframe : Common f g := branch_common f 1 (entry + 6)
  have fpc : f.pc = word width (entry + 2) := flagFinished_position (n := n) state entry base _ position capacity
  have fheld : f.reg 1 = Controller.Horn.MarkStorage.encode width row.tautology := by
    simp [f, flagFinished, State.put]
  have gpc : g.pc = word width (entry + 3) := by
    simpa [inert] using flag_branch_position f entry row.tautology fpc fheld capacity
  have first := flag_execution program entry base exit pcur ncur tcur present state row stored
    position running capacity heapFits
  have second := branch_execution program (entry + 2) (entry + 6) 1
    (flag_branch_at program entry base exit present) f fpc (fframe.running.trans running) (by omega)
  have third := tail_execution program (entry + 3) exit 1 3 (word width 0) (word width 0)
    (inert_tail_at program entry base exit present) g gpc
    ((gframe.zero.trans fframe.zero).trans zero) (by decide) (by decide)
    ((gframe.running.trans fframe.running).trans running) (by omega)
  have trace := (first.append second).append third
  have frame := (fframe.trans gframe).trans (inert_common g exit)
  refine ⟨final, ?_, frame, rfl, ?_, ?_⟩
  · simpa [fframe.liveWords, gframe.liveWords] using trace
  · simp [final, tailFinished, State.put, State.advance, Row.rule, inert, Controller.Horn.RuleCopy.tag]
  · simp [final, tailFinished, State.put, State.advance, Row.rule, inert, Controller.Horn.RuleCopy.headWord]


/-- The active selector prefix reads both actual headers, compares the physical
cursor with its allocated endpoint, and reaches exactly one of the two tails. -/
theorem active_prefix_execution (program : Program width 8) (entry base exit pcur ncur tcur : Nat)
    (present : CodeAt program entry base exit n) (state : State width 8) (row : Row n)
    (stored : Controller.Horn.LiteralDispatch.RowStored row base pcur ncur tcur state.heap)
    (_supported : Supported row) (active : row.tautology = false)
    (position : state.pc = word width entry) (running : state.halted = false)
    (capacity : entry + 17 < 2 ^ width) (heapFits : state.heap.size < 2 ^ width) :
    ∃ final : State width 8,
      Execution program state final 8 state.liveWords ∧ Common state final ∧
      final.pc = word width (entry + if ncur = base + 4 * n + 4 then 14 else 11) ∧
      final.reg 0 = word width ncur ∧
      Controller.Horn.LiteralDispatch.RowStored row base pcur ncur tcur final.heap := by
  let f := flagFinished (n := n) state base row.tautology
  let g := branchFinished f 1 (entry + 6)
  let h := negativeFinished (n := n) g base ncur
  let i := Controller.Horn.RuleCopy.bodyTest h ncur (base + 4 * n + 4)
  let j := branchFinished i 1 (entry + 14)
  have ff : Common state f := flag_common (n := n) state base row.tautology
  have gf : Common f g := branch_common f 1 (entry + 6)
  have hf : Common g h := negative_common (n := n) g base ncur
  have inf : Common h i := compare_common h ncur (base + 4 * n + 4)
  have jf : Common i j := branch_common i 1 (entry + 14)
  have fg := ff.trans gf
  have fgh := fg.trans hf
  have fghi := fgh.trans inf
  have frame := fghi.trans jf
  have fpc : f.pc = word width (entry + 2) :=
    flagFinished_position (n := n) state entry base _ position capacity
  have fheld : f.reg 1 = Controller.Horn.MarkStorage.encode width row.tautology := by
    simp [f, flagFinished, State.put]
  have gpc : g.pc = word width (entry + 6) := by
    simpa [active] using flag_branch_position f entry row.tautology fpc fheld capacity
  have hpc : h.pc = word width (entry + 8) :=
    negativeFinished_position (n := n) g entry base ncur gpc capacity
  have ipc : i.pc = word width (entry + 10) := compare_position h entry ncur _ hpc capacity
  have hheld : h.reg 0 = word width ncur := by simp [h, negativeFinished, State.put]
  have iheld : i.reg 1 = word width (Nat.xor ncur (base + 4 * n + 4)) := by
    simp [i, Controller.Horn.RuleCopy.bodyTest, State.put]
  have cursorFits : ncur < 2 ^ width := by
    have := stored.negative.buffer.cursor_le_heap
    omega
  have limitFits : base + 4 * n + 4 < 2 ^ width := stored.negative.buffer.fits.trans_lt heapFits
  have storedG : Controller.Horn.LiteralDispatch.RowStored row base pcur ncur tcur g.heap := by
    rw [fg.heap]
    exact stored
  have t0 := flag_execution program entry base exit pcur ncur tcur present state row stored
    position running capacity heapFits
  have t1 := branch_execution program (entry + 2) (entry + 6) 1
    (flag_branch_at program entry base exit present) f fpc (ff.running.trans running) (by omega)
  have t2 := negative_execution program entry base exit pcur ncur tcur present g row storedG
    gpc (fg.running.trans running) capacity (by rw [fg.heap]; exact heapFits)
  have t3 := compare_execution program entry base exit ncur present h hpc hheld
    (fgh.running.trans running) capacity cursorFits limitFits
  have t4 := branch_execution program (entry + 10) (entry + 14) 1
    (negative_branch_at program entry base exit present) i ipc (fghi.running.trans running) (by omega)
  have trace := (((t0.append t1).append t2).append t3).append t4
  refine ⟨j, ?_, frame, ?_, ?_, ?_⟩
  · simpa [ff.liveWords, fg.liveWords, fgh.liveWords, fghi.liveWords] using trace
  · exact negative_branch_position i entry ncur _ ipc iheld capacity cursorFits limitFits
  · change (branchFinished i 1 (entry + 14)).reg 0 = _
    rw [(branchFinished_frame i 1 (entry + 14)).1]
    simp [i, Controller.Horn.RuleCopy.bodyTest, State.put, State.advance, hheld]
  · rw [frame.heap]
    exact stored


/-- The actual active selector always executes eleven instructions. Its headless
and headed tags are distinct even when the stored head is channel zero. -/
theorem active_execution (program : Program width 8) (entry base exit pcur ncur tcur : Nat)
    (present : CodeAt program entry base exit n) (state : State width 8) (row : Row n)
    (stored : Controller.Horn.LiteralDispatch.RowStored row base pcur ncur tcur state.heap)
    (supported : Supported row) (active : row.tautology = false)
    (position : state.pc = word width entry) (zero : state.reg 2 = word width 0)
    (running : state.halted = false) (capacity : entry + 17 < 2 ^ width)
    (heapFits : state.heap.size < 2 ^ width) :
    ∃ final : State width 8,
      Execution program state final 11 state.liveWords ∧ Common state final ∧
      final.pc = word width exit ∧
      final.reg 1 = word width (Controller.Horn.RuleCopy.tag row.rule) ∧
      final.reg 3 = Controller.Horn.RuleCopy.headWord width row.rule := by
  obtain ⟨middle, prefixTrace, frame, pc, cursor, storedMiddle⟩ :=
    active_prefix_execution program entry base exit pcur ncur tcur present state row stored
      supported active position running capacity heapFits
  cases negatives : row.negative with
  | nil =>
    have equal : ncur = base + 4 * n + 4 :=
      (negative_empty_iff row base pcur ncur tcur state.heap stored).mpr negatives
    have middlePC : middle.pc = word width (entry + 14) := by simpa [equal] using pc
    let final := tailFinished middle exit 3 1 (word width 0) (word width 1)
    have tail := tail_execution program (entry + 14) exit 3 1 (word width 0) (word width 1)
      (positive_tail_at program entry base exit present) middle middlePC (frame.zero.trans zero)
      (by decide) (by decide) (frame.running.trans running) (by omega)
    have trace := prefixTrace.append tail
    refine ⟨final, ?_, frame.trans (positive_common middle exit), rfl, ?_, ?_⟩
    · simpa [frame.liveWords] using trace
    · simp [final, tailFinished, State.put, State.advance, Row.rule, active, negatives, Controller.Horn.RuleCopy.tag]
    · simp [final, tailFinished, State.put, State.advance, Row.rule, active, negatives, Controller.Horn.RuleCopy.headWord]
  | cons label rest =>
    have different : ncur ≠ base + 4 * n + 4 := by
      intro equal
      have empty := (negative_empty_iff row base pcur ncur tcur state.heap stored).mp equal
      rw [negatives] at empty
      cases empty
    have middlePC : middle.pc = word width (entry + 11) := by simpa [different] using pc
    have labels : Controller.Horn.ResetTouched.LabelsStored (label :: rest) ncur middle.heap := by
      simpa [negatives] using storedMiddle.negative.buffer.labels
    let final := headFinished middle exit label
    have tail := head_execution program entry base exit ncur present middle label rest labels
      middlePC cursor (frame.zero.trans zero) (frame.running.trans running) capacity
      (by rw [frame.heap]; exact heapFits)
    have trace := prefixTrace.append tail
    refine ⟨final, ?_, frame.trans (head_common middle exit label), rfl, ?_, ?_⟩
    · simpa [frame.liveWords] using trace
    · simp [final, headFinished, State.put, State.advance, Row.rule, active, negatives, Controller.Horn.RuleCopy.tag]
    · simp [final, headFinished, State.put, State.advance, Row.rule, active, negatives, Controller.Horn.RuleCopy.headWord]

/-- Universal supported-row selector: six actual instructions for an inert row,
eleven for an active row, with the exact selected tag and physical head word. -/
theorem selection_execution (program : Program width 8) (entry base exit pcur ncur tcur : Nat)
    (present : CodeAt program entry base exit n) (state : State width 8) (row : Row n)
    (stored : Controller.Horn.LiteralDispatch.RowStored row base pcur ncur tcur state.heap)
    (supported : Supported row)
    (position : state.pc = word width entry) (zero : state.reg 2 = word width 0)
    (running : state.halted = false) (capacity : entry + 17 < 2 ^ width)
    (heapFits : state.heap.size < 2 ^ width) :
    ∃ final : State width 8,
      Execution program state final (if row.tautology then 6 else 11) state.liveWords ∧
      Common state final ∧ final.pc = word width exit ∧
      final.reg 1 = word width (Controller.Horn.RuleCopy.tag row.rule) ∧
      final.reg 3 = Controller.Horn.RuleCopy.headWord width row.rule := by
  cases flag : row.tautology
  · simpa [flag] using active_execution program entry base exit pcur ncur tcur present state row
      stored supported flag position zero running capacity heapFits
  · simpa [flag] using inert_execution program entry base exit pcur ncur tcur present state row
      stored supported flag position zero running capacity heapFits

end Controller.Horn.JoinedDispatch
