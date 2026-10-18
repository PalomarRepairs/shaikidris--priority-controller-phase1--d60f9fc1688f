module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.UniformDAGRightRead

@[expose] public section

/-! Complete live-AND execution uses cached left and right identifiers and
stored Boolean values. The fixed program appends its result to the node table. -/
namespace Controller.Cost.UniformDAGAndGate
open Controller.Cost.GateProgram

def code (width base headBase sourceBase : ℕ) : Code width :=
  UniformDAGHeadRead.code width headBase ++
    (UniformDAGRightRead.code width sourceBase ++ UniformDAGAndFinish.code width (base + 13))
@[simp] theorem code_length : (code width base headBase sourceBase).length = 16 := rfl
@[simp] theorem code_words : 4 * (code width base headBase sourceBase).length = 64 := rfl

theorem execution (program : Program width 4) (s : State width 4)
    (base headBase sourceBase valueBase offset cursor leftID rightID : ℕ) (left right : Bool)
    (offsetHeld : s.reg 3 = word width offset) (valueHeld : s.reg 1 = word width valueBase)
    (headFits : headBase + offset < 2 ^ width)
    (sourceFits : sourceBase + offset < 2 ^ width) (cursorFits : cursor + 1 < 2 ^ width)
    (leftFits : valueBase + leftID < 2 ^ width) (rightFits : valueBase + rightID < 2 ^ width)
    (headBound : headBase + offset < s.heap.size)
    (sourceBound : sourceBase + offset < s.heap.size) (cursorBound : cursor + 1 < s.heap.size)
    (leftBound : valueBase + leftID < s.heap.size) (rightBound : valueBase + rightID < s.heap.size)
    (headCell : s.heap[headBase + offset]'headBound = word width leftID)
    (sourceCell : s.heap[sourceBase + offset]'sourceBound = word width cursor)
    (rightCell : s.heap[cursor + 1]'cursorBound = word width rightID)
    (leftValue : s.heap[valueBase + leftID]'leftBound = boolWord width left)
    (rightValue : s.heap[valueBase + rightID]'rightBound = boolWord width right)
    (pc : s.pc = word width base) (running : s.halted = false)
    (fits : base + 16 < 2 ^ width) (room : s.heap.size < 2 ^ width)
    (block : BlockAt program base (code width base headBase sourceBase)) :
    ∃ final, Execution program s final (if left then 16 else 15) (s.liveWords + 1) ∧
      final.reg 2 = boolWord width (left && right) ∧ final.reg 3 = word width (cursor + 1) ∧
      final.heap = s.heap.push (boolWord width (left && right)) ∧
      final.stack = s.stack ∧ final.output = s.output ∧
      final.pc = word width (base + 16) ∧ final.halted = false := by
  have headBlock := BlockAt.prefix program base (UniformDAGHeadRead.code width headBase)
    (UniformDAGRightRead.code width sourceBase ++ UniformDAGAndFinish.code width (base + 13)) block
  have tailBlock : BlockAt program (base + 5)
      (UniformDAGRightRead.code width sourceBase ++ UniformDAGAndFinish.code width (base + 13)) := by
    simpa only [UniformDAGHeadRead.code_length] using BlockAt.suffix program base
      (UniformDAGHeadRead.code width headBase) _ block
  have rightBlock := BlockAt.prefix program (base + 5) (UniformDAGRightRead.code width sourceBase)
    (UniformDAGAndFinish.code width (base + 13)) tailBlock
  have finishBlock : BlockAt program (base + 13) (UniformDAGAndFinish.code width (base + 13)) := by
    simpa only [UniformDAGRightRead.code_length, Nat.add_assoc] using BlockAt.suffix program
      (base + 5) (UniformDAGRightRead.code width sourceBase) _ tailBlock
  obtain ⟨head, ht, h0, h1, h2, h3, hh, hs, ho, hp, hr⟩ :=
    UniformDAGHeadRead.execution program s base headBase valueBase offset leftID left
      offsetHeld valueHeld headFits leftFits headBound leftBound headCell leftValue pc running
      (by omega) headBlock
  have hl : head.liveWords = s.liveWords := by simp [State.liveWords, hh, hs, ho]
  obtain ⟨loaded, rt, r0, r1, r2, r3, rh, rs, ro, rp, rr⟩ :=
    UniformDAGRightRead.execution program head (base + 5) sourceBase valueBase offset cursor rightID right
      (h3.trans offsetHeld) (h1.trans valueHeld) sourceFits cursorFits rightFits
      (by simpa [hh] using sourceBound) (by simpa [hh] using cursorBound)
      (by simpa [hh] using rightBound) (by simpa [hh] using sourceCell)
      (by simpa [hh] using rightCell) (by simpa [hh] using rightValue) hp hr
      (by omega) rightBlock
  have rl : loaded.liveWords = s.liveWords := by simp [State.liveWords, rh, rs, ro, hh, hs, ho]
  have loadedPC : loaded.pc = word width (base + 13) := by simpa [Nat.add_assoc] using rp
  obtain ⟨final, ft, f2, f3, fh, fs, fo, fp, fr⟩ :=
    UniformDAGAndFinish.execution program loaded (base + 13) left right (r2.trans h2) r0
      loadedPC rr (by omega) (by simpa [rh, hh] using room) finishBlock
  refine ⟨final, ?_, f2, f3.trans r3, ?_, fs.trans (rs.trans hs), fo.trans (ro.trans ho), ?_, fr⟩
  · have trace := (ht.append rt).append ft
    cases left <;> simpa [hl, rl, Nat.max_eq_right (by omega : s.liveWords ≤ s.liveWords + 1)] using trace
  · simpa [rh, hh] using fh
  · simpa [Nat.add_assoc] using fp

end Controller.Cost.UniformDAGAndGate
