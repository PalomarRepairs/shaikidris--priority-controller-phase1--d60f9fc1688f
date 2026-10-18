module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.UniformDAGAndGate

public import Mathlib.Tactic.FinCases

@[expose] public section

/-! Literal-sign propagation through a stored guard. The fetched child value is
joined with every stored guard-label value by Boolean union. -/
namespace Controller.Cost.LiteralGuardUnion
open Controller.Cost.GateProgram Controller.Cost.UniformDAGScan

def code (width base headBase channelBase arityBase sourceBase : ℕ) : Code width :=
  UniformDAGHeadRead.code width headBase ++
    ([.constant 1 (word width channelBase)] ++
      UniformDAGGateScan.code width (base + 6) arityBase sourceBase true)
@[simp] theorem code_length : (code width base headBase channelBase arityBase sourceBase).length = 32 := rfl

private theorem canonical (s : State width 4) (pc : ℕ) (r0 r1 r2 r3 : Word width)
    (zero : s.reg 0 = r0) (one : s.reg 1 = r1) (two : s.reg 2 = r2) (three : s.reg 3 = r3)
    (position : s.pc = word width pc) (running : s.halted = false) :
    s = state s.heap pc r0 r1 r2 r3 s.stack s.output := by
  rcases s with ⟨registers, heap, stack, output, cursor, halted⟩
  simp only [state, State.mk.injEq]
  refine ⟨?_, True.intro, True.intro, True.intro, position, running⟩
  funext register
  fin_cases register <;> simp_all

/-- Every guard incidence is fetched from the cache and channel table. -/
theorem execution (program : Program width 4) (s : State width 4)
    (base headBase nodeBase channelBase arityBase sourceBase offset childID cursor : ℕ)
    (child : Bool) (guards : List Bool)
    (offsetHeld : s.reg 3 = word width offset) (nodeHeld : s.reg 1 = word width nodeBase)
    (headFits : headBase + offset < 2 ^ width) (childFits : nodeBase + childID < 2 ^ width)
    (headBound : headBase + offset < s.heap.size) (childBound : nodeBase + childID < s.heap.size)
    (headCell : s.heap[headBase + offset]'headBound = word width childID)
    (childCell : s.heap[nodeBase + childID]'childBound = boolWord width child)
    (arityFits : arityBase + offset < 2 ^ width) (sourceFits : sourceBase + offset < 2 ^ width)
    (arityBound : arityBase + offset < s.heap.size) (sourceBound : sourceBase + offset < s.heap.size)
    (arityCell : s.heap[arityBase + offset]'arityBound = word width guards.length)
    (sourceCell : s.heap[sourceBase + offset]'sourceBound = word width cursor)
    (cursorFits : cursor + guards.length < 2 ^ width) (countFits : guards.length < 2 ^ width)
    (cells : UniformDAGScanLoop.Stored s.heap channelBase cursor guards)
    (pc : s.pc = word width base) (running : s.halted = false)
    (fits : base + 32 < 2 ^ width) (room : s.heap.size < 2 ^ width)
    (block : BlockAt program base (code width base headBase channelBase arityBase sourceBase)) :
    ∃ final ticks peak, Execution program s final ticks peak ∧ ticks ≤ 18 * guards.length + 16 ∧
      peak ≤ s.liveWords + 2 ∧
      final.heap = s.heap.push (boolWord width (child || guards.any (fun x => x))) ∧
      final.stack = s.stack ∧ final.output = s.output ∧
      final.pc = word width (base + 32) ∧ final.halted = false := by
  have headBlock := BlockAt.prefix program base (UniformDAGHeadRead.code width headBase)
    ([.constant 1 (word width channelBase)] ++ UniformDAGGateScan.code width (base + 6) arityBase sourceBase true) block
  have tailBlock : BlockAt program (base + 5)
      ([.constant 1 (word width channelBase)] ++ UniformDAGGateScan.code width (base + 6) arityBase sourceBase true) := by
    simpa only [UniformDAGHeadRead.code_length] using BlockAt.suffix program base
      (UniformDAGHeadRead.code width headBase) _ block
  have constantBlock := BlockAt.prefix program (base + 5)
    ([.constant 1 (word width channelBase)] : Code width) _ tailBlock
  have scanBlock : BlockAt program (base + 6)
      (UniformDAGGateScan.code width (base + 6) arityBase sourceBase true) := by
    simpa only [List.length_singleton, Nat.add_assoc] using BlockAt.suffix program (base + 5)
      ([.constant 1 (word width channelBase)] : Code width) _ tailBlock
  obtain ⟨head, ht, h0, h1, h2, h3, hh, hs, ho, hp, hr⟩ :=
    UniformDAGHeadRead.execution program s base headBase nodeBase offset childID child
      offsetHeld nodeHeld headFits childFits headBound childBound headCell childCell pc running
      (by omega) headBlock
  let initialized := head.advance.put 1 (word width channelBase)
  have p5 : head.pc.val = base + 5 := by rw [hp]; exact Nat.mod_eq_of_lt (by omega)
  have initStep : programStep program head = some initialized := by
    unfold programStep
    rw [p5, show program[base + 5]? = some (.constant 1 (word width channelBase)) from constantBlock 0 (by simp)]
    simp [step, initialized, hr]
  have initializedPC : initialized.pc = word width (base + 6) := by
    simp [initialized, State.put, State.advance, p5, Nat.add_assoc]
  have initializedEq : initialized = state s.heap (base + 6) (word width (nodeBase + childID))
      (word width channelBase) (boolWord width child) (word width offset) s.stack s.output := by
    have eq := canonical initialized (base + 6) (word width (nodeBase + childID))
      (word width channelBase) (boolWord width child) (word width offset)
      (by simpa [initialized, State.put, State.advance] using h0) (by simp [initialized, State.put])
      (by simpa [initialized, State.put, State.advance] using h2)
      (by simpa [initialized, State.put, State.advance] using h3.trans offsetHeld)
      initializedPC (by simpa [initialized, State.put, State.advance] using hr)
    simpa [initialized, State.put, State.advance, hh, hs, ho] using eq
  have hl : head.liveWords = s.liveWords := by simp [State.liveWords, hh, hs, ho]
  have il : initialized.liveWords = s.liveWords := by simp [initialized, State.put, State.advance, State.liveWords, hh, hs, ho]
  have initTrace := Execution.cons initStep (Execution.refl initialized)
  obtain ⟨ticks, peak, scan, time, space⟩ := UniformDAGGateScan.execution program s.heap
    (base + 6) channelBase arityBase sourceBase offset cursor guards (word width (nodeBase + childID))
    (boolWord width child) true s.stack s.output (by omega) room arityFits sourceFits arityBound
    sourceBound arityCell sourceCell cursorFits countFits cells scanBlock
  rw [← initializedEq] at scan
  let final := state (s.heap.push (UniformDAGScanLoop.accumulate true (boolWord width child) guards))
    (base + 6 + 26) (word width 0) (word width channelBase)
    (UniformDAGScanLoop.accumulate true (boolWord width child) guards)
    (word width (cursor + guards.length)) s.stack s.output
  refine ⟨final, 5 + 1 + ticks, max (max s.liveWords (max head.liveWords initialized.liveWords)) peak, ?_, ?_, ?_, ?_, rfl, rfl, ?_, rfl⟩
  · exact (ht.append initTrace).append scan
  · omega
  · simp only [hl, il, Nat.max_self]
    apply max_le (by omega)
    change peak ≤ 4 + s.heap.size + s.stack.length + s.output.length + 1 + 2
    omega
  · simp [final, state, UniformDAGGateScan.accumulate_or]
  · simp [final, state, Nat.add_assoc]

end Controller.Cost.LiteralGuardUnion
