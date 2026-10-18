module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.UniformDAGGuardGate

public import Mathlib.Tactic.FinCases

@[expose] public section

/-! Complete OR execution initializes the runtime table base and false
accumulator, scans the original child stream, and allocates the computed value. -/
namespace Controller.Cost.UniformDAGOrGate
open Controller.Cost.GateProgram Controller.Cost.UniformDAGScan

def code (width base valueBase arityBase sourceBase : ℕ) : Code width :=
  [.constant 1 (word width valueBase), .constant 2 (boolWord width false)] ++
    UniformDAGGateScan.code width (base + 2) arityBase sourceBase true
@[simp] theorem code_length : (code width base valueBase arityBase sourceBase).length = 28 := rfl

private theorem canonical (s : State width 4) (pc : ℕ) (r0 r1 r2 r3 : Word width)
    (zero : s.reg 0 = r0) (one : s.reg 1 = r1) (two : s.reg 2 = r2) (three : s.reg 3 = r3)
    (position : s.pc = word width pc) (running : s.halted = false) :
    s = state s.heap pc r0 r1 r2 r3 s.stack s.output := by
  rcases s with ⟨registers, heap, stack, output, cursor, halted⟩
  simp only [state, State.mk.injEq]
  refine ⟨?_, True.intro, True.intro, True.intro, position, running⟩
  funext register
  fin_cases register <;> simp_all

theorem execution (program : Program width 4) (s : State width 4)
    (base valueBase arityBase sourceBase offset cursor : ℕ) (values : List Bool)
    (offsetHeld : s.reg 3 = word width offset)
    (arityFits : arityBase + offset < 2 ^ width) (sourceFits : sourceBase + offset < 2 ^ width)
    (arityBound : arityBase + offset < s.heap.size) (sourceBound : sourceBase + offset < s.heap.size)
    (arityCell : s.heap[arityBase + offset]'arityBound = word width values.length)
    (sourceCell : s.heap[sourceBase + offset]'sourceBound = word width cursor)
    (cursorFits : cursor + values.length < 2 ^ width) (countFits : values.length < 2 ^ width)
    (cells : UniformDAGScanLoop.Stored s.heap valueBase cursor values)
    (pc : s.pc = word width base) (running : s.halted = false)
    (fits : base + 28 < 2 ^ width) (room : s.heap.size < 2 ^ width)
    (block : BlockAt program base (code width base valueBase arityBase sourceBase)) :
    ∃ final ticks peak, Execution program s final ticks peak ∧ ticks ≤ 18 * values.length + 12 ∧
      peak ≤ s.liveWords + 2 ∧
      final.heap = s.heap.push (boolWord width (values.any (fun x => x))) ∧
      final.stack = s.stack ∧ final.output = s.output ∧
      final.pc = word width (base + 28) ∧ final.halted = false := by
  let setupCode : Code width := [.constant 1 (word width valueBase), .constant 2 (boolWord width false)]
  have setupBlock := BlockAt.prefix program base setupCode
    (UniformDAGGateScan.code width (base + 2) arityBase sourceBase true) block
  have scanBlock : BlockAt program (base + 2)
      (UniformDAGGateScan.code width (base + 2) arityBase sourceBase true) := by
    simpa [setupCode] using BlockAt.suffix program base setupCode _ block
  let one := s.advance.put 1 (word width valueBase)
  let ready := one.advance.put 2 (boolWord width false)
  have baseVal : s.pc.val = base := by rw [pc]; exact Nat.mod_eq_of_lt (by omega)
  have p1 : one.pc = word width (base + 1) := by simp [one, State.put, State.advance, baseVal]
  have p1Val : one.pc.val = base + 1 := by rw [p1]; exact Nat.mod_eq_of_lt (by omega)
  have readyPC : ready.pc = word width (base + 2) := by simp [ready, State.put, State.advance, p1Val, Nat.add_assoc]
  have first : programStep program s = some one := by
    unfold programStep
    rw [baseVal, show program[base]? = some (.constant 1 (word width valueBase)) from
      (by simpa [setupCode] using setupBlock 0 (by simp [setupCode]))]
    simp [step, one, running]
  have second : programStep program one = some ready := by
    unfold programStep
    rw [p1Val, show program[base + 1]? = some (.constant 2 (boolWord width false)) from
      (by simpa [setupCode] using setupBlock 1 (by simp [setupCode]))]
    simp [step, one, ready, State.put, State.advance, running]
  have readyEq : ready = state s.heap (base + 2) (s.reg 0) (word width valueBase)
      (boolWord width false) (word width offset) s.stack s.output := by
    have eq := canonical ready (base + 2) (s.reg 0) (word width valueBase)
      (boolWord width false) (word width offset)
      (by simp [ready, one, State.put, State.advance])
      (by simp [ready, one, State.put, State.advance])
      (by simp [ready, State.put])
      (by simpa [ready, one, State.put, State.advance] using offsetHeld)
      readyPC (by simp [ready, one, State.put, State.advance, running])
    simpa [ready, one, State.put, State.advance] using eq
  have ol : one.liveWords = s.liveWords := rfl
  have rl : ready.liveWords = s.liveWords := rfl
  have setupTrace := Execution.cons first (Execution.cons second (Execution.refl ready))
  obtain ⟨ticks, peak, scan, time, space⟩ := UniformDAGGateScan.execution program s.heap
    (base + 2) valueBase arityBase sourceBase offset cursor values (s.reg 0)
    (boolWord width false) true s.stack s.output (by omega) room arityFits sourceFits arityBound
    sourceBound arityCell sourceCell cursorFits countFits cells scanBlock
  rw [← readyEq] at scan
  let final := state (s.heap.push (UniformDAGScanLoop.accumulate true (boolWord width false) values))
    (base + 2 + 26) (word width 0) (word width valueBase)
    (UniformDAGScanLoop.accumulate true (boolWord width false) values)
    (word width (cursor + values.length)) s.stack s.output
  refine ⟨final, 2 + ticks, max (max s.liveWords (max one.liveWords ready.liveWords)) peak, ?_, ?_, ?_, ?_, rfl, rfl, ?_, rfl⟩
  · exact setupTrace.append scan
  · omega
  · simp only [ol, rl, Nat.max_self]
    apply max_le (by omega)
    change peak ≤ 4 + s.heap.size + s.stack.length + s.output.length + 1 + 2
    omega
  · simp [final, state, UniformDAGGateScan.accumulate_or]
  · simp [final, state, Nat.add_assoc]

end Controller.Cost.UniformDAGOrGate
