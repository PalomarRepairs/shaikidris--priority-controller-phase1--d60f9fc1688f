module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.Refinement

@[expose] public section

/-! Successful machine executions preserve an arbitrary trailing stack/output
frame. Existing words are charged at every transition; invalid source steps
are not asserted to remain invalid after framing. -/
namespace Controller.Cost

def State.frame (s : State width registers) (stack output : List (Word width)) :
    State width registers :=
  { s with stack := s.stack ++ stack, output := s.output ++ output }

@[simp] theorem State.frame_liveWords (s : State width registers)
    (stack output : List (Word width)) :
    (s.frame stack output).liveWords = s.liveWords + (stack.length + output.length) := by
  simp [State.frame, State.liveWords]; omega

/-- Appending a frame lifts every successful primitive, including stack pops. -/
theorem step_frame (instruction : Instruction width registers) (s t : State width registers)
    (stack output : List (Word width)) (transition : step instruction s = some t) :
    step instruction (s.frame stack output) = some (t.frame stack output) := by
  by_cases halted : s.halted = true
  · simp [step, halted] at transition
  have running : s.halted = false := Bool.eq_false_iff.mpr halted
  cases instruction
  case pop dst =>
    cases storedStack : s.stack with
    | nil => simp [step, running, storedStack] at transition
    | cons value rest =>
      simp only [step, running, Bool.false_eq_true, ite_false, storedStack] at transition
      cases transition
      simp [step, State.frame, State.advance, State.put, running, storedStack]
  case load dst address =>
    by_cases valid : (s.reg address).val < s.heap.size
    · simp only [step, running, Bool.false_eq_true, ite_false, dite_eq_left valid] at transition
      cases transition
      simp [step, State.frame, State.advance, State.put, running, valid]
    · simp [step, running, valid] at transition
  case store address src =>
    by_cases valid : (s.reg address).val < s.heap.size
    · simp only [step, running, Bool.false_eq_true, ite_false, dite_eq_left valid] at transition
      cases transition
      simp [step, State.frame, State.advance, State.put, running, valid]
    · simp [step, running, valid] at transition
  case allocate src =>
    by_cases room : s.heap.size < 2 ^ width
    · simp only [step, running, Bool.false_eq_true, ite_false, ite_eq_left room] at transition
      cases transition
      simp [step, State.frame, State.advance, State.put, running, room]
    · simp [step, running, room] at transition
  case release =>
    by_cases empty : s.heap.isEmpty = true
    · simp [step, running, empty] at transition
    · simp only [step, running, Bool.false_eq_true, ite_false, ite_eq_right empty] at transition
      cases transition
      simp [step, State.frame, State.advance, State.put, running, empty]
  case branchZero src target =>
    by_cases zero : (s.reg src).val = 0
    · simp only [step, running, Bool.false_eq_true, ite_false, ite_eq_left zero] at transition
      cases transition
      simp only [step, State.frame, State.advance, running, Bool.false_eq_true, ite_false, ite_eq_left zero]
    · simp only [step, running, Bool.false_eq_true, ite_false, ite_eq_right zero] at transition
      cases transition
      simp only [step, State.frame, State.advance, running, Bool.false_eq_true, ite_false, ite_eq_right zero]
  all_goals
    simp only [step, running, Bool.false_eq_true, ite_false] at transition
    all_goals cases transition
    all_goals simp_all [step, State.frame, State.advance, State.put, List.cons_append]

/-- Fetch reads the same opcode because framing leaves the program counter intact. -/
theorem programStep_frame (program : Program width registers) (s t : State width registers)
    (stack output : List (Word width)) (transition : programStep program s = some t) :
    programStep program (s.frame stack output) = some (t.frame stack output) := by
  unfold programStep at transition ⊢
  change (do let instruction ← program[s.pc.val]?; step instruction (s.frame stack output)) = _
  cases fetch : program[s.pc.val]? with
  | none => simp [fetch] at transition
  | some instruction =>
    simp only [fetch, Option.bind_some] at transition ⊢
    exact step_frame instruction s t stack output transition

/-- Framing preserves executed ticks and charges the added words at the peak. -/
theorem Execution.frame {program : Program width registers} {s t ticks peak}
    (trace : Execution program s t ticks peak) (stack output : List (Word width)) :
    Execution program (s.frame stack output) (t.frame stack output) ticks
      (peak + (stack.length + output.length)) := by
  induction trace with
  | refl s => simpa only [State.frame_liveWords] using Execution.refl (p := program) (s.frame stack output)
  | cons transition rest ih =>
    have lifted := Execution.cons (programStep_frame program _ _ stack output transition) ih
    simpa only [State.frame_liveWords, Nat.add_max_add_right] using lifted

end Controller.Cost
