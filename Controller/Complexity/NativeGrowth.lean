module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.NativeLoop

@[expose] public section

/-! Every genuine native transition adds at most one live word. Consequently
native peak storage along a finite trace is bounded by initial words plus
executed instructions, without capacity or termination assumptions. -/
namespace Controller.Complexity.NativeGrowth

theorem step_le (instruction : Controller.Cost.Instruction width registers)
    (state next : Controller.Cost.State width registers)
    (transition : Controller.Cost.step instruction state=some next) : next.liveWords ≤ state.liveWords+1 := by
  cases flag : state.halted with
  | true => simp [Controller.Cost.step,flag] at transition
  | false =>
    cases instruction with
    | constant dst value =>
      simp only [Controller.Cost.step,flag,Bool.false_eq_true,↓reduceIte,Option.some.injEq] at transition
      subst next
      simp only [Controller.Cost.State.liveWords,Controller.Cost.State.advance,Controller.Cost.State.put]
      omega
    | copy dst src =>
      simp only [Controller.Cost.step,flag,Bool.false_eq_true,↓reduceIte,Option.some.injEq] at transition
      subst next
      simp only [Controller.Cost.State.liveWords,Controller.Cost.State.advance,Controller.Cost.State.put]
      omega
    | add dst left right =>
      simp only [Controller.Cost.step,flag,Bool.false_eq_true,↓reduceIte,Option.some.injEq] at transition
      subst next
      simp only [Controller.Cost.State.liveWords,Controller.Cost.State.advance,Controller.Cost.State.put]
      omega
    | xor dst left right =>
      simp only [Controller.Cost.step,flag,Bool.false_eq_true,↓reduceIte,Option.some.injEq] at transition
      subst next
      simp only [Controller.Cost.State.liveWords,Controller.Cost.State.advance,Controller.Cost.State.put]
      omega
    | push src =>
      simp only [Controller.Cost.step,flag,Bool.false_eq_true,↓reduceIte,Option.some.injEq] at transition
      subst next
      simp only [Controller.Cost.State.liveWords,Controller.Cost.State.advance,List.length_cons]
      omega
    | emit src =>
      simp only [Controller.Cost.step,flag,Bool.false_eq_true,↓reduceIte,Option.some.injEq] at transition
      subst next
      simp only [Controller.Cost.State.liveWords,Controller.Cost.State.advance,List.length_cons]
      omega
    | halt =>
      simp only [Controller.Cost.step,flag,Bool.false_eq_true,↓reduceIte,Option.some.injEq] at transition
      subst next
      simp only [Controller.Cost.State.liveWords,Controller.Cost.State.advance]
      omega
    | load dst address =>
      simp only [Controller.Cost.step,flag,Bool.false_eq_true,↓reduceIte] at transition
      split at transition
      · cases Option.some.inj transition
        simp only [Controller.Cost.State.liveWords,Controller.Cost.State.advance,Controller.Cost.State.put]
        omega
      · contradiction
    | store address src =>
      simp only [Controller.Cost.step,flag,Bool.false_eq_true,↓reduceIte] at transition
      split at transition
      · cases Option.some.inj transition
        simp only [Controller.Cost.State.liveWords,Controller.Cost.State.advance,Array.size_set]
        omega
      · contradiction
    | allocate src =>
      simp only [Controller.Cost.step,flag,Bool.false_eq_true,↓reduceIte] at transition
      split at transition
      · cases Option.some.inj transition
        simp only [Controller.Cost.State.liveWords,Controller.Cost.State.advance,Array.size_push]
        omega
      · contradiction
    | release =>
      simp only [Controller.Cost.step,flag,Bool.false_eq_true,↓reduceIte] at transition
      split at transition
      · contradiction
      · cases Option.some.inj transition
        simp only [Controller.Cost.State.liveWords,Controller.Cost.State.advance,Array.size_pop]
        omega
    | pop dst =>
      cases contents : state.stack with
      | nil => simp [Controller.Cost.step,flag,contents] at transition
      | cons head rest =>
        simp only [Controller.Cost.step,flag,Bool.false_eq_true,↓reduceIte,contents,Option.some.injEq] at transition
        subst next
        simp only [Controller.Cost.State.liveWords,Controller.Cost.State.advance,Controller.Cost.State.put,contents,List.length_cons]
        omega
    | branchZero src target =>
      by_cases zero : (state.reg src).val=0 <;>
        simp only [Controller.Cost.step,flag,Bool.false_eq_true,↓reduceIte,zero,Option.some.injEq] at transition <;>
        subst next <;> simp only [Controller.Cost.State.liveWords,Controller.Cost.State.advance] <;> omega

theorem program_step_le (program : Controller.Cost.Program width registers)
    (state next : Controller.Cost.State width registers)
    (transition : Controller.Cost.programStep program state=some next) : next.liveWords ≤ state.liveWords+1 := by
  cases entry : program[state.pc.val]? with
  | none => simp [Controller.Cost.programStep,entry] at transition
  | some instruction =>
    apply step_le instruction state next
    simpa only [Controller.Cost.programStep,entry,Bind.bind,Option.bind] using transition

theorem peak_le {program : Controller.Cost.Program width registers} {state final : Controller.Cost.State width registers} {ticks peak}
    (trace : Controller.Cost.Execution program state final ticks peak) : peak ≤ state.liveWords+ticks := by
  induction trace with
  | refl state => omega
  | @cons state middle final ticks peak transition rest ih =>
    have growth := program_step_le program state middle transition
    omega

end Controller.Complexity.NativeGrowth
