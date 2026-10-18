module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestZeroCallerWiden
public import Controller.Cost.SharedDetectorAssembly

@[expose] public section

/-! Redirect a running output-only block to the caller stack. This is a
simulation of fetched instructions: emit and push exchange roles, and a pop
in the proof-local view becomes halt. A running final state excludes that
unsupported instruction. Code outside the block remains unrestricted. -/
namespace Controller.Extensions.WitnessStack
open Controller.Cost

def swap (state : State width registers) : State width registers :=
  { state with stack := state.output, output := state.stack }

@[simp] theorem swap_swap (state : State width registers) : swap (swap state) = state := rfl

@[simp] theorem swap_live (state : State width registers) : (swap state).liveWords = state.liveWords := by
  simp only [swap, State.liveWords]; omega

def redirect : Instruction width registers → Instruction width registers
  | .emit r => .push r
  | .push r => .emit r
  | .pop _ => .halt
  | instruction => instruction

def Safe : Instruction width registers → Prop
  | .pop _ => False
  | _ => True

theorem redirect_twice (instruction : Instruction width registers) (safe : Safe instruction) :
    redirect (redirect instruction) = instruction := by
  cases instruction <;> simp_all [redirect, Safe]

theorem step_lift (instruction : Instruction width registers) (before after : State width registers)
    (transition : step (redirect instruction) before = some after) (running : after.halted = false) :
    step instruction (swap before) = some (swap after) := by
  cases instruction <;> simp only [redirect, step] at transition ⊢
  all_goals by_cases active : before.halted = true
  all_goals try simp [active] at transition
  all_goals have off : before.halted = false := Bool.eq_false_iff.mpr active
  all_goals simp only [off, Bool.false_eq_true, ite_false, swap] at transition ⊢
  all_goals try split_ifs at transition
  all_goals try simp only [Option.some.injEq] at transition
  all_goals try subst after
  all_goals simp_all [State.advance, State.put, swap]
  all_goals obtain ⟨valid, rfl⟩ := transition
  all_goals simp_all

def view (program : Program width registers) : Program width registers := program.map redirect

theorem execution (program : Program width 8) (before after : State width 8) (ticks peak : Nat)
    (trace : Execution (view program) before after ticks peak) (running : after.halted = false) :
    Execution program (swap before) (swap after) ticks peak := by
  induction trace with
  | refl state => simpa using Execution.refl (p := program) (swap state)
  | @cons first middle last ticks peak transition rest ih =>
    have middleRunning := ForestZeroNormalizeFrame.execution_running rest running
    have lifted : programStep program (swap first) = some (swap middle) := by
      unfold programStep at transition ⊢
      simp only [view, Array.getElem?_map] at transition
      cases found : program[first.pc.val]? with
      | none => simp [found] at transition
      | some instruction =>
        simp only [found, Option.map_some] at transition
        change step (redirect instruction) first = some middle at transition
        simp only [swap, found, Option.bind_some]
        exact step_lift instruction first middle transition middleRunning
    simpa only [swap_live] using Execution.cons lifted (ih running)

theorem view_block (program : Program width registers) (entry : Nat)
    (code : List (Instruction width registers)) (safe : ∀ instruction ∈ code, Safe instruction)
    (present : ∀ i, i < code.length → program[entry + i]? = (code[i]?).map redirect) :
    ∀ i, i < code.length → (view program)[entry + i]? = code[i]? := by
  intro i bound
  simp only [view, Array.getElem?_map, present i bound]
  rw [List.getElem?_eq_getElem bound]
  simp only [Option.map_some, redirect_twice _ (safe _ (List.getElem_mem bound))]

end Controller.Extensions.WitnessStack
