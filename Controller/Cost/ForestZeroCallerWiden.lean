module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.RegisterWiden
public import Controller.Cost.GateProgram
public import Controller.Cost.ForestZeroNormalizeFrame

@[expose] public section

/-! Successful four-register traces execute inside an arbitrary eight-register
caller. A proof-local program view replaces instructions using high registers
with halt; the running final state excludes those substitutions from the trace.
The actual caller program executes directly, preserves the four saved high
registers, and retains the original heap, stack, output and step count. The
four additional registers contribute four words to the recorded peak. -/
namespace Controller.Cost.ForestZeroCallerWiden
open Controller.Cost Controller.Cost.GateProgram
variable {width : Nat}

def lowerInstruction : Instruction width 8 → Instruction width 4
  | .constant dst value => if h : dst.val < 4 then .constant ⟨dst.val, h⟩ value else .halt
  | .copy dst src => if d : dst.val < 4 then
      if s : src.val < 4 then .copy ⟨dst.val, d⟩ ⟨src.val, s⟩ else .halt else .halt
  | .add dst left right => if d : dst.val < 4 then if l : left.val < 4 then
      if r : right.val < 4 then .add ⟨dst.val, d⟩ ⟨left.val, l⟩ ⟨right.val, r⟩ else .halt
      else .halt else .halt
  | .xor dst left right => if d : dst.val < 4 then if l : left.val < 4 then
      if r : right.val < 4 then .xor ⟨dst.val, d⟩ ⟨left.val, l⟩ ⟨right.val, r⟩ else .halt
      else .halt else .halt
  | .load dst address => if d : dst.val < 4 then if a : address.val < 4 then
      .load ⟨dst.val, d⟩ ⟨address.val, a⟩ else .halt else .halt
  | .store address src => if a : address.val < 4 then if s : src.val < 4 then
      .store ⟨address.val, a⟩ ⟨src.val, s⟩ else .halt else .halt
  | .allocate src => if h : src.val < 4 then .allocate ⟨src.val, h⟩ else .halt
  | .release => .release
  | .push src => if h : src.val < 4 then .push ⟨src.val, h⟩ else .halt
  | .pop dst => if h : dst.val < 4 then .pop ⟨dst.val, h⟩ else .halt
  | .emit src => if h : src.val < 4 then .emit ⟨src.val, h⟩ else .halt
  | .branchZero src target => if h : src.val < 4 then .branchZero ⟨src.val, h⟩ target else .halt
  | .halt => .halt

def lowerProgram (program : Program width 8) : Program width 4 :=
  program.map lowerInstruction

theorem lower_widen (instruction : Instruction width 4) :
    lowerInstruction (Controller.Cost.RegisterWiden.widenInstruction instruction) = instruction := by
  cases instruction <;>
    simp [lowerInstruction, Controller.Cost.RegisterWiden.widenInstruction,
      Controller.Cost.RegisterWiden.widenRegister]

theorem lower_fetch (program : Program width 8) (position : Nat)
    (instruction : Instruction width 4)
    (found : program[position]? = some (Controller.Cost.RegisterWiden.widenInstruction instruction)) :
    (lowerProgram program)[position]? = some instruction := by
  simp only [lowerProgram, Array.getElem?_map, found, Option.map_some, lower_widen]

theorem lower_inverse (actual : Instruction width 8) (low : Instruction width 4)
    (same : lowerInstruction actual = low) (active : low ≠ .halt) :
    Controller.Cost.RegisterWiden.widenInstruction low = actual := by
  cases actual <;> simp only [lowerInstruction] at same
  all_goals try split_ifs at same
  all_goals subst low
  all_goals first
    | exact False.elim (active rfl)
    | simp [Controller.Cost.RegisterWiden.widenInstruction,
        Controller.Cost.RegisterWiden.widenRegister]
    | congr 1 <;> apply Fin.ext <;> rfl

theorem lower_nonhalt {instruction : Instruction width 4}
    {before after : State width 4}
    (transition : step instruction before = some after) (running : after.halted = false) :
    instruction ≠ .halt := by
  intro halted
  rw [halted] at transition
  unfold step at transition
  by_cases stopped : before.halted = true
  · simp [stopped] at transition
  · have firstRunning : before.halted = false := Bool.eq_false_iff.mpr stopped
    simp only [firstRunning, Bool.false_eq_true, ite_false, Option.some.injEq] at transition
    subst after
    cases running

theorem execution (program : Program width 8)
    (before after : State width 4) (ticks peak : Nat)
    (trace : Execution (lowerProgram program) before after ticks peak)
    (running : after.halted = false) (saved : Fin 8 → Word width) :
    Execution program (Controller.Cost.RegisterWiden.widenState before saved)
      (Controller.Cost.RegisterWiden.widenState after saved) ticks (peak + 4) := by
  induction trace with
  | refl state =>
    simpa only [Controller.Cost.RegisterWiden.widenState_liveWords] using
      Execution.refl (p := program) (Controller.Cost.RegisterWiden.widenState state saved)
  | @cons first middle last ticks peak transition rest ih =>
    have middleRunning : middle.halted = false :=
      Controller.Cost.ForestZeroNormalizeFrame.execution_running rest running
    have lifted : programStep program (Controller.Cost.RegisterWiden.widenState first saved) =
        some (Controller.Cost.RegisterWiden.widenState middle saved) := by
      unfold programStep at transition
      simp only [lowerProgram, Array.getElem?_map] at transition
      cases found : program[first.pc.val]? with
      | none => simp [found] at transition
      | some instruction =>
        simp only [found, Option.map_some] at transition
        change step (lowerInstruction instruction) first = some middle at transition
        have inverse := lower_inverse instruction (lowerInstruction instruction) rfl
          (lower_nonhalt transition middleRunning)
        unfold programStep
        rw [Controller.Cost.RegisterWiden.widenState_pc, found]
        change step instruction (Controller.Cost.RegisterWiden.widenState first saved) =
          some (Controller.Cost.RegisterWiden.widenState middle saved)
        rw [← inverse, Controller.Cost.RegisterWiden.widen_step, transition]
        rfl
    simpa only [Controller.Cost.RegisterWiden.widenState_liveWords,
      Nat.add_max_add_right] using Execution.cons lifted (ih running)

/-- The actual caller stores only widened constructor instructions at the
constructor's own slots. All other eight-register code remains unrestricted. -/
def WidenedBlockAt (program : Program width 8) (base : Nat) (code : Code width) : Prop :=
  ∀ offset, offset < code.length → program[base + offset]? =
    (code[offset]?).map Controller.Cost.RegisterWiden.widenInstruction

theorem lower_block (program : Program width 8) (base : Nat) (code : Code width)
    (present : WidenedBlockAt program base code) : BlockAt (lowerProgram program) base code := by
  intro offset bound
  simp only [lowerProgram, Array.getElem?_map, present offset bound]
  cases found : code[offset]? with
  | none => rfl
  | some instruction => simp only [Option.map_some, lower_widen]


end Controller.Cost.ForestZeroCallerWiden
