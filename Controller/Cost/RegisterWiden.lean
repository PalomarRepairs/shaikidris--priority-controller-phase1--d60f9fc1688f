module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Horn.SourceDirectory

@[expose] public section

/-! Four-register kernels execute in an eight-register caller with identical
transitions and four additional charged resident words. -/
namespace Controller.Cost.RegisterWiden
open Controller.Cost

def widenRegister (register : Fin 4) : Fin 8 := register.castLE (by decide)

def widenInstruction : Instruction width 4 → Instruction width 8
  | .constant dst value => .constant (widenRegister dst) value
  | .copy dst src => .copy (widenRegister dst) (widenRegister src)
  | .add dst left right => .add (widenRegister dst) (widenRegister left) (widenRegister right)
  | .xor dst left right => .xor (widenRegister dst) (widenRegister left) (widenRegister right)
  | .load dst address => .load (widenRegister dst) (widenRegister address)
  | .store address src => .store (widenRegister address) (widenRegister src)
  | .allocate src => .allocate (widenRegister src)
  | .release => .release
  | .push src => .push (widenRegister src)
  | .pop dst => .pop (widenRegister dst)
  | .emit src => .emit (widenRegister src)
  | .branchZero src target => .branchZero (widenRegister src) target
  | .halt => .halt

def widenState (state : State width 4) (saved : Fin 8 → Word width) : State width 8 :=
  { reg := fun register => if small : register.val < 4 then
      state.reg ⟨register.val, small⟩ else saved register
    heap := state.heap, stack := state.stack, output := state.output,
    pc := state.pc, halted := state.halted }

@[simp] theorem widenState_low (state : State width 4) (saved : Fin 8 → Word width)
    (register : Fin 4) : (widenState state saved).reg (widenRegister register) = state.reg register := by
  simp [widenState, widenRegister]

@[simp] theorem widenState_high (state : State width 4) (saved : Fin 8 → Word width)
    (register : Fin 8) (large : 4 ≤ register.val) :
    (widenState state saved).reg register = saved register := by
  simp [widenState, show ¬register.val < 4 from by omega]

@[simp] theorem widenState_liveWords (state : State width 4) (saved : Fin 8 → Word width) :
    (widenState state saved).liveWords = state.liveWords + 4 := by
  simp [widenState, State.liveWords]; omega

@[simp] theorem widenState_advance (state : State width 4) (saved : Fin 8 → Word width) :
    (widenState state saved).advance = widenState state.advance saved := rfl

@[simp] theorem widenState_put (state : State width 4) (saved : Fin 8 → Word width)
    (dst : Fin 4) (value : Word width) :
    (widenState state saved).put (widenRegister dst) value =
      widenState (state.put dst value) saved := by
  unfold widenState State.put
  congr 1
  funext register
  by_cases small : register.val < 4
  · simp [widenRegister, small, Fin.ext_iff]
  · have other : register ≠ widenRegister dst := by
      intro same
      have val := congrArg Fin.val same
      change register.val = dst.val at val
      omega
    simp [small, other]

@[simp] theorem widenState_heap (state : State width 4) (saved : Fin 8 → Word width) :
    (widenState state saved).heap = state.heap := rfl

@[simp] theorem widenState_stack (state : State width 4) (saved : Fin 8 → Word width) :
    (widenState state saved).stack = state.stack := rfl

@[simp] theorem widenState_output (state : State width 4) (saved : Fin 8 → Word width) :
    (widenState state saved).output = state.output := rfl

@[simp] theorem widenState_pc (state : State width 4) (saved : Fin 8 → Word width) :
    (widenState state saved).pc = state.pc := rfl

@[simp] theorem widenState_halted (state : State width 4) (saved : Fin 8 → Word width) :
    (widenState state saved).halted = state.halted := rfl

/-- Every original primitive executes in the eight-register machine with the
same heap, stack, output and PC transition; the four high registers are framed. -/
theorem widen_step (instruction : Instruction width 4) (state : State width 4)
    (saved : Fin 8 → Word width) :
    step (widenInstruction instruction) (widenState state saved) =
      (step instruction state).map (fun final => widenState final saved) := by
  cases stopped : state.halted <;> cases instruction <;>
    simp [step, widenInstruction, stopped]
  all_goals first
    | rfl
    | split <;> rfl
    | cases state.stack <;> rfl

def widenProgram (program : Program width 4) : Program width 8 :=
  program.map widenInstruction

/-- Fetched program access uses the same PC and array position after widening. -/
theorem widen_programStep (program : Program width 4) (state : State width 4)
    (saved : Fin 8 → Word width) :
    programStep (widenProgram program) (widenState state saved) =
      (programStep program state).map (fun final => widenState final saved) := by
  unfold programStep
  simp only [widenProgram, widenState, Array.getElem?_map]
  cases found : program[state.pc.val]? with
  | none => rfl
  | some instruction => exact widen_step instruction state saved

/-- Widening carries the complete actual trace without a machine reset. The
additional four registers contribute four charged resident words. -/
theorem widen_execution (program : Program width 4) (state final : State width 4)
    (ticks peak : Nat) (trace : Execution program state final ticks peak)
    (saved : Fin 8 → Word width) :
    Execution (widenProgram program) (widenState state saved)
      (widenState final saved) ticks (peak + 4) := by
  induction trace with
  | refl state =>
    simpa only [widenState_liveWords] using
      Execution.refl (p := widenProgram program) (widenState state saved)
  | @cons start middle final ticks peak transition rest ih =>
    have lifted : programStep (widenProgram program) (widenState start saved) =
        some (widenState middle saved) := by
      rw [widen_programStep, transition]
      rfl
    simpa only [widenState_liveWords, Nat.add_max_add_right] using
      Execution.cons lifted ih


end Controller.Cost.RegisterWiden
