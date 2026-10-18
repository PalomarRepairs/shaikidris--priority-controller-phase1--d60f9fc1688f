module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.WordArithmetic
public import Controller.Complexity.StackBlocks

@[expose] public section

/-! Relocation of three-port binary routines into a larger fixed work bank.
Mapped ports carry the routine's data; all other stack contents form an
unchanged frame. Literal execution time is preserved and live storage adds. -/
namespace Controller.Complexity.StackFrames
open StackMachine
open scoped BigOperators

def threePorts (shared first second : Option K) (h₁ : shared ≠ first) (h₂ : shared ≠ second) (h₃ : first ≠ second) :
    Option Bool ↪ Option K where
  toFun port := match port with | none => shared | some false => first | some true => second
  inj' := by
    intro a b h
    cases a with
    | none => cases b with
      | none => rfl
      | some bit => cases bit <;> simp_all
    | some bit => cases b with
      | none => cases bit <;> simp_all
      | some other => cases bit <;> cases other <;> simp_all

def embedStorage [DecidableEq K] (ports : Option Bool ↪ Option K)
    (frame : Option K → List Bool) (bank : Option Bool → List Bool) (target : Option K) : List Bool :=
  if target=ports none then bank none
  else if target=ports (some false) then bank (some false)
  else if target=ports (some true) then bank (some true)
  else frame target

theorem embedStorage_at [DecidableEq K] (ports : Option Bool ↪ Option K)
    (frame : Option K → List Bool) (bank : Option Bool → List Bool) (port : Option Bool) :
    embedStorage ports frame bank (ports port) = bank port := by
  cases port with
  | none => simp [embedStorage]
  | some bit => cases bit <;> simp [embedStorage, ports.injective.eq_iff]

theorem embedStorage_other [DecidableEq K] (ports : Option Bool ↪ Option K)
    (frame : Option K → List Bool) (bank : Option Bool → List Bool) (target : Option K)
    (outside : ∀ port, target ≠ ports port) : embedStorage ports frame bank target = frame target := by
  simp [embedStorage, outside]

theorem embedStorage_update [DecidableEq K] (ports : Option Bool ↪ Option K)
    (frame : Option K → List Bool) (bank : Option Bool → List Bool) (port : Option Bool) (value : List Bool) :
    embedStorage ports frame (Function.update bank port value) =
      Function.update (embedStorage ports frame bank) (ports port) value := by
  classical
  funext target
  by_cases mapped : ∃ selected, target=ports selected
  · obtain ⟨selected,rfl⟩ := mapped
    simp only [embedStorage_at, Function.update_apply, ports.injective.eq_iff]
  · have outside : ∀ selected, target ≠ ports selected := by simpa using mapped
    simp [embedStorage_other ports frame _ target outside, outside]

def embedState [DecidableEq K] (ports : Option Bool ↪ Option K) (frame : Option K → List Bool)
    (state : State Bool Q) : State K Q := ⟨state.pc, embedStorage ports frame state.stk⟩

def relocateInstruction (ports : Option Bool ↪ Option K) : Instruction Bool Q → Instruction K Q
  | .push stack bit next => .push (ports stack) bit next
  | .pop stack empty low high => .pop (ports stack) empty low high
  | .peek stack empty low high => .peek (ports stack) empty low high
  | .jump next => .jump next
  | .halt => .halt

def relocate (ports : Option Bool ↪ Option K) (program : Program Bool Q) : Program K Q :=
  ⟨program.main, fun label => relocateInstruction ports (program.code label)⟩

theorem instructionStep_embed [DecidableEq K] (ports : Option Bool ↪ Option K)
    (frame : Option K → List Bool) (instruction : Instruction Bool Q) (state : State Bool Q) :
    instructionStep (relocateInstruction ports instruction) (embedState ports frame state) =
      embedState ports frame (instructionStep instruction state) := by
  cases instruction with
  | push stack bit next =>
    simp only [relocateInstruction, instructionStep, embedState, embedStorage_at, embedStorage_update]
  | pop stack empty low high =>
    simp only [relocateInstruction, instructionStep, embedState, embedStorage_at, embedStorage_update]
  | peek stack empty low high =>
    simp only [relocateInstruction, instructionStep, embedState, embedStorage_at]
  | jump next => rfl
  | halt => rfl

theorem step_embed [DecidableEq K] (ports : Option Bool ↪ Option K)
    (frame : Option K → List Bool) (program : Program Bool Q) (state : State Bool Q) :
    step (relocate ports program) (embedState ports frame state) =
      (step program state).map (embedState ports frame) := by
  cases position : state.pc with
  | none => simp [step, embedState, position]
  | some label =>
    simp only [step, embedState, position, Option.map_some, relocate]
    exact congrArg some (instructionStep_embed ports frame (program.code label) state)

def frameBits [Fintype K] [DecidableEq K] (ports : Option Bool ↪ Option K) (frame : Option K → List Bool) : Nat :=
  ∑ target, (embedStorage ports frame (fun _ => []) target).length

theorem cell_length [DecidableEq K] (ports : Option Bool ↪ Option K)
    (frame : Option K → List Bool) (bank : Option Bool → List Bool) (target : Option K) :
    (embedStorage ports frame bank target).length =
      (embedStorage ports frame (fun _ => []) target).length +
      (if target=ports none then (bank none).length else 0) +
      (if target=ports (some false) then (bank (some false)).length else 0) +
      (if target=ports (some true) then (bank (some true)).length else 0) := by
  by_cases shared : target=ports none
  · subst target
    simp [embedStorage, ports.injective.eq_iff]
  · by_cases first : target=ports (some false)
    · subst target
      simp [embedStorage, ports.injective.eq_iff]
    · by_cases second : target=ports (some true)
      · subst target
        simp [embedStorage, ports.injective.eq_iff]
      · simp [embedStorage, shared, first, second]

theorem live_embed [Fintype K] [DecidableEq K] (ports : Option Bool ↪ Option K)
    (frame : Option K → List Bool) (state : State Bool Q) :
    live (embedState ports frame state) = live state + frameBits ports frame := by
  calc
    _ = ∑ target, ((embedStorage ports frame (fun _ => []) target).length +
        (if target=ports none then (state.stk none).length else 0) +
        (if target=ports (some false) then (state.stk (some false)).length else 0) +
        (if target=ports (some true) then (state.stk (some true)).length else 0)) :=
      Finset.sum_congr rfl fun target _ => cell_length ports frame state.stk target
    _ = frameBits ports frame + (state.stk none).length +
        (state.stk (some false)).length + (state.stk (some true)).length := by
      simp [Finset.sum_add_distrib, frameBits]
    _ = live state + frameBits ports frame := by
      simp [live, Fintype.sum_option, Nat.add_comm, Nat.add_assoc]

theorem execution [Fintype K] [DecidableEq K] (ports : Option Bool ↪ Option K)
    (frame : Option K → List Bool) {program : Program Bool Q} {state final ticks peak}
    (trace : Execution program state final ticks peak) :
    Execution (relocate ports program) (embedState ports frame state) (embedState ports frame final)
      ticks (peak+frameBits ports frame) := by
  induction trace with
  | refl state =>
    simpa only [live_embed] using Execution.refl (program := relocate ports program) (embedState ports frame state)
  | @cons state next final ticks peak transition tail ih =>
    have lifted : step (relocate ports program) (embedState ports frame state) = some (embedState ports frame next) := by
      rw [step_embed, transition]
      rfl
    have shift : max (live state+frameBits ports frame) (peak+frameBits ports frame) =
        max (live state) peak + frameBits ports frame := by omega
    simpa only [live_embed, shift] using Execution.cons lifted ih

theorem statementSize_relocate (ports : Option Bool ↪ Option K) (instruction : Instruction Bool Q) :
    statementSize (tmStatement (relocateInstruction ports instruction)) = statementSize (tmStatement instruction) := by
  cases instruction <;> rfl

theorem resident_relocate [Fintype Q] (ports : Option Bool ↪ Option K) (program : Program Bool Q) :
    (∑ label, statementSize (tmStatement ((relocate ports program).code label))) =
      ∑ label, statementSize (tmStatement (program.code label)) := by
  simp only [relocate, statementSize_relocate]

theorem addition [Fintype K] [DecidableEq K] (ports : Option Bool ↪ Option K)
    (frame : Option K → List Bool) (width left right : Nat) (output : List Bool) :
    Execution (relocate ports WordArithmetic.program)
      (embedState ports frame (WordArithmetic.state (some (WordArithmetic.entry false))
        (Encoding.bits width left) (Encoding.bits width right) output))
      (embedState ports frame (terminal ((Encoding.bits width (left+right)).reverse ++ output)))
      (3*width+2) (2*width+output.length+frameBits ports frame) :=
  execution ports frame (WordArithmetic.encoded_execution width left right output)

theorem xor [Fintype K] [DecidableEq K] (ports : Option Bool ↪ Option K)
    (frame : Option K → List Bool) (width left right : Nat) (output : List Bool) :
    Execution (relocate ports WordXor.program)
      (embedState ports frame (WordXor.state (some WordXor.entry)
        (Encoding.bits width left) (Encoding.bits width right) output))
      (embedState ports frame (terminal ((Encoding.bits width (left ^^^ right)).reverse ++ output)))
      (3*width+2) (2*width+output.length+frameBits ports frame) :=
  execution ports frame (WordXor.encoded_execution width left right output)

theorem reversal [Fintype K] [DecidableEq K] (ports : Option Bool ↪ Option K)
    (frame : Option K → List Bool) (input : List Bool) :
    Execution (relocate ports StackBlocks.reverseProgram)
      (embedState ports frame (initial StackBlocks.reverseProgram input))
      (embedState ports frame (terminal input.reverse))
      (6*input.length+6) (input.length+frameBits ports frame) :=
  execution ports frame (StackBlocks.reverse_execution input)

end Controller.Complexity.StackFrames
