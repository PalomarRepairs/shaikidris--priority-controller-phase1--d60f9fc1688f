module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Horn.NormalizeCode

@[expose] public section

/-! Embedding the shared normalizer in a program with input and output code.
A fixed-layout proof transform replaces caller-mutating instructions by halt.
A traced execution ending in a running state cannot have executed those halts,
so its instructions and resource counts lift unchanged to the original program.
The transform is used in the proof, not as a runtime compiler pass. -/
namespace Controller.Horn.NormalizeEmbed
open Controller.Cost Controller.Horn.SourceDirectory
open Controller.Horn.Worklist.IndexedNormalize

/-- The original instruction positions and operand words are retained. -/
def neutralOp : Instruction width registers → Instruction width registers
  | .push _ | .pop _ | .emit _ => .halt
  | operation => operation

def neutralize (program : Program width registers) : Program width registers :=
  program.map neutralOp

@[simp] theorem neutralize_size (program : Program width registers) :
    (neutralize program).size = program.size := by simp [neutralize]

@[simp] theorem neutralize_words (program : Program width registers) :
    programWords (neutralize program) = programWords program := by simp [programWords]

theorem neutralOp_neutral (operation : Instruction width registers) :
    CallerNeutral (neutralOp operation) := by
  cases operation <;> simp [neutralOp, CallerNeutral]

theorem neutralOp_eq (operation : Instruction width registers) (neutral : CallerNeutral operation) :
    neutralOp operation = operation := by
  cases operation <;> simp_all [neutralOp, CallerNeutral]

theorem neutralOp_bad (operation : Instruction width registers) (bad : ¬CallerNeutral operation) :
    neutralOp operation = .halt := by
  cases operation <;> simp_all [neutralOp, CallerNeutral]

/-- A halted machine has no next fetched transition, regardless of its program. -/
theorem halted_no_step (program : Program width registers) (state : State width registers)
    (halted : state.halted = true) : programStep program state = none := by
  cases fetch : program[state.pc.val]? <;> simp [programStep, fetch, step, halted]

/-- The only trace from an already halted state is its zero-step reflexive trace. -/
theorem halted_persistent {program : Program width registers}
    {before after : State width registers} {ticks peak : Nat}
    (trace : Execution program before after ticks peak) (halted : before.halted = true) :
    after.halted = true := by
  cases trace with
  | refl => exact halted
  | cons transition rest =>
    rw [halted_no_step program before halted] at transition
    contradiction

theorem execution_running_start {program : Program width registers}
    {before after : State width registers} {ticks peak : Nat}
    (trace : Execution program before after ticks peak) (running : after.halted = false) :
    before.halted = false := by
  by_cases halted : before.halted = true
  · have stopped := halted_persistent trace halted
    rw [running] at stopped
    contradiction
  · exact Bool.eq_false_iff.mpr halted

/-- A successful transformed step with a running endpoint fetched an unchanged
instruction. It therefore has exactly the same transition in the full program. -/
theorem lift_step (program : Program width registers) (before after : State width registers)
    (transition : programStep (neutralize program) before = some after)
    (running : after.halted = false) : programStep program before = some after := by
  cases fetch : program[before.pc.val]? with
  | none => simp [programStep, neutralize, Array.getElem?_map, fetch] at transition
  | some operation =>
    have transformed : step (neutralOp operation) before = some after := by
      simpa [programStep, neutralize, Array.getElem?_map, fetch] using transition
    by_cases neutral : CallerNeutral operation
    · rw [neutralOp_eq operation neutral] at transformed
      simpa [programStep, fetch] using transformed
    · rw [neutralOp_bad operation neutral] at transformed
      by_cases stopped : before.halted = true
      · simp [step, stopped] at transformed
      · have active : before.halted = false := Bool.eq_false_iff.mpr stopped
        simp only [step, active, Bool.false_eq_true, ite_false] at transformed
        have equal := Option.some.inj transformed
        have haltValue := congrArg State.halted equal
        simp only [running] at haltValue
        contradiction

/-- Universal same-state, same-tick, same-peak transport. Ending in a running
state rules out executing any of the replacement halts. -/
theorem lift_execution {program : Program width registers}
    {before after : State width registers} {ticks peak : Nat}
    (trace : Execution (neutralize program) before after ticks peak)
    (running : after.halted = false) : Execution program before after ticks peak := by
  induction trace with
  | refl state => exact Execution.refl state
  | cons transition rest ih =>
    exact Execution.cons (lift_step program _ _ transition (execution_running_start rest running))
      (ih running)

/-- Every fetched transformed opcode satisfies the global proof premise. -/
theorem neutralized_neutral (program : Program width registers) (position : Nat)
    (operation : Instruction width registers)
    (fetch : (neutralize program)[position]? = some operation) : CallerNeutral operation := by
  cases original : program[position]? with
  | none => simp [neutralize, Array.getElem?_map, original] at fetch
  | some source =>
    have equal : neutralOp source = operation := by
      simpa [neutralize, Array.getElem?_map, original] using fetch
    rw [← equal]
    exact neutralOp_neutral source

/-- A known neutral instruction keeps its actual address in the transformed array. -/
theorem neutralized_fetch (program : Program width registers) (position : Nat)
    (operation : Instruction width registers) (neutral : CallerNeutral operation)
    (fetch : program[position]? = some operation) :
    (neutralize program)[position]? = some operation := by
  simp [neutralize, Array.getElem?_map, fetch, neutralOp_eq operation neutral]

/-- The fixed stored normalizer block is identical under the proof transform. -/
theorem neutralized_kernel (program : Program width 8)
    (entry n base recordHeader inputHeader firstHeader directoryHeader endHeader : Nat)
    (present : Controller.Horn.NormalizeCode.KernelAt program entry n base recordHeader
      inputHeader firstHeader directoryHeader endHeader) :
    Controller.Horn.NormalizeCode.KernelAt (neutralize program) entry n base recordHeader
      inputHeader firstHeader directoryHeader endHeader := by
  intro phase
  cases fetched : (Controller.Horn.NormalizeCNF.code width entry n base recordHeader
      inputHeader firstHeader directoryHeader endHeader)[phase.val]? with
  | none =>
    have original := (present phase).trans fetched
    simp [neutralize, Array.getElem?_map, original]
  | some operation =>
    have neutral := Controller.Horn.NormalizeCNF.code_caller_neutral width entry n base recordHeader
      inputHeader firstHeader directoryHeader endHeader phase.val operation fetched
    exact neutralized_fetch program _ operation neutral ((present phase).trans fetched)

/-- The original full program may contain pops, pushes and emits outside the
normalizer. The complete physical source loop still runs in that same program. -/
theorem normalize_all_execution (program : Program width 8) (entry : Nat)
    (clauses : List (Controller.CNF.Clause (Fin n))) (layout : Layout clauses)
    (present : Controller.Horn.NormalizeCode.KernelAt program entry n layout.base layout.recordHeader
      layout.inputHeader layout.firstHeader layout.directoryHeader layout.endHeader)
    (recordStart : Nat) (marks : Marks n) (state : State width 8)
    (invariant : Controller.Horn.NormalizeLoop.Invariant clauses layout recordStart 0 marks state)
    (dual : ∀ index : Fin clauses.length, Controller.Horn.DualHornClause clauses[index.val])
    (position : state.pc = word width entry) (capacity : entry + 161 < 2 ^ width)
    (room : state.heap.size + 3 * clauses.length + (clauses.map List.length).sum < 2 ^ width) :
    ∃ final : State width 8, ∃ finalMarks : Marks n, ∃ ticks peak : Nat,
      Execution program state final ticks peak ∧
      Controller.Horn.NormalizeLoop.Invariant clauses layout recordStart clauses.length finalMarks final ∧
      final.pc = word width (entry + 161) ∧
      ticks ≤ 61 * (clauses.map List.length).sum + 71 * clauses.length + 6 ∧
      programWords program + peak ≤ programWords program + state.liveWords +
        3 * clauses.length + (clauses.map List.length).sum := by
  have transformedKernel := neutralized_kernel program entry n layout.base layout.recordHeader
    layout.inputHeader layout.firstHeader layout.directoryHeader layout.endHeader present
  have components := Controller.Horn.NormalizeCode.kernel_components (neutralize program) entry
    clauses layout transformedKernel
  obtain ⟨final, finalMarks, ticks, peak, trace, complete, finalPC, cost, storage⟩ :=
    Controller.Horn.NormalizeLoop.normalize_all_execution (neutralize program) entry clauses layout
      components recordStart marks state invariant dual position capacity room (neutralized_neutral program)
  exact ⟨final, finalMarks, ticks, peak, lift_execution trace complete.input.running,
    complete, finalPC, cost, by simpa only [neutralize_words] using storage⟩

end Controller.Horn.NormalizeEmbed
