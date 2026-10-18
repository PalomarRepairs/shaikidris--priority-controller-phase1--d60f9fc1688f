module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.SpaceMicro

@[expose] public section

/-! Every internal work-bank span of a compiled source instruction is bounded
by its two actual endpoint lengths. Internal input/output operations and the
finite register are kept separate from designated work-bank allocation. -/
namespace Controller.Complexity.SpaceMicroBounds
open SpaceMachine SpaceMicro

theorem instruction_spans [DecidableEq K] (instruction : SpaceMachine.Instruction K Q)
    (source : SpaceMachine.State K Q) (port : K) :
    (run (SpaceTM.statement instruction) none (SpaceTM.storage source)).spans port ≤
      max (source.work port).length ((instructionStep instruction source).work port).length := by
  cases instruction with
  | push selected bit next =>
    by_cases same : port=selected
    · subst port
      simp [SpaceTM.statement,SpaceTM.next,run,prepend,SpaceTM.storage,SpaceTM.workPort,
        instructionStep,advance,Function.update_apply]
    · simp [SpaceTM.statement,SpaceTM.next,run,prepend,SpaceTM.storage,SpaceTM.workPort,
        instructionStep,advance,Function.update_apply,same]
  | pop selected empty low high =>
    cases contents : source.work selected with
    | nil =>
      by_cases same : port=selected
      · subst port
        simp [SpaceTM.statement,SpaceTM.next,SpaceTM.branch,run,prepend,SpaceTM.storage,SpaceTM.workPort,
          instructionStep,advance,observed,Function.update_apply,contents]
      · simp [SpaceTM.statement,SpaceTM.next,SpaceTM.branch,run,prepend,SpaceTM.storage,SpaceTM.workPort,
          instructionStep,advance,observed,Function.update_apply,contents,same]
    | cons bit rest =>
      cases bit <;> by_cases same : port=selected
      all_goals try subst port
      all_goals simp [SpaceTM.statement,SpaceTM.next,SpaceTM.branch,run,prepend,SpaceTM.storage,SpaceTM.workPort,
        instructionStep,advance,observed,Function.update_apply, *]
  | peek selected empty low high =>
    cases bit : (source.work selected).head? with
    | none => simp [SpaceTM.statement,SpaceTM.next,SpaceTM.branch,run,prepend,SpaceTM.storage,SpaceTM.workPort,
        instructionStep,advance,bit]
    | some value => cases value <;>
        simp [SpaceTM.statement,SpaceTM.next,SpaceTM.branch,run,prepend,SpaceTM.storage,SpaceTM.workPort,
          instructionStep,advance,bit]
  | readInput eof low high =>
    cases bit : source.tape.right.head? with
    | none => simp [SpaceTM.statement,SpaceTM.next,SpaceTM.branch,run,prepend,SpaceTM.storage,SpaceTM.rightPort,SpaceTM.workPort,
        instructionStep,advance,bit]
    | some value => cases value <;>
        simp [SpaceTM.statement,SpaceTM.next,SpaceTM.branch,run,prepend,SpaceTM.storage,SpaceTM.rightPort,SpaceTM.workPort,
          instructionStep,advance,bit]
  | atStart yes no =>
    cases contents : source.tape.left with
    | nil => simp [SpaceTM.statement,SpaceTM.next,run,prepend,SpaceTM.storage,SpaceTM.leftPort,SpaceTM.workPort,
        instructionStep,advance,contents]
    | cons bit rest => cases bit <;>
        simp [SpaceTM.statement,SpaceTM.next,run,prepend,SpaceTM.storage,SpaceTM.leftPort,SpaceTM.workPort,
          instructionStep,advance,contents]
  | left next =>
    cases contents : source.tape.left with
    | nil => simp [SpaceTM.statement,SpaceTM.next,run,prepend,SpaceTM.storage,SpaceTM.leftPort,SpaceTM.rightPort,SpaceTM.workPort,
        instructionStep,advance,contents]
    | cons bit rest => cases bit <;>
        simp [SpaceTM.statement,SpaceTM.next,run,prepend,SpaceTM.storage,SpaceTM.leftPort,SpaceTM.rightPort,SpaceTM.workPort,
          instructionStep,advance,contents]
  | right next =>
    cases contents : source.tape.right with
    | nil => simp [SpaceTM.statement,SpaceTM.next,run,prepend,SpaceTM.storage,SpaceTM.leftPort,SpaceTM.rightPort,SpaceTM.workPort,
        instructionStep,advance,contents]
    | cons bit rest => cases bit <;>
        simp [SpaceTM.statement,SpaceTM.next,run,prepend,SpaceTM.storage,SpaceTM.leftPort,SpaceTM.rightPort,SpaceTM.workPort,
          instructionStep,advance,contents]
  | emit bit next =>
    simp [SpaceTM.statement,SpaceTM.next,run,prepend,SpaceTM.storage,SpaceTM.workPort,instructionStep,advance]
  | jump next => simp [SpaceTM.statement,SpaceTM.next,run,prepend,SpaceTM.storage,SpaceTM.workPort,instructionStep,advance]
  | halt => simp [SpaceTM.statement,run,prepend,SpaceTM.storage,SpaceTM.workPort,instructionStep]

theorem instruction_execution [DecidableEq K] (instruction : SpaceMachine.Instruction K Q)
    (source : SpaceMachine.State K Q) :
    ∃ ticks spans, Trace (.pending (SpaceTM.statement instruction) none (SpaceTM.storage source))
      (.done (SpaceTM.configuration (instructionStep instruction source))) ticks spans ∧
      ticks ≤ 5 ∧ ∀ port, spans port ≤ max (source.work port).length ((instructionStep instruction source).work port).length := by
  have actual := library_execution (SpaceTM.statement instruction) none (SpaceTM.storage source)
  rw [SpaceTM.statement_step] at actual
  refine ⟨_,_,actual,(ticks_le_depth _ _ _).trans (SpaceTM.statement_depth instruction),?_⟩
  exact instruction_spans instruction source

end Controller.Complexity.SpaceMicroBounds
