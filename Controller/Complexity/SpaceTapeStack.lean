module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.SpaceTapeOrdinary

@[expose] public section

/-! Work-stack pop and peek use a physical left move, a head-symbol branch
and either erasure in place or a restoring right move. -/
namespace Controller.Complexity.SpaceTapeStack
open SpaceTapeMachine SpaceMachine SpaceTapeRun

def lower [DecidableEq K] (source : SpaceMachine.State K Q) (port : K) (phase : Label n K Q) :
    SpaceTapeMachine.State n K Q :=
  { (configuration source : SpaceTapeMachine.State n K Q) with
    pc := some phase
    work := Function.update (fun selected => SpaceWorkTape.encode (source.work selected)) port
      ((SpaceWorkTape.encode (source.work port)).move .left)
    heads := Function.update (fun selected => (source.work selected).length+1) port
      ((source.work port).length+1-1) }

theorem lower_within [DecidableEq K] (source : SpaceMachine.State K Q) (port : K) (phase : Label n K Q)
    (bound : ∀ selected, (source.work selected).length+2 ≤ capacity) : Within capacity (lower source port phase) := by
  intro selected
  have current := bound selected
  by_cases same : selected=port
  · subst selected
    simp only [lower,Function.update_self]
    constructor <;> omega
  · simp only [lower,Function.update_of_ne same]
    constructor <;> omega

theorem pop_first [DecidableEq K] (enumeration : Fin n ≃ K) (program : SpaceMachine.Program K Q)
    (source : SpaceMachine.State K Q) (label : Q) (port : K) (empty low high : Q)
    (position : source.pc=some label) (code : program.code label=.pop port empty low high) :
    SpaceTapeMachine.step enumeration program (configuration source)=some (lower source port (.pop port empty low high)) := by
  rw [SpaceTapeOrdinary.run_step enumeration program source label position]
  simp only [delta,code]
  rfl

theorem peek_first [DecidableEq K] (enumeration : Fin n ≃ K) (program : SpaceMachine.Program K Q)
    (source : SpaceMachine.State K Q) (label : Q) (port : K) (empty low high : Q)
    (position : source.pc=some label) (code : program.code label=.peek port empty low high) :
    SpaceTapeMachine.step enumeration program (configuration source)=some (lower source port (.peek port empty low high)) := by
  rw [SpaceTapeOrdinary.run_step enumeration program source label position]
  simp only [delta,code]
  rfl

theorem peek_return [DecidableEq K] (enumeration : Fin n ≃ K) (program : SpaceMachine.Program K Q)
    (source : SpaceMachine.State K Q) (port : K) (empty low high : Q) :
    SpaceTapeMachine.step enumeration program (lower source port (.peek port empty low high))=
      some (configuration (instructionStep (.peek port empty low high) source)) := by
  simp only [SpaceTapeMachine.step,lower,Option.map_some,delta,Function.update_self,SpaceWorkTape.observed_left]
  congr 1
  simp only [apply,configuration,instructionStep,advance,operate,shift,Option.elim_some,Option.elim_none,Option.map_some]
  congr 1
  · funext selected
    by_cases same : selected=port
    · subst selected; simp
    · simp [same]
  · funext selected
    by_cases same : selected=port
    · subst selected; simp
    · simp [same]

theorem pop_return [DecidableEq K] (enumeration : Fin n ≃ K) (program : SpaceMachine.Program K Q)
    (source : SpaceMachine.State K Q) (port : K) (empty low high : Q) :
    SpaceTapeMachine.step enumeration program (lower source port (.pop port empty low high))=
      some (configuration (instructionStep (.pop port empty low high) source)) := by
  cases contents : source.work port with
  | nil =>
    simp only [SpaceTapeMachine.step,lower,Option.map_some,delta,Function.update_self,contents,SpaceWorkTape.left_empty]
    congr 1
    simp only [apply,configuration,instructionStep,advance,observed,operate,shift,Option.elim_some,Option.elim_none,Option.map_some,contents,List.head?_nil,List.tail_nil]
    congr 1
    · funext selected
      by_cases same : selected=port
      · subst selected; simp
      · simp [same]
    · funext selected
      by_cases same : selected=port
      · subst selected; simp
      · simp [same]
  | cons bit rest =>
    cases bit <;>
      simp only [SpaceTapeMachine.step,lower,Option.map_some,delta,Function.update_self,contents,SpaceWorkTape.left_cons]
    all_goals congr 1
    all_goals simp only [apply,configuration,instructionStep,advance,observed,operate,shift,Option.elim_some,Option.elim_none,Option.map_some,contents,List.head?_cons,List.tail_cons,Bool.false_eq_true,ite_false,ite_true]
    all_goals congr 1
    all_goals funext selected
    all_goals by_cases same : selected=port
    all_goals try subst selected
    all_goals simp [SpaceWorkTape.pop, *]

end Controller.Complexity.SpaceTapeStack
