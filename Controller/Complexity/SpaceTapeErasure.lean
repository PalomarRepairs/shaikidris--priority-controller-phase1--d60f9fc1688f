module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.SpaceTapeAllocation

@[expose] public section

/-! Erasing allocation ghosts gives an ordinary finite-control multitape
machine. Its configuration contains only control, actual input/work tapes and
append-only output; literal step iteration is preserved by erasure. -/
namespace Controller.Complexity.SpaceTapeErasure
open SpaceTapeMachine SpaceTapeRun
open scoped BigOperators

structure Configuration (n : Nat) (K Q : Type) where
  pc : Option (Label n K Q)
  input : Turing.Tape SpaceInputTape.Symbol
  work : K → Turing.Tape SpaceWorkTape.Symbol
  output : List Bool

def erase (state : SpaceTapeMachine.State n K Q) : Configuration n K Q :=
  ⟨state.pc,state.input,state.work,state.output⟩

def apply [DecidableEq K] (action : Action n K Q) (state : Configuration n K Q) : Configuration n K Q where
  pc := action.next
  input := action.input.elim state.input fun direction => state.input.move direction
  work := action.work.elim state.work fun (port,write,move) =>
    Function.update state.work port (operate write move (state.work port))
  output := action.output.elim state.output fun bit => bit::state.output

def step [DecidableEq K] (enumeration : Fin n ≃ K) (program : SpaceMachine.Program K Q)
    (state : Configuration n K Q) : Option (Configuration n K Q) :=
  state.pc.map fun label => apply (delta enumeration program label state.input.head (fun port => (state.work port).head)) state

theorem erase_step [DecidableEq K] (enumeration : Fin n ≃ K) (program : SpaceMachine.Program K Q)
    (state : SpaceTapeMachine.State n K Q) :
    (SpaceTapeMachine.step enumeration program state).map erase=step enumeration program (erase state) := by
  cases position : state.pc <;> simp [SpaceTapeMachine.step,step,erase,position]
  rfl

theorem evals [DecidableEq K] {enumeration : Fin n ≃ K} {program : SpaceMachine.Program K Q}
    {capacity state final ticks} (actual : Run enumeration program capacity state final ticks) :
    Nonempty (StateTransition.EvalsToInTime (step enumeration program) (erase state) (some (erase final)) ticks) := by
  induction actual with
  | refl => exact ⟨StateTransition.EvalsToInTime.refl _ _⟩
  | @cons state middle final ticks transition within rest ih =>
    obtain ⟨tail⟩ := ih
    have moved : step enumeration program (erase state)=some (erase middle) := by
      rw [← erase_step,transition]
      rfl
    have first : StateTransition.EvalsToInTime (step enumeration program) (erase state) (some (erase middle)) 1 :=
      ⟨⟨1,moved⟩,le_rfl⟩
    exact ⟨StateTransition.EvalsToInTime.trans _ 1 ticks _ _ _ first tail⟩

theorem logspace [Fintype K] [DecidableEq K] [Fintype Q]
    (enumeration : Fin n ≃ K) {program : SpaceMachine.Program K Q} {function constant}
    (computed : LogSpaceBounds.Computes program function constant) (input : List Bool) :
    ∃ final ticks allocated,
      Nonempty (StateTransition.EvalsToInTime (step enumeration program)
        (erase (SpaceTapeMachine.initial input)) (some (erase (configuration final))) ticks) ∧
      SpaceTapeAllocation.Covered enumeration program allocated (SpaceTapeMachine.initial input) (configuration final) ticks ∧
      (erase (configuration (n := n) final)).pc=none ∧
      (erase (configuration (n := n) final)).output.reverse=function input ∧
      (∑ port, (allocated port).card)=Fintype.card K*(constant+2)*LogSpaceBounds.bits input.length ∧
      ticks ≤ n+1+2*LogSpaceBounds.timeBound (Fintype.card Q) (Fintype.card K) constant input.length := by
  obtain ⟨final,ticks,actual,halted,output,time⟩ := SpaceTapeBridge.computes enumeration computed input
  obtain ⟨allocated,coverage,space⟩ := SpaceTapeAllocation.cells actual
  exact ⟨final,ticks,allocated,evals actual,coverage,by simp [erase,configuration,halted],output,
    by simpa only [Nat.mul_assoc] using space,time⟩

end Controller.Complexity.SpaceTapeErasure
