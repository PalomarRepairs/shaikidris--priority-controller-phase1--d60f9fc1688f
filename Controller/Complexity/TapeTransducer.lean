module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.SpaceTapeErasure

@[expose] public section

/-! Ordinary finite multitape transducers with an arbitrary transition table.
Only current head symbols and finite control are readable. Input is immutable
and end-marker bounded; output is append-only. Allocation annotations are
erased from the actual configuration and never supplied to the controller. -/
namespace Controller.Complexity.TapeTransducer
open Turing

structure Action (K Q : Type) where
  next : Option Q
  writes : K → Option SpaceWorkTape.Symbol
  moves : K → Option Dir
  input : Option Dir
  output : Option Bool

structure Machine (K Q : Type) where
  main : Q
  delta : Q → SpaceInputTape.Symbol → (K → SpaceWorkTape.Symbol) → Action K Q

structure Configuration (K Q : Type) where
  pc : Option Q
  input : Tape SpaceInputTape.Symbol
  work : K → Tape SpaceWorkTape.Symbol
  output : List Bool

def moveInput (direction : Dir) (input : Tape SpaceInputTape.Symbol) : Tape SpaceInputTape.Symbol :=
  match direction with
  | .left => if input.head=.start then input else input.move .left
  | .right => if input.head=.stop then input else input.move .right

def apply (action : Action K Q) (state : Configuration K Q) : Configuration K Q :=
  ⟨action.next,action.input.elim state.input (fun direction => moveInput direction state.input),
    fun port => SpaceTapeMachine.operate (action.writes port) (action.moves port) (state.work port),
    action.output.elim state.output (fun bit => bit::state.output)⟩

def step (machine : Machine K Q) (state : Configuration K Q) : Option (Configuration K Q) :=
  state.pc.map fun label => apply (machine.delta label state.input.head (fun port => (state.work port).head)) state

def initial (machine : Machine K Q) (input : List Bool) : Configuration K Q :=
  ⟨some machine.main,SpaceInputTape.encode (ReadOnlyInput.start input),fun _ => SpaceWorkTape.blank,[]⟩

structure Annotated (K Q : Type) where
  configuration : Configuration K Q
  positions : K → Int

def initialAnnotated (machine : Machine K Q) (input : List Bool) : Annotated K Q :=
  ⟨initial machine input,fun _ => 0⟩

def markedStep (machine : Machine K Q) (state : Annotated K Q) : Option (Annotated K Q) :=
  state.configuration.pc.map fun label =>
    let action := machine.delta label state.configuration.input.head (fun port => (state.configuration.work port).head)
    ⟨apply action state.configuration,fun port => state.positions port+SpaceTapeMachine.shift (action.moves port)⟩

theorem projection (machine : Machine K Q) (state : Annotated K Q) :
    (markedStep machine state).map Annotated.configuration=step machine state.configuration := by
  cases position : state.configuration.pc <;> simp [markedStep,step,position]

inductive Covered (machine : Machine K Q) (cells : K → Finset Int) : Annotated K Q → Annotated K Q → Nat → Prop
  | refl {state} : (∀ port, state.positions port ∈ cells port) → Covered machine cells state state 0
  | cons {state next final ticks} : markedStep machine state=some next →
      (∀ port, state.positions port ∈ cells port) → Covered machine cells next final ticks →
      Covered machine cells state final (ticks+1)

theorem Covered.evals {machine : Machine K Q} {cells state final ticks}
    (actual : Covered machine cells state final ticks) :
    Nonempty (StateTransition.EvalsToInTime (step machine) state.configuration (some final.configuration) ticks) := by
  induction actual with
  | refl => exact ⟨StateTransition.EvalsToInTime.refl _ _⟩
  | @cons state middle final ticks transition positions rest ih =>
    obtain ⟨tail⟩ := ih
    have physical : step machine state.configuration=some middle.configuration := by
      rw [← projection,transition]
      rfl
    have first : StateTransition.EvalsToInTime (step machine) state.configuration (some middle.configuration) 1 :=
      ⟨⟨1,physical⟩,le_rfl⟩
    exact ⟨StateTransition.EvalsToInTime.trans _ 1 ticks _ _ _ first tail⟩

theorem output_blind (machine : Machine K Q) (first second : Configuration K Q)
    (control : first.pc=second.pc) (input : first.input.head=second.input.head)
    (work : ∀ port, (first.work port).head=(second.work port).head) :
    first.pc.map (fun label => machine.delta label first.input.head (fun port => (first.work port).head))=
      second.pc.map (fun label => machine.delta label second.input.head (fun port => (second.work port).head)) := by
  rw [control,input,funext work]

end Controller.Complexity.TapeTransducer
