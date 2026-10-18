module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.SpaceInputTape
public import Controller.Complexity.SpaceWorkTape

@[expose] public section

/-! A finite multitape controller with an immutable input tape, ordinary
read/write work tapes and append-only output. Its transition function receives
only finite control and current head symbols. Absolute work-head positions are
ghost allocation counters and are unavailable to that function. -/
namespace Controller.Complexity.SpaceTapeMachine
open Turing

inductive Label (n : Nat) (K Q : Type)
  | init (index : Fin (n+1))
  | run (label : Q)
  | pop (port : K) (empty low high : Q)
  | peek (port : K) (empty low high : Q)
  | left (next : Q)
  | start (yes no : Q)
  deriving DecidableEq, Fintype

structure Action (n : Nat) (K Q : Type) where
  next : Option (Label n K Q)
  work : Option (K × Option SpaceWorkTape.Symbol × Option Dir) := none
  input : Option Dir := none
  output : Option Bool := none

structure State (n : Nat) (K Q : Type) where
  pc : Option (Label n K Q)
  input : Tape SpaceInputTape.Symbol
  work : K → Tape SpaceWorkTape.Symbol
  heads : K → Int
  output : List Bool

def delta (enumeration : Fin n ≃ K) (program : SpaceMachine.Program K Q)
    (label : Label n K Q) (input : SpaceInputTape.Symbol) (work : K → SpaceWorkTape.Symbol) : Action n K Q :=
  match label with
  | .init index =>
      if available : index.val<n then
        ⟨some (.init ⟨index.val+1,by omega⟩),some (enumeration ⟨index.val,available⟩,some .bottom,some .right),none,none⟩
      else ⟨some (.run program.main),none,none,none⟩
  | .run label => match program.code label with
      | .push port bit next => ⟨some (.run next),some (port,some (.bit bit),some .right),none,none⟩
      | .pop port empty low high => ⟨some (.pop port empty low high),some (port,none,some .left),none,none⟩
      | .peek port empty low high => ⟨some (.peek port empty low high),some (port,none,some .left),none,none⟩
      | .readInput eof low high => ⟨some (.run (SpaceMachine.observed eof low high (SpaceInputTape.observed input))),none,none,none⟩
      | .atStart yes no => ⟨some (.start yes no),none,some .left,none⟩
      | .left next => ⟨some (.left next),none,some .left,none⟩
      | .right next => ⟨some (.run next),none,if input=.stop then none else some .right,none⟩
      | .emit bit next => ⟨some (.run next),none,none,some bit⟩
      | .jump next => ⟨some (.run next),none,none,none⟩
      | .halt => ⟨none,none,none,none⟩
  | .pop port empty low high =>
      match work port with
      | .bit bit => ⟨some (.run (if bit then high else low)),some (port,some .blank,none),none,none⟩
      | .bottom => ⟨some (.run empty),some (port,none,some .right),none,none⟩
      | .blank => ⟨none,none,none,none⟩
  | .peek port empty low high =>
      ⟨some (.run (SpaceMachine.observed empty low high (SpaceWorkTape.observed (work port)))),
        some (port,none,some .right),none,none⟩
  | .left next => ⟨some (.run next),none,if input=.start then some .right else none,none⟩
  | .start yes no => ⟨some (.run (if input=.start then yes else no)),none,some .right,none⟩

def shift : Option Dir → Int
  | none => 0
  | some .left => -1
  | some .right => 1

def operate (write : Option SpaceWorkTape.Symbol) (move : Option Dir) (tape : Tape SpaceWorkTape.Symbol) : Tape SpaceWorkTape.Symbol :=
  let written := write.elim tape fun symbol => tape.write symbol
  move.elim written fun direction => written.move direction

def apply [DecidableEq K] (action : Action n K Q) (state : State n K Q) : State n K Q where
  pc := action.next
  input := action.input.elim state.input fun direction => state.input.move direction
  work := action.work.elim state.work fun (port,write,move) => Function.update state.work port (operate write move (state.work port))
  heads := action.work.elim state.heads fun (port,_,move) => Function.update state.heads port (state.heads port+shift move)
  output := action.output.elim state.output fun bit => bit::state.output

def step [DecidableEq K] (enumeration : Fin n ≃ K) (program : SpaceMachine.Program K Q)
    (state : State n K Q) : Option (State n K Q) :=
  state.pc.map fun label => apply (delta enumeration program label state.input.head (fun port => (state.work port).head)) state

def initial (input : List Bool) : State n K Q :=
  ⟨some (.init ⟨0,by omega⟩),SpaceInputTape.encode (ReadOnlyInput.start input),
    fun _ => SpaceWorkTape.blank,fun _ => 0,[]⟩

def configuration (source : SpaceMachine.State K Q) : State n K Q :=
  ⟨source.pc.map Label.run,SpaceInputTape.encode source.tape,
    fun port => SpaceWorkTape.encode (source.work port),fun port => (source.work port).length+1,source.output⟩

theorem head_information_only (enumeration : Fin n ≃ K) (program : SpaceMachine.Program K Q)
    (first second : State n K Q) (pc : first.pc=second.pc)
    (input : first.input.head=second.input.head)
    (work : ∀ port, (first.work port).head=(second.work port).head) :
    first.pc.map (fun label => delta enumeration program label first.input.head (fun port => (first.work port).head))=
      second.pc.map (fun label => delta enumeration program label second.input.head (fun port => (second.work port).head)) := by
  rw [pc,input,funext work]

end Controller.Complexity.SpaceTapeMachine
