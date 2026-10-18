module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.SpaceRequest

public import Mathlib.Tactic.Ring

@[expose] public section

/-! A finite transducer implementing the second machine with virtual input.
Original input remains physical; the caller holds the second machine's work,
its canonical binary virtual-head index and an empty counter scratch bank.
Reads and right moves call the complete first-output request program. -/
namespace Controller.Complexity.SpaceVirtual
open SpaceMachine

abbrev Caller (B : Type) := B ⊕ Bool
abbrev Bank (A B : Type) := SpaceRequestSetup.Bank A (Caller B)
abbrev Label (n : Nat) (P Q : Type) :=
  Q ⊕ ((Q × SpaceRequest.Label n P) ⊕ (Q ⊕ ((Q × Fin 7) ⊕ (Q × Fin 7))))

def sourceLabel (next : Q) : Label n P Q := .inl next
def requestLabel (origin : Q) (label : SpaceRequest.Label n P) : Label n P Q := .inr (.inl (origin,label))
def finishLabel (origin : Q) : Label n P Q := .inr (.inr (.inl origin))
def incrementLabel (next : Q) (label : Fin 7) : Label n P Q := .inr (.inr (.inr (.inl (next,label))))
def decrementLabel (next : Q) (label : Fin 7) : Label n P Q := .inr (.inr (.inr (.inr (next,label))))
def secondPort (port : B) : Bank A B := .inr (.inl port)
def headCaller : Caller B := .inr false
def headPort : Bank A B := .inr headCaller
def scratchPort : Bank A B := .inr (.inr true)
def answerPort : Bank A B := .inl SpaceLookup.answer
def ports : Bool ↪ Bank A B := SpaceFrames.twoPorts headPort scratchPort (by simp [headPort,headCaller,scratchPort])

def program (first : SpaceMachine.Program A P) (second : SpaceMachine.Program B Q)
    (enumeration : Fin n ≃ SpaceLookup.Bank A) : SpaceMachine.Program (Bank A B) (Label n P Q) where
  main := sourceLabel second.main
  code label := match label with
    | .inl origin => match second.code origin with
      | .push port bit next => .push (secondPort port) bit (sourceLabel next)
      | .pop port empty low high => .pop (secondPort port) (sourceLabel empty) (sourceLabel low) (sourceLabel high)
      | .peek port empty low high => .peek (secondPort port) (sourceLabel empty) (sourceLabel low) (sourceLabel high)
      | .readInput _ _ _ => .jump (requestLabel origin (SpaceRequest.program first enumeration (headCaller (B:=B))).main)
      | .atStart yes no => .peek headPort (sourceLabel yes) (sourceLabel no) (sourceLabel no)
      | .left next => .jump (decrementLabel next (SpaceDecrement.program (ports (A:=A) (B:=B))).main)
      | .right _ => .jump (requestLabel origin (SpaceRequest.program first enumeration (headCaller (B:=B))).main)
      | .emit bit next => .emit bit (sourceLabel next)
      | .jump next => .jump (sourceLabel next)
      | .halt => .halt
    | .inr (.inl (origin,label)) =>
        SpaceControl.instruction (requestLabel origin) (some (finishLabel origin))
          ((SpaceRequest.program first enumeration (headCaller (B:=B))).code label)
    | .inr (.inr (.inl origin)) => match second.code origin with
      | .readInput eof low high => .peek answerPort (sourceLabel eof) (sourceLabel low) (sourceLabel high)
      | .right next => .peek answerPort (sourceLabel next)
          (incrementLabel next (SpaceCounter.program (ports (A:=A) (B:=B))).main)
          (incrementLabel next (SpaceCounter.program (ports (A:=A) (B:=B))).main)
      | _ => .halt
    | .inr (.inr (.inr (.inl (next,label)))) =>
        SpaceControl.instruction (incrementLabel next) (some (sourceLabel next)) ((SpaceCounter.program ports).code label)
    | .inr (.inr (.inr (.inr (next,label)))) =>
        SpaceControl.instruction (decrementLabel next) (some (sourceLabel next)) ((SpaceDecrement.program ports).code label)

theorem label_card [Fintype P] [Fintype Q] (n : Nat) :
    Fintype.card (Label n P Q)=Fintype.card Q*(2*n+8*Fintype.card P+34) := by
  simp only [Label,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,Fintype.card_unit]
  ring

theorem resident [Fintype P] [Fintype Q] (first : SpaceMachine.Program A P) (second : SpaceMachine.Program B Q)
    (enumeration : Fin n ≃ SpaceLookup.Bank A) :
    (∑ label, StackMachine.statementSize (SpaceTM.statement ((program first second enumeration).code label))) ≤
      9*(Fintype.card Q*(2*n+8*Fintype.card P+34)) := by
  simpa only [label_card] using SpaceTM.resident (program first second enumeration)

def leftMass [Fintype A] (state : SpaceMachine.State (Bank A B) R) :=
  SpaceBuffers.mass (fun port => state.work (.inl port))
def callerMass [Fintype B] (state : SpaceMachine.State (Bank A B) R) :=
  SpaceBuffers.mass (SpaceRequestSetup.caller state.work)

theorem workspace_split [Fintype A] [Fintype B] (state : SpaceMachine.State (Bank A B) R) :
    workspace state=leftMass state+callerMass state := by
  simp [workspace,leftMass,callerMass,SpaceBuffers.mass,SpaceRequestSetup.caller,Fintype.sum_sum_type]

structure DataRep [Fintype A] (original : List Bool) (shadow : SpaceMachine.State B Q)
    (actual : SpaceMachine.State (Bank A B) R) (limit : Nat) : Prop where
  input : ReadOnlyInput.word actual.tape=original
  work : ∀ port, actual.work (secondPort port)=shadow.work port
  head : actual.work headPort=(ReadOnlyInput.position shadow.tape).bits
  scratch : actual.work scratchPort=[]
  output : actual.output=shadow.output
  left : leftMass actual ≤ limit

structure Represents [Fintype A] (original : List Bool) (shadow : SpaceMachine.State B Q)
    (actual : SpaceMachine.State (Bank A B) (Label n P Q)) (limit : Nat)
    extends DataRep original shadow actual limit where
  pc : actual.pc=shadow.pc.map sourceLabel

theorem DataRep.caller_mass [Fintype A] [Fintype B] {original : List Bool}
    {shadow : SpaceMachine.State B Q} {actual : SpaceMachine.State (Bank A B) R} {limit : Nat}
    (related : DataRep (A:=A) (B:=B) original shadow actual limit) :
    callerMass actual=workspace shadow+(ReadOnlyInput.position shadow.tape).bits.length := by
  have bank : SpaceRequestSetup.caller actual.work=
      Sum.elim shadow.work (BinaryIncrement.work (ReadOnlyInput.position shadow.tape).bits []) := by
    funext port
    cases port with
    | inl port => exact related.work port
    | inr bit => cases bit with
      | false => exact related.head
      | true => exact related.scratch
  simp [callerMass,bank,SpaceBuffers.mass,workspace,Fintype.sum_sum_type,BinaryIncrement.work,Nat.add_comm]

theorem DataRep.workspace_le [Fintype A] [Fintype B] {original : List Bool}
    {shadow : SpaceMachine.State B Q} {actual : SpaceMachine.State (Bank A B) R} {limit : Nat}
    (related : DataRep (A:=A) (B:=B) original shadow actual limit) :
    workspace actual ≤ limit+workspace shadow+(ReadOnlyInput.position shadow.tape).bits.length := by
  rw [workspace_split,related.caller_mass]
  have bound := related.left
  omega

theorem initial [Fintype A] (first : SpaceMachine.Program A P) (second : SpaceMachine.Program B Q)
    (enumeration : Fin n ≃ SpaceLookup.Bank A) (original virtual : List Bool) (limit : Nat) :
    Represents original (SpaceMachine.initial second virtual)
      (SpaceMachine.initial (program first second enumeration) original) limit := by
  refine ⟨?_,rfl⟩
  constructor
  · exact ReadOnlyInput.word_start original
  · intro port; rfl
  · rfl
  · rfl
  · rfl
  · simp [leftMass,SpaceBuffers.mass,SpaceMachine.initial]

end Controller.Complexity.SpaceVirtual
