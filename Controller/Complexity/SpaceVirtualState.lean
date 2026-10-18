module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.SpaceVirtual

@[expose] public section

/-! Canonical views of the virtual-input simulation invariant. The original
input head and dirty first-machine work are physical data; the second input
word is represented only by its binary head position and request semantics. -/
namespace Controller.Complexity.SpaceVirtualState
open SpaceMachine SpaceVirtual

def bank (left : SpaceLookup.Bank A → List Bool) (work : B → List Bool) (position : Nat) : Bank A B → List Bool :=
  Sum.elim left (Sum.elim work (BinaryIncrement.work position.bits []))

def view (left : SpaceLookup.Bank A → List Bool) (tape : ReadOnlyInput.Tape) (shadow : SpaceMachine.State B Q) :
    SpaceMachine.State (Bank A B) (Label n P Q) :=
  ⟨shadow.pc.map sourceLabel,tape,bank left shadow.work (ReadOnlyInput.position shadow.tape),shadow.output⟩

theorem bank_second (left : SpaceLookup.Bank A → List Bool) (work : B → List Bool) (number : Nat) (port : B) :
    bank left work number (secondPort port)=work port := rfl

theorem bank_head (left : SpaceLookup.Bank A → List Bool) (work : B → List Bool) (number : Nat) :
    bank left work number headPort=number.bits := rfl

theorem bank_update [DecidableEq A] [DecidableEq B] (left : SpaceLookup.Bank A → List Bool)
    (work : B → List Bool) (number : Nat) (port : B) (bits : List Bool) :
    bank left (Function.update work port bits) number=Function.update (bank left work number) (secondPort port) bits := by
  funext target
  cases target with
  | inl target => simp only [bank,secondPort,Function.update_apply,Sum.elim_inl,reduceCtorEq,ite_false]
  | inr target => cases target with
    | inl target => simp only [bank,secondPort,Function.update_apply,Sum.elim_inl,Sum.elim_inr,Sum.inl.injEq,Sum.inr.injEq]
    | inr bit => simp only [bank,secondPort,Function.update_apply,Sum.elim_inr,Sum.inr.injEq,reduceCtorEq,ite_false]

theorem state_ext {first second : SpaceMachine.State K R}
    (pc : first.pc=second.pc) (tape : first.tape=second.tape)
    (work : first.work=second.work) (output : first.output=second.output) : first=second := by
  cases first
  cases second
  cases pc
  cases tape
  cases work
  cases output
  rfl

theorem view_eq [Fintype A] {original : List Bool} {shadow : SpaceMachine.State B Q}
    {actual : SpaceMachine.State (Bank A B) (Label n P Q)} {limit : Nat}
    (related : Represents (A:=A) (B:=B) (n:=n) (P:=P) original shadow actual limit) :
    actual=view (fun port => actual.work (.inl port)) actual.tape shadow := by
  have work : actual.work=bank (fun port => actual.work (.inl port)) shadow.work (ReadOnlyInput.position shadow.tape) := by
    funext port
    cases port with
    | inl port => rfl
    | inr port => cases port with
      | inl port => exact related.work port
      | inr bit => cases bit with
        | false => exact related.head
        | true => exact related.scratch
  exact state_ext related.pc rfl work related.output

theorem represents [Fintype A] (left : SpaceLookup.Bank A → List Bool) (tape : ReadOnlyInput.Tape)
    (shadow : SpaceMachine.State B Q) (original : List Bool) (limit : Nat)
    (input : ReadOnlyInput.word tape=original) (bounded : SpaceBuffers.mass left ≤ limit) :
    Represents original shadow (view (n:=n) (P:=P) left tape shadow) limit := by
  refine ⟨?_,rfl⟩
  exact ⟨input,fun _ => rfl,rfl,rfl,rfl,bounded⟩

theorem retain [Fintype A] {original : List Bool} {shadow : SpaceMachine.State B Q}
    {before : SpaceMachine.State (Bank A B) R} {after : SpaceMachine.State (Bank A B) S} {limit : Nat}
    (related : DataRep original shadow before limit)
    (input : ReadOnlyInput.word after.tape=ReadOnlyInput.word before.tape)
    (output : after.output=before.output)
    (caller : ∀ port, after.work (.inr port)=before.work (.inr port)) (bounded : leftMass after ≤ limit) :
    DataRep original shadow after limit := by
  exact ⟨input.trans related.input,fun port => (caller (.inl port)).trans (related.work port),
    (caller headCaller).trans related.head,(caller (.inr true)).trans related.scratch,
    output.trans related.output,bounded⟩

theorem shadow_change [Fintype A] {original : List Bool} {before : SpaceMachine.State B Q}
    {after : SpaceMachine.State B T} {actual : SpaceMachine.State (Bank A B) R} {limit : Nat}
    (related : DataRep original before actual limit) (work : after.work=before.work)
    (position : ReadOnlyInput.position after.tape=ReadOnlyInput.position before.tape)
    (output : after.output=before.output) : DataRep original after actual limit := by
  constructor
  · exact related.input
  · intro port; rw [work]; exact related.work port
  · rw [position]; exact related.head
  · exact related.scratch
  · rw [output]; exact related.output
  · exact related.left

theorem head_change [Fintype A] [DecidableEq A] [DecidableEq B]
    {original : List Bool} {before : SpaceMachine.State B Q} {after : SpaceMachine.State B T}
    {actual : SpaceMachine.State (Bank A B) R} {limit number : Nat}
    (related : DataRep original before actual limit) (work : after.work=before.work)
    (position : ReadOnlyInput.position after.tape=number) (output : after.output=before.output)
    (pc : Option S) :
    DataRep original after
      (⟨pc,actual.tape,Function.update actual.work headPort number.bits,actual.output⟩ : SpaceMachine.State (Bank A B) S) limit := by
  constructor
  · exact related.input
  · intro port
    rw [work]
    simpa [Function.update_apply,secondPort,headPort,headCaller] using related.work port
  · rw [position]
    simp
  · simpa [scratchPort,headPort,headCaller] using related.scratch
  · rw [output]; exact related.output
  · simpa [leftMass,SpaceBuffers.mass,headPort] using related.left

theorem observed_bits (yes no : R) (number : Nat) :
    observed yes no no number.bits.head?=(if number=0 then yes else no) := by
  by_cases zero : number=0
  · subst number; simp [observed]
  · have nonempty : number.bits ≠ [] := by
      intro empty
      have size := Nat.size_eq_bits_len number
      rw [empty,List.length_nil] at size
      exact zero (Nat.size_eq_zero.mp size.symm)
    cases bits : number.bits with
    | nil => exact (nonempty bits).elim
    | cons bit rest => cases bit <;> simp [observed,zero]

theorem head_test (yes no : R) (tape : ReadOnlyInput.Tape) :
    observed yes no no (ReadOnlyInput.position tape).bits.head?=(if tape.left.isEmpty then yes else no) := by
  rw [observed_bits]
  cases left : tape.left <;> simp [ReadOnlyInput.position,left]

end Controller.Complexity.SpaceVirtualState
