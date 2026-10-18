module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.SpaceMachine

@[expose] public section

/-! Binary stacks on ordinary work tapes. The head rests on the blank cell
immediately to the right of the stack. A bottom marker occupies cell zero;
initialization writes that marker onto an initially blank tape. Push, pop and
peek use only ordinary tape writes, moves and the observed head symbol. -/
namespace Controller.Complexity.SpaceWorkTape
open Turing

inductive Symbol
  | blank
  | bottom
  | bit (value : Bool)
  deriving DecidableEq, Fintype

instance : Inhabited Symbol := ⟨.blank⟩

def blank : Tape Symbol := ⟨.blank,ListBlank.mk [],ListBlank.mk []⟩

def encode (bits : List Bool) : Tape Symbol :=
  ⟨.blank,ListBlank.mk (bits.map Symbol.bit++[.bottom]),ListBlank.mk []⟩

theorem blank_padding : ListBlank.mk ([Symbol.blank])=ListBlank.mk [] := by
  exact Quotient.sound' (Or.inr ⟨1,rfl⟩)

theorem initialization : (blank.write .bottom).move .right=encode [] := by
  rfl

theorem head_encode (bits : List Bool) : (encode bits).head=.blank := rfl

theorem push (bit : Bool) (bits : List Bool) :
    ((encode bits).write (.bit bit)).move .right=encode (bit::bits) := by
  simp [encode,Tape.move,Tape.write,Inhabited.default]

theorem left_empty : ((encode []).move .left).head=.bottom := rfl

theorem left_cons (bit : Bool) (bits : List Bool) :
    ((encode (bit::bits)).move .left).head=.bit bit := rfl

theorem pop (bit : Bool) (bits : List Bool) :
    ((encode (bit::bits)).move .left).write .blank=encode bits := by
  simp [encode,Tape.move,Tape.write,blank_padding]

theorem restore (bits : List Bool) :
    ((encode bits).move .left).move .right=encode bits := Tape.move_left_right _

def observed : Symbol → Option Bool
  | .bit value => some value
  | .blank | .bottom => none

theorem observed_left (bits : List Bool) :
    observed ((encode bits).move .left).head=bits.head? := by
  cases bits <;> rfl

end Controller.Complexity.SpaceWorkTape
