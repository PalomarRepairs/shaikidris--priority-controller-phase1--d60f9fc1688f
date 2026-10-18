module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.SpaceMachine

@[expose] public section

/-! An immutable ordinary input tape with start/end markers. The source zipper
is represented literally by the cells on either side of the input head.
Start tests and clamped movement use only observed symbols and head moves. -/
namespace Controller.Complexity.SpaceInputTape
open Turing

inductive Symbol
  | blank
  | start
  | stop
  | bit (value : Bool)
  deriving DecidableEq, Fintype

instance : Inhabited Symbol := ⟨.blank⟩

def encode (source : ReadOnlyInput.Tape) : Tape Symbol :=
  Tape.mk₂ (source.left.map Symbol.bit++[.start]) (source.right.map Symbol.bit++[.stop])

def observed : Symbol → Option Bool
  | .bit value => some value
  | _ => none

theorem symbol (source : ReadOnlyInput.Tape) :
    observed (encode source).head=ReadOnlyInput.symbol source := by
  cases source with
  | mk left right => cases right <;> rfl

theorem start (source : ReadOnlyInput.Tape) :
    ((encode source).move .left).head=.start ↔ source.left=[] := by
  cases source with
  | mk left right => cases left <;> simp [encode,Tape.mk₂,Tape.mk',Tape.move]

theorem right_cons (left : List Bool) (bit : Bool) (right : List Bool) :
    (encode ⟨left,bit::right⟩).move .right=encode ⟨bit::left,right⟩ := by
  simp only [encode,Tape.mk₂,List.map_cons,List.cons_append,Tape.move_right_mk',
    ListBlank.head_mk,List.headI_cons,ListBlank.tail_mk,List.tail_cons,ListBlank.cons_mk]

theorem left_cons (left : List Bool) (bit : Bool) (right : List Bool) :
    (encode ⟨bit::left,right⟩).move .left=encode ⟨left,bit::right⟩ := by
  simp only [encode,Tape.mk₂,List.map_cons,List.cons_append,Tape.move_left_mk',
    ListBlank.head_mk,List.headI_cons,ListBlank.tail_mk,List.tail_cons,ListBlank.cons_mk]

theorem left_clamped (source : ReadOnlyInput.Tape) :
    (if ((encode source).move .left).head=.start then
      ((encode source).move .left).move .right else (encode source).move .left)=
      encode (ReadOnlyInput.moveLeft source) := by
  cases source with
  | mk left right =>
    cases left with
    | nil => simp [start,ReadOnlyInput.moveLeft]
    | cons bit rest =>
      rw [ite_eq_right (by rw [start]; simp)]
      exact left_cons rest bit right

theorem right_clamped (source : ReadOnlyInput.Tape) :
    (if (encode source).head=.stop then encode source else (encode source).move .right)=
      encode (ReadOnlyInput.moveRight source) := by
  cases source with
  | mk left right =>
    cases right with
    | nil => simp [encode,Tape.mk₂,Tape.mk',ReadOnlyInput.moveRight]
    | cons bit rest =>
      have current : (encode ⟨left,bit::rest⟩).head=Symbol.bit bit := rfl
      simp [current,ReadOnlyInput.moveRight,right_cons]

end Controller.Complexity.SpaceInputTape
