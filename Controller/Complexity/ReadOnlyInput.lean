module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.Reductions

@[expose] public section

/-! A two-way read-only input head represented by two binary lists. The left
list stores the already passed prefix in reverse order. Moving at either end
stays at that end; every movement preserves the exact original input word. -/
namespace Controller.Complexity.ReadOnlyInput

structure Tape where
  left : List Bool
  right : List Bool
  deriving DecidableEq

def start (input : List Bool) : Tape := ⟨[],input⟩
def word (tape : Tape) := tape.left.reverse++tape.right
def position (tape : Tape) := tape.left.length
def symbol (tape : Tape) := tape.right.head?

def moveLeft (tape : Tape) : Tape :=
  match tape.left with
  | [] => tape
  | bit :: rest => ⟨rest,bit :: tape.right⟩

def moveRight (tape : Tape) : Tape :=
  match tape.right with
  | [] => tape
  | bit :: rest => ⟨bit :: tape.left,rest⟩

@[simp] theorem word_start (input : List Bool) : word (start input)=input := rfl

@[simp] theorem word_moveLeft (tape : Tape) : word (moveLeft tape)=word tape := by
  rcases tape with ⟨left,right⟩
  cases left <;> simp [moveLeft,word,List.append_assoc]

@[simp] theorem word_moveRight (tape : Tape) : word (moveRight tape)=word tape := by
  rcases tape with ⟨left,right⟩
  cases right <;> simp [moveRight,word,List.append_assoc]

theorem length (tape : Tape) : tape.left.length+tape.right.length=(word tape).length := by
  simp [word]

theorem position_le (tape : Tape) : position tape ≤ (word tape).length := by
  have size := length tape
  unfold position
  omega

theorem left_eq (tape : Tape) : tape.left=((word tape).take (position tape)).reverse := by
  simp [word,position]

theorem right_eq (tape : Tape) : tape.right=(word tape).drop (position tape) := by
  simp [word,position]

theorem ext_word_position {first second : Tape}
    (sameWord : word first=word second) (samePosition : position first=position second) : first=second := by
  have left : first.left=second.left := by rw [left_eq first,left_eq second,sameWord,samePosition]
  have right : first.right=second.right := by rw [right_eq first,right_eq second,sameWord,samePosition]
  cases first
  cases second
  cases left
  cases right
  rfl

theorem position_left (tape : Tape) : position (moveLeft tape)=position tape-1 := by
  rcases tape with ⟨left,right⟩
  cases left <;> simp [moveLeft,position]

theorem position_right (tape : Tape) : position (moveRight tape)=min (position tape+1) (word tape).length := by
  rcases tape with ⟨left,right⟩
  cases right <;> simp [moveRight,position,word]

theorem symbol_eq (tape : Tape) : symbol tape=(word tape)[position tape]? := by
  rw [symbol,right_eq]
  simp

end Controller.Complexity.ReadOnlyInput
