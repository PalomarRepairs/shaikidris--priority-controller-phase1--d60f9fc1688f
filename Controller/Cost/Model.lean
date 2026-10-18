module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Basic.Sizes

@[expose] public section

/-! An indexed-word machine. Each transition executes one specified primitive.
The heap is a contiguous allocation; releasing its last word shrinks storage.
Stack and output words are charged separately. Array access is a primitive of
this model; a simulation into a standard machine is a separate obligation. -/
namespace Controller.Cost

abbrev Word (width : Nat) := Fin (2 ^ width)

def word (width value : Nat) : Word width :=
  ⟨value % (2 ^ width), Nat.mod_lt _ (Nat.two_pow_pos width)⟩

structure State (width registers : Nat) where
  reg : Fin registers → Word width
  heap : Array (Word width)
  stack : List (Word width)
  output : List (Word width)
  pc : Word width
  halted : Bool

def State.liveWords (s : State width registers) : Nat :=
  registers + s.heap.size + s.stack.length + s.output.length + 1

inductive Instruction (width registers : Nat) where
  | constant (dst : Fin registers) (value : Word width)
  | copy (dst src : Fin registers)
  | add (dst left right : Fin registers)
  | xor (dst left right : Fin registers)
  | load (dst address : Fin registers)
  | store (address src : Fin registers)
  | allocate (src : Fin registers)
  | release
  | push (src : Fin registers)
  | pop (dst : Fin registers)
  | emit (src : Fin registers)
  | branchZero (src : Fin registers) (target : Word width)
  | halt

/-- Arithmetic is a distinguished subset of primitive operations; indexed
memory and output operations still count as machine steps. -/
def Instruction.arithmeticOps : Instruction width registers → Nat
  | .add .. | .xor .. => 1
  | _ => 0

def State.put (s : State width registers) (dst : Fin registers)
    (value : Word width) : State width registers :=
  { s with reg := fun i => if i = dst then value else s.reg i }

def State.advance (s : State width registers) : State width registers :=
  { s with pc := word width (s.pc.val + 1) }

/-- Invalid reads, writes, stack pops and releases have no transition.
A halted state also has no further transition. -/
def step (instruction : Instruction width registers) (s : State width registers) :
    Option (State width registers) :=
  if s.halted then none else
  let next := s.advance
  match instruction with
  | .constant dst value => some (next.put dst value)
  | .copy dst src => some (next.put dst (s.reg src))
  | .add dst left right => some (next.put dst (word width ((s.reg left).val + (s.reg right).val)))
  | .xor dst left right => some (next.put dst (word width (Nat.xor (s.reg left).val (s.reg right).val)))
  | .load dst address =>
      if h : (s.reg address).val < s.heap.size then
        some (next.put dst s.heap[(s.reg address).val]) else none
  | .store address src =>
      if h : (s.reg address).val < s.heap.size then
        some { next with heap := s.heap.set (s.reg address).val (s.reg src) } else none
  | .allocate src =>
      if s.heap.size < 2 ^ width then some { next with heap := s.heap.push (s.reg src) }
      else none
  | .release => if s.heap.isEmpty then none else some { next with heap := s.heap.pop }
  | .push src => some { next with stack := s.reg src :: s.stack }
  | .pop dst => match s.stack with
      | [] => none
      | value :: rest => some { next.put dst value with stack := rest }
  | .emit src => some { next with output := s.reg src :: s.output }
  | .branchZero src target =>
      some (if (s.reg src).val = 0 then { next with pc := target } else next)
  | .halt => some { next with halted := true }

abbrev Program (width registers : Nat) := Array (Instruction width registers)

/-- Fixed program storage is charged in addition to dynamic state storage:
one opcode and at most three operand words per instruction. -/
def programWords (p : Program width registers) : Nat := 4 * p.size

def residentWords (p : Program width registers) (s : State width registers) : Nat :=
  programWords p + s.liveWords

def residentBits (p : Program width registers) (s : State width registers) : Nat :=
  width * residentWords p s

/-- Instruction identifiers, addresses and the initial contiguous heap must
fit the declared word width. This is a representation hypothesis for simulations. -/
def Representable (p : Program width registers) (s : State width registers) : Prop :=
  registers ≤ 2 ^ width ∧ p.size ≤ 2 ^ width ∧ s.heap.size ≤ 2 ^ width

structure InputMeasure where
  declaredVariables : Nat
  representedNodes : Nat
  incidences : Nat
  serializedBits : Nat

def InputMeasure.combinatorial (m : InputMeasure) : Nat :=
  m.declaredVariables + m.representedNodes + m.incidences

/-- Output words remain live in the state and therefore count toward peak
storage even when a consumer has not yet serialized them. -/
def outputWords (s : State width registers) : Nat := s.output.length

def programStep (p : Program width registers) (s : State width registers) :
    Option (State width registers) := do
  let instruction ← p[s.pc.val]?
  step instruction s

/-- A proof trace consists of genuine successive machine transitions. -/
inductive Execution (p : Program width registers) :
    State width registers → State width registers → Nat → Nat → Prop where
  | refl (s) : Execution p s s 0 s.liveWords
  | cons {s middle final ticks peak}
      (transition : programStep p s = some middle)
      (rest : Execution p middle final ticks peak) :
      Execution p s final (ticks + 1) (max s.liveWords peak)

end Controller.Cost
