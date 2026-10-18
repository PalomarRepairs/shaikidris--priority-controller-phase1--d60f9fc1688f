module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Certificate.LRATAdapter

@[expose] public section

/-! Structured typed-input binding. The supported transport has a declared
variable count and ordered rows of zero-based natural identifiers with Boolean
polarities. Row order, duplicate rows, repeated literals and empty rows survive
serialization. Raw DIMACS and JSON text are rejected by this boundary. -/
namespace Controller.Certificate
open Controller.CNF

structure InputPacket where
  declaredVariables : ℕ
  rows : List (List (ℕ × Bool))
  deriving DecidableEq

namespace InputPacket

def encodeLiteral (literal : Literal (Fin varCount)) : ℕ × Bool :=
  (literal.1.val, literal.2)

def decodeLiteral (varCount : ℕ) (literal : ℕ × Bool) : Option (Literal (Fin varCount)) :=
  if lower : literal.1 < varCount then some (⟨literal.1, lower⟩, literal.2) else none

@[simp] theorem decodeLiteral_encode (literal : Literal (Fin varCount)) :
    decodeLiteral varCount (encodeLiteral literal) = some literal := by
  rcases literal with ⟨indexVar, polarity⟩
  simp [decodeLiteral, encodeLiteral, indexVar.isLt]

def decodeClause (varCount : ℕ) : List (ℕ × Bool) → Option (Clause (Fin varCount))
  | [] => some []
  | literal :: rest => do
    let decoded ← decodeLiteral varCount literal
    let tail ← decodeClause varCount rest
    pure (decoded :: tail)

@[simp] theorem decodeClause_encode (clause : Clause (Fin varCount)) :
    decodeClause varCount (clause.map encodeLiteral) = some clause := by
  induction clause with
  | nil => rfl
  | cons literal rest ih => simp [decodeClause, ih]

def decodeRows (varCount : ℕ) : List (List (ℕ × Bool)) → Option (List (Clause (Fin varCount)))
  | [] => some []
  | clause :: rest => do
    let decoded ← decodeClause varCount clause
    let tail ← decodeRows varCount rest
    pure (decoded :: tail)

@[simp] theorem decodeRows_encode (rows : List (Clause (Fin varCount))) :
    decodeRows varCount (rows.map (List.map encodeLiteral)) = some rows := by
  induction rows with
  | nil => rfl
  | cons clause rest ih => simp [decodeRows, ih]

def serialize (source : FiniteFormula varCount) : InputPacket :=
  ⟨varCount, source.clauses.toList.map (List.map encodeLiteral)⟩

def decode (varCount : ℕ) (packet : InputPacket) : Option (FiniteFormula varCount) :=
  if packet.declaredVariables = varCount then
    (decodeRows varCount packet.rows).map ofClauses else none

/-- This is equality of the complete ordered typed input, not a digest test. -/
@[simp] theorem decode_serialize (source : FiniteFormula varCount) :
    decode varCount (serialize source) = some source := by
  cases source with
  | mk rows => simp [decode, serialize, ofClauses]

/-- Supported decoding checks the declared count before examining rows. -/
theorem decode_wrong_count (packet : InputPacket) (different : packet.declaredVariables ≠ varCount) :
    decode varCount packet = none := by simp [decode, different]

end InputPacket

/-- Raw parser paths have no acceptance route in this typed adapter. -/
inductive SubmittedInput where
  | structured (packet : InputPacket)
  | dimacsText (text : String)
  | jsonText (text : String)

def checkPacket (source : FiniteFormula varCount) (packet : InputPacket)
    (certificate : Certificate varCount) : Bool :=
  if packet = InputPacket.serialize source then
    match InputPacket.decode varCount packet with
    | none => false
    | some decoded => checkTyped decoded certificate
  else false

/-- A round-tripped structured packet runs exactly the selected typed backend. -/
@[simp] theorem checkPacket_serialized (source : FiniteFormula varCount)
    (certificate : Certificate varCount) :
    checkPacket source (InputPacket.serialize source) certificate = checkTyped source certificate := by
  simp [checkPacket]

theorem checkPacket_sound (source : FiniteFormula varCount) (packet : InputPacket)
    (certificate : Certificate varCount) (accepted : checkPacket source packet certificate = true) :
    packet = InputPacket.serialize source ∧ Unsatisfiable source := by
  by_cases equal : packet = InputPacket.serialize source
  · subst packet
    exact ⟨rfl, checkTyped_sound source certificate (by simpa using accepted)⟩
  · simp [checkPacket, equal] at accepted

def checkSubmitted (source : FiniteFormula varCount) (input : SubmittedInput)
    (certificate : Certificate varCount) : Bool :=
  match input with
  | .structured packet => checkPacket source packet certificate
  | .dimacsText _ => false
  | .jsonText _ => false

@[simp] theorem dimacs_rejected (source : FiniteFormula varCount) (text : String)
    (certificate : Certificate varCount) :
    checkSubmitted source (.dimacsText text) certificate = false := rfl

@[simp] theorem json_rejected (source : FiniteFormula varCount) (text : String)
    (certificate : Certificate varCount) :
    checkSubmitted source (.jsonText text) certificate = false := rfl

theorem checkSubmitted_sound (source : FiniteFormula varCount) (input : SubmittedInput)
    (certificate : Certificate varCount) (accepted : checkSubmitted source input certificate = true) :
    ∃ packet, input = .structured packet ∧ packet = InputPacket.serialize source ∧ Unsatisfiable source := by
  cases input with
  | structured packet =>
    obtain ⟨bound, unsat⟩ := checkPacket_sound source packet certificate accepted
    exact ⟨packet, rfl, bound, unsat⟩
  | dimacsText text => simp [checkSubmitted] at accepted
  | jsonText text => simp [checkSubmitted] at accepted

end Controller.Certificate
