module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.LocalUnitCases
public import Controller.NativeProof.SourceStageXor
public import Controller.NativeProof.SourceBusSchedule

@[expose] public section

/-! Bounded native XOR identities. Local cases use the four actual XOR rows,
earlier units or equality clauses, and actual NOT rows. Literal identities
contribute no fabricated premise. -/
namespace Controller.NativeProof.XorUnits
open Controller.CNF Controller.Resolution
open Controller.NativeProof.FoldProjection Controller.NativeProof.LocalUnitCases
open Controller.NativeProof.SourceStageCongruence Controller.NativeProof.SourceStageXor
open Controller.NativeProof.SourceBusSchedule
open Controller.NativeProof.SourceStagePolarity
variable {v : Nat} {state : State v} {context : Clause (Fin v)}

def contextual (row : AvailableSubclause state clause) : Premise state context :=
  ⟨clause, retarget row (fun _ member => List.mem_append_right _ member)⟩

def xorPremises (rows : XorRows state a b output) : List (Premise state context) :=
  [contextual rows.zeroZero, contextual rows.oneOne,
   contextual rows.zeroOne, contextual rows.oneZero]

theorem xorPremises_value (rows : XorRows state a b output) (values : Fin v → Bool)
    (all : ∀ premise ∈ xorPremises (context := context) rows, ClauseHolds values premise.clause) :
    literalValue values output = (literalValue values a ^^ literalValue values b) := by
  have first := all (contextual rows.zeroZero) (by simp [xorPremises])
  have second := all (contextual rows.oneOne) (by simp [xorPremises])
  have third := all (contextual rows.zeroOne) (by simp [xorPremises])
  have fourth := all (contextual rows.oneZero) (by simp [xorPremises])
  have satisfied : Satisfies values (Gate.block output (.xor a b)) := by
    rw [Gate.block, satisfies_ofClauses]
    intro clause member
    simp only [Gate.clauses, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact first
    · exact second
    · exact third
    · exact fourth
  exact (Gate.block_correct values output (.xor a b)).mp satisfied

theorem valueLiteral_holds (values : Fin v → Bool) (literal : Literal (Fin v)) (bit : Bool) :
    LiteralHolds values (valueLiteral literal bit) ↔ literalValue values literal = bit := by
  cases bit <;> simp [valueLiteral]

def fixed (state : State v) (context : Clause (Fin v)) (a b output : Literal (Fin v))
    (rows : XorRows state a b output) (x y : Bool)
    (first : AvailableSubclause state (context ++ [valueLiteral a x]))
    (second : AvailableSubclause state (context ++ [valueLiteral b y])) :
    SubclauseProjection state (context ++ [valueLiteral output (x ^^ y)]) 3 := by
  let premises : List (Premise state context) := xorPremises rows ++
    [⟨[valueLiteral a x], first⟩, ⟨[valueLiteral b y], second⟩]
  have entails : EntailsUnit premises (valueLiteral output (x ^^ y)) := by
    intro values all
    have xor := xorPremises_value rows values (fun p member => all p (List.mem_append_left _ member))
    have aTrue := all ⟨[valueLiteral a x], first⟩ (by simp [premises])
    have bTrue := all ⟨[valueLiteral b y], second⟩ (by simp [premises])
    have aValue := (valueLiteral_holds values a x).mp (by simpa using aTrue)
    have bValue := (valueLiteral_holds values b y).mp (by simpa using bTrue)
    apply (valueLiteral_holds values output (x ^^ y)).mpr
    rw [xor, aValue, bValue]
  have covers : Covers premises [valueLiteral output (x ^^ y)] [a.1, b.1] := by
    intro premise member literal present
    cases x <;> cases y <;>
      simp only [premises, xorPremises, contextual, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at member <;>
      rcases member with ⟨rfl | rfl | rfl | rfl⟩ | ⟨rfl | rfl⟩ <;>
      simp only [valueLiteral, Bool.false_eq_true, ite_false, ite_true, labelsOf,
        List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
        negate, Std.Sat.Literal.negate] at present ⊢ <;> aesop
  exact unitUsing state context premises (valueLiteral output (x ^^ y)) entails [a.1, b.1] covers

def transferPremises (transfer : GuardedTransfer state context input output) :
    List (Premise state context) :=
  match transfer with
  | .identity _ => []
  | .derived row => [⟨[negate input, output], row⟩]

theorem transfer_holds (transfer : GuardedTransfer state context input output)
    (values : Fin v → Bool)
    (all : ∀ p ∈ transferPremises transfer, ClauseHolds values p.clause) :
    LiteralHolds values input → LiteralHolds values output := by
  cases transfer with
  | identity same => rw [same]; exact id
  | derived row =>
    have clause := all ⟨[negate input, output], row⟩ (by simp [transferPremises])
    intro held
    have alternatives : ¬LiteralHolds values input ∨ LiteralHolds values output := by simpa using clause
    exact alternatives.resolve_left (fun no => no held)

def pairPremises (pair : DirectionPair state context left right) : List (Premise state context) :=
  transferPremises pair.forward ++ transferPremises pair.backward

theorem pair_value (pair : DirectionPair state context left right) (values : Fin v → Bool)
    (all : ∀ p ∈ pairPremises pair, ClauseHolds values p.clause) :
    literalValue values left = literalValue values right := by
  have forward := transfer_holds pair.forward values
    (fun p member => all p (List.mem_append_left _ member))
  have backward := transfer_holds pair.backward values
    (fun p member => all p (List.mem_append_right _ member))
  cases first : literalValue values left <;> cases second : literalValue values right <;>
    simp_all [literalValue_eq_true, literalValue_eq_false]

theorem xor_labels (rows : XorRows state a b output) (premise : Premise state context)
    (member : premise ∈ xorPremises rows) (literal : Literal (Fin v))
    (present : literal ∈ premise.clause) : literal.1 ∈ [a.1, b.1, output.1] := by
  simp only [xorPremises, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;>
    simp only [contextual, List.mem_cons, List.not_mem_nil, or_false] at present <;>
    rcases present with rfl | rfl | rfl <;> simp [negate, Std.Sat.Literal.negate]

theorem transfer_labels (transfer : GuardedTransfer state context input output)
    (premise : Premise state context) (member : premise ∈ transferPremises transfer)
    (literal : Literal (Fin v)) (present : literal ∈ premise.clause) :
    literal.1 ∈ [input.1, output.1] := by
  cases transfer with
  | identity => simp [transferPremises] at member
  | derived row =>
    have same : premise = ⟨[negate input, output], row⟩ := by simpa [transferPremises] using member
    subst premise
    simp only [List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl <;> simp [negate, Std.Sat.Literal.negate]

/-- A flag equal to a local term and the term's actual NOT output have XOR
one. At most three local variables are split; no extension variable is used. -/
def complementary (state : State v) (context : Clause (Fin v))
    (a b term output : Literal (Fin v)) (rows : XorRows state a b output)
    (notRows : NotRows state term b) (equal : DirectionPair state context a term) :
    SubclauseProjection state (context ++ [output]) 7 := by
  let premises : List (Premise state context) := xorPremises rows ++
    [contextual notRows.positive, contextual notRows.negative] ++ pairPremises equal
  have entails : EntailsUnit premises output := by
    intro values all
    have xor := xorPremises_value rows values (fun p member => all p
      (List.mem_append_left _ (List.mem_append_left _ member)))
    have pos := all (contextual notRows.positive) (by simp [premises])
    have neg := all (contextual notRows.negative) (by simp [premises])
    have notModel : Satisfies values (Gate.block b (.not term)) := by
      rw [Gate.block, satisfies_ofClauses]
      intro clause member
      simp only [Gate.clauses, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact pos
      · exact neg
    have notValue := (Gate.block_correct values b (.not term)).mp notModel
    have same := pair_value equal values (fun p member => all p (List.mem_append_right _ member))
    apply (literalValue_eq_true _ _).mp
    rw [xor, same, show literalValue values b = !literalValue values term from notValue]
    cases literalValue values term <;> rfl
  have covers : Covers premises [output] [a.1, b.1, term.1] := by
    intro premise member literal present
    rcases List.mem_append.mp member with before | pairs
    · rcases List.mem_append.mp before with gate | negations
      · have allowed := xor_labels rows premise gate literal present
        simp only [List.mem_cons, List.not_mem_nil, or_false] at allowed
        simp only [labelsOf, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false]
        aesop
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at negations
        rcases negations with rfl | rfl <;>
          simp only [contextual, List.mem_cons, List.not_mem_nil, or_false] at present <;>
          rcases present with rfl | rfl <;> simp [labelsOf, negate, Std.Sat.Literal.negate]
    · rcases List.mem_append.mp pairs with first | second
      · have allowed := transfer_labels equal.forward premise first literal present
        simp only [List.mem_cons, List.not_mem_nil, or_false] at allowed
        simp only [labelsOf, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false]
        aesop
      · have allowed := transfer_labels equal.backward premise second literal present
        simp only [List.mem_cons, List.not_mem_nil, or_false] at allowed
        simp only [labelsOf, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false]
        aesop
  exact unitUsing state context premises output entails [a.1, b.1, term.1] covers

end Controller.NativeProof.XorUnits
