module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Recognition.LocalTables
public import Controller.Certificate.LRATAdapter
public import Controller.Native.ObservationProjection
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Tactic.Tauto

@[expose] public section

/-! Bounded bridge-interface records checked relative to retained driver rows.
A proposed extension table is data, not an assumed projection theorem. The
checker enumerates its declared local boundary/private domains. Its cost is
exponential in those local dimensions; a bounded interface supplies the
separate constant-size hypothesis. No global auxiliary SAT oracle is used. -/

namespace Controller.Recognition.BridgeProjection
open Controller.CNF

structure Record (boundary auxCount : Nat) where
  retained : Formula (Fin boundary)
  interface : Formula (Fin boundary ⊕ Fin auxCount)
  target : (Fin boundary → Bool) → Bool
  extension : (Fin boundary → Bool) → (Fin auxCount → Bool)

namespace Record
variable {boundary auxCount : Nat}

def joint (signals : Fin boundary → Bool) (auxiliary : Fin auxCount → Bool) :
    (Fin boundary ⊕ Fin auxCount) → Bool := Sum.elim signals auxiliary

def Valid (record : Record boundary auxCount) : Prop :=
  (∀ signals auxiliary, Satisfies signals record.retained →
    Satisfies (joint signals auxiliary) record.interface → record.target signals = true) ∧
  (∀ signals, Satisfies signals record.retained → record.target signals = true →
    Satisfies (joint signals (record.extension signals)) record.interface)

instance (record : Record boundary auxCount) : Decidable record.Valid := by
  letI : ∀ a : Fin boundary → Bool, Decidable (Satisfies a record.retained) := fun a =>
    decidable_of_iff (Controller.CNF.OrderedFormula.eval a record.retained = true)
      (satisfies_iff_stdSat a record.retained).symm
  letI : ∀ a : (Fin boundary ⊕ Fin auxCount) → Bool,
      Decidable (Satisfies a record.interface) := fun a =>
    decidable_of_iff (Controller.CNF.OrderedFormula.eval a record.interface = true)
      (satisfies_iff_stdSat a record.interface).symm
  unfold Valid
  infer_instance

def check (record : Record boundary auxCount) : Bool := decide record.Valid

@[simp] theorem check_iff (record : Record boundary auxCount) :
    record.check = true ↔ record.Valid := by simp [check]

theorem projection (record : Record boundary auxCount) (accepted : record.check = true)
    (signals : Fin boundary → Bool) (retained : Satisfies signals record.retained) :
    (∃ auxiliary, Satisfies (joint signals auxiliary) record.interface) ↔
      record.target signals = true := by
  have valid := record.check_iff.mp accepted
  constructor
  · rintro ⟨auxiliary, model⟩
    exact valid.1 signals auxiliary retained model
  · intro target
    exact ⟨record.extension signals, valid.2 signals retained target⟩

theorem advertised_lift (record : Record boundary auxCount)
    (accepted : record.check = true) (signals : Fin boundary → Bool)
    (retained : Satisfies signals record.retained) (target : record.target signals = true) :
    Satisfies (joint signals (record.extension signals)) record.interface :=
  (record.check_iff.mp accepted).2 signals retained target

end Record
end Controller.Recognition.BridgeProjection


namespace Controller.Recognition.Attachment
open Controller.CNF
open Controller.Certificate

/-- A checked entailment is an UNSAT certificate for the exact premise rows
followed by the negation of every literal of the advertised conclusion. -/
def negativeUnits (clause : Clause (Fin count)) : Formula (Fin count) :=
  ofClauses (clause.map fun literal => [negate literal])

def entailCheck (premise : Formula (Fin count)) (conclusion : Clause (Fin count))
    (certificate : Certificate count) : Bool :=
  checkTyped (premise ++ negativeUnits conclusion) certificate

theorem entailCheck_sound (premise : Formula (Fin count))
    (conclusion : Clause (Fin count)) (certificate : Certificate count)
    (accepted : entailCheck premise conclusion certificate = true) :
    Entails premise conclusion := by
  intro assignment model
  by_contra missing
  apply checkTyped_sound _ certificate accepted
  refine ⟨assignment, (satisfies_append _ _ _).mpr ⟨model, ?_⟩⟩
  apply (satisfies_ofClauses _ _).mpr
  intro clause member
  obtain ⟨literal, literalMember, rfl⟩ := List.mem_map.mp member
  refine ⟨negate literal, by simp, (literalHolds_negate assignment literal).mpr ?_⟩
  intro holds
  exact missing ⟨literal, literalMember, holds⟩

/-- Disjoint private coordinates have their own canonical finite IDs. -/
def flatten (formula : Formula (Fin boundary ⊕ Fin auxCount)) :
    Formula (Fin (boundary + auxCount)) := relabel finSumFinEquiv formula

def flattenRow (clause : Clause (Fin boundary ⊕ Fin auxCount)) :
    Clause (Fin (boundary + auxCount)) :=
  clause.map fun literal => (finSumFinEquiv literal.1, literal.2)

theorem flattened_entailment (premise : Formula (Fin boundary ⊕ Fin auxCount))
    (conclusion : Clause (Fin boundary ⊕ Fin auxCount))
    (certificate : Certificate (boundary + auxCount))
    (accepted : entailCheck (flatten premise) (flattenRow conclusion) certificate = true) :
    Entails premise conclusion := by
  intro assignment model
  let flatAssignment : Fin (boundary + auxCount) → Bool := assignment ∘ finSumFinEquiv.symm
  have flatModel : Satisfies flatAssignment (flatten premise) := by
    apply (satisfies_relabel finSumFinEquiv flatAssignment premise).mpr
    simpa [flatAssignment, Function.comp_def] using model
  obtain ⟨literal, member, holds⟩ := entailCheck_sound _ _ certificate accepted flatAssignment flatModel
  obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
  exact ⟨original, originalMember, by simpa [LiteralHolds, flatAssignment] using holds⟩

/-- `none` is a row already satisfied by a private constant; `some row` retains
all unsatisfied signal literals and their occurrences. -/
def substitutePrivate (values : Fin auxCount → Bool) :
    Clause (Fin boundary ⊕ Fin auxCount) → Option (Clause (Fin boundary))
  | [] => some []
  | (Sum.inl channel, polarity) :: rest =>
      (substitutePrivate values rest).map fun row => (channel, polarity) :: row
  | (Sum.inr channel, polarity) :: rest =>
      if values channel = polarity then none else substitutePrivate values rest

theorem substitutePrivate_sound (values : Fin auxCount → Bool)
    (signals : Fin boundary → Bool) (clause : Clause (Fin boundary ⊕ Fin auxCount)) :
    ClauseHolds (Native.ObservationProjection.joint signals values) clause ↔
      match substitutePrivate values clause with
      | none => True
      | some row => ClauseHolds signals row := by
  induction clause with
  | nil => simp [substitutePrivate]
  | cons literal rest ih =>
    rcases literal with ⟨channel, polarity⟩
    cases channel with
    | inl channel =>
      cases reduced : substitutePrivate values rest <;>
        simp [substitutePrivate, reduced, LiteralHolds,
          Native.ObservationProjection.joint] at ih ⊢ <;> tauto
    | inr channel =>
      rw [clauseHolds_cons]
      change (values channel = polarity ∨
        ClauseHolds (Native.ObservationProjection.joint signals values) rest) ↔
        match (if values channel = polarity then none else substitutePrivate values rest) with
        | none => True
        | some row => ClauseHolds signals row
      by_cases active : values channel = polarity
      · simp only [active, ite_true, true_or]
      · simp only [active, ite_false, false_or]
        exact ih

/-- Signed orientation units constrain literal values, including complemented
observations. -/
def orientationFormula (definitions : Formula (Fin boundary))
    (pair : Literal (Fin boundary) × Literal (Fin boundary)) (left right : Bool) :
    Formula (Fin boundary) :=
  definitions ++ ofClauses [[(pair.1.1, pair.1.2 == left)], [(pair.2.1, pair.2.2 == right)]]

theorem orientationFormula_model (definitions : Formula (Fin boundary))
    (pair : Literal (Fin boundary) × Literal (Fin boundary)) (left right : Bool)
    (signals : Fin boundary → Bool) (model : Satisfies signals definitions)
    (first : literalValue signals pair.1 = left) (second : literalValue signals pair.2 = right) :
    Satisfies signals (orientationFormula definitions pair left right) := by
  apply (satisfies_append _ _ _).mpr
  refine ⟨model, ?_⟩
  rcases pair with ⟨⟨x, xp⟩, ⟨y, yp⟩⟩
  simp only [literalValue] at first second
  have decodeBool (value polarity outcome : Bool) (equation : (value == polarity) = outcome) :
      value = (polarity == outcome) := by
    cases value <;> cases polarity <;> cases outcome <;> simp_all
  have xValue : signals x = (xp == left) := decodeBool _ _ _ first
  have yValue : signals y = (yp == right) := decodeBool _ _ _ second
  simp [satisfies_ofClauses, ClauseHolds, LiteralHolds, xValue, yValue]

inductive OrientationEvidence (boundary auxCount rows : Nat) where
  | impossible (certificate : Certificate boundary)
  | extension (values : Fin auxCount → Bool)
      (certificates : Fin rows → Certificate boundary)

/-- Certificate size is supplied data. Checking these certificates does not
search for auxiliary models or promise a polynomial-size certificate for every
arbitrary wrapper. All rows refer to the original ordered wrapper array. -/
def orientationCheck (definitions : Formula (Fin boundary))
    (wrapper : Formula (Fin boundary ⊕ Fin auxCount))
    (pair : Literal (Fin boundary) × Literal (Fin boundary)) (left right : Bool) :
    OrientationEvidence boundary auxCount wrapper.clauses.size → Bool
  | .impossible certificate => checkTyped (orientationFormula definitions pair left right) certificate
  | .extension values certificates =>
      letI : ∀ i : Fin wrapper.clauses.size, Decidable
          (match substitutePrivate values wrapper.clauses[i] with
          | none => True
          | some row => entailCheck (orientationFormula definitions pair left right) row (certificates i) = true) :=
        fun i => by
          cases reduced : substitutePrivate values wrapper.clauses[i] <;>
            simp only [reduced] <;> infer_instance
      decide (∀ i : Fin wrapper.clauses.size,
        match substitutePrivate values wrapper.clauses[i] with
        | none => True
        | some row => entailCheck (orientationFormula definitions pair left right) row (certificates i) = true)

theorem orientationCheck_sound (definitions : Formula (Fin boundary))
    (wrapper : Formula (Fin boundary ⊕ Fin auxCount))
    (pair : Literal (Fin boundary) × Literal (Fin boundary)) (left right : Bool)
    (evidence : OrientationEvidence boundary auxCount wrapper.clauses.size)
    (accepted : orientationCheck definitions wrapper pair left right evidence = true) :
    (¬∃ signals, Satisfies signals definitions ∧ literalValue signals pair.1 = left ∧
      literalValue signals pair.2 = right) ∨
    ∃ values, ∀ signals, Satisfies signals definitions → literalValue signals pair.1 = left →
      literalValue signals pair.2 = right →
      Satisfies (Native.ObservationProjection.joint signals values) wrapper := by
  cases evidence with
  | impossible certificate =>
    apply Or.inl
    rintro ⟨signals, model, first, second⟩
    exact checkTyped_sound _ certificate accepted
      ⟨signals, orientationFormula_model definitions pair left right signals model first second⟩
  | extension values certificates =>
    apply Or.inr
    refine ⟨values, ?_⟩
    intro signals model first second
    have orientation := orientationFormula_model definitions pair left right signals model first second
    have allRows : ∀ i : Fin wrapper.clauses.size,
        match substitutePrivate values wrapper.clauses[i] with
        | none => True
        | some row => entailCheck (orientationFormula definitions pair left right) row (certificates i) = true := by
      simpa [orientationCheck] using accepted
    rw [satisfies_iff_rows]
    intro i
    apply (substitutePrivate_sound values signals wrapper.clauses[i]).mpr
    have rowCheck := allRows i
    cases reduced : substitutePrivate values wrapper.clauses[i] with
    | none => simp [reduced]
    | some row =>
      have rowAccepted : entailCheck (orientationFormula definitions pair left right) row
          (certificates i) = true := by simpa only [reduced] using rowCheck
      exact entailCheck_sound _ row (certificates i) rowAccepted signals orientation


/-- Every guard conclusion, activity disjunction, and uniform extension is
backed by an independently replayed certificate on exact finite premises. -/
structure WrapperRecord (boundary auxCount observations : Nat) where
  definitions : Formula (Fin boundary)
  wrapper : Formula (Fin boundary ⊕ Fin auxCount)
  pairs : Fin observations → Literal (Fin boundary) × Literal (Fin boundary)
  activities : Fin observations → Fin auxCount
  selected : List (Fin observations)
  guards : Fin observations → Fin 2 → Certificate (boundary + auxCount)
  necessity : Certificate (boundary + auxCount)
  orientations : Fin observations → Bool → Bool →
    OrientationEvidence boundary auxCount wrapper.clauses.size

namespace WrapperRecord
variable {boundary auxCount observations : Nat}

def guardRow (record : WrapperRecord boundary auxCount observations)
    (i : Fin observations) (slot : Fin 2) : Clause (Fin boundary ⊕ Fin auxCount) :=
  (Native.ObservationProjection.guardRows (record.activities i) (record.pairs i))[slot.val]'(by
    simpa [Native.ObservationProjection.guardRows] using slot.isLt)

def necessaryRow (record : WrapperRecord boundary auxCount observations) :
    Clause (Fin boundary ⊕ Fin auxCount) :=
  record.selected.map fun i => (Sum.inr (record.activities i), true)

def Checks (record : WrapperRecord boundary auxCount observations) : Prop :=
  (∀ i slot, entailCheck (flatten record.wrapper) (flattenRow (record.guardRow i slot))
    (record.guards i slot) = true) ∧
  entailCheck (flatten record.wrapper) (flattenRow record.necessaryRow) record.necessity = true ∧
  (∀ i left right, i ∈ record.selected → left ≠ right →
    orientationCheck record.definitions record.wrapper (record.pairs i) left right
      (record.orientations i left right) = true)

instance (record : WrapperRecord boundary auxCount observations) : Decidable record.Checks := by
  unfold Checks
  infer_instance

def check (record : WrapperRecord boundary auxCount observations) : Bool := decide record.Checks

@[simp] theorem check_iff (record : WrapperRecord boundary auxCount observations) :
    record.check = true ↔ record.Checks := by simp [check]

theorem checked_contract (record : WrapperRecord boundary auxCount observations)
    (accepted : record.check = true) :
    Native.ObservationProjection.ProjectionContract record.definitions record.wrapper
      record.pairs (fun i => (record.activities i, true)) {i | i ∈ record.selected} := by
  have checks := record.check_iff.mp accepted
  refine ⟨?_, ?_, ?_⟩
  · intro signals auxiliary model i active
    apply (Native.ObservationProjection.guardRows_iff (record.activities i) (record.pairs i)
      signals auxiliary).mp ?_ active
    apply (satisfies_ofClauses _ _).mpr
    intro clause member
    have first := flattened_entailment record.wrapper (record.guardRow i ⟨0, by decide⟩)
      (record.guards i ⟨0, by decide⟩) (checks.1 i ⟨0, by decide⟩) _ model
    have second := flattened_entailment record.wrapper (record.guardRow i ⟨1, by decide⟩)
      (record.guards i ⟨1, by decide⟩) (checks.1 i ⟨1, by decide⟩) _ model
    simp only [Native.ObservationProjection.guardRows, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · simpa [guardRow, Native.ObservationProjection.guardRows] using first
    · simpa [guardRow, Native.ObservationProjection.guardRows] using second
  · intro signals auxiliary model
    obtain ⟨literal, member, holds⟩ := flattened_entailment record.wrapper record.necessaryRow
      record.necessity checks.2.1 _ model
    obtain ⟨i, selected, rfl⟩ := List.mem_map.mp member
    exact ⟨i, selected, holds⟩
  · intro i selected left right different
    exact orientationCheck_sound record.definitions record.wrapper (record.pairs i) left right
      (record.orientations i left right) (checks.2.2 i left right selected different)

theorem checked_projection (record : WrapperRecord boundary auxCount observations)
    (accepted : record.check = true) (signals : Fin boundary → Bool)
    (model : Satisfies signals record.definitions) :
    (∃ auxiliary, Satisfies (Native.ObservationProjection.joint signals auxiliary) record.wrapper) ↔
      ∃ i ∈ record.selected, Native.ObservationProjection.Discrepant signals (record.pairs i) :=
  Native.ObservationProjection.observation_projection (record.checked_contract accepted) signals model

end WrapperRecord

namespace TargetLink

/-- Detection is related to the declared observed root pairs by checked
orientation consequences and a checked all-equal contradiction. -/
structure Record (boundary observations : Nat) where
  definitions : Formula (Fin boundary)
  target : Literal (Fin boundary)
  pairs : Fin observations → Literal (Fin boundary) × Literal (Fin boundary)
  selected : List (Fin observations)
  forward : Fin observations → Bool → Bool → Certificate boundary
  necessary : Certificate boundary

namespace Record
variable {boundary observations : Nat}

def equalFormula (record : Record boundary observations) : Formula (Fin boundary) :=
  ofClauses (record.selected.flatMap fun i =>
    (Gate.alias (record.pairs i).2).clauses (record.pairs i).1)

def contradictionFormula (record : Record boundary observations) : Formula (Fin boundary) :=
  (record.definitions ++ ofClauses [[record.target]]) ++ record.equalFormula

def Checks (record : Record boundary observations) : Prop :=
  (∀ i left right, i ∈ record.selected → left ≠ right →
    entailCheck (orientationFormula record.definitions (record.pairs i) left right)
      [record.target] (record.forward i left right) = true) ∧
  checkTyped record.contradictionFormula record.necessary = true

instance (record : Record boundary observations) : Decidable record.Checks := by
  unfold Checks
  infer_instance

def check (record : Record boundary observations) : Bool := decide record.Checks

@[simp] theorem check_iff (record : Record boundary observations) :
    record.check = true ↔ record.Checks := by simp [check]

theorem checked_target_iff (record : Record boundary observations)
    (accepted : record.check = true) (signals : Fin boundary → Bool)
    (model : Satisfies signals record.definitions) :
    LiteralHolds signals record.target ↔
      ∃ i ∈ record.selected, Native.ObservationProjection.Discrepant signals (record.pairs i) := by
  have checks := record.check_iff.mp accepted
  constructor
  · intro target
    by_contra missing
    have equal : ∀ i ∈ record.selected,
        literalValue signals (record.pairs i).1 = literalValue signals (record.pairs i).2 := by
      intro i member
      by_contra difference
      exact missing ⟨i, member, difference⟩
    apply checkTyped_sound _ record.necessary checks.2
    refine ⟨signals, (satisfies_append _ _ _).mpr ⟨?_, ?_⟩⟩
    · apply (satisfies_append _ _ _).mpr
      refine ⟨model, (satisfies_ofClauses _ _).mpr ?_⟩
      intro row member
      simp only [List.mem_singleton] at member
      subst row
      exact ⟨record.target, by simp, target⟩
    · apply (satisfies_ofClauses _ _).mpr
      intro row member
      obtain ⟨i, selected, rowMember⟩ := List.mem_flatMap.mp member
      have equalityModel : Satisfies signals
          (Gate.block (record.pairs i).1 (.alias (record.pairs i).2)) := by
        apply (Gate.block_correct _ _ _).mpr
        exact equal i selected
      exact (satisfies_ofClauses _ _).mp equalityModel row rowMember
  · rintro ⟨i, selected, different⟩
    have premise := orientationFormula_model record.definitions (record.pairs i)
      (literalValue signals (record.pairs i).1) (literalValue signals (record.pairs i).2)
      signals model rfl rfl
    have targetRow := entailCheck_sound _ [record.target]
      (record.forward i _ _) (checks.1 i _ _ selected different) signals premise
    simpa [ClauseHolds] using targetRow

end Record
end TargetLink

theorem orientation_extension_model (definitions : Formula (Fin boundary))
    (wrapper : Formula (Fin boundary ⊕ Fin auxCount))
    (pair : Literal (Fin boundary) × Literal (Fin boundary)) (left right : Bool)
    (values : Fin auxCount → Bool) (certificates : Fin wrapper.clauses.size → Certificate boundary)
    (accepted : orientationCheck definitions wrapper pair left right (.extension values certificates) = true)
    (signals : Fin boundary → Bool) (model : Satisfies signals definitions)
    (first : literalValue signals pair.1 = left) (second : literalValue signals pair.2 = right) :
    Satisfies (Native.ObservationProjection.joint signals values) wrapper := by
  have orientation := orientationFormula_model definitions pair left right signals model first second
  have allRows : ∀ i : Fin wrapper.clauses.size,
      match substitutePrivate values wrapper.clauses[i] with
      | none => True
      | some row => entailCheck (orientationFormula definitions pair left right) row (certificates i) = true := by
    simpa [orientationCheck] using accepted
  rw [satisfies_iff_rows]
  intro i
  apply (substitutePrivate_sound values signals wrapper.clauses[i]).mpr
  have rowCheck := allRows i
  cases reduced : substitutePrivate values wrapper.clauses[i] with
  | none => trivial
  | some row =>
    have checked : entailCheck (orientationFormula definitions pair left right) row
        (certificates i) = true := by simpa only [reduced] using rowCheck
    exact entailCheck_sound _ row (certificates i) checked signals orientation

namespace WrapperRecord
variable {boundary auxCount observations : Nat}

instance (signals : Fin boundary → Bool)
    (pair : Literal (Fin boundary) × Literal (Fin boundary)) :
    Decidable (Native.ObservationProjection.Discrepant signals pair) := by
  unfold Native.ObservationProjection.Discrepant
  infer_instance

def extension (record : WrapperRecord boundary auxCount observations)
    (signals : Fin boundary → Bool) : Fin auxCount → Bool :=
  match record.selected.find? (fun i => decide
      (Native.ObservationProjection.Discrepant signals (record.pairs i))) with
  | none => fun _ => false
  | some i =>
      match record.orientations i (literalValue signals (record.pairs i).1)
          (literalValue signals (record.pairs i).2) with
      | .impossible _ => fun _ => false
      | .extension values _ => values

theorem checked_extension (record : WrapperRecord boundary auxCount observations)
    (accepted : record.check = true) (signals : Fin boundary → Bool)
    (model : Satisfies signals record.definitions)
    (detects : ∃ i ∈ record.selected, Native.ObservationProjection.Discrepant signals (record.pairs i)) :
    Satisfies (Native.ObservationProjection.joint signals (record.extension signals)) record.wrapper := by
  have checks := record.check_iff.mp accepted
  have found : (record.selected.find? (fun i => decide
      (Native.ObservationProjection.Discrepant signals (record.pairs i)))).isSome := by
    apply List.find?_isSome.mpr
    obtain ⟨i, member, different⟩ := detects
    exact ⟨i, member, by simpa using different⟩
  cases selected : record.selected.find? (fun i => decide
      (Native.ObservationProjection.Discrepant signals (record.pairs i))) with
  | none => simp [selected] at found
  | some i =>
    have member := List.mem_of_find?_eq_some selected
    have different : Native.ObservationProjection.Discrepant signals (record.pairs i) := by
      simpa using List.find?_some selected
    have orientationAccepted := checks.2.2 i _ _ member different
    have premise := orientationFormula_model record.definitions (record.pairs i)
        (literalValue signals (record.pairs i).1) (literalValue signals (record.pairs i).2)
      signals model rfl rfl
    cases evidence : record.orientations i (literalValue signals (record.pairs i).1)
        (literalValue signals (record.pairs i).2) with
    | impossible certificate =>
      have checked : checkTyped (orientationFormula record.definitions (record.pairs i)
        (literalValue signals (record.pairs i).1) (literalValue signals (record.pairs i).2))
          certificate = true := by simpa [evidence, orientationCheck] using orientationAccepted
      exact False.elim (checkTyped_sound _ certificate checked ⟨signals, premise⟩)
    | extension values certificates =>
      have checked : orientationCheck record.definitions record.wrapper (record.pairs i)
          (literalValue signals (record.pairs i).1) (literalValue signals (record.pairs i).2)
          (.extension values certificates) = true := by simpa only [evidence] using orientationAccepted
      simpa only [extension, selected, evidence] using
        orientation_extension_model record.definitions record.wrapper (record.pairs i)
          (literalValue signals (record.pairs i).1) (literalValue signals (record.pairs i).2)
          values certificates checked signals model rfl rfl

end WrapperRecord
end Controller.Recognition.Attachment
