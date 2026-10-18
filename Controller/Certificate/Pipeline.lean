module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Certificate.InputBinding
public import Controller.Certificate.ModelCheck
public import Controller.Recognition.FamilyRecord
public import Controller.Native.Lift

@[expose] public section

/-! Exact-input answer validation and guarded-family SAT production. The transport
boundary accepts structured typed packets. Byte strings have no parser or acceptance
route here. Recognition failure and incomplete solver results remain nonanswers;
an UNSAT answer always requires a certificate checked against the original input. -/
namespace Controller.Certificate.Pipeline
open Controller Controller.CNF

/-- Untrusted solver results, including explicit nonanswer states. -/
inductive Candidate (varCount : Nat) where
  | sat (assignment : Fin varCount → Bool)
  | unsat (certificate : Certificate varCount)
  | outside
  | invalid
  | timeout

/-- Only these two outcomes assert a mathematical answer. -/
inductive Verdict where
  | sat
  | unsat
  | outside
  | invalid
  | timeout
  deriving DecidableEq, Repr

/-- Full ordered packet equality binds SAT models as well as UNSAT traces. -/
def checkModelInput (source : FiniteFormula varCount) (input : SubmittedInput)
    (assignment : Fin varCount → Bool) : Bool :=
  match input with
  | .structured packet =>
    if packet = InputPacket.serialize source then ModelCheck.check source assignment else false
  | .dimacsText _ | .jsonText _ => false

theorem checkModelInput_sound (source : FiniteFormula varCount) (input : SubmittedInput)
    (assignment : Fin varCount → Bool) (accepted : checkModelInput source input assignment = true) :
    (∃ packet, input = .structured packet ∧ packet = InputPacket.serialize source) ∧
      Satisfies assignment source := by
  cases input with
  | structured packet =>
    by_cases equal : packet = InputPacket.serialize source
    · exact ⟨⟨packet, rfl, equal⟩, (ModelCheck.check_iff _ _).mp
        (by simpa [checkModelInput, equal] using accepted)⟩
    · simp [checkModelInput, equal] at accepted
  | dimacsText text => simp [checkModelInput] at accepted
  | jsonText text => simp [checkModelInput] at accepted

/-- Every answer passes its own generic checker on the exact original formula. -/
def validate (source : FiniteFormula varCount) (input : SubmittedInput) :
    Candidate varCount → Verdict
  | .sat assignment => if checkModelInput source input assignment then .sat else .invalid
  | .unsat certificate => if checkSubmitted source input certificate then .unsat else .invalid
  | .outside => .outside
  | .invalid => .invalid
  | .timeout => .timeout

theorem sat_sound (source : FiniteFormula varCount) (input : SubmittedInput)
    (candidate : Candidate varCount) (accepted : validate source input candidate = .sat) :
    (∃ packet, input = .structured packet ∧ packet = InputPacket.serialize source) ∧
      Satisfiable source := by
  cases candidate with
  | sat assignment =>
    simp only [validate] at accepted
    split at accepted
    next good =>
      obtain ⟨bound, model⟩ := checkModelInput_sound source input assignment good
      exact ⟨bound, assignment, model⟩
    next => contradiction
  | unsat certificate => simp only [validate] at accepted; split at accepted <;> contradiction
  | outside | invalid | timeout => contradiction

theorem unsat_sound (source : FiniteFormula varCount) (input : SubmittedInput)
    (candidate : Candidate varCount) (accepted : validate source input candidate = .unsat) :
    ∃ packet, input = .structured packet ∧ packet = InputPacket.serialize source ∧
      Unsatisfiable source := by
  cases candidate with
  | unsat certificate =>
    simp only [validate] at accepted
    split at accepted
    next good => exact checkSubmitted_sound source input certificate good
    next => contradiction
  | sat assignment => simp only [validate] at accepted; split at accepted <;> contradiction
  | outside | invalid | timeout => contradiction

@[simp] theorem outside_preserved (source : FiniteFormula varCount) (input : SubmittedInput) :
    validate source input .outside = .outside := rfl
@[simp] theorem invalid_preserved (source : FiniteFormula varCount) (input : SubmittedInput) :
    validate source input .invalid = .invalid := rfl
@[simp] theorem timeout_preserved (source : FiniteFormula varCount) (input : SubmittedInput) :
    validate source input .timeout = .timeout := rfl

/-- Checked recognition followed by the guarded detector and the complete source
model lift. A missing witness remains a timeout unless a supplied refutation passes
the generic validator; no semantic absence result is used as a certificate. -/
def familyCandidate {source : FiniteFormula varCount}
    (payload : Recognition.PrivateFamily.CompletePayload source recovered parameters boundary auxCount)
    (refutation : Option (Certificate varCount)) : Candidate varCount :=
  match Recognition.GuardedFamily.decodeChecked payload with
  | none => .outside
  | some record =>
    match Native.Lift.detectNamed parameters with
    | some assignment => .sat (record.liftNative assignment)
    | none => match refutation with
      | some certificate => .unsat certificate
      | none => .timeout

/-- The full public composition always checks the original source after lifting. -/
def runFamily (source : FiniteFormula varCount) (input : SubmittedInput)
    (payload : Recognition.PrivateFamily.CompletePayload source recovered parameters boundary auxCount)
    (refutation : Option (Certificate varCount)) : Verdict :=
  validate source input (familyCandidate payload refutation)

theorem detected_lift_checked
    (payload : Recognition.PrivateFamily.CompletePayload source recovered parameters boundary auxCount)
    (record : Recognition.PrivateFamily.Record source recovered parameters boundary auxCount)
    (recognized : Recognition.GuardedFamily.decodeChecked payload = some record)
    (assignment : Native.Variable parameters → Bool)
    (detected : Native.Lift.detectNamed parameters = some assignment) :
    ModelCheck.check source (record.liftNative assignment) = true := by
  apply (ModelCheck.check_iff _ _).mpr
  apply Recognition.GuardedFamily.decodeChecked_lifting payload record recognized
  exact (ModelCheck.check_iff _ _).mp
    (Native.Lift.detectNamed_some parameters
      (Recognition.GuardedFamily.decodeChecked_sound payload record recognized).1 assignment detected)

theorem runFamily_detected (source : FiniteFormula varCount)
    (payload : Recognition.PrivateFamily.CompletePayload source recovered parameters boundary auxCount)
    (record : Recognition.PrivateFamily.Record source recovered parameters boundary auxCount)
    (recognized : Recognition.GuardedFamily.decodeChecked payload = some record)
    (assignment : Native.Variable parameters → Bool)
    (detected : Native.Lift.detectNamed parameters = some assignment)
    (refutation : Option (Certificate varCount)) :
    runFamily source (.structured (InputPacket.serialize source)) payload refutation = .sat := by
  simp [runFamily, familyCandidate, recognized, detected, validate, checkModelInput,
    detected_lift_checked payload record recognized assignment detected]

theorem runFamily_sat_sound (source : FiniteFormula varCount) (input : SubmittedInput)
    (payload : Recognition.PrivateFamily.CompletePayload source recovered parameters boundary auxCount)
    (refutation : Option (Certificate varCount))
    (accepted : runFamily source input payload refutation = .sat) : Satisfiable source :=
  (sat_sound source input _ accepted).2

theorem runFamily_unsat_sound (source : FiniteFormula varCount) (input : SubmittedInput)
    (payload : Recognition.PrivateFamily.CompletePayload source recovered parameters boundary auxCount)
    (refutation : Option (Certificate varCount))
    (accepted : runFamily source input payload refutation = .unsat) : Unsatisfiable source :=
  (unsat_sound source input _ accepted).choose_spec.2.2

theorem runFamily_outside (source : FiniteFormula varCount) (input : SubmittedInput)
    (payload : Recognition.PrivateFamily.CompletePayload source recovered parameters boundary auxCount)
    (rejected : Recognition.GuardedFamily.decodeChecked payload = none)
    (refutation : Option (Certificate varCount)) :
    runFamily source input payload refutation = .outside := by
  simp [runFamily, familyCandidate, rejected, validate]

theorem runFamily_timeout (source : FiniteFormula varCount) (input : SubmittedInput)
    (payload : Recognition.PrivateFamily.CompletePayload source recovered parameters boundary auxCount)
    (record : Recognition.PrivateFamily.Record source recovered parameters boundary auxCount)
    (recognized : Recognition.GuardedFamily.decodeChecked payload = some record)
    (absent : Native.Lift.detectNamed parameters = none) :
    runFamily source input payload none = .timeout := by
  simp [runFamily, familyCandidate, recognized, absent, validate]

/-- Semantic detector completeness is separate from refutation production. -/
theorem recognized_absence_iff
    (payload : Recognition.PrivateFamily.CompletePayload source recovered parameters boundary auxCount)
    (record : Recognition.PrivateFamily.Record source recovered parameters boundary auxCount)
    (recognized : Recognition.GuardedFamily.decodeChecked payload = some record) :
    Native.Lift.detectNamed parameters = none ↔ Unsatisfiable source := by
  obtain ⟨guarded, _, projection⟩ :=
    Recognition.GuardedFamily.decodeChecked_sound payload record recognized
  rw [Native.Lift.detectNamed, Option.map_eq_none_iff,
    Physical.detectInput_none_iff parameters.bridge parameters.positiveBuses parameters.drive
      parameters.decoder guarded]
  exact not_congr projection.symm

theorem runFamily_sat_iff (source : FiniteFormula varCount)
    (payload : Recognition.PrivateFamily.CompletePayload source recovered parameters boundary auxCount)
    (record : Recognition.PrivateFamily.Record source recovered parameters boundary auxCount)
    (recognized : Recognition.GuardedFamily.decodeChecked payload = some record)
    (refutation : Option (Certificate varCount)) :
    runFamily source (.structured (InputPacket.serialize source)) payload refutation = .sat ↔
      Satisfiable source := by
  constructor
  · exact runFamily_sat_sound source _ payload refutation
  · intro satisfiable
    cases found : Native.Lift.detectNamed parameters with
    | none =>
      exact False.elim (((recognized_absence_iff payload record recognized).mp found) satisfiable)
    | some assignment => exact runFamily_detected source payload record recognized assignment found refutation

theorem runFamily_certified_unsat (source : FiniteFormula varCount)
    (payload : Recognition.PrivateFamily.CompletePayload source recovered parameters boundary auxCount)
    (record : Recognition.PrivateFamily.Record source recovered parameters boundary auxCount)
    (recognized : Recognition.GuardedFamily.decodeChecked payload = some record)
    (certificate : Certificate varCount) (checked : checkTyped source certificate = true) :
    runFamily source (.structured (InputPacket.serialize source)) payload (some certificate) = .unsat := by
  have absent := (recognized_absence_iff payload record recognized).mpr
    (checkTyped_sound source certificate checked)
  simp [runFamily, familyCandidate, recognized, absent, validate, checkSubmitted, checked]

end Controller.Certificate.Pipeline
