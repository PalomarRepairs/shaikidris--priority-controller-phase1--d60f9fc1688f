module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Recognition.Record
public import Controller.Native.Encode
public import Controller.CNF.Relabel
public import Controller.Recognition.BridgeProjection
public import Mathlib.Data.Fintype.Sum

@[expose] public section

/-! Independent typed-record validation and its two model transports. Rejection
is a record-validation result and does not assert that the input CNF is UNSAT.
The checks compare bounded local alias blocks and literal sets of exact rows;
they do not solve the supplied CNF or trust the recognizer's recovered model. -/

namespace Controller.Recognition
open Controller.CNF

namespace Record
variable {original recovered : Nat} {source : Formula (Fin original)}

def check (record : Record source recovered) : Bool :=
  decide record.AliasChecks && decide record.RowChecks

@[simp] theorem check_iff (record : Record source recovered) :
    record.check = true ↔ record.AliasChecks ∧ record.RowChecks := by
  simp [check]

theorem lift_model (record : Record source recovered) (checked : record.RowChecks)
    (assignment : Fin recovered → Bool) (model : Satisfies assignment record.expected) :
    Satisfies (record.lift assignment) source := by
  rw [satisfies_iff_rows]
  intro i
  apply (clauseHolds_signedLiteral record.coordinate record.phase assignment source.clauses[i]).mp
  change ClauseHolds assignment (record.mappedRow i)
  have rowCheck := checked.1 i
  cases choice : record.sourceRows i with
  | none =>
    rw [choice] at rowCheck
    obtain ⟨literal, member, opposite⟩ := rowCheck
    exact tautology_holds assignment member opposite
  | some j =>
    rw [choice] at rowCheck
    exact (clauseHolds_congr rowCheck).mpr ((satisfies_iff_rows assignment record.expected).mp model j)

theorem project_model (record : Record source recovered)
    (accepted : record.check = true) (assignment : Fin original → Bool)
    (model : Satisfies assignment source) : Satisfies (record.project assignment) record.expected := by
  obtain ⟨aliases, rows⟩ := record.check_iff.mp accepted
  have represented := record.source_is_lift aliases assignment model
  rw [satisfies_iff_rows]
  intro j
  have originalRow := (satisfies_iff_rows assignment source).mp model (record.expectedRows j)
  rw [represented] at originalRow
  have mapped := (clauseHolds_signedLiteral record.coordinate record.phase
    (record.project assignment) source.clauses[record.expectedRows j]).mpr originalRow
  exact (clauseHolds_congr (rows.2 j)).mp mapped

theorem accepted_projection (record : Record source recovered) (accepted : record.check = true) :
    Satisfiable source ↔ Satisfiable record.expected := by
  constructor
  · rintro ⟨assignment, model⟩
    exact ⟨record.project assignment, record.project_model accepted assignment model⟩
  · rintro ⟨assignment, model⟩
    exact ⟨record.lift assignment, record.lift_model (record.check_iff.mp accepted).2 assignment model⟩

theorem accepted_lifting_map (record : Record source recovered) (accepted : record.check = true)
    (assignment : Fin recovered → Bool) (model : Satisfies assignment record.expected) :
    Satisfies (record.lift assignment) source :=
  record.lift_model (record.check_iff.mp accepted).2 assignment model

theorem rejected_alias (record : Record source recovered) (bad : ¬record.AliasChecks) :
    record.check = false := by simp [check, bad]

theorem rejected_row (record : Record source recovered) (bad : ¬record.RowChecks) :
    record.check = false := by simp [check, bad]

/-- Exact canonical role/gate comparison is a syntactic check. The typed role
bijection is a serialization boundary; no recovered-CNF semantics is assumed. -/
def nativeCheck (record : Record source recovered) (parameters : Native.Parameters)
    (roles : Native.Variable parameters ≃ Fin recovered)
    (nativePhase : Native.Variable parameters → Bool) : Bool :=
  record.check && decide (record.expected.clauses =
    (signedRelabel roles nativePhase parameters.specificationFormula).clauses)

theorem nativeCheck_projection (record : Record source recovered)
    (parameters : Native.Parameters) (roles : Native.Variable parameters ≃ Fin recovered)
    (nativePhase : Native.Variable parameters → Bool)
    (accepted : record.nativeCheck parameters roles nativePhase = true) :
    Satisfiable source ↔ Physical.BridgeDetectable (b := parameters.buses)
      parameters.bridge parameters.drive parameters.observations := by
  have rowParts : record.check = true ∧ record.expected.clauses =
      (signedRelabel roles nativePhase parameters.specificationFormula).clauses := by
    simpa [nativeCheck] using accepted
  have same : record.expected = signedRelabel roles nativePhase parameters.specificationFormula := by
    cases originalFormula : record.expected
    cases nativeFormula : signedRelabel roles nativePhase parameters.specificationFormula
    simp only [originalFormula, nativeFormula] at rowParts
    exact congrArg Controller.CNF.OrderedFormula.mk rowParts.2
  have parts := And.intro rowParts.1 same
  rw [record.accepted_projection parts.1, parts.2]
  exact (satisfiable_signedRelabel_equiv roles nativePhase parameters.specificationFormula).trans
    (parameters.specification_satisfiable_iff)

theorem nativeCheck_model_projects (record : Record source recovered)
    (parameters : Native.Parameters) (roles : Native.Variable parameters ≃ Fin recovered)
    (nativePhase : Native.Variable parameters → Bool)
    (accepted : record.nativeCheck parameters roles nativePhase = true)
    (assignment : Fin original → Bool) (model : Satisfies assignment source) :
    let named := signedPullback roles nativePhase (record.project assignment)
    Physical.BridgeInputDetects parameters.bridge parameters.drive parameters.observations
      (parameters.primaryInput (fun primary => named (.primary primary)))
      (named (.primary .wire)) := by
  have rowParts : record.check = true ∧ record.expected.clauses =
      (signedRelabel roles nativePhase parameters.specificationFormula).clauses := by
    simpa [nativeCheck] using accepted
  have same : record.expected = signedRelabel roles nativePhase parameters.specificationFormula := by
    cases originalFormula : record.expected
    cases nativeFormula : signedRelabel roles nativePhase parameters.specificationFormula
    simp only [originalFormula, nativeFormula] at rowParts
    exact congrArg Controller.CNF.OrderedFormula.mk rowParts.2
  have parts := And.intro rowParts.1 same
  have recoveredModel := record.project_model parts.1 assignment model
  rw [parts.2] at recoveredModel
  exact parameters.specification_model_projects _
    ((satisfies_signedRelabel roles nativePhase _ _).mp recoveredModel)

end Record

/-- Integer-ID payload at the Python/typed-record boundary. This schema carries
both ordered clause arrays and all original row origins. JSON parsing itself is
outside the theorem; acceptance checks the complete payload against typed data. -/
structure SerializedRecord where
  sourceClauses : List (List (Nat × Bool))
  expectedClauses : List (List (Nat × Bool))
  coordinates : List Nat
  phases : List Bool
  anchors : List Nat
  aliasOrigins : List (List Nat)
  sourceRows : List (Option Nat)
  expectedRows : List Nat
  deriving DecidableEq

namespace Record
variable {original recovered : Nat} {source : Formula (Fin original)}

def serialize (record : Record source recovered) : SerializedRecord where
  sourceClauses := source.clauses.toList.map (List.map fun literal => (literal.1.val, literal.2))
  expectedClauses := record.expected.clauses.toList.map (List.map fun literal => (literal.1.val, literal.2))
  coordinates := (List.finRange original).map (fun i => (record.coordinate i).val)
  phases := (List.finRange original).map record.phase
  anchors := (List.finRange recovered).map (fun i => (record.anchor i).val)
  aliasOrigins := (List.finRange original).map (fun i => (record.aliases i).map Fin.val)
  sourceRows := (List.finRange source.clauses.size).map (fun i => (record.sourceRows i).map Fin.val)
  expectedRows := (List.finRange record.expected.clauses.size).map (fun i => (record.expectedRows i).val)

def serializedCheck (record : Record source recovered) (payload : SerializedRecord) : Bool :=
  decide (payload = record.serialize) && record.check

theorem serializedCheck_sound (record : Record source recovered) (payload : SerializedRecord)
    (accepted : record.serializedCheck payload = true) :
    payload = record.serialize ∧ (Satisfiable source ↔ Satisfiable record.expected) := by
  have parts : payload = record.serialize ∧ record.check = true := by
    simpa [serializedCheck] using accepted
  exact ⟨parts.1, record.accepted_projection parts.2⟩

end Record

namespace SerializedRecord

/-- Checked integer decoding uses the stated bound; it never reduces an ID
modulo that bound. In particular, a nonempty vector into `Fin 0` is rejected. -/
def decodeID (bound value : Nat) : Option (Fin bound) :=
  if valid : value < bound then some ⟨value, valid⟩ else none

def decodeLiteral (bound : Nat) (literal : Nat × Bool) :
    Option (Literal (Fin bound)) := do
  let coordinate ← decodeID bound literal.1
  pure (coordinate, literal.2)

/-- A length check converts a decoded vector to a total finite-coordinate map.
This is executable indexing into the supplied vector, rather than a witness
chosen by the caller. -/
def decodeVector {α : Type} (count : Nat) (values : List α) :
    Option (Fin count → α) :=
  if lengthMatches : values.length = count then
    some (fun i => values[i.val]'(by omega))
  else none

def decodeOptionalID (bound : Nat) : Option Nat → Option (Option (Fin bound))
  | none => some none
  | some value => (decodeID bound value).map some

/-- Decode every original row origin, retaining its order and every repeated
occurrence. The input formula is an independent argument and is compared to
`sourceClauses` by the final exact serialization check. -/
def decodeRaw {original : Nat} (source : Formula (Fin original))
    (recovered : Nat) (payload : SerializedRecord) : Option (Record source recovered) := do
  let expectedClauses ← payload.expectedClauses.mapM
    (fun clause => clause.mapM (decodeLiteral recovered))
  let expected := ofClauses expectedClauses
  let coordinates ← payload.coordinates.mapM (decodeID recovered)
  let coordinate ← decodeVector original coordinates
  let phase ← decodeVector original payload.phases
  let anchors ← payload.anchors.mapM (decodeID original)
  let anchor ← decodeVector recovered anchors
  let originLists ← payload.aliasOrigins.mapM
    (fun origins => origins.mapM (decodeID source.clauses.size))
  let aliases ← decodeVector original originLists
  let rowChoices ← payload.sourceRows.mapM (decodeOptionalID expected.clauses.size)
  let sourceRows ← decodeVector source.clauses.size rowChoices
  let rowOrigins ← payload.expectedRows.mapM (decodeID source.clauses.size)
  let expectedRows ← decodeVector expected.clauses.size rowOrigins
  pure { expected, coordinate, phase, anchor, aliases, sourceRows, expectedRows }

/-- Acceptance is decoding followed by exact payload/source binding and the
independent local checks. `none` denotes a rejected record, not an UNSAT answer. -/
def decodeChecked {original : Nat} (source : Formula (Fin original))
    (recovered : Nat) (payload : SerializedRecord) : Option (Record source recovered) :=
  match decodeRaw source recovered payload with
  | none => none
  | some record => if record.serializedCheck payload then some record else none

theorem decodeChecked_accepts {original recovered : Nat} {source : Formula (Fin original)}
    {payload : SerializedRecord} {record : Record source recovered}
    (accepted : decodeChecked source recovered payload = some record) :
    record.serializedCheck payload = true := by
  unfold decodeChecked at accepted
  cases decoded : decodeRaw source recovered payload with
  | none => simp [decoded] at accepted
  | some candidate =>
    simp only [decoded] at accepted
    split at accepted
    next checked =>
      have same : candidate = record := Option.some.inj accepted
      simpa [same] using checked
    next rejected => simp at accepted

theorem decodeChecked_sound {original recovered : Nat} {source : Formula (Fin original)}
    {payload : SerializedRecord} {record : Record source recovered}
    (accepted : decodeChecked source recovered payload = some record) :
    payload = record.serialize ∧ (Satisfiable source ↔ Satisfiable record.expected) :=
  record.serializedCheck_sound payload (decodeChecked_accepts accepted)

theorem decodeChecked_lifting {original recovered : Nat} {source : Formula (Fin original)}
    {payload : SerializedRecord} {record : Record source recovered}
    (accepted : decodeChecked source recovered payload = some record)
    (assignment : Fin recovered → Bool) (model : Satisfies assignment record.expected) :
    Satisfies (record.lift assignment) source := by
  have checked := decodeChecked_accepts accepted
  have parts : payload = record.serialize ∧ record.check = true := by
    simpa [Record.serializedCheck] using checked
  have localChecks : record.check = true := parts.2
  exact record.accepted_lifting_map localChecks assignment model

end SerializedRecord

namespace AliasTrace.Record
variable {original recovered : Nat} {source : Formula (Fin original)}

theorem checked_rows (record : AliasTrace.Record source recovered)
    (accepted : record.check = true) : record.base.RowChecks := by
  have checks : ((record.EdgeChecks ∧ record.base.RowChecks) ∧ record.AnchorChecks) ∧
      (∀ i, record.pathCheck i = true) := by simpa [check] using accepted
  exact checks.1.1.2

theorem project_model (record : AliasTrace.Record source recovered)
    (accepted : record.check = true) (assignment : Fin original → Bool)
    (model : Satisfies assignment source) :
    Satisfies (record.base.project assignment) record.base.expected := by
  have represented := record.checked_source_is_lift accepted assignment model
  have rows := record.checked_rows accepted
  rw [satisfies_iff_rows]
  intro j
  have originalRow := (satisfies_iff_rows assignment source).mp model (record.base.expectedRows j)
  rw [represented] at originalRow
  have mapped := (clauseHolds_signedLiteral record.base.coordinate record.base.phase
    (record.base.project assignment) source.clauses[record.base.expectedRows j]).mpr originalRow
  exact (clauseHolds_congr (rows.2 j)).mp mapped

theorem accepted_projection (record : AliasTrace.Record source recovered)
    (accepted : record.check = true) : Satisfiable source ↔ Satisfiable record.base.expected := by
  constructor
  · rintro ⟨assignment, model⟩
    exact ⟨record.base.project assignment, record.project_model accepted assignment model⟩
  · rintro ⟨assignment, model⟩
    exact ⟨record.base.lift assignment,
      record.base.lift_model (record.checked_rows accepted) assignment model⟩

theorem accepted_lifting_map (record : AliasTrace.Record source recovered)
    (accepted : record.check = true) (assignment : Fin recovered → Bool)
    (model : Satisfies assignment record.base.expected) : Satisfies (record.base.lift assignment) source :=
  record.base.lift_model (record.checked_rows accepted) assignment model

end AliasTrace.Record

namespace FamilyRecord

/-- Physical role maps are checked in both directions. Neither an equivalence
nor a semantic role-identification theorem is accepted as input evidence. -/
structure Roles (parameters : Native.Parameters) (recovered : Nat) where
  identify : Native.Variable parameters → Fin recovered
  name : Fin recovered → Native.Variable parameters
  phase : Native.Variable parameters → Bool

namespace Roles
variable {parameters : Native.Parameters} {recovered : Nat}

def Valid (roles : Roles parameters recovered) : Prop :=
  (∀ named, roles.name (roles.identify named) = named) ∧
  (∀ index, roles.identify (roles.name index) = index)

instance (roles : Roles parameters recovered) : Decidable roles.Valid := by
  unfold Valid
  infer_instance

def check (roles : Roles parameters recovered) : Bool := decide roles.Valid

@[simp] theorem check_iff (roles : Roles parameters recovered) :
    roles.check = true ↔ roles.Valid := by simp [check]

def equivalence (roles : Roles parameters recovered) (accepted : roles.check = true) :
    Native.Variable parameters ≃ Fin recovered where
  toFun := roles.identify
  invFun := roles.name
  left_inv := (roles.check_iff.mp accepted).1
  right_inv := (roles.check_iff.mp accepted).2

end Roles

/-- Per-row certificates allow syntactically different recovered gate formulas
and certified cuts. Checking is polynomial in the supplied certificate length;
no existence or shortness claim for arbitrary equivalence proofs is made. -/
@[irreducible] def NativeRowCertificates (parameters : Native.Parameters) (recovered : Nat) : Type :=
  Fin parameters.specificationFormula.clauses.size → Certificate.Certificate recovered

def NativeRowCertificates.get (certificates : NativeRowCertificates parameters recovered)
    (index : Fin parameters.specificationFormula.clauses.size) : Certificate.Certificate recovered := by
  have carrier : NativeRowCertificates parameters recovered =
      (Fin parameters.specificationFormula.clauses.size → Certificate.Certificate recovered) := by
    unfold NativeRowCertificates
    rfl
  exact (cast carrier certificates) index

structure Record (source : Formula (Fin original)) (recovered : Nat)
    (parameters : Native.Parameters) where
  aliases : AliasTrace.Record source recovered
  roles : Roles parameters recovered
  forward : NativeRowCertificates parameters recovered
  backward : Fin aliases.base.expected.clauses.size → Certificate.Certificate recovered

namespace Record
variable {original recovered : Nat} {source : Formula (Fin original)}
  {parameters : Native.Parameters}

def namedFormula (record : Record source recovered parameters) : Formula (Fin recovered) :=
  signedRelabel record.roles.identify record.roles.phase parameters.specificationFormula

def namedRow (record : Record source recovered parameters)
    (i : Fin parameters.specificationFormula.clauses.size) : Clause (Fin recovered) :=
  parameters.specificationFormula.clauses[i].map
    (signedLiteral record.roles.identify record.roles.phase)

def check (record : Record source recovered parameters) : Bool :=
  record.aliases.check && record.roles.check &&
    decide (∀ i, Attachment.entailCheck record.aliases.base.expected (record.namedRow i)
      (NativeRowCertificates.get record.forward i) = true) &&
    decide (∀ i, Attachment.entailCheck record.namedFormula record.aliases.base.expected.clauses[i]
      (record.backward i) = true)

theorem checked_models (record : Record source recovered parameters)
    (accepted : record.check = true) (assignment : Fin recovered → Bool) :
    Satisfies assignment record.aliases.base.expected ↔ Satisfies assignment record.namedFormula := by
  have checks : ((record.aliases.check = true ∧ record.roles.check = true) ∧
      (∀ i, Attachment.entailCheck record.aliases.base.expected (record.namedRow i)
        (NativeRowCertificates.get record.forward i) = true)) ∧
      (∀ i, Attachment.entailCheck record.namedFormula record.aliases.base.expected.clauses[i]
        (record.backward i) = true) := by simpa [check] using accepted
  constructor
  · intro model
    apply (satisfies_signedRelabel record.roles.identify record.roles.phase assignment _).mpr
    rw [satisfies_iff_rows]
    intro i
    exact (clauseHolds_signedLiteral record.roles.identify record.roles.phase assignment _).mp
      (Attachment.entailCheck_sound _ _ (NativeRowCertificates.get record.forward i) (checks.1.2 i) assignment model)
  · intro model
    rw [satisfies_iff_rows]
    intro i
    exact Attachment.entailCheck_sound _ _ (record.backward i) (checks.2 i) assignment model

theorem checked_projection (record : Record source recovered parameters)
    (accepted : record.check = true) :
    Satisfiable source ↔ Physical.BridgeDetectable (b := parameters.buses)
      parameters.bridge parameters.drive parameters.observations := by
  have checks : record.aliases.check = true ∧ record.roles.check = true := by
    have parts : ((record.aliases.check = true ∧ record.roles.check = true) ∧
        (∀ i, Attachment.entailCheck record.aliases.base.expected (record.namedRow i)
          (NativeRowCertificates.get record.forward i) = true)) ∧
        (∀ i, Attachment.entailCheck record.namedFormula record.aliases.base.expected.clauses[i]
          (record.backward i) = true) := by simpa [check] using accepted
    exact parts.1.1
  rw [record.aliases.accepted_projection checks.1]
  have named : Satisfiable record.aliases.base.expected ↔ Satisfiable record.namedFormula := by
    constructor <;> rintro ⟨assignment, model⟩
    · exact ⟨assignment, (record.checked_models accepted assignment).mp model⟩
    · exact ⟨assignment, (record.checked_models accepted assignment).mpr model⟩
  exact named.trans ((satisfiable_signedRelabel_equiv
    (record.roles.equivalence checks.2) record.roles.phase parameters.specificationFormula).trans
      parameters.specification_satisfiable_iff)

theorem checked_lifting_map (record : Record source recovered parameters)
    (accepted : record.check = true) (assignment : Fin recovered → Bool)
    (model : Satisfies assignment record.namedFormula) :
    Satisfies (record.aliases.base.lift assignment) source := by
  have localChecks : record.aliases.check = true := by
    simp only [check, Bool.and_eq_true] at accepted
    exact accepted.1.1.1
  exact record.aliases.accepted_lifting_map localChecks assignment
    ((record.checked_models accepted assignment).mpr model)

end Record
end FamilyRecord

structure SerializedChainedRecord where
  base : SerializedRecord
  edges : List ((Nat × Nat) × Bool)
  origins : List (List Nat)
  paths : List (List (Nat × Bool))
  deriving DecidableEq

namespace AliasTrace.Record
variable {original recovered : Nat} {source : Formula (Fin original)}

def serialize (record : AliasTrace.Record source recovered) : SerializedChainedRecord where
  base := record.base.serialize
  edges := record.edges.map fun edge => ((edge.left.val, edge.right.val), edge.phase)
  origins := (List.finRange record.edges.length).map fun i => (record.origins i).map Fin.val
  paths := (List.finRange original).map fun i =>
    (record.paths i).map fun step => (step.1.val, step.2)

def serializedCheck (record : AliasTrace.Record source recovered)
    (payload : SerializedChainedRecord) : Bool :=
  decide (payload = record.serialize) && record.check

end AliasTrace.Record

namespace SerializedChainedRecord

def decodeEdge (original : Nat) (edge : (Nat × Nat) × Bool) :
    Option (AliasEdge (Fin original)) := do
  let left ← SerializedRecord.decodeID original edge.1.1
  let right ← SerializedRecord.decodeID original edge.1.2
  pure ⟨left, right, edge.2⟩

def decodeRaw {original : Nat} (source : Formula (Fin original))
    (recovered : Nat) (payload : SerializedChainedRecord) :
    Option (AliasTrace.Record source recovered) := do
  let base ← SerializedRecord.decodeRaw source recovered payload.base
  let edges ← payload.edges.mapM (decodeEdge original)
  let decodedOrigins ← payload.origins.mapM fun row =>
    row.mapM (SerializedRecord.decodeID source.clauses.size)
  let origins ← SerializedRecord.decodeVector edges.length decodedOrigins
  let decodedPaths ← payload.paths.mapM fun path =>
    path.mapM fun step => do
      let index ← SerializedRecord.decodeID edges.length step.1
      pure (index, step.2)
  let paths ← SerializedRecord.decodeVector original decodedPaths
  pure ⟨base, edges, origins, paths⟩

def decodeChecked {original : Nat} (source : Formula (Fin original))
    (recovered : Nat) (payload : SerializedChainedRecord) :
    Option (AliasTrace.Record source recovered) :=
  match decodeRaw source recovered payload with
  | none => none
  | some record => if record.serializedCheck payload then some record else none

theorem decodeChecked_accepts {original recovered : Nat} {source : Formula (Fin original)}
    {payload : SerializedChainedRecord} {record : AliasTrace.Record source recovered}
    (accepted : decodeChecked source recovered payload = some record) :
    record.serializedCheck payload = true := by
  unfold decodeChecked at accepted
  cases decoded : decodeRaw source recovered payload with
  | none => simp [decoded] at accepted
  | some candidate =>
    simp only [decoded] at accepted
    split at accepted
    next checked =>
      have same : candidate = record := Option.some.inj accepted
      simpa [same] using checked
    next rejected => simp at accepted

theorem decodeChecked_sound {original recovered : Nat} {source : Formula (Fin original)}
    {payload : SerializedChainedRecord} {record : AliasTrace.Record source recovered}
    (accepted : decodeChecked source recovered payload = some record) :
    payload = record.serialize ∧ (Satisfiable source ↔ Satisfiable record.base.expected) := by
  have checks : payload = record.serialize ∧ record.check = true := by
    simpa [AliasTrace.Record.serializedCheck] using decodeChecked_accepts accepted
  exact ⟨checks.1, record.accepted_projection checks.2⟩

theorem decodeChecked_lifting {original recovered : Nat} {source : Formula (Fin original)}
    {payload : SerializedChainedRecord} {record : AliasTrace.Record source recovered}
    (accepted : decodeChecked source recovered payload = some record)
    (assignment : Fin recovered → Bool) (model : Satisfies assignment record.base.expected) :
    Satisfies (record.base.lift assignment) source := by
  have checks : payload = record.serialize ∧ record.check = true := by
    simpa [AliasTrace.Record.serializedCheck] using decodeChecked_accepts accepted
  exact record.accepted_lifting_map checks.2 assignment model

end SerializedChainedRecord

structure SerializedRoles where
  coordinates : List Nat
  names : List Nat
  phases : List Bool
  deriving DecidableEq

namespace FamilyRecord.Roles
variable {parameters : Native.Parameters} {recovered : Nat}

def serialize (roles : FamilyRecord.Roles parameters recovered) : SerializedRoles where
  coordinates := parameters.variableRoles.map fun role => (roles.identify role).val
  names := (List.finRange recovered).map fun i => parameters.variableRoles.idxOf (roles.name i)
  phases := parameters.variableRoles.map roles.phase

def serializedCheck (roles : FamilyRecord.Roles parameters recovered) (payload : SerializedRoles) : Bool :=
  decide (payload = roles.serialize) && roles.check

end FamilyRecord.Roles

namespace SerializedRoles

def roleIndex (parameters : Native.Parameters) (role : Native.Variable parameters) :
    Fin parameters.variableRoles.length :=
  ⟨parameters.variableRoles.idxOf role, List.idxOf_lt_length_of_mem (parameters.mem_variableRoles role)⟩

def decodeRaw (parameters : Native.Parameters) (recovered : Nat) (payload : SerializedRoles) :
    Option (FamilyRecord.Roles parameters recovered) := do
  let decodedIDs ← payload.coordinates.mapM (SerializedRecord.decodeID recovered)
  let coordinates ← SerializedRecord.decodeVector parameters.variableRoles.length decodedIDs
  let decodedNames ← payload.names.mapM
    (SerializedRecord.decodeID parameters.variableRoles.length)
  let names ← SerializedRecord.decodeVector recovered decodedNames
  let phases ← SerializedRecord.decodeVector parameters.variableRoles.length payload.phases
  pure {
    identify := fun role => coordinates (roleIndex parameters role)
    name := fun index => parameters.variableRoles.get (names index)
    phase := fun role => phases (roleIndex parameters role) }

def decodeChecked (parameters : Native.Parameters) (recovered : Nat) (payload : SerializedRoles) :
    Option (FamilyRecord.Roles parameters recovered) :=
  match decodeRaw parameters recovered payload with
  | none => none
  | some roles => if roles.serializedCheck payload then some roles else none

theorem decodeChecked_accepts {parameters : Native.Parameters} {recovered : Nat}
    {payload : SerializedRoles} {roles : FamilyRecord.Roles parameters recovered}
    (accepted : decodeChecked parameters recovered payload = some roles) :
    payload = roles.serialize ∧ roles.Valid := by
  unfold decodeChecked at accepted
  cases decoded : decodeRaw parameters recovered payload with
  | none => simp [decoded] at accepted
  | some candidate =>
    simp only [decoded] at accepted
    split at accepted
    next checked =>
      have same : candidate = roles := Option.some.inj accepted
      have checks : payload = candidate.serialize ∧ candidate.check = true := by
        simpa [FamilyRecord.Roles.serializedCheck] using checked
      exact same ▸ ⟨checks.1, candidate.check_iff.mp checks.2⟩
    next rejected => simp at accepted

end SerializedRoles

namespace PrivateFamily
open Controller.Certificate

@[simp] theorem unitClause_iff (assignment : α → Bool) (literal : Literal α) :
    ClauseHolds assignment [literal] ↔ LiteralHolds assignment literal := by
  constructor
  · rintro ⟨candidate, member, holds⟩
    simp only [List.mem_singleton] at member
    subst candidate
    exact holds
  · intro holds
    exact ⟨literal, by simp, holds⟩

/-- Both certificate families are indexed by the exact conclusion row arrays.
Every original row occurrence has its own index, including duplicates. -/
structure Cuts (left right : Formula (Fin count)) where
  forward : Fin right.clauses.size → Certificate count
  backward : Fin left.clauses.size → Certificate count

namespace Cuts
variable {count : Nat} {left right : Formula (Fin count)}

def check (cuts : Cuts left right) : Bool :=
  decide (∀ i, Attachment.entailCheck left right.clauses[i] (cuts.forward i) = true) &&
    decide (∀ i, Attachment.entailCheck right left.clauses[i] (cuts.backward i) = true)

theorem checked_models (cuts : Cuts left right) (accepted : cuts.check = true)
    (assignment : Fin count → Bool) : Satisfies assignment left ↔ Satisfies assignment right := by
  have checks : (∀ i, Attachment.entailCheck left right.clauses[i] (cuts.forward i) = true) ∧
      (∀ i, Attachment.entailCheck right left.clauses[i] (cuts.backward i) = true) := by
    simpa [check] using accepted
  constructor
  · intro model
    rw [satisfies_iff_rows]
    intro i
    exact Attachment.entailCheck_sound _ _ (cuts.forward i) (checks.1 i) assignment model
  · intro model
    rw [satisfies_iff_rows]
    intro i
    exact Attachment.entailCheck_sound _ _ (cuts.backward i) (checks.2 i) assignment model

end Cuts

/-- The two partitions are physically disjoint tagged coordinate domains.
The inverse functions and phases are checked before constructing an equivalence. -/
structure Partition (boundary auxCount recovered : Nat) where
  identify : Fin boundary ⊕ Fin auxCount → Fin recovered
  name : Fin recovered → Fin boundary ⊕ Fin auxCount
  phase : Fin boundary ⊕ Fin auxCount → Bool

namespace Partition
variable {boundary auxCount recovered : Nat}

def Valid (partition : Partition boundary auxCount recovered) : Prop :=
  (∀ coordinate, partition.name (partition.identify coordinate) = coordinate) ∧
    (∀ index, partition.identify (partition.name index) = index)

instance (partition : Partition boundary auxCount recovered) : Decidable partition.Valid := by
  unfold Valid
  infer_instance

def check (partition : Partition boundary auxCount recovered) : Bool := decide partition.Valid

@[simp] theorem check_iff (partition : Partition boundary auxCount recovered) :
    partition.check = true ↔ partition.Valid := by simp [check]

def equivalence (partition : Partition boundary auxCount recovered)
    (accepted : partition.check = true) : (Fin boundary ⊕ Fin auxCount) ≃ Fin recovered where
  toFun := partition.identify
  invFun := partition.name
  left_inv := (partition.check_iff.mp accepted).1
  right_inv := (partition.check_iff.mp accepted).2

end Partition

def driveFormula (parameters : Native.Parameters) : Formula (Native.Variable parameters) :=
  parameters.equationFormula ++
    ofClauses ((parameters.assertions.take 3).map fun literal => [literal])

theorem native_drive_detection_iff (parameters : Native.Parameters)
    (assignment : Native.Variable parameters → Bool) :
    Satisfies assignment parameters.specificationFormula ↔
      Satisfies assignment (driveFormula parameters) ∧
        LiteralHolds assignment (Native.Parameters.internal parameters .detected) := by
  simp only [Native.Parameters.specificationFormula, Native.Parameters.assertionFormula,
    driveFormula, satisfies_append, satisfies_ofClauses, Native.Parameters.assertions,
    List.take, List.map_cons, List.map_nil, List.forall_mem_cons, unitClause_iff]
  tauto


structure Record (source : Formula (Fin original)) (recovered : Nat)
    (parameters : Native.Parameters) (boundary auxCount : Nat) where
  aliases : AliasTrace.Record source recovered
  roles : FamilyRecord.Roles parameters boundary
  partition : Partition boundary auxCount recovered
  wrapper : Attachment.WrapperRecord boundary auxCount parameters.decoder.roots.length
  targetLink : Attachment.TargetLink.Record boundary parameters.decoder.roots.length
  metadata : ProducerMetadata.Record wrapper.definitions
  namedDrive : Formula (Fin boundary)
  bundle : Formula (Fin recovered)
  coreCuts : Cuts wrapper.definitions namedDrive
  sourceCuts : Cuts aliases.base.expected bundle

namespace Record
variable {original recovered boundary auxCount : Nat} {source : Formula (Fin original)}
  {parameters : Native.Parameters}

def signalBundle (record : Record source recovered parameters boundary auxCount) :
    Formula (Fin boundary ⊕ Fin auxCount) :=
  relabel Sum.inl record.wrapper.definitions ++ record.wrapper.wrapper

def physicalPairs (record : Record source recovered parameters boundary auxCount)
    (i : Fin parameters.decoder.roots.length) : Literal (Fin boundary) × Literal (Fin boundary) :=
  (signedLiteral record.roles.identify record.roles.phase
      (Native.Parameters.internal parameters (.decoder .healthy (parameters.decoder.roots.get i))),
   signedLiteral record.roles.identify record.roles.phase
      (Native.Parameters.internal parameters (.decoder .faulty (parameters.decoder.roots.get i))))

def physicalRoots (record : Record source recovered parameters boundary auxCount) : Finset (Fin boundary) :=
  (parameters.primaryRoles.map fun role => record.roles.identify (.primary role)).toFinset

def Checks (record : Record source recovered parameters boundary auxCount) : Prop :=
  record.aliases.check = true ∧ record.roles.check = true ∧ record.partition.check = true ∧
  record.coreCuts.check = true ∧ record.sourceCuts.check = true ∧
  record.wrapper.check = true ∧ record.targetLink.check = true ∧ record.metadata.check = true ∧
  record.namedDrive.clauses = (signedRelabel record.roles.identify record.roles.phase
    (driveFormula parameters)).clauses ∧
  record.bundle.clauses = (signedRelabel record.partition.identify record.partition.phase record.signalBundle).clauses ∧
  record.targetLink.definitions.clauses = record.wrapper.definitions.clauses ∧
  record.targetLink.pairs = record.wrapper.pairs ∧ record.targetLink.selected = record.wrapper.selected ∧
  record.targetLink.target = signedLiteral record.roles.identify record.roles.phase
    (Native.Parameters.internal parameters .detected) ∧
  record.wrapper.pairs = record.physicalPairs ∧
  record.wrapper.selected = List.finRange parameters.decoder.roots.length ∧
  record.metadata.roots = record.physicalRoots

instance (record : Record source recovered parameters boundary auxCount) : Decidable record.Checks := by
  unfold Checks
  infer_instance

def check (record : Record source recovered parameters boundary auxCount) : Bool := decide record.Checks

@[simp] theorem check_iff (record : Record source recovered parameters boundary auxCount) :
    record.check = true ↔ record.Checks := by simp [check]

theorem formula_of_rows {left right : Formula α} (same : left.clauses = right.clauses) :
    left = right := by
  cases left
  cases right
  exact congrArg Controller.CNF.OrderedFormula.mk same

/-- The forward projection uses the original model, checked signed partitions,
retained definitions, and the native controller's actual three interface units. -/
theorem checked_model_projects (record : Record source recovered parameters boundary auxCount)
    (accepted : record.check = true) (assignment : Fin original → Bool)
    (model : Satisfies assignment source) :
    ∃ nativeAssignment : Native.Variable parameters → Bool,
      Satisfies nativeAssignment parameters.specificationFormula := by
  rcases record.check_iff.mp accepted with
    ⟨aliasGood, roleGood, partitionGood, coreGood, sourceGood, wrapperGood, targetGood,
      metadataGood, driveRows, bundleRows, targetRows, targetPairs, targetSelected, targetLiteral,
      physicalPairsChecked, selectedChecked, physicalRootsChecked⟩
  let recoveredAssignment := record.aliases.base.project assignment
  have recoveredModel := record.aliases.project_model aliasGood assignment model
  have bundleModel := (record.sourceCuts.checked_models sourceGood recoveredAssignment).mp recoveredModel
  rw [formula_of_rows bundleRows] at bundleModel
  have pulledModel := (satisfies_signedRelabel record.partition.identify record.partition.phase
    recoveredAssignment record.signalBundle).mp bundleModel
  let pulled := signedPullback record.partition.identify record.partition.phase recoveredAssignment
  let signals : Fin boundary → Bool := fun i => pulled (Sum.inl i)
  let auxiliary : Fin auxCount → Bool := fun i => pulled (Sum.inr i)
  have joined : Native.ObservationProjection.joint signals auxiliary = pulled := by
    funext coordinate
    cases coordinate <;> rfl
  have parts := (satisfies_append _ _ _).mp pulledModel
  have signalModel : Satisfies signals record.wrapper.definitions :=
    (satisfies_relabel Sum.inl pulled record.wrapper.definitions).mp parts.1
  have wrapperModel : Satisfies (Native.ObservationProjection.joint signals auxiliary)
      record.wrapper.wrapper := by simpa only [joined] using parts.2
  have discrepancy := (record.wrapper.checked_projection wrapperGood signals signalModel).mp
    ⟨auxiliary, wrapperModel⟩
  have linkModel : Satisfies signals record.targetLink.definitions := by
    rw [formula_of_rows targetRows]
    exact signalModel
  have detected := (record.targetLink.checked_target_iff targetGood signals linkModel).mpr
    (by simpa only [targetPairs, targetSelected] using discrepancy)
  rw [targetLiteral] at detected
  have namedDriveModel := (record.coreCuts.checked_models coreGood signals).mp signalModel
  rw [formula_of_rows driveRows] at namedDriveModel
  let nativeAssignment := signedPullback record.roles.identify record.roles.phase signals
  have nativeDriveModel : Satisfies nativeAssignment (driveFormula parameters) :=
    (satisfies_signedRelabel record.roles.identify record.roles.phase signals _).mp namedDriveModel
  have nativeDetected : LiteralHolds nativeAssignment (Native.Parameters.internal parameters .detected) :=
    (literalHolds_signedLiteral record.roles.identify record.roles.phase signals _).mp detected
  exact ⟨nativeAssignment, (native_drive_detection_iff parameters nativeAssignment).mpr
    ⟨nativeDriveModel, nativeDetected⟩⟩

/-- Soundness includes the recovered physical roles and actual declared roots;
the private observation target is discharged by checked certificates. -/
theorem checked_physical_projection (record : Record source recovered parameters boundary auxCount)
    (accepted : record.check = true) : Satisfiable source →
    Physical.BridgeDetectable (b := parameters.buses) parameters.bridge parameters.drive
      parameters.observations := by
  rintro ⟨assignment, model⟩
  obtain ⟨nativeAssignment, nativeModel⟩ := record.checked_model_projects accepted assignment model
  exact parameters.specification_satisfiable_iff.mp ⟨nativeAssignment, nativeModel⟩


def signalsOfNative (record : Record source recovered parameters boundary auxCount)
    (assignment : Native.Variable parameters → Bool) : Fin boundary → Bool :=
  fun index => assignment (record.roles.name index) == record.roles.phase (record.roles.name index)

/-- The advertised full extension is deterministic: signed native coordinates,
one checked selected-orientation extension, inverse private partition, and the
checked original alias lift. No model search occurs in this map. -/
def liftNative (record : Record source recovered parameters boundary auxCount)
    (assignment : Native.Variable parameters → Bool) : Fin original → Bool :=
  let signals := record.signalsOfNative assignment
  let joined := Native.ObservationProjection.joint signals (record.wrapper.extension signals)
  record.aliases.base.lift (fun index => joined (record.partition.name index) ==
    record.partition.phase (record.partition.name index))

theorem checked_lift_native (record : Record source recovered parameters boundary auxCount)
    (accepted : record.check = true) (nativeAssignment : Native.Variable parameters → Bool)
    (nativeModel : Satisfies nativeAssignment parameters.specificationFormula) :
    Satisfies (record.liftNative nativeAssignment) source := by
  rcases record.check_iff.mp accepted with
    ⟨aliasGood, roleGood, partitionGood, coreGood, sourceGood, wrapperGood, targetGood,
      metadataGood, driveRows, bundleRows, targetRows, targetPairs, targetSelected, targetLiteral,
      physicalPairsChecked, selectedChecked, physicalRootsChecked⟩
  let signals := record.signalsOfNative nativeAssignment
  have rolePullback : signedPullback record.roles.identify record.roles.phase signals = nativeAssignment := by
    change signedPullback record.roles.identify record.roles.phase
      (fun index => nativeAssignment (record.roles.name index) ==
        record.roles.phase (record.roles.name index)) = nativeAssignment
    exact signedPullback_inverse (record.roles.equivalence roleGood) record.roles.phase nativeAssignment
  have nativeParts := (native_drive_detection_iff parameters nativeAssignment).mp nativeModel
  have namedDriveModel : Satisfies signals record.namedDrive := by
    rw [formula_of_rows driveRows]
    apply (satisfies_signedRelabel record.roles.identify record.roles.phase signals _).mpr
    rw [rolePullback]
    exact nativeParts.1
  have signalModel := (record.coreCuts.checked_models coreGood signals).mpr namedDriveModel
  have signalDetected : LiteralHolds signals (signedLiteral record.roles.identify record.roles.phase
      (Native.Parameters.internal parameters .detected)) := by
    apply (literalHolds_signedLiteral record.roles.identify record.roles.phase signals _).mpr
    rw [rolePullback]
    exact nativeParts.2
  have linkModel : Satisfies signals record.targetLink.definitions := by
    rw [formula_of_rows targetRows]
    exact signalModel
  have discrepancy := (record.targetLink.checked_target_iff targetGood signals linkModel).mp
    (by simpa only [targetLiteral] using signalDetected)
  have wrapperDifference : ∃ i ∈ record.wrapper.selected,
      Native.ObservationProjection.Discrepant signals (record.wrapper.pairs i) := by
    simpa only [targetPairs, targetSelected] using discrepancy
  have extensionModel := record.wrapper.checked_extension wrapperGood signals signalModel wrapperDifference
  let joined := Native.ObservationProjection.joint signals (record.wrapper.extension signals)
  have joinedModel : Satisfies joined record.signalBundle := by
    apply (satisfies_append _ _ _).mpr
    exact ⟨(satisfies_relabel Sum.inl joined record.wrapper.definitions).mpr signalModel, extensionModel⟩
  let recoveredAssignment : Fin recovered → Bool := fun index =>
    joined (record.partition.name index) == record.partition.phase (record.partition.name index)
  have partitionPullback : signedPullback record.partition.identify record.partition.phase
      recoveredAssignment = joined := by
    simpa [recoveredAssignment, Partition.equivalence] using
      signedPullback_inverse (record.partition.equivalence partitionGood) record.partition.phase joined
  have bundleModel : Satisfies recoveredAssignment record.bundle := by
    rw [formula_of_rows bundleRows]
    apply (satisfies_signedRelabel record.partition.identify record.partition.phase
      recoveredAssignment record.signalBundle).mpr
    rw [partitionPullback]
    exact joinedModel
  have expectedModel := (record.sourceCuts.checked_models sourceGood recoveredAssignment).mpr bundleModel
  exact record.aliases.accepted_lifting_map aliasGood recoveredAssignment expectedModel

theorem checked_projection (record : Record source recovered parameters boundary auxCount)
    (accepted : record.check = true) : Satisfiable source ↔
    Physical.BridgeDetectable (b := parameters.buses) parameters.bridge parameters.drive
      parameters.observations := by
  constructor
  · exact record.checked_physical_projection accepted
  · intro detects
    obtain ⟨nativeAssignment, nativeModel⟩ := parameters.specification_satisfiable_iff.mpr detects
    exact ⟨record.liftNative nativeAssignment, record.checked_lift_native accepted nativeAssignment nativeModel⟩

end Record

structure SerializedPartition where
  coordinates : List Nat
  names : List Nat
  phases : List Bool
  deriving DecidableEq

namespace Partition
variable {boundary auxCount recovered : Nat}

def serialize (partition : Partition boundary auxCount recovered) : SerializedPartition where
  coordinates := (List.finRange (boundary + auxCount)).map fun index =>
    (partition.identify (finSumFinEquiv.symm index)).val
  names := (List.finRange recovered).map fun index => (finSumFinEquiv (partition.name index)).val
  phases := (List.finRange (boundary + auxCount)).map fun index => partition.phase (finSumFinEquiv.symm index)

def serializedCheck (partition : Partition boundary auxCount recovered) (payload : SerializedPartition) : Bool :=
  decide (payload = partition.serialize) && partition.check

end Partition

namespace SerializedPartition

def decodeRaw (boundary auxCount recovered : Nat) (payload : SerializedPartition) :
    Option (Partition boundary auxCount recovered) := do
  let decodedIDs ← payload.coordinates.mapM (SerializedRecord.decodeID recovered)
  let coordinates ← SerializedRecord.decodeVector (boundary + auxCount) decodedIDs
  let decodedNames ← payload.names.mapM (SerializedRecord.decodeID (boundary + auxCount))
  let names ← SerializedRecord.decodeVector recovered decodedNames
  let phases ← SerializedRecord.decodeVector (boundary + auxCount) payload.phases
  pure {
    identify := fun coordinate => coordinates (finSumFinEquiv coordinate)
    name := fun index => finSumFinEquiv.symm (names index)
    phase := fun coordinate => phases (finSumFinEquiv coordinate) }

def decodeChecked (boundary auxCount recovered : Nat) (payload : SerializedPartition) :
    Option (Partition boundary auxCount recovered) :=
  match decodeRaw boundary auxCount recovered payload with
  | none => none
  | some partition => if partition.serializedCheck payload then some partition else none

theorem decodeChecked_accepts {boundary auxCount recovered : Nat}
    {payload : SerializedPartition} {partition : Partition boundary auxCount recovered}
    (accepted : decodeChecked boundary auxCount recovered payload = some partition) :
    payload = partition.serialize ∧ partition.Valid := by
  unfold decodeChecked at accepted
  cases decoded : decodeRaw boundary auxCount recovered payload with
  | none => simp [decoded] at accepted
  | some candidate =>
    simp only [decoded] at accepted
    split at accepted
    next checked =>
      have same : candidate = partition := Option.some.inj accepted
      have checks : payload = candidate.serialize ∧ candidate.check = true := by
        simpa [Partition.serializedCheck] using checked
      exact same ▸ ⟨checks.1, candidate.check_iff.mp checks.2⟩
    next rejected => simp at accepted

end SerializedPartition

/-- A typed transport packet for a complete recovery certificate. Original
coordinates, alias-edge IDs, physical roles, and the signal/private partition
arrive as natural-number vectors and are decoded below. Certificate traces and
bounded attachment syntax are typed input here; parsing those syntax objects
from an external JSON document is a separate boundary. No semantic proof is a
field of this packet. -/
structure CompletePayload (source : Formula (Fin original)) (recovered : Nat)
    (parameters : Native.Parameters) (boundary auxCount : Nat) where
  aliases : SerializedChainedRecord
  roles : SerializedRoles
  partition : SerializedPartition
  expected : Formula (Fin recovered)
  wrapper : Attachment.WrapperRecord boundary auxCount parameters.decoder.roots.length
  targetLink : Attachment.TargetLink.Record boundary parameters.decoder.roots.length
  metadata : ProducerMetadata.Record wrapper.definitions
  namedDrive : Formula (Fin boundary)
  bundle : Formula (Fin recovered)
  coreCuts : Cuts wrapper.definitions namedDrive
  sourceCuts : Cuts expected bundle

namespace CompletePayload
variable {original recovered boundary auxCount : Nat} {source : Formula (Fin original)}
  {parameters : Native.Parameters}

theorem formula_of_rows {left right : Formula α}
    (same : left.clauses = right.clauses) : left = right := by
  cases left
  cases right
  exact congrArg Controller.CNF.OrderedFormula.mk same

/-- Decoding constructs the finite maps from the raw vectors. The provided
expected rows must agree with the actually decoded alias target before the
row-indexed cut evidence can be attached to the constructed record. -/
def decodeRaw (payload : CompletePayload source recovered parameters boundary auxCount) :
    Option (Record source recovered parameters boundary auxCount) := do
  let aliases ← SerializedChainedRecord.decodeChecked source recovered payload.aliases
  let roles ← SerializedRoles.decodeChecked parameters boundary payload.roles
  let partition ← SerializedPartition.decodeChecked boundary auxCount recovered payload.partition
  if rows : aliases.base.expected.clauses = payload.expected.clauses then
    let same := formula_of_rows rows
    pure {
      aliases := aliases
      roles := roles
      partition := partition
      wrapper := payload.wrapper
      targetLink := payload.targetLink
      metadata := payload.metadata
      namedDrive := payload.namedDrive
      bundle := payload.bundle
      coreCuts := payload.coreCuts
      sourceCuts := same.symm ▸ payload.sourceCuts }
  else none

/-- Validation failure returns no record. It does not report UNSAT. -/
def decodeChecked (payload : CompletePayload source recovered parameters boundary auxCount) :
    Option (Record source recovered parameters boundary auxCount) :=
  match payload.decodeRaw with
  | none => none
  | some record => if record.check then some record else none

theorem decodeChecked_accepts
    {payload : CompletePayload source recovered parameters boundary auxCount}
    {record : Record source recovered parameters boundary auxCount}
    (accepted : payload.decodeChecked = some record) : record.check = true := by
  unfold decodeChecked at accepted
  cases decoded : payload.decodeRaw with
  | none => simp [decoded] at accepted
  | some candidate =>
    simp only [decoded] at accepted
    split at accepted
    next checked =>
      have same : candidate = record := Option.some.inj accepted
      simpa only [same] using checked
    next rejected => simp at accepted

theorem decodeChecked_projection
    {payload : CompletePayload source recovered parameters boundary auxCount}
    {record : Record source recovered parameters boundary auxCount}
    (accepted : payload.decodeChecked = some record) : Satisfiable source ↔
    Physical.BridgeDetectable (b := parameters.buses) parameters.bridge parameters.drive
      parameters.observations :=
  record.checked_projection (decodeChecked_accepts accepted)

theorem decodeChecked_lifting
    {payload : CompletePayload source recovered parameters boundary auxCount}
    {record : Record source recovered parameters boundary auxCount}
    (accepted : payload.decodeChecked = some record)
    (assignment : Native.Variable parameters → Bool)
    (model : Satisfies assignment parameters.specificationFormula) :
    Satisfies (record.liftNative assignment) source :=
  record.checked_lift_native (decodeChecked_accepts accepted) assignment model

end CompletePayload
end PrivateFamily
end Controller.Recognition
