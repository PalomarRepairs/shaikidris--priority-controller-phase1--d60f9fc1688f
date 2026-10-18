module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Recognition.Coverage
public import Controller.Recognition.Producers
public import Controller.Recognition.Normalization
public import Mathlib.Data.Fintype.Prod

@[expose] public section

/-! Typed recognition records for signed source coordinates and exact row
coverage. Every source row has a retained ID. Direct alias blocks certify the
advertised lift from recovered coordinates, and expected-row origins certify
that no reconstructed equation was invented by the recognizer. -/

namespace Controller.Recognition
open Controller.CNF

structure Record (source : Formula (Fin original)) (recovered : Nat) where
  expected : Formula (Fin recovered)
  coordinate : Fin original → Fin recovered
  phase : Fin original → Bool
  anchor : Fin recovered → Fin original
  aliases : Fin original → Coverage.Origins source
  sourceRows : Fin source.clauses.size → Option (Fin expected.clauses.size)
  expectedRows : Fin expected.clauses.size → Fin source.clauses.size

namespace Record
variable {original recovered : Nat} {source : Formula (Fin original)}

def mappedRow (record : Record source recovered) (i : Fin source.clauses.size) :
    Clause (Fin recovered) := source.clauses[i].map (signedLiteral record.coordinate record.phase)

def Tautological (clause : Clause (Fin recovered)) : Prop :=
  ∃ literal ∈ clause, negate literal ∈ clause

instance (clause : Clause (Fin recovered)) : Decidable (Tautological clause) := by
  unfold Tautological
  infer_instance

def AliasChecks (record : Record source recovered) : Prop :=
  ∀ i, (record.anchor (record.coordinate i) = i ∧ record.phase i = true) ∨
    Gate.CompleteProducer (Coverage.block source (record.aliases i)) (i, true)
      (.alias (record.anchor (record.coordinate i), record.phase i))

instance (record : Record source recovered) : Decidable record.AliasChecks := by
  unfold AliasChecks
  infer_instance

def RowChecks (record : Record source recovered) : Prop :=
  (∀ i, match record.sourceRows i with
    | none => Tautological (record.mappedRow i)
    | some j => SameLiterals (record.mappedRow i) record.expected.clauses[j]) ∧
  (∀ j, SameLiterals (record.mappedRow (record.expectedRows j)) record.expected.clauses[j])

instance (record : Record source recovered) : Decidable record.RowChecks := by
  letI : ∀ c d : Clause (Fin recovered), Decidable (SameLiterals c d) := fun c d => by
    unfold SameLiterals
    infer_instance
  letI : ∀ i : Fin source.clauses.size, Decidable (match record.sourceRows i with
      | none => Tautological (record.mappedRow i)
      | some j => SameLiterals (record.mappedRow i) record.expected.clauses[j]) := fun i => by
    cases choice : record.sourceRows i with
    | none => simp only [choice]; infer_instance
    | some j => simp only [choice]; unfold SameLiterals; infer_instance
  unfold RowChecks
  infer_instance

def project (record : Record source recovered) (assignment : Fin original → Bool) :
    Fin recovered → Bool := fun i => assignment (record.anchor i)

def lift (record : Record source recovered) (assignment : Fin recovered → Bool) :
    Fin original → Bool := signedPullback record.coordinate record.phase assignment

theorem source_is_lift (record : Record source recovered) (checked : record.AliasChecks)
    (assignment : Fin original → Bool) (model : Satisfies assignment source) :
    assignment = record.lift (record.project assignment) := by
  funext i
  rcases checked i with identity | aliasBlock
  · simp [lift, project, signedPullback, identity.1, identity.2]
  · have blockModel := Coverage.source_implies_block source (record.aliases i) assignment model
    have equation := (Gate.CompleteProducer.correct aliasBlock assignment).mp blockModel
    simpa [lift, project, signedPullback, Gate.eval, literalValue] using equation

end Record

namespace AliasTrace
open Controller.Recognition

/-- The path proof is produced by replay, erased at execution, and cannot be
supplied in place of the signed edge IDs and traversal directions. -/
structure Result (edges : List (AliasEdge (Fin original))) (start : Fin original) where
  endpoint : Fin original
  phase : Bool
  sound : AliasPath edges start endpoint phase

def replay (edges : List (AliasEdge (Fin original))) (start : Fin original) :
    List (Fin edges.length × Bool) → Option (Result edges start)
  | [] => some ⟨start, true, .refl start⟩
  | (index, direction) :: rest =>
      let edge := edges.get index
      if direction then
        if connected : start = edge.left then
          match replay edges edge.right rest with
          | none => none
          | some tail => some ⟨tail.endpoint, tail.phase == edge.phase,
              by subst start; exact .trans (.edge edge (List.get_mem ..)) tail.sound⟩
        else none
      else
        if connected : start = edge.right then
          match replay edges edge.left rest with
          | none => none
          | some tail => some ⟨tail.endpoint, tail.phase == edge.phase,
              by subst start; exact .trans (.symm (.edge edge (List.get_mem ..))) tail.sound⟩
        else none

/-- All alias edges refer to exact original-ID blocks. The replayed paths may
reuse edges and reverse their direction, retaining their signed composition. -/
structure Record (source : Formula (Fin original)) (recovered : Nat) where
  base : Recognition.Record source recovered
  edges : List (AliasEdge (Fin original))
  origins : Fin edges.length → Coverage.Origins source
  paths : Fin original → List (Fin edges.length × Bool)

namespace Record
variable {original recovered : Nat} {source : Formula (Fin original)}

def EdgeChecks (record : Record source recovered) : Prop :=
  ∀ i : Fin record.edges.length, Gate.CompleteProducer
    (Coverage.block source (record.origins i)) ((record.edges.get i).left, true)
    (.alias ((record.edges.get i).right, (record.edges.get i).phase))

instance (record : Record source recovered) : Decidable record.EdgeChecks := by
  unfold EdgeChecks
  infer_instance

def pathCheck (record : Record source recovered) (i : Fin original) : Bool :=
  match replay record.edges i (record.paths i) with
  | none => false
  | some result => decide (result.endpoint = record.base.anchor (record.base.coordinate i) ∧
      result.phase = record.base.phase i)

def AnchorChecks (record : Record source recovered) : Prop :=
  ∀ j, record.base.coordinate (record.base.anchor j) = j ∧
    record.base.phase (record.base.anchor j) = true

instance (record : Record source recovered) : Decidable record.AnchorChecks := by
  unfold AnchorChecks
  infer_instance

def check (record : Record source recovered) : Bool :=
  decide record.EdgeChecks && decide record.base.RowChecks &&
    decide record.AnchorChecks && decide (∀ i, record.pathCheck i = true)

theorem checked_source_is_lift (record : Record source recovered)
    (accepted : record.check = true) (assignment : Fin original → Bool)
    (model : Satisfies assignment source) :
    assignment = record.base.lift (record.base.project assignment) := by
  have checks : ((record.EdgeChecks ∧ record.base.RowChecks) ∧ record.AnchorChecks) ∧
      (∀ i, record.pathCheck i = true) := by simpa [check] using accepted
  have edgeModels : ∀ edge ∈ record.edges, edge.Holds assignment := by
    intro edge member
    obtain ⟨index, same⟩ := List.mem_iff_get.mp member
    have block := Coverage.source_implies_block source (record.origins index) assignment model
    have equation := (Gate.CompleteProducer.correct (checks.1.1.1 index) assignment).mp block
    subst edge
    simpa [AliasEdge.Holds, Gate.eval, literalValue] using equation
  funext i
  have checked := checks.2 i
  unfold pathCheck at checked
  cases replayed : replay record.edges i (record.paths i) with
  | none => simp [replayed] at checked
  | some result =>
    have endpoint : result.endpoint = record.base.anchor (record.base.coordinate i) ∧
        result.phase = record.base.phase i := by simpa [replayed] using checked
    have equation := AliasPath.sound record.edges assignment edgeModels result.sound
    simpa [Recognition.Record.lift, Recognition.Record.project, signedPullback,
      endpoint.1, endpoint.2] using equation

end Record
end AliasTrace

namespace ProducerMetadata

/-- Exact local producer blocks and their finite source origins are replayed in
reported execution order. Freshness is checked against the current known set. -/
def replay (known : Finset (Fin count)) (source : Formula (Fin count)) :
    List (BlockRecord (Fin count) source) → Option (Finset (Fin count))
  | [] => some known
  | block :: rest =>
      if decide block.Valid && decide (block.producer.Ready known) then
        replay (insert block.producer.output.1 known) source rest
      else none

structure Record (source : Formula (Fin count)) where
  roots : Finset (Fin count)
  rank : Fin count → Nat
  blocks : List (BlockRecord (Fin count) source)

namespace Record
variable {count : Nat} {source : Formula (Fin count)}

def selected (record : Record source) : List (Producer (Fin count)) :=
  record.blocks.map BlockRecord.producer

def Checks (record : Record source) : Prop :=
  ValidSelection record.roots record.rank record.selected ∧
    (∀ block ∈ record.blocks, block.Valid) ∧
    replay record.roots source record.blocks = some Finset.univ

instance (record : Record source) : Decidable record.Checks := by
  unfold Checks
  infer_instance

def check (record : Record source) : Bool := decide record.Checks

@[simp] theorem check_iff (record : Record source) :
    record.check = true ↔ record.Checks := by simp [check]

theorem checked_unique (record : Record source) (accepted : record.check = true)
    (left right : Fin count → Bool) (leftModel : Satisfies left source)
    (rightModel : Satisfies right source)
    (sameRoots : ∀ coordinate ∈ record.roots, left coordinate = right coordinate) : left = right := by
  have checks := record.check_iff.mp accepted
  apply validSelection_unique checks.1 left right sameRoots
  · intro producer member
    obtain ⟨block, selected, rfl⟩ := List.mem_map.mp member
    exact block.source_implies (checks.2.1 block selected) left leftModel
  · intro producer member
    obtain ⟨block, selected, rfl⟩ := List.mem_map.mp member
    exact block.source_implies (checks.2.1 block selected) right rightModel

theorem checked_order (record : Record source) (accepted : record.check = true) :
    replay record.roots source record.blocks = some Finset.univ :=
  (record.check_iff.mp accepted).2.2

theorem checked_roots_not_overwritten (record : Record source)
    (accepted : record.check = true) :
    ∀ producer ∈ record.selected, producer.output.1 ∉ record.roots :=
  (record.check_iff.mp accepted).1.2.1

theorem checked_outputs_complete (record : Record source)
    (accepted : record.check = true) :
    ∀ coordinate, coordinate ∉ record.roots →
      ∃ producer ∈ record.selected, producer.output.1 = coordinate :=
  (record.check_iff.mp accepted).1.2.2.1

end Record
end ProducerMetadata
end Controller.Recognition
