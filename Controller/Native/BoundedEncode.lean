module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Native.Encode

@[expose] public section

/-!
# Binary expansion of native n-ary producers

Each producer retains its signed principal output and receives a disjoint finite
set of private prefix outputs. Empty conjunctions and disjunctions retain their
unit blocks; unary producers retain a complete alias block. Every larger fold
uses binary gates, with one principal output and exactly `arity - 2` private
outputs.
-/

namespace Controller.Native.Bounded

inductive Junction where
  | conjunction
  | disjunction
  deriving DecidableEq, Repr

def Junction.gate (junction : Junction) (inputs : List (CNF.Literal α)) : CNF.Gate α :=
  match junction with
  | .conjunction => .and inputs
  | .disjunction => .or inputs

def Junction.eval (junction : Junction) (assignment : α → Bool)
    (inputs : List (CNF.Literal α)) : Bool := (junction.gate inputs).eval assignment

def auxiliaryCount : CNF.Gate α → ℕ
  | .and inputs | .or inputs => inputs.length - 2
  | _ => 0

/-- Private slots are distinct from every variable already present in the circuit. -/
inductive LocalVariable (α : Type*) (count : ℕ) where
  | original (slot : α)
  | auxiliary (index : Fin count)
  deriving DecidableEq, Repr

def originalLiteral (literal : CNF.Literal α) : CNF.Literal (LocalVariable α count) :=
  (.original literal.1, literal.2)

structure Producer (α : Type*) where
  output : CNF.Literal α
  gate : CNF.Gate α
  deriving DecidableEq, Repr

def Producer.rows (producer : Producer α) : List (CNF.Clause α) :=
  producer.gate.clauses producer.output

def Producer.relabel (map : α → β) (producer : Producer α) : Producer β where
  output := (map producer.output.1, producer.output.2)
  gate := producer.gate.relabel map

/-- The prefix ending at `index + 2`, with the final prefix using the principal output. -/
def foldOutput (inputs : List (CNF.Literal α)) (output : CNF.Literal α)
    (index : Fin (inputs.length - 1)) :
    CNF.Literal (LocalVariable α (inputs.length - 2)) :=
  if privateOutput : index.val < inputs.length - 2 then
    (.auxiliary ⟨index.val, privateOutput⟩, true)
  else originalLiteral output

def foldInputs (inputs : List (CNF.Literal α)) (atLeastTwo : 2 ≤ inputs.length)
    (index : Fin (inputs.length - 1)) :
    List (CNF.Literal (LocalVariable α (inputs.length - 2))) :=
  [if first : index.val = 0 then
      originalLiteral (inputs.get ⟨0, by omega⟩)
    else
      (.auxiliary ⟨index.val - 1, by have := index.isLt; omega⟩, true),
    originalLiteral (inputs.get ⟨index.val + 1, by have := index.isLt; omega⟩)]

/-- Ordered binary prefix producers; all private outputs precede the principal output. -/
def foldProducers (junction : Junction) (inputs : List (CNF.Literal α))
    (output : CNF.Literal α) : List (Producer (LocalVariable α (inputs.length - 2))) :=
  if empty : inputs.length = 0 then
    [{ output := originalLiteral output, gate := junction.gate [] }]
  else if unary : inputs.length = 1 then
    [{ output := originalLiteral output,
       gate := .alias (originalLiteral (inputs.get ⟨0, by omega⟩)) }]
  else
    (List.finRange (inputs.length - 1)).map fun index =>
      { output := foldOutput inputs output index
        gate := junction.gate (foldInputs inputs (by omega) index) }

/-- Private values are fully determined by the original input-literal values. -/
def foldAssignment (junction : Junction) (inputs : List (CNF.Literal α))
    (assignment : α → Bool) : LocalVariable α (inputs.length - 2) → Bool
  | .original slot => assignment slot
  | .auxiliary index => junction.eval assignment (inputs.take (index.val + 2))

/-- Expansion leaves every non-n-ary native producer as its complete original block. -/
def expand (output : CNF.Literal α) :
    (gate : CNF.Gate α) → List (Producer (LocalVariable α (auxiliaryCount gate)))
  | .and inputs => foldProducers .conjunction inputs output
  | .or inputs => foldProducers .disjunction inputs output
  | .xor left right =>
      [{ output := originalLiteral output,
         gate := .xor (originalLiteral left) (originalLiteral right) }]
  | .alias input => [{ output := originalLiteral output, gate := .alias (originalLiteral input) }]
  | .not input => [{ output := originalLiteral output, gate := .not (originalLiteral input) }]
  | .constant value => [{ output := originalLiteral output, gate := .constant value }]

def rows (output : CNF.Literal α) (gate : CNF.Gate α) :
    List (CNF.Clause (LocalVariable α (auxiliaryCount gate))) :=
  (expand output gate).flatMap Producer.rows

/-- The exact number of binary-fold producers, including empty and unary cases. -/
def foldProducerCount (arity : ℕ) : ℕ := max 1 (arity - 1)

/-- AND/OR block counts after binary expansion. -/
def foldRowCount (arity : ℕ) : ℕ :=
  if arity = 0 then 1 else if arity = 1 then 2 else 3 * (arity - 1)

/-- Literal incidences count repeated occurrences as stored in the native blocks. -/
def foldLiteralCount (arity : ℕ) : ℕ :=
  if arity = 0 then 1 else if arity = 1 then 4 else 7 * (arity - 1)


@[simp] theorem literalValue_original (assignment : LocalVariable α count → Bool)
    (literal : CNF.Literal α) :
    CNF.literalValue assignment (originalLiteral literal) =
      CNF.literalValue (fun slot => assignment (.original slot)) literal := rfl

@[simp] theorem foldAssignment_original (junction : Junction) (inputs : List (CNF.Literal α))
    (assignment : α → Bool) (slot : α) :
    foldAssignment junction inputs assignment (.original slot) = assignment slot := rfl

/-- The n-ary replacement allocates exactly the displayed number of producers. -/
theorem foldProducers_length (junction : Junction) (inputs : List (CNF.Literal α))
    (output : CNF.Literal α) :
    (foldProducers junction inputs output).length = foldProducerCount inputs.length := by
  unfold foldProducers
  split
  · rename_i empty
    simp [foldProducerCount, empty]
  · split
    · rename_i unary
      simp [foldProducerCount, unary]
    · rename_i nonempty nonunary
      simp only [List.length_map, List.length_finRange, foldProducerCount]
      omega

/-- Every expanded fold producer has at most two input incidences. -/
theorem foldProducers_bounded (junction : Junction) (inputs : List (CNF.Literal α))
    (output : CNF.Literal α) :
    ∀ producer ∈ foldProducers junction inputs output, producer.gate.inputs.length ≤ 2 := by
  unfold foldProducers
  split
  · cases junction <;> simp [Junction.gate, CNF.Gate.inputs]
  · split
    · simp [CNF.Gate.inputs]
    · cases junction <;> simp [Junction.gate, CNF.Gate.inputs, foldInputs]

/-- Row count includes both directions of every complete binary producer. -/
theorem foldProducers_rows_length (junction : Junction) (inputs : List (CNF.Literal α))
    (output : CNF.Literal α) :
    ((foldProducers junction inputs output).flatMap Producer.rows).length =
      foldRowCount inputs.length := by
  unfold foldProducers
  split
  · rename_i empty
    cases junction <;> simp [Producer.rows, Junction.gate, CNF.Gate.clauses, foldRowCount, empty]
  · split
    · rename_i unary
      simp [Producer.rows, CNF.Gate.clauses, foldRowCount, unary]
    · rename_i nonempty nonunary
      cases junction <;>
        simp [Producer.rows, Junction.gate, CNF.Gate.clauses, foldInputs,
          foldRowCount, nonempty, nonunary, List.map_const', Nat.mul_comm, Function.comp_def]

private theorem sum_map_flatMap (items : List α) (rows : α → List β) (weight : β → ℕ) :
    ((items.flatMap rows).map weight).sum =
      (items.map fun item => ((rows item).map weight).sum).sum := by
  induction items with
  | nil => simp
  | cons head tail inductionHypothesis => simp [inductionHypothesis]

/-- Exact stored literal incidences, including repeated and complementary inputs. -/
theorem foldProducers_literals_length (junction : Junction) (inputs : List (CNF.Literal α))
    (output : CNF.Literal α) :
    (((foldProducers junction inputs output).flatMap Producer.rows).map List.length).sum =
      foldLiteralCount inputs.length := by
  unfold foldProducers
  split
  · rename_i empty
    cases junction <;>
      simp [Producer.rows, Junction.gate, CNF.Gate.clauses, foldLiteralCount, empty]
  · split
    · rename_i unary
      simp [Producer.rows, CNF.Gate.clauses, foldLiteralCount, unary]
    · rename_i nonempty nonunary
      cases junction <;>
        simp [Producer.rows, Junction.gate, CNF.Gate.clauses, foldInputs,
          foldLiteralCount, nonempty, nonunary, List.map_const', Nat.mul_comm, sum_map_flatMap, Function.comp_def]


/-- Complete local blocks impose exactly their listed producer equations. -/
theorem satisfies_producer_rows_iff (producers : List (Producer α)) (assignment : α → Bool) :
    CNF.Satisfies assignment (CNF.ofClauses (producers.flatMap Producer.rows)) ↔
      ∀ producer ∈ producers,
        CNF.literalValue assignment producer.output = producer.gate.eval assignment := by
  constructor
  · intro satisfied producer membership
    apply (CNF.Gate.block_correct assignment producer.output producer.gate).mp
    rw [CNF.Gate.block, CNF.satisfies_ofClauses]
    intro row rowMember
    exact (CNF.satisfies_ofClauses assignment _).mp satisfied row
      (List.mem_flatMap.mpr ⟨producer, membership, rowMember⟩)
  · intro equations
    rw [CNF.satisfies_ofClauses]
    intro row membership
    obtain ⟨producer, producerMember, rowMember⟩ := List.mem_flatMap.mp membership
    have satisfied := (CNF.Gate.block_correct assignment producer.output producer.gate).mpr
      (equations producer producerMember)
    exact (CNF.satisfies_ofClauses assignment _).mp satisfied row rowMember

def Junction.combine : Junction → Bool → Bool → Bool
  | .conjunction => (· && ·)
  | .disjunction => (· || ·)

@[simp] theorem Junction.eval_pair (junction : Junction) (assignment : α → Bool)
    (left right : CNF.Literal α) :
    junction.eval assignment [left, right] =
      junction.combine (CNF.literalValue assignment left) (CNF.literalValue assignment right) := by
  cases junction <;> simp [Junction.eval, Junction.gate, Junction.combine, CNF.Gate.eval]

@[simp] theorem Junction.eval_singleton (junction : Junction) (assignment : α → Bool)
    (input : CNF.Literal α) :
    junction.eval assignment [input] = CNF.literalValue assignment input := by
  cases junction <;> simp [Junction.eval, Junction.gate, CNF.Gate.eval]

theorem Junction.eval_append (junction : Junction) (assignment : α → Bool)
    (left right : List (CNF.Literal α)) :
    junction.eval assignment (left ++ right) =
      junction.combine (junction.eval assignment left) (junction.eval assignment right) := by
  cases junction <;> simp [Junction.eval, Junction.gate, Junction.combine, CNF.Gate.eval]

/-- The next prefix value is one binary junction with the next stored input incidence. -/
theorem Junction.eval_take_succ (junction : Junction) (assignment : α → Bool)
    (inputs : List (CNF.Literal α)) (index : Fin inputs.length) :
    junction.eval assignment (inputs.take (index.val + 1)) =
      junction.combine (junction.eval assignment (inputs.take index.val))
        (CNF.literalValue assignment (inputs.get index)) := by
  rw [List.take_succ_eq_append_getElem index.isLt, Junction.eval_append, Junction.eval_singleton]
  rfl

/-- The final prefix reads the signed principal output; all earlier prefixes are private. -/
theorem foldAssignment_foldOutput (junction : Junction) (inputs : List (CNF.Literal α))
    (output : CNF.Literal α) (assignment : α → Bool)
    (equation : CNF.literalValue assignment output = junction.eval assignment inputs)
    (index : Fin (inputs.length - 1)) :
    CNF.literalValue (foldAssignment junction inputs assignment) (foldOutput inputs output index) =
      junction.eval assignment (inputs.take (index.val + 2)) := by
  unfold foldOutput
  split
  · simp [CNF.literalValue, foldAssignment]
  · rename_i last
    have full : inputs.length ≤ index.val + 2 := by omega
    rw [List.take_of_length_le full]
    simpa [originalLiteral, CNF.literalValue, foldAssignment] using equation

private theorem Junction.eval_take_one (junction : Junction) (assignment : α → Bool)
    (inputs : List (CNF.Literal α)) (nonempty : 0 < inputs.length) :
    junction.eval assignment (inputs.take 1) =
      CNF.literalValue assignment (inputs.get ⟨0, nonempty⟩) := by
  cases inputs with
  | nil => simp at nonempty
  | cons head tail => simp

/-- The fold inputs evaluate to the preceding prefix and the next input incidence. -/
theorem foldAssignment_foldInputs (junction : Junction) (inputs : List (CNF.Literal α))
    (assignment : α → Bool) (atLeastTwo : 2 ≤ inputs.length)
    (index : Fin (inputs.length - 1)) :
    (junction.gate (foldInputs inputs atLeastTwo index)).eval
      (foldAssignment junction inputs assignment) =
        junction.eval assignment (inputs.take (index.val + 2)) := by
  change junction.eval (foldAssignment junction inputs assignment)
    (foldInputs inputs atLeastTwo index) = _
  unfold foldInputs
  rw [Junction.eval_pair]
  have nextBound : index.val + 1 < inputs.length := by have := index.isLt; omega
  have step := junction.eval_take_succ assignment inputs ⟨index.val + 1, nextBound⟩
  simp only [Fin.val_mk] at step
  rw [step]
  congr 1
  · split
    · rename_i first
      simp only [literalValue_original, foldAssignment_original]
      simpa [first] using (junction.eval_take_one assignment inputs (by omega)).symm
    · rename_i nonfirst
      have previous : index.val - 1 + 2 = index.val + 1 := by omega
      simp [CNF.literalValue, foldAssignment, previous]

/-- A complete n-ary producer model extends to every complete binary fold block. -/
theorem foldAssignment_satisfies (junction : Junction) (inputs : List (CNF.Literal α))
    (output : CNF.Literal α) (assignment : α → Bool)
    (equation : CNF.literalValue assignment output = junction.eval assignment inputs) :
    CNF.Satisfies (foldAssignment junction inputs assignment)
      (CNF.ofClauses ((foldProducers junction inputs output).flatMap Producer.rows)) := by
  apply (satisfies_producer_rows_iff _ _).mpr
  unfold foldProducers
  split
  · rename_i empty
    have inputsEmpty : inputs = [] := List.eq_nil_of_length_eq_zero empty
    subst inputs
    intro producer membership
    simp only [List.mem_singleton] at membership
    subst producer
    cases junction <;>
      simpa [originalLiteral, CNF.literalValue, foldAssignment, Junction.eval,
        Junction.gate, CNF.Gate.eval] using equation
  · split
    · rename_i unary
      cases inputs with
      | nil => simp at unary
      | cons head tail =>
          have tailEmpty : tail = [] := List.eq_nil_of_length_eq_zero (by simpa using unary)
          subst tail
          intro producer membership
          simp only [List.mem_singleton] at membership
          subst producer
          simpa [originalLiteral, CNF.literalValue, foldAssignment, CNF.Gate.eval] using equation
    · intro producer membership
      obtain ⟨index, _, rfl⟩ := List.mem_map.mp membership
      exact (foldAssignment_foldOutput junction inputs output assignment equation index).trans
        (foldAssignment_foldInputs junction inputs assignment (by omega) index).symm

/-- Every model of the fold determines every prefix, including its signed final output. -/
theorem fold_model_prefixes (junction : Junction) (inputs : List (CNF.Literal α))
    (output : CNF.Literal α)
    (assignment : LocalVariable α (inputs.length - 2) → Bool)
    (atLeastTwo : 2 ≤ inputs.length)
    (satisfied : CNF.Satisfies assignment
      (CNF.ofClauses ((foldProducers junction inputs output).flatMap Producer.rows))) :
    ∀ index : Fin (inputs.length - 1),
      CNF.literalValue assignment (foldOutput inputs output index) =
        junction.eval (fun slot => assignment (.original slot)) (inputs.take (index.val + 2)) := by
  have equations := (satisfies_producer_rows_iff _ _).mp satisfied
  have nonempty : inputs.length ≠ 0 := by omega
  have nonunary : inputs.length ≠ 1 := by omega
  have ranked : ∀ height, ∀ index : Fin (inputs.length - 1), index.val = height →
      CNF.literalValue assignment (foldOutput inputs output index) =
        junction.eval (fun slot => assignment (.original slot)) (inputs.take (index.val + 2)) := by
    intro height
    induction height using Nat.strong_induction_on with
    | h height inductionHypothesis =>
        intro index indexHeight
        have defining := equations
          { output := foldOutput inputs output index,
            gate := junction.gate (foldInputs inputs atLeastTwo index) }
          (by
            simp only [foldProducers, dite_eq_right nonempty, dite_eq_right nonunary]
            exact List.mem_map.mpr ⟨index, List.mem_finRange index, rfl⟩)
        rw [defining]
        change junction.eval assignment (foldInputs inputs atLeastTwo index) = _
        unfold foldInputs
        rw [Junction.eval_pair]
        have nextBound : index.val + 1 < inputs.length := by have := index.isLt; omega
        have step := junction.eval_take_succ (fun slot => assignment (.original slot)) inputs
          ⟨index.val + 1, nextBound⟩
        rw [step]
        congr 1
        split
        · rename_i first
          simp only [literalValue_original]
          simpa [first] using
            (junction.eval_take_one (fun slot => assignment (.original slot)) inputs (by omega)).symm
        · rename_i nonfirst
          have earlierBound : index.val - 1 < inputs.length - 1 := by have := index.isLt; omega
          have earlier : index.val - 1 < height := by omega
          have privateOutput : index.val - 1 < inputs.length - 2 := by have := index.isLt; omega
          have prefixLength : index.val - 1 + 2 = index.val + 1 := by omega
          have previous := inductionHypothesis (index.val - 1) earlier
            ⟨index.val - 1, earlierBound⟩ rfl
          simpa [foldOutput, privateOutput, prefixLength] using previous
  intro index
  exact ranked index.val index rfl

/-- The private auxiliary assignment is uniquely determined by the original slots. -/
theorem fold_model_eq_assignment (junction : Junction) (inputs : List (CNF.Literal α))
    (output : CNF.Literal α)
    (assignment : LocalVariable α (inputs.length - 2) → Bool)
    (satisfied : CNF.Satisfies assignment
      (CNF.ofClauses ((foldProducers junction inputs output).flatMap Producer.rows))) :
    assignment = foldAssignment junction inputs (fun slot => assignment (.original slot)) := by
  funext slot
  cases slot with
  | original original => rfl
  | auxiliary index =>
      have atLeastTwo : 2 ≤ inputs.length := by have := index.isLt; omega
      have prefixIndex : index.val < inputs.length - 1 := by have := index.isLt; omega
      have value := fold_model_prefixes junction inputs output assignment atLeastTwo satisfied
        ⟨index.val, prefixIndex⟩
      simpa [foldOutput, index.isLt, CNF.literalValue, foldAssignment] using value

/-- Projecting a complete fold model yields the original n-ary producer equation. -/
theorem fold_model_projects (junction : Junction) (inputs : List (CNF.Literal α))
    (output : CNF.Literal α)
    (assignment : LocalVariable α (inputs.length - 2) → Bool)
    (satisfied : CNF.Satisfies assignment
      (CNF.ofClauses ((foldProducers junction inputs output).flatMap Producer.rows))) :
    CNF.literalValue (fun slot => assignment (.original slot)) output =
      junction.eval (fun slot => assignment (.original slot)) inputs := by
  have equations := (satisfies_producer_rows_iff _ _).mp satisfied
  by_cases empty : inputs.length = 0
  · have inputsEmpty : inputs = [] := List.eq_nil_of_length_eq_zero empty
    subst inputs
    have defining := equations
      { output := originalLiteral output, gate := junction.gate [] }
      (by simp [foldProducers])
    cases junction <;>
      simpa [originalLiteral, CNF.literalValue, Junction.eval, Junction.gate, CNF.Gate.eval] using defining
  · by_cases unary : inputs.length = 1
    · cases inputs with
      | nil => simp at unary
      | cons head tail =>
          have tailEmpty : tail = [] := List.eq_nil_of_length_eq_zero (by simpa using unary)
          subst tail
          have defining := equations
            { output := originalLiteral output, gate := .alias (originalLiteral head) }
            (by simp [foldProducers])
          simpa [originalLiteral, CNF.literalValue, CNF.Gate.eval] using defining
    · have atLeastTwo : 2 ≤ inputs.length := by omega
      have finalIndex : inputs.length - 2 < inputs.length - 1 := by omega
      have value := fold_model_prefixes junction inputs output assignment atLeastTwo satisfied
        ⟨inputs.length - 2, finalIndex⟩
      have full : inputs.length ≤ inputs.length - 2 + 2 := by omega
      simpa [foldOutput, List.take_of_length_le full] using value

/-- Existence of a fold extension imposes precisely its complete original equation. -/
theorem fold_extension_iff (junction : Junction) (inputs : List (CNF.Literal α))
    (output : CNF.Literal α) (original : α → Bool) :
    (∃ assignment : LocalVariable α (inputs.length - 2) → Bool,
      (∀ slot, assignment (.original slot) = original slot) ∧
        CNF.Satisfies assignment
          (CNF.ofClauses ((foldProducers junction inputs output).flatMap Producer.rows))) ↔
      CNF.literalValue original output = junction.eval original inputs := by
  constructor
  · rintro ⟨assignment, roots, satisfied⟩
    have restriction : (fun slot => assignment (.original slot)) = original := funext roots
    simpa [restriction] using fold_model_projects junction inputs output assignment satisfied
  · intro equation
    exact ⟨foldAssignment junction inputs original, fun _ => rfl,
      foldAssignment_satisfies junction inputs output original equation⟩

/-- A fixed original producer model has exactly one complete private fold extension. -/
theorem fold_unique_extension (junction : Junction) (inputs : List (CNF.Literal α))
    (output : CNF.Literal α) (original : α → Bool)
    (equation : CNF.literalValue original output = junction.eval original inputs) :
    ∃! assignment : LocalVariable α (inputs.length - 2) → Bool,
      (∀ slot, assignment (.original slot) = original slot) ∧
        CNF.Satisfies assignment
          (CNF.ofClauses ((foldProducers junction inputs output).flatMap Producer.rows)) := by
  refine ⟨foldAssignment junction inputs original,
    ⟨fun _ => rfl, foldAssignment_satisfies junction inputs output original equation⟩, ?_⟩
  intro assignment properties
  have restriction : (fun slot => assignment (.original slot)) = original := funext properties.1
  simpa [restriction] using fold_model_eq_assignment junction inputs output assignment properties.2

/-- Private extension for every native producer kind. -/
def expansionAssignment (gate : CNF.Gate α) (assignment : α → Bool) :
    LocalVariable α (auxiliaryCount gate) → Bool :=
  match gate with
  | .and inputs => foldAssignment .conjunction inputs assignment
  | .or inputs => foldAssignment .disjunction inputs assignment
  | .xor _ _ | .alias _ | .not _ | .constant _ => fun slot =>
      match slot with
      | .original original => assignment original
      | .auxiliary index => Fin.elim0 index

@[simp] theorem expansionAssignment_original (gate : CNF.Gate α) (assignment : α → Bool)
    (slot : α) : expansionAssignment gate assignment (.original slot) = assignment slot := by
  cases gate <;> rfl

/-- Complete bounded expansion preserves the original producer equation in projection. -/
theorem expansion_model_projects (gate : CNF.Gate α) (output : CNF.Literal α)
    (assignment : LocalVariable α (auxiliaryCount gate) → Bool)
    (satisfied : CNF.Satisfies assignment (CNF.ofClauses (rows output gate))) :
    CNF.literalValue (fun slot => assignment (.original slot)) output =
      gate.eval (fun slot => assignment (.original slot)) := by
  have equations := (satisfies_producer_rows_iff _ _).mp satisfied
  cases gate with
  | and inputs => exact fold_model_projects .conjunction inputs output assignment satisfied
  | or inputs => exact fold_model_projects .disjunction inputs output assignment satisfied
  | xor left right =>
      have defining := equations
        { output := originalLiteral output,
          gate := .xor (originalLiteral left) (originalLiteral right) } (by simp [expand])
      simpa [CNF.Gate.eval] using defining
  | «alias» input =>
      have defining := equations
        { output := originalLiteral output, gate := .alias (originalLiteral input) } (by simp [expand])
      simpa [CNF.Gate.eval] using defining
  | not input =>
      have defining := equations
        { output := originalLiteral output, gate := .not (originalLiteral input) } (by simp [expand])
      simpa [CNF.Gate.eval] using defining
  | constant value =>
      have defining := equations
        { output := originalLiteral output, gate := .constant value } (by simp [expand])
      simpa [CNF.Gate.eval] using defining

/-- Every complete original producer model extends through its bounded replacement. -/
theorem expansionAssignment_satisfies (gate : CNF.Gate α) (output : CNF.Literal α)
    (assignment : α → Bool)
    (equation : CNF.literalValue assignment output = gate.eval assignment) :
    CNF.Satisfies (expansionAssignment gate assignment) (CNF.ofClauses (rows output gate)) := by
  cases gate with
  | and inputs => exact foldAssignment_satisfies .conjunction inputs output assignment equation
  | or inputs => exact foldAssignment_satisfies .disjunction inputs output assignment equation
  | xor left right =>
      apply (satisfies_producer_rows_iff _ _).mpr
      intro producer membership
      simp only [expand, List.mem_singleton] at membership
      subst producer
      simpa [CNF.Gate.eval, originalLiteral, CNF.literalValue, expansionAssignment] using equation
  | «alias» input =>
      apply (satisfies_producer_rows_iff _ _).mpr
      intro producer membership
      simp only [expand, List.mem_singleton] at membership
      subst producer
      simpa [CNF.Gate.eval, originalLiteral, CNF.literalValue, expansionAssignment] using equation
  | not input =>
      apply (satisfies_producer_rows_iff _ _).mpr
      intro producer membership
      simp only [expand, List.mem_singleton] at membership
      subst producer
      simpa [CNF.Gate.eval, originalLiteral, CNF.literalValue, expansionAssignment] using equation
  | constant value =>
      apply (satisfies_producer_rows_iff _ _).mpr
      intro producer membership
      simp only [expand, List.mem_singleton] at membership
      subst producer
      simpa [CNF.Gate.eval, originalLiteral, CNF.literalValue, expansionAssignment] using equation

/-- Private coordinates of any expanded model equal their canonical values. -/
theorem expansion_model_eq_assignment (gate : CNF.Gate α) (output : CNF.Literal α)
    (assignment : LocalVariable α (auxiliaryCount gate) → Bool)
    (satisfied : CNF.Satisfies assignment (CNF.ofClauses (rows output gate))) :
    assignment = expansionAssignment gate (fun slot => assignment (.original slot)) := by
  cases gate with
  | and inputs => exact fold_model_eq_assignment .conjunction inputs output assignment satisfied
  | or inputs => exact fold_model_eq_assignment .disjunction inputs output assignment satisfied
  | xor left right | «alias» left | not left | constant left =>
      funext slot
      cases slot with
      | original original => rfl
      | auxiliary index => exact Fin.elim0 index
def expansionProducerCount : CNF.Gate α → ℕ
  | .and inputs | .or inputs => foldProducerCount inputs.length
  | _ => 1

def expansionRowCount : CNF.Gate α → ℕ
  | .and inputs | .or inputs => foldRowCount inputs.length
  | .xor _ _ => 4
  | .alias _ | .not _ => 2
  | .constant _ => 1

def expansionLiteralCount : CNF.Gate α → ℕ
  | .and inputs | .or inputs => foldLiteralCount inputs.length
  | .xor _ _ => 12
  | .alias _ | .not _ => 4
  | .constant _ => 1

theorem expand_length (gate : CNF.Gate α) (output : CNF.Literal α) :
    (expand output gate).length = expansionProducerCount gate := by
  cases gate with
  | and inputs => exact foldProducers_length .conjunction inputs output
  | or inputs => exact foldProducers_length .disjunction inputs output
  | xor left right | «alias» left | not left | constant left => simp [expand, expansionProducerCount]

/-- Every replacement producer has at most two stored input incidences. -/
theorem expand_bounded (gate : CNF.Gate α) (output : CNF.Literal α) :
    ∀ producer ∈ expand output gate, producer.gate.inputs.length ≤ 2 := by
  cases gate with
  | and inputs => exact foldProducers_bounded .conjunction inputs output
  | or inputs => exact foldProducers_bounded .disjunction inputs output
  | xor left right | «alias» left | not left | constant left => simp [expand, CNF.Gate.inputs]

theorem rows_length (gate : CNF.Gate α) (output : CNF.Literal α) :
    (rows output gate).length = expansionRowCount gate := by
  cases gate with
  | and inputs => exact foldProducers_rows_length .conjunction inputs output
  | or inputs => exact foldProducers_rows_length .disjunction inputs output
  | xor left right | «alias» left | not left | constant left =>
      simp [rows, expand, Producer.rows, CNF.Gate.clauses, expansionRowCount]

theorem rows_literal_count (gate : CNF.Gate α) (output : CNF.Literal α) :
    ((rows output gate).map List.length).sum = expansionLiteralCount gate := by
  cases gate with
  | and inputs => exact foldProducers_literals_length .conjunction inputs output
  | or inputs => exact foldProducers_literals_length .disjunction inputs output
  | xor left right | «alias» left | not left | constant left =>
      simp [rows, expand, Producer.rows, CNF.Gate.clauses, expansionLiteralCount]

/-- Private prefix slots carry their owning producer role. -/
inductive GlobalVariable (parameters : Parameters) where
  | original (slot : Controller.Native.Variable parameters)
  | auxiliary (owner : Internal parameters)
      (index : Fin (auxiliaryCount (parameters.gate owner)))
  deriving DecidableEq

def localSlots (parameters : Parameters) (owner : Internal parameters) :
    LocalVariable (Controller.Native.Variable parameters) (auxiliaryCount (parameters.gate owner)) →
      GlobalVariable parameters
  | .original slot => .original slot
  | .auxiliary index => .auxiliary owner index

/-- Every original slot and every private prefix slot is retained in the declared universe. -/
def globalVariables (parameters : Parameters) : List (GlobalVariable parameters) :=
  parameters.variableRoles.map GlobalVariable.original ++
    parameters.roles.flatMap fun owner =>
      (List.finRange (auxiliaryCount (parameters.gate owner))).map (.auxiliary owner)

@[simp] theorem mem_globalVariables (parameters : Parameters) (slot : GlobalVariable parameters) :
    slot ∈ globalVariables parameters := by
  cases slot with
  | original original =>
      apply List.mem_append_left
      exact List.mem_map.mpr ⟨original, parameters.mem_variableRoles original, rfl⟩
  | auxiliary owner index =>
      apply List.mem_append_right
      exact List.mem_flatMap.mpr ⟨owner, parameters.mem_roles owner,
        List.mem_map.mpr ⟨index, by simp, rfl⟩⟩

instance (parameters : Parameters) : Fintype (GlobalVariable parameters) :=
  Fintype.ofList (globalVariables parameters) (mem_globalVariables parameters)

/-- Exact additional variable count is the sum of private outputs for each producer. -/
theorem globalVariables_length (parameters : Parameters) :
    (globalVariables parameters).length = parameters.variableRoles.length +
      (parameters.roles.map fun owner => auxiliaryCount (parameters.gate owner)).sum := by
  simp [globalVariables]

/-- Different producers have disjoint private slot families. -/
theorem private_owner_injective (parameters : Parameters) (left right : Internal parameters)
    (leftIndex : Fin (auxiliaryCount (parameters.gate left)))
    (rightIndex : Fin (auxiliaryCount (parameters.gate right)))
    (equality : GlobalVariable.auxiliary left leftIndex = .auxiliary right rightIndex) : left = right := by
  cases equality
  rfl

/-- Each declared slot occurs once, including slots of producers with equal values. -/
theorem globalVariables_nodup (parameters : Parameters) : (globalVariables parameters).Nodup := by
  have originals : (parameters.variableRoles.map GlobalVariable.original).Nodup :=
    List.Nodup.map (by intro left right equality; cases equality; rfl) parameters.variableRoles_nodup
  have privates : (parameters.roles.flatMap fun owner =>
      (List.finRange (auxiliaryCount (parameters.gate owner))).map
        (GlobalVariable.auxiliary owner)).Nodup := by
    rw [List.nodup_flatMap]
    constructor
    · intro owner _
      exact List.Nodup.map (by intro left right equality; cases equality; rfl) (List.nodup_finRange _)
    · apply parameters.roles_nodup.imp
      intro left right different value leftMember rightMember
      obtain ⟨leftIndex, _, rfl⟩ := List.mem_map.mp leftMember
      obtain ⟨rightIndex, _, equality⟩ := List.mem_map.mp rightMember
      exact different (private_owner_injective parameters left right leftIndex rightIndex equality.symm)
  simp [globalVariables, List.nodup_append, originals, privates]
  grind

def producerFormula (parameters : Parameters) (owner : Internal parameters) :
    CNF.Formula (GlobalVariable parameters) :=
  CNF.relabel (localSlots parameters owner)
    (CNF.ofClauses (rows (parameters.internal owner) (parameters.gate owner)))

def globalEquationFormula (parameters : Parameters) : CNF.Formula (GlobalVariable parameters) :=
  parameters.roles.foldr (fun owner suffix => producerFormula parameters owner ++ suffix) Controller.CNF.OrderedFormula.empty

def globalFormula (parameters : Parameters) : CNF.Formula (GlobalVariable parameters) :=
  globalEquationFormula parameters ++
    CNF.relabel GlobalVariable.original parameters.assertionFormula

/-- The full bounded equation layout contains every local producer exactly as a conjunct. -/
theorem globalEquationFormula_iff (parameters : Parameters) (assignment : GlobalVariable parameters → Bool) :
    CNF.Satisfies assignment (globalEquationFormula parameters) ↔
      ∀ owner, CNF.Satisfies (assignment ∘ localSlots parameters owner)
        (CNF.ofClauses (rows (parameters.internal owner) (parameters.gate owner))) := by
  have fold (owners : List (Internal parameters)) :
      CNF.Satisfies assignment
        (owners.foldr (fun owner suffix => producerFormula parameters owner ++ suffix) Controller.CNF.OrderedFormula.empty) ↔
      ∀ owner ∈ owners, CNF.Satisfies assignment (producerFormula parameters owner) := by
    induction owners with
    | nil => simp
    | cons head tail inductionHypothesis =>
        simp [CNF.satisfies_append, inductionHypothesis]
  simpa [globalEquationFormula, producerFormula, CNF.satisfies_relabel] using fold parameters.roles

def globalAssignment (parameters : Parameters) (original : Controller.Native.Variable parameters → Bool) :
    GlobalVariable parameters → Bool
  | .original slot => original slot
  | .auxiliary owner index =>
      expansionAssignment (parameters.gate owner) original (.auxiliary index)

theorem globalAssignment_local (parameters : Parameters)
    (original : Controller.Native.Variable parameters → Bool) (owner : Internal parameters) :
    globalAssignment parameters original ∘ localSlots parameters owner =
      expansionAssignment (parameters.gate owner) original := by
  funext slot
  cases slot with
  | original original => simp [globalAssignment, localSlots]
  | auxiliary index => rfl

/-- A complete named native model lifts to the complete bounded layout. -/
theorem globalAssignment_satisfies (parameters : Parameters)
    (original : Controller.Native.Variable parameters → Bool)
    (satisfied : CNF.Satisfies original parameters.specificationFormula) :
    CNF.Satisfies (globalAssignment parameters original) (globalFormula parameters) := by
  have parts := (CNF.satisfies_append _ _ _).mp satisfied
  apply (CNF.satisfies_append _ _ _).mpr
  constructor
  · apply (globalEquationFormula_iff _ _).mpr
    intro owner
    rw [globalAssignment_local]
    apply expansionAssignment_satisfies
    have equation := (parameters.equationFormula_iff original).mp parts.1 owner
    simpa [Parameters.internal, Parameters.positive, CNF.literalValue] using equation
  · apply (CNF.satisfies_relabel _ _ _).mpr
    exact parts.2

/-- Full bounded models project through every complete producer and retained assertion. -/
theorem global_model_projects (parameters : Parameters) (assignment : GlobalVariable parameters → Bool)
    (satisfied : CNF.Satisfies assignment (globalFormula parameters)) :
    CNF.Satisfies (fun slot => assignment (.original slot)) parameters.specificationFormula := by
  have parts := (CNF.satisfies_append _ _ _).mp satisfied
  apply (CNF.satisfies_append _ _ _).mpr
  constructor
  · apply (parameters.equationFormula_iff _).mpr
    intro owner
    have localModel := (globalEquationFormula_iff _ _).mp parts.1 owner
    have projected := expansion_model_projects (parameters.gate owner) (parameters.internal owner)
      (assignment ∘ localSlots parameters owner) localModel
    simpa [Parameters.internal, Parameters.positive, CNF.literalValue, localSlots, Function.comp_def] using projected
  · exact (CNF.satisfies_relabel _ _ _).mp parts.2

/-- Every private bounded coordinate is determined by the original named slots. -/
theorem global_model_eq_assignment (parameters : Parameters) (assignment : GlobalVariable parameters → Bool)
    (satisfied : CNF.Satisfies assignment (globalFormula parameters)) :
    assignment = globalAssignment parameters (fun slot => assignment (.original slot)) := by
  have equations := (globalEquationFormula_iff _ _).mp
    ((CNF.satisfies_append _ _ _).mp satisfied).1
  funext slot
  cases slot with
  | original original => rfl
  | auxiliary owner index =>
      have localEquality := expansion_model_eq_assignment (parameters.gate owner) (parameters.internal owner)
        (assignment ∘ localSlots parameters owner) (equations owner)
      have value := congrFun localEquality (.auxiliary index)
      simpa [globalAssignment, localSlots, Function.comp_def] using value

/-- Fixed original slots admit a bounded model exactly when they admit the named specification. -/
theorem global_extension_iff (parameters : Parameters)
    (original : Controller.Native.Variable parameters → Bool) :
    (∃ assignment : GlobalVariable parameters → Bool,
      (∀ slot, assignment (.original slot) = original slot) ∧
        CNF.Satisfies assignment (globalFormula parameters)) ↔
      CNF.Satisfies original parameters.specificationFormula := by
  constructor
  · rintro ⟨assignment, roots, satisfied⟩
    have restriction : (fun slot => assignment (.original slot)) = original := funext roots
    simpa [restriction] using global_model_projects parameters assignment satisfied
  · intro satisfied
    exact ⟨globalAssignment parameters original, fun _ => rfl,
      globalAssignment_satisfies parameters original satisfied⟩

/-- Every named-specification model has exactly one complete bounded extension. -/
theorem global_unique_extension (parameters : Parameters)
    (original : Controller.Native.Variable parameters → Bool)
    (satisfied : CNF.Satisfies original parameters.specificationFormula) :
    ∃! assignment : GlobalVariable parameters → Bool,
      (∀ slot, assignment (.original slot) = original slot) ∧
        CNF.Satisfies assignment (globalFormula parameters) := by
  refine ⟨globalAssignment parameters original,
    ⟨fun _ => rfl, globalAssignment_satisfies parameters original satisfied⟩, ?_⟩
  intro assignment properties
  have restriction : (fun slot => assignment (.original slot)) = original := funext properties.1
  simpa [restriction] using global_model_eq_assignment parameters assignment properties.2

def literalIncidences (formula : CNF.Formula α) : ℕ :=
  (formula.clauses.toList.map List.length).sum

theorem producerFormula_rows (parameters : Parameters) (owner : Internal parameters) :
    (producerFormula parameters owner).clauses.size = expansionRowCount (parameters.gate owner) := by
  simpa [producerFormula, CNF.relabel, Controller.CNF.OrderedFormula.relabel, CNF.ofClauses] using
    rows_length (parameters.gate owner) (parameters.internal owner)

theorem producerFormula_literals (parameters : Parameters) (owner : Internal parameters) :
    literalIncidences (producerFormula parameters owner) =
      expansionLiteralCount (parameters.gate owner) := by
  simpa [producerFormula, literalIncidences, CNF.relabel, Controller.CNF.OrderedFormula.relabel,
    Controller.CNF.OrderedFormula.Clause.relabel, CNF.ofClauses, Function.comp_def] using
      rows_literal_count (parameters.gate owner) (parameters.internal owner)

/-- Exact complete bounded row count, with all four original assertion occurrences. -/
theorem globalFormula_rows (parameters : Parameters) :
    (globalFormula parameters).clauses.size =
      (parameters.roles.map fun owner => expansionRowCount (parameters.gate owner)).sum + 4 := by
  have fold (owners : List (Internal parameters)) :
      (owners.foldr (fun owner suffix => producerFormula parameters owner ++ suffix)
        Controller.CNF.OrderedFormula.empty).clauses.size =
      (owners.map fun owner => expansionRowCount (parameters.gate owner)).sum := by
    induction owners with
    | nil => simp [Controller.CNF.OrderedFormula.empty]
    | cons head tail inductionHypothesis =>
        simp [Controller.CNF.OrderedFormula.Internal.clauses_append, producerFormula_rows, inductionHypothesis]
  simp [globalFormula, globalEquationFormula, Controller.CNF.OrderedFormula.Internal.clauses_append,
    fold, CNF.relabel, Controller.CNF.OrderedFormula.relabel, Parameters.assertionFormula,
    Parameters.assertions, CNF.ofClauses]

/-- Exact literal incidence count, including every occurrence in every bounded block. -/
theorem globalFormula_literals (parameters : Parameters) :
    literalIncidences (globalFormula parameters) =
      (parameters.roles.map fun owner => expansionLiteralCount (parameters.gate owner)).sum + 4 := by
  have append (left right : CNF.Formula (GlobalVariable parameters)) :
      literalIncidences (left ++ right) = literalIncidences left + literalIncidences right := by
    simp [literalIncidences, Controller.CNF.OrderedFormula.Internal.clauses_append]
  have fold (owners : List (Internal parameters)) :
      literalIncidences (owners.foldr (fun owner suffix => producerFormula parameters owner ++ suffix)
        Controller.CNF.OrderedFormula.empty) =
      (owners.map fun owner => expansionLiteralCount (parameters.gate owner)).sum := by
    induction owners with
    | nil => simp [literalIncidences, Controller.CNF.OrderedFormula.empty]
    | cons head tail inductionHypothesis =>
        simp [append, producerFormula_literals, inductionHypothesis]
  rw [globalFormula, append, globalEquationFormula, fold]
  simp [literalIncidences,
    CNF.relabel, Controller.CNF.OrderedFormula.relabel, Controller.CNF.OrderedFormula.Clause.relabel,
    Parameters.assertionFormula, Parameters.assertions, CNF.ofClauses]

end Controller.Native.Bounded
