module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Recognition.Normalization
public import Mathlib.Data.Fintype.Pi

@[expose] public section

/-! Bounded local truth-table certificates.

All checks quantify over every local row, including both output values. A row
encoding must carry inverse laws and the little-endian bit convention. Support
partitions carry an explicit bijection, so disjointness and exhaustiveness do
not follow from a reported support size. No global input table is enumerated.
-/

namespace Controller.Recognition.LocalTables
open Controller.CNF

abbrev Row (k : Nat) := Fin k → Bool

/-- Inverse laws certify exhaustive row coverage. The bit convention matches
Python's row >> position encoding. These are bounded finite certificates. -/
structure RowIndex (k : Nat) where
  decode : Fin (2 ^ k) → Row k
  encode : Row k → Fin (2 ^ k)
  decode_encode : ∀ row, decode (encode row) = row
  encode_decode : ∀ index, encode (decode index) = index
  littleEndian : ∀ index coordinate, decode index coordinate = index.val.testBit coordinate.val

/-- Untrusted row maps can be checked over their finite local domains. -/
structure RowMaps (k : Nat) where
  decode : Fin (2 ^ k) → Row k
  encode : Row k → Fin (2 ^ k)

namespace RowMaps

def Valid (maps : RowMaps k) : Prop :=
  (∀ row, maps.decode (maps.encode row) = row) ∧
  (∀ numeric, maps.encode (maps.decode numeric) = numeric) ∧
  (∀ numeric coordinate, maps.decode numeric coordinate = numeric.val.testBit coordinate.val)

instance (maps : RowMaps k) : Decidable maps.Valid :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def checked (maps : RowMaps k) (valid : maps.Valid) : RowIndex k where
  decode := maps.decode
  encode := maps.encode
  decode_encode := valid.1
  encode_decode := valid.2.1
  littleEndian := valid.2.2

end RowMaps

namespace RowIndex

def equivalence (index : RowIndex k) : Fin (2 ^ k) ≃ Row k where
  toFun := index.decode
  invFun := index.encode
  left_inv := index.encode_decode
  right_inv := index.decode_encode

theorem all_rows (index : RowIndex k) (predicate : Row k → Prop) :
    (∀ numeric, predicate (index.decode numeric)) ↔ ∀ row, predicate row := by
  constructor
  · intro checked row
    simpa only [index.decode_encode] using checked (index.encode row)
  · exact fun checked numeric => checked (index.decode numeric)

end RowIndex

structure Table (k : Nat) where
  index : RowIndex k
  entry : Fin (2 ^ k) → Bool

namespace Table

def eval (table : Table k) (row : Row k) : Bool := table.entry (table.index.encode row)

@[simp] theorem eval_decode (table : Table k) (numeric : Fin (2 ^ k)) :
    table.eval (table.index.decode numeric) = table.entry numeric := by
  simp only [eval, table.index.encode_decode]

def assignment (row : Row k) (output : Bool) : (Fin k ⊕ Unit) → Bool :=
  Sum.elim row (fun _ => output)

/-- Neither one-way implications nor unchecked output polarities pass this test. -/
def Complete (table : Table k) (block : Formula (Fin k ⊕ Unit)) : Prop :=
  ∀ numeric output,
    Satisfies (assignment (table.index.decode numeric) output) block ↔
      output = table.entry numeric

instance (table : Table k) (block : Formula (Fin k ⊕ Unit)) :
    Decidable (table.Complete block) := by
  letI : ∀ a : (Fin k ⊕ Unit) → Bool, Decidable (Satisfies a block) := fun a =>
    decidable_of_iff (Controller.CNF.OrderedFormula.eval a block = true) (satisfies_iff_stdSat a block).symm
  unfold Complete
  infer_instance

theorem complete_correct (table : Table k) (block : Formula (Fin k ⊕ Unit))
    (checked : table.Complete block) (row : Row k) (output : Bool) :
    Satisfies (assignment row output) block ↔ output = table.eval row := by
  simpa only [table.index.decode_encode, eval] using checked (table.index.encode row) output

/-- Signed external input/output identities are supplied explicitly. Repeated
or complementary inputs are allowed for this semantic direction. -/
def signal (inputs : Fin k → Literal α) (output : Literal α) : (Fin k ⊕ Unit) → Literal α :=
  Sum.elim inputs (fun _ => output)

def instantiate (block : Formula (Fin k ⊕ Unit)) (inputs : Fin k → Literal α)
    (output : Literal α) : Formula α :=
  signedRelabel (fun i => (signal inputs output i).1)
    (fun i => (signal inputs output i).2) block

theorem signed_complete_correct (table : Table k) (block : Formula (Fin k ⊕ Unit))
    (checked : table.Complete block) (inputs : Fin k → Literal α) (output : Literal α)
    (a : α → Bool) :
    Satisfies a (instantiate block inputs output) ↔
      literalValue a output = table.eval (fun i => literalValue a (inputs i)) := by
  rw [instantiate, satisfies_signedRelabel]
  have same : signedPullback (fun i => (signal inputs output i).1)
      (fun i => (signal inputs output i).2) a =
      assignment (fun i => literalValue a (inputs i)) (literalValue a output) := by
    funext coordinate
    cases coordinate <;> rfl
  rw [same]
  exact table.complete_correct block checked _ _

/-- Removing inessential coordinates is certified on every original row. -/
def Reduced (table : Table k) (reduced : Table m) (coordinates : Fin m ↪ Fin k) : Prop :=
  ∀ numeric, table.entry numeric =
    reduced.eval (fun i => table.index.decode numeric (coordinates i))

instance (table : Table k) (reduced : Table m) (coordinates : Fin m ↪ Fin k) :
    Decidable (table.Reduced reduced coordinates) := inferInstanceAs (Decidable (∀ _, _))

theorem reduced_correct (table : Table k) (reduced : Table m) (coordinates : Fin m ↪ Fin k)
    (checked : table.Reduced reduced coordinates) (row : Row k) :
    table.eval row = reduced.eval (fun i => row (coordinates i)) := by
  simpa only [eval, table.index.decode_encode] using checked (table.index.encode row)

/-- Flipping a proposed removed coordinate leaves the table value unchanged. -/
theorem inessential_coordinate (table : Table k) (reduced : Table m)
    (coordinates : Fin m ↪ Fin k) (checked : table.Reduced reduced coordinates)
    (first second : Row k) (same : ∀ i, first (coordinates i) = second (coordinates i)) :
    table.eval first = table.eval second := by
  rw [table.reduced_correct reduced coordinates checked first,
    table.reduced_correct reduced coordinates checked second]
  exact congrArg reduced.eval (funext same)

end Table

inductive Operation where
  | and | or | xor
  deriving DecidableEq

namespace Operation

def eval : Operation → Bool → Bool → Bool
  | .and, first, second => first && second
  | .or, first, second => first || second
  | .xor, first, second => first ^^ second

end Operation

/-- The two scopes have no common coordinate and exhaust the original scope. -/
structure Partition (k left right : Nat) where
  coordinates : (Fin left ⊕ Fin right) ≃ Fin k

namespace Partition

def left (p : Partition k l r) : Fin l → Fin k := fun i => p.coordinates (.inl i)
def right (p : Partition k l r) : Fin r → Fin k := fun i => p.coordinates (.inr i)

theorem disjoint (p : Partition k l r) (i : Fin l) (j : Fin r) : p.left i ≠ p.right j := by
  intro same
  have impossible := p.coordinates.injective same
  cases impossible

theorem exhaustive (p : Partition k l r) (i : Fin k) :
    (∃ j, p.left j = i) ∨ (∃ j, p.right j = i) := by
  obtain ⟨coordinate, equal⟩ := p.coordinates.surjective i
  cases coordinate with
  | inl j => exact Or.inl ⟨j, equal⟩
  | inr j => exact Or.inr ⟨j, equal⟩

end Partition

/-- A proposed decomposition checks every row after the declared disjoint cut. -/
def Decomposition (table : Table k) (first : Table l) (second : Table r)
    (partition : Partition k l r) (operation : Operation) (phase : Bool) : Prop :=
  ∀ numeric, table.entry numeric =
    (operation.eval
      (first.eval (fun i => table.index.decode numeric (partition.left i)))
      (second.eval (fun i => table.index.decode numeric (partition.right i))) == phase)

instance (table : Table k) (first : Table l) (second : Table r)
    (partition : Partition k l r) (operation : Operation) (phase : Bool) :
    Decidable (Decomposition table first second partition operation phase) :=
  inferInstanceAs (Decidable (∀ _, _))

theorem decomposition_correct (table : Table k) (first : Table l) (second : Table r)
    (partition : Partition k l r) (operation : Operation) (phase : Bool)
    (checked : Decomposition table first second partition operation phase) (row : Row k) :
    table.eval row =
      (operation.eval (first.eval (fun i => row (partition.left i)))
        (second.eval (fun i => row (partition.right i))) == phase) := by
  simpa only [Table.eval, table.index.decode_encode] using checked (table.index.encode row)

end Controller.Recognition.LocalTables
