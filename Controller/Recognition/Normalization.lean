module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Recognition.Producers

@[expose] public section

/-! Signed normalization certificates.

Term identities refer to their explicit leaf variables and the same term store.
Alias representatives are justified by signed paths rather than missing-value
lookups. These rewrites certify proposed simplifications, not discovery.
-/

namespace Controller.Recognition
open Controller.CNF

inductive BooleanTerm (α : Type*) where
  | constant (value : Bool)
  | leaf (identity : α)
  | neg (child : BooleanTerm α)
  | and (left right : BooleanTerm α)
  | or (left right : BooleanTerm α)
  | xor (left right : BooleanTerm α)
  deriving DecidableEq

namespace BooleanTerm

def eval (a : α → Bool) : BooleanTerm α → Bool
  | .constant value => value
  | .leaf identity => a identity
  | .neg child => !child.eval a
  | .and left right => left.eval a && right.eval a
  | .or left right => left.eval a || right.eval a
  | .xor left right => left.eval a ^^ right.eval a

def substitute (leaf : α → BooleanTerm β) : BooleanTerm α → BooleanTerm β
  | .constant value => .constant value
  | .leaf identity => leaf identity
  | .neg child => .neg (child.substitute leaf)
  | .and left right => .and (left.substitute leaf) (right.substitute leaf)
  | .or left right => .or (left.substitute leaf) (right.substitute leaf)
  | .xor left right => .xor (left.substitute leaf) (right.substitute leaf)

theorem eval_substitute (a : β → Bool) (leaf : α → BooleanTerm β) (term : BooleanTerm α) :
    (term.substitute leaf).eval a = term.eval (fun i => (leaf i).eval a) := by
  induction term <;> simp_all [substitute, eval]

/-- Explicit cut-leaf identities suffice; term IDs alone do not. -/
theorem cut_substitution (a : β → Bool) (values : α → Bool)
    (leaf : α → BooleanTerm β) (identity : ∀ i, (leaf i).eval a = values i)
    (term : BooleanTerm α) : (term.substitute leaf).eval a = term.eval values := by
  rw [eval_substitute]
  have same : (fun i => (leaf i).eval a) = values := funext identity
  rw [same]

inductive Rewrite : BooleanTerm α → BooleanTerm α → Prop where
  | refl (term) : Rewrite term term
  | trans {first second third} : Rewrite first second → Rewrite second third → Rewrite first third
  | neg {first second} : Rewrite first second → Rewrite (.neg first) (.neg second)
  | andCongr {a b c d} : Rewrite a b → Rewrite c d → Rewrite (.and a c) (.and b d)
  | orCongr {a b c d} : Rewrite a b → Rewrite c d → Rewrite (.or a c) (.or b d)
  | xorCongr {a b c d} : Rewrite a b → Rewrite c d → Rewrite (.xor a c) (.xor b d)
  | doubleNeg (a) : Rewrite (.neg (.neg a)) a
  | negConstant (value) : Rewrite (.neg (.constant value)) (.constant (!value))
  | andTrue (a) : Rewrite (.and (.constant true) a) a
  | andFalse (a) : Rewrite (.and (.constant false) a) (.constant false)
  | orFalse (a) : Rewrite (.or (.constant false) a) a
  | orTrue (a) : Rewrite (.or (.constant true) a) (.constant true)
  | xorFalse (a) : Rewrite (.xor (.constant false) a) a
  | xorTrue (a) : Rewrite (.xor (.constant true) a) (.neg a)
  | andDuplicate (a) : Rewrite (.and a a) a
  | orDuplicate (a) : Rewrite (.or a a) a
  | xorDuplicate (a) : Rewrite (.xor a a) (.constant false)
  | andComplement (a) : Rewrite (.and a (.neg a)) (.constant false)
  | orComplement (a) : Rewrite (.or a (.neg a)) (.constant true)
  | andSwap (a b) : Rewrite (.and a b) (.and b a)
  | orSwap (a b) : Rewrite (.or a b) (.or b a)
  | xorSwap (a b) : Rewrite (.xor a b) (.xor b a)
  | andFlatten (a b c) : Rewrite (.and (.and a b) c) (.and a (.and b c))
  | orFlatten (a b c) : Rewrite (.or (.or a b) c) (.or a (.or b c))
  | xorFlatten (a b c) : Rewrite (.xor (.xor a b) c) (.xor a (.xor b c))
  | deMorgan (a b) : Rewrite (.or a b) (.neg (.and (.neg a) (.neg b)))
  | xorPhase (a b) : Rewrite (.xor (.neg a) b) (.neg (.xor a b))

theorem Rewrite.sound (a : α → Bool) {first second : BooleanTerm α}
    (proof : Rewrite first second) : first.eval a = second.eval a := by
  induction proof with
  | refl => rfl
  | trans _ _ first second => exact first.trans second
  | neg _ ih => simp only [eval, ih]
  | andCongr _ _ first second => simp only [eval, first, second]
  | orCongr _ _ first second => simp only [eval, first, second]
  | xorCongr _ _ first second => simp only [eval, first, second]
  | doubleNeg term => simp only [eval]; cases term.eval a <;> rfl
  | negConstant value => rfl
  | andTrue term => simp only [eval]; cases term.eval a <;> rfl
  | andFalse term => simp only [eval]; cases term.eval a <;> rfl
  | orFalse term => simp only [eval]; cases term.eval a <;> rfl
  | orTrue term => simp only [eval]; cases term.eval a <;> rfl
  | xorFalse term => simp only [eval]; cases term.eval a <;> rfl
  | xorTrue term => simp only [eval]; cases term.eval a <;> rfl
  | andDuplicate term => simp only [eval]; cases term.eval a <;> rfl
  | orDuplicate term => simp only [eval]; cases term.eval a <;> rfl
  | xorDuplicate term => simp only [eval]; cases term.eval a <;> rfl
  | andComplement term => simp only [eval]; cases term.eval a <;> rfl
  | orComplement term => simp only [eval]; cases term.eval a <;> rfl
  | andSwap left right => simp only [eval]; cases left.eval a <;> cases right.eval a <;> rfl
  | orSwap left right => simp only [eval]; cases left.eval a <;> cases right.eval a <;> rfl
  | xorSwap left right => simp only [eval]; cases left.eval a <;> cases right.eval a <;> rfl
  | andFlatten left middle right =>
    simp only [eval]
    cases left.eval a <;> cases middle.eval a <;> cases right.eval a <;> rfl
  | orFlatten left middle right =>
    simp only [eval]
    cases left.eval a <;> cases middle.eval a <;> cases right.eval a <;> rfl
  | xorFlatten left middle right =>
    simp only [eval]
    cases left.eval a <;> cases middle.eval a <;> cases right.eval a <;> rfl
  | deMorgan left right => simp only [eval]; cases left.eval a <;> cases right.eval a <;> rfl
  | xorPhase left right => simp only [eval]; cases left.eval a <;> cases right.eval a <;> rfl

end BooleanTerm

/-- An interning identity names a term in one explicit store. -/
structure TermStore (α : Type*) (ι : Type*) where
  term : ι → BooleanTerm α

namespace TermStore

theorem reuse (store : TermStore α ι) (a : α → Bool) {first second : ι}
    (key : store.term first = store.term second) :
    (store.term first).eval a = (store.term second).eval a := congrArg (BooleanTerm.eval a) key

end TermStore

structure AliasEdge (α : Type*) where
  left : α
  right : α
  phase : Bool

namespace AliasEdge

def Holds (a : α → Bool) (edge : AliasEdge α) : Prop :=
  a edge.left = (a edge.right == edge.phase)

def block (edge : AliasEdge α) : Formula α :=
  (Gate.alias (edge.right, edge.phase)).block (edge.left, true)

theorem block_correct (edge : AliasEdge α) (a : α → Bool) :
    Satisfies a edge.block ↔ edge.Holds a := by
  rw [block, Gate.block_correct]
  simp [Holds, Gate.eval, literalValue]

end AliasEdge

/-- True phase is equality; false phase is disequality. -/
inductive AliasPath (edges : List (AliasEdge α)) : α → α → Bool → Prop where
  | refl (i) : AliasPath edges i i true
  | edge (e) (member : e ∈ edges) : AliasPath edges e.left e.right e.phase
  | symm {i j phase} : AliasPath edges i j phase → AliasPath edges j i phase
  | trans {i j k first second} : AliasPath edges i j first → AliasPath edges j k second →
      AliasPath edges i k (second == first)

theorem AliasPath.sound (edges : List (AliasEdge α)) (a : α → Bool)
    (model : ∀ e ∈ edges, e.Holds a) {i j phase} (path : AliasPath edges i j phase) :
    a i = (a j == phase) := by
  induction path with
  | refl i => cases a i <;> rfl
  | edge e member => exact model e member
  | @symm i j phase _ ih =>
    cases hi : a i <;> cases hj : a j <;> cases hp : phase <;> simp_all
  | @trans i j k first second _ _ ihFirst ihSecond =>
    rw [ihFirst, ihSecond]
    cases a k <;> cases first <;> cases second <;> rfl

theorem contradictory_alias_cycle (edges : List (AliasEdge α)) {i : α}
    (cycle : AliasPath edges i i false) : ¬∃ a, ∀ e ∈ edges, e.Holds a := by
  rintro ⟨a, model⟩
  have impossible := AliasPath.sound edges a model cycle
  cases hi : a i <;> simp_all

/-- Every variable has an explicit, path-justified representative. -/
structure AliasRepresentatives (edges : List (AliasEdge α)) (β : Type*) where
  representative : α → β
  anchor : β → α
  phase : α → Bool
  anchor_identity : ∀ b, representative (anchor b) = b
  anchor_phase : ∀ b, phase (anchor b) = true
  path : ∀ i, AliasPath edges i (anchor (representative i)) (phase i)
  edge_compatible : ∀ e ∈ edges, representative e.left = representative e.right ∧
    phase e.left = (phase e.right == e.phase)

namespace AliasRepresentatives
variable {α β : Type*} {edges : List (AliasEdge α)}

def lift (r : AliasRepresentatives edges β) (values : β → Bool) : α → Bool :=
  fun i => values (r.representative i) == r.phase i

def quotient (r : AliasRepresentatives edges β) (formula : Formula α) : Formula β :=
  signedRelabel r.representative r.phase formula

theorem lift_models_aliases (r : AliasRepresentatives edges β) (values : β → Bool) :
    ∀ e ∈ edges, e.Holds (r.lift values) := by
  intro e member
  obtain ⟨same, phase⟩ := r.edge_compatible e member
  simp only [AliasEdge.Holds, lift, same, phase]
  cases values (r.representative e.right) <;> cases r.phase e.right <;> cases e.phase <;> rfl

theorem original_is_lift (r : AliasRepresentatives edges β) (a : α → Bool)
    (model : ∀ e ∈ edges, e.Holds a) :
    a = r.lift (fun b => a (r.anchor b)) := by
  funext i
  exact AliasPath.sound edges a model (r.path i)

theorem quotient_models (r : AliasRepresentatives edges β) (values : β → Bool)
    (formula : Formula α) :
    Satisfies values (r.quotient formula) ↔ Satisfies (r.lift values) formula :=
  satisfies_signedRelabel r.representative r.phase values formula

theorem quotient_projection (r : AliasRepresentatives edges β) (formula : Formula α) :
    (∃ a, (∀ e ∈ edges, e.Holds a) ∧ Satisfies a formula) ↔
      ∃ values, Satisfies values (r.quotient formula) := by
  constructor
  · rintro ⟨a, aliases, model⟩
    refine ⟨fun b => a (r.anchor b), (r.quotient_models _ formula).mpr ?_⟩
    rw [← r.original_is_lift a aliases]
    exact model
  · rintro ⟨values, model⟩
    exact ⟨r.lift values, r.lift_models_aliases values, (r.quotient_models values formula).mp model⟩

end AliasRepresentatives

/-- A complementary literal pair is true under every assignment. -/
theorem complementary_clause (a : α → Bool) (row : Clause α) (literal : Literal α)
    (positive : literal ∈ row) (negative : negate literal ∈ row) : ClauseHolds a row := by
  by_cases holds : LiteralHolds a literal
  · exact ⟨literal, positive, holds⟩
  · exact ⟨negate literal, negative, (literalHolds_negate a literal).mpr holds⟩

/-- Erasure is justified by the substituted row's actual literals. -/
theorem erase_complementary_row (a : α → Bool) (rows : List (Clause α))
    (row : Clause α) (literal : Literal α) (positive : literal ∈ row)
    (negative : negate literal ∈ row) :
    Satisfies a (ofClauses (row :: rows)) ↔ Satisfies a (ofClauses rows) := by
  simp only [satisfies_ofClauses, List.forall_mem_cons]
  exact and_iff_right (complementary_clause a row literal positive negative)

end Controller.Recognition
