module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Native.BoundedEncode
public import Mathlib.Data.Fintype.Card
public import Mathlib.Tactic.FinCases

@[expose] public section

/-! Syntactic strong and deletion backdoors in the complete native encoding.
Restriction only deletes satisfied clauses and assigned literals. In particular,
an empty residual clause does not remove any other clause from the formula.
-/
namespace Controller.Boundaries.Backdoors

open Controller

variable {α : Type*} [DecidableEq α]

/-- Hornness counts distinct positive variables, allowing repeated literals. -/
def HornClause (clause : CNF.Clause α) : Prop :=
  ∀ left ∈ clause, ∀ right ∈ clause,
    left.2 = true → right.2 = true → left.1 = right.1

/-- At most two distinct literals, independently of clause satisfiability. -/
def TwoClause (clause : CNF.Clause α) : Prop :=
  ∀ first ∈ clause, ∀ second ∈ clause, ∀ third ∈ clause,
    first = second ∨ first = third ∨ second = third

def Horn (formula : List (CNF.Clause α)) : Prop :=
  ∀ clause ∈ formula, HornClause clause

def TwoCNF (formula : List (CNF.Clause α)) : Prop :=
  ∀ clause ∈ formula, TwoClause clause

def renameLiteral (phase : α → Bool) (literal : CNF.Literal α) : CNF.Literal α :=
  (literal.1, if phase literal.1 then !literal.2 else literal.2)

def renameClause (phase : α → Bool) (clause : CNF.Clause α) :=
  clause.map (renameLiteral phase)

def RenamableHorn (formula : List (CNF.Clause α)) : Prop :=
  ∃ phase : α → Bool, Horn (formula.map (renameClause phase))

inductive BaseClass where
  | horn | renamableHorn | twoCNF
  deriving DecidableEq

def InClass (target : BaseClass) (formula : List (CNF.Clause α)) : Prop :=
  match target with
  | .horn => Horn formula
  | .renamableHorn => RenamableHorn formula
  | .twoCNF => TwoCNF formula

def deleteClause (backdoor : Finset α) (clause : CNF.Clause α) :=
  clause.filter fun literal => literal.1 ∉ backdoor

def delete (backdoor : Finset α) (formula : List (CNF.Clause α)) :=
  formula.map (deleteClause backdoor)

/-- Values outside the selected finite set are ignored. -/
def restrictClause (backdoor : Finset α) (assignment : α → Bool)
    (clause : CNF.Clause α) : Option (CNF.Clause α) :=
  if ∃ literal ∈ clause, literal.1 ∈ backdoor ∧ assignment literal.1 = literal.2 then
    none
  else some (deleteClause backdoor clause)

def restrict (backdoor : Finset α) (assignment : α → Bool)
    (formula : List (CNF.Clause α)) :=
  formula.filterMap (restrictClause backdoor assignment)

def DeletionBackdoor (target : BaseClass) (formula : List (CNF.Clause α))
    (backdoor : Finset α) : Prop := InClass target (delete backdoor formula)

def StrongBackdoor (target : BaseClass) (formula : List (CNF.Clause α))
    (backdoor : Finset α) : Prop :=
  ∀ assignment : α → Bool, InClass target (restrict backdoor assignment formula)

def xorBlock (left right output : α) : List (CNF.Clause α) :=
  (CNF.Gate.xor (left, true) (right, true)).clauses (output, true)

/-- The finite four-row obstruction holds under every variable polarity choice. -/
theorem xor_not_horn_renamed (left right output : α)
    (different : left ≠ right) (leftOutput : left ≠ output) (rightOutput : right ≠ output)
    (phase : α → Bool) : ¬Horn ((xorBlock left right output).map (renameClause phase)) := by
  intro horn
  cases hl : phase left <;> cases hr : phase right <;> cases ho : phase output <;>
    simp [Horn, HornClause, xorBlock, CNF.Gate.clauses, CNF.negate,
      Std.Sat.Literal.negate, renameClause, renameLiteral, hl, hr, ho,
      different, leftOutput, rightOutput, Ne.symm different,
      Ne.symm leftOutput, Ne.symm rightOutput] at horn

theorem xor_not_twoCNF (left right output : α)
    (different : left ≠ right) (leftOutput : left ≠ output) (rightOutput : right ≠ output) :
    ¬TwoCNF (xorBlock left right output) := by
  intro small
  have row := small [(left, true), (right, true), (output, false)] (by
    simp [xorBlock, CNF.Gate.clauses, CNF.negate, Std.Sat.Literal.negate])
  have impossible := row (left, true) (by simp) (right, true) (by simp)
    (output, false) (by simp)
  simp [different] at impossible

theorem containing_xor_not_class (target : BaseClass)
    (formula : List (CNF.Clause α)) (left right output : α)
    (different : left ≠ right) (leftOutput : left ≠ output) (rightOutput : right ≠ output)
    (embedded : ∀ clause ∈ xorBlock left right output, clause ∈ formula) :
    ¬InClass target formula := by
  cases target with
  | horn =>
      intro horn
      apply xor_not_horn_renamed left right output different leftOutput rightOutput (fun _ => false)
      intro clause member
      obtain ⟨original, rawMember, rfl⟩ := List.mem_map.mp member
      have identity : renameLiteral (fun _ : α => false) = id := by
        funext literal
        rcases literal with ⟨coordinate, polarity⟩
        rfl
      simpa only [renameClause, identity, List.map_id] using
        horn original (embedded original rawMember)
  | renamableHorn =>
      rintro ⟨phase, horn⟩
      apply xor_not_horn_renamed left right output different leftOutput rightOutput phase
      intro clause member
      obtain ⟨original, rawMember, rfl⟩ := List.mem_map.mp member
      exact horn _ (List.mem_map.mpr ⟨original, embedded original rawMember, rfl⟩)
  | twoCNF =>
      intro small
      exact xor_not_twoCNF left right output different leftOutput rightOutput
        (fun clause member => small clause (embedded clause member))

/-- Syntactic obstruction is not waived by an empty clause elsewhere. -/
theorem empty_clause_xor_obstruction (target : BaseClass) (left right output : α)
    (different : left ≠ right) (leftOutput : left ≠ output) (rightOutput : right ≠ output) :
    ¬InClass target ([] :: xorBlock left right output) := by
  apply containing_xor_not_class target _ left right output different leftOutput rightOutput
  intro clause member
  exact List.mem_cons_of_mem [] member

theorem deleteClause_missed (backdoor : Finset α) (clause : CNF.Clause α)
    (missed : ∀ literal ∈ clause, literal.1 ∉ backdoor) :
    deleteClause backdoor clause = clause := by
  apply List.filter_eq_self.mpr
  simpa using missed

theorem restrictClause_missed (backdoor : Finset α) (assignment : α → Bool)
    (clause : CNF.Clause α) (missed : ∀ literal ∈ clause, literal.1 ∉ backdoor) :
    restrictClause backdoor assignment clause = some clause := by
  have unsatisfied : ¬∃ literal ∈ clause,
      literal.1 ∈ backdoor ∧ assignment literal.1 = literal.2 := by
    rintro ⟨literal, member, assigned, _⟩
    exact missed literal member assigned
  simp [restrictClause, unsatisfied, deleteClause_missed backdoor clause missed]

theorem xor_variables (left right output : α) (clause : CNF.Clause α)
    (member : clause ∈ xorBlock left right output) (literal : CNF.Literal α)
    (literalMember : literal ∈ clause) :
    literal.1 = left ∨ literal.1 = right ∨ literal.1 = output := by
  simp only [xorBlock, CNF.Gate.clauses, CNF.negate, Std.Sat.Literal.negate,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at literalMember <;>
    rcases literalMember with rfl | rfl | rfl <;> simp

/-- A missed block is retained literally; unrelated empty clauses have no effect. -/
theorem missed_xor_survives (formula : List (CNF.Clause α)) (backdoor : Finset α)
    (left right output : α)
    (embedded : ∀ clause ∈ xorBlock left right output, clause ∈ formula)
    (missLeft : left ∉ backdoor) (missRight : right ∉ backdoor)
    (missOutput : output ∉ backdoor) :
    (∀ clause ∈ xorBlock left right output, clause ∈ delete backdoor formula) ∧
    (∀ assignment clause, clause ∈ xorBlock left right output →
      clause ∈ restrict backdoor assignment formula) := by
  have missed : ∀ clause ∈ xorBlock left right output,
      ∀ literal ∈ clause, literal.1 ∉ backdoor := by
    intro clause member literal literalMember
    rcases xor_variables left right output clause member literal literalMember with h | h | h
    · simpa [h] using missLeft
    · simpa [h] using missRight
    · simpa [h] using missOutput
  constructor
  · intro clause member
    exact List.mem_map.mpr ⟨clause, embedded clause member,
      deleteClause_missed backdoor clause (missed clause member)⟩
  · intro assignment clause member
    exact List.mem_filterMap.mpr ⟨clause, embedded clause member,
      restrictClause_missed backdoor assignment clause (missed clause member)⟩

def XorFamily (count : Nat) (formula : List (CNF.Clause α))
    (triple : Fin count → Fin 3 → α) : Prop :=
  (∀ bus other slot otherSlot, triple bus slot = triple other otherSlot →
    bus = other ∧ slot = otherSlot) ∧
  (∀ bus clause, clause ∈ xorBlock (triple bus 0) (triple bus 1) (triple bus 2) →
    clause ∈ formula)

theorem backdoor_hits_family (count : Nat) (formula : List (CNF.Clause α))
    (triple : Fin count → Fin 3 → α) (family : XorFamily count formula triple)
    (target : BaseClass) (backdoor : Finset α)
    (valid : DeletionBackdoor target formula backdoor ∨ StrongBackdoor target formula backdoor) :
    ∀ bus, ∃ slot, triple bus slot ∈ backdoor := by
  intro bus
  by_contra absent
  have missed : ∀ slot, triple bus slot ∉ backdoor := by simpa using absent
  have distinct : ∀ a b : Fin 3, a ≠ b → triple bus a ≠ triple bus b := by
    intro a b neq equality
    exact neq (family.1 bus bus a b equality).2
  have retained := missed_xor_survives formula backdoor _ _ _ (family.2 bus)
    (missed 0) (missed 1) (missed 2)
  rcases valid with deletion | strong
  · exact containing_xor_not_class target _ _ _ _
      (distinct 0 1 (by decide)) (distinct 0 2 (by decide))
      (distinct 1 2 (by decide)) retained.1 deletion
  · exact containing_xor_not_class target _ _ _ _
      (distinct 0 1 (by decide)) (distinct 0 2 (by decide))
      (distinct 1 2 (by decide)) (retained.2 (fun _ => false)) (strong (fun _ => false))

/-- Disjoint triples give a cardinal lower bound, including the empty family. -/
theorem backdoor_card (count : Nat) (formula : List (CNF.Clause α))
    (triple : Fin count → Fin 3 → α) (family : XorFamily count formula triple)
    (target : BaseClass) (backdoor : Finset α)
    (valid : DeletionBackdoor target formula backdoor ∨ StrongBackdoor target formula backdoor) :
    count ≤ backdoor.card := by
  classical
  have hit := backdoor_hits_family count formula triple family target backdoor valid
  let selected (bus : Fin count) : {value // value ∈ backdoor} :=
    ⟨triple bus (Classical.choose (hit bus)), Classical.choose_spec (hit bus)⟩
  have injective : Function.Injective selected := by
    intro bus other equality
    exact (family.1 bus other _ _ (congrArg Subtype.val equality)).1
  simpa using Fintype.card_le_of_injective selected injective

open Native

def healthyTriple (parameters : Parameters) (channel : Fin parameters.channels)
    (bus : Fin parameters.buses) (slot : Fin 3) : Variable parameters :=
  if slot = 0 then .internal (.flag .healthy bus)
  else if slot = 1 then .internal (.absent .healthy bus channel)
  else .internal (.mask .healthy bus channel)

theorem healthyTriple_disjoint (parameters : Parameters) (channel : Fin parameters.channels)
    (bus other : Fin parameters.buses) (slot otherSlot : Fin 3)
    (same : healthyTriple parameters channel bus slot =
      healthyTriple parameters channel other otherSlot) : bus = other ∧ slot = otherSlot := by
  fin_cases slot <;> fin_cases otherSlot <;>
    simp_all [healthyTriple]

/-- Literal complete mask rows in the named native specification. -/
theorem native_mask_rows (parameters : Parameters) (channel : Fin parameters.channels)
    (bus : Fin parameters.buses) (clause : CNF.Clause (Variable parameters))
    (member : clause ∈ xorBlock (healthyTriple parameters channel bus 0)
      (healthyTriple parameters channel bus 1) (healthyTriple parameters channel bus 2)) :
    clause ∈ parameters.specificationFormula.clauses.toList := by
  have gateMember : clause ∈ (parameters.gate (.mask .healthy bus channel)).clauses
      (parameters.internal (.mask .healthy bus channel)) := by
    simpa [healthyTriple, xorBlock, Parameters.gate, Parameters.internal,
      Parameters.positive] using member
  have equations : clause ∈ parameters.equationClauses :=
    List.mem_flatMap.mpr ⟨.mask .healthy bus channel,
      parameters.mem_roles _, gateMember⟩
  simpa [Parameters.specificationFormula, Parameters.equationFormula, CNF.ofClauses,
    Controller.CNF.OrderedFormula.Internal.clauses_append] using
    (List.mem_append_left parameters.assertionFormula.clauses.toList equations)

theorem native_xor_family (parameters : Parameters) (channel : Fin parameters.channels) :
    XorFamily parameters.buses parameters.specificationFormula.clauses.toList
      (healthyTriple parameters channel) :=
  ⟨healthyTriple_disjoint parameters channel, native_mask_rows parameters channel⟩

open Native.Bounded

/-- Every literal producer row remains in the full bounded native formula. -/
theorem producer_row_mem (parameters : Parameters) (owner : Internal parameters)
    (clause : CNF.Clause (GlobalVariable parameters))
    (member : clause ∈ (producerFormula parameters owner).clauses.toList) :
    clause ∈ (globalFormula parameters).clauses.toList := by
  have fold : ∀ owners : List (Internal parameters), owner ∈ owners →
      clause ∈ (owners.foldr (fun role suffix => producerFormula parameters role ++ suffix)
        Controller.CNF.OrderedFormula.empty).clauses.toList := by
    intro owners
    induction owners with
    | nil => simp
    | cons head tail ih =>
        intro ownerMember
        simp only [List.mem_cons] at ownerMember
        simp only [List.foldr_cons, Controller.CNF.OrderedFormula.Internal.clauses_append, Array.toList_append,
          List.mem_append]
        rcases ownerMember with rfl | inTail
        · exact Or.inl member
        · exact Or.inr (ih inTail)
  have equations := fold parameters.roles (parameters.mem_roles owner)
  simpa [globalFormula, globalEquationFormula, Controller.CNF.OrderedFormula.Internal.clauses_append] using
    (List.mem_append_left
      (CNF.relabel GlobalVariable.original parameters.assertionFormula).clauses.toList equations)

def boundedHealthyTriple (parameters : Parameters) (channel : Fin parameters.channels)
    (bus : Fin parameters.buses) (slot : Fin 3) : GlobalVariable parameters :=
  .original (healthyTriple parameters channel bus slot)

theorem bounded_mask_rows (parameters : Parameters) (channel : Fin parameters.channels)
    (bus : Fin parameters.buses) (clause : CNF.Clause (GlobalVariable parameters))
    (member : clause ∈ xorBlock (boundedHealthyTriple parameters channel bus 0)
      (boundedHealthyTriple parameters channel bus 1) (boundedHealthyTriple parameters channel bus 2)) :
    clause ∈ (globalFormula parameters).clauses.toList := by
  apply producer_row_mem parameters (.mask .healthy bus channel) clause
  simpa [producerFormula, rows, expand, Producer.rows, Parameters.gate,
    Parameters.internal, Parameters.positive, originalLiteral, localSlots,
    boundedHealthyTriple, healthyTriple, xorBlock, CNF.Gate.clauses,
    CNF.relabel, Controller.CNF.OrderedFormula.relabel, Controller.CNF.OrderedFormula.Clause.relabel, CNF.ofClauses, CNF.negate,
    Std.Sat.Literal.negate] using member

theorem bounded_xor_family (parameters : Parameters) (channel : Fin parameters.channels) :
    XorFamily parameters.buses (globalFormula parameters).clauses.toList
      (boundedHealthyTriple parameters channel) := by
  constructor
  · intro bus other slot otherSlot equality
    apply healthyTriple_disjoint parameters channel bus other slot otherSlot
    exact GlobalVariable.original.inj equality
  · exact bounded_mask_rows parameters channel

/-- All three syntactic classes and both backdoor notions for the actual bounded CNF. -/
theorem native_backdoor_lower_bound (parameters : Parameters)
    (target : BaseClass) (backdoor : Finset (GlobalVariable parameters))
    (valid : DeletionBackdoor target (globalFormula parameters).clauses.toList backdoor ∨
      StrongBackdoor target (globalFormula parameters).clauses.toList backdoor) :
    parameters.buses ≤ backdoor.card :=
  backdoor_card parameters.buses _ _
    (bounded_xor_family parameters parameters.bridge.target) target backdoor valid

theorem specification_backdoor_lower_bound (parameters : Parameters)
    (target : BaseClass) (backdoor : Finset (Variable parameters))
    (valid : DeletionBackdoor target parameters.specificationFormula.clauses.toList backdoor ∨
      StrongBackdoor target parameters.specificationFormula.clauses.toList backdoor) :
    parameters.buses ≤ backdoor.card :=
  backdoor_card parameters.buses _ _
    (native_xor_family parameters parameters.bridge.target) target backdoor valid

/-- The native bridge supplies an actual channel; no extra nonemptiness premise is hidden. -/
theorem native_channel_positive (parameters : Parameters) : 0 < parameters.channels :=
  Nat.zero_lt_of_lt parameters.bridge.target.isLt

/-- The generic cardinal theorem also covers zero buses without native positive-bus data. -/
theorem zero_bus_bound (backdoor : Finset α) : 0 ≤ backdoor.card := Nat.zero_le _

end Controller.Boundaries.Backdoors
