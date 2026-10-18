module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.CNF.Relabel
public import Controller.CNF.Tseitin
public import Mathlib.Data.List.Forall2

@[expose] public section

/-!
# Existential projection of private observation wrappers

Signal variables and private auxiliaries are disjoint tagged types. General
observation projection requires necessity and uniform orientation extensions.
The optional-activity grammar and negative-Horn attachment grammar have
separate constructive extensions. No uniqueness or model-count assertion is
made for these wrappers.
-/

namespace Controller.Native.ObservationProjection

open CNF

/-- Assemble signal and private assignments without identifying their coordinates. -/
def joint (signals : σ → Bool) (auxiliary : α → Bool) : Sum σ α → Bool :=
  Sum.elim signals auxiliary

/-- A signal pair is discrepant in either unequal orientation. -/
def Discrepant (signals : σ → Bool) (pair : Literal σ × Literal σ) : Prop :=
  literalValue signals pair.1 ≠ literalValue signals pair.2

/-- The exact semantic hypotheses of observation projection, with one extension
working uniformly for every signal model in each realized orientation. -/
structure ProjectionContract (definitions : Formula σ) (wrapper : Formula (Sum σ α))
    (pairs : ρ → Literal σ × Literal σ) (activities : ρ → Literal α)
    (accepted : Set ρ) : Prop where
  guards : ∀ signals auxiliary, Satisfies (joint signals auxiliary) wrapper →
    ∀ i, LiteralHolds auxiliary (activities i) → Discrepant signals (pairs i)
  necessary : ∀ signals auxiliary, Satisfies (joint signals auxiliary) wrapper →
    ∃ i ∈ accepted, LiteralHolds auxiliary (activities i)
  uniform : ∀ i ∈ accepted, ∀ left right : Bool, left ≠ right →
    (¬∃ signals, Satisfies signals definitions ∧ literalValue signals (pairs i).1 = left ∧
      literalValue signals (pairs i).2 = right) ∨
    ∃ auxiliary, ∀ signals, Satisfies signals definitions →
      literalValue signals (pairs i).1 = left → literalValue signals (pairs i).2 = right →
      Satisfies (joint signals auxiliary) wrapper

/-- Both directions are under the supplied functional signal definitions. -/
theorem observation_projection {definitions : Formula σ} {wrapper : Formula (Sum σ α)}
    {pairs : ρ → Literal σ × Literal σ} {activities : ρ → Literal α} {accepted : Set ρ}
    (contract : ProjectionContract definitions wrapper pairs activities accepted)
    (signals : σ → Bool) (model : Satisfies signals definitions) :
    (∃ auxiliary, Satisfies (joint signals auxiliary) wrapper) ↔
      ∃ i ∈ accepted, Discrepant signals (pairs i) := by
  constructor
  · rintro ⟨auxiliary, satisfies⟩
    obtain ⟨i, membership, active⟩ := contract.necessary signals auxiliary satisfies
    exact ⟨i, membership, contract.guards signals auxiliary satisfies i active⟩
  · rintro ⟨i, membership, difference⟩
    rcases contract.uniform i membership _ _ difference with impossible | extension
    · exact False.elim (impossible ⟨signals, model, rfl, rfl⟩)
    · obtain ⟨auxiliary, satisfies⟩ := extension
      exact ⟨auxiliary, satisfies signals model rfl rfl⟩

/-- Auxiliary-only inactivity contradiction supplies the necessity condition. -/
theorem accepted_activity_forced (auxiliary : α → Bool) (pure : Formula α)
    (activities : ρ → Literal α) (accepted : Set ρ)
    (model : Satisfies auxiliary pure)
    (inactiveConflict : ¬∃ assignment, Satisfies assignment pure ∧
      ∀ i ∈ accepted, ¬LiteralHolds assignment (activities i)) :
    ∃ i ∈ accepted, LiteralHolds auxiliary (activities i) := by
  classical
  by_contra missing
  apply inactiveConflict
  refine ⟨auxiliary, model, ?_⟩
  intro i membership active
  exact missing ⟨i, membership, active⟩


/-- Unit propagation certificate: source rows, occurrence-preserving reordering,
and deletion of a literal whose negation has already been derived as a unit. -/
inductive UnitDerived (formula : Formula α) : Clause α → Prop where
  | source (clause : Clause α) (membership : clause ∈ formula.clauses) : UnitDerived formula clause
  | reorder {left right : Clause α} (proof : UnitDerived formula left)
      (permutation : left.Perm right) : UnitDerived formula right
  | propagate (literal : Literal α) (tail : Clause α)
      (clause : UnitDerived formula (literal :: tail))
      (unit : UnitDerived formula [negate literal]) : UnitDerived formula tail

/-- Every derived propagation row is entailed by its original formula. -/
theorem unitDerived_sound {formula : Formula α} {clause : Clause α}
    (proof : UnitDerived formula clause) (values : α → Bool) (model : Satisfies values formula) :
    ClauseHolds values clause := by
  induction proof with
  | source clause membership => exact model clause membership
  | reorder proof permutation ih =>
    obtain ⟨literal, membership, holds⟩ := ih
    exact ⟨literal, permutation.mem_iff.mp membership, holds⟩
  | propagate literal tail clause unit clauseHolds unitHolds =>
    have negative : ¬LiteralHolds values literal := by
      have holds : LiteralHolds values (negate literal) := by
        simpa [ClauseHolds] using unitHolds
      exact (literalHolds_negate values literal).mp holds
    exact (clauseHolds_cons values literal tail).mp clauseHolds |>.resolve_left negative

theorem unit_conflict_unsatisfiable {formula : Formula α}
    (conflict : UnitDerived formula []) : Unsatisfiable formula := by
  rintro ⟨values, model⟩
  exact clauseHolds_nil values (unitDerived_sound conflict values model)

/-- The precise auxiliary-only formula in the accepted-inactivity UP test. -/
def inactiveFormula (pure : Formula α) (activities : ρ → Literal α) (accepted : List ρ) : Formula α :=
  pure ++ ofClauses (accepted.map fun i => [negate (activities i)])

/-- A checked empty UP row forces at least one accepted activity in every pure model. -/
theorem accepted_activity_forced_by_unit_conflict (pure : Formula α)
    (activities : ρ → Literal α) (accepted : List ρ)
    (conflict : UnitDerived (inactiveFormula pure activities accepted) [])
    (values : α → Bool) (model : Satisfies values pure) :
    ∃ i ∈ accepted, LiteralHolds values (activities i) := by
  apply accepted_activity_forced values pure activities {i | i ∈ accepted} model
  rintro ⟨assignment, satisfies, inactive⟩
  apply unit_conflict_unsatisfiable conflict
  refine ⟨assignment, (satisfies_append _ _ _).mpr ⟨satisfies, ?_⟩⟩
  apply (satisfies_ofClauses _ _).mpr
  intro clause rowMember
  obtain ⟨i, acceptedMember, rowEq⟩ := List.mem_map.mp rowMember
  subst clause
  have negative := (literalHolds_negate assignment (activities i)).mpr (inactive i acceptedMember)
  exact ⟨negate (activities i), by simp, negative⟩

/-- The manuscript's syntactic UP condition discharges necessity; uniform
orientation witnesses discharge sufficiency under the functional definitions. -/
theorem observation_projection_of_unit_conflict (definitions : Formula σ)
    (wrapper : Formula (Sum σ α)) (pure : Formula α)
    (pairs : ρ → Literal σ × Literal σ) (activities : ρ → Literal α) (accepted : List ρ)
    (pureCovered : ∀ signals values, Satisfies (joint signals values) wrapper → Satisfies values pure)
    (guards : ∀ signals values, Satisfies (joint signals values) wrapper →
      ∀ i, LiteralHolds values (activities i) → Discrepant signals (pairs i))
    (conflict : UnitDerived (inactiveFormula pure activities accepted) [])
    (uniform : ∀ i ∈ accepted, ∀ left right : Bool, left ≠ right →
      (¬∃ signals, Satisfies signals definitions ∧ literalValue signals (pairs i).1 = left ∧
        literalValue signals (pairs i).2 = right) ∨
      ∃ values, ∀ signals, Satisfies signals definitions → literalValue signals (pairs i).1 = left →
        literalValue signals (pairs i).2 = right → Satisfies (joint signals values) wrapper)
    (signals : σ → Bool) (model : Satisfies signals definitions) :
    (∃ values, Satisfies (joint signals values) wrapper) ↔ ∃ i ∈ accepted, Discrepant signals (pairs i) := by
  apply observation_projection (activities := activities) (accepted := {i | i ∈ accepted})
    (definitions := definitions) (wrapper := wrapper) (pairs := pairs) _ signals model
  exact ⟨guards,
    fun signals values satisfies => accepted_activity_forced_by_unit_conflict pure activities accepted conflict
      values (pureCovered signals values satisfies), uniform⟩

/-- A Horn implication has an optional positive head; no head is a constraint. -/
structure HornRule (α : Type*) where
  body : List α
  head : Option α

/-- True body variables require the positive head, or contradict a constraint. -/
def HornRule.Holds (values : α → Bool) (rule : HornRule α) : Prop :=
  (∀ a ∈ rule.body, values a = true) → ∃ a, rule.head = some a ∧ values a = true

def HornModel (rules : List (HornRule α)) (values : α → Bool) : Prop :=
  ∀ rule ∈ rules, rule.Holds values

/-- Closure contains exactly heads supported by finite Horn derivations. -/
inductive Forced (rules : List (HornRule α)) : α → Prop where
  | head (rule : HornRule α) (membership : rule ∈ rules) (a : α)
      (isHead : rule.head = some a) (premises : ∀ b ∈ rule.body, Forced rules b) : Forced rules a

/-- A constraint whose complete premise is forced makes the pure part inconsistent. -/
def NoHornConflict (rules : List (HornRule α)) : Prop :=
  ∀ rule ∈ rules, rule.head = none → ¬∀ a ∈ rule.body, Forced rules a

noncomputable def leastHornValues (rules : List (HornRule α)) : α → Bool := by
  classical
  exact fun a => decide (Forced rules a)

@[simp] theorem leastHornValues_true (rules : List (HornRule α)) (a : α) :
    leastHornValues rules a = true ↔ Forced rules a := by
  classical
  simp [leastHornValues]

theorem forced_in_every_horn_model {rules : List (HornRule α)} {a : α}
    (forced : Forced rules a) (values : α → Bool) (model : HornModel rules values) : values a = true := by
  induction forced with
  | head rule membership a isHead premises ih =>
    obtain ⟨b, head, active⟩ := model rule membership (fun b hb => ih b hb)
    have equal : b = a := Option.some.inj (head.symm.trans isHead)
    simpa [equal] using active

theorem horn_model_no_conflict {rules : List (HornRule α)} {values : α → Bool}
    (model : HornModel rules values) : NoHornConflict rules := by
  intro rule membership noHead premises
  obtain ⟨a, head, _⟩ := model rule membership
    (fun a ha => forced_in_every_horn_model (premises a ha) values model)
  rw [noHead] at head
  cases head

theorem leastHornValues_model {rules : List (HornRule α)} (consistent : NoHornConflict rules) :
    HornModel rules (leastHornValues rules) := by
  intro rule membership premises
  have forced : ∀ a ∈ rule.body, Forced rules a :=
    fun a ha => (leastHornValues_true rules a).mp (premises a ha)
  cases head : rule.head with
  | none => exact False.elim (consistent rule membership head forced)
  | some a => exact ⟨a, rfl, (leastHornValues_true rules a).mpr (.head rule membership a head forced)⟩

/-- Existence and forced coordinates establish minimality; a model alone does not. -/
theorem least_horn_closure (rules : List (HornRule α)) :
    (∃ values, HornModel rules values) ↔ NoHornConflict rules :=
  ⟨fun ⟨_, model⟩ => horn_model_no_conflict model,
    fun consistent => ⟨leastHornValues rules, leastHornValues_model consistent⟩⟩

/-- Signal attachments contain only negative private premises after orientation. -/
structure NegativeAttachment (σ α : Type*) where
  premises : List α
  signals : Clause σ

def NegativeAttachment.Holds (signals : σ → Bool) (values : α → Bool)
    (attachment : NegativeAttachment σ α) : Prop :=
  (∀ a ∈ attachment.premises, values a = true) → ClauseHolds signals attachment.signals

def NegativeHornWrapper (rules : List (HornRule α)) (attachments : List (NegativeAttachment σ α))
    (signals : σ → Bool) (values : α → Bool) : Prop :=
  HornModel rules values ∧ ∀ attachment ∈ attachments, attachment.Holds signals values

def ProjectedAttachments (rules : List (HornRule α)) (attachments : List (NegativeAttachment σ α))
    (signals : σ → Bool) : Prop :=
  ∀ attachment ∈ attachments, (∀ a ∈ attachment.premises, Forced rules a) →
    ClauseHolds signals attachment.signals

/-- The least private model is a simultaneous extension of every projected signal model. -/
theorem negative_horn_projection (rules : List (HornRule α))
    (attachments : List (NegativeAttachment σ α)) (signals : σ → Bool) :
    (∃ values, NegativeHornWrapper rules attachments signals values) ↔
      NoHornConflict rules ∧ ProjectedAttachments rules attachments signals := by
  constructor
  · rintro ⟨values, pure, attached⟩
    refine ⟨horn_model_no_conflict pure, ?_⟩
    intro attachment membership premises
    exact attached attachment membership
      (fun a ha => forced_in_every_horn_model (premises a ha) values pure)
  · rintro ⟨consistent, projected⟩
    refine ⟨leastHornValues rules, leastHornValues_model consistent, ?_⟩
    intro attachment membership premises
    exact projected attachment membership
      (fun a ha => (leastHornValues_true rules a).mp (premises a ha))

/-- One consistent auxiliary polarity changes coordinates but leaves signals fixed. -/
def auxiliaryPhase (phase : α → Bool) : Sum σ α → Bool
  | .inl _ => true
  | .inr a => phase a

theorem signed_private_projection (wrapper : Formula (Sum σ α)) (phase : α → Bool)
    (signals : σ → Bool) :
    (∃ values, Satisfies (joint signals values)
      (signedRelabel (Equiv.refl (Sum σ α)) (auxiliaryPhase phase) wrapper)) ↔
      ∃ values, Satisfies (joint signals values) wrapper := by
  constructor
  · rintro ⟨values, model⟩
    refine ⟨fun a => values a == phase a, ?_⟩
    have pullback := (satisfies_signedRelabel _ _ _ _).mp model
    have equal : signedPullback (Equiv.refl (Sum σ α)) (auxiliaryPhase phase)
        (joint signals values) = joint signals (fun a => values a == phase a) := by
      funext coordinate
      cases coordinate with
      | inl signal => simp [signedPullback, auxiliaryPhase, joint]
      | inr a => rfl
    simpa only [equal] using pullback
  · rintro ⟨values, model⟩
    refine ⟨fun a => values a == phase a, ?_⟩
    apply (satisfies_signedRelabel _ _ _ _).mpr
    have equal : signedPullback (Equiv.refl (Sum σ α)) (auxiliaryPhase phase)
        (joint signals (fun a => values a == phase a)) = joint signals values := by
      funext coordinate
      cases coordinate with
      | inl signal => simp [signedPullback, auxiliaryPhase, joint]
      | inr a =>
        change ((values a == phase a) == phase a) = values a
        cases values a <;> cases phase a <;> rfl
    simpa only [equal] using model

/-- Fresh requirement nodes are identified by their binary-tree position. -/
inductive RequirementTree (ρ : Type*) where
  | leaf (observation : ρ)
  | branch (left right : RequirementTree ρ)

def RequirementTree.leaves : RequirementTree ρ → List ρ
  | .leaf i => [i]
  | .branch left right => left.leaves ++ right.leaves

def RequirementTree.atPath (tree : RequirementTree ρ) : List Bool → Option (RequirementTree ρ)
  | [] => some tree
  | false :: rest => match tree with
    | .leaf _ => none
    | .branch left _ => left.atPath rest
  | true :: rest => match tree with
    | .leaf _ => none
    | .branch _ right => right.atPath rest

theorem RequirementTree.atPath_append (tree : RequirementTree ρ) (pathPrefix suffix : List Bool) :
    tree.atPath (pathPrefix ++ suffix) = (tree.atPath pathPrefix).bind (fun subtree => subtree.atPath suffix) := by
  induction pathPrefix generalizing tree with
  | nil => simp [RequirementTree.atPath]
  | cons side rest ih =>
    cases tree with
    | leaf i => cases side <;> rfl
    | branch left right => cases side <;> exact ih _

inductive PrivateActivity (ι ρ : Type*) where
  | internal (activity : ι)
  | observed (observation : ρ)
  | tree (path : List Bool)

def RequirementTree.root (tree : RequirementTree ρ) (path : List Bool) : PrivateActivity ι ρ :=
  match tree with
  | .leaf i => .observed i
  | .branch _ _ => .tree path

/-- The requirement clauses are implications from each parent to one of its children. -/
def RequirementTree.Holds (tree : RequirementTree ρ) (path : List Bool)
    (values : PrivateActivity ι ρ → Bool) : Prop :=
  match tree with
  | .leaf _ => True
  | .branch left right =>
      (values (.tree path) = true →
        values (left.root (path ++ [false])) = true ∨ values (right.root (path ++ [true])) = true) ∧
      left.Holds (path ++ [false]) values ∧ right.Holds (path ++ [true]) values
termination_by tree

/-- An active requirement root forces an active observed leaf. -/
theorem RequirementTree.active_leaf (tree : RequirementTree ρ) (path : List Bool)
    (values : PrivateActivity ι ρ → Bool) (model : tree.Holds path values)
    (active : values (tree.root path) = true) :
    ∃ i ∈ tree.leaves, values (.observed i) = true := by
  induction tree generalizing path with
  | leaf i => exact ⟨i, by simp [leaves], active⟩
  | branch left right ihLeft ihRight =>
    simp only [RequirementTree.Holds] at model
    simp only [RequirementTree.root] at active
    rcases model.1 active with leftActive | rightActive
    · obtain ⟨i, membership, active⟩ := ihLeft _ model.2.1 leftActive
      exact ⟨i, List.mem_append_left _ membership, active⟩
    · obtain ⟨i, membership, active⟩ := ihRight _ model.2.2 rightActive
      exact ⟨i, List.mem_append_right _ membership, active⟩

/-- Internal activities are disabled; only the chosen observed leaf and its tree path are active. -/
noncomputable def pathExtension (tree : RequirementTree ρ) (chosen : ρ) : PrivateActivity ι ρ → Bool := by
  classical
  exact fun activity => match activity with
    | .internal _ => false
    | .observed i => decide (i = chosen)
    | .tree path => decide (∃ subtree, tree.atPath path = some subtree ∧ chosen ∈ subtree.leaves)

/-- A subtree root is active exactly when it contains the selected leaf. -/
theorem pathExtension_root (whole subtree : RequirementTree ρ) (chosen : ρ) (path : List Bool)
    (located : whole.atPath path = some subtree) :
    pathExtension (ι := ι) whole chosen (subtree.root path) = true ↔ chosen ∈ subtree.leaves := by
  classical
  cases subtree with
  | leaf i => simp [pathExtension, RequirementTree.root, RequirementTree.leaves, eq_comm]
  | branch left right => simp [pathExtension, RequirementTree.root, located]

/-- The constant path extension satisfies every requirement clause. -/
theorem pathExtension_tree (whole subtree : RequirementTree ρ) (chosen : ρ) (path : List Bool)
    (located : whole.atPath path = some subtree) :
    subtree.Holds path (pathExtension (ι := ι) whole chosen) := by
  induction subtree generalizing path with
  | leaf i => simp [RequirementTree.Holds]
  | branch left right ihLeft ihRight =>
    simp only [RequirementTree.Holds]
    have leftLocated : whole.atPath (path ++ [false]) = some left := by
      rw [RequirementTree.atPath_append, located]
      simp [RequirementTree.atPath]
    have rightLocated : whole.atPath (path ++ [true]) = some right := by
      rw [RequirementTree.atPath_append, located]
      simp [RequirementTree.atPath]
    refine ⟨?_, ihLeft _ leftLocated, ihRight _ rightLocated⟩
    intro active
    have membership := (pathExtension_root whole (.branch left right) chosen path located).mp active
    rcases List.mem_append.mp membership with leftMember | rightMember
    · exact Or.inl ((pathExtension_root whole left chosen _ leftLocated).mpr leftMember)
    · exact Or.inr ((pathExtension_root whole right chosen _ rightLocated).mpr rightMember)

/-- An optional internal clause has a negative internal premise and only positive
private alternatives, followed by an arbitrary signal clause. -/
structure OptionalClause (σ ι ρ : Type*) where
  premise : ι
  alternatives : List (PrivateActivity ι ρ)
  signals : Clause σ

def OptionalClause.Holds (signals : σ → Bool) (values : PrivateActivity ι ρ → Bool)
    (clause : OptionalClause σ ι ρ) : Prop :=
  values (.internal clause.premise) = false ∨
    (∃ alternative ∈ clause.alternatives, values alternative = true) ∨ ClauseHolds signals clause.signals

/-- The exact optional grammar; all observed activities are the tree's distinct leaves. -/
structure OptionalWrapper (σ ι ρ : Type*) where
  tree : RequirementTree ρ
  distinctLeaves : tree.leaves.Nodup
  observedPairs : ρ → Literal σ × Literal σ
  internalPairs : ι → Literal σ × Literal σ
  clauses : List (OptionalClause σ ι ρ)

def OptionalWrapper.Holds (wrapper : OptionalWrapper σ ι ρ) (signals : σ → Bool)
    (values : PrivateActivity ι ρ → Bool) : Prop :=
  (∀ i, values (.internal i) = true → Discrepant signals (wrapper.internalPairs i)) ∧
  (∀ i ∈ wrapper.tree.leaves, values (.observed i) = true → Discrepant signals (wrapper.observedPairs i)) ∧
  (∀ clause ∈ wrapper.clauses, clause.Holds signals values) ∧
  wrapper.tree.Holds [] values ∧ values (wrapper.tree.root []) = true

/-- A chosen discrepant leaf gives a constant private extension, independent of every other signal. -/
theorem optional_constant_extension (wrapper : OptionalWrapper σ ι ρ) (chosen : ρ)
    (member : chosen ∈ wrapper.tree.leaves) (signals : σ → Bool)
    (difference : Discrepant signals (wrapper.observedPairs chosen)) :
    wrapper.Holds signals (pathExtension wrapper.tree chosen) := by
  classical
  refine ⟨?_, ?_, ?_, pathExtension_tree _ _ chosen [] (by simp [RequirementTree.atPath]),
    (pathExtension_root _ _ chosen [] (by simp [RequirementTree.atPath])).mpr member⟩
  · intro i active
    simp [pathExtension] at active
  · intro i _ active
    have equal : i = chosen := by simpa [pathExtension] using active
    simpa [equal] using difference
  · intro clause _
    exact Or.inl (by simp [pathExtension])

/-- Optional activities project to exactly the disjunction of observed discrepancies. -/
theorem optional_activity_projection (wrapper : OptionalWrapper σ ι ρ) (signals : σ → Bool) :
    (∃ values, wrapper.Holds signals values) ↔
      ∃ i ∈ wrapper.tree.leaves, Discrepant signals (wrapper.observedPairs i) := by
  constructor
  · rintro ⟨values, internal, observed, clauses, tree, root⟩
    obtain ⟨i, membership, active⟩ := wrapper.tree.active_leaf [] values tree root
    exact ⟨i, membership, observed i membership active⟩
  · rintro ⟨i, membership, difference⟩
    exact ⟨pathExtension wrapper.tree i, optional_constant_extension wrapper i membership signals difference⟩

/-- Selected observations retain the entire optional wrapper and append the selected disjunction. -/
def SelectedWrapper (wrapper : OptionalWrapper σ ι ρ) (selected : Set ρ)
    (signals : σ → Bool) (values : PrivateActivity ι ρ → Bool) : Prop :=
  wrapper.Holds signals values ∧ ∃ i ∈ selected, i ∈ wrapper.tree.leaves ∧ values (.observed i) = true

theorem selected_activity_projection (wrapper : OptionalWrapper σ ι ρ) (selected : Set ρ)
    (signals : σ → Bool) :
    (∃ values, SelectedWrapper wrapper selected signals values) ↔
      ∃ i ∈ selected, i ∈ wrapper.tree.leaves ∧ Discrepant signals (wrapper.observedPairs i) := by
  constructor
  · rintro ⟨values, model, i, membership, leaf, active⟩
    exact ⟨i, membership, leaf, model.2.1 i leaf active⟩
  · rintro ⟨i, membership, leaf, difference⟩
    refine ⟨pathExtension wrapper.tree i, optional_constant_extension wrapper i leaf signals difference,
      i, membership, leaf, ?_⟩
    classical
    simp [pathExtension]



/-- Horn rows retain every premise occurrence and their optional positive head. -/
def HornRule.clause (rule : HornRule α) : Clause (Sum σ α) :=
  rule.body.map (fun a => (Sum.inr a, false)) ++
    (rule.head.toList.map (fun a => (Sum.inr a, true)))

def NegativeAttachment.clause (attachment : NegativeAttachment σ α) : Clause (Sum σ α) :=
  attachment.premises.map (fun a => (Sum.inr a, false)) ++
    attachment.signals.map (fun literal => (Sum.inl literal.1, literal.2))

/-- Embedding a signal clause changes its variable tag, not its truth value. -/
theorem signal_clause_embed (clause : Clause σ) (signals : σ → Bool) (values : α → Bool) :
    ClauseHolds (joint signals values) (clause.map fun literal => (Sum.inl literal.1, literal.2)) ↔
      ClauseHolds signals clause := by
  constructor
  · rintro ⟨literal, membership, holds⟩
    obtain ⟨source, sourceMember, rowEq⟩ := List.mem_map.mp membership
    subst literal
    exact ⟨source, sourceMember, holds⟩
  · rintro ⟨literal, membership, holds⟩
    exact ⟨(Sum.inl literal.1, literal.2), List.mem_map.mpr ⟨literal, membership, rfl⟩, holds⟩

theorem auxiliary_clause_embed (labels : List α) (sign : Bool) (signals : σ → Bool) (values : α → Bool) :
    ClauseHolds (joint signals values) (labels.map fun a => (Sum.inr a, sign)) ↔
      ∃ a ∈ labels, values a = sign := by
  constructor
  · rintro ⟨literal, membership, holds⟩
    obtain ⟨a, labelMember, rowEq⟩ := List.mem_map.mp membership
    subst literal
    exact ⟨a, labelMember, holds⟩
  · rintro ⟨a, membership, holds⟩
    exact ⟨(Sum.inr a, sign), List.mem_map.mpr ⟨a, membership, rfl⟩, holds⟩

theorem negative_premises_iff (labels : List α) (values : α → Bool) :
    (∃ a ∈ labels, values a = false) ↔ ¬∀ a ∈ labels, values a = true := by
  classical
  constructor
  · rintro ⟨a, membership, inactive⟩ allActive
    exact Bool.false_ne_true (inactive.symm.trans (allActive a membership))
  · intro notAll
    by_contra missing
    apply notAll
    intro a member
    apply Bool.eq_true_of_not_eq_false
    intro inactive
    exact missing ⟨a, member, inactive⟩

theorem negative_or_iff_imp (premise conclusion : Prop) :
    (¬premise ∨ conclusion) ↔ (premise → conclusion) := by
  classical
  constructor
  · rintro (missing | holds) active
    · exact False.elim (missing active)
    · exact holds
  · intro implication
    by_cases active : premise
    · exact Or.inr (implication active)
    · exact Or.inl active

theorem horn_rule_clause (rule : HornRule α) (signals : σ → Bool) (values : α → Bool) :
    ClauseHolds (joint signals values) rule.clause ↔ rule.Holds values := by
  classical
  rw [HornRule.clause, clauseHolds_append, auxiliary_clause_embed, negative_premises_iff]
  cases head : rule.head with
  | none => simp [head, HornRule.Holds]
  | some a =>
    simp only [head, Option.toList_some, auxiliary_clause_embed, List.mem_singleton,
      exists_eq_left, HornRule.Holds, Option.some.injEq]
    refine (negative_or_iff_imp _ _).trans ?_
    constructor
    · intro implication premises
      exact ⟨a, rfl, implication premises⟩
    · intro implication premises
      obtain ⟨b, equal, active⟩ := implication premises
      simpa only [← equal] using active

theorem negative_attachment_clause (attachment : NegativeAttachment σ α)
    (signals : σ → Bool) (values : α → Bool) :
    ClauseHolds (joint signals values) attachment.clause ↔ attachment.Holds signals values := by
  classical
  rw [NegativeAttachment.clause, clauseHolds_append, auxiliary_clause_embed,
    negative_premises_iff, signal_clause_embed]
  exact negative_or_iff_imp _ _

def negativeHornFormula (rules : List (HornRule α))
    (attachments : List (NegativeAttachment σ α)) : Formula (Sum σ α) :=
  ofClauses (rules.map HornRule.clause ++ attachments.map NegativeAttachment.clause)

theorem negativeHornFormula_iff (rules : List (HornRule α))
    (attachments : List (NegativeAttachment σ α)) (signals : σ → Bool) (values : α → Bool) :
    Satisfies (joint signals values) (negativeHornFormula rules attachments) ↔
      NegativeHornWrapper rules attachments signals values := by
  simp only [negativeHornFormula, satisfies_ofClauses, List.forall_mem_append, List.forall_mem_map,
    horn_rule_clause, negative_attachment_clause, NegativeHornWrapper, HornModel]

theorem negative_horn_cnf_projection (rules : List (HornRule α))
    (attachments : List (NegativeAttachment σ α)) (signals : σ → Bool) :
    (∃ values, Satisfies (joint signals values) (negativeHornFormula rules attachments)) ↔
      NoHornConflict rules ∧ ProjectedAttachments rules attachments signals := by
  simp only [negativeHornFormula_iff]
  exact negative_horn_projection rules attachments signals

/-- The two source discrepancy clauses encode activity implies signed signal XOR. -/
def guardRows (activity : α) (pair : Literal σ × Literal σ) : List (Clause (Sum σ α)) :=
  [[(Sum.inr activity, false), (Sum.inl pair.1.1, pair.1.2), (Sum.inl pair.2.1, pair.2.2)],
   [(Sum.inr activity, false), (Sum.inl pair.1.1, !pair.1.2), (Sum.inl pair.2.1, !pair.2.2)]]

theorem guardRows_iff (activity : α) (pair : Literal σ × Literal σ)
    (signals : σ → Bool) (values : α → Bool) :
    Satisfies (joint signals values) (ofClauses (guardRows activity pair)) ↔
      (values activity = true → Discrepant signals pair) := by
  rcases pair with ⟨⟨left, leftSign⟩, ⟨right, rightSign⟩⟩
  simp only [guardRows, satisfies_ofClauses, List.forall_mem_cons, clauseHolds_cons, clauseHolds_nil, or_false]
  cases leftSign <;> cases rightSign <;> cases hl : signals left <;> cases hr : signals right <;>
    cases ha : values activity <;>
    simp [LiteralHolds, joint, Discrepant, literalValue, hl, hr, ha]

/-- Parent and children are private positive activity literals. -/
def requirementRow (parent left right : α) : Clause (Sum σ α) :=
  [(Sum.inr parent, false), (Sum.inr left, true), (Sum.inr right, true)]

theorem requirementRow_iff (parent left right : α) (signals : σ → Bool) (values : α → Bool) :
    ClauseHolds (joint signals values) (requirementRow parent left right) ↔
      (values parent = true → values left = true ∨ values right = true) := by
  simp only [requirementRow, clauseHolds_cons, clauseHolds_nil, or_false]
  cases hp : values parent <;> cases hl : values left <;> cases hr : values right <;>
    simp [LiteralHolds, joint, hp, hl, hr]

def RequirementTree.rows (tree : RequirementTree ρ) (path : List Bool) :
    List (Clause (Sum σ (PrivateActivity ι ρ))) :=
  match tree with
  | .leaf _ => []
  | .branch left right =>
      requirementRow (.tree path) (left.root (path ++ [false])) (right.root (path ++ [true])) ::
        left.rows (path ++ [false]) ++ right.rows (path ++ [true])

theorem requirementTree_rows_iff (tree : RequirementTree ρ) (path : List Bool)
    (signals : σ → Bool) (values : PrivateActivity ι ρ → Bool) :
    Satisfies (joint signals values) (ofClauses (tree.rows path)) ↔ tree.Holds path values := by
  induction tree generalizing path with
  | leaf i => simp [RequirementTree.rows, RequirementTree.Holds, satisfies_ofClauses]
  | branch left right ihLeft ihRight =>
    simp only [RequirementTree.rows, satisfies_ofClauses, List.forall_mem_cons, List.forall_mem_append,
      requirementRow_iff, RequirementTree.Holds]
    rw [and_assoc]
    exact and_congr Iff.rfl (and_congr (by simpa only [satisfies_ofClauses] using ihLeft (path ++ [false]))
      (by simpa only [satisfies_ofClauses] using ihRight (path ++ [true])))

def OptionalClause.clause (clause : OptionalClause σ ι ρ) : Clause (Sum σ (PrivateActivity ι ρ)) :=
  (Sum.inr (.internal clause.premise), false) ::
    (clause.alternatives.map (fun alternative => (Sum.inr alternative, true)) ++
      clause.signals.map (fun literal => (Sum.inl literal.1, literal.2)))

theorem optionalClause_clause_iff (clause : OptionalClause σ ι ρ)
    (signals : σ → Bool) (values : PrivateActivity ι ρ → Bool) :
    ClauseHolds (joint signals values) clause.clause ↔ clause.Holds signals values := by
  simp only [OptionalClause.clause, clauseHolds_cons, clauseHolds_append,
    auxiliary_clause_embed, signal_clause_embed, OptionalClause.Holds]
  rfl

/-- The optional CNF consists exactly of discrepancy guards, optional internal
clauses, requirement-tree implications and the positive requirement-root unit. -/
noncomputable def OptionalWrapper.formula [Fintype ι] (wrapper : OptionalWrapper σ ι ρ) :
    Formula (Sum σ (PrivateActivity ι ρ)) := by
  classical
  exact ofClauses ((Finset.univ.toList.flatMap fun i => guardRows (.internal i) (wrapper.internalPairs i)) ++
    (wrapper.tree.leaves.flatMap fun i => guardRows (.observed i) (wrapper.observedPairs i)) ++
    wrapper.clauses.map OptionalClause.clause ++ wrapper.tree.rows [] ++
    [[(Sum.inr (wrapper.tree.root []), true)]])

theorem optionalWrapper_formula_iff [Fintype ι] (wrapper : OptionalWrapper σ ι ρ)
    (signals : σ → Bool) (values : PrivateActivity ι ρ → Bool) :
    Satisfies (joint signals values) wrapper.formula ↔ wrapper.Holds signals values := by
  classical
  simp only [OptionalWrapper.formula, satisfies_ofClauses, List.forall_mem_append,
    List.forall_mem_flatMap, List.forall_mem_map]
  have guards : ∀ activity pair,
      (∀ row ∈ guardRows activity pair, ClauseHolds (joint signals values) row) ↔
      (values activity = true → Discrepant signals pair) := by
    intro activity pair
    simpa only [satisfies_ofClauses] using guardRows_iff activity pair signals values
  have treeRows : (∀ row ∈ wrapper.tree.rows [], ClauseHolds (joint signals values) row) ↔
      wrapper.tree.Holds [] values := by
    simpa only [satisfies_ofClauses] using requirementTree_rows_iff wrapper.tree [] signals values
  simp only [guards, optionalClause_clause_iff, treeRows, OptionalWrapper.Holds,
    Finset.mem_toList, Finset.mem_univ, forall_true_left, List.forall_mem_cons, clauseHolds_cons, clauseHolds_nil, or_false, and_assoc]
  simp [LiteralHolds, joint]

theorem optional_activity_cnf_projection [Fintype ι] (wrapper : OptionalWrapper σ ι ρ)
    (signals : σ → Bool) :
    (∃ values, Satisfies (joint signals values) wrapper.formula) ↔
      ∃ i ∈ wrapper.tree.leaves, Discrepant signals (wrapper.observedPairs i) := by
  simp only [optionalWrapper_formula_iff]
  exact optional_activity_projection wrapper signals

/-- Selected CNFs append one positive activity disjunction and retain all optional rows. -/
noncomputable def selectedFormula [Fintype ι] (wrapper : OptionalWrapper σ ι ρ) (selected : List ρ) :
    Formula (Sum σ (PrivateActivity ι ρ)) :=
  wrapper.formula ++ ofClauses [selected.map (fun i => (Sum.inr (.observed i), true))]

theorem selected_activity_cnf_projection [Fintype ι] (wrapper : OptionalWrapper σ ι ρ)
    (selected : List ρ) (allLeaves : ∀ i ∈ selected, i ∈ wrapper.tree.leaves) (signals : σ → Bool) :
    (∃ values, Satisfies (joint signals values) (selectedFormula wrapper selected)) ↔
      ∃ i ∈ selected, Discrepant signals (wrapper.observedPairs i) := by
  have selectedModel : ∀ values,
      Satisfies (joint signals values) (selectedFormula wrapper selected) ↔
      SelectedWrapper wrapper {i | i ∈ selected} signals values := by
    intro values
    rw [selectedFormula, satisfies_append, optionalWrapper_formula_iff]
    have chosen : Satisfies (joint signals values)
        (ofClauses [selected.map (fun i => (Sum.inr (.observed i), true))]) ↔
        ∃ i ∈ selected, values (.observed i) = true := by
      rw [satisfies_ofClauses]
      simp only [List.forall_mem_singleton]
      constructor
      · rintro ⟨literal, rowMember, active⟩
        obtain ⟨i, selectedMember, rowEq⟩ := List.mem_map.mp rowMember
        subst literal
        exact ⟨i, selectedMember, active⟩
      · rintro ⟨i, selectedMember, active⟩
        exact ⟨(Sum.inr (.observed i), true), List.mem_map.mpr ⟨i, selectedMember, rfl⟩, active⟩

    rw [chosen]
    constructor
    · rintro ⟨model, i, membership, active⟩
      exact ⟨model, i, membership, allLeaves i membership, active⟩
    · rintro ⟨model, i, membership, _, active⟩
      exact ⟨model, i, membership, active⟩
  simp only [selectedModel, selected_activity_projection, Set.mem_setOf_eq]
  constructor
  · rintro ⟨i, membership, _, difference⟩
    exact ⟨i, membership, difference⟩
  · rintro ⟨i, membership, difference⟩
    exact ⟨i, membership, allLeaves i membership, difference⟩



/-- Only auxiliary coordinates occurring in the finite CNF are allocated by this support schema. -/
noncomputable def formulaAuxiliarySupport (formula : Formula (Sum σ α)) : Finset α := by
  classical
  exact (formula.clauses.toList.flatMap fun clause => clause.flatMap fun literal =>
    match literal.1 with
    | .inl _ => []
    | .inr a => [a]).toFinset

theorem auxiliary_mem_support {formula : Formula (Sum σ α)} {clause : Clause (Sum σ α)}
    {a : α} {sign : Bool} (row : clause ∈ formula.clauses) (literal : (Sum.inr a, sign) ∈ clause) :
    a ∈ formulaAuxiliarySupport formula := by
  classical
  apply List.mem_toFinset.mpr
  apply List.mem_flatMap.mpr
  refine ⟨clause, ?_, ?_⟩
  · simpa using row
  · apply List.mem_flatMap.mpr
    exact ⟨(Sum.inr a, sign), literal, by simp⟩

/-- Restriction to actual finite support; unused ambient tree paths have no allocated role. -/
noncomputable def finiteAuxiliaryExtension (formula : Formula (Sum σ α))
    (values : {a // a ∈ formulaAuxiliarySupport formula} → Bool) : α → Bool := by
  classical
  exact fun a => if membership : a ∈ formulaAuxiliarySupport formula then values ⟨a, membership⟩ else false

theorem satisfies_auxiliary_restriction (formula : Formula (Sum σ α))
    (signals : σ → Bool) (values : α → Bool) :
    Satisfies (joint signals (finiteAuxiliaryExtension formula (fun a => values a.val))) formula ↔
      Satisfies (joint signals values) formula := by
  classical
  have agrees : ∀ clause ∈ formula.clauses, ∀ literal ∈ clause,
      joint signals (finiteAuxiliaryExtension formula (fun a => values a.val)) literal.1 =
        joint signals values literal.1 := by
    intro clause row literal membership
    rcases literal with ⟨coordinate, sign⟩
    cases coordinate with
    | inl signal => rfl
    | inr a =>
      have support : a ∈ formulaAuxiliarySupport formula := auxiliary_mem_support row membership
      simp [joint, finiteAuxiliaryExtension, support]

  constructor
  · intro model clause row
    obtain ⟨literal, membership, holds⟩ := model clause row
    exact ⟨literal, membership, (agrees clause row literal membership).symm.trans holds⟩
  · intro model clause row
    obtain ⟨literal, membership, holds⟩ := model clause row
    exact ⟨literal, membership, (agrees clause row literal membership).trans holds⟩

/-- Ambient private assignments and assignments to the actual finite clause support
have identical existential projections; no counting claim is involved. -/
theorem finite_auxiliary_projection (formula : Formula (Sum σ α)) (signals : σ → Bool) :
    (∃ values : {a // a ∈ formulaAuxiliarySupport formula} → Bool,
      Satisfies (joint signals (finiteAuxiliaryExtension formula values)) formula) ↔
      ∃ values : α → Bool, Satisfies (joint signals values) formula := by
  constructor
  · rintro ⟨values, model⟩
    exact ⟨finiteAuxiliaryExtension formula values, model⟩
  · rintro ⟨values, model⟩
    exact ⟨fun a => values a.val, (satisfies_auxiliary_restriction formula signals values).mpr model⟩

/-- Auxiliary-only source clauses embed into the tagged wrapper without changing their truth. -/
theorem pure_auxiliary_embedding (pure : Formula α) (rest : Formula (Sum σ α))
    (signals : σ → Bool) (values : α → Bool)
    (model : Satisfies (joint signals values) (relabel Sum.inr pure ++ rest)) :
    Satisfies values pure := by
  have pureModel := (satisfies_append _ _ _).mp model |>.1
  exact (satisfies_relabel Sum.inr (joint signals values) pure).mp pureModel



/-- Enumerate precisely the fresh branch positions, not all ambient binary paths. -/
def RequirementTree.branchPositions (tree : RequirementTree ρ) (path : List Bool) : List (List Bool) :=
  match tree with
  | .leaf _ => []
  | .branch left right => path ::
      left.branchPositions (path ++ [false]) ++ right.branchPositions (path ++ [true])

/-- The finite declared partition comprises internal activities, observed leaves,
and actual fresh requirement-tree branch positions. -/
noncomputable def OptionalWrapper.declaredAuxiliaries [Fintype ι] (wrapper : OptionalWrapper σ ι ρ) :
    Finset (PrivateActivity ι ρ) := by
  classical
  exact ((Finset.univ.toList.map PrivateActivity.internal) ++
    wrapper.tree.leaves.map PrivateActivity.observed ++
    (wrapper.tree.branchPositions []).map PrivateActivity.tree).toFinset

/-- Declaration validity forbids extra observed activities or non-tree positions
in positive alternatives. It does not require any internal activity to be true. -/
def OptionalWrapper.DeclaredPrivate [Fintype ι] (wrapper : OptionalWrapper σ ι ρ) : Prop :=
  formulaAuxiliarySupport wrapper.formula ⊆ wrapper.declaredAuxiliaries

/-- Extend a finite declared auxiliary assignment; off-support ambient values are irrelevant. -/
noncomputable def extendDeclaredAuxiliaries (support : Finset α)
    (values : {a // a ∈ support} → Bool) : α → Bool := by
  classical
  exact fun a => if membership : a ∈ support then values ⟨a, membership⟩ else false

theorem finite_declared_projection (formula : Formula (Sum σ α)) (support : Finset α)
    (covers : formulaAuxiliarySupport formula ⊆ support) (signals : σ → Bool) :
    (∃ values : {a // a ∈ support} → Bool,
      Satisfies (joint signals (extendDeclaredAuxiliaries support values)) formula) ↔
      ∃ values : α → Bool, Satisfies (joint signals values) formula := by
  classical
  constructor
  · rintro ⟨values, model⟩
    exact ⟨extendDeclaredAuxiliaries support values, model⟩
  · rintro ⟨values, model⟩
    refine ⟨fun a => values a.val, ?_⟩
    intro clause row
    obtain ⟨literal, membership, holds⟩ := model clause row
    refine ⟨literal, membership, ?_⟩
    rcases literal with ⟨coordinate, sign⟩
    cases coordinate with
    | inl signal => exact holds
    | inr a =>
      have declared : a ∈ support := covers (auxiliary_mem_support row membership)
      simpa [LiteralHolds, joint, extendDeclaredAuxiliaries, declared] using holds

/-- Exact optional grammar projection over its finite declared private variables. -/
theorem optional_declared_cnf_projection [Fintype ι] (wrapper : OptionalWrapper σ ι ρ)
    (valid : wrapper.DeclaredPrivate) (signals : σ → Bool) :
    (∃ values : {a // a ∈ wrapper.declaredAuxiliaries} → Bool,
      Satisfies (joint signals (extendDeclaredAuxiliaries wrapper.declaredAuxiliaries values)) wrapper.formula) ↔
      ∃ i ∈ wrapper.tree.leaves, Discrepant signals (wrapper.observedPairs i) :=
  (finite_declared_projection wrapper.formula wrapper.declaredAuxiliaries valid signals).trans
    (optional_activity_cnf_projection wrapper signals)

/-- Appending a selected clause mentions only declared observed leaves. -/
theorem selected_declared_support [Fintype ι] (wrapper : OptionalWrapper σ ι ρ)
    (valid : wrapper.DeclaredPrivate) (selected : List ρ)
    (allLeaves : ∀ i ∈ selected, i ∈ wrapper.tree.leaves) :
    formulaAuxiliarySupport (selectedFormula wrapper selected) ⊆ wrapper.declaredAuxiliaries := by
  classical
  intro a membership
  have occurrence : ∃ clause ∈ (selectedFormula wrapper selected).clauses,
      ∃ sign, (Sum.inr a, sign) ∈ clause := by
    have raw := List.mem_toFinset.mp membership
    obtain ⟨clause, row, literalOccurrence⟩ := List.mem_flatMap.mp raw
    obtain ⟨literal, lit, auxiliary⟩ := List.mem_flatMap.mp literalOccurrence
    rcases literal with ⟨coordinate, sign⟩
    cases coordinate with
    | inl signal => simp at auxiliary
    | inr source =>
      have equal : a = source := by simpa using auxiliary
      subst source
      exact ⟨clause, by simpa using row, sign, lit⟩
  obtain ⟨clause, row, sign, lit⟩ := occurrence
  have rowCases : clause ∈ wrapper.formula.clauses ∨
      clause ∈ (ofClauses [selected.map (fun i => (Sum.inr (.observed i), true))]).clauses := by
    simpa only [selectedFormula, Controller.CNF.OrderedFormula.Internal.clauses_append, Array.mem_append] using row
  rcases rowCases with original | chosen
  · exact valid (auxiliary_mem_support original lit)
  · have clauseEq : clause = selected.map (fun i => (Sum.inr (.observed i), true)) := by
      simpa [ofClauses] using chosen
    rw [clauseEq] at lit
    obtain ⟨i, selectedMember, equality⟩ := List.mem_map.mp lit
    have auxiliaryEq : a = PrivateActivity.observed i := by
      exact (Sum.inr.inj (congrArg Prod.fst equality)).symm
    rw [auxiliaryEq]
    apply List.mem_toFinset.mpr
    apply List.mem_append.mpr
    exact Or.inl (List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨i, allLeaves i selectedMember, rfl⟩)))

/-- Selected projection also uses only the same finite declared private partition. -/
theorem selected_declared_cnf_projection [Fintype ι] (wrapper : OptionalWrapper σ ι ρ)
    (valid : wrapper.DeclaredPrivate) (selected : List ρ)
    (allLeaves : ∀ i ∈ selected, i ∈ wrapper.tree.leaves) (signals : σ → Bool) :
    (∃ values : {a // a ∈ wrapper.declaredAuxiliaries} → Bool,
      Satisfies (joint signals (extendDeclaredAuxiliaries wrapper.declaredAuxiliaries values))
        (selectedFormula wrapper selected)) ↔
      ∃ i ∈ selected, Discrepant signals (wrapper.observedPairs i) :=
  (finite_declared_projection (selectedFormula wrapper selected) wrapper.declaredAuxiliaries
    (selected_declared_support wrapper valid selected allLeaves) signals).trans
    (selected_activity_cnf_projection wrapper selected allLeaves signals)

end Controller.Native.ObservationProjection
