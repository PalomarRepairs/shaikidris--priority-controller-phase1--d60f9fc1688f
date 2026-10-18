module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Decoder.PartialTruth
public import Controller.Basic.Admissible
public import Controller.Horn.GreatestModel

@[expose] public section

/-!
# Zero-witness activity clauses

Channel variables and node activities have separate finite namespaces. Input
activities are equated with their channel values; internal clauses propagate
truth only in the forward direction. The queried activity is forced false.
-/

namespace Controller.Decoder.ZeroSystem

open CNF

/-- A positive clause retains every listed variable incidence. -/
def positiveClause (entries : List α) : Clause α := entries.map (fun v => (v, true))

/-- A single negative premise followed by positive alternatives. -/
def implicationClause (premise : α) (alternatives : List α) : Clause α :=
  (premise, false) :: positiveClause alternatives

@[simp] theorem positiveClause_holds (a : α → Bool) (entries : List α) :
    ClauseHolds a (positiveClause entries) ↔ ∃ v ∈ entries, a v = true := by
  simp [positiveClause, ClauseHolds, LiteralHolds]

@[simp] theorem implicationClause_holds (a : α → Bool) (premise : α)
    (alternatives : List α) :
    ClauseHolds a (implicationClause premise alternatives) ↔
      (a premise = true → ∃ v ∈ alternatives, a v = true) := by
  cases premiseValue : a premise <;>
    simp [implicationClause, LiteralHolds, premiseValue]

theorem positiveClause_dualHorn (entries : List α) :
    Horn.DualHornClause (positiveClause entries) := by
  apply Horn.dualHornClause_positive
  intro literal membership
  obtain ⟨v, _, rfl⟩ := List.mem_map.mp membership
  rfl

theorem implicationClause_dualHorn (premise : α) (alternatives : List α) :
    Horn.DualHornClause (implicationClause premise alternatives) := by
  right
  intro left leftMember right rightMember leftNegative rightNegative
  have negative_unique : ∀ literal ∈ implicationClause premise alternatives,
      literal.2 = false → literal.1 = premise := by
    intro literal membership negative
    rcases List.mem_cons.mp membership with rfl | positive
    · rfl
    · obtain ⟨v, _, literalEquation⟩ := List.mem_map.mp positive
      subst literal
      cases negative
  exact (negative_unique left leftMember leftNegative).trans
    (negative_unique right rightMember rightNegative).symm

end Controller.Decoder.ZeroSystem

namespace Controller.Decoder.DAG

open CNF ZeroSystem

variable {n : ℕ}

/-- Separate namespaces for declared channels and all represented node activities. -/
abbrev ZeroVar (graph : DAG n) := Channel n ⊕ Fin graph.nodeCount

/-- Combine fixed channel values with an arbitrary internal-activity assignment. -/
def zeroAssignment (graph : DAG n) (channels : Assignment n)
    (activities : Fin graph.nodeCount → Bool) : graph.ZeroVar → Bool :=
  Sum.elim channels activities

/-- Forward activity rows belonging to one stored node. -/
def nodeClauses (graph : DAG n) (index : Fin graph.nodeCount) : List (Clause graph.ZeroVar) :=
  match graph.node index with
  | .zero => [implicationClause (.inr index) []]
  | .input channel =>
      [implicationClause (.inl channel) [.inr index],
        implicationClause (.inr index) [.inl channel]]
  | .disj refs => refs.map fun child =>
      implicationClause (.inr (graph.childIndex index child)) [.inr index]
  | .guard child labels =>
      [implicationClause (.inr (graph.childIndex index child))
        (labels.map Sum.inl ++ [.inr index])]
  | .liveAnd left right =>
      [[(.inr (graph.childIndex index left), false),
        (.inr (graph.childIndex index right), false), (.inr index, true)]]

/-- Node rows in topological order, preserving every input incidence. -/
def forwardClauses (graph : DAG n) : List (Clause graph.ZeroVar) :=
  (List.finRange graph.nodeCount).flatMap graph.nodeClauses

/-- Every local activity row is satisfied. -/
def ForwardModel (graph : DAG n) (channels : Assignment n)
    (activities : Fin graph.nodeCount → Bool) : Prop :=
  ∀ index, ∀ clause ∈ graph.nodeClauses index,
    ClauseHolds (graph.zeroAssignment channels activities) clause

theorem forwardClauses_holds_iff (graph : DAG n) (channels : Assignment n)
    (activities : Fin graph.nodeCount → Bool) :
    (∀ clause ∈ graph.forwardClauses,
      ClauseHolds (graph.zeroAssignment channels activities) clause) ↔
      graph.ForwardModel channels activities := by
  constructor
  · intro satisfied index clause membership
    exact satisfied clause (List.mem_flatMap.mpr
      ⟨index, List.mem_finRange index, membership⟩)
  · intro satisfied clause membership
    obtain ⟨index, _, localMembership⟩ := List.mem_flatMap.mp membership
    exact satisfied index clause localMembership

/-- The two input rows identify a leaf activity with its channel in every model. -/
theorem input_activity_eq_channel (graph : DAG n) (channels : Assignment n)
    (activities : Fin graph.nodeCount → Bool) (forward : graph.ForwardModel channels activities)
    (index : Fin graph.nodeCount) (channel : Channel n)
    (gateEquation : graph.node index = .input channel) :
    activities index = channels channel := by
  have forwardRow := forward index (implicationClause (.inl channel) [.inr index])
    (by simp [nodeClauses, gateEquation])
  have reverseRow := forward index (implicationClause (.inr index) [.inl channel])
    (by simp [nodeClauses, gateEquation])
  have forwardTrue := (implicationClause_holds _ _ _).mp forwardRow
  have reverseTrue := (implicationClause_holds _ _ _).mp reverseRow
  cases channelValue : channels channel <;> cases activityValue : activities index <;>
    simp_all [zeroAssignment]

/-- The exact semantic values satisfy every forward row in a guarded graph. -/
theorem exact_forwardModel (graph : DAG n) (guarded : graph.Guarded)
    (channels : Assignment n) : graph.ForwardModel channels (graph.eval channels) := by
  intro index clause membership
  cases gateEquation : graph.node index with
  | zero =>
      have clauseEquation : clause = implicationClause (.inr index) [] := by
        simpa [nodeClauses, gateEquation] using membership
      subst clause
      rw [implicationClause_holds]
      simp [zeroAssignment, graph.eval_zero channels index gateEquation]
  | input channel =>
      have inputValue := graph.eval_input channels index channel gateEquation
      simp only [nodeClauses, gateEquation, List.mem_cons, List.not_mem_nil, or_false] at membership
      rcases membership with rfl | rfl <;>
        rw [implicationClause_holds] <;> simp [zeroAssignment, inputValue]
  | disj refs =>
      obtain ⟨child, childMember, rfl⟩ : ∃ child ∈ refs,
          implicationClause (.inr (graph.childIndex index child)) [.inr index] = clause := by
        simpa only [nodeClauses, gateEquation, List.mem_map] using membership
      apply (implicationClause_holds _ _ _).mpr
      intro childTrue
      refine ⟨.inr index, by simp, ?_⟩
      change graph.eval channels index = true
      rw [graph.eval_disj channels index refs gateEquation]
      exact List.any_eq_true.mpr ⟨child, childMember, childTrue⟩
  | guard child labels =>
      have clauseEquation : clause = implicationClause
          (.inr (graph.childIndex index child)) (labels.map Sum.inl ++ [.inr index]) := by
        simpa [nodeClauses, gateEquation] using membership
      subst clause
      apply (implicationClause_holds _ _ _).mpr
      intro childTrue
      by_cases guardTrue : labels.any channels = true
      · obtain ⟨channel, channelMember, channelTrue⟩ := List.any_eq_true.mp guardTrue
        exact ⟨.inl channel, List.mem_append_left _ (List.mem_map.mpr
          ⟨channel, channelMember, rfl⟩), channelTrue⟩
      · refine ⟨.inr index, by simp, ?_⟩
        change graph.eval channels index = true
        rw [graph.eval_guard channels index child labels gateEquation]
        have guardFalse : labels.any channels = false := Bool.eq_false_of_not_eq_true guardTrue
        simp [show graph.eval channels (graph.childIndex index child) = true from childTrue,
          guardFalse]
  | liveAnd left right =>
      have guardCondition := guarded index
      simp [Gate.IsGuarded, gateEquation, Gate.isLiveAnd] at guardCondition

/-- Each row of a guarded node has at most one distinct negative variable. -/
theorem nodeClauses_dualHorn (graph : DAG n) (guarded : graph.Guarded)
    (index : Fin graph.nodeCount) (clause : Clause graph.ZeroVar)
    (membership : clause ∈ graph.nodeClauses index) : Horn.DualHornClause clause := by
  cases gateEquation : graph.node index with
  | zero =>
      have : clause = implicationClause (.inr index) [] := by
        simpa [nodeClauses, gateEquation] using membership
      subst clause
      exact implicationClause_dualHorn _ _
  | input channel =>
      simp only [nodeClauses, gateEquation, List.mem_cons, List.not_mem_nil, or_false] at membership
      rcases membership with rfl | rfl <;> exact implicationClause_dualHorn _ _
  | disj refs =>
      obtain ⟨child, _, rfl⟩ : ∃ child ∈ refs,
          implicationClause (.inr (graph.childIndex index child)) [.inr index] = clause := by
        simpa only [nodeClauses, gateEquation, List.mem_map] using membership
      exact implicationClause_dualHorn _ _
  | guard child labels =>
      have : clause = implicationClause (.inr (graph.childIndex index child))
          (labels.map Sum.inl ++ [.inr index]) := by
        simpa [nodeClauses, gateEquation] using membership
      subst clause
      exact implicationClause_dualHorn _ _
  | liveAnd left right =>
      have guardCondition := guarded index
      simp [Gate.IsGuarded, gateEquation, Gate.isLiveAnd] at guardCondition

end Controller.Decoder.DAG

namespace Controller.Decoder.LivePath

open CNF ZeroSystem

variable {n : ℕ} {graph : DAG n} {index : Fin graph.nodeCount}
variable {head : Channel n} {blocked : Finset (Channel n)}

/-- A successful live path forces the queried activity in every forward model. -/
theorem activity_true (path : LivePath graph index head blocked)
    (K : Finset (Channel n)) (activities : Fin graph.nodeCount → Bool)
    (forward : graph.ForwardModel (assignmentOfSet K) activities) :
    head ∈ K → Disjoint blocked K → activities index = true := by
  induction path with
  | input index head gateEquation =>
      intro headTrue _
      have row := forward index (implicationClause (.inl head) [.inr index])
        (by simp [DAG.nodeClauses, gateEquation])
      have alternatives := (implicationClause_holds _ _ _).mp row
        ((assignmentOfSet_eq_true K head).mpr headTrue)
      simpa [DAG.zeroAssignment] using alternatives
  | disj index refs child head blocked gateEquation membership tail inductionHypothesis =>
      intro headTrue guardsFalse
      have childTrue := inductionHypothesis headTrue guardsFalse
      have row := forward index
        (implicationClause (.inr (graph.childIndex index child)) [.inr index])
        (by simpa only [DAG.nodeClauses, gateEquation] using
          List.mem_map.mpr ⟨child, membership, rfl⟩)
      simpa [DAG.zeroAssignment] using (implicationClause_holds _ _ _).mp row childTrue
  | guard index child labels head blocked gateEquation tail inductionHypothesis =>
      intro headTrue guardsFalse
      have childTrue := inductionHypothesis headTrue
        (guardsFalse.mono_left Finset.subset_union_right)
      have row := forward index (implicationClause (.inr (graph.childIndex index child))
        (labels.map Sum.inl ++ [.inr index])) (by simp [DAG.nodeClauses, gateEquation])
      obtain ⟨literalVar, membership, trueValue⟩ := (implicationClause_holds _ _ _).mp row childTrue
      rcases List.mem_append.mp membership with guardMember | rootMember
      · obtain ⟨channel, channelMember, rfl⟩ := List.mem_map.mp guardMember
        have channelTrue : channel ∈ K := (assignmentOfSet_eq_true K channel).mp trueValue
        exact False.elim (Finset.disjoint_left.mp guardsFalse
          (Finset.mem_union_left _ (by simpa using channelMember)) channelTrue)
      · have variableEquation : literalVar = .inr index := List.mem_singleton.mp rootMember
        subst literalVar
        exact trueValue

end Controller.Decoder.LivePath

namespace Controller.Decoder.DAG

open CNF ZeroSystem

variable {n : ℕ}

/-- All semantically true nodes are active in every forward model. -/
theorem eval_true_implies_activity (graph : DAG n) (guarded : graph.Guarded)
    (K : Finset (Channel n)) (activities : Fin graph.nodeCount → Bool)
    (forward : graph.ForwardModel (assignmentOfSet K) activities)
    (index : Fin graph.nodeCount) (trueValue : graph.eval (assignmentOfSet K) index = true) :
    activities index = true := by
  obtain ⟨head, blocked, path, headTrue, guardsFalse⟩ :=
    graph.exists_livePath_of_eval_true guarded K index trueValue
  exact path.activity_true K activities forward headTrue guardsFalse

/-- Positive units for every channel fixed true. -/
def trueUnitClauses (graph : DAG n) (T : Finset (Channel n)) : List (Clause graph.ZeroVar) :=
  ((List.finRange n).filter fun channel => decide (channel ∈ T)).map fun channel =>
    positiveClause [.inl channel]

/-- Negative units for every channel fixed false. -/
def falseUnitClauses (graph : DAG n) (F : Finset (Channel n)) : List (Clause graph.ZeroVar) :=
  ((List.finRange n).filter fun channel => decide (channel ∈ F)).map fun channel =>
    implicationClause (.inl channel) []

theorem trueUnitClauses_holds_iff (graph : DAG n) (T K : Finset (Channel n))
    (activities : Fin graph.nodeCount → Bool) :
    (∀ clause ∈ graph.trueUnitClauses T,
      ClauseHolds (graph.zeroAssignment (assignmentOfSet K) activities) clause) ↔ T ⊆ K := by
  simp only [trueUnitClauses, List.forall_mem_map, List.forall_mem_filter, positiveClause_holds]
  simp [zeroAssignment, Finset.subset_iff]

theorem falseUnitClauses_holds_iff (graph : DAG n) (F K : Finset (Channel n))
    (activities : Fin graph.nodeCount → Bool) :
    (∀ clause ∈ graph.falseUnitClauses F,
      ClauseHolds (graph.zeroAssignment (assignmentOfSet K) activities) clause) ↔ Disjoint K F := by
  simp only [falseUnitClauses, List.forall_mem_map, List.forall_mem_filter, implicationClause_holds]
  simp [zeroAssignment, Finset.disjoint_right]

/-- Nonemptiness, the one-bus target condition, and the supplied fixed units. -/
def channelClauses (graph : DAG n) (b : ℕ) (target : Channel n)
    (T F : Finset (Channel n)) : List (Clause graph.ZeroVar) :=
  (([positiveClause ((List.finRange n).map Sum.inl)] ++
    (if b = 1 then [positiveClause [.inl target]] else [])) ++
      graph.trueUnitClauses T) ++ graph.falseUnitClauses F

theorem channelClauses_holds_iff (graph : DAG n) (b : ℕ) (target : Channel n)
    (T F K : Finset (Channel n)) (activities : Fin graph.nodeCount → Bool) :
    (∀ clause ∈ graph.channelClauses b target T F,
      ClauseHolds (graph.zeroAssignment (assignmentOfSet K) activities) clause) ↔
      Admissible b target K ∧ ExtendsFixed T F K := by
  by_cases oneBus : b = 1 <;>
    simp only [channelClauses, oneBus, ite_true, ite_false, List.forall_mem_append,
      List.forall_mem_singleton, trueUnitClauses_holds_iff,
      falseUnitClauses_holds_iff, positiveClause_holds] <;>
    simp [zeroAssignment, oneBus, Admissible, ExtendsFixed, Finset.Nonempty, and_assoc]

/-- The complete forward zero system, including reachability and partial units. -/
def zeroSystem (graph : DAG n) (b : ℕ) (target : Channel n)
    (root : Fin graph.nodeCount) (T F : Finset (Channel n)) : Formula graph.ZeroVar :=
  ofClauses ((graph.forwardClauses ++ graph.channelClauses b target T F) ++
    [implicationClause (.inr root) []])

/-- Satisfaction separates into the forward, channel, and false-root obligations. -/
theorem zeroSystem_satisfies_iff (graph : DAG n) (b : ℕ) (target : Channel n)
    (root : Fin graph.nodeCount) (T F K : Finset (Channel n))
    (activities : Fin graph.nodeCount → Bool) :
    Satisfies (graph.zeroAssignment (assignmentOfSet K) activities)
        (graph.zeroSystem b target root T F) ↔
      graph.ForwardModel (assignmentOfSet K) activities ∧
        (Admissible b target K ∧ ExtendsFixed T F K) ∧ activities root = false := by
  simp only [zeroSystem, satisfies_ofClauses, List.forall_mem_append,
    List.forall_mem_singleton, forwardClauses_holds_iff, channelClauses_holds_iff,
    implicationClause_holds]
  simp [zeroAssignment, and_assoc]

/-- Fixing the channel assignment leaves activities existentially quantified. -/
theorem zeroSystem_projection (graph : DAG n) (guarded : graph.Guarded)
    (b : ℕ) (target : Channel n) (root : Fin graph.nodeCount)
    (T F K : Finset (Channel n)) :
    (∃ activities, Satisfies (graph.zeroAssignment (assignmentOfSet K) activities)
      (graph.zeroSystem b target root T F)) ↔
      Admissible b target K ∧ ExtendsFixed T F K ∧
        graph.eval (assignmentOfSet K) root = false := by
  constructor
  · rintro ⟨activities, satisfies⟩
    obtain ⟨forward, channelConditions, rootFalse⟩ :=
      (graph.zeroSystem_satisfies_iff b target root T F K activities).mp satisfies
    refine ⟨channelConditions.1, channelConditions.2, ?_⟩
    apply Bool.eq_false_of_not_eq_true
    intro rootTrue
    have active := graph.eval_true_implies_activity guarded K activities forward root rootTrue
    exact Bool.false_ne_true (rootFalse.symm.trans active)
  · rintro ⟨admissible, fixed, rootFalse⟩
    refine ⟨graph.eval (assignmentOfSet K), ?_⟩
    apply (graph.zeroSystem_satisfies_iff b target root T F K _).mpr
    exact ⟨graph.exact_forwardModel guarded _, ⟨admissible, fixed⟩, rootFalse⟩

/-- Recover the channel set of an assignment over both variable namespaces. -/
def zeroChannelSet (graph : DAG n) (assignment : graph.ZeroVar → Bool) : Finset (Channel n) :=
  setOfAssignment (fun channel => assignment (.inl channel))

/-- Every combined assignment has exactly its channel-set/activity decomposition. -/
theorem zeroAssignment_channelSet (graph : DAG n) (assignment : graph.ZeroVar → Bool) :
    graph.zeroAssignment (assignmentOfSet (graph.zeroChannelSet assignment))
      (fun index => assignment (.inr index)) = assignment := by
  funext literalVar
  cases literalVar with
  | inl channel =>
      change assignmentOfSet (setOfAssignment (fun channel => assignment (.inl channel))) channel = _
      rw [assignmentOfSet_setOfAssignment]
  | inr index => rfl

/-- The existential decision projection follows from the fixed-channel projection. -/
theorem zeroSystem_satisfiable_iff (graph : DAG n) (guarded : graph.Guarded)
    (b : ℕ) (target : Channel n) (root : Fin graph.nodeCount)
    (T F : Finset (Channel n)) :
    Satisfiable (graph.zeroSystem b target root T F) ↔
      ∃ K, Admissible b target K ∧ ExtendsFixed T F K ∧
        graph.eval (assignmentOfSet K) root = false := by
  constructor
  · rintro ⟨assignment, satisfies⟩
    refine ⟨graph.zeroChannelSet assignment, ?_⟩
    apply (graph.zeroSystem_projection guarded b target root T F _).mp
    refine ⟨fun index => assignment (.inr index), ?_⟩
    simpa only [graph.zeroAssignment_channelSet assignment] using satisfies
  · rintro ⟨K, zero⟩
    obtain ⟨activities, satisfies⟩ := (graph.zeroSystem_projection guarded b target root T F K).mpr zero
    exact ⟨graph.zeroAssignment (assignmentOfSet K) activities, satisfies⟩

/-- All channel restrictions use positive clauses or single negative units. -/
theorem channelClauses_dualHorn (graph : DAG n) (b : ℕ) (target : Channel n)
    (T F : Finset (Channel n)) (clause : Clause graph.ZeroVar)
    (membership : clause ∈ graph.channelClauses b target T F) : Horn.DualHornClause clause := by
  have positiveUnits : ∀ clause ∈ graph.trueUnitClauses T, Horn.DualHornClause clause := by
    intro clause member
    obtain ⟨channel, _, rfl⟩ := List.mem_map.mp member
    exact positiveClause_dualHorn _
  have negativeUnits : ∀ clause ∈ graph.falseUnitClauses F, Horn.DualHornClause clause := by
    intro clause member
    obtain ⟨channel, _, rfl⟩ := List.mem_map.mp member
    exact implicationClause_dualHorn _ _
  by_cases oneBus : b = 1
  · simp only [channelClauses, oneBus, ite_true, List.mem_append, List.mem_singleton] at membership
    rcases membership with ((rfl | rfl) | trueUnit) | falseUnit
    · exact positiveClause_dualHorn _
    · exact positiveClause_dualHorn _
    · exact positiveUnits _ trueUnit
    · exact negativeUnits _ falseUnit
  · simp only [channelClauses, oneBus, ite_false, List.mem_append, List.mem_singleton,
      List.not_mem_nil, or_false] at membership
    rcases membership with (rfl | trueUnit) | falseUnit
    · exact positiveClause_dualHorn _
    · exact positiveUnits _ trueUnit
    · exact negativeUnits _ falseUnit

/-- A guarded decoder's complete zero system is dual-Horn. -/
theorem zeroSystem_dualHorn (graph : DAG n) (guarded : graph.Guarded)
    (b : ℕ) (target : Channel n) (root : Fin graph.nodeCount) (T F : Finset (Channel n)) :
    Horn.DualHorn (graph.zeroSystem b target root T F) := by
  intro clause membership
  have rowMembership : clause ∈ (graph.forwardClauses ++ graph.channelClauses b target T F) ++
      [implicationClause (.inr root) []] := by
    simpa only [zeroSystem, ofClauses, List.mem_toArray] using membership
  rcases List.mem_append.mp rowMembership with preceding | final
  · rcases List.mem_append.mp preceding with nodeMember | channelMember
    · obtain ⟨index, _, localMember⟩ := List.mem_flatMap.mp nodeMember
      exact graph.nodeClauses_dualHorn guarded index clause localMember
    · exact graph.channelClauses_dualHorn b target T F clause channelMember
  · have rowEquation := List.mem_singleton.mp final
    subst clause
    exact implicationClause_dualHorn _ _

/-- The channel projection of any greatest activity model is a greatest eligible zero set. -/
theorem greatest_model_projects_to_greatest_zero (graph : DAG n) (guarded : graph.Guarded)
    (b : ℕ) (target : Channel n) (root : Fin graph.nodeCount) (T F : Finset (Channel n))
    (assignment : graph.ZeroVar → Bool)
    (satisfies : Satisfies assignment (graph.zeroSystem b target root T F))
    (dominates : ∀ model, Satisfies model (graph.zeroSystem b target root T F) →
      Horn.Below model assignment) :
    (Admissible b target (graph.zeroChannelSet assignment) ∧
      ExtendsFixed T F (graph.zeroChannelSet assignment) ∧
      graph.eval (assignmentOfSet (graph.zeroChannelSet assignment)) root = false) ∧
      ∀ K, Admissible b target K → ExtendsFixed T F K →
        graph.eval (assignmentOfSet K) root = false → K ⊆ graph.zeroChannelSet assignment := by
  constructor
  · apply (graph.zeroSystem_projection guarded b target root T F _).mp
    refine ⟨fun index => assignment (.inr index), ?_⟩
    simpa only [graph.zeroAssignment_channelSet assignment] using satisfies
  · intro K admissible fixed zero channel membership
    obtain ⟨activities, model⟩ :=
      (graph.zeroSystem_projection guarded b target root T F K).mpr ⟨admissible, fixed, zero⟩
    have positive : (graph.zeroAssignment (assignmentOfSet K) activities) (.inl channel) = true :=
      (assignmentOfSet_eq_true K channel).mpr membership
    have greatestPositive := dominates _ model (.inl channel) positive
    exact (mem_setOfAssignment _ channel).mpr greatestPositive

/-- A satisfiable guarded zero query has an inclusion-wise greatest eligible witness. -/
theorem exists_greatest_zero (graph : DAG n) (guarded : graph.Guarded)
    (b : ℕ) (target : Channel n) (root : Fin graph.nodeCount) (T F : Finset (Channel n))
    (hasZero : ∃ K, Admissible b target K ∧ ExtendsFixed T F K ∧
      graph.eval (assignmentOfSet K) root = false) :
    ∃ greatest, (Admissible b target greatest ∧ ExtendsFixed T F greatest ∧
      graph.eval (assignmentOfSet greatest) root = false) ∧
      ∀ K, Admissible b target K → ExtendsFixed T F K →
        graph.eval (assignmentOfSet K) root = false → K ⊆ greatest := by
  have satisfiable := (graph.zeroSystem_satisfiable_iff guarded b target root T F).mpr hasZero
  obtain ⟨assignment, satisfies, dominates⟩ :=
    Horn.exists_greatest_model (graph.zeroSystem_dualHorn guarded b target root T F) satisfiable
  exact ⟨graph.zeroChannelSet assignment,
    graph.greatest_model_projects_to_greatest_zero guarded b target root T F
      assignment satisfies dominates⟩

end Controller.Decoder.DAG
