module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Decoder.Cone
public import Controller.Decoder.Detect
public import Controller.Decoder.Foundation
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Sum
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Data.Fintype.Fin

@[expose] public section

/-!
# Internal occurrence forests

Root positions and child-list positions are distinct uses of stored nodes.
Only internal nodes are required to have at most one use in the union of output
cones. Input and zero terminals may be shared, and channel labels may repeat.
Pruning keeps one copy of each reachable stored identity.
-/

namespace Controller.Decoder

namespace Gate

def isInternal : Gate n available → Bool
  | .zero | .input _ => false
  | .disj _ | .guard _ _ | .liveAnd _ _ => true

@[simp] theorem mapChildren_isInternal (gate : Gate n a)
    (rename : (child : Fin a) → child ∈ gate.children → Fin b) :
    (gate.mapChildren rename).isInternal = gate.isInternal := by
  cases gate <;> rfl

end Gate

namespace DAG

variable {n : ℕ}

/-- Positions, rather than endpoints, retain repeated child references. -/
abbrev ParentOccurrence (graph : DAG n) :=
  Σ parent : Fin graph.nodeCount, Fin (graph.node parent).children.length

abbrev StoredOccurrence (graph : DAG n) :=
  Fin graph.roots.length ⊕ graph.ParentOccurrence

instance storedOccurrenceFintype (graph : DAG n) : Fintype graph.StoredOccurrence := by
  dsimp [StoredOccurrence, ParentOccurrence]
  infer_instance

def refers (graph : DAG n) : graph.StoredOccurrence → Fin graph.nodeCount
  | .inl rootPosition => graph.roots.get rootPosition
  | .inr childPosition => graph.childIndex childPosition.1
      ((graph.node childPosition.1).children.get childPosition.2)

def parentRetained (graph : DAG n) (nodes : Finset (Fin graph.nodeCount)) :
    graph.StoredOccurrence → Prop
  | .inl _ => True
  | .inr childPosition => childPosition.1 ∈ nodes

abbrev StoredUses (graph : DAG n) (node : Fin graph.nodeCount) :=
  {occurrence : graph.StoredOccurrence // graph.refers occurrence = node}

abbrev ActiveUses (graph : DAG n) (nodes : Finset (Fin graph.nodeCount))
    (node : Fin graph.nodeCount) :=
  {occurrence : graph.StoredOccurrence //
    graph.parentRetained nodes occurrence ∧ graph.refers occurrence = node}

noncomputable instance storedUsesFintype (graph : DAG n) (node : Fin graph.nodeCount) :
    Fintype (graph.StoredUses node) := Fintype.ofFinite _

noncomputable instance activeUsesFintype (graph : DAG n) (nodes : Finset (Fin graph.nodeCount))
    (node : Fin graph.nodeCount) : Fintype (graph.ActiveUses nodes node) := Fintype.ofFinite _

/-- Exact manuscript promise; irrelevant stored parents contribute no uses. -/
def FormulaForest (graph : DAG n) : Prop :=
  graph.Guarded ∧ ∀ node, (graph.node node).isInternal = true →
    Nat.card (graph.ActiveUses (graph.cones graph.roots) node) ≤ 1

/-- The stricter all-stored parent-count precheck, suitable after pruning. -/
def StoredForest (graph : DAG n) : Prop :=
  graph.Guarded ∧ ∀ node, (graph.node node).isInternal = true →
    Nat.card (graph.StoredUses node) ≤ 1

theorem storedForest_formulaForest (graph : DAG n) (forest : graph.StoredForest) :
    graph.FormulaForest := by
  refine ⟨forest.1, ?_⟩
  intro node internal
  have injective : Function.Injective (fun use : graph.ActiveUses (graph.cones graph.roots) node =>
      (⟨use.val, use.property.2⟩ : graph.StoredUses node)) := by
    intro first second equal
    exact Subtype.ext (congrArg (fun use : graph.StoredUses node => use.val) equal)
  exact (Nat.card_le_card_of_injective _ injective).trans (forest.2 node internal)

namespace Selection

variable {graph : DAG n}

private theorem mapped_get_option {α β : Type*} (f : α → β) (items : List α)
    (offset : ℕ) (bound : offset < items.length) :
    (items.map f)[offset]? = some (f (items.get ⟨offset, bound⟩)) := by
  rw [List.getElem?_map, List.getElem?_eq_getElem bound]
  rfl

/-- Reindex every occurrence position without merging repeated endpoints. -/
def occurrenceMap (selection : Selection graph)
    (rootMembership : ∀ root ∈ graph.roots, root ∈ selection.nodes) :
    (selection.extract graph.roots rootMembership).StoredOccurrence → graph.StoredOccurrence
  | .inl position => .inl ⟨position.val, by
      simpa only [extract_root_length] using position.isLt⟩
  | .inr ⟨parent, position⟩ => .inr ⟨selection.oldIndex parent,
      ⟨position.val, by simpa only [extract_child_length] using position.isLt⟩⟩

theorem occurrenceMap_injective (selection : Selection graph)
    (rootMembership : ∀ root ∈ graph.roots, root ∈ selection.nodes) :
    Function.Injective (selection.occurrenceMap rootMembership) := by
  intro first second equal
  cases first with
  | inl first =>
    cases second with
    | inl second =>
      apply congrArg Sum.inl
      apply Fin.ext
      have values := congrArg (fun occurrence : graph.StoredOccurrence =>
        match occurrence with | .inl position => position.val | .inr _ => 0) equal
      exact values
    | inr second => cases equal
  | inr first =>
    cases second with
    | inl second => cases equal
    | inr second =>
      obtain ⟨firstParent, firstPosition⟩ := first
      obtain ⟨secondParent, secondPosition⟩ := second
      have data := Sum.inr.inj equal
      have parents : firstParent = secondParent := selection.oldIndex.injective
        (congrArg Sigma.fst data)
      subst secondParent
      have positions : firstPosition = secondPosition := Fin.ext
        (congrArg (fun occurrence : graph.ParentOccurrence => occurrence.2.val) data)
      subst secondPosition
      rfl

theorem occurrenceMap_refers (selection : Selection graph)
    (rootMembership : ∀ root ∈ graph.roots, root ∈ selection.nodes)
    (occurrence : (selection.extract graph.roots rootMembership).StoredOccurrence) :
    graph.refers (selection.occurrenceMap rootMembership occurrence) =
      selection.oldIndex ((selection.extract graph.roots rootMembership).refers occurrence) := by
  cases occurrence with
  | inl position =>
    have oldBound : position.val < graph.roots.length := by
      simpa only [extract_root_length] using position.isLt
    have value := congrArg (fun entries : List (Fin graph.nodeCount) => entries[position.val]?)
      (selection.extract_roots graph.roots rootMembership)
    have mapped : ((selection.extract graph.roots rootMembership).roots.map selection.oldIndex)[position.val]? =
        some (selection.oldIndex ((selection.extract graph.roots rootMembership).roots.get position)) := by
      exact mapped_get_option selection.oldIndex
        (graph.roots.attach.map fun root => selection.newIndex root.val (rootMembership _ root.property))
        position.val (by simpa only [extract] using position.isLt)
    rw [mapped, List.getElem?_eq_getElem oldBound] at value
    exact (Option.some.inj value).symm
  | inr occurrence =>
    obtain ⟨parent, position⟩ := occurrence
    have oldBound : position.val < (graph.node (selection.oldIndex parent)).children.length := by
      simpa only [extract_child_length] using position.isLt
    have value := congrArg (fun entries : List (Fin graph.nodeCount) => entries[position.val]?)
      (selection.extract_children graph.roots rootMembership parent)
    simp only [List.getElem?_map, List.getElem?_eq_getElem position.isLt,
      List.getElem?_eq_getElem oldBound, Option.map_some, Option.some.injEq] at value
    exact value.symm

theorem occurrenceMap_retained (selection : Selection graph)
    (rootMembership : ∀ root ∈ graph.roots, root ∈ selection.nodes)
    (occurrence : (selection.extract graph.roots rootMembership).StoredOccurrence) :
    graph.parentRetained selection.nodes
      (selection.occurrenceMap rootMembership occurrence) := by
  cases occurrence with
  | inl position => trivial
  | inr occurrence => exact selection.oldIndex_mem occurrence.1

/-- Exact occurrences in the extracted table inject into retained original uses. -/
def useMap (selection : Selection graph)
    (rootMembership : ∀ root ∈ graph.roots, root ∈ selection.nodes)
    (node : Fin selection.nodes.card) :
    (selection.extract graph.roots rootMembership).StoredUses node →
      graph.ActiveUses selection.nodes (selection.oldIndex node) :=
  fun use => ⟨selection.occurrenceMap rootMembership use.val,
    selection.occurrenceMap_retained rootMembership use.val,
    (selection.occurrenceMap_refers rootMembership use.val).trans
      (congrArg selection.oldIndex use.property)⟩

theorem useMap_injective (selection : Selection graph)
    (rootMembership : ∀ root ∈ graph.roots, root ∈ selection.nodes)
    (node : Fin selection.nodes.card) :
    Function.Injective (selection.useMap rootMembership node) := by
  intro first second equal
  apply Subtype.ext
  apply selection.occurrenceMap_injective rootMembership
  exact congrArg Subtype.val equal

/-- Recover the reindexed position of every retained original occurrence. -/
def occurrenceInverse (selection : Selection graph)
    (rootMembership : ∀ root ∈ graph.roots, root ∈ selection.nodes)
    (occurrence : graph.StoredOccurrence) (retained : graph.parentRetained selection.nodes occurrence) :
    (selection.extract graph.roots rootMembership).StoredOccurrence :=
  match occurrence with
  | .inl position => .inl ⟨position.val, by simpa only [extract_root_length] using position.isLt⟩
  | .inr ⟨parent, position⟩ =>
    let membership : parent ∈ selection.nodes := retained
    .inr ⟨selection.newIndex parent membership, ⟨position.val, by
      dsimp only [extract]
      rw [Gate.mapChildren_children_length, oldIndex_newIndex]
      exact position.isLt⟩⟩

theorem occurrenceMap_inverse (selection : Selection graph)
    (rootMembership : ∀ root ∈ graph.roots, root ∈ selection.nodes)
    (occurrence : graph.StoredOccurrence) (retained : graph.parentRetained selection.nodes occurrence) :
    selection.occurrenceMap rootMembership
      (selection.occurrenceInverse rootMembership occurrence retained) = occurrence := by
  cases occurrence with
  | inl position => rfl
  | inr occurrence =>
    obtain ⟨parent, position⟩ := occurrence
    apply congrArg Sum.inr
    apply Sigma.ext (selection.oldIndex_newIndex parent retained)
    exact (Fin.heq_ext_iff (congrArg (fun index => (graph.node index).children.length)
      (selection.oldIndex_newIndex parent retained))).mpr rfl

theorem useMap_surjective (selection : Selection graph)
    (rootMembership : ∀ root ∈ graph.roots, root ∈ selection.nodes)
    (node : Fin selection.nodes.card) :
    Function.Surjective (selection.useMap rootMembership node) := by
  intro use
  let occurrence := selection.occurrenceInverse rootMembership use.val use.property.1
  have mapped : selection.occurrenceMap rootMembership occurrence = use.val :=
    selection.occurrenceMap_inverse rootMembership use.val use.property.1
  have reference := selection.occurrenceMap_refers rootMembership occurrence
  rw [mapped, use.property.2] at reference
  have newReference : (selection.extract graph.roots rootMembership).refers occurrence = node :=
    selection.oldIndex.injective reference.symm
  refine ⟨⟨occurrence, newReference⟩, ?_⟩
  exact Subtype.ext mapped

/-- Complete positional use equivalence, rather than only a count upper bound. -/
noncomputable def useEquiv (selection : Selection graph)
    (rootMembership : ∀ root ∈ graph.roots, root ∈ selection.nodes)
    (node : Fin selection.nodes.card) :
    (selection.extract graph.roots rootMembership).StoredUses node ≃
      graph.ActiveUses selection.nodes (selection.oldIndex node) :=
  Equiv.ofBijective _ ⟨selection.useMap_injective rootMembership node,
    selection.useMap_surjective rootMembership node⟩

theorem extract_use_count (selection : Selection graph)
    (rootMembership : ∀ root ∈ graph.roots, root ∈ selection.nodes)
    (node : Fin selection.nodes.card) :
    Nat.card ((selection.extract graph.roots rootMembership).StoredUses node) =
      Nat.card (graph.ActiveUses selection.nodes (selection.oldIndex node)) :=
  Nat.card_congr (selection.useEquiv rootMembership node)

theorem activeUse_node_mem (selection : Selection graph)
    (rootMembership : ∀ root ∈ graph.roots, root ∈ selection.nodes)
    (node : Fin graph.nodeCount) (use : graph.ActiveUses selection.nodes node) :
    node ∈ selection.nodes := by
  obtain ⟨occurrence, retained, reference⟩ := use
  rw [← reference]
  cases occurrence with
  | inl position => exact rootMembership _ (List.get_mem _ _)
  | inr occurrence =>
    exact selection.closed occurrence.1 retained
      ((graph.node occurrence.1).children.get occurrence.2) (List.get_mem _ _)

/-- The parent-count test after extraction is equivalent to the exact retained test. -/
theorem extract_count_test_iff (selection : Selection graph)
    (rootMembership : ∀ root ∈ graph.roots, root ∈ selection.nodes) :
    (∀ node, ((selection.extract graph.roots rootMembership).node node).isInternal = true →
      Nat.card ((selection.extract graph.roots rootMembership).StoredUses node) ≤ 1) ↔
    (∀ node, (graph.node node).isInternal = true →
      Nat.card (graph.ActiveUses selection.nodes node) ≤ 1) := by
  constructor
  · intro counts node internal
    by_cases retained : node ∈ selection.nodes
    · let newNode := selection.newIndex node retained
      have newInternal : ((selection.extract graph.roots rootMembership).node newNode).isInternal = true := by
        simp only [extract, Gate.mapChildren_isInternal]
        rw [show selection.oldIndex newNode = node from selection.oldIndex_newIndex node retained]
        exact internal
      have bound := counts newNode newInternal
      rw [selection.extract_use_count rootMembership newNode] at bound
      simpa only [newNode, oldIndex_newIndex] using bound
    · have : IsEmpty (graph.ActiveUses selection.nodes node) :=
        ⟨fun use => retained (selection.activeUse_node_mem rootMembership node use)⟩
      simp
  · intro counts node internal
    rw [selection.extract_use_count rootMembership node]
    apply counts
    simpa only [extract, Gate.mapChildren_isInternal] using internal

theorem extract_storedForest (selection : Selection graph)
    (rootMembership : ∀ root ∈ graph.roots, root ∈ selection.nodes)
    (guarded : graph.Guarded)
    (counts : ∀ node, (graph.node node).isInternal = true →
      Nat.card (graph.ActiveUses selection.nodes node) ≤ 1) :
    (selection.extract graph.roots rootMembership).StoredForest := by
  constructor
  · intro node
    simpa only [extract, Gate.IsGuarded, Gate.mapChildren_isLiveAnd] using guarded (selection.oldIndex node)
  · intro node internal
    have oldInternal : (graph.node (selection.oldIndex node)).isInternal = true := by
      simpa only [extract, Gate.mapChildren_isInternal] using internal
    exact (Nat.card_le_card_of_injective _
      (selection.useMap_injective rootMembership node)).trans (counts _ oldInternal)

end Selection

/-- One sharing-preserving pruning pass reconciles the source forest promise
with the stricter all-stored-parent precheck. -/
theorem prune_storedForest (graph : DAG n) (forest : graph.FormulaForest) :
    graph.prune.StoredForest := by
  exact Selection.extract_storedForest
    ⟨graph.cones graph.roots, graph.cones_childClosed graph.roots⟩
    (graph.root_mem_cones graph.roots) forest.1 forest.2

theorem prune_storedForest_iff (graph : DAG n) (guarded : graph.Guarded) :
    graph.prune.StoredForest ↔ graph.FormulaForest := by
  constructor
  · intro forest
    refine ⟨guarded, ?_⟩
    exact (Selection.extract_count_test_iff
      ⟨graph.cones graph.roots, graph.cones_childClosed graph.roots⟩
      (graph.root_mem_cones graph.roots)).mp forest.2
  · exact graph.prune_storedForest

theorem prune_forest_outputs (graph : DAG n) (assignment : Assignment n) :
    graph.prune.outputValues assignment = graph.outputValues assignment :=
  graph.prune_outputValues assignment

/-- An unmarked channel makes the guarded cone agree with the all-zero input.
The many-bus image then admits its singleton. -/
theorem unmarked_many_zero (graph : DAG n) (b : ℕ) (many : 2 ≤ b) (target : Channel n)
    (root : Fin graph.nodeCount) (channel : Channel n) (unmarked : channel ∉ graph.scope root) :
    Admissible b target {channel} ∧ graph.eval (assignmentOfSet {channel}) root = false := by
  refine ⟨(admissible_many many target _).mpr (by simp), ?_⟩
  exact unmarked_singleton_zero graph root channel unmarked

/-- Root-local retained channels include the forced target only for one bus. -/
def zeroScope (graph : DAG n) (b : ℕ) (target : Channel n)
    (root : Fin graph.nodeCount) : Finset (Channel n) :=
  if b = 1 then insert target (graph.scope root) else graph.scope root

/-- Restricting a valuation to the cone and optional target preserves its root. -/
theorem eval_inter_zeroScope (graph : DAG n) (b : ℕ) (target : Channel n)
    (root : Fin graph.nodeCount) (K : Finset (Channel n)) :
    graph.eval (assignmentOfSet (K ∩ graph.zeroScope b target root)) root =
      graph.eval (assignmentOfSet K) root := by
  apply graph.eval_eq_of_agree_scope
  intro channel inScope
  have retained : channel ∈ graph.zeroScope b target root := by
    unfold zeroScope
    split <;> simp_all
  simp only [assignmentOfSet, Finset.mem_inter, retained, and_true]

/-- In the forced-target case the local restriction retains reachability. -/
theorem oneBus_inter_zeroScope_admissible (graph : DAG n) (target : Channel n)
    (root : Fin graph.nodeCount) (K : Finset (Channel n))
    (eligible : Admissible 1 target K) :
    Admissible 1 target (K ∩ graph.zeroScope 1 target root) := by
  have retained : target ∈ K ∩ graph.zeroScope 1 target root := by
    simp [zeroScope, eligible.2 rfl]
  exact ⟨⟨target, retained⟩, fun _ => retained⟩

/-- If there is no unmarked channel, retaining scope changes no coordinates. -/
theorem zeroScope_eq_univ_of_no_unmarked (graph : DAG n) (b : ℕ) (target : Channel n)
    (root : Fin graph.nodeCount) (allMarked : ∀ channel, channel ∈ graph.scope root) :
    graph.zeroScope b target root = Finset.univ := by
  ext channel
  unfold zeroScope
  split <;> simp [allMarked channel]

/-- A root's shared-node cone, retaining each reachable stored identity once. -/
def singleConeSelection (graph : DAG n) (root : Fin graph.nodeCount) : Selection graph :=
  ⟨graph.cones [root], graph.cones_childClosed [root]⟩

def singleCone (graph : DAG n) (root : Fin graph.nodeCount) : DAG n :=
  (graph.singleConeSelection root).extract [root] (graph.root_mem_cones [root])

def singleConeRoot (graph : DAG n) (root : Fin graph.nodeCount) :
    Fin (graph.singleCone root).nodeCount :=
  (graph.singleConeSelection root).newIndex root
    (graph.root_mem_cones [root] root (by simp))

theorem singleCone_eval (graph : DAG n) (root : Fin graph.nodeCount) (assignment : Assignment n) :
    (graph.singleCone root).eval assignment (graph.singleConeRoot root) = graph.eval assignment root := by
  exact ((graph.singleConeSelection root).extract_eval [root]
    (graph.root_mem_cones [root]) assignment
    ((graph.singleConeSelection root).newIndex root
      (graph.root_mem_cones [root] root (by simp)))).trans
    (congrArg (graph.eval assignment)
      ((graph.singleConeSelection root).oldIndex_newIndex root
        (graph.root_mem_cones [root] root (by simp))))

theorem singleCone_guarded (graph : DAG n) (guarded : graph.Guarded)
    (root : Fin graph.nodeCount) : (graph.singleCone root).Guarded := by
  intro node
  simpa only [singleCone, Selection.extract, Gate.IsGuarded, Gate.mapChildren_isLiveAnd]
    using guarded ((graph.singleConeSelection root).oldIndex node)

/-- A healthy-one root necessarily marks the target channel. -/
theorem healthyOne_target_mem_scope (graph : DAG n) (target : Channel n)
    (root : Fin graph.nodeCount) (healthy : graph.eval (assignmentOfSet {target}) root = true) :
    target ∈ graph.scope root := by
  by_contra unmarked
  have zero := unmarked_singleton_zero graph root target unmarked
  rw [healthy] at zero
  cases zero

/-- Only the first min(n,|scope|+1) channel indices are materialized. -/
def unmarkedCandidates (graph : DAG n) (root : Fin graph.nodeCount) : List (Channel n) :=
  (List.finRange (min n ((graph.scope root).card + 1))).map fun index =>
    ⟨index.val, lt_of_lt_of_le index.isLt (Nat.min_le_left _ _)⟩

def firstUnmarked (graph : DAG n) (root : Fin graph.nodeCount) : Option (Channel n) :=
  (graph.unmarkedCandidates root).find? fun channel => decide (channel ∉ graph.scope root)

theorem firstUnmarked_some (graph : DAG n) (root : Fin graph.nodeCount)
    (channel : Channel n) (selected : graph.firstUnmarked root = some channel) :
    channel ∉ graph.scope root := by
  have hit : decide (channel ∉ graph.scope root) = true :=
    List.find?_some (p := fun item => decide (item ∉ graph.scope root))
      (a := channel) (by simpa only [firstUnmarked] using selected)
  exact of_decide_eq_true hit

theorem firstUnmarked_none_iff (graph : DAG n) (root : Fin graph.nodeCount) :
    graph.firstUnmarked root = none ↔ ∀ channel, channel ∈ graph.scope root := by
  constructor
  · intro absent
    have allLow : ∀ channel : Channel n,
        channel.val < min n ((graph.scope root).card + 1) → channel ∈ graph.scope root := by
      intro channel low
      have present : channel ∈ graph.unmarkedCandidates root := by
        apply List.mem_map.mpr
        refine ⟨⟨channel.val, low⟩, List.mem_finRange _, ?_⟩
        exact Fin.ext rfl
      have rejected := (List.find?_eq_none.mp absent) channel present
      simpa using rejected
    by_cases small : n ≤ (graph.scope root).card + 1
    · intro channel
      exact allLow channel (by simpa only [Nat.min_eq_left small] using channel.isLt)
    · have subset : (Finset.univ.filter fun channel : Channel n =>
          channel.val < (graph.scope root).card + 1) ⊆ graph.scope root := by
        intro channel present
        exact allLow channel (by
          rw [Nat.min_eq_right (by omega)]
          exact (Finset.mem_filter.mp present).2)
      have count := Finset.card_le_card subset
      rw [Fin.card_filter_val_lt, Nat.min_eq_right (by omega)] at count
      omega
  · intro allMarked
    apply List.find?_eq_none.mpr
    intro channel _
    simp [allMarked channel]

theorem unmarkedCandidates_length (graph : DAG n) (root : Fin graph.nodeCount) :
    (graph.unmarkedCandidates root).length ≤ (graph.scope root).card + 1 := by
  simp only [unmarkedCandidates, List.length_map, List.length_finRange]
  exact Nat.min_le_right _ _

end DAG
end Controller.Decoder
