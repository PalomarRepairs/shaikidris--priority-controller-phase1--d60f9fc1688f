module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Decoder.Eval
public import Mathlib.Data.Finset.Sort

@[expose] public section

/-!
# Sharing-preserving decoder cones

A closed set of stored node identities is enumerated in its inherited
topological order. Each retained identity gives exactly one output node.
Child, guard and root lists retain their order and repeated incidences.
The finite-set construction specifies the extraction; sparse-array costs
are a separate operational refinement.
-/

namespace Controller.Decoder

namespace Gate

variable {n a b : ℕ}

/-- Reindex only the live child incidences that a gate actually contains. -/
def mapChildren (gate : Gate n a)
    (f : (child : Fin a) → child ∈ gate.children → Fin b) : Gate n b := by
  cases gate with
  | zero => exact .zero
  | input channel => exact .input channel
  | disj refs => exact .disj (refs.attach.map fun child => f child.val child.property)
  | guard child labels => exact .guard (f child (by simp [children])) labels
  | liveAnd left right =>
      exact .liveAnd (f left (by simp [children])) (f right (by simp [children]))

/-- The complete ordered child list is mapped incidence by incidence. -/
theorem mapChildren_children (gate : Gate n a)
    (f : (child : Fin a) → child ∈ gate.children → Fin b) :
    (gate.mapChildren f).children =
      gate.children.attach.map (fun child => f child.val child.property) := by
  cases gate <;> simp [mapChildren, children]

/-- Recovering old identities after reindexing preserves the exact child list. -/
theorem mapChildren_children_map {α : Type*} (gate : Gate n a)
    (f : (child : Fin a) → child ∈ gate.children → Fin b)
    (newIdentity : Fin b → α) (oldIdentity : Fin a → α)
    (agreement : ∀ child membership, newIdentity (f child membership) = oldIdentity child) :
    (gate.mapChildren f).children.map newIdentity = gate.children.map oldIdentity := by
  rw [mapChildren_children, List.map_map]
  calc
    _ = gate.children.attach.map (fun child => oldIdentity child.val) := by
      apply List.map_congr_left
      intro child _
      exact agreement child.val child.property
    _ = gate.children.map oldIdentity := List.attach_map_val

/-- Reindexing neither duplicates nor removes child incidences. -/
@[simp] theorem mapChildren_children_length (gate : Gate n a)
    (f : (child : Fin a) → child ∈ gate.children → Fin b) :
    (gate.mapChildren f).children.length = gate.children.length := by
  cases gate <;> simp [mapChildren, children]

/-- Negative channel incidences are copied verbatim. -/
@[simp] theorem mapChildren_guardLabels (gate : Gate n a)
    (f : (child : Fin a) → child ∈ gate.children → Fin b) :
    (gate.mapChildren f).guardLabels = gate.guardLabels := by
  cases gate <;> rfl

/-- Node reindexing preserves the live-AND constructor. -/
@[simp] theorem mapChildren_isLiveAnd (gate : Gate n a)
    (f : (child : Fin a) → child ∈ gate.children → Fin b) :
    (gate.mapChildren f).isLiveAnd = gate.isLiveAnd := by
  cases gate <;> rfl

/-- Evaluation commutes with any reindexing that preserves referenced values. -/
theorem eval_mapChildren (gate : Gate n a)
    (f : (child : Fin a) → child ∈ gate.children → Fin b)
    (assignment : Assignment n) (oldValues : Fin a → Bool) (newValues : Fin b → Bool)
    (agreement : ∀ child membership, newValues (f child membership) = oldValues child) :
    (gate.mapChildren f).eval assignment newValues = gate.eval assignment oldValues := by
  cases gate with
  | zero => rfl
  | input channel => rfl
  | disj refs =>
      simp only [mapChildren, eval, List.any_map]
      rw [Bool.eq_iff_iff]
      simp only [List.any_eq_true, List.mem_attach, true_and, Subtype.exists]
      constructor
      · rintro ⟨child, membership, value⟩
        exact ⟨child, membership, (agreement child membership).symm.trans value⟩
      · rintro ⟨child, membership, value⟩
        exact ⟨child, membership, (agreement child membership).trans value⟩
  | guard child labels =>
      exact congrArg (fun value => value && !(labels.any assignment)) (agreement child _)
  | liveAnd left right =>
      exact congrArg₂ (fun leftValue rightValue => leftValue && rightValue)
        (agreement left _) (agreement right _)

end Gate

namespace DAG

variable {n : ℕ}

/-- The stored node identities in the syntactic cone of one root. -/
def cone (graph : DAG n) (root : Fin graph.nodeCount) : Finset (Fin graph.nodeCount) :=
  insert root ((graph.node root).children.toFinset.biUnion fun child =>
    graph.cone (graph.childIndex root child))
termination_by root.val
decreasing_by exact graph.childIndex_lt root child

theorem cone_eq (graph : DAG n) (root : Fin graph.nodeCount) :
    graph.cone root = insert root ((graph.node root).children.toFinset.biUnion fun child =>
      graph.cone (graph.childIndex root child)) := by
  rw [cone]

@[simp] theorem self_mem_cone (graph : DAG n) (root : Fin graph.nodeCount) :
    root ∈ graph.cone root := by
  rw [cone_eq]
  exact Finset.mem_insert_self _ _

/-- A listed child's cone is contained in its parent's cone. -/
theorem cone_child_subset (graph : DAG n) (parent : Fin graph.nodeCount)
    (child : Fin parent.val) (membership : child ∈ (graph.node parent).children) :
    graph.cone (graph.childIndex parent child) ⊆ graph.cone parent := by
  intro index indexMembership
  rw [cone_eq]
  exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr
    ⟨child, by simpa using membership, indexMembership⟩)

/-- Closure is stated only for listed child incidences. -/
def ChildClosed (graph : DAG n) (nodes : Finset (Fin graph.nodeCount)) : Prop :=
  ∀ parent ∈ nodes, ∀ child ∈ (graph.node parent).children,
    graph.childIndex parent child ∈ nodes

/-- Every syntactic cone is closed under live child references. -/
theorem cone_childClosed (graph : DAG n) (root : Fin graph.nodeCount) :
    graph.ChildClosed (graph.cone root) := by
  intro parent parentMembership child childMembership
  rw [cone_eq] at parentMembership
  rcases Finset.mem_insert.mp parentMembership with equality | membership
  · subst parent
    exact graph.cone_child_subset root child childMembership
      (graph.self_mem_cone (graph.childIndex root child))
  · obtain ⟨earlier, earlierMembership, parentMembership⟩ := Finset.mem_biUnion.mp membership
    exact graph.cone_child_subset root earlier (by simpa using earlierMembership)
      (graph.cone_childClosed (graph.childIndex root earlier)
        parent parentMembership child childMembership)
termination_by root.val
decreasing_by exact graph.childIndex_lt root earlier

/-- The cone is the smallest child-closed set containing its root. -/
theorem cone_subset_of_childClosed (graph : DAG n) (nodes : Finset (Fin graph.nodeCount))
    (closed : graph.ChildClosed nodes) (root : Fin graph.nodeCount) (rootMembership : root ∈ nodes) :
    graph.cone root ⊆ nodes := by
  intro index membership
  rw [cone_eq] at membership
  rcases Finset.mem_insert.mp membership with equality | membership
  · exact equality.symm ▸ rootMembership
  · obtain ⟨child, childMembership, membership⟩ := Finset.mem_biUnion.mp membership
    exact graph.cone_subset_of_childClosed nodes closed (graph.childIndex root child)
      (closed root rootMembership child (by simpa using childMembership)) membership
termination_by root.val
decreasing_by exact graph.childIndex_lt root child

/-- The union of the supplied output cones; repeated roots remain in the root list. -/
def cones (graph : DAG n) (roots : List (Fin graph.nodeCount)) : Finset (Fin graph.nodeCount) :=
  roots.toFinset.biUnion graph.cone

theorem root_mem_cones (graph : DAG n) (roots : List (Fin graph.nodeCount))
    (root : Fin graph.nodeCount) (membership : root ∈ roots) : root ∈ graph.cones roots := by
  exact Finset.mem_biUnion.mpr ⟨root, by simpa using membership, graph.self_mem_cone root⟩

theorem cones_childClosed (graph : DAG n) (roots : List (Fin graph.nodeCount)) :
    graph.ChildClosed (graph.cones roots) := by
  intro parent parentMembership child childMembership
  obtain ⟨root, rootMembership, parentMembership⟩ := Finset.mem_biUnion.mp parentMembership
  exact Finset.mem_biUnion.mpr ⟨root, rootMembership,
    graph.cone_childClosed root parent parentMembership child childMembership⟩

/-- A retained set of identities together with the reference-closure invariant. -/
structure Selection (graph : DAG n) where
  nodes : Finset (Fin graph.nodeCount)
  closed : graph.ChildClosed nodes

namespace Selection

variable {graph : DAG n}

/-- Increasing enumeration maps every new node to its unique old identity. -/
def oldIndex (selection : Selection graph) : Fin selection.nodes.card ↪o Fin graph.nodeCount :=
  selection.nodes.orderEmbOfFin rfl

/-- The inverse map is defined exactly on retained old identities. -/
def newIndex (selection : Selection graph) (old : Fin graph.nodeCount)
    (membership : old ∈ selection.nodes) : Fin selection.nodes.card :=
  (selection.nodes.orderIsoOfFin rfl).symm ⟨old, membership⟩

@[simp] theorem oldIndex_mem (selection : Selection graph) (index : Fin selection.nodes.card) :
    selection.oldIndex index ∈ selection.nodes := Finset.orderEmbOfFin_mem _ _ _

@[simp] theorem oldIndex_newIndex (selection : Selection graph) (old : Fin graph.nodeCount)
    (membership : old ∈ selection.nodes) :
    selection.oldIndex (selection.newIndex old membership) = old := by
  exact congrArg Subtype.val ((selection.nodes.orderIsoOfFin rfl).apply_symm_apply
    ⟨old, membership⟩)

@[simp] theorem newIndex_oldIndex (selection : Selection graph) (index : Fin selection.nodes.card) :
    selection.newIndex (selection.oldIndex index) (selection.oldIndex_mem index) = index := by
  apply selection.oldIndex.injective
  simp only [oldIndex_newIndex]

/-- Each reindexed live child precedes its reindexed parent. -/
def child (selection : Selection graph) (parent : Fin selection.nodes.card)
    (oldChild : Fin (selection.oldIndex parent).val)
    (membership : oldChild ∈ (graph.node (selection.oldIndex parent)).children) : Fin parent.val :=
  let newChild := selection.newIndex (graph.childIndex (selection.oldIndex parent) oldChild)
    (selection.closed _ (selection.oldIndex_mem parent) oldChild membership)
  ⟨newChild.val, (selection.oldIndex.lt_iff_lt).mp (by
    dsimp only [newChild]
    rw [oldIndex_newIndex]
    exact oldChild.isLt)⟩

/-- Reindexing a child and then recovering its old identity is exact. -/
theorem oldIndex_child (selection : Selection graph) (parent : Fin selection.nodes.card)
    (oldChild : Fin (selection.oldIndex parent).val)
    (membership : oldChild ∈ (graph.node (selection.oldIndex parent)).children) :
    selection.oldIndex ⟨(selection.child parent oldChild membership).val,
      Nat.lt_trans (selection.child parent oldChild membership).isLt parent.isLt⟩ =
        graph.childIndex (selection.oldIndex parent) oldChild := by
  exact selection.oldIndex_newIndex _ _

/-- Copy the selected table once, retaining the supplied root-list multiplicities. -/
def extract (selection : Selection graph) (roots : List (Fin graph.nodeCount))
    (rootMembership : ∀ root ∈ roots, root ∈ selection.nodes) : DAG n where
  nodeCount := selection.nodes.card
  node := fun index => (graph.node (selection.oldIndex index)).mapChildren (selection.child index)
  roots := roots.attach.map fun root => selection.newIndex root.val (rootMembership _ root.property)

@[simp] theorem extract_nodeCount (selection : Selection graph) (roots)
    (rootMembership : ∀ root ∈ roots, root ∈ selection.nodes) :
    (selection.extract roots rootMembership).nodeCount = selection.nodes.card := rfl

@[simp] theorem extract_root_length (selection : Selection graph) (roots)
    (rootMembership : ∀ root ∈ roots, root ∈ selection.nodes) :
    (selection.extract roots rootMembership).roots.length = roots.length := by
  simp [extract]

/-- The exact retained child incidence count at each stored node. -/
theorem extract_child_length (selection : Selection graph) (roots)
    (rootMembership : ∀ root ∈ roots, root ∈ selection.nodes) (index) :
    ((selection.extract roots rootMembership).node index).children.length =
      (graph.node (selection.oldIndex index)).children.length := by
  exact Gate.mapChildren_children_length _ _

/-- Every ordered child incidence recovers its original shared node identity. -/
theorem extract_children (selection : Selection graph) (roots)
    (rootMembership : ∀ root ∈ roots, root ∈ selection.nodes) (index) :
    ((selection.extract roots rootMembership).node index).children.map
        (fun child => selection.oldIndex ((selection.extract roots rootMembership).childIndex index child)) =
      (graph.node (selection.oldIndex index)).children.map
        (graph.childIndex (selection.oldIndex index)) := by
  exact Gate.mapChildren_children_map _ _ _ _ (selection.oldIndex_child index)

/-- Recovering old identities preserves the full output list, including duplicates. -/
theorem extract_roots (selection : Selection graph) (roots)
    (rootMembership : ∀ root ∈ roots, root ∈ selection.nodes) :
    (selection.extract roots rootMembership).roots.map selection.oldIndex = roots := by
  simp only [extract, List.map_map, Function.comp_def, oldIndex_newIndex]
  exact List.attach_map_subtype_val roots

/-- Every extracted node has exactly its original semantic value. -/
theorem extract_eval (selection : Selection graph) (roots)
    (rootMembership : ∀ root ∈ roots, root ∈ selection.nodes) (assignment : Assignment n)
    (index : Fin selection.nodes.card) :
    (selection.extract roots rootMembership).eval assignment index =
      graph.eval assignment (selection.oldIndex index) := by
  rw [(selection.extract roots rootMembership).eval_eq assignment index,
    graph.eval_eq assignment (selection.oldIndex index)]
  apply Gate.eval_mapChildren
  intro oldChild membership
  exact (selection.extract_eval roots rootMembership assignment
    ⟨(selection.child index oldChild membership).val,
      Nat.lt_trans (selection.child index oldChild membership).isLt index.isLt⟩).trans
    (congrArg (graph.eval assignment) (selection.oldIndex_child index oldChild membership))
termination_by index.val
decreasing_by exact (selection.child index oldChild membership).isLt

/-- The extracted output vector equals the original values at the requested roots. -/
theorem extract_outputValues (selection : Selection graph) (roots)
    (rootMembership : ∀ root ∈ roots, root ∈ selection.nodes) (assignment : Assignment n) :
    (selection.extract roots rootMembership).outputValues assignment =
      roots.map (graph.eval assignment) := by
  calc
    _ = (selection.extract roots rootMembership).roots.map
        (fun index => graph.eval assignment (selection.oldIndex index)) := by
      apply List.map_congr_left
      intro index _
      exact selection.extract_eval roots rootMembership assignment index
    _ = ((selection.extract roots rootMembership).roots.map selection.oldIndex).map
        (graph.eval assignment) := List.map_map.symm
    _ = roots.map (graph.eval assignment) :=
      congrArg (List.map (graph.eval assignment)) (selection.extract_roots roots rootMembership)

/-- Extraction cannot increase the number of distinct stored nodes. -/
theorem extract_nodeCount_le (selection : Selection graph) (roots)
    (rootMembership : ∀ root ∈ roots, root ∈ selection.nodes) :
    (selection.extract roots rootMembership).nodeCount ≤ graph.nodeCount :=
  card_finset_fin_le selection.nodes

end Selection

/-- Extract the exact union of any list of output cones. -/
def extractCones (graph : DAG n) (roots : List (Fin graph.nodeCount)) : DAG n :=
  let selection : Selection graph := ⟨graph.cones roots, graph.cones_childClosed roots⟩
  selection.extract roots (graph.root_mem_cones roots)

/-- Cone extraction retains one node per reachable old identity. -/
theorem extractCones_nodeCount (graph : DAG n) (roots : List (Fin graph.nodeCount)) :
    (graph.extractCones roots).nodeCount = (graph.cones roots).card := rfl

/-- Reindexing all requested cones preserves the observed vector. -/
theorem extractCones_outputValues (graph : DAG n) (roots : List (Fin graph.nodeCount))
    (assignment : Assignment n) :
    (graph.extractCones roots).outputValues assignment = roots.map (graph.eval assignment) := by
  exact Selection.extract_outputValues
    ⟨graph.cones roots, graph.cones_childClosed roots⟩ roots (graph.root_mem_cones roots) assignment

/-- Remove all nodes outside the current output cones. -/
def prune (graph : DAG n) : DAG n := graph.extractCones graph.roots

/-- Reachable-node pruning preserves all outputs and their multiplicity. -/
theorem prune_outputValues (graph : DAG n) (assignment : Assignment n) :
    graph.prune.outputValues assignment = graph.outputValues assignment :=
  graph.extractCones_outputValues graph.roots assignment

end DAG
end Controller.Decoder
