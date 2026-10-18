module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Decoder.Cone
public import Mathlib.Data.List.NodupEquivFin
public import Mathlib.Order.WellFounded

@[expose] public section

/-!
# Finite unordered decoder input

Raw channel and node numbers are checked before they enter finite types.
A source-elimination pass numbers every stored node exactly once, including
nodes outside the observed cones. Failure distinguishes malformed references
from directed cycles. Numbering preserves the simultaneous gate equations,
sharing, and ordered incidence lists. This list implementation specifies the
adapter; an indexed-array refinement supplies the separate linear cost theorem.
-/

namespace Controller.Decoder

/-- Bounded references without any assumed topological numbering. -/
structure UnorderedDAG (n : ℕ) where
  nodeCount : ℕ
  node : Fin nodeCount → Gate n nodeCount
  roots : List (Fin nodeCount)

namespace UnorderedDAG

variable {n : ℕ}

def Child (graph : UnorderedDAG n) (child parent : Fin graph.nodeCount) : Prop :=
  child ∈ (graph.node parent).children

/-- Well-foundedness of the child relation; on this finite universe it means no directed cycle. -/
def Acyclic (graph : UnorderedDAG n) : Prop := WellFounded graph.Child

theorem acyclic_iff_no_cycle (graph : UnorderedDAG n) :
    graph.Acyclic ↔ ∀ index, ¬ Relation.TransGen graph.Child index index := by
  constructor
  · intro acyclic index cycle
    exact acyclic.transGen.irrefl.irrefl index cycle
  · intro noCycle
    let : Std.Irrefl (Relation.TransGen graph.Child) := ⟨noCycle⟩
    exact (Finite.wellFounded_of_trans_of_irrefl
      (Relation.TransGen graph.Child)).mono (fun _ _ => Relation.TransGen.single)

/-- A node is ready when no listed child remains unnumbered. -/
def ready (graph : UnorderedDAG n) (remaining : List (Fin graph.nodeCount))
    (parent : Fin graph.nodeCount) : Bool :=
  (graph.node parent).children.all fun child => !remaining.contains child

theorem ready_iff (graph : UnorderedDAG n) (remaining) (parent) :
    graph.ready remaining parent = true ↔
      ∀ child ∈ (graph.node parent).children, child ∉ remaining := by
  simp [ready, List.all_eq_true]

/-- A permutation of the remaining nodes with all internal dependencies earlier. -/
structure Schedule (graph : UnorderedDAG n) (remaining : List (Fin graph.nodeCount)) where
  order : List (Fin graph.nodeCount)
  perm : order.Perm remaining
  earlier : ∀ parent ∈ remaining, ∀ child ∈ (graph.node parent).children,
    child ∈ remaining → order.idxOf child < order.idxOf parent

namespace Schedule

variable {graph : UnorderedDAG n} {remaining : List (Fin graph.nodeCount)}

def empty (graph : UnorderedDAG n) : Schedule graph [] where
  order := []
  perm := .refl _
  earlier := by simp

/-- Prepend a ready node without changing any remaining node identity. -/
def prepend (tail : Schedule graph (remaining.erase chosen))
    (distinct : remaining.Nodup) (present : chosen ∈ remaining)
    (isReady : graph.ready remaining chosen = true) : Schedule graph remaining where
  order := chosen :: tail.order
  perm := (tail.perm.cons chosen).trans (List.perm_cons_erase present).symm
  earlier := by
    intro parent parentMembership child childMembership childRemaining
    by_cases parentEq : parent = chosen
    · subst parent
      exact False.elim ((graph.ready_iff remaining chosen).mp isReady
        child childMembership childRemaining)
    · have parentTail : parent ∈ remaining.erase chosen :=
        distinct.mem_erase_iff.mpr ⟨parentEq, parentMembership⟩
      by_cases childEq : child = chosen
      · subst child
        rw [List.idxOf_cons_self, List.idxOf_cons_ne _ (Ne.symm parentEq)]
        exact Nat.zero_lt_succ _
      · rw [List.idxOf_cons_ne _ (Ne.symm childEq), List.idxOf_cons_ne _ (Ne.symm parentEq)]
        exact Nat.succ_lt_succ (tail.earlier parent parentTail child childMembership
          (distinct.mem_erase_iff.mpr ⟨childEq, childRemaining⟩))

end Schedule

/-- Finite source elimination; the fuel bounds the number of stored nodes removed. -/
def schedule (graph : UnorderedDAG n) : (fuel : ℕ) →
    (remaining : List (Fin graph.nodeCount)) → remaining.Nodup → Option (Schedule graph remaining)
  | _, [], _ => some (Schedule.empty graph)
  | 0, _ :: _, _ => none
  | fuel + 1, first :: rest, distinct =>
      match found : (first :: rest).find? (graph.ready (first :: rest)) with
      | none => none
      | some chosen =>
          let present := List.mem_of_find?_eq_some found
          let isReady := List.find?_some found
          (graph.schedule fuel ((first :: rest).erase chosen) (distinct.erase chosen)).map
            fun tail => tail.prepend distinct present isReady

/-- Every nonempty remainder of an acyclic graph contains a ready node. -/
theorem exists_ready (graph : UnorderedDAG n) (acyclic : graph.Acyclic)
    (remaining : List (Fin graph.nodeCount)) (nonempty : remaining ≠ []) :
    ∃ chosen ∈ remaining, graph.ready remaining chosen = true := by
  have setNonempty : ({index | index ∈ remaining} : Set (Fin graph.nodeCount)).Nonempty := by
    obtain ⟨first, rest, rfl⟩ := List.exists_cons_of_ne_nil nonempty
    exact ⟨first, by simp⟩
  obtain ⟨chosen, present, minimal⟩ := acyclic.has_min {index | index ∈ remaining} setNonempty
  refine ⟨chosen, present, (graph.ready_iff remaining chosen).mpr ?_⟩
  intro child childMembership childRemaining
  exact minimal child childRemaining childMembership

/-- Source elimination succeeds for every finite acyclic input when all nodes are charged. -/
theorem schedule_isSome (graph : UnorderedDAG n) (acyclic : graph.Acyclic) :
    ∀ fuel remaining distinct, remaining.length ≤ fuel →
      (graph.schedule fuel remaining distinct).isSome = true := by
  intro fuel
  induction fuel with
  | zero =>
      intro remaining distinct bound
      have : remaining = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero bound)
      subst remaining
      rfl
  | succ fuel inductionHypothesis =>
      intro remaining distinct bound
      cases remaining with
      | nil => rfl
      | cons first rest =>
          obtain ⟨chosen, present, isReady⟩ := graph.exists_ready acyclic (first :: rest) (by simp)
          simp only [schedule]
          split
          · rename_i absent
            exact False.elim ((List.find?_eq_none.mp absent chosen present) isReady)
          · rename_i selected found
            have selectedPresent := List.mem_of_find?_eq_some found
            have smaller : ((first :: rest).erase selected).length ≤ fuel := by
              have lengthErase := List.length_erase_add_one selectedPresent
              omega
            simpa only [Option.isSome_map] using
              inductionHypothesis ((first :: rest).erase selected) (distinct.erase selected) smaller

/-- A complete topological numbering of the original finite identities. -/
structure Numbering (graph : UnorderedDAG n) where
  order : List (Fin graph.nodeCount)
  distinct : order.Nodup
  complete : ∀ index, index ∈ order
  earlier : ∀ parent child, child ∈ (graph.node parent).children →
    order.idxOf child < order.idxOf parent

namespace Numbering

variable {graph : UnorderedDAG n}

def ofSchedule (numbered : Schedule graph (List.finRange graph.nodeCount)) : Numbering graph where
  order := numbered.order
  distinct := numbered.perm.nodup_iff.mpr (List.nodup_finRange _)
  complete := fun index => numbered.perm.mem_iff.mpr (List.mem_finRange index)
  earlier := fun parent child membership => numbered.earlier parent (List.mem_finRange parent)
    child membership (List.mem_finRange child)

/-- A bijection, rather than an unfolding, records the new and old node identities. -/
def indices (numbering : Numbering graph) : Fin numbering.order.length ≃ Fin graph.nodeCount :=
  numbering.distinct.getEquivOfForallMemList numbering.order numbering.complete

def oldIndex (numbering : Numbering graph) := numbering.indices

def newIndex (numbering : Numbering graph) := numbering.indices.symm

@[simp] theorem newIndex_val (numbering : Numbering graph) (index) :
    (numbering.newIndex index).val = numbering.order.idxOf index := rfl

@[simp] theorem oldIndex_newIndex (numbering : Numbering graph) (index) :
    numbering.oldIndex (numbering.newIndex index) = index := numbering.indices.apply_symm_apply index

@[simp] theorem newIndex_oldIndex (numbering : Numbering graph) (index) :
    numbering.newIndex (numbering.oldIndex index) = index := numbering.indices.symm_apply_apply index

theorem length_eq_nodeCount (numbering : Numbering graph) :
    numbering.order.length = graph.nodeCount := by
  simpa only [Fintype.card_fin] using Fintype.card_congr numbering.indices

def child (numbering : Numbering graph) (parent : Fin numbering.order.length)
    (oldChild : Fin graph.nodeCount)
    (membership : oldChild ∈ (graph.node (numbering.oldIndex parent)).children) : Fin parent.val :=
  ⟨(numbering.newIndex oldChild).val, by
    have earlier := numbering.earlier (numbering.oldIndex parent) oldChild membership
    have parentIndex : numbering.order.idxOf (numbering.oldIndex parent) = parent.val :=
      congrArg Fin.val (numbering.newIndex_oldIndex parent)
    simpa only [newIndex_val, parentIndex] using earlier⟩

/-- Reindex every gate and every output incidence through the same bijection. -/
def toDAG (numbering : Numbering graph) : DAG n where
  nodeCount := numbering.order.length
  node := fun parent => (graph.node (numbering.oldIndex parent)).mapChildren (numbering.child parent)
  roots := graph.roots.map numbering.newIndex

theorem oldIndex_child (numbering : Numbering graph) (parent : Fin numbering.order.length)
    (oldChild : Fin graph.nodeCount)
    (membership : oldChild ∈ (graph.node (numbering.oldIndex parent)).children) :
    numbering.oldIndex (numbering.toDAG.childIndex parent (numbering.child parent oldChild membership)) =
      oldChild := numbering.oldIndex_newIndex oldChild

/-- An accepted numbering rules out every directed cycle. -/
theorem acyclic (numbering : Numbering graph) : graph.Acyclic := by
  exact (measure (fun index => (numbering.newIndex index).val)).wf.mono
    (fun parent child membership => numbering.earlier child parent membership)

/-- The adapter keeps exactly one stored node for every original stored identity. -/
theorem toDAG_nodeCount (numbering : Numbering graph) :
    numbering.toDAG.nodeCount = graph.nodeCount := numbering.length_eq_nodeCount

/-- Child incidence counts are unchanged, including repeated references. -/
theorem toDAG_child_length (numbering : Numbering graph) (parent) :
    (numbering.toDAG.node parent).children.length =
      (graph.node (numbering.oldIndex parent)).children.length :=
  Gate.mapChildren_children_length _ _

/-- The original ordered child identities, including all repeated references, are recovered exactly. -/
theorem toDAG_children (numbering : Numbering graph) (parent) :
    (numbering.toDAG.node parent).children.map
        (fun child => numbering.oldIndex (numbering.toDAG.childIndex parent child)) =
      (graph.node (numbering.oldIndex parent)).children := by
  have mapped := Gate.mapChildren_children_map (graph.node (numbering.oldIndex parent))
    (numbering.child parent) (fun child => numbering.oldIndex (numbering.toDAG.childIndex parent child))
    id (numbering.oldIndex_child parent)
  exact mapped.trans (List.map_id _)

/-- The ordered root list is recovered exactly, including repeated roots. -/
theorem toDAG_roots (numbering : Numbering graph) :
    numbering.toDAG.roots.map numbering.oldIndex = graph.roots := by
  simp [toDAG, List.map_map, Function.comp_def]

end Numbering

/-- Compute a complete numbering, rejecting cycles anywhere in the stored graph. -/
def number? (graph : UnorderedDAG n) : Option (Numbering graph) :=
  (graph.schedule graph.nodeCount (List.finRange graph.nodeCount) (List.nodup_finRange _)).map
    Numbering.ofSchedule

theorem number?_isSome (graph : UnorderedDAG n) (acyclic : graph.Acyclic) :
    graph.number?.isSome = true := by
  simpa only [number?, Option.isSome_map] using graph.schedule_isSome acyclic graph.nodeCount
    (List.finRange graph.nodeCount) (List.nodup_finRange _) (by simp)

/-- Successful numbering and finite acyclicity are equivalent. -/
theorem number?_eq_none_iff (graph : UnorderedDAG n) : graph.number? = none ↔ ¬graph.Acyclic := by
  constructor
  · intro rejected acyclic
    have accepted := graph.number?_isSome acyclic
    simp [rejected] at accepted
  · intro cyclic
    cases result : graph.number? with
    | none => rfl
    | some numbering => exact False.elim (cyclic numbering.acyclic)

/-- Raw gate semantics are simultaneous equations on the shared node table. -/
def Evaluates (graph : UnorderedDAG n) (assignment : Assignment n)
    (values : Fin graph.nodeCount → Bool) : Prop :=
  ∀ index, values index = (graph.node index).eval assignment values

namespace Numbering

variable {graph : UnorderedDAG n}

/-- Every valuation satisfying the original equations agrees with topological evaluation. -/
theorem eval_eq_of_equations (numbering : Numbering graph) (assignment : Assignment n)
    (values : Fin graph.nodeCount → Bool) (equations : graph.Evaluates assignment values)
    (index : Fin numbering.order.length) :
    numbering.toDAG.eval assignment index = values (numbering.oldIndex index) := by
  rw [numbering.toDAG.eval_eq assignment index, equations (numbering.oldIndex index)]
  apply Gate.eval_mapChildren
  intro oldChild membership
  exact (numbering.eval_eq_of_equations assignment values equations
    ⟨(numbering.child index oldChild membership).val,
      Nat.lt_trans (numbering.child index oldChild membership).isLt index.isLt⟩).trans
    (congrArg values (numbering.oldIndex_child index oldChild membership))
termination_by index.val
decreasing_by exact (numbering.child index oldChild membership).isLt

def values (numbering : Numbering graph) (assignment : Assignment n) : Fin graph.nodeCount → Bool :=
  fun old => numbering.toDAG.eval assignment (numbering.newIndex old)

/-- Topological evaluation supplies a solution to every original gate equation. -/
theorem values_evaluate (numbering : Numbering graph) (assignment : Assignment n) :
    graph.Evaluates assignment (numbering.values assignment) := by
  intro old
  unfold values
  rw [numbering.toDAG.eval_eq assignment (numbering.newIndex old)]
  change ((graph.node (numbering.oldIndex (numbering.newIndex old))).mapChildren
    (numbering.child (numbering.newIndex old))).eval assignment _ = _
  have mapped := Gate.eval_mapChildren (graph.node (numbering.oldIndex (numbering.newIndex old)))
    (numbering.child (numbering.newIndex old)) assignment
    (fun child => numbering.toDAG.eval assignment (numbering.newIndex child))
    (fun child => numbering.toDAG.eval assignment (numbering.toDAG.childIndex _ child))
    (by intro child membership; rfl)
  simpa only [oldIndex_newIndex] using mapped

/-- An accepted acyclic table has exactly one total node valuation for fixed channel values. -/
theorem existsUnique_evaluation (numbering : Numbering graph) (assignment : Assignment n) :
    ∃! values, graph.Evaluates assignment values := by
  refine ⟨numbering.values assignment, numbering.values_evaluate assignment, ?_⟩
  intro values equations
  funext old
  have agreement := numbering.eval_eq_of_equations assignment values equations (numbering.newIndex old)
  simpa only [Numbering.values, oldIndex_newIndex] using agreement.symm

/-- Numbering choices cannot change the original node values. -/
theorem values_independent (first second : Numbering graph) (assignment : Assignment n) :
    first.values assignment = second.values assignment := by
  exact (second.existsUnique_evaluation assignment).unique
    (first.values_evaluate assignment) (second.values_evaluate assignment)

/-- The requested output vector is the original ordered list of root values. -/
theorem outputValues_eq (numbering : Numbering graph) (assignment : Assignment n)
    (values : Fin graph.nodeCount → Bool) (equations : graph.Evaluates assignment values) :
    numbering.toDAG.outputValues assignment = graph.roots.map values := by
  calc
    _ = graph.roots.map (fun old => numbering.toDAG.eval assignment (numbering.newIndex old)) :=
      List.map_map
    _ = graph.roots.map values := by
      apply List.map_congr_left
      intro old _
      exact (numbering.eval_eq_of_equations assignment values equations (numbering.newIndex old)).trans
        (congrArg values (numbering.oldIndex_newIndex old))

end Numbering
end UnorderedDAG

/-- Untrusted natural-number channel and node references. -/
inductive RawGate where
  | zero
  | input (channel : ℕ)
  | disj (children : List ℕ)
  | guard (child : ℕ) (labels : List ℕ)
  | liveAnd (left right : ℕ)
  deriving DecidableEq, Repr

namespace RawGate

def children : RawGate → List ℕ
  | .zero | .input _ => []
  | .disj refs => refs
  | .guard child _ => [child]
  | .liveAnd left right => [left, right]

def channels : RawGate → List ℕ
  | .input channel => [channel]
  | .guard _ labels => labels
  | _ => []

def WellFormed (gate : RawGate) (n m : ℕ) : Prop :=
  (∀ child ∈ gate.children, child < m) ∧ (∀ channel ∈ gate.channels, channel < n)

instance (gate : RawGate) (n m : ℕ) : Decidable (gate.WellFormed n m) := by
  unfold WellFormed
  infer_instance

/-- Bounds checking changes reference types, not gate constructors or incidence lists. -/
def toGate (gate : RawGate) (valid : gate.WellFormed n m) : Gate n m := by
  cases gate with
  | zero => exact .zero
  | input channel => exact .input ⟨channel, valid.2 channel (by simp [channels])⟩
  | disj refs => exact .disj (refs.attach.map fun child =>
      ⟨child.val, valid.1 child.val child.property⟩)
  | guard child labels =>
      exact .guard ⟨child, valid.1 child (by simp [children])⟩
        (labels.attach.map fun label => ⟨label.val, valid.2 label.val label.property⟩)
  | liveAnd left right =>
      exact .liveAnd ⟨left, valid.1 left (by simp [children])⟩
        ⟨right, valid.1 right (by simp [children])⟩

/-- Erase only the finite-type bounds, preserving every incidence. -/
def ofGate (gate : Gate n m) : RawGate :=
  match gate with
  | .zero => .zero
  | .input channel => .input channel.val
  | .disj refs => .disj (refs.map Fin.val)
  | .guard child labels => .guard child.val (labels.map Fin.val)
  | .liveAnd left right => .liveAnd left.val right.val

/-- The validated gate decodes to the exact original raw syntax. -/
theorem ofGate_toGate (gate : RawGate) (valid : gate.WellFormed n m) :
    ofGate (gate.toGate valid) = gate := by
  cases gate <;> simp [toGate, ofGate, List.map_map, Function.comp_def]

end RawGate

/-- Stored raw nodes are an array; outputs are a separate ordered incidence list. -/
structure RawDAG where
  nodes : Array RawGate
  roots : List ℕ
  deriving Repr

inductive AdapterError where
  | malformed
  | cyclic
  deriving DecidableEq, Repr

namespace RawDAG

def WellFormed (raw : RawDAG) (n : ℕ) : Prop :=
  (∀ index : Fin raw.nodes.size, raw.nodes[index.val].WellFormed n raw.nodes.size) ∧
    (∀ root ∈ raw.roots, root < raw.nodes.size)

instance (raw : RawDAG) (n : ℕ) : Decidable (raw.WellFormed n) := by
  unfold WellFormed
  infer_instance

def toUnordered (raw : RawDAG) (valid : raw.WellFormed n) : UnorderedDAG n where
  nodeCount := raw.nodes.size
  node := fun index => (raw.nodes[index.val]).toGate (valid.1 index)
  roots := raw.roots.attach.map fun root => ⟨root.val, valid.2 root.val root.property⟩

/-- Every stored validated gate has the exact raw constructor and ordered references. -/
theorem toUnordered_node (raw : RawDAG) (valid : raw.WellFormed n) (index) :
    RawGate.ofGate ((raw.toUnordered valid).node index) = raw.nodes[index.val] :=
  RawGate.ofGate_toGate _ _

theorem toUnordered_roots (raw : RawDAG) (valid : raw.WellFormed n) :
    (raw.toUnordered valid).roots.map Fin.val = raw.roots := by
  simp only [toUnordered, List.map_map, Function.comp_def]
  exact List.attach_map_subtype_val raw.roots

/-- Accepted data carry both reference validation and the verified identity bijection. -/
structure Accepted (raw : RawDAG) (n : ℕ) where
  valid : raw.WellFormed n
  numbering : UnorderedDAG.Numbering (raw.toUnordered valid)

def Accepted.toDAG {raw : RawDAG} {n : ℕ} (accepted : Accepted raw n) : DAG n :=
  accepted.numbering.toDAG

/-- Validate all stored input, then topologically number it without unfolding sharing. -/
def adapt (raw : RawDAG) (n : ℕ) : Except AdapterError (Accepted raw n) :=
  if valid : raw.WellFormed n then
    match (raw.toUnordered valid).number? with
    | none => .error .cyclic
    | some numbering => .ok ⟨valid, numbering⟩
  else .error .malformed

theorem adapt_malformed (raw : RawDAG) (invalid : ¬raw.WellFormed n) :
    raw.adapt n = .error .malformed := by
  simp [adapt, invalid]

/-- Malformed-reference rejection occurs exactly when bounds validation fails. -/
theorem adapt_malformed_iff (raw : RawDAG) :
    raw.adapt n = .error .malformed ↔ ¬raw.WellFormed n := by
  by_cases valid : raw.WellFormed n
  · simp only [adapt, dite_eq_left valid]
    cases (raw.toUnordered valid).number? <;> simp [valid]
  · simp [adapt, valid]

/-- A cycle anywhere in a well-formed stored table is explicitly rejected. -/
theorem adapt_cyclic (raw : RawDAG) (valid : raw.WellFormed n)
    (cyclic : ¬(raw.toUnordered valid).Acyclic) : raw.adapt n = .error .cyclic := by
  simp [adapt, valid, (raw.toUnordered valid).number?_eq_none_iff.mpr cyclic]

/-- Every finite well-formed acyclic raw input is accepted. -/
theorem adapt_complete (raw : RawDAG) (valid : raw.WellFormed n)
    (acyclic : (raw.toUnordered valid).Acyclic) :
    ∃ accepted, raw.adapt n = .ok accepted := by
  have succeeds := (raw.toUnordered valid).number?_isSome acyclic
  cases found : (raw.toUnordered valid).number? with
  | none => simp [found] at succeeds
  | some numbering => exact ⟨⟨valid, numbering⟩, by simp [adapt, valid, found]⟩

/-- Cycle rejection occurs exactly for a well-formed input whose finite child relation is cyclic. -/
theorem adapt_cyclic_iff (raw : RawDAG) :
    raw.adapt n = .error .cyclic ↔
      ∃ valid : raw.WellFormed n, ¬(raw.toUnordered valid).Acyclic := by
  constructor
  · intro rejected
    by_cases valid : raw.WellFormed n
    · refine ⟨valid, ?_⟩
      intro acyclic
      obtain ⟨accepted, success⟩ := raw.adapt_complete valid acyclic
      rw [success] at rejected
      contradiction
    · simp [adapt, valid] at rejected
  · rintro ⟨valid, cyclic⟩
    exact raw.adapt_cyclic valid cyclic

/-- A nonempty directed cycle gives the explicit cycle error. -/
theorem adapt_cycle (raw : RawDAG) (valid : raw.WellFormed n) (index)
    (cycle : Relation.TransGen (raw.toUnordered valid).Child index index) :
    raw.adapt n = .error .cyclic := by
  apply raw.adapt_cyclic valid
  intro acyclic
  exact ((raw.toUnordered valid).acyclic_iff_no_cycle.mp acyclic) index cycle

/-- Accepted root values agree with every solution of the validated raw gate equations. -/
theorem Accepted.outputValues_eq {raw : RawDAG} {n : ℕ} (accepted : Accepted raw n)
    (assignment : Assignment n) (values : Fin raw.nodes.size → Bool)
    (equations : (raw.toUnordered accepted.valid).Evaluates assignment values) :
    accepted.toDAG.outputValues assignment =
      (raw.toUnordered accepted.valid).roots.map values :=
  accepted.numbering.outputValues_eq assignment values equations

/-- All free channel values determine exactly one total valuation of an accepted raw table. -/
theorem Accepted.existsUnique_evaluation {raw : RawDAG} {n : ℕ} (accepted : Accepted raw n)
    (assignment : Assignment n) :
    ∃! values, (raw.toUnordered accepted.valid).Evaluates assignment values :=
  accepted.numbering.existsUnique_evaluation assignment

end RawDAG
end Controller.Decoder
