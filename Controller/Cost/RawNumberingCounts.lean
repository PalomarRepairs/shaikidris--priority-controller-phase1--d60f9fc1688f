module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Decoder.Raw
public import Controller.Cost.ForestIndexedOperands
public import Controller.Cost.UniformDAGSource
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# Original incidence counts under topological numbering

The rows preserve constructors and every ordered child and guard occurrence.
The numbering is a bijection on stored nodes, so its permutation changes
neither incidence totals nor root-list length. These are size identities;
executing the numbering and copying the source have separate cost contracts.
-/

namespace Controller.Cost.RawNumberingCounts

open Controller.Decoder Controller.Cost.ForestIndexedOperands

variable {n : Nat}

/-- Sum every stored node weight once in the produced topological order. -/
theorem numbering_sum {M : Type*} [AddCommMonoid M]
    (graph : UnorderedDAG n) (numbering : graph.Numbering)
    (weight : Fin graph.nodeCount → M) :
    ((List.finRange numbering.order.length).map
      (fun index => weight (numbering.oldIndex index))).sum =
      ((List.finRange graph.nodeCount).map weight).sum := by
  simpa only [← List.ofFn_eq_map, List.sum_ofFn, UnorderedDAG.Numbering.oldIndex]
    using numbering.indices.sum_comp weight

/-- Serialized rows retain all reference occurrences before word encoding. -/
def rowOfGate : RawGate → Row
  | .zero => ⟨0, 0, [], []⟩
  | .input channel => ⟨1, channel, [], []⟩
  | .disj children => ⟨2, 0, children, []⟩
  | .guard child labels => ⟨3, child, [child], labels⟩
  | .liveAnd left right => ⟨4, left, [left, right], []⟩

def rawRows (raw : RawDAG) : List Row := raw.nodes.toList.map rowOfGate

def rawChildren (raw : RawDAG) : Nat := (rowChildren (rawRows raw)).length

def rawGuards (raw : RawDAG) : Nat := (rowGuards (rawRows raw)).length

@[simp] theorem rowOfGate_children (gate : RawGate) :
    (rowOfGate gate).children = gate.children := by cases gate <;> rfl

/-- Validating bounds retains the constructor and both occurrence lists. -/
theorem rowOfGate_matches (gate : RawGate) (valid : gate.WellFormed n m) :
    (rowOfGate gate).Matches (gate.toGate valid) := by
  cases gate <;> simp [rowOfGate, Row.Matches, RawGate.toGate, Gate.children,
    Gate.guardLabels, List.map_map, Function.comp_def]

theorem rowOfGate_head (gate : RawGate) (valid : gate.WellFormed n m) :
    (rowOfGate gate).head = UniformDAGSource.typedHead (gate.toGate valid) := by
  cases gate <;> rfl

theorem erased_children_length (gate : Gate n m) :
    (RawGate.ofGate gate).children.length = gate.children.length := by
  cases gate <;> simp [RawGate.ofGate, RawGate.children, Gate.children]

theorem erased_guards_length (gate : Gate n m) :
    (rowOfGate (RawGate.ofGate gate)).guards.length = gate.guardLabels.length := by
  cases gate <;> simp [RawGate.ofGate, rowOfGate, Gate.guardLabels]

theorem rawRows_ofFn (raw : RawDAG) :
    rawRows raw = List.ofFn (fun index : Fin raw.nodes.size => rowOfGate raw.nodes[index.val]) := by
  apply List.ext_getElem
  · simp [rawRows]
  · intro index left right
    simp only [rawRows, List.getElem_map, Array.getElem_toList, List.getElem_ofFn]

theorem rawChildren_sum (raw : RawDAG) :
    rawChildren raw = ((List.finRange raw.nodes.size).map
      (fun index => raw.nodes[index.val].children.length)).sum := by
  simp only [rawChildren, rowChildren, rawRows_ofFn, List.length_flatMap,
    List.ofFn_eq_map, List.map_map, Function.comp_def, rowOfGate_children]

theorem rawGuards_sum (raw : RawDAG) :
    rawGuards raw = ((List.finRange raw.nodes.size).map
      (fun index => (rowOfGate raw.nodes[index.val]).guards.length)).sum := by
  simp only [rawGuards, rowGuards, rawRows_ofFn, List.length_flatMap,
    List.ofFn_eq_map, List.map_map, Function.comp_def]

/-- Reordering stored nodes does not change the sum of child occurrences. -/
theorem numbered_children (raw : RawDAG) (valid : raw.WellFormed n)
    (numbering : (raw.toUnordered valid).Numbering) :
    numbering.toDAG.childIncidences = rawChildren raw := by
  have pointwise : ∀ index : Fin numbering.order.length,
      (numbering.toDAG.node index).children.length =
      raw.nodes[(numbering.oldIndex index).val].children.length := by
    intro index
    have erased := erased_children_length ((raw.toUnordered valid).node (numbering.oldIndex index))
    rw [raw.toUnordered_node valid] at erased
    exact (numbering.toDAG_child_length index).trans erased.symm
  calc
    numbering.toDAG.childIncidences =
        ((List.finRange numbering.order.length).map
          (fun index => raw.nodes[(numbering.oldIndex index).val].children.length)).sum := by
      change (List.ofFn (fun index : Fin numbering.order.length =>
        (numbering.toDAG.node index).children.length)).sum = _
      simpa only [List.ofFn_eq_map] using congrArg
        (fun f : Fin numbering.order.length → Nat => (List.ofFn f).sum) (funext pointwise)
    _ = rawChildren raw := (numbering_sum (raw.toUnordered valid) numbering
      (fun index => raw.nodes[index.val].children.length)).trans (rawChildren_sum raw).symm

/-- Guard occurrences remain occurrences even when their channel labels repeat. -/
theorem numbered_guards (raw : RawDAG) (valid : raw.WellFormed n)
    (numbering : (raw.toUnordered valid).Numbering) :
    numbering.toDAG.guardIncidences = rawGuards raw := by
  have pointwise : ∀ index : Fin numbering.order.length,
      (numbering.toDAG.node index).guardLabels.length =
      (rowOfGate raw.nodes[(numbering.oldIndex index).val]).guards.length := by
    intro index
    change (((raw.toUnordered valid).node (numbering.oldIndex index)).mapChildren
      (numbering.child index)).guardLabels.length = _
    rw [Gate.mapChildren_guardLabels]
    have erased := erased_guards_length ((raw.toUnordered valid).node (numbering.oldIndex index))
    rw [raw.toUnordered_node valid] at erased
    exact erased.symm
  calc
    numbering.toDAG.guardIncidences =
        ((List.finRange numbering.order.length).map
          (fun index => (rowOfGate raw.nodes[(numbering.oldIndex index).val]).guards.length)).sum := by
      change (List.ofFn (fun index : Fin numbering.order.length =>
        (numbering.toDAG.node index).guardLabels.length)).sum = _
      simpa only [List.ofFn_eq_map] using congrArg
        (fun f : Fin numbering.order.length → Nat => (List.ofFn f).sum) (funext pointwise)
    _ = rawGuards raw := (numbering_sum (raw.toUnordered valid) numbering
      (fun index => (rowOfGate raw.nodes[index.val]).guards.length)).trans (rawGuards_sum raw).symm

/-- Root occurrences keep their original positions, including repeated roots. -/
theorem numbered_roots (raw : RawDAG) (valid : raw.WellFormed n)
    (numbering : (raw.toUnordered valid).Numbering) :
    numbering.toDAG.roots.length = raw.roots.length := by
  have roots := raw.toUnordered_roots valid
  have counts := congrArg List.length roots
  simpa only [UnorderedDAG.Numbering.toDAG, List.length_map] using counts

/-- The source-relative representation counts charge every stored incidence once. -/
theorem numbered_size (raw : RawDAG) (valid : raw.WellFormed n)
    (numbering : (raw.toUnordered valid).Numbering) :
    numbering.toDAG.countedSize =
      n + raw.nodes.size + rawChildren raw + rawGuards raw + raw.roots.length := by
  have nodes := numbering.toDAG_nodeCount
  change numbering.toDAG.nodeCount = raw.nodes.size at nodes
  have children := numbered_children raw valid numbering
  have guards := numbered_guards raw valid numbering
  have roots := numbered_roots raw valid numbering
  simp only [DAG.countedSize_eq]
  omega

end Controller.Cost.RawNumberingCounts
