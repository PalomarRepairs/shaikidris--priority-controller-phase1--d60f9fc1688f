module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Basic.Assignments
public import Controller.Basic.Sizes
public import Mathlib.Data.Fintype.Card

@[expose] public section

/-!
# Finite topological decoder syntax

A node may reference only earlier nodes. Child and guard lists retain repeated
incidences, and roots are stored separately. The finite dependent table is a
semantic representation; an indexed-array execution refinement and raw-input
adapter have their own contracts.
-/

namespace Controller.Decoder

/-- A gate whose live children are among the preceding `available` nodes. -/
inductive Gate (n available : ℕ) where
  | zero : Gate n available
  | input (channel : Channel n) : Gate n available
  | disj (children : List (Fin available)) : Gate n available
  | guard (child : Fin available) (labels : List (Channel n)) : Gate n available
  | liveAnd (left right : Fin available) : Gate n available
  deriving DecidableEq, Repr

namespace Gate

variable {n available : ℕ}

/-- Live child references, with their original multiplicities. -/
def children : Gate n available → List (Fin available)
  | .zero => []
  | .input _ => []
  | .disj refs => refs
  | .guard child _ => [child]
  | .liveAnd left right => [left, right]

/-- Negative channel incidences belonging to this gate itself. -/
def guardLabels : Gate n available → List (Channel n)
  | .guard _ labels => labels
  | _ => []

/-- Channel incidences read directly at a gate, before following live children. -/
def directChannels : Gate n available → List (Channel n)
  | .input channel => [channel]
  | .guard _ labels => labels
  | _ => []

/-- Whether this represented node is a binary conjunction of two live children. -/
def isLiveAnd : Gate n available → Bool
  | .liveAnd _ _ => true
  | _ => false

/-- The original guarded language excludes the live-AND constructor. -/
def IsGuarded (gate : Gate n available) : Prop := gate.isLiveAnd = false

/-- Evaluate one gate using channel values and values for the earlier nodes. -/
def eval (gate : Gate n available) (assignment : Assignment n)
    (earlier : Fin available → Bool) : Bool :=
  match gate with
  | .zero => false
  | .input channel => assignment channel
  | .disj refs => refs.any earlier
  | .guard child labels => earlier child && !(labels.any assignment)
  | .liveAnd left right => earlier left && earlier right

end Gate

/-- A finite topological table with an explicit ordered list of observed roots. -/
structure DAG (n : ℕ) where
  nodeCount : ℕ
  node : (index : Fin nodeCount) → Gate n index.val
  roots : List (Fin nodeCount)

namespace DAG

variable {n : ℕ}

/-- Embed an earlier-node reference in the complete node-index type. -/
def childIndex (graph : DAG n) (parent : Fin graph.nodeCount)
    (child : Fin parent.val) : Fin graph.nodeCount :=
  ⟨child.val, Nat.lt_trans child.isLt parent.isLt⟩

/-- A child embedding preserves the numerical index. -/
@[simp] theorem childIndex_val (graph : DAG n) (parent : Fin graph.nodeCount)
    (child : Fin parent.val) : (graph.childIndex parent child).val = child.val := rfl

/-- Every represented child precedes its parent. -/
theorem childIndex_lt (graph : DAG n) (parent : Fin graph.nodeCount)
    (child : Fin parent.val) : (graph.childIndex parent child).val < parent.val :=
  child.isLt

/-- All represented nodes belong to the original guarded language. -/
def Guarded (graph : DAG n) : Prop := ∀ index, (graph.node index).IsGuarded

/-- Child occurrences in the stored table; shared references remain occurrences. -/
def childIncidences (graph : DAG n) : ℕ :=
  (List.ofFn fun index : Fin graph.nodeCount => (graph.node index).children.length).sum

/-- Negative channel occurrences in the stored table. -/
def guardIncidences (graph : DAG n) : ℕ :=
  (List.ofFn fun index : Fin graph.nodeCount => (graph.node index).guardLabels.length).sum

/-- Distinct stored nodes using binary live conjunction. -/
def liveAndNodes (graph : DAG n) : Finset (Fin graph.nodeCount) :=
  Finset.univ.filter fun index => (graph.node index).isLiveAnd = true

/-- The live-conjunction parameter counts nodes, rather than unfolded uses. -/
def liveAndCount (graph : DAG n) : ℕ := graph.liveAndNodes.card

/-- There cannot be more live-AND nodes than represented nodes. -/
theorem liveAndCount_le_nodeCount (graph : DAG n) :
    graph.liveAndCount ≤ graph.nodeCount :=
  card_finset_fin_le graph.liveAndNodes

/-- Size components for the common decoder resource interface. -/
def size (graph : DAG n) : DecoderSize where
  channels := n
  nodes := graph.nodeCount
  children := graph.childIncidences
  guards := graph.guardIncidences
  roots := graph.roots.length

/-- Decoder size charges channels, nodes, child, guard and root incidences. -/
def countedSize (graph : DAG n) : ℕ := graph.size.total

/-- The total includes every incidence retained by the syntax. -/
theorem countedSize_eq (graph : DAG n) :
    graph.countedSize =
      n + graph.nodeCount + graph.childIncidences + graph.guardIncidences + graph.roots.length :=
  rfl

/-- The empty topological table has no observed roots. -/
def empty (n : ℕ) : DAG n where
  nodeCount := 0
  node := fun index => Fin.elim0 index
  roots := []

/-- Append one gate while retaining the old output list and all existing node identities. -/
def append (graph : DAG n) (gate : Gate n graph.nodeCount) : DAG n where
  nodeCount := graph.nodeCount + 1
  node := Fin.lastCases gate (fun index => graph.node index)
  roots := graph.roots.map Fin.castSucc

/-- Replace only the list of observed roots. -/
def withRoots (graph : DAG n) (roots : List (Fin graph.nodeCount)) : DAG n :=
  { graph with roots := roots }

/-- Appending a gate increases the stored node count by one. -/
@[simp] theorem append_nodeCount (graph : DAG n) (gate : Gate n graph.nodeCount) :
    (graph.append gate).nodeCount = graph.nodeCount + 1 := rfl

/-- Appending retains each earlier gate. -/
@[simp] theorem append_node_castSucc (graph : DAG n) (gate : Gate n graph.nodeCount)
    (index : Fin graph.nodeCount) :
    (graph.append gate).node index.castSucc = graph.node index := by
  simp [append]

/-- The appended gate occupies the final node index. -/
@[simp] theorem append_node_last (graph : DAG n) (gate : Gate n graph.nodeCount) :
    (graph.append gate).node (Fin.last graph.nodeCount) = gate := by
  simp [append]

/-- Replacing roots preserves every gate in the table. -/
@[simp] theorem withRoots_node (graph : DAG n) (roots : List (Fin graph.nodeCount))
    (index : Fin graph.nodeCount) : (graph.withRoots roots).node index = graph.node index := rfl

end DAG
end Controller.Decoder
