module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Extensions.ResolvedSourceEmit
public import Controller.Extensions.ResolvedResident

@[expose] public section

/-! An expansion's occurrence producer keeps the original DAG packet and
selector mask. Only a live AND's negative premise depends on the selector;
its child identifier is fetched from the corresponding original incidence.
All other coordinates are fixed fields of the supplied representation. -/
namespace Controller.Extensions.ResolvedSourcePlan
open Controller Controller.Decoder Controller.Decoder.DAG Controller.CNF
open Controller.Extensions.BoundedAnd Controller.Extensions.ResolvedSourceEmit
open Controller.Cost Controller.Cost.GateProgram Controller.Cost.ForestIndexedOperands
open Controller.Cost.ForestInputStored

def coordinates (graph : DAG n) (clauses : List (Clause graph.ZeroVar)) : List Nat :=
  clauses.flatten.map (fun literal => (graph.zeroIndex literal.1).val)

def literals (width : Nat) (values : List Nat) : List (Operand width) :=
  values.map (fun value => .literal (word width value))

theorem literals_stored (heap : Array (Word width)) (values : List Nat) :
    List.Forall₂ (Stored heap) (literals width values) (values.map (word width)) := by
  induction values with
  | nil => exact .nil
  | cons value rest ih => exact .cons (.literal _) ih

def childBase (packet : Array (Word width)) (rows : List Row) (index : Nat) : Nat :=
  packet.size + 6 * rows.length + (rowChildren (rows.take index)).length

def selectorValues (graph : DAG n) (right : Finset (Fin graph.nodeCount)) : Fin graph.liveAndCount → Bool :=
  fun position => decide (((andIdentities graph)[position.val]'(by rw [andIdentities_length]; exact position.isLt)) ∈ right)

def rank (graph : DAG n) (index : Fin graph.nodeCount) : Nat := (andIdentities graph).idxOf index

def node (width : Nat) (graph : DAG n) (packet : Array (Word width)) (rows : List Row) (roots : List Nat)
    (index : Fin graph.nodeCount) : List (Operand width) :=
  match graph.node index with
  | .liveAnd _ _ =>
    [.choice ((cacheHeap width packet rows roots).size + rank graph index)
      (childBase packet rows index.val) (childBase packet rows index.val + 1) (word width n),
      .literal (word width (n + index.val))]
  | _ => literals width (coordinates (resolved graph ∅) ((resolved graph ∅).nodeClauses index))

theorem child_stored (packet : Array (Word width)) (graph : DAG n) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (right : Finset (Fin graph.nodeCount)) (index : Fin graph.nodeCount)
    (slot : Nat) (valid : slot < (graph.node index).children.length) :
    (withValues (cacheHeap width packet rows roots) (selectorValues graph right))[childBase packet rows index.val + slot]? =
      some (word width ((graph.node index).children[slot]'valid).val) := by
  have cell := typed_child_cell packet graph rows roots matched index slot valid
  have bound : childBase packet rows index.val + slot < (cacheHeap width packet rows roots).size := by
    have rowBound : index.val < rows.length := by rw [matched.length_eq]; exact index.isLt
    have split := row_children_split rows index.val rowBound
    have lengths := congrArg List.length split
    have children := (matched.node index).2.2.1
    simp only [List.length_append, children, List.length_map] at lengths
    simp only [childBase, cacheHeap_size]
    omega
  unfold withValues
  rw [Array.getElem?_append_left bound, Array.getElem?_eq_getElem bound]
  exact congrArg some cell

set_option maxHeartbeats 800000 in
theorem node_stored (packet : Array (Word width)) (graph : DAG n) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (right : Finset (Fin graph.nodeCount)) (index : Fin graph.nodeCount)
    (capacity : n + graph.nodeCount < 2 ^ width) :
    List.Forall₂ (Stored (withValues (cacheHeap width packet rows roots) (selectorValues graph right)))
      (node width graph packet rows roots index)
      ((coordinates (resolved graph right) ((resolved graph right).nodeClauses index)).map (word width)) := by
  cases gate : graph.node index with
  | liveAnd left rightChild =>
    have lc := child_stored packet graph rows roots matched right index 0 (by simp [gate, Gate.children])
    have rc := child_stored packet graph rows roots matched right index 1 (by simp [gate, Gate.children])
    have bit : (withValues (cacheHeap width packet rows roots) (selectorValues graph right))[
        (cacheHeap width packet rows roots).size + rank graph index]? = some (boolWord width (decide (index ∈ right))) := by
      have member : index ∈ andIdentities graph := by simp [andIdentities, gate, Gate.isLiveAnd]
      have bound := List.idxOf_lt_length_of_mem member
      let position : Fin graph.liveAndCount := ⟨rank graph index, by simpa only [rank, andIdentities_length] using bound⟩
      have cell := value_cell (cacheHeap width packet rows roots) (selectorValues graph right) position
      rw [Array.getElem?_eq_getElem (by simp; exact position.isLt)]
      simpa only [selectorValues, position, rank, List.getElem_idxOf bound] using congrArg some cell
    have choice := Stored.choice _ _ _ (word width n) (word width left.val) (word width rightChild.val)
      (decide (index ∈ right)) bit (by simpa [gate, Gate.children, childBase] using lc)
      (by simpa [gate, Gate.children, childBase] using rc)
    have leftFits : left.val < 2 ^ width := by have := left.isLt; have := index.isLt; omega
    have rightFits : rightChild.val < 2 ^ width := by have := rightChild.isLt; have := index.isLt; omega
    have channelFits : n < 2 ^ width := by omega
    simp only [node, gate]
    have shape : coordinates (resolved graph right) ((resolved graph right).nodeClauses index) =
        [n + (if decide (index ∈ right) then rightChild else left).val, n + index.val] := by
      simp [coordinates, resolved, DAG.nodeClauses, gate, Gate.resolve, DAG.childIndex,
        DAG.zeroIndex, ZeroSystem.implicationClause, ZeroSystem.positiveClause]
    rw [shape]
    apply List.Forall₂.cons
    · cases selected : decide (index ∈ right) <;>
        simpa only [selected, Bool.false_eq_true, ite_false, ite_true,
          show (word width left.val).val = left.val from Nat.mod_eq_of_lt leftFits,
          show (word width rightChild.val).val = rightChild.val from Nat.mod_eq_of_lt rightFits,
          show (word width n).val = n from Nat.mod_eq_of_lt channelFits, Nat.add_comm, childBase] using choice
    · exact .cons (.literal _) .nil
  | zero =>
    simpa [node, gate, coordinates, resolved, DAG.nodeClauses, Gate.resolve, DAG.zeroIndex, DAG.childIndex] using
      literals_stored (withValues (cacheHeap width packet rows roots) (selectorValues graph right))
        (coordinates (resolved graph ∅) ((resolved graph ∅).nodeClauses index))
  | input channel =>
    simpa [node, gate, coordinates, resolved, DAG.nodeClauses, Gate.resolve, DAG.zeroIndex, DAG.childIndex] using
      literals_stored (withValues (cacheHeap width packet rows roots) (selectorValues graph right))
        (coordinates (resolved graph ∅) ((resolved graph ∅).nodeClauses index))
  | disj children =>
    simpa [node, gate, coordinates, resolved, DAG.nodeClauses, Gate.resolve, DAG.zeroIndex, DAG.childIndex] using
      literals_stored (withValues (cacheHeap width packet rows roots) (selectorValues graph right))
        (coordinates (resolved graph ∅) ((resolved graph ∅).nodeClauses index))
  | guard child labels =>
    simpa [node, gate, coordinates, resolved, DAG.nodeClauses, Gate.resolve, DAG.zeroIndex, DAG.childIndex] using
      literals_stored (withValues (cacheHeap width packet rows roots) (selectorValues graph right))
        (coordinates (resolved graph ∅) ((resolved graph ∅).nodeClauses index))

def forwards (width : Nat) (graph : DAG n) (packet : Array (Word width)) (rows : List Row) (roots : List Nat) :
    List (Operand width) :=
  (List.finRange graph.nodeCount).flatMap (node width graph packet rows roots)

theorem forwards_stored (packet : Array (Word width)) (graph : DAG n) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (right : Finset (Fin graph.nodeCount))
    (capacity : n + graph.nodeCount < 2 ^ width) :
    List.Forall₂ (Stored (withValues (cacheHeap width packet rows roots) (selectorValues graph right)))
      (forwards width graph packet rows roots)
      ((coordinates (resolved graph right) (resolved graph right).forwardClauses).map (word width)) := by
  have each : ∀ indices : List (Fin graph.nodeCount),
      List.Forall₂ (Stored (withValues (cacheHeap width packet rows roots) (selectorValues graph right)))
        (indices.flatMap (node width graph packet rows roots))
        ((indices.flatMap fun index => coordinates (resolved graph right)
          ((resolved graph right).nodeClauses index)).map (word width)) := by
    intro indices
    induction indices with
    | nil => exact .nil
    | cons index rest ih =>
      simpa only [List.flatMap_cons, List.map_append] using
        List.rel_append (node_stored packet graph rows roots matched right index capacity) ih
  simpa only [forwards, coordinates, DAG.forwardClauses, List.flatten_eq_flatMap, List.flatMap_assoc,
    List.map_flatMap, List.flatMap_map, Function.comp_def] using each (List.finRange graph.nodeCount)

def touchCoordinates (graph : DAG n) : List Nat :=
  (SharedZeroTemplate.touchRows (n + graph.nodeCount)).flatten.map (fun literal => literal.1.val)

def channelCoordinates (graph : DAG n) (b : Nat) (target : Channel n) : List Nat :=
  coordinates graph (graph.channelClauses b target ∅ ∅)

def query (width : Nat) (graph : DAG n) (packet : Array (Word width)) (rows : List Row) (roots : List Nat)
    (b : Nat) (target : Channel n) (rootSlot : Nat) : List (Operand width) :=
  literals width (touchCoordinates graph) ++
    (forwards width graph packet rows roots ++
      (literals width (channelCoordinates graph b target) ++ [.read rootSlot (word width n)]))

def words (width : Nat) (graph : DAG n) (right : Finset (Fin graph.nodeCount)) (b : Nat)
    (target : Channel n) (root : Fin graph.nodeCount) : List (Word width) :=
  (ResolvedResident.rows graph right b target root).flatten.map (fun literal => word width literal.1.val)

theorem node_length (graph : DAG n) (packet : Array (Word width)) (rows : List Row) (roots : List Nat)
    (index : Fin graph.nodeCount) :
    (node width graph packet rows roots index).length =
      (coordinates (resolved graph ∅) ((resolved graph ∅).nodeClauses index)).length := by
  cases gate : graph.node index <;>
    simp [node, gate, literals, coordinates, resolved, DAG.nodeClauses, Gate.resolve,
      ZeroSystem.implicationClause, ZeroSystem.positiveClause, Function.comp_def]

theorem forwards_length (graph : DAG n) (packet : Array (Word width)) (rows : List Row) (roots : List Nat) :
    (forwards width graph packet rows roots).length =
      (coordinates (resolved graph ∅) (resolved graph ∅).forwardClauses).length := by
  have each : ∀ indices : List (Fin graph.nodeCount),
      (indices.flatMap (node width graph packet rows roots)).length =
        (indices.flatMap fun index => coordinates (resolved graph ∅) ((resolved graph ∅).nodeClauses index)).length := by
    intro indices
    induction indices with
    | nil => rfl
    | cons index rest ih => simp only [List.flatMap_cons, List.length_append, node_length, ih]
  simpa only [forwards, coordinates, DAG.forwardClauses, List.flatten_eq_flatMap, List.flatMap_assoc,
    List.map_flatMap, List.flatMap_map, Function.comp_def] using each (List.finRange graph.nodeCount)

theorem words_eq (graph : DAG n) (right : Finset (Fin graph.nodeCount)) (b : Nat)
    (target : Channel n) (root : Fin graph.nodeCount) :
    words width graph right b target root =
      (touchCoordinates graph).map (word width) ++
        (((coordinates (resolved graph right) (resolved graph right).forwardClauses).map (word width)) ++
          ((channelCoordinates graph b target).map (word width) ++ [word width (n + root.val)])) := by
  simp [words, ResolvedResident.rows, SharedZeroTemplate.formula, DAG.finiteZeroSystem,
    DAG.zeroSystem, CNF.relabel, Controller.CNF.OrderedFormula.relabel, Controller.CNF.OrderedFormula.Clause.relabel,
    CNF.ofClauses, coordinates, channelCoordinates, touchCoordinates,
    DAG.zeroIndex, DAG.channelClauses, DAG.trueUnitClauses, DAG.falseUnitClauses,
    ZeroSystem.implicationClause, ZeroSystem.positiveClause, resolved,
    Function.comp_def, List.append_assoc]
  apply List.ext_getElem
  · simp
  · intro i left right
    simp

theorem query_length (graph : DAG n) (packet : Array (Word width)) (rows : List Row) (roots : List Nat)
    (b : Nat) (target : Channel n) (reference : Fin graph.nodeCount) :
    (query width graph packet rows roots b target rootSlot).length =
      (ResolvedResident.rows graph ∅ b target reference).flatten.length := by
  have lengths := congrArg List.length (words_eq (width := width) graph ∅ b target reference)
  simp only [words, List.length_map, List.length_append, List.length_cons, List.length_nil] at lengths
  simp only [query, literals, List.length_append, List.length_map, forwards_length, List.length_cons, List.length_nil]
  omega

theorem query_stored (packet : Array (Word width)) (graph : DAG n) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (right : Finset (Fin graph.nodeCount))
    (b : Nat) (target : Channel n) (root : Fin graph.nodeCount) (rootSlot : Nat)
    (rootStored : (withValues (cacheHeap width packet rows roots) (selectorValues graph right))[rootSlot]? =
      some (word width root.val)) (capacity : n + graph.nodeCount < 2 ^ width) :
    List.Forall₂ (Stored (withValues (cacheHeap width packet rows roots) (selectorValues graph right)))
      (query width graph packet rows roots b target rootSlot) (words width graph right b target root) := by
  rw [words_eq]
  have rootWord := Stored.read rootSlot (word width n) (word width root.val) rootStored
  have rootFits : root.val < 2 ^ width := by have := root.isLt; omega
  have channelFits : n < 2 ^ width := by omega
  have rootMatch : Stored (withValues (cacheHeap width packet rows roots) (selectorValues graph right))
      (.read rootSlot (word width n)) (word width (n + root.val)) := by
    simpa only [show (word width root.val).val = root.val from Nat.mod_eq_of_lt rootFits,
      show (word width n).val = n from Nat.mod_eq_of_lt channelFits, Nat.add_comm] using rootWord
  exact List.rel_append (literals_stored _ _) (List.rel_append
    (forwards_stored packet graph rows roots matched right capacity)
    (List.rel_append (literals_stored _ _) (.cons rootMatch .nil)))

theorem words_bound (graph : DAG n) (right : Finset (Fin graph.nodeCount)) (b : Nat)
    (target : Channel n) (root : Fin graph.nodeCount) :
    (words width graph right b target root).length ≤ 11 * (graph.countedSize + 1) := by
  have count := ResolvedResident.rows_bound graph right b target root
  simpa only [words, List.length_map] using (show (ResolvedResident.rows graph right b target root).flatten.length ≤
    11 * (graph.countedSize + 1) by omega)

theorem execution (program : Program width 8) (state : State width 8)
    (packet : Array (Word width)) (graph : DAG n) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (right : Finset (Fin graph.nodeCount)) (b : Nat)
    (target : Channel n) (root : Fin graph.nodeCount) (rootSlot entry : Nat)
    (heapStored : state.heap = withValues (cacheHeap width packet rows roots) (selectorValues graph right))
    (rootStored : state.heap[rootSlot]? = some (word width root.val))
    (capacity : n + graph.nodeCount < 2 ^ width)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + (ResolvedSourceEmit.code width entry
      (query width graph packet rows roots b target rootSlot)).length < 2 ^ width)
    (heapFits : state.heap.size + (words width graph right b target root).length < 2 ^ width)
    (present : SharedRootRead.BlockAt program entry
      (ResolvedSourceEmit.code width entry (query width graph packet rows roots b target rootSlot))) :
    ∃ final ticks, Execution program state final ticks (state.liveWords + (words width graph right b target root).length) ∧
      ticks ≤ 132 * (graph.countedSize + 1) ∧
      final.heap = state.heap ++ (words width graph right b target root).toArray ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry + (ResolvedSourceEmit.code width entry
        (query width graph packet rows roots b target rootSlot)).length) ∧ final.halted = false := by
  have represented := query_stored packet graph rows roots matched right b target root rootSlot
    (by simpa only [heapStored] using rootStored) capacity
  obtain ⟨final, ticks, trace, time, heap, stack, output, pc, active⟩ :=
    ResolvedSourceEmit.execution program state entry _ _ (by simpa only [heapStored] using represented)
      position running room heapFits present
  have length := represented.length_eq
  have bound := words_bound (width := width) graph right b target root
  exact ⟨final, ticks, trace, by omega, heap, stack, output, pc, active⟩

end Controller.Extensions.ResolvedSourcePlan
