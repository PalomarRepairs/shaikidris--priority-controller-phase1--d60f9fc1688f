module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestZeroEmit
public import Controller.Cost.ForestZeroInitialize

@[expose] public section

/-! Source occurrences retain their exact positions in the loaded packet.
The five-word global header and all node/guard/declared-root streams are
physically present before dictionary reservation. Node coordinates are formed
by adding the loaded channel count; channel coordinates are read directly.
Incoming node identities come from root or child stream cells. -/
namespace Controller.Cost.ForestZeroSource
open Controller.Decoder Controller.Decoder.DAG Controller.CNF
open Controller.Cost.GateProgram Controller.Cost.ForestIndexedOperands
open Controller.Cost.ForestInputStored Controller.Cost.ForestZeroEmit
open Controller.Cost.ForestZeroRows Controller.Cost.ForestCursorMaterialize

/-- The actual global header is loaded before the shared indexed cache. -/
def headerHeap (width channels : ℕ) (rows : List Row) (roots : List ℕ) : Array (Word width) :=
  ((globalHeader channels rows roots).map (word width)).toArray

def packetHeap (width channels : ℕ) (rows : List Row) (roots : List ℕ) : Array (Word width) :=
  cacheHeap width (headerHeap width channels rows roots) rows roots

@[simp] theorem headerHeap_size (width channels : ℕ) (rows : List Row) (roots : List ℕ) : (headerHeap width channels rows roots).size = 5 := by
  simp [headerHeap]

@[simp] theorem packetHeap_size (width channels : ℕ) (rows : List Row) (roots : List ℕ) : (packetHeap width channels rows roots).size =
    5 + 6 * rows.length + (rowChildren rows).length + (rowGuards rows).length + roots.length := by
  simp only [packetHeap, cacheHeap_size, headerHeap_size]

theorem packet_header (width channels : ℕ) (rows : List Row) (roots : List ℕ) : (packetHeap width channels rows roots)[0]? = some (word width channels) := by
  rw [packetHeap, cacheHeap, allocatedHeap_prefix width _ _ 0 (by simp)]
  simp [headerHeap, globalHeader]

/-- The concrete heap is the exact encoded input, not a supplied source array. -/
theorem packet_exact (width channels : ℕ) (rows : List Row) (roots : List ℕ) : packetHeap width channels rows roots =
    ((inputPacket channels 0 rows roots).map (word width)).toArray := by
  simp only [packetHeap, cacheHeap, allocatedHeap, headerHeap, inputPacket, headerHeap_size,
    Nat.zero_add, List.map_append, List.append_toArray, List.size_toArray, List.length_map, globalHeader_length]

/-- The five actual loaded global words instantiate the once-only initializer. -/
def packetHeader (width channels : ℕ) (rows : List Row) (roots : List ℕ) :
    Controller.Cost.ForestZeroInitialize.PacketHeader (packetHeap width channels rows roots)
      channels rows.length (rowChildren rows).length (rowGuards rows).length roots.length := by
  have headerCell : ∀ address, address < 5 →
      (packetHeap width channels rows roots)[address]? = (headerHeap width channels rows roots)[address]? := by
    intro address bound
    exact allocatedHeap_prefix width (headerHeap width channels rows roots)
      (serializedRows (headerHeap width channels rows roots).size rows roots) address (by simpa using bound)
  refine ⟨?_, packet_header width channels rows roots, ?_, ?_, ?_, ?_, packetHeap_size width channels rows roots⟩
  · rw [packetHeap_size]; omega
  · rw [headerCell 1 (by decide)]
    simp [headerHeap, globalHeader, countSource_value]
  · rw [headerCell 2 (by decide)]
    simp [headerHeap, globalHeader, countSource_value]
  · rw [headerCell 3 (by decide)]
    simp [headerHeap, globalHeader, countSource_value]
  · rw [headerCell 4 (by decide)]
    simp [headerHeap, globalHeader, countSource_value]

/-- Channel occurrences use the original stored identifier. -/
def channelReference (slot : ℕ) (channel : Fin n) (positive : Bool) : Reference (n + nodes) where
  slot := slot
  raw := channel.val
  activity := false
  coordinate := ⟨channel.val, by have := channel.isLt; omega⟩
  positive := positive

/-- An activity occurrence carries its original node ID, not a local solver ID. -/
def nodeReference (slot : ℕ) (node : Fin nodes) (positive : Bool) : Reference (n + nodes) where
  slot := slot
  raw := node.val
  activity := true
  coordinate := ⟨n + node.val, by have := node.isLt; omega⟩
  positive := positive

private theorem channel_stored {width nodes : ℕ} {rows : List Row} {roots : List ℕ} (slot : ℕ) (channel : Fin n) (positive : Bool)
    (bound : slot < (packetHeap width n rows roots).size)
    (cell : (packetHeap width n rows roots)[slot]? = some (word width channel.val)) :
    StoredReference (packetHeap width n rows roots) n (packetHeap width n rows roots).size
      (channelReference (nodes := nodes) slot channel positive) := by
  refine ⟨le_rfl, bound, ?_, cell, packet_header width n rows roots, ?_⟩
  · rw [packetHeap_size]; omega
  · simp [channelReference]

private theorem node_stored {width n : ℕ} {rows : List Row} {roots : List ℕ} (slot : ℕ) (node : Fin nodes) (positive : Bool)
    (bound : slot < (packetHeap width n rows roots).size)
    (cell : (packetHeap width n rows roots)[slot]? = some (word width node.val)) :
    StoredReference (packetHeap width n rows roots) n (packetHeap width n rows roots).size
      (nodeReference (n := n) slot node positive) := by
  refine ⟨le_rfl, bound, ?_, cell, packet_header width n rows roots, ?_⟩
  · rw [packetHeap_size]; omega
  · simp [nodeReference, Nat.add_comm]

/-- Declared roots are read from their original ordered stream, including duplicates. -/
def rootReference (graph : DAG n) (rows : List Row) (roots : List ℕ)
    (position : Fin graph.roots.length) (positive : Bool) : Reference (n + graph.nodeCount) :=
  nodeReference (5 + (6 * rows.length + (rowChildren rows).length +
    (rowGuards rows).length) + position.val) (graph.roots.get position) positive

theorem root_stored (graph : DAG n) (rows : List Row) (roots : List ℕ)
    (rootMatches : RootsMatch graph roots) (position : Fin graph.roots.length) (positive : Bool) :
    StoredReference (packetHeap width n rows roots) n (packetHeap width n rows roots).size
      (rootReference graph rows roots position positive) := by
  have lengths : roots.length = graph.roots.length := by rw [rootMatches, List.length_map]
  have bound : 5 + (6 * rows.length + (rowChildren rows).length +
      (rowGuards rows).length) + position.val < (packetHeap width n rows roots).size := by
    rw [packetHeap_size]; have := position.isLt; omega
  apply node_stored _ _ _ bound
  rw [Array.getElem?_eq_getElem bound]
  apply congrArg some
  simpa only [packetHeap, headerHeap_size] using cache_declared_root_word
    (headerHeap width n rows roots) graph rows roots rootMatches position

/-- Every child position has its own source address; repeated child IDs remain repeated. -/
def childReference (graph : DAG n) (rows : List Row) (owner : Fin graph.nodeCount)
    (slot : Fin (graph.node owner).children.length) (positive : Bool) : Reference (n + graph.nodeCount) :=
  nodeReference (5 + 6 * rows.length + (rowChildren (rows.take owner.val)).length + slot.val)
    (graph.childIndex owner ((graph.node owner).children.get slot)) positive

theorem child_stored (graph : DAG n) (rows : List Row) (roots : List ℕ)
    (corresponds : RowsMatch graph rows) (owner : Fin graph.nodeCount)
    (slot : Fin (graph.node owner).children.length) (positive : Bool) :
    StoredReference (packetHeap width n rows roots) n (packetHeap width n rows roots).size
      (childReference graph rows owner slot positive) := by
  have rowValid : owner.val < rows.length := by rw [corresponds.length_eq]; exact owner.isLt
  have split := row_children_split rows owner.val rowValid
  have lengths := congrArg List.length split
  simp only [List.length_append, (corresponds.node owner).2.2.1, List.length_map] at lengths
  have bound : 5 + 6 * rows.length + (rowChildren (rows.take owner.val)).length + slot.val <
      (packetHeap width n rows roots).size := by rw [packetHeap_size]; have := slot.isLt; omega
  apply node_stored _ _ _ bound
  rw [Array.getElem?_eq_getElem bound]
  apply congrArg some
  simpa only [packetHeap, headerHeap_size, childIndex, List.get_eq_getElem] using
    typed_child_cell (headerHeap width n rows roots) graph rows roots corresponds owner slot.val slot.isLt

/-- Guard labels retain their original label positions and channel coordinate domain. -/
def guardReference (graph : DAG n) (rows : List Row) (owner : Fin graph.nodeCount)
    (slot : Fin (graph.node owner).guardLabels.length) (positive : Bool) : Reference (n + graph.nodeCount) :=
  channelReference (5 + 6 * rows.length + (rowChildren rows).length +
    (rowGuards (rows.take owner.val)).length + slot.val)
    ((graph.node owner).guardLabels.get slot) positive

theorem guard_stored (graph : DAG n) (rows : List Row) (roots : List ℕ)
    (corresponds : RowsMatch graph rows) (owner : Fin graph.nodeCount)
    (slot : Fin (graph.node owner).guardLabels.length) (positive : Bool) :
    StoredReference (packetHeap width n rows roots) n (packetHeap width n rows roots).size
      (guardReference graph rows owner slot positive) := by
  have rowValid : owner.val < rows.length := by rw [corresponds.length_eq]; exact owner.isLt
  have split := row_guards_split rows owner.val rowValid
  have lengths := congrArg List.length split
  simp only [List.length_append, (corresponds.node owner).2.2.2, List.length_map] at lengths
  have bound : 5 + 6 * rows.length + (rowChildren rows).length +
      (rowGuards (rows.take owner.val)).length + slot.val < (packetHeap width n rows roots).size := by
    rw [packetHeap_size]; have := slot.isLt; omega
  apply channel_stored _ _ _ bound
  rw [Array.getElem?_eq_getElem bound]
  apply congrArg some
  simpa only [packetHeap, headerHeap_size, List.get_eq_getElem] using
    typed_guard_cell (headerHeap width n rows roots) graph rows roots corresponds owner slot.val slot.isLt

/-- Input heads use the stored row-head cell only at an actual input gate. -/
def inputReference (graph : DAG n) (owner : Fin graph.nodeCount)
    (channel : Fin n) (positive : Bool) : Reference (n + graph.nodeCount) :=
  channelReference (5 + (2 * owner.val + 1)) channel positive

theorem input_stored (graph : DAG n) (rows : List Row) (roots : List ℕ)
    (corresponds : RowsMatch graph rows) (owner : Fin graph.nodeCount)
    (channel : Fin n) (inputGate : graph.node owner = .input channel) (positive : Bool) :
    StoredReference (packetHeap width n rows roots) n (packetHeap width n rows roots).size
      (inputReference graph owner channel positive) := by
  have rowValid : owner.val < rows.length := by rw [corresponds.length_eq]; exact owner.isLt
  have bound : 5 + (2 * owner.val + 1) < (packetHeap width n rows roots).size := by
    rw [packetHeap_size]; omega
  have cell := cache_header_word (headerHeap width n rows roots) rows roots
    (2 * owner.val + 1) (by rw [rowHeaders_length]; omega)
  rw [header_head_value rows owner.val rowValid] at cell
  have head := (corresponds.node owner).2.1 channel inputGate
  rw [head] at cell
  apply channel_stored _ _ _ bound
  rw [Array.getElem?_eq_getElem bound]
  exact congrArg some (by simpa only [packetHeap, headerHeap_size] using cell)

/-- Polarity is an emitted pair field; changing it never changes the read cell. -/
def signed (reference : Reference ambient) (positive : Bool) : Reference ambient :=
  { reference with positive := positive }

def sourceLiteralOf (reference : Reference ambient) : Literal ℕ :=
  (reference.coordinate.val, reference.positive)

theorem signed_stored (reference : Reference ambient) (positive : Bool)
    (stored : StoredReference heap channels sourceEnd reference) :
    StoredReference heap channels sourceEnd (signed reference positive) := by
  exact ⟨stored.sourceBound, stored.slotBound, stored.headerBound, stored.slotWord,
    stored.channelWord, stored.coordinateEq⟩

/-- This recurrence dispatches original row fields and source-position references.
The owner reference comes from the incoming child or declared-root position;
children and guards remain ordered positional lists, including duplicates. -/
def referenceClauses (row : Row) (owner head : Reference ambient)
    (children guards : List (Reference ambient)) : List (List (Reference ambient)) :=
  match row.tag, children with
  | 0, _ => [[signed owner false]]
  | 1, _ => [[signed head false, signed owner true],
             [signed owner false, signed head true]]
  | 2, refs => refs.map fun child => [signed child false, signed owner true]
  | 3, child :: _ => [[signed child false] ++ guards.map (fun guard => signed guard true) ++ [signed owner true]]
  | 4, left :: right :: _ => [[signed left false, signed right false, signed owner true]]
  | _, _ => []

/-- Source-coordinate agreement is exact for all five original gate shapes. -/
theorem referenceClauses_exact (channels ownerID : ℕ) (row : Row)
    (owner head : Reference ambient) (children guards : List (Reference ambient))
    (ownerEq : owner.coordinate.val = channels + ownerID)
    (headEq : row.tag = 1 → head.coordinate.val = row.head)
    (childrenEq : children.map (fun child => child.coordinate.val) =
      row.children.map (fun child => channels + child))
    (guardsEq : guards.map (fun guard => guard.coordinate.val) = row.guards) :
    (referenceClauses row owner head children guards).map (List.map sourceLiteralOf) =
      rowClauses channels ownerID row := by
  by_cases tag0 : row.tag = 0
  · simp [referenceClauses, rowClauses, tag0, sourceLiteralOf, signed, ownerEq]
  by_cases tag1 : row.tag = 1
  · simp [referenceClauses, rowClauses, tag1, sourceLiteralOf, signed, ownerEq, headEq tag1]
  by_cases tag2 : row.tag = 2
  · have mapped := congrArg (List.map (fun child => [(child, false), (channels + ownerID, true)])) childrenEq
    simpa [referenceClauses, rowClauses, tag2, sourceLiteralOf, signed, ownerEq,
      List.map_map, Function.comp_def] using mapped
  by_cases tag3 : row.tag = 3
  · cases childCase : children with
    | nil =>
      have empty : row.children = [] := by
        apply List.map_eq_nil_iff.mp
        simpa only [childCase, List.map_nil] using childrenEq.symm
      simp [referenceClauses, rowClauses, tag3, childCase, empty]
    | cons child rest =>
      cases rowCase : row.children with
      | nil => simp [childCase, rowCase] at childrenEq
      | cons first tail =>
        have relation := childrenEq
        simp only [childCase, rowCase, List.map_cons] at relation
        have firstEq := (List.cons.inj relation).1
        have mapped := congrArg (List.map (fun guard => (guard, true))) guardsEq
        simp only [List.map_map, Function.comp_def] at mapped
        simpa [referenceClauses, rowClauses, tag3, childCase, rowCase, sourceLiteralOf,
          signed, ownerEq, firstEq, List.map_map, Function.comp_def] using
          congrArg (fun labels => [(channels + first, false)] ++ labels ++ [(channels + ownerID, true)]) mapped
  by_cases tag4 : row.tag = 4
  · cases childCase : children with
    | nil =>
      have empty : row.children = [] := by
        apply List.map_eq_nil_iff.mp
        simpa only [childCase, List.map_nil] using childrenEq.symm
      simp [referenceClauses, rowClauses, tag4, childCase, empty]
    | cons left rest =>
      cases restCase : rest with
      | nil =>
        cases rowCase : row.children with
        | nil => simp [childCase, restCase, rowCase] at childrenEq
        | cons first tail =>
          have relation := childrenEq
          simp only [childCase, restCase, rowCase, List.map_cons, List.map_nil] at relation
          have empty : tail = [] := List.map_eq_nil_iff.mp (List.cons.inj relation).2.symm
          simp [referenceClauses, rowClauses, tag4, childCase, restCase, rowCase, empty]
      | cons right remaining =>
        cases rowCase : row.children with
        | nil => simp [childCase, restCase, rowCase] at childrenEq
        | cons first tail =>
          cases tailCase : tail with
          | nil => simp [childCase, restCase, rowCase, tailCase] at childrenEq
          | cons second further =>
            have relation := childrenEq
            simp only [childCase, restCase, rowCase, tailCase, List.map_cons] at relation
            have firstEq := (List.cons.inj relation).1
            have secondEq := (List.cons.inj (List.cons.inj relation).2).1
            simp [referenceClauses, rowClauses, tag4, childCase, restCase, rowCase, tailCase,
              sourceLiteralOf, signed, ownerEq, firstEq, secondEq]
  simp [referenceClauses, rowClauses, tag0, tag1, tag2, tag3, tag4]

/-- The base is loaded from the cache column in four fetched instructions.
The preceding-row prefix appears only in the ghost returned-value equation;
the executed code doubles the node ID and reads one directory cell. -/
theorem child_base_execution (program : Program width 4) (graph : DAG n)
    (rows : List Row) (roots : List ℕ) (corresponds : RowsMatch graph rows)
    (owner : Fin graph.nodeCount) (base : ℕ) (loaded temporary : Word width)
    (fits : base + 4 < 2 ^ width) (heapFits : (packetHeap width n rows roots).size ≤ 2 ^ width)
    (block : BlockAt program base
      (Controller.Cost.ForestGraphDirectory.indexedCode width (5 + 2 * rows.length))) :
    Execution program
      (Controller.Cost.ForestCounter.counterState (packetHeap width n rows roots)
        base (word width owner.val) loaded temporary)
      (Controller.Cost.ForestCounter.counterState (packetHeap width n rows roots)
        (base + 4) (word width (5 + 2 * rows.length + 2 * owner.val))
        (word width (5 + 6 * rows.length + (rowChildren (rows.take owner.val)).length))
        (word width (5 + 2 * rows.length)))
      4 (5 + (packetHeap width n rows roots).size) := by
  have rowValid : owner.val < rows.length := by rw [corresponds.length_eq]; exact owner.isLt
  have valid : 5 + 2 * rows.length + 2 * owner.val < (packetHeap width n rows roots).size := by
    rw [packetHeap_size]; omega
  have cell := (cache_base_words (headerHeap width n rows roots) rows roots owner.val rowValid).1
  exact Controller.Cost.ForestGraphDirectory.indexed_execution program _ base
    (5 + 2 * rows.length) owner.val loaded temporary _ fits
    (Nat.lt_of_lt_of_le valid heapFits) valid
    (by simpa only [packetHeap, headerHeap_size] using cell) block

/-- Guard bases are the adjacent cache column; no prior guards are rescanned. -/
theorem guard_base_execution (program : Program width 4) (graph : DAG n)
    (rows : List Row) (roots : List ℕ) (corresponds : RowsMatch graph rows)
    (owner : Fin graph.nodeCount) (base : ℕ) (loaded temporary : Word width)
    (fits : base + 4 < 2 ^ width) (heapFits : (packetHeap width n rows roots).size ≤ 2 ^ width)
    (block : BlockAt program base
      (Controller.Cost.ForestGraphDirectory.indexedCode width (5 + 2 * rows.length + 1))) :
    Execution program
      (Controller.Cost.ForestCounter.counterState (packetHeap width n rows roots)
        base (word width owner.val) loaded temporary)
      (Controller.Cost.ForestCounter.counterState (packetHeap width n rows roots)
        (base + 4) (word width (5 + 2 * rows.length + 2 * owner.val + 1))
        (word width (5 + 6 * rows.length + (rowChildren rows).length +
          (rowGuards (rows.take owner.val)).length))
        (word width (5 + 2 * rows.length + 1)))
      4 (5 + (packetHeap width n rows roots).size) := by
  have rowValid : owner.val < rows.length := by rw [corresponds.length_eq]; exact owner.isLt
  have valid : 5 + 2 * rows.length + 2 * owner.val + 1 < (packetHeap width n rows roots).size := by
    rw [packetHeap_size]; omega
  have address : 5 + 2 * rows.length + 1 + 2 * owner.val =
      5 + 2 * rows.length + 2 * owner.val + 1 := by omega
  have cell := (cache_base_words (headerHeap width n rows roots) rows roots owner.val rowValid).2
  simpa only [address] using Controller.Cost.ForestGraphDirectory.indexed_execution program _ base
    (5 + 2 * rows.length + 1) owner.val loaded temporary _ fits
    (by rw [address]; exact Nat.lt_of_lt_of_le valid heapFits)
    (by rw [address]; exact valid)
    (by simpa only [packetHeap, headerHeap_size, address, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using cell) block

/-- Reserving both dictionaries retains every physically derived occurrence. -/
theorem reserved_stored (reference : Reference ambient)
    (stored : StoredReference heap channels heap.size reference) :
    StoredReference (Controller.Cost.ForestZeroInitialize.reserveHeap heap ambient)
      channels heap.size reference := by
  refine ⟨?_, stored.slotBound, stored.headerBound, ?_, ?_, stored.coordinateEq⟩
  · simp [Controller.Cost.ForestZeroInitialize.reserveHeap]
  · exact (Controller.Cost.ForestZeroInitialize.reserve_source heap ambient reference.slot stored.slotBound).trans stored.slotWord
  · exact (Controller.Cost.ForestZeroInitialize.reserve_source heap ambient 0 stored.headerBound).trans stored.channelWord

end Controller.Cost.ForestZeroSource
