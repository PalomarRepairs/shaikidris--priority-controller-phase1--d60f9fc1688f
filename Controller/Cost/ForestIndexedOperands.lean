module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestGraphDirectory
public import Controller.Cost.CompilerAppendTrace
public import Controller.Cost.ForestInputMetadata

@[expose] public section

/-!
# Indexed source operands for the forest cursor

The fixed header-read kernel accepts a node identifier, doubles it, adds the
stored header offset and reads the actual source cell. Input-field formation
uses the same indexed cell and emits a physical four-word constant record.
Child and guard base values are read from the allocated two-column directory.
List-length metadata, position lookup and counter-offset field formation have
separate interfaces; no graph-node function evaluation is assigned unit cost.
-/
namespace Controller.Cost.ForestIndexedOperands
open Controller.Decoder Controller.Decoder.DAG Controller.Cost.GateProgram
open Controller.Cost.ForestCounter Controller.Cost.ForestCursorTraversal
open Controller.Cost.ForestGraphDirectory

/-- This value identifies the stored word; the executed kernel reads memory. -/
def tagValue (graph : DAG n) (node : Fin graph.nodeCount) : ℕ :=
  match graph.node node with
  | .zero => 0 | .input _ => 1 | .disj _ => 2 | .guard _ _ => 3 | .liveAnd _ _ => 4

theorem header_tag_execution (machine : Program width 4) (heap : Array (Word width))
    (graph : DAG n) (records : GraphRecords width heap graph) (node : Fin graph.nodeCount)
    (base : ℕ) (loaded temporary : Word width)
    (fits : base + 4 < 2 ^ width) (heapFits : heap.size ≤ 2 ^ width)
    (block : BlockAt machine base (indexedCode width records.recordBase)) :
    Execution machine (counterState heap base (word width node.val) loaded temporary)
      (counterState heap (base + 4) (word width (records.recordBase + 2 * node.val))
        (word width (tagValue graph node)) (word width records.recordBase))
      4 (5 + heap.size) := by
  exact indexed_execution machine heap base records.recordBase node.val loaded temporary
    (word width (tagValue graph node)) fits
    (Nat.lt_of_lt_of_le (records.tagValid node) heapFits) (records.tagValid node)
    (records.tagWord node) block

theorem header_head_execution (machine : Program width 4) (heap : Array (Word width))
    (graph : DAG n) (records : GraphRecords width heap graph) (node : Fin graph.nodeCount)
    (head : Channel n) (input : graph.node node = .input head)
    (base : ℕ) (loaded temporary : Word width)
    (fits : base + 4 < 2 ^ width) (heapFits : heap.size ≤ 2 ^ width)
    (block : BlockAt machine base (indexedCode width (records.recordBase + 1))) :
    Execution machine (counterState heap base (word width node.val) loaded temporary)
      (counterState heap (base + 4) (word width (records.recordBase + 2 * node.val + 1))
        (word width head.val) (word width (records.recordBase + 1)))
      4 (5 + heap.size) := by
  have address : records.recordBase + 1 + 2 * node.val = records.recordBase + 2 * node.val + 1 := by omega
  simpa only [address] using indexed_execution machine heap base (records.recordBase + 1) node.val
    loaded temporary (word width head.val) fits (by rw [address]; exact Nat.lt_of_lt_of_le (records.headValid node) heapFits)
    (by rw [address]; exact records.headValid node)
    (by simpa only [address] using records.headWord node head input) block

/-- The source-dependent instruction field is read and allocated, not supplied
as an already encoded register tuple. Exactly thirteen fetched steps are used. -/
theorem header_head_constant (machine : Program width 4) (heap : Array (Word width))
    (graph : DAG n) (records : GraphRecords width heap graph) (node : Fin graph.nodeCount)
    (head : Channel n) (input : graph.node node = .input head)
    (base : ℕ) (loaded temporary : Word width)
    (fits : base + 13 < 2 ^ width) (heapFits : heap.size ≤ 2 ^ width)
    (channelsFit : n ≤ 2 ^ width) (room : heap.size + 4 ≤ 2 ^ width)
    (block : BlockAt machine base (baseConstantCode width (records.recordBase + 1))) :
    ∃ final, Execution machine (counterState heap base (word width node.val) loaded temporary)
      final 13 (9 + heap.size) ∧
      final.heap = heap ++ (InstructionEncoding.encode (.constant 0 (word width head.val) : Instruction width 4)).toArray ∧
      final.stack = [] ∧ final.output = [] ∧ final.pc = word width (base + 13) ∧ final.halted = false := by
  have address : records.recordBase + 1 + 2 * node.val = records.recordBase + 2 * node.val + 1 := by omega
  exact baseConstant_execution machine heap base (records.recordBase + 1) node.val head.val loaded temporary
    fits (by rw [address]; exact Nat.lt_of_lt_of_le (records.headValid node) heapFits)
    (Nat.lt_of_lt_of_le head.isLt channelsFit) (by rw [address]; exact records.headValid node)
    (by simpa only [address] using records.headWord node head input) room block

/-- Directory cells are physically allocated words. Matching identifies their
contents with the represented graph; the runtime kernel only reads those cells. -/
theorem directory_child_execution (machine : Program width 4) (heap : Array (Word width))
    (graph : DAG n) (records : GraphRecords width heap graph) (source : Source graph)
    (corresponds : source.Matches records) (node : Fin graph.nodeCount) (base : ℕ)
    (loaded temporary : Word width) (fits : base + 4 < 2 ^ width)
    (heapFits : (backingHeap width heap source.entries).size ≤ 2 ^ width)
    (block : BlockAt machine base (indexedCode width heap.size)) :
    Execution machine (counterState (backingHeap width heap source.entries) base (word width node.val) loaded temporary)
      (counterState (backingHeap width heap source.entries) (base + 4)
        (word width (heap.size + 2 * node.val)) (word width (records.childBase node)) (word width heap.size))
      4 (5 + (backingHeap width heap source.entries).size) := by
  have valid : node.val < source.entries.length := by rw [source.length_eq]; exact node.isLt
  have cellValid : heap.size + 2 * node.val < (backingHeap width heap source.entries).size := by simp; omega
  have stored : (backingHeap width heap source.entries)[heap.size + 2 * node.val] = word width (records.childBase node) := by
    rw [child_word heap source.entries node.val valid]
    exact congrArg (word width) (corresponds node).1
  exact indexed_execution machine _ base heap.size node.val loaded temporary (word width (records.childBase node))
    fits (Nat.lt_of_lt_of_le cellValid heapFits) cellValid stored block

/-- Guard bases use the second stored column, with the same indexed read cost. -/
theorem directory_guard_execution (machine : Program width 4) (heap : Array (Word width))
    (graph : DAG n) (records : GraphRecords width heap graph) (source : Source graph)
    (corresponds : source.Matches records) (node : Fin graph.nodeCount) (base : ℕ)
    (loaded temporary : Word width) (fits : base + 4 < 2 ^ width)
    (heapFits : (backingHeap width heap source.entries).size ≤ 2 ^ width)
    (block : BlockAt machine base (indexedCode width (heap.size + 1))) :
    Execution machine (counterState (backingHeap width heap source.entries) base (word width node.val) loaded temporary)
      (counterState (backingHeap width heap source.entries) (base + 4)
        (word width (heap.size + 2 * node.val + 1)) (word width (records.guardBase node)) (word width (heap.size + 1)))
      4 (5 + (backingHeap width heap source.entries).size) := by
  have valid : node.val < source.entries.length := by rw [source.length_eq]; exact node.isLt
  have address : heap.size + 1 + 2 * node.val = heap.size + 2 * node.val + 1 := by omega
  have cellValid : heap.size + 2 * node.val + 1 < (backingHeap width heap source.entries).size := by simp; omega
  have stored : (backingHeap width heap source.entries)[heap.size + 2 * node.val + 1] = word width (records.guardBase node) := by
    rw [guard_word heap source.entries node.val valid]
    exact congrArg (word width) (corresponds node).2
  simpa only [address] using indexed_execution machine _ base (heap.size + 1) node.val
    loaded temporary (word width (records.guardBase node)) fits
    (by rw [address]; exact Nat.lt_of_lt_of_le cellValid heapFits)
    (by rw [address]; exact cellValid) (by simpa only [address] using stored) block

/-- Executable tail traversal of a supplied source incidence list. This
pre-loading operation counts one inspected cons and one increment at each step.
It is a list-construction operation contract, distinct from fetched RAM ticks. -/
def countSource (items : List α) (before : ℕ) : ℕ :=
  match items with
  | [] => before
  | _ :: rest => countSource rest (before + 1)

inductive CountSourceTrace {α : Type} : List α → ℕ → ℕ → ℕ → Prop
  | nil (before : ℕ) : CountSourceTrace [] before before 0
  | cons (head : α) (rest : List α) (before after visits : ℕ)
      (next : CountSourceTrace rest (before + 1) after visits) :
      CountSourceTrace (head :: rest) before after (visits + 1)

theorem countSource_trace (items : List α) (before : ℕ) :
    CountSourceTrace items before (countSource items before) items.length := by
  induction items generalizing before with
  | nil => exact CountSourceTrace.nil before
  | cons head rest ih => simpa only [countSource, List.length_cons] using
      CountSourceTrace.cons head rest before (countSource rest (before + 1)) rest.length (ih (before + 1))

theorem countSource_value (items : List α) (before : ℕ) :
    countSource items before = before + items.length := by
  induction items generalizing before with
  | nil => simp [countSource]
  | cons head rest ih => simp [countSource, ih]; omega

/-- Raw node rows are the logical input to the shared source serializer.
Incidence lists retain multiplicities and their construction is charged. -/
structure Row where
  tag : ℕ
  head : ℕ
  children : List ℕ
  guards : List ℕ
  deriving DecidableEq, Repr

/-- This correspondence is a semantic input check, not an executed node query. -/
def Row.Matches (row : Row) (gate : Gate n available) : Prop :=
  row.tag = (match gate with
    | .zero => 0 | .input _ => 1 | .disj _ => 2 | .guard _ _ => 3 | .liveAnd _ _ => 4) ∧
  (∀ channel, gate = .input channel → row.head = channel.val) ∧
  row.children = gate.children.map Fin.val ∧ row.guards = gate.guardLabels.map Fin.val

def rowHeaders (rows : List Row) : List ℕ := rows.flatMap (fun row => [row.tag, row.head])
def rowArities (rows : List Row) : List ℕ := rows.flatMap (fun row => [countSource row.children 0, countSource row.guards 0])
def rowChildren (rows : List Row) : List ℕ := rows.flatMap Row.children
def rowGuards (rows : List Row) : List ℕ := rows.flatMap Row.guards

/-- An indexed row table agrees with the exact typed node, including each
child and guard occurrence. The relation is checked before the source scan. -/
structure RowsMatch (graph : DAG n) (rows : List Row) : Prop where
  length_eq : rows.length = graph.nodeCount
  node : ∀ index : Fin graph.nodeCount,
    (rows[index.val]'(by rw [length_eq]; exact index.isLt)).Matches (graph.node index)

/-- Each count is obtained from the actual raw incidence list, and matching
identifies it with the source gate arity without another source-node query. -/
theorem matched_counts (graph : DAG n) (rows : List Row) (corresponds : RowsMatch graph rows)
    (index : Fin graph.nodeCount) :
    let row := rows[index.val]'(by rw [corresponds.length_eq]; exact index.isLt)
    countSource row.children 0 = (graph.node index).children.length ∧
    countSource row.guards 0 = (graph.node index).guardLabels.length := by
  have matched := corresponds.node index
  rcases matched with ⟨tag, head, children, guards⟩
  simp only [countSource_value, Nat.zero_add, children, guards, List.length_map]
  exact ⟨trivial, trivial⟩

/-- The packed streams contain exactly the original incidence counts,
including repetitions; row correspondence derives this input-size bridge. -/
theorem matched_incidence_lengths (graph : DAG n) (rows : List Row)
    (corresponds : RowsMatch graph rows) :
    (rowChildren rows).length = graph.childIncidences ∧
    (rowGuards rows).length = graph.guardIncidences := by
  have children : rows.map (fun row => row.children.length) =
      List.ofFn (fun index : Fin graph.nodeCount => (graph.node index).children.length) := by
    apply List.ext_getElem
    · simp [corresponds.length_eq]
    · intro index left right
      have bounded : index < graph.nodeCount := by simpa using right
      have equal := (corresponds.node ⟨index, bounded⟩).2.2.1
      simpa only [List.getElem_map, List.getElem_ofFn, List.length_map] using congrArg List.length equal
  have guards : rows.map (fun row => row.guards.length) =
      List.ofFn (fun index : Fin graph.nodeCount => (graph.node index).guardLabels.length) := by
    apply List.ext_getElem
    · simp [corresponds.length_eq]
    · intro index left right
      have bounded : index < graph.nodeCount := by simpa using right
      have equal := (corresponds.node ⟨index, bounded⟩).2.2.2
      simpa only [List.getElem_map, List.getElem_ofFn, List.length_map] using congrArg List.length equal
  constructor
  · simpa only [rowChildren, List.length_flatMap, children, DAG.childIncidences]
  · simpa only [rowGuards, List.length_flatMap, guards, DAG.guardIncidences]

/-- Two independent pre-loading passes count the lists used in arity cells and
base-cursor updates. Their traces witness all actual repeated cons inspections. -/
def RowCountTrace (row : Row) (visits : ℕ) : Prop :=
  CountSourceTrace row.children 0 (countSource row.children 0) row.children.length ∧
  CountSourceTrace row.guards 0 (countSource row.guards 0) row.guards.length ∧
  CountSourceTrace row.children 0 (countSource row.children 0) row.children.length ∧
  CountSourceTrace row.guards 0 (countSource row.guards 0) row.guards.length ∧
  visits = 2 * (row.children.length + row.guards.length)

theorem row_count_trace (row : Row) :
    RowCountTrace row (2 * (row.children.length + row.guards.length)) :=
  ⟨countSource_trace row.children 0, countSource_trace row.guards 0,
    countSource_trace row.children 0, countSource_trace row.guards 0, rfl⟩

/-- The cursors advance once per row and preserve every repeated incidence.
The input-list lengths require their counted source pass before this pass. -/
def rowBases : List Row → ℕ → ℕ → List ℕ
  | [], _, _ => []
  | row :: rest, childCursor, guardCursor =>
      childCursor :: guardCursor :: rowBases rest
        (childCursor + countSource row.children 0) (guardCursor + countSource row.guards 0)

@[simp] theorem rowHeaders_length (rows : List Row) : (rowHeaders rows).length = 2 * rows.length := by
  induction rows with
  | nil => rfl
  | cons row rest ih => simp [rowHeaders, ih]; omega

@[simp] theorem rowArities_length (rows : List Row) : (rowArities rows).length = 2 * rows.length := by
  induction rows with
  | nil => rfl
  | cons row rest ih => simp [rowArities, ih]; omega

@[simp] theorem rowBases_length (rows : List Row) (childCursor guardCursor : ℕ) :
    (rowBases rows childCursor guardCursor).length = 2 * rows.length := by
  induction rows generalizing childCursor guardCursor with
  | nil => rfl
  | cons row rest ih => simp [rowBases, ih]; omega

/-- One complete shared cache: headers, bases, arities, both incidence streams
and the declared root IDs. This logical specification has a separate generation
trace; its physical loading below does not imply free list construction. -/
def serializedRows (heapOffset : ℕ) (rows : List Row) (roots : List ℕ) : List ℕ :=
  let children := rowChildren rows
  let guards := rowGuards rows
  rowHeaders rows ++ rowBases rows (heapOffset + 6 * rows.length)
    (heapOffset + 6 * rows.length + children.length) ++ rowArities rows ++
    children ++ guards ++ roots

theorem serializedRows_length (heapOffset : ℕ) (rows : List Row) (roots : List ℕ) :
    (serializedRows heapOffset rows roots).length =
      6 * rows.length + (rowChildren rows).length + (rowGuards rows).length + roots.length := by
  simp [serializedRows]; omega

/-- Each incidence segment is copied as the first append operand once;
the already constructed suffix is never traversed by that operation. -/
inductive IncidenceCopyTrace (field : Row → List ℕ) : List Row → List ℕ → ℕ → Prop
  | nil : IncidenceCopyTrace field [] [] 0
  | cons (row : Row) (rest : List Row) (tail copied : List ℕ) (tailVisits copyVisits : ℕ)
      (suffix : IncidenceCopyTrace field rest tail tailVisits)
      (copy : CompilerAppendTrace.AppendTrace (field row) tail copied copyVisits) :
      IncidenceCopyTrace field (row :: rest) copied (tailVisits + copyVisits + 1)

theorem incidence_copy_trace (field : Row → List ℕ) (rows : List Row) :
    IncidenceCopyTrace field rows (rows.flatMap field) (rows.length + (rows.flatMap field).length) := by
  induction rows with
  | nil => exact IncidenceCopyTrace.nil
  | cons row rest ih =>
      have copied := CompilerAppendTrace.append_exists (field row) (rest.flatMap field)
      have trace := IncidenceCopyTrace.cons row rest (rest.flatMap field)
        (field row ++ rest.flatMap field) (rest.length + (rest.flatMap field).length)
        (field row).length ih copied
      convert trace using 1 <;> simp [List.flatMap_cons, List.length_append] <;> omega

/-- The two incidence streams have independent executable append traces.
These counts concern source-list construction, not fetched instruction ticks. -/
theorem incidence_copy_bounds (rows : List Row) :
    IncidenceCopyTrace Row.children rows (rowChildren rows) (rows.length + (rowChildren rows).length) ∧
    IncidenceCopyTrace Row.guards rows (rowGuards rows) (rows.length + (rowGuards rows).length) := by
  exact ⟨incidence_copy_trace Row.children rows, incidence_copy_trace Row.guards rows⟩

def cacheHeap (width : ℕ) (heap : Array (Word width)) (rows : List Row) (roots : List ℕ) : Array (Word width) :=
  Controller.Cost.ForestCursorMaterialize.allocatedHeap width heap (serializedRows heap.size rows roots)

@[simp] theorem cacheHeap_size (heap : Array (Word width)) (rows : List Row) (roots : List ℕ) :
    (cacheHeap width heap rows roots).size =
      heap.size + 6 * rows.length + (rowChildren rows).length + (rowGuards rows).length + roots.length := by
  simp [cacheHeap, serializedRows_length]; omega

theorem header_tag_value (rows : List Row) (index : ℕ) (valid : index < rows.length) :
    (rowHeaders rows)[2 * index]'(by rw [rowHeaders_length]; omega) = (rows[index]'valid).tag := by
  induction rows generalizing index with
  | nil => simp at valid
  | cons row rest ih =>
      cases index with
      | zero => rfl
      | succ index =>
          have next : index < rest.length := by simpa using valid
          simpa only [rowHeaders, List.flatMap_cons, List.cons_append, List.nil_append,
            Nat.mul_succ, List.getElem_cons_succ] using ih index next

theorem header_head_value (rows : List Row) (index : ℕ) (valid : index < rows.length) :
    (rowHeaders rows)[2 * index + 1]'(by rw [rowHeaders_length]; omega) = (rows[index]'valid).head := by
  induction rows generalizing index with
  | nil => simp at valid
  | cons row rest ih =>
      cases index with
      | zero => rfl
      | succ index =>
          have next : index < rest.length := by simpa using valid
          simpa only [rowHeaders, List.flatMap_cons, List.cons_append, List.nil_append,
            Nat.mul_succ, List.getElem_cons_succ] using ih index next

/-- The physical header word follows from the actual complete cache allocation;
there is no caller-supplied source-cell oracle at this endpoint. -/
theorem cache_header_word (heap : Array (Word width)) (rows : List Row) (roots : List ℕ)
    (index : ℕ) (valid : index < (rowHeaders rows).length) :
    (cacheHeap width heap rows roots)[heap.size + index]'(by simp; rw [rowHeaders_length] at valid; omega) =
      word width ((rowHeaders rows)[index]'valid) := by
  have beforeSegment : serializedRows heap.size rows roots = rowHeaders rows ++
      (rowBases rows (heap.size + 6 * rows.length)
        (heap.size + 6 * rows.length + (rowChildren rows).length) ++ rowArities rows ++
        rowChildren rows ++ rowGuards rows ++ roots) := by simp only [serializedRows, List.append_assoc]
  have bounded : index < (serializedRows heap.size rows roots).length := by
    rw [beforeSegment, List.length_append]
    omega
  have stored := Controller.Cost.ForestCursorMaterialize.allocatedHeap_cell width heap
    (serializedRows heap.size rows roots) index bounded
  simpa only [cacheHeap, beforeSegment, List.getElem_append_left valid] using stored

/-- Raw row correspondence plus actual cache loading derives the stored tag. -/
theorem cache_tag_word (heap : Array (Word width)) (graph : DAG n) (rows : List Row) (roots : List ℕ)
    (corresponds : RowsMatch graph rows) (index : Fin graph.nodeCount) :
    (cacheHeap width heap rows roots)[heap.size + 2 * index.val]'(by simp; rw [corresponds.length_eq]; omega) =
      word width (tagValue graph index) := by
  have bounded : index.val < rows.length := by rw [corresponds.length_eq]; exact index.isLt
  have stored := cache_header_word heap rows roots (2 * index.val) (by rw [rowHeaders_length]; omega)
  rw [header_tag_value rows index.val bounded] at stored
  have tag : rows[index.val].tag = tagValue graph index := by
    cases gateEq : graph.node index <;> simpa only [tagValue, gateEq] using (corresponds.node index).1
  exact stored.trans (congrArg (word width) tag)

/-- Every source-cache word is popped and allocated exactly once. The input
words remain charged in the initial state, and the caller suffix is retained. -/
theorem serializedRows_load (machine : Program width 4) (state : State width 4)
    (rows : List Row) (roots : List ℕ) (suffix : List (Word width)) (base : ℕ)
    (pc : state.pc = word width base) (running : state.halted = false)
    (input : state.stack = (serializedRows state.heap.size rows roots).map (word width) ++ suffix)
    (fits : base + 2 * (serializedRows state.heap.size rows roots).length < 2 ^ width)
    (room : state.heap.size + (serializedRows state.heap.size rows roots).length ≤ 2 ^ width)
    (block : BlockAt machine base (InputLoad.code (width := width) (serializedRows state.heap.size rows roots).length)) :
    ∃ final, Execution machine state final
      (2 * (serializedRows state.heap.size rows roots).length) state.liveWords ∧
      final.heap = state.heap ++ ((serializedRows state.heap.size rows roots).map (word width)).toArray ∧
      final.stack = suffix ∧ final.output = state.output ∧
      final.pc = word width (base + 2 * (serializedRows state.heap.size rows roots).length) ∧ final.halted = false := by
  simpa only [List.length_map] using InputLoad.code_execution machine state
    ((serializedRows state.heap.size rows roots).map (word width)) suffix base pc running input
      (by simpa only [List.length_map] using fits)
      (by simpa only [List.length_map] using room)
      (by simpa only [List.length_map] using block)

/-- The declared output list retains its occurrence order. Distinct declared
positions may name the same terminal, and every occurrence is serialized. -/
def RootsMatch (graph : DAG n) (roots : List ℕ) : Prop :=
  roots = graph.roots.map Fin.val

/-- Source correspondence derives the complete packet size rather than
assigning a free size bound to an enriched cache representation. -/
theorem matched_packet_length (heapOffset : ℕ) (graph : DAG n) (rows : List Row)
    (roots : List ℕ) (corresponds : RowsMatch graph rows) (rootMatches : RootsMatch graph roots) :
    (serializedRows heapOffset rows roots).length =
      6 * graph.nodeCount + graph.childIncidences + graph.guardIncidences + graph.roots.length := by
  obtain ⟨children, guards⟩ := matched_incidence_lengths graph rows corresponds
  rw [serializedRows_length, corresponds.length_eq, children, guards]
  change 6 * graph.nodeCount + graph.childIncidences + graph.guardIncidences + roots.length = _
  rw [rootMatches, List.length_map]

/-- All cache segments before the declared-root stream. -/
def packetPrefix (heapOffset : ℕ) (rows : List Row) : List ℕ :=
  rowHeaders rows ++ rowBases rows (heapOffset + 6 * rows.length)
    (heapOffset + 6 * rows.length + (rowChildren rows).length) ++ rowArities rows ++
    rowChildren rows ++ rowGuards rows

theorem packetPrefix_length (heapOffset : ℕ) (rows : List Row) :
    (packetPrefix heapOffset rows).length =
      6 * rows.length + (rowChildren rows).length + (rowGuards rows).length := by
  simp [packetPrefix]; omega

theorem packet_prefix_roots (heapOffset : ℕ) (rows : List Row) (roots : List ℕ) :
    serializedRows heapOffset rows roots = packetPrefix heapOffset rows ++ roots := by
  simp only [serializedRows, packetPrefix, List.append_assoc]

/-- The loaded root word is derived from actual packet allocation. The root
position is an occurrence index, so repeated output IDs remain distinguishable. -/
theorem cache_root_word (heap : Array (Word width)) (rows : List Row) (roots : List ℕ)
    (position : ℕ) (valid : position < roots.length) :
    (cacheHeap width heap rows roots)[heap.size +
      (6 * rows.length + (rowChildren rows).length + (rowGuards rows).length) + position]'
      (by simp; omega) = word width (roots[position]'valid) := by
  let beforeSegment := packetPrefix heap.size rows
  have length : beforeSegment.length = 6 * rows.length + (rowChildren rows).length + (rowGuards rows).length :=
    packetPrefix_length heap.size rows
  have packet := packet_prefix_roots heap.size rows roots
  have bounded : beforeSegment.length + position < (serializedRows heap.size rows roots).length := by
    rw [packet, List.length_append]
    change beforeSegment.length + position < beforeSegment.length + roots.length
    omega
  have stored := Controller.Cost.ForestCursorMaterialize.allocatedHeap_cell width heap
    (serializedRows heap.size rows roots) (beforeSegment.length + position) bounded
  have storedValue : (serializedRows heap.size rows roots)[beforeSegment.length + position]'bounded =
      roots[position]'valid := by
    simp only [packet, beforeSegment, List.getElem_append_right (as := packetPrefix heap.size rows)
      (bs := roots) (i := (packetPrefix heap.size rows).length + position) (Nat.le_add_right _ _),
      Nat.add_sub_cancel_left]
  rw [storedValue] at stored
  simpa only [cacheHeap, length, Nat.add_assoc] using stored

/-- Raw row and declared-root correspondence identify the loaded root with
its exact typed source node. No runtime graph-root function query is required. -/
theorem cache_declared_root_word (heap : Array (Word width)) (graph : DAG n)
    (rows : List Row) (roots : List ℕ) (rootMatches : RootsMatch graph roots)
    (position : Fin graph.roots.length) :
    (cacheHeap width heap rows roots)[heap.size +
      (6 * rows.length + (rowChildren rows).length + (rowGuards rows).length) + position.val]'
      (by
        have lengths : roots.length = graph.roots.length := by rw [rootMatches, List.length_map]
        have bounded := position.isLt
        simp only [cacheHeap_size]
        omega) =
      word width (graph.roots.get position).val := by
  have valid : position.val < roots.length := by rw [rootMatches, List.length_map]; exact position.isLt
  have stored := cache_root_word heap rows roots position.val valid
  have rootsEq : roots = graph.roots.map Fin.val := rootMatches
  simpa only [rootsEq, List.getElem_map, List.get_eq_getElem] using stored

/-- The three source columns execute both real incidence-count passes.
The cost counts one row dispatch, six output cons cells, two cursor additions,
and the inspected-cons/increment pair for each executed count step. -/
inductive RowColumnsTrace : List Row → ℕ → ℕ → List ℕ → List ℕ → List ℕ → ℕ → Prop
  | nil (childCursor guardCursor : ℕ) : RowColumnsTrace [] childCursor guardCursor [] [] [] 0
  | cons (row : Row) (rest : List Row) (childCursor guardCursor : ℕ)
      (headers bases arities : List ℕ) (work : ℕ)
      (childrenOne guardsOne childrenTwo guardsTwo : ℕ)
      (countChildrenOne : CountSourceTrace row.children 0 (countSource row.children 0) childrenOne)
      (countGuardsOne : CountSourceTrace row.guards 0 (countSource row.guards 0) guardsOne)
      (countChildrenTwo : CountSourceTrace row.children 0 (countSource row.children 0) childrenTwo)
      (countGuardsTwo : CountSourceTrace row.guards 0 (countSource row.guards 0) guardsTwo)
      (suffix : RowColumnsTrace rest (childCursor + countSource row.children 0)
        (guardCursor + countSource row.guards 0) headers bases arities work) :
      RowColumnsTrace (row :: rest) childCursor guardCursor
        (row.tag :: row.head :: headers) (childCursor :: guardCursor :: bases)
        (countSource row.children 0 :: countSource row.guards 0 :: arities)
        (work + 9 + 2 * (childrenOne + guardsOne + childrenTwo + guardsTwo))

/-- Column generation is linear in the original rows and repeated incidences.
This is an executable source-list construction relation, not a RAM instruction
count and not an evaluation of an arbitrary graph-node function. -/
theorem row_columns_trace (rows : List Row) (childCursor guardCursor : ℕ) :
    RowColumnsTrace rows childCursor guardCursor (rowHeaders rows)
      (rowBases rows childCursor guardCursor) (rowArities rows)
      (9 * rows.length + 4 * ((rowChildren rows).length + (rowGuards rows).length)) := by
  induction rows generalizing childCursor guardCursor with
  | nil => exact RowColumnsTrace.nil childCursor guardCursor
  | cons row rest ih =>
      have trace := RowColumnsTrace.cons row rest childCursor guardCursor
        (rowHeaders rest)
        (rowBases rest (childCursor + countSource row.children 0) (guardCursor + countSource row.guards 0))
        (rowArities rest)
        (9 * rest.length + 4 * ((rowChildren rest).length + (rowGuards rest).length))
        row.children.length row.guards.length row.children.length row.guards.length
        (countSource_trace row.children 0) (countSource_trace row.guards 0)
        (countSource_trace row.children 0) (countSource_trace row.guards 0)
        (ih (childCursor + countSource row.children 0) (guardCursor + countSource row.guards 0))
      convert trace using 1 <;>
        simp only [rowHeaders, rowArities, rowBases, rowChildren, rowGuards,
          List.flatMap_cons, List.cons_append, List.nil_append, List.length_cons, List.length_append] <;> omega

/-- Segment assembly traverses each first append operand once. The root suffix
is retained rather than repeatedly copied during preceding segment assembly. -/
def PacketAssemblyTrace (heapOffset : ℕ) (rows : List Row) (roots : List ℕ) : Prop :=
  let children := rowChildren rows
  let guards := rowGuards rows
  let arities := rowArities rows
  let bases := rowBases rows (heapOffset + 6 * rows.length) (heapOffset + 6 * rows.length + children.length)
  CompilerAppendTrace.AppendTrace guards roots (guards ++ roots) guards.length ∧
  CompilerAppendTrace.AppendTrace children (guards ++ roots) (children ++ guards ++ roots) children.length ∧
  CompilerAppendTrace.AppendTrace arities (children ++ guards ++ roots)
    (arities ++ children ++ guards ++ roots) arities.length ∧
  CompilerAppendTrace.AppendTrace bases (arities ++ children ++ guards ++ roots)
    (bases ++ arities ++ children ++ guards ++ roots) bases.length ∧
  CompilerAppendTrace.AppendTrace (rowHeaders rows) (bases ++ arities ++ children ++ guards ++ roots)
    (serializedRows heapOffset rows roots) (rowHeaders rows).length

theorem packet_assembly_trace (heapOffset : ℕ) (rows : List Row) (roots : List ℕ) :
    PacketAssemblyTrace heapOffset rows roots := by
  unfold PacketAssemblyTrace
  simp only [serializedRows, List.append_assoc]
  exact ⟨CompilerAppendTrace.append_exists _ _, CompilerAppendTrace.append_exists _ _,
    CompilerAppendTrace.append_exists _ _, CompilerAppendTrace.append_exists _ _,
    CompilerAppendTrace.append_exists _ _⟩

/-- The complete generation witnesses include column counting, copying both
incidence streams, and actual segment assembly. Their source-list operation
budget is linear in the exact typed input size; loading is charged separately. -/
theorem source_packet_generation (heapOffset : ℕ) (graph : DAG n) (rows : List Row)
    (roots : List ℕ) (corresponds : RowsMatch graph rows) (rootMatches : RootsMatch graph roots) :
    RowColumnsTrace rows (heapOffset + 6 * rows.length)
      (heapOffset + 6 * rows.length + (rowChildren rows).length)
      (rowHeaders rows)
      (rowBases rows (heapOffset + 6 * rows.length) (heapOffset + 6 * rows.length + (rowChildren rows).length))
      (rowArities rows) (9 * graph.nodeCount + 4 * (graph.childIncidences + graph.guardIncidences)) ∧
    IncidenceCopyTrace Row.children rows (rowChildren rows) (graph.nodeCount + graph.childIncidences) ∧
    IncidenceCopyTrace Row.guards rows (rowGuards rows) (graph.nodeCount + graph.guardIncidences) ∧
    PacketAssemblyTrace heapOffset rows roots ∧
    (serializedRows heapOffset rows roots).length =
      6 * graph.nodeCount + graph.childIncidences + graph.guardIncidences + graph.roots.length := by
  obtain ⟨children, guards⟩ := matched_incidence_lengths graph rows corresponds
  refine ⟨?_, ?_, ?_, packet_assembly_trace heapOffset rows roots,
    matched_packet_length heapOffset graph rows roots corresponds rootMatches⟩
  · simpa only [corresponds.length_eq, children, guards] using
      row_columns_trace rows (heapOffset + 6 * rows.length)
        (heapOffset + 6 * rows.length + (rowChildren rows).length)
  · simpa only [corresponds.length_eq, children] using (incidence_copy_bounds rows).1
  · simpa only [corresponds.length_eq, guards] using (incidence_copy_bounds rows).2

/-- A global input header precedes the shared node cache. All four list counts
are executed on the supplied source lists; the declared channel count is one
input scalar. This header is loaded once, rather than supplied as free registers. -/
def globalHeader (channels : ℕ) (rows : List Row) (roots : List ℕ) : List ℕ :=
  [channels, countSource rows 0, countSource (rowChildren rows) 0,
    countSource (rowGuards rows) 0, countSource roots 0]

@[simp] theorem globalHeader_length (channels : ℕ) (rows : List Row) (roots : List ℕ) :
    (globalHeader channels rows roots).length = 5 := rfl

/-- Actual independent passes derive every global arity word from raw input. -/
theorem global_header_count_traces (rows : List Row) (roots : List ℕ) :
    CountSourceTrace rows 0 (countSource rows 0) rows.length ∧
    CountSourceTrace (rowChildren rows) 0 (countSource (rowChildren rows) 0) (rowChildren rows).length ∧
    CountSourceTrace (rowGuards rows) 0 (countSource (rowGuards rows) 0) (rowGuards rows).length ∧
    CountSourceTrace roots 0 (countSource roots 0) roots.length :=
  ⟨countSource_trace rows 0, countSource_trace (rowChildren rows) 0,
    countSource_trace (rowGuards rows) 0, countSource_trace roots 0⟩

theorem matched_global_header (graph : DAG n) (rows : List Row) (roots : List ℕ)
    (corresponds : RowsMatch graph rows) (rootMatches : RootsMatch graph roots) :
    globalHeader n rows roots =
      [n, graph.nodeCount, graph.childIncidences, graph.guardIncidences, graph.roots.length] := by
  obtain ⟨children, guards⟩ := matched_incidence_lengths graph rows corresponds
  have rootsEq : roots = graph.roots.map Fin.val := rootMatches
  simp only [globalHeader, countSource_value, Nat.zero_add, corresponds.length_eq, children, guards,
    rootsEq, List.length_map]

/-- Node-column bases are relative to the cache origin, five words beyond the
input origin. The origin is part of the input ABI, not a runtime heap-size query. -/
def inputPacket (channels heapOffset : ℕ) (rows : List Row) (roots : List ℕ) : List ℕ :=
  globalHeader channels rows roots ++ serializedRows (heapOffset + 5) rows roots

/-- Exact typed input correspondence at the cold origin. The payload retains
all declared roots and repeated child or guard incidences. -/
theorem matched_cold_input_words (graph : DAG n) (rows : List Row) (roots : List ℕ)
    (corresponds : RowsMatch graph rows) (rootMatches : RootsMatch graph roots) :
    (inputPacket n 0 rows roots).map (word width) =
      [word width n, word width graph.nodeCount, word width graph.childIncidences,
        word width graph.guardIncidences, word width graph.roots.length] ++
      (serializedRows 5 rows roots).map (word width) := by
  rw [inputPacket, List.map_append, matched_global_header graph rows roots corresponds rootMatches]
  rfl

theorem matched_input_packet_length (heapOffset : ℕ) (graph : DAG n) (rows : List Row)
    (roots : List ℕ) (corresponds : RowsMatch graph rows) (rootMatches : RootsMatch graph roots) :
    (inputPacket n heapOffset rows roots).length =
      5 + 6 * graph.nodeCount + graph.childIncidences + graph.guardIncidences + graph.roots.length := by
  rw [inputPacket, List.length_append, globalHeader_length,
    matched_packet_length (heapOffset + 5) graph rows roots corresponds rootMatches]
  omega

/-- The complete typed source packet is loaded once by the fixed cold loader.
The represented word input, retained suffix and output are all included in
peak storage. The program contains thirty-three instructions independently of
node counts; source serialization has its own operational construction traces. -/
theorem cold_input_packet_execution (program : Program width 4) (base : ℕ)
    (graph : DAG n) (rows : List Row) (roots : List ℕ)
    (corresponds : RowsMatch graph rows) (rootMatches : RootsMatch graph roots)
    (suffix output : List (Word width)) (address loaded temporary : Word width)
    (fits : base + 33 < 2 ^ width)
    (room : (inputPacket n 0 rows roots).length ≤ 2 ^ width)
    (block : BlockAt program base (ForestInputMetadata.fullCode width base)) :
    ∃ final, Execution program
      ((counterState (#[] : Array (Word width)) base address loaded temporary).frame
        ((inputPacket n 0 rows roots).map (word width) ++ suffix) output)
      final
        (27 + 7 * (6 * graph.nodeCount + graph.childIncidences + graph.guardIncidences + graph.roots.length))
        (10 + (6 * graph.nodeCount + graph.childIncidences + graph.guardIncidences + graph.roots.length) +
          suffix.length + output.length) ∧
      final.heap = ((inputPacket n 0 rows roots).map (word width)).toArray ∧
      final.stack = suffix ∧ final.output = output ∧
      final.pc = word width (base + 33) ∧ final.halted = false := by
  let payload := (serializedRows 5 rows roots).map (word width)
  have payloadLength : payload.length =
      6 * graph.nodeCount + graph.childIncidences + graph.guardIncidences + graph.roots.length := by
    simpa only [payload, List.length_map] using matched_packet_length 5 graph rows roots corresponds rootMatches
  have packetWords := matched_cold_input_words (width := width) graph rows roots corresponds rootMatches
  have packetLength := matched_input_packet_length 0 graph rows roots corresponds rootMatches
  obtain ⟨final, trace, heap, stack, emitted, pc, running⟩ :=
    ForestInputMetadata.cold_packet_execution program base n graph.nodeCount graph.childIncidences
      graph.guardIncidences graph.roots.length payload suffix output address loaded temporary
      payloadLength fits (by rw [payloadLength]; omega) block
  rw [payloadLength] at trace
  refine ⟨final, ?_, ?_, stack, emitted, pc, running⟩
  · simpa only [packetWords, ForestInputMetadata.headerWords, payload,
      List.append_assoc] using trace
  · rw [packetWords]
    simpa only [ForestInputMetadata.headerWords, payload, List.append_toArray] using heap

/-- A local refinement of the length-dependent unrolled loading program.
It supplies exact stored input words, but its code generation and resident
program size are separate from the fixed-code uniform loader contract. -/
theorem input_packet_load (machine : Program width 4) (state : State width 4)
    (channels : ℕ) (rows : List Row) (roots : List ℕ) (suffix : List (Word width)) (base : ℕ)
    (pc : state.pc = word width base) (running : state.halted = false)
    (input : state.stack = (inputPacket channels state.heap.size rows roots).map (word width) ++ suffix)
    (fits : base + 2 * (inputPacket channels state.heap.size rows roots).length < 2 ^ width)
    (room : state.heap.size + (inputPacket channels state.heap.size rows roots).length ≤ 2 ^ width)
    (block : BlockAt machine base (InputLoad.code (width := width)
      (inputPacket channels state.heap.size rows roots).length)) :
    ∃ final, Execution machine state final
      (2 * (inputPacket channels state.heap.size rows roots).length) state.liveWords ∧
      final.heap = state.heap ++ ((inputPacket channels state.heap.size rows roots).map (word width)).toArray ∧
      final.stack = suffix ∧ final.output = state.output ∧
      final.pc = word width (base + 2 * (inputPacket channels state.heap.size rows roots).length) ∧
      final.halted = false := by
  simpa only [List.length_map] using InputLoad.code_execution machine state
    ((inputPacket channels state.heap.size rows roots).map (word width)) suffix base pc running input
      (by simpa only [List.length_map] using fits)
      (by simpa only [List.length_map] using room)
      (by simpa only [List.length_map] using block)

set_option backward.isDefEq.respectTransparency false in
/-- Every global metadata field is an actual loaded word of the input packet. -/
theorem input_header_word (heap : Array (Word width)) (channels : ℕ) (rows : List Row)
    (roots : List ℕ) (index : Fin 5) :
    (Controller.Cost.ForestCursorMaterialize.allocatedHeap width heap
      (inputPacket channels heap.size rows roots))[heap.size + index.val]'
      (by simp [inputPacket]; omega) =
      word width ((globalHeader channels rows roots)[index.val]'(by simpa using index.isLt)) := by
  have valid : index.val < (inputPacket channels heap.size rows roots).length := by
    simp only [inputPacket, List.length_append, globalHeader_length]
    omega
  have stored := Controller.Cost.ForestCursorMaterialize.allocatedHeap_cell width heap
    (inputPacket channels heap.size rows roots) index.val valid
  simpa only [inputPacket, List.getElem_append_left (by simpa using index.isLt : index.val < (globalHeader channels rows roots).length)] using stored

private theorem pair_first_value (items : List α) (first second : α → ℕ)
    (index : ℕ) (valid : index < items.length) :
    (items.flatMap (fun item => [first item, second item]))[2 * index]'
      (by simp; omega) = first (items[index]'valid) := by
  induction items generalizing index with
  | nil => simp at valid
  | cons item rest ih =>
      cases index with
      | zero => rfl
      | succ index =>
          have next : index < rest.length := by simpa using valid
          simpa only [List.flatMap_cons, List.cons_append, List.nil_append,
            Nat.mul_succ, List.getElem_cons_succ] using ih index next

private theorem pair_second_value (items : List α) (first second : α → ℕ)
    (index : ℕ) (valid : index < items.length) :
    (items.flatMap (fun item => [first item, second item]))[2 * index + 1]'
      (by simp; omega) = second (items[index]'valid) := by
  induction items generalizing index with
  | nil => simp at valid
  | cons item rest ih =>
      cases index with
      | zero => rfl
      | succ index =>
          have next : index < rest.length := by simpa using valid
          simpa only [List.flatMap_cons, List.cons_append, List.nil_append,
            Nat.mul_succ, List.getElem_cons_succ] using ih index next

theorem row_arity_values (rows : List Row) (index : ℕ) (valid : index < rows.length) :
    (rowArities rows)[2 * index]'(by rw [rowArities_length]; omega) =
      countSource (rows[index]'valid).children 0 ∧
    (rowArities rows)[2 * index + 1]'(by rw [rowArities_length]; omega) =
      countSource (rows[index]'valid).guards 0 :=
  ⟨pair_first_value rows (fun row => countSource row.children 0)
      (fun row => countSource row.guards 0) index valid,
    pair_second_value rows (fun row => countSource row.children 0)
      (fun row => countSource row.guards 0) index valid⟩

/-- Base columns store the cumulative lengths of preceding raw incidence
rows. These prefix lists describe the stored address; an interpreter reads the
column and does not reconstruct the prefix list at runtime. -/
theorem row_base_values (rows : List Row) (childCursor guardCursor index : ℕ)
    (valid : index < rows.length) :
    (rowBases rows childCursor guardCursor)[2 * index]'(by rw [rowBases_length]; omega) =
      childCursor + (rowChildren (rows.take index)).length ∧
    (rowBases rows childCursor guardCursor)[2 * index + 1]'(by rw [rowBases_length]; omega) =
      guardCursor + (rowGuards (rows.take index)).length := by
  induction rows generalizing childCursor guardCursor index with
  | nil => simp at valid
  | cons row rest ih =>
      cases index with
      | zero => simp [rowBases, rowChildren, rowGuards]
      | succ index =>
          have next : index < rest.length := by simpa using valid
          obtain ⟨child, guard⟩ := ih (childCursor + countSource row.children 0)
            (guardCursor + countSource row.guards 0) index next
          constructor
          · simpa only [rowBases, Nat.mul_succ, List.getElem_cons_succ,
              List.take_succ_cons, rowChildren, List.flatMap_cons, List.length_append,
              countSource_value, Nat.zero_add, Nat.add_assoc] using child
          · simpa only [rowBases, Nat.mul_succ, List.getElem_cons_succ,
              List.take_succ_cons, rowGuards, List.flatMap_cons, List.length_append,
              countSource_value, Nat.zero_add, Nat.add_assoc] using guard

/-- Every middle segment is read from its actual allocated input words.
The decomposition is a source-layout proof, not an executable address oracle. -/
theorem allocated_segment_word (heap : Array (Word width)) (beforeSegment segment suffix : List ℕ)
    (index : ℕ) (valid : index < segment.length) :
    (Controller.Cost.ForestCursorMaterialize.allocatedHeap width heap
      (beforeSegment ++ segment ++ suffix))[heap.size + beforeSegment.length + index]'
      (by simp; omega) = word width (segment[index]'valid) := by
  have bounded : beforeSegment.length + index < (beforeSegment ++ segment ++ suffix).length := by simp; omega
  have stored := Controller.Cost.ForestCursorMaterialize.allocatedHeap_cell width heap
    (beforeSegment ++ segment ++ suffix) (beforeSegment.length + index) bounded
  simpa only [List.append_assoc, List.getElem_append_right (as := beforeSegment)
    (bs := segment ++ suffix) (i := beforeSegment.length + index) (Nat.le_add_right _ _),
    Nat.add_sub_cancel_left, List.getElem_append_left valid, Nat.add_assoc] using stored

/-- Both incidence bases are actual stored source words. Repeated references
contribute to the preceding-row prefix counts and retain distinct positions. -/
theorem cache_base_words (heap : Array (Word width)) (rows : List Row) (roots : List ℕ)
    (index : ℕ) (valid : index < rows.length) :
    (cacheHeap width heap rows roots)[heap.size + 2 * rows.length + 2 * index]'
      (by simp; omega) = word width
        (heap.size + 6 * rows.length + (rowChildren (rows.take index)).length) ∧
    (cacheHeap width heap rows roots)[heap.size + 2 * rows.length + (2 * index + 1)]'
      (by simp; omega) = word width
        (heap.size + 6 * rows.length + (rowChildren rows).length +
          (rowGuards (rows.take index)).length) := by
  let bases := rowBases rows (heap.size + 6 * rows.length)
    (heap.size + 6 * rows.length + (rowChildren rows).length)
  let suffix := rowArities rows ++ rowChildren rows ++ rowGuards rows ++ roots
  have packet : serializedRows heap.size rows roots = rowHeaders rows ++ bases ++ suffix := by
    simp only [serializedRows, bases, suffix, List.append_assoc]
  obtain ⟨child, guard⟩ := row_base_values rows (heap.size + 6 * rows.length)
    (heap.size + 6 * rows.length + (rowChildren rows).length) index valid
  have first := allocated_segment_word heap (rowHeaders rows) bases suffix (2 * index)
    (by simp only [bases, rowBases_length]; omega)
  have second := allocated_segment_word heap (rowHeaders rows) bases suffix (2 * index + 1)
    (by simp only [bases, rowBases_length]; omega)
  rw [show bases[2 * index]'(by simp only [bases, rowBases_length]; omega) =
    heap.size + 6 * rows.length + (rowChildren (rows.take index)).length from child] at first
  rw [show bases[2 * index + 1]'(by simp only [bases, rowBases_length]; omega) =
    heap.size + 6 * rows.length + (rowChildren rows).length +
      (rowGuards (rows.take index)).length from guard] at second
  exact ⟨by simpa only [cacheHeap, packet, rowHeaders_length] using first,
    by simpa only [cacheHeap, packet, rowHeaders_length] using second⟩

/-- The child arity of every source node is physically present in the loaded
cache. Matching ties the computed count to the exact typed child occurrences. -/
theorem cache_child_arity_word (heap : Array (Word width)) (graph : DAG n)
    (rows : List Row) (roots : List ℕ) (corresponds : RowsMatch graph rows)
    (index : Fin graph.nodeCount) :
    (cacheHeap width heap rows roots)[heap.size + 4 * rows.length + 2 * index.val]'
      (by simp; rw [corresponds.length_eq]; omega) = word width (graph.node index).children.length := by
  let beforeSegment := rowHeaders rows ++ rowBases rows (heap.size + 6 * rows.length)
    (heap.size + 6 * rows.length + (rowChildren rows).length)
  have length : beforeSegment.length = 4 * rows.length := by simp [beforeSegment]; omega
  have packet : serializedRows heap.size rows roots =
      beforeSegment ++ rowArities rows ++ (rowChildren rows ++ rowGuards rows ++ roots) := by
    simp only [serializedRows, beforeSegment, List.append_assoc]
  have valid : index.val < rows.length := by rw [corresponds.length_eq]; exact index.isLt
  have cell := allocated_segment_word heap beforeSegment (rowArities rows)
    (rowChildren rows ++ rowGuards rows ++ roots) (2 * index.val) (by rw [rowArities_length]; omega)
  rw [(row_arity_values rows index.val valid).1, (matched_counts graph rows corresponds index).1] at cell
  simpa only [cacheHeap, packet, length] using cell

/-- Guard arities retain all repeated labels and delimit the uniform guard
loop; they are loaded counts rather than a runtime list-length query. -/
theorem cache_guard_arity_word (heap : Array (Word width)) (graph : DAG n)
    (rows : List Row) (roots : List ℕ) (corresponds : RowsMatch graph rows)
    (index : Fin graph.nodeCount) :
    (cacheHeap width heap rows roots)[heap.size + 4 * rows.length + (2 * index.val + 1)]'
      (by simp; rw [corresponds.length_eq]; omega) = word width (graph.node index).guardLabels.length := by
  let beforeSegment := rowHeaders rows ++ rowBases rows (heap.size + 6 * rows.length)
    (heap.size + 6 * rows.length + (rowChildren rows).length)
  have length : beforeSegment.length = 4 * rows.length := by simp [beforeSegment]; omega
  have packet : serializedRows heap.size rows roots =
      beforeSegment ++ rowArities rows ++ (rowChildren rows ++ rowGuards rows ++ roots) := by
    simp only [serializedRows, beforeSegment, List.append_assoc]
  have valid : index.val < rows.length := by rw [corresponds.length_eq]; exact index.isLt
  have cell := allocated_segment_word heap beforeSegment (rowArities rows)
    (rowChildren rows ++ rowGuards rows ++ roots) (2 * index.val + 1) (by rw [rowArities_length]; omega)
  rw [(row_arity_values rows index.val valid).2, (matched_counts graph rows corresponds index).2] at cell
  simpa only [cacheHeap, packet, length] using cell

end Controller.Cost.ForestIndexedOperands
