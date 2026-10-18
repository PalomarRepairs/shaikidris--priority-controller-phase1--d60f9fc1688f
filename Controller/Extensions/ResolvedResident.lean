module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Extensions.ResolvedProgram
public import Controller.Cost.EnumerationResident
public import Controller.Cost.SharedZeroMeaning
public import Controller.Cost.EnumerationFixedResident

@[expose] public section

/-! A quiet returning query for consistently resolved DAGs. Literal coordinates
occupy consecutive source cells; instructions refer to occurrence addresses.
Changing a selector changes source words while preserving the query code. -/
namespace Controller.Extensions.ResolvedResident
open Controller.CNF Controller.Decoder Controller.Decoder.DAG
open Controller.Extensions.BoundedAnd Controller.Cost Controller.Cost.GateProgram
open Controller.Cost.ForestZeroEmit Controller.Cost.ForestZeroDictionary
open Controller.Cost.ForestZeroCompile Controller.Cost.ForestZeroAdmissibleCaller

/-- One physical cell per original literal occurrence. -/
def rowRefs (base : Nat) : List (Literal (Fin ambient)) → List (Reference ambient)
  | [] => []
  | literal :: rest =>
    { slot := base, raw := literal.1.val, activity := false,
      coordinate := literal.1, positive := literal.2 } :: rowRefs (base + 1) rest

def refs (base : Nat) : List (Clause (Fin ambient)) → List (List (Reference ambient))
  | [] => []
  | row :: rest => rowRefs base row :: refs (base + row.length) rest

@[simp] theorem rowRefs_length (row : Clause (Fin ambient)) :
    (rowRefs base row).length = row.length := by
  induction row generalizing base with
  | nil => rfl
  | cons literal rest ih => simp [rowRefs, ih]

@[simp] theorem refs_length (rows : List (Clause (Fin ambient))) :
    (refs base rows).length = rows.length := by
  induction rows generalizing base with
  | nil => rfl
  | cons row rest ih => simp [refs, ih]

@[simp] theorem refs_literals (rows : List (Clause (Fin ambient))) :
    (refs base rows).flatten.length = rows.flatten.length := by
  induction rows generalizing base with
  | nil => rfl
  | cons row rest ih => simp [refs, ih]

@[simp] theorem row_coordinates (row : Clause (Fin ambient)) :
    (rowRefs base row).map (fun item => (item.coordinate, item.positive)) = row := by
  induction row generalizing base with
  | nil => rfl
  | cons literal rest ih => simp [rowRefs, ih]

@[simp] theorem original_rows (rows : List (Clause (Fin ambient))) :
    ForestZeroAssembly.originalRows (refs base rows) = rows := by
  induction rows generalizing base with
  | nil => rfl
  | cons row rest ih =>
    simpa only [refs, ForestZeroAssembly.originalRows, List.map_cons, row_coordinates] using congrArg (List.cons row) (ih (base := base + row.length))

theorem row_wire (left right : Clause (Fin ambient))
    (signs : left.map Prod.snd = right.map Prod.snd) :
    List.Forall₂ SharedZeroCode.WireEqual (rowRefs base left) (rowRefs base right) := by
  induction left generalizing right base with
  | nil => cases right <;> simp_all [rowRefs]
  | cons literal rest ih =>
    cases right with
    | nil => simp at signs
    | cons other tail =>
      simp only [List.map_cons, List.cons.injEq] at signs
      exact .cons ⟨rfl, rfl, signs.1⟩ (ih _ signs.2)

theorem rows_wire (left right : List (Clause (Fin ambient)))
    (signs : left.map (List.map Prod.snd) = right.map (List.map Prod.snd)) :
    List.Forall₂ (List.Forall₂ SharedZeroCode.WireEqual) (refs base left) (refs base right) := by
  induction left generalizing right base with
  | nil => cases right <;> simp_all [refs]
  | cons row rest ih =>
    cases right with
    | nil => simp at signs
    | cons other tail =>
      simp only [List.map_cons, List.cons.injEq] at signs
      have lengths : row.length = other.length := by
        simpa only [List.length_map] using congrArg List.length signs.1
      simpa only [refs, lengths] using List.Forall₂.cons (row_wire row other signs.1) (ih tail signs.2 (base := base + other.length))

theorem source_entry_congr (left right : List (List (Reference ambient)))
    (same : List.Forall₂ (List.Forall₂ SharedZeroCode.WireEqual) left right) :
    SharedQuerySourceCode.solverEntry width entry keep left =
      SharedQuerySourceCode.solverEntry width entry keep right := by
  unfold SharedQuerySourceCode.solverEntry reservedReferences
  rw [SharedZeroCode.query_congr _ _ (List.rel_append same (.cons .nil .nil))]

theorem source_code_congr (left right : List (List (Reference ambient)))
    (same : List.Forall₂ (List.Forall₂ SharedZeroCode.WireEqual) left right) :
    SharedQuerySourceCode.code width entry keep left = SharedQuerySourceCode.code width entry keep right := by
  unfold SharedQuerySourceCode.code
  rw [same.length_eq, source_entry_congr left right same, SharedZeroCode.constructor_congr left right same]

theorem code_congr (left right : List (List (Reference ambient)))
    (same : List.Forall₂ (List.Forall₂ SharedZeroCode.WireEqual) left right) :
    EnumerationResident.code width entry keep count scratch left =
      EnumerationResident.code width entry keep count scratch right := by
  unfold EnumerationResident.code
  rw [source_code_congr left right same, source_entry_congr left right same]

/-- Tautologies fix the dictionary independently of selected children. -/
def rows (graph : DAG n) (right : Finset (Fin graph.nodeCount)) (b : Nat)
    (target : Fin n) (root : Fin graph.nodeCount) : List (Clause (Fin (n + graph.nodeCount))) :=
  (SharedZeroTemplate.formula (resolved graph right) b target root ∅ ∅).clauses.toList

theorem node_signs (graph : DAG n) (left right : Finset (Fin graph.nodeCount)) (i : Fin graph.nodeCount) :
    ((resolved graph left).nodeClauses i).map (List.map Prod.snd) =
      ((resolved graph right).nodeClauses i).map (List.map Prod.snd) := by
  unfold DAG.nodeClauses
  simp only [resolved]
  cases h : graph.node i <;>
    simp [Gate.resolve, Controller.Decoder.ZeroSystem.implicationClause,
      Controller.Decoder.ZeroSystem.positiveClause, List.map_map, Function.comp_def]

theorem rows_signs (graph : DAG n) (left right : Finset (Fin graph.nodeCount)) (b : Nat)
    (target : Fin n) (first second : Fin graph.nodeCount) :
    (rows graph left b target first).map (List.map Prod.snd) =
      (rows graph right b target second).map (List.map Prod.snd) := by
  have forward : ((resolved graph left).forwardClauses.map (List.map Prod.snd)) =
      ((resolved graph right).forwardClauses.map (List.map Prod.snd)) := by
    simp only [DAG.forwardClauses, List.map_flatMap]
    congr 1
    funext i
    exact node_signs graph left right i
  simp only [rows, SharedZeroTemplate.formula, ofClauses, List.toList_toArray, List.map_append,
    DAG.finiteZeroSystem, relabel, Controller.CNF.OrderedFormula.relabel, Array.toList_map, List.map_map,
    Controller.CNF.OrderedFormula.Clause.relabel, Function.comp_def, DAG.zeroSystem]
  rw [forward]
  simp [DAG.channelClauses, DAG.trueUnitClauses, DAG.falseUnitClauses,
    Controller.Decoder.ZeroSystem.implicationClause, Controller.Decoder.ZeroSystem.positiveClause]

/-- Every selector and queried root uses the identical resident instruction list. -/
theorem selector_root_code (graph : DAG n) (left right : Finset (Fin graph.nodeCount)) (b : Nat)
    (target : Fin n) (first second : Fin graph.nodeCount) :
    EnumerationResident.code width entry keep count scratch (refs base (rows graph left b target first)) =
      EnumerationResident.code width entry keep count scratch (refs base (rows graph right b target second)) :=
  code_congr _ _ (rows_wire _ _ (rows_signs graph left right b target first second))

theorem rows_bound (graph : DAG n) (right : Finset (Fin graph.nodeCount)) (b : Nat)
    (target : Fin n) (root : Fin graph.nodeCount) :
    (rows graph right b target root).length + (rows graph right b target root).flatten.length ≤
      11 * (graph.countedSize + 1) := by
  have bound := SharedZeroTemplate.input_size_bound (resolved graph right) b target root ∅ ∅
  have size := ResolvedQuery.resolved_size graph right
  simp only [Horn.inputSize, rows, List.length_flatten, Array.length_toList] at bound ⊢
  omega

/-- The source packet retains channel/node headers and one coordinate per occurrence. -/
def packet (width channels nodes : Nat) (clauses : List (Clause (Fin ambient))) : Array (Word width) :=
  #[word width channels, word width nodes] ++
    (clauses.flatten.map (fun literal => word width literal.1.val)).toArray

@[simp] theorem packet_size (clauses : List (Clause (Fin ambient))) :
    (packet width channels nodes clauses).size = 2 + clauses.flatten.length := by
  simp only [packet, Array.size_append, List.size_toArray, List.length_map]
  simp

@[simp] theorem packet_channel (clauses : List (Clause (Fin ambient))) :
    (packet width channels nodes clauses)[0]? = some (word width channels) := by simp [packet]

@[simp] theorem packet_nodes (clauses : List (Clause (Fin ambient))) :
    (packet width channels nodes clauses)[1]? = some (word width nodes) := by simp [packet]

theorem row_stored (heap : Array (Word width)) (channels sourceEnd base : Nat)
    (row : Clause (Fin ambient)) (sourceBound : sourceEnd ≤ heap.size)
    (headerRoom : 0 < sourceEnd) (header : heap[0]? = some (word width channels))
    (bound : base + row.length ≤ sourceEnd)
    (cells : ∀ i (hi : i < row.length), heap[base + i]? = some (word width row[i].1.val)) :
    ∀ item ∈ rowRefs base row, StoredReference heap channels sourceEnd item := by
  induction row generalizing base with
  | nil => simp [rowRefs]
  | cons literal rest ih =>
    intro item member
    simp only [rowRefs, List.mem_cons] at member
    rcases member with rfl | tail
    · exact ⟨sourceBound, by change base < sourceEnd; simp only [List.length_cons] at bound; omega, headerRoom,
        by
          change heap[base]? = some (word width literal.1.val)
          have h := cells 0 (by simp)
          change heap[base + 0]? = some (word width literal.1.val) at h
          simpa only [Nat.add_zero] using h, header, by simp⟩
    · apply ih (base + 1) (by simp only [List.length_cons] at bound; omega) _ item tail
      intro i hi
      have h := cells (i + 1) (by simp; omega)
      change heap[base + (i + 1)]? = some (word width rest[i].1.val) at h
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

theorem refs_stored (heap : Array (Word width)) (channels sourceEnd base : Nat)
    (clauses : List (Clause (Fin ambient))) (sourceBound : sourceEnd ≤ heap.size)
    (headerRoom : 0 < sourceEnd) (header : heap[0]? = some (word width channels))
    (bound : base + clauses.flatten.length ≤ sourceEnd)
    (cells : ∀ i (hi : i < clauses.flatten.length),
      heap[base + i]? = some (word width clauses.flatten[i].1.val)) :
    ∀ item ∈ (refs base clauses).flatten, StoredReference heap channels sourceEnd item := by
  induction clauses generalizing base with
  | nil => simp [refs]
  | cons row rest ih =>
    intro item member
    simp only [refs, List.flatten_cons, List.mem_append] at member
    rcases member with first | tail
    · apply row_stored heap channels sourceEnd base row sourceBound headerRoom header
        (by simp only [List.flatten_cons, List.length_append] at bound; omega) _ item first
      intro i hi
      simpa only [List.flatten_cons, List.getElem_append_left hi] using
        cells i (by simp only [List.flatten_cons, List.length_append]; omega)
    · apply ih (base + row.length) (by simp only [List.flatten_cons, List.length_append] at bound; omega) _ item tail
      intro i hi
      simpa only [List.flatten_cons, List.getElem_append_right (by omega : row.length ≤ row.length + i),
        Nat.add_sub_cancel_left, Nat.add_assoc] using
        cells (row.length + i) (by simp only [List.flatten_cons, List.length_append]; omega)

theorem packet_stored (clauses : List (Clause (Fin ambient))) :
    ∀ item ∈ (refs 2 clauses).flatten,
      StoredReference (packet width channels nodes clauses) channels (2 + clauses.flatten.length) item := by
  apply refs_stored _ channels (2 + clauses.flatten.length) 2 clauses
    (by simp) (by omega) (packet_channel clauses) (by omega)
  intro i hi
  rw [show 2 + i = (#[word width channels, word width nodes] : Array (Word width)).size + i by rfl]
  unfold packet
  rw [Array.getElem?_append_right (Nat.le_add_right _ _)]
  simp only [Nat.add_sub_cancel_left, List.getElem?_toArray, List.getElem?_map,
    List.getElem?_eq_getElem hi, Option.map_some]


theorem touches (graph : DAG n) (right : Finset (Fin graph.nodeCount)) (b : Nat)
    (target : Fin n) (root : Fin graph.nodeCount) :
    ∃ tail, ForestZeroAssembly.originalRows (refs base (rows graph right b target root)) =
      SharedZeroTemplate.touchRows (n + graph.nodeCount) ++ tail := by
  rw [original_rows]
  exact ⟨_, rfl⟩

theorem dictionary_fixed (graph : DAG n) (right : Finset (Fin graph.nodeCount)) (b : Nat)
    (target : Fin n) (root : Fin graph.nodeCount) (heap : Array (Word width))
    (layout : Layout (n + graph.nodeCount) heap.size) :
    constructorDictionary heap layout (empty _) (refs base (rows graph right b target root)) =
      (compileRows (empty _) (SharedZeroTemplate.touchRows (n + graph.nodeCount))).1 := by
  have fixed := EnumerationFixedResident.dictionary_fixed (refs base (rows graph right b target root)) []
    (touches graph right b target root) (fun _ => false) (fun _ => false) heap layout
  simpa [EnumerationFixedResident.selected, EnumerationFixedConstructor.references,
    EnumerationFixedProfile.selectedRefs] using fixed

theorem dictionary_size (graph : DAG n) (right : Finset (Fin graph.nodeCount)) (b : Nat)
    (target : Fin n) (root : Fin graph.nodeCount) (heap : Array (Word width))
    (layout : Layout (n + graph.nodeCount) heap.size) :
    (constructorDictionary heap layout (empty _) (refs base (rows graph right b target root))).coordinates.size =
      n + graph.nodeCount := by
  rw [dictionary_fixed]
  simpa using SharedZeroDictionary.dictionary_size ([] : List (Clause (Fin (n + graph.nodeCount))))

theorem constructor_meaning (graph : DAG n) (right : Finset (Fin graph.nodeCount)) (b : Nat)
    (target : Fin n) (root : Fin graph.nodeCount) (heap : Array (Word width))
    (layout : Layout (n + graph.nodeCount) heap.size) :
    Satisfiable (constructorFormula heap layout (empty _) (empty_coherent _)
      (refs base (rows graph right b target root)) n (by omega)) ↔
      ∃ K, Admissible b target K ∧ (resolved graph right).eval (assignmentOfSet K) root = false := by
  rw [SharedZeroModel.constructor_satisfiable]
  · rw [original_rows]
    simpa [rows, ofClauses, ExtendsFixed] using
      SharedZeroTemplate.satisfiable_iff (resolved graph right) (resolved_guarded graph right) b target root ∅ ∅
  · intro assignment model
    apply SharedZeroMeaning.source_nonempty (base := 0) (slot := 0) (resolved graph right) b target ∅ ∅ root assignment
    rw [SharedZeroSource.originalRows_eq]
    simpa only [original_rows, rows] using model

theorem source_dual (graph : DAG n) (right : Finset (Fin graph.nodeCount)) (b : Nat)
    (target : Fin n) (root : Fin graph.nodeCount) :
    Horn.DualHorn (ofClauses (ForestZeroAssembly.originalRows
      (reservedReferences (refs base (rows graph right b target root))))) := by
  intro clause member
  have dual := SharedZeroTemplate.dualHorn (resolved graph right) (resolved_guarded graph right) b target root ∅ ∅
  have member' : clause ∈ rows graph right b target root ++ [[]] := by
    have eq : ForestZeroAssembly.originalRows (reservedReferences (refs base (rows graph right b target root))) =
        rows graph right b target root ++ [[]] := by
      rw [reservedReferences, ForestZeroAssembly.originalRows, List.map_append]
      change ForestZeroAssembly.originalRows (refs base (rows graph right b target root)) ++ [[]] = _
      rw [original_rows]
    simpa only [eq, ofClauses, List.mem_toArray] using member
  rcases List.mem_append.mp member' with first | last
  · exact dual clause (by simpa [rows] using first)
  · have eq : clause = [] := by simpa using last
    subst clause
    simp [Horn.DualHornClause, Horn.NegativeUnique]

/-- Two fixed dictionary regions follow the retained occurrence packet. -/
def sourceHeap (width channels nodes : Nat) (clauses : List (Clause (Fin ambient))) : Array (Word width) :=
  packet width channels nodes clauses ++ Array.replicate (2 * ambient) (word width 0)

@[simp] theorem sourceHeap_size (clauses : List (Clause (Fin ambient))) :
    (sourceHeap width channels nodes clauses).size = 2 + clauses.flatten.length + 2 * ambient := by
  simp only [sourceHeap, Array.size_append, Array.size_replicate, packet_size]

theorem sourceHeap_cell (clauses : List (Clause (Fin ambient))) (i : Nat)
    (bound : i < 2 + clauses.flatten.length) :
    (sourceHeap width channels nodes clauses)[i]? = (packet width channels nodes clauses)[i]? := by
  simp only [sourceHeap, Array.getElem?_append, packet_size, ite_eq_left bound]

def endSource (graph : DAG n) (right : Finset (Fin graph.nodeCount)) (b : Nat)
    (target : Fin n) (root : Fin graph.nodeCount) := 2 + (rows graph right b target root).flatten.length

def scratchSize (keep channels ambient : Nat) (clauses : List (Clause (Fin ambient))) : Nat :=
  EnumerationFixedResident.heapSize keep channels (refs 2 clauses) []

theorem scratch_bound (clauses : List (Clause (Fin ambient))) :
    scratchSize keep channels ambient clauses ≤
      keep + 7 + 2 * clauses.length + 2 * clauses.flatten.length + 2 * channels := by
  have bound := EnumerationFixedResident.heap_size_bound (keep := keep) (channels := channels) (refs 2 clauses) []
  simp only [refs_length, refs_literals, List.length_nil] at bound
  unfold scratchSize
  omega

theorem scratch_congr (left right : List (Clause (Fin ambient)))
    (same : left.map (List.map Prod.snd) = right.map (List.map Prod.snd)) :
    scratchSize keep channels ambient left = scratchSize keep channels ambient right := by
  have wire := rows_wire (base := 2) left right same
  have rowLength : left.length = right.length := by simpa using wire.length_eq
  have profiles : left.map List.length = right.map List.length := by
    have lengths := congrArg (List.map List.length) same
    simpa only [List.map_map, List.length_map, Function.comp_def] using lengths
  have flatLength : left.flatten.length = right.flatten.length := by
    simpa only [List.length_flatten] using congrArg List.sum profiles
  simp only [scratchSize, EnumerationFixedResident.heapSize, refs_length, refs_literals, rowLength, flatLength]

def queryCode (graph : DAG n) (right : Finset (Fin graph.nodeCount)) (b : Nat)
    (target : Fin n) (root : Fin graph.nodeCount) (width entry keep : Nat) : List (Instruction width 8) :=
  EnumerationResident.code width entry keep (n + graph.nodeCount)
    (scratchSize keep n (n + graph.nodeCount) (rows graph right b target root))
    (refs 2 (rows graph right b target root))

theorem query_uniform (graph : DAG n) (left right : Finset (Fin graph.nodeCount)) (b : Nat)
    (target : Fin n) (first second : Fin graph.nodeCount) :
    queryCode graph left b target first width entry keep = queryCode graph right b target second width entry keep := by
  unfold queryCode
  rw [scratch_congr _ _ (rows_signs graph left right b target first second)]
  exact selector_root_code graph left right b target first second

theorem query_code_bound (graph : DAG n) (right : Finset (Fin graph.nodeCount)) (b : Nat)
    (target : Fin n) (root : Fin graph.nodeCount) :
    (queryCode graph right b target root width entry keep).length ≤ 900 * (graph.countedSize + 1) := by
  have bound := ForestZeroQueryCaller.queryCode_length width (entry + 15) keep
    (reservedReferences (refs 2 (rows graph right b target root)))
  have count := rows_bound graph right b target root
  simp only [reservedReferences_length, reservedReferences_flatten, refs_length, refs_literals] at bound
  have codeEnd := EnumerationResident.code_end width entry keep (n + graph.nodeCount)
    (scratchSize keep n (n + graph.nodeCount) (rows graph right b target root))
    (refs 2 (rows graph right b target root))
  change entry + (queryCode graph right b target root width entry keep).length = _ at codeEnd
  unfold SharedQuerySourceCode.solverEntry at codeEnd
  omega

theorem constructor_size (graph : DAG n) (right : Finset (Fin graph.nodeCount)) (b : Nat)
    (target : Fin n) (root : Fin graph.nodeCount) (heap : Array (Word width))
    (layout : Layout (n + graph.nodeCount) heap.size) :
    (constructorHeap heap layout (empty _) (refs 2 (rows graph right b target root)) n).size =
      scratchSize heap.size n (n + graph.nodeCount) (rows graph right b target root) := by
  have eq := EnumerationFixedResident.heap_size (refs 2 (rows graph right b target root)) []
    (touches graph right b target root) (fun _ => false) (fun _ => false) heap layout n
  simpa [EnumerationFixedResident.selected, EnumerationFixedConstructor.references,
    EnumerationFixedProfile.selectedRefs, scratchSize] using eq

/-- The reusable boundary fixes the source packet, empty dictionary and caller frame. -/
abbrev Ready (graph : DAG n) (right : Finset (Fin graph.nodeCount)) (b : Nat)
    (target : Fin n) (root : Fin graph.nodeCount) (entry : Nat) (rest : List (Word width))
    (state : State width 8) :=
  QueryReady (ambient := n + graph.nodeCount)
    (sourceHeap width n graph.nodeCount (rows graph right b target root))
    (endSource graph right b target root) (endSource graph right b target root + n + graph.nodeCount)
    entry rest state

def readyLayout (graph : DAG n) (right : Finset (Fin graph.nodeCount)) (b : Nat)
    (target : Fin n) (root : Fin graph.nodeCount) (state : State width 8)
    (ready : Ready graph right b target root entry rest state) : Layout (n + graph.nodeCount) state.heap.size where
  tableBase := endSource graph right b target root
  inverseBase := endSource graph right b target root + n + graph.nodeCount
  tableBound := by have h := ready.heapSize; simp only [sourceHeap_size] at h; unfold endSource; omega
  inverseBound := by have h := ready.heapSize; simp only [sourceHeap_size] at h; unfold endSource; omega
  disjoint := Or.inl (by omega)

theorem ready_cell (graph : DAG n) (right : Finset (Fin graph.nodeCount)) (b : Nat)
    (target : Fin n) (root : Fin graph.nodeCount) (state : State width 8)
    (ready : Ready graph right b target root entry rest state) (i : Nat)
    (bound : i < endSource graph right b target root) :
    state.heap[i]? = (packet width n graph.nodeCount (rows graph right b target root))[i]? :=
  (ready.sourceFrame.2.2 i bound).trans (sourceHeap_cell _ i bound)

set_option maxHeartbeats 200000 in
set_option maxRecDepth 4096 in
theorem ready_conditions (graph : DAG n) (right : Finset (Fin graph.nodeCount)) (b : Nat)
    (target : Fin n) (root : Fin graph.nodeCount)
    (program : Program (width) 8)
    (entry : Nat) (rest : List (Word (width)))
    (state : State (width) 8)
    (ready : Ready graph right b target root entry rest state)
    (entryBound : entry ≤ 1024 * (graph.countedSize + 1))
    (capacity : 4096 * (graph.countedSize + 1) < 2 ^ width) :
    EnumerationResident.Conditions (ambient := n + graph.nodeCount) n program state (readyLayout graph right b target root state ready)
      (refs 2 (rows graph right b target root)) (endSource graph right b target root) graph.nodeCount entry rest (by omega) := by
  let layout := readyLayout graph right b target root state ready
  let rs := refs 2 (rows graph right b target root)
  have counts := rows_bound graph right b target root
  have graphSize := graph.countedSize_eq
  have cap := capacity
  have hs : state.heap.size = endSource graph right b target root + 2 * (n + graph.nodeCount) := by
    simpa only [sourceHeap_size, endSource] using ready.heapSize
  have sourceBound : endSource graph right b target root ≤ state.heap.size := by omega
  have positive : 1 < endSource graph right b target root := by unfold endSource; omega
  have stored : ∀ item ∈ rs.flatten, StoredReference state.heap n (endSource graph right b target root) item := by
    intro item member
    have old := packet_stored (width := width) (channels := n)
      (nodes := graph.nodeCount) (rows graph right b target root) item member
    exact ⟨sourceBound, old.slotBound, old.headerBound,
      (ready_cell graph right b target root state ready item.slot old.slotBound).trans old.slotWord,
      (ready_cell graph right b target root state ready 0 (by omega)).trans (packet_channel _), old.coordinateEq⟩
  refine {
    sourceReferences := stored
    sourceBeforeTable := le_refl _
    sourceBeforeInverse := by dsimp [readyLayout]; omega
    sourceBound := sourceBound
    sourcePositive := by omega
    sourceChannel := (ready_cell graph right b target root state ready 0 (by omega)).trans (packet_channel _)
    sourceNodes := (ready_cell graph right b target root state ready 1 positive).trans (packet_nodes _)
    ambientEq := rfl
    adjacent := by dsimp [readyLayout]; omega
    tablePositive := by dsimp [readyLayout]; omega
    sourceHeaderRoom := positive
    sourceDual := source_dual graph right b target root
    sourceEndpoint := by dsimp [readyLayout]; omega
    constructorRoom := ?_
    room := ?_
    residentCapacity := ?_ }
  · simp only [refs_length, refs_literals]
    unfold endSource at hs
    omega
  · let dictionary := constructorDictionary state.heap layout (empty _) rs
    let clauses := constructorClauses state.heap layout (empty _) (empty_coherent _) rs n (by omega)
    have ds : dictionary.coordinates.size = n + graph.nodeCount := dictionary_size graph right b target root state.heap layout
    have cs := constructorClauses_length state.heap layout (empty _) (empty_coherent _) rs n (by omega)
    have cb : clauses.length ≤ rs.length + 1 := by
      change clauses.length = _ at cs
      split_ifs at cs <;> omega
    have ls := constructorClauses_profile_bound state.heap layout (empty _) (empty_coherent _) rs n (by omega)
    change (clauses.map List.length).sum ≤ rs.flatten.length + dictionary.coordinates.size at ls
    have heapBound := scratch_bound (keep := state.heap.size) (channels := n) (rows graph right b target root)
    rw [← constructor_size graph right b target root state.heap layout] at heapBound
    have occurrenceBound := Horn.IndexScanCold.occurrences_length_le clauses
      ((constructorHeap state.heap layout (empty _) rs n).size + 5 * dictionary.coordinates.size + 4)
    change (constructorHeap state.heap layout (empty _) rs n).size + 5 * dictionary.coordinates.size + 4 +
      3 * clauses.length + (clauses.map List.length).sum +
      2 * (Horn.IndexScan.occurrences clauses
        ((constructorHeap state.heap layout (empty _) rs n).size + 5 * dictionary.coordinates.size + 4)).length < _
    simp only [rs, refs_length, refs_literals] at cb ls
    dsimp only [rs] at heapBound occurrenceBound ⊢
    unfold endSource at hs
    omega
  · have size := query_code_bound (width := width) (entry := entry) (keep := state.heap.size)
      graph right b target root
    have endpoint := EnumerationResident.code_end (width) entry state.heap.size (n + graph.nodeCount)
      (scratchSize state.heap.size n (n + graph.nodeCount) (rows graph right b target root)) rs
    change entry + (queryCode graph right b target root _ entry state.heap.size).length = _ at endpoint
    dsimp only [rs] at endpoint
    omega

set_option maxHeartbeats 200000 in
set_option maxRecDepth 4096 in
/-- One fixed instruction array handles every expansion and root. A query
returns with its source/frame retained, output unchanged, and no live-space
accumulation. The ready packet is the input boundary of this callback. -/
theorem execution (graph : DAG n) (right : Finset (Fin graph.nodeCount)) (b : Nat)
    (target : Fin n) (reference root : Fin graph.nodeCount)
    (program : Program (width) 8)
    (entry : Nat) (rest : List (Word (width)))
    (state : State (width) 8)
    (ready : Ready graph right b target root entry rest state)
    (entryBound : entry ≤ 1024 * (graph.countedSize + 1))
    (capacity : 4096 * (graph.countedSize + 1) < 2 ^ width)
    (present : SharedRootRead.BlockAt program entry
      (queryCode graph ∅ b target reference (width) entry state.heap.size)) :
    ∃ answer : Bool, ∃ final ticks peak,
      Execution program state final ticks peak ∧ final.halted = false ∧
      final.reg 4 = word (width) (if answer then 1 else 0) ∧
      ticks ≤ 4700 * (graph.countedSize + 1) ∧ peak ≤ state.liveWords + 200 * (graph.countedSize + 1) ∧
      final.output = state.output ∧ final.liveWords = state.liveWords ∧
      (answer = true ↔ ∃ K, Admissible b target K ∧ (resolved graph right).eval (assignmentOfSet K) root = false) ∧
      Ready graph right b target root
        (entry + (queryCode graph ∅ b target reference (width) entry state.heap.size).length) rest final := by
  let layout := readyLayout graph right b target root state ready
  have physical : SharedRootRead.BlockAt program entry
      (EnumerationResident.code (width) entry state.heap.size
        (constructorDictionary state.heap layout (empty _) (refs 2 (rows graph right b target root))).coordinates.size
        (constructorHeap state.heap layout (empty _) (refs 2 (rows graph right b target root)) n).size
        (refs 2 (rows graph right b target root))) := by
    rw [dictionary_size, constructor_size]
    change SharedRootRead.BlockAt program entry (queryCode graph right b target root _ entry state.heap.size)
    rw [query_uniform graph right ∅ b target root reference]
    exact present
  obtain ⟨answer, final, ticks, peak, trace, running, decision, time, space, output, meaning, finalReady⟩ :=
    EnumerationResident.execution n program state _ layout (refs 2 (rows graph right b target root))
      (endSource graph right b target root) graph.nodeCount entry rest (by omega)
      (ready_conditions graph right b target root program entry rest state ready entryBound capacity) physical ready
  have semantic := constructor_meaning (base := 2) graph right b target root state.heap layout
  have counts := rows_bound graph right b target root
  have graphSize := graph.countedSize_eq
  simp only [refs_length, refs_literals] at time space
  have live : final.liveWords = state.liveWords := by
    simp only [State.liveWords, output, finalReady.heapSize, ready.heapSize, finalReady.stack, ready.stack]
  refine ⟨answer, final, ticks, peak, trace, running, decision, by omega, by omega, output, live,
    meaning.trans semantic, ?_⟩
  have endpoint := EnumerationResident.code_end (width) entry state.heap.size (n + graph.nodeCount)
    (scratchSize state.heap.size n (n + graph.nodeCount) (rows graph right b target root))
    (refs 2 (rows graph right b target root))
  change entry + (queryCode graph right b target root _ entry state.heap.size).length = _ at endpoint
  rw [query_uniform graph right ∅ b target root reference] at endpoint
  rw [endpoint]
  exact finalReady

theorem source_size_uniform (graph : DAG n) (left right : Finset (Fin graph.nodeCount)) (b : Nat)
    (target : Fin n) (first second : Fin graph.nodeCount) :
    (sourceHeap width n graph.nodeCount (rows graph left b target first)).size =
      (sourceHeap width n graph.nodeCount (rows graph right b target second)).size := by
  have signs := rows_signs graph left right b target first second
  have profiles := congrArg (List.map List.length) signs
  simp only [List.map_map, List.length_map, Function.comp_def] at profiles
  have flat := congrArg List.sum profiles
  simp only [sourceHeap_size, List.length_flatten, flat]

def initial (graph : DAG n) (right : Finset (Fin graph.nodeCount)) (b : Nat)
    (target : Fin n) (root : Fin graph.nodeCount) (width : Nat)
    (rest output : List (Word width)) : State width 8 where
  reg r := if r = 1 then word width (endSource graph right b target root)
    else if r = 2 then word width (endSource graph right b target root + n + graph.nodeCount)
    else word width 0
  heap := sourceHeap width n graph.nodeCount (rows graph right b target root)
  stack := rest
  output := output
  pc := word width 0
  halted := false

theorem initial_ready (graph : DAG n) (right : Finset (Fin graph.nodeCount)) (b : Nat)
    (target : Fin n) (root : Fin graph.nodeCount) (rest output : List (Word width)) :
    Ready graph right b target root 0 rest (initial graph right b target root width rest output) := by
  refine ⟨rfl, ForestZeroBackendFrame.refl _ (by simp only [sourceHeap_size, endSource]; omega),
    ?_, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · intro coordinate
    change (sourceHeap width n graph.nodeCount (rows graph right b target root))[
      endSource graph right b target root + coordinate.val]? = some (word width 0)
    unfold sourceHeap endSource
    rw [Array.getElem?_append_right (by rw [packet_size]; omega)]
    simp only [packet_size, Nat.add_sub_cancel_left, Array.getElem?_replicate,
      ite_eq_left (show coordinate.val < 2 * (n + graph.nodeCount) by have := coordinate.isLt; omega)]
  all_goals simp [initial]

/-- Program code is selected once. Only the packet varies at runtime. -/
def program (graph : DAG n) (b : Nat) (target : Fin n) (reference : Fin graph.nodeCount) :
    Program (ResolvedQuery.wordWidth graph) 8 :=
  (queryCode graph ∅ b target reference (ResolvedQuery.wordWidth graph) 0
    (sourceHeap (ResolvedQuery.wordWidth graph) n graph.nodeCount (rows graph ∅ b target reference)).size).toArray

set_option maxRecDepth 4096 in
/-- Concrete packet-entry execution, with all capacity and code-placement
premises discharged. The callback returns the decision in register four;
source generation, traversal and final witness extraction are caller work. -/
theorem from_packet (graph : DAG n) (right : Finset (Fin graph.nodeCount)) (b : Nat)
    (target : Fin n) (reference root : Fin graph.nodeCount)
    (rest output : List (Word (ResolvedQuery.wordWidth graph))) :
    ∃ answer : Bool, ∃ final ticks peak,
      Execution (program graph b target reference)
        (initial graph right b target root (ResolvedQuery.wordWidth graph) rest output) final ticks peak ∧
      final.halted = false ∧ final.reg 4 = word (ResolvedQuery.wordWidth graph) (if answer then 1 else 0) ∧
      ticks ≤ 4700 * (graph.countedSize + 1) ∧
      programWords (program graph b target reference) + peak ≤
        4000 * (graph.countedSize + 1) + rest.length + output.length ∧
      final.output = output ∧
      final.liveWords = (initial graph right b target root (ResolvedQuery.wordWidth graph) rest output).liveWords ∧
      (answer = true ↔ ∃ K, Admissible b target K ∧ (resolved graph right).eval (assignmentOfSet K) root = false) ∧
      Ready graph right b target root (program graph b target reference).size rest final := by
  let state := initial graph right b target root (ResolvedQuery.wordWidth graph) rest output
  have sameHeap : state.heap.size =
      (sourceHeap (ResolvedQuery.wordWidth graph) n graph.nodeCount (rows graph ∅ b target reference)).size :=
    source_size_uniform graph right ∅ b target root reference
  have present : SharedRootRead.BlockAt (program graph b target reference) 0
      (queryCode graph ∅ b target reference (ResolvedQuery.wordWidth graph) 0 state.heap.size) := by
    rw [sameHeap]
    intro offset below
    simp only [program, Nat.zero_add, List.getElem?_toArray]
  obtain ⟨answer, final, ticks, peak, trace, running, decision, time, space, out, live, meaning, ready⟩ :=
    execution graph right b target reference root (program graph b target reference) 0 rest state
      (initial_ready graph right b target root rest output) (by omega) (ResolvedQuery.capacity graph) present
  have codeBound := query_code_bound (width := ResolvedQuery.wordWidth graph) (entry := 0)
    (keep := (sourceHeap (ResolvedQuery.wordWidth graph) n graph.nodeCount (rows graph ∅ b target reference)).size)
    graph ∅ b target reference
  have counts := rows_bound graph right b target root
  have graphSize := graph.countedSize_eq
  have initialLive : state.liveWords ≤ 13 * (graph.countedSize + 1) + 11 + rest.length + output.length := by
    simp only [state, initial, State.liveWords, sourceHeap_size]
    omega
  refine ⟨answer, final, ticks, peak, trace, running, decision, time, ?_, out, live, meaning, ?_⟩
  · simp only [programWords, program, List.size_toArray]
    omega
  · simpa only [program, List.size_toArray, Nat.zero_add, sameHeap] using ready

/-- A fetched return branch re-enters the callback without changing any data. -/
theorem reenter (graph : DAG n) (right : Finset (Fin graph.nodeCount)) (b : Nat)
    (target : Fin n) (root : Fin graph.nodeCount) (program : Program width 8)
    (entry next : Nat) (rest : List (Word width)) (state : State width 8)
    (ready : Ready graph right b target root next rest state)
    (fits : next < 2 ^ width)
    (atReturn : program[next]? = some (.branchZero 0 (word width entry))) :
    Execution program state { state with pc := word width entry } 1 state.liveWords ∧
      Ready graph right b target root entry rest { state with pc := word width entry } := by
  have transition : programStep program state = some { state with pc := word width entry } := by
    rw [RawTransferLoops.fetched program state next _ ready.position fits atReturn]
    simp only [step, ready.running, Bool.false_eq_true, ite_false, ready.zeroRegister, word,
      Nat.zero_mod, ite_true, State.advance]
  constructor
  · simpa only [State.liveWords, Nat.max_self] using Execution.cons transition (Execution.refl _)
  · exact { ready with position := rfl }

end Controller.Extensions.ResolvedResident
