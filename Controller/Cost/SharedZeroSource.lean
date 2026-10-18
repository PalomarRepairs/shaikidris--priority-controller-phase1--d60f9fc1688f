module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedZeroDictionary

@[expose] public section

/-! Fixed zero-system rows read the once-allocated coordinate table; the queried activity reads one shared source slot. -/
namespace Controller.Cost.SharedZeroSource
open Controller.CNF Controller.Decoder Controller.Decoder.DAG Controller.Decoder.ZeroSystem
open Controller.Cost.GateProgram Controller.Cost.ForestZeroEmit

def fixedRows (graph : DAG n) (b : Nat) (target : Fin n) (T F : Finset (Fin n)) :
    List (Clause (Fin (n + graph.nodeCount))) :=
  SharedZeroTemplate.touchRows (n + graph.nodeCount) ++
    (graph.forwardClauses ++ graph.channelClauses b target T F).map
      (fun clause => clause.map (fun literal => (graph.zeroIndex literal.1, literal.2)))

def references (graph : DAG n) (b : Nat) (target : Fin n) (T F : Finset (Fin n))
    (base slot : Nat) (root : Fin graph.nodeCount) : List (List (Reference (n + graph.nodeCount))) :=
  SharedCoordinateTable.rows base (fixedRows graph b target T F) ++
    [[SharedZeroCode.rootReference n graph.nodeCount slot root]]

theorem constructor_shared (graph : DAG n) (b : Nat) (target : Fin n) (T F : Finset (Fin n))
    (left right : Fin graph.nodeCount) :
    ForestZeroAdmissibleCaller.constructorCode width entry protectedEnd recordHeader endHeader returnPC
      (references graph b target T F base slot left) =
    ForestZeroAdmissibleCaller.constructorCode width entry protectedEnd recordHeader endHeader returnPC
      (references graph b target T F base slot right) :=
  SharedZeroCode.constructor_root_irrel _ left right

theorem originalRows_eq (graph : DAG n) (b : Nat) (target : Fin n) (T F : Finset (Fin n))
    (root : Fin graph.nodeCount) :
    ForestZeroAssembly.originalRows (references graph b target T F base slot root) =
      (SharedZeroTemplate.formula graph b target root T F).clauses.toList := by
  simp [references, ForestZeroAssembly.originalRows, SharedCoordinateTable.rows_coordinates,
    SharedCoordinateTable.rows, SharedCoordinateTable.reference, fixedRows,
    SharedZeroTemplate.formula, DAG.finiteZeroSystem, DAG.zeroIndex, DAG.zeroSystem,
    ofClauses, relabel, Controller.CNF.OrderedFormula.relabel, Controller.CNF.OrderedFormula.Clause.relabel, implicationClause, positiveClause, SharedZeroCode.rootReference,
    List.map_map, Function.comp_def, List.append_assoc]
  rfl

theorem dictionary_size (graph : DAG n) (b : Nat) (target : Fin n) (T F : Finset (Fin n))
    (root : Fin graph.nodeCount) (heap : Array (Word width))
    (layout : ForestZeroDictionary.Layout (n + graph.nodeCount) heap.size) :
    (ForestZeroAdmissibleCaller.constructorDictionary heap layout (ForestZeroCompile.empty _)
      (references graph b target T F base slot root)).coordinates.size = n + graph.nodeCount := by
  unfold ForestZeroAdmissibleCaller.constructorDictionary
  have rowsEq : ForestZeroAssembly.originalRows
      (ForestZeroAdmissibleCaller.reservedReferences (references graph b target T F base slot root)) =
      SharedZeroTemplate.touchRows (n + graph.nodeCount) ++
        ((graph.forwardClauses ++ graph.channelClauses b target T F).map
          (fun clause => clause.map (fun literal => (graph.zeroIndex literal.1, literal.2))) ++
        [[((⟨n + root.val, by omega⟩ : Fin (n + graph.nodeCount)), false)]] ++ [[]]) := by
    simp [ForestZeroAdmissibleCaller.reservedReferences, ForestZeroAssembly.originalRows,
      references, fixedRows, SharedCoordinateTable.rows, SharedCoordinateTable.reference,
      SharedZeroCode.rootReference, List.map_map, Function.comp_def, List.append_assoc]
  rw [rowsEq]
  exact SharedZeroDictionary.dictionary_size _

theorem source_stored (graph : DAG n) (b : Nat) (target : Fin n) (T F : Finset (Fin n))
    (root : Fin graph.nodeCount) (heap : Array (Word width)) (slot : Nat)
    (slotPositive : 0 < slot) (slotBound : slot < heap.size)
    (header : heap[0]? = some (word width n)) :
    ∀ item ∈ (references graph b target T F heap.size slot root).flatten,
      StoredReference
        ((heap ++ (SharedCoordinateTable.words width (n + graph.nodeCount)).toArray).set slot
          (word width root.val) (by simp; omega))
        n (heap.size + (n + graph.nodeCount)) item := by
  intro item member
  simp only [references, List.flatten_append, List.flatten_cons, List.flatten_nil,
    List.append_nil, List.mem_append, List.mem_singleton] at member
  rcases member with fixed | queried
  · exact SharedCoordinateTable.rows_stored_after_root heap n slot header slotPositive slotBound
      (word width root.val) (fixedRows graph b target T F) item fixed
  · subst item
    apply SharedZeroRootSelect.root_stored _ n graph.nodeCount slot _ root
    · simp
    · omega
    · exact slotPositive
    · simpa [Array.getElem?_append, show 0 < heap.size from by omega] using header

theorem occurrence_bound (graph : DAG n) (b : Nat) (target : Fin n) (T F : Finset (Fin n))
    (root : Fin graph.nodeCount) :
    (references graph b target T F base slot root).length +
      (references graph b target T F base slot root).flatten.length ≤ 11 * (graph.countedSize + 1) := by
  have size := SharedZeroTemplate.input_size_bound graph b target root T F
  have rowsEq := originalRows_eq (base := base) (slot := slot) graph b target T F root
  have rowLength := congrArg List.length rowsEq
  have literalLength := congrArg (fun clauses => (clauses.map List.length).sum) rowsEq
  simp only [ForestZeroAssembly.originalRows, List.length_map, List.map_map,
    Function.comp_def, List.length_flatten] at rowLength literalLength ⊢
  simp only [Controller.Cost.Horn.inputSize] at size
  rw [rowLength, literalLength]
  simp only [Array.length_toList]
  omega

theorem constructor_code_bound (graph : DAG n) (b : Nat) (target : Fin n) (T F : Finset (Fin n))
    (root : Fin graph.nodeCount) :
    (ForestZeroAdmissibleCaller.constructorCode width entry protectedEnd recordHeader endHeader returnPC
      (references graph b target T F base slot root)).length ≤ 410 * (graph.countedSize + 1) := by
  have occurrences := occurrence_bound (base := base) (slot := slot) graph b target T F root
  have codeBound := ForestZeroAdmissibleCaller.constructorCode_length width entry protectedEnd recordHeader endHeader
    returnPC (references graph b target T F base slot root)
  omega

theorem dictionary_fixed (graph : DAG n) (b : Nat) (target : Fin n) (T F : Finset (Fin n))
    (root : Fin graph.nodeCount) (heap : Array (Word width))
    (layout : ForestZeroDictionary.Layout (n + graph.nodeCount) heap.size) :
    (ForestZeroAdmissibleCaller.constructorDictionary heap layout (ForestZeroCompile.empty _)
      (references graph b target T F base slot root)) =
      (ForestZeroCompile.compileRows (ForestZeroCompile.empty _) (SharedZeroTemplate.touchRows (n + graph.nodeCount))).1 := by
  unfold ForestZeroAdmissibleCaller.constructorDictionary
  have rowsEq : ForestZeroAssembly.originalRows
      (ForestZeroAdmissibleCaller.reservedReferences (references graph b target T F base slot root)) =
      SharedZeroTemplate.touchRows (n + graph.nodeCount) ++
        ((graph.forwardClauses ++ graph.channelClauses b target T F).map
          (fun clause => clause.map (fun literal => (graph.zeroIndex literal.1, literal.2))) ++
        [[((⟨n + root.val, by omega⟩ : Fin (n + graph.nodeCount)), false)]] ++ [[]]) := by
    simp [ForestZeroAdmissibleCaller.reservedReferences, ForestZeroAssembly.originalRows,
      references, fixedRows, SharedCoordinateTable.rows, SharedCoordinateTable.reference,
      SharedZeroCode.rootReference, List.map_map, Function.comp_def, List.append_assoc]
  rw [rowsEq]
  exact SharedZeroDictionary.dictionary_fixed _

theorem dictionary_root_irrel (graph : DAG n) (b : Nat) (target : Fin n) (T F : Finset (Fin n))
    (left right : Fin graph.nodeCount) (heap : Array (Word width))
    (layout : ForestZeroDictionary.Layout (n + graph.nodeCount) heap.size) :
    ForestZeroAdmissibleCaller.constructorDictionary heap layout (ForestZeroCompile.empty _)
      (references graph b target T F base slot left) =
    ForestZeroAdmissibleCaller.constructorDictionary heap layout (ForestZeroCompile.empty _)
      (references graph b target T F base slot right) := by
  rw [dictionary_fixed graph b target T F left heap layout, dictionary_fixed graph b target T F right heap layout]


theorem references_length_root_irrel (graph : DAG n) (b : Nat) (target : Fin n) (T F : Finset (Fin n))
    (left right : Fin graph.nodeCount) :
    (references graph b target T F base slot left).length =
      (references graph b target T F base slot right).length := by
  simp [references]

theorem references_literals_root_irrel (graph : DAG n) (b : Nat) (target : Fin n) (T F : Finset (Fin n))
    (left right : Fin graph.nodeCount) :
    (references graph b target T F base slot left).flatten.length =
      (references graph b target T F base slot right).flatten.length := by
  simp [references]

theorem constructor_heap_size_root_irrel (graph : DAG n) (b : Nat) (target : Fin n) (T F : Finset (Fin n))
    (left right : Fin graph.nodeCount) (heap : Array (Word width))
    (layout : ForestZeroDictionary.Layout (n + graph.nodeCount) heap.size) :
    (ForestZeroAdmissibleCaller.constructorHeap heap layout (ForestZeroCompile.empty _)
      (references graph b target T F base slot left) n).size =
    (ForestZeroAdmissibleCaller.constructorHeap heap layout (ForestZeroCompile.empty _)
      (references graph b target T F base slot right) n).size := by
  rw [ForestZeroAdmissibleCaller.constructorHeap_size, ForestZeroAdmissibleCaller.constructorHeap_size,
    references_length_root_irrel graph b target T F left right,
    references_literals_root_irrel graph b target T F left right,
    dictionary_root_irrel graph b target T F left right heap layout]

end Controller.Cost.SharedZeroSource
