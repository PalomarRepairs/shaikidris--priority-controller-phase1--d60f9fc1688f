module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestZeroControlLoad
public import Controller.Cost.ForestZeroResident
public import Controller.Cost.ForestZeroReferenceCone
public import Controller.Cost.ForestZeroUnits
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Data.Nat.Log

public import Mathlib.Tactic.FinCases

@[expose] public section

/-! Declared source occurrences produce cone rows and their actual negative
root unit. Positional query identities preserve repeated declared roots.
Resident fetch formation and the complete original-controller semantic
projection are composed with these source producers. -/
namespace Controller.Cost.ForestZeroSourcePlan
open Controller.Decoder Controller.Decoder.DAG Controller.CNF
open Controller.Cost Controller.Cost.ForestIndexedOperands
open Controller.Cost.ForestZeroSource Controller.Cost.ForestZeroEmit
open Controller.Cost.ForestZeroRows Controller.Cost.ForestZeroReferenceCone
open Controller.Cost.ForestZeroAdmissibleCaller

/-- The negative unit is the original declared occurrence, never a new ID. -/
def query (graph : DAG n) (rows : List Row) (rawRoots : List Nat)
    (rowsMatch : RowsMatch graph rows) (position : Fin graph.roots.length) :
    List (List (Reference (n + graph.nodeCount))) :=
  referenceCone graph rows rowsMatch (graph.roots.get position)
    (rootReference graph rows rawRoots position false) [] ++
      [[rootReference graph rows rawRoots position false]]

def queries (graph : DAG n) (rows : List Row) (rawRoots : List Nat)
    (rowsMatch : RowsMatch graph rows) : List (List (List (Reference (n + graph.nodeCount)))) :=
  List.ofFn (query graph rows rawRoots rowsMatch)

@[simp] theorem queries_length (graph : DAG n) (rows : List Row) (rawRoots : List Nat)
    (rowsMatch : RowsMatch graph rows) :
    (queries graph rows rawRoots rowsMatch).length = graph.roots.length := by simp [queries]

theorem query_stored (graph : DAG n) (rows : List Row) (rawRoots : List Nat)
    (rowsMatch : RowsMatch graph rows) (rootsMatch : RootsMatch graph rawRoots)
    (position : Fin graph.roots.length) :
    ReferencesStored (packetHeap width n rows rawRoots) n (packetHeap width n rows rawRoots).size
      (query graph rows rawRoots rowsMatch position) := by
  apply ReferencesStored.append
  · exact referenceCone_stored graph rows rawRoots rowsMatch _ _ []
      (root_stored graph rows rawRoots rootsMatch position false) (by simp [ReferencesStored])
  · intro clause present reference member
    simp only [List.mem_singleton] at present
    subst clause
    simp only [List.mem_singleton] at member
    subst reference
    exact root_stored graph rows rawRoots rootsMatch position false

theorem queries_stored (graph : DAG n) (rows : List Row) (rawRoots : List Nat)
    (rowsMatch : RowsMatch graph rows) (rootsMatch : RootsMatch graph rawRoots) :
    ∀ original ∈ queries graph rows rawRoots rowsMatch,
      ReferencesStored (packetHeap width n rows rawRoots) n (packetHeap width n rows rawRoots).size original := by
  intro original present
  obtain ⟨position, equality⟩ := List.mem_ofFn.mp present
  subst original
  exact query_stored graph rows rawRoots rowsMatch rootsMatch position

private theorem literal_projection_injective :
    Function.Injective (fun literal : Literal (Fin ambient) => (literal.1.val, literal.2)) := by
  intro first second equality
  exact Prod.ext (Fin.ext (congrArg (fun pair : Nat × Bool => pair.1) equality))
    (congrArg (fun pair : Nat × Bool => pair.2) equality)

private theorem clause_projection_injective :
    Function.Injective (List.map (List.map (fun literal : Literal (Fin ambient) => (literal.1.val, literal.2)))) :=
  List.map_injective_iff.mpr (List.map_injective_iff.mpr literal_projection_injective)

/-- Finite source coordinates project the exact original node clauses. -/
theorem query_original_rows (graph : DAG n) (rows : List Row) (rawRoots : List Nat)
    (rowsMatch : RowsMatch graph rows) (position : Fin graph.roots.length) :
    ForestZeroAssembly.originalRows (query graph rows rawRoots rowsMatch position) =
      (ForestNodeVisits.walkNodes graph (graph.roots.get position)).flatMap
        (fun owner => (graph.nodeClauses owner).map
          (List.map (fun literal => (sourceIndex graph literal.1, literal.2)))) ++
      [[(sourceIndex graph (.inr (graph.roots.get position)), false)]] := by
  apply clause_projection_injective
  have original := referenceCone_exact graph rows rowsMatch (graph.roots.get position)
    (rootReference graph rows rawRoots position false) [] (by rfl)
  rw [typedCone_visits] at original
  simp only [List.map_nil, List.append_nil] at original
  have projected := congrArg (fun clauses => clauses ++ [[(n + (graph.roots.get position).val, false)]]) original
  simp only [query, ForestZeroAssembly.originalRows, List.map_append, List.map_map,
    List.map_flatMap, Function.comp_def, List.map_cons, List.map_nil,
    rootReference, nodeReference, sourceIndex]
  exact projected

/-- An actual compiled query has only the guarded source grammar and a negative
root unit. The empty reserved row preserves this grammar. -/
theorem query_dualHorn (graph : DAG n) (guarded : graph.Guarded) (rows : List Row)
    (rawRoots : List Nat) (rowsMatch : RowsMatch graph rows) (position : Fin graph.roots.length) :
    Controller.Horn.DualHorn (ofClauses (ForestZeroAssembly.originalRows
      (reservedReferences (query graph rows rawRoots rowsMatch position)))) := by
  intro clause present
  simp only [ofClauses, List.mem_toArray, reservedReferences,
    ForestZeroAssembly.originalRows, List.map_append, List.map_cons, List.map_nil,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with original | empty
  · have rowExact := query_original_rows graph rows rawRoots rowsMatch position
    change clause ∈ ForestZeroAssembly.originalRows (query graph rows rawRoots rowsMatch position) at original
    rw [rowExact] at original
    obtain cone | root := List.mem_append.mp original
    · obtain ⟨owner, visited, mappedMember⟩ := List.mem_flatMap.mp cone
      obtain ⟨source, sourceMember, equality⟩ := List.mem_map.mp mappedMember
      subst clause
      exact Controller.Decoder.SparseFormula.clause_relabel_dualHorn (sourceIndex graph) source
        (graph.nodeClauses_dualHorn guarded owner source sourceMember)
    · simp only [List.mem_singleton] at root
      subst clause
      right
      intro left leftMember right rightMember _ _
      exact congrArg Prod.fst ((List.mem_singleton.mp leftMember).trans
        (List.mem_singleton.mp rightMember).symm)
  · subst clause
    right
    intro left impossible
    exact False.elim (List.not_mem_nil impossible)

private theorem sum_plus (items : List α) (charge : α → Nat) (extra : Nat) :
    (items.map fun item => charge item + extra).sum = (items.map charge).sum + extra * items.length := by
  induction items with
  | nil => simp
  | cons item rest ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, ih, Nat.mul_add, Nat.mul_one]
      omega

theorem queries_row_sum (graph : DAG n) (rows : List Row) (rawRoots : List Nat)
    (rowsMatch : RowsMatch graph rows) :
    ((queries graph rows rawRoots rowsMatch).map List.length).sum =
      ((rootReferenceCones graph rows rawRoots rowsMatch).map List.length).sum + graph.roots.length := by
  simp only [queries, rootReferenceCones, List.map_ofFn, query, List.length_append,
    List.length_cons, List.length_nil]
  rw [List.ofFn_eq_map, List.ofFn_eq_map]
  simp only [Function.comp_def, query, List.length_append, List.length_cons, List.length_nil,
    List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil]
  simpa only [List.length_finRange, Nat.one_mul] using sum_plus (List.finRange graph.roots.length)
    (fun position => (referenceCone graph rows rowsMatch (graph.roots.get position)
      (rootReference graph rows rawRoots position false) []).length) 1

theorem queries_literal_sum (graph : DAG n) (rows : List Row) (rawRoots : List Nat)
    (rowsMatch : RowsMatch graph rows) :
    ((queries graph rows rawRoots rowsMatch).map fun clauses => clauses.flatten.length).sum =
      ((rootReferenceCones graph rows rawRoots rowsMatch).map fun clauses => clauses.flatten.length).sum + graph.roots.length := by
  simp only [queries, rootReferenceCones, List.map_ofFn, query, List.flatten_append,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.length_append,
    List.length_cons, List.length_nil]
  rw [List.ofFn_eq_map, List.ofFn_eq_map]
  simp only [Function.comp_def, query, List.length_append, List.length_cons, List.length_nil,
    List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil]
  simpa only [List.length_finRange, Nat.one_mul] using sum_plus (List.finRange graph.roots.length)
    (fun position => (referenceCone graph rows rowsMatch (graph.roots.get position)
      (rootReference graph rows rawRoots position false) []).flatten.length) 1

theorem queries_forest_bounds (graph : DAG n) (rows : List Row) (rawRoots : List Nat)
    (rowsMatch : RowsMatch graph rows) (forest : graph.FormulaForest) :
    ((queries graph rows rawRoots rowsMatch).map List.length).sum ≤ 4 * graph.roots.length + 3 * graph.childIncidences ∧
    ((queries graph rows rawRoots rowsMatch).map fun clauses => clauses.flatten.length).sum ≤
      7 * graph.roots.length + 6 * graph.childIncidences + graph.guardIncidences := by
  have rowBound := rootReferenceCones_row_bound graph rows rawRoots rowsMatch forest
  have literalBound := rootReferenceCones_literal_bound graph rows rawRoots rowsMatch forest
  rw [queries_row_sum, queries_literal_sum]
  omega

/-- Relocating a continuation changes operands and keeps the actual number
of resident instructions. -/
theorem resident_length_next (heap : Array (Word width))
    (layout : ForestZeroDictionary.Layout ambient heap.size) (channels : Nat) (within : channels ≤ ambient)
    (current : List (List (Reference ambient))) (entry firstNext secondNext : Nat) :
    (ForestZeroResident.instructions heap layout current channels within entry firstNext).length =
      (ForestZeroResident.instructions heap layout current channels within entry secondNext).length := by
  simp only [ForestZeroResident.instructions, List.length_flatMap, Array.length_toList, Function.comp_def]
  change ((ForestZeroResident.chunks heap layout current channels within entry firstNext).map Array.size).sum =
    ((ForestZeroResident.chunks heap layout current channels within entry secondNext).map Array.size).sum
  rw [ForestZeroResident.chunk_sizes, ForestZeroResident.chunk_sizes]
  rfl

/-- Static occurrence blocks advance by the actual length of their resident
instruction list. The final empty-stream block is physically included. -/
def residentInstructions (heap : Array (Word width)) (layout : ForestZeroDictionary.Layout ambient heap.size)
    (channels : Nat) (within : channels ≤ ambient) :
    Nat → List (List (List (Reference ambient))) → List (Instruction width 8)
  | entry, [] => (ForestZeroRootLoop.exhaustedCode width).toList
  | entry, current :: rest =>
      let next := entry + (ForestZeroResident.instructions heap layout current channels within entry 0).length
      ForestZeroResident.instructions heap layout current channels within entry next ++
        residentInstructions heap layout channels within next rest

/-- Both array pushes and backing writes consume this exact generated stream. -/
@[irreducible] def residentProgram (priorProgram : Program width 8) (heap : Array (Word width))
    (layout : ForestZeroDictionary.Layout ambient heap.size) (channels : Nat) (within : channels ≤ ambient)
    (originalQueries : List (List (List (Reference ambient)))) : Program width 8 :=
  ForestZeroResident.materialize priorProgram
    (residentInstructions heap layout channels within priorProgram.size originalQueries)

/-- No ambient-sized program block is copied for a root occurrence. -/
theorem residentInstructions_length (heap : Array (Word width))
    (layout : ForestZeroDictionary.Layout ambient heap.size) (channels : Nat) (within : channels ≤ ambient)
    (originalQueries : List (List (List (Reference ambient)))) (entry : Nat) :
    (residentInstructions heap layout channels within entry originalQueries).length ≤
      584 * originalQueries.length + 5 * (originalQueries.map List.length).sum +
        28 * (originalQueries.map fun refs => refs.flatten.length).sum + 2 := by
  induction originalQueries generalizing entry with
  | nil => simp [residentInstructions, ForestZeroRootLoop.exhaustedCode]
  | cons current rest ih =>
      have next := ih (entry + (ForestZeroResident.instructions heap layout current channels within entry 0).length)
      have currentBound := ForestZeroResident.instruction_length heap layout current channels within entry
        (entry + (ForestZeroResident.instructions heap layout current channels within entry 0).length)
      simp only [residentInstructions, List.length_append, List.length_cons,
        List.map_cons, List.sum_cons, Nat.mul_add, Nat.mul_one]
      omega

/-- Source occurrence visits and literals bound resident code before its
four backing-field writes are charged. -/
theorem original_resident_length (graph : DAG n) (rows : List Row) (rawRoots : List Nat)
    (rowsMatch : RowsMatch graph rows) (forest : graph.FormulaForest)
    (heap : Array (Word width)) (layout : ForestZeroDictionary.Layout (n + graph.nodeCount) heap.size)
    (entry : Nat) :
    (residentInstructions heap layout n (by omega) entry (queries graph rows rawRoots rowsMatch)).length ≤
      800 * graph.roots.length + 183 * graph.childIncidences + 28 * graph.guardIncidences + 2 := by
  have codeBound := residentInstructions_length heap layout n (by omega) (queries graph rows rawRoots rowsMatch) entry
  have sourceBound := queries_forest_bounds graph rows rawRoots rowsMatch forest
  rw [queries_length] at codeBound
  omega

/-- Reserving the shared dictionary retains the exact original source words. -/
theorem reserved_queries_stored (graph : DAG n) (rows : List Row) (rawRoots : List Nat)
    (rowsMatch : RowsMatch graph rows) (rootsMatch : RootsMatch graph rawRoots) :
    ∀ original ∈ queries graph rows rawRoots rowsMatch,
      ReferencesStored
        (ForestZeroInitialize.reserveHeap (packetHeap width n rows rawRoots) (n + graph.nodeCount))
        n (packetHeap width n rows rawRoots).size original := by
  intro original present clause rowMember reference member
  exact reserved_stored reference
    (queries_stored graph rows rawRoots rowsMatch rootsMatch original present clause rowMember reference member)

/-- The whole resident stream is appended by the actual array-push recursion. -/
theorem resident_materialize_trace (priorProgram : Program width 8) (heap : Array (Word width))
    (layout : ForestZeroDictionary.Layout ambient heap.size) (channels : Nat) (within : channels ≤ ambient)
    (originalQueries : List (List (List (Reference ambient)))) :
    CompilerArrayTrace.Trace
      (residentInstructions heap layout channels within priorProgram.size originalQueries)
      priorProgram (residentProgram priorProgram heap layout channels within originalQueries)
      (residentInstructions heap layout channels within priorProgram.size originalQueries).length := by
  unfold residentProgram
  exact ForestZeroResident.materialize_trace _ _

/-- A head occurrence is fetched from the actual appended stream; its next
target is the physical end of that occurrence's instructions. -/
theorem resident_head_fetch (priorProgram : Program width 8) (heap : Array (Word width))
    (layout : ForestZeroDictionary.Layout ambient heap.size) (channels : Nat) (within : channels ≤ ambient)
    (current : List (List (Reference ambient))) (rest : List (List (List (Reference ambient))))
    (index : Nat)
    (valid : index < (ForestZeroResident.instructions heap layout current channels within priorProgram.size
      (priorProgram.size + (ForestZeroResident.instructions heap layout current channels within priorProgram.size 0).length)).length) :
    (residentProgram priorProgram heap layout channels within (current :: rest))[priorProgram.size + index]? =
      (ForestZeroResident.instructions heap layout current channels within priorProgram.size
        (priorProgram.size + (ForestZeroResident.instructions heap layout current channels within priorProgram.size 0).length))[index]? := by
  simpa only [residentProgram, residentInstructions, List.nil_append, List.length_nil, Nat.add_zero] using
    ForestZeroResident.materialize_block priorProgram []
      (ForestZeroResident.instructions heap layout current channels within priorProgram.size
        (priorProgram.size + (ForestZeroResident.instructions heap layout current channels within priorProgram.size 0).length))
      (residentInstructions heap layout channels within
        (priorProgram.size + (ForestZeroResident.instructions heap layout current channels within priorProgram.size 0).length) rest)
      index valid

/-- Each encoded field is formed or copied once and physically pushed once.
This charge is separate from execution ticks and arithmetic bit length. -/
theorem resident_backing_trace (heap : Array (Word width))
    (layout : ForestZeroDictionary.Layout ambient heap.size) (channels : Nat) (within : channels ≤ ambient)
    (entry : Nat) (originalQueries : List (List (List (Reference ambient))))
    (initialWords : Array (Word width)) :
    ForestZeroResident.BackingTrace
      (residentInstructions heap layout channels within entry originalQueries)
      initialWords
      (ForestZeroResident.backing (residentInstructions heap layout channels within entry originalQueries) initialWords)
      (4 * (residentInstructions heap layout channels within entry originalQueries).length)
      (4 * (residentInstructions heap layout channels within entry originalQueries).length) :=
  ForestZeroResident.backing_trace _ _

/-- Forest incidence bounds charge the actual instruction pushes and all four
encoded backing fields, including the exhausted-stream block. -/
theorem original_resident_construction_bound (graph : DAG n) (rows : List Row) (rawRoots : List Nat)
    (rowsMatch : RowsMatch graph rows) (forest : graph.FormulaForest)
    (heap : Array (Word width)) (layout : ForestZeroDictionary.Layout (n + graph.nodeCount) heap.size)
    (priorProgram : Program width 8) (initialWords : Array (Word width)) :
    let stream := residentInstructions heap layout n (by omega) priorProgram.size
      (queries graph rows rawRoots rowsMatch)
    (residentProgram priorProgram heap layout n (by omega) (queries graph rows rawRoots rowsMatch)).size
      ≤ priorProgram.size + 800 * graph.roots.length + 183 * graph.childIncidences + 28 * graph.guardIncidences + 2 ∧
    (ForestZeroResident.backing stream initialWords).size
      ≤ initialWords.size + 3200 * graph.roots.length + 732 * graph.childIncidences + 112 * graph.guardIncidences + 8 ∧
    9 * stream.length ≤
      7200 * graph.roots.length + 1647 * graph.childIncidences + 252 * graph.guardIncidences + 18 := by
  dsimp only
  have count := original_resident_length graph rows rawRoots rowsMatch forest heap layout priorProgram.size
  have backingSize := ForestZeroResident.backing_size
    (resident_backing_trace heap layout n (by omega) priorProgram.size
      (queries graph rows rawRoots rowsMatch) initialWords)
  have codeSize := ForestZeroResident.materialize_size priorProgram
    (residentInstructions heap layout n (by omega) priorProgram.size (queries graph rows rawRoots rowsMatch))
  unfold residentProgram
  change (ForestZeroResident.materialize priorProgram _).size ≤ _ ∧ _
  omega

end Controller.Cost.ForestZeroSourcePlan


namespace Controller.Cost.ForestZeroSourcePlan
open Controller.Decoder Controller.Decoder.DAG Controller.CNF
open Controller.Cost.ForestZeroRows Controller.Cost.ForestZeroCone
open Controller.Decoder.ZeroSystem

/-- Reachability ignores repeated visits, while the query list retains their
separate source rows and construction charges. -/
theorem walkNodes_mem_cone (graph : DAG n) (root candidate : Fin graph.nodeCount) :
    candidate ∈ ForestNodeVisits.walkNodes graph root ↔ candidate ∈ graph.cone root := by
  have claim : ∀ rank : Nat, ∀ owner : Fin graph.nodeCount, owner.val = rank →
      ∀ candidate, candidate ∈ ForestNodeVisits.walkNodes graph owner ↔ candidate ∈ graph.cone owner := by
    intro rank
    induction rank using Nat.strong_induction_on with
    | h rank ih =>
        intro owner ownerRank candidate
        rw [ForestNodeVisits.walkNodes.eq_def, graph.cone_eq]
        simp only [List.mem_cons, List.mem_flatMap, Finset.mem_insert,
          Finset.mem_biUnion, List.mem_toFinset]
        apply or_congr Iff.rfl
        constructor
        · rintro ⟨child, present, visited⟩
          exact ⟨child, present, (ih (graph.childIndex owner child).val
            (by have earlier := graph.childIndex_lt owner child; omega) _ rfl candidate).mp visited⟩
        · rintro ⟨child, present, retained⟩
          exact ⟨child, present, (ih (graph.childIndex owner child).val
            (by have earlier := graph.childIndex_lt owner child; omega) _ rfl candidate).mpr retained⟩
  exact claim root.val root rfl candidate

/-- The source coordinate encoding is precisely the finite sum equivalence. -/
theorem sourceIndex_equiv (graph : DAG n) (sourceVar : graph.ZeroVar) :
    sourceIndex graph sourceVar = finSumFinEquiv sourceVar := by
  cases sourceVar with
  | inl channel => rfl
  | inr node => rfl

/-- This assignment is a semantic projection; the physical channel output is
formed by the already checked dictionary/FIFO emitter. -/
def sourceAssignment (graph : DAG n) (channels : Assignment n)
    (activities : Fin graph.nodeCount → Bool) : Fin (n + graph.nodeCount) → Bool :=
  graph.zeroAssignment channels activities ∘ finSumFinEquiv.symm

@[simp] theorem sourceAssignment_index (graph : DAG n) (channels : Assignment n)
    (activities : Fin graph.nodeCount → Bool) (sourceVar : graph.ZeroVar) :
    sourceAssignment graph channels activities (sourceIndex graph sourceVar) =
      graph.zeroAssignment channels activities sourceVar := by
  rw [sourceIndex_equiv]
  simp only [sourceAssignment, Function.comp_def, Equiv.symm_apply_apply]

private theorem holds_source_map (graph : DAG n) (channels : Assignment n)
    (activities : Fin graph.nodeCount → Bool) (clause : Clause graph.ZeroVar) :
    ClauseHolds (sourceAssignment graph channels activities)
      (clause.map fun literal => (sourceIndex graph literal.1, literal.2)) ↔
    ClauseHolds (graph.zeroAssignment channels activities) clause := by
  simp only [ClauseHolds, List.mem_map, LiteralHolds]
  constructor
  · rintro ⟨mapped, ⟨literal, present, equality⟩, truth⟩
    subst mapped
    exact ⟨literal, present, (sourceAssignment_index graph channels activities literal.1) ▸ truth⟩
  · rintro ⟨literal, present, truth⟩
    exact ⟨(sourceIndex graph literal.1, literal.2), ⟨literal, present, rfl⟩,
      (sourceAssignment_index graph channels activities literal.1).symm ▸ truth⟩

/-- Every queried clause belongs to an actual original cone node, followed by
its original root unit. No unrelated node rows are required. -/
theorem query_model_iff (graph : DAG n) (rows : List ForestIndexedOperands.Row) (rawRoots : List Nat)
    (rowsMatch : ForestIndexedOperands.RowsMatch graph rows) (position : Fin graph.roots.length)
    (channels : Assignment n) (activities : Fin graph.nodeCount → Bool) :
    Satisfies (sourceAssignment graph channels activities)
      (ofClauses (ForestZeroAssembly.originalRows (query graph rows rawRoots rowsMatch position))) ↔
    LocalForward graph (graph.cone (graph.roots.get position)) channels activities ∧
      activities (graph.roots.get position) = false := by
  rw [query_original_rows, satisfies_ofClauses]
  constructor
  · intro model
    refine ⟨?_, ?_⟩
    · intro owner retained clause present
      apply (holds_source_map graph channels activities clause).mp
      apply model
      exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨owner,
        (walkNodes_mem_cone graph _ owner).mpr retained, List.mem_map.mpr ⟨clause, present, rfl⟩⟩)
    · have root := model [(sourceIndex graph (.inr (graph.roots.get position)), false)]
        (List.mem_append_right _ (by simp))
      simpa only [ClauseHolds, List.mem_singleton, exists_eq_left, LiteralHolds,
        sourceAssignment_index, zeroAssignment, Sum.elim_inr] using root
  · rintro ⟨forward, zero⟩ clause present
    rcases List.mem_append.mp present with coneMember | rootMember
    · obtain ⟨owner, visited, mapped⟩ := List.mem_flatMap.mp coneMember
      obtain ⟨original, originalMember, equality⟩ := List.mem_map.mp mapped
      subst clause
      exact (holds_source_map graph channels activities original).mpr
        (forward owner ((walkNodes_mem_cone graph _ owner).mp visited) original originalMember)
    · have equality := List.mem_singleton.mp rootMember
      subst clause
      exact ⟨(sourceIndex graph (.inr (graph.roots.get position)), false), by simp,
        by simpa only [LiteralHolds, sourceAssignment_index, zeroAssignment, Sum.elim_inr] using zero⟩

/-- Original source-query models and root evaluation agree exactly, before the
constructor adds the checked nonempty/forced-target constraints. -/
theorem query_zero_iff (graph : DAG n) (guarded : graph.Guarded)
    (rows : List ForestIndexedOperands.Row) (rawRoots : List Nat)
    (rowsMatch : ForestIndexedOperands.RowsMatch graph rows) (position : Fin graph.roots.length)
    (K : Finset (Channel n)) :
    (∃ activities, Satisfies (sourceAssignment graph (assignmentOfSet K) activities)
      (ofClauses (ForestZeroAssembly.originalRows (query graph rows rawRoots rowsMatch position)))) ↔
      graph.eval (assignmentOfSet K) (graph.roots.get position) = false := by
  simp only [query_model_iff]
  exact cone_zero_iff graph guarded K (graph.roots.get position)

end Controller.Cost.ForestZeroSourcePlan


namespace Controller.Cost.ForestZeroSourcePlan
open Controller.Cost Controller.Cost.ForestZeroResident

/-- Every chunk has an exact prefix/single-block/suffix decomposition. -/
theorem chunks_split (blocks : List (Array (Instruction width 8))) (position : Fin blocks.length) :
    blocks.flatMap Array.toList =
      (blocks.take position.val).flatMap Array.toList ++ blocks[position.val].toList ++
        (blocks.drop (position.val + 1)).flatMap Array.toList := by
  have split : blocks = blocks.take position.val ++
      blocks[position.val] :: blocks.drop (position.val + 1) := by
    rw [← List.drop_eq_getElem_cons position.isLt]
    exact (List.take_append_drop position.val blocks).symm
  conv_lhs => rw [split]
  simp only [List.flatMap_append, List.flatMap_cons, List.append_assoc]

/-- Array fetches use the actual sum of preceding physical chunk lengths. -/
theorem materialized_chunk_fetch (priorProgram : Program width 8)
    (blocks : List (Array (Instruction width 8))) (tail : List (Instruction width 8))
    (position : Fin blocks.length) (index : Nat) (valid : index < blocks[position.val].size) :
    (materialize priorProgram (blocks.flatMap Array.toList ++ tail))[
      priorProgram.size + ((blocks.take position.val).map Array.size).sum + index]? =
      blocks[position.val][index]? := by
  have split := chunks_split blocks position
  have fetch := materialize_block priorProgram ((blocks.take position.val).flatMap Array.toList)
    blocks[position.val].toList ((blocks.drop (position.val + 1)).flatMap Array.toList ++ tail)
    index (by simpa only [Array.length_toList] using valid)
  rw [split]
  simp only [List.append_assoc]
  simpa only [List.length_flatMap, Array.length_toList, Function.comp_def,
    Array.getElem?_toList, List.append_assoc] using fetch

/-- Prefix arithmetic identifies the fixed program positions without unfolding
any source-dependent instruction operand. -/
def chunkStart (priorProgram : Program width 8) (blocks : List (Array (Instruction width 8)))
    (position : Fin blocks.length) : Nat :=
  priorProgram.size + ((blocks.take position.val).map Array.size).sum

theorem chunkStart_count (priorProgram : Program width 8)
    (blocks : List (Array (Instruction width 8))) (counts : List Nat)
    (same : blocks.map Array.size = counts) (position : Fin blocks.length) :
    chunkStart priorProgram blocks position = priorProgram.size + (counts.take position.val).sum := by
  unfold chunkStart
  rw [List.map_take, same]

end Controller.Cost.ForestZeroSourcePlan

namespace Controller.Cost.ForestZeroSourcePlan
open Controller.Cost Controller.Cost.ForestZeroResident
open Controller.Cost.ForestZeroDictionary Controller.Cost.ForestZeroEmit

/-- Each fixed backend block is recovered from the generated occurrence's
actual resident instruction array, at its computed prefix offset. -/
theorem resident_head_chunk_fetch (priorProgram : Program width 8) (heap : Array (Word width))
    (layout : Layout ambient heap.size) (channels : Nat) (within : channels ≤ ambient)
    (current : List (List (Reference ambient))) (rest : List (List (List (Reference ambient))))
    (position : Fin (chunks heap layout current channels within priorProgram.size
      (priorProgram.size + (instructions heap layout current channels within priorProgram.size 0).length)).length)
    (index : Nat)
    (valid : index < (chunks heap layout current channels within priorProgram.size
      (priorProgram.size + (instructions heap layout current channels within priorProgram.size 0).length))[position.val].size) :
    (residentProgram priorProgram heap layout channels within (current :: rest))[
      chunkStart priorProgram (chunks heap layout current channels within priorProgram.size
        (priorProgram.size + (instructions heap layout current channels within priorProgram.size 0).length)) position + index]? =
      (chunks heap layout current channels within priorProgram.size
        (priorProgram.size + (instructions heap layout current channels within priorProgram.size 0).length))[position.val][index]? := by
  unfold residentProgram
  simp only [residentInstructions, instructions]
  exact materialized_chunk_fetch priorProgram
    (chunks heap layout current channels within priorProgram.size
      (priorProgram.size + (instructions heap layout current channels within priorProgram.size 0).length))
    (residentInstructions heap layout channels within
      (priorProgram.size + (instructions heap layout current channels within priorProgram.size 0).length) rest)
    position index valid

end Controller.Cost.ForestZeroSourcePlan


namespace Controller.Cost.ForestZeroSourcePlan
open Controller.Decoder Controller.Decoder.DAG Controller.CNF
open Controller.Cost.ForestZeroRows Controller.Cost.ForestZeroCone

/-- Every finite source assignment splits into its actual channel and activity
columns; the correspondence is an equality, not a supplied model oracle. -/
theorem sourceAssignment_split (graph : DAG n) (values : Fin (n + graph.nodeCount) → Bool) :
    sourceAssignment graph
      (fun channel => values (sourceIndex graph (.inl channel)))
      (fun node => values (sourceIndex graph (.inr node))) = values := by
  funext coordinate
  obtain ⟨sourceVar, rfl⟩ := (finSumFinEquiv : graph.ZeroVar ≃ Fin (n + graph.nodeCount)).surjective coordinate
  cases sourceVar with
  | inl channel =>
      rw [← sourceIndex_equiv graph (.inl channel), sourceAssignment_index]
      rfl
  | inr node =>
      rw [← sourceIndex_equiv graph (.inr node), sourceAssignment_index]
      rfl

/-- The model obtained from the constructor is projected through actual
source coordinates before the guarded cone theorem is invoked. -/
theorem query_model_projection (graph : DAG n) (rows : List ForestIndexedOperands.Row)
    (rawRoots : List Nat) (rowsMatch : ForestIndexedOperands.RowsMatch graph rows)
    (position : Fin graph.roots.length) (values : Fin (n + graph.nodeCount) → Bool) :
    Satisfies values (ofClauses (ForestZeroAssembly.originalRows (query graph rows rawRoots rowsMatch position))) ↔
      LocalForward graph (graph.cone (graph.roots.get position))
        (fun channel => values (sourceIndex graph (.inl channel)))
        (fun node => values (sourceIndex graph (.inr node))) ∧
      values (sourceIndex graph (.inr (graph.roots.get position))) = false := by
  have image := query_model_iff graph rows rawRoots rowsMatch position
    (fun channel => values (sourceIndex graph (.inl channel)))
    (fun node => values (sourceIndex graph (.inr node)))
  rw [sourceAssignment_split] at image
  exact image

end Controller.Cost.ForestZeroSourcePlan


namespace Controller.Cost.ForestZeroSourcePlan
open Controller.Cost Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestZeroSource
open Controller.Cost.ForestZeroEmit Controller.Cost.ForestZeroInitialize
open Controller.Cost.ForestZeroAdmissibleCaller

/-- A failed occurrence's frame transports every original source slot,
without reloading the packet or assuming a fresh source heap. -/
theorem stored_reference_ready (heap : Array (Word width)) (sourceEnd tableBase inverseBase entry : Nat)
    (rest : List (Word width)) (state : State width 8)
    (ready : QueryReady (ambient := ambient) (reserveHeap heap ambient) tableBase inverseBase entry rest state)
    (beforeTable : sourceEnd ≤ tableBase) (sourceBound : sourceEnd ≤ heap.size)
    (reference : Reference ambient) (stored : StoredReference heap channels sourceEnd reference) :
    StoredReference state.heap channels sourceEnd reference := by
  refine ⟨?_, stored.slotBound, stored.headerBound, ?_, ?_, stored.coordinateEq⟩
  · rw [ready.heapSize, reserveHeap_size]
    omega
  · exact (ready.sourceFrame.2.2 reference.slot (lt_of_lt_of_le stored.slotBound beforeTable)).trans
      ((reserve_source heap ambient reference.slot (lt_of_lt_of_le stored.slotBound sourceBound)).trans stored.slotWord)
  · exact (ready.sourceFrame.2.2 0 (lt_of_lt_of_le stored.headerBound beforeTable)).trans
      ((reserve_source heap ambient 0 (lt_of_lt_of_le stored.headerBound sourceBound)).trans stored.channelWord)

/-- Declared occurrence source cells are recovered from the live readiness
invariant and the original typed packet correspondence. -/
theorem query_ready_references (graph : DAG n) (rows : List Row) (rawRoots : List Nat)
    (rowsMatch : RowsMatch graph rows) (rootsMatch : RootsMatch graph rawRoots)
    (position : Fin graph.roots.length) (entry : Nat) (rest : List (Word width)) (state : State width 8)
    (ready : QueryReady (ambient := n + graph.nodeCount)
      (reserveHeap (packetHeap width n rows rawRoots) (n + graph.nodeCount))
      (packetHeap width n rows rawRoots).size
      ((packetHeap width n rows rawRoots).size + n + graph.nodeCount) entry rest state) :
    ∀ reference ∈ (query graph rows rawRoots rowsMatch position).flatten,
      StoredReference state.heap n (packetHeap width n rows rawRoots).size reference := by
  intro reference present
  obtain ⟨clause, clauseMember, member⟩ := List.mem_flatten.mp present
  exact stored_reference_ready (packetHeap width n rows rawRoots) _ _ _ entry rest state ready
    le_rfl le_rfl reference
    (query_stored graph rows rawRoots rowsMatch rootsMatch position clause clauseMember reference member)

/-- Channel and node metadata are actual retained packet words, not supplied
registers or a runtime heap-size observation. -/
theorem query_ready_headers (graph : DAG n) (rows : List Row) (rawRoots : List Nat)
    (rowsMatch : RowsMatch graph rows) (entry : Nat) (rest : List (Word width)) (state : State width 8)
    (ready : QueryReady (ambient := n + graph.nodeCount)
      (reserveHeap (packetHeap width n rows rawRoots) (n + graph.nodeCount))
      (packetHeap width n rows rawRoots).size
      ((packetHeap width n rows rawRoots).size + n + graph.nodeCount) entry rest state) :
    state.heap[0]? = some (word width n) ∧
      state.heap[1]? = some (word width graph.nodeCount) := by
  have headerSize : 1 < (packetHeap width n rows rawRoots).size := by rw [packetHeap_size]; omega
  constructor
  · exact (ready.sourceFrame.2.2 0 (by omega)).trans
      ((reserve_source _ _ 0 (by omega)).trans (packet_header width n rows rawRoots))
  · exact (ready.sourceFrame.2.2 1 headerSize).trans
      ((reserve_source _ _ 1 headerSize).trans (by
        simpa only [rowsMatch.length_eq] using (packetHeader width n rows rawRoots).nodeWord))

end Controller.Cost.ForestZeroSourcePlan


namespace Controller.Cost.ForestZeroSourcePlan
open Controller.Cost Controller.Cost.ForestZeroResident
open Controller.Cost.ForestZeroDictionary Controller.Cost.ForestZeroEmit
open Controller.Cost.ForestZeroAdmissibleCaller Controller.Cost.ForestZeroCompile

@[simp] theorem resident_chunks_length (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (current : List (List (Reference ambient))) (channels : Nat) (within : channels ≤ ambient)
    (entry next : Nat) : (chunks heap layout current channels within entry next).length = 32 := rfl

/-- The normalizer address is the actual sum of the preceding stored chunks.
Constructor jump relocation does not change its instruction count. -/
theorem resident_normalizer_start (priorProgram : Program width 8) (heap : Array (Word width))
    (layout : Layout ambient heap.size) (current : List (List (Reference ambient)))
    (channels : Nat) (within : channels ≤ ambient) (next : Nat) :
    chunkStart priorProgram (chunks heap layout current channels within priorProgram.size next)
      ⟨9, by rw [resident_chunks_length]; decide⟩ =
      (placement width heap.size priorProgram.size next current).query + 42 := by
  rw [chunkStart_count priorProgram _ _ (chunk_sizes heap layout current channels within priorProgram.size next)]
  simp only [List.take_succ_cons, List.take_zero, List.sum_cons, List.sum_nil]
  have relocated := constructor_length_relocate width (priorProgram.size + 15) (priorProgram.size + 15)
    heap.size heap.size (heap.size + 4)
    (placement width heap.size priorProgram.size next current).query 0 current
  change priorProgram.size + (3 + (11 + (1 +
    ((constructorCode width (priorProgram.size + 15) heap.size heap.size (heap.size + 4)
      (placement width heap.size priorProgram.size next current).query current).length +
    (11 + (5 + (15 + (5 + (6 + 0))))))))) = _
  rw [relocated]
  simp only [placement]
  omega

/-- All seven normalizer components come from the physically materialized
fixed kernel of this occurrence, not from supplied per-stage fetch premises. -/
theorem resident_head_normalizer (priorProgram : Program width 8) (heap : Array (Word width))
    (layout : Layout ambient heap.size) (current : List (List (Reference ambient)))
    (rest : List (List (List (Reference ambient)))) (channels : Nat) (within : channels ≤ ambient) :
    let next := priorProgram.size + (instructions heap layout current channels within priorProgram.size 0).length
    let entry := (placement width heap.size priorProgram.size next current).query + 42
    Controller.Horn.NormalizeLoop.CodeAt
      (residentProgram priorProgram heap layout channels within (current :: rest)) entry
      (constructorFormula heap layout (empty ambient) (empty_coherent ambient) current channels within).clauses.toList
      (constructorFormulaBackend heap layout (empty ambient) (empty_coherent ambient) current channels within) := by
  dsimp only
  apply Controller.Horn.NormalizeCode.kernel_components
  intro phase
  let next := priorProgram.size + (instructions heap layout current channels within priorProgram.size 0).length
  let position : Fin (chunks heap layout current channels within priorProgram.size next).length :=
    ⟨9, by rw [resident_chunks_length]; decide⟩
  have valid : phase.val < (chunks heap layout current channels within priorProgram.size next)[position.val].size := by
    change phase.val < (Controller.Horn.NormalizeCNF.code width
      ((placement width heap.size priorProgram.size next current).query + 42)
      (constructorDictionary heap layout (empty ambient) current).coordinates.size
      (constructorFormulaBackend heap layout (empty ambient) (empty_coherent ambient) current channels within).base
      (constructorFormulaBackend heap layout (empty ambient) (empty_coherent ambient) current channels within).recordHeader
      (constructorFormulaBackend heap layout (empty ambient) (empty_coherent ambient) current channels within).inputHeader
      (constructorFormulaBackend heap layout (empty ambient) (empty_coherent ambient) current channels within).firstHeader
      (constructorFormulaBackend heap layout (empty ambient) (empty_coherent ambient) current channels within).directoryHeader
      (constructorFormulaBackend heap layout (empty ambient) (empty_coherent ambient) current channels within).endHeader).size
    rw [Controller.Horn.NormalizeCNF.code_size]
    exact phase.isLt
  have actual := resident_head_chunk_fetch priorProgram heap layout channels within current rest position phase.val valid
  rw [resident_normalizer_start] at actual
  exact actual

end Controller.Cost.ForestZeroSourcePlan

namespace Controller.Cost.ForestZeroSourcePlan
open Controller.Cost Controller.Cost.ForestZeroDictionary Controller.Cost.ForestZeroCompile
open Controller.Cost.ForestZeroEmit
open Controller.Cost.ForestZeroAdmissibleCaller

/-- The complete packed-record and incidence region is bounded by the original
query rows and occurrences, including the optional nonemptiness row. -/
theorem query_region_bound (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (references : List (List (Reference ambient))) (channels : Nat) (within : channels ≤ ambient) :
    let dictionary := constructorDictionary heap layout (empty ambient) references
    let clauses := (constructorFormula heap layout (empty ambient) (empty_coherent ambient)
      references channels within).clauses.toList
    let start := (constructorHeap heap layout (empty ambient) references channels).size +
      5 * dictionary.coordinates.size + 4
    start + 3 * clauses.length + (clauses.map List.length).sum +
      2 * (Controller.Horn.IndexScan.occurrences clauses start).length ≤
        heap.size + 14 + 5 * references.length + 15 * references.flatten.length := by
  intro dictionary clauses start
  have allocated := constructorDictionary_size_bound heap layout (empty ambient) references
  have constructed := constructor_heap_local_bound heap layout (empty ambient) (empty_coherent ambient)
    references channels within
  have literalBound := constructorClauses_profile_bound heap layout (empty ambient) (empty_coherent ambient)
    references channels within
  have rowsEq := constructorClauses_length heap layout (empty ambient) (empty_coherent ambient)
    references channels within
  have incidenceBound := source_incidence_bound clauses start
  have rowBound : clauses.length ≤ references.length + 1 := by
    dsimp only [clauses]
    rw [constructorFormula_rows, rowsEq]
    split_ifs <;> omega
  change dictionary.coordinates.size ≤ 0 + references.flatten.length at allocated
  change (constructorHeap heap layout (empty ambient) references channels).size ≤
    heap.size + 7 + 2 * references.length + 2 * references.flatten.length +
      2 * dictionary.coordinates.size at constructed
  change ((constructorClauses heap layout (empty ambient) (empty_coherent ambient)
    references channels within).map List.length).sum ≤
      references.flatten.length + dictionary.coordinates.size at literalBound
  have literals : (clauses.map List.length).sum ≤ references.flatten.length + dictionary.coordinates.size := by
    simpa only [clauses, constructorFormula_rows] using literalBound
  dsimp only [start] at incidenceBound ⊢
  omega

/-- A single source-derived word room inequality supplies the entire dynamic
query-region fit required by SourceQueryPlan; no packed-size oracle is needed. -/
theorem query_region_fits (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (references : List (List (Reference ambient))) (channels : Nat) (within : channels ≤ ambient)
    (room : heap.size + 14 + 5 * references.length + 15 * references.flatten.length < 2 ^ width) :
    let dictionary := constructorDictionary heap layout (empty ambient) references
    let clauses := (constructorFormula heap layout (empty ambient) (empty_coherent ambient)
      references channels within).clauses.toList
    let start := (constructorHeap heap layout (empty ambient) references channels).size +
      5 * dictionary.coordinates.size + 4
    start + 3 * clauses.length + (clauses.map List.length).sum +
      2 * (Controller.Horn.IndexScan.occurrences clauses start).length < 2 ^ width :=
  lt_of_le_of_lt (query_region_bound heap layout references channels within) room

end Controller.Cost.ForestZeroSourcePlan

namespace Controller.Cost.ForestZeroSourcePlan
open Controller.Cost Controller.Cost.ForestZeroResident
open Controller.Cost.ForestZeroDictionary Controller.Cost.ForestZeroAdmissibleCaller
open Controller.Cost.ForestZeroEmit

/-- The reused entry's actual push and constants are fetched from the first
resident chunk of this occurrence. -/
theorem resident_head_reuse (priorProgram : Program width 8) (heap : Array (Word width))
    (layout : Layout ambient heap.size) (current : List (List (Reference ambient)))
    (rest : List (List (List (Reference ambient)))) (channels : Nat) (within : channels ≤ ambient) :
    ∀ phase : Fin 3,
      (residentProgram priorProgram heap layout channels within (current :: rest))[priorProgram.size + phase.val]? =
        (reuseEntryCode width)[phase.val]? := by
  intro phase
  let next := priorProgram.size + (instructions heap layout current channels within priorProgram.size 0).length
  let position : Fin (chunks heap layout current channels within priorProgram.size next).length :=
    ⟨0, by rw [resident_chunks_length]; decide⟩
  have valid : phase.val < (chunks heap layout current channels within priorProgram.size next)[position.val].size := by
    change phase.val < 3
    exact phase.isLt
  have actual := resident_head_chunk_fetch priorProgram heap layout channels within current rest position phase.val valid
  have address : chunkStart priorProgram (chunks heap layout current channels within priorProgram.size next) position =
      priorProgram.size := by simp only [chunkStart, position, List.take_zero, List.map_nil, List.sum_nil, Nat.add_zero]
  rw [address] at actual
  exact actual

/-- The actual singleton cursor instruction uses the source heap's retained
size and original row-occurrence count; no cursor register is supplied. -/
theorem resident_head_cursor (priorProgram : Program width 8) (heap : Array (Word width))
    (layout : Layout ambient heap.size) (current : List (List (Reference ambient)))
    (rest : List (List (List (Reference ambient)))) (channels : Nat) (within : channels ≤ ambient) :
    (residentProgram priorProgram heap layout channels within (current :: rest))[priorProgram.size + 14]? =
      some (.constant 0 (word width (heap.size + 5 + 2 * (current.length + 1)))) := by
  let next := priorProgram.size + (instructions heap layout current channels within priorProgram.size 0).length
  let position : Fin (chunks heap layout current channels within priorProgram.size next).length :=
    ⟨2, by rw [resident_chunks_length]; decide⟩
  have valid : 0 < (chunks heap layout current channels within priorProgram.size next)[position.val].size := by
    change 0 < 1
    decide
  have actual := resident_head_chunk_fetch priorProgram heap layout channels within current rest position 0 valid
  have address : chunkStart priorProgram (chunks heap layout current channels within priorProgram.size next) position =
      priorProgram.size + 14 := by
    rw [chunkStart_count priorProgram _ _ (chunk_sizes heap layout current channels within priorProgram.size next)]
    simp only [position, List.take_succ_cons, List.take_zero, List.sum_cons, List.sum_nil]
    omega
  rw [address] at actual
  change _ = some (Instruction.constant (width := width) (registers := 8) 0
    (word width (heap.size + 5 + 2 * (current.length + 1)))) at actual
  simpa only [Nat.add_zero] using actual

/-- The saved shared-dictionary endpoint is pushed by the widened existing
keep kernel, resident once at this declared occurrence's static position. -/
theorem resident_head_keep (priorProgram : Program width 8) (heap : Array (Word width))
    (layout : Layout ambient heap.size) (current : List (List (Reference ambient)))
    (rest : List (List (List (Reference ambient)))) (channels : Nat) (within : channels ≤ ambient) :
    ForestZeroCallerWiden.WidenedBlockAt
      (residentProgram priorProgram heap layout channels within (current :: rest))
      (priorProgram.size + 3) (keepCode width) := by
  intro offset bound
  let next := priorProgram.size + (instructions heap layout current channels within priorProgram.size 0).length
  let position : Fin (chunks heap layout current channels within priorProgram.size next).length :=
    ⟨1, by rw [resident_chunks_length]; decide⟩
  have valid : offset < (chunks heap layout current channels within priorProgram.size next)[position.val].size := by
    change offset < ((keepCode width).map RegisterWiden.widenInstruction).toArray.size
    simpa only [List.size_toArray, List.length_map] using bound
  have actual := resident_head_chunk_fetch priorProgram heap layout channels within current rest position offset valid
  have address : chunkStart priorProgram (chunks heap layout current channels within priorProgram.size next) position =
      priorProgram.size + 3 := by
    rw [chunkStart_count priorProgram _ _ (chunk_sizes heap layout current channels within priorProgram.size next)]
    simp only [position, List.take_succ_cons, List.take_zero, List.sum_cons, List.sum_nil]
    omega
  rw [address] at actual
  change _ = ((keepCode width).map RegisterWiden.widenInstruction).toArray[offset]? at actual
  simpa only [List.getElem?_toArray, List.getElem?_map] using actual

/-- The complete occurrence-dependent constructor block is actually widened
and resident; its return address is its computed following kernel position. -/
theorem resident_head_constructor (priorProgram : Program width 8) (heap : Array (Word width))
    (layout : Layout ambient heap.size) (current : List (List (Reference ambient)))
    (rest : List (List (List (Reference ambient)))) (channels : Nat) (within : channels ≤ ambient) :
    let next := priorProgram.size + (instructions heap layout current channels within priorProgram.size 0).length
    let p := placement width heap.size priorProgram.size next current
    ForestZeroCallerWiden.WidenedBlockAt
      (residentProgram priorProgram heap layout channels within (current :: rest)) p.constructor
      (constructorCode width p.constructor heap.size heap.size (heap.size + 4) p.query current) := by
  dsimp only
  intro offset bound
  let next := priorProgram.size + (instructions heap layout current channels within priorProgram.size 0).length
  let p := placement width heap.size priorProgram.size next current
  let position : Fin (chunks heap layout current channels within priorProgram.size next).length :=
    ⟨3, by rw [resident_chunks_length]; decide⟩
  have valid : offset < (chunks heap layout current channels within priorProgram.size next)[position.val].size := by
    change offset < ((constructorCode width p.constructor heap.size heap.size (heap.size + 4) p.query current).map
      RegisterWiden.widenInstruction).toArray.size
    simpa only [List.size_toArray, List.length_map] using bound
  have actual := resident_head_chunk_fetch priorProgram heap layout channels within current rest position offset valid
  have address : chunkStart priorProgram (chunks heap layout current channels within priorProgram.size next) position =
      p.constructor := by
    rw [chunkStart_count priorProgram _ _ (chunk_sizes heap layout current channels within priorProgram.size next)]
    simp only [position, List.take_succ_cons, List.take_zero, List.sum_cons, List.sum_nil]
    change priorProgram.size + (3 + (11 + (1 + 0))) = priorProgram.size + 15
    omega
  rw [address] at actual
  change _ = ((constructorCode width p.constructor heap.size heap.size (heap.size + 4) p.query current).map
    RegisterWiden.widenInstruction).toArray[offset]? at actual
  simpa only [List.getElem?_toArray, List.getElem?_map] using actual

end Controller.Cost.ForestZeroSourcePlan

namespace Controller.Cost.ForestZeroSourcePlan
open Controller.Cost Controller.Cost.ForestZeroResident
open Controller.Cost.ForestZeroDictionary Controller.Cost.ForestZeroAdmissibleCaller
open Controller.Cost.ForestZeroEmit

/-- All blocks following the variable constructor have fixed resident sizes. -/
def residentTailCounts : List Nat :=
  [11, 5, 15, 5, 6, 161, 7, 32, 3, 6, 10, 47, 4, 14, 5, 12, 26,
   13, 13, 2, 19, 14, 3, 4, 15, 12, 1, 2]

/-- The common dynamic constructor extent is charged once in the actual
address of each fixed tail block. Later offsets are sums of resident sizes. -/
theorem resident_tail_start (priorProgram : Program width 8) (heap : Array (Word width))
    (layout : Layout ambient heap.size) (current : List (List (Reference ambient)))
    (channels : Nat) (within : channels ≤ ambient) (next : Nat)
    (position : Fin (chunks heap layout current channels within priorProgram.size next).length)
    (afterConstructor : 4 ≤ position.val) :
    chunkStart priorProgram (chunks heap layout current channels within priorProgram.size next) position =
      (placement width heap.size priorProgram.size next current).query +
        (residentTailCounts.take (position.val - 4)).sum := by
  rw [chunkStart_count priorProgram _ _ (chunk_sizes heap layout current channels within priorProgram.size next)]
  let k := position.val - 4
  have indexEq : position.val = k + 4 := by dsimp only [k]; omega
  rw [indexEq]
  simp only [Nat.add_sub_cancel]
  have relocated := constructor_length_relocate width (priorProgram.size + 15) (priorProgram.size + 15)
    heap.size heap.size (heap.size + 4)
    (placement width heap.size priorProgram.size next current).query 0 current
  change priorProgram.size + (3 + (11 + (1 +
    ((constructorCode width (priorProgram.size + 15) heap.size heap.size (heap.size + 4)
      (placement width heap.size priorProgram.size next current).query current).length +
    (residentTailCounts.take k).sum)))) = _
  rw [relocated]
  change priorProgram.size + (3 + (11 + (1 +
    ((constructorCode width (priorProgram.size + 15) heap.size heap.size (heap.size + 4) 0 current).length +
    (residentTailCounts.take k).sum)))) =
      priorProgram.size + 15 +
        (constructorCode width (priorProgram.size + 15) heap.size heap.size (heap.size + 4) 0 current).length +
        (residentTailCounts.take k).sum
  omega

/-- Every fixed tail instruction is fetched from its generated occurrence
block at its actual computed address. This supplies all backend fetch fields
without assuming a per-stage program or a runtime layout oracle. -/
theorem resident_tail_fetch (priorProgram : Program width 8) (heap : Array (Word width))
    (layout : Layout ambient heap.size) (channels : Nat) (within : channels ≤ ambient)
    (current : List (List (Reference ambient))) (rest : List (List (List (Reference ambient))))
    (position : Fin (chunks heap layout current channels within priorProgram.size
      (priorProgram.size + (instructions heap layout current channels within priorProgram.size 0).length)).length)
    (afterConstructor : 4 ≤ position.val) (index : Nat)
    (valid : index < (chunks heap layout current channels within priorProgram.size
      (priorProgram.size + (instructions heap layout current channels within priorProgram.size 0).length))[position.val].size) :
    let next := priorProgram.size + (instructions heap layout current channels within priorProgram.size 0).length
    (residentProgram priorProgram heap layout channels within (current :: rest))[
      (placement width heap.size priorProgram.size next current).query +
        (residentTailCounts.take (position.val - 4)).sum + index]? =
      (chunks heap layout current channels within priorProgram.size next)[position.val][index]? := by
  dsimp only
  have actual := resident_head_chunk_fetch priorProgram heap layout channels within current rest position index valid
  rw [resident_tail_start priorProgram heap layout current channels within _ position afterConstructor] at actual
  exact actual

end Controller.Cost.ForestZeroSourcePlan

namespace Controller.Cost.ForestZeroSourcePlan
open Controller.Decoder Controller.Decoder.DAG Controller.CNF
open Controller.Cost Controller.Cost.ForestIndexedOperands Controller.Cost.ForestZeroSource
open Controller.Cost.ForestZeroEmit Controller.Cost.ForestZeroUnits Controller.Cost.ForestZeroRows
open Controller.Cost.ForestZeroCone Controller.Cost.ForestZeroReferenceCone
variable {width : Nat}

/-- A declared occurrence carries its negative activity unit and the positive
fault-target unit fetched from the once-loaded immutable target trailer. -/
def forcedQuery (width : Nat) (graph : DAG n) (rows : List Row) (rawRoots : List Nat)
    (rowsMatch : RowsMatch graph rows) (position : Fin graph.roots.length) (target : Fin n) :
    List (List (Reference (n + graph.nodeCount))) :=
  query graph rows rawRoots rowsMatch position ++
    [[targetReference (nodes := graph.nodeCount) (packetHeap width n rows rawRoots).size target]]

/-- Extending the real packet by its target word preserves every original
source cell and supplies the forced-target reference's actual load. -/
theorem forced_query_stored (graph : DAG n) (rows : List Row) (rawRoots : List Nat)
    (rowsMatch : RowsMatch graph rows) (rootsMatch : RootsMatch graph rawRoots)
    (position : Fin graph.roots.length) (target : Fin n) :
    ReferencesStored ((packetHeap width n rows rawRoots).push (word width target.val)) n
      ((packetHeap width n rows rawRoots).size + 1)
      (forcedQuery (width := width) graph rows rawRoots rowsMatch position target) := by
  apply ReferencesStored.append
  · intro clause present reference member
    exact trailer_preserves_reference _ n reference
      (query_stored graph rows rawRoots rowsMatch rootsMatch position clause present reference member) _
  · intro clause present reference member
    simp only [List.mem_singleton] at present
    subst clause
    simp only [List.mem_singleton] at member
    subst reference
    exact target_stored (nodes := graph.nodeCount) _ (packet_header width n rows rawRoots)
      (by rw [packetHeap_size]; omega) target

/-- The new original source row contains precisely the forced channel literal. -/
theorem forced_query_original_rows (graph : DAG n) (rows : List Row) (rawRoots : List Nat)
    (rowsMatch : RowsMatch graph rows) (position : Fin graph.roots.length) (target : Fin n) :
    ForestZeroAssembly.originalRows (forcedQuery (width := width) graph rows rawRoots rowsMatch position target) =
      ForestZeroAssembly.originalRows (query graph rows rawRoots rowsMatch position) ++
        [[(sourceIndex graph (.inl target), true)]] := by
  have coordinate : (targetReference (nodes := graph.nodeCount)
      (packetHeap width n rows rawRoots).size target).coordinate = sourceIndex graph (.inl target) := by
    apply Fin.ext
    rfl
  simp only [forcedQuery, ForestZeroAssembly.originalRows, List.map_append,
    List.map_cons, List.map_nil, coordinate]
  rfl

/-- The forced-unit model is an original cone model with the actual target on. -/
theorem forced_query_model_iff (graph : DAG n) (rows : List Row) (rawRoots : List Nat)
    (rowsMatch : RowsMatch graph rows) (position : Fin graph.roots.length) (target : Fin n)
    (channels : Assignment n) (activities : Fin graph.nodeCount → Bool) :
    Satisfies (sourceAssignment graph channels activities)
      (ofClauses (ForestZeroAssembly.originalRows
        (forcedQuery (width := width) graph rows rawRoots rowsMatch position target))) ↔
    LocalForward graph (graph.cone (graph.roots.get position)) channels activities ∧
      activities (graph.roots.get position) = false ∧ channels target = true := by
  rw [forced_query_original_rows, satisfies_ofClauses]
  constructor
  · intro model
    have original : Satisfies (sourceAssignment graph channels activities)
        (ofClauses (ForestZeroAssembly.originalRows (query graph rows rawRoots rowsMatch position))) := by
      rw [satisfies_ofClauses]
      exact fun clause present => model clause (List.mem_append_left _ present)
    have image := (query_model_iff graph rows rawRoots rowsMatch position channels activities).mp original
    have forced := model [(sourceIndex graph (.inl target), true)]
      (List.mem_append_right _ (List.mem_singleton_self _))
    refine ⟨image.1, image.2, ?_⟩
    simpa only [ClauseHolds, List.mem_singleton, exists_eq_left, LiteralHolds,
      sourceAssignment_index, zeroAssignment, Sum.elim_inl] using forced
  · rintro ⟨forward, zero, forced⟩ clause present
    rcases List.mem_append.mp present with original | unit
    · have model := (query_model_iff graph rows rawRoots rowsMatch position channels activities).mpr ⟨forward, zero⟩
      exact ((satisfies_ofClauses _ _).mp model) clause original
    · have same := List.mem_singleton.mp unit
      subst clause
      refine ⟨(sourceIndex graph (.inl target), true), List.mem_singleton_self _, ?_⟩
      simpa only [LiteralHolds, sourceAssignment_index, zeroAssignment, Sum.elim_inl] using forced

/-- Healthy-one feasibility uses an existing zero witness containing the
forced target; it does not manufacture a zero witness from an unseen slot. -/
theorem forced_query_zero_iff (graph : DAG n) (guarded : graph.Guarded)
    (rows : List Row) (rawRoots : List Nat) (rowsMatch : RowsMatch graph rows)
    (position : Fin graph.roots.length) (target : Fin n) (K : Finset (Channel n)) :
    (∃ activities, Satisfies (sourceAssignment graph (assignmentOfSet K) activities)
      (ofClauses (ForestZeroAssembly.originalRows
        (forcedQuery (width := width) graph rows rawRoots rowsMatch position target)))) ↔
      graph.eval (assignmentOfSet K) (graph.roots.get position) = false ∧ target ∈ K := by
  constructor
  · rintro ⟨activities, model⟩
    have actual := (forced_query_model_iff graph rows rawRoots rowsMatch position target _ activities).mp model
    have zero := (query_model_iff graph rows rawRoots rowsMatch position _ activities).mpr ⟨actual.1, actual.2.1⟩
    exact ⟨(query_zero_iff graph guarded rows rawRoots rowsMatch position K).mp ⟨activities, zero⟩,
      (assignmentOfSet_eq_true K target).mp actual.2.2⟩
  · rintro ⟨zero, targetPresent⟩
    obtain ⟨activities, model⟩ := (query_zero_iff graph guarded rows rawRoots rowsMatch position K).mpr zero
    have actual := (query_model_iff graph rows rawRoots rowsMatch position _ activities).mp model
    exact ⟨activities, (forced_query_model_iff graph rows rawRoots rowsMatch position target _ activities).mpr
      ⟨actual.1, actual.2, (assignmentOfSet_eq_true K target).mpr targetPresent⟩⟩

end Controller.Cost.ForestZeroSourcePlan

namespace Controller.Cost.ForestZeroSourcePlan
open Controller.Decoder Controller.Decoder.DAG Controller.Cost Controller.Cost.ForestIndexedOperands
open Controller.Cost.ForestZeroSource Controller.Cost.ForestZeroEmit Controller.Cost.ForestZeroUnits
open Controller.Cost.ForestZeroDictionary
variable {width : Nat}

/-- Each declared occurrence retains its own forced-target row, even when
several declared occurrences identify the same root. -/
def forcedQueries (width : Nat) (graph : DAG n) (rows : List Row) (rawRoots : List Nat)
    (rowsMatch : RowsMatch graph rows) (target : Fin n) : List (List (List (Reference (n + graph.nodeCount)))) :=
  (queries graph rows rawRoots rowsMatch).map (fun current => current ++
    [[targetReference (nodes := graph.nodeCount) (packetHeap width n rows rawRoots).size target]])

@[simp] theorem forced_queries_length (graph : DAG n) (rows : List Row) (rawRoots : List Nat)
    (rowsMatch : RowsMatch graph rows) (target : Fin n) :
    (forcedQueries (width := width) graph rows rawRoots rowsMatch target).length = graph.roots.length := by
  simp only [forcedQueries, List.length_map, queries_length]

/-- A single actual unit adds one row and one literal occurrence per position. -/
private theorem appended_unit_profile (items : List (List (List (Reference ambient))))
    (unit : Reference ambient) :
    ((items.map (fun current => current ++ [[unit]])).map List.length).sum =
        (items.map List.length).sum + items.length ∧
    ((items.map (fun current => current ++ [[unit]])).map fun current => current.flatten.length).sum =
        (items.map fun current => current.flatten.length).sum + items.length := by
  induction items with
  | nil => simp only [List.map_nil, List.sum_nil, List.length_nil, Nat.add_zero, and_self]
  | cons current rest ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, List.length_nil,
      List.length_append, List.flatten_append, List.flatten_cons, List.flatten_nil,
      List.nil_append, List.append_nil] at ⊢
    exact ⟨by omega, by omega⟩

/-- Forest charging includes the root-negative and target-positive unit for
every declared occurrence; ordered duplicates remain charged occurrences. -/
theorem forced_queries_forest_bounds (graph : DAG n) (rows : List Row) (rawRoots : List Nat)
    (rowsMatch : RowsMatch graph rows) (target : Fin n) (forest : graph.FormulaForest) :
    ((forcedQueries (width := width) graph rows rawRoots rowsMatch target).map List.length).sum ≤
        5 * graph.roots.length + 3 * graph.childIncidences ∧
    ((forcedQueries (width := width) graph rows rawRoots rowsMatch target).map fun current => current.flatten.length).sum ≤
        8 * graph.roots.length + 6 * graph.childIncidences + graph.guardIncidences := by
  have original := queries_forest_bounds graph rows rawRoots rowsMatch forest
  have profile := appended_unit_profile (queries graph rows rawRoots rowsMatch)
    (targetReference (nodes := graph.nodeCount) (packetHeap width n rows rawRoots).size target)
  rw [queries_length] at profile
  change _ ≤ _ ∧ _ ≤ _
  dsimp only [forcedQueries]
  exact ⟨by omega, by omega⟩

/-- These are the actual resident instructions for the forced source queries,
including one physical final exhausted block and all repeated positions. -/
theorem forced_resident_length (graph : DAG n) (rows : List Row) (rawRoots : List Nat)
    (rowsMatch : RowsMatch graph rows) (target : Fin n) (forest : graph.FormulaForest)
    (heap : Array (Word width)) (layout : Layout (n + graph.nodeCount) heap.size) (entry : Nat) :
    (residentInstructions heap layout n (by omega) entry
      (forcedQueries (width := width) graph rows rawRoots rowsMatch target)).length ≤
        833 * graph.roots.length + 183 * graph.childIncidences + 28 * graph.guardIncidences + 2 := by
  have bounded := residentInstructions_length heap layout n (by omega)
    (forcedQueries (width := width) graph rows rawRoots rowsMatch target) entry
  have inputBound := forced_queries_forest_bounds (width := width) graph rows rawRoots rowsMatch target forest
  rw [forced_queries_length] at bounded
  omega

end Controller.Cost.ForestZeroSourcePlan

namespace Controller.Cost.ForestZeroSourcePlan
open Controller.Cost Controller.Cost.ForestZeroResident Controller.Cost.ForestZeroDictionary
open Controller.Cost.ForestZeroEmit Controller.Cost.ForestZeroAdmissibleCaller

/-- The actual stream ends with two resident exhausted instructions. -/
theorem resident_stream_min_length (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (channels : Nat) (within : channels ≤ ambient)
    (items : List (List (List (Reference ambient)))) (entry : Nat) :
    2 ≤ (residentInstructions heap layout channels within entry items).length := by
  induction items generalizing entry with
  | nil => exact Nat.le_refl 2
  | cons current rest ih =>
    simp only [residentInstructions, List.length_append]
    exact le_trans (ih _) (Nat.le_add_left _ _)

/-- The continuation is strictly inside the actual materialized resident
program because the remaining stream contains its exhausted block. -/
theorem resident_head_next_bound (priorProgram : Program width 8) (heap : Array (Word width))
    (layout : Layout ambient heap.size) (channels : Nat) (within : channels ≤ ambient)
    (current : List (List (Reference ambient))) (rest : List (List (List (Reference ambient)))) :
    priorProgram.size + (instructions heap layout current channels within priorProgram.size 0).length <
      (residentProgram priorProgram heap layout channels within (current :: rest)).size := by
  let next := priorProgram.size + (instructions heap layout current channels within priorProgram.size 0).length
  have tailBound := resident_stream_min_length heap layout channels within rest next
  have relocated := resident_length_next heap layout channels within current priorProgram.size next 0
  simp only [residentProgram, materialize_size, residentInstructions, List.length_append]
  rw [relocated]
  rw [← Nat.add_assoc]
  change next < next + (residentInstructions heap layout channels within next rest).length
  omega

/-- Actual resident length includes the fixed tail through physical dispatch. -/
theorem resident_head_end (priorProgram : Program width 8) (heap : Array (Word width))
    (layout : Layout ambient heap.size) (current : List (List (Reference ambient)))
    (channels : Nat) (within : channels ≤ ambient) (next : Nat) :
    (placement width heap.size priorProgram.size next current).query + 467 =
      priorProgram.size + (instructions heap layout current channels within priorProgram.size next).length := by
  have sizes := chunk_sizes heap layout current channels within priorProgram.size next
  have relocated := constructor_length_relocate width (priorProgram.size + 15) (priorProgram.size + 15)
    heap.size heap.size (heap.size + 4)
    (placement width heap.size priorProgram.size next current).query 0 current
  simp only [instructions, List.length_flatMap, Array.length_toList, Function.comp_def]
  change _ = priorProgram.size + ((chunks heap layout current channels within priorProgram.size next).map Array.size).sum
  rw [sizes]
  simp only [List.sum_cons, List.sum_nil]
  rw [relocated]
  simp only [placement]
  omega

/-- One actual resident program-size fit discharges every head kernel PC fit,
including constructor, normalizer, reset, and the duplicate-sensitive dispatch. -/
theorem resident_head_pc_room (priorProgram : Program width 8) (heap : Array (Word width))
    (layout : Layout ambient heap.size) (current : List (List (Reference ambient)))
    (rest : List (List (List (Reference ambient)))) (channels : Nat) (within : channels ≤ ambient)
    (programRoom : (residentProgram priorProgram heap layout channels within (current :: rest)).size < 2 ^ width) :
    let next := priorProgram.size + (instructions heap layout current channels within priorProgram.size 0).length
    (placement width heap.size priorProgram.size next current).query + 467 < 2 ^ width := by
  dsimp only
  rw [resident_head_end priorProgram heap layout current channels within
    (priorProgram.size + (instructions heap layout current channels within priorProgram.size 0).length)]
  have relocated := resident_length_next heap layout channels within current priorProgram.size
    (priorProgram.size + (instructions heap layout current channels within priorProgram.size 0).length) 0
  rw [relocated]
  exact lt_trans (resident_head_next_bound priorProgram heap layout channels within current rest) programRoom

end Controller.Cost.ForestZeroSourcePlan

namespace Controller.Cost.ForestZeroSourcePlan
open Controller.Cost Controller.Cost.ForestZeroDictionary Controller.Cost.ForestZeroCompile
open Controller.Cost.ForestZeroEmit Controller.Cost.ForestZeroAdmissibleCaller

/-- Natural width selection from the actual source, shared dictionary, and
query occurrence counts covers every non-PC SourceQueryPlan word fit. -/
theorem query_all_word_rooms (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (references : List (List (Reference ambient))) (channels : Nat) (within : channels ≤ ambient)
    (room : heap.size + 2 * ambient + 14 + 5 * references.length + 15 * references.flatten.length < 2 ^ width) :
    ambient + 1 < 2 ^ width ∧ channels + 1 < 2 ^ width ∧
    heap.size + 5 + 2 * (references.length + 1) + 2 * references.flatten.length + 2 * ambient < 2 ^ width ∧
    (constructorDictionary heap layout (empty ambient) references).coordinates.size + 1 < 2 ^ width ∧
    (constructorHeap heap layout (empty ambient) references channels).size + 1 < 2 ^ width ∧
    (constructorHeap heap layout (empty ambient) references channels).size +
      5 * (constructorDictionary heap layout (empty ambient) references).coordinates.size + 4 +
      3 * (constructorFormula heap layout (empty ambient) (empty_coherent ambient) references channels within).clauses.toList.length +
      ((constructorFormula heap layout (empty ambient) (empty_coherent ambient) references channels within).clauses.toList.map List.length).sum +
      2 * (Controller.Horn.IndexScan.occurrences
        (constructorFormula heap layout (empty ambient) (empty_coherent ambient) references channels within).clauses.toList
        ((constructorHeap heap layout (empty ambient) references channels).size +
          5 * (constructorDictionary heap layout (empty ambient) references).coordinates.size + 4)).length < 2 ^ width := by
  have localBound := constructorDictionary_size_bound heap layout (empty ambient) references
  change (constructorDictionary heap layout (empty ambient) references).coordinates.size ≤
    0 + references.flatten.length at localBound
  have heapBound := constructor_heap_local_bound heap layout (empty ambient) (empty_coherent ambient)
    references channels within
  have region := query_region_fits heap layout references channels within
    (show heap.size + 14 + 5 * references.length + 15 * references.flatten.length < 2 ^ width by omega)
  exact ⟨by omega, by omega, by omega, by omega, by omega, region⟩

end Controller.Cost.ForestZeroSourcePlan

namespace Controller.Cost.ForestZeroSourcePlan
open Controller.Cost Controller.Cost.ForestZeroDictionary Controller.Cost.ForestZeroCompile
open Controller.Cost.ForestZeroEmit Controller.Cost.ForestZeroAdmissibleCaller

/-- The source constructor allocates an exact number of words determined by
row occurrences and its actual nonemptiness search, independently of cells
outside the retained input and dictionary regions. -/
theorem constructor_heap_size_exact (heap : Array (Word width))
    (layout : Layout ambient heap.size) (dictionary : Dictionary ambient)
    (references : List (List (Reference ambient))) (channels : Nat) :
    (constructorHeap heap layout dictionary references channels).size =
      heap.size + 5 + 2 * (references.length + 1) + 2 * references.flatten.length +
      (if (ForestZeroNonempty.search
        (constructorDictionary heap layout dictionary references)
        ((constructorDictionary heap layout dictionary references).coordinates.size + 1)
        channels 0).reason = .covered then 2 * channels else 0) := by
  unfold constructorHeap
  dsimp only
  split_ifs <;>
    simp only [ForestZeroAdmissible.activeHeap_size, ForestZeroAdmissible.boundaryHeap_size, ForestZeroPositive.pairHeap_size,
      ForestZeroQueryCaller.queryHeap_size, reservedReferences_length,
      reservedReferences_flatten, ForestZeroPositive.channelLabels_length] <;> omega

/-- A failed-query heap retains the exact resident constructor base. This
uses the executable constructor's allocation equation rather than equating
whole heaps whose inverse words may still contain previous local IDs. -/
theorem constructor_heap_size_rebase (first second : Array (Word width))
    (firstLayout : Layout ambient first.size) (secondLayout : Layout ambient second.size)
    (dictionary : Dictionary ambient) (references : List (List (Reference ambient)))
    (channels : Nat) (sameSize : first.size = second.size) :
    (constructorHeap first firstLayout dictionary references channels).size =
      (constructorHeap second secondLayout dictionary references channels).size := by
  rw [constructor_heap_size_exact, constructor_heap_size_exact, sameSize]

/-- The local-ID compiler itself is independent of input heap contents. Its
result is tied to the same ordered original references, including duplicates. -/
theorem constructor_dictionary_rebase (first second : Array (Word width))
    (firstLayout : Layout ambient first.size) (secondLayout : Layout ambient second.size)
    (dictionary : Dictionary ambient) (references : List (List (Reference ambient))) :
    constructorDictionary first firstLayout dictionary references =
      constructorDictionary second secondLayout dictionary references := rfl

/-- The normalizer receives the same actual finite formula after failed-query
reuse; this transports its typed row indices without an external CNF oracle. -/
theorem constructor_formula_rebase (first second : Array (Word width))
    (firstLayout : Layout ambient first.size) (secondLayout : Layout ambient second.size)
    (dictionary : Dictionary ambient) (coherent : Coherent dictionary)
    (references : List (List (Reference ambient))) (channels : Nat) (within : channels ≤ ambient) :
    constructorFormula first firstLayout dictionary coherent references channels within =
      constructorFormula second secondLayout dictionary coherent references channels within := rfl

/-- A failed query does not invalidate the actual resident instruction
operands. Constructor metadata and every fixed kernel field depend on the
retained heap extent and original ordered references, not stale inverse cells. -/
theorem resident_chunks_rebase (first second : Array (Word width))
    (firstLayout : Layout ambient first.size) (secondLayout : Layout ambient second.size)
    (references : List (List (Reference ambient))) (channels : Nat) (within : channels ≤ ambient)
    (entry next : Nat) (sameSize : first.size = second.size) :
    ForestZeroResident.chunks first firstLayout references channels within entry next =
      ForestZeroResident.chunks second secondLayout references channels within entry next := by
  have heapSize := constructor_heap_size_rebase first second firstLayout secondLayout
    (empty ambient) references channels sameSize
  simp only [ForestZeroResident.chunks, constructorDictionary, constructorFormulaBackend,
    backendLayout, sameSize, heapSize]

/-- Reusing the actual resident array across failed occurrences retains every
original stored kernel instruction, without regenerating or recopying it. -/
theorem resident_instructions_rebase (first second : Array (Word width))
    (firstLayout : Layout ambient first.size) (secondLayout : Layout ambient second.size)
    (references : List (List (Reference ambient))) (channels : Nat) (within : channels ≤ ambient)
    (entry next : Nat) (sameSize : first.size = second.size) :
    ForestZeroResident.instructions first firstLayout references channels within entry next =
      ForestZeroResident.instructions second secondLayout references channels within entry next := by
  unfold ForestZeroResident.instructions
  rw [resident_chunks_rebase first second firstLayout secondLayout references channels within entry next sameSize]

/-- Static occurrence positions remain identical when the shared heap is
reused. Each induction step uses the actual resident instruction-length
identity before continuing to the next occurrence's physical address. -/
theorem resident_stream_rebase (first second : Array (Word width))
    (firstLayout : Layout ambient first.size) (secondLayout : Layout ambient second.size)
    (queries : List (List (List (Reference ambient)))) (channels : Nat) (within : channels ≤ ambient)
    (entry : Nat) (sameSize : first.size = second.size) :
    residentInstructions first firstLayout channels within entry queries =
      residentInstructions second secondLayout channels within entry queries := by
  induction queries generalizing entry with
  | nil => rfl
  | cons current later ih =>
    have lengths := congrArg List.length
      (resident_instructions_rebase first second firstLayout secondLayout current channels within entry 0 sameSize)
    simp only [residentInstructions]
    rw [lengths, resident_instructions_rebase first second firstLayout secondLayout current channels within
      entry (entry + (ForestZeroResident.instructions second secondLayout current channels within entry 0).length) sameSize]
    rw [ih]

/-- The same resident array executes all failed-query repetitions. This is an
array equality from concrete instruction formation, not an assumption that
kernel code is regenerated at no cost for each restored source heap. -/
theorem resident_program_rebase (priorProgram : Program width 8) (first second : Array (Word width))
    (firstLayout : Layout ambient first.size) (secondLayout : Layout ambient second.size)
    (queries : List (List (List (Reference ambient)))) (channels : Nat) (within : channels ≤ ambient)
    (sameSize : first.size = second.size) :
    residentProgram priorProgram first firstLayout channels within queries =
      residentProgram priorProgram second secondLayout channels within queries := by
  unfold residentProgram
  rw [resident_stream_rebase first second firstLayout secondLayout queries channels within priorProgram.size sameSize]

end Controller.Cost.ForestZeroSourcePlan

namespace Controller.Cost.ForestZeroSourcePlan
open Controller.CNF
open Controller.Cost Controller.Cost.ForestZeroResident Controller.Cost.ForestZeroDictionary
open Controller.Cost.ForestZeroCompile Controller.Cost.ForestZeroEmit Controller.Cost.ForestZeroAdmissibleCaller

/-- The countAt field is fetched from the actual materialized occurrence block. -/
theorem resident_head_countAt (priorProgram : Program width 8) (heap : Array (Word width))
    (layout : Layout ambient heap.size) (current : List (List (Reference ambient)))
    (later : List (List (List (Reference ambient)))) (channels : Nat) (within : channels ≤ ambient) :
    let next := priorProgram.size + (instructions heap layout current channels within priorProgram.size 0).length
    let p := placement width heap.size priorProgram.size next current
    let resident := residentProgram priorProgram heap layout channels within (current :: later)
    ∀ phase : Fin 11, resident[p.query + phase.val]? = (scratchCountCode width)[phase.val]? := by
  dsimp only
  intro phase
  let next := priorProgram.size + (instructions heap layout current channels within priorProgram.size 0).length
  let position : Fin (chunks heap layout current channels within priorProgram.size next).length :=
    ⟨4, by rw [resident_chunks_length]; decide⟩
  have sizes := congrArg (fun counts : List Nat => counts[position.val]?)
    (chunk_sizes heap layout current channels within priorProgram.size next)
  rw [List.getElem?_map, List.getElem?_eq_getElem position.isLt] at sizes
  change some ((chunks heap layout current channels within priorProgram.size next)[position.val].size) = some 11 at sizes
  have valid : phase.val < (chunks heap layout current channels within priorProgram.size next)[position.val].size := by
    rw [Option.some.inj sizes]
    exact phase.isLt
  have actual := resident_tail_fetch priorProgram heap layout channels within current later
    position (by change 4 ≤ 4; decide) phase.val valid
  norm_num only [residentTailCounts, List.take_succ_cons, List.take_zero, List.sum_cons,
    List.sum_nil, Nat.add_zero] at actual
  simpa only [chunks, placement, List.getElem_cons_zero, List.getElem_cons_succ,
    Nat.add_assoc, Nat.add_zero] using actual

/-- The allocateAt field is fetched from the actual materialized occurrence block. -/
theorem resident_head_allocateAt (priorProgram : Program width 8) (heap : Array (Word width))
    (layout : Layout ambient heap.size) (current : List (List (Reference ambient)))
    (later : List (List (List (Reference ambient)))) (channels : Nat) (within : channels ≤ ambient) :
    let next := priorProgram.size + (instructions heap layout current channels within priorProgram.size 0).length
    let p := placement width heap.size priorProgram.size next current
    let resident := residentProgram priorProgram heap layout channels within (current :: later)
    Controller.Horn.TrackedAllocate.CodeAt resident (p.query + 11) := by
  dsimp only
  intro phase
  let next := priorProgram.size + (instructions heap layout current channels within priorProgram.size 0).length
  let position : Fin (chunks heap layout current channels within priorProgram.size next).length :=
    ⟨5, by rw [resident_chunks_length]; decide⟩
  have sizes := congrArg (fun counts : List Nat => counts[position.val]?)
    (chunk_sizes heap layout current channels within priorProgram.size next)
  rw [List.getElem?_map, List.getElem?_eq_getElem position.isLt] at sizes
  change some ((chunks heap layout current channels within priorProgram.size next)[position.val].size) = some 5 at sizes
  have valid : phase.val < (chunks heap layout current channels within priorProgram.size next)[position.val].size := by
    rw [Option.some.inj sizes]
    exact phase.isLt
  have actual := resident_tail_fetch priorProgram heap layout channels within current later
    position (by change 4 ≤ 5; decide) phase.val valid
  norm_num only [residentTailCounts, List.take_succ_cons, List.take_zero, List.sum_cons,
    List.sum_nil, Nat.add_zero] at actual
  have optionEq : (Controller.Horn.TrackedAllocate.code width ((placement width heap.size priorProgram.size next current).query + 11))[phase.val]? = some (Controller.Horn.TrackedAllocate.code width ((placement width heap.size priorProgram.size next current).query + 11))[phase.val] :=
    Array.getElem?_eq_getElem (show phase.val < (Controller.Horn.TrackedAllocate.code width ((placement width heap.size priorProgram.size next current).query + 11)).size from phase.isLt)
  have fetched :
      (residentProgram priorProgram heap layout channels within (current :: later))[
        ((placement width heap.size priorProgram.size next current).query + 11) + phase.val]? =
        (Controller.Horn.TrackedAllocate.code width ((placement width heap.size priorProgram.size next current).query + 11))[phase.val]? := by
    simpa only [chunks, placement, List.getElem_cons_zero, List.getElem_cons_succ,
      Nat.add_assoc, Nat.add_zero] using actual
  exact fetched.trans optionEq

/-- The headersAt field is fetched from the actual materialized occurrence block. -/
theorem resident_head_headersAt (priorProgram : Program width 8) (heap : Array (Word width))
    (layout : Layout ambient heap.size) (current : List (List (Reference ambient)))
    (later : List (List (List (Reference ambient)))) (channels : Nat) (within : channels ≤ ambient) :
    let next := priorProgram.size + (instructions heap layout current channels within priorProgram.size 0).length
    let p := placement width heap.size priorProgram.size next current
    let resident := residentProgram priorProgram heap layout channels within (current :: later)
    ∀ phase : Fin 15, resident[p.query + 16 + phase.val]? = (scratchHeaderCode width)[phase.val]? := by
  dsimp only
  intro phase
  let next := priorProgram.size + (instructions heap layout current channels within priorProgram.size 0).length
  let position : Fin (chunks heap layout current channels within priorProgram.size next).length :=
    ⟨6, by rw [resident_chunks_length]; decide⟩
  have sizes := congrArg (fun counts : List Nat => counts[position.val]?)
    (chunk_sizes heap layout current channels within priorProgram.size next)
  rw [List.getElem?_map, List.getElem?_eq_getElem position.isLt] at sizes
  change some ((chunks heap layout current channels within priorProgram.size next)[position.val].size) = some 15 at sizes
  have valid : phase.val < (chunks heap layout current channels within priorProgram.size next)[position.val].size := by
    rw [Option.some.inj sizes]
    exact phase.isLt
  have actual := resident_tail_fetch priorProgram heap layout channels within current later
    position (by change 4 ≤ 6; decide) phase.val valid
  norm_num only [residentTailCounts, List.take_succ_cons, List.take_zero, List.sum_cons,
    List.sum_nil, Nat.add_zero] at actual
  simpa only [chunks, placement, List.getElem_cons_zero, List.getElem_cons_succ,
    Nat.add_assoc, Nat.add_zero] using actual

/-- The endpointAt field is fetched from the actual materialized occurrence block. -/
theorem resident_head_endpointAt (priorProgram : Program width 8) (heap : Array (Word width))
    (layout : Layout ambient heap.size) (current : List (List (Reference ambient)))
    (later : List (List (List (Reference ambient)))) (channels : Nat) (within : channels ≤ ambient) :
    let next := priorProgram.size + (instructions heap layout current channels within priorProgram.size 0).length
    let p := placement width heap.size priorProgram.size next current
    let resident := residentProgram priorProgram heap layout channels within (current :: later)
    ∀ phase : Fin 5, resident[p.query + 31 + phase.val]? = (scratchEndpointCode (width := width))[phase.val]? := by
  dsimp only
  intro phase
  let next := priorProgram.size + (instructions heap layout current channels within priorProgram.size 0).length
  let position : Fin (chunks heap layout current channels within priorProgram.size next).length :=
    ⟨7, by rw [resident_chunks_length]; decide⟩
  have sizes := congrArg (fun counts : List Nat => counts[position.val]?)
    (chunk_sizes heap layout current channels within priorProgram.size next)
  rw [List.getElem?_map, List.getElem?_eq_getElem position.isLt] at sizes
  change some ((chunks heap layout current channels within priorProgram.size next)[position.val].size) = some 5 at sizes
  have valid : phase.val < (chunks heap layout current channels within priorProgram.size next)[position.val].size := by
    rw [Option.some.inj sizes]
    exact phase.isLt
  have actual := resident_tail_fetch priorProgram heap layout channels within current later
    position (by change 4 ≤ 7; decide) phase.val valid
  norm_num only [residentTailCounts, List.take_succ_cons, List.take_zero, List.sum_cons,
    List.sum_nil, Nat.add_zero] at actual
  simpa only [chunks, placement, List.getElem_cons_zero, List.getElem_cons_succ,
    Nat.add_assoc, Nat.add_zero] using actual

/-- The saveAt field is fetched from the actual materialized occurrence block. -/
theorem resident_head_saveAt (priorProgram : Program width 8) (heap : Array (Word width))
    (layout : Layout ambient heap.size) (current : List (List (Reference ambient)))
    (later : List (List (List (Reference ambient)))) (channels : Nat) (within : channels ≤ ambient) :
    let next := priorProgram.size + (instructions heap layout current channels within priorProgram.size 0).length
    let p := placement width heap.size priorProgram.size next current
    let resident := residentProgram priorProgram heap layout channels within (current :: later)
    ∀ phase : Fin 6, resident[p.query + 36 + phase.val]? = (saveProjectionCode (width := width))[phase.val]? := by
  dsimp only
  intro phase
  let next := priorProgram.size + (instructions heap layout current channels within priorProgram.size 0).length
  let position : Fin (chunks heap layout current channels within priorProgram.size next).length :=
    ⟨8, by rw [resident_chunks_length]; decide⟩
  have sizes := congrArg (fun counts : List Nat => counts[position.val]?)
    (chunk_sizes heap layout current channels within priorProgram.size next)
  rw [List.getElem?_map, List.getElem?_eq_getElem position.isLt] at sizes
  change some ((chunks heap layout current channels within priorProgram.size next)[position.val].size) = some 6 at sizes
  have valid : phase.val < (chunks heap layout current channels within priorProgram.size next)[position.val].size := by
    rw [Option.some.inj sizes]
    exact phase.isLt
  have actual := resident_tail_fetch priorProgram heap layout channels within current later
    position (by change 4 ≤ 8; decide) phase.val valid
  norm_num only [residentTailCounts, List.take_succ_cons, List.take_zero, List.sum_cons,
    List.sum_nil, Nat.add_zero] at actual
  simpa only [chunks, placement, List.getElem_cons_zero, List.getElem_cons_succ,
    Nat.add_assoc, Nat.add_zero] using actual

/-- The indexSaveAt field is fetched from the actual materialized occurrence block. -/
theorem resident_head_indexSaveAt (priorProgram : Program width 8) (heap : Array (Word width))
    (layout : Layout ambient heap.size) (current : List (List (Reference ambient)))
    (later : List (List (List (Reference ambient)))) (channels : Nat) (within : channels ≤ ambient) :
    let next := priorProgram.size + (instructions heap layout current channels within priorProgram.size 0).length
    let p := placement width heap.size priorProgram.size next current
    let resident := residentProgram priorProgram heap layout channels within (current :: later)
    Controller.Cost.ForestZeroHeaderBridge.SaveAt resident (p.query + 203) (heap.size) := by
  dsimp only
  intro phase
  let next := priorProgram.size + (instructions heap layout current channels within priorProgram.size 0).length
  let position : Fin (chunks heap layout current channels within priorProgram.size next).length :=
    ⟨10, by rw [resident_chunks_length]; decide⟩
  have sizes := congrArg (fun counts : List Nat => counts[position.val]?)
    (chunk_sizes heap layout current channels within priorProgram.size next)
  rw [List.getElem?_map, List.getElem?_eq_getElem position.isLt] at sizes
  change some ((chunks heap layout current channels within priorProgram.size next)[position.val].size) = some 7 at sizes
  have valid : phase.val < (chunks heap layout current channels within priorProgram.size next)[position.val].size := by
    rw [Option.some.inj sizes]
    exact phase.isLt
  have actual := resident_tail_fetch priorProgram heap layout channels within current later
    position (by change 4 ≤ 10; decide) phase.val valid
  norm_num only [residentTailCounts, List.take_succ_cons, List.take_zero, List.sum_cons,
    List.sum_nil, Nat.add_zero] at actual
  have optionEq : (ForestZeroHeaderBridge.saveCode width heap.size)[phase.val]? = some (ForestZeroHeaderBridge.saveCode width heap.size)[phase.val] :=
    Array.getElem?_eq_getElem (show phase.val < (ForestZeroHeaderBridge.saveCode width heap.size).size from phase.isLt)
  have fetched :
      (residentProgram priorProgram heap layout channels within (current :: later))[
        ((placement width heap.size priorProgram.size next current).query + 203) + phase.val]? =
        (ForestZeroHeaderBridge.saveCode width heap.size)[phase.val]? := by
    simpa only [chunks, placement, List.getElem_cons_zero, List.getElem_cons_succ,
      Nat.add_assoc, Nat.add_zero] using actual
  exact fetched.trans optionEq

/-- The indexAt field is fetched from the actual materialized occurrence block. -/
theorem resident_head_indexAt (priorProgram : Program width 8) (heap : Array (Word width))
    (layout : Layout ambient heap.size) (current : List (List (Reference ambient)))
    (later : List (List (List (Reference ambient)))) (channels : Nat) (within : channels ≤ ambient) :
    let next := priorProgram.size + (instructions heap layout current channels within priorProgram.size 0).length
    let p := placement width heap.size priorProgram.size next current
    let resident := residentProgram priorProgram heap layout channels within (current :: later)
    Controller.Horn.IndexScan.At (n := (constructorDictionary heap layout (ForestZeroCompile.empty ambient) current).coordinates.size) resident (p.query + 210) ((constructorHeap heap layout (ForestZeroCompile.empty ambient) current channels).size) ((constructorHeap heap layout (ForestZeroCompile.empty ambient) current channels).size + 5 * (constructorDictionary heap layout (ForestZeroCompile.empty ambient) current).coordinates.size + 4) := by
  dsimp only
  intro phase
  let next := priorProgram.size + (instructions heap layout current channels within priorProgram.size 0).length
  let position : Fin (chunks heap layout current channels within priorProgram.size next).length :=
    ⟨11, by rw [resident_chunks_length]; decide⟩
  have sizes := congrArg (fun counts : List Nat => counts[position.val]?)
    (chunk_sizes heap layout current channels within priorProgram.size next)
  rw [List.getElem?_map, List.getElem?_eq_getElem position.isLt] at sizes
  change some ((chunks heap layout current channels within priorProgram.size next)[position.val].size) = some 32 at sizes
  have valid : phase.val < (chunks heap layout current channels within priorProgram.size next)[position.val].size := by
    rw [Option.some.inj sizes]
    exact phase.isLt
  have actual := resident_tail_fetch priorProgram heap layout channels within current later
    position (by change 4 ≤ 11; decide) phase.val valid
  norm_num only [residentTailCounts, List.take_succ_cons, List.take_zero, List.sum_cons,
    List.sum_nil, Nat.add_zero] at actual
  simpa only [chunks, placement, List.getElem_cons_zero, List.getElem_cons_succ,
    Nat.add_assoc, Nat.add_zero] using actual

/-- The indexRestoreAt field is fetched from the actual materialized occurrence block. -/
theorem resident_head_indexRestoreAt (priorProgram : Program width 8) (heap : Array (Word width))
    (layout : Layout ambient heap.size) (current : List (List (Reference ambient)))
    (later : List (List (List (Reference ambient)))) (channels : Nat) (within : channels ≤ ambient) :
    let next := priorProgram.size + (instructions heap layout current channels within priorProgram.size 0).length
    let p := placement width heap.size priorProgram.size next current
    let resident := residentProgram priorProgram heap layout channels within (current :: later)
    Controller.Cost.ForestZeroHeaderBridge.RestoreAt resident (p.query + 242) := by
  dsimp only
  intro phase
  let next := priorProgram.size + (instructions heap layout current channels within priorProgram.size 0).length
  let position : Fin (chunks heap layout current channels within priorProgram.size next).length :=
    ⟨12, by rw [resident_chunks_length]; decide⟩
  have sizes := congrArg (fun counts : List Nat => counts[position.val]?)
    (chunk_sizes heap layout current channels within priorProgram.size next)
  rw [List.getElem?_map, List.getElem?_eq_getElem position.isLt] at sizes
  change some ((chunks heap layout current channels within priorProgram.size next)[position.val].size) = some 3 at sizes
  have valid : phase.val < (chunks heap layout current channels within priorProgram.size next)[position.val].size := by
    rw [Option.some.inj sizes]
    exact phase.isLt
  have actual := resident_tail_fetch priorProgram heap layout channels within current later
    position (by change 4 ≤ 12; decide) phase.val valid
  norm_num only [residentTailCounts, List.take_succ_cons, List.take_zero, List.sum_cons,
    List.sum_nil, Nat.add_zero] at actual
  have optionEq : (ForestZeroHeaderBridge.restoreCode width)[phase.val]? = some (ForestZeroHeaderBridge.restoreCode width)[phase.val] :=
    Array.getElem?_eq_getElem (show phase.val < (ForestZeroHeaderBridge.restoreCode width).size from phase.isLt)
  have fetched :
      (residentProgram priorProgram heap layout channels within (current :: later))[
        ((placement width heap.size priorProgram.size next current).query + 242) + phase.val]? =
        (ForestZeroHeaderBridge.restoreCode width)[phase.val]? := by
    simpa only [chunks, placement, List.getElem_cons_zero, List.getElem_cons_succ,
      Nat.add_assoc, Nat.add_zero] using actual
  exact fetched.trans optionEq

/-- The captureAt field is fetched from the actual materialized occurrence block. -/
theorem resident_head_captureAt (priorProgram : Program width 8) (heap : Array (Word width))
    (layout : Layout ambient heap.size) (current : List (List (Reference ambient)))
    (later : List (List (List (Reference ambient)))) (channels : Nat) (within : channels ≤ ambient) :
    let next := priorProgram.size + (instructions heap layout current channels within priorProgram.size 0).length
    let p := placement width heap.size priorProgram.size next current
    let resident := residentProgram priorProgram heap layout channels within (current :: later)
    ∀ phase : Fin 6, resident[p.query + 245 + phase.val]? = (Controller.Cost.ForestZeroReclaim.captureCode width)[phase.val]? := by
  dsimp only
  intro phase
  let next := priorProgram.size + (instructions heap layout current channels within priorProgram.size 0).length
  let position : Fin (chunks heap layout current channels within priorProgram.size next).length :=
    ⟨13, by rw [resident_chunks_length]; decide⟩
  have sizes := congrArg (fun counts : List Nat => counts[position.val]?)
    (chunk_sizes heap layout current channels within priorProgram.size next)
  rw [List.getElem?_map, List.getElem?_eq_getElem position.isLt] at sizes
  change some ((chunks heap layout current channels within priorProgram.size next)[position.val].size) = some 6 at sizes
  have valid : phase.val < (chunks heap layout current channels within priorProgram.size next)[position.val].size := by
    rw [Option.some.inj sizes]
    exact phase.isLt
  have actual := resident_tail_fetch priorProgram heap layout channels within current later
    position (by change 4 ≤ 13; decide) phase.val valid
  norm_num only [residentTailCounts, List.take_succ_cons, List.take_zero, List.sum_cons,
    List.sum_nil, Nat.add_zero] at actual
  simpa only [chunks, placement, List.getElem_cons_zero, List.getElem_cons_succ,
    Nat.add_assoc, Nat.add_zero] using actual

/-- The setupAt field is fetched from the actual materialized occurrence block. -/
theorem resident_head_setupAt (priorProgram : Program width 8) (heap : Array (Word width))
    (layout : Layout ambient heap.size) (current : List (List (Reference ambient)))
    (later : List (List (List (Reference ambient)))) (channels : Nat) (within : channels ≤ ambient) :
    let next := priorProgram.size + (instructions heap layout current channels within priorProgram.size 0).length
    let p := placement width heap.size priorProgram.size next current
    let resident := residentProgram priorProgram heap layout channels within (current :: later)
    ∀ phase : Fin 10, resident[p.query + 251 + phase.val]? =
          (Controller.Cost.ForestZeroSeedSetup.code (n := (constructorDictionary heap layout (ForestZeroCompile.empty ambient) current).coordinates.size) width ((constructorHeap heap layout (ForestZeroCompile.empty ambient) current channels).size) (heap.size) ((constructorHeap heap layout (ForestZeroCompile.empty ambient) current channels).size + 5 * (constructorDictionary heap layout (ForestZeroCompile.empty ambient) current).coordinates.size + 4) p.scan)[phase.val]? := by
  dsimp only
  intro phase
  let next := priorProgram.size + (instructions heap layout current channels within priorProgram.size 0).length
  let position : Fin (chunks heap layout current channels within priorProgram.size next).length :=
    ⟨14, by rw [resident_chunks_length]; decide⟩
  have sizes := congrArg (fun counts : List Nat => counts[position.val]?)
    (chunk_sizes heap layout current channels within priorProgram.size next)
  rw [List.getElem?_map, List.getElem?_eq_getElem position.isLt] at sizes
  change some ((chunks heap layout current channels within priorProgram.size next)[position.val].size) = some 10 at sizes
  have valid : phase.val < (chunks heap layout current channels within priorProgram.size next)[position.val].size := by
    rw [Option.some.inj sizes]
    exact phase.isLt
  have actual := resident_tail_fetch priorProgram heap layout channels within current later
    position (by change 4 ≤ 14; decide) phase.val valid
  norm_num only [residentTailCounts, List.take_succ_cons, List.take_zero, List.sum_cons,
    List.sum_nil, Nat.add_zero] at actual
  simpa only [chunks, placement, List.getElem_cons_zero, List.getElem_cons_succ,
    Nat.add_assoc, Nat.add_zero] using actual

/-- The scanAt field is fetched from the actual materialized occurrence block. -/
theorem resident_head_scanAt (priorProgram : Program width 8) (heap : Array (Word width))
    (layout : Layout ambient heap.size) (current : List (List (Reference ambient)))
    (later : List (List (List (Reference ambient)))) (channels : Nat) (within : channels ≤ ambient) :
    let next := priorProgram.size + (instructions heap layout current channels within priorProgram.size 0).length
    let p := placement width heap.size priorProgram.size next current
    let resident := residentProgram priorProgram heap layout channels within (current :: later)
    Controller.Horn.WorklistSeed.At (n := (constructorDictionary heap layout (ForestZeroCompile.empty ambient) current).coordinates.size) resident ((constructorHeap heap layout (ForestZeroCompile.empty ambient) current channels).size) p.scan p.seedDone p.conflict := by
  dsimp only
  intro phase
  let next := priorProgram.size + (instructions heap layout current channels within priorProgram.size 0).length
  let position : Fin (chunks heap layout current channels within priorProgram.size next).length :=
    ⟨15, by rw [resident_chunks_length]; decide⟩
  have sizes := congrArg (fun counts : List Nat => counts[position.val]?)
    (chunk_sizes heap layout current channels within priorProgram.size next)
  rw [List.getElem?_map, List.getElem?_eq_getElem position.isLt] at sizes
  change some ((chunks heap layout current channels within priorProgram.size next)[position.val].size) = some 47 at sizes
  have valid : phase.val < (chunks heap layout current channels within priorProgram.size next)[position.val].size := by
    rw [Option.some.inj sizes]
    exact phase.isLt
  have actual := resident_tail_fetch priorProgram heap layout channels within current later
    position (by change 4 ≤ 15; decide) phase.val valid
  norm_num only [residentTailCounts, List.take_succ_cons, List.take_zero, List.sum_cons,
    List.sum_nil, Nat.add_zero] at actual
  simpa only [chunks, placement, List.getElem_cons_zero, List.getElem_cons_succ,
    Nat.add_assoc, Nat.add_zero] using actual

/-- The headAt field is fetched from the actual materialized occurrence block. -/
theorem resident_head_headAt (priorProgram : Program width 8) (heap : Array (Word width))
    (layout : Layout ambient heap.size) (current : List (List (Reference ambient)))
    (later : List (List (List (Reference ambient)))) (channels : Nat) (within : channels ≤ ambient) :
    let next := priorProgram.size + (instructions heap layout current channels within priorProgram.size 0).length
    let p := placement width heap.size priorProgram.size next current
    let resident := residentProgram priorProgram heap layout channels within (current :: later)
    ∀ phase : Fin 4, resident[p.seedDone + phase.val]? =
          (Controller.Horn.WorklistAccept.headSetupCode (n := (constructorDictionary heap layout (ForestZeroCompile.empty ambient) current).coordinates.size) width ((constructorHeap heap layout (ForestZeroCompile.empty ambient) current channels).size) p.fetch)[phase.val]? := by
  dsimp only
  intro phase
  let next := priorProgram.size + (instructions heap layout current channels within priorProgram.size 0).length
  let position : Fin (chunks heap layout current channels within priorProgram.size next).length :=
    ⟨16, by rw [resident_chunks_length]; decide⟩
  have sizes := congrArg (fun counts : List Nat => counts[position.val]?)
    (chunk_sizes heap layout current channels within priorProgram.size next)
  rw [List.getElem?_map, List.getElem?_eq_getElem position.isLt] at sizes
  change some ((chunks heap layout current channels within priorProgram.size next)[position.val].size) = some 4 at sizes
  have valid : phase.val < (chunks heap layout current channels within priorProgram.size next)[position.val].size := by
    rw [Option.some.inj sizes]
    exact phase.isLt
  have actual := resident_tail_fetch priorProgram heap layout channels within current later
    position (by change 4 ≤ 16; decide) phase.val valid
  norm_num only [residentTailCounts, List.take_succ_cons, List.take_zero, List.sum_cons,
    List.sum_nil, Nat.add_zero] at actual
  simpa only [chunks, placement, List.getElem_cons_zero, List.getElem_cons_succ,
    Nat.add_assoc, Nat.add_zero] using actual

/-- The fetchAt field is fetched from the actual materialized occurrence block. -/
theorem resident_head_fetchAt (priorProgram : Program width 8) (heap : Array (Word width))
    (layout : Layout ambient heap.size) (current : List (List (Reference ambient)))
    (later : List (List (List (Reference ambient)))) (channels : Nat) (within : channels ≤ ambient) :
    let next := priorProgram.size + (instructions heap layout current channels within priorProgram.size 0).length
    let p := placement width heap.size priorProgram.size next current
    let resident := residentProgram priorProgram heap layout channels within (current :: later)
    Controller.Horn.WorklistFIFO.FetchAt (n := (constructorDictionary heap layout (ForestZeroCompile.empty ambient) current).coordinates.size) resident ((constructorHeap heap layout (ForestZeroCompile.empty ambient) current channels).size) p.fetch p.success p.bucket := by
  dsimp only
  intro phase
  let next := priorProgram.size + (instructions heap layout current channels within priorProgram.size 0).length
  let position : Fin (chunks heap layout current channels within priorProgram.size next).length :=
    ⟨17, by rw [resident_chunks_length]; decide⟩
  have sizes := congrArg (fun counts : List Nat => counts[position.val]?)
    (chunk_sizes heap layout current channels within priorProgram.size next)
  rw [List.getElem?_map, List.getElem?_eq_getElem position.isLt] at sizes
  change some ((chunks heap layout current channels within priorProgram.size next)[position.val].size) = some 14 at sizes
  have valid : phase.val < (chunks heap layout current channels within priorProgram.size next)[position.val].size := by
    rw [Option.some.inj sizes]
    exact phase.isLt
  have actual := resident_tail_fetch priorProgram heap layout channels within current later
    position (by change 4 ≤ 17; decide) phase.val valid
  norm_num only [residentTailCounts, List.take_succ_cons, List.take_zero, List.sum_cons,
    List.sum_nil, Nat.add_zero] at actual
  simpa only [chunks, placement, List.getElem_cons_zero, List.getElem_cons_succ,
    Nat.add_assoc, Nat.add_zero] using actual

/-- The advanceAt field is fetched from the actual materialized occurrence block. -/
theorem resident_head_advanceAt (priorProgram : Program width 8) (heap : Array (Word width))
    (layout : Layout ambient heap.size) (current : List (List (Reference ambient)))
    (later : List (List (List (Reference ambient)))) (channels : Nat) (within : channels ≤ ambient) :
    let next := priorProgram.size + (instructions heap layout current channels within priorProgram.size 0).length
    let p := placement width heap.size priorProgram.size next current
    let resident := residentProgram priorProgram heap layout channels within (current :: later)
    Controller.Horn.WorklistFIFO.AdvanceAt (n := (constructorDictionary heap layout (ForestZeroCompile.empty ambient) current).coordinates.size) resident ((constructorHeap heap layout (ForestZeroCompile.empty ambient) current channels).size) p.advance p.fetch := by
  dsimp only
  intro phase
  let next := priorProgram.size + (instructions heap layout current channels within priorProgram.size 0).length
  let position : Fin (chunks heap layout current channels within priorProgram.size next).length :=
    ⟨18, by rw [resident_chunks_length]; decide⟩
  have sizes := congrArg (fun counts : List Nat => counts[position.val]?)
    (chunk_sizes heap layout current channels within priorProgram.size next)
  rw [List.getElem?_map, List.getElem?_eq_getElem position.isLt] at sizes
  change some ((chunks heap layout current channels within priorProgram.size next)[position.val].size) = some 5 at sizes
  have valid : phase.val < (chunks heap layout current channels within priorProgram.size next)[position.val].size := by
    rw [Option.some.inj sizes]
    exact phase.isLt
  have actual := resident_tail_fetch priorProgram heap layout channels within current later
    position (by change 4 ≤ 18; decide) phase.val valid
  norm_num only [residentTailCounts, List.take_succ_cons, List.take_zero, List.sum_cons,
    List.sum_nil, Nat.add_zero] at actual
  simpa only [chunks, placement, List.getElem_cons_zero, List.getElem_cons_succ,
    Nat.add_assoc, Nat.add_zero] using actual

/-- The loopAt field is fetched from the actual materialized occurrence block. -/
theorem resident_head_loopAt (priorProgram : Program width 8) (heap : Array (Word width))
    (layout : Layout ambient heap.size) (current : List (List (Reference ambient)))
    (later : List (List (List (Reference ambient)))) (channels : Nat) (within : channels ≤ ambient) :
    let next := priorProgram.size + (instructions heap layout current channels within priorProgram.size 0).length
    let p := placement width heap.size priorProgram.size next current
    let resident := residentProgram priorProgram heap layout channels within (current :: later)
    Controller.Horn.WorklistBucketLoop.At resident p.bucket p.advance p.ready := by
  dsimp only
  intro phase
  let next := priorProgram.size + (instructions heap layout current channels within priorProgram.size 0).length
  let position : Fin (chunks heap layout current channels within priorProgram.size next).length :=
    ⟨19, by rw [resident_chunks_length]; decide⟩
  have sizes := congrArg (fun counts : List Nat => counts[position.val]?)
    (chunk_sizes heap layout current channels within priorProgram.size next)
  rw [List.getElem?_map, List.getElem?_eq_getElem position.isLt] at sizes
  change some ((chunks heap layout current channels within priorProgram.size next)[position.val].size) = some 12 at sizes
  have valid : phase.val < (chunks heap layout current channels within priorProgram.size next)[position.val].size := by
    rw [Option.some.inj sizes]
    exact phase.isLt
  have actual := resident_tail_fetch priorProgram heap layout channels within current later
    position (by change 4 ≤ 19; decide) phase.val valid
  norm_num only [residentTailCounts, List.take_succ_cons, List.take_zero, List.sum_cons,
    List.sum_nil, Nat.add_zero] at actual
  simpa only [chunks, placement, List.getElem_cons_zero, List.getElem_cons_succ,
    Nat.add_assoc, Nat.add_zero] using actual

/-- The readyAt field is fetched from the actual materialized occurrence block. -/
theorem resident_head_readyAt (priorProgram : Program width 8) (heap : Array (Word width))
    (layout : Layout ambient heap.size) (current : List (List (Reference ambient)))
    (later : List (List (List (Reference ambient)))) (channels : Nat) (within : channels ≤ ambient) :
    let next := priorProgram.size + (instructions heap layout current channels within priorProgram.size 0).length
    let p := placement width heap.size priorProgram.size next current
    let resident := residentProgram priorProgram heap layout channels within (current :: later)
    Controller.Horn.WorklistBucketReady.At (n := (constructorDictionary heap layout (ForestZeroCompile.empty ambient) current).coordinates.size) resident ((constructorHeap heap layout (ForestZeroCompile.empty ambient) current channels).size) p.ready p.advance p.conflict p.bucket := by
  dsimp only
  intro phase
  let next := priorProgram.size + (instructions heap layout current channels within priorProgram.size 0).length
  let position : Fin (chunks heap layout current channels within priorProgram.size next).length :=
    ⟨20, by rw [resident_chunks_length]; decide⟩
  have sizes := congrArg (fun counts : List Nat => counts[position.val]?)
    (chunk_sizes heap layout current channels within priorProgram.size next)
  rw [List.getElem?_map, List.getElem?_eq_getElem position.isLt] at sizes
  change some ((chunks heap layout current channels within priorProgram.size next)[position.val].size) = some 26 at sizes
  have valid : phase.val < (chunks heap layout current channels within priorProgram.size next)[position.val].size := by
    rw [Option.some.inj sizes]
    exact phase.isLt
  have actual := resident_tail_fetch priorProgram heap layout channels within current later
    position (by change 4 ≤ 20; decide) phase.val valid
  norm_num only [residentTailCounts, List.take_succ_cons, List.take_zero, List.sum_cons,
    List.sum_nil, Nat.add_zero] at actual
  simpa only [chunks, placement, List.getElem_cons_zero, List.getElem_cons_succ,
    Nat.add_assoc, Nat.add_zero] using actual

/-- The successAt field is fetched from the actual materialized occurrence block. -/
theorem resident_head_successAt (priorProgram : Program width 8) (heap : Array (Word width))
    (layout : Layout ambient heap.size) (current : List (List (Reference ambient)))
    (later : List (List (List (Reference ambient)))) (channels : Nat) (within : channels ≤ ambient) :
    let next := priorProgram.size + (instructions heap layout current channels within priorProgram.size 0).length
    let p := placement width heap.size priorProgram.size next current
    let resident := residentProgram priorProgram heap layout channels within (current :: later)
    Controller.Cost.ForestZeroAnswer.SavedAt resident p.success 1 p.projection := by
  dsimp only
  intro phase
  let next := priorProgram.size + (instructions heap layout current channels within priorProgram.size 0).length
  let position : Fin (chunks heap layout current channels within priorProgram.size next).length :=
    ⟨21, by rw [resident_chunks_length]; decide⟩
  have sizes := congrArg (fun counts : List Nat => counts[position.val]?)
    (chunk_sizes heap layout current channels within priorProgram.size next)
  rw [List.getElem?_map, List.getElem?_eq_getElem position.isLt] at sizes
  change some ((chunks heap layout current channels within priorProgram.size next)[position.val].size) = some 13 at sizes
  have valid : phase.val < (chunks heap layout current channels within priorProgram.size next)[position.val].size := by
    rw [Option.some.inj sizes]
    exact phase.isLt
  have actual := resident_tail_fetch priorProgram heap layout channels within current later
    position (by change 4 ≤ 21; decide) phase.val valid
  norm_num only [residentTailCounts, List.take_succ_cons, List.take_zero, List.sum_cons,
    List.sum_nil, Nat.add_zero] at actual
  simpa only [chunks, placement, List.getElem_cons_zero, List.getElem_cons_succ,
    Nat.add_assoc, Nat.add_zero] using actual

/-- The conflictAt field is fetched from the actual materialized occurrence block. -/
theorem resident_head_conflictAt (priorProgram : Program width 8) (heap : Array (Word width))
    (layout : Layout ambient heap.size) (current : List (List (Reference ambient)))
    (later : List (List (List (Reference ambient)))) (channels : Nat) (within : channels ≤ ambient) :
    let next := priorProgram.size + (instructions heap layout current channels within priorProgram.size 0).length
    let p := placement width heap.size priorProgram.size next current
    let resident := residentProgram priorProgram heap layout channels within (current :: later)
    Controller.Cost.ForestZeroAnswer.SavedAt resident p.conflict 0 p.cleanup := by
  dsimp only
  intro phase
  let next := priorProgram.size + (instructions heap layout current channels within priorProgram.size 0).length
  let position : Fin (chunks heap layout current channels within priorProgram.size next).length :=
    ⟨22, by rw [resident_chunks_length]; decide⟩
  have sizes := congrArg (fun counts : List Nat => counts[position.val]?)
    (chunk_sizes heap layout current channels within priorProgram.size next)
  rw [List.getElem?_map, List.getElem?_eq_getElem position.isLt] at sizes
  change some ((chunks heap layout current channels within priorProgram.size next)[position.val].size) = some 13 at sizes
  have valid : phase.val < (chunks heap layout current channels within priorProgram.size next)[position.val].size := by
    rw [Option.some.inj sizes]
    exact phase.isLt
  have actual := resident_tail_fetch priorProgram heap layout channels within current later
    position (by change 4 ≤ 22; decide) phase.val valid
  norm_num only [residentTailCounts, List.take_succ_cons, List.take_zero, List.sum_cons,
    List.sum_nil, Nat.add_zero] at actual
  simpa only [chunks, placement, List.getElem_cons_zero, List.getElem_cons_succ,
    Nat.add_assoc, Nat.add_zero] using actual

/-- The constantsAt field is fetched from the actual materialized occurrence block. -/
theorem resident_head_constantsAt (priorProgram : Program width 8) (heap : Array (Word width))
    (layout : Layout ambient heap.size) (current : List (List (Reference ambient)))
    (later : List (List (List (Reference ambient)))) (channels : Nat) (within : channels ≤ ambient) :
    let next := priorProgram.size + (instructions heap layout current channels within priorProgram.size 0).length
    let p := placement width heap.size priorProgram.size next current
    let resident := residentProgram priorProgram heap layout channels within (current :: later)
    ∀ phase : Fin 2, resident[p.projection + phase.val]? =
          (projectionConstantsCode width)[phase.val]? := by
  dsimp only
  intro phase
  let next := priorProgram.size + (instructions heap layout current channels within priorProgram.size 0).length
  let position : Fin (chunks heap layout current channels within priorProgram.size next).length :=
    ⟨23, by rw [resident_chunks_length]; decide⟩
  have sizes := congrArg (fun counts : List Nat => counts[position.val]?)
    (chunk_sizes heap layout current channels within priorProgram.size next)
  rw [List.getElem?_map, List.getElem?_eq_getElem position.isLt] at sizes
  change some ((chunks heap layout current channels within priorProgram.size next)[position.val].size) = some 2 at sizes
  have valid : phase.val < (chunks heap layout current channels within priorProgram.size next)[position.val].size := by
    rw [Option.some.inj sizes]
    exact phase.isLt
  have actual := resident_tail_fetch priorProgram heap layout channels within current later
    position (by change 4 ≤ 23; decide) phase.val valid
  norm_num only [residentTailCounts, List.take_succ_cons, List.take_zero, List.sum_cons,
    List.sum_nil, Nat.add_zero] at actual
  simpa only [chunks, placement, List.getElem_cons_zero, List.getElem_cons_succ,
    Nat.add_assoc, Nat.add_zero] using actual

/-- The preparationAt field is fetched from the actual materialized occurrence block. -/
theorem resident_head_preparationAt (priorProgram : Program width 8) (heap : Array (Word width))
    (layout : Layout ambient heap.size) (current : List (List (Reference ambient)))
    (later : List (List (List (Reference ambient)))) (channels : Nat) (within : channels ≤ ambient) :
    let next := priorProgram.size + (instructions heap layout current channels within priorProgram.size 0).length
    let p := placement width heap.size priorProgram.size next current
    let resident := residentProgram priorProgram heap layout channels within (current :: later)
    ∀ phase : Fin 19, resident[p.projection + 2 + phase.val]? =
          (channelPrepareCode width)[phase.val]? := by
  dsimp only
  intro phase
  let next := priorProgram.size + (instructions heap layout current channels within priorProgram.size 0).length
  let position : Fin (chunks heap layout current channels within priorProgram.size next).length :=
    ⟨24, by rw [resident_chunks_length]; decide⟩
  have sizes := congrArg (fun counts : List Nat => counts[position.val]?)
    (chunk_sizes heap layout current channels within priorProgram.size next)
  rw [List.getElem?_map, List.getElem?_eq_getElem position.isLt] at sizes
  change some ((chunks heap layout current channels within priorProgram.size next)[position.val].size) = some 19 at sizes
  have valid : phase.val < (chunks heap layout current channels within priorProgram.size next)[position.val].size := by
    rw [Option.some.inj sizes]
    exact phase.isLt
  have actual := resident_tail_fetch priorProgram heap layout channels within current later
    position (by change 4 ≤ 24; decide) phase.val valid
  norm_num only [residentTailCounts, List.take_succ_cons, List.take_zero, List.sum_cons,
    List.sum_nil, Nat.add_zero] at actual
  simpa only [chunks, placement, List.getElem_cons_zero, List.getElem_cons_succ,
    ← Nat.add_assoc, Nat.reduceAdd, Nat.add_zero] using actual

/-- The emitAt field is fetched from the actual materialized occurrence block. -/
theorem resident_head_emitAt (priorProgram : Program width 8) (heap : Array (Word width))
    (layout : Layout ambient heap.size) (current : List (List (Reference ambient)))
    (later : List (List (List (Reference ambient)))) (channels : Nat) (within : channels ≤ ambient) :
    let next := priorProgram.size + (instructions heap layout current channels within priorProgram.size 0).length
    let p := placement width heap.size priorProgram.size next current
    let resident := residentProgram priorProgram heap layout channels within (current :: later)
    Controller.Cost.ForestZeroChannelEmit.CodeAt resident (p.projection + 21) p.cleanup := by
  dsimp only
  intro phase
  let next := priorProgram.size + (instructions heap layout current channels within priorProgram.size 0).length
  let position : Fin (chunks heap layout current channels within priorProgram.size next).length :=
    ⟨25, by rw [resident_chunks_length]; decide⟩
  have sizes := congrArg (fun counts : List Nat => counts[position.val]?)
    (chunk_sizes heap layout current channels within priorProgram.size next)
  rw [List.getElem?_map, List.getElem?_eq_getElem position.isLt] at sizes
  change some ((chunks heap layout current channels within priorProgram.size next)[position.val].size) = some 14 at sizes
  have valid : phase.val < (chunks heap layout current channels within priorProgram.size next)[position.val].size := by
    rw [Option.some.inj sizes]
    exact phase.isLt
  have actual := resident_tail_fetch priorProgram heap layout channels within current later
    position (by change 4 ≤ 25; decide) phase.val valid
  norm_num only [residentTailCounts, List.take_succ_cons, List.take_zero, List.sum_cons,
    List.sum_nil, Nat.add_zero] at actual
  simpa only [chunks, placement, List.getElem_cons_zero, List.getElem_cons_succ,
    ← Nat.add_assoc, Nat.reduceAdd, Nat.add_zero] using actual

/-- The cleanupSetup field is fetched from the actual materialized occurrence block. -/
theorem resident_head_cleanupSetup (priorProgram : Program width 8) (heap : Array (Word width))
    (layout : Layout ambient heap.size) (current : List (List (Reference ambient)))
    (later : List (List (List (Reference ambient)))) (channels : Nat) (within : channels ≤ ambient) :
    let next := priorProgram.size + (instructions heap layout current channels within priorProgram.size 0).length
    let p := placement width heap.size priorProgram.size next current
    let resident := residentProgram priorProgram heap layout channels within (current :: later)
    ∀ phase : Fin 3, resident[p.cleanup + phase.val]? =
          (Controller.Cost.ForestZeroReclaim.setupCode width)[phase.val]? := by
  dsimp only
  intro phase
  let next := priorProgram.size + (instructions heap layout current channels within priorProgram.size 0).length
  let position : Fin (chunks heap layout current channels within priorProgram.size next).length :=
    ⟨26, by rw [resident_chunks_length]; decide⟩
  have sizes := congrArg (fun counts : List Nat => counts[position.val]?)
    (chunk_sizes heap layout current channels within priorProgram.size next)
  rw [List.getElem?_map, List.getElem?_eq_getElem position.isLt] at sizes
  change some ((chunks heap layout current channels within priorProgram.size next)[position.val].size) = some 3 at sizes
  have valid : phase.val < (chunks heap layout current channels within priorProgram.size next)[position.val].size := by
    rw [Option.some.inj sizes]
    exact phase.isLt
  have actual := resident_tail_fetch priorProgram heap layout channels within current later
    position (by change 4 ≤ 26; decide) phase.val valid
  norm_num only [residentTailCounts, List.take_succ_cons, List.take_zero, List.sum_cons,
    List.sum_nil, Nat.add_zero] at actual
  simpa only [chunks, placement, List.getElem_cons_zero, List.getElem_cons_succ,
    ← Nat.add_assoc, Nat.reduceAdd, Nat.add_zero] using actual

/-- The cleanupLoop field is fetched from the actual materialized occurrence block. -/
theorem resident_head_cleanupLoop (priorProgram : Program width 8) (heap : Array (Word width))
    (layout : Layout ambient heap.size) (current : List (List (Reference ambient)))
    (later : List (List (List (Reference ambient)))) (channels : Nat) (within : channels ≤ ambient) :
    let next := priorProgram.size + (instructions heap layout current channels within priorProgram.size 0).length
    let p := placement width heap.size priorProgram.size next current
    let resident := residentProgram priorProgram heap layout channels within (current :: later)
    Controller.Cost.ForestZeroReclaim.At resident (p.cleanup + 3) p.returned := by
  dsimp only
  intro phase
  let next := priorProgram.size + (instructions heap layout current channels within priorProgram.size 0).length
  let position : Fin (chunks heap layout current channels within priorProgram.size next).length :=
    ⟨27, by rw [resident_chunks_length]; decide⟩
  have sizes := congrArg (fun counts : List Nat => counts[position.val]?)
    (chunk_sizes heap layout current channels within priorProgram.size next)
  rw [List.getElem?_map, List.getElem?_eq_getElem position.isLt] at sizes
  change some ((chunks heap layout current channels within priorProgram.size next)[position.val].size) = some 4 at sizes
  have valid : phase.val < (chunks heap layout current channels within priorProgram.size next)[position.val].size := by
    rw [Option.some.inj sizes]
    exact phase.isLt
  have actual := resident_tail_fetch priorProgram heap layout channels within current later
    position (by change 4 ≤ 27; decide) phase.val valid
  norm_num only [residentTailCounts, List.take_succ_cons, List.take_zero, List.sum_cons,
    List.sum_nil, Nat.add_zero] at actual
  simpa only [chunks, placement, List.getElem_cons_zero, List.getElem_cons_succ,
    ← Nat.add_assoc, Nat.reduceAdd, Nat.add_zero] using actual

/-- The dispatchAt field is fetched from the actual materialized occurrence block. -/
theorem resident_head_dispatchAt (priorProgram : Program width 8) (heap : Array (Word width))
    (layout : Layout ambient heap.size) (current : List (List (Reference ambient)))
    (later : List (List (List (Reference ambient)))) (channels : Nat) (within : channels ≤ ambient) :
    let next := priorProgram.size + (instructions heap layout current channels within priorProgram.size 0).length
    let p := placement width heap.size priorProgram.size next current
    let resident := residentProgram priorProgram heap layout channels within (current :: later)
    ∀ phase : Fin 2, resident[p.dispatch + phase.val]? =
    (ForestZeroRootLoop.dispatchCode width next)[phase.val]? := by
  dsimp only
  intro phase
  let next := priorProgram.size + (instructions heap layout current channels within priorProgram.size 0).length
  let position : Fin (chunks heap layout current channels within priorProgram.size next).length :=
    ⟨31, by rw [resident_chunks_length]; decide⟩
  have sizes := congrArg (fun counts : List Nat => counts[position.val]?)
    (chunk_sizes heap layout current channels within priorProgram.size next)
  rw [List.getElem?_map, List.getElem?_eq_getElem position.isLt] at sizes
  change some ((chunks heap layout current channels within priorProgram.size next)[position.val].size) = some 2 at sizes
  have valid : phase.val < (chunks heap layout current channels within priorProgram.size next)[position.val].size := by
    rw [Option.some.inj sizes]
    exact phase.isLt
  have actual := resident_tail_fetch priorProgram heap layout channels within current later
    position (by change 4 ≤ 31; decide) phase.val valid
  norm_num only [residentTailCounts, List.take_succ_cons, List.take_zero, List.sum_cons,
    List.sum_nil, Nat.add_zero] at actual
  simpa only [chunks, placement, List.getElem_cons_zero, List.getElem_cons_succ,
    ← Nat.add_assoc, Nat.reduceAdd, Nat.add_zero] using actual

end Controller.Cost.ForestZeroSourcePlan

namespace Controller.Cost.ForestZeroSourcePlan
open Controller.CNF
open Controller.Cost Controller.Cost.ForestZeroResident Controller.Cost.ForestZeroDictionary
open Controller.Cost.ForestZeroCompile Controller.Cost.ForestZeroEmit
open Controller.Cost.ForestZeroAdmissibleCaller

/-- Resident array formation discharges every fetched field of the complete
query endpoint. Input cells remain explicit source correspondences, not
execution or formula oracles. -/
def resident_head_plan (priorProgram : Program width 8) (initial : State width 8)
    (layout : Layout ambient initial.heap.size) (current : List (List (Reference ambient)))
    (later : List (List (List (Reference ambient)))) (channels sourceEnd nodes : Nat)
    (within : channels ≤ ambient) (callerRest : List (Word width))
    (stored : ∀ reference ∈ current.flatten, StoredReference initial.heap channels sourceEnd reference)
    (beforeTable : sourceEnd ≤ layout.tableBase) (beforeInverse : sourceEnd ≤ layout.inverseBase)
    (sourceBound : sourceEnd ≤ initial.heap.size) (headerRoom : 1 < sourceEnd)
    (channelsCell : initial.heap[0]? = some (word width channels))
    (nodesCell : initial.heap[1]? = some (word width nodes))
    (ambientEq : ambient = channels + nodes) (adjacent : layout.inverseBase = layout.tableBase + ambient)
    (endpoint : initial.heap.size = layout.inverseBase + ambient)
    (grammar : Controller.Horn.DualHorn (ofClauses (ForestZeroAssembly.originalRows (reservedReferences current))))
    (programRoom : (residentProgram priorProgram initial.heap layout channels within (current :: later)).size < 2 ^ width)
    (wordRoom : initial.heap.size + 2 * ambient + 14 + 5 * current.length + 15 * current.flatten.length < 2 ^ width) :
    let next := priorProgram.size + (instructions initial.heap layout current channels within priorProgram.size 0).length
    let p := placement width initial.heap.size priorProgram.size next current
    SourceQueryPlan (residentProgram priorProgram initial.heap layout channels within (current :: later))
      initial layout current sourceEnd nodes priorProgram.size callerRest within p.dispatch next := by
  intro next p
  have pcRoom := resident_head_pc_room priorProgram initial.heap layout current later channels within programRoom
  have rooms := query_all_word_rooms initial.heap layout current channels within wordRoom
  have constructorLength := constructor_length_relocate width (priorProgram.size + 15) (priorProgram.size + 15)
    initial.heap.size initial.heap.size (initial.heap.size + 4) p.query 0 current
  have queryEnd : priorProgram.size + 15 +
      (constructorCode width (priorProgram.size + 15) initial.heap.size initial.heap.size
        (initial.heap.size + 4) p.query current).length = p.query := by
    rw [constructorLength]
    rfl
  have tablesPositive : 0 < layout.tableBase := lt_of_lt_of_le (by omega) beforeTable
  refine {
    sourceReferences := stored
    sourceBeforeTable := beforeTable
    sourceBeforeInverse := beforeInverse
    sourceBound := sourceBound
    sourcePositive := by omega
    sourceChannel := channelsCell
    sourceNodes := nodesCell
    ambientEq := ambientEq
    adjacent := adjacent
    tablePositive := tablesPositive
    sourceHeaderRoom := headerRoom
    sourceDual := grammar
    constructorEntry := p.constructor
    entry := p.query
    entryEq := rfl
    sourceEndpoint := endpoint
    entryCapacity := by dsimp only [p, placement] at pcRoom ⊢; omega
    entryAt := resident_head_reuse priorProgram initial.heap layout current later channels within
    keepAt := resident_head_keep priorProgram initial.heap layout current later channels within
    cursorAt := resident_head_cursor priorProgram initial.heap layout current later channels within
    constructorRoom := rooms.2.2.1
    ambientFits := rooms.1
    constructorCapacity := by
      change priorProgram.size + 15 +
        (constructorCode width (priorProgram.size + 15) initial.heap.size initial.heap.size
          (initial.heap.size + 4) p.query current).length < 2 ^ width
      rw [queryEnd]
      have queryRoom : p.query + 467 < 2 ^ width := pcRoom
      omega
    constructorAt := resident_head_constructor priorProgram initial.heap layout current later channels within
    scan := p.scan
    seedDone := p.seedDone
    conflict := p.conflict
    normalizerAt := resident_head_normalizer priorProgram initial.heap layout current later channels within
    fullCapacity := by dsimp only [p, placement] at pcRoom ⊢; omega
    room := rooms.2.2.2.2.2
    scanCapacity := by dsimp only [p, placement] at pcRoom ⊢; omega
    fetch := p.fetch
    headCapacity := by dsimp only [p, placement] at pcRoom ⊢; omega
    fifoDone := p.success
    bucket := p.bucket
    advance := p.advance
    ready := p.ready
    skip := p.advance
    fetchCapacity := by dsimp only [p, placement] at pcRoom ⊢; omega
    advanceCapacity := by dsimp only [p, placement] at pcRoom ⊢; omega
    bucketCapacity := by dsimp only [p, placement] at pcRoom ⊢; omega
    readyCapacity := by dsimp only [p, placement] at pcRoom ⊢; omega
    projectionEntry := p.projection
    cleanupEntry := p.cleanup
    returnPc := p.returned
    successCapacity := by dsimp only [p, placement] at pcRoom ⊢; omega
    conflictCapacity := by dsimp only [p, placement] at pcRoom ⊢; omega
    localFit := rooms.2.2.2.1
    channelsFit := rooms.2.1
    offRoom := rooms.2.2.2.2.1
    projectionCapacity := by dsimp only [p, placement] at pcRoom ⊢; omega
    cleanupCapacity := by dsimp only [p, placement] at pcRoom ⊢; omega
    resetCapacity := by dsimp only [p, placement] at pcRoom ⊢; omega
    decisionCapacity := by dsimp only [p, placement] at pcRoom ⊢; omega
    dispatchEq := by dsimp only [p, placement]
    dispatchCapacity := by dsimp only [p, placement] at pcRoom ⊢; omega
    countAt := resident_head_countAt priorProgram initial.heap layout current later channels within
    allocateAt := resident_head_allocateAt priorProgram initial.heap layout current later channels within
    headersAt := resident_head_headersAt priorProgram initial.heap layout current later channels within
    endpointAt := resident_head_endpointAt priorProgram initial.heap layout current later channels within
    saveAt := resident_head_saveAt priorProgram initial.heap layout current later channels within
    indexSaveAt := resident_head_indexSaveAt priorProgram initial.heap layout current later channels within
    indexAt := resident_head_indexAt priorProgram initial.heap layout current later channels within
    indexRestoreAt := resident_head_indexRestoreAt priorProgram initial.heap layout current later channels within
    captureAt := resident_head_captureAt priorProgram initial.heap layout current later channels within
    setupAt := resident_head_setupAt priorProgram initial.heap layout current later channels within
    scanAt := resident_head_scanAt priorProgram initial.heap layout current later channels within
    headAt := resident_head_headAt priorProgram initial.heap layout current later channels within
    fetchAt := resident_head_fetchAt priorProgram initial.heap layout current later channels within
    advanceAt := resident_head_advanceAt priorProgram initial.heap layout current later channels within
    loopAt := resident_head_loopAt priorProgram initial.heap layout current later channels within
    readyAt := resident_head_readyAt priorProgram initial.heap layout current later channels within
    successAt := resident_head_successAt priorProgram initial.heap layout current later channels within
    conflictAt := resident_head_conflictAt priorProgram initial.heap layout current later channels within
    constantsAt := resident_head_constantsAt priorProgram initial.heap layout current later channels within
    preparationAt := resident_head_preparationAt priorProgram initial.heap layout current later channels within
    emitAt := resident_head_emitAt priorProgram initial.heap layout current later channels within
    cleanupSetup := resident_head_cleanupSetup priorProgram initial.heap layout current later channels within
    cleanupLoop := resident_head_cleanupLoop priorProgram initial.heap layout current later channels within
    dispatchAt := resident_head_dispatchAt priorProgram initial.heap layout current later channels within
    resetPrepareAt := by
      intro offset valid
      have actual := resident_tail_fetch priorProgram initial.heap layout channels within current later
        ⟨28, by rw [resident_chunks_length]; decide⟩ (by change 4 ≤ 28; decide) offset (by
          change offset < 15
          simpa only [resetPrepareCode, ForestZeroReset.code, List.length_cons, List.length_nil] using valid)
      norm_num only [residentTailCounts, List.take_succ_cons, List.take_zero, List.sum_cons,
        List.sum_nil, Nat.add_zero] at actual
      simp only [chunks, List.getElem_cons_zero, List.getElem_cons_succ] at actual
      change _ = ((resetPrepareCode width).toList.map RegisterWiden.widenInstruction).toArray[offset]? at actual
      simp only [List.getElem?_toArray, List.getElem?_map] at actual
      simpa only [p, placement, ← Nat.add_assoc, Nat.reduceAdd, Nat.add_zero] using actual
    resetLoopAt := by
      intro offset valid
      have actual := resident_tail_fetch priorProgram initial.heap layout channels within current later
        ⟨29, by rw [resident_chunks_length]; decide⟩ (by change 4 ≤ 29; decide) offset (by
          change offset < 12
          simpa only [resetPrepareCode, ForestZeroReset.code, List.length_cons, List.length_nil] using valid)
      norm_num only [residentTailCounts, List.take_succ_cons, List.take_zero, List.sum_cons,
        List.sum_nil, Nat.add_zero] at actual
      simp only [chunks, List.getElem_cons_zero, List.getElem_cons_succ] at actual
      change _ = ((ForestZeroReset.code width (p.returned + 15)).map RegisterWiden.widenInstruction).toArray[offset]? at actual
      simp only [List.getElem?_toArray, List.getElem?_map] at actual
      simpa only [p, placement, ← Nat.add_assoc, Nat.reduceAdd, Nat.add_zero] using actual
    decisionAt := by
      have actual := resident_tail_fetch priorProgram initial.heap layout channels within current later
        ⟨30, by rw [resident_chunks_length]; decide⟩ (by change 4 ≤ 30; decide) 0 (by change 0 < 1; decide)
      norm_num only [residentTailCounts, List.take_succ_cons, List.take_zero, List.sum_cons,
        List.sum_nil, Nat.add_zero] at actual
      simp only [chunks, List.getElem_cons_zero, List.getElem_cons_succ] at actual
      change _ = some (Instruction.pop 4) at actual
      simpa only [p, placement, ← Nat.add_assoc, Nat.reduceAdd, Nat.add_zero] using actual }
end Controller.Cost.ForestZeroSourcePlan


namespace Controller.Cost.ForestZeroSourcePlan
open Controller.CNF
open Controller.Cost Controller.Cost.ForestZeroResident Controller.Cost.ForestZeroDictionary
open Controller.Cost.ForestZeroCompile Controller.Cost.ForestZeroEmit Controller.Cost.ForestZeroAdmissibleCaller

/-- Restored source readiness instantiates the complete resident query plan
in the original, once-formed program. No kernel code or query metadata is
supplied by the per-occurrence execution callback. -/
def resident_ready_plan (priorProgram : Program width 8) (sourceHeap : Array (Word width))
    (layout : Layout ambient sourceHeap.size) (initial : State width 8)
    (current : List (List (Reference ambient))) (later : List (List (List (Reference ambient))))
    (channels sourceEnd nodes : Nat) (within : channels ≤ ambient) (callerRest : List (Word width))
    (ready : QueryReady (ambient := ambient) sourceHeap layout.tableBase layout.inverseBase
      priorProgram.size callerRest initial)
    (stored : ∀ reference ∈ current.flatten, StoredReference sourceHeap channels sourceEnd reference)
    (beforeTable : sourceEnd ≤ layout.tableBase) (beforeInverse : sourceEnd ≤ layout.inverseBase)
    (sourceBound : sourceEnd ≤ sourceHeap.size) (headerRoom : 1 < sourceEnd)
    (channelsCell : sourceHeap[0]? = some (word width channels))
    (nodesCell : sourceHeap[1]? = some (word width nodes))
    (ambientEq : ambient = channels + nodes) (adjacent : layout.inverseBase = layout.tableBase + ambient)
    (endpoint : sourceHeap.size = layout.inverseBase + ambient)
    (grammar : Controller.Horn.DualHorn (ofClauses (ForestZeroAssembly.originalRows (reservedReferences current))))
    (programRoom : (residentProgram priorProgram sourceHeap layout channels within (current :: later)).size < 2 ^ width)
    (wordRoom : sourceHeap.size + 2 * ambient + 14 + 5 * current.length + 15 * current.flatten.length < 2 ^ width) :
    let next := priorProgram.size + (instructions sourceHeap layout current channels within priorProgram.size 0).length
    let p := placement width sourceHeap.size priorProgram.size next current
    SourceQueryPlan (residentProgram priorProgram sourceHeap layout channels within (current :: later))
      initial (ready.current_layout layout) current sourceEnd nodes priorProgram.size callerRest within p.dispatch next := by
  intro next p
  let actualLayout := ready.current_layout layout
  have sameProgram := resident_program_rebase priorProgram sourceHeap initial.heap layout actualLayout
    (current :: later) channels within ready.heapSize.symm
  have sameInstructions := resident_instructions_rebase sourceHeap initial.heap layout actualLayout
    current channels within priorProgram.size 0 ready.heapSize.symm
  have sameNext : next = priorProgram.size +
      (instructions initial.heap actualLayout current channels within priorProgram.size 0).length :=
    congrArg (fun instructions => priorProgram.size + instructions.length) sameInstructions
  have actualStored : ∀ reference ∈ current.flatten,
      StoredReference initial.heap channels sourceEnd reference := by
    intro reference member
    exact ready.stored_reference beforeTable (stored reference member)
  have channelFrame := ready.sourceFrame.2.2 0
    (lt_of_lt_of_le (by omega : 0 < sourceEnd) beforeTable)
  have nodeFrame := ready.sourceFrame.2.2 1
    (lt_of_lt_of_le headerRoom beforeTable)
  have actualPlan := resident_head_plan priorProgram initial actualLayout current later channels sourceEnd nodes
    within callerRest actualStored beforeTable beforeInverse
    (by rw [ready.heapSize]; exact sourceBound) headerRoom
    (channelFrame.trans channelsCell) (nodeFrame.trans nodesCell) ambientEq adjacent
    (by change initial.heap.size = layout.inverseBase + ambient; exact ready.heapSize.trans endpoint) grammar
    (by rw [← sameProgram]; exact programRoom)
    (by rw [ready.heapSize]; exact wordRoom)
  dsimp only at actualPlan
  rw [← sameProgram, ← sameNext] at actualPlan
  simpa only [p, placement, ready.heapSize] using actualPlan

end Controller.Cost.ForestZeroSourcePlan


namespace Controller.Cost.ForestZeroSourcePlan
open Controller.Decoder Controller.Decoder.DAG Controller.CNF
open Controller.Cost Controller.Cost.ForestIndexedOperands Controller.Cost.ForestZeroSource
open Controller.Cost.ForestZeroCompile Controller.Cost.ForestZeroDictionary Controller.Cost.ForestZeroInitialize
open Controller.Cost.ForestZeroEmit Controller.Cost.ForestZeroUnits Controller.Cost.ForestZeroRows
open Controller.Cost.ForestZeroAdmissibleCaller Controller.Cost.ForestZeroReferenceCone
variable {width : Nat}

/-- The target is a positive unit in the original source grammar; it does not
require an unrestricted auxiliary SAT backend. -/
theorem forced_query_dualHorn (graph : DAG n) (guarded : graph.Guarded)
    (rows : List Row) (rawRoots : List Nat) (rowsMatch : RowsMatch graph rows)
    (position : Fin graph.roots.length) (target : Fin n) :
    Controller.Horn.DualHorn (ofClauses (ForestZeroAssembly.originalRows
      (reservedReferences (forcedQuery (width := width) graph rows rawRoots rowsMatch position target)))) := by
  have original := query_dualHorn graph guarded rows rawRoots rowsMatch position
  intro clause present
  have projection : ForestZeroAssembly.originalRows
      (reservedReferences (forcedQuery (width := width) graph rows rawRoots rowsMatch position target)) =
      ForestZeroAssembly.originalRows (query graph rows rawRoots rowsMatch position) ++
        [[(sourceIndex graph (.inl target), true)]] ++ [[]] := by
    calc
      _ = ForestZeroAssembly.originalRows
          (forcedQuery (width := width) graph rows rawRoots rowsMatch position target) ++ [[]] := by
        simp only [reservedReferences, ForestZeroAssembly.originalRows, List.map_append,
          List.map_cons, List.map_nil]
      _ = _ := by rw [forced_query_original_rows]
  change clause ∈ (ForestZeroAssembly.originalRows
    (reservedReferences (forcedQuery (width := width) graph rows rawRoots rowsMatch position target))).toArray at present
  rw [List.mem_toArray, projection] at present
  rcases List.mem_append.mp present with oldOrTarget | empty
  · rcases List.mem_append.mp oldOrTarget with old | targetClause
    · apply original clause
      change clause ∈ (ForestZeroAssembly.originalRows
        (reservedReferences (query graph rows rawRoots rowsMatch position))).toArray
      simp only [List.mem_toArray, reservedReferences, ForestZeroAssembly.originalRows,
        List.map_append, List.map_cons, List.map_nil, List.mem_append]
      exact Or.inl old
    · obtain rfl := List.mem_singleton.mp targetClause
      exact Controller.Horn.dualHornClause_singleton _
  · obtain rfl := List.mem_singleton.mp empty
    exact Controller.Horn.dualHornClause_positive (by intro literal impossible; cases impossible)

/-- The original packet, actual loaded target trailer, and once-reserved
regions form the complete runtime query plan for this declared occurrence.
Every original source correspondence and header is derived here. -/
def forced_query_ready_plan (graph : DAG n) (guarded : graph.Guarded)
    (rows : List Row) (rawRoots : List Nat) (rowsMatch : RowsMatch graph rows)
    (rootsMatch : RootsMatch graph rawRoots) (position : Fin graph.roots.length) (target : Fin n)
    (priorProgram : Program width 8) (initial : State width 8)
    (later : List (List (List (Reference (n + graph.nodeCount))))) (callerRest : List (Word width))
    (ready : QueryReady (ambient := n + graph.nodeCount)
      (reserveHeap ((packetHeap width n rows rawRoots).push (word width target.val)) (n + graph.nodeCount))
      (reservedLayout ((packetHeap width n rows rawRoots).push (word width target.val)) (n + graph.nodeCount)).tableBase
      (reservedLayout ((packetHeap width n rows rawRoots).push (word width target.val)) (n + graph.nodeCount)).inverseBase
      priorProgram.size callerRest initial)
    (programRoom :
      (residentProgram priorProgram
        (reserveHeap ((packetHeap width n rows rawRoots).push (word width target.val)) (n + graph.nodeCount))
        (reservedLayout ((packetHeap width n rows rawRoots).push (word width target.val)) (n + graph.nodeCount))
        n (Nat.le_add_right _ _)
        (forcedQuery (width := width) graph rows rawRoots rowsMatch position target :: later)).size < 2 ^ width)
    (wordRoom :
      (reserveHeap ((packetHeap width n rows rawRoots).push (word width target.val)) (n + graph.nodeCount)).size +
        2 * (n + graph.nodeCount) + 14 +
        5 * (forcedQuery (width := width) graph rows rawRoots rowsMatch position target).length +
        15 * (forcedQuery (width := width) graph rows rawRoots rowsMatch position target).flatten.length < 2 ^ width) :
    let loaded := (packetHeap width n rows rawRoots).push (word width target.val)
    let sourceHeap := reserveHeap loaded (n + graph.nodeCount)
    let layout := reservedLayout loaded (n + graph.nodeCount)
    let refs := forcedQuery (width := width) graph rows rawRoots rowsMatch position target
    let next := priorProgram.size +
      (ForestZeroResident.instructions sourceHeap layout refs n (Nat.le_add_right _ _) priorProgram.size 0).length
    let p := ForestZeroResident.placement width sourceHeap.size priorProgram.size next refs
    SourceQueryPlan (residentProgram priorProgram sourceHeap layout n (Nat.le_add_right _ _) (refs :: later))
      initial (ready.current_layout layout) refs loaded.size graph.nodeCount priorProgram.size callerRest
      (Nat.le_add_right _ _) p.dispatch next := by
  intro loaded sourceHeap layout refs next p
  have headerSize : 1 < (packetHeap width n rows rawRoots).size := by rw [packetHeap_size]; omega
  have stored : ∀ reference ∈ refs.flatten, StoredReference sourceHeap n loaded.size reference := by
    intro reference member
    obtain ⟨clause, clauseMember, referenceMember⟩ := List.mem_flatten.mp member
    have actual := forced_query_stored graph rows rawRoots rowsMatch rootsMatch position target
      clause clauseMember reference referenceMember
    have loadedStored : StoredReference loaded n loaded.size reference := by
      simpa only [loaded, Array.size_push] using actual
    refine ⟨?_, loadedStored.slotBound, loadedStored.headerBound, ?_, ?_, loadedStored.coordinateEq⟩
    · dsimp only [sourceHeap]; rw [reserveHeap_size]; have := actual.sourceBound; omega
    · exact (reserve_source loaded _ reference.slot loadedStored.slotBound).trans loadedStored.slotWord
    · exact (reserve_source loaded _ 0 loadedStored.headerBound).trans loadedStored.channelWord
  have pushedPrefix : ∀ address, address < (packetHeap width n rows rawRoots).size →
      loaded[address]? = (packetHeap width n rows rawRoots)[address]? := by
    intro address bound
    simp only [loaded, Array.getElem?_push, ite_eq_right (show address ≠ (packetHeap width n rows rawRoots).size by omega)]
  have channelWord : sourceHeap[0]? = some (word width n) :=
    (reserve_source loaded _ 0 (by dsimp only [loaded]; rw [Array.size_push]; omega)).trans
      ((pushedPrefix 0 (by omega)).trans
        (packet_header width n rows rawRoots))
  have nodeWord : sourceHeap[1]? = some (word width graph.nodeCount) :=
    (reserve_source loaded _ 1 (by dsimp only [loaded]; rw [Array.size_push]; omega)).trans
      ((pushedPrefix 1 headerSize).trans
        (by simpa only [rowsMatch.length_eq] using (packetHeader width n rows rawRoots).nodeWord))
  exact resident_ready_plan priorProgram sourceHeap layout initial refs later n loaded.size graph.nodeCount
    (Nat.le_add_right _ _) callerRest ready stored
    (by rfl) (by dsimp only [layout, reservedLayout]; omega)
    (by dsimp only [sourceHeap]; rw [reserveHeap_size]; omega)
    (by dsimp only [loaded]; rw [Array.size_push]; omega) channelWord nodeWord rfl
    (by rfl) (by dsimp only [sourceHeap, layout, reservedLayout]; rw [reserveHeap_size]; omega)
    (forced_query_dualHorn graph guarded rows rawRoots rowsMatch position target) programRoom wordRoom

end Controller.Cost.ForestZeroSourcePlan


namespace Controller.Cost.ForestZeroSourcePlan
open Controller.CNF
open Controller.Cost Controller.Cost.ForestZeroResident Controller.Cost.ForestZeroDictionary
open Controller.Cost.ForestZeroCompile Controller.Cost.ForestZeroEmit Controller.Cost.ForestZeroAdmissibleCaller

theorem resident_ready_execution (priorProgram : Program width 8) (sourceHeap : Array (Word width))
    (layout : Layout ambient sourceHeap.size) (initial : State width 8)
    (current : List (List (Reference ambient))) (later : List (List (List (Reference ambient))))
    (channels sourceEnd nodes : Nat) (within : channels ≤ ambient) (callerRest : List (Word width))
    (ready : QueryReady (ambient := ambient) sourceHeap layout.tableBase layout.inverseBase
      priorProgram.size callerRest initial)
    (stored : ∀ reference ∈ current.flatten, StoredReference sourceHeap channels sourceEnd reference)
    (beforeTable : sourceEnd ≤ layout.tableBase) (beforeInverse : sourceEnd ≤ layout.inverseBase)
    (sourceBound : sourceEnd ≤ sourceHeap.size) (headerRoom : 1 < sourceEnd)
    (channelsCell : sourceHeap[0]? = some (word width channels))
    (nodesCell : sourceHeap[1]? = some (word width nodes))
    (ambientEq : ambient = channels + nodes) (adjacent : layout.inverseBase = layout.tableBase + ambient)
    (endpoint : sourceHeap.size = layout.inverseBase + ambient)
    (grammar : Controller.Horn.DualHorn (ofClauses (ForestZeroAssembly.originalRows (reservedReferences current))))
    (programRoom : (residentProgram priorProgram sourceHeap layout channels within (current :: later)).size < 2 ^ width)
    (wordRoom : sourceHeap.size + 2 * ambient + 14 + 5 * current.length + 15 * current.flatten.length < 2 ^ width) :
    let next := priorProgram.size + (instructions sourceHeap layout current channels within priorProgram.size 0).length
    let p := placement width sourceHeap.size priorProgram.size next current
    ∃ answer : Bool, ∃ final ticks peak,
      Execution (residentProgram priorProgram sourceHeap layout channels within (current :: later))
        initial final ticks peak ∧
      final.pc = word width p.dispatch ∧ final.halted = false ∧
      final.reg 4 = word width (if answer then 1 else 0) ∧
      ticks ≤ 150 * current.length + 387 * current.flatten.length + 441 +
        (if answer then 13 * channels else 0) ∧
      peak ≤ initial.liveWords + 5 * current.length + 15 * current.flatten.length + channels + 20 ∧
      final.liveWords ≤ initial.liveWords + 1 + (if answer then channels else 0) ∧
      (answer = true ↔ Satisfiable (constructorFormula initial.heap (ready.current_layout layout)
        (empty ambient) (empty_coherent ambient) current channels within)) ∧
      (answer = true → QueryChannelWitness initial.heap (ready.current_layout layout)
        current channels within final.output) ∧
      (answer = false → QueryReady (ambient := ambient) sourceHeap layout.tableBase layout.inverseBase
        next callerRest (ForestZeroRootLoop.dispatchState final p.dispatch next false)) ∧
      p.dispatch + 2 < 2 ^ width ∧
      (∀ phase : Fin 2,
        (residentProgram priorProgram sourceHeap layout channels within (current :: later))[p.dispatch + phase.val]? =
          (ForestZeroRootLoop.dispatchCode width next)[phase.val]?) := by
  intro next p
  have plan := resident_ready_plan priorProgram sourceHeap layout initial current later channels sourceEnd nodes
    within callerRest ready stored beforeTable beforeInverse sourceBound headerRoom channelsCell nodesCell
    ambientEq adjacent endpoint grammar programRoom wordRoom
  exact SourceQueryPlan.execute
    (residentProgram priorProgram sourceHeap layout channels within (current :: later)) initial sourceHeap
    (ready.current_layout layout) current sourceEnd nodes priorProgram.size callerRest within p.dispatch next plan ready

end Controller.Cost.ForestZeroSourcePlan


namespace Controller.Cost.ForestZeroSourcePlan
open Controller.Cost Controller.Cost.ForestZeroDictionary Controller.Cost.ForestZeroResident
open Controller.Cost.ForestZeroEmit

/-- The actual pushed resident program before a declared occurrence. This
retains repeated roots and includes no artificial exhausted block between
occurrences. -/
def residentPrefix (priorProgram : Program width 8) (heap : Array (Word width))
    (layout : Layout ambient heap.size) (channels : Nat) (within : channels ≤ ambient) :
    List (List (List (Reference ambient))) → Program width 8
  | [] => priorProgram
  | current :: later =>
      let next := priorProgram.size + (instructions heap layout current channels within priorProgram.size 0).length
      residentPrefix (materialize priorProgram (instructions heap layout current channels within priorProgram.size next))
        heap layout channels within later

/-- Consecutive actual array-push traversals form the same resident array as
one traversal of their concatenated instruction lists. -/
theorem materialize_append (priorProgram : Program width 8)
    (first second : List (Instruction width 8)) :
    materialize priorProgram (first ++ second) = materialize (materialize priorProgram first) second := by
  apply Array.toList_inj.mp
  rw [materialize_contents, materialize_contents, materialize_contents]
  exact (List.append_assoc _ _ _).symm

/-- The full once-formed program is the exact suffix resident program at each
occurrence's pushed prefix, not a per-query replacement program. -/
theorem resident_prefix_split (priorProgram : Program width 8) (heap : Array (Word width))
    (layout : Layout ambient heap.size) (channels : Nat) (within : channels ≤ ambient)
    (before after : List (List (List (Reference ambient)))) :
    residentProgram priorProgram heap layout channels within (before ++ after) =
      residentProgram (residentPrefix priorProgram heap layout channels within before)
        heap layout channels within after := by
  induction before generalizing priorProgram with
  | nil => rfl
  | cons current earlier ih =>
    let next := priorProgram.size + (instructions heap layout current channels within priorProgram.size 0).length
    let pushed := materialize priorProgram (instructions heap layout current channels within priorProgram.size next)
    have nextEq : pushed.size = next := by
      dsimp only [pushed]
      rw [materialize_size, resident_length_next heap layout channels within current priorProgram.size next 0]
    have first : residentProgram priorProgram heap layout channels within (current :: (earlier ++ after)) =
        residentProgram pushed heap layout channels within (earlier ++ after) := by
      unfold residentProgram
      simp only [residentInstructions]
      rw [materialize_append]
      rw [nextEq]
    rw [List.cons_append, first, ih]
    rfl

/-- Physical static entries are indexed by declared occurrences, including
identical root labels. The empty continuation is the actual exhausted block. -/
def occurrenceEntry (priorProgram : Program width 8) (heap : Array (Word width))
    (layout : Layout ambient heap.size) (channels : Nat) (within : channels ≤ ambient)
    (queries : List (List (List (Reference ambient)))) (position : Nat) : Nat :=
  (residentPrefix priorProgram heap layout channels within (queries.take position)).size

/-- The occurrence's dispatch follows all of its actual resident instructions,
with its two physical branch/halt instructions at the end. -/
def occurrenceDispatch (priorProgram : Program width 8) (heap : Array (Word width))
    (layout : Layout ambient heap.size) (channels : Nat) (within : channels ≤ ambient)
    (queries : List (List (List (Reference ambient)))) (position : Fin queries.length) : Nat :=
  let before := residentPrefix priorProgram heap layout channels within (queries.take position.val)
  let current := queries[position]
  let next := before.size + (instructions heap layout current channels within before.size 0).length
  (placement width heap.size before.size next current).dispatch

end Controller.Cost.ForestZeroSourcePlan


namespace Controller.Cost.ForestZeroSourcePlan
open Controller.Cost Controller.Cost.ForestZeroResident Controller.Cost.ForestZeroDictionary
open Controller.Cost.ForestZeroEmit Controller.Cost.ForestZeroAdmissibleCaller

/-- The position at the head of a declared suffix is its original occurrence
number. Equal root labels do not identify these static positions. -/
theorem occurrence_suffix_index {count : Nat} (position : Fin count) (tail : List (Fin count))
    (suffix : ForestZeroRootLoop.TailOf (List.finRange count) (position :: tail)) :
    count - (position :: tail).length = position.val := by
  obtain ⟨before, same⟩ := suffix
  have lengths := congrArg List.length same
  simp only [List.length_finRange, List.length_append, List.length_cons] at lengths
  have bound : before.length < (List.finRange count).length := by
    rw [List.length_finRange]
    omega
  have headEq : (List.finRange count)[before.length]? = some position := by
    rw [same, List.getElem?_append_right (Nat.le_refl before.length)]
    simp only [Nat.sub_self, List.getElem?_cons_zero]
  rw [List.getElem?_eq_getElem bound] at headEq
  have actual := congrArg Fin.val (Option.some.inj headEq)
  simp only [List.getElem_finRange, Fin.val_cast] at actual
  simp only [List.length_cons]
  omega

/-- A mapped suffix is the original query stream after exactly the declared
prefix; no deduplication or separately supplied list is involved. -/
theorem occurrence_suffix_queries (queries : List (List (List (Reference ambient))))
    (position : Fin queries.length) (tail : List (Fin queries.length))
    (suffix : ForestZeroRootLoop.TailOf (List.finRange queries.length) (position :: tail)) :
    queries.drop position.val = queries[position] :: tail.map (fun index => queries[index]) := by
  obtain ⟨before, same⟩ := suffix
  have indexEq := occurrence_suffix_index position tail ⟨before, same⟩
  have lengths := congrArg List.length same
  simp only [List.length_finRange, List.length_append, List.length_cons] at lengths
  have beforeEq : before.length = position.val := by
    simp only [List.length_cons] at indexEq
    omega
  have mapped := congrArg (List.map (fun index : Fin queries.length => queries[index])) same
  have allMapped : (List.finRange queries.length).map (fun index => queries[index]) = queries := by
    simpa only [Fin.getElem_fin] using List.map_getElem_finRange queries
  rw [allMapped] at mapped
  have dropped := congrArg (fun stream => stream.drop before.length) mapped
  simp only [List.map_append, List.map_cons] at dropped
  have mapLength : before.length = (before.map (fun index : Fin queries.length => queries[index])).length := by
    rw [List.length_map]
  rw [mapLength, List.drop_append_length] at dropped
  simpa only [List.length_map, beforeEq] using dropped

/-- The next continuation is the actual end of this occurrence's pushed
instruction list, including when the remaining stream is empty. -/
theorem occurrence_entry_successor (priorProgram : Program width 8) (heap : Array (Word width))
    (layout : Layout ambient heap.size) (channels : Nat) (within : channels ≤ ambient)
    (queries : List (List (List (Reference ambient)))) (position : Fin queries.length) :
    occurrenceEntry priorProgram heap layout channels within queries (position.val + 1) =
      occurrenceEntry priorProgram heap layout channels within queries position.val +
        (instructions heap layout queries[position] channels within
          (occurrenceEntry priorProgram heap layout channels within queries position.val) 0).length := by
  unfold occurrenceEntry
  rw [List.take_succ_eq_append_getElem position.isLt]
  have prefixAppend : ∀ (before after : List (List (List (Reference ambient)))) (prior : Program width 8),
      residentPrefix prior heap layout channels within (before ++ after) =
        residentPrefix (residentPrefix prior heap layout channels within before) heap layout channels within after := by
    intro before after prior
    induction before generalizing prior with
    | nil => rfl
    | cons head rest ih =>
      simp only [List.cons_append, residentPrefix]
      exact ih _
  rw [prefixAppend]
  simp only [residentPrefix]
  rw [materialize_size]
  let earlier := residentPrefix priorProgram heap layout channels within (queries.take position.val)
  have relocated := resident_length_next heap layout channels within queries[position.val] earlier.size
    (earlier.size + (instructions heap layout queries[position.val] channels within earlier.size 0).length) 0
  simpa only [earlier, Fin.getElem_fin] using congrArg (fun length => earlier.size + length) relocated

end Controller.Cost.ForestZeroSourcePlan


namespace Controller.Cost.ForestZeroSourcePlan
open Controller.CNF
open Controller.Cost Controller.Cost.ForestZeroResident Controller.Cost.ForestZeroDictionary
open Controller.Cost.ForestZeroEmit Controller.Cost.ForestZeroAdmissibleCaller

def occurrenceResume (priorProgram : Program width 8) (heap : Array (Word width))
    (layout : Layout ambient heap.size) (channels : Nat) (within : channels ≤ ambient)
    (queries : List (List (List (Reference ambient)))) (remaining : List (Fin queries.length)) : Nat :=
  occurrenceEntry priorProgram heap layout channels within queries (queries.length - remaining.length)

/-- Each physical plan is produced in the same resident array at its declared
occurrence. The suffix proof determines the next entry from original list
positions; no query execution or separately chosen code array is supplied. -/
def resident_occurrence_plan (priorProgram : Program width 8) (sourceHeap : Array (Word width))
    (layout : Layout ambient sourceHeap.size)
    (queries : List (List (List (Reference ambient)))) (channels sourceEnd nodes : Nat)
    (within : channels ≤ ambient) (callerRest : List (Word width))
    (stored : ∀ position : Fin queries.length, ∀ reference ∈ queries[position].flatten,
      StoredReference sourceHeap channels sourceEnd reference)
    (beforeTable : sourceEnd ≤ layout.tableBase) (beforeInverse : sourceEnd ≤ layout.inverseBase)
    (sourceBound : sourceEnd ≤ sourceHeap.size) (headerRoom : 1 < sourceEnd)
    (channelsCell : sourceHeap[0]? = some (word width channels))
    (nodesCell : sourceHeap[1]? = some (word width nodes))
    (ambientEq : ambient = channels + nodes) (adjacent : layout.inverseBase = layout.tableBase + ambient)
    (endpoint : sourceHeap.size = layout.inverseBase + ambient)
    (grammar : ∀ position : Fin queries.length,
      Controller.Horn.DualHorn (ofClauses (ForestZeroAssembly.originalRows (reservedReferences queries[position]))))
    (programRoom : (residentProgram priorProgram sourceHeap layout channels within queries).size < 2 ^ width)
    (wordRoom : ∀ position : Fin queries.length, sourceHeap.size + 2 * ambient + 14 +
      5 * queries[position].length + 15 * queries[position].flatten.length < 2 ^ width)
    (position : Fin queries.length) (tail : List (Fin queries.length)) (initial : State width 8)
    (suffix : ForestZeroRootLoop.TailOf (List.finRange queries.length) (position :: tail))
    (ready : QueryReady (ambient := ambient) sourceHeap layout.tableBase layout.inverseBase
      (occurrenceResume priorProgram sourceHeap layout channels within queries (position :: tail)) callerRest initial) :
    SourceQueryPlan (residentProgram priorProgram sourceHeap layout channels within queries)
      initial (ready.current_layout layout) queries[position] sourceEnd nodes
      (occurrenceResume priorProgram sourceHeap layout channels within queries (position :: tail)) callerRest within
      (occurrenceDispatch priorProgram sourceHeap layout channels within queries position)
      (occurrenceResume priorProgram sourceHeap layout channels within queries tail) := by
  let before := residentPrefix priorProgram sourceHeap layout channels within (queries.take position.val)
  let later := queries.drop (position.val + 1)
  have indexEq := occurrence_suffix_index position tail suffix
  have nextIndex : queries.length - tail.length = position.val + 1 := by
    have suffixLength : (position :: tail).length ≤ queries.length := by
      obtain ⟨earlier, same⟩ := suffix
      have lengths := congrArg List.length same
      simp only [List.length_finRange, List.length_append] at lengths
      omega
    simp only [List.length_cons] at indexEq suffixLength
    omega
  have entryEq : occurrenceResume priorProgram sourceHeap layout channels within queries (position :: tail) =
      before.size := by
    simp only [occurrenceResume, indexEq, occurrenceEntry, before]
  have readyAt : QueryReady (ambient := ambient) sourceHeap layout.tableBase layout.inverseBase
      before.size callerRest initial := by
    simpa only [entryEq] using ready
  have sameProgram : residentProgram priorProgram sourceHeap layout channels within queries =
      residentProgram before sourceHeap layout channels within (queries[position] :: later) := by
    have split := resident_prefix_split priorProgram sourceHeap layout channels within
      (queries.take position.val) (queries.drop position.val)
    rw [List.take_append_drop] at split
    rw [List.drop_eq_getElem_cons position.isLt] at split
    simpa only [Fin.getElem_fin, before, later] using split
  have nextEq : occurrenceResume priorProgram sourceHeap layout channels within queries tail =
      before.size + (instructions sourceHeap layout queries[position] channels within before.size 0).length := by
    simp only [occurrenceResume, nextIndex]
    exact occurrence_entry_successor priorProgram sourceHeap layout channels within queries position
  have produced := resident_ready_plan before sourceHeap layout initial queries[position] later channels sourceEnd nodes
    within callerRest readyAt (stored position) beforeTable beforeInverse sourceBound headerRoom
    channelsCell nodesCell ambientEq adjacent endpoint (grammar position)
    (by rw [← sameProgram]; exact programRoom) (wordRoom position)
  dsimp only at produced
  rw [← sameProgram] at produced
  simpa only [entryEq, nextEq, occurrenceDispatch, before] using produced

/-- The existing physical first-success contract is discharged by generated
plans rather than a caller-supplied array of SourceQueryPlan certificates. -/
theorem resident_occurrence_contract (priorProgram : Program width 8) (sourceHeap : Array (Word width))
    (layout : Layout ambient sourceHeap.size)
    (queries : List (List (List (Reference ambient)))) (channels sourceEnd nodes : Nat)
    (within : channels ≤ ambient) (callerRest : List (Word width))
    (stored : ∀ position : Fin queries.length, ∀ reference ∈ queries[position].flatten,
      StoredReference sourceHeap channels sourceEnd reference)
    (beforeTable : sourceEnd ≤ layout.tableBase) (beforeInverse : sourceEnd ≤ layout.inverseBase)
    (sourceBound : sourceEnd ≤ sourceHeap.size) (headerRoom : 1 < sourceEnd)
    (channelsCell : sourceHeap[0]? = some (word width channels))
    (nodesCell : sourceHeap[1]? = some (word width nodes))
    (ambientEq : ambient = channels + nodes) (adjacent : layout.inverseBase = layout.tableBase + ambient)
    (endpoint : sourceHeap.size = layout.inverseBase + ambient)
    (grammar : ∀ position : Fin queries.length,
      Controller.Horn.DualHorn (ofClauses (ForestZeroAssembly.originalRows (reservedReferences queries[position]))))
    (programRoom : (residentProgram priorProgram sourceHeap layout channels within queries).size < 2 ^ width)
    (wordRoom : ∀ position : Fin queries.length, sourceHeap.size + 2 * ambient + 14 +
      5 * queries[position].length + 15 * queries[position].flatten.length < 2 ^ width)
    (scratch : Nat) (scratchBound : ∀ position : Fin queries.length,
      5 * queries[position].length + 15 * queries[position].flatten.length + channels + 20 ≤ scratch) :
    ForestZeroRootLoop.QueryContract
      (residentProgram priorProgram sourceHeap layout channels within queries) (List.finRange queries.length)
      (fun remaining state => QueryReady (ambient := ambient) sourceHeap layout.tableBase layout.inverseBase
        (occurrenceResume priorProgram sourceHeap layout channels within queries remaining) callerRest state)
      (fun position => Satisfiable (constructorFormula sourceHeap layout
        (ForestZeroCompile.empty ambient) (ForestZeroCompile.empty_coherent ambient) queries[position] channels within))
      (fun position output => QueryChannelWitness sourceHeap layout queries[position] channels within output)
      (occurrenceResume priorProgram sourceHeap layout channels within queries)
      (occurrenceDispatch priorProgram sourceHeap layout channels within queries)
      (fun position => 150 * queries[position].length + 387 * queries[position].flatten.length + 441)
      scratch (13 * channels) channels := by
  apply occurrence_query_contract _ sourceHeap layout queries sourceEnd nodes callerRest within
    _ _ scratch scratchBound
  intro position tail state suffix ready
  exact resident_occurrence_plan priorProgram sourceHeap layout queries channels sourceEnd nodes within callerRest
    stored beforeTable beforeInverse sourceBound headerRoom channelsCell nodesCell ambientEq adjacent endpoint
    grammar programRoom wordRoom position tail state suffix ready

end Controller.Cost.ForestZeroSourcePlan


namespace Controller.Cost.ForestZeroSourcePlan
open Controller.Cost Controller.Cost.ForestZeroDictionary Controller.Cost.ForestZeroResident
open Controller.Cost.ForestZeroEmit

/-- The physical empty continuation is the exhausted block appended after
all declared occurrences in the same resident program. -/
theorem resident_empty_program (priorProgram : Program width 8) (heap : Array (Word width))
    (layout : Layout ambient heap.size) (channels : Nat) (within : channels ≤ ambient)
    (queries : List (List (List (Reference ambient)))) :
    residentProgram priorProgram heap layout channels within queries =
      materialize (residentPrefix priorProgram heap layout channels within queries)
        (ForestZeroRootLoop.exhaustedCode width).toList := by
  have split := resident_prefix_split priorProgram heap layout channels within queries []
  simp only [List.append_nil] at split
  rw [split]
  unfold residentProgram
  simp only [residentInstructions]

theorem resident_empty_size (priorProgram : Program width 8) (heap : Array (Word width))
    (layout : Layout ambient heap.size) (channels : Nat) (within : channels ≤ ambient)
    (queries : List (List (List (Reference ambient)))) :
    (residentProgram priorProgram heap layout channels within queries).size =
      occurrenceResume priorProgram heap layout channels within queries [] + 2 := by
  rw [resident_empty_program, materialize_size]
  simp only [occurrenceResume, List.length_nil, Nat.sub_zero, occurrenceEntry, List.take_length]
  congr 1

theorem resident_empty_fetch (priorProgram : Program width 8) (heap : Array (Word width))
    (layout : Layout ambient heap.size) (channels : Nat) (within : channels ≤ ambient)
    (queries : List (List (List (Reference ambient)))) (phase : Fin 2) :
    (residentProgram priorProgram heap layout channels within queries)[
      occurrenceResume priorProgram heap layout channels within queries [] + phase.val]? =
      (ForestZeroRootLoop.exhaustedCode width)[phase.val]? := by
  rw [resident_empty_program]
  have actual := materialize_block
    (residentPrefix priorProgram heap layout channels within queries) []
    (ForestZeroRootLoop.exhaustedCode width).toList [] phase.val
    (by change phase.val < 2; exact phase.isLt)
  simpa only [occurrenceResume, occurrenceEntry, List.length_nil, Nat.sub_zero, List.take_length,
    List.nil_append, List.append_nil, Nat.add_zero, Array.getElem?_toList] using actual

end Controller.Cost.ForestZeroSourcePlan


namespace Controller.Cost.ForestZeroSourcePlan
open Controller.CNF
open Controller.Cost Controller.Cost.ForestZeroResident Controller.Cost.ForestZeroDictionary
open Controller.Cost.ForestZeroEmit Controller.Cost.ForestZeroAdmissibleCaller

/-- The complete same-program first-success trace consumes only generated
resident plans. Its per-query source correspondences are subsequently
instantiated by the original packet producer. -/
theorem resident_first_success_execution (priorProgram : Program width 8) (sourceHeap : Array (Word width))
    (layout : Layout ambient sourceHeap.size)
    (queries : List (List (List (Reference ambient)))) (channels sourceEnd nodes : Nat)
    (within : channels ≤ ambient) (callerRest : List (Word width))
    (stored : ∀ position : Fin queries.length, ∀ reference ∈ queries[position].flatten,
      StoredReference sourceHeap channels sourceEnd reference)
    (beforeTable : sourceEnd ≤ layout.tableBase) (beforeInverse : sourceEnd ≤ layout.inverseBase)
    (sourceBound : sourceEnd ≤ sourceHeap.size) (headerRoom : 1 < sourceEnd)
    (channelsCell : sourceHeap[0]? = some (word width channels))
    (nodesCell : sourceHeap[1]? = some (word width nodes))
    (ambientEq : ambient = channels + nodes) (adjacent : layout.inverseBase = layout.tableBase + ambient)
    (endpoint : sourceHeap.size = layout.inverseBase + ambient)
    (grammar : ∀ position : Fin queries.length,
      Controller.Horn.DualHorn (ofClauses (ForestZeroAssembly.originalRows (reservedReferences queries[position]))))
    (programRoom : (residentProgram priorProgram sourceHeap layout channels within queries).size < 2 ^ width)
    (wordRoom : ∀ position : Fin queries.length, sourceHeap.size + 2 * ambient + 14 +
      5 * queries[position].length + 15 * queries[position].flatten.length < 2 ^ width)
    (scratch : Nat) (scratchBound : ∀ position : Fin queries.length,
      5 * queries[position].length + 15 * queries[position].flatten.length + channels + 20 ≤ scratch)
    (initial : State width 8)
    (ready : QueryReady (ambient := ambient) sourceHeap layout.tableBase layout.inverseBase
      (occurrenceResume priorProgram sourceHeap layout channels within queries (List.finRange queries.length))
      callerRest initial) :
    ∃ answer : Bool, ∃ final ticks peak,
      Execution (residentProgram priorProgram sourceHeap layout channels within queries) initial final ticks peak ∧
      final.halted = true ∧ final.reg 4 = word width (if answer then 1 else 0) ∧
      ticks ≤ 150 * (queries.map List.length).sum +
        387 * (queries.map (fun rows => rows.flatten.length)).sum + 442 * queries.length + 13 * channels + 2 ∧
      peak ≤ initial.liveWords + scratch + queries.length + channels + 1 ∧
      (answer = true ↔ ∃ position : Fin queries.length,
        Satisfiable (constructorFormula sourceHeap layout (ForestZeroCompile.empty ambient)
          (ForestZeroCompile.empty_coherent ambient) queries[position] channels within)) ∧
      (answer = true → ∃ position : Fin queries.length,
        Satisfiable (constructorFormula sourceHeap layout (ForestZeroCompile.empty ambient)
          (ForestZeroCompile.empty_coherent ambient) queries[position] channels within) ∧
        QueryChannelWitness sourceHeap layout queries[position] channels within final.output) := by
  have emptyFits : occurrenceResume priorProgram sourceHeap layout channels within queries [] + 2 < 2 ^ width := by
    rw [← resident_empty_size]
    exact programRoom
  apply source_first_success_execution
    (residentProgram priorProgram sourceHeap layout channels within queries) sourceHeap layout queries sourceEnd nodes
    callerRest within (occurrenceResume priorProgram sourceHeap layout channels within queries)
    (occurrenceDispatch priorProgram sourceHeap layout channels within queries) scratch scratchBound
    _ emptyFits (resident_empty_fetch priorProgram sourceHeap layout channels within queries) initial ready
  intro position tail state suffix initialReady
  exact resident_occurrence_plan priorProgram sourceHeap layout queries channels sourceEnd nodes within callerRest
    stored beforeTable beforeInverse sourceBound headerRoom channelsCell nodesCell ambientEq adjacent endpoint
    grammar programRoom wordRoom position tail state suffix initialReady

end Controller.Cost.ForestZeroSourcePlan


namespace Controller.Cost.ForestZeroSourcePlan
open Controller.Decoder Controller.Decoder.DAG
open Controller.Cost Controller.Cost.ForestZeroEmit Controller.Cost.ForestZeroSource Controller.Cost.ForestIndexedOperands
open Controller.Cost.ForestZeroInitialize Controller.Cost.ForestZeroUnits Controller.Cost.ForestZeroAdmissibleCaller
variable {width : Nat}

/-- All declared query occurrences retain actual source cells from the packet
and its loaded control trailer. Repeated declared roots keep repeated clauses
and source references. -/
theorem forced_stream_stored (graph : DAG n) (rows : List Row) (rawRoots : List Nat)
    (rowsMatch : RowsMatch graph rows) (rootsMatch : RootsMatch graph rawRoots) (target : Fin n) :
    ∀ current ∈ forcedQueries (width := width) graph rows rawRoots rowsMatch target,
      ∀ reference ∈ current.flatten,
        StoredReference
          (reserveHeap ((packetHeap width n rows rawRoots).push (word width target.val)) (n + graph.nodeCount))
          n ((packetHeap width n rows rawRoots).size + 1) reference := by
  intro current member reference present
  obtain ⟨original, originalMember, same⟩ := List.mem_map.mp member
  subst current
  change original ∈ List.ofFn (query graph rows rawRoots rowsMatch) at originalMember
  obtain ⟨position, same⟩ := List.mem_ofFn.mp originalMember
  subst original
  have forcedPresent : reference ∈
      (forcedQuery (width := width) graph rows rawRoots rowsMatch position target).flatten := present
  obtain ⟨clause, clauseMember, referenceMember⟩ := List.mem_flatten.mp forcedPresent
  have actual := forced_query_stored graph rows rawRoots rowsMatch rootsMatch position target
    clause clauseMember reference referenceMember
  let loaded := (packetHeap width n rows rawRoots).push (word width target.val)
  have loadedSize : loaded.size = (packetHeap width n rows rawRoots).size + 1 := by
    simp only [loaded, Array.size_push]
  refine ⟨?_, actual.slotBound, actual.headerBound, ?_, ?_, actual.coordinateEq⟩
  · rw [reserveHeap_size, Array.size_push]
    omega
  · exact (reserve_source loaded _ reference.slot (by rw [loadedSize]; exact actual.slotBound)).trans actual.slotWord
  · exact (reserve_source loaded _ 0 (by rw [loadedSize]; exact actual.headerBound)).trans actual.channelWord

/-- The full occurrence stream's grammar follows from original guarded node
rows and its actual root/target units, without a supplied per-query certificate. -/
theorem forced_stream_dualHorn (graph : DAG n) (guarded : graph.Guarded)
    (rows : List Row) (rawRoots : List Nat) (rowsMatch : RowsMatch graph rows) (target : Fin n) :
    ∀ current ∈ forcedQueries (width := width) graph rows rawRoots rowsMatch target,
      Controller.Horn.DualHorn (Controller.CNF.ofClauses
        (ForestZeroAssembly.originalRows (reservedReferences current))) := by
  intro current member
  obtain ⟨original, originalMember, same⟩ := List.mem_map.mp member
  subst current
  change original ∈ List.ofFn (query graph rows rawRoots rowsMatch) at originalMember
  obtain ⟨position, same⟩ := List.mem_ofFn.mp originalMember
  subst original
  exact forced_query_dualHorn graph guarded rows rawRoots rowsMatch position target

end Controller.Cost.ForestZeroSourcePlan


namespace Controller.Cost.ForestZeroSourcePlan
open Controller.Decoder Controller.Decoder.DAG
open Controller.Cost Controller.Cost.ForestZeroEmit Controller.Cost.ForestIndexedOperands
variable {width : Nat}

/-- A declared occurrence is charged against the original forest's complete
row and literal incidence totals, including its physical root/target units. -/
theorem forced_query_component_bounds (graph : DAG n) (rows : List Row) (rawRoots : List Nat)
    (rowsMatch : RowsMatch graph rows) (target : Fin n) (forest : graph.FormulaForest)
    (position : Fin (forcedQueries (width := width) graph rows rawRoots rowsMatch target).length) :
    (forcedQueries (width := width) graph rows rawRoots rowsMatch target)[position].length ≤
      5 * graph.roots.length + 3 * graph.childIncidences ∧
    (forcedQueries (width := width) graph rows rawRoots rowsMatch target)[position].flatten.length ≤
      8 * graph.roots.length + 6 * graph.childIncidences + graph.guardIncidences := by
  let stream := forcedQueries (width := width) graph rows rawRoots rowsMatch target
  have rowMember : stream[position].length ∈ stream.map List.length :=
    List.mem_map.mpr ⟨stream[position], List.getElem_mem position.isLt, rfl⟩
  have literalMember : stream[position].flatten.length ∈ stream.map (fun query => query.flatten.length) :=
    List.mem_map.mpr ⟨stream[position], List.getElem_mem position.isLt, rfl⟩
  have memberSum : ∀ (values : List Nat) (value : Nat), value ∈ values → value ≤ values.sum := by
    intro values value present
    induction values with
    | nil => cases present
    | cons head tail ih =>
      rcases List.mem_cons.mp present with same | tailMember
      · subst value
        simp only [List.sum_cons]
        omega
      · have tailBound := ih tailMember
        simp only [List.sum_cons]
        omega
  have row := memberSum _ _ rowMember
  have literals := memberSum _ _ literalMember
  have totals := forced_queries_forest_bounds (width := width) graph rows rawRoots rowsMatch target forest
  exact ⟨row.trans totals.1, literals.trans totals.2⟩

/-- A single global word room derives every per-occurrence allocation room;
no independent room oracle is attached to the declared queries. -/
theorem forced_query_word_rooms (graph : DAG n) (rows : List Row) (rawRoots : List Nat)
    (rowsMatch : RowsMatch graph rows) (target : Fin n) (forest : graph.FormulaForest)
    (heap : Array (Word width))
    (room : heap.size + 2 * (n + graph.nodeCount) + 14 +
      5 * (5 * graph.roots.length + 3 * graph.childIncidences) +
      15 * (8 * graph.roots.length + 6 * graph.childIncidences + graph.guardIncidences) < 2 ^ width) :
    ∀ position : Fin (forcedQueries (width := width) graph rows rawRoots rowsMatch target).length,
      heap.size + 2 * (n + graph.nodeCount) + 14 +
        5 * (forcedQueries (width := width) graph rows rawRoots rowsMatch target)[position].length +
        15 * (forcedQueries (width := width) graph rows rawRoots rowsMatch target)[position].flatten.length < 2 ^ width := by
  intro position
  have localCounts := forced_query_component_bounds (width := width) graph rows rawRoots rowsMatch target forest position
  omega

end Controller.Cost.ForestZeroSourcePlan


namespace Controller.Cost.ForestZeroSourcePlan
open Controller.Decoder Controller.Decoder.DAG
open Controller.Cost Controller.Cost.ForestZeroEmit Controller.Cost.ForestZeroDictionary Controller.Cost.ForestIndexedOperands
variable {width : Nat}

/-- Actual resident array pushes and all four physical backing fields are
charged once over the original forest incidence bounds. These construction
operations remain separate from fetched query-execution ticks. -/
theorem forced_resident_construction_bound (graph : DAG n) (rows : List Row) (rawRoots : List Nat)
    (rowsMatch : RowsMatch graph rows) (target : Fin n) (forest : graph.FormulaForest)
    (heap : Array (Word width)) (layout : Layout (n + graph.nodeCount) heap.size)
    (priorProgram : Program width 8) (initialWords : Array (Word width)) :
    let stream := residentInstructions heap layout n (Nat.le_add_right _ _) priorProgram.size
      (forcedQueries (width := width) graph rows rawRoots rowsMatch target)
    (residentProgram priorProgram heap layout n (Nat.le_add_right _ _)
      (forcedQueries (width := width) graph rows rawRoots rowsMatch target)).size ≤
      priorProgram.size + 833 * graph.roots.length + 183 * graph.childIncidences + 28 * graph.guardIncidences + 2 ∧
    (ForestZeroResident.backing stream initialWords).size ≤
      initialWords.size + 3332 * graph.roots.length + 732 * graph.childIncidences + 112 * graph.guardIncidences + 8 ∧
    9 * stream.length ≤ 7497 * graph.roots.length +
      1647 * graph.childIncidences + 252 * graph.guardIncidences + 18 := by
  dsimp only
  have count := forced_resident_length (width := width) graph rows rawRoots rowsMatch target forest
    heap layout priorProgram.size
  have backingSize := ForestZeroResident.backing_size
    (resident_backing_trace heap layout n (Nat.le_add_right _ _) priorProgram.size
      (forcedQueries (width := width) graph rows rawRoots rowsMatch target) initialWords)
  unfold residentProgram
  rw [ForestZeroResident.materialize_size]
  omega

end Controller.Cost.ForestZeroSourcePlan


namespace Controller.Cost.ForestZeroSourcePlan
open Controller.Decoder Controller.Decoder.DAG
open Controller.Cost Controller.Cost.ForestZeroEmit Controller.Cost.ForestZeroDictionary
open Controller.Cost.ForestZeroInitialize Controller.Cost.ForestIndexedOperands Controller.Cost.ForestZeroSource
variable {width : Nat}

/-- The retained source heap is the actual packet plus its loaded target cell
and the once-reserved empty dictionary regions. -/
def controlledHeap (graph : DAG n) (rows : List Row) (rawRoots : List Nat) (target : Fin n) :
    Array (Word width) :=
  reserveHeap ((packetHeap width n rows rawRoots).push (word width target.val)) (n + graph.nodeCount)

def controlledLayout (graph : DAG n) (rows : List Row) (rawRoots : List Nat) (target : Fin n) :
    Layout (n + graph.nodeCount) (controlledHeap (width := width) graph rows rawRoots target).size :=
  reservedLayout ((packetHeap width n rows rawRoots).push (word width target.val)) (n + graph.nodeCount)

theorem controlled_headers (graph : DAG n) (rows : List Row) (rawRoots : List Nat)
    (rowsMatch : RowsMatch graph rows) (target : Fin n) :
    (controlledHeap (width := width) graph rows rawRoots target)[0]? = some (word width n) ∧
    (controlledHeap (width := width) graph rows rawRoots target)[1]? = some (word width graph.nodeCount) := by
  have headerSize : 1 < (packetHeap width n rows rawRoots).size := by rw [packetHeap_size]; omega
  have pushed : ∀ address, address < (packetHeap width n rows rawRoots).size →
      ((packetHeap width n rows rawRoots).push (word width target.val))[address]? =
        (packetHeap width n rows rawRoots)[address]? := by
    intro address bound
    simp only [Array.getElem?_push, ite_eq_right (show address ≠ (packetHeap width n rows rawRoots).size by omega)]
  constructor
  · exact (reserve_source _ _ 0 (by rw [Array.size_push]; omega)).trans
      ((pushed 0 (by omega)).trans (packet_header width n rows rawRoots))
  · exact (reserve_source _ _ 1 (by rw [Array.size_push]; omega)).trans
      ((pushed 1 headerSize).trans
        (by simpa only [rowsMatch.length_eq] using (packetHeader width n rows rawRoots).nodeWord))

/-- The actual reserved layout fixes both dictionary bases and the physical
heap endpoint. No caller-selected query geometry is introduced. -/
theorem controlled_geometry (graph : DAG n) (rows : List Row) (rawRoots : List Nat) (target : Fin n) :
    let sourceEnd := (packetHeap width n rows rawRoots).size + 1
    let heap := controlledHeap (width := width) graph rows rawRoots target
    let layout := controlledLayout (width := width) graph rows rawRoots target
    sourceEnd = layout.tableBase ∧ sourceEnd ≤ layout.inverseBase ∧ sourceEnd ≤ heap.size ∧
      1 < sourceEnd ∧ layout.inverseBase = layout.tableBase + (n + graph.nodeCount) ∧
      heap.size = layout.inverseBase + (n + graph.nodeCount) := by
  dsimp only [controlledHeap, controlledLayout, reservedLayout]
  rw [reserveHeap_size, Array.size_push]
  have packetSize := packetHeap_size width n rows rawRoots
  omega

end Controller.Cost.ForestZeroSourcePlan


namespace Controller.Cost.ForestZeroSourcePlan
open Controller.Decoder Controller.Decoder.DAG Controller.CNF
open Controller.Cost Controller.Cost.ForestZeroResident Controller.Cost.ForestZeroDictionary
open Controller.Cost.ForestZeroEmit Controller.Cost.ForestZeroAdmissibleCaller Controller.Cost.ForestIndexedOperands Controller.Cost.ForestZeroSource
variable {width : Nat}

/-- The actual original packet and control trailer determine all resident
query plans. Declared occurrences execute in order in one formed program;
original-channel reconstruction is charged only on the successful query. -/
theorem forced_resident_execution (graph : DAG n) (guarded : graph.Guarded)
    (rows : List Row) (rawRoots : List Nat) (rowsMatch : RowsMatch graph rows)
    (rootsMatch : RootsMatch graph rawRoots) (target : Fin n) (forest : graph.FormulaForest)
    (priorProgram : Program width 8) (callerRest : List (Word width)) (initial : State width 8)
    (programRoom :
      (residentProgram priorProgram (controlledHeap (width := width) graph rows rawRoots target)
        (controlledLayout (width := width) graph rows rawRoots target) n (Nat.le_add_right _ _)
        (forcedQueries (width := width) graph rows rawRoots rowsMatch target)).size < 2 ^ width)
    (wordRoom : (controlledHeap (width := width) graph rows rawRoots target).size + 2 * (n + graph.nodeCount) + 14 +
      5 * (5 * graph.roots.length + 3 * graph.childIncidences) +
      15 * (8 * graph.roots.length + 6 * graph.childIncidences + graph.guardIncidences) < 2 ^ width)
    (initialReady : QueryReady (ambient := n + graph.nodeCount)
      (controlledHeap (width := width) graph rows rawRoots target)
      (controlledLayout (width := width) graph rows rawRoots target).tableBase
      (controlledLayout (width := width) graph rows rawRoots target).inverseBase
      (occurrenceResume priorProgram (controlledHeap (width := width) graph rows rawRoots target)
        (controlledLayout (width := width) graph rows rawRoots target) n (Nat.le_add_right _ _)
        (forcedQueries (width := width) graph rows rawRoots rowsMatch target)
        (List.finRange (forcedQueries (width := width) graph rows rawRoots rowsMatch target).length)) callerRest initial) :
    ∃ answer : Bool, ∃ final ticks peak,
      Execution (residentProgram priorProgram (controlledHeap (width := width) graph rows rawRoots target)
        (controlledLayout (width := width) graph rows rawRoots target) n (Nat.le_add_right _ _)
        (forcedQueries (width := width) graph rows rawRoots rowsMatch target)) initial final ticks peak ∧
      final.halted = true ∧ final.reg 4 = word width (if answer then 1 else 0) ∧
      ticks ≤ 4288 * graph.roots.length + 2772 * graph.childIncidences +
        387 * graph.guardIncidences + 13 * n + 2 ∧
      peak ≤ initial.liveWords + 146 * graph.roots.length + 105 * graph.childIncidences +
        15 * graph.guardIncidences + 2 * n + 21 ∧
      (answer = true ↔ ∃ position : Fin (forcedQueries (width := width) graph rows rawRoots rowsMatch target).length,
        Satisfiable (constructorFormula (controlledHeap (width := width) graph rows rawRoots target)
          (controlledLayout (width := width) graph rows rawRoots target)
          (ForestZeroCompile.empty (n + graph.nodeCount)) (ForestZeroCompile.empty_coherent _)
          (forcedQueries (width := width) graph rows rawRoots rowsMatch target)[position] n (Nat.le_add_right _ _))) ∧
      (answer = true → ∃ position : Fin (forcedQueries (width := width) graph rows rawRoots rowsMatch target).length,
        Satisfiable (constructorFormula (controlledHeap (width := width) graph rows rawRoots target)
          (controlledLayout (width := width) graph rows rawRoots target)
          (ForestZeroCompile.empty (n + graph.nodeCount)) (ForestZeroCompile.empty_coherent _)
          (forcedQueries (width := width) graph rows rawRoots rowsMatch target)[position] n (Nat.le_add_right _ _)) ∧
        QueryChannelWitness (controlledHeap (width := width) graph rows rawRoots target)
          (controlledLayout (width := width) graph rows rawRoots target)
          (forcedQueries (width := width) graph rows rawRoots rowsMatch target)[position] n (Nat.le_add_right _ _) final.output) := by
  let heap := controlledHeap (width := width) graph rows rawRoots target
  let layout := controlledLayout (width := width) graph rows rawRoots target
  let stream := forcedQueries (width := width) graph rows rawRoots rowsMatch target
  let sourceEnd := (packetHeap width n rows rawRoots).size + 1
  have geometry := controlled_geometry (width := width) graph rows rawRoots target
  have headers := controlled_headers (width := width) graph rows rawRoots rowsMatch target
  have stored : ∀ position : Fin stream.length, ∀ reference ∈ stream[position].flatten,
      StoredReference heap n sourceEnd reference := by
    intro position
    exact forced_stream_stored (width := width) graph rows rawRoots rowsMatch rootsMatch target
      stream[position] (List.getElem_mem position.isLt)
  have grammar : ∀ position : Fin stream.length,
      Controller.Horn.DualHorn (ofClauses (ForestZeroAssembly.originalRows (reservedReferences stream[position]))) := by
    intro position
    exact forced_stream_dualHorn (width := width) graph guarded rows rawRoots rowsMatch target
      stream[position] (List.getElem_mem position.isLt)
  have perRoom := forced_query_word_rooms (width := width) graph rows rawRoots rowsMatch target forest heap wordRoom
  let scratch := 145 * graph.roots.length + 105 * graph.childIncidences + 15 * graph.guardIncidences + n + 20
  have scratchBound : ∀ position : Fin stream.length,
      5 * stream[position].length + 15 * stream[position].flatten.length + n + 20 ≤ scratch := by
    intro position
    have localCounts := forced_query_component_bounds (width := width) graph rows rawRoots rowsMatch target forest position
    change stream[position].length ≤ _ ∧ stream[position].flatten.length ≤ _ at localCounts
    dsimp only [scratch]
    omega
  obtain ⟨answer, final, ticks, peak, trace, halted, tag, timeBound, peakBound, meaning, model⟩ :=
    resident_first_success_execution priorProgram heap layout stream n sourceEnd graph.nodeCount
      (Nat.le_add_right _ _) callerRest stored geometry.1.le geometry.2.1 geometry.2.2.1 geometry.2.2.2.1
      headers.1 headers.2 rfl geometry.2.2.2.2.1 geometry.2.2.2.2.2 grammar programRoom perRoom
      scratch scratchBound initial initialReady
  have totals := forced_queries_forest_bounds (width := width) graph rows rawRoots rowsMatch target forest
  have streamLength : stream.length = graph.roots.length := forced_queries_length (width := width) graph rows rawRoots rowsMatch target
  change (stream.map List.length).sum ≤ _ ∧
    (stream.map fun refs => refs.flatten.length).sum ≤ _ at totals
  rw [streamLength] at timeBound peakBound
  refine ⟨answer, final, ticks, peak, trace, halted, tag, ?_, ?_, meaning, model⟩
  · omega
  · dsimp only [scratch] at peakBound
    omega

end Controller.Cost.ForestZeroSourcePlan


namespace Controller.Cost.ForestZeroSourcePlan
open Controller.Decoder Controller.Decoder.DAG
open Controller.Cost Controller.Cost.GateProgram Controller.Cost.ForestIndexedOperands
open Controller.Cost.ForestZeroSource Controller.Cost.ForestZeroResident
open Controller.Cost.ForestZeroInitialize Controller.Cost.ForestZeroCallerWiden
variable {width : Nat}

/-- The fixed loader consumes the original positional packet payload. -/
theorem cold_payload_length (graph : DAG n) (rows : List Row) (rawRoots : List Nat)
    (rowsMatch : RowsMatch graph rows) (rootsMatch : RootsMatch graph rawRoots) :
    ((serializedRows 5 rows rawRoots).map (word width)).length =
      6 * graph.nodeCount + graph.childIncidences + graph.guardIncidences + graph.roots.length := by
  simpa only [List.length_map] using matched_packet_length 5 graph rows rawRoots rowsMatch rootsMatch

/-- The loader's physically allocated array equals the original typed source
packet, including every duplicate incidence and declared root occurrence. -/
theorem cold_packet_source (graph : DAG n) (rows : List Row) (rawRoots : List Nat)
    (rowsMatch : RowsMatch graph rows) (rootsMatch : RootsMatch graph rawRoots) :
    ForestZeroControlLoad.packetHeap width n graph.nodeCount graph.childIncidences
      graph.guardIncidences graph.roots.length ((serializedRows 5 rows rawRoots).map (word width)) =
      ForestZeroSource.packetHeap width n rows rawRoots := by
  rw [packet_exact, matched_cold_input_words (width := width) graph rows rawRoots rowsMatch rootsMatch]
  simp only [ForestZeroControlLoad.packetHeap, ForestInputMetadata.headerWords, List.append_toArray]

/-- A resident assembler retains fetched instructions in its preceding array. -/
theorem resident_prior_fetch (priorProgram : Program width 8) (heap : Array (Word width))
    (layout : ForestZeroDictionary.Layout ambient heap.size) (channels : Nat)
    (within : channels ≤ ambient) (queries : List (List (List (ForestZeroEmit.Reference ambient))))
    (position : Nat) (before : position < priorProgram.size) :
    (residentProgram priorProgram heap layout channels within queries)[position]? = priorProgram[position]? := by
  unfold residentProgram
  have contents := materialize_contents priorProgram
    (residentInstructions heap layout channels within priorProgram.size queries)
  have getter := congrArg (fun items : List (Instruction width 8) => items[position]?) contents
  simp only [Array.getElem?_toList] at getter
  rw [getter, List.getElem?_append_left (by simpa only [Array.length_toList] using before)]
  simp only [Array.getElem?_toList]

/-- The cold prefix has fixed resident size independent of every source count. -/
def coldPrefix (priorProgram : Program width 8) : Program width 8 :=
  materialize priorProgram ((ForestZeroControlLoad.code width priorProgram.size ++ [Instruction.pop 2]).map
    RegisterWiden.widenInstruction)

theorem coldPrefix_size (priorProgram : Program width 8) :
    (coldPrefix priorProgram).size = priorProgram.size + 75 := by
  rw [coldPrefix, materialize_size]
  simp only [List.length_map, List.length_append, ForestZeroControlLoad.code_length,
    List.length_cons, List.length_nil]

/-- Every loader instruction is fetched from the same once-assembled resident
program subsequently used by the declared root occurrences. -/
theorem resident_cold_fetch (priorProgram : Program width 8) (heap : Array (Word width))
    (layout : ForestZeroDictionary.Layout ambient heap.size) (channels : Nat)
    (within : channels ≤ ambient) (queries : List (List (List (ForestZeroEmit.Reference ambient)))) :
    WidenedBlockAt (residentProgram (coldPrefix priorProgram) heap layout channels within queries)
      priorProgram.size (ForestZeroControlLoad.code width priorProgram.size ++ [Instruction.pop 2]) := by
  intro offset bound
  have codeLength : (ForestZeroControlLoad.code width priorProgram.size ++ [Instruction.pop 2]).length = 75 := by
    simp only [List.length_append, ForestZeroControlLoad.code_length, List.length_cons, List.length_nil]
  rw [resident_prior_fetch _ _ _ _ _ _ _ (by rw [coldPrefix_size]; omega)]
  have stored := materialize_block priorProgram []
    ((ForestZeroControlLoad.code width priorProgram.size ++ [Instruction.pop 2]).map RegisterWiden.widenInstruction)
    [] offset (by simpa only [List.length_map] using bound)
  simpa only [coldPrefix, List.nil_append, List.append_nil, List.length_nil, Nat.add_zero,
    List.getElem?_map] using stored

end Controller.Cost.ForestZeroSourcePlan


namespace Controller.Cost.ForestZeroSourcePlan
open Controller.Cost Controller.Cost.GateProgram Controller.Cost.ForestZeroTouch
open Controller.Cost.ForestZeroInitialize Controller.Cost.ForestZeroUnits
open Controller.Cost.ForestZeroControlLoad
variable {width : Nat}
open Controller.Cost.ForestZeroCallerWiden Controller.Cost.ForestZeroAdmissibleCaller

/-- A fixed cold loader consumes the actual header, incidence payload, and
control word before reserving dictionary regions. Its computed inverse base is
popped by one further fetched instruction into the actual query-entry register. -/
theorem cold_bootstrap_execution
    (program : Program width 8) (base channels nodes children guards roots : Nat)
    (payload rest output : List (Word width)) (target : Fin channels)
    (address loaded temporary : Word width) (saved : Fin 8 → Word width)
    (lengthEq : payload.length = 6 * nodes + children + guards + roots)
    (room : 6 + payload.length + 2 * (channels + nodes) < 2 ^ width)
    (fits : base + 75 < 2 ^ width)
    (present : WidenedBlockAt program base (ForestZeroControlLoad.code width base ++ [Instruction.pop 2])) :
    let packet := ForestZeroControlLoad.packetHeap width channels nodes children guards roots payload
    let source := reserveHeap (packet.push (word width target.val)) (channels + nodes)
    let layout := reservedLayout (packet.push (word width target.val)) (channels + nodes)
    let initial := RegisterWiden.widenState
      ((ForestCounter.counterState (#[] : Array (Word width)) base address loaded temporary).frame
        (ForestInputMetadata.headerWords width channels nodes children guards roots ++ payload ++
          (word width target.val :: rest)) output) saved
    let final := RegisterWiden.widenState
      (atState source (base + 75) 0 (6 + payload.length) (6 + payload.length + channels + nodes) 0 rest output) saved
    Execution program initial final (63 + 7 * payload.length + 14 * (channels + nodes))
      (16 + payload.length + 2 * (channels + nodes) + rest.length + output.length) ∧
    QueryReady (ambient := channels + nodes) source layout.tableBase layout.inverseBase (base + 75) rest final := by
  intro packet source layout initial final
  have packetSize : packet.size = 5 + payload.length := by
    simp only [packet, ForestZeroControlLoad.packetHeap, Array.size_append,
      List.size_toArray, ForestInputMetadata.headerWords, List.length_cons, List.length_nil]
  have allCode := lower_block program base _ present
  have controlAt := BlockAt.prefix (lowerProgram program) base (ForestZeroControlLoad.code width base) [.pop 2] allCode
  have control := ForestZeroControlLoad.execution (lowerProgram program) base channels nodes children guards roots
    payload rest output target address loaded temporary lengthEq room (by omega) controlAt
  let middle := atState source (base + 74) 0 (6 + payload.length) 0 0
    (word width (6 + payload.length + channels + nodes) :: rest) output
  let lowFinal := atState source (base + 75) 0 (6 + payload.length) (6 + payload.length + channels + nodes) 0 rest output
  have popAt : (lowerProgram program)[base + 74]? = some (.pop 2) := by
    have pop := BlockAt.suffix (lowerProgram program) base (ForestZeroControlLoad.code width base) [.pop 2] allCode
    have actual := pop 0 (by change 0 < 1; exact Nat.zero_lt_succ 0)
    simpa only [ForestZeroControlLoad.code_length, Nat.add_zero, List.getElem?_cons_zero] using actual
  have popStep : programStep (lowerProgram program) middle = some lowFinal := by
    unfold programStep
    have pcVal : middle.pc.val = base + 74 := by
      change (word width (base + 74)).val = base + 74
      exact Nat.mod_eq_of_lt (by omega)
    rw [pcVal, popAt]
    change step (.pop 2) middle = some lowFinal
    simp only [step, middle, atState, Bool.false_eq_true, ite_false]
    apply congrArg some
    change State.mk _ source rest output _ false =
      State.mk _ source rest output (word width (base + 75)) false
    rw [State.mk.injEq]
    refine ⟨?_, rfl, rfl, rfl, ?_, rfl⟩
    · funext register
      fin_cases register <;> rfl
    · change word width ((word width (base + 74)).val + 1) = word width (base + 75)
      rw [show (word width (base + 74)).val = base + 74 from Nat.mod_eq_of_lt (by omega)]
  have popTrace : Execution (lowerProgram program) middle lowFinal 1 middle.liveWords := by
    have tail := Execution.refl (p := lowerProgram program) lowFinal
    have joined := Execution.cons popStep tail
    have peakEq : max middle.liveWords lowFinal.liveWords = middle.liveWords := by
      dsimp only [middle, lowFinal]
      simp only [atState_liveWords, List.length_cons]
      exact max_eq_left (by omega)
    simpa only [Nat.zero_add, peakEq] using joined
  have lowTrace := control.append popTrace
  have peakEq : max (12 + payload.length + 2 * (channels + nodes) + rest.length + output.length)
      middle.liveWords = 12 + payload.length + 2 * (channels + nodes) + rest.length + output.length := by
    dsimp only [middle, source]
    simp only [atState_liveWords, reserveHeap_size, Array.size_push, List.length_cons, packetSize]
    omega
  rw [peakEq] at lowTrace
  have trace := ForestZeroCallerWiden.execution program _ _ _ _ lowTrace (by rfl) saved
  constructor
  · convert trace using 1 <;>
      (try simp only [initial, final, lowFinal, Nat.add_assoc]) <;> omega
  · refine ⟨rfl, ForestZeroBackendFrame.refl source (by dsimp only [source, layout, reservedLayout]; rw [reserveHeap_size, Array.size_push]; omega), ?_, rfl, rfl, rfl, ?_, ?_, ?_⟩
    · intro coordinate
      have represented := reserve_represented (packet.push (word width target.val)) (channels + nodes)
      change source[layout.tableBase + coordinate.val]? = some (word width 0)
      simpa only [source, layout, ForestZeroCompile.empty, Vector.getElem_replicate] using represented.slots coordinate
    · rfl
    · change word width (6 + payload.length) = word width (packet.push (word width target.val)).size
      rw [Array.size_push, packetSize]
      congr 1
      omega
    · change word width (6 + payload.length + channels + nodes) =
        word width ((packet.push (word width target.val)).size + (channels + nodes))
      rw [Array.size_push, packetSize]
      congr 1
      omega

end Controller.Cost.ForestZeroSourcePlan


namespace Controller.Cost.ForestZeroSourcePlan
open Controller.Decoder Controller.Decoder.DAG
open Controller.Cost Controller.Cost.GateProgram Controller.Cost.ForestZeroTouch
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestZeroSource
open Controller.Cost.ForestZeroInitialize Controller.Cost.ForestZeroAdmissibleCaller
open Controller.Cost.ForestZeroResident
variable {width : Nat}

/-- Original words, including the target trailer, form the cold machine input. -/
def coldInitial (graph : DAG n) (rows : List Row) (rawRoots : List Nat) (target : Fin n)
    (base : Nat) (rest output : List (Word width))
    (address loaded temporary : Word width) (saved : Fin 8 → Word width) : State width 8 :=
  RegisterWiden.widenState
    ((ForestCounter.counterState (#[] : Array (Word width)) base address loaded temporary).frame
      ((inputPacket n 0 rows rawRoots).map (word width) ++ (word width target.val :: rest)) output) saved

/-- Initial source readiness is derived by the actual cold execution. Both
source cells and dictionary register values come from loaded input words. -/
theorem cold_forced_ready_execution (graph : DAG n) (rows : List Row) (rawRoots : List Nat)
    (rowsMatch : RowsMatch graph rows) (rootsMatch : RootsMatch graph rawRoots) (target : Fin n)
    (priorProgram : Program width 8) (rest output : List (Word width))
    (address loaded temporary : Word width) (saved : Fin 8 → Word width)
    (programRoom :
      (residentProgram (coldPrefix priorProgram) (controlledHeap (width := width) graph rows rawRoots target)
        (controlledLayout (width := width) graph rows rawRoots target) n (Nat.le_add_right _ _)
        (forcedQueries (width := width) graph rows rawRoots rowsMatch target)).size < 2 ^ width)
    (room : (controlledHeap (width := width) graph rows rawRoots target).size < 2 ^ width) :
    ∃ ready,
      Execution (residentProgram (coldPrefix priorProgram) (controlledHeap (width := width) graph rows rawRoots target)
        (controlledLayout (width := width) graph rows rawRoots target) n (Nat.le_add_right _ _)
        (forcedQueries (width := width) graph rows rawRoots rowsMatch target))
        (coldInitial graph rows rawRoots target priorProgram.size rest output address loaded temporary saved)
        ready (63 + 7 * (6 * graph.nodeCount + graph.childIncidences + graph.guardIncidences + graph.roots.length) +
          14 * (n + graph.nodeCount))
        (16 + (6 * graph.nodeCount + graph.childIncidences + graph.guardIncidences + graph.roots.length) +
          2 * (n + graph.nodeCount) + rest.length + output.length) ∧
      QueryReady (ambient := n + graph.nodeCount)
        (controlledHeap (width := width) graph rows rawRoots target)
        (controlledLayout (width := width) graph rows rawRoots target).tableBase
        (controlledLayout (width := width) graph rows rawRoots target).inverseBase
        (occurrenceResume (coldPrefix priorProgram) (controlledHeap (width := width) graph rows rawRoots target)
          (controlledLayout (width := width) graph rows rawRoots target) n (Nat.le_add_right _ _)
          (forcedQueries (width := width) graph rows rawRoots rowsMatch target)
          (List.finRange (forcedQueries (width := width) graph rows rawRoots rowsMatch target).length)) rest ready ∧
      ready.liveWords =
        (coldInitial graph rows rawRoots target priorProgram.size rest output address loaded temporary saved).liveWords +
          2 * (n + graph.nodeCount) := by
  let payload := (serializedRows 5 rows rawRoots).map (word width)
  let heap := controlledHeap (width := width) graph rows rawRoots target
  let layout := controlledLayout (width := width) graph rows rawRoots target
  let queries := forcedQueries (width := width) graph rows rawRoots rowsMatch target
  let program := residentProgram (coldPrefix priorProgram) heap layout n (Nat.le_add_right _ _) queries
  have lengthEq := cold_payload_length (width := width) graph rows rawRoots rowsMatch rootsMatch
  change payload.length = 6 * graph.nodeCount + graph.childIncidences + graph.guardIncidences + graph.roots.length at lengthEq
  have packetEq := cold_packet_source (width := width) graph rows rawRoots rowsMatch rootsMatch
  have prefixBound : priorProgram.size + 75 ≤ program.size := by
    unfold program residentProgram
    rw [materialize_size, coldPrefix_size]
    omega
  have dataRoom : 6 + payload.length + 2 * (n + graph.nodeCount) < 2 ^ width := by
    change (reserveHeap ((packetHeap width n rows rawRoots).push (word width target.val))
      (n + graph.nodeCount)).size < 2 ^ width at room
    have packetSize : (packetHeap width n rows rawRoots).size = 5 + payload.length := by
      have exactSize := packetHeap_size width n rows rawRoots
      have payloadSize := serializedRows_length 5 rows rawRoots
      simp only [payload, List.length_map]
      omega
    rw [reserveHeap_size, Array.size_push, packetSize] at room
    omega
  have boot := cold_bootstrap_execution program priorProgram.size n graph.nodeCount graph.childIncidences
    graph.guardIncidences graph.roots.length payload rest output target address loaded temporary saved
    lengthEq dataRoom (lt_of_le_of_lt prefixBound programRoom)
    (resident_cold_fetch priorProgram heap layout n (Nat.le_add_right _ _) queries)
  dsimp only at boot
  rw [packetEq] at boot
  let ready := RegisterWiden.widenState
    (atState heap (priorProgram.size + 75) 0 (6 + payload.length)
      (6 + payload.length + n + graph.nodeCount) 0 rest output) saved
  have initialEq : RegisterWiden.widenState
      ((ForestCounter.counterState (#[] : Array (Word width)) priorProgram.size address loaded temporary).frame
        (ForestInputMetadata.headerWords width n graph.nodeCount graph.childIncidences graph.guardIncidences
          graph.roots.length ++ payload ++ (word width target.val :: rest)) output) saved =
      coldInitial graph rows rawRoots target priorProgram.size rest output address loaded temporary saved := by
    rw [coldInitial, matched_cold_input_words (width := width) graph rows rawRoots rowsMatch rootsMatch]
    rfl
  have entryEq : occurrenceResume (coldPrefix priorProgram) heap layout n (Nat.le_add_right _ _) queries
      (List.finRange queries.length) = priorProgram.size + 75 := by
    simp only [occurrenceResume, List.length_finRange, Nat.sub_self, occurrenceEntry,
      List.take_zero, residentPrefix, coldPrefix_size]
  refine ⟨ready, ?_, ?_, ?_⟩
  · have trace := boot.1
    rw [initialEq] at trace
    simpa only [ready, lengthEq, heap, controlledHeap, program, layout, queries] using trace
  · rw [entryEq]
    exact boot.2
  · have inputSize : (inputPacket n 0 rows rawRoots).length = 5 + payload.length := by
      simp only [inputPacket, List.length_append, globalHeader_length, payload, List.length_map, Nat.zero_add]
    have heapSize : heap.size = 6 + payload.length + 2 * (n + graph.nodeCount) := by
      change (reserveHeap ((packetHeap width n rows rawRoots).push (word width target.val))
        (n + graph.nodeCount)).size = _
      rw [reserveHeap_size, Array.size_push, packetHeap_size]
      have payloadSize := serializedRows_length 5 rows rawRoots
      simp only [payload, List.length_map]
      omega
    have initialLive :
        (coldInitial graph rows rawRoots target priorProgram.size rest output address loaded temporary saved).liveWords =
          15 + payload.length + rest.length + output.length := by
      simp only [coldInitial, RegisterWiden.widenState_liveWords, State.frame_liveWords,
        ForestCounter.counterState_liveWords, List.length_append, List.length_cons,
        List.length_map, Array.size_empty]
      rw [inputSize]
      omega
    have readyLive : ready.liveWords = 15 + payload.length + 2 * (n + graph.nodeCount) +
        rest.length + output.length := by
      simp only [ready, RegisterWiden.widenState_liveWords, atState_liveWords, heapSize]
      omega
    rw [initialLive, readyLive]
    omega

end Controller.Cost.ForestZeroSourcePlan


namespace Controller.Cost.ForestZeroSourcePlan
open Controller.Decoder Controller.Decoder.DAG Controller.CNF
open Controller.Cost Controller.Cost.GateProgram Controller.Cost.ForestZeroAdmissibleCaller
open Controller.Cost.ForestIndexedOperands
variable {width : Nat}

/-- Every cold word is retained in the actual initial storage charge. -/
theorem coldInitial_liveWords (graph : DAG n) (rows : List Row) (rawRoots : List Nat) (target : Fin n)
    (base : Nat) (rest output : List (Word width))
    (address loaded temporary : Word width) (saved : Fin 8 → Word width) :
    (coldInitial graph rows rawRoots target base rest output address loaded temporary saved).liveWords =
      10 + (inputPacket n 0 rows rawRoots).length + rest.length + output.length := by
  simp only [coldInitial, RegisterWiden.widenState_liveWords, State.frame_liveWords,
    ForestCounter.counterState_liveWords, Array.size_empty, List.length_append,
    List.length_map, List.length_cons]
  omega

/-- The fixed cold loader and the original positional query stream execute
one actual resident program. Initial query metadata and readiness are derived
from loaded words; original-channel output is emitted at most once. -/
theorem cold_forced_resident_execution (graph : DAG n) (guarded : graph.Guarded)
    (rows : List Row) (rawRoots : List Nat) (rowsMatch : RowsMatch graph rows)
    (rootsMatch : RootsMatch graph rawRoots) (target : Fin n) (forest : graph.FormulaForest)
    (priorProgram : Program width 8) (callerRest output : List (Word width))
    (address loaded temporary : Word width) (saved : Fin 8 → Word width)
    (programRoom :
      (residentProgram (coldPrefix priorProgram) (controlledHeap (width := width) graph rows rawRoots target)
        (controlledLayout (width := width) graph rows rawRoots target) n (Nat.le_add_right _ _)
        (forcedQueries (width := width) graph rows rawRoots rowsMatch target)).size < 2 ^ width)
    (wordRoom : (controlledHeap (width := width) graph rows rawRoots target).size + 2 * (n + graph.nodeCount) + 14 +
      5 * (5 * graph.roots.length + 3 * graph.childIncidences) +
      15 * (8 * graph.roots.length + 6 * graph.childIncidences + graph.guardIncidences) < 2 ^ width) :
    ∃ answer : Bool, ∃ final ticks peak,
      Execution (residentProgram (coldPrefix priorProgram) (controlledHeap (width := width) graph rows rawRoots target)
        (controlledLayout (width := width) graph rows rawRoots target) n (Nat.le_add_right _ _)
        (forcedQueries (width := width) graph rows rawRoots rowsMatch target)) (coldInitial graph rows rawRoots target priorProgram.size callerRest output address loaded temporary saved) final ticks peak ∧
      final.halted = true ∧ final.reg 4 = word width (if answer then 1 else 0) ∧
      ticks ≤ 63 + 7 * (6 * graph.nodeCount + graph.childIncidences + graph.guardIncidences + graph.roots.length) +
        14 * (n + graph.nodeCount) + 4288 * graph.roots.length + 2772 * graph.childIncidences +
        387 * graph.guardIncidences + 13 * n + 2 ∧
      peak ≤ (coldInitial graph rows rawRoots target priorProgram.size callerRest output address loaded temporary saved).liveWords + 2 * (n + graph.nodeCount) + 146 * graph.roots.length + 105 * graph.childIncidences +
        15 * graph.guardIncidences + 2 * n + 21 ∧
      (answer = true ↔ ∃ position : Fin (forcedQueries (width := width) graph rows rawRoots rowsMatch target).length,
        Satisfiable (constructorFormula (controlledHeap (width := width) graph rows rawRoots target)
          (controlledLayout (width := width) graph rows rawRoots target)
          (ForestZeroCompile.empty (n + graph.nodeCount)) (ForestZeroCompile.empty_coherent _)
          (forcedQueries (width := width) graph rows rawRoots rowsMatch target)[position] n (Nat.le_add_right _ _))) ∧
      (answer = true → ∃ position : Fin (forcedQueries (width := width) graph rows rawRoots rowsMatch target).length,
        Satisfiable (constructorFormula (controlledHeap (width := width) graph rows rawRoots target)
          (controlledLayout (width := width) graph rows rawRoots target)
          (ForestZeroCompile.empty (n + graph.nodeCount)) (ForestZeroCompile.empty_coherent _)
          (forcedQueries (width := width) graph rows rawRoots rowsMatch target)[position] n (Nat.le_add_right _ _)) ∧
        QueryChannelWitness (controlledHeap (width := width) graph rows rawRoots target)
          (controlledLayout (width := width) graph rows rawRoots target)
          (forcedQueries (width := width) graph rows rawRoots rowsMatch target)[position] n (Nat.le_add_right _ _) final.output) := by
  have loadRoom : (controlledHeap (width := width) graph rows rawRoots target).size < 2 ^ width := by
    omega
  obtain ⟨ready, loadTrace, initialReady, readyLive⟩ :=
    cold_forced_ready_execution graph rows rawRoots rowsMatch rootsMatch target priorProgram callerRest output
      address loaded temporary saved programRoom loadRoom
  obtain ⟨answer, final, queryTicks, queryPeak, queried, halted, tag, queryTime, querySpace, meaning, model⟩ :=
    forced_resident_execution graph guarded rows rawRoots rowsMatch rootsMatch target forest
      (coldPrefix priorProgram) callerRest ready programRoom wordRoom initialReady
  have allTrace := loadTrace.append queried
  let loadTicks := 63 + 7 * (6 * graph.nodeCount + graph.childIncidences + graph.guardIncidences + graph.roots.length) +
    14 * (n + graph.nodeCount)
  let loadPeak := 16 + (6 * graph.nodeCount + graph.childIncidences + graph.guardIncidences + graph.roots.length) +
    2 * (n + graph.nodeCount) + callerRest.length + output.length
  refine ⟨answer, final, loadTicks + queryTicks, max loadPeak queryPeak,
    allTrace, halted, tag, ?_, ?_, meaning, model⟩
  · dsimp only [loadTicks]
    omega
  · have inputSize := matched_input_packet_length 0 graph rows rawRoots rowsMatch rootsMatch
    have coldSize := coldInitial_liveWords graph rows rawRoots target priorProgram.size callerRest output
      address loaded temporary saved
    rw [readyLive] at querySpace
    apply max_le
    · dsimp only [loadPeak]
      omega
    · exact querySpace

end Controller.Cost.ForestZeroSourcePlan

namespace Controller.Cost.ForestZeroSourcePlan
open Controller.Decoder Controller.Decoder.DAG
open Controller.Cost Controller.Cost.ForestZeroResident Controller.Cost.ForestZeroDictionary
open Controller.Cost.ForestZeroEmit Controller.Cost.ForestIndexedOperands
variable {width : Nat}

/-- One instruction stream contains the fixed cold entry and every positional
query block. Its source-dependent lengths are charged by original incidences. -/
def coldResidentItems (priorProgram : Program width 8) (heap : Array (Word width))
    (layout : Layout ambient heap.size) (channels : Nat) (within : channels ≤ ambient)
    (queries : List (List (List (Reference ambient)))) : List (Instruction width 8) :=
  ((ForestZeroControlLoad.code width priorProgram.size ++ [Instruction.pop 2]).map
    RegisterWiden.widenInstruction) ++
  residentInstructions heap layout channels within (coldPrefix priorProgram).size queries

theorem coldResidentItems_materialize (priorProgram : Program width 8) (heap : Array (Word width))
    (layout : Layout ambient heap.size) (channels : Nat) (within : channels ≤ ambient)
    (queries : List (List (List (Reference ambient)))) :
    materialize priorProgram (coldResidentItems priorProgram heap layout channels within queries) =
      residentProgram (coldPrefix priorProgram) heap layout channels within queries := by
  unfold coldResidentItems residentProgram
  rw [materialize_append]
  rfl

/-- Actual instruction pushes, field formation, and backing-cell pushes are
witnessed for the complete stream, including the cold prefix. Their primitive
construction count is kept separate from fetched execution ticks. -/
theorem coldResidentItems_formation (priorProgram : Program width 8) (heap : Array (Word width))
    (layout : Layout ambient heap.size) (channels : Nat) (within : channels ≤ ambient)
    (queries : List (List (List (Reference ambient)))) (initialWords : Array (Word width)) :
    let items := coldResidentItems priorProgram heap layout channels within queries
    CompilerArrayTrace.Trace items priorProgram
      (residentProgram (coldPrefix priorProgram) heap layout channels within queries) items.length ∧
    BackingTrace items initialWords (backing items initialWords) (4 * items.length) (4 * items.length) := by
  intro items
  constructor
  · rw [← coldResidentItems_materialize]
    exact materialize_trace priorProgram items
  · exact backing_trace items initialWords

/-- Register IDs, opcodes and original stored word operands have an exact
lossless four-word representation whenever the chosen word width admits them. -/
theorem coldResidentItems_fields_exact (priorProgram : Program width 8) (heap : Array (Word width))
    (layout : Layout ambient heap.size) (channels : Nat) (within : channels ≤ ambient)
    (queries : List (List (List (Reference ambient)))) (room : 13 ≤ 2 ^ width) :
    ∀ instruction ∈ coldResidentItems priorProgram heap layout channels within queries,
      (instructionFields instruction).map Fin.val = numericFields instruction := by
  intro instruction _
  exact instructionFields_exact instruction (by omega) room

/-- Both program storage and construction use the actual complete stream.
Repeated root occurrences are counted, and no channel-sized kernel is copied
inside a per-occurrence block. -/
theorem cold_forced_construction_bound (graph : DAG n) (rows : List Row) (rawRoots : List Nat)
    (rowsMatch : RowsMatch graph rows) (target : Fin n) (forest : graph.FormulaForest)
    (priorProgram : Program width 8) (initialWords : Array (Word width)) :
    let heap := controlledHeap (width := width) graph rows rawRoots target
    let layout := controlledLayout (width := width) graph rows rawRoots target
    let queries := forcedQueries (width := width) graph rows rawRoots rowsMatch target
    let items := coldResidentItems priorProgram heap layout n (Nat.le_add_right _ _) queries
    programWords (residentProgram (coldPrefix priorProgram) heap layout n (Nat.le_add_right _ _) queries) ≤
      4 * priorProgram.size + 3332 * graph.roots.length + 732 * graph.childIncidences +
        112 * graph.guardIncidences + 308 ∧
    (backing items initialWords).size ≤ initialWords.size + 3332 * graph.roots.length +
      732 * graph.childIncidences + 112 * graph.guardIncidences + 308 ∧
    9 * items.length ≤ 7497 * graph.roots.length + 1647 * graph.childIncidences +
      252 * graph.guardIncidences + 693 := by
  intro heap layout queries items
  have queryLength := forced_resident_length (width := width) graph rows rawRoots rowsMatch target forest
    heap layout (coldPrefix priorProgram).size
  change (residentInstructions heap layout n (Nat.le_add_right _ _) (coldPrefix priorProgram).size queries).length ≤ _ at queryLength
  have streamLength : items.length = 75 +
      (residentInstructions heap layout n (Nat.le_add_right _ _) (coldPrefix priorProgram).size queries).length := by
    simp only [items, coldResidentItems, List.length_append, List.length_map,
      ForestZeroControlLoad.code_length, List.length_cons, List.length_nil]
  have codeSize : (residentProgram (coldPrefix priorProgram) heap layout n (Nat.le_add_right _ _) queries).size =
      priorProgram.size + items.length := by
    rw [← coldResidentItems_materialize, materialize_size]
  have backingSize := backing_size (backing_trace items initialWords)
  unfold programWords
  rw [codeSize]
  exact ⟨by omega, by omega, by omega⟩

end Controller.Cost.ForestZeroSourcePlan

namespace Controller.Cost.ForestZeroSourcePlan
open Controller.Decoder Controller.Decoder.DAG
open Controller.Cost Controller.Cost.ForestZeroResident Controller.Cost.ForestZeroDictionary
open Controller.Cost.ForestZeroEmit Controller.Cost.ForestIndexedOperands Controller.Cost.ForestZeroSource
open Controller.Cost.ForestZeroInitialize
variable {width : Nat}

/-- The chosen word capacity depends only on original source counts and the
retained program prefix. No per-query endpoint or descriptor bound is supplied. -/
def coldCapacity (graph : DAG n) (priorSize : Nat) : Nat :=
  priorSize + 97 + 979 * graph.roots.length + 289 * graph.childIncidences +
    44 * graph.guardIncidences + 10 * graph.nodeCount + 4 * n

theorem controlled_heap_size (graph : DAG n) (rows : List Row) (rawRoots : List Nat)
    (rowsMatch : RowsMatch graph rows) (rootsMatch : RootsMatch graph rawRoots) (target : Fin n) :
    (controlledHeap (width := width) graph rows rawRoots target).size =
      6 + 6 * graph.nodeCount + graph.childIncidences + graph.guardIncidences + graph.roots.length +
        2 * (n + graph.nodeCount) := by
  unfold controlledHeap
  rw [reserveHeap_size, Array.size_push, packetHeap_size]
  have incidence := matched_incidence_lengths graph rows rowsMatch
  have rootLength : rawRoots.length = graph.roots.length := by
    have rootsEq : rawRoots = graph.roots.map Fin.val := rootsMatch
    rw [rootsEq, List.length_map]
  rw [rowsMatch.length_eq, incidence.1, incidence.2, rootLength]
  omega

/-- One original-count capacity derives both executable code fit and every
query allocation room, retaining repeated occurrences and signed incidences. -/
theorem cold_capacity_rooms (graph : DAG n) (rows : List Row) (rawRoots : List Nat)
    (rowsMatch : RowsMatch graph rows) (rootsMatch : RootsMatch graph rawRoots) (target : Fin n)
    (forest : graph.FormulaForest) (priorProgram : Program width 8)
    (capacity : coldCapacity graph priorProgram.size < 2 ^ width) :
    (residentProgram (coldPrefix priorProgram) (controlledHeap (width := width) graph rows rawRoots target)
      (controlledLayout (width := width) graph rows rawRoots target) n (Nat.le_add_right _ _)
      (forcedQueries (width := width) graph rows rawRoots rowsMatch target)).size < 2 ^ width ∧
    (controlledHeap (width := width) graph rows rawRoots target).size + 2 * (n + graph.nodeCount) + 14 +
      5 * (5 * graph.roots.length + 3 * graph.childIncidences) +
      15 * (8 * graph.roots.length + 6 * graph.childIncidences + graph.guardIncidences) < 2 ^ width ∧
    13 ≤ 2 ^ width := by
  have lengthBound := forced_resident_length (width := width) graph rows rawRoots rowsMatch target forest
    (controlledHeap (width := width) graph rows rawRoots target)
    (controlledLayout (width := width) graph rows rawRoots target) (coldPrefix priorProgram).size
  have heapSize := controlled_heap_size (width := width) graph rows rawRoots rowsMatch rootsMatch target
  have programSize :
      (residentProgram (coldPrefix priorProgram) (controlledHeap (width := width) graph rows rawRoots target)
        (controlledLayout (width := width) graph rows rawRoots target) n (Nat.le_add_right _ _)
        (forcedQueries (width := width) graph rows rawRoots rowsMatch target)).size =
      priorProgram.size + 75 +
        (residentInstructions (controlledHeap (width := width) graph rows rawRoots target)
          (controlledLayout (width := width) graph rows rawRoots target) n (Nat.le_add_right _ _)
          (coldPrefix priorProgram).size (forcedQueries (width := width) graph rows rawRoots rowsMatch target)).length := by
    unfold residentProgram
    rw [materialize_size, coldPrefix_size]
  unfold coldCapacity at capacity
  refine ⟨?_, ?_, ?_⟩
  · rw [programSize]
    omega
  · rw [heapSize]
    omega
  · omega

/-- The capacity is representable using a logarithmic source-dependent word
width. Generic weight-operation and weight-bit costs remain separate. -/
theorem cold_capacity_log_width (graph : DAG n) (priorSize : Nat) :
    coldCapacity graph priorSize < 2 ^ (Nat.log 2 (coldCapacity graph priorSize) + 1) :=
  Nat.lt_pow_succ_log_self (by decide : 1 < 2) _

end Controller.Cost.ForestZeroSourcePlan

namespace Controller.Cost.ForestZeroSourcePlan
open Controller.Decoder Controller.Decoder.DAG Controller.CNF
open Controller.Cost Controller.Cost.ForestZeroAdmissibleCaller Controller.Cost.ForestIndexedOperands
variable {width : Nat}

/-- Full cold execution needs only one capacity chosen from original source
counts; all program, query, heap and register geometry is derived internally. -/
theorem cold_capacity_execution (graph : DAG n) (guarded : graph.Guarded)
    (rows : List Row) (rawRoots : List Nat) (rowsMatch : RowsMatch graph rows)
    (rootsMatch : RootsMatch graph rawRoots) (target : Fin n) (forest : graph.FormulaForest)
    (priorProgram : Program width 8) (callerRest output : List (Word width))
    (address loaded temporary : Word width) (saved : Fin 8 → Word width)
    (capacity : coldCapacity graph priorProgram.size < 2 ^ width) :
    ∃ answer : Bool, ∃ final ticks peak,
      Execution (residentProgram (coldPrefix priorProgram) (controlledHeap (width := width) graph rows rawRoots target)
        (controlledLayout (width := width) graph rows rawRoots target) n (Nat.le_add_right _ _)
        (forcedQueries (width := width) graph rows rawRoots rowsMatch target)) (coldInitial graph rows rawRoots target priorProgram.size callerRest output address loaded temporary saved) final ticks peak ∧
      final.halted = true ∧ final.reg 4 = word width (if answer then 1 else 0) ∧
      ticks ≤ 63 + 7 * (6 * graph.nodeCount + graph.childIncidences + graph.guardIncidences + graph.roots.length) +
        14 * (n + graph.nodeCount) + 4288 * graph.roots.length + 2772 * graph.childIncidences +
        387 * graph.guardIncidences + 13 * n + 2 ∧
      peak ≤ (coldInitial graph rows rawRoots target priorProgram.size callerRest output address loaded temporary saved).liveWords + 2 * (n + graph.nodeCount) + 146 * graph.roots.length + 105 * graph.childIncidences +
        15 * graph.guardIncidences + 2 * n + 21 ∧
      (answer = true ↔ ∃ position : Fin (forcedQueries (width := width) graph rows rawRoots rowsMatch target).length,
        Satisfiable (constructorFormula (controlledHeap (width := width) graph rows rawRoots target)
          (controlledLayout (width := width) graph rows rawRoots target)
          (ForestZeroCompile.empty (n + graph.nodeCount)) (ForestZeroCompile.empty_coherent _)
          (forcedQueries (width := width) graph rows rawRoots rowsMatch target)[position] n (Nat.le_add_right _ _))) ∧
      (answer = true → ∃ position : Fin (forcedQueries (width := width) graph rows rawRoots rowsMatch target).length,
        Satisfiable (constructorFormula (controlledHeap (width := width) graph rows rawRoots target)
          (controlledLayout (width := width) graph rows rawRoots target)
          (ForestZeroCompile.empty (n + graph.nodeCount)) (ForestZeroCompile.empty_coherent _)
          (forcedQueries (width := width) graph rows rawRoots rowsMatch target)[position] n (Nat.le_add_right _ _)) ∧
        QueryChannelWitness (controlledHeap (width := width) graph rows rawRoots target)
          (controlledLayout (width := width) graph rows rawRoots target)
          (forcedQueries (width := width) graph rows rawRoots rowsMatch target)[position] n (Nat.le_add_right _ _) final.output) := by
  have rooms := cold_capacity_rooms graph rows rawRoots rowsMatch rootsMatch target forest priorProgram capacity
  exact cold_forced_resident_execution graph guarded rows rawRoots rowsMatch rootsMatch target forest
    priorProgram callerRest output address loaded temporary saved rooms.1 rooms.2.1

end Controller.Cost.ForestZeroSourcePlan

namespace Controller.Cost.ForestZeroSourcePlan
open Controller.Decoder Controller.Decoder.DAG Controller.CNF
open Controller.Cost Controller.Cost.ForestIndexedOperands Controller.Cost.ForestZeroRows
open Controller.Cost.ForestZeroAdmissibleCaller Controller.Cost.ForestZeroUnits
open Controller.Cost.ForestZeroEmit

/-- A zero query retains the target unit precisely in the one-bus branch.
Every other bus count uses the original cone query and its negative root unit. -/
def zeroQuery (width : Nat) (graph : DAG n) (rows : List Row) (rawRoots : List Nat)
    (rowsMatch : RowsMatch graph rows) (b : Nat) (position : Fin graph.roots.length)
    (target : Fin n) : List (List (Reference (n + graph.nodeCount))) :=
  if b = 1 then forcedQuery width graph rows rawRoots rowsMatch position target
  else query graph rows rawRoots rowsMatch position

/-- Positions, rather than root labels, identify queries, including repeated roots. -/
def zeroQueries (width : Nat) (graph : DAG n) (rows : List Row) (rawRoots : List Nat)
    (rowsMatch : RowsMatch graph rows) (b : Nat) (target : Fin n) :
    List (List (List (Reference (n + graph.nodeCount)))) :=
  List.ofFn (fun position => zeroQuery width graph rows rawRoots rowsMatch b position target)

@[simp] theorem zeroQuery_one (graph : DAG n) (rows : List Row) (rawRoots : List Nat)
    (rowsMatch : RowsMatch graph rows) (position : Fin graph.roots.length) (target : Fin n) :
    zeroQuery width graph rows rawRoots rowsMatch 1 position target =
      forcedQuery width graph rows rawRoots rowsMatch position target := by
  simp only [zeroQuery, ite_true]

theorem zeroQuery_other (graph : DAG n) (rows : List Row) (rawRoots : List Nat)
    (rowsMatch : RowsMatch graph rows) (other : b ≠ 1) (position : Fin graph.roots.length)
    (target : Fin n) : zeroQuery width graph rows rawRoots rowsMatch b position target =
      query graph rows rawRoots rowsMatch position := by
  simp only [zeroQuery, ite_eq_right other]

@[simp] theorem zeroQueries_length (graph : DAG n) (rows : List Row) (rawRoots : List Nat)
    (rowsMatch : RowsMatch graph rows) (b : Nat) (target : Fin n) :
    (zeroQueries width graph rows rawRoots rowsMatch b target).length = graph.roots.length := by
  simp only [zeroQueries, List.length_ofFn]

theorem zeroQueries_one (graph : DAG n) (rows : List Row) (rawRoots : List Nat)
    (rowsMatch : RowsMatch graph rows) (target : Fin n) :
    zeroQueries width graph rows rawRoots rowsMatch 1 target =
      forcedQueries width graph rows rawRoots rowsMatch target := by
  simp only [zeroQueries, zeroQuery_one, forcedQueries, queries, forcedQuery,
    List.map_ofFn, Function.comp_def]

theorem zeroQueries_other (graph : DAG n) (rows : List Row) (rawRoots : List Nat)
    (rowsMatch : RowsMatch graph rows) (other : b ≠ 1) (target : Fin n) :
    zeroQueries width graph rows rawRoots rowsMatch b target =
      queries graph rows rawRoots rowsMatch := by
  simp only [zeroQueries, zeroQuery_other graph rows rawRoots rowsMatch other, queries]

/-- Both actual syntax branches remain dual-Horn after reserving the optional row. -/
theorem zero_query_dualHorn (graph : DAG n) (guarded : graph.Guarded)
    (rows : List Row) (rawRoots : List Nat) (rowsMatch : RowsMatch graph rows)
    (b : Nat) (position : Fin graph.roots.length) (target : Fin n) :
    Controller.Horn.DualHorn (ofClauses (ForestZeroAssembly.originalRows
      (reservedReferences (zeroQuery width graph rows rawRoots rowsMatch b position target)))) := by
  by_cases one : b = 1
  · subst b
    rw [zeroQuery_one]
    exact forced_query_dualHorn graph guarded rows rawRoots rowsMatch position target
  · rw [zeroQuery_other graph rows rawRoots rowsMatch one]
    exact query_dualHorn graph guarded rows rawRoots rowsMatch position

end Controller.Cost.ForestZeroSourcePlan

namespace Controller.Cost.ForestZeroSourcePlan
open Controller.Decoder Controller.Decoder.DAG Controller.CNF
open Controller.Cost Controller.Cost.ForestZeroEmit Controller.Cost.ForestZeroSource
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestZeroInitialize
open Controller.Cost.ForestZeroAdmissibleCaller Controller.Cost.ForestZeroUnits
variable {width : Nat}

/-- The unforced query uses the same physical loaded packet/trailer and
reusable dictionary region. Only the trailer reference is absent. -/
theorem zero_query_stored (graph : DAG n) (rows : List Row) (rawRoots : List Nat)
    (rowsMatch : RowsMatch graph rows) (rootsMatch : RootsMatch graph rawRoots)
    (b : Nat) (position : Fin graph.roots.length) (target : Fin n) :
    ∀ reference ∈ (zeroQuery width graph rows rawRoots rowsMatch b position target).flatten,
      StoredReference (controlledHeap (width := width) graph rows rawRoots target)
        n ((packetHeap width n rows rawRoots).size + 1) reference := by
  intro reference member
  by_cases one : b = 1
  · subst b
    rw [zeroQuery_one] at member
    exact forced_stream_stored graph rows rawRoots rowsMatch rootsMatch target
      (forcedQuery width graph rows rawRoots rowsMatch position target)
      (by rw [← zeroQueries_one]; exact List.mem_ofFn.mpr ⟨position, zeroQuery_one _ _ _ _ _ _⟩)
      reference member
  · rw [zeroQuery_other graph rows rawRoots rowsMatch one] at member
    obtain ⟨clause, clauseMember, referenceMember⟩ := List.mem_flatten.mp member
    have actual := query_stored (width := width) graph rows rawRoots rowsMatch rootsMatch position
      clause clauseMember reference referenceMember
    let packet := packetHeap width n rows rawRoots
    let loaded := packet.push (word width target.val)
    have loadedSize : loaded.size = packet.size + 1 := by simp only [loaded, Array.size_push]
    have slotOld : reference.slot < packet.size := actual.slotBound
    have headerOld : 0 < packet.size := actual.headerBound
    have slot : reference.slot < loaded.size := by rw [loadedSize]; omega
    have header : 0 < loaded.size := by rw [loadedSize]; omega
    refine ⟨?_, by change reference.slot < packet.size + 1; omega,
      by change 0 < packet.size + 1; omega, ?_, ?_, actual.coordinateEq⟩
    · simp only [controlledHeap, reserveHeap_size, Array.size_push]; omega
    · have pushFrame : loaded[reference.slot]? = packet[reference.slot]? := by
        simp only [loaded, Array.getElem?_push, ite_eq_right (Nat.ne_of_lt slotOld)]
      exact (reserve_source loaded _ reference.slot slot).trans (pushFrame.trans actual.slotWord)
    · have pushFrame : loaded[0]? = packet[0]? := by
        simp only [loaded, Array.getElem?_push, ite_eq_right (Nat.ne_of_lt headerOld)]
      exact (reserve_source loaded _ 0 header).trans (pushFrame.trans actual.channelWord)

theorem zero_stream_stored (graph : DAG n) (rows : List Row) (rawRoots : List Nat)
    (rowsMatch : RowsMatch graph rows) (rootsMatch : RootsMatch graph rawRoots)
    (b : Nat) (target : Fin n) :
    ∀ current ∈ zeroQueries width graph rows rawRoots rowsMatch b target,
      ∀ reference ∈ current.flatten,
      StoredReference (controlledHeap (width := width) graph rows rawRoots target)
        n ((packetHeap width n rows rawRoots).size + 1) reference := by
  intro current member
  obtain ⟨position, same⟩ := List.mem_ofFn.mp member
  subst current
  exact zero_query_stored graph rows rawRoots rowsMatch rootsMatch b position target

theorem zero_stream_dualHorn (graph : DAG n) (guarded : graph.Guarded)
    (rows : List Row) (rawRoots : List Nat) (rowsMatch : RowsMatch graph rows)
    (b : Nat) (target : Fin n) :
    ∀ current ∈ zeroQueries width graph rows rawRoots rowsMatch b target,
      Controller.Horn.DualHorn (ofClauses (ForestZeroAssembly.originalRows
        (reservedReferences current))) := by
  intro current member
  obtain ⟨position, same⟩ := List.mem_ofFn.mp member
  subst current
  exact zero_query_dualHorn graph guarded rows rawRoots rowsMatch b position target

end Controller.Cost.ForestZeroSourcePlan
namespace Controller.Cost.ForestZeroSourcePlan
open Controller.Decoder Controller.Decoder.DAG Controller.CNF
open Controller.Cost Controller.Cost.ForestZeroEmit Controller.Cost.ForestZeroSource
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestZeroInitialize
open Controller.Cost.ForestZeroAdmissibleCaller Controller.Cost.ForestZeroUnits
open Controller.Cost.GateProgram Controller.Cost.ForestZeroDictionary Controller.Cost.ForestZeroResident
open Controller.Cost.ForestZeroCallerWiden Controller.Cost.ForestZeroTouch
variable {width : Nat}

theorem zero_queries_forest_bounds (graph : DAG n) (rows : List Row) (rawRoots : List Nat)
    (rowsMatch : RowsMatch graph rows) (b : Nat) (target : Fin n) (forest : graph.FormulaForest) :
    ((zeroQueries width graph rows rawRoots rowsMatch b target).map List.length).sum ≤
      5 * graph.roots.length + 3 * graph.childIncidences ∧
    ((zeroQueries width graph rows rawRoots rowsMatch b target).map fun clauses => clauses.flatten.length).sum ≤
      8 * graph.roots.length + 6 * graph.childIncidences + graph.guardIncidences := by
  by_cases one : b = 1
  · subst b
    rw [zeroQueries_one]
    exact forced_queries_forest_bounds graph rows rawRoots rowsMatch target forest
  · rw [zeroQueries_other graph rows rawRoots rowsMatch one]
    have bounds := queries_forest_bounds graph rows rawRoots rowsMatch forest
    constructor <;> omega


theorem zero_query_component_bounds (graph : DAG n) (rows : List Row) (rawRoots : List Nat)
    (rowsMatch : RowsMatch graph rows) (b : Nat) (target : Fin n) (forest : graph.FormulaForest)
    (position : Fin (zeroQueries width graph rows rawRoots rowsMatch b target).length) :
    (zeroQueries width graph rows rawRoots rowsMatch b target)[position].length ≤
      5 * graph.roots.length + 3 * graph.childIncidences ∧
    (zeroQueries width graph rows rawRoots rowsMatch b target)[position].flatten.length ≤
      8 * graph.roots.length + 6 * graph.childIncidences + graph.guardIncidences := by
  let stream := zeroQueries width graph rows rawRoots rowsMatch b target
  have rowMember : stream[position].length ∈ stream.map List.length :=
    List.mem_map.mpr ⟨stream[position], List.getElem_mem position.isLt, rfl⟩
  have literalMember : stream[position].flatten.length ∈ stream.map (fun query => query.flatten.length) :=
    List.mem_map.mpr ⟨stream[position], List.getElem_mem position.isLt, rfl⟩
  have memberSum : ∀ (values : List Nat) (value : Nat), value ∈ values → value ≤ values.sum := by
    intro values value present
    induction values with
    | nil => cases present
    | cons head tail ih =>
      rcases List.mem_cons.mp present with same | tailMember
      · subst value
        simp only [List.sum_cons]
        omega
      · have tailBound := ih tailMember
        simp only [List.sum_cons]
        omega
  have row := memberSum _ _ rowMember
  have literals := memberSum _ _ literalMember
  have totals := zero_queries_forest_bounds (width := width) graph rows rawRoots rowsMatch b target forest
  exact ⟨row.trans totals.1, literals.trans totals.2⟩



theorem zero_query_word_rooms (graph : DAG n) (rows : List Row) (rawRoots : List Nat)
    (rowsMatch : RowsMatch graph rows) (b : Nat) (target : Fin n) (forest : graph.FormulaForest)
    (heap : Array (Word width))
    (room : heap.size + 2 * (n + graph.nodeCount) + 14 +
      5 * (5 * graph.roots.length + 3 * graph.childIncidences) +
      15 * (8 * graph.roots.length + 6 * graph.childIncidences + graph.guardIncidences) < 2 ^ width) :
    ∀ position : Fin (zeroQueries width graph rows rawRoots rowsMatch b target).length,
      heap.size + 2 * (n + graph.nodeCount) + 14 +
        5 * (zeroQueries width graph rows rawRoots rowsMatch b target)[position].length +
        15 * (zeroQueries width graph rows rawRoots rowsMatch b target)[position].flatten.length < 2 ^ width := by
  intro position
  have localCounts := zero_query_component_bounds (width := width) graph rows rawRoots rowsMatch b target forest position
  omega



theorem zero_resident_execution (graph : DAG n) (guarded : graph.Guarded)
    (rows : List Row) (rawRoots : List Nat) (rowsMatch : RowsMatch graph rows)
    (rootsMatch : RootsMatch graph rawRoots) (b : Nat) (target : Fin n) (forest : graph.FormulaForest)
    (priorProgram : Program width 8) (callerRest : List (Word width)) (initial : State width 8)
    (programRoom :
      (residentProgram priorProgram (controlledHeap (width := width) graph rows rawRoots target)
        (controlledLayout (width := width) graph rows rawRoots target) n (Nat.le_add_right _ _)
        (zeroQueries width graph rows rawRoots rowsMatch b target)).size < 2 ^ width)
    (wordRoom : (controlledHeap (width := width) graph rows rawRoots target).size + 2 * (n + graph.nodeCount) + 14 +
      5 * (5 * graph.roots.length + 3 * graph.childIncidences) +
      15 * (8 * graph.roots.length + 6 * graph.childIncidences + graph.guardIncidences) < 2 ^ width)
    (initialReady : QueryReady (ambient := n + graph.nodeCount)
      (controlledHeap (width := width) graph rows rawRoots target)
      (controlledLayout (width := width) graph rows rawRoots target).tableBase
      (controlledLayout (width := width) graph rows rawRoots target).inverseBase
      (occurrenceResume priorProgram (controlledHeap (width := width) graph rows rawRoots target)
        (controlledLayout (width := width) graph rows rawRoots target) n (Nat.le_add_right _ _)
        (zeroQueries width graph rows rawRoots rowsMatch b target)
        (List.finRange (zeroQueries width graph rows rawRoots rowsMatch b target).length)) callerRest initial) :
    ∃ answer : Bool, ∃ final ticks peak,
      Execution (residentProgram priorProgram (controlledHeap (width := width) graph rows rawRoots target)
        (controlledLayout (width := width) graph rows rawRoots target) n (Nat.le_add_right _ _)
        (zeroQueries width graph rows rawRoots rowsMatch b target)) initial final ticks peak ∧
      final.halted = true ∧ final.reg 4 = word width (if answer then 1 else 0) ∧
      ticks ≤ 4288 * graph.roots.length + 2772 * graph.childIncidences +
        387 * graph.guardIncidences + 13 * n + 2 ∧
      peak ≤ initial.liveWords + 146 * graph.roots.length + 105 * graph.childIncidences +
        15 * graph.guardIncidences + 2 * n + 21 ∧
      (answer = true ↔ ∃ position : Fin (zeroQueries width graph rows rawRoots rowsMatch b target).length,
        Satisfiable (constructorFormula (controlledHeap (width := width) graph rows rawRoots target)
          (controlledLayout (width := width) graph rows rawRoots target)
          (ForestZeroCompile.empty (n + graph.nodeCount)) (ForestZeroCompile.empty_coherent _)
          (zeroQueries width graph rows rawRoots rowsMatch b target)[position] n (Nat.le_add_right _ _))) ∧
      (answer = true → ∃ position : Fin (zeroQueries width graph rows rawRoots rowsMatch b target).length,
        Satisfiable (constructorFormula (controlledHeap (width := width) graph rows rawRoots target)
          (controlledLayout (width := width) graph rows rawRoots target)
          (ForestZeroCompile.empty (n + graph.nodeCount)) (ForestZeroCompile.empty_coherent _)
          (zeroQueries width graph rows rawRoots rowsMatch b target)[position] n (Nat.le_add_right _ _)) ∧
        QueryChannelWitness (controlledHeap (width := width) graph rows rawRoots target)
          (controlledLayout (width := width) graph rows rawRoots target)
          (zeroQueries width graph rows rawRoots rowsMatch b target)[position] n (Nat.le_add_right _ _) final.output) := by
  let heap := controlledHeap (width := width) graph rows rawRoots target
  let layout := controlledLayout (width := width) graph rows rawRoots target
  let stream := zeroQueries width graph rows rawRoots rowsMatch b target
  let sourceEnd := (packetHeap width n rows rawRoots).size + 1
  have geometry := controlled_geometry (width := width) graph rows rawRoots target
  have headers := controlled_headers (width := width) graph rows rawRoots rowsMatch target
  have stored : ∀ position : Fin stream.length, ∀ reference ∈ stream[position].flatten,
      StoredReference heap n sourceEnd reference := by
    intro position
    exact zero_stream_stored (width := width) graph rows rawRoots rowsMatch rootsMatch b target
      stream[position] (List.getElem_mem position.isLt)
  have grammar : ∀ position : Fin stream.length,
      Controller.Horn.DualHorn (ofClauses (ForestZeroAssembly.originalRows (reservedReferences stream[position]))) := by
    intro position
    exact zero_stream_dualHorn (width := width) graph guarded rows rawRoots rowsMatch b target
      stream[position] (List.getElem_mem position.isLt)
  have perRoom := zero_query_word_rooms (width := width) graph rows rawRoots rowsMatch b target forest heap wordRoom
  let scratch := 145 * graph.roots.length + 105 * graph.childIncidences + 15 * graph.guardIncidences + n + 20
  have scratchBound : ∀ position : Fin stream.length,
      5 * stream[position].length + 15 * stream[position].flatten.length + n + 20 ≤ scratch := by
    intro position
    have localCounts := zero_query_component_bounds (width := width) graph rows rawRoots rowsMatch b target forest position
    change stream[position].length ≤ _ ∧ stream[position].flatten.length ≤ _ at localCounts
    dsimp only [scratch]
    omega
  obtain ⟨answer, final, ticks, peak, trace, halted, tag, timeBound, peakBound, meaning, model⟩ :=
    resident_first_success_execution priorProgram heap layout stream n sourceEnd graph.nodeCount
      (Nat.le_add_right _ _) callerRest stored geometry.1.le geometry.2.1 geometry.2.2.1 geometry.2.2.2.1
      headers.1 headers.2 rfl geometry.2.2.2.2.1 geometry.2.2.2.2.2 grammar programRoom perRoom
      scratch scratchBound initial initialReady
  have totals := zero_queries_forest_bounds (width := width) graph rows rawRoots rowsMatch b target forest
  have streamLength : stream.length = graph.roots.length := zeroQueries_length (width := width) graph rows rawRoots rowsMatch b target
  change (stream.map List.length).sum ≤ _ ∧
    (stream.map fun refs => refs.flatten.length).sum ≤ _ at totals
  rw [streamLength] at timeBound peakBound
  refine ⟨answer, final, ticks, peak, trace, halted, tag, ?_, ?_, meaning, model⟩
  · omega
  · dsimp only [scratch] at peakBound
    omega



theorem cold_zero_ready_execution (graph : DAG n) (rows : List Row) (rawRoots : List Nat)
    (rowsMatch : RowsMatch graph rows) (rootsMatch : RootsMatch graph rawRoots) (b : Nat) (target : Fin n)
    (priorProgram : Program width 8) (rest output : List (Word width))
    (address loaded temporary : Word width) (saved : Fin 8 → Word width)
    (programRoom :
      (residentProgram (coldPrefix priorProgram) (controlledHeap (width := width) graph rows rawRoots target)
        (controlledLayout (width := width) graph rows rawRoots target) n (Nat.le_add_right _ _)
        (zeroQueries width graph rows rawRoots rowsMatch b target)).size < 2 ^ width)
    (room : (controlledHeap (width := width) graph rows rawRoots target).size < 2 ^ width) :
    ∃ ready,
      Execution (residentProgram (coldPrefix priorProgram) (controlledHeap (width := width) graph rows rawRoots target)
        (controlledLayout (width := width) graph rows rawRoots target) n (Nat.le_add_right _ _)
        (zeroQueries width graph rows rawRoots rowsMatch b target))
        (coldInitial graph rows rawRoots target priorProgram.size rest output address loaded temporary saved)
        ready (63 + 7 * (6 * graph.nodeCount + graph.childIncidences + graph.guardIncidences + graph.roots.length) +
          14 * (n + graph.nodeCount))
        (16 + (6 * graph.nodeCount + graph.childIncidences + graph.guardIncidences + graph.roots.length) +
          2 * (n + graph.nodeCount) + rest.length + output.length) ∧
      QueryReady (ambient := n + graph.nodeCount)
        (controlledHeap (width := width) graph rows rawRoots target)
        (controlledLayout (width := width) graph rows rawRoots target).tableBase
        (controlledLayout (width := width) graph rows rawRoots target).inverseBase
        (occurrenceResume (coldPrefix priorProgram) (controlledHeap (width := width) graph rows rawRoots target)
          (controlledLayout (width := width) graph rows rawRoots target) n (Nat.le_add_right _ _)
          (zeroQueries width graph rows rawRoots rowsMatch b target)
          (List.finRange (zeroQueries width graph rows rawRoots rowsMatch b target).length)) rest ready ∧
      ready.liveWords =
        (coldInitial graph rows rawRoots target priorProgram.size rest output address loaded temporary saved).liveWords +
          2 * (n + graph.nodeCount) := by
  let payload := (serializedRows 5 rows rawRoots).map (word width)
  let heap := controlledHeap (width := width) graph rows rawRoots target
  let layout := controlledLayout (width := width) graph rows rawRoots target
  let queries := zeroQueries width graph rows rawRoots rowsMatch b target
  let program := residentProgram (coldPrefix priorProgram) heap layout n (Nat.le_add_right _ _) queries
  have lengthEq := cold_payload_length (width := width) graph rows rawRoots rowsMatch rootsMatch
  change payload.length = 6 * graph.nodeCount + graph.childIncidences + graph.guardIncidences + graph.roots.length at lengthEq
  have packetEq := cold_packet_source (width := width) graph rows rawRoots rowsMatch rootsMatch
  have prefixBound : priorProgram.size + 75 ≤ program.size := by
    unfold program residentProgram
    rw [materialize_size, coldPrefix_size]
    omega
  have dataRoom : 6 + payload.length + 2 * (n + graph.nodeCount) < 2 ^ width := by
    change (reserveHeap ((packetHeap width n rows rawRoots).push (word width target.val))
      (n + graph.nodeCount)).size < 2 ^ width at room
    have packetSize : (packetHeap width n rows rawRoots).size = 5 + payload.length := by
      have exactSize := packetHeap_size width n rows rawRoots
      have payloadSize := serializedRows_length 5 rows rawRoots
      simp only [payload, List.length_map]
      omega
    rw [reserveHeap_size, Array.size_push, packetSize] at room
    omega
  have boot := cold_bootstrap_execution program priorProgram.size n graph.nodeCount graph.childIncidences
    graph.guardIncidences graph.roots.length payload rest output target address loaded temporary saved
    lengthEq dataRoom (lt_of_le_of_lt prefixBound programRoom)
    (resident_cold_fetch priorProgram heap layout n (Nat.le_add_right _ _) queries)
  dsimp only at boot
  rw [packetEq] at boot
  let ready := RegisterWiden.widenState
    (atState heap (priorProgram.size + 75) 0 (6 + payload.length)
      (6 + payload.length + n + graph.nodeCount) 0 rest output) saved
  have initialEq : RegisterWiden.widenState
      ((ForestCounter.counterState (#[] : Array (Word width)) priorProgram.size address loaded temporary).frame
        (ForestInputMetadata.headerWords width n graph.nodeCount graph.childIncidences graph.guardIncidences
          graph.roots.length ++ payload ++ (word width target.val :: rest)) output) saved =
      coldInitial graph rows rawRoots target priorProgram.size rest output address loaded temporary saved := by
    rw [coldInitial, matched_cold_input_words (width := width) graph rows rawRoots rowsMatch rootsMatch]
    rfl
  have entryEq : occurrenceResume (coldPrefix priorProgram) heap layout n (Nat.le_add_right _ _) queries
      (List.finRange queries.length) = priorProgram.size + 75 := by
    simp only [occurrenceResume, List.length_finRange, Nat.sub_self, occurrenceEntry,
      List.take_zero, residentPrefix, coldPrefix_size]
  refine ⟨ready, ?_, ?_, ?_⟩
  · have trace := boot.1
    rw [initialEq] at trace
    simpa only [ready, lengthEq, heap, controlledHeap, program, layout, queries] using trace
  · rw [entryEq]
    exact boot.2
  · have inputSize : (inputPacket n 0 rows rawRoots).length = 5 + payload.length := by
      simp only [inputPacket, List.length_append, globalHeader_length, payload, List.length_map, Nat.zero_add]
    have heapSize : heap.size = 6 + payload.length + 2 * (n + graph.nodeCount) := by
      change (reserveHeap ((packetHeap width n rows rawRoots).push (word width target.val))
        (n + graph.nodeCount)).size = _
      rw [reserveHeap_size, Array.size_push, packetHeap_size]
      have payloadSize := serializedRows_length 5 rows rawRoots
      simp only [payload, List.length_map]
      omega
    have initialLive :
        (coldInitial graph rows rawRoots target priorProgram.size rest output address loaded temporary saved).liveWords =
          15 + payload.length + rest.length + output.length := by
      simp only [coldInitial, RegisterWiden.widenState_liveWords, State.frame_liveWords,
        ForestCounter.counterState_liveWords, List.length_append, List.length_cons,
        List.length_map, Array.size_empty]
      rw [inputSize]
      omega
    have readyLive : ready.liveWords = 15 + payload.length + 2 * (n + graph.nodeCount) +
        rest.length + output.length := by
      simp only [ready, RegisterWiden.widenState_liveWords, atState_liveWords, heapSize]
      omega
    rw [initialLive, readyLive]
    omega



theorem cold_zero_resident_execution (graph : DAG n) (guarded : graph.Guarded)
    (rows : List Row) (rawRoots : List Nat) (rowsMatch : RowsMatch graph rows)
    (rootsMatch : RootsMatch graph rawRoots) (b : Nat) (target : Fin n) (forest : graph.FormulaForest)
    (priorProgram : Program width 8) (callerRest output : List (Word width))
    (address loaded temporary : Word width) (saved : Fin 8 → Word width)
    (programRoom :
      (residentProgram (coldPrefix priorProgram) (controlledHeap (width := width) graph rows rawRoots target)
        (controlledLayout (width := width) graph rows rawRoots target) n (Nat.le_add_right _ _)
        (zeroQueries width graph rows rawRoots rowsMatch b target)).size < 2 ^ width)
    (wordRoom : (controlledHeap (width := width) graph rows rawRoots target).size + 2 * (n + graph.nodeCount) + 14 +
      5 * (5 * graph.roots.length + 3 * graph.childIncidences) +
      15 * (8 * graph.roots.length + 6 * graph.childIncidences + graph.guardIncidences) < 2 ^ width) :
    ∃ answer : Bool, ∃ final ticks peak,
      Execution (residentProgram (coldPrefix priorProgram) (controlledHeap (width := width) graph rows rawRoots target)
        (controlledLayout (width := width) graph rows rawRoots target) n (Nat.le_add_right _ _)
        (zeroQueries width graph rows rawRoots rowsMatch b target)) (coldInitial graph rows rawRoots target priorProgram.size callerRest output address loaded temporary saved) final ticks peak ∧
      final.halted = true ∧ final.reg 4 = word width (if answer then 1 else 0) ∧
      ticks ≤ 63 + 7 * (6 * graph.nodeCount + graph.childIncidences + graph.guardIncidences + graph.roots.length) +
        14 * (n + graph.nodeCount) + 4288 * graph.roots.length + 2772 * graph.childIncidences +
        387 * graph.guardIncidences + 13 * n + 2 ∧
      peak ≤ (coldInitial graph rows rawRoots target priorProgram.size callerRest output address loaded temporary saved).liveWords + 2 * (n + graph.nodeCount) + 146 * graph.roots.length + 105 * graph.childIncidences +
        15 * graph.guardIncidences + 2 * n + 21 ∧
      (answer = true ↔ ∃ position : Fin (zeroQueries width graph rows rawRoots rowsMatch b target).length,
        Satisfiable (constructorFormula (controlledHeap (width := width) graph rows rawRoots target)
          (controlledLayout (width := width) graph rows rawRoots target)
          (ForestZeroCompile.empty (n + graph.nodeCount)) (ForestZeroCompile.empty_coherent _)
          (zeroQueries width graph rows rawRoots rowsMatch b target)[position] n (Nat.le_add_right _ _))) ∧
      (answer = true → ∃ position : Fin (zeroQueries width graph rows rawRoots rowsMatch b target).length,
        Satisfiable (constructorFormula (controlledHeap (width := width) graph rows rawRoots target)
          (controlledLayout (width := width) graph rows rawRoots target)
          (ForestZeroCompile.empty (n + graph.nodeCount)) (ForestZeroCompile.empty_coherent _)
          (zeroQueries width graph rows rawRoots rowsMatch b target)[position] n (Nat.le_add_right _ _)) ∧
        QueryChannelWitness (controlledHeap (width := width) graph rows rawRoots target)
          (controlledLayout (width := width) graph rows rawRoots target)
          (zeroQueries width graph rows rawRoots rowsMatch b target)[position] n (Nat.le_add_right _ _) final.output) := by
  have loadRoom : (controlledHeap (width := width) graph rows rawRoots target).size < 2 ^ width := by
    omega
  obtain ⟨ready, loadTrace, initialReady, readyLive⟩ :=
    cold_zero_ready_execution graph rows rawRoots rowsMatch rootsMatch b target priorProgram callerRest output
      address loaded temporary saved programRoom loadRoom
  obtain ⟨answer, final, queryTicks, queryPeak, queried, halted, tag, queryTime, querySpace, meaning, model⟩ :=
    zero_resident_execution graph guarded rows rawRoots rowsMatch rootsMatch b target forest
      (coldPrefix priorProgram) callerRest ready programRoom wordRoom initialReady
  have allTrace := loadTrace.append queried
  let loadTicks := 63 + 7 * (6 * graph.nodeCount + graph.childIncidences + graph.guardIncidences + graph.roots.length) +
    14 * (n + graph.nodeCount)
  let loadPeak := 16 + (6 * graph.nodeCount + graph.childIncidences + graph.guardIncidences + graph.roots.length) +
    2 * (n + graph.nodeCount) + callerRest.length + output.length
  refine ⟨answer, final, loadTicks + queryTicks, max loadPeak queryPeak,
    allTrace, halted, tag, ?_, ?_, meaning, model⟩
  · dsimp only [loadTicks]
    omega
  · have inputSize := matched_input_packet_length 0 graph rows rawRoots rowsMatch rootsMatch
    have coldSize := coldInitial_liveWords graph rows rawRoots target priorProgram.size callerRest output
      address loaded temporary saved
    rw [readyLive] at querySpace
    apply max_le
    · dsimp only [loadPeak]
      omega
    · exact querySpace


end Controller.Cost.ForestZeroSourcePlan
