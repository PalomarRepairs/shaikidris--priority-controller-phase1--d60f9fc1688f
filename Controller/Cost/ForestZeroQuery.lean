module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestZeroRows
public import Controller.Cost.ForestZeroInitialize
public import Controller.Cost.ForestNodeVisits
public import Controller.Horn.SourceDirectory
public import Controller.Cost.ForestZeroBackendFrame

public import Mathlib.Tactic.FinCases

@[expose] public section

/-! Cone-local source production uses original indexed rows and descending
original child identifiers. Its accumulator retains repeated terminal visits,
clause order and every signed occurrence. Query control cells are appended
above the protected source/dictionary prefix. The indexed packet-to-row access
and complete fetched construction have separate explicit refinement contracts.
-/
namespace Controller.Cost.ForestZeroQuery
open Controller.Decoder Controller.Decoder.DAG Controller.CNF
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestZeroRows
open Controller.Cost.GateProgram
open Controller.Cost.ForestZeroTouch

/-- Original row-array correspondence retains all repeated child occurrences. -/
abbrev SourceMatches (graph : DAG n) (rows : Array Row) := RowsMatch graph rows.toList

def sourceRow (graph : DAG n) (rows : Array Row) (corresponds : SourceMatches graph rows)
    (owner : Fin graph.nodeCount) : Row :=
  rows[owner.val]'(by have size := corresponds.length_eq; simp only [Array.length_toList] at size; omega)

theorem sourceRow_matches (graph : DAG n) (rows : Array Row)
    (corresponds : SourceMatches graph rows) (owner : Fin graph.nodeCount) :
    (sourceRow graph rows corresponds owner).Matches (graph.node owner) := by
  simpa only [sourceRow, Array.getElem_toList] using corresponds.node owner

theorem sourceRow_children (graph : DAG n) (rows : Array Row)
    (corresponds : SourceMatches graph rows) (owner : Fin graph.nodeCount) :
    (sourceRow graph rows corresponds owner).children = (graph.node owner).children.map Fin.val :=
  (sourceRow_matches graph rows corresponds owner).2.2.1

/-- The runtime branch validates each original child ID before descent. The
well-founded proof is erased; it does not perform a typed graph-node lookup. -/
def emitCone (graph : DAG n) (rows : Array Row) (corresponds : SourceMatches graph rows)
    (owner : Fin graph.nodeCount) (tail : List (Clause ℕ)) : List (Clause ℕ) :=
  let row := sourceRow graph rows corresponds owner
  let descendants := row.children.foldr (fun child acc =>
    if earlier : child < owner.val then
      emitCone graph rows corresponds ⟨child, Nat.lt_trans earlier owner.isLt⟩ acc
    else acc) tail
  rowClauses n owner.val row ++ descendants
termination_by owner.val
decreasing_by all_goals omega

/-- This list is a ghost correspondence target, not a runtime graph accessor. -/
def typedCone (graph : DAG n) (owner : Fin graph.nodeCount)
    (tail : List (Clause ℕ)) : List (Clause ℕ) :=
  (graph.nodeClauses owner).map (List.map (sourceLiteral graph)) ++
    (graph.node owner).children.foldr (fun child acc =>
      typedCone graph (graph.childIndex owner child) acc) tail
termination_by owner.val
decreasing_by exact graph.childIndex_lt _ _

/-- The executable raw-array descent produces the exact original cone rows.
Repeated endpoints remain repeated visits, rather than being silently deduped. -/
theorem emitCone_exact (graph : DAG n) (rows : Array Row)
    (corresponds : SourceMatches graph rows) :
    ∀ owner tail, emitCone graph rows corresponds owner tail = typedCone graph owner tail := by
  have claim : ∀ rank : ℕ, ∀ owner : Fin graph.nodeCount, owner.val = rank →
      ∀ tail, emitCone graph rows corresponds owner tail = typedCone graph owner tail := by
    intro rank
    induction rank using Nat.strong_induction_on with
    | h rank ih =>
      intro owner ownerEq tail
      rw [emitCone.eq_def, typedCone.eq_def]
      dsimp only
      rw [rowClauses_exact graph owner _ (sourceRow_matches graph rows corresponds owner),
        sourceRow_children graph rows corresponds owner]
      congr 1
      rw [List.foldr_map]
      apply congrArg (fun step : Fin owner.val → List (Clause ℕ) → List (Clause ℕ) =>
        (graph.node owner).children.foldr step tail)
      funext child acc
      simp only [dite_eq_left child.isLt]
      exact ih (graph.childIndex owner child).val (by simpa only [ownerEq] using graph.childIndex_lt owner child) _ rfl acc
  intro owner tail
  exact claim owner.val owner rfl tail

/-- A physical source count scans every row and literal occurrence once. -/
def countClause : Clause α → ℕ
  | [] => 0
  | _ :: rest => countClause rest + 1

def countRows : List (Clause α) → ℕ × ℕ
  | [] => (0, 0)
  | row :: rest =>
      let counted := countRows rest
      (counted.1 + 1, countClause row + counted.2)

inductive ClauseCount : Clause α → ℕ → Prop
  | nil : ClauseCount [] 0
  | cons (literal : Literal α) (rest : Clause α) (count : ℕ)
      (tail : ClauseCount rest count) : ClauseCount (literal :: rest) (count + 1)

inductive RowsCount : List (Clause α) → ℕ → ℕ → Prop
  | nil : RowsCount [] 0 0
  | cons (row : Clause α) (rest : List (Clause α)) (rows literals localCount : ℕ)
      (localTrace : ClauseCount row localCount) (tail : RowsCount rest rows literals) :
      RowsCount (row :: rest) (rows + 1) (localCount + literals)

theorem countClause_trace (row : Clause α) : ClauseCount row (countClause row) := by
  induction row with
  | nil => exact ClauseCount.nil
  | cons literal rest ih => exact ClauseCount.cons literal rest _ ih

theorem countRows_trace (rows : List (Clause α)) :
    RowsCount rows (countRows rows).1 (countRows rows).2 := by
  induction rows with
  | nil => exact RowsCount.nil
  | cons row rest ih => exact RowsCount.cons row rest _ _ _ (countClause_trace row) ih

theorem countClause_exact (row : Clause α) : countClause row = row.length := by
  induction row <;> simp_all [countClause]

theorem countRows_exact (rows : List (Clause α)) :
    (countRows rows).1 = rows.length ∧ (countRows rows).2 = (rows.map List.length).sum := by
  induction rows with
  | nil => simp [countRows]
  | cons row rest ih => simp [countRows, countClause_exact, ih, Nat.add_comm]

/-- The running cursor advances exactly twice per original occurrence. This
recurrence never recomputes a take-prefix sum for each directory entry. -/
def directoryValues (cursor : ℕ) : List (Clause α) → List ℕ
  | [] => []
  | row :: rest => cursor :: (cursor + 2 * countClause row) ::
      directoryValues (cursor + 2 * countClause row) rest

@[simp] theorem directoryValues_length (cursor : ℕ) (rows : List (Clause α)) :
    (directoryValues cursor rows).length = 2 * rows.length := by
  induction rows generalizing cursor <;> simp_all [directoryValues] <;> omega

/-- All mutable query headers lie above the complete protected prefix. -/
def layout (protectedEnd : ℕ) (clauses : List (Clause (Fin locals))) :
    Controller.Horn.SourceDirectory.Layout clauses where
  recordHeader := protectedEnd
  inputHeader := protectedEnd + 1
  firstHeader := protectedEnd + 2
  directoryHeader := protectedEnd + 3
  endHeader := protectedEnd + 4
  directory := protectedEnd + 5
  source := protectedEnd + 5 + 2 * clauses.length
  base := protectedEnd + 5 + 2 * clauses.length + 2 * (clauses.map List.length).sum
  directoryBefore := by omega
  sourceBefore := by simp [Controller.Horn.SourceDirectory.sourceOffset]
  headersBefore := by
    intro header member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> omega
  headersDistinct := by simp

theorem headers_protectedEnd (protectedEnd : ℕ) (clauses : List (Clause (Fin locals))) :
    ∀ header ∈ [(layout protectedEnd clauses).recordHeader, (layout protectedEnd clauses).inputHeader,
      (layout protectedEnd clauses).firstHeader, (layout protectedEnd clauses).directoryHeader,
      (layout protectedEnd clauses).endHeader], protectedEnd ≤ header := by
  intro header member
  simp only [layout, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl <;> omega

/-- The concrete appended query layout satisfies the reusable hot-backend
header-separation contract without changing protected source cells. -/
def reusableLayout (protectedEnd : ℕ) (clauses : List (Clause (Fin locals))) :
    Controller.Cost.ForestZeroBackendFrame.ReusableLayout clauses protectedEnd where
  toLayout := layout protectedEnd clauses
  headersAbove := headers_protectedEnd protectedEnd clauses

/-- The exact allocation count is obtained from the executable row count. -/
theorem query_size_from_count (protectedEnd : ℕ) (clauses : List (Clause (Fin locals))) :
    (layout protectedEnd clauses).base =
      protectedEnd + 5 + 2 * (countRows clauses).1 + 2 * (countRows clauses).2 := by
  have counts := countRows_exact clauses
  simp only [layout, counts.1, counts.2]

/-- The boundary loop consumes a physically counted row length in register
 two. Both boundary pointers are formed by fetched instructions, rather than
 supplied as a directory backing array. -/
def boundaryCode (width : ℕ) : Code width :=
  [.allocate 0, .add 2 2 2, .add 0 0 2, .allocate 0]

@[simp] theorem boundaryCode_length : (boundaryCode width).length = 4 := rfl

private theorem fetched (program : Program width 4) (state : State width 4)
    (cursor : ℕ) (instruction : Instruction width 4)
    (pc : state.pc = word width cursor) (fits : cursor < 2 ^ width)
    (entry : program[cursor]? = some instruction) :
    programStep program state = step instruction state := by
  unfold programStep
  rw [pc, show (word width cursor).val = cursor from Nat.mod_eq_of_lt fits, entry]
  rfl

private theorem advance_at (heap : Array (Word width)) (cursor x0 x1 x2 x3 : ℕ)
    (stack output : List (Word width)) (fits : cursor < 2 ^ width) :
    (atState heap cursor x0 x1 x2 x3 stack output).advance =
      atState heap (cursor + 1) x0 x1 x2 x3 stack output := by
  simp [atState, State.advance, show (word width cursor).val = cursor from Nat.mod_eq_of_lt fits]

private theorem put0_at (heap : Array (Word width)) (cursor x0 x1 x2 x3 value : ℕ)
    (stack output : List (Word width)) :
    (atState heap cursor x0 x1 x2 x3 stack output).put 0 (word width value) =
      atState heap cursor value x1 x2 x3 stack output := by
  unfold atState State.put
  congr 1
  funext register
  fin_cases register <;> rfl

private theorem put2_at (heap : Array (Word width)) (cursor x0 x1 x2 x3 value : ℕ)
    (stack output : List (Word width)) :
    (atState heap cursor x0 x1 x2 x3 stack output).put 2 (word width value) =
      atState heap cursor x0 x1 value x3 stack output := by
  unfold atState State.put
  congr 1
  funext register
  fin_cases register <;> rfl

/-- Four actual instructions allocate both row endpoints, advance the running
source cursor and preserve the protected heap prefix and caller lists. -/
theorem boundary_execution (program : Program width 4) (heap : Array (Word width))
    (base cursor tableBase literals scratch : ℕ) (stack output : List (Word width))
    (room : heap.size + 2 ≤ 2 ^ width) (pointerFits : cursor + 2 * literals < 2 ^ width)
    (programFits : base + 4 < 2 ^ width)
    (block : BlockAt program base (boundaryCode width)) :
    Execution program (atState heap base cursor tableBase literals scratch stack output)
      (atState ((heap.push (word width cursor)).push (word width (cursor + 2 * literals)))
        (base + 4) (cursor + 2 * literals) tableBase (2 * literals) scratch stack output)
      4 (7 + heap.size + stack.length + output.length) := by
  let s0 := atState heap base cursor tableBase literals scratch stack output
  let firstHeap := heap.push (word width cursor)
  let s1 := atState firstHeap (base + 1) cursor tableBase literals scratch stack output
  let s2 := atState firstHeap (base + 2) cursor tableBase (2 * literals) scratch stack output
  let s3 := atState firstHeap (base + 3) (cursor + 2 * literals) tableBase (2 * literals) scratch stack output
  let s4 := atState (firstHeap.push (word width (cursor + 2 * literals)))
    (base + 4) (cursor + 2 * literals) tableBase (2 * literals) scratch stack output
  have cursorValue : (word width cursor).val = cursor := Nat.mod_eq_of_lt (by omega)
  have countValue : (word width literals).val = literals := Nat.mod_eq_of_lt (by omega)
  have doubledValue : (word width (2 * literals)).val = 2 * literals := Nat.mod_eq_of_lt (by omega)
  have t0 : programStep program s0 = some s1 := by
    rw [fetched program s0 base (.allocate 0) rfl (by omega)
      (by simpa [boundaryCode] using block 0 (by simp [boundaryCode]))]
    change (if heap.size < 2 ^ width then some { s0.advance with heap := firstHeap } else none) = some s1
    rw [ite_eq_left (by omega), advance_at _ _ _ _ _ _ _ _ (by omega)] <;> rfl
  have t1 : programStep program s1 = some s2 := by
    rw [fetched program s1 (base + 1) (.add 2 2 2) rfl (by omega)
      (by simpa [boundaryCode] using block 1 (by simp [boundaryCode]))]
    change some (s1.advance.put 2 (word width ((word width literals).val + (word width literals).val))) = some s2
    rw [countValue, advance_at _ _ _ _ _ _ _ _ (by omega), put2_at]
    change some (atState firstHeap (base + 1 + 1) cursor tableBase (literals + literals) scratch stack output) =
      some (atState firstHeap (base + 2) cursor tableBase (2 * literals) scratch stack output)
    rw [show base + 1 + 1 = base + 2 by omega, show literals + literals = 2 * literals by omega]
  have t2 : programStep program s2 = some s3 := by
    rw [fetched program s2 (base + 2) (.add 0 0 2) rfl (by omega)
      (by simpa [boundaryCode] using block 2 (by simp [boundaryCode]))]
    change some (s2.advance.put 0 (word width ((word width cursor).val + (word width (2 * literals)).val))) = some s3
    rw [cursorValue, doubledValue, advance_at _ _ _ _ _ _ _ _ (by omega), put0_at]
  have t3 : programStep program s3 = some s4 := by
    rw [fetched program s3 (base + 3) (.allocate 0) rfl (by omega)
      (by simpa [boundaryCode] using block 3 (by simp [boundaryCode]))]
    change (if firstHeap.size < 2 ^ width then
      some { s3.advance with heap := firstHeap.push (word width (cursor + 2 * literals)) } else none) = some s4
    rw [ite_eq_left (by simp only [firstHeap, Array.size_push]; omega),
      advance_at _ _ _ _ _ _ _ _ (by omega)] <;> rfl
  have first := Execution.cons t0 (Execution.cons t1 (Execution.refl s2))
  have last := Execution.cons t2 (Execution.cons t3 (Execution.refl s4))
  have joined := first.append last
  convert joined using 1 <;>
    simp only [s0, s1, s2, s3, s4, firstHeap, atState_liveWords, Array.size_push] <;> omega

theorem boundary_prefix (heap : Array (Word width)) (cursor literals index : ℕ)
    (valid : index < heap.size) :
    ((heap.push (word width cursor)).push (word width (cursor + 2 * literals)))[index]? = heap[index]? := by
  rw [Array.getElem?_push, Array.size_push,
    ite_eq_right (show index ≠ heap.size + 1 by omega), Array.getElem?_push,
    ite_eq_right (show index ≠ heap.size by omega)]

end Controller.Cost.ForestZeroQuery
