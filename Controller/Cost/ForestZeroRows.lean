module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestZeroCone
public import Controller.Cost.ForestIndexedOperands
public import Controller.Cost.ForestZeroDictionary

public import Mathlib.Tactic.FinCases

@[expose] public section

/-! Original cone rows retain source node identities, child positions, and
signed guard occurrences. Global source coordinates separate channels from
activities; first-touch allocation maps them to local solver coordinates.
Physical literal-pair append operations preserve label/polarity order. -/
namespace Controller.Cost.ForestZeroRows
open Controller.Decoder Controller.Decoder.DAG Controller.CNF
open Controller.Cost.ForestIndexedOperands
open Controller.Cost.ForestZeroTouch Controller.Cost.GateProgram
open Controller.Cost.ForestZeroCompile Controller.Cost.ForestZeroDictionary
open Controller.Decoder.ZeroSystem

/-- Activities follow channels in the fixed original-coordinate table. -/
def sourceIndex (graph : DAG n) : graph.ZeroVar → Fin (n + graph.nodeCount)
  | .inl channel => ⟨channel.val, by have := channel.isLt; omega⟩
  | .inr node => ⟨n + node.val, by have := node.isLt; omega⟩

def sourceLiteral (graph : DAG n) (literal : Literal graph.ZeroVar) : Literal ℕ :=
  ((sourceIndex graph literal.1).val, literal.2)

/-- This recurrence consumes the actual stored row fields. Guard children are
read from the original child stream, never an unconstrained head field. -/
def rowClauses (channels owner : ℕ) (row : Row) : List (Clause ℕ) :=
  match row.tag, row.children with
  | 0, _ => [[(channels + owner, false)]]
  | 1, _ => [[(row.head, false), (channels + owner, true)],
              [(channels + owner, false), (row.head, true)]]
  | 2, children => children.map fun child => [(channels + child, false), (channels + owner, true)]
  | 3, child :: _ => [[(channels + child, false)] ++
      row.guards.map (fun guard => (guard, true)) ++ [(channels + owner, true)]]
  | 4, left :: right :: _ => [[(channels + left, false), (channels + right, false), (channels + owner, true)]]
  | _, _ => []

/-- Exact typed correspondence includes all original repeated incidences. -/
theorem rowClauses_exact (graph : DAG n) (owner : Fin graph.nodeCount) (row : Row)
    (matchesRow : row.Matches (graph.node owner)) :
    rowClauses n owner.val row =
      (graph.nodeClauses owner).map (List.map (sourceLiteral graph)) := by
  rcases matchesRow with ⟨tag, head, children, guards⟩
  cases gate : graph.node owner with
  | zero =>
      simp only [gate, Gate.children, Gate.guardLabels] at tag children guards
      simp [rowClauses, tag, children, nodeClauses, gate, sourceLiteral, sourceIndex,
        Controller.Decoder.ZeroSystem.implicationClause, Controller.Decoder.ZeroSystem.positiveClause]
  | input channel =>
      have headEq := head channel gate
      simp only [gate, Gate.children, Gate.guardLabels] at tag children guards
      simp [rowClauses, tag, headEq, children, nodeClauses, gate, sourceLiteral, sourceIndex,
        Controller.Decoder.ZeroSystem.implicationClause, Controller.Decoder.ZeroSystem.positiveClause]
  | disj refs =>
      simp only [gate, Gate.children, Gate.guardLabels] at tag children guards
      simp [rowClauses, tag, children, nodeClauses, gate, sourceLiteral, sourceIndex,
        childIndex, List.map_map, Function.comp_def,
        Controller.Decoder.ZeroSystem.implicationClause, Controller.Decoder.ZeroSystem.positiveClause]
  | guard child labels =>
      simp only [gate, Gate.children, Gate.guardLabels, List.map_cons, List.map_nil] at tag children guards
      simp [rowClauses, tag, children, guards, nodeClauses, gate, sourceLiteral, sourceIndex,
        childIndex, List.map_map, Function.comp_def,
        Controller.Decoder.ZeroSystem.implicationClause, Controller.Decoder.ZeroSystem.positiveClause]
  | liveAnd left right =>
      simp only [gate, Gate.children, Gate.guardLabels, List.map_cons, List.map_nil] at tag children guards
      simp [rowClauses, tag, children, nodeClauses, gate, sourceLiteral, sourceIndex, childIndex]

/-- Every generated original coordinate is checked before Nat-to-Fin conversion. -/
theorem rowClauses_bounded (graph : DAG n) (owner : Fin graph.nodeCount) (row : Row)
    (matchesRow : row.Matches (graph.node owner)) :
    ∀ clause ∈ rowClauses n owner.val row, ∀ literal ∈ clause, literal.1 < n + graph.nodeCount := by
  rw [rowClauses_exact graph owner row matchesRow]
  intro clause present literal member
  obtain ⟨original, _, rfl⟩ := List.mem_map.mp present
  obtain ⟨source, _, rfl⟩ := List.mem_map.mp member
  exact (sourceIndex graph source.1).isLt

/-- At most two clauses are emitted per node, except for the original OR child
stream. Literal bounds retain every original guard and child incidence. -/
theorem rowClauses_size (channels owner : ℕ) (row : Row) :
    (rowClauses channels owner row).length ≤ 2 + row.children.length ∧
      ((rowClauses channels owner row).map List.length).sum ≤
        4 + 2 * row.children.length + row.guards.length := by
  unfold rowClauses
  split <;> simp_all only [List.length_cons, List.length_nil, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, List.length_append, List.length_map]
  · omega
  · omega
  · induction row.children with
    | nil => simp
    | cons child children ih => simp only [List.map_cons, List.length_cons, List.map_nil,
        List.sum_cons, List.length_nil] at *; omega
  · omega
  · omega
  · omega

/-- Three fixed instructions append the returned local ID and its polarity. -/
def pairCode (width : ℕ) (positive : Bool) : Code width :=
  [.allocate 0, .constant 3 (word width (if positive then 1 else 0)), .allocate 3]

@[simp] theorem pairCode_length : (pairCode width positive).length = 3 := rfl

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

private theorem put3_at (heap : Array (Word width)) (cursor x0 x1 x2 x3 value : ℕ)
    (stack output : List (Word width)) :
    (atState heap cursor x0 x1 x2 x3 stack output).put 3 (word width value) =
      atState heap cursor x0 x1 x2 value stack output := by
  unfold atState State.put
  congr 1
  funext register
  fin_cases register <;> rfl

/-- Actual label/polarity allocation retains the local count and table base,
while every older source, table, inverse and row-directory cell stays intact. -/
theorem pair_execution (program : Program width 4) (heap : Array (Word width))
    (base index tableBase count scratch : ℕ) (positive : Bool)
    (stack output : List (Word width)) (room : heap.size + 2 ≤ 2 ^ width)
    (programFits : base + 3 < 2 ^ width)
    (block : BlockAt program base (pairCode width positive)) :
    Execution program
      (atState heap base index tableBase count scratch stack output)
      (atState ((heap.push (word width index)).push (word width (if positive then 1 else 0)))
        (base + 3) index tableBase count (if positive then 1 else 0) stack output)
      3 (7 + heap.size + stack.length + output.length) := by
  let initial := atState heap base index tableBase count scratch stack output
  let firstHeap := heap.push (word width index)
  let one := atState firstHeap (base + 1) index tableBase count scratch stack output
  let two := atState firstHeap (base + 2) index tableBase count (if positive then 1 else 0) stack output
  let final := atState (firstHeap.push (word width (if positive then 1 else 0)))
    (base + 3) index tableBase count (if positive then 1 else 0) stack output
  have first : programStep program initial = some one := by
    rw [fetched program initial base (.allocate 0) rfl (by omega)
      (by simpa [pairCode] using block 0 (by simp [pairCode]))]
    change (if heap.size < 2 ^ width then some { initial.advance with heap := heap.push (word width index) }
      else none) = some one
    rw [ite_eq_left (by omega), advance_at _ _ _ _ _ _ _ _ (by omega)] <;> rfl
  have middle : programStep program one = some two := by
    rw [fetched program one (base + 1) (.constant 3 (word width (if positive then 1 else 0))) rfl (by omega)
      (by simpa [pairCode] using block 1 (by simp [pairCode]))]
    change some (one.advance.put 3 (word width (if positive then 1 else 0))) = some two
    rw [advance_at _ _ _ _ _ _ _ _ (by omega), put3_at]
  have last : programStep program two = some final := by
    rw [fetched program two (base + 2) (.allocate 3) rfl (by omega)
      (by simpa [pairCode] using block 2 (by simp [pairCode]))]
    change (if firstHeap.size < 2 ^ width then
      some { two.advance with heap := firstHeap.push (word width (if positive then 1 else 0)) } else none) = some final
    rw [ite_eq_left (by simp [firstHeap]; omega), advance_at _ _ _ _ _ _ _ _ (by omega)] <;> rfl
  have joined := Execution.cons first (Execution.cons middle (Execution.cons last (Execution.refl final)))
  convert joined using 1 <;>
    simp only [initial, one, two, final, firstHeap, atState_liveWords, Array.size_push] <;> omega

/-- Physical first-touch updates only reserved cells; emitted pairs follow the
unchanged source prefix and reserved dictionary regions. -/
def touchedHeap (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (state : Dictionary ambient) (coordinate : Fin ambient) : Array (Word width) :=
  if state.slots[coordinate.val] = 0 then
    freshHeap heap layout.tableBase layout.inverseBase state coordinate
  else heap

@[simp] theorem touchedHeap_size (heap : Array (Word width))
    (layout : Layout ambient heap.size) (state : Dictionary ambient) (coordinate : Fin ambient) :
    (touchedHeap heap layout state coordinate).size = heap.size := by
  unfold touchedHeap
  split <;> simp

def literalHeap (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (state : Dictionary ambient) (literal : Literal (Fin ambient)) : Array (Word width) :=
  ((touchedHeap heap layout state literal.1).push
    (word width (touch state literal.1).2.1)).push
    (word width (if literal.2 then 1 else 0))

@[simp] theorem literalHeap_size (heap : Array (Word width))
    (layout : Layout ambient heap.size) (state : Dictionary ambient) (literal : Literal (Fin ambient)) :
    (literalHeap heap layout state literal).size = heap.size + 2 := by
  simp [literalHeap]

/-- Reserved bases are unchanged when two solver-source words are appended. -/
def literalLayout (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (state : Dictionary ambient) (literal : Literal (Fin ambient)) :
    Layout ambient (literalHeap heap layout state literal).size where
  tableBase := layout.tableBase
  inverseBase := layout.inverseBase
  tableBound := by have := layout.tableBound; simp only [literalHeap_size]; omega
  inverseBound := by have := layout.inverseBound; simp only [literalHeap_size]; omega
  disjoint := layout.disjoint

/-- The complete physical literal call executes a dictionary lookup followed
by both actual allocations. Repeated original coordinates still emit a pair.
The inverse-base stack word is retained for the next literal call. -/
theorem literal_execution (program : Program width 4) (heap : Array (Word width))
    (layout : Layout ambient heap.size) (state : Dictionary ambient)
    (represented : Represented heap layout state) (literal : Literal (Fin ambient))
    (base scratch : ℕ) (stack output : List (Word width))
    (room : heap.size + 2 < 2 ^ width) (ambientFits : ambient + 1 < 2 ^ width)
    (programFits : base + 23 < 2 ^ width)
    (lookupBlock : BlockAt program base (Controller.Cost.ForestZeroTouch.code width base))
    (pairBlock : BlockAt program (base + 20) (pairCode width literal.2)) :
    ∃ ticks, ticks ≤ 18 ∧ Execution program
      (atState heap base literal.1.val layout.tableBase state.coordinates.size scratch
        (word width layout.inverseBase :: stack) output)
      (atState (literalHeap heap layout state literal) (base + 23)
        (touch state literal.1).2.1 layout.tableBase (touch state literal.1).1.coordinates.size
        (if literal.2 then 1 else 0) (word width layout.inverseBase :: stack) output)
      ticks (8 + heap.size + stack.length + output.length) := by
  by_cases unseen : state.slots[literal.1.val] = 0
  · have lookup := fresh_execution_refines program heap layout state represented literal.1 unseen
      base scratch stack output (by omega) ambientFits (by omega) lookupBlock
    have pair := pair_execution program
      (freshHeap heap layout.tableBase layout.inverseBase state literal.1) (base + 20)
      (touch state literal.1).2.1 layout.tableBase (touch state literal.1).1.coordinates.size 1
      literal.2 (word width layout.inverseBase :: stack) output
      (by simp only [freshHeap_size]; omega) (by omega) pairBlock
    have joined := lookup.append pair
    refine ⟨18, by omega, ?_⟩
    convert joined using 1 <;>
      simp only [literalHeap, touchedHeap, ite_eq_left unseen, freshHeap_size,
        List.length_cons, Nat.add_assoc] <;> omega
  · have lookup := existing_execution_refines program heap layout state represented literal.1 unseen
      base scratch stack output (by omega) ambientFits (by omega) lookupBlock
    have pair := pair_execution program heap (base + 20) (touch state literal.1).2.1
      layout.tableBase (touch state literal.1).1.coordinates.size 0 literal.2
      (word width layout.inverseBase :: stack) output (by omega) (by omega) pairBlock
    have joined := lookup.append pair
    refine ⟨12, by omega, ?_⟩
    convert joined using 1 <;>
      simp only [literalHeap, touchedHeap, ite_eq_right unseen, List.length_cons, Nat.add_assoc] <;> omega

/-- Appending emitted words preserves every old dictionary cell, and hence its
exact inverse relation. The dynamic bounds are derived from coherent allocation. -/
theorem literal_represented (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (state : Dictionary ambient) (represented : Represented heap layout state)
    (literal : Literal (Fin ambient)) :
    Represented (literalHeap heap layout state literal) (literalLayout heap layout state literal)
      (touch state literal.1).1 := by
  have touched : Represented (touchedHeap heap layout state literal.1)
      { tableBase := layout.tableBase
        inverseBase := layout.inverseBase
        tableBound := by simpa using layout.tableBound
        inverseBound := by simpa using layout.inverseBound
        disjoint := layout.disjoint }
      (touch state literal.1).1 := by
    constructor
    · exact touch_coherent state represented.coherent literal.1
    · intro coordinate
      change (touchedHeap heap layout state literal.1)[layout.tableBase + coordinate.val]? =
        some (word width (touch state literal.1).1.slots[coordinate.val])
      by_cases unseen : state.slots[literal.1.val] = 0
      · rw [show touchedHeap heap layout state literal.1 =
          freshHeap heap layout.tableBase layout.inverseBase state literal.1 by
            simp [touchedHeap, unseen]]
        exact (fresh_represented heap layout state represented literal.1 unseen).slots coordinate
      · rw [show touchedHeap heap layout state literal.1 = heap by simp [touchedHeap, unseen]]
        simpa only [touch, ite_eq_right unseen] using represented.slots coordinate
    · intro index coordinate present
      change (touchedHeap heap layout state literal.1)[layout.inverseBase + index]? =
        some (word width coordinate.val)
      by_cases unseen : state.slots[literal.1.val] = 0
      · rw [show touchedHeap heap layout state literal.1 =
          freshHeap heap layout.tableBase layout.inverseBase state literal.1 by
            simp [touchedHeap, unseen]]
        exact (fresh_represented heap layout state represented literal.1 unseen).inverse index coordinate present
      · rw [show touchedHeap heap layout state literal.1 = heap by simp [touchedHeap, unseen]]
        have oldPresent : state.coordinates[index]? = some coordinate := by
          simpa only [touch, ite_eq_right unseen] using present
        exact represented.inverse index coordinate oldPresent
  constructor
  · exact touched.coherent
  · intro coordinate
    have valid := layout.table_valid coordinate
    have same := touched.slots coordinate
    simpa only [literalLayout, literalHeap, Array.getElem?_push, Array.size_push,
      touchedHeap_size, ite_eq_right (show layout.tableBase + coordinate.val ≠ heap.size by omega),
      ite_eq_right (show layout.tableBase + coordinate.val ≠ heap.size + 1 by omega),
      Array.size_push] using same
  · intro index coordinate present
    have bounded := (Array.getElem?_eq_some_iff.mp present).1
    have countBound := count_le_ambient (touch state literal.1).1 touched.coherent
    have valid := layout.inverse_valid index (by omega)
    have same := touched.inverse index coordinate present
    simpa only [literalLayout, literalHeap, Array.getElem?_push,
      touchedHeap_size, Array.size_push,
      ite_eq_right (show layout.inverseBase + index ≠ heap.size by omega),
      ite_eq_right (show layout.inverseBase + index ≠ heap.size + 1 by omega)] using same

end Controller.Cost.ForestZeroRows
