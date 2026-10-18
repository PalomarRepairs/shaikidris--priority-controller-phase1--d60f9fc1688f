module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestWitnessEmit
public import Controller.Cost.ForestIndexedOperands
public import Controller.Cost.ForestInputStored

public import Mathlib.Tactic.FinCases

@[expose] public section

/-! Fixed source-row navigation for witness reconstruction. The current node
ID is register zero; the forward child positions are consumed from the stack.
Guard labels are fetched from their own stored incidence stream and marked by
dynamic stores. Source headers and both incidence streams lie before the
marker region. Zero and live-AND nodes are outside a feasible guarded route. -/
namespace Controller.Cost.ForestWitnessPath
open Controller.Decoder Controller.Decoder.DAG Controller.Cost.GateProgram
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestInputStored

/-- Physical column bases of the one shared serialized source packet. -/
structure Layout where
  headerBase : ℕ
  childrenBaseColumn : ℕ
  arityBaseColumn : ℕ
  markerBase : ℕ

/-- One fixed program follows a retained positional route. The guard loop
writes one marker per stored label occurrence; a repeated label is harmless.
The input exit leaves its source-derived channel ID in register zero. -/
def code (width base : ℕ) (layout : Layout) : ForestCounter.Code width :=
  [ -- 0: source tag dispatch
    .copy 1 0, .add 1 1 1, .constant 2 (word width layout.headerBase),
    .add 1 1 2, .load 1 1,
    .branchZero 1 (word width (base + 53)),
    .constant 2 (word width (2 ^ width - 1)), .add 1 1 2,
    .branchZero 1 (word width (base + 46)), .add 1 1 2,
    .branchZero 1 (word width (base + 36)),
    -- 11: save the current node; read actual guard arity and stream base
    .push 0, .copy 1 0, .add 1 1 1,
    .constant 2 (word width (layout.arityBaseColumn + 1)), .add 1 1 2, .load 3 1,
    .copy 1 0, .add 1 1 1,
    .constant 2 (word width (layout.childrenBaseColumn + 1)), .add 1 1 2, .load 0 1,
    -- 22: guard labels, including repetitions, are marked once per incidence
    .branchZero 3 (word width (base + 33)), .load 1 0,
    .constant 2 (word width layout.markerBase), .add 1 1 2,
    .constant 2 (word width 1), .store 1 2, .add 0 0 2,
    .constant 2 (word width (2 ^ width - 1)), .add 3 3 2,
    .constant 2 (word width 0), .branchZero 2 (word width (base + 22)),
    -- 33: restore the node; share the selected-child fetch
    .pop 0, .constant 2 (word width 0), .branchZero 2 (word width (base + 36)),
    -- 36: read one actual child slot chosen by the reconstructed route stack
    .pop 3, .copy 1 0, .add 1 1 1,
    .constant 2 (word width layout.childrenBaseColumn), .add 1 1 2, .load 1 1,
    .add 1 1 3, .load 0 1, .constant 2 (word width 0), .branchZero 2 (word width base),
    -- 46: source input channel; 53 is the invalid-route halt
    .copy 1 0, .add 1 1 1, .constant 2 (word width (layout.headerBase + 1)),
    .add 1 1 2, .load 0 1, .constant 2 (word width 0),
    .branchZero 2 (word width (base + 54)), .halt ]

@[simp] theorem code_length : (code width base layout).length = 54 := rfl

/-- A layout reads the actual stored columns: tag/head pairs, child/guard
stream-base pairs, and child/guard arity pairs. -/
def packetLayout (sourceBase nodeCount markerBase : ℕ) : Layout :=
  ⟨sourceBase, sourceBase + 2 * nodeCount, sourceBase + 4 * nodeCount, markerBase⟩

@[simp] theorem packet_columns (sourceBase nodeCount markerBase : ℕ) :
    (packetLayout sourceBase nodeCount markerBase).headerBase = sourceBase ∧
    (packetLayout sourceBase nodeCount markerBase).childrenBaseColumn = sourceBase + 2 * nodeCount ∧
    (packetLayout sourceBase nodeCount markerBase).arityBaseColumn = sourceBase + 4 * nodeCount ∧
    (packetLayout sourceBase nodeCount markerBase).markerBase = markerBase := by
  exact ⟨rfl, rfl, rfl, rfl⟩

def guardPhases (heap : Array (Word width)) (base : ℕ) (layout : Layout)
    (cursor identifier remaining : ℕ) (scratch temporary : Word width)
    (stack output : List (Word width)) : ℕ → State width 4 :=
  let modified := heap.setIfInBounds (layout.markerBase + identifier) (word width 1)
  fun index => match index with
  | 0 => UniformDAGScan.state heap (base + 22) (word width cursor) scratch temporary (word width (remaining + 1)) stack output
  | 1 => UniformDAGScan.state heap (base + 23) (word width cursor) scratch temporary (word width (remaining + 1)) stack output
  | 2 => UniformDAGScan.state heap (base + 24) (word width cursor) (word width identifier) temporary (word width (remaining + 1)) stack output
  | 3 => UniformDAGScan.state heap (base + 25) (word width cursor) (word width identifier) (word width layout.markerBase) (word width (remaining + 1)) stack output
  | 4 => UniformDAGScan.state heap (base + 26) (word width cursor) (word width (identifier + layout.markerBase)) (word width layout.markerBase) (word width (remaining + 1)) stack output
  | 5 => UniformDAGScan.state heap (base + 27) (word width cursor) (word width (identifier + layout.markerBase)) (word width 1) (word width (remaining + 1)) stack output
  | 6 => UniformDAGScan.state modified (base + 28) (word width cursor) (word width (identifier + layout.markerBase)) (word width 1) (word width (remaining + 1)) stack output
  | 7 => UniformDAGScan.state modified (base + 29) (word width (cursor + 1)) (word width (identifier + layout.markerBase)) (word width 1) (word width (remaining + 1)) stack output
  | 8 => UniformDAGScan.state modified (base + 30) (word width (cursor + 1)) (word width (identifier + layout.markerBase)) (word width (2 ^ width - 1)) (word width (remaining + 1)) stack output
  | 9 => UniformDAGScan.state modified (base + 31) (word width (cursor + 1)) (word width (identifier + layout.markerBase)) (word width (2 ^ width - 1)) (word width remaining) stack output
  | 10 => UniformDAGScan.state modified (base + 32) (word width (cursor + 1)) (word width (identifier + layout.markerBase)) (word width 0) (word width remaining) stack output
  | _ => UniformDAGScan.state modified (base + 22) (word width (cursor + 1)) (word width (identifier + layout.markerBase)) (word width 0) (word width remaining) stack output

private theorem fetched (program : Program width 4) (s : State width 4) (base offset : ℕ)
    (layout : Layout) (pc : s.pc = word width (base + offset))
    (fits : base + offset < 2 ^ width) (inside : offset < 54)
    (block : BlockAt program base (code width base layout)) :
    programStep program s = ((code width base layout)[offset]?).bind (fun instruction => step instruction s) := by
  unfold programStep
  rw [pc, show (word width (base + offset)).val = base + offset from Nat.mod_eq_of_lt fits,
    block offset (by simpa only [code_length] using inside)]
  rfl

/- Individual guard instructions use explicit source and destination states;
the ghost phase function is used only to assemble their checked sequence. -/
private theorem advance_pc (s : State width 4) (pcValue : s.pc = word width pc)
    (fits : pc < 2 ^ width) : s.advance.pc = word width (pc + 1) := by
  simp only [State.advance, pcValue]
  rw [show (word width pc).val = pc from Nat.mod_eq_of_lt fits]

private theorem primitive_copy (s : State width 4) (dst src : Fin 4)
    (value : Word width) (running : s.halted = false) (held : s.reg src = value) :
    step (.copy dst src) s = some (s.advance.put dst value) := by
  simp only [step, running, Bool.false_eq_true, ↓reduceIte, held]

private theorem primitive_constant (s : State width 4) (dst : Fin 4)
    (value : Word width) (running : s.halted = false) :
    step (.constant dst value) s = some (s.advance.put dst value) := by
  simp only [step, running, Bool.false_eq_true, ↓reduceIte]

private theorem primitive_add (s : State width 4) (dst left right : Fin 4)
    (a b : ℕ) (running : s.halted = false)
    (heldLeft : (s.reg left).val = a) (heldRight : (s.reg right).val = b) :
    step (.add dst left right) s = some (s.advance.put dst (word width (a + b))) := by
  simp only [step, running, Bool.false_eq_true, ↓reduceIte, heldLeft, heldRight]

private theorem primitive_load (s : State width 4) (dst address : Fin 4)
    (index : ℕ) (value : Word width) (running : s.halted = false)
    (held : (s.reg address).val = index) (valid : index < s.heap.size)
    (stored : s.heap[index]'valid = value) :
    step (.load dst address) s = some (s.advance.put dst value) := by
  simp only [step, running, Bool.false_eq_true, ↓reduceIte, held, dite_eq_left valid, stored]

private theorem primitive_pop (s : State width 4) (dst : Fin 4)
    (value : Word width) (rest : List (Word width))
    (running : s.halted = false) (held : s.stack = value :: rest) :
    step (.pop dst) s = some { s.advance.put dst value with stack := rest } := by
  simp only [step, running, Bool.false_eq_true, ↓reduceIte, held]

private theorem primitive_jump (s : State width 4) (src : Fin 4)
    (target : Word width) (running : s.halted = false) (held : s.reg src = word width 0) :
    step (.branchZero src target) s = some { s.advance with pc := target } := by
  simp only [step, running, Bool.false_eq_true, ↓reduceIte, held, word, Nat.zero_mod,
    Fin.val_mk, ↓reduceIte]

/-- A reconstructed child position is consumed once, then the original stored
child occurrence is fetched. No endpoint table or copied route is consulted. -/
private theorem child_prefix (program : Program width 4) (s : State width 4)
    (base : ℕ) (layout : Layout) (node position cursor child : ℕ)
    (suffix : List (Word width)) (nodeHeld : s.reg 0 = word width node)
    (positionHeld : s.stack = word width position :: suffix)
    (rowFits : layout.childrenBaseColumn + 2 * node < 2 ^ width)
    (childFits : cursor + position < 2 ^ width)
    (rowBound : layout.childrenBaseColumn + 2 * node < s.heap.size)
    (childBound : cursor + position < s.heap.size)
    (row : s.heap[layout.childrenBaseColumn + 2 * node]'rowBound = word width cursor)
    (stored : s.heap[cursor + position]'childBound = word width child)
    (pc : s.pc = word width (base + 36)) (running : s.halted = false)
    (programFits : base + 54 < 2 ^ width)
    (block : BlockAt program base (code width base layout)) :
    Execution program (s) (UniformDAGScan.state s.heap (base + 39) (word width node) (word width (2 * node)) (s.reg 2) (word width position) suffix s.output) 3 s.liveWords := by
  let one := UniformDAGScan.state s.heap (base + 37) (word width node) (s.reg 1) (s.reg 2) (word width position) suffix s.output
  let two := UniformDAGScan.state s.heap (base + 38) (word width node) (word width node) (s.reg 2) (word width position) suffix s.output
  let three := UniformDAGScan.state s.heap (base + 39) (word width node) (word width (2 * node)) (s.reg 2) (word width position) suffix s.output
  have nValue : (word width node).val = node := Nat.mod_eq_of_lt (by omega)
  have doubleValue : (word width (2 * node)).val = 2 * node := Nat.mod_eq_of_lt (by omega)
  have columnValue : (word width layout.childrenBaseColumn).val = layout.childrenBaseColumn := Nat.mod_eq_of_lt (by omega)
  have rowValue : (word width (layout.childrenBaseColumn + 2 * node)).val = layout.childrenBaseColumn + 2 * node := Nat.mod_eq_of_lt rowFits
  have cursorValue : (word width cursor).val = cursor := Nat.mod_eq_of_lt (by omega)
  have positionValue : (word width position).val = position := Nat.mod_eq_of_lt (by omega)
  have childAddress : (word width (cursor + position)).val = cursor + position := Nat.mod_eq_of_lt childFits
  have doubledValue : (word width (node + node)).val = node + node := by
    simpa only [two_mul] using doubleValue
  have rowSumValue : (word width (layout.childrenBaseColumn + (node + node))).val =
      layout.childrenBaseColumn + (node + node) := by simpa only [two_mul] using rowValue
  have rowSumBound : layout.childrenBaseColumn + (node + node) < s.heap.size := by omega
  have rowSumCell : s.heap[layout.childrenBaseColumn + (node + node)]'rowSumBound = word width cursor := by
    simpa only [two_mul] using row
  have chosenValue : (word width (position + cursor)).val = position + cursor := by
    simpa only [Nat.add_comm] using childAddress
  have chosenBound : position + cursor < s.heap.size := by omega
  have chosenCell : s.heap[position + cursor]'chosenBound = word width child := by
    simpa only [Nat.add_comm] using stored
  have zeroWord : word width 0 = (0 : Word width) := by apply Fin.ext; simp [word]
  have p1 : one.pc = word width (base + 37) := rfl
  have p2 : two.pc = word width (base + 38) := rfl
  have p3 : three.pc = word width (base + 39) := rfl
  have entryPC : (base + 36) % 2 ^ width = base + 36 := Nat.mod_eq_of_lt (by omega)
  have pc37 : (base + 37) % 2 ^ width = base + 37 := Nat.mod_eq_of_lt (by omega)
  have pc38 : (base + 38) % 2 ^ width = base + 38 := Nat.mod_eq_of_lt (by omega)
  have pcWord36 : (word width (base + 36)).val = base + 36 := Nat.mod_eq_of_lt (by omega)
  have pcWord37 : (word width (base + 37)).val = base + 37 := Nat.mod_eq_of_lt (by omega)
  have pcWord38 : (word width (base + 38)).val = base + 38 := Nat.mod_eq_of_lt (by omega)
  have step0 : programStep program s = some one := by
    rw [fetched program s base 36 layout pc (by omega) (by decide) block]
    change step (.pop 3) s = some one
    simp [step, one, one, UniformDAGScan.state,
      State.advance, State.put, running, nodeHeld, positionHeld, pc, entryPC,
      pc37, pc38, nValue, doubleValue, columnValue,
      rowValue, cursorValue, positionValue, childAddress, rowBound, childBound,
      row, stored, doubledValue, rowSumValue, rowSumBound, rowSumCell,
      chosenValue, chosenBound, chosenCell, zeroWord, two_mul, Nat.add_comm, Nat.add_assoc]
    all_goals
      first
      | constructor
        · funext register
          fin_cases register <;> simp [nodeHeld]
        · simp only [pcWord36, pcWord37, pcWord38]
          congr 1 <;> omega
      | funext register
        fin_cases register <;> simp [nodeHeld]
  have step1 : programStep program one = some two := by
    rw [fetched program one base 37 layout p1 (by omega) (by decide) block]
    change step (.copy 1 0) one = some two
    simp [step, one, two, UniformDAGScan.state,
      State.advance, State.put, running, nodeHeld, positionHeld, pc, entryPC,
      pc37, pc38, nValue, doubleValue, columnValue,
      rowValue, cursorValue, positionValue, childAddress, rowBound, childBound,
      row, stored, doubledValue, rowSumValue, rowSumBound, rowSumCell,
      chosenValue, chosenBound, chosenCell, zeroWord, two_mul, Nat.add_comm, Nat.add_assoc]
    all_goals
      first
      | constructor
        · funext register
          fin_cases register <;> simp [nodeHeld]
        · simp only [pcWord36, pcWord37, pcWord38]
          congr 1 <;> omega
      | funext register
        fin_cases register <;> simp [nodeHeld]
  have step2 : programStep program two = some three := by
    rw [fetched program two base 38 layout p2 (by omega) (by decide) block]
    change step (.add 1 1 1) two = some three
    simp [step, two, three, UniformDAGScan.state,
      State.advance, State.put, running, nodeHeld, positionHeld, pc, entryPC,
      pc37, pc38, nValue, doubleValue, columnValue,
      rowValue, cursorValue, positionValue, childAddress, rowBound, childBound,
      row, stored, doubledValue, rowSumValue, rowSumBound, rowSumCell,
      chosenValue, chosenBound, chosenCell, zeroWord, two_mul, Nat.add_comm, Nat.add_assoc]
    all_goals
      first
      | constructor
        · funext register
          fin_cases register <;> simp [nodeHeld]
        · simp only [pcWord36, pcWord37, pcWord38]
          congr 1 <;> omega
      | funext register
        fin_cases register <;> simp [nodeHeld]
  have initialLive : s.liveWords = 6 + s.heap.size + suffix.length + s.output.length := by
    simp [State.liveWords, positionHeld]; omega
  have l1 : one.liveWords = 5 + s.heap.size + suffix.length + s.output.length := by
    simp [State.liveWords, UniformDAGScan.state, one]; omega
  have l2 : two.liveWords = 5 + s.heap.size + suffix.length + s.output.length := by
    simp [State.liveWords, UniformDAGScan.state, two]; omega
  have l3 : three.liveWords = 5 + s.heap.size + suffix.length + s.output.length := by
    simp [State.liveWords, UniformDAGScan.state, three]; omega
  have trace := Execution.cons step0 (Execution.cons step1 (Execution.cons step2 (Execution.refl three)))
  convert trace using 1 <;> simp only [initialLive, l1, l2, l3, Nat.max_self] <;> omega

private theorem child_middle (program : Program width 4) (s : State width 4)
    (base : ℕ) (layout : Layout) (node position cursor child : ℕ)
    (suffix : List (Word width)) (nodeHeld : s.reg 0 = word width node)
    (positionHeld : s.stack = word width position :: suffix)
    (rowFits : layout.childrenBaseColumn + 2 * node < 2 ^ width)
    (childFits : cursor + position < 2 ^ width)
    (rowBound : layout.childrenBaseColumn + 2 * node < s.heap.size)
    (childBound : cursor + position < s.heap.size)
    (row : s.heap[layout.childrenBaseColumn + 2 * node]'rowBound = word width cursor)
    (stored : s.heap[cursor + position]'childBound = word width child)
    (pc : s.pc = word width (base + 36)) (running : s.halted = false)
    (programFits : base + 54 < 2 ^ width)
    (block : BlockAt program base (code width base layout)) :
    Execution program (UniformDAGScan.state s.heap (base + 39) (word width node) (word width (2 * node)) (s.reg 2) (word width position) suffix s.output) (UniformDAGScan.state s.heap (base + 42) (word width node) (word width cursor) (word width layout.childrenBaseColumn) (word width position) suffix s.output) 3 (5 + s.heap.size + suffix.length + s.output.length) := by
  let three := UniformDAGScan.state s.heap (base + 39) (word width node) (word width (2 * node)) (s.reg 2) (word width position) suffix s.output
  let four := UniformDAGScan.state s.heap (base + 40) (word width node) (word width (2 * node)) (word width layout.childrenBaseColumn) (word width position) suffix s.output
  let five := UniformDAGScan.state s.heap (base + 41) (word width node) (word width (layout.childrenBaseColumn + 2 * node)) (word width layout.childrenBaseColumn) (word width position) suffix s.output
  let six := UniformDAGScan.state s.heap (base + 42) (word width node) (word width cursor) (word width layout.childrenBaseColumn) (word width position) suffix s.output
  have nValue : (word width node).val = node := Nat.mod_eq_of_lt (by omega)
  have doubleValue : (word width (2 * node)).val = 2 * node := Nat.mod_eq_of_lt (by omega)
  have columnValue : (word width layout.childrenBaseColumn).val = layout.childrenBaseColumn := Nat.mod_eq_of_lt (by omega)
  have rowValue : (word width (layout.childrenBaseColumn + 2 * node)).val = layout.childrenBaseColumn + 2 * node := Nat.mod_eq_of_lt rowFits
  have cursorValue : (word width cursor).val = cursor := Nat.mod_eq_of_lt (by omega)
  have positionValue : (word width position).val = position := Nat.mod_eq_of_lt (by omega)
  have childAddress : (word width (cursor + position)).val = cursor + position := Nat.mod_eq_of_lt childFits
  have doubledValue : (word width (node + node)).val = node + node := by
    simpa only [two_mul] using doubleValue
  have rowSumValue : (word width (layout.childrenBaseColumn + (node + node))).val =
      layout.childrenBaseColumn + (node + node) := by simpa only [two_mul] using rowValue
  have rowSumBound : layout.childrenBaseColumn + (node + node) < s.heap.size := by omega
  have rowSumCell : s.heap[layout.childrenBaseColumn + (node + node)]'rowSumBound = word width cursor := by
    simpa only [two_mul] using row
  have chosenValue : (word width (position + cursor)).val = position + cursor := by
    simpa only [Nat.add_comm] using childAddress
  have chosenBound : position + cursor < s.heap.size := by omega
  have chosenCell : s.heap[position + cursor]'chosenBound = word width child := by
    simpa only [Nat.add_comm] using stored
  have zeroWord : word width 0 = (0 : Word width) := by apply Fin.ext; simp [word]
  have p3 : three.pc = word width (base + 39) := rfl
  have p4 : four.pc = word width (base + 40) := rfl
  have p5 : five.pc = word width (base + 41) := rfl
  have p6 : six.pc = word width (base + 42) := rfl
  have pc39 : (base + 39) % 2 ^ width = base + 39 := Nat.mod_eq_of_lt (by omega)
  have pc40 : (base + 40) % 2 ^ width = base + 40 := Nat.mod_eq_of_lt (by omega)
  have pc41 : (base + 41) % 2 ^ width = base + 41 := Nat.mod_eq_of_lt (by omega)
  have pcWord39 : (word width (base + 39)).val = base + 39 := Nat.mod_eq_of_lt (by omega)
  have pcWord40 : (word width (base + 40)).val = base + 40 := Nat.mod_eq_of_lt (by omega)
  have pcWord41 : (word width (base + 41)).val = base + 41 := Nat.mod_eq_of_lt (by omega)
  have step3 : programStep program three = some four := by
    rw [fetched program three base 39 layout p3 (by omega) (by decide) block]
    change step (.constant 2 (word width layout.childrenBaseColumn)) three = some four
    simp [step, three, four, UniformDAGScan.state,
      State.advance, State.put, running, nodeHeld, positionHeld, pc, pc39, pc40, pc41, nValue, doubleValue, columnValue,
      rowValue, cursorValue, positionValue, childAddress, rowBound, childBound,
      row, stored, doubledValue, rowSumValue, rowSumBound, rowSumCell,
      chosenValue, chosenBound, chosenCell, zeroWord, two_mul, Nat.add_comm, Nat.add_assoc]
    all_goals
      first
      | constructor
        · funext register
          fin_cases register <;> simp [nodeHeld]
        · simp only [pcWord39, pcWord40,
            pcWord41]
          congr 1 <;> omega
      | funext register
        fin_cases register <;> simp [nodeHeld]
  have step4 : programStep program four = some five := by
    rw [fetched program four base 40 layout p4 (by omega) (by decide) block]
    change step (.add 1 1 2) four = some five
    simp [step, four, five, UniformDAGScan.state,
      State.advance, State.put, running, nodeHeld, positionHeld, pc, pc39, pc40, pc41, nValue, doubleValue, columnValue,
      rowValue, cursorValue, positionValue, childAddress, rowBound, childBound,
      row, stored, doubledValue, rowSumValue, rowSumBound, rowSumCell,
      chosenValue, chosenBound, chosenCell, zeroWord, two_mul, Nat.add_comm, Nat.add_assoc]
    all_goals
      first
      | constructor
        · funext register
          fin_cases register <;> simp [nodeHeld]
        · simp only [pcWord39, pcWord40,
            pcWord41]
          congr 1 <;> omega
      | funext register
        fin_cases register <;> simp [nodeHeld]
  have step5 : programStep program five = some six := by
    rw [fetched program five base 41 layout p5 (by omega) (by decide) block]
    change step (.load 1 1) five = some six
    simp [step, five, six, UniformDAGScan.state,
      State.advance, State.put, running, nodeHeld, positionHeld, pc, pc39, pc40, pc41, nValue, doubleValue, columnValue,
      rowValue, cursorValue, positionValue, childAddress, rowBound, childBound,
      row, stored, doubledValue, rowSumValue, rowSumBound, rowSumCell,
      chosenValue, chosenBound, chosenCell, zeroWord, two_mul, Nat.add_comm, Nat.add_assoc]
    all_goals
      first
      | constructor
        · funext register
          fin_cases register <;> simp [nodeHeld]
        · simp only [pcWord39, pcWord40,
            pcWord41]
          congr 1 <;> omega
      | funext register
        fin_cases register <;> simp [nodeHeld]
  have l3 : three.liveWords = 5 + s.heap.size + suffix.length + s.output.length := by
    simp [State.liveWords, UniformDAGScan.state, three]; omega
  have l4 : four.liveWords = 5 + s.heap.size + suffix.length + s.output.length := by
    simp [State.liveWords, UniformDAGScan.state, four]; omega
  have l5 : five.liveWords = 5 + s.heap.size + suffix.length + s.output.length := by
    simp [State.liveWords, UniformDAGScan.state, five]; omega
  have l6 : six.liveWords = 5 + s.heap.size + suffix.length + s.output.length := by
    simp [State.liveWords, UniformDAGScan.state, six]; omega
  have trace := Execution.cons step3 (Execution.cons step4 (Execution.cons step5 (Execution.refl six)))
  simpa only [l3, l4, l5, l6, Nat.max_self] using trace

private theorem child_tail (program : Program width 4) (s : State width 4)
    (base : ℕ) (layout : Layout) (node position cursor child : ℕ)
    (suffix : List (Word width)) (nodeHeld : s.reg 0 = word width node)
    (positionHeld : s.stack = word width position :: suffix)
    (rowFits : layout.childrenBaseColumn + 2 * node < 2 ^ width)
    (childFits : cursor + position < 2 ^ width)
    (rowBound : layout.childrenBaseColumn + 2 * node < s.heap.size)
    (childBound : cursor + position < s.heap.size)
    (row : s.heap[layout.childrenBaseColumn + 2 * node]'rowBound = word width cursor)
    (stored : s.heap[cursor + position]'childBound = word width child)
    (pc : s.pc = word width (base + 36)) (running : s.halted = false)
    (programFits : base + 54 < 2 ^ width)
    (block : BlockAt program base (code width base layout)) :
    Execution program (UniformDAGScan.state s.heap (base + 42) (word width node) (word width cursor) (word width layout.childrenBaseColumn) (word width position) suffix s.output) (UniformDAGScan.state s.heap base (word width child) (word width (cursor + position)) (word width 0) (word width position) suffix s.output) 4 (5 + s.heap.size + suffix.length + s.output.length) := by
  let six := UniformDAGScan.state s.heap (base + 42) (word width node) (word width cursor) (word width layout.childrenBaseColumn) (word width position) suffix s.output
  let seven := UniformDAGScan.state s.heap (base + 43) (word width node) (word width (cursor + position)) (word width layout.childrenBaseColumn) (word width position) suffix s.output
  let eight := UniformDAGScan.state s.heap (base + 44) (word width child) (word width (cursor + position)) (word width layout.childrenBaseColumn) (word width position) suffix s.output
  let nine := UniformDAGScan.state s.heap (base + 45) (word width child) (word width (cursor + position)) (word width 0) (word width position) suffix s.output
  let ready := UniformDAGScan.state s.heap base (word width child) (word width (cursor + position)) (word width 0) (word width position) suffix s.output
  have nValue : (word width node).val = node := Nat.mod_eq_of_lt (by omega)
  have doubleValue : (word width (2 * node)).val = 2 * node := Nat.mod_eq_of_lt (by omega)
  have columnValue : (word width layout.childrenBaseColumn).val = layout.childrenBaseColumn := Nat.mod_eq_of_lt (by omega)
  have rowValue : (word width (layout.childrenBaseColumn + 2 * node)).val = layout.childrenBaseColumn + 2 * node := Nat.mod_eq_of_lt rowFits
  have cursorValue : (word width cursor).val = cursor := Nat.mod_eq_of_lt (by omega)
  have positionValue : (word width position).val = position := Nat.mod_eq_of_lt (by omega)
  have childAddress : (word width (cursor + position)).val = cursor + position := Nat.mod_eq_of_lt childFits
  have doubledValue : (word width (node + node)).val = node + node := by
    simpa only [two_mul] using doubleValue
  have rowSumValue : (word width (layout.childrenBaseColumn + (node + node))).val =
      layout.childrenBaseColumn + (node + node) := by simpa only [two_mul] using rowValue
  have rowSumBound : layout.childrenBaseColumn + (node + node) < s.heap.size := by omega
  have rowSumCell : s.heap[layout.childrenBaseColumn + (node + node)]'rowSumBound = word width cursor := by
    simpa only [two_mul] using row
  have chosenValue : (word width (position + cursor)).val = position + cursor := by
    simpa only [Nat.add_comm] using childAddress
  have chosenBound : position + cursor < s.heap.size := by omega
  have chosenCell : s.heap[position + cursor]'chosenBound = word width child := by
    simpa only [Nat.add_comm] using stored
  have zeroWord : word width 0 = (0 : Word width) := by apply Fin.ext; simp [word]
  have p6 : six.pc = word width (base + 42) := rfl
  have p7 : seven.pc = word width (base + 43) := rfl
  have p8 : eight.pc = word width (base + 44) := rfl
  have p9 : nine.pc = word width (base + 45) := rfl
  have pc42 : (base + 42) % 2 ^ width = base + 42 := Nat.mod_eq_of_lt (by omega)
  have pc43 : (base + 43) % 2 ^ width = base + 43 := Nat.mod_eq_of_lt (by omega)
  have pc44 : (base + 44) % 2 ^ width = base + 44 := Nat.mod_eq_of_lt (by omega)
  have pc45 : (base + 45) % 2 ^ width = base + 45 := Nat.mod_eq_of_lt (by omega)
  have pcWord42 : (word width (base + 42)).val = base + 42 := Nat.mod_eq_of_lt (by omega)
  have pcWord43 : (word width (base + 43)).val = base + 43 := Nat.mod_eq_of_lt (by omega)
  have pcWord44 : (word width (base + 44)).val = base + 44 := Nat.mod_eq_of_lt (by omega)
  have pcWord45 : (word width (base + 45)).val = base + 45 := Nat.mod_eq_of_lt (by omega)
  have step6 : programStep program six = some seven := by
    rw [fetched program six base 42 layout p6 (by omega) (by decide) block]
    change step (.add 1 1 3) six = some seven
    simp [step, six, seven, UniformDAGScan.state,
      State.advance, State.put, running, nodeHeld, positionHeld, pc, pc42, pc43, pc44, pc45, nValue, doubleValue, columnValue,
      rowValue, cursorValue, positionValue, childAddress, rowBound, childBound,
      row, stored, doubledValue, rowSumValue, rowSumBound, rowSumCell,
      chosenValue, chosenBound, chosenCell, zeroWord, two_mul, Nat.add_comm, Nat.add_assoc]
    all_goals
      first
      | constructor
        · funext register
          fin_cases register <;> simp [nodeHeld]
        · simp only [pcWord42, pcWord43, pcWord44, pcWord45]
          congr 1 <;> omega
      | funext register
        fin_cases register <;> simp [nodeHeld]
  have step7 : programStep program seven = some eight := by
    rw [fetched program seven base 43 layout p7 (by omega) (by decide) block]
    change step (.load 0 1) seven = some eight
    simp [step, seven, eight, UniformDAGScan.state,
      State.advance, State.put, running, nodeHeld, positionHeld, pc, pc42, pc43, pc44, pc45, nValue, doubleValue, columnValue,
      rowValue, cursorValue, positionValue, childAddress, rowBound, childBound,
      row, stored, doubledValue, rowSumValue, rowSumBound, rowSumCell,
      chosenValue, chosenBound, chosenCell, zeroWord, two_mul, Nat.add_comm, Nat.add_assoc]
    all_goals
      first
      | constructor
        · funext register
          fin_cases register <;> simp [nodeHeld]
        · simp only [pcWord42, pcWord43, pcWord44, pcWord45]
          congr 1 <;> omega
      | funext register
        fin_cases register <;> simp [nodeHeld]
  have step8 : programStep program eight = some nine := by
    rw [fetched program eight base 44 layout p8 (by omega) (by decide) block]
    change step (.constant 2 (word width 0)) eight = some nine
    simp [step, eight, nine, UniformDAGScan.state,
      State.advance, State.put, running, nodeHeld, positionHeld, pc, pc42, pc43, pc44, pc45, nValue, doubleValue, columnValue,
      rowValue, cursorValue, positionValue, childAddress, rowBound, childBound,
      row, stored, doubledValue, rowSumValue, rowSumBound, rowSumCell,
      chosenValue, chosenBound, chosenCell, zeroWord, two_mul, Nat.add_comm, Nat.add_assoc]
    all_goals
      first
      | constructor
        · funext register
          fin_cases register <;> simp [nodeHeld]
        · simp only [pcWord42, pcWord43, pcWord44, pcWord45]
          congr 1 <;> omega
      | funext register
        fin_cases register <;> simp [nodeHeld]
  have step9 : programStep program nine = some ready := by
    rw [fetched program nine base 45 layout p9 (by omega) (by decide) block]
    change step (.branchZero 2 (word width base)) nine = some ready
    simp [step, nine, ready, UniformDAGScan.state,
      State.advance, State.put, running, nodeHeld, positionHeld, pc, pc42, pc43, pc44, pc45, nValue, doubleValue, columnValue,
      rowValue, cursorValue, positionValue, childAddress, rowBound, childBound,
      row, stored, doubledValue, rowSumValue, rowSumBound, rowSumCell,
      chosenValue, chosenBound, chosenCell, zeroWord, two_mul, Nat.add_comm, Nat.add_assoc]
    all_goals
      first
      | constructor
        · funext register
          fin_cases register <;> simp [nodeHeld]
        · simp only [pcWord42, pcWord43, pcWord44, pcWord45]
          congr 1 <;> omega
      | funext register
        fin_cases register <;> simp [nodeHeld]
  have l6 : six.liveWords = 5 + s.heap.size + suffix.length + s.output.length := by
    simp [State.liveWords, UniformDAGScan.state, six]; omega
  have l7 : seven.liveWords = 5 + s.heap.size + suffix.length + s.output.length := by
    simp [State.liveWords, UniformDAGScan.state, seven]; omega
  have l8 : eight.liveWords = 5 + s.heap.size + suffix.length + s.output.length := by
    simp [State.liveWords, UniformDAGScan.state, eight]; omega
  have l9 : nine.liveWords = 5 + s.heap.size + suffix.length + s.output.length := by
    simp [State.liveWords, UniformDAGScan.state, nine]; omega
  have l10 : ready.liveWords = 5 + s.heap.size + suffix.length + s.output.length := by
    simp [State.liveWords, UniformDAGScan.state, ready]; omega
  have trace := Execution.cons step6 (Execution.cons step7 (Execution.cons step8 (Execution.cons step9 (Execution.refl ready))))
  simpa only [l6, l7, l8, l9, l10, Nat.max_self] using trace

theorem child_execution (program : Program width 4) (s : State width 4)
    (base : ℕ) (layout : Layout) (node position cursor child : ℕ)
    (suffix : List (Word width)) (nodeHeld : s.reg 0 = word width node)
    (positionHeld : s.stack = word width position :: suffix)
    (rowFits : layout.childrenBaseColumn + 2 * node < 2 ^ width)
    (childFits : cursor + position < 2 ^ width)
    (rowBound : layout.childrenBaseColumn + 2 * node < s.heap.size)
    (childBound : cursor + position < s.heap.size)
    (row : s.heap[layout.childrenBaseColumn + 2 * node]'rowBound = word width cursor)
    (stored : s.heap[cursor + position]'childBound = word width child)
    (pc : s.pc = word width (base + 36)) (running : s.halted = false)
    (programFits : base + 54 < 2 ^ width)
    (block : BlockAt program base (code width base layout)) :
    ∃ ready, Execution program s ready 10 s.liveWords ∧
      ready.reg 0 = word width child ∧ ready.reg 3 = word width position ∧
      ready.heap = s.heap ∧ ready.stack = suffix ∧ ready.output = s.output ∧
      ready.pc = word width base ∧ ready.halted = false := by
  let ready := UniformDAGScan.state s.heap base (word width child) (word width (cursor + position)) (word width 0) (word width position) suffix s.output
  have first := child_prefix program s base layout node position cursor child suffix nodeHeld positionHeld rowFits childFits rowBound childBound row stored pc running programFits block
  have second := child_middle program s base layout node position cursor child suffix nodeHeld positionHeld rowFits childFits rowBound childBound row stored pc running programFits block
  have third := child_tail program s base layout node position cursor child suffix nodeHeld positionHeld rowFits childFits rowBound childBound row stored pc running programFits block
  have initialLive : s.liveWords = 6 + s.heap.size + suffix.length + s.output.length := by
    simp [State.liveWords, positionHeld]; omega
  refine ⟨ready, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
  · have joined := (first.append second).append third
    convert joined using 1 <;> simp only [initialLive, Nat.max_self] <;> omega
  all_goals simp [ready, UniformDAGScan.state]

private theorem guard_transition_0 (program : Program width 4) (heap : Array (Word width))
    (base : ℕ) (layout : Layout) (cursor identifier remaining : ℕ)
    (scratch temporary : Word width) (stack output : List (Word width))
    (programFits : base + 54 < 2 ^ width) (cursorFits : cursor + 1 < 2 ^ width)
    (countFits : remaining + 1 < 2 ^ width)
    (cursorBound : cursor < heap.size) (markerBound : layout.markerBase + identifier < heap.size)
    (heapFits : heap.size ≤ 2 ^ width)
    (source : heap[cursor]'cursorBound = word width identifier)
    (block : BlockAt program base (code width base layout)) :
    programStep program (UniformDAGScan.state (heap) (base + 22) (word width cursor) (scratch) (temporary) (word width (remaining + 1)) stack output) = some (UniformDAGScan.state (heap) (base + 23) (word width cursor) (scratch) (temporary) (word width (remaining + 1)) stack output) := by
  have pcFits (offset : ℕ) (inside : offset ≤ 54) : base + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left inside base) programFits
  rw [fetched program _ base 22 layout (by rfl) (pcFits 22 (by decide)) (by decide) block]
  change step (.branchZero 3 (word width (base + 33))) (UniformDAGScan.state (heap) (base + 22) (word width cursor) (scratch) (temporary) (word width (remaining + 1)) stack output) = some (UniformDAGScan.state (heap) (base + 23) (word width cursor) (scratch) (temporary) (word width (remaining + 1)) stack output)
  have pcValue : (base + 22) % 2 ^ width = base + 22 := Nat.mod_eq_of_lt (pcFits 22 (by decide))
  have countValue : (remaining + 1) % 2 ^ width = remaining + 1 := Nat.mod_eq_of_lt countFits
  simp [step, UniformDAGScan.state, State.advance, State.put, word, pcValue, countValue, Nat.add_assoc]
  all_goals try (congr 1; funext register; fin_cases register <;> simp)
  all_goals try (congr 1; omega)

private theorem guard_transition_1 (program : Program width 4) (heap : Array (Word width))
    (base : ℕ) (layout : Layout) (cursor identifier remaining : ℕ)
    (scratch temporary : Word width) (stack output : List (Word width))
    (programFits : base + 54 < 2 ^ width) (cursorFits : cursor + 1 < 2 ^ width)
    (countFits : remaining + 1 < 2 ^ width)
    (cursorBound : cursor < heap.size) (markerBound : layout.markerBase + identifier < heap.size)
    (heapFits : heap.size ≤ 2 ^ width)
    (source : heap[cursor]'cursorBound = word width identifier)
    (block : BlockAt program base (code width base layout)) :
    programStep program (UniformDAGScan.state (heap) (base + 23) (word width cursor) (scratch) (temporary) (word width (remaining + 1)) stack output) = some (UniformDAGScan.state (heap) (base + 24) (word width cursor) (word width identifier) (temporary) (word width (remaining + 1)) stack output) := by
  have pcFits (offset : ℕ) (inside : offset ≤ 54) : base + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left inside base) programFits
  rw [fetched program _ base 23 layout (by rfl) (pcFits 23 (by decide)) (by decide) block]
  change step (.load 1 0) (UniformDAGScan.state (heap) (base + 23) (word width cursor) (scratch) (temporary) (word width (remaining + 1)) stack output) = some (UniformDAGScan.state (heap) (base + 24) (word width cursor) (word width identifier) (temporary) (word width (remaining + 1)) stack output)
  have pcValue : (base + 23) % 2 ^ width = base + 23 := Nat.mod_eq_of_lt (pcFits 23 (by decide))
  have cursorValue : cursor % 2 ^ width = cursor := Nat.mod_eq_of_lt (by omega)
  simp [step, UniformDAGScan.state, State.advance, State.put, word, pcValue, cursorValue, cursorBound, source, Nat.add_assoc]
  all_goals try (congr 1; funext register; fin_cases register <;> simp)
  all_goals try (congr 1; omega)

private theorem guard_transition_2 (program : Program width 4) (heap : Array (Word width))
    (base : ℕ) (layout : Layout) (cursor identifier remaining : ℕ)
    (scratch temporary : Word width) (stack output : List (Word width))
    (programFits : base + 54 < 2 ^ width) (cursorFits : cursor + 1 < 2 ^ width)
    (countFits : remaining + 1 < 2 ^ width)
    (cursorBound : cursor < heap.size) (markerBound : layout.markerBase + identifier < heap.size)
    (heapFits : heap.size ≤ 2 ^ width)
    (source : heap[cursor]'cursorBound = word width identifier)
    (block : BlockAt program base (code width base layout)) :
    programStep program (UniformDAGScan.state (heap) (base + 24) (word width cursor) (word width identifier) (temporary) (word width (remaining + 1)) stack output) = some (UniformDAGScan.state (heap) (base + 25) (word width cursor) (word width identifier) (word width layout.markerBase) (word width (remaining + 1)) stack output) := by
  have pcFits (offset : ℕ) (inside : offset ≤ 54) : base + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left inside base) programFits
  rw [fetched program _ base 24 layout (by rfl) (pcFits 24 (by decide)) (by decide) block]
  change step (.constant 2 (word width layout.markerBase)) (UniformDAGScan.state (heap) (base + 24) (word width cursor) (word width identifier) (temporary) (word width (remaining + 1)) stack output) = some (UniformDAGScan.state (heap) (base + 25) (word width cursor) (word width identifier) (word width layout.markerBase) (word width (remaining + 1)) stack output)
  have pcValue : (base + 24) % 2 ^ width = base + 24 := Nat.mod_eq_of_lt (pcFits 24 (by decide))
  simp [step, UniformDAGScan.state, State.advance, State.put, word, pcValue, Nat.add_assoc]
  all_goals try (congr 1; funext register; fin_cases register <;> simp)
  all_goals try (congr 1; omega)

private theorem guard_transition_3 (program : Program width 4) (heap : Array (Word width))
    (base : ℕ) (layout : Layout) (cursor identifier remaining : ℕ)
    (scratch temporary : Word width) (stack output : List (Word width))
    (programFits : base + 54 < 2 ^ width) (cursorFits : cursor + 1 < 2 ^ width)
    (countFits : remaining + 1 < 2 ^ width)
    (cursorBound : cursor < heap.size) (markerBound : layout.markerBase + identifier < heap.size)
    (heapFits : heap.size ≤ 2 ^ width)
    (source : heap[cursor]'cursorBound = word width identifier)
    (block : BlockAt program base (code width base layout)) :
    programStep program (UniformDAGScan.state (heap) (base + 25) (word width cursor) (word width identifier) (word width layout.markerBase) (word width (remaining + 1)) stack output) = some (UniformDAGScan.state (heap) (base + 26) (word width cursor) (word width (identifier + layout.markerBase)) (word width layout.markerBase) (word width (remaining + 1)) stack output) := by
  have pcFits (offset : ℕ) (inside : offset ≤ 54) : base + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left inside base) programFits
  rw [fetched program _ base 25 layout (by rfl) (pcFits 25 (by decide)) (by decide) block]
  change step (.add 1 1 2) (UniformDAGScan.state (heap) (base + 25) (word width cursor) (word width identifier) (word width layout.markerBase) (word width (remaining + 1)) stack output) = some (UniformDAGScan.state (heap) (base + 26) (word width cursor) (word width (identifier + layout.markerBase)) (word width layout.markerBase) (word width (remaining + 1)) stack output)
  have pcValue : (base + 25) % 2 ^ width = base + 25 := Nat.mod_eq_of_lt (pcFits 25 (by decide))
  have idValue : identifier % 2 ^ width = identifier := Nat.mod_eq_of_lt (by omega)
  have baseValue : layout.markerBase % 2 ^ width = layout.markerBase := Nat.mod_eq_of_lt (by omega)
  simp [step, UniformDAGScan.state, State.advance, State.put, word, pcValue, idValue, baseValue, Nat.add_assoc]
  all_goals try (congr 1; funext register; fin_cases register <;> simp)
  all_goals try (congr 1; omega)

private theorem guard_transition_4 (program : Program width 4) (heap : Array (Word width))
    (base : ℕ) (layout : Layout) (cursor identifier remaining : ℕ)
    (scratch temporary : Word width) (stack output : List (Word width))
    (programFits : base + 54 < 2 ^ width) (cursorFits : cursor + 1 < 2 ^ width)
    (countFits : remaining + 1 < 2 ^ width)
    (cursorBound : cursor < heap.size) (markerBound : layout.markerBase + identifier < heap.size)
    (heapFits : heap.size ≤ 2 ^ width)
    (source : heap[cursor]'cursorBound = word width identifier)
    (block : BlockAt program base (code width base layout)) :
    programStep program (UniformDAGScan.state (heap) (base + 26) (word width cursor) (word width (identifier + layout.markerBase)) (word width layout.markerBase) (word width (remaining + 1)) stack output) = some (UniformDAGScan.state (heap) (base + 27) (word width cursor) (word width (identifier + layout.markerBase)) (word width 1) (word width (remaining + 1)) stack output) := by
  have pcFits (offset : ℕ) (inside : offset ≤ 54) : base + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left inside base) programFits
  rw [fetched program _ base 26 layout (by rfl) (pcFits 26 (by decide)) (by decide) block]
  change step (.constant 2 (word width 1)) (UniformDAGScan.state (heap) (base + 26) (word width cursor) (word width (identifier + layout.markerBase)) (word width layout.markerBase) (word width (remaining + 1)) stack output) = some (UniformDAGScan.state (heap) (base + 27) (word width cursor) (word width (identifier + layout.markerBase)) (word width 1) (word width (remaining + 1)) stack output)
  have pcValue : (base + 26) % 2 ^ width = base + 26 := Nat.mod_eq_of_lt (pcFits 26 (by decide))
  simp [step, UniformDAGScan.state, State.advance, State.put, word, pcValue, Nat.add_assoc]
  all_goals try (congr 1; funext register; fin_cases register <;> simp)
  all_goals try (congr 1; omega)

private theorem guard_transition_5 (program : Program width 4) (heap : Array (Word width))
    (base : ℕ) (layout : Layout) (cursor identifier remaining : ℕ)
    (scratch temporary : Word width) (stack output : List (Word width))
    (programFits : base + 54 < 2 ^ width) (cursorFits : cursor + 1 < 2 ^ width)
    (countFits : remaining + 1 < 2 ^ width)
    (cursorBound : cursor < heap.size) (markerBound : layout.markerBase + identifier < heap.size)
    (heapFits : heap.size ≤ 2 ^ width)
    (source : heap[cursor]'cursorBound = word width identifier)
    (block : BlockAt program base (code width base layout)) :
    programStep program (UniformDAGScan.state (heap) (base + 27) (word width cursor) (word width (identifier + layout.markerBase)) (word width 1) (word width (remaining + 1)) stack output) = some (UniformDAGScan.state (heap.setIfInBounds (layout.markerBase + identifier) (word width 1)) (base + 28) (word width cursor) (word width (identifier + layout.markerBase)) (word width 1) (word width (remaining + 1)) stack output) := by
  have pcFits (offset : ℕ) (inside : offset ≤ 54) : base + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left inside base) programFits
  rw [fetched program _ base 27 layout (by rfl) (pcFits 27 (by decide)) (by decide) block]
  change step (.store 1 2) (UniformDAGScan.state (heap) (base + 27) (word width cursor) (word width (identifier + layout.markerBase)) (word width 1) (word width (remaining + 1)) stack output) = some (UniformDAGScan.state (heap.setIfInBounds (layout.markerBase + identifier) (word width 1)) (base + 28) (word width cursor) (word width (identifier + layout.markerBase)) (word width 1) (word width (remaining + 1)) stack output)
  have pcValue : (base + 27) % 2 ^ width = base + 27 := Nat.mod_eq_of_lt (pcFits 27 (by decide))
  have addressValue : (identifier + layout.markerBase) % 2 ^ width = identifier + layout.markerBase := Nat.mod_eq_of_lt (by omega)
  have actualBound : identifier + layout.markerBase < heap.size := by omega
  simp [step, UniformDAGScan.state, State.advance, State.put, word, pcValue, addressValue, actualBound, Array.setIfInBounds_def, Nat.add_comm, Nat.add_assoc]
  all_goals try (congr 1; funext register; fin_cases register <;> simp)
  all_goals try (congr 1; omega)

private theorem guard_transition_6 (program : Program width 4) (heap : Array (Word width))
    (base : ℕ) (layout : Layout) (cursor identifier remaining : ℕ)
    (scratch temporary : Word width) (stack output : List (Word width))
    (programFits : base + 54 < 2 ^ width) (cursorFits : cursor + 1 < 2 ^ width)
    (countFits : remaining + 1 < 2 ^ width)
    (cursorBound : cursor < heap.size) (markerBound : layout.markerBase + identifier < heap.size)
    (heapFits : heap.size ≤ 2 ^ width)
    (source : heap[cursor]'cursorBound = word width identifier)
    (block : BlockAt program base (code width base layout)) :
    programStep program (UniformDAGScan.state (heap.setIfInBounds (layout.markerBase + identifier) (word width 1)) (base + 28) (word width cursor) (word width (identifier + layout.markerBase)) (word width 1) (word width (remaining + 1)) stack output) = some (UniformDAGScan.state (heap.setIfInBounds (layout.markerBase + identifier) (word width 1)) (base + 29) (word width (cursor + 1)) (word width (identifier + layout.markerBase)) (word width 1) (word width (remaining + 1)) stack output) := by
  have pcFits (offset : ℕ) (inside : offset ≤ 54) : base + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left inside base) programFits
  rw [fetched program _ base 28 layout (by rfl) (pcFits 28 (by decide)) (by decide) block]
  change step (.add 0 0 2) (UniformDAGScan.state (heap.setIfInBounds (layout.markerBase + identifier) (word width 1)) (base + 28) (word width cursor) (word width (identifier + layout.markerBase)) (word width 1) (word width (remaining + 1)) stack output) = some (UniformDAGScan.state (heap.setIfInBounds (layout.markerBase + identifier) (word width 1)) (base + 29) (word width (cursor + 1)) (word width (identifier + layout.markerBase)) (word width 1) (word width (remaining + 1)) stack output)
  have pcValue : (base + 28) % 2 ^ width = base + 28 := Nat.mod_eq_of_lt (pcFits 28 (by decide))
  have cursorValue : cursor % 2 ^ width = cursor := Nat.mod_eq_of_lt (by omega)
  have oneValue : 1 % 2 ^ width = 1 := Nat.mod_eq_of_lt (by omega)
  simp [step, UniformDAGScan.state, State.advance, State.put, word, pcValue, cursorValue, oneValue, Nat.add_assoc]
  all_goals try (congr 1; funext register; fin_cases register <;> simp)
  all_goals try (congr 1; omega)

private theorem guard_transition_7 (program : Program width 4) (heap : Array (Word width))
    (base : ℕ) (layout : Layout) (cursor identifier remaining : ℕ)
    (scratch temporary : Word width) (stack output : List (Word width))
    (programFits : base + 54 < 2 ^ width) (cursorFits : cursor + 1 < 2 ^ width)
    (countFits : remaining + 1 < 2 ^ width)
    (cursorBound : cursor < heap.size) (markerBound : layout.markerBase + identifier < heap.size)
    (heapFits : heap.size ≤ 2 ^ width)
    (source : heap[cursor]'cursorBound = word width identifier)
    (block : BlockAt program base (code width base layout)) :
    programStep program (UniformDAGScan.state (heap.setIfInBounds (layout.markerBase + identifier) (word width 1)) (base + 29) (word width (cursor + 1)) (word width (identifier + layout.markerBase)) (word width 1) (word width (remaining + 1)) stack output) = some (UniformDAGScan.state (heap.setIfInBounds (layout.markerBase + identifier) (word width 1)) (base + 30) (word width (cursor + 1)) (word width (identifier + layout.markerBase)) (word width (2 ^ width - 1)) (word width (remaining + 1)) stack output) := by
  have pcFits (offset : ℕ) (inside : offset ≤ 54) : base + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left inside base) programFits
  rw [fetched program _ base 29 layout (by rfl) (pcFits 29 (by decide)) (by decide) block]
  change step (.constant 2 (word width (2 ^ width - 1))) (UniformDAGScan.state (heap.setIfInBounds (layout.markerBase + identifier) (word width 1)) (base + 29) (word width (cursor + 1)) (word width (identifier + layout.markerBase)) (word width 1) (word width (remaining + 1)) stack output) = some (UniformDAGScan.state (heap.setIfInBounds (layout.markerBase + identifier) (word width 1)) (base + 30) (word width (cursor + 1)) (word width (identifier + layout.markerBase)) (word width (2 ^ width - 1)) (word width (remaining + 1)) stack output)
  have pcValue : (base + 29) % 2 ^ width = base + 29 := Nat.mod_eq_of_lt (pcFits 29 (by decide))
  simp [step, UniformDAGScan.state, State.advance, State.put, word, pcValue, Nat.add_assoc]
  all_goals try (congr 1; funext register; fin_cases register <;> simp)
  all_goals try (congr 1; omega)

private theorem guard_transition_8 (program : Program width 4) (heap : Array (Word width))
    (base : ℕ) (layout : Layout) (cursor identifier remaining : ℕ)
    (scratch temporary : Word width) (stack output : List (Word width))
    (programFits : base + 54 < 2 ^ width) (cursorFits : cursor + 1 < 2 ^ width)
    (countFits : remaining + 1 < 2 ^ width)
    (cursorBound : cursor < heap.size) (markerBound : layout.markerBase + identifier < heap.size)
    (heapFits : heap.size ≤ 2 ^ width)
    (source : heap[cursor]'cursorBound = word width identifier)
    (block : BlockAt program base (code width base layout)) :
    programStep program (UniformDAGScan.state (heap.setIfInBounds (layout.markerBase + identifier) (word width 1)) (base + 30) (word width (cursor + 1)) (word width (identifier + layout.markerBase)) (word width (2 ^ width - 1)) (word width (remaining + 1)) stack output) = some (UniformDAGScan.state (heap.setIfInBounds (layout.markerBase + identifier) (word width 1)) (base + 31) (word width (cursor + 1)) (word width (identifier + layout.markerBase)) (word width (2 ^ width - 1)) (word width remaining) stack output) := by
  have pcFits (offset : ℕ) (inside : offset ≤ 54) : base + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left inside base) programFits
  rw [fetched program _ base 30 layout (by rfl) (pcFits 30 (by decide)) (by decide) block]
  change step (.add 3 3 2) (UniformDAGScan.state (heap.setIfInBounds (layout.markerBase + identifier) (word width 1)) (base + 30) (word width (cursor + 1)) (word width (identifier + layout.markerBase)) (word width (2 ^ width - 1)) (word width (remaining + 1)) stack output) = some (UniformDAGScan.state (heap.setIfInBounds (layout.markerBase + identifier) (word width 1)) (base + 31) (word width (cursor + 1)) (word width (identifier + layout.markerBase)) (word width (2 ^ width - 1)) (word width remaining) stack output)
  have pcValue : (base + 30) % 2 ^ width = base + 30 := Nat.mod_eq_of_lt (pcFits 30 (by decide))
  have countValue : (remaining + 1) % 2 ^ width = remaining + 1 := Nat.mod_eq_of_lt countFits
  have remainingValue : remaining % 2 ^ width = remaining := Nat.mod_eq_of_lt (by omega)
  have decrementValue : (2 ^ width - 1) % 2 ^ width = 2 ^ width - 1 :=
    Nat.mod_eq_of_lt (Nat.sub_lt (Nat.two_pow_pos width) (by decide))
  have wrap : remaining + 1 + (2 ^ width - 1) = 2 ^ width + remaining := by
    have := Nat.two_pow_pos width
    omega
  have arithmetic : (remaining + (1 + (2 ^ width - 1))) % 2 ^ width = remaining := by
    rw [← Nat.add_assoc, wrap, Nat.add_mod_left, remainingValue]
  simp [step, UniformDAGScan.state, State.advance, State.put, word, pcValue, countValue, remainingValue, decrementValue, arithmetic, Nat.add_assoc]
  all_goals try (congr 1; funext register; fin_cases register <;> simp)
  all_goals try (congr 1; omega)

private theorem guard_transition_9 (program : Program width 4) (heap : Array (Word width))
    (base : ℕ) (layout : Layout) (cursor identifier remaining : ℕ)
    (scratch temporary : Word width) (stack output : List (Word width))
    (programFits : base + 54 < 2 ^ width) (cursorFits : cursor + 1 < 2 ^ width)
    (countFits : remaining + 1 < 2 ^ width)
    (cursorBound : cursor < heap.size) (markerBound : layout.markerBase + identifier < heap.size)
    (heapFits : heap.size ≤ 2 ^ width)
    (source : heap[cursor]'cursorBound = word width identifier)
    (block : BlockAt program base (code width base layout)) :
    programStep program (UniformDAGScan.state (heap.setIfInBounds (layout.markerBase + identifier) (word width 1)) (base + 31) (word width (cursor + 1)) (word width (identifier + layout.markerBase)) (word width (2 ^ width - 1)) (word width remaining) stack output) = some (UniformDAGScan.state (heap.setIfInBounds (layout.markerBase + identifier) (word width 1)) (base + 32) (word width (cursor + 1)) (word width (identifier + layout.markerBase)) (word width 0) (word width remaining) stack output) := by
  have pcFits (offset : ℕ) (inside : offset ≤ 54) : base + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left inside base) programFits
  rw [fetched program _ base 31 layout (by rfl) (pcFits 31 (by decide)) (by decide) block]
  change step (.constant 2 (word width 0)) (UniformDAGScan.state (heap.setIfInBounds (layout.markerBase + identifier) (word width 1)) (base + 31) (word width (cursor + 1)) (word width (identifier + layout.markerBase)) (word width (2 ^ width - 1)) (word width remaining) stack output) = some (UniformDAGScan.state (heap.setIfInBounds (layout.markerBase + identifier) (word width 1)) (base + 32) (word width (cursor + 1)) (word width (identifier + layout.markerBase)) (word width 0) (word width remaining) stack output)
  have pcValue : (base + 31) % 2 ^ width = base + 31 := Nat.mod_eq_of_lt (pcFits 31 (by decide))
  simp [step, UniformDAGScan.state, State.advance, State.put, word, pcValue, Nat.add_assoc]
  all_goals try (congr 1; funext register; fin_cases register <;> simp)
  all_goals try (congr 1; omega)

private theorem guard_transition_10 (program : Program width 4) (heap : Array (Word width))
    (base : ℕ) (layout : Layout) (cursor identifier remaining : ℕ)
    (scratch temporary : Word width) (stack output : List (Word width))
    (programFits : base + 54 < 2 ^ width) (cursorFits : cursor + 1 < 2 ^ width)
    (countFits : remaining + 1 < 2 ^ width)
    (cursorBound : cursor < heap.size) (markerBound : layout.markerBase + identifier < heap.size)
    (heapFits : heap.size ≤ 2 ^ width)
    (source : heap[cursor]'cursorBound = word width identifier)
    (block : BlockAt program base (code width base layout)) :
    programStep program (UniformDAGScan.state (heap.setIfInBounds (layout.markerBase + identifier) (word width 1)) (base + 32) (word width (cursor + 1)) (word width (identifier + layout.markerBase)) (word width 0) (word width remaining) stack output) = some (UniformDAGScan.state (heap.setIfInBounds (layout.markerBase + identifier) (word width 1)) (base + 22) (word width (cursor + 1)) (word width (identifier + layout.markerBase)) (word width 0) (word width remaining) stack output) := by
  have pcFits (offset : ℕ) (inside : offset ≤ 54) : base + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left inside base) programFits
  rw [fetched program _ base 32 layout (by rfl) (pcFits 32 (by decide)) (by decide) block]
  change step (.branchZero 2 (word width (base + 22))) (UniformDAGScan.state (heap.setIfInBounds (layout.markerBase + identifier) (word width 1)) (base + 32) (word width (cursor + 1)) (word width (identifier + layout.markerBase)) (word width 0) (word width remaining) stack output) = some (UniformDAGScan.state (heap.setIfInBounds (layout.markerBase + identifier) (word width 1)) (base + 22) (word width (cursor + 1)) (word width (identifier + layout.markerBase)) (word width 0) (word width remaining) stack output)
  have pcValue : (base + 32) % 2 ^ width = base + 32 := Nat.mod_eq_of_lt (pcFits 32 (by decide))
  simp [step, UniformDAGScan.state, State.advance, State.put, word, pcValue, Nat.add_assoc]
  all_goals try (congr 1; funext register; fin_cases register <;> simp)
  all_goals try (congr 1; omega)

private theorem guard_transitions (program : Program width 4) (heap : Array (Word width))
    (base : ℕ) (layout : Layout) (cursor identifier remaining : ℕ)
    (scratch temporary : Word width) (stack output : List (Word width))
    (programFits : base + 54 < 2 ^ width) (cursorFits : cursor + 1 < 2 ^ width)
    (countFits : remaining + 1 < 2 ^ width)
    (cursorBound : cursor < heap.size) (markerBound : layout.markerBase + identifier < heap.size)
    (heapFits : heap.size ≤ 2 ^ width)
    (source : heap[cursor]'cursorBound = word width identifier)
    (block : BlockAt program base (code width base layout)) (index : Fin 11) :
    programStep program (guardPhases heap base layout cursor identifier remaining scratch temporary stack output index.val) =
      some (guardPhases heap base layout cursor identifier remaining scratch temporary stack output (index.val + 1)) := by
  fin_cases index
  · exact guard_transition_0 program heap base layout cursor identifier remaining scratch temporary
      stack output programFits cursorFits countFits cursorBound markerBound heapFits source block
  · exact guard_transition_1 program heap base layout cursor identifier remaining scratch temporary
      stack output programFits cursorFits countFits cursorBound markerBound heapFits source block
  · exact guard_transition_2 program heap base layout cursor identifier remaining scratch temporary
      stack output programFits cursorFits countFits cursorBound markerBound heapFits source block
  · exact guard_transition_3 program heap base layout cursor identifier remaining scratch temporary
      stack output programFits cursorFits countFits cursorBound markerBound heapFits source block
  · exact guard_transition_4 program heap base layout cursor identifier remaining scratch temporary
      stack output programFits cursorFits countFits cursorBound markerBound heapFits source block
  · exact guard_transition_5 program heap base layout cursor identifier remaining scratch temporary
      stack output programFits cursorFits countFits cursorBound markerBound heapFits source block
  · exact guard_transition_6 program heap base layout cursor identifier remaining scratch temporary
      stack output programFits cursorFits countFits cursorBound markerBound heapFits source block
  · exact guard_transition_7 program heap base layout cursor identifier remaining scratch temporary
      stack output programFits cursorFits countFits cursorBound markerBound heapFits source block
  · exact guard_transition_8 program heap base layout cursor identifier remaining scratch temporary
      stack output programFits cursorFits countFits cursorBound markerBound heapFits source block
  · exact guard_transition_9 program heap base layout cursor identifier remaining scratch temporary
      stack output programFits cursorFits countFits cursorBound markerBound heapFits source block
  · exact guard_transition_10 program heap base layout cursor identifier remaining scratch temporary
      stack output programFits cursorFits countFits cursorBound markerBound heapFits source block

private theorem constant_chain (program : Program width registers)
    (history : ℕ → State width registers) (count bound : ℕ)
    (transitions : ∀ index < count, programStep program (history index) = some (history (index + 1)))
    (live : ∀ index ≤ count, (history index).liveWords = bound) :
    Execution program (history 0) (history count) count bound := by
  induction count generalizing history with
  | zero => simpa only [live 0 (Nat.le_refl 0)] using Execution.refl (history 0)
  | succ count ih =>
      have tail := ih (fun index => history (index + 1))
        (fun index inside => transitions (index + 1) (by omega))
        (fun index inside => live (index + 1) (by omega))
      have whole := Execution.cons (transitions 0 (by omega)) tail
      simpa only [live 0 (by omega), max_self, Nat.add_comm] using whole

/-- One actual guard-ID read and dynamic marker store uses eleven instructions
of the shared path program and ordinary decremented count. -/
theorem guard_entry (program : Program width 4) (heap : Array (Word width))
    (base : ℕ) (layout : Layout) (cursor identifier remaining : ℕ)
    (scratch temporary : Word width) (stack output : List (Word width))
    (programFits : base + 54 < 2 ^ width) (cursorFits : cursor + 1 < 2 ^ width)
    (countFits : remaining + 1 < 2 ^ width)
    (cursorBound : cursor < heap.size) (markerBound : layout.markerBase + identifier < heap.size)
    (heapFits : heap.size ≤ 2 ^ width)
    (source : heap[cursor]'cursorBound = word width identifier)
    (block : BlockAt program base (code width base layout)) :
    Execution program
      (UniformDAGScan.state heap (base + 22) (word width cursor) scratch temporary
        (word width (remaining + 1)) stack output)
      (UniformDAGScan.state (heap.setIfInBounds (layout.markerBase + identifier) (word width 1))
        (base + 22) (word width (cursor + 1)) (word width (identifier + layout.markerBase))
        (word width 0) (word width remaining) stack output)
      11 (5 + heap.size + stack.length + output.length) := by
  have trace := constant_chain program
    (guardPhases heap base layout cursor identifier remaining scratch temporary stack output)
    11 (5 + heap.size + stack.length + output.length)
    (by
      intro index inside
      exact guard_transitions program heap base layout cursor identifier remaining scratch temporary
        stack output programFits cursorFits countFits cursorBound markerBound heapFits source block ⟨index, inside⟩)
    (by intro index inside; interval_cases index <;>
          simp [guardPhases, UniformDAGScan.state, State.liveWords] <;> omega)
  exact trace

/-- Zero remaining labels use the actual shared guard-loop exit branch. -/
theorem guard_zero (program : Program width 4) (heap : Array (Word width))
    (base : ℕ) (layout : Layout) (cursor scratch temporary : Word width)
    (stack output : List (Word width)) (programFits : base + 54 < 2 ^ width)
    (block : BlockAt program base (code width base layout)) :
    Execution program
      (UniformDAGScan.state heap (base + 22) cursor scratch temporary (word width 0) stack output)
      (UniformDAGScan.state heap (base + 33) cursor scratch temporary (word width 0) stack output)
      1 (5 + heap.size + stack.length + output.length) := by
  have entry : program[base + 22]? = some (.branchZero 3 (word width (base + 33))) := by
    simpa [code] using block 22 (by simp [code])
  have fits : base + 22 < 2 ^ width := by omega
  have transition : programStep program
      (UniformDAGScan.state heap (base + 22) cursor scratch temporary (word width 0) stack output) =
        some (UniformDAGScan.state heap (base + 33) cursor scratch temporary (word width 0) stack output) := by
    unfold programStep
    rw [show (UniformDAGScan.state heap (base + 22) cursor scratch temporary (word width 0) stack output).pc.val = base + 22 from Nat.mod_eq_of_lt fits, entry]
    simp [step, UniformDAGScan.state, State.advance, word]
  have trace := Execution.cons transition (Execution.refl
    (UniformDAGScan.state heap (base + 33) cursor scratch temporary (word width 0) stack output))
  convert trace using 1 <;> simp [UniformDAGScan.state, State.liveWords] <;> omega

/-- Semantic image of the actual marker stores. Label lists annotate fetched
source occurrences; this definition does not supply a machine input list. -/
def markLabels (heap : Array (Word width)) (markerBase : ℕ) :
    List (Channel n) → Array (Word width)
  | [] => heap
  | label :: rest => markLabels (heap.setIfInBounds (markerBase + label.val) (word width 1)) markerBase rest

@[simp] theorem markLabels_size (heap : Array (Word width)) (markerBase : ℕ)
    (labels : List (Channel n)) : (markLabels heap markerBase labels).size = heap.size := by
  induction labels generalizing heap with
  | nil => rfl
  | cons label rest ih => simp only [markLabels, ih, Array.size_setIfInBounds]

/-- Dynamic guard stores cannot change a source packet preceding the marker
region. This includes cached headers, arities, bases and future source IDs. -/
theorem markLabels_prefix (heap : Array (Word width)) (markerBase : ℕ)
    (labels : List (Channel n)) (region : markerBase + n ≤ heap.size)
    (address : ℕ) (beforeMarkers : address < markerBase) :
    (markLabels heap markerBase labels)[address]'(by rw [markLabels_size]; omega) =
      heap[address]'(by omega) := by
  induction labels generalizing heap with
  | nil => rfl
  | cons label rest ih =>
      have written : markerBase + label.val < heap.size := by have := label.isLt; omega
      have preserved : (heap.setIfInBounds (markerBase + label.val) (word width 1))[address]'(by simp only [Array.size_setIfInBounds]; omega) = heap[address]'(by omega) := by
        exact Array.getElem_setIfInBounds_ne (by omega) (by omega)
      have later := ih (heap.setIfInBounds (markerBase + label.val) (word width 1))
        (by simpa only [Array.size_setIfInBounds] using region)
      exact later.trans preserved

/-- Repeated labels set the same bit idempotently. The final marker cells
represent the union of the initial blocked set and all fetched guard labels. -/
theorem markLabels_cells (heap : Array (Word width)) (markerBase : ℕ)
    (blocked : Finset (Channel n)) (labels : List (Channel n))
    (region : markerBase + n ≤ heap.size)
    (cells : ∀ coordinate : Channel n,
      heap[markerBase + coordinate.val]'(by have := coordinate.isLt; omega) =
        boolWord width (decide (coordinate ∈ blocked))) :
    ∀ coordinate : Channel n,
      (markLabels heap markerBase labels)[markerBase + coordinate.val]'
        (by rw [markLabels_size]; have := coordinate.isLt; omega) =
        boolWord width (decide (coordinate ∈ blocked ∪ labels.toFinset)) := by
  induction labels generalizing heap blocked with
  | nil => intro coordinate; simpa only [markLabels, List.toFinset_nil, Finset.union_empty] using cells coordinate
  | cons label rest ih =>
      have written : markerBase + label.val < heap.size := by have := label.isLt; omega
      have newCells : ∀ coordinate : Channel n,
          (heap.setIfInBounds (markerBase + label.val) (word width 1))[markerBase + coordinate.val]'
            (by simp only [Array.size_setIfInBounds]; have := coordinate.isLt; omega) =
          boolWord width (decide (coordinate ∈ insert label blocked)) := by
        intro coordinate
        by_cases same : coordinate = label
        · subst coordinate
          simp [Array.setIfInBounds_def, written, boolWord]
        · have different : markerBase + label.val ≠ markerBase + coordinate.val := by
            intro equal
            apply same
            apply Fin.ext
            omega
          have preserved : (heap.setIfInBounds (markerBase + label.val) (word width 1))[markerBase + coordinate.val]'(by simp only [Array.size_setIfInBounds]; have := coordinate.isLt; omega) =
              heap[markerBase + coordinate.val]'(by have := coordinate.isLt; omega) := by
            exact Array.getElem_setIfInBounds_ne (by have := coordinate.isLt; omega) different
          rw [preserved, cells coordinate]
          simp only [Finset.mem_insert, same, false_or]
      have later := ih (heap.setIfInBounds (markerBase + label.val) (word width 1)) (insert label blocked)
        (by simpa only [Array.size_setIfInBounds] using region) newCells
      have sets : insert label blocked ∪ rest.toFinset = blocked ∪ (label :: rest).toFinset := by
        ext coordinate
        simp [or_assoc, or_left_comm, or_comm]
      intro coordinate
      simpa only [markLabels, sets] using later coordinate

/-- Each fetched guard occurrence lies in the unchanged source prefix. -/
inductive GuardStream (heap : Array (Word width)) (markerBase : ℕ) :
    ℕ → List (Channel n) → Prop
  | nil (cursor) : GuardStream heap markerBase cursor []
  | cons {cursor label rest} (before : cursor < markerBase) (valid : cursor < heap.size)
      (source : heap[cursor]'valid = word width label.val)
      (tail : GuardStream heap markerBase (cursor + 1) rest) :
      GuardStream heap markerBase cursor (label :: rest)

/-- Exact source-coordinate cells derive a guard stream without supplying an
independent runtime list. The list indexes only the physical fetched cells. -/
theorem guardStream_of_cells (heap : Array (Word width)) (markerBase cursor : ℕ)
    (labels : List (Channel n)) (markerBound : markerBase ≤ heap.size)
    (sourceBounds : ∀ slot, (valid : slot < labels.length) → cursor + slot < markerBase)
    (sourceCells : ∀ slot, (valid : slot < labels.length) →
      heap[cursor + slot]'(by have := sourceBounds slot valid; omega) =
        word width (labels[slot]'valid).val) :
    GuardStream heap markerBase cursor labels := by
  induction labels generalizing cursor with
  | nil => exact GuardStream.nil cursor
  | cons label rest ih =>
      have before : cursor < markerBase := by simpa using sourceBounds 0 (by simp)
      have valid : cursor < heap.size := by omega
      have first := sourceCells 0 (by simp)
      have stored : heap[cursor]'valid = word width label.val := by simpa only [Nat.add_zero, List.getElem_cons_zero] using first
      refine GuardStream.cons before valid stored ?_
      have tailBounds : ∀ slot, (valid : slot < rest.length) → cursor + 1 + slot < markerBase := by
        intro slot valid
        have bound := sourceBounds (slot + 1) (by simpa using valid)
        omega
      have tailCells : ∀ slot, (valid : slot < rest.length) →
          heap[cursor + 1 + slot]'(by have := tailBounds slot valid; omega) = word width (rest[slot]'valid).val := by
        intro slot valid
        have validNext : slot + 1 < (label :: rest).length := by simpa using valid
        have next := sourceCells (slot + 1) validNext
        simpa only [List.getElem_cons_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using next
      exact ih (cursor + 1) tailBounds tailCells

/-- The loaded typed packet provides all guard IDs at their actual source
coordinates; the appended marker table does not replace those source cells. -/
theorem typed_guardStream (heap : Array (Word width)) (graph : DAG n)
    (rows : List Controller.Cost.ForestIndexedOperands.Row) (roots : List ℕ)
    (corresponds : Controller.Cost.ForestIndexedOperands.RowsMatch graph rows)
    (node : Fin graph.nodeCount) (markers : Channel n → Bool) :
    let cache := Controller.Cost.ForestIndexedOperands.cacheHeap width heap rows roots
    GuardStream (Controller.Cost.ForestInputStored.withValues cache markers) cache.size
      (heap.size + 6 * rows.length +
        (Controller.Cost.ForestIndexedOperands.rowChildren rows).length +
        (Controller.Cost.ForestIndexedOperands.rowGuards (rows.take node.val)).length)
      (graph.node node).guardLabels := by
  dsimp only
  have bounds : ∀ slot, (valid : slot < (graph.node node).guardLabels.length) →
    heap.size + 6 * rows.length + (rowChildren rows).length +
        (rowGuards (rows.take node.val)).length + slot < (cacheHeap width heap rows roots).size := by
    intro slot valid
    have rowValid : node.val < rows.length := by rw [corresponds.length_eq]; exact node.isLt
    have split := row_guards_split rows node.val rowValid
    have rowGuardsEq := (corresponds.node node).2.2.2
    have lengths := congrArg List.length split
    simp only [List.length_append, rowGuardsEq, List.length_map] at lengths
    simp only [cacheHeap_size]
    omega
  refine guardStream_of_cells _ _ _ _ (by simp only [withValues_size]; omega) bounds ?_
  intro slot valid
  exact (source_preserved _ markers _ (bounds slot valid)).trans
    (typed_guard_cell heap graph rows roots corresponds node slot valid)


/-- The dynamic marker store preserves every not-yet-read source ID. -/
theorem guardStream_store (heap : Array (Word width)) (markerBase : ℕ)
    (cursor : ℕ) (labels : List (Channel n)) (stream : GuardStream heap markerBase cursor labels)
    (region : markerBase + n ≤ heap.size) (label : Channel n) :
    GuardStream (heap.setIfInBounds (markerBase + label.val) (word width 1)) markerBase cursor labels := by
  induction stream with
  | nil cursor => exact GuardStream.nil cursor
  | cons before valid source tail ih =>
      have written : markerBase + label.val < heap.size := by have := label.isLt; omega
      refine GuardStream.cons before (by simpa only [Array.size_setIfInBounds] using valid) ?_ ih
      exact (Array.getElem_setIfInBounds_ne valid (by omega)).trans source

/-- The same fixed guard loop marks the complete actual stored stream,
including duplicate channel IDs, without touching the packet or stack. -/
theorem guard_execution (program : Program width 4) (heap : Array (Word width))
    (base : ℕ) (layout : Layout) (cursor : ℕ) (labels : List (Channel n))
    (scratch temporary : Word width) (stack output : List (Word width))
    (programFits : base + 54 < 2 ^ width) (cursorFits : cursor + labels.length < 2 ^ width)
    (countFits : labels.length < 2 ^ width) (region : layout.markerBase + n ≤ heap.size)
    (heapFits : heap.size ≤ 2 ^ width)
    (stream : GuardStream heap layout.markerBase cursor labels)
    (block : BlockAt program base (code width base layout)) :
    ∃ finalScratch finalTemporary,
      Execution program
        (UniformDAGScan.state heap (base + 22) (word width cursor) scratch temporary
          (word width labels.length) stack output)
        (UniformDAGScan.state (markLabels heap layout.markerBase labels) (base + 33)
          (word width (cursor + labels.length)) finalScratch finalTemporary (word width 0) stack output)
        (11 * labels.length + 1) (5 + heap.size + stack.length + output.length) := by
  induction labels generalizing heap cursor scratch temporary with
  | nil =>
      exact ⟨scratch, temporary, by simpa [markLabels] using (guard_zero program heap base layout
        (word width cursor) scratch temporary stack output programFits block)⟩
  | cons label rest ih =>
    cases stream with
    | cons before valid source tail =>
        have markerBound : layout.markerBase + label.val < heap.size := by have := label.isLt; omega
        have first := guard_entry program heap base layout cursor label.val rest.length scratch temporary
          stack output programFits (by simp only [List.length_cons] at cursorFits; omega)
          (by simpa only [List.length_cons] using countFits) valid markerBound heapFits source block
        have nextStream := guardStream_store heap layout.markerBase (cursor + 1) rest tail region label
        obtain ⟨finalScratch, finalTemporary, later⟩ := ih
          (heap.setIfInBounds (layout.markerBase + label.val) (word width 1)) (cursor + 1)
          (word width (label.val + layout.markerBase)) (word width 0)
          (by simp only [List.length_cons] at cursorFits; omega) (by simp only [List.length_cons] at countFits; omega)
          (by simpa only [Array.size_setIfInBounds] using region) (by simpa only [Array.size_setIfInBounds] using heapFits)
          nextStream
        have joined := first.append later
        refine ⟨finalScratch, finalTemporary, ?_⟩
        convert joined using 1 <;> simp only [markLabels, List.length_cons, Array.size_setIfInBounds, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.max_self] <;> omega

end Controller.Cost.ForestWitnessPath
