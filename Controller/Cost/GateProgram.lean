module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.Decoder

@[expose] public section

/-! Concrete decoder gate instruction blocks. The heap prefix holds channel
values followed by earlier node values. Program counters and heap addresses
are natural offsets encoded as words; execution requires representability.
Block-size proofs count stored code, not executed instructions or compilation
cost. Gate simulation and whole-decoder composition are separate obligations. -/
namespace Controller.Cost.GateProgram

open Controller.Decoder

/-- Registers: address, loaded value, accumulated result, and constant zero. -/
abbrev Code (width : Nat) := List (Instruction width 4)

/-- Set the accumulator to true when this stored child is true. -/
def orCell (width base address : Nat) : Code width :=
  [.constant 0 (word width address), .load 1 0,
    .branchZero 1 (word width (base + 4)), .constant 2 (boolWord width true)]

/-- Set the accumulator to false when this guard channel is true. -/
def guardCell (width base address : Nat) : Code width :=
  [.constant 0 (word width address), .load 1 0,
    .branchZero 1 (word width (base + 4)), .constant 2 (boolWord width false)]

/-- Reset the accumulator precisely when the stored live child is false.
Register 3 must contain zero for the unconditional skip. -/
def andCell (width base address : Nat) : Code width :=
  [.constant 0 (word width address), .load 1 0,
    .branchZero 1 (word width (base + 4)),
    .branchZero 3 (word width (base + 5)), .constant 2 (boolWord width false)]

/-- Lay out cells consecutively with their actual absolute branch targets. -/
def cells (cell : Nat → Nat → Code width) (stride base : Nat) : List Nat → Code width
  | [] => []
  | address :: rest => cell base address ++ cells cell stride (base + stride) rest

theorem cells_length (cell : Nat → Nat → Code width) (stride : Nat)
    (fixed : ∀ base address, (cell base address).length = stride)
    (addresses : List Nat) (base : Nat) :
    (cells cell stride base addresses).length = stride * addresses.length := by
  induction addresses generalizing base with
  | nil => simp [cells]
  | cons address rest inductionHypothesis =>
    simp [cells, fixed, inductionHypothesis, Nat.mul_succ, Nat.add_comm]

/-- Each gate appends exactly one result cell. Repeated references and guards
are retained as repeated instruction cells. -/
def gateCode (width base : Nat) : Gate n available → Code width
  | .zero => [.constant 2 (boolWord width false), .allocate 2]
  | .input channel => [.constant 0 (word width channel.val), .load 2 0, .allocate 2]
  | .disj children =>
    [.constant 2 (boolWord width false)] ++
      cells (orCell width) 4 (base + 1) (children.map fun child => n + child.val) ++
      [.allocate 2]
  | .guard child labels =>
    [.constant 0 (word width (n + child.val)), .load 2 0] ++
      cells (guardCell width) 4 (base + 2) (labels.map Fin.val) ++ [.allocate 2]
  | .liveAnd left right =>
    [.constant 2 (boolWord width true)] ++
      cells (andCell width) 5 (base + 1) [n + left.val, n + right.val] ++ [.allocate 2]

/-- Exact static instruction count for every represented gate. -/
theorem gateCode_length (width base : Nat) (gate : Gate n available) :
    (gateCode width base gate).length = match gate with
      | .zero => 2
      | .input _ => 3
      | .disj children => 2 + 4 * children.length
      | .guard _ labels => 3 + 4 * labels.length
      | .liveAnd _ _ => 12 := by
  cases gate with
  | zero => rfl
  | input channel => rfl
  | disj children =>
    simp only [gateCode, List.length_append, List.length_cons, List.length_nil,
      cells_length (orCell width) 4 (by intros; rfl), List.length_map]
    omega
  | guard child labels =>
    simp only [gateCode, List.length_append, List.length_cons, List.length_nil,
      cells_length (guardCell width) 4 (by intros; rfl), List.length_map]
    omega
  | liveAnd left right => rfl

/-- The stored code length is linear in every gate and incidence occurrence. -/
theorem gateCode_length_le (width base : Nat) (gate : Gate n available) :
    (gateCode width base gate).length ≤
      12 * (1 + gate.children.length + gate.guardLabels.length) := by
  rw [gateCode_length]
  cases gate <;> simp [Gate.children, Gate.guardLabels] <;> omega

/-- Concrete four-register configuration at a gate-cell boundary. -/
def cellState (heap : Array (Word width)) (cursor : Nat)
    (address loaded : Word width) (accumulator : Bool) : State width 4 where
  reg := fun register => if register = 0 then address else if register = 1 then loaded
    else if register = 2 then boolWord width accumulator else word width 0
  heap := heap
  stack := []
  output := []
  pc := word width cursor
  halted := false

@[simp] theorem cellState_liveWords (heap : Array (Word width)) (cursor : Nat)
    (address loaded : Word width) (accumulator : Bool) :
    (cellState heap cursor address loaded accumulator).liveWords = 5 + heap.size := by
  simp [cellState, State.liveWords]
  omega

private theorem encoded_value (width value : Nat) (fits : value < 2 ^ width) :
    (word width value).val = value := Nat.mod_eq_of_lt fits

private theorem cellState_advance (heap : Array (Word width)) (cursor : Nat)
    (address loaded : Word width) (accumulator : Bool) (fits : cursor < 2 ^ width) :
    (cellState heap cursor address loaded accumulator).advance =
      cellState heap (cursor + 1) address loaded accumulator := by
  unfold State.advance cellState
  rw [encoded_value width cursor fits]

private theorem cellState_put_address (heap : Array (Word width)) (cursor : Nat)
    (address loaded next : Word width) (accumulator : Bool) :
    (cellState heap cursor address loaded accumulator).put 0 next =
      cellState heap cursor next loaded accumulator := by
  unfold State.put cellState
  congr 1
  funext register
  by_cases first : register = 0 <;> simp [first]

private theorem cellState_put_loaded (heap : Array (Word width)) (cursor : Nat)
    (address loaded next : Word width) (accumulator : Bool) :
    (cellState heap cursor address loaded accumulator).put 1 next =
      cellState heap cursor address next accumulator := by
  unfold State.put cellState
  congr 1
  funext register
  by_cases first : register = 0
  · subst register; simp
  · by_cases second : register = 1 <;> simp [first, second]

private theorem cellState_put_accumulator (heap : Array (Word width)) (cursor : Nat)
    (address loaded : Word width) (accumulator next : Bool) :
    (cellState heap cursor address loaded accumulator).put 2 (boolWord width next) =
      cellState heap cursor address loaded next := by
  unfold State.put cellState
  congr 1
  funext register
  by_cases first : register = 0
  · subst register; simp
  · by_cases second : register = 1
    · subst register; simp
    · by_cases third : register = 2 <;> simp [first, second, third]

/-- The first cell instruction loads its literal heap address. -/
theorem cell_address_transition (program : Program width 4) (heap : Array (Word width))
    (base address : Nat) (oldAddress oldLoaded : Word width) (accumulator : Bool)
    (fits : base < 2 ^ width)
    (fetched : program[base]? = some (.constant 0 (word width address))) :
    programStep program (cellState heap base oldAddress oldLoaded accumulator) =
      some (cellState heap (base + 1) (word width address) oldLoaded accumulator) := by
  unfold programStep
  rw [show (cellState heap base oldAddress oldLoaded accumulator).pc.val = base from
    encoded_value width base fits, fetched]
  change step (.constant (0 : Fin 4) (word width address))
    (cellState heap base oldAddress oldLoaded accumulator) = _
  simp only [step, cellState, Bool.false_eq_true, ite_false]
  change some ((cellState heap base oldAddress oldLoaded accumulator).advance.put 0
    (word width address)) = _
  rw [cellState_advance heap base oldAddress oldLoaded accumulator fits,
    cellState_put_address]
  rfl

/-- The second cell instruction reads a represented Boolean heap entry. -/
theorem cell_read_transition (program : Program width 4) (heap : Array (Word width))
    (cursor address : Nat) (oldLoaded : Word width) (accumulator value : Bool)
    (cursorFits : cursor < 2 ^ width) (addressFits : address < 2 ^ width)
    (valid : address < heap.size)
    (stored : heap[address] = boolWord width value)
    (fetched : program[cursor]? = some (.load 1 0)) :
    programStep program (cellState heap cursor (word width address) oldLoaded accumulator) =
      some (cellState heap (cursor + 1) (word width address) (boolWord width value) accumulator) := by
  unfold programStep
  rw [show (cellState heap cursor (word width address) oldLoaded accumulator).pc.val = cursor from
    encoded_value width cursor cursorFits, fetched]
  change step (.load (1 : Fin 4) (0 : Fin 4))
    (cellState heap cursor (word width address) oldLoaded accumulator) = _
  have held : (cellState heap cursor (word width address) oldLoaded accumulator).reg 0 =
      word width address := by simp [cellState]
  have readFits : ((cellState heap cursor (word width address) oldLoaded accumulator).reg 0).val < heap.size := by
    simpa [held, encoded_value width address addressFits] using valid
  simp only [step, cellState, Bool.false_eq_true, ite_false]
  change (if h : (word width address).val < heap.size then
    some ((cellState heap cursor (word width address) oldLoaded accumulator).advance.put 1
      heap[(word width address).val]) else none) = _
  rw [dite_eq_left (by simpa [encoded_value width address addressFits] using valid)]
  simp only [encoded_value width address addressFits, stored]
  rw [cellState_advance heap cursor (word width address) oldLoaded accumulator cursorFits,
    cellState_put_loaded]
  rfl

@[simp] theorem cellState_running (heap : Array (Word width)) (cursor : Nat)
    (address loaded : Word width) (accumulator : Bool) :
    (cellState heap cursor address loaded accumulator).halted = false := rfl

/-- The third instruction follows the represented heap Boolean. -/
theorem cell_branch_transition (program : Program width 4) (heap : Array (Word width))
    (cursor target : Nat) (address : Word width) (accumulator value : Bool)
    (cursorFits : cursor < 2 ^ width) (capacity : 1 < 2 ^ width)
    (fetched : program[cursor]? = some (.branchZero 1 (word width target))) :
    programStep program (cellState heap cursor address (boolWord width value) accumulator) =
      some (cellState heap (if value then cursor + 1 else target)
        address (boolWord width value) accumulator) := by
  unfold programStep
  rw [show (cellState heap cursor address (boolWord width value) accumulator).pc.val = cursor from
    encoded_value width cursor cursorFits, fetched]
  change step (.branchZero (1 : Fin 4) (word width target))
    (cellState heap cursor address (boolWord width value) accumulator) = _
  have held : (cellState heap cursor address (boolWord width value) accumulator).reg 1 =
      boolWord width value := by simp [cellState]
  simp only [step, cellState_running, Bool.false_eq_true, ite_false]
  rw [held, boolWord_val width capacity value,
    cellState_advance heap cursor address (boolWord width value) accumulator cursorFits]
  cases value <;> rfl

/-- A reached fourth instruction changes only the accumulated Boolean. -/
theorem cell_set_transition (program : Program width 4) (heap : Array (Word width))
    (cursor : Nat) (address loaded : Word width) (accumulator replacement : Bool)
    (fits : cursor < 2 ^ width)
    (fetched : program[cursor]? = some (.constant 2 (boolWord width replacement))) :
    programStep program (cellState heap cursor address loaded accumulator) =
      some (cellState heap (cursor + 1) address loaded replacement) := by
  unfold programStep
  rw [show (cellState heap cursor address loaded accumulator).pc.val = cursor from
    encoded_value width cursor fits, fetched]
  change step (.constant (2 : Fin 4) (boolWord width replacement))
    (cellState heap cursor address loaded accumulator) = _
  simp only [step, cellState_running, Bool.false_eq_true, ite_false]
  rw [cellState_advance heap cursor address loaded accumulator fits,
    cellState_put_accumulator]

/-- Complete execution of an OR/guard cell for every represented heap value.
Its final program counter points to the next cell or gate continuation. -/
theorem conditional_cell_execution (program : Program width 4) (heap : Array (Word width))
    (base address : Nat) (oldAddress oldLoaded : Word width)
    (accumulator value replacement : Bool)
    (programFits : base + 4 < 2 ^ width) (addressFits : address < 2 ^ width)
    (valid : address < heap.size) (stored : heap[address] = boolWord width value)
    (first : program[base]? = some (.constant 0 (word width address)))
    (second : program[base + 1]? = some (.load 1 0))
    (third : program[base + 2]? = some (.branchZero 1 (word width (base + 4))))
    (fourth : program[base + 3]? = some (.constant 2 (boolWord width replacement))) :
    Execution program (cellState heap base oldAddress oldLoaded accumulator)
      (cellState heap (base + 4) (word width address) (boolWord width value)
        (if value then replacement else accumulator))
      (if value then 4 else 3) (5 + heap.size) := by
  have addressStep := cell_address_transition program heap base address oldAddress oldLoaded
    accumulator (by omega) first
  have readStep := cell_read_transition program heap (base + 1) address oldLoaded accumulator value
    (by omega) addressFits valid stored second
  have branchStep := cell_branch_transition program heap (base + 2) (base + 4)
    (word width address) accumulator value (by omega) (by omega) third
  simp only [Nat.add_assoc] at readStep branchStep
  cases value with
  | false =>
    have path := Execution.cons addressStep (Execution.cons readStep
      (Execution.cons branchStep (Execution.refl
        (cellState heap (base + 4) (word width address) (boolWord width false) accumulator))))
    simpa [cellState_liveWords] using path
  | true =>
    have setStep := cell_set_transition program heap (base + 3) (word width address)
      (boolWord width true) accumulator replacement (by omega) fourth
    simp only [Nat.add_assoc] at setStep
    have path := Execution.cons addressStep (Execution.cons readStep
      (Execution.cons branchStep (Execution.cons setStep (Execution.refl
        (cellState heap (base + 4) (word width address) (boolWord width true) replacement)))))
    simpa [cellState_liveWords] using path

/-- Fetched layout and represented inputs for successive OR/guard cells.
Every incidence is retained, including repeated addresses. -/
def ConditionalCellsStored (program : Program width 4) (heap : Array (Word width))
    (replacement : Bool) : Nat → List (Nat × Bool) → Prop
  | _, [] => True
  | base, (address, value) :: rest =>
    base + 4 < 2 ^ width ∧ address < 2 ^ width ∧
    ∃ valid : address < heap.size,
      heap[address] = boolWord width value ∧
      program[base]? = some (.constant 0 (word width address)) ∧
      program[base + 1]? = some (.load 1 0) ∧
      program[base + 2]? = some (.branchZero 1 (word width (base + 4))) ∧
      program[base + 3]? = some (.constant 2 (boolWord width replacement)) ∧
      ConditionalCellsStored program heap replacement (base + 4) rest

/-- A complete incidence loop executes at most four instructions per cell,
without growing its heap or temporary storage. The accumulator is the actual
ordered fold of the represented inputs. -/
theorem conditional_cells_execution (program : Program width 4)
    (heap : Array (Word width)) (replacement accumulator : Bool)
    (entries : List (Nat × Bool)) (base : Nat) (oldAddress oldLoaded : Word width)
    (stored : ConditionalCellsStored program heap replacement base entries) :
    ∃ finalAddress finalLoaded ticks,
      Execution program (cellState heap base oldAddress oldLoaded accumulator)
        (cellState heap (base + 4 * entries.length) finalAddress finalLoaded
          (entries.foldl (fun acc entry => if entry.2 then replacement else acc) accumulator))
        ticks (5 + heap.size) ∧ ticks ≤ 4 * entries.length := by
  induction entries generalizing base oldAddress oldLoaded accumulator with
  | nil =>
    refine ⟨oldAddress, oldLoaded, 0, ?_, by simp⟩
    simpa using Execution.refl (cellState heap base oldAddress oldLoaded accumulator)
  | cons entry rest inductionHypothesis =>
    rcases entry with ⟨address, value⟩
    rcases stored with ⟨programFits, addressFits, valid, valueStored,
      first, second, third, fourth, remaining⟩
    have firstTrace := conditional_cell_execution program heap base address oldAddress oldLoaded
      accumulator value replacement programFits addressFits valid valueStored
      first second third fourth
    obtain ⟨finalAddress, finalLoaded, ticks, restTrace, tickBound⟩ :=
      inductionHypothesis (if value then replacement else accumulator) (base + 4)
        (word width address) (boolWord width value) remaining
    refine ⟨finalAddress, finalLoaded, (if value then 4 else 3) + ticks, ?_, ?_⟩
    · have joined := firstTrace.append restTrace
      have cursor : base + 4 + 4 * rest.length = base + 4 * ((address, value) :: rest).length := by
        simp only [List.length_cons]; omega
      simpa only [cursor, List.foldl_cons, max_self] using joined
    · simp only [List.length_cons]
      cases value <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> omega

/-- Register three implements the unconditional skip in a live-AND cell. -/
theorem cell_zero_jump_transition (program : Program width 4) (heap : Array (Word width))
    (cursor target : Nat) (address loaded : Word width) (accumulator : Bool)
    (cursorFits : cursor < 2 ^ width)
    (fetched : program[cursor]? = some (.branchZero 3 (word width target))) :
    programStep program (cellState heap cursor address loaded accumulator) =
      some (cellState heap target address loaded accumulator) := by
  unfold programStep
  rw [show (cellState heap cursor address loaded accumulator).pc.val = cursor from
    encoded_value width cursor cursorFits, fetched]
  change step (.branchZero (3 : Fin 4) (word width target))
    (cellState heap cursor address loaded accumulator) = _
  simp only [step, cellState_running, Bool.false_eq_true, ite_false]
  have held : (cellState heap cursor address loaded accumulator).reg 3 = word width 0 := by
    simp [cellState]
  rw [held]
  simp only [word, Nat.zero_mod, Fin.val_mk, ite_true]
  rfl

/-- A live-AND cell executes four instructions for either stored Boolean. -/
theorem and_cell_execution (program : Program width 4) (heap : Array (Word width))
    (base address : Nat) (oldAddress oldLoaded : Word width) (accumulator value : Bool)
    (programFits : base + 5 < 2 ^ width) (addressFits : address < 2 ^ width)
    (valid : address < heap.size) (stored : heap[address] = boolWord width value)
    (first : program[base]? = some (.constant 0 (word width address)))
    (second : program[base + 1]? = some (.load 1 0))
    (third : program[base + 2]? = some (.branchZero 1 (word width (base + 4))))
    (fourth : program[base + 3]? = some (.branchZero 3 (word width (base + 5))))
    (fifth : program[base + 4]? = some (.constant 2 (boolWord width false))) :
    Execution program (cellState heap base oldAddress oldLoaded accumulator)
      (cellState heap (base + 5) (word width address) (boolWord width value)
        (accumulator && value)) 4 (5 + heap.size) := by
  have addressStep := cell_address_transition program heap base address oldAddress oldLoaded
    accumulator (by omega) first
  have readStep := cell_read_transition program heap (base + 1) address oldLoaded accumulator value
    (by omega) addressFits valid stored second
  have branchStep := cell_branch_transition program heap (base + 2) (base + 4)
    (word width address) accumulator value (by omega) (by omega) third
  simp only [Nat.add_assoc] at readStep branchStep
  cases value with
  | false =>
    have setStep := cell_set_transition program heap (base + 4) (word width address)
      (boolWord width false) accumulator false (by omega) fifth
    simp only [Nat.add_assoc] at setStep
    have path := Execution.cons addressStep (Execution.cons readStep
      (Execution.cons branchStep (Execution.cons setStep (Execution.refl
        (cellState heap (base + 5) (word width address) (boolWord width false) false)))))
    simpa [cellState_liveWords] using path
  | true =>
    have jumpStep := cell_zero_jump_transition program heap (base + 3) (base + 5)
      (word width address) (boolWord width true) accumulator (by omega) fourth
    have path := Execution.cons addressStep (Execution.cons readStep
      (Execution.cons branchStep (Execution.cons jumpStep (Execution.refl
        (cellState heap (base + 5) (word width address) (boolWord width true) accumulator)))))
    simpa [cellState_liveWords] using path

/-- Agreement with a concrete instruction block at its actual address. -/
def BlockAt (program : Program width 4) (base : Nat) (code : Code width) : Prop :=
  ∀ offset, offset < code.length → program[base + offset]? = code[offset]?

theorem BlockAt.prefix (program : Program width 4) (base : Nat)
    (first rest : Code width) (stored : BlockAt program base (first ++ rest)) :
    BlockAt program base first := by
  intro offset bound
  have whole := stored offset (by simp only [List.length_append]; omega)
  rw [List.getElem?_append_left bound] at whole
  exact whole

theorem BlockAt.suffix (program : Program width 4) (base : Nat)
    (first rest : Code width) (stored : BlockAt program base (first ++ rest)) :
    BlockAt program (base + first.length) rest := by
  intro offset bound
  have whole := stored (first.length + offset) (by simp only [List.length_append]; omega)
  rw [List.getElem?_append_right (by omega)] at whole
  simpa only [Nat.add_sub_cancel_left, Nat.add_assoc] using whole

/-- Common instruction cell instantiated by OR and negative guards. -/
def conditionalCell (width : Nat) (replacement : Bool) (base address : Nat) : Code width :=
  [.constant 0 (word width address), .load 1 0,
    .branchZero 1 (word width (base + 4)), .constant 2 (boolWord width replacement)]

/-- Every listed incidence supplies a representable address and a heap Boolean. -/
def EntriesStored (heap : Array (Word width)) (entries : List (Nat × Bool)) : Prop :=
  ∀ entry ∈ entries, entry.1 < 2 ^ width ∧
    ∃ valid : entry.1 < heap.size, heap[entry.1] = boolWord width entry.2

/-- Generated cells provide the fetched layout used by the loop theorem. -/
theorem conditionalCellsStored_of_block (program : Program width 4)
    (heap : Array (Word width)) (replacement : Bool) (entries : List (Nat × Bool))
    (base : Nat) (fits : base + 4 * entries.length < 2 ^ width)
    (values : EntriesStored heap entries)
    (block : BlockAt program base
      (cells (conditionalCell width replacement) 4 base (entries.map Prod.fst))) :
    ConditionalCellsStored program heap replacement base entries := by
  induction entries generalizing base with
  | nil => trivial
  | cons entry rest inductionHypothesis =>
    rcases entry with ⟨address, value⟩
    obtain ⟨addressFits, valid, valueStored⟩ := values (address, value) (by simp)
    simp only [cells, List.map_cons] at block
    have headBlock := BlockAt.prefix program base (conditionalCell width replacement base address)
      (cells (conditionalCell width replacement) 4 (base + 4) (rest.map Prod.fst)) block
    have tailBlock := BlockAt.suffix program base (conditionalCell width replacement base address)
      (cells (conditionalCell width replacement) 4 (base + 4) (rest.map Prod.fst)) block
    have first := headBlock 0 (by simp [conditionalCell])
    have second := headBlock 1 (by simp [conditionalCell])
    have third := headBlock 2 (by simp [conditionalCell])
    have fourth := headBlock 3 (by simp [conditionalCell])
    simp only [conditionalCell, List.length_cons, List.length_nil] at tailBlock
    simp only [conditionalCell, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Nat.add_zero] at first second third fourth
    refine ⟨by simp only [List.length_cons] at fits; omega, addressFits, valid, valueStored,
      first, second, third, fourth, ?_⟩
    apply inductionHypothesis (base + 4)
    · simp only [List.length_cons] at fits
      omega
    · intro item member
      exact values item (List.mem_cons_of_mem _ member)
    · exact tailBlock

/-- An allocation instruction appends the actual accumulator word. -/
theorem cell_allocate_transition (program : Program width 4)
    (heap : Array (Word width)) (cursor : Nat) (address loaded : Word width)
    (accumulator : Bool) (cursorFits : cursor < 2 ^ width)
    (heapFits : heap.size < 2 ^ width)
    (fetched : program[cursor]? = some (.allocate 2)) :
    programStep program (cellState heap cursor address loaded accumulator) =
      some (cellState (heap.push (boolWord width accumulator)) (cursor + 1)
        address loaded accumulator) := by
  unfold programStep
  rw [show (cellState heap cursor address loaded accumulator).pc.val = cursor from
    encoded_value width cursor cursorFits, fetched]
  change step (.allocate (2 : Fin 4)) (cellState heap cursor address loaded accumulator) = _
  simp only [step, cellState_running, Bool.false_eq_true, ite_false]
  have held : (cellState heap cursor address loaded accumulator).reg 2 =
      boolWord width accumulator := by simp [cellState]
  change (if heap.size < 2 ^ width then
    some { (cellState heap cursor address loaded accumulator).advance with
      heap := heap.push ((cellState heap cursor address loaded accumulator).reg 2) } else none) = _
  rw [ite_eq_left heapFits, held, cellState_advance heap cursor address loaded accumulator cursorFits]
  rfl

/-- Appending a gate result increases the dynamic peak by exactly one word. -/
theorem cell_allocate_execution (program : Program width 4)
    (heap : Array (Word width)) (cursor : Nat) (address loaded : Word width)
    (accumulator : Bool) (cursorFits : cursor < 2 ^ width)
    (heapFits : heap.size < 2 ^ width)
    (fetched : program[cursor]? = some (.allocate 2)) :
    Execution program (cellState heap cursor address loaded accumulator)
      (cellState (heap.push (boolWord width accumulator)) (cursor + 1)
        address loaded accumulator) 1 (6 + heap.size) := by
  have path := Execution.cons
    (cell_allocate_transition program heap cursor address loaded accumulator cursorFits heapFits fetched)
    (Execution.refl (cellState (heap.push (boolWord width accumulator)) (cursor + 1)
      address loaded accumulator))
  have peak : max (5 + heap.size) (5 + (heap.push (boolWord width accumulator)).size) =
      6 + heap.size := by simp only [Array.size_push]; omega
  simpa only [cellState_liveWords, peak] using path

/-- The ordered accumulator updates implement disjunction. -/
theorem fold_replace_true (entries : List (Nat × Bool)) (accumulator : Bool) :
    entries.foldl (fun acc entry => if entry.2 then true else acc) accumulator =
      (accumulator || entries.any Prod.snd) := by
  induction entries generalizing accumulator with
  | nil => simp
  | cons entry rest inductionHypothesis =>
    simp only [List.foldl_cons, inductionHypothesis, List.any_cons]
    cases entry.2 <;> cases accumulator <;> simp

/-- Complete OR-gate execution includes accumulator initialization, every
generated child-incidence cell, and the appended result word. -/
theorem or_gate_execution (program : Program width 4) (heap : Array (Word width))
    (base : Nat) (entries : List (Nat × Bool)) (oldAddress oldLoaded : Word width)
    (oldAccumulator : Bool) (programFits : base + 2 + 4 * entries.length < 2 ^ width)
    (heapFits : heap.size < 2 ^ width) (values : EntriesStored heap entries)
    (block : BlockAt program base
      ([.constant 2 (boolWord width false)] ++
        cells (orCell width) 4 (base + 1) (entries.map Prod.fst) ++ [.allocate 2])) :
    ∃ finalAddress finalLoaded ticks,
      Execution program (cellState heap base oldAddress oldLoaded oldAccumulator)
        (cellState (heap.push (boolWord width (entries.any Prod.snd)))
          (base + 2 + 4 * entries.length) finalAddress finalLoaded (entries.any Prod.snd))
        ticks (6 + heap.size) ∧ ticks ≤ 2 + 4 * entries.length := by
  have startBlock := BlockAt.prefix program base [.constant 2 (boolWord width false)]
    (cells (orCell width) 4 (base + 1) (entries.map Prod.fst) ++ [.allocate 2])
    (by simpa only [List.append_assoc] using block)
  have startFetched := startBlock 0 (by simp)
  simp only [List.getElem?_cons_zero, Nat.add_zero] at startFetched
  have afterStart := BlockAt.suffix program base [.constant 2 (boolWord width false)]
    (cells (orCell width) 4 (base + 1) (entries.map Prod.fst) ++ [.allocate 2])
    (by simpa only [List.append_assoc] using block)
  simp only [List.length_cons, List.length_nil] at afterStart
  have loopBlock := BlockAt.prefix program (base + 1)
    (cells (orCell width) 4 (base + 1) (entries.map Prod.fst)) [.allocate 2] afterStart
  have allocateBlock := BlockAt.suffix program (base + 1)
    (cells (orCell width) 4 (base + 1) (entries.map Prod.fst)) [.allocate 2] afterStart
  have stored : ConditionalCellsStored program heap true (base + 1) entries := by
    apply conditionalCellsStored_of_block program heap true entries (base + 1) (by omega) values
    exact loopBlock
  obtain ⟨finalAddress, finalLoaded, loopTicks, loopTrace, loopBound⟩ :=
    conditional_cells_execution program heap true false entries (base + 1)
      oldAddress oldLoaded stored
  rw [fold_replace_true] at loopTrace
  simp only [Bool.false_or] at loopTrace
  have initializeStep := cell_set_transition program heap base oldAddress oldLoaded
    oldAccumulator false (by omega) startFetched
  have allocateFetched := allocateBlock 0 (by simp)
  simp only [cells_length (orCell width) 4 (by intros; rfl), List.length_map,
    Nat.add_zero, List.getElem?_cons_zero] at allocateFetched
  have finish := cell_allocate_execution program heap (base + 1 + 4 * entries.length)
    finalAddress finalLoaded (entries.any Prod.snd) (by omega) heapFits allocateFetched
  have joined := Execution.cons initializeStep (loopTrace.append finish)
  have cursor : base + 1 + 4 * entries.length + 1 = base + 2 + 4 * entries.length := by omega
  have peak : max (5 + heap.size) (max (5 + heap.size) (6 + heap.size)) = 6 + heap.size := by omega
  refine ⟨finalAddress, finalLoaded, loopTicks + 1 + 1, ?_, by omega⟩
  simpa only [cursor, cellState_liveWords, peak] using joined

/-- The OR trace is for the original stored gate constructor, with its exact
child order and multiplicities, not an independently supplied Boolean formula. -/
theorem disj_gate_execution (program : Program width 4) (heap : Array (Word width))
    (base : Nat) (children : List (Fin available)) (childValue : Fin available → Bool)
    (oldAddress oldLoaded : Word width) (oldAccumulator : Bool)
    (programFits : base + 2 + 4 * children.length < 2 ^ width)
    (heapFits : heap.size < 2 ^ width)
    (values : EntriesStored heap (children.map fun child => (n + child.val, childValue child)))
    (block : BlockAt program base (gateCode width base (.disj children : Gate n available))) :
    ∃ finalAddress finalLoaded ticks,
      Execution program (cellState heap base oldAddress oldLoaded oldAccumulator)
        (cellState (heap.push (boolWord width (children.any childValue)))
          (base + 2 + 4 * children.length) finalAddress finalLoaded (children.any childValue))
        ticks (6 + heap.size) ∧ ticks ≤ 2 + 4 * children.length := by
  have generated : BlockAt program base
      ([.constant 2 (boolWord width false)] ++
        cells (orCell width) 4 (base + 1)
          ((children.map fun child => (n + child.val, childValue child)).map Prod.fst) ++
        [.allocate 2]) := by
    simpa only [gateCode, List.map_map, Function.comp_def] using block
  have path := or_gate_execution program heap base
    (children.map fun child => (n + child.val, childValue child)) oldAddress oldLoaded
    oldAccumulator (by simpa only [List.length_map] using programFits) heapFits values generated
  simpa only [List.length_map, List.any_map, Function.comp_def] using path

/-- A fetched child read initializes the accumulator without changing the
loaded-value scratch register. -/
theorem cell_read_accumulator_transition (program : Program width 4)
    (heap : Array (Word width)) (cursor address : Nat) (oldLoaded : Word width)
    (accumulator value : Bool) (cursorFits : cursor < 2 ^ width)
    (addressFits : address < 2 ^ width) (valid : address < heap.size)
    (stored : heap[address] = boolWord width value)
    (fetched : program[cursor]? = some (.load 2 0)) :
    programStep program (cellState heap cursor (word width address) oldLoaded accumulator) =
      some (cellState heap (cursor + 1) (word width address) oldLoaded value) := by
  unfold programStep
  rw [show (cellState heap cursor (word width address) oldLoaded accumulator).pc.val = cursor from
    encoded_value width cursor cursorFits, fetched]
  change step (.load (2 : Fin 4) (0 : Fin 4))
    (cellState heap cursor (word width address) oldLoaded accumulator) = _
  simp only [step, cellState_running, Bool.false_eq_true, ite_false]
  change (if h : (word width address).val < heap.size then
    some ((cellState heap cursor (word width address) oldLoaded accumulator).advance.put 2
      heap[(word width address).val]) else none) = _
  rw [dite_eq_left (by simpa [encoded_value width address addressFits] using valid)]
  simp only [encoded_value width address addressFits, stored]
  rw [cellState_advance heap cursor (word width address) oldLoaded accumulator cursorFits,
    cellState_put_accumulator]

/-- The ordered false replacement fold implements a negative guard union. -/
theorem fold_replace_false (entries : List (Nat × Bool)) (accumulator : Bool) :
    entries.foldl (fun acc entry => if entry.2 then false else acc) accumulator =
      (accumulator && !(entries.any Prod.snd)) := by
  induction entries generalizing accumulator with
  | nil => simp
  | cons entry rest inductionHypothesis =>
    simp only [List.foldl_cons, inductionHypothesis, List.any_cons]
    cases entry.2 <;> cases accumulator <;> simp

/-- Complete original negative-guard gate execution, retaining every guard
occurrence and appending exactly its semantic output value. -/
theorem guard_gate_execution (program : Program width 4) (heap : Array (Word width))
    (base : Nat) (child : Fin available) (labels : List (Channel n))
    (assignment : Assignment n) (childValue : Bool) (oldAddress oldLoaded : Word width)
    (oldAccumulator : Bool) (programFits : base + 3 + 4 * labels.length < 2 ^ width)
    (heapFits : heap.size < 2 ^ width) (childAddressFits : n + child.val < 2 ^ width)
    (childValid : n + child.val < heap.size)
    (childStored : heap[n + child.val] = boolWord width childValue)
    (values : EntriesStored heap (labels.map fun label => (label.val, assignment label)))
    (block : BlockAt program base (gateCode width base (.guard child labels : Gate n available))) :
    ∃ finalAddress finalLoaded ticks,
      Execution program (cellState heap base oldAddress oldLoaded oldAccumulator)
        (cellState (heap.push (boolWord width (childValue && !(labels.any assignment))))
          (base + 3 + 4 * labels.length) finalAddress finalLoaded (childValue && !(labels.any assignment)))
        ticks (6 + heap.size) ∧ ticks ≤ 3 + 4 * labels.length := by
  let prefixCode : Code width := [.constant 0 (word width (n + child.val)), .load 2 0]
  let body := cells (guardCell width) 4 (base + 2) (labels.map Fin.val)
  have assembled : BlockAt program base (prefixCode ++ (body ++ [.allocate 2])) := by
    simpa only [gateCode, prefixCode, body, List.append_assoc] using block
  have prefixBlock := BlockAt.prefix program base prefixCode (body ++ [.allocate 2]) assembled
  have first := prefixBlock 0 (by simp [prefixCode])
  have second := prefixBlock 1 (by simp [prefixCode])
  simp only [prefixCode, List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.add_zero] at first second
  have afterPrefix := BlockAt.suffix program base prefixCode (body ++ [.allocate 2]) assembled
  have loopBlock := BlockAt.prefix program (base + 2) body [.allocate 2]
    (by simpa only [prefixCode, List.length_cons, List.length_nil] using afterPrefix)
  have allocateBlock := BlockAt.suffix program (base + 2) body [.allocate 2]
    (by simpa only [prefixCode, List.length_cons, List.length_nil] using afterPrefix)
  have stored : ConditionalCellsStored program heap false (base + 2)
      (labels.map fun label => (label.val, assignment label)) := by
    apply conditionalCellsStored_of_block program heap false _ (base + 2)
      (by simpa only [List.length_map] using (show base + 2 + 4 * labels.length < 2 ^ width by omega)) values
    rw [show conditionalCell width false = guardCell width from rfl]
    simpa only [body, List.map_map, Function.comp_def] using loopBlock
  obtain ⟨finalAddress, finalLoaded, loopTicks, loopTrace, loopBound⟩ :=
    conditional_cells_execution program heap false childValue _ (base + 2)
      (word width (n + child.val)) oldLoaded stored
  rw [fold_replace_false] at loopTrace
  simp only [List.length_map, List.any_map, Function.comp_def] at loopTrace loopBound
  have firstStep := cell_address_transition program heap base (n + child.val)
    oldAddress oldLoaded oldAccumulator (by omega) first
  have secondStep := cell_read_accumulator_transition program heap (base + 1) (n + child.val)
    oldLoaded oldAccumulator childValue (by omega) childAddressFits childValid childStored second
  simp only [Nat.add_assoc] at secondStep
  have allocateFetched := allocateBlock 0 (by simp)
  simp only [body, cells_length (guardCell width) 4 (by intros; rfl), List.length_map,
    Nat.add_zero, List.getElem?_cons_zero] at allocateFetched
  have finish := cell_allocate_execution program heap (base + 2 + 4 * labels.length)
    finalAddress finalLoaded (childValue && !(labels.any assignment)) (by omega) heapFits allocateFetched
  have joined := Execution.cons firstStep (Execution.cons secondStep (loopTrace.append finish))
  have cursor : base + 2 + 4 * labels.length + 1 = base + 3 + 4 * labels.length := by omega
  have peak : max (5 + heap.size) (max (5 + heap.size) (max (5 + heap.size) (6 + heap.size))) =
      6 + heap.size := by omega
  refine ⟨finalAddress, finalLoaded, loopTicks + 1 + 1 + 1, ?_, by omega⟩
  simpa only [cursor, cellState_liveWords, peak] using joined

/-- Complete zero-gate execution initializes and appends a false word. -/
theorem zero_gate_execution (program : Program width 4) (heap : Array (Word width))
    (base : Nat) (oldAddress oldLoaded : Word width) (oldAccumulator : Bool)
    (programFits : base + 2 < 2 ^ width) (heapFits : heap.size < 2 ^ width)
    (block : BlockAt program base (gateCode width base (.zero : Gate n available))) :
    Execution program (cellState heap base oldAddress oldLoaded oldAccumulator)
      (cellState (heap.push (boolWord width false)) (base + 2) oldAddress oldLoaded false)
      2 (6 + heap.size) := by
  have first := block 0 (by simp [gateCode])
  have second := block 1 (by simp [gateCode])
  simp only [gateCode, List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.add_zero] at first second
  have setStep := cell_set_transition program heap base oldAddress oldLoaded
    oldAccumulator false (by omega) first
  have finish := cell_allocate_execution program heap (base + 1) oldAddress oldLoaded false
    (by omega) heapFits second
  have path := Execution.cons setStep finish
  have peak : max (5 + heap.size) (6 + heap.size) = 6 + heap.size := by omega
  simpa only [cellState_liveWords, peak, Nat.add_assoc] using path

/-- Complete input-gate execution reads its represented input and appends it. -/
theorem input_gate_execution (program : Program width 4) (heap : Array (Word width))
    (base : Nat) (channel : Channel n) (value : Bool) (oldAddress oldLoaded : Word width)
    (oldAccumulator : Bool) (programFits : base + 3 < 2 ^ width)
    (heapFits : heap.size < 2 ^ width) (addressFits : channel.val < 2 ^ width)
    (valid : channel.val < heap.size) (stored : heap[channel.val] = boolWord width value)
    (block : BlockAt program base (gateCode width base (.input channel : Gate n available))) :
    Execution program (cellState heap base oldAddress oldLoaded oldAccumulator)
      (cellState (heap.push (boolWord width value)) (base + 3) (word width channel.val) oldLoaded value)
      3 (6 + heap.size) := by
  have first := block 0 (by simp [gateCode])
  have second := block 1 (by simp [gateCode])
  have third := block 2 (by simp [gateCode])
  simp only [gateCode, List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.add_zero] at first second third
  have firstStep := cell_address_transition program heap base channel.val oldAddress oldLoaded
    oldAccumulator (by omega) first
  have secondStep := cell_read_accumulator_transition program heap (base + 1) channel.val
    oldLoaded oldAccumulator value (by omega) addressFits valid stored second
  simp only [Nat.add_assoc] at secondStep
  have finish := cell_allocate_execution program heap (base + 2) (word width channel.val)
    oldLoaded value (by omega) heapFits third
  have path := Execution.cons firstStep (Execution.cons secondStep finish)
  have peak : max (5 + heap.size) (max (5 + heap.size) (6 + heap.size)) = 6 + heap.size := by omega
  simpa only [cellState_liveWords, peak, Nat.add_assoc] using path

/-- Actual stored inputs required by one gate, retaining incidence lists. -/
structure GateValuesStored (heap : Array (Word width)) (gate : Gate n available)
    (assignment : Assignment n) (earlier : Fin available → Bool) : Prop where
  channel : ∀ label ∈ gate.directChannels,
    ∃ valid : label.val < heap.size, heap[label.val] = boolWord width (assignment label)
  child : ∀ ref ∈ gate.children,
    ∃ valid : n + ref.val < heap.size, heap[n + ref.val] = boolWord width (earlier ref)

/-- Every gate of the original guarded basis has a genuine generated-program
trace, appending its semantic value within its stored instruction count. -/
theorem guarded_gate_execution (program : Program width 4) (heap : Array (Word width))
    (base : Nat) (gate : Gate n available) (guarded : gate.IsGuarded)
    (assignment : Assignment n) (earlier : Fin available → Bool)
    (oldAddress oldLoaded : Word width) (oldAccumulator : Bool)
    (programFits : base + (gateCode width base gate).length < 2 ^ width)
    (heapFits : heap.size < 2 ^ width)
    (values : GateValuesStored heap gate assignment earlier)
    (block : BlockAt program base (gateCode width base gate)) :
    ∃ finalAddress finalLoaded ticks,
      Execution program (cellState heap base oldAddress oldLoaded oldAccumulator)
        (cellState (heap.push (boolWord width (gate.eval assignment earlier)))
          (base + (gateCode width base gate).length) finalAddress finalLoaded (gate.eval assignment earlier))
        ticks (6 + heap.size) ∧ ticks ≤ (gateCode width base gate).length := by
  rw [gateCode_length] at programFits
  cases gate with
  | zero =>
    refine ⟨oldAddress, oldLoaded, 2, ?_, by simp [gateCode_length]⟩
    simpa only [gateCode_length, Gate.eval] using zero_gate_execution program heap base
      oldAddress oldLoaded oldAccumulator programFits heapFits block
  | input label =>
    obtain ⟨valid, stored⟩ := values.channel label (by simp [Gate.directChannels])
    refine ⟨word width label.val, oldLoaded, 3, ?_, by simp [gateCode_length]⟩
    simpa only [gateCode_length, Gate.eval] using input_gate_execution program heap base label
      (assignment label) oldAddress oldLoaded oldAccumulator programFits heapFits
      (by omega) valid stored block
  | disj children =>
    have entries : EntriesStored heap (children.map fun ref => (n + ref.val, earlier ref)) := by
      intro entry member
      obtain ⟨ref, present, rfl⟩ := List.mem_map.mp member
      obtain ⟨valid, stored⟩ := values.child ref present
      exact ⟨by omega, valid, stored⟩
    simpa only [gateCode_length, Gate.eval, Nat.add_assoc] using disj_gate_execution program heap base
      children earlier oldAddress oldLoaded oldAccumulator
      (by simpa only [Nat.add_assoc] using programFits) heapFits entries block
  | guard ref labels =>
    obtain ⟨valid, stored⟩ := values.child ref (by simp [Gate.children])
    have entries : EntriesStored heap (labels.map fun label => (label.val, assignment label)) := by
      intro entry member
      obtain ⟨label, present, rfl⟩ := List.mem_map.mp member
      obtain ⟨labelValid, labelStored⟩ := values.channel label present
      exact ⟨by omega, labelValid, labelStored⟩
    simpa only [gateCode_length, Gate.eval, Nat.add_assoc] using guard_gate_execution program heap base ref
      labels assignment (earlier ref) oldAddress oldLoaded oldAccumulator
      (by simpa only [Nat.add_assoc] using programFits) heapFits
      (by omega) valid stored entries block
  | liveAnd left right =>
    simp [Gate.IsGuarded, Gate.isLiveAnd] at guarded

end Controller.Cost.GateProgram
