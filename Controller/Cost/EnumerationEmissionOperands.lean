module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.EnumerationMaskedEmit

@[expose] public section

/-! One fixed sequence of constant, stored and target-masked output coordinates.
Each coordinate is fetched and emitted; the instruction sequence is independent
of the result bits. -/
namespace Controller.Cost.EnumerationEmissionOperands
open Controller.Cost.GateProgram Controller.Cost.RawTransferLoops

inductive Operand where
  | literal (value : Bool)
  | cell (address : Nat)
  | masked (address : Nat)
  deriving DecidableEq

def operandCode (width entry : Nat) : Operand → List (Instruction width 8)
  | .literal value => EnumerationLiteralEmit.code width value
  | .cell address => EnumerationStreamEmit.emitCell width address
  | .masked address => EnumerationMaskedEmit.code width entry address

def cost : Operand → Nat
  | .literal _ => 2
  | .cell _ => 3
  | .masked _ => 4

def value (heap : Array (Word width)) (targetPresent : Bool) : Operand → Word width
  | .literal bit => boolWord width bit
  | .cell address => EnumerationStreamEmit.heapValue heap address
  | .masked address => if targetPresent then boolWord width false else EnumerationStreamEmit.heapValue heap address

def Valid (heap : Array (Word width)) : Operand → Prop
  | .literal _ => True
  | .cell address => address < heap.size
  | .masked address => address < heap.size

@[simp] theorem operandCode_length (operand : Operand) :
    (operandCode width entry operand).length = match operand with
      | .literal _ => 2 | .cell _ => 3 | .masked _ => 6 := by
  cases operand <;> rfl

private theorem operand_execution (program : Program width 8) (state : State width 8)
    (entry : Nat) (operand : Operand) (targetPresent : Bool)
    (position : state.pc = word width entry) (running : state.halted = false)
    (flag : state.reg 2 = boolWord width targetPresent) (zero : state.reg 7 = word width 0)
    (widthPositive : 0 < width) (room : entry + (operandCode width entry operand).length < 2 ^ width)
    (heapFits : state.heap.size < 2 ^ width) (valid : Valid state.heap operand)
    (present : SharedRootRead.BlockAt program entry (operandCode width entry operand)) :
    ∃ final, Execution program state final (cost operand) (state.liveWords + 1) ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧
      final.output = value state.heap targetPresent operand :: state.output ∧
      final.pc = word width (entry + (operandCode width entry operand).length) ∧ final.halted = false ∧
      (∀ register : Fin 8, register ≠ 0 → register ≠ 1 → final.reg register = state.reg register) := by
  cases operand with
  | literal bit =>
    obtain ⟨final, trace, heap, stack, output, pc, live, frame⟩ :=
      EnumerationLiteralEmit.execution program state entry bit position running room present
    exact ⟨final, trace, heap, stack, output, pc, live, fun register _ other => frame register other⟩
  | cell address =>
    exact EnumerationStreamEmit.emitCell_execution program state entry address position running room heapFits valid present
  | masked address =>
    apply EnumerationMaskedEmit.execution program state entry address targetPresent
      (EnumerationStreamEmit.heapValue state.heap address) position running flag zero widthPositive room heapFits valid _ present
    rw [Array.getElem?_eq_getElem valid, EnumerationStreamEmit.heapValue_eq state.heap address valid]

def code (width entry : Nat) : List Operand → List (Instruction width 8)
  | [] => []
  | operand :: rest => operandCode width entry operand ++
      code width (entry + (operandCode width entry operand).length) rest

def ticks (operands : List Operand) : Nat := (operands.map cost).sum

@[simp] theorem code_length (width entry : Nat) (operands : List Operand) :
    (code width entry operands).length = (operands.map fun operand => (operandCode width 0 operand).length).sum := by
  induction operands generalizing entry with
  | nil => simp [code]
  | cons operand rest ih =>
    simp only [code, List.length_append, ih, List.map_cons, List.sum_cons]
    cases operand <;> rfl

theorem code_length_bound (width entry : Nat) (operands : List Operand) :
    (code width entry operands).length ≤ 6 * operands.length := by
  induction operands generalizing entry with
  | nil => simp [code]
  | cons operand rest ih =>
    have tail := ih (entry + (operandCode width entry operand).length)
    simp only [code, List.length_append, List.length_cons]
    cases operand <;> simp only [operandCode_length] at * <;> omega

theorem ticks_bound (operands : List Operand) : ticks operands ≤ 4 * operands.length := by
  induction operands with
  | nil => simp [ticks]
  | cons operand rest ih =>
    simp only [ticks, List.map_cons, List.sum_cons, List.length_cons] at *
    cases operand <;> simp only [cost] <;> omega

private theorem block_prefix (program : Program width 8) (entry : Nat)
    (first rest : List (Instruction width 8)) (stored : SharedRootRead.BlockAt program entry (first ++ rest)) :
    SharedRootRead.BlockAt program entry first := by
  intro offset bound
  have whole := stored offset (by simp only [List.length_append]; omega)
  rw [List.getElem?_append_left bound] at whole
  exact whole

private theorem block_suffix (program : Program width 8) (entry : Nat)
    (first rest : List (Instruction width 8)) (stored : SharedRootRead.BlockAt program entry (first ++ rest)) :
    SharedRootRead.BlockAt program (entry + first.length) rest := by
  intro offset bound
  have whole := stored (first.length + offset) (by simp only [List.length_append]; omega)
  rw [List.getElem?_append_right (by omega)] at whole
  simpa only [Nat.add_sub_cancel_left, Nat.add_assoc] using whole

theorem execution (program : Program width 8) (state : State width 8)
    (entry : Nat) (operands : List Operand) (targetPresent : Bool)
    (position : state.pc = word width entry) (running : state.halted = false)
    (flag : state.reg 2 = boolWord width targetPresent) (zero : state.reg 7 = word width 0)
    (widthPositive : 0 < width) (room : entry + (code width entry operands).length < 2 ^ width)
    (heapFits : state.heap.size < 2 ^ width) (valid : ∀ operand ∈ operands, Valid state.heap operand)
    (present : SharedRootRead.BlockAt program entry (code width entry operands)) :
    ∃ final, Execution program state final (ticks operands) (state.liveWords + operands.length) ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧
      final.output = (operands.map (value state.heap targetPresent)).reverse ++ state.output ∧
      final.pc = word width (entry + (code width entry operands).length) ∧ final.halted = false ∧
      (∀ register : Fin 8, register ≠ 0 → register ≠ 1 → final.reg register = state.reg register) := by
  induction operands generalizing state entry with
  | nil =>
    refine ⟨state, ?_, rfl, rfl, ?_, ?_, running, fun _ _ _ => rfl⟩
    · simpa [ticks] using Execution.refl (p := program) state
    · simp
    · simpa [code] using position
  | cons operand rest ih =>
    have firstBlock := block_prefix program entry (operandCode width entry operand)
      (code width (entry + (operandCode width entry operand).length) rest) present
    obtain ⟨middle, first, middleHeap, middleStack, middleOutput, middlePC, middleRunning, middleFrame⟩ :=
      operand_execution program state entry operand targetPresent position running flag zero widthPositive
        (by simp only [code, List.length_append] at room; omega) heapFits (valid operand (by simp)) firstBlock
    have restBlock := block_suffix program entry (operandCode width entry operand)
      (code width (entry + (operandCode width entry operand).length) rest) present
    obtain ⟨final, tail, finalHeap, finalStack, finalOutput, finalPC, finalRunning, finalFrame⟩ :=
      ih middle (entry + (operandCode width entry operand).length) middlePC middleRunning
        ((middleFrame 2 (by decide) (by decide)).trans flag)
        ((middleFrame 7 (by decide) (by decide)).trans zero) (by
          simpa only [code, List.length_append, Nat.add_assoc] using room)
        (by simpa only [middleHeap] using heapFits)
        (by intro current member; rw [middleHeap]; exact valid current (by simp [member])) restBlock
    have middleLive : middle.liveWords = state.liveWords + 1 := by
      simp only [State.liveWords, middleHeap, middleStack, middleOutput, List.length_cons]; omega
    refine ⟨final, ?_, finalHeap.trans middleHeap, finalStack.trans middleStack, ?_, ?_, finalRunning, ?_⟩
    · have joined := first.append tail
      have peak : max (state.liveWords + 1) (middle.liveWords + rest.length) = state.liveWords + (operand :: rest).length := by
        rw [middleLive]; simp only [List.length_cons]; omega
      simpa only [ticks, List.map_cons, List.sum_cons, peak] using joined
    · rw [finalOutput, middleHeap, middleOutput]
      simp [List.reverse_cons, List.append_assoc]
    · simpa only [code, List.length_append, Nat.add_assoc] using finalPC
    · intro register notZero notOne; rw [finalFrame register notZero notOne, middleFrame register notZero notOne]

end Controller.Cost.EnumerationEmissionOperands
