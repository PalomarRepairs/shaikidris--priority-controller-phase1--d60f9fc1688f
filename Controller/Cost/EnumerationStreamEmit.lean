module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.EnumerationSteps

@[expose] public section

/-! Fetched streaming reads on the eight-register enumeration machine. Output
history is explicit in execution accounting and excluded only by the separately
named working-word measure. -/
namespace Controller.Cost.EnumerationStreamEmit
open Controller.Cost.GateProgram

abbrev Code (width : Nat) := List (Instruction width 8)

private theorem block_prefix (program : Program width 8) (base : Nat)
    (first rest : Code width) (stored : SharedRootRead.BlockAt program base (first ++ rest)) :
    SharedRootRead.BlockAt program base first := by
  intro offset bound
  have whole := stored offset (by simp only [List.length_append]; omega)
  rw [List.getElem?_append_left bound] at whole
  exact whole

private theorem block_suffix (program : Program width 8) (base : Nat)
    (first rest : Code width) (stored : SharedRootRead.BlockAt program base (first ++ rest)) :
    SharedRootRead.BlockAt program (base + first.length) rest := by
  intro offset bound
  have whole := stored (first.length + offset) (by simp only [List.length_append]; omega)
  rw [List.getElem?_append_right (by omega)] at whole
  simpa only [Nat.add_sub_cancel_left, Nat.add_assoc] using whole

def emitCell (width address : Nat) : Code width :=
  [.constant 0 (word width address), .load 1 0, .emit 1]

def emitCode (width : Nat) (addresses : List Nat) : Code width :=
  addresses.flatMap (emitCell width)

@[simp] theorem emitCode_length (width : Nat) (addresses : List Nat) :
    (emitCode width addresses).length = 3 * addresses.length := by
  induction addresses with
  | nil => simp [emitCode]
  | cons address rest ih => simp [emitCode, emitCell, Nat.mul_succ]; omega

def heapValue (heap : Array (Word width)) (address : Nat) : Word width :=
  (heap[address]?).getD (word width 0)

theorem heapValue_eq (heap : Array (Word width)) (address : Nat)
    (valid : address < heap.size) : heapValue heap address = heap[address] := by
  simp [heapValue, Array.getElem?_eq_getElem valid]

private theorem fetch (program : Program width 8) (s : State width 8)
    (cursor : Nat) (instruction : Instruction width 8)
    (pc : s.pc = word width cursor) (fits : cursor < 2 ^ width)
    (fetched : program[cursor]? = some instruction) :
    programStep program s = step instruction s := by
  unfold programStep
  rw [pc, show (word width cursor).val = cursor from Nat.mod_eq_of_lt fits, fetched]
  rfl

private theorem advance_pc (s : State width 8) (cursor : Nat)
    (pc : s.pc = word width cursor) (fits : cursor < 2 ^ width) :
    s.advance.pc = word width (cursor + 1) := by
  simp only [State.advance, pc]
  rw [show (word width cursor).val = cursor from Nat.mod_eq_of_lt fits]

/-- Three fetched instructions read one real heap word and prepend it to output. -/
theorem emitCell_execution (program : Program width 8) (s : State width 8)
    (base address : Nat) (pc : s.pc = word width base) (running : s.halted = false)
    (fits : base + 3 < 2 ^ width) (heapFits : s.heap.size < 2 ^ width)
    (valid : address < s.heap.size) (block : SharedRootRead.BlockAt program base (emitCell width address)) :
    ∃ final, Execution program s final 3 (s.liveWords + 1) ∧
      final.heap = s.heap ∧ final.stack = s.stack ∧
      final.output = heapValue s.heap address :: s.output ∧
      final.pc = word width (base + 3) ∧ final.halted = false ∧
      (∀ register : Fin 8, register ≠ 0 → register ≠ 1 → final.reg register = s.reg register) := by
  let first := s.advance.put 0 (word width address)
  let second := first.advance.put 1 (heapValue s.heap address)
  let final := { second.advance with output := heapValue s.heap address :: s.output }
  have firstPC : first.pc = word width (base + 1) := by
    exact advance_pc s base pc (by omega)
  have secondPC : second.pc = word width (base + 2) := by
    change first.advance.pc = word width (base + 2)
    simpa only [Nat.add_assoc, Nat.reduceAdd] using advance_pc first (base + 1) firstPC (by omega)
  have addressHeld : first.reg 0 = word width address := by simp [first, State.put]
  have addressFits : address < 2 ^ width := by omega
  have firstStep : programStep program s = some first := by
    rw [fetch program s base (.constant 0 (word width address)) pc (by omega)
      (by simpa [emitCell] using block 0 (by simp [emitCell]))]
    simp [step, running, first]
  have secondStep : programStep program first = some second := by
    rw [fetch program first (base + 1) (.load 1 0) firstPC (by omega)
      (by simpa [emitCell] using block 1 (by simp [emitCell]))]
    have firstRunning : first.halted = false := running
    have firstHeap : first.heap = s.heap := rfl
    simp only [step, firstRunning, Bool.false_eq_true, ite_false, addressHeld,
      show (word width address).val = address from Nat.mod_eq_of_lt addressFits, firstHeap]
    rw [dite_eq_left valid, ← heapValue_eq s.heap address valid]
  have finalStep : programStep program second = some final := by
    rw [fetch program second (base + 2) (.emit 1) secondPC (by omega)
      (by simpa [emitCell] using block 2 (by simp [emitCell]))]
    have secondRunning : second.halted = false := running
    simp [step, running, final, second, first, State.put, State.advance]
  have firstLive : first.liveWords = s.liveWords := rfl
  have secondLive : second.liveWords = s.liveWords := rfl
  have finalLive : final.liveWords = s.liveWords + 1 := by
    simp [final, second, first, State.put, State.advance, State.liveWords]; omega
  refine ⟨final, ?_, rfl, rfl, rfl, ?_, running, ?_⟩
  · have trace := Execution.cons firstStep (Execution.cons secondStep
      (Execution.cons finalStep (Execution.refl final)))
    simpa only [firstLive, secondLive, finalLive, Nat.zero_add, Nat.add_zero,
      show max s.liveWords (s.liveWords + 1) = s.liveWords + 1 by omega] using trace
  · simpa only [Nat.add_assoc] using advance_pc second (base + 2) secondPC (by omega)

  · intro register notZero notOne
    simp [final, second, first, State.put, State.advance, notZero, notOne]

/-- Stored order is emitted in order; the machine output list is reversed. -/
theorem emitCode_execution (program : Program width 8) (s : State width 8)
    (base : Nat) (addresses : List Nat) (pc : s.pc = word width base)
    (running : s.halted = false) (fits : base + 3 * addresses.length < 2 ^ width)
    (heapFits : s.heap.size < 2 ^ width)
    (valid : ∀ address ∈ addresses, address < s.heap.size)
    (block : SharedRootRead.BlockAt program base (emitCode width addresses)) :
    ∃ final, Execution program s final (3 * addresses.length) (s.liveWords + addresses.length) ∧
      final.heap = s.heap ∧ final.stack = s.stack ∧
      final.output = (addresses.map (heapValue s.heap)).reverse ++ s.output ∧
      final.pc = word width (base + 3 * addresses.length) ∧ final.halted = false ∧
      (∀ register : Fin 8, register ≠ 0 → register ≠ 1 → final.reg register = s.reg register) := by
  induction addresses generalizing s base with
  | nil =>
    refine ⟨s, ?_, rfl, rfl, ?_, ?_, running, fun _ _ _ => rfl⟩
    · simpa using Execution.refl (p := program) s
    · simp
    · simpa using pc
  | cons address rest ih =>
    have code : emitCode width (address :: rest) = emitCell width address ++ emitCode width rest := by
      simp [emitCode]
    have headBlock := block_prefix program base (emitCell width address) (emitCode width rest)
      (by simpa only [code] using block)
    obtain ⟨middle, headTrace, middleHeap, middleStack, middleOutput, middlePC, middleRunning, middleFrame⟩ :=
      emitCell_execution program s base address pc running (by simp only [List.length_cons] at fits; omega)
        heapFits (valid address (by simp)) headBlock
    have restBlock : SharedRootRead.BlockAt program (base + 3) (emitCode width rest) := by
      simpa [emitCell] using block_suffix program base (emitCell width address)
        (emitCode width rest) (by simpa only [code] using block)
    obtain ⟨final, restTrace, finalHeap, finalStack, finalOutput, finalPC, finalRunning, finalFrame⟩ :=
      ih middle (base + 3) middlePC middleRunning
        (by simp only [List.length_cons] at fits; omega) (by simpa only [middleHeap] using heapFits)
        (by intro a member; rw [middleHeap]; exact valid a (by simp [member])) restBlock
    have middleLive : middle.liveWords = s.liveWords + 1 := by
      simp only [State.liveWords, middleHeap, middleStack, middleOutput, List.length_cons]; omega
    refine ⟨final, ?_, finalHeap.trans middleHeap, finalStack.trans middleStack, ?_, ?_, finalRunning, ?_⟩
    · have joined := headTrace.append restTrace
      have peak : max (s.liveWords + 1) (middle.liveWords + rest.length) =
          s.liveWords + (address :: rest).length := by rw [middleLive]; simp only [List.length_cons]; omega
      rw [peak] at joined
      simpa only [List.length_cons, Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using joined
    · rw [finalOutput, middleHeap, middleOutput]
      simp [List.reverse_cons, List.append_assoc]
    · simpa only [List.length_cons, Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using finalPC


    · intro register notZero notOne
      rw [finalFrame register notZero notOne, middleFrame register notZero notOne]

/-- Live working words exclude the external output stream. -/
def workingWords (state : State width 8) : Nat :=
  9 + state.heap.size + state.stack.length

@[simp] theorem live_eq_working_output (state : State width 8) :
    state.liveWords = workingWords state + state.output.length := by
  simp only [State.liveWords, workingWords]; omega

/-- Streaming a block changes no working storage, independently of history length. -/
theorem emission_working_words (before after : State width 8)
    (heap : after.heap = before.heap) (stack : after.stack = before.stack) :
    workingWords after = workingWords before := by
  simp only [workingWords, heap, stack]

end Controller.Cost.EnumerationStreamEmit
