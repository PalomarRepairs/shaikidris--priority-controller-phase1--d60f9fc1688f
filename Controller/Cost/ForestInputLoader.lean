module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestMarkerMachine
public import Controller.Cost.ForestCursorMaterialize

@[expose] public section

/-!
# Fixed fetched input-word loader

One shared seven-instruction loop consumes the remaining word count in register
zero and transfers represented stack words to fresh heap cells. The count is
an explicit entry-state word; a separate header-reading initialization derives
it from the stored input metadata. The loop code is independent of that count.
Caller stack and output suffixes are retained and charged at every transition.
-/
namespace Controller.Cost.ForestInputLoader
open Controller.Cost.GateProgram Controller.Cost.ForestCounter
open Controller.Cost.ForestMarkerMachine

/-- The all-ones word implements modular decrement; positive entry counts
make its result the ordinary remaining count. -/
def code (width base : ℕ) : ForestCounter.Code width :=
  [.branchZero 0 (word width (base + 7)), .pop 2, .allocate 2,
    .constant 1 (word width (2 ^ width - 1)), .add 0 0 1,
    .constant 2 (word width 0), .branchZero 2 (word width base)]

@[simp] theorem code_length (width base : ℕ) : (code width base).length = 7 := rfl

private theorem put_payload (heap : Array (Word width)) (cursor : ℕ)
    (count loaded temporary next : Word width) :
    (counterState heap cursor count loaded temporary).put 2 next =
      counterState heap cursor count loaded next := by
  unfold State.put counterState
  congr 1
  funext register
  by_cases first : register = 0
  · subst register; simp
  · by_cases second : register = 1
    · subst register; simp
    · by_cases third : register = 2 <;> simp [first, second, third]

private theorem advance_state (heap : Array (Word width)) (cursor : ℕ)
    (count loaded temporary : Word width) (fits : cursor < 2 ^ width) :
    (counterState heap cursor count loaded temporary).advance =
      counterState heap (cursor + 1) count loaded temporary := by
  unfold State.advance counterState
  rw [show (word width cursor).val = cursor from Nat.mod_eq_of_lt fits]

theorem pop_payload_transition (program : Program width 4) (heap : Array (Word width))
    (cursor : ℕ) (count loaded temporary value : Word width) (fits : cursor < 2 ^ width)
    (fetched : program[cursor]? = some (.pop 2)) :
    programStep program ((counterState heap cursor count loaded temporary).frame [value] []) =
      some (counterState heap (cursor + 1) count loaded value) := by
  unfold programStep
  rw [show ((counterState heap cursor count loaded temporary).frame [value] []).pc.val = cursor from
    Nat.mod_eq_of_lt fits, fetched]
  change step (.pop (2 : Fin 4))
    ((counterState heap cursor count loaded temporary).frame [value] []) = _
  simp only [step, State.frame, counterState, Bool.false_eq_true, ite_false, List.nil_append]
  change some ((counterState heap cursor count loaded temporary).advance.put 2 value) = _
  rw [advance_state heap cursor count loaded temporary fits, put_payload]
  rfl

/-- Zero remaining words take the actual exit branch without a stack pop. -/
theorem zero_execution (program : Program width 4) (heap : Array (Word width))
    (base : ℕ) (loaded temporary : Word width) (fits : base + 7 < 2 ^ width)
    (block : BlockAt program base (code width base)) :
    Execution program (counterState heap base (word width 0) loaded temporary)
      (counterState heap (base + 7) (word width 0) loaded temporary) 1 (5 + heap.size) := by
  have transition := branch_transition program heap base (base + 7) 0
    (word width 0) loaded temporary (by omega)
    (by simpa [code] using block 0 (by simp [code]))
  have zero : ((counterState heap base (word width 0) loaded temporary).reg (0 : Fin 4)).val = 0 := by
    simp [counterState, word]
  rw [zero, ite_eq_left rfl] at transition
  have trace := Execution.cons transition
    (Execution.refl (counterState heap (base + 7) (word width 0) loaded temporary))
  convert trace using 1 <;> simp only [counterState_liveWords] <;> omega

theorem decrement_word (remaining : ℕ) (fits : remaining + 1 < 2 ^ width) :
    word width ((word width (remaining + 1)).val + (word width (2 ^ width - 1)).val) =
      word width remaining := by
  have positive : 0 < 2 ^ width := Nat.two_pow_pos width
  rw [show (word width (remaining + 1)).val = remaining + 1 from Nat.mod_eq_of_lt fits,
    show (word width (2 ^ width - 1)).val = 2 ^ width - 1 from Nat.mod_eq_of_lt (by omega)]
  have sum : remaining + 1 + (2 ^ width - 1) = 2 ^ width + remaining := by omega
  rw [sum]
  simp only [word, Nat.add_mod_left]

/-- Every positive entry transfers exactly one represented word and returns
to the same code with the ordinary decremented remaining count. -/
theorem entry_execution (program : Program width 4) (heap : Array (Word width))
    (base remaining : ℕ) (loaded temporary value : Word width)
    (fits : base + 7 < 2 ^ width) (countFits : remaining + 1 < 2 ^ width)
    (room : heap.size < 2 ^ width) (block : BlockAt program base (code width base)) :
    Execution program
      ((counterState heap base (word width (remaining + 1)) loaded temporary).frame [value] [])
      (counterState (heap.push value) base (word width remaining)
        (word width (2 ^ width - 1)) (word width 0)) 7 (6 + heap.size) := by
  have first := branch_transition program heap base (base + 7) 0
    (word width (remaining + 1)) loaded temporary (by omega)
    (by simpa [code] using block 0 (by simp [code]))
  have positive : ((counterState heap base (word width (remaining + 1)) loaded temporary).reg
      (0 : Fin 4)).val = remaining + 1 := by
    simp only [counterState]
    exact Nat.mod_eq_of_lt countFits
  rw [positive, ite_eq_right (by omega : remaining + 1 ≠ 0)] at first
  have framedFirst := programStep_frame program _ _ [value] [] first
  have second := pop_payload_transition program heap (base + 1)
    (word width (remaining + 1)) loaded temporary value (by omega)
    (by simpa [code] using block 1 (by simp [code]))
  have third := ForestCursorMaterialize.allocate_transition program heap (base + 2)
    (word width (remaining + 1)) loaded value (by omega) room
    (by simpa [code] using block 2 (by simp [code]))
  have fourth := constant_loaded_transition program (heap.push value) (base + 3)
    (word width (remaining + 1)) loaded value (word width (2 ^ width - 1)) (by omega)
    (by simpa [code] using block 3 (by simp [code]))
  have fifth := add_address_transition program (heap.push value) (base + 4)
    (word width (remaining + 1)) (word width (2 ^ width - 1)) value (by omega)
    (by simpa [code] using block 4 (by simp [code]))
  rw [decrement_word remaining countFits] at fifth
  have sixth := increment_transition program (heap.push value) (base + 5) 0
    (word width remaining) (word width (2 ^ width - 1)) value (by omega)
    (by simpa [code] using block 5 (by simp [code]))
  have seventh := branch_transition program (heap.push value) (base + 6) base 2
    (word width remaining) (word width (2 ^ width - 1)) (word width 0) (by omega)
    (by simpa [code] using block 6 (by simp [code]))
  have zero : ((counterState (heap.push value) (base + 6) (word width remaining)
      (word width (2 ^ width - 1)) (word width 0)).reg (2 : Fin 4)).val = 0 := by
    simp [counterState, word]
  rw [zero, ite_eq_left rfl] at seventh
  simp only [Nat.add_assoc] at second third fourth fifth sixth seventh
  have trace := Execution.cons framedFirst (Execution.cons second (Execution.cons third
    (Execution.cons fourth (Execution.cons fifth (Execution.cons sixth (Execution.cons seventh
      (Execution.refl (counterState (heap.push value) base (word width remaining)
        (word width (2 ^ width - 1)) (word width 0)))))))))
  convert trace using 1 <;> simp only [counterState_liveWords, State.frame_liveWords,
    List.length_cons, List.length_nil, Nat.add_zero, Array.size_push] <;> omega

/-- One fixed fetched loop loads the complete represented input in order.
No input-length-dependent program construction is used. Initial count formation
is separate; every stack word and retained caller suffix is included in peak. -/
theorem load_words_execution (program : Program width 4) (heap : Array (Word width))
    (values : List (Word width)) (base : ℕ) (loaded temporary : Word width)
    (fits : base + 7 < 2 ^ width) (countFits : values.length < 2 ^ width)
    (room : heap.size + values.length ≤ 2 ^ width) (block : BlockAt program base (code width base)) :
    ∃ final, Execution program
      ((counterState heap base (word width values.length) loaded temporary).frame values [])
      final (7 * values.length + 1) (5 + heap.size + values.length) ∧
      final.heap = heap ++ values.toArray ∧ final.stack = [] ∧ final.output = [] ∧
      final.pc = word width (base + 7) ∧ final.halted = false := by
  induction values generalizing heap loaded temporary with
  | nil =>
      refine ⟨counterState heap (base + 7) (word width 0) loaded temporary, ?_, ?_, rfl, rfl, rfl, rfl⟩
      · simpa only [State.frame, counterState, List.nil_append, List.length_nil, Nat.mul_zero,
          Nat.zero_add, Nat.add_zero] using zero_execution program heap base loaded temporary fits block
      · simp [counterState]
  | cons value rest ih =>
      have remainingFits : rest.length + 1 < 2 ^ width := by simpa using countFits
      have first := (entry_execution program heap base rest.length loaded temporary value fits remainingFits
        (by simp only [List.length_cons] at room; omega) block).frame rest []
      obtain ⟨final, later, finalHeap, finalStack, finalOutput, finalPC, running⟩ :=
        ih (heap.push value) (word width (2 ^ width - 1)) (word width 0)
          (by omega) (by simp only [Array.size_push]; simp only [List.length_cons] at room; omega)
      have joined := first.append later
      refine ⟨final, ?_, ?_, finalStack, finalOutput, finalPC, running⟩
      · convert joined using 1 <;>
          simp only [State.frame, counterState, List.nil_append, List.append_nil,
            List.cons_append, List.length_nil, List.length_cons, Array.size_push] <;> omega
      · rw [finalHeap]
        apply Array.toList_inj.mp
        simp [List.append_assoc]

end Controller.Cost.ForestInputLoader
