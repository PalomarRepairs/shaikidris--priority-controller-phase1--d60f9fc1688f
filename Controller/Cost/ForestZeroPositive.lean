module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestZeroNonempty

public import Mathlib.Tactic.FinCases

@[expose] public section

/-! If every channel has already been assigned a localIndex dictionary ID, a fixed
countdown loop reads those actual IDs and appends one positive clause. The loop
visits channels in descending order, retains repeated localIndex IDs, and never
copies a candidate assignment. Its use is conditional on the all-covered
outcome; an unused coordinate instead extends an existing zero model. -/
namespace Controller.Cost.ForestZeroPositive
open Controller.Cost.GateProgram Controller.Cost.ForestZeroTouch
open Controller.Cost.ForestZeroCompile Controller.Cost.ForestZeroDictionary

def code (width base : ℕ) : Code width :=
  [.branchZero 0 (word width (base + 12)),
   .constant 3 (word width (2 ^ width - 1)), .add 2 2 3,
   .load 1 2, .add 1 1 3, .allocate 1,
   .constant 3 (word width 1), .allocate 3,
   .constant 3 (word width (2 ^ width - 1)), .add 0 0 3,
   .constant 3 (word width 0), .branchZero 3 (word width base)]

@[simp] theorem code_length : (code width base).length = 12 := rfl

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

private theorem put3_at (heap : Array (Word width)) (cursor x0 x1 x2 x3 value : ℕ)
    (stack output : List (Word width)) :
    (atState heap cursor x0 x1 x2 x3 stack output).put 3 (word width value) =
      atState heap cursor x0 x1 x2 value stack output := by
  unfold atState State.put
  congr 1
  funext register
  fin_cases register <;> rfl

private theorem put1_at (heap : Array (Word width)) (cursor x0 x1 x2 x3 value : ℕ)
    (stack output : List (Word width)) :
    (atState heap cursor x0 x1 x2 x3 stack output).put 1 (word width value) =
      atState heap cursor x0 value x2 x3 stack output := by
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



private theorem atState_liveWords (heap : Array (Word width)) (cursor x0 x1 x2 x3 : ℕ)
    (stack output : List (Word width)) :
    (atState heap cursor x0 x1 x2 x3 stack output).liveWords =
      5 + heap.size + stack.length + output.length := by
  simp only [atState, State.liveWords]; omega

/-- One channel contributes two allocated words: its decoded localIndex ID and the
positive polarity. The slot is fetched from the existing physical table. -/
theorem iteration_execution (program : Program width 4) (heap : Array (Word width))
    (base remaining pointer localIndex scratch : ℕ) (stack output : List (Word width))
    (leftFits : remaining + 1 < 2 ^ width) (pointerFits : pointer + 1 < 2 ^ width)
    (localFits : localIndex + 1 < 2 ^ width) (pointerValid : pointer < heap.size)
    (cell : heap[pointer]? = some (word width (localIndex + 1)))
    (room : heap.size + 2 ≤ 2 ^ width) (programFits : base + 12 < 2 ^ width)
    (block : BlockAt program base (code width base)) :
    Execution program (atState heap base (remaining + 1) scratch (pointer + 1) 0 stack output)
      (atState ((heap.push (word width localIndex)).push (word width 1)) base
        remaining localIndex pointer 0 stack output)
      12 (7 + heap.size + stack.length + output.length) := by
  let mask := 2 ^ width - 1
  have maskFits : mask < 2 ^ width := by have := Nat.two_pow_pos width; dsimp [mask]; omega
  have maskWord : (word width mask).val = mask := Nat.mod_eq_of_lt maskFits
  have decrement (value : ℕ) : word width ((value + 1) + mask) = word width value := by
    have same : (value + 1) + mask = value + 2 ^ width := by
      have := Nat.two_pow_pos width; dsimp [mask]; omega
    apply Fin.ext; simp only [word, same, Nat.add_mod_right]
  have pointerWord : (word width pointer).val = pointer := Nat.mod_eq_of_lt (by omega)
  have actual : heap[pointer] = word width (localIndex + 1) := by
    rw [Array.getElem?_eq_getElem pointerValid] at cell
    exact Option.some.inj cell
  let s0 := atState (heap) (base) (remaining + 1) (scratch) (pointer + 1) (0) stack output
  let s1 := atState (heap) (base + 1) (remaining + 1) (scratch) (pointer + 1) (0) stack output
  let s2 := atState (heap) (base + 2) (remaining + 1) (scratch) (pointer + 1) (mask) stack output
  let s3 := atState (heap) (base + 3) (remaining + 1) (scratch) (pointer) (mask) stack output
  let s4 := atState (heap) (base + 4) (remaining + 1) (localIndex + 1) (pointer) (mask) stack output
  let s5 := atState (heap) (base + 5) (remaining + 1) (localIndex) (pointer) (mask) stack output
  let s6 := atState (heap.push (word width localIndex)) (base + 6) (remaining + 1) (localIndex) (pointer) (mask) stack output
  let s7 := atState (heap.push (word width localIndex)) (base + 7) (remaining + 1) (localIndex) (pointer) (1) stack output
  let s8 := atState ((heap.push (word width localIndex)).push (word width 1)) (base + 8) (remaining + 1) (localIndex) (pointer) (1) stack output
  let s9 := atState ((heap.push (word width localIndex)).push (word width 1)) (base + 9) (remaining + 1) (localIndex) (pointer) (mask) stack output
  let s10 := atState ((heap.push (word width localIndex)).push (word width 1)) (base + 10) (remaining) (localIndex) (pointer) (mask) stack output
  let s11 := atState ((heap.push (word width localIndex)).push (word width 1)) (base + 11) (remaining) (localIndex) (pointer) (0) stack output
  let s12 := atState ((heap.push (word width localIndex)).push (word width 1)) (base) (remaining) (localIndex) (pointer) (0) stack output
  have t0 : programStep program s0 = some s1 := by
    rw [fetched program s0 (base + 0) (.branchZero 0 (word width (base + 12))) rfl (by omega)
      (by simpa [code, mask] using block 0 (by simp [code]))]
    change some (if (word width (remaining + 1)).val = 0 then
      { s0.advance with pc := word width (base + 12) } else s0.advance) = some s1
    rw [show (word width (remaining + 1)).val = remaining + 1 from Nat.mod_eq_of_lt leftFits,
      ite_eq_right (by omega), advance_at _ _ _ _ _ _ _ _ (by omega)]
  have t1 : programStep program s1 = some s2 := by
    rw [fetched program s1 (base + 1) (.constant 3 (word width mask)) rfl (by omega)
      (by simpa [code, mask] using block 1 (by simp [code]))]
    change some (s1.advance.put 3 (word width mask)) = some s2
    rw [advance_at _ _ _ _ _ _ _ _ (by omega), put3_at]
  have t2 : programStep program s2 = some s3 := by
    rw [fetched program s2 (base + 2) (.add 2 2 3) rfl (by omega)
      (by simpa [code, mask] using block 2 (by simp [code]))]
    change some (s2.advance.put 2 (word width ((word width (pointer + 1)).val + (word width mask).val))) = some s3
    rw [show (word width (pointer + 1)).val = pointer + 1 from Nat.mod_eq_of_lt pointerFits,
      maskWord, decrement, advance_at _ _ _ _ _ _ _ _ (by omega), put2_at]
  have t3 : programStep program s3 = some s4 := by
    rw [fetched program s3 (base + 3) (.load 1 2) rfl (by omega)
      (by simpa [code, mask] using block 3 (by simp [code]))]
    change (if valid : (word width pointer).val < heap.size then
      some (s3.advance.put 1 heap[(word width pointer).val]) else none) = some s4
    rw [pointerWord, dite_eq_left pointerValid, actual, advance_at _ _ _ _ _ _ _ _ (by omega), put1_at]
  have t4 : programStep program s4 = some s5 := by
    rw [fetched program s4 (base + 4) (.add 1 1 3) rfl (by omega)
      (by simpa [code, mask] using block 4 (by simp [code]))]
    change some (s4.advance.put 1 (word width ((word width (localIndex + 1)).val + (word width mask).val))) = some s5
    rw [show (word width (localIndex + 1)).val = localIndex + 1 from Nat.mod_eq_of_lt localFits,
      maskWord, decrement, advance_at _ _ _ _ _ _ _ _ (by omega), put1_at]
  have t5 : programStep program s5 = some s6 := by
    rw [fetched program s5 (base + 5) (.allocate 1) rfl (by omega)
      (by simpa [code, mask] using block 5 (by simp [code]))]
    change (if (heap).size < 2 ^ width then
      some { s5.advance with heap := (heap).push (word width localIndex) } else none) = some s6
    rw [ite_eq_left (by omega), advance_at _ _ _ _ _ _ _ _ (by omega)]
    rfl
  have t6 : programStep program s6 = some s7 := by
    rw [fetched program s6 (base + 6) (.constant 3 (word width 1)) rfl (by omega)
      (by simpa [code, mask] using block 6 (by simp [code]))]
    change some (s6.advance.put 3 (word width 1)) = some s7
    rw [advance_at _ _ _ _ _ _ _ _ (by omega), put3_at]
  have t7 : programStep program s7 = some s8 := by
    rw [fetched program s7 (base + 7) (.allocate 3) rfl (by omega)
      (by simpa [code, mask] using block 7 (by simp [code]))]
    change (if (heap.push (word width localIndex)).size < 2 ^ width then
      some { s7.advance with heap := (heap.push (word width localIndex)).push (word width 1) } else none) = some s8
    rw [ite_eq_left (by simp only [Array.size_push]; omega), advance_at _ _ _ _ _ _ _ _ (by omega)]
    rfl
  have t8 : programStep program s8 = some s9 := by
    rw [fetched program s8 (base + 8) (.constant 3 (word width mask)) rfl (by omega)
      (by simpa [code, mask] using block 8 (by simp [code]))]
    change some (s8.advance.put 3 (word width mask)) = some s9
    rw [advance_at _ _ _ _ _ _ _ _ (by omega), put3_at]
  have t9 : programStep program s9 = some s10 := by
    rw [fetched program s9 (base + 9) (.add 0 0 3) rfl (by omega)
      (by simpa [code, mask] using block 9 (by simp [code]))]
    change some (s9.advance.put 0 (word width ((word width (remaining + 1)).val + (word width mask).val))) = some s10
    rw [show (word width (remaining + 1)).val = remaining + 1 from Nat.mod_eq_of_lt leftFits,
      maskWord, decrement, advance_at _ _ _ _ _ _ _ _ (by omega), put0_at]
  have t10 : programStep program s10 = some s11 := by
    rw [fetched program s10 (base + 10) (.constant 3 (word width 0)) rfl (by omega)
      (by simpa [code, mask] using block 10 (by simp [code]))]
    change some (s10.advance.put 3 (word width 0)) = some s11
    rw [advance_at _ _ _ _ _ _ _ _ (by omega), put3_at]
  have t11 : programStep program s11 = some s12 := by
    rw [fetched program s11 (base + 11) (.branchZero 3 (word width base)) rfl (by omega)
      (by simpa [code, mask] using block 11 (by simp [code]))]
    change some (if (word width 0).val = 0 then
      { s11.advance with pc := word width base } else s11.advance) = some s12
    simp only [word, Nat.zero_mod, ite_true, s11, s12, atState, State.advance]
  have chunk0 := Execution.cons t0 (Execution.cons t1 (Execution.cons t2 (Execution.refl s3)))
  have chunk1 := Execution.cons t3 (Execution.cons t4 (Execution.cons t5 (Execution.refl s6)))
  have chunk2 := Execution.cons t6 (Execution.cons t7 (Execution.cons t8 (Execution.refl s9)))
  have chunk3 := Execution.cons t9 (Execution.cons t10 (Execution.cons t11 (Execution.refl s12)))
  convert ((chunk0.append chunk1).append chunk2).append chunk3 using 1 <;>
    simp only [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, atState_liveWords, Array.size_push] <;> omega

/-- Descending labels are ghost specifications of table cells, not runtime
lists built or traversed by the code. -/
def StoredDescending (heap : Array (Word width)) (table : ℕ) : List ℕ → Prop
  | [] => True
  | localIndex :: rest => table + rest.length < heap.size ∧
      heap[table + rest.length]? = some (word width (localIndex + 1)) ∧
      localIndex + 1 < 2 ^ width ∧ StoredDescending heap table rest

def pairHeap (heap : Array (Word width)) : List ℕ → Array (Word width)
  | [] => heap
  | localIndex :: rest => pairHeap ((heap.push (word width localIndex)).push (word width 1)) rest

def lastScratch (scratch : ℕ) : List ℕ → ℕ
  | [] => scratch
  | localIndex :: rest => lastScratch localIndex rest

@[simp] theorem pairHeap_size (heap : Array (Word width)) (labels : List ℕ) :
    (pairHeap heap labels).size = heap.size + 2 * labels.length := by
  induction labels generalizing heap with
  | nil => simp [pairHeap]
  | cons localIndex rest ih => simp only [pairHeap, ih, Array.size_push, List.length_cons]; omega

theorem stored_append (heap : Array (Word width)) (table : ℕ) (labels : List ℕ)
    (stored : StoredDescending heap table labels) (suffix : Array (Word width)) :
    StoredDescending (heap ++ suffix) table labels := by
  induction labels with
  | nil => trivial
  | cons localIndex rest ih =>
    rcases stored with ⟨bound, cell, fits, tail⟩
    exact ⟨by simp only [Array.size_append]; omega,
      (Array.getElem?_append_left bound).trans cell, fits, ih tail⟩

/-- The whole physical countdown appends exactly one signed positive row.
The list parameter only states the actual indexed table correspondence. -/
theorem execution (program : Program width 4) (heap : Array (Word width))
    (base table scratch : ℕ) (labels : List ℕ) (stack output : List (Word width))
    (stored : StoredDescending heap table labels)
    (pointerFits : table + labels.length < 2 ^ width)
    (countFits : labels.length < 2 ^ width)
    (room : heap.size + 2 * labels.length ≤ 2 ^ width)
    (fits : base + 12 < 2 ^ width) (block : BlockAt program base (code width base)) :
    Execution program (atState heap base labels.length scratch (table + labels.length) 0 stack output)
      (atState (pairHeap heap labels) (base + 12) 0 (lastScratch scratch labels) table 0 stack output)
      (12 * labels.length + 1) (5 + heap.size + 2 * labels.length + stack.length + output.length) := by
  induction labels generalizing heap scratch with
  | nil =>
    have transition : programStep program (atState heap base 0 scratch table 0 stack output) =
        some (atState heap (base + 12) 0 scratch table 0 stack output) := by
      rw [fetched program _ base (.branchZero 0 (word width (base + 12))) rfl (by omega)
        (by simpa [code] using block 0 (by simp [code]))]
      simp [step, atState, State.advance, word]
    simpa only [List.length_nil, pairHeap, lastScratch, Nat.mul_zero, Nat.add_zero,
      atState_liveWords, Nat.max_self] using Execution.cons transition (Execution.refl _)
  | cons localIndex rest ih =>
    rcases stored with ⟨bound, cell, localFits, tail⟩
    have first := iteration_execution program heap base rest.length (table + rest.length)
      localIndex scratch stack output (by simpa using countFits) (by simpa [Nat.add_assoc] using pointerFits)
      localFits bound cell (by simp only [List.length_cons] at room; omega) fits block
    have appended : StoredDescending ((heap.push (word width localIndex)).push (word width 1)) table rest := by
      have pairEq : (heap.push (word width localIndex)).push (word width 1) =
          heap ++ #[(word width localIndex), (word width 1)] := by
        rw [Array.push_eq_append, Array.push_eq_append, Array.append_assoc]
        rfl
      rw [pairEq]
      exact stored_append heap table rest tail _
    have later := ih ((heap.push (word width localIndex)).push (word width 1)) localIndex appended
      (by simp only [List.length_cons] at pointerFits; omega)
      (by simp only [List.length_cons] at countFits; omega)
      (by simp only [List.length_cons] at room; simp only [Array.size_push]; omega)
    convert first.append later using 1 <;>
      (try simp only [List.length_cons, pairHeap, lastScratch, Array.size_push, Nat.add_assoc]) <;> omega


/-- These labels specify the real descending channel-table traversal. -/
def channelLabels (state : Dictionary ambient) : ℕ → List ℕ
  | 0 => []
  | count + 1 => (ForestZeroNonempty.slotAt state count - 1) :: channelLabels state count

@[simp] theorem channelLabels_length (state : Dictionary ambient) (count : ℕ) :
    (channelLabels state count).length = count := by
  induction count with
  | zero => rfl
  | succ count ih => simp only [channelLabels, List.length_cons, ih]

/-- The actual inverse invariant supplies every bounded encoded table entry.
No caller-supplied label stream is required for the all-covered branch. -/
theorem channels_stored (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (state : Dictionary ambient) (represented : Represented heap layout state)
    (channels : ℕ) (within : channels ≤ ambient)
    (covered : ∀ channel : Fin channels,
      state.slots[(⟨channel.val, lt_of_lt_of_le channel.isLt within⟩ : Fin ambient).val] ≠ 0)
    (ambientFits : ambient + 1 < 2 ^ width) :
    StoredDescending heap layout.tableBase (channelLabels state channels) := by
  have coveredNat : ∀ index < channels, ForestZeroNonempty.slotAt state index ≠ 0 := by
    intro index bound
    simpa only [ForestZeroNonempty.slotAt, dite_eq_left (lt_of_lt_of_le bound within)] using
      covered ⟨index, bound⟩
  have storedPrefix : ∀ count ≤ channels,
      StoredDescending heap layout.tableBase (channelLabels state count) := by
    intro count
    induction count with
    | zero => intro _; trivial
    | succ count ih =>
      intro bounded
      have valid : count < ambient := by omega
      let coordinate : Fin ambient := ⟨count, valid⟩
      have nonzero : state.slots[count] ≠ 0 := by
        simpa only [ForestZeroNonempty.slotAt, dite_eq_left valid] using coveredNat count (by omega)
      have encoded := encoded_bound state represented.coherent coordinate
      have capacity := count_le_ambient state represented.coherent
      have exactCode : state.slots[count] - 1 + 1 = state.slots[count] := by omega
      dsimp only [channelLabels, StoredDescending]
      refine ⟨?_, ?_, ?_, ih (by omega)⟩
      · simpa only [channelLabels_length] using layout.table_valid coordinate
      · simpa only [channelLabels_length, ForestZeroNonempty.slotAt, dite_eq_left valid, exactCode]
          using represented.slots coordinate
      · simp only [ForestZeroNonempty.slotAt, dite_eq_left valid, exactCode]
        change state.slots[count] < 2 ^ width
        have bound : state.slots[count] ≤ state.coordinates.size := encoded
        omega
  exact storedPrefix channels (le_refl _)

/-- All-covered channel count is bounded by the actual first-touch local count. -/
theorem covered_count (state : Dictionary ambient) (coherent : Coherent state)
    (channels : ℕ) (within : channels ≤ ambient)
    (covered : ∀ channel : Fin channels,
      state.slots[(⟨channel.val, lt_of_lt_of_le channel.isLt within⟩ : Fin ambient).val] ≠ 0) :
    channels ≤ state.coordinates.size := by
  apply ForestZeroNonempty.marked_bound state coherent channels within
  intro index bound
  simpa only [ForestZeroNonempty.slotAt, dite_eq_left (lt_of_lt_of_le bound within)] using covered ⟨index, bound⟩

def positiveClause (state : Dictionary ambient) (channels : ℕ) : Controller.CNF.Clause ℕ :=
  (channelLabels state channels).map (fun localIndex => (localIndex, true))

private theorem positiveClause_index (state : Dictionary ambient) (values : ℕ → Bool) (channels : ℕ) :
    Controller.CNF.ClauseHolds values (positiveClause state channels) ↔
      ∃ index < channels, values (ForestZeroNonempty.slotAt state index - 1) = true := by
  induction channels with
  | zero => simp [positiveClause, channelLabels, Controller.CNF.ClauseHolds]
  | succ channels ih =>
    rw [show positiveClause state (channels + 1) =
      (ForestZeroNonempty.slotAt state channels - 1, true) :: positiveClause state channels from rfl,
      Controller.CNF.clauseHolds_cons, ih]
    change (values (ForestZeroNonempty.slotAt state channels - 1) = true ∨
      ∃ index < channels, values (ForestZeroNonempty.slotAt state index - 1) = true) ↔ _
    constructor
    · rintro (last | earlier)
      · exact ⟨channels, by omega, last⟩
      · rcases earlier with ⟨index, bound, value⟩
        exact ⟨index, by omega, value⟩
    · rintro ⟨index, bound, value⟩
      by_cases last : index = channels
      · subst index; exact Or.inl value
      · exact Or.inr ⟨index, by omega, value⟩

/-- The emitted positive row enforces genuine channel nonemptiness under the
same dictionary lift used by the cone zero-model theorem. -/
theorem positiveClause_holds (state : Dictionary ambient) (values : ℕ → Bool) (unused : Bool)
    (channels : ℕ) (within : channels ≤ ambient)
    (covered : ∀ channel : Fin channels,
      state.slots[(⟨channel.val, lt_of_lt_of_le channel.isLt within⟩ : Fin ambient).val] ≠ 0) :
    Controller.CNF.ClauseHolds values (positiveClause state channels) ↔
      ∃ channel : Fin channels, ForestZeroModelLift.lift state unused values
        ⟨channel.val, lt_of_lt_of_le channel.isLt within⟩ = true := by
  rw [positiveClause_index]
  constructor
  · rintro ⟨index, bound, value⟩
    refine ⟨⟨index, bound⟩, ?_⟩
    simpa only [ForestZeroModelLift.lift, ite_eq_right (covered ⟨index, bound⟩),
      ForestZeroNonempty.slotAt, dite_eq_left (lt_of_lt_of_le bound within)] using value
  · rintro ⟨channel, value⟩
    refine ⟨channel.val, channel.isLt, ?_⟩
    simpa only [ForestZeroModelLift.lift, ite_eq_right (covered channel),
      ForestZeroNonempty.slotAt, dite_eq_left (lt_of_lt_of_le channel.isLt within)] using value

/-- The full countdown is instantiated from the physical dictionary. Its
channel visits are bounded by the actual localIndex count, not the ambient size. -/
theorem allcovered_execution (program : Program width 4) (heap : Array (Word width))
    (layout : Layout ambient heap.size) (state : Dictionary ambient)
    (represented : Represented heap layout state) (channels base scratch : ℕ)
    (within : channels ≤ ambient)
    (covered : ∀ channel : Fin channels,
      state.slots[(⟨channel.val, lt_of_lt_of_le channel.isLt within⟩ : Fin ambient).val] ≠ 0)
    (stack output : List (Word width)) (ambientFits : ambient + 1 < 2 ^ width)
    (room : heap.size + 2 * channels < 2 ^ width)
    (fits : base + 12 < 2 ^ width) (block : BlockAt program base (code width base)) :
    Execution program (atState heap base channels scratch (layout.tableBase + channels) 0 stack output)
      (atState (pairHeap heap (channelLabels state channels)) (base + 12) 0
        (lastScratch scratch (channelLabels state channels)) layout.tableBase 0 stack output)
      (12 * channels + 1) (5 + heap.size + 2 * channels + stack.length + output.length) ∧
      channels ≤ state.coordinates.size := by
  have stored := channels_stored heap layout state represented channels within covered ambientFits
  have pointerFits : layout.tableBase + channels < 2 ^ width := by
    have := layout.tableBound; omega
  have run := execution program heap base layout.tableBase scratch (channelLabels state channels) stack output
    stored (by simpa only [channelLabels_length] using pointerFits)
    (by simp only [channelLabels_length]; omega)
    (by simp only [channelLabels_length]; omega) fits block
  exact ⟨by simpa only [channelLabels_length] using run,
    covered_count state represented.coherent channels within covered⟩


def entryCode (width : ℕ) : Code width := [.constant 0 (word width 0), .load 0 0]

@[simp] theorem entryCode_length : (entryCode width).length = 2 := rfl

/-- After the all-covered search, register zero is exhausted. Two actual
instructions reload the channel count from the protected graph header. -/
theorem entry_execution (program : Program width 4) (heap : Array (Word width))
    (base channels scratch pointer : ℕ) (stack output : List (Word width))
    (nonempty : 0 < heap.size) (cell : heap[0]? = some (word width channels))
    (fits : base + 2 < 2 ^ width) (block : BlockAt program base (entryCode width)) :
    Execution program (atState heap base 0 scratch pointer 0 stack output)
      (atState heap (base + 2) channels scratch pointer 0 stack output)
      2 (5 + heap.size + stack.length + output.length) := by
  let one := atState heap (base + 1) 0 scratch pointer 0 stack output
  let final := atState heap (base + 2) channels scratch pointer 0 stack output
  have first : programStep program (atState heap base 0 scratch pointer 0 stack output) = some one := by
    rw [fetched program _ base (.constant 0 (word width 0)) rfl (by omega)
      (by simpa [entryCode] using block 0 (by simp [entryCode]))]
    change some ((atState heap base 0 scratch pointer 0 stack output).advance.put 0 (word width 0)) = some one
    rw [advance_at _ _ _ _ _ _ _ _ (by omega), put0_at]
  have actual : heap[0] = word width channels := by
    rw [Array.getElem?_eq_getElem nonempty] at cell
    exact Option.some.inj cell
  have second : programStep program one = some final := by
    rw [fetched program one (base + 1) (.load 0 0) rfl (by omega)
      (by simpa [entryCode] using block 1 (by simp [entryCode]))]
    change (if valid : (word width 0).val < heap.size then
      some (one.advance.put 0 heap[(word width 0).val]) else none) = some final
    rw [show (word width 0).val = 0 by simp [word], dite_eq_left nonempty, actual,
      advance_at _ _ _ _ _ _ _ _ (by omega), put0_at]
  simpa only [one, final, atState_liveWords, Nat.max_self] using
    Execution.cons first (Execution.cons second (Execution.refl final))

def fullCode (width base : ℕ) : Code width := entryCode width ++ code width (base + 2)

@[simp] theorem fullCode_length : (fullCode width base).length = 14 := rfl

/-- This fetched caller uses the original count header, the search's retained
physical end pointer, and the actual allocated localIndex IDs. Initialization and
the preceding search are separate phases; neither is repeated here. -/
theorem loaded_allcovered_execution (program : Program width 4) (heap : Array (Word width))
    (layout : Layout ambient heap.size) (state : Dictionary ambient)
    (represented : Represented heap layout state) (channels base scratch : ℕ)
    (within : channels ≤ ambient)
    (covered : ∀ channel : Fin channels,
      state.slots[(⟨channel.val, lt_of_lt_of_le channel.isLt within⟩ : Fin ambient).val] ≠ 0)
    (stack output : List (Word width)) (ambientFits : ambient + 1 < 2 ^ width)
    (nonempty : 0 < heap.size) (header : heap[0]? = some (word width channels))
    (room : heap.size + 2 * channels < 2 ^ width)
    (fits : base + 14 < 2 ^ width) (block : BlockAt program base (fullCode width base)) :
    Execution program (atState heap base 0 scratch (layout.tableBase + channels) 0 stack output)
      (atState (pairHeap heap (channelLabels state channels)) (base + 14) 0
        (lastScratch scratch (channelLabels state channels)) layout.tableBase 0 stack output)
      (12 * channels + 3) (5 + heap.size + 2 * channels + stack.length + output.length) ∧
      12 * channels + 3 ≤ 12 * state.coordinates.size + 3 := by
  have entryBlock := BlockAt.prefix program base _ _ block
  have loopBlock : BlockAt program (base + 2) (code width (base + 2)) := by
    simpa only [entryCode_length] using BlockAt.suffix program base (entryCode width) _ block
  have first := entry_execution program heap base channels scratch (layout.tableBase + channels)
    stack output nonempty header (by omega) entryBlock
  obtain ⟨later, bounded⟩ := allcovered_execution program heap layout state represented channels
    (base + 2) scratch within covered stack output ambientFits room (by omega) loopBlock
  refine ⟨?_, by omega⟩
  convert first.append later using 1 <;> (try simp only [Nat.add_assoc]) <;> omega

end Controller.Cost.ForestZeroPositive
