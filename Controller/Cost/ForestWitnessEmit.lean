module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestInputLoader
public import Controller.Cost.UniformDAGScan
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.IntervalCases

@[expose] public section

/-! A fixed fetched loop emits the complement of a stored Boolean marker
region. It visits channel coordinates in descending order, so the machine's
prepending output operation produces ascending channel order. Repeated path
guards can be marked idempotently before this single emission phase. -/
namespace Controller.Cost.ForestWitnessEmit
open Controller.Cost.GateProgram Controller.Cost.ForestCounter
open Controller.Cost.ForestMarkerMachine

/-- Remaining count is register zero; the persistent marker base is register
three. The same ten instructions are reused for every output coordinate. -/
def code (width base : ℕ) : ForestCounter.Code width :=
  [.branchZero 0 (word width (base + 10)),
   .constant 1 (word width (2 ^ width - 1)), .add 0 0 1,
   .add 1 0 3, .load 2 1, .constant 1 (word width 1), .xor 2 2 1,
   .emit 2, .constant 1 (word width 0), .branchZero 1 (word width base)]
@[simp] theorem code_length : (code width base).length = 10 := rfl

def state (heap : Array (Word width)) (pc : ℕ) (count scratch loaded markerBase : Word width)
    (stack output : List (Word width)) : State width 4 :=
  UniformDAGScan.state heap pc count scratch loaded markerBase stack output

private theorem final_live (program : Program width registers)
    (trace : Execution program initial final ticks peak) : final.liveWords ≤ peak := by
  induction trace with
  | refl => exact Nat.le_refl _
  | cons transition rest ih => exact ih.trans (Nat.le_max_right _ _)

private theorem chain (program : Program width registers) (history : ℕ → State width registers)
    (count bound : ℕ)
    (transitions : ∀ index < count, programStep program (history index) = some (history (index + 1)))
    (live : ∀ index ≤ count, (history index).liveWords ≤ bound) :
    ∃ peak, Execution program (history 0) (history count) count peak ∧ peak ≤ bound := by
  induction count generalizing history with
  | zero => exact ⟨_, Execution.refl _, live 0 (by omega)⟩
  | succ count ih =>
      obtain ⟨peak, trace, peakBound⟩ := ih (fun index => history (index + 1))
        (fun index inside => transitions (index + 1) (by omega))
        (fun index inside => live (index + 1) (by omega))
      refine ⟨_, ?_, max_le (live 0 (by omega)) peakBound⟩
      simpa [Nat.add_comm] using Execution.cons (transitions 0 (by omega)) trace

private theorem fetchedBlock (program : Program width 4) (s : State width 4)
    (base offset : ℕ) (pc : s.pc = word width (base + offset))
    (fits : base + offset < 2 ^ width) (inside : offset < 10)
    (block : BlockAt program base (code width base)) :
    programStep program s = ((code width base)[offset]?).bind (fun instruction => step instruction s) := by
  unfold programStep
  rw [pc, show (word width (base + offset)).val = base + offset from Nat.mod_eq_of_lt fits,
    block offset (by simpa only [code_length] using inside)]
  rfl

def phases (heap : Array (Word width)) (base markerBase remaining : ℕ)
    (scratch loaded : Word width) (marked : Bool) (stack output : List (Word width)) :
    ℕ → State width 4 := fun index => match index with
  | 0 => state heap base (word width (remaining + 1)) scratch loaded (word width markerBase) stack output
  | 1 => state heap (base + 1) (word width (remaining + 1)) scratch loaded (word width markerBase) stack output
  | 2 => state heap (base + 2) (word width (remaining + 1)) (word width (2 ^ width - 1)) loaded (word width markerBase) stack output
  | 3 => state heap (base + 3) (word width remaining) (word width (2 ^ width - 1)) loaded (word width markerBase) stack output
  | 4 => state heap (base + 4) (word width remaining) (word width (remaining + markerBase)) loaded (word width markerBase) stack output
  | 5 => state heap (base + 5) (word width remaining) (word width (remaining + markerBase)) (boolWord width marked) (word width markerBase) stack output
  | 6 => state heap (base + 6) (word width remaining) (word width 1) (boolWord width marked) (word width markerBase) stack output
  | 7 => state heap (base + 7) (word width remaining) (word width 1) (boolWord width (!marked)) (word width markerBase) stack output
  | 8 => state heap (base + 8) (word width remaining) (word width 1) (boolWord width (!marked)) (word width markerBase) stack (boolWord width (!marked) :: output)
  | 9 => state heap (base + 9) (word width remaining) (word width 0) (boolWord width (!marked)) (word width markerBase) stack (boolWord width (!marked) :: output)
  | _ => state heap base (word width remaining) (word width 0) (boolWord width (!marked)) (word width markerBase) stack (boolWord width (!marked) :: output)

/- Each fetched instruction is checked on its explicit incoming and outgoing
state. The ghost phase function is only used when assembling the ten checked
transitions; it is never decoded inside an instruction proof. -/
private theorem transition_0 (program : Program width 4) (heap : Array (Word width))
    (base markerBase remaining : ℕ) (scratch loaded : Word width) (marked : Bool)
    (stack output : List (Word width)) (programFits : base + 10 < 2 ^ width)
    (countFits : remaining + 1 < 2 ^ width) (cellBound : markerBase + remaining < heap.size)
    (heapFits : heap.size ≤ 2 ^ width)
    (cell : heap[markerBase + remaining]'cellBound = boolWord width marked)
    (block : BlockAt program base (code width base)) :
    programStep program (state heap (base) (word width (remaining + 1)) (scratch) (loaded) (word width markerBase) stack (output)) = some (state heap (base + 1) (word width (remaining + 1)) (scratch) (loaded) (word width markerBase) stack (output)) := by
  have pcFits (offset : ℕ) (bound : offset ≤ 10) : base + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left bound base) programFits
  rw [fetchedBlock program _ base 0 (by rfl) (pcFits 0 (by decide)) (by decide) block]
  change step (.branchZero 0 (word width (base + 10))) (state heap (base) (word width (remaining + 1)) (scratch) (loaded) (word width markerBase) stack (output)) = some (state heap (base + 1) (word width (remaining + 1)) (scratch) (loaded) (word width markerBase) stack (output))
  have pcValue : (base + 0) % 2 ^ width = base + 0 := Nat.mod_eq_of_lt (pcFits 0 (by decide))
  have countValue : (remaining + 1) % 2 ^ width = remaining + 1 := Nat.mod_eq_of_lt countFits
  all_goals simp [step, state, UniformDAGScan.state, State.advance, State.put, boolWord, word, pcValue, countValue, Nat.add_assoc]
  all_goals try (congr 1; funext register; fin_cases register <;> simp)

private theorem transition_1 (program : Program width 4) (heap : Array (Word width))
    (base markerBase remaining : ℕ) (scratch loaded : Word width) (marked : Bool)
    (stack output : List (Word width)) (programFits : base + 10 < 2 ^ width)
    (countFits : remaining + 1 < 2 ^ width) (cellBound : markerBase + remaining < heap.size)
    (heapFits : heap.size ≤ 2 ^ width)
    (cell : heap[markerBase + remaining]'cellBound = boolWord width marked)
    (block : BlockAt program base (code width base)) :
    programStep program (state heap (base + 1) (word width (remaining + 1)) (scratch) (loaded) (word width markerBase) stack (output)) = some (state heap (base + 2) (word width (remaining + 1)) (word width (2 ^ width - 1)) (loaded) (word width markerBase) stack (output)) := by
  have pcFits (offset : ℕ) (bound : offset ≤ 10) : base + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left bound base) programFits
  rw [fetchedBlock program _ base 1 (by rfl) (pcFits 1 (by decide)) (by decide) block]
  change step (.constant 1 (word width (2 ^ width - 1))) (state heap (base + 1) (word width (remaining + 1)) (scratch) (loaded) (word width markerBase) stack (output)) = some (state heap (base + 2) (word width (remaining + 1)) (word width (2 ^ width - 1)) (loaded) (word width markerBase) stack (output))
  have pcValue : (base + 1) % 2 ^ width = base + 1 := Nat.mod_eq_of_lt (pcFits 1 (by decide))
  all_goals simp [step, state, UniformDAGScan.state, State.advance, State.put, boolWord, word, pcValue, Nat.add_assoc]
  all_goals try (congr 1; funext register; fin_cases register <;> simp)

private theorem transition_2 (program : Program width 4) (heap : Array (Word width))
    (base markerBase remaining : ℕ) (scratch loaded : Word width) (marked : Bool)
    (stack output : List (Word width)) (programFits : base + 10 < 2 ^ width)
    (countFits : remaining + 1 < 2 ^ width) (cellBound : markerBase + remaining < heap.size)
    (heapFits : heap.size ≤ 2 ^ width)
    (cell : heap[markerBase + remaining]'cellBound = boolWord width marked)
    (block : BlockAt program base (code width base)) :
    programStep program (state heap (base + 2) (word width (remaining + 1)) (word width (2 ^ width - 1)) (loaded) (word width markerBase) stack (output)) = some (state heap (base + 3) (word width remaining) (word width (2 ^ width - 1)) (loaded) (word width markerBase) stack (output)) := by
  have pcFits (offset : ℕ) (bound : offset ≤ 10) : base + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left bound base) programFits
  rw [fetchedBlock program _ base 2 (by rfl) (pcFits 2 (by decide)) (by decide) block]
  change step (.add 0 0 1) (state heap (base + 2) (word width (remaining + 1)) (word width (2 ^ width - 1)) (loaded) (word width markerBase) stack (output)) = some (state heap (base + 3) (word width remaining) (word width (2 ^ width - 1)) (loaded) (word width markerBase) stack (output))
  have pcValue : (base + 2) % 2 ^ width = base + 2 := Nat.mod_eq_of_lt (pcFits 2 (by decide))
  have countValue : (remaining + 1) % 2 ^ width = remaining + 1 := Nat.mod_eq_of_lt countFits
  have remainingValue : remaining % 2 ^ width = remaining := Nat.mod_eq_of_lt (by omega)
  have decrementValue : (2 ^ width - 1) % 2 ^ width = 2 ^ width - 1 :=
    Nat.mod_eq_of_lt (Nat.sub_lt (Nat.two_pow_pos width) (by decide))
  have wrap : remaining + 1 + (2 ^ width - 1) = 2 ^ width + remaining := by
    have := Nat.two_pow_pos width
    omega
  have arithmetic : (remaining + (1 + (2 ^ width - 1))) % 2 ^ width = remaining := by
    rw [← Nat.add_assoc, wrap, Nat.add_mod_left, remainingValue]
  all_goals simp [step, state, UniformDAGScan.state, State.advance, State.put, boolWord, word, pcValue, countValue, remainingValue, decrementValue, arithmetic, Nat.add_assoc]
  all_goals try (congr 1; funext register; fin_cases register <;> simp)

private theorem transition_3 (program : Program width 4) (heap : Array (Word width))
    (base markerBase remaining : ℕ) (scratch loaded : Word width) (marked : Bool)
    (stack output : List (Word width)) (programFits : base + 10 < 2 ^ width)
    (countFits : remaining + 1 < 2 ^ width) (cellBound : markerBase + remaining < heap.size)
    (heapFits : heap.size ≤ 2 ^ width)
    (cell : heap[markerBase + remaining]'cellBound = boolWord width marked)
    (block : BlockAt program base (code width base)) :
    programStep program (state heap (base + 3) (word width remaining) (word width (2 ^ width - 1)) (loaded) (word width markerBase) stack (output)) = some (state heap (base + 4) (word width remaining) (word width (remaining + markerBase)) (loaded) (word width markerBase) stack (output)) := by
  have pcFits (offset : ℕ) (bound : offset ≤ 10) : base + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left bound base) programFits
  rw [fetchedBlock program _ base 3 (by rfl) (pcFits 3 (by decide)) (by decide) block]
  change step (.add 1 0 3) (state heap (base + 3) (word width remaining) (word width (2 ^ width - 1)) (loaded) (word width markerBase) stack (output)) = some (state heap (base + 4) (word width remaining) (word width (remaining + markerBase)) (loaded) (word width markerBase) stack (output))
  have pcValue : (base + 3) % 2 ^ width = base + 3 := Nat.mod_eq_of_lt (pcFits 3 (by decide))
  have remainingValue : remaining % 2 ^ width = remaining := Nat.mod_eq_of_lt (by omega)
  have baseValue : markerBase % 2 ^ width = markerBase := Nat.mod_eq_of_lt (by omega)
  all_goals simp [step, state, UniformDAGScan.state, State.advance, State.put, boolWord, word, pcValue, remainingValue, baseValue, Nat.add_assoc]
  all_goals try (congr 1; funext register; fin_cases register <;> simp)

private theorem transition_4 (program : Program width 4) (heap : Array (Word width))
    (base markerBase remaining : ℕ) (scratch loaded : Word width) (marked : Bool)
    (stack output : List (Word width)) (programFits : base + 10 < 2 ^ width)
    (countFits : remaining + 1 < 2 ^ width) (cellBound : markerBase + remaining < heap.size)
    (heapFits : heap.size ≤ 2 ^ width)
    (cell : heap[markerBase + remaining]'cellBound = boolWord width marked)
    (block : BlockAt program base (code width base)) :
    programStep program (state heap (base + 4) (word width remaining) (word width (remaining + markerBase)) (loaded) (word width markerBase) stack (output)) = some (state heap (base + 5) (word width remaining) (word width (remaining + markerBase)) (boolWord width marked) (word width markerBase) stack (output)) := by
  have pcFits (offset : ℕ) (bound : offset ≤ 10) : base + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left bound base) programFits
  rw [fetchedBlock program _ base 4 (by rfl) (pcFits 4 (by decide)) (by decide) block]
  change step (.load 2 1) (state heap (base + 4) (word width remaining) (word width (remaining + markerBase)) (loaded) (word width markerBase) stack (output)) = some (state heap (base + 5) (word width remaining) (word width (remaining + markerBase)) (boolWord width marked) (word width markerBase) stack (output))
  have pcValue : (base + 4) % 2 ^ width = base + 4 := Nat.mod_eq_of_lt (pcFits 4 (by decide))
  have addressValue : (remaining + markerBase) % 2 ^ width = remaining + markerBase :=
    Nat.mod_eq_of_lt (by omega)
  have actualBound : remaining + markerBase < heap.size := by omega
  have actualCell : heap[remaining + markerBase]'actualBound = boolWord width marked := by
    simpa only [Nat.add_comm] using cell
  all_goals simp [step, state, UniformDAGScan.state, State.advance, State.put, boolWord, word, pcValue, addressValue, actualBound, actualCell, Nat.add_assoc]
  all_goals try (congr 1; funext register; fin_cases register <;> simp)

private theorem transition_5 (program : Program width 4) (heap : Array (Word width))
    (base markerBase remaining : ℕ) (scratch loaded : Word width) (marked : Bool)
    (stack output : List (Word width)) (programFits : base + 10 < 2 ^ width)
    (countFits : remaining + 1 < 2 ^ width) (cellBound : markerBase + remaining < heap.size)
    (heapFits : heap.size ≤ 2 ^ width)
    (cell : heap[markerBase + remaining]'cellBound = boolWord width marked)
    (block : BlockAt program base (code width base)) :
    programStep program (state heap (base + 5) (word width remaining) (word width (remaining + markerBase)) (boolWord width marked) (word width markerBase) stack (output)) = some (state heap (base + 6) (word width remaining) (word width 1) (boolWord width marked) (word width markerBase) stack (output)) := by
  have pcFits (offset : ℕ) (bound : offset ≤ 10) : base + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left bound base) programFits
  rw [fetchedBlock program _ base 5 (by rfl) (pcFits 5 (by decide)) (by decide) block]
  change step (.constant 1 (word width 1)) (state heap (base + 5) (word width remaining) (word width (remaining + markerBase)) (boolWord width marked) (word width markerBase) stack (output)) = some (state heap (base + 6) (word width remaining) (word width 1) (boolWord width marked) (word width markerBase) stack (output))
  have pcValue : (base + 5) % 2 ^ width = base + 5 := Nat.mod_eq_of_lt (pcFits 5 (by decide))
  all_goals simp [step, state, UniformDAGScan.state, State.advance, State.put, boolWord, word, pcValue, Nat.add_assoc]
  all_goals try (congr 1; funext register; fin_cases register <;> simp)

private theorem transition_6 (program : Program width 4) (heap : Array (Word width))
    (base markerBase remaining : ℕ) (scratch loaded : Word width) (marked : Bool)
    (stack output : List (Word width)) (programFits : base + 10 < 2 ^ width)
    (countFits : remaining + 1 < 2 ^ width) (cellBound : markerBase + remaining < heap.size)
    (heapFits : heap.size ≤ 2 ^ width)
    (cell : heap[markerBase + remaining]'cellBound = boolWord width marked)
    (block : BlockAt program base (code width base)) :
    programStep program (state heap (base + 6) (word width remaining) (word width 1) (boolWord width marked) (word width markerBase) stack (output)) = some (state heap (base + 7) (word width remaining) (word width 1) (boolWord width (!marked)) (word width markerBase) stack (output)) := by
  have pcFits (offset : ℕ) (bound : offset ≤ 10) : base + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left bound base) programFits
  rw [fetchedBlock program _ base 6 (by rfl) (pcFits 6 (by decide)) (by decide) block]
  change step (.xor 2 2 1) (state heap (base + 6) (word width remaining) (word width 1) (boolWord width marked) (word width markerBase) stack (output)) = some (state heap (base + 7) (word width remaining) (word width 1) (boolWord width (!marked)) (word width markerBase) stack (output))
  have pcValue : (base + 6) % 2 ^ width = base + 6 := Nat.mod_eq_of_lt (pcFits 6 (by decide))
  have oneValue : 1 % 2 ^ width = 1 := Nat.mod_eq_of_lt (by omega)
  cases marked
  all_goals simp [step, state, UniformDAGScan.state, State.advance, State.put, boolWord, word, pcValue, oneValue, Nat.add_assoc]
  all_goals try (congr 1; funext register; fin_cases register <;> simp)

private theorem transition_7 (program : Program width 4) (heap : Array (Word width))
    (base markerBase remaining : ℕ) (scratch loaded : Word width) (marked : Bool)
    (stack output : List (Word width)) (programFits : base + 10 < 2 ^ width)
    (countFits : remaining + 1 < 2 ^ width) (cellBound : markerBase + remaining < heap.size)
    (heapFits : heap.size ≤ 2 ^ width)
    (cell : heap[markerBase + remaining]'cellBound = boolWord width marked)
    (block : BlockAt program base (code width base)) :
    programStep program (state heap (base + 7) (word width remaining) (word width 1) (boolWord width (!marked)) (word width markerBase) stack (output)) = some (state heap (base + 8) (word width remaining) (word width 1) (boolWord width (!marked)) (word width markerBase) stack (boolWord width (!marked) :: output)) := by
  have pcFits (offset : ℕ) (bound : offset ≤ 10) : base + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left bound base) programFits
  rw [fetchedBlock program _ base 7 (by rfl) (pcFits 7 (by decide)) (by decide) block]
  change step (.emit 2) (state heap (base + 7) (word width remaining) (word width 1) (boolWord width (!marked)) (word width markerBase) stack (output)) = some (state heap (base + 8) (word width remaining) (word width 1) (boolWord width (!marked)) (word width markerBase) stack (boolWord width (!marked) :: output))
  have pcValue : (base + 7) % 2 ^ width = base + 7 := Nat.mod_eq_of_lt (pcFits 7 (by decide))
  all_goals simp [step, state, UniformDAGScan.state, State.advance, State.put, boolWord, word, pcValue, Nat.add_assoc]
  all_goals try (congr 1; funext register; fin_cases register <;> simp)

private theorem transition_8 (program : Program width 4) (heap : Array (Word width))
    (base markerBase remaining : ℕ) (scratch loaded : Word width) (marked : Bool)
    (stack output : List (Word width)) (programFits : base + 10 < 2 ^ width)
    (countFits : remaining + 1 < 2 ^ width) (cellBound : markerBase + remaining < heap.size)
    (heapFits : heap.size ≤ 2 ^ width)
    (cell : heap[markerBase + remaining]'cellBound = boolWord width marked)
    (block : BlockAt program base (code width base)) :
    programStep program (state heap (base + 8) (word width remaining) (word width 1) (boolWord width (!marked)) (word width markerBase) stack (boolWord width (!marked) :: output)) = some (state heap (base + 9) (word width remaining) (word width 0) (boolWord width (!marked)) (word width markerBase) stack (boolWord width (!marked) :: output)) := by
  have pcFits (offset : ℕ) (bound : offset ≤ 10) : base + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left bound base) programFits
  rw [fetchedBlock program _ base 8 (by rfl) (pcFits 8 (by decide)) (by decide) block]
  change step (.constant 1 (word width 0)) (state heap (base + 8) (word width remaining) (word width 1) (boolWord width (!marked)) (word width markerBase) stack (boolWord width (!marked) :: output)) = some (state heap (base + 9) (word width remaining) (word width 0) (boolWord width (!marked)) (word width markerBase) stack (boolWord width (!marked) :: output))
  have pcValue : (base + 8) % 2 ^ width = base + 8 := Nat.mod_eq_of_lt (pcFits 8 (by decide))
  all_goals simp [step, state, UniformDAGScan.state, State.advance, State.put, boolWord, word, pcValue, Nat.add_assoc]
  all_goals try (congr 1; funext register; fin_cases register <;> simp)

private theorem transition_9 (program : Program width 4) (heap : Array (Word width))
    (base markerBase remaining : ℕ) (scratch loaded : Word width) (marked : Bool)
    (stack output : List (Word width)) (programFits : base + 10 < 2 ^ width)
    (countFits : remaining + 1 < 2 ^ width) (cellBound : markerBase + remaining < heap.size)
    (heapFits : heap.size ≤ 2 ^ width)
    (cell : heap[markerBase + remaining]'cellBound = boolWord width marked)
    (block : BlockAt program base (code width base)) :
    programStep program (state heap (base + 9) (word width remaining) (word width 0) (boolWord width (!marked)) (word width markerBase) stack (boolWord width (!marked) :: output)) = some (state heap (base) (word width remaining) (word width 0) (boolWord width (!marked)) (word width markerBase) stack (boolWord width (!marked) :: output)) := by
  have pcFits (offset : ℕ) (bound : offset ≤ 10) : base + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left bound base) programFits
  rw [fetchedBlock program _ base 9 (by rfl) (pcFits 9 (by decide)) (by decide) block]
  change step (.branchZero 1 (word width base)) (state heap (base + 9) (word width remaining) (word width 0) (boolWord width (!marked)) (word width markerBase) stack (boolWord width (!marked) :: output)) = some (state heap (base) (word width remaining) (word width 0) (boolWord width (!marked)) (word width markerBase) stack (boolWord width (!marked) :: output))
  have pcValue : (base + 9) % 2 ^ width = base + 9 := Nat.mod_eq_of_lt (pcFits 9 (by decide))
  all_goals simp [step, state, UniformDAGScan.state, State.advance, State.put, boolWord, word, pcValue, Nat.add_assoc]
  all_goals try (congr 1; funext register; fin_cases register <;> simp)

private theorem transitions (program : Program width 4) (heap : Array (Word width))
    (base markerBase remaining : ℕ) (scratch loaded : Word width) (marked : Bool)
    (stack output : List (Word width)) (programFits : base + 10 < 2 ^ width)
    (countFits : remaining + 1 < 2 ^ width) (cellBound : markerBase + remaining < heap.size)
    (heapFits : heap.size ≤ 2 ^ width)
    (cell : heap[markerBase + remaining]'cellBound = boolWord width marked)
    (block : BlockAt program base (code width base)) (index : Fin 10) :
    programStep program (phases heap base markerBase remaining scratch loaded marked stack output index.val) =
      some (phases heap base markerBase remaining scratch loaded marked stack output (index.val + 1)) := by
  fin_cases index
  · exact transition_0 program heap base markerBase remaining scratch loaded marked
      stack output programFits countFits cellBound heapFits cell block
  · exact transition_1 program heap base markerBase remaining scratch loaded marked
      stack output programFits countFits cellBound heapFits cell block
  · exact transition_2 program heap base markerBase remaining scratch loaded marked
      stack output programFits countFits cellBound heapFits cell block
  · exact transition_3 program heap base markerBase remaining scratch loaded marked
      stack output programFits countFits cellBound heapFits cell block
  · exact transition_4 program heap base markerBase remaining scratch loaded marked
      stack output programFits countFits cellBound heapFits cell block
  · exact transition_5 program heap base markerBase remaining scratch loaded marked
      stack output programFits countFits cellBound heapFits cell block
  · exact transition_6 program heap base markerBase remaining scratch loaded marked
      stack output programFits countFits cellBound heapFits cell block
  · exact transition_7 program heap base markerBase remaining scratch loaded marked
      stack output programFits countFits cellBound heapFits cell block
  · exact transition_8 program heap base markerBase remaining scratch loaded marked
      stack output programFits countFits cellBound heapFits cell block
  · exact transition_9 program heap base markerBase remaining scratch loaded marked
      stack output programFits countFits cellBound heapFits cell block

/-- One marker read contributes exactly ten fetched steps and one output word.
No heap cell or caller stack word is modified. -/
theorem entry_execution (program : Program width 4) (heap : Array (Word width))
    (base markerBase remaining : ℕ) (scratch loaded : Word width) (marked : Bool)
    (stack output : List (Word width)) (programFits : base + 10 < 2 ^ width)
    (countFits : remaining + 1 < 2 ^ width) (cellBound : markerBase + remaining < heap.size)
    (heapFits : heap.size ≤ 2 ^ width)
    (cell : heap[markerBase + remaining]'cellBound = boolWord width marked)
    (block : BlockAt program base (code width base)) :
    Execution program
      (state heap base (word width (remaining + 1)) scratch loaded (word width markerBase) stack output)
      (state heap base (word width remaining) (word width 0) (boolWord width (!marked))
        (word width markerBase) stack (boolWord width (!marked) :: output))
      10 (6 + heap.size + stack.length + output.length) := by
  obtain ⟨peak, trace, bound⟩ := chain program
    (phases heap base markerBase remaining scratch loaded marked stack output) 10
    (6 + heap.size + stack.length + output.length)
    (by intro index inside; exact transitions program heap base markerBase remaining scratch loaded marked
          stack output programFits countFits cellBound heapFits cell block ⟨index, inside⟩)
    (by intro index inside; interval_cases index <;>
          simp [phases, state, UniformDAGScan.state, State.liveWords] <;> omega)
  have lower := final_live program trace
  have equal : peak = 6 + heap.size + stack.length + output.length := by
    simp only [phases, state, UniformDAGScan.state, State.liveWords, List.length_cons] at lower
    omega
  subst peak
  exact trace

/-- The zero count takes only the stored exit branch. -/
theorem zero_execution (program : Program width 4) (heap : Array (Word width))
    (base markerBase : ℕ) (scratch loaded : Word width) (stack output : List (Word width))
    (programFits : base + 10 < 2 ^ width) (block : BlockAt program base (code width base)) :
    Execution program (state heap base (word width 0) scratch loaded (word width markerBase) stack output)
      (state heap (base + 10) (word width 0) scratch loaded (word width markerBase) stack output)
      1 (5 + heap.size + stack.length + output.length) := by
  have fetched : program[base]? = some (.branchZero 0 (word width (base + 10))) := by
    simpa [code] using block 0 (by simp [code])
  have pcFits : base < 2 ^ width := by omega
  have transition : programStep program
      (state heap base (word width 0) scratch loaded (word width markerBase) stack output) =
        some (state heap (base + 10) (word width 0) scratch loaded (word width markerBase) stack output) := by
    unfold programStep
    rw [show (state heap base (word width 0) scratch loaded (word width markerBase) stack output).pc.val = base from Nat.mod_eq_of_lt pcFits, fetched]
    simp [code, step, state, UniformDAGScan.state, State.advance, word]
  have trace := Execution.cons transition (Execution.refl
    (state heap (base + 10) (word width 0) scratch loaded (word width markerBase) stack output))
  convert trace using 1 <;> simp [state, UniformDAGScan.state, State.liveWords] <;> omega

/-- Every actual marker cell is read once. Descending visits and prepending
emission give ascending coordinate order, with exact linear ticks and peak. -/
theorem execution (program : Program width 4) (heap : Array (Word width))
    (base markerBase : ℕ) (marked : Fin n → Bool) (scratch loaded : Word width)
    (stack output : List (Word width))
    (programFits : base + 10 < 2 ^ width) (countFits : n < 2 ^ width)
    (region : markerBase + n ≤ heap.size) (heapFits : heap.size ≤ 2 ^ width)
    (cells : ∀ coordinate : Fin n,
      heap[markerBase + coordinate.val]'(by have := coordinate.isLt; omega) = boolWord width (marked coordinate))
    (block : BlockAt program base (code width base)) :
    ∃ finalScratch finalLoaded,
      Execution program (state heap base (word width n) scratch loaded (word width markerBase) stack output)
        (state heap (base + 10) (word width 0) finalScratch finalLoaded (word width markerBase) stack
          (List.ofFn (fun coordinate => boolWord width (!(marked coordinate))) ++ output))
        (10 * n + 1) (5 + heap.size + stack.length + (n + output.length)) := by
  induction n generalizing scratch loaded output with
  | zero =>
      exact ⟨scratch, loaded, by simpa using zero_execution program heap base markerBase scratch loaded stack output programFits block⟩
  | succ n ih =>
      have cellBound : markerBase + n < heap.size := by omega
      have first := entry_execution program heap base markerBase n scratch loaded (marked (Fin.last n))
        stack output programFits countFits cellBound heapFits (cells (Fin.last n)) block
      obtain ⟨finalScratch, finalLoaded, later⟩ := ih (fun coordinate => marked coordinate.castSucc)
        (word width 0) (boolWord width (!(marked (Fin.last n))))
        (boolWord width (!(marked (Fin.last n))) :: output) (by omega) (by omega)
        (by intro coordinate; exact cells coordinate.castSucc)
      have joined := first.append later
      refine ⟨finalScratch, finalLoaded, ?_⟩
      convert joined using 1
      · simp only [List.ofFn_succ_last, List.singleton_append, List.append_assoc]
      · omega
      · simp only [List.length_cons]
        omega

end Controller.Cost.ForestWitnessEmit
