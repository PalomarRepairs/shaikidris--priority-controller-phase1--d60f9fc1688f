module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.EnumerationFixedProfile

public import Mathlib.Tactic.FinCases

@[expose] public section

/-! Directory allocation with a saved physical dictionary count. The pass
appends every row boundary before emitting source pairs and restores register
two from the caller stack. -/
namespace Controller.Cost.EnumerationDirectoryFrame
open Controller.CNF Controller.Cost.GateProgram Controller.Cost.ForestZeroTouch

def code (width : Nat) (rows : List (Clause α)) : Code width :=
  [.push 2] ++ (ForestZeroDirectory.code width rows ++ [.pop 2])

@[simp] theorem code_length (rows : List (Clause α)) :
    (code width rows).length = 2 + 5 * rows.length := by
  simp [code]
  omega

private theorem fetched (program : Program width 4) (state : State width 4)
    (cursor : Nat) (instruction : Instruction width 4)
    (position : state.pc = word width cursor) (room : cursor < 2 ^ width)
    (present : program[cursor]? = some instruction) :
    programStep program state = step instruction state := by
  unfold programStep
  rw [position, show (word width cursor).val = cursor from Nat.mod_eq_of_lt room, present]
  rfl

theorem save_count (program : Program width 4) (heap : Array (Word width))
    (base cursor table count scratch : Nat) (stack output : List (Word width))
    (room : base + 1 < 2 ^ width) (present : program[base]? = some (.push 2)) :
    Execution program (atState heap base cursor table count scratch stack output)
      (atState heap (base + 1) cursor table count scratch (word width count :: stack) output)
      1 (6 + heap.size + stack.length + output.length) := by
  let first := atState heap base cursor table count scratch stack output
  let last := atState heap (base + 1) cursor table count scratch (word width count :: stack) output
  have transition : programStep program first = some last := by
    rw [fetched program first base (.push 2) rfl (by omega) present]
    change some { first.advance with stack := word width count :: stack } = some last
    simp only [first, last, atState, State.advance,
      show (word width base).val = base from Nat.mod_eq_of_lt (by omega)]
  convert Execution.cons transition (Execution.refl last) using 1
  all_goals simp only [first, last, atState_liveWords, List.length_cons]
  all_goals omega

theorem restore_count (program : Program width 4) (heap : Array (Word width))
    (base cursor table oldCount count scratch : Nat) (stack output : List (Word width))
    (room : base + 1 < 2 ^ width) (present : program[base]? = some (.pop 2)) :
    Execution program (atState heap base cursor table oldCount scratch (word width count :: stack) output)
      (atState heap (base + 1) cursor table count scratch stack output)
      1 (6 + heap.size + stack.length + output.length) := by
  let first := atState heap base cursor table oldCount scratch (word width count :: stack) output
  let last := atState heap (base + 1) cursor table count scratch stack output
  have transition : programStep program first = some last := by
    rw [fetched program first base (.pop 2) rfl (by omega) present]
    change some { first.advance.put 2 (word width count) with stack := stack } = some last
    simp only [first, last, atState, State.advance, State.put,
      show (word width base).val = base from Nat.mod_eq_of_lt (by omega)]
    simp only [Option.some.injEq, State.mk.injEq, and_true]
    funext register
    fin_cases register <;> rfl
  convert Execution.cons transition (Execution.refl last) using 1
  all_goals simp only [first, last, atState_liveWords, List.length_cons]
  all_goals omega

theorem execution (program : Program width 4) (heap : Array (Word width))
    (base cursor table count scratch : Nat) (stack output : List (Word width))
    (rows : List (Clause α)) (room : heap.size + 2 * rows.length ≤ 2 ^ width)
    (pointersFit : cursor + 2 * (rows.map List.length).sum < 2 ^ width)
    (programFits : base + (code width rows).length < 2 ^ width)
    (block : BlockAt program base (code width rows)) :
    let result := ForestZeroDirectory.build heap cursor count rows
    Execution program (atState heap base cursor table count scratch stack output)
      (atState result.heap (base + (code width rows).length) result.cursor table count scratch stack output)
      (2 + 5 * rows.length) (6 + heap.size + 2 * rows.length + stack.length + output.length) := by
  have lengthEq := code_length (width := width) rows
  have countEq : (ForestZeroQuery.countClause : Clause α → Nat) = List.length := funext ForestZeroQuery.countClause_exact
  unfold code at block
  have pushAt := BlockAt.prefix program base _ _ block
  have rest := BlockAt.suffix program base _ _ block
  have directoryAt : BlockAt program (base + 1) (ForestZeroDirectory.code width rows) := by
    simpa only [List.length_cons, List.length_nil, Nat.add_zero] using BlockAt.prefix program _ _ _ rest
  have popAt := BlockAt.suffix program (base + 1) _ _ rest
  have first := save_count program heap base cursor table count scratch stack output (by omega)
    (by simpa using pushAt 0 (by simp))
  have middle := ForestZeroDirectory.execution program heap (base + 1) cursor table count scratch
    (word width count :: stack) output rows room
    (by rw [countEq]; exact pointersFit) (by rw [lengthEq] at programFits; simp; omega)
    directoryAt
  have last := restore_count program (ForestZeroDirectory.build heap cursor count rows).heap
    (base + 1 + (ForestZeroDirectory.code width rows).length)
    (ForestZeroDirectory.build heap cursor count rows).cursor table
    (ForestZeroDirectory.build heap cursor count rows).count count scratch stack output
    (by simp only [code_length] at programFits; simp; omega) (by simpa using popAt 0 (by simp))
  have joined := (first.append middle).append last
  simp only [ForestZeroDirectory.code_length, ForestZeroDirectory.build_size, List.length_cons] at joined
  rw [lengthEq]
  convert joined using 1
  all_goals first | rfl | omega | (congr 1; omega)

end Controller.Cost.EnumerationDirectoryFrame
