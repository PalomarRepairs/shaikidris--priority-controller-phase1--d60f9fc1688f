module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedNativeSuccessCode

public import Mathlib.Tactic.FinCases

@[expose] public section

namespace Controller.Cost.SharedQueryCleanupCode
open Controller.Cost.GateProgram

def code (width entry : Nat) : List (Instruction width 8) :=
  (ForestZeroReclaim.setupCode width).toList ++
  (ForestZeroReclaim.code width (entry + 3) (entry + 7)).toList ++
  (ForestZeroAdmissibleCaller.resetPrepareCode width).toList.map RegisterWiden.widenInstruction ++
  (ForestZeroReset.code width (entry + 22)).map RegisterWiden.widenInstruction ++
  [.pop 4]

@[simp] theorem code_length : (code width entry).length = 35 := by
  simp [code, ForestZeroReclaim.setupCode, ForestZeroReclaim.code,
    ForestZeroAdmissibleCaller.resetPrepareCode]

structure Physical (program : Program width 8) (entry : Nat) : Prop where
  setup : ∀ phase : Fin 3, program[entry + phase.val]? =
    (ForestZeroReclaim.setupCode width)[phase.val]?
  release : ForestZeroReclaim.At program (entry + 3) (entry + 7)
  prepare : ForestZeroCallerWiden.WidenedBlockAt program (entry + 7)
    (ForestZeroAdmissibleCaller.resetPrepareCode width).toList
  reset : ForestZeroCallerWiden.WidenedBlockAt program (entry + 22)
    (ForestZeroReset.code width (entry + 22))
  decision : program[entry + 34]? = some (.pop 4)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem physical_at (program : Program width 8) (entry : Nat)
    (present : SharedRootRead.BlockAt program entry (code width entry)) :
    Physical program entry := by
  have fetched : ∀ offset, offset < 35 → program[entry + offset]? =
      (code width entry)[offset]? := by
    intro offset bound
    exact present offset (by simpa using bound)
  constructor
  · intro phase
    fin_cases phase
    all_goals rw [fetched _ (by omega)]
    all_goals simp [code, ForestZeroReclaim.setupCode, List.getElem?_append]
  · intro phase
    fin_cases phase
    all_goals simp only [Nat.add_assoc, Nat.reduceAdd]
    all_goals rw [fetched _ (by omega)]
    all_goals simp [code, ForestZeroReclaim.setupCode, ForestZeroReclaim.code,
      List.getElem?_append]
  · intro offset bound
    have small : offset < 15 := by simpa [ForestZeroAdmissibleCaller.resetPrepareCode] using bound
    interval_cases offset
    all_goals simp only [Nat.add_assoc, Nat.reduceAdd]
    all_goals rw [fetched _ (by omega)]
    all_goals simp [code, ForestZeroReclaim.setupCode, ForestZeroReclaim.code,
      ForestZeroAdmissibleCaller.resetPrepareCode, List.getElem?_append,
      RegisterWiden.widenInstruction]
  · intro offset bound
    have small : offset < 12 := by simpa using bound
    interval_cases offset
    all_goals simp only [Nat.add_assoc, Nat.reduceAdd]
    all_goals rw [fetched _ (by omega)]
    all_goals simp [code, ForestZeroReclaim.setupCode, ForestZeroReclaim.code,
      ForestZeroAdmissibleCaller.resetPrepareCode, ForestZeroReset.code,
      List.getElem?_append, RegisterWiden.widenInstruction]
  · rw [fetched _ (by omega)]
    simp [code, ForestZeroReclaim.setupCode, ForestZeroReclaim.code,
      ForestZeroAdmissibleCaller.resetPrepareCode, ForestZeroReset.code,
      List.getElem?_append]

end Controller.Cost.SharedQueryCleanupCode
