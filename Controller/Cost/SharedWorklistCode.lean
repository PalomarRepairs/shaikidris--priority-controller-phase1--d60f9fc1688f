module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedSolverPrefix

public import Mathlib.Tactic.FinCases

@[expose] public section

namespace Controller.Cost.SharedWorklistCode
open Controller.Cost.GateProgram

def code (width entry n base projection cleanup : Nat) : Program width 8 :=
  Controller.Horn.WorklistSeed.code (n := n) width base entry (entry + 47) (entry + 121) ++
  Controller.Horn.WorklistAccept.headSetupCode (n := n) width base (entry + 51) ++
  Controller.Horn.WorklistFIFO.fetchCode (n := n) width base (entry + 51) (entry + 108) (entry + 70) ++
  Controller.Horn.WorklistFIFO.advanceCode (n := n) width base (entry + 51) ++
  Controller.Horn.WorklistBucketLoop.code width (entry + 70) (entry + 65) (entry + 82) ++
  Controller.Horn.WorklistBucketReady.code (n := n) width base (entry + 82) (entry + 65) (entry + 121) (entry + 70) ++
  ForestZeroAnswer.savedCode width 1 projection ++ ForestZeroAnswer.savedCode width 0 cleanup

@[simp] theorem code_size : (code width entry n base projection cleanup).size = 134 := by
  simp [code, Controller.Horn.WorklistSeed.code, Controller.Horn.WorklistAccept.headSetupCode,
    Controller.Horn.WorklistFIFO.fetchCode, Controller.Horn.WorklistFIFO.advanceCode,
    Controller.Horn.WorklistBucketLoop.code, Controller.Horn.WorklistBucketReady.code,
    ForestZeroAnswer.savedCode, ForestZeroAnswer.saveTagCode, ForestZeroAnswer.code]

structure Physical (program : Program width 8) (entry n base projection cleanup : Nat) : Prop where
  seed : Controller.Horn.WorklistSeed.At (n := n) program base entry (entry + 47) (entry + 121)
  head : ∀ phase : Fin 4, program[entry + 47 + phase.val]? =
    (Controller.Horn.WorklistAccept.headSetupCode (n := n) width base (entry + 51))[phase.val]?
  fetch : Controller.Horn.WorklistFIFO.FetchAt (n := n) program base (entry + 51) (entry + 108) (entry + 70)
  advance : Controller.Horn.WorklistFIFO.AdvanceAt (n := n) program base (entry + 65) (entry + 51)
  bucket : Controller.Horn.WorklistBucketLoop.At program (entry + 70) (entry + 65) (entry + 82)
  ready : Controller.Horn.WorklistBucketReady.At (n := n) program base (entry + 82) (entry + 65) (entry + 121) (entry + 70)
  success : ForestZeroAnswer.SavedAt program (entry + 108) 1 projection
  conflict : ForestZeroAnswer.SavedAt program (entry + 121) 0 cleanup

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem physical_at (program : Program width 8) (entry n base projection cleanup : Nat)
    (present : SharedRootRead.BlockAt program entry (code width entry n base projection cleanup).toList) :
    Physical program entry n base projection cleanup := by
  have fetched : ∀ offset, offset < 134 → program[entry + offset]? =
      (code width entry n base projection cleanup)[offset]? := by
    intro offset bound
    simpa only [Array.getElem?_toList] using present offset (by simp; exact bound)
  constructor
  all_goals intro phase
  all_goals fin_cases phase
  all_goals try simp only [Nat.add_assoc, Nat.reduceAdd]
  all_goals rw [fetched _ (by omega)]
  all_goals simp [code, Array.getElem?_append, Controller.Horn.WorklistSeed.code,
    Controller.Horn.WorklistAccept.headSetupCode, Controller.Horn.WorklistFIFO.fetchCode,
    Controller.Horn.WorklistFIFO.advanceCode, Controller.Horn.WorklistBucketLoop.code,
    Controller.Horn.WorklistBucketReady.code, ForestZeroAnswer.savedCode, ForestZeroAnswer.saveTagCode,
    ForestZeroAnswer.code, Nat.add_assoc]

end Controller.Cost.SharedWorklistCode
