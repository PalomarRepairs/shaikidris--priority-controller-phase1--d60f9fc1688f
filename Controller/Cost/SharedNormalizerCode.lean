module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedNormalizationShape
public import Controller.Cost.SharedRootRead

public import Mathlib.Tactic.FinCases

@[expose] public section

namespace Controller.Cost.SharedNormalizerCode
open Controller.Cost.GateProgram

def code (width entry n base directoryHeader endHeader inputHeader firstHeader recordHeader : Nat) : Program width 8 :=
  Controller.Horn.ClauseEntry.code width directoryHeader endHeader inputHeader firstHeader (entry + 161) ++
  Controller.Horn.RowScan.rowCode width (entry + 16) n base inputHeader firstHeader (entry + 93) ++
  Controller.Horn.JoinedRuleCopy.code width n (entry + 93) base recordHeader ++
  Controller.Horn.ResetPointer.setupCode width (base + 2 * n + 2) base ++
  Controller.Horn.ResetPointer.code width (entry + 138) (base + 5 * n + 4) ++
  Controller.Horn.ResetReuse.headerCode width n base ++
  #[.branchZero 2 (word width entry)]

@[simp] theorem code_size :
    (code width entry n base directoryHeader endHeader inputHeader firstHeader recordHeader).size = 161 := by
  simp [code, Controller.Horn.ClauseEntry.code, Controller.Horn.JoinedRuleCopy.code,
    Controller.Horn.ResetPointer.setupCode, Controller.Horn.ResetReuse.headerCode]


set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem resident_at (program : Program width 8) (entry : Nat)
    (clauses : List (Controller.CNF.Clause (Fin n)))
    (layout : Controller.Horn.SourceDirectory.Layout clauses)
    (present : SharedRootRead.BlockAt program entry
      (code width entry n layout.base layout.directoryHeader layout.endHeader layout.inputHeader layout.firstHeader layout.recordHeader).toList) :
    Controller.Horn.NormalizeLoop.CodeAt program entry clauses layout := by
  have fetched : ∀ offset, offset < 161 → program[entry + offset]? =
      (code width entry n layout.base layout.directoryHeader layout.endHeader layout.inputHeader layout.firstHeader layout.recordHeader)[offset]? := by
    intro offset bound
    simpa only [Array.getElem?_toList] using present offset (by simp; exact bound)
  constructor
  all_goals repeat' constructor
  all_goals try unfold Controller.Horn.RuleCopy.FinishAt
  all_goals try intro phase
  all_goals try fin_cases phase
  all_goals try simp only [Nat.add_assoc, Nat.reduceAdd]
  all_goals rw [fetched _ (by omega)]
  all_goals simp [code, Array.getElem?_append, Array.getElem?_eq_getElem, Controller.Horn.ClauseEntry.code, Controller.Horn.RowScan.rowCode,
    Controller.Horn.RowScan.testCode, Controller.Horn.RowScan.readMarksCode, Controller.Horn.RowScan.writeMarkCode,
    Controller.Horn.RowScan.dispatchCode, Controller.Horn.LiteralDispatch.rowLayout,
    Controller.Horn.JoinedRuleCopy.code, Controller.Horn.RuleDispatch.code, Controller.Horn.RuleDispatch.skipCode,
    Controller.Horn.RuleCopy.recordAddressCode, Controller.Horn.RuleCopy.headerCode, Controller.Horn.RuleCopy.setupCode,
    Controller.Horn.RuleCopy.bodyCode, Controller.Horn.RuleCopy.finishCode, Controller.Horn.RuleCopy.cursorUpdateCode,
    Controller.Horn.ResetPointer.setupCode, Controller.Horn.ResetPointer.code, Controller.Horn.ResetReuse.headerCode,
    Controller.Horn.SourceScan.pairCode, Nat.add_assoc]

end Controller.Cost.SharedNormalizerCode
