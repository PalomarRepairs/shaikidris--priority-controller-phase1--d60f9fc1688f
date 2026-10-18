module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Horn.NormalizeLoop
public import Mathlib.Tactic.FinCases

@[expose] public section

/-! Fetched boundaries for the shared normalizer in a physically stored storedPrefix.
The constants inside the code use its actual placement; source occurrences
remain heap data and do not create additional program blocks. -/
namespace Controller.Horn.NormalizeCode
open Controller.Cost

def KernelAt (program : Program width 8) (entry n base recordHeader inputHeader firstHeader directoryHeader endHeader : Nat) : Prop :=
  ∀ phase : Fin 161, program[entry + phase.val]? =
    (Controller.Horn.NormalizeCNF.code width entry n base recordHeader inputHeader
      firstHeader directoryHeader endHeader)[phase.val]?

/-- Optional fetches are exactly the original complete161-position contract. -/
theorem kernelAt_exact (program : Program width 8) (entry n base recordHeader inputHeader firstHeader directoryHeader endHeader : Nat) :
    KernelAt program entry n base recordHeader inputHeader firstHeader directoryHeader endHeader ↔
      ∀ phase : Fin 161, program[entry + phase.val]? =
        some ((Controller.Horn.NormalizeCNF.code width entry n base recordHeader inputHeader firstHeader directoryHeader endHeader)[phase.val]'(by
          rw [Controller.Horn.NormalizeCNF.code_size]; exact phase.isLt)) := by
  unfold KernelAt
  apply forall_congr'
  intro phase
  have canonical : (Controller.Horn.NormalizeCNF.code width entry n base recordHeader inputHeader firstHeader directoryHeader endHeader)[phase.val]? =
      some ((Controller.Horn.NormalizeCNF.code width entry n base recordHeader inputHeader firstHeader directoryHeader endHeader)[phase.val]'(by
        rw [Controller.Horn.NormalizeCNF.code_size]; exact phase.isLt)) :=
    Array.getElem?_eq_getElem (by rw [Controller.Horn.NormalizeCNF.code_size]; exact phase.isLt)
  rw [canonical]

/-- The physical array storedPrefix determines the code placement. -/
theorem prefix_kernel (storedPrefix : Program width 8)
    (n base recordHeader inputHeader firstHeader directoryHeader endHeader : Nat) :
    KernelAt (storedPrefix ++ Controller.Horn.NormalizeCNF.code width storedPrefix.size n base recordHeader
      inputHeader firstHeader directoryHeader endHeader)
      storedPrefix.size n base recordHeader inputHeader firstHeader directoryHeader endHeader := by
  intro phase
  rw [Array.getElem?_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left]

private theorem setup_size (width header base : Nat) :
    (Controller.Horn.ResetPointer.setupCode width header base).size = 3 := rfl

private theorem append_fetch_left (first rest : Array α) (index : Nat)
    (bound : index < first.size) : (first ++ rest)[index]? = first[index]? :=
  Array.getElem?_append_left bound

private theorem append_fetch_right (first rest : Array α) (index : Nat)
    (bound : first.size ≤ index) :
    (first ++ rest)[index]? = rest[index - first.size]? :=
  Array.getElem?_append_right bound

private theorem kernel_directory (program : Program width 8) (entry : Nat)
    (clauses : List (Controller.CNF.Clause (Fin n)))
    (layout : Controller.Horn.SourceDirectory.Layout clauses)
    (present : KernelAt program entry n layout.base layout.recordHeader layout.inputHeader
      layout.firstHeader layout.directoryHeader layout.endHeader) :
    Controller.Horn.ClauseEntry.At program entry layout.directoryHeader layout.endHeader layout.inputHeader layout.firstHeader (entry + 161) := by
  intro phase
  have phaseBound := phase.isLt
  have fetched := present ⟨0 + phase.val, by omega⟩
  simp only [Nat.zero_add, Controller.Horn.NormalizeCNF.code] at fetched
  iterate 6 rw [append_fetch_left _ _ _ (by simp only [Array.size_append, Controller.Horn.ClauseEntry.code_size, Controller.Horn.RowScan.rowCode_size, Controller.Horn.JoinedRuleCopy.code_size, setup_size, Controller.Horn.ResetPointer.code_size, Controller.Horn.ResetReuse.headerCode_size, Nat.reduceAdd]; omega)] at fetched
  have bound : phase.val < (Controller.Horn.ClauseEntry.code width layout.directoryHeader layout.endHeader layout.inputHeader layout.firstHeader (entry + 161)).size := by
    rw [Controller.Horn.ClauseEntry.code_size]; exact phaseBound
  simpa only [Array.getElem?_eq_getElem bound] using fetched

private theorem kernel_row (program : Program width 8) (entry : Nat)
    (clauses : List (Controller.CNF.Clause (Fin n)))
    (layout : Controller.Horn.SourceDirectory.Layout clauses)
    (present : KernelAt program entry n layout.base layout.recordHeader layout.inputHeader
      layout.firstHeader layout.directoryHeader layout.endHeader) :
    Controller.Horn.RowScan.RowAt program (entry + 16) n layout.base layout.inputHeader layout.firstHeader (entry + 93) := by
  intro phase
  have phaseBound := phase.isLt
  have fetched := present ⟨16 + phase.val, by omega⟩
  simp only [Controller.Horn.NormalizeCNF.code] at fetched
  iterate 5 rw [append_fetch_left _ _ _ (by simp only [Array.size_append, Controller.Horn.ClauseEntry.code_size, Controller.Horn.RowScan.rowCode_size, Controller.Horn.JoinedRuleCopy.code_size, setup_size, Controller.Horn.ResetPointer.code_size, Controller.Horn.ResetReuse.headerCode_size, Nat.reduceAdd]; omega)] at fetched
  rw [append_fetch_right _ _ _ (by rw [Controller.Horn.ClauseEntry.code_size]; omega)] at fetched
  simp only [Controller.Horn.ClauseEntry.code_size, Nat.add_sub_cancel_left] at fetched
  have bound : phase.val < (Controller.Horn.RowScan.rowCode width (entry + 16) n layout.base layout.inputHeader layout.firstHeader (entry + 93)).size := by
    rw [Controller.Horn.RowScan.rowCode_size]; exact phaseBound
  simpa only [Array.getElem?_eq_getElem bound, Nat.add_assoc] using fetched

/-- All stage consumers are recovered from the same physically fetched block. -/
theorem kernel_components (program : Program width 8) (entry : Nat)
    (clauses : List (Controller.CNF.Clause (Fin n)))
    (layout : Controller.Horn.SourceDirectory.Layout clauses)
    (present : KernelAt program entry n layout.base layout.recordHeader layout.inputHeader
      layout.firstHeader layout.directoryHeader layout.endHeader) :
    Controller.Horn.NormalizeLoop.CodeAt program entry clauses layout := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact kernel_directory program entry clauses layout present
  · exact kernel_row program entry clauses layout present
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    ·
      intro phase
      have fetched := present ⟨93 + phase.val, by have := phase.isLt; omega⟩
      fin_cases phase <;>
        simp only [Controller.Horn.NormalizeCNF.code, Array.getElem?_append, Array.size_append, Array.size_push, Array.size_empty, Array.size_singleton, Controller.Horn.ClauseEntry.code_size, Controller.Horn.RowScan.rowCode_size, Controller.Horn.JoinedRuleCopy.code_size, setup_size, Controller.Horn.ResetPointer.code_size, Controller.Horn.ResetReuse.headerCode_size, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, ↓reduceDIte, ite_true, ite_false] at fetched <;>
        simpa [Controller.Horn.RuleCopy.FinishAt, Controller.Horn.NormalizeCNF.code, Controller.Horn.ClauseEntry.code,
        Controller.Horn.RowScan.rowCode, Controller.Horn.RowScan.testCode,
        Controller.Horn.SourceScan.pairCode, Controller.Horn.RowScan.readMarksCode,
        Controller.Horn.RowScan.dispatchCode, Controller.Horn.RowScan.writeMarkCode,
        Controller.Horn.JoinedRuleCopy.code, Controller.Horn.RuleDispatch.code,
        Controller.Horn.RuleCopy.recordAddressCode, Controller.Horn.RuleCopy.headerCode,
        Controller.Horn.RuleDispatch.skipCode, Controller.Horn.RuleCopy.setupCode,
        Controller.Horn.RuleCopy.bodyCode, Controller.Horn.RuleCopy.finishCode,
        Controller.Horn.RuleCopy.cursorUpdateCode, Controller.Horn.ResetPointer.setupCode,
        Controller.Horn.ResetPointer.code, Controller.Horn.ResetReuse.headerCode, Nat.add_assoc] using fetched
    ·
      intro phase
      have fetched := present ⟨110 + phase.val, by have := phase.isLt; omega⟩
      fin_cases phase <;>
        simp only [Controller.Horn.NormalizeCNF.code, Array.getElem?_append, Array.size_append, Array.size_push, Array.size_empty, Array.size_singleton, Controller.Horn.ClauseEntry.code_size, Controller.Horn.RowScan.rowCode_size, Controller.Horn.JoinedRuleCopy.code_size, setup_size, Controller.Horn.ResetPointer.code_size, Controller.Horn.ResetReuse.headerCode_size, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, ↓reduceDIte, ite_true, ite_false] at fetched <;>
        simpa [Controller.Horn.RuleCopy.FinishAt, Controller.Horn.NormalizeCNF.code, Controller.Horn.ClauseEntry.code,
        Controller.Horn.RowScan.rowCode, Controller.Horn.RowScan.testCode,
        Controller.Horn.SourceScan.pairCode, Controller.Horn.RowScan.readMarksCode,
        Controller.Horn.RowScan.dispatchCode, Controller.Horn.RowScan.writeMarkCode,
        Controller.Horn.JoinedRuleCopy.code, Controller.Horn.RuleDispatch.code,
        Controller.Horn.RuleCopy.recordAddressCode, Controller.Horn.RuleCopy.headerCode,
        Controller.Horn.RuleDispatch.skipCode, Controller.Horn.RuleCopy.setupCode,
        Controller.Horn.RuleCopy.bodyCode, Controller.Horn.RuleCopy.finishCode,
        Controller.Horn.RuleCopy.cursorUpdateCode, Controller.Horn.ResetPointer.setupCode,
        Controller.Horn.ResetPointer.code, Controller.Horn.ResetReuse.headerCode, Nat.add_assoc] using fetched
    ·
      intro phase
      have fetched := present ⟨114 + phase.val, by have := phase.isLt; omega⟩
      fin_cases phase <;>
        simp only [Controller.Horn.NormalizeCNF.code, Array.getElem?_append, Array.size_append, Array.size_push, Array.size_empty, Array.size_singleton, Controller.Horn.ClauseEntry.code_size, Controller.Horn.RowScan.rowCode_size, Controller.Horn.JoinedRuleCopy.code_size, setup_size, Controller.Horn.ResetPointer.code_size, Controller.Horn.ResetReuse.headerCode_size, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, ↓reduceDIte, ite_true, ite_false] at fetched <;>
        simpa [Controller.Horn.RuleCopy.FinishAt, Controller.Horn.NormalizeCNF.code, Controller.Horn.ClauseEntry.code,
        Controller.Horn.RowScan.rowCode, Controller.Horn.RowScan.testCode,
        Controller.Horn.SourceScan.pairCode, Controller.Horn.RowScan.readMarksCode,
        Controller.Horn.RowScan.dispatchCode, Controller.Horn.RowScan.writeMarkCode,
        Controller.Horn.JoinedRuleCopy.code, Controller.Horn.RuleDispatch.code,
        Controller.Horn.RuleCopy.recordAddressCode, Controller.Horn.RuleCopy.headerCode,
        Controller.Horn.RuleDispatch.skipCode, Controller.Horn.RuleCopy.setupCode,
        Controller.Horn.RuleCopy.bodyCode, Controller.Horn.RuleCopy.finishCode,
        Controller.Horn.RuleCopy.cursorUpdateCode, Controller.Horn.ResetPointer.setupCode,
        Controller.Horn.ResetPointer.code, Controller.Horn.ResetReuse.headerCode, Nat.add_assoc] using fetched
    · constructor
      · have fetched := present ⟨117, by decide⟩
        simp only [Controller.Horn.NormalizeCNF.code, Array.getElem?_append, Array.size_append, Array.size_push, Array.size_empty, Array.size_singleton, Controller.Horn.ClauseEntry.code_size, Controller.Horn.RowScan.rowCode_size, Controller.Horn.JoinedRuleCopy.code_size, setup_size, Controller.Horn.ResetPointer.code_size, Controller.Horn.ResetReuse.headerCode_size, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, ↓reduceDIte, ite_true, ite_false] at fetched <;>
        simpa [Controller.Horn.RuleCopy.FinishAt, Controller.Horn.NormalizeCNF.code, Controller.Horn.ClauseEntry.code,
      Controller.Horn.RowScan.rowCode, Controller.Horn.RowScan.testCode,
      Controller.Horn.SourceScan.pairCode, Controller.Horn.RowScan.readMarksCode,
      Controller.Horn.RowScan.dispatchCode, Controller.Horn.RowScan.writeMarkCode,
      Controller.Horn.JoinedRuleCopy.code, Controller.Horn.RuleDispatch.code,
      Controller.Horn.RuleCopy.recordAddressCode, Controller.Horn.RuleCopy.headerCode,
      Controller.Horn.RuleDispatch.skipCode, Controller.Horn.RuleCopy.setupCode,
      Controller.Horn.RuleCopy.bodyCode, Controller.Horn.RuleCopy.finishCode,
      Controller.Horn.RuleCopy.cursorUpdateCode, Controller.Horn.ResetPointer.setupCode,
      Controller.Horn.ResetPointer.code, Controller.Horn.ResetReuse.headerCode, Nat.add_assoc] using fetched
      · have fetched := present ⟨118, by decide⟩
        simp only [Controller.Horn.NormalizeCNF.code, Array.getElem?_append, Array.size_append, Array.size_push, Array.size_empty, Array.size_singleton, Controller.Horn.ClauseEntry.code_size, Controller.Horn.RowScan.rowCode_size, Controller.Horn.JoinedRuleCopy.code_size, setup_size, Controller.Horn.ResetPointer.code_size, Controller.Horn.ResetReuse.headerCode_size, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, ↓reduceDIte, ite_true, ite_false] at fetched <;>
        simpa [Controller.Horn.RuleCopy.FinishAt, Controller.Horn.NormalizeCNF.code, Controller.Horn.ClauseEntry.code,
      Controller.Horn.RowScan.rowCode, Controller.Horn.RowScan.testCode,
      Controller.Horn.SourceScan.pairCode, Controller.Horn.RowScan.readMarksCode,
      Controller.Horn.RowScan.dispatchCode, Controller.Horn.RowScan.writeMarkCode,
      Controller.Horn.JoinedRuleCopy.code, Controller.Horn.RuleDispatch.code,
      Controller.Horn.RuleCopy.recordAddressCode, Controller.Horn.RuleCopy.headerCode,
      Controller.Horn.RuleDispatch.skipCode, Controller.Horn.RuleCopy.setupCode,
      Controller.Horn.RuleCopy.bodyCode, Controller.Horn.RuleCopy.finishCode,
      Controller.Horn.RuleCopy.cursorUpdateCode, Controller.Horn.ResetPointer.setupCode,
      Controller.Horn.ResetPointer.code, Controller.Horn.ResetReuse.headerCode, Nat.add_assoc] using fetched
    ·
      intro phase
      have fetched := present ⟨119 + phase.val, by have := phase.isLt; omega⟩
      fin_cases phase <;>
        simp only [Controller.Horn.NormalizeCNF.code, Array.getElem?_append, Array.size_append, Array.size_push, Array.size_empty, Array.size_singleton, Controller.Horn.ClauseEntry.code_size, Controller.Horn.RowScan.rowCode_size, Controller.Horn.JoinedRuleCopy.code_size, setup_size, Controller.Horn.ResetPointer.code_size, Controller.Horn.ResetReuse.headerCode_size, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, ↓reduceDIte, ite_true, ite_false] at fetched <;>
        simpa [Controller.Horn.RuleCopy.FinishAt, Controller.Horn.NormalizeCNF.code, Controller.Horn.ClauseEntry.code,
        Controller.Horn.RowScan.rowCode, Controller.Horn.RowScan.testCode,
        Controller.Horn.SourceScan.pairCode, Controller.Horn.RowScan.readMarksCode,
        Controller.Horn.RowScan.dispatchCode, Controller.Horn.RowScan.writeMarkCode,
        Controller.Horn.JoinedRuleCopy.code, Controller.Horn.RuleDispatch.code,
        Controller.Horn.RuleCopy.recordAddressCode, Controller.Horn.RuleCopy.headerCode,
        Controller.Horn.RuleDispatch.skipCode, Controller.Horn.RuleCopy.setupCode,
        Controller.Horn.RuleCopy.bodyCode, Controller.Horn.RuleCopy.finishCode,
        Controller.Horn.RuleCopy.cursorUpdateCode, Controller.Horn.ResetPointer.setupCode,
        Controller.Horn.ResetPointer.code, Controller.Horn.ResetReuse.headerCode, Nat.add_assoc] using fetched
    ·
      intro phase
      have fetched := present ⟨122 + phase.val, by have := phase.isLt; omega⟩
      fin_cases phase <;>
        simp only [Controller.Horn.NormalizeCNF.code, Array.getElem?_append, Array.size_append, Array.size_push, Array.size_empty, Array.size_singleton, Controller.Horn.ClauseEntry.code_size, Controller.Horn.RowScan.rowCode_size, Controller.Horn.JoinedRuleCopy.code_size, setup_size, Controller.Horn.ResetPointer.code_size, Controller.Horn.ResetReuse.headerCode_size, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, ↓reduceDIte, ite_true, ite_false] at fetched <;>
        simpa [Controller.Horn.RuleCopy.FinishAt, Controller.Horn.NormalizeCNF.code, Controller.Horn.ClauseEntry.code,
        Controller.Horn.RowScan.rowCode, Controller.Horn.RowScan.testCode,
        Controller.Horn.SourceScan.pairCode, Controller.Horn.RowScan.readMarksCode,
        Controller.Horn.RowScan.dispatchCode, Controller.Horn.RowScan.writeMarkCode,
        Controller.Horn.JoinedRuleCopy.code, Controller.Horn.RuleDispatch.code,
        Controller.Horn.RuleCopy.recordAddressCode, Controller.Horn.RuleCopy.headerCode,
        Controller.Horn.RuleDispatch.skipCode, Controller.Horn.RuleCopy.setupCode,
        Controller.Horn.RuleCopy.bodyCode, Controller.Horn.RuleCopy.finishCode,
        Controller.Horn.RuleCopy.cursorUpdateCode, Controller.Horn.ResetPointer.setupCode,
        Controller.Horn.ResetPointer.code, Controller.Horn.ResetReuse.headerCode, Nat.add_assoc] using fetched
    · have fetched := present ⟨130, by decide⟩
      simp only [Controller.Horn.NormalizeCNF.code, Array.getElem?_append, Array.size_append, Array.size_push, Array.size_empty, Array.size_singleton, Controller.Horn.ClauseEntry.code_size, Controller.Horn.RowScan.rowCode_size, Controller.Horn.JoinedRuleCopy.code_size, setup_size, Controller.Horn.ResetPointer.code_size, Controller.Horn.ResetReuse.headerCode_size, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, ↓reduceDIte, ite_true, ite_false] at fetched <;>
      simpa [Controller.Horn.RuleCopy.FinishAt, Controller.Horn.NormalizeCNF.code, Controller.Horn.ClauseEntry.code,
      Controller.Horn.RowScan.rowCode, Controller.Horn.RowScan.testCode,
      Controller.Horn.SourceScan.pairCode, Controller.Horn.RowScan.readMarksCode,
      Controller.Horn.RowScan.dispatchCode, Controller.Horn.RowScan.writeMarkCode,
      Controller.Horn.JoinedRuleCopy.code, Controller.Horn.RuleDispatch.code,
      Controller.Horn.RuleCopy.recordAddressCode, Controller.Horn.RuleCopy.headerCode,
      Controller.Horn.RuleDispatch.skipCode, Controller.Horn.RuleCopy.setupCode,
      Controller.Horn.RuleCopy.bodyCode, Controller.Horn.RuleCopy.finishCode,
      Controller.Horn.RuleCopy.cursorUpdateCode, Controller.Horn.ResetPointer.setupCode,
      Controller.Horn.ResetPointer.code, Controller.Horn.ResetReuse.headerCode, Nat.add_assoc] using fetched
    ·
      intro phase
      have fetched := present ⟨131 + phase.val, by have := phase.isLt; omega⟩
      fin_cases phase <;>
        simp only [Controller.Horn.NormalizeCNF.code, Array.getElem?_append, Array.size_append, Array.size_push, Array.size_empty, Array.size_singleton, Controller.Horn.ClauseEntry.code_size, Controller.Horn.RowScan.rowCode_size, Controller.Horn.JoinedRuleCopy.code_size, setup_size, Controller.Horn.ResetPointer.code_size, Controller.Horn.ResetReuse.headerCode_size, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, ↓reduceDIte, ite_true, ite_false] at fetched <;>
        simpa [Controller.Horn.RuleCopy.FinishAt, Controller.Horn.NormalizeCNF.code, Controller.Horn.ClauseEntry.code,
        Controller.Horn.RowScan.rowCode, Controller.Horn.RowScan.testCode,
        Controller.Horn.SourceScan.pairCode, Controller.Horn.RowScan.readMarksCode,
        Controller.Horn.RowScan.dispatchCode, Controller.Horn.RowScan.writeMarkCode,
        Controller.Horn.JoinedRuleCopy.code, Controller.Horn.RuleDispatch.code,
        Controller.Horn.RuleCopy.recordAddressCode, Controller.Horn.RuleCopy.headerCode,
        Controller.Horn.RuleDispatch.skipCode, Controller.Horn.RuleCopy.setupCode,
        Controller.Horn.RuleCopy.bodyCode, Controller.Horn.RuleCopy.finishCode,
        Controller.Horn.RuleCopy.cursorUpdateCode, Controller.Horn.ResetPointer.setupCode,
        Controller.Horn.ResetPointer.code, Controller.Horn.ResetReuse.headerCode, Nat.add_assoc] using fetched
  ·
    intro phase
    have fetched := present ⟨135 + phase.val, by have := phase.isLt; omega⟩
    fin_cases phase <;>
      simp only [Controller.Horn.NormalizeCNF.code, Array.getElem?_append, Array.size_append, Array.size_push, Array.size_empty, Array.size_singleton, Controller.Horn.ClauseEntry.code_size, Controller.Horn.RowScan.rowCode_size, Controller.Horn.JoinedRuleCopy.code_size, setup_size, Controller.Horn.ResetPointer.code_size, Controller.Horn.ResetReuse.headerCode_size, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, ↓reduceDIte, ite_true, ite_false] at fetched <;>
      simpa [Controller.Horn.RuleCopy.FinishAt, Controller.Horn.NormalizeCNF.code, Controller.Horn.ClauseEntry.code,
      Controller.Horn.RowScan.rowCode, Controller.Horn.RowScan.testCode,
      Controller.Horn.SourceScan.pairCode, Controller.Horn.RowScan.readMarksCode,
      Controller.Horn.RowScan.dispatchCode, Controller.Horn.RowScan.writeMarkCode,
      Controller.Horn.JoinedRuleCopy.code, Controller.Horn.RuleDispatch.code,
      Controller.Horn.RuleCopy.recordAddressCode, Controller.Horn.RuleCopy.headerCode,
      Controller.Horn.RuleDispatch.skipCode, Controller.Horn.RuleCopy.setupCode,
      Controller.Horn.RuleCopy.bodyCode, Controller.Horn.RuleCopy.finishCode,
      Controller.Horn.RuleCopy.cursorUpdateCode, Controller.Horn.ResetPointer.setupCode,
      Controller.Horn.ResetPointer.code, Controller.Horn.ResetReuse.headerCode, Nat.add_assoc] using fetched
  ·
    intro phase
    have fetched := present ⟨138 + phase.val, by have := phase.isLt; omega⟩
    fin_cases phase <;>
      simp only [Controller.Horn.NormalizeCNF.code, Array.getElem?_append, Array.size_append, Array.size_push, Array.size_empty, Array.size_singleton, Controller.Horn.ClauseEntry.code_size, Controller.Horn.RowScan.rowCode_size, Controller.Horn.JoinedRuleCopy.code_size, setup_size, Controller.Horn.ResetPointer.code_size, Controller.Horn.ResetReuse.headerCode_size, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, ↓reduceDIte, ite_true, ite_false] at fetched <;>
      simpa [Controller.Horn.RuleCopy.FinishAt, Controller.Horn.NormalizeCNF.code, Controller.Horn.ClauseEntry.code,
      Controller.Horn.RowScan.rowCode, Controller.Horn.RowScan.testCode,
      Controller.Horn.SourceScan.pairCode, Controller.Horn.RowScan.readMarksCode,
      Controller.Horn.RowScan.dispatchCode, Controller.Horn.RowScan.writeMarkCode,
      Controller.Horn.JoinedRuleCopy.code, Controller.Horn.RuleDispatch.code,
      Controller.Horn.RuleCopy.recordAddressCode, Controller.Horn.RuleCopy.headerCode,
      Controller.Horn.RuleDispatch.skipCode, Controller.Horn.RuleCopy.setupCode,
      Controller.Horn.RuleCopy.bodyCode, Controller.Horn.RuleCopy.finishCode,
      Controller.Horn.RuleCopy.cursorUpdateCode, Controller.Horn.ResetPointer.setupCode,
      Controller.Horn.ResetPointer.code, Controller.Horn.ResetReuse.headerCode, Nat.add_assoc] using fetched
  ·
    intro phase
    have fetched := present ⟨149 + phase.val, by have := phase.isLt; omega⟩
    fin_cases phase <;>
      simp only [Controller.Horn.NormalizeCNF.code, Array.getElem?_append, Array.size_append, Array.size_push, Array.size_empty, Array.size_singleton, Controller.Horn.ClauseEntry.code_size, Controller.Horn.RowScan.rowCode_size, Controller.Horn.JoinedRuleCopy.code_size, setup_size, Controller.Horn.ResetPointer.code_size, Controller.Horn.ResetReuse.headerCode_size, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, ↓reduceDIte, ite_true, ite_false] at fetched <;>
      simpa [Controller.Horn.RuleCopy.FinishAt, Controller.Horn.NormalizeCNF.code, Controller.Horn.ClauseEntry.code,
      Controller.Horn.RowScan.rowCode, Controller.Horn.RowScan.testCode,
      Controller.Horn.SourceScan.pairCode, Controller.Horn.RowScan.readMarksCode,
      Controller.Horn.RowScan.dispatchCode, Controller.Horn.RowScan.writeMarkCode,
      Controller.Horn.JoinedRuleCopy.code, Controller.Horn.RuleDispatch.code,
      Controller.Horn.RuleCopy.recordAddressCode, Controller.Horn.RuleCopy.headerCode,
      Controller.Horn.RuleDispatch.skipCode, Controller.Horn.RuleCopy.setupCode,
      Controller.Horn.RuleCopy.bodyCode, Controller.Horn.RuleCopy.finishCode,
      Controller.Horn.RuleCopy.cursorUpdateCode, Controller.Horn.ResetPointer.setupCode,
      Controller.Horn.ResetPointer.code, Controller.Horn.ResetReuse.headerCode, Nat.add_assoc] using fetched
  · have fetched := present ⟨160, by decide⟩
    simp only [Controller.Horn.NormalizeCNF.code, Array.getElem?_append, Array.size_append, Array.size_push, Array.size_empty, Array.size_singleton, Controller.Horn.ClauseEntry.code_size, Controller.Horn.RowScan.rowCode_size, Controller.Horn.JoinedRuleCopy.code_size, setup_size, Controller.Horn.ResetPointer.code_size, Controller.Horn.ResetReuse.headerCode_size, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, ↓reduceDIte, ite_true, ite_false] at fetched <;>
    simpa [Controller.Horn.RuleCopy.FinishAt, Controller.Horn.NormalizeCNF.code, Controller.Horn.ClauseEntry.code,
      Controller.Horn.RowScan.rowCode, Controller.Horn.RowScan.testCode,
      Controller.Horn.SourceScan.pairCode, Controller.Horn.RowScan.readMarksCode,
      Controller.Horn.RowScan.dispatchCode, Controller.Horn.RowScan.writeMarkCode,
      Controller.Horn.JoinedRuleCopy.code, Controller.Horn.RuleDispatch.code,
      Controller.Horn.RuleCopy.recordAddressCode, Controller.Horn.RuleCopy.headerCode,
      Controller.Horn.RuleDispatch.skipCode, Controller.Horn.RuleCopy.setupCode,
      Controller.Horn.RuleCopy.bodyCode, Controller.Horn.RuleCopy.finishCode,
      Controller.Horn.RuleCopy.cursorUpdateCode, Controller.Horn.ResetPointer.setupCode,
      Controller.Horn.ResetPointer.code, Controller.Horn.ResetReuse.headerCode, Nat.add_assoc] using fetched

end Controller.Horn.NormalizeCode
