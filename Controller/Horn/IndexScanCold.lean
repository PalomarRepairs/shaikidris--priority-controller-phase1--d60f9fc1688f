module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Horn.IndexScanOuter

@[expose] public section

/-! Original serialized clauses are normalized and indexed by a single appended
program. The initial physical index and fixed header come from executed cold
normalization, with source input and caller storage charged. -/
namespace Controller.Horn.IndexScanCold
open Controller.Cost Controller.Horn.WorklistStorage Controller.Horn.IndexScanOuter
variable {width n : Nat}

theorem append_step (before tail : Program width registers) (state final : State width registers)
    (transition : programStep before state = some final) :
    programStep (before ++ tail) state = some final := by
  have inside : state.pc.val < before.size := by
    by_contra outside
    have missing : before[state.pc.val]? = none := Array.getElem?_eq_none_iff.mpr (by omega)
    simp [programStep, missing] at transition
  simpa only [programStep, Array.getElem?_append_left inside] using transition

theorem append_execution (before tail : Program width registers)
    {state final : State width registers} {ticks peak : Nat}
    (trace : Execution before state final ticks peak) :
    Execution (before ++ tail) state final ticks peak := by
  induction trace with
  | refl => exact Execution.refl _
  | cons transition rest ih => exact Execution.cons (append_step before tail _ _ transition) ih

def entry (width : Nat) (clauses : List (Controller.CNF.Clause (Fin n))) : Nat :=
  (Controller.Horn.NormalizeCold.program width clauses).size

def recordStart (width : Nat) (clauses : List (Controller.CNF.Clause (Fin n))) : Nat :=
  Controller.Horn.NormalizeCold.words (width := width) clauses + 5 * n + 4

def program (width : Nat) (clauses : List (Controller.CNF.Clause (Fin n))) : Program width 8 :=
  Controller.Horn.NormalizeCold.program width clauses ++ IndexScan.code (n := n) width
    (Controller.Horn.SourceSerialize.base clauses) (recordStart width clauses) (entry width clauses)

theorem index_at (clauses : List (Controller.CNF.Clause (Fin n))) :
    IndexScan.At (n := n) (program width clauses) (entry width clauses)
      (Controller.Horn.SourceSerialize.base clauses) (recordStart width clauses) := by
  intro phase
  unfold program entry
  rw [Array.getElem?_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left]

@[simp] theorem program_size (clauses : List (Controller.CNF.Clause (Fin n))) :
    (program width clauses).size = entry width clauses + 32 := by simp [program, entry]

@[simp] theorem program_words (clauses : List (Controller.CNF.Clause (Fin n))) :
    programWords (program width clauses) = 4 * (entry width clauses + 32) := by
  simp [programWords]

theorem positive_count_le (clause : Controller.CNF.Clause (Fin n)) :
    (Controller.Horn.Worklist.compileClause clause).positives.length ≤ clause.length := by
  have labels : (Controller.Horn.Worklist.signedLabels clause true).length ≤ clause.length := by
    have dedup := (List.dedup_sublist
      ((clause.filter fun literal => decide (literal.2 = true)).map Prod.fst)).length_le
    have filtered := List.length_filter_le (fun literal : Controller.CNF.Literal (Fin n) => decide (literal.2 = true)) clause
    simp only [List.length_map] at dedup
    exact dedup.trans filtered
  unfold Controller.Horn.Worklist.compileClause
  split
  · simp [Controller.Horn.Worklist.Rule.positives]
  · cases Controller.Horn.Worklist.signedLabels clause false <;> exact labels

theorem occurrences_length_le (clauses : List (Controller.CNF.Clause (Fin n))) (start : Nat) :
    (IndexScan.occurrences clauses start).length ≤ (clauses.map List.length).sum := by
  induction clauses generalizing start with
  | nil => simp [IndexScan.occurrences]
  | cons clause rest ih =>
      have tail := ih (start + 3 + (Controller.Horn.Worklist.compileClause clause).positives.length)
      have head := positive_count_le clause
      simp only [IndexScan.occurrences, List.length_append, List.length_map,
        List.map_cons, List.sum_cons]
      omega

theorem packed_endpoint (clauses : List (Controller.CNF.Clause (Fin n))) (start : Nat) :
    Controller.Horn.NormalizeLoop.recordOffset clauses start clauses.length = start + 3 * clauses.length +
      (IndexScan.occurrences clauses start).length := by
  induction clauses generalizing start with
  | nil => simp [Controller.Horn.NormalizeLoop.recordOffset, IndexScan.occurrences]
  | cons clause rest ih =>
      have tail := ih (start + 3 + (Controller.Horn.Worklist.compileClause clause).positives.length)
      simp [Controller.Horn.NormalizeLoop.recordOffset, IndexScan.occurrences] at tail ⊢
      omega

/-- The complete cold run consumes the original serialized input. Its index
state is derived from normalization's output, without a supplied incidence table. -/
theorem execution (clauses : List (Controller.CNF.Clause (Fin n)))
    (state : State width 8) (suffix : List (Word width))
    (emptyHeap : state.heap = #[])
    (input : state.stack = (Controller.Horn.SourceSerialize.heap (width := width) clauses).toList ++ suffix)
    (position : state.pc = word width 0) (running : state.halted = false)
    (dual : ∀ index : Fin clauses.length, Controller.Horn.DualHornClause clauses[index.val])
    (codeFits : (program width clauses).size < 2 ^ width)
    (heapFits : recordStart width clauses + 3 * clauses.length + 3 * (clauses.map List.length).sum < 2 ^ width) :
    ∃ final : State width 8, ∃ recordEnd ticks peak : Nat,
      Execution (program width clauses) state final ticks peak ∧
      IndexScan.PhysicalIndex clauses (recordStart width clauses) recordEnd
        (Controller.Horn.SourceSerialize.base clauses)
        (IndexScan.occurrences clauses (recordStart width clauses)).length final.heap ∧
      final.pc = word width (program width clauses).size ∧
      final.stack = suffix ∧ final.output = state.output ∧
      ticks ≤ 25 * n + 83 * (clauses.map List.length).sum + 95 * clauses.length + 66 ∧
      peak ≤ state.liveWords + 5 * n + 4 + 3 * clauses.length + 3 * (clauses.map List.length).sum ∧
      programWords (program width clauses) + peak ≤
        4 * (entry width clauses + 32) + state.liveWords + 5 * n + 4 +
          3 * clauses.length + 3 * (clauses.map List.length).sum := by
  obtain ⟨normalized, marks, normalizeTicks, normalizePeak, normalizeTrace, invariant,
      normalizePosition, normalizeStack, normalizeOutput, normalizeCost, normalizeStorage⟩ :=
    Controller.Horn.NormalizeCold.execution clauses state suffix emptyHeap input position running dual
      (by have := program_size (width := width) clauses; unfold entry at this; omega)
      (by unfold recordStart at heapFits; omega)
  have physical := IndexScan.initial clauses (Controller.Horn.SourceSerialize.layout clauses)
    (recordStart width clauses) marks normalized invariant
  have header : Controller.Horn.SourceScan.CursorStored normalized.heap.size 0 normalized.heap := by
    simpa [Controller.Horn.SourceSerialize.layout] using invariant.recordCursor
  have endpoints := invariant.records.endpoint
  have packed := packed_endpoint clauses (recordStart width clauses)
  have incidences := occurrences_length_le clauses (recordStart width clauses)
  have scanRoom : normalized.heap.size + 2 * (IndexScan.occurrences clauses (recordStart width clauses)).length < 2 ^ width := by
    change normalized.heap.size = Controller.Horn.NormalizeLoop.recordOffset clauses (recordStart width clauses) clauses.length at endpoints
    omega
  obtain ⟨final, scanTrace, result⟩ := all_rows (program width clauses) clauses (recordStart width clauses)
    normalized.heap.size (Controller.Horn.SourceSerialize.base clauses) (entry width clauses) normalized
    (index_at clauses) physical header (Controller.Horn.IndexScanWhole.cold_base_positive clauses)
    normalizePosition invariant.input.running invariant.input.zero invariant.input.one
    (by simpa only [program_size] using codeFits) scanRoom
  let full := (append_execution _ _ normalizeTrace).append scanTrace
  refine ⟨final, normalized.heap.size, normalizeTicks +
    (16 * (IndexScan.occurrences clauses (recordStart width clauses)).length + 18 * clauses.length + 6),
    max normalizePeak (normalized.liveWords + 2 * (IndexScan.occurrences clauses (recordStart width clauses)).length),
    full, result.physical, ?_, result.stack.trans normalizeStack, result.output.trans normalizeOutput, ?_, ?_, ?_⟩
  · simpa only [program_size] using result.position
  · omega
  · have resident := normalizeTrace.final_storage_le
    omega
  · have resident := normalizeTrace.final_storage_le
    rw [program_words]
    omega

end Controller.Horn.IndexScanCold
