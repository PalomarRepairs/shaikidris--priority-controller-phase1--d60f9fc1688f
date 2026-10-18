module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.WrapperSummaryOperations

@[expose] public section

/-! Cached summary elimination and label erasure preserve retained origins. -/
namespace Controller.NativeProof.Wrapper
open Controller.CNF Controller.Resolution
open Controller.NativeProof.FoldProjection Controller.NativeProof.SourceStageCongruence
open Controller.NativeProof.SourceBusSchedule Controller.NativeProof.SourceFoldProvenance
open Controller.NativeProof.SourceMismatchHandles Controller.NativeProof.SupportRows
variable {v n : Nat}

theorem summaryEliminate_supported {α : Type} (state : State v) (cofactor target : Clause (Fin v))
    (items : List α) (label : α → Literal (Fin v)) (supportHeads : α → Clause (Fin v))
    (summaries : ∀ item ∈ items, SupportRows.Summary state cofactor (label item) (supportHeads item))
    (contextIncluded : ClauseSubset cofactor target)
    (headsIncluded : ∀ item ∈ items, ClauseSubset (supportHeads item) target)
    (parent : AvailableSubclause state (items.map label ++ target))
    (originalCount : Nat) (allowed : Nat → Prop) (prior : List (Step v))
    (supported : TraceOriginalSupport originalCount allowed prior)
    (originalBound : ∀ row, allowed row → row ≤ originalCount) (bound : originalCount ≤ state.lastId)
    (summaryOrigins : ∀ item member, SummaryResultOrigin originalCount allowed prior (summaries item member))
    (parentOrigin : ResultOrigin originalCount allowed prior parent.row.id) :
    let actual := SupportRows.eliminate state cofactor target items label supportHeads summaries contextIncluded headsIncluded parent
    TraceOriginalSupport originalCount allowed (prior ++ actual.steps) ∧
      ResultOrigin originalCount allowed (prior ++ actual.steps) actual.result.row.id := by
  induction items generalizing state prior with
  | nil => simpa only [SupportRows.eliminate, List.append_nil] using And.intro supported parentOrigin
  | cons item rest ih =>
    let expanded := SupportRows.expand state cofactor (rest.map label ++ target) (label item) (supportHeads item)
      (summaries item List.mem_cons_self) parent
      (fun literal member => List.mem_append_right _ (contextIncluded literal member))
      (fun literal member => List.mem_append_right _ (headsIncluded item List.mem_cons_self literal member))
    let tailSummaries := fun old (present : old ∈ rest) =>
      (summaries old (List.mem_cons_of_mem _ present)).afterTrace expanded.state expanded.steps expanded.checked
    have one := summaryExpand_supported state cofactor (rest.map label ++ target) (label item) (supportHeads item)
      (summaries item List.mem_cons_self) parent
      (fun literal member => List.mem_append_right _ (contextIncluded literal member))
      (fun literal member => List.mem_append_right _ (headsIncluded item List.mem_cons_self literal member))
      originalCount allowed prior supported originalBound bound (summaryOrigins item List.mem_cons_self) parentOrigin
    have nextOrigins : ∀ old present, SummaryResultOrigin originalCount allowed (prior ++ expanded.steps)
        (tailSummaries old present) := fun old present => SummaryResultOrigin.afterTrace _ _ prior
      (summaries old (List.mem_cons_of_mem _ present)) (summaryOrigins old (List.mem_cons_of_mem _ present))
      expanded.state expanded.steps expanded.checked
    have nextBound : originalCount ≤ expanded.state.lastId := Nat.le_trans bound (runSteps_lastId_le expanded.checked)
    have tail := ih expanded.state tailSummaries (fun old present => headsIncluded old (List.mem_cons_of_mem _ present))
      expanded.result (prior ++ expanded.steps) one.1 nextBound nextOrigins one.2
    simpa only [SupportRows.eliminate, SupportRows.eliminateStep, expanded, tailSummaries, List.append_assoc] using tail

theorem summaryEraseLabels_supported (state : State v) (cofactor : Clause (Fin v)) (output : Literal (Fin v))
    (support : Finset (Fin n)) (handle : Fin n → Literal (Fin v)) (labels : List (Fin n))
    (parent : AvailableSubclause state (cofactor ++ negate output :: heads support handle))
    (blocked : ∀ channel ∈ labels, AvailableSubclause state [negate output, negate (handle channel)])
    (originalCount : Nat) (allowed : Nat → Prop) (prior : List (Step v))
    (supported : TraceOriginalSupport originalCount allowed prior)
    (originalBound : ∀ row, allowed row → row ≤ originalCount) (bound : originalCount ≤ state.lastId)
    (parentOrigin : ResultOrigin originalCount allowed prior parent.row.id)
    (blockedOrigins : ∀ channel member, ResultOrigin originalCount allowed prior (blocked channel member).row.id) :
    let actual := SupportRows.eraseLabels state cofactor output support handle labels parent blocked
    TraceOriginalSupport originalCount allowed (prior ++ actual.steps) ∧
      ResultOrigin originalCount allowed (prior ++ actual.steps) actual.result.row.id := by
  induction labels generalizing state support prior with
  | nil =>
    refine ⟨?_, ?_⟩
    · simpa only [SupportRows.eraseLabels, List.append_nil] using supported
    · unfold SupportRows.eraseLabels
      dsimp only [id]
      rw [List.append_nil]
      apply available_indices_mpr_resultOrigin originalCount allowed prior (by simp) _
      exact parentOrigin
  | cons channel rest ih =>
    let removed := SupportRows.erase state cofactor output support handle channel parent (blocked channel List.mem_cons_self)
    let tailBlocked := fun old (present : old ∈ rest) => FoldProjection.afterTrace
      (blocked old (List.mem_cons_of_mem _ present)) removed.state removed.steps removed.checked
    let tail := SupportRows.eraseLabels removed.state cofactor output (support.erase channel) handle rest removed.result tailBlocked
    have one := summaryErase_supported state cofactor output support handle channel parent (blocked channel List.mem_cons_self)
      originalCount allowed prior supported originalBound bound parentOrigin (blockedOrigins channel List.mem_cons_self)
    have nextOrigins : ∀ old present, ResultOrigin originalCount allowed (prior ++ removed.steps) (tailBlocked old present).row.id :=
      fun old present => resultOrigin_append_right _ _ prior removed.steps _ (blockedOrigins old (List.mem_cons_of_mem _ present))
    have nextBound : originalCount ≤ removed.state.lastId := Nat.le_trans bound (runSteps_lastId_le removed.checked)
    have tailOrigins := ih removed.state (support.erase channel) removed.result tailBlocked (prior ++ removed.steps)
      one.1 nextBound one.2 nextOrigins
    have sets : support.erase channel \ rest.toFinset = support \ (channel :: rest).toFinset := by
      ext head
      simp [Finset.mem_erase, Finset.mem_sdiff, and_assoc, and_left_comm, and_comm]
    have stepsEqual : (SupportRows.eraseLabels state cofactor output support handle (channel :: rest) parent blocked).steps =
        removed.steps ++ tail.steps := rfl
    have indexEqual : (SupportRows.eraseLabels state cofactor output support handle (channel :: rest) parent blocked).result.row.id =
        tail.result.row.id := by
      rw [SupportRows.eraseLabels.eq_def]
      dsimp only [id]
      apply SourceMixedSchedule.subclause_cast_id
      rw [sets]
    dsimp only
    rw [stepsEqual, indexEqual]
    simpa only [List.append_assoc] using tailOrigins

end Controller.NativeProof.Wrapper
