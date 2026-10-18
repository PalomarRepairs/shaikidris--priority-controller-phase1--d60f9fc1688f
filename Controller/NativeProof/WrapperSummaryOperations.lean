module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.WrapperHornRowOrigins

@[expose] public section

/-! Support-summary operations preserve the origins of stronger native clauses. -/
namespace Controller.NativeProof.Wrapper
open Controller.CNF Controller.Resolution
open Controller.NativeProof.FoldProjection Controller.NativeProof.SourceStageCongruence
open Controller.NativeProof.SourceBusSchedule Controller.NativeProof.SourceFoldProvenance
open Controller.NativeProof.SourceMismatchHandles Controller.NativeProof.SupportRows
variable {v n : Nat}

def SummaryResultOrigin (originalCount : Nat) (allowed : Nat → Prop) (prior : List (Step v))
    {state : State v} {cofactor : Clause (Fin v)} {output : Literal (Fin v)} {headList : Clause (Fin v)}
    (summary : SupportRows.Summary state cofactor output headList) : Prop :=
  match (generalizing := false) summary with
  | .identity _ => True
  | .derived row => ResultOrigin originalCount allowed prior row.row.id

theorem SummaryResultOrigin.afterTrace (originalCount : Nat) (allowed : Nat → Prop) (prior : List (Step v))
    {state : State v} {cofactor : Clause (Fin v)} {output : Literal (Fin v)} {headList : Clause (Fin v)}
    (summary : SupportRows.Summary state cofactor output headList)
    (origin : SummaryResultOrigin originalCount allowed prior summary)
    (next : State v) (steps : List (Step v)) (checked : runSteps state steps = some next) :
    SummaryResultOrigin originalCount allowed (prior ++ steps) (summary.afterTrace next steps checked) := by
  cases summary with
  | identity same => trivial
  | derived row => exact resultOrigin_append_right _ _ prior steps _ origin

theorem summaryExpand_supported (state : State v) (cofactor target : Clause (Fin v)) (output : Literal (Fin v))
    (headList : Clause (Fin v)) (summary : SupportRows.Summary state cofactor output headList)
    (parent : AvailableSubclause state (output :: target))
    (contextIncluded : ClauseSubset cofactor target) (headsIncluded : ClauseSubset headList target)
    (originalCount : Nat) (allowed : Nat → Prop) (prior : List (Step v))
    (supported : TraceOriginalSupport originalCount allowed prior)
    (originalBound : ∀ row, allowed row → row ≤ originalCount) (bound : originalCount ≤ state.lastId)
    (summaryOrigin : SummaryResultOrigin originalCount allowed prior summary)
    (parentOrigin : ResultOrigin originalCount allowed prior parent.row.id) :
    let actual := SupportRows.expand state cofactor target output headList summary parent contextIncluded headsIncluded
    TraceOriginalSupport originalCount allowed (prior ++ actual.steps) ∧
      ResultOrigin originalCount allowed (prior ++ actual.steps) actual.result.row.id := by
  cases summary with
  | identity same =>
    simpa only [SupportRows.expand, retarget, List.append_nil] using And.intro supported parentOrigin
  | derived row =>
    let negative : AvailableSubclause state (negate output :: target) := retarget row (by
      intro literal member
      rcases List.mem_append.mp member with old | other
      · exact List.mem_cons_of_mem _ (contextIncluded literal old)
      · rcases List.mem_cons.mp other with pivot | head
        · exact List.mem_cons.mpr (Or.inl pivot)
        · exact List.mem_cons_of_mem _ (headsIncluded literal head))
    have actual := SourceMixedSchedule.longMerge_supported originalCount allowed prior state output target target negative parent
      supported originalBound bound summaryOrigin parentOrigin
    simpa only [SupportRows.expand, retarget, negative] using actual

theorem summaryKill_supported (state : State v) (cofactor : Clause (Fin v)) (output head : Literal (Fin v))
    (blocked : AvailableSubclause state [negate output, negate head])
    (unit : AvailableSubclause state (cofactor ++ [head]))
    (originalCount : Nat) (allowed : Nat → Prop) (prior : List (Step v))
    (supported : TraceOriginalSupport originalCount allowed prior)
    (originalBound : ∀ row, allowed row → row ≤ originalCount) (bound : originalCount ≤ state.lastId)
    (blockedOrigin : ResultOrigin originalCount allowed prior blocked.row.id)
    (unitOrigin : ResultOrigin originalCount allowed prior unit.row.id) :
    let actual := SupportRows.kill state cofactor output head blocked unit
    TraceOriginalSupport originalCount allowed (prior ++ actual.steps) ∧
      ResultOrigin originalCount allowed (prior ++ actual.steps) actual.result.row.id := by
  unfold SupportRows.kill
  dsimp only [id]
  apply SourceMixedSchedule.longMerge_supported
  · exact supported
  · exact originalBound
  · exact bound
  · exact blockedOrigin
  · exact unitOrigin

theorem summaryErase_supported (state : State v) (cofactor : Clause (Fin v)) (output : Literal (Fin v))
    (support : Finset (Fin n)) (handle : Fin n → Literal (Fin v)) (channel : Fin n)
    (parent : AvailableSubclause state (cofactor ++ negate output :: heads support handle))
    (blocked : AvailableSubclause state [negate output, negate (handle channel)])
    (originalCount : Nat) (allowed : Nat → Prop) (prior : List (Step v))
    (supported : TraceOriginalSupport originalCount allowed prior)
    (originalBound : ∀ row, allowed row → row ≤ originalCount) (bound : originalCount ≤ state.lastId)
    (parentOrigin : ResultOrigin originalCount allowed prior parent.row.id)
    (blockedOrigin : ResultOrigin originalCount allowed prior blocked.row.id) :
    let actual := SupportRows.erase state cofactor output support handle channel parent blocked
    TraceOriginalSupport originalCount allowed (prior ++ actual.steps) ∧
      ResultOrigin originalCount allowed (prior ++ actual.steps) actual.result.row.id := by
  unfold SupportRows.erase
  dsimp only [id]
  apply SourceMixedSchedule.longMerge_supported
  · exact supported
  · exact originalBound
  · exact bound
  · exact blockedOrigin
  · exact parentOrigin

end Controller.NativeProof.Wrapper
