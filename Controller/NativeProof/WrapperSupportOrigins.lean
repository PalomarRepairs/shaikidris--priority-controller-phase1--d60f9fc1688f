module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.WrapperSummaryLoops
public import Controller.NativeProof.WrapperHealthyOneQuery

@[expose] public section

/-! Stored support summaries retain preparation and native row origins. -/
namespace Controller.NativeProof.Wrapper
open Controller.CNF Controller.Resolution Controller.Native Controller.Native.SourceController
open Controller.NativeProof.FoldProjection Controller.NativeProof.SourceFoldProjection
open Controller.NativeProof.SourceStageCongruence Controller.NativeProof.SourceStagePolarity
open Controller.NativeProof.SourceStageXor Controller.NativeProof.SourceBusSchedule
open Controller.NativeProof.SourceFoldProvenance Controller.NativeProof.SourceMismatchHandles
open Controller.NativeProof.SourceDecoderEvaluation Controller.NativeProof.SourceDecoderTraversal
open Controller.NativeProof.SourceDecoderSchedule Controller.NativeProof.SourceHealthyOne Controller.NativeProof.SupportRows
variable {parameters : Parameters} {v : Nat}

structure SupportTableOrigins (rename : Nat → Fin v)
    (table : SourceSupportSummaries.Table (parameters := parameters) rename count) : Prop where
  prepared : PreparationOrigins rename table.prepared
  entries : ∀ node before, SummaryResultOrigin (SourceController.formula parameters).clauses.size
    (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) table.prepared.proofPrefix.steps
    (table.entries node before).summary

structure SupportNodeStepOrigins (rename : Nat → Fin v) (node : Fin parameters.decoder.nodeCount)
    (start : SourceSupportSummaries.Table (parameters := parameters) rename node.val)
    (added : SourceSupportSummaries.NodeStep rename node start) : Prop where
  supported : SourceDecoderSchedule.PrefixOriginalSupport rename
    (start.prepared.proofPrefix.extend added.state added.steps added.checked)
  summary : SummaryResultOrigin (SourceController.formula parameters).clauses.size
    (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
    (start.prepared.proofPrefix.steps ++ added.steps) added.entry.summary

theorem SupportTableOrigins.afterTrace (rename : Nat → Fin v)
    (table : SourceSupportSummaries.Table (parameters := parameters) rename count) (origins : SupportTableOrigins rename table)
    (next : State v) (steps : List (Step v)) (checked : runSteps table.prepared.proofPrefix.state steps = some next)
    (supported : SourceDecoderSchedule.PrefixOriginalSupport rename (table.prepared.proofPrefix.extend next steps checked)) :
    SupportTableOrigins rename (table.afterTrace next steps checked) := by
  refine ⟨PreparationOrigins.afterTrace rename table.prepared origins.prepared next steps checked supported, ?_⟩
  intro node before
  exact SummaryResultOrigin.afterTrace _ _ table.prepared.proofPrefix.steps (table.entries node before).summary
    (origins.entries node before) next steps checked

theorem supportZero_origins (rename : Nat → Fin v) (node : Fin parameters.decoder.nodeCount)
    (table : SourceSupportSummaries.Table (parameters := parameters) rename node.val)
    (shape : parameters.decoder.node node = .zero) (origins : SupportTableOrigins rename table) :
    SupportNodeStepOrigins rename node table (SourceSupportSummaries.zero rename node table shape) := by
  have same : SourceSupportSummaries.output rename node = mapLiteral rename (decoderLiveAndOutput .faulty node) := by
    simp only [SourceSupportSummaries.output, outputLiteral, decoderZero_output .faulty node _ shape]
    rfl
  unfold SourceSupportSummaries.zero
  dsimp only [id]
  refine ⟨?_, ?_⟩
  · simpa only [SourceDecoderSchedule.PrefixOriginalSupport, SourcePrefix.extend, List.append_nil] using origins.prepared.supported
  · unfold SummaryResultOrigin
    dsimp only [id]
    rw [List.append_nil]
    apply available_indices_mpr_resultOrigin _ _ table.prepared.proofPrefix.steps
      (by simp only [heads_empty, same]) _
    exact Or.inl (decoderZeroUnit_allowed rename .faulty node shape table.prepared.proofPrefix)

theorem supportInput_origins (rename : Nat → Fin v) (node : Fin parameters.decoder.nodeCount)
    (table : SourceSupportSummaries.Table (parameters := parameters) rename node.val)
    (channel : Fin parameters.channels) (shape : parameters.decoder.node node = .input channel)
    (origins : SupportTableOrigins rename table) :
    SupportNodeStepOrigins rename node table (SourceSupportSummaries.input rename node table channel shape) := by
  unfold SourceSupportSummaries.input
  dsimp only [id]
  refine ⟨?_, ?_⟩
  · simpa only [SourceDecoderSchedule.PrefixOriginalSupport, SourcePrefix.extend, List.append_nil] using origins.prepared.supported
  · trivial

theorem summary_indices_mpr_origin (originalCount : Nat) (allowed : Nat → Prop) (prior : List (Step v))
    {state : State v} {cofactor : Clause (Fin v)} {beforeOutput afterOutput : Literal (Fin v)}
    {beforeHeads afterHeads : Clause (Fin v)} (outputEqual : beforeOutput = afterOutput) (headsEqual : beforeHeads = afterHeads)
    (value : SupportRows.Summary state cofactor afterOutput afterHeads)
    (origin : SummaryResultOrigin originalCount allowed prior value) :
    SummaryResultOrigin originalCount allowed prior
      (Eq.mpr (congrArg₂ (SupportRows.Summary state cofactor) outputEqual headsEqual) value) := by
  subst afterOutput
  subst afterHeads
  exact origin

end Controller.NativeProof.Wrapper
