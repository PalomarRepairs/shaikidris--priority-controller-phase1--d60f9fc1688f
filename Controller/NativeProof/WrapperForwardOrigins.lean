module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.WrapperDecoderTable

@[expose] public section

/-! Forward Horn rows retain native occurrences; aliases carry no row parent. -/
namespace Controller.NativeProof.Wrapper
open Controller.CNF Controller.Resolution Controller.Native Controller.Native.SourceController
open Controller.Decoder.ZeroSystem
open Controller.NativeProof.FoldProjection Controller.NativeProof.SourceFoldProjection
open Controller.NativeProof.SourceStageCongruence Controller.NativeProof.SourceStagePolarity
open Controller.NativeProof.SourceStageXor Controller.NativeProof.SourceBusSchedule
open Controller.NativeProof.SourceFoldProvenance Controller.NativeProof.SourceMismatchHandles
open Controller.NativeProof.SourceDecoderEvaluation Controller.NativeProof.SourceDecoderTraversal
open Controller.NativeProof.SourceDecoderClauses Controller.NativeProof.SourceDecoderSchedule
variable {parameters : Parameters} {v : Nat}

def ForwardOriginResultOrigin (originalCount : Nat) (allowed : Nat → Prop) (steps : List (Step v))
    (origin : SourceForwardRows.Origin (parameters := parameters) rename side state cofactor row) : Prop :=
  match (generalizing := false) origin with
  | .native available => ResultOrigin originalCount allowed steps available.row.id
  | .identity _ _ _ _ => True

def ForwardOriginProvenance (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (origin : SourceForwardRows.Origin (parameters := parameters) rename side prefixState.state cofactor row) : Prop :=
  ForwardOriginResultOrigin (formula parameters).clauses.size
    (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) prefixState.steps origin

structure ForwardNodeRowsOrigins (rename : Nat → Fin v) (side : Side) (cofactor : Clause (Fin v))
    (node : Fin parameters.decoder.nodeCount) (start : SourcePrefix (parameters := parameters) rename)
    (added : SourceForwardRows.NodeRows rename side cofactor node start) : Prop where
  supported : SourceDecoderSchedule.PrefixOriginalSupport rename (start.extend added.state added.steps added.checked)
  rows : ∀ row member, ForwardOriginProvenance rename (start.extend added.state added.steps added.checked)
    (added.rows row member)

structure ForwardTableOrigins (rename : Nat → Fin v) (side : Side)
    (table : SourceForwardRows.Table (parameters := parameters) rename side cofactor count) : Prop where
  supported : SourceDecoderSchedule.PrefixOriginalSupport rename table.proofPrefix
  rows : ∀ node before row member, ForwardOriginProvenance rename table.proofPrefix
    (table.rows node before row member)

theorem ForwardOriginProvenance.afterTrace (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (origin : SourceForwardRows.Origin (parameters := parameters) rename side prefixState.state cofactor row)
    (original : ForwardOriginProvenance rename prefixState origin)
    (next : State v) (steps : List (Step v)) (checked : runSteps prefixState.state steps = some next) :
    ForwardOriginProvenance rename (prefixState.extend next steps checked)
      (origin.afterTrace next steps checked) := by
  cases origin with
  | native available => exact resultOrigin_append_right _ _ prefixState.steps steps _ original
  | identity premise conclusion shape same => trivial

theorem ForwardTableOrigins.afterTrace (rename : Nat → Fin v) (side : Side)
    (table : SourceForwardRows.Table (parameters := parameters) rename side cofactor count)
    (origins : ForwardTableOrigins rename side table)
    (next : State v) (steps : List (Step v)) (checked : runSteps table.proofPrefix.state steps = some next)
    (supported : SourceDecoderSchedule.PrefixOriginalSupport rename (table.proofPrefix.extend next steps checked)) :
    ForwardTableOrigins rename side (table.afterTrace next steps checked) := by
  refine ⟨supported, ?_⟩
  intro node before row member
  exact ForwardOriginProvenance.afterTrace rename table.proofPrefix (table.rows node before row member)
    (origins.rows node before row member) next steps checked

theorem forwardZero_origins (rename : Nat → Fin v) (side : Side) (cofactor : Clause (Fin v))
    (node : Fin parameters.decoder.nodeCount) (start : SourcePrefix (parameters := parameters) rename)
    (shape : parameters.decoder.node node = .zero) (supported : SourceDecoderSchedule.PrefixOriginalSupport rename start) :
    ForwardNodeRowsOrigins rename side cofactor node start (SourceForwardRows.zero rename side cofactor node start shape) := by
  unfold SourceForwardRows.zero
  dsimp only [id]
  refine ⟨?_, ?_⟩
  · simpa only [SourceDecoderSchedule.PrefixOriginalSupport, SourcePrefix.extend, List.append_nil] using supported
  · intro row member
    have same : row = implicationClause (.inr node) [] := by
      simpa [Controller.Decoder.DAG.nodeClauses, shape] using member
    subst row
    have output : outputLiteral rename side node = mapLiteral rename (decoderLiveAndOutput side node) := by
      simp only [outputLiteral, decoderZero_output side node _ shape]
      rfl
    unfold ForwardOriginProvenance ForwardOriginResultOrigin
    dsimp only [id]
    change ResultOrigin (formula parameters).clauses.size
      (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) (start.steps ++ []) _
    rw [List.append_nil]
    apply available_indices_mpr_resultOrigin _ _ start.steps
      (by simp only [SourceForwardRows.implication, List.map_nil, SourceForwardRows.handle, Sum.elim_inr, output]) _
    exact Or.inl (decoderZeroUnit_allowed rename side node shape start)

end Controller.NativeProof.Wrapper
