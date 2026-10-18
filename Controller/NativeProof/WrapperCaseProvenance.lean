module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.WrapperControllerOperations

@[expose] public section

/-! Retained controller support for cofactor truth-case propagation. -/
namespace Controller.NativeProof.Wrapper.ControllerOrigins
open Controller.CNF Controller.Resolution Controller.Native Controller.Native.SourceController
open Controller.NativeProof.FoldProjection Controller.NativeProof.SourceStageCongruence
open Controller.NativeProof.SourceStagePolarity Controller.NativeProof.SourceBusSchedule
open Controller.NativeProof.SourceFoldProvenance Controller.NativeProof.SourceMismatchHandles
variable {parameters : Parameters} {v : Nat}

theorem forceFromCases_supported (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (context : Clause (Fin v)) (input output : Literal (Fin v))
    (positive : AvailableSubclause prefixState.state (context ++ [input, output]))
    (negative : GuardedTransfer prefixState.state context input output)
    (supported : SourceMixedSchedule.PrefixOriginalSupport rename prefixState)
    (positiveOrigin : ResultOrigin (formula parameters).clauses.size
      (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      prefixState.steps positive.row.id)
    (negativeOrigin : GuardedTransferOrigin rename prefixState negative) :
    SourceMixedSchedule.ProjectionOriginalSupport rename prefixState
      (TreeUnits.forceFromCases (root := output) prefixState.state context input output positive negative) := by
  cases negative with
  | identity same =>
    simpa only [TreeUnits.forceFromCases, SourceMixedSchedule.ProjectionOriginalSupport,
      List.append_nil, retarget] using ⟨supported, positiveOrigin⟩
  | derived row =>
    let left : AvailableSubclause prefixState.state (input :: (context ++ [output])) := retarget positive (by
      intro literal member
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member ⊢
      rcases member with old | first | last
      · exact Or.inr (Or.inl old)
      · exact Or.inl first
      · exact Or.inr (Or.inr last))
    let right : AvailableSubclause prefixState.state (negate input :: (context ++ [output])) := retarget row (by
      intro literal member
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member ⊢
      rcases member with old | first | last
      · exact Or.inr (Or.inl old)
      · exact Or.inl first
      · exact Or.inr (Or.inr last))
    have actual := SourceMixedSchedule.longMerge_supported (formula parameters).clauses.size
      (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      prefixState.steps prefixState.state input (context ++ [output]) (context ++ [output]) right left
      supported (SourceMixedSchedule.allowed_native_count_le rename)
      (SourceMixedSchedule.prefix_native_count_le rename prefixState) negativeOrigin positiveOrigin
    simpa only [TreeUnits.forceFromCases, SourceMixedSchedule.ProjectionOriginalSupport,
      left, right, retarget] using actual

def XorRowsOrigins (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (rows : SourceStageXor.XorRows prefixState.state a b output) : Prop :=
  ResultOrigin (formula parameters).clauses.size
      (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename) prefixState.steps rows.zeroZero.row.id ∧
  ResultOrigin (formula parameters).clauses.size
      (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename) prefixState.steps rows.oneOne.row.id ∧
  ResultOrigin (formula parameters).clauses.size
      (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename) prefixState.steps rows.zeroOne.row.id ∧
  ResultOrigin (formula parameters).clauses.size
      (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename) prefixState.steps rows.oneZero.row.id

def NotRowsOrigins (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (rows : NotRows prefixState.state input output) : Prop :=
  ResultOrigin (formula parameters).clauses.size
      (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename) prefixState.steps rows.positive.row.id ∧
  ResultOrigin (formula parameters).clauses.size
      (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename) prefixState.steps rows.negative.row.id

theorem transferPremises_origins (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (transfer : GuardedTransfer prefixState.state context input output)
    (origin : GuardedTransferOrigin rename prefixState transfer) :
    ∀ premise ∈ XorUnits.transferPremises transfer, ResultOrigin (formula parameters).clauses.size
      (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      prefixState.steps premise.row.row.id := by
  cases transfer with
  | identity equal => intro premise member; simp [XorUnits.transferPremises] at member
  | derived row =>
    intro premise member
    have same : premise = ⟨[negate input, output], row⟩ := by simpa [XorUnits.transferPremises] using member
    subst premise
    exact origin

theorem pairPremises_origins (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (pair : DirectionPair prefixState.state context input output)
    (origins : DirectionPairOrigin rename prefixState pair) :
    ∀ premise ∈ XorUnits.pairPremises pair, ResultOrigin (formula parameters).clauses.size
      (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      prefixState.steps premise.row.row.id := by
  intro premise member
  rcases List.mem_append.mp member with forward | backward
  · exact transferPremises_origins rename prefixState pair.forward origins.1 premise forward
  · exact transferPremises_origins rename prefixState pair.backward origins.2 premise backward

theorem xorComplementary_supported (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename) (context : Clause (Fin v))
    (a b term output : Literal (Fin v)) (rows : SourceStageXor.XorRows prefixState.state a b output)
    (notRows : NotRows prefixState.state term b) (equal : DirectionPair prefixState.state context a term)
    (supported : SourceMixedSchedule.PrefixOriginalSupport rename prefixState)
    (xorOrigins : XorRowsOrigins rename prefixState rows)
    (notOrigins : NotRowsOrigins rename prefixState notRows)
    (equalOrigins : DirectionPairOrigin rename prefixState equal) :
    SourceMixedSchedule.ProjectionOriginalSupport rename prefixState
      (XorUnits.complementary prefixState.state context a b term output rows notRows equal) := by
  unfold XorUnits.complementary
  apply Wrapper.local_unit_supported
  · exact supported
  · exact SourceMixedSchedule.allowed_native_count_le rename
  · exact SourceMixedSchedule.prefix_native_count_le rename prefixState
  · intro premise member
    rcases List.mem_append.mp member with before | pairs
    · rcases List.mem_append.mp before with gates | negations
      · simp only [XorUnits.xorPremises, List.mem_cons, List.not_mem_nil, or_false] at gates
        rcases gates with rfl | rfl | rfl | rfl
        · exact xorOrigins.1
        · exact xorOrigins.2.1
        · exact xorOrigins.2.2.1
        · exact xorOrigins.2.2.2
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at negations
        rcases negations with rfl | rfl
        · exact notOrigins.1
        · exact notOrigins.2
    · exact pairPremises_origins rename prefixState equal equalOrigins premise pairs

end Controller.NativeProof.Wrapper.ControllerOrigins
