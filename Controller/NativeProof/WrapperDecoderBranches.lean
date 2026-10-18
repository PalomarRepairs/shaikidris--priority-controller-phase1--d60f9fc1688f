module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.WrapperDecoderEvaluation

@[expose] public section

/-! Native disjunction and guard evaluation retain occurrence provenance. -/
namespace Controller.NativeProof.Wrapper
open Controller.CNF Controller.Resolution Controller.Native Controller.Native.SourceController
open Controller.NativeProof.FoldProjection Controller.NativeProof.SourceFoldProjection
open Controller.NativeProof.SourceStageCongruence Controller.NativeProof.SourceStagePolarity
open Controller.NativeProof.SourceStageXor Controller.NativeProof.SourceBusSchedule
open Controller.NativeProof.SourceFoldProvenance Controller.NativeProof.SourceMismatchHandles
open Controller.NativeProof.SourceDecoderEvaluation Controller.NativeProof.SourceDecoderTraversal
open Controller.NativeProof.SourceDecoderClauses Controller.NativeProof.SourceDecoderSchedule
variable {parameters : Parameters} {v : Nat}

theorem nodeStep_dite_origins (rename : Nat → Fin v) (side : Side) (node : Fin parameters.decoder.nodeCount)
    (table : SourceDecoderEvaluation.Table (parameters := parameters) rename side cofactor assignment node.val)
    (condition : Prop) [Decidable condition]
    (yes : condition → NodeStep rename side cofactor assignment node table)
    (no : ¬condition → NodeStep rename side cofactor assignment node table)
    (yesOrigins : ∀ proof, DecoderNodeStepOrigins rename side node table (yes proof))
    (noOrigins : ∀ proof, DecoderNodeStepOrigins rename side node table (no proof)) :
    DecoderNodeStepOrigins rename side node table (dite condition yes no) := by
  by_cases proof : condition
  · rw [dite_eq_left proof]; exact yesOrigins proof
  · rw [dite_eq_right proof]; exact noOrigins proof

theorem available_indices_mpr_resultOrigin (originalCount : Nat) (allowed : Nat → Prop)
    (steps : List (Step v)) {state : State v} {before after : Clause (Fin v)}
    (clauseEqual : before = after)
    (value : AvailableSubclause state after) (origin : ResultOrigin originalCount allowed steps value.row.id) :
    ResultOrigin originalCount allowed steps
      (Eq.mpr (congrArg (fun target => AvailableSubclause state target) clauseEqual) value).row.id := by
  rw [SourceMixedSchedule.subclause_indices_mpr_id rfl clauseEqual]
  exact origin

theorem available_indices_mp_resultOrigin (originalCount : Nat) (allowed : Nat → Prop)
    (steps : List (Step v)) {state : State v} {before after : Clause (Fin v)}
    (clauseEqual : before = after)
    (value : AvailableSubclause state before) (origin : ResultOrigin originalCount allowed steps value.row.id) :
    ResultOrigin originalCount allowed steps
      (Eq.mp (congrArg (fun target => AvailableSubclause state target) clauseEqual) value).row.id := by
  rw [SourceMixedSchedule.subclause_indices_cast_id rfl clauseEqual]
  exact origin

theorem decoderDisjunction_origins (rename : Nat → Fin v) (side : Side) (node : Fin parameters.decoder.nodeCount)
    (table : SourceDecoderEvaluation.Table (parameters := parameters) rename side cofactor assignment node.val)
    (children : List (Fin node.val)) (shape : parameters.decoder.node node = .disj children)
    (origins : DecoderTableOrigins rename side table) :
    DecoderNodeStepOrigins rename side node table
      (SourceDecoderEvaluation.disjunction rename side node table children shape) := by
  unfold SourceDecoderEvaluation.disjunction
  apply nodeStep_dite_origins
  · intro empty
    subst children
    have bit : nodeBit assignment node = false := by
      simp only [nodeBit, parameters.decoder.eval_disj assignment node [] shape, List.any_nil]
    have output : outputLiteral rename side node = mapLiteral rename (decoderLiveAndOutput side node) := by
      simp [outputLiteral, decoderNode, shape, Cursor.foldNative, Cursor.assign,
        decoderLiveAndOutput, SourceSerialFold.allocate]
    dsimp only [id]
    refine ⟨?_, ?_⟩
    · simpa only [SourceDecoderSchedule.PrefixOriginalSupport, SourcePrefix.extend, List.append_nil] using origins.supported
    · change ResultOrigin (formula parameters).clauses.size
        (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) (table.proofPrefix.steps ++ []) _
      rw [List.append_nil]
      apply available_indices_mpr_resultOrigin _ _ table.proofPrefix.steps
        (by simp only [bit, output, valueLiteral, Bool.false_eq_true, ite_false]) _
      exact Or.inl (decoderEmptyDisjunctionUnit_allowed rename side node shape table.proofPrefix)
  · intro empty
    let tree := (decoderDisjunctionTree rename side node children shape empty).afterTrace
      table.proofPrefix.state table.proofPrefix.steps table.proofPrefix.checked
    have output : outputLiteral rename side node = mapLiteral rename (decoderDisjunctionOutput side node children) := by
      simp only [outputLiteral, decoderDisjunction_output side node children shape]
    have bits : nodeBit assignment node = children.any (fun child => nodeBit assignment (parameters.decoder.childIndex node child)) :=
      parameters.decoder.eval_disj assignment node children shape
    have originals := treeOriginals_afterTrace
      (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
      (decoderDisjunctionTree rename side node children shape empty)
      (decoderDisjunctionTree_originals rename side node children shape empty)
      table.proofPrefix.state table.proofPrefix.steps table.proofPrefix.checked
    dsimp only [id]
    apply nodeStep_dite_origins
    · intro active
      have someChild : ∃ child ∈ children, nodeBit assignment (parameters.decoder.childIndex node child) = true := by
        rw [bits] at active
        exact List.any_eq_true.mp active
      let selected := pick children (fun child => nodeBit assignment (parameters.decoder.childIndex node child) = true) someChild
      let leaf := negate (childLiteral rename side node selected.val)
      have member : leaf ∈ (children.map (fun child => (SourceFoldOccurrences.decoderPositionBefore side node).slots
          (.internal (.decoder side (parameters.decoder.childIndex node child))))).map (dualLiteral rename) :=
        List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨selected.val, selected.property.1, rfl⟩, rfl⟩
      let unit : AvailableSubclause table.proofPrefix.state (cofactor ++ [negate leaf]) := by
        simpa only [selected.property.2, valueLiteral, ite_true, leaf, negate_negate] using childUnit rename side node table selected.val
      have unitId : unit.row.id = (childUnit rename side node table selected.val).row.id := by
        dsimp only [unit]
        with_unfolding_all
          apply Eq.trans (SourceMixedSchedule.subclause_indices_mpr_id rfl
            (by simp only [leaf, negate_negate]) _ _)
          apply SourceMixedSchedule.subclause_indices_cast_id rfl
          simp only [selected.property.2, valueLiteral, ite_true]
      have unitOrigin : ResultOrigin (formula parameters).clauses.size
          (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) table.proofPrefix.steps unit.row.id := by
        rw [unitId]
        exact decoderChildUnit_origins rename side node table origins selected.val
      let denied := TreeUnits.deny tree cofactor leaf member unit
      have actual := Wrapper.tree_deny_supported rename table.proofPrefix tree cofactor leaf member unit
        origins.supported originals unitOrigin
      refine ⟨actual.1, ?_⟩
      change ResultOrigin (formula parameters).clauses.size
        (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) (table.proofPrefix.steps ++ denied.steps) _
      apply available_indices_mpr_resultOrigin _ _ (table.proofPrefix.steps ++ denied.steps)
        (by simp only [active, valueLiteral, ite_true, output, dualLiteral, negate_negate, decoderDisjunctionOutput]) _
      apply available_indices_mp_resultOrigin _ _ (table.proofPrefix.steps ++ denied.steps)
        (by simp only [dualLiteral, negate_negate, decoderDisjunctionOutput]) _
      exact actual.2
    · intro active
      have inactive : nodeBit assignment node = false := Bool.eq_false_of_not_eq_true active
      have childrenFalse : ∀ child ∈ children, nodeBit assignment (parameters.decoder.childIndex node child) = false := by
        rw [bits] at inactive
        intro child present
        exact Bool.eq_false_of_not_eq_true (List.any_eq_false.mp inactive child present)
      let rows : ∀ child ∈ children, AvailableSubclause table.proofPrefix.state
          (cofactor ++ [negate (childLiteral rename side node child)]) := fun child present => by
        simpa only [childrenFalse child present, valueLiteral, Bool.false_eq_true, ite_false] using
          childUnit rename side node table child
      let units : ∀ leaf ∈ (children.map (fun child => (SourceFoldOccurrences.decoderPositionBefore side node).slots
          (.internal (.decoder side (parameters.decoder.childIndex node child))))).map (dualLiteral rename),
          AvailableSubclause table.proofPrefix.state (cofactor ++ [leaf]) := by
        intro leaf listed
        have member : leaf ∈ children.map (fun child => negate (childLiteral rename side node child)) := by
          simpa only [List.map_map, childLiteral, dualLiteral, Function.comp_def] using listed
        exact TreeUnits.mappedUnit children _ cofactor rows leaf member
      have rowOrigins : ∀ child present, ResultOrigin (formula parameters).clauses.size
          (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) table.proofPrefix.steps (rows child present).row.id := by
        intro child present
        have indexEqual : (rows child present).row.id = (childUnit rename side node table child).row.id := by
          dsimp only [rows]
          apply SourceMixedSchedule.subclause_cast_id
          simp only [childrenFalse child present, valueLiteral, Bool.false_eq_true, ite_false]
        rw [indexEqual]
        exact decoderChildUnit_origins rename side node table origins child
      have unitOrigins : ∀ leaf listed, ResultOrigin (formula parameters).clauses.size
          (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) table.proofPrefix.steps (units leaf listed).row.id := by
        intro leaf listed
        exact mappedUnit_resultOrigin table.proofPrefix.state children (fun child => negate (childLiteral rename side node child))
          cofactor rows _ _ table.proofPrefix.steps rowOrigins leaf
          (by simpa only [List.map_map, childLiteral, dualLiteral, Function.comp_def] using listed)
      let forced := TreeUnits.force tree cofactor units
      have actual := Wrapper.tree_force_supported rename table.proofPrefix tree cofactor units origins.supported originals unitOrigins
      refine ⟨actual.1, ?_⟩
      change ResultOrigin (formula parameters).clauses.size
        (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) (table.proofPrefix.steps ++ forced.steps) _
      apply available_indices_mpr_resultOrigin _ _ (table.proofPrefix.steps ++ forced.steps)
        (by simp only [inactive, valueLiteral, Bool.false_eq_true, ite_false, output, dualLiteral, decoderDisjunctionOutput]) _
      exact actual.2

end Controller.NativeProof.Wrapper
