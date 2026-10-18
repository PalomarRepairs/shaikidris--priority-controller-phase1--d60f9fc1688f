module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Extensions.ResolvedResident
public import Controller.Cost.SharedNormalizationShape

@[expose] public section

/-! Selecting a child at a live AND preserves normalization record sizes.
The selected child is strictly earlier than its parent, so its two-literal
implication cannot become a tautology. Root units have no positive entries. -/
namespace Controller.Extensions.ResolvedNativeProfile
open Controller Controller.Decoder Controller.Decoder.DAG Controller.CNF
open Controller.Extensions.BoundedAnd Controller.Cost

theorem implication_positives [DecidableEq α] (child parent : α) (different : child ≠ parent) :
    (Horn.Worklist.compileClause [(child,false),(parent,true)]).positives.length = 1 := by
  simp [Horn.Worklist.compileClause,Horn.Worklist.tautologyCheck,Horn.Worklist.signedLabels,
    Horn.Worklist.Rule.positives,negate,Std.Sat.Literal.negate,different,Ne.symm different]

def rawProfile [DecidableEq α] (clauses : List (Clause α)) : List Nat :=
  clauses.map (fun clause => (Horn.Worklist.compileClause clause).positives.length)

theorem node_profile (graph : DAG n) (left right : Finset (Fin graph.nodeCount)) (index : Fin graph.nodeCount) :
    rawProfile ((resolved graph left).nodeClauses index) = rawProfile ((resolved graph right).nodeClauses index) := by
  cases gate : graph.node index with
  | zero => simp [DAG.nodeClauses,resolved,gate,Gate.resolve]
  | input channel => simp [DAG.nodeClauses,resolved,gate,Gate.resolve]
  | disj children => simp [DAG.nodeClauses,resolved,gate,Gate.resolve,DAG.childIndex]
  | guard child labels => simp [DAG.nodeClauses,resolved,gate,Gate.resolve,DAG.childIndex]
  | liveAnd first second =>
    have different (child : Fin index.val) : (Sum.inr (graph.childIndex index child) : graph.ZeroVar) ≠ Sum.inr index := by
      intro equal
      have val := congrArg Fin.val (Sum.inr.inj equal)
      change child.val = index.val at val
      have below := child.isLt
      omega
    have firstProfile := implication_positives _ _ (different first)
    have secondProfile := implication_positives _ _ (different second)
    simp only [DAG.childIndex] at firstProfile secondProfile
    by_cases l : index ∈ left <;> by_cases r : index ∈ right <;>
      simp [DAG.nodeClauses,resolved,gate,Gate.resolve,l,r,rawProfile,
        ZeroSystem.implicationClause,ZeroSystem.positiveClause,DAG.childIndex,firstProfile,secondProfile]

private theorem relabel_profile [DecidableEq α] [DecidableEq β] (f : α → β)
    (injective : Function.Injective f) (clauses : List (Clause α)) :
    rawProfile (clauses.map (fun clause => clause.map (fun literal => (f literal.1,literal.2)))) = rawProfile clauses := by
  simp only [rawProfile,List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro clause member
  exact SharedNormalizationShape.positives_length_map f injective clause

theorem rows_profile (graph : DAG n) (left right : Finset (Fin graph.nodeCount)) (b : Nat)
    (target : Channel n) (first second : Fin graph.nodeCount) :
    SharedNormalizationShape.profile (ResolvedResident.rows graph left b target first) =
      SharedNormalizationShape.profile (ResolvedResident.rows graph right b target second) := by
  have forwards : rawProfile (resolved graph left).forwardClauses = rawProfile (resolved graph right).forwardClauses := by
    simp only [rawProfile,DAG.forwardClauses,List.map_flatMap]
    congr 1
    funext index
    exact node_profile graph left right index
  have roots : rawProfile ([(ZeroSystem.implicationClause (Sum.inr first : graph.ZeroVar) [])]) =
      rawProfile ([(ZeroSystem.implicationClause (Sum.inr second : graph.ZeroVar) [])]) := by
    simp [rawProfile,ZeroSystem.implicationClause,ZeroSystem.positiveClause,Horn.Worklist.compileClause,
      Horn.Worklist.tautologyCheck,Horn.Worklist.signedLabels,Horn.Worklist.Rule.positives,
      negate,Std.Sat.Literal.negate]
  have raw : rawProfile ((resolved graph left).zeroSystem b target first ∅ ∅).clauses.toList =
      rawProfile ((resolved graph right).zeroSystem b target second ∅ ∅).clauses.toList := by
    simp only [DAG.zeroSystem,ofClauses,List.toList_toArray,rawProfile,List.map_append] at *
    rw [forwards,roots]
    rfl
  have mappedLeft := relabel_profile (resolved graph left).zeroIndex (resolved graph left).zeroIndex.injective
    ((resolved graph left).zeroSystem b target first ∅ ∅).clauses.toList
  have mappedRight := relabel_profile (resolved graph right).zeroIndex (resolved graph right).zeroIndex.injective
    ((resolved graph right).zeroSystem b target second ∅ ∅).clauses.toList
  change rawProfile (ResolvedResident.rows graph left b target first) = rawProfile (ResolvedResident.rows graph right b target second)
  simp only [ResolvedResident.rows,SharedZeroTemplate.formula,ofClauses,List.toList_toArray,rawProfile,List.map_append]
  congr 1
  change rawProfile ((relabel (resolved graph left).zeroIndex
      ((resolved graph left).zeroSystem b target first ∅ ∅)).clauses.toList) =
    rawProfile ((relabel (resolved graph right).zeroIndex
      ((resolved graph right).zeroSystem b target second ∅ ∅)).clauses.toList)
  have clauseRelabel (f : graph.ZeroVar → Fin (n+graph.nodeCount)) :
      Controller.CNF.OrderedFormula.Clause.relabel f = fun clause => clause.map (fun literal => (f literal.1,literal.2)) := by
    funext clause
    rfl
  simpa only [relabel,Controller.CNF.OrderedFormula.relabel,Array.toList_map,clauseRelabel] using
    mappedLeft.trans (raw.trans mappedRight.symm)

theorem native_base_uniform (graph : DAG n) (left right : Finset (Fin graph.nodeCount)) (b : Nat)
    (target : Channel n) (first second : Fin graph.nodeCount) (leftHeap rightHeap : Array (Word width))
    (leftLayout : ForestZeroDictionary.Layout (n+graph.nodeCount) leftHeap.size)
    (rightLayout : ForestZeroDictionary.Layout (n+graph.nodeCount) rightHeap.size)
    (sameSize : leftHeap.size = rightHeap.size) :
    SharedZeroNativeQuery.nativeBase leftHeap leftLayout (ResolvedResident.refs 2 (ResolvedResident.rows graph left b target first)) n (by omega) =
      SharedZeroNativeQuery.nativeBase rightHeap rightLayout (ResolvedResident.refs 2 (ResolvedResident.rows graph right b target second)) n (by omega) := by
  let leftRows := ForestZeroAdmissibleCaller.constructorClauses leftHeap leftLayout
    (ForestZeroCompile.empty _) (ForestZeroCompile.empty_coherent _)
    (ResolvedResident.refs 2 (ResolvedResident.rows graph left b target first)) n (by omega)
  let rightRows := ForestZeroAdmissibleCaller.constructorClauses rightHeap rightLayout
    (ForestZeroCompile.empty _) (ForestZeroCompile.empty_coherent _)
    (ResolvedResident.refs 2 (ResolvedResident.rows graph right b target second)) n (by omega)
  have profile : SharedNormalizationShape.profile leftRows = SharedNormalizationShape.profile rightRows := by
    simp only [leftRows,rightRows,SharedNormalizationShape.constructor_profile,ResolvedResident.original_rows,
      ResolvedResident.dictionary_fixed,rows_profile graph left right b target first second]
  have heaps : (ForestZeroAdmissibleCaller.constructorHeap leftHeap leftLayout (ForestZeroCompile.empty _)
      (ResolvedResident.refs 2 (ResolvedResident.rows graph left b target first)) n).size =
      (ForestZeroAdmissibleCaller.constructorHeap rightHeap rightLayout (ForestZeroCompile.empty _)
      (ResolvedResident.refs 2 (ResolvedResident.rows graph right b target second)) n).size := by
    rw [ResolvedResident.constructor_size,ResolvedResident.constructor_size,sameSize,
      ResolvedResident.scratch_congr _ _ (ResolvedResident.rows_signs graph left right b target first second)]
  unfold SharedZeroNativeQuery.nativeBase
  simp only [ForestZeroAdmissibleCaller.constructorFormula_rows,ResolvedResident.dictionary_size,heaps]
  exact SharedNormalizationShape.native_base leftRows rightRows _ profile

theorem native_base_bound (graph : DAG n) (right : Finset (Fin graph.nodeCount)) (b : Nat)
    (target : Channel n) (root : Fin graph.nodeCount) (heap : Array (Word width))
    (layout : ForestZeroDictionary.Layout (n+graph.nodeCount) heap.size) :
    SharedZeroNativeQuery.nativeBase heap layout (ResolvedResident.refs 2 (ResolvedResident.rows graph right b target root)) n (by omega) ≤
      heap.size+100*(graph.countedSize+1) := by
  let refs := ResolvedResident.refs 2 (ResolvedResident.rows graph right b target root)
  let dictionary := ForestZeroAdmissibleCaller.constructorDictionary heap layout (ForestZeroCompile.empty _) refs
  let clauses := ForestZeroAdmissibleCaller.constructorClauses heap layout (ForestZeroCompile.empty _)
    (ForestZeroCompile.empty_coherent _) refs n (by omega)
  let start := (ForestZeroAdmissibleCaller.constructorHeap heap layout (ForestZeroCompile.empty _) refs n).size+
    5*dictionary.coordinates.size+4
  have count := ResolvedResident.rows_bound graph right b target root
  have size := graph.countedSize_eq
  have dictionarySize : dictionary.coordinates.size = n+graph.nodeCount :=
    ResolvedResident.dictionary_size graph right b target root heap layout
  have clauseCount := ForestZeroAdmissibleCaller.constructorClauses_length heap layout (ForestZeroCompile.empty _)
    (ForestZeroCompile.empty_coherent _) refs n (by omega)
  have clauseBound : clauses.length ≤ refs.length+1 := by
    change clauses.length = _ at clauseCount
    split_ifs at clauseCount <;> omega
  have literalBound := ForestZeroAdmissibleCaller.constructorClauses_profile_bound heap layout (ForestZeroCompile.empty _)
    (ForestZeroCompile.empty_coherent _) refs n (by omega)
  change (clauses.map List.length).sum ≤ refs.flatten.length+dictionary.coordinates.size at literalBound
  have heapBound := ResolvedResident.scratch_bound (keep := heap.size) (channels := n)
    (ResolvedResident.rows graph right b target root)
  rw [← ResolvedResident.constructor_size graph right b target root heap layout] at heapBound
  have records := ForestZeroAdmissibleCaller.source_record_end_bound clauses start
  have incidences := Horn.IndexScanCold.occurrences_length_le clauses start
  simp only [refs,ResolvedResident.refs_length,ResolvedResident.refs_literals] at clauseBound literalBound
  change Horn.NormalizeLoop.recordOffset clauses start clauses.length+
    2*(Horn.IndexScan.occurrences clauses start).length ≤ _
  change _ ≤ heap.size+7+2*(ResolvedResident.rows graph right b target root).length+
    2*(ResolvedResident.rows graph right b target root).flatten.length+2*n at heapBound
  dsimp only [refs,start] at heapBound records incidences ⊢
  omega

end Controller.Extensions.ResolvedNativeProfile
