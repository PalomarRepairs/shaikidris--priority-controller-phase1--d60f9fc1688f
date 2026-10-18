module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestWeightedIndexed
public import Controller.Cost.UniformDAGResources
public import Controller.Cost.ForestZeroOutputImage
public import Controller.Physical.DetectCorrect

@[expose] public section

/-! Original root occurrences partitioned by the executed Boolean value table.
Subfamilies share the source nodes and retain original occurrence identities. -/

namespace Controller.Cost.Forest
open Controller.Decoder Controller.Decoder.DAG

@[reducible] def rootFamily (graph : DAG n) (positions : List (Fin graph.roots.length)) : DAG n :=
  ⟨graph.nodeCount, graph.node, positions.map graph.roots.get⟩

theorem rootFamily_guarded (graph : DAG n) (guarded : graph.Guarded)
    (positions : List (Fin graph.roots.length)) : (rootFamily graph positions).Guarded := guarded

private theorem rootFamily_cone (graph : DAG n) (positions : List (Fin graph.roots.length))
    (owner : Fin graph.nodeCount) : (rootFamily graph positions).cone owner = graph.cone owner := by
  have sameCone : ∀ rank : Nat, ∀ index : Fin graph.nodeCount, index.val = rank →
      (rootFamily graph positions).cone index = graph.cone index := by
    intro rank
    induction rank using Nat.strong_induction_on with
    | h rank ih =>
      intro index rankEq
      rw [DAG.cone_eq (rootFamily graph positions) index, DAG.cone_eq graph index]
      apply congrArg (fun set : Finset (Fin graph.nodeCount) => insert index set)
      apply Finset.biUnion_congr (by rfl)
      intro child member
      have earlier : child.val < rank := by rw [← rankEq]; exact child.isLt
      exact ih child.val earlier (graph.childIndex index child) rfl
  exact sameCone owner.val owner rfl

/-- Every selected root cone is contained in the original declared union. -/
theorem rootFamily_cones_subset (graph : DAG n) (positions : List (Fin graph.roots.length)) :
    (rootFamily graph positions).cones (rootFamily graph positions).roots ⊆ graph.cones graph.roots := by
  intro owner present
  obtain ⟨root, member, coneMember⟩ := Finset.mem_biUnion.mp present
  change root ∈ (positions.map graph.roots.get).toFinset at member
  have listMember := List.mem_toFinset.mp member
  obtain ⟨position, positionMember, same⟩ := List.mem_map.mp listMember
  have coneEq := rootFamily_cone graph positions (root : Fin graph.nodeCount)
  have originalMember : owner ∈ graph.cone root := by exact coneEq ▸ coneMember
  subst root
  exact Finset.mem_biUnion.mpr ⟨graph.roots.get position,
    List.mem_toFinset.mpr (List.get_mem _ _), originalMember⟩

/-- Active-use injection preserves internal forestness when occurrence
positions are selected without duplication. Terminal labels may still repeat. -/
def rootFamilyUse (graph : DAG n) (positions : List (Fin graph.roots.length))
    (owner : Fin graph.nodeCount) :
    (rootFamily graph positions).ActiveUses
      ((rootFamily graph positions).cones (rootFamily graph positions).roots) owner →
    graph.ActiveUses (graph.cones graph.roots) owner := by
  intro use
  rcases use with ⟨occurrence, retained, same⟩
  cases occurrence with
  | inl position =>
    let source : Fin positions.length := ⟨position.val, by simpa [rootFamily] using position.isLt⟩
    refine ⟨.inl (positions.get source), trivial, ?_⟩
    simpa only [DAG.refers, rootFamily, List.get_eq_getElem, List.getElem_map] using same
  | inr child =>
    refine ⟨.inr child, rootFamily_cones_subset graph positions retained, ?_⟩
    exact same

theorem rootFamilyUse_injective (graph : DAG n) (positions : List (Fin graph.roots.length))
    (unique : positions.Nodup) (owner : Fin graph.nodeCount) :
    Function.Injective (rootFamilyUse graph positions owner) := by
  intro first second same
  apply Subtype.ext
  have actual := congrArg Subtype.val same
  cases first with
  | mk first validFirst =>
    cases second with
    | mk second validSecond =>
      rcases validFirst with ⟨retainedFirst, refersFirst⟩
      rcases validSecond with ⟨retainedSecond, refersSecond⟩
      cases first <;> cases second <;> simp only [rootFamilyUse] at actual
      · apply congrArg Sum.inl
        apply Fin.ext
        have equality := Sum.inl.inj actual
        have positionsEqual := unique.get_inj_iff.mp equality
        exact congrArg (fun index : Fin positions.length => index.val) positionsEqual
      · cases actual
      · cases actual
      · exact congrArg Sum.inr (Sum.inr.inj actual)

theorem rootFamily_forest (graph : DAG n) (forest : graph.FormulaForest)
    (positions : List (Fin graph.roots.length)) (unique : positions.Nodup) :
    (rootFamily graph positions).FormulaForest := by
  refine ⟨rootFamily_guarded graph forest.1 positions, ?_⟩
  intro owner internal
  exact (Nat.card_le_card_of_injective _ (rootFamilyUse_injective graph positions unique owner)).trans
    (forest.2 owner internal)

end Controller.Cost.Forest
namespace Controller.Cost.Forest
open Controller.Decoder Controller.Decoder.DAG Controller.Cost.GateProgram
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestInputPrefixStored
open Controller.Cost.UniformDAGRun

/-- Root records are built by a forward list scan with an advancing position.
The checked bound is the declared root count. -/
def rootRecordsFrom (bound offset : Nat) : List (Fin nodes) → List (Fin bound × Fin nodes)
  | [] => []
  | root :: rest => if valid : offset < bound then
      (⟨offset, valid⟩, root) :: rootRecordsFrom bound (offset + 1) rest else []

inductive RootRecordTrace (bound : Nat) : Nat → List (Fin nodes) →
    List (Fin bound × Fin nodes) → Nat → Prop
  | nil (offset : Nat) : RootRecordTrace bound offset [] [] 0
  | cons (offset : Nat) (root : Fin nodes) (rest : List (Fin nodes))
      (records : List (Fin bound × Fin nodes)) (steps : Nat) (valid : offset < bound)
      (tail : RootRecordTrace bound (offset + 1) rest records steps) :
      RootRecordTrace bound offset (root :: rest) ((⟨offset, valid⟩, root) :: records) (steps + 1)

theorem rootRecordsFrom_trace (bound offset : Nat) (roots : List (Fin nodes))
    (room : offset + roots.length ≤ bound) :
    RootRecordTrace bound offset roots (rootRecordsFrom bound offset roots) roots.length := by
  induction roots generalizing offset with
  | nil => exact .nil offset
  | cons root rest ih =>
    have valid : offset < bound := by simp only [List.length_cons] at room; omega
    simpa only [rootRecordsFrom, dite_eq_left valid, List.length_cons] using
      RootRecordTrace.cons offset root rest _ _ valid (ih (offset + 1) (by simp only [List.length_cons] at room; omega))

theorem rootRecordsFrom_length (bound offset : Nat) (roots : List (Fin nodes))
    (room : offset + roots.length ≤ bound) :
    (rootRecordsFrom bound offset roots).length = roots.length := by
  induction roots generalizing offset with
  | nil => rfl
  | cons root rest ih =>
    have valid : offset < bound := by simp only [List.length_cons] at room; omega
    simp only [rootRecordsFrom, dite_eq_left valid, List.length_cons]
    rw [ih (offset + 1) (by simp only [List.length_cons] at room; omega)]

private theorem rootRecordsFrom_get (bound offset : Nat) (roots : List (Fin nodes))
    (room : offset + roots.length ≤ bound) (index : Nat) (valid : index < roots.length) :
    (rootRecordsFrom bound offset roots)[index]'(by rw [rootRecordsFrom_length bound offset roots room]; exact valid) =
      (⟨offset + index, by omega⟩, roots[index]'valid) := by
  induction roots generalizing offset index with
  | nil => simp only [List.length_nil] at valid; omega
  | cons root rest ih =>
    have fits : offset < bound := by simp only [List.length_cons] at room; omega
    have tailRoom : offset + 1 + rest.length ≤ bound := by simp only [List.length_cons] at room; omega
    cases index with
    | zero => simp only [rootRecordsFrom, dite_eq_left fits, List.getElem_cons_zero, Nat.add_zero]
    | succ index =>
      simp only [rootRecordsFrom, dite_eq_left fits, List.getElem_cons_succ]
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (offset + 1) tailRoom index (by simp only [List.length_cons] at valid; omega)

/-- The list-index expression occurs only in this semantic correspondence;
the executable producer traverses each source cons once. -/
theorem rootRecords_eq_ofFn (graph : DAG n) :
    rootRecordsFrom graph.roots.length 0 graph.roots =
      List.ofFn (fun position : Fin graph.roots.length => (position, graph.roots.get position)) := by
  apply List.ext_getElem
  · rw [rootRecordsFrom_length _ _ _ (by omega), List.length_ofFn]
  · intro index left right
    have valid : index < graph.roots.length := by simpa only [List.length_ofFn] using right
    rw [rootRecordsFrom_get _ _ _ (by omega) index valid, List.getElem_ofFn]
    simp only [Nat.zero_add, List.get_eq_getElem]

/-- Classification reads one Boolean cell using the current record's stored
root ID, rather than indexing back into the original root list. -/
def storedRootValue (heap : Array (Word width)) (valueBase : Nat) (root : Fin nodes) : Bool :=
  ((heap[valueBase + root.val]?).getD (word width 0)).val != 0

def classifyRecords (heap : Array (Word width)) (valueBase : Nat) (healthy : Bool)
    (records : List (Fin bound × Fin nodes)) : List (Fin bound × Fin nodes) :=
  records.filter (fun record => storedRootValue heap valueBase record.2 == healthy)

inductive RootReadTrace (heap : Array (Word width)) (valueBase : Nat) (healthy : Bool) :
    List (Fin bound × Fin nodes) → List (Fin bound × Fin nodes) → Nat → Prop
  | nil : RootReadTrace heap valueBase healthy [] [] 0
  | read (record : Fin bound × Fin nodes) (rest selected : List (Fin bound × Fin nodes))
      (reads : Nat) (tail : RootReadTrace heap valueBase healthy rest selected reads) :
      RootReadTrace heap valueBase healthy (record :: rest)
        (if storedRootValue heap valueBase record.2 == healthy then record :: selected else selected) (reads + 1)

theorem classifyRecords_trace (heap : Array (Word width)) (valueBase : Nat) (healthy : Bool)
    (records : List (Fin bound × Fin nodes)) :
    RootReadTrace heap valueBase healthy records (classifyRecords heap valueBase healthy records) records.length := by
  induction records with
  | nil => exact .nil
  | cons record rest ih =>
    simpa only [classifyRecords, List.filter_cons, List.length_cons] using RootReadTrace.read record rest _ _ ih

/-- Position filtering describes the result, but performs no runtime root access. -/
def positionFilter (graph : DAG n) (heap : Array (Word width)) (valueBase : Nat) (healthy : Bool) :
    List (Fin graph.roots.length) :=
  (List.finRange graph.roots.length).filter
    (fun position => storedRootValue heap valueBase (graph.roots.get position) == healthy)

theorem classifyRecords_source (graph : DAG n) (heap : Array (Word width)) (valueBase : Nat) (healthy : Bool) :
    classifyRecords heap valueBase healthy (rootRecordsFrom graph.roots.length 0 graph.roots) =
      (positionFilter graph heap valueBase healthy).map
        (fun position => (position, graph.roots.get position)) := by
  rw [rootRecords_eq_ofFn]
  simp only [classifyRecords, List.ofFn_eq_map, List.filter_map, positionFilter, Function.comp_def]

theorem classifiedPositions (graph : DAG n) (heap : Array (Word width)) (valueBase : Nat) (healthy : Bool) :
    (classifyRecords heap valueBase healthy (rootRecordsFrom graph.roots.length 0 graph.roots)).map Prod.fst =
      positionFilter graph heap valueBase healthy := by
  rw [classifyRecords_source]
  simp only [List.map_map, Function.comp_def, List.map_id_fun', id_eq]

@[reducible] def recordFamily (graph : DAG n) (records : List (Fin graph.roots.length × Fin graph.nodeCount)) : DAG n :=
  ⟨graph.nodeCount, graph.node, records.map Prod.snd⟩

theorem classifiedFamily (graph : DAG n) (heap : Array (Word width)) (valueBase : Nat) (healthy : Bool) :
    recordFamily graph (classifyRecords heap valueBase healthy (rootRecordsFrom graph.roots.length 0 graph.roots)) =
      rootFamily graph (positionFilter graph heap valueBase healthy) := by
  rw [classifyRecords_source]
  simp only [recordFamily, rootFamily, List.map_map, Function.comp_def]

theorem storedRootValue_correct (heap : Array (Word width)) (values : Fin nodes → Bool)
    (root : Fin nodes) (capacity : 1 < 2 ^ width) :
    storedRootValue (ForestInputStored.withValues heap values) heap.size root = values root := by
  have bound : heap.size + root.val < (ForestInputStored.withValues heap values).size := by
    simp only [ForestInputStored.withValues_size]; omega
  have cell := ForestInputStored.value_cell heap values root
  unfold storedRootValue
  rw [Array.getElem?_eq_getElem bound, cell]
  simp only [Option.getD_some, Controller.Cost.boolWord_val width capacity]
  cases values root <;> decide

theorem classified_source_positions (graph : DAG n) (rows : List Row) (rawRoots : List Nat)
    (assignment : Assignment n) (healthy : Bool) (capacity : 1 < 2 ^ width) :
    positionFilter graph
      (evaluationHeap (packetHeaderHeap width n rows rawRoots) rows rawRoots assignment (graph.evalTable assignment))
      (channelHeap (packetHeaderHeap width n rows rawRoots) rows rawRoots assignment).size healthy =
    (List.finRange graph.roots.length).filter
      (fun position => graph.eval assignment (graph.roots.get position) == healthy) := by
  apply List.filter_congr
  intro position member
  change (storedRootValue (ForestInputStored.withValues _ (graph.evalTable assignment)) _
    (graph.roots.get position) == healthy) = _
  rw [storedRootValue_correct _ _ _ capacity, DAG.evalTable_eq_eval]

end Controller.Cost.Forest
namespace Controller.Cost.Forest
open Controller.Decoder Controller.Decoder.DAG Controller.Cost.GateProgram
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestInputPrefixStored
open Controller.Cost.UniformDAGRun

/-- One executed source evaluation supplies both healthy-root partitions.
Classification performs two linear scans over declared positions; both
subfamilies inherit the internal occurrence forest without merging roots. -/
theorem classification_execution (graph : DAG n) (forest : graph.FormulaForest)
    (rows : List Row) (rawRoots : List Nat) (matched : RowsMatch graph rows)
    (heads : UniformDAGSource.HeadsMatch graph rows matched) (rootsMatch : RootsMatch graph rawRoots)
    (target : Channel n)
    (suffix output : List (Word (UniformDAGResources.chosenWidth graph)))
    (address loaded temporary : Word (UniformDAGResources.chosenWidth graph)) :
    ∃ final ticks peak,
      Execution (UniformDAGResources.program (UniformDAGResources.chosenWidth graph) n rows
        rawRoots (assignmentOfSet {target}))
        ((ForestCounter.counterState (#[] : Array (Word (UniformDAGResources.chosenWidth graph))) 0
          address loaded temporary).frame
          ((inputPacket n 0 rows rawRoots).map (word (UniformDAGResources.chosenWidth graph)) ++
            List.ofFn (fun i => boolWord (UniformDAGResources.chosenWidth graph)
              (assignmentOfSet {target} i)) ++ suffix) output)
        final ticks peak ∧
      ticks ≤ 85 * graph.countedSize + 33 ∧
      peak ≤ 7 * graph.countedSize + 14 + suffix.length + output.length ∧
      final.stack = suffix ∧ final.output = output ∧
      final.heap = evaluationHeap (packetHeaderHeap (UniformDAGResources.chosenWidth graph) n rows rawRoots)
        rows rawRoots (assignmentOfSet {target}) (graph.evalTable (assignmentOfSet {target})) ∧
      RootRecordTrace graph.roots.length 0 graph.roots
        (rootRecordsFrom graph.roots.length 0 graph.roots) graph.roots.length ∧
      ∀ healthy : Bool,
        let valueBase := (channelHeap (packetHeaderHeap (UniformDAGResources.chosenWidth graph) n rows rawRoots)
          rows rawRoots (assignmentOfSet {target})).size
        let records := classifyRecords final.heap valueBase healthy
          (rootRecordsFrom graph.roots.length 0 graph.roots)
        RootReadTrace final.heap valueBase healthy
          (rootRecordsFrom graph.roots.length 0 graph.roots) records graph.roots.length ∧
        (records.map Prod.fst).Nodup ∧ records.length ≤ graph.roots.length ∧
        (recordFamily graph records).FormulaForest ∧
        ∀ root ∈ (recordFamily graph records).roots,
          graph.eval (assignmentOfSet {target}) root = healthy := by
  obtain ⟨final, ticks, peak, trace, time, space, heap, stack, out, pc, running⟩ :=
    UniformDAGResources.execution graph rows rawRoots matched heads rootsMatch
      (assignmentOfSet {target}) suffix output address loaded temporary
  refine ⟨final, ticks, peak, trace, time, space, stack, out, heap,
    rootRecordsFrom_trace _ _ _ (by omega), ?_⟩
  intro healthy
  dsimp only
  let valueBase := (channelHeap (packetHeaderHeap (UniformDAGResources.chosenWidth graph) n rows rawRoots)
    rows rawRoots (assignmentOfSet {target})).size
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [rootRecordsFrom_length graph.roots.length 0 graph.roots (by omega)] using classifyRecords_trace
      final.heap valueBase healthy (rootRecordsFrom graph.roots.length 0 graph.roots)
  · rw [classifiedPositions]
    exact (List.nodup_finRange _).filter _
  · rw [classifyRecords_source, List.length_map]
    unfold positionFilter
    simpa only [List.length_finRange] using List.length_filter_le
      (fun position => storedRootValue final.heap valueBase (graph.roots.get position) == healthy)
      (List.finRange graph.roots.length)
  · rw [classifiedFamily]
    exact rootFamily_forest graph forest _ ((List.nodup_finRange _).filter _)
  · intro root member
    change root ∈ List.map Prod.snd (classifyRecords final.heap valueBase healthy
      (rootRecordsFrom graph.roots.length 0 graph.roots)) at member
    rw [classifyRecords_source] at member
    simp only [List.map_map, Function.comp_def] at member
    obtain ⟨position, present, same⟩ := List.mem_map.mp member
    rw [heap, classified_source_positions] at present
    · have selected := (List.mem_filter.mp present).2
      simpa only [← same, beq_iff_eq] using selected
    · unfold UniformDAGResources.chosenWidth
      exact Nat.one_lt_two_pow (by omega)

end Controller.Cost.Forest
namespace Controller.Cost.Forest
open Controller.Decoder Controller.Decoder.DAG Controller.Cost.ForestIndexedOperands

/-- Subfamily formation changes only the root occurrence list. -/
theorem rootFamily_rows (graph : DAG n) (positions : List (Fin graph.roots.length))
    (rows : List Row) (matched : RowsMatch graph rows) :
    RowsMatch (rootFamily graph positions) rows := by
  refine ⟨matched.length_eq, ?_⟩
  intro index
  exact matched.node index

def familyRootIds (graph : DAG n) (positions : List (Fin graph.roots.length)) : List Nat :=
  positions.map (fun position => (graph.roots.get position).val)

theorem rootFamily_rootIds (graph : DAG n) (positions : List (Fin graph.roots.length)) :
    RootsMatch (rootFamily graph positions) (familyRootIds graph positions) := by
  simp only [RootsMatch, familyRootIds, rootFamily, List.map_map, Function.comp_def]

theorem rootFamily_eval (graph : DAG n) (positions : List (Fin graph.roots.length))
    (assignment : Assignment n) (owner : Fin graph.nodeCount) :
    (rootFamily graph positions).eval assignment owner = graph.eval assignment owner := by
  have same : ∀ rank : Nat, ∀ index : Fin graph.nodeCount, index.val = rank →
      (rootFamily graph positions).eval assignment index = graph.eval assignment index := by
    intro rank
    induction rank using Nat.strong_induction_on with
    | h rank ih =>
      intro index rankEq
      rw [DAG.eval_eq (rootFamily graph positions) assignment index, DAG.eval_eq graph assignment index]
      apply Gate.eval_congr
      · intro channel member; rfl
      · intro child member
        exact ih child.val (by rw [← rankEq]; exact child.isLt) (graph.childIndex index child) rfl
  exact same owner.val owner rfl

def healthyPositions (graph : DAG n) (target : Channel n) (healthy : Bool) :
    List (Fin graph.roots.length) :=
  (List.finRange graph.roots.length).filter
    (fun position => graph.eval (assignmentOfSet {target}) (graph.roots.get position) == healthy)

theorem healthyFamily_membership (graph : DAG n) (target : Channel n) (healthy : Bool)
    (root : Fin graph.nodeCount) :
    root ∈ (rootFamily graph (healthyPositions graph target healthy)).roots ↔
      root ∈ graph.roots ∧ graph.eval (assignmentOfSet {target}) root = healthy := by
  constructor
  · intro member
    obtain ⟨position, selected, same⟩ := List.mem_map.mp member
    have classified := (List.mem_filter.mp selected).2
    refine ⟨?_, ?_⟩
    · rw [← same]; exact List.get_mem _ _
    · simpa only [← same, beq_iff_eq] using classified
  · rintro ⟨member, value⟩
    obtain ⟨position, same⟩ := List.mem_iff_get.mp member
    apply List.mem_map.mpr
    refine ⟨position, ?_, same⟩
    apply List.mem_filter.mpr
    refine ⟨List.mem_finRange position, ?_⟩
    simpa only [same, value, beq_self_eq_true]

/-- Detection over the declared roots is exactly the disjunction of the
healthy-zero true-witness branch and healthy-one zero-witness branch. -/
theorem mixed_root_discrepancy (graph : DAG n) (b : Nat) (target : Channel n) :
    (∃ root ∈ graph.roots, ∃ K : Finset (Channel n), Admissible b target K ∧
      graph.eval (assignmentOfSet K) root ≠ graph.eval (assignmentOfSet {target}) root) ↔
    (∃ root ∈ (rootFamily graph (healthyPositions graph target false)).roots,
      ∃ K : Finset (Channel n), Admissible b target K ∧ graph.eval (assignmentOfSet K) root = true) ∨
    (∃ root ∈ (rootFamily graph (healthyPositions graph target true)).roots,
      ∃ K : Finset (Channel n), Admissible b target K ∧ graph.eval (assignmentOfSet K) root = false) := by
  constructor
  · rintro ⟨root, member, K, admissible, different⟩
    cases healthy : graph.eval (assignmentOfSet {target}) root with
    | false =>
      left
      refine ⟨root, (healthyFamily_membership graph target false root).mpr ⟨member, healthy⟩,
        K, admissible, ?_⟩
      cases faulty : graph.eval (assignmentOfSet K) root
      · exact False.elim (different (faulty.trans healthy.symm))
      · rfl
    | true =>
      right
      refine ⟨root, (healthyFamily_membership graph target true root).mpr ⟨member, healthy⟩,
        K, admissible, ?_⟩
      cases faulty : graph.eval (assignmentOfSet K) root
      · rfl
      · exact False.elim (different (faulty.trans healthy.symm))
  · rintro (⟨root, selected, K, admissible, faulty⟩ | ⟨root, selected, K, admissible, faulty⟩)
    · obtain ⟨member, healthy⟩ := (healthyFamily_membership graph target false root).mp selected
      refine ⟨root, member, K, admissible, ?_⟩
      rw [faulty, healthy]; decide
    · obtain ⟨member, healthy⟩ := (healthyFamily_membership graph target true root).mp selected
      refine ⟨root, member, K, admissible, ?_⟩
      rw [faulty, healthy]; decide

end Controller.Cost.Forest
namespace Controller.Cost.Forest
open Controller.Decoder Controller.Decoder.DAG

theorem rootFamily_incidence_counts (graph : DAG n) (positions : List (Fin graph.roots.length)) :
    (rootFamily graph positions).nodeCount = graph.nodeCount ∧
    (rootFamily graph positions).childIncidences = graph.childIncidences ∧
    (rootFamily graph positions).guardIncidences = graph.guardIncidences ∧
    (rootFamily graph positions).roots.length = positions.length := by
  simp only [rootFamily, DAG.childIncidences, DAG.guardIncidences, List.length_map]
  exact ⟨trivial, trivial, trivial, trivial⟩

theorem healthyPositions_nodup (graph : DAG n) (target : Channel n) (healthy : Bool) :
    (healthyPositions graph target healthy).Nodup :=
  (List.nodup_finRange _).filter _

theorem healthyPositions_length_le (graph : DAG n) (target : Channel n) (healthy : Bool) :
    (healthyPositions graph target healthy).length ≤ graph.roots.length := by
  simpa only [healthyPositions, List.length_finRange] using List.length_filter_le
    (fun position => graph.eval (assignmentOfSet {target}) (graph.roots.get position) == healthy)
    (List.finRange graph.roots.length)

/-- Both subfamilies share all original node and incidence cells. Only their
root occurrence lists differ; a constant number of shared-source passes stays
linear even when many roots terminate at the same input. -/
theorem healthyFamily_countedSize_le (graph : DAG n) (target : Channel n) (healthy : Bool) :
    (rootFamily graph (healthyPositions graph target healthy)).countedSize ≤ graph.countedSize := by
  have rootCount := healthyPositions_length_le graph target healthy
  have counts := rootFamily_incidence_counts graph (healthyPositions graph target healthy)
  simp only [DAG.countedSize_eq, rootFamily, DAG.childIncidences, DAG.guardIncidences, List.length_map] at *
  omega

/-- Declared positions occur in exactly one healthy subfamily, including
positions carrying repeated root labels. -/
theorem healthyPositions_length_sum (graph : DAG n) (target : Channel n) :
    (healthyPositions graph target false).length +
      (healthyPositions graph target true).length = graph.roots.length := by
  have split := List.length_eq_length_filter_add
    (l := List.finRange graph.roots.length)
    (fun position => graph.eval (assignmentOfSet {target}) (graph.roots.get position))
  simp only [healthyPositions, beq_false, beq_true, List.length_finRange] at *
  omega

end Controller.Cost.Forest
namespace Controller.Cost.Forest
open Controller.Decoder Controller.Decoder.DAG Controller.Cost.ForestIndexedOperands
open Controller.Cost.ForestZeroSourcePlan Controller.Cost.ForestZeroOutputImage
open Controller.Cost.ForestZeroAdmissibleCaller Controller.Cost.ForestZeroCompile
open Controller.Cost.GateProgram
variable {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]

private theorem rootPosition_exists (graph : DAG n) (property : Fin graph.nodeCount → Prop) :
    (∃ position : Fin graph.roots.length, property (graph.roots.get position)) ↔
      ∃ root ∈ graph.roots, property root := by
  constructor
  · rintro ⟨position, holds⟩
    exact ⟨graph.roots.get position, List.get_mem _ _, holds⟩
  · rintro ⟨root, member, holds⟩
    obtain ⟨position, same⟩ := List.mem_iff_get.mp member
    exact ⟨position, same.symm ▸ holds⟩

/-- The positive branch uses the actual decoded-source evaluator. The
negative branch tests the actual constructor formulas produced from its
selected occurrence stream. No root is classified by a semantic oracle. -/
theorem mixed_candidate_iff (graph : DAG n) (forest : graph.FormulaForest)
    (rows : List Row) (matched : RowsMatch graph rows) (weights : Channel n → W)
    (nonnegative : ∀ channel, 0 ≤ weights channel) (b : Nat) (target : Channel n)
    (heap : Array (Word width))
    (layout : ForestZeroDictionary.Layout (n + graph.nodeCount) heap.size) :
    let positive := rootFamily graph (healthyPositions graph target false)
    let negative := rootFamily graph (healthyPositions graph target true)
    ((ForestWeightedIndexed.runAll (ForestWeightedIndexed.source n rows) weights b target
        (familyRootIds graph (healthyPositions graph target false))).2.selected ≠ none ∨
      ∃ position : Fin negative.roots.length,
        Controller.CNF.Satisfiable (constructorFormula heap layout (empty (n + graph.nodeCount))
          (empty_coherent _) (zeroQuery width negative rows
            (familyRootIds graph (healthyPositions graph target true))
            (rootFamily_rows graph _ rows matched) b position target) n (Nat.le_add_right _ _))) ↔
      ∃ root ∈ graph.roots, ∃ K : Finset (Channel n), Admissible b target K ∧
        graph.eval (assignmentOfSet K) root ≠ graph.eval (assignmentOfSet {target}) root := by
  dsimp only
  have positiveMeaning := ForestWeightedIndexed.indexed_none_iff
    (rootFamily graph (healthyPositions graph target false))
    (rootFamily_guarded graph forest.1 _) rows _ (rootFamily_rows graph _ rows matched)
    (rootFamily_rootIds graph _) weights nonnegative b target
  have nonemptyMeaning := not_congr positiveMeaning
  simp only [not_not] at nonemptyMeaning
  refine (or_congr nonemptyMeaning Iff.rfl).trans ?_
  have zeroMeaning :
      (∃ position : Fin (rootFamily graph (healthyPositions graph target true)).roots.length,
        Controller.CNF.Satisfiable (constructorFormula heap layout (empty (n + graph.nodeCount))
          (empty_coherent _) (zeroQuery width (rootFamily graph (healthyPositions graph target true))
            rows (familyRootIds graph (healthyPositions graph target true))
            (rootFamily_rows graph _ rows matched) b position target) n (Nat.le_add_right _ _))) ↔
      ∃ position : Fin (rootFamily graph (healthyPositions graph target true)).roots.length,
        ∃ K : Finset (Channel n), Admissible b target K ∧
          graph.eval (assignmentOfSet K)
            ((rootFamily graph (healthyPositions graph target true)).roots.get position) = false := by
    simp_rw [zero_query_constructor_iff _ (rootFamily_guarded graph forest.1 _), rootFamily_eval]
  refine (or_congr Iff.rfl zeroMeaning).trans ?_
  simp_rw [rootFamily_eval]
  have positiveRoots := rootPosition_exists (rootFamily graph (healthyPositions graph target false))
    (fun root => ∃ K : Finset (Channel n), Admissible b target K ∧
      graph.eval (assignmentOfSet K) root = true)
  have negativeRoots := rootPosition_exists (rootFamily graph (healthyPositions graph target true))
    (fun root => ∃ K : Finset (Channel n), Admissible b target K ∧
      graph.eval (assignmentOfSet K) root = false)
  exact (or_congr positiveRoots negativeRoots).trans (mixed_root_discrepancy graph b target).symm

/-- All positive bus counts and mixed healthy root values are covered by the
two actual source-query branches. The low-drive case is rejected directly. -/
theorem mixed_candidate_physical_iff (graph : DAG n) (forest : graph.FormulaForest)
    (rows : List Row) (matched : RowsMatch graph rows) (weights : Channel n → W)
    (nonnegative : ∀ channel, 0 ≤ weights channel) (b : Nat) (positive : 0 < b)
    (bridge : Controller.Physical.Bridge n) (drive : Bool)
    (heap : Array (Word width))
    (layout : ForestZeroDictionary.Layout (n + graph.nodeCount) heap.size) :
    Controller.Physical.BridgeDetectable (b := b) bridge drive graph.observations ↔
      drive = true ∧
      ((ForestWeightedIndexed.runAll (ForestWeightedIndexed.source n rows) weights b bridge.target
        (familyRootIds graph (healthyPositions graph bridge.target false))).2.selected ≠ none ∨
      ∃ position : Fin (rootFamily graph (healthyPositions graph bridge.target true)).roots.length,
        Controller.CNF.Satisfiable (constructorFormula heap layout (empty (n + graph.nodeCount))
          (empty_coherent _) (zeroQuery width (rootFamily graph (healthyPositions graph bridge.target true))
            rows (familyRootIds graph (healthyPositions graph bridge.target true))
            (rootFamily_rows graph _ rows matched) b position bridge.target) n (Nat.le_add_right _ _))) := by
  rw [Controller.Physical.bridge_detectable_iff_root bridge positive drive graph]
  have meaning := mixed_candidate_iff graph forest rows matched weights nonnegative b bridge.target heap layout
  dsimp only at meaning
  exact and_congr_right (fun _ => meaning.symm)

end Controller.Cost.Forest

namespace Controller.Cost.Forest
open Controller.Decoder Controller.Decoder.DAG Controller.Cost.ForestIndexedOperands

/-- Runtime root records are decoded from the supplied original ID stream.
Neither classification nor record formation reads DAG.roots by position. -/
def rawRootRecords (nodes occurrences : Nat) (rawRoots : List Nat) : List (Fin occurrences × Fin nodes) :=
  match ForestWeightedIndexed.boundedIds nodes rawRoots with
  | none => []
  | some roots => rootRecordsFrom occurrences 0 roots

theorem rawRootRecords_source (graph : DAG n) (rawRoots : List Nat)
    (matched : RootsMatch graph rawRoots) :
    rawRootRecords graph.nodeCount graph.roots.length rawRoots =
      rootRecordsFrom graph.roots.length 0 graph.roots := by
  unfold rawRootRecords
  rw [matched, ForestWeightedIndexed.boundedIds_fin_values]

/-- Decoding validates each supplied root ID and preserves repetitions. The
following record scan charges each decoded occurrence once. -/
theorem rawRootRecords_trace (graph : DAG n) (rawRoots : List Nat)
    (matched : RootsMatch graph rawRoots) :
    ∃ checks cells,
      ForestWeightedIndexed.IdValidationTrace graph.nodeCount rawRoots (some graph.roots) checks cells ∧
      checks ≤ graph.roots.length ∧ cells ≤ graph.roots.length ∧
      RootRecordTrace graph.roots.length 0 graph.roots
        (rawRootRecords graph.nodeCount graph.roots.length rawRoots) graph.roots.length := by
  obtain ⟨checks, cells, trace, checkBound, cellBound⟩ :=
    ForestWeightedIndexed.boundedIds_validation graph.nodeCount rawRoots
  have decoded : ForestWeightedIndexed.boundedIds graph.nodeCount rawRoots = some graph.roots := by
    rw [matched, ForestWeightedIndexed.boundedIds_fin_values]
  rw [decoded] at trace
  have length : rawRoots.length = graph.roots.length := by rw [matched, List.length_map]
  refine ⟨checks, cells, trace, length ▸ checkBound, length ▸ cellBound, ?_⟩
  rw [rawRootRecords_source graph rawRoots matched]
  exact rootRecordsFrom_trace _ _ _ (by omega)

end Controller.Cost.Forest

namespace Controller.Cost.Forest
open Controller.Decoder Controller.Decoder.DAG Controller.Cost.GateProgram
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestInputPrefixStored
open Controller.Cost.UniformDAGRun

/-- Both root IDs and their original occurrence positions remain in the
selected stream. Forming a query root list projects those cached IDs. -/
def recordRootIds {occurrences nodes : Nat} (records : List (Fin occurrences × Fin nodes)) : List Nat :=
  records.map (fun record => record.2.val)

theorem recordFamily_rows (graph : DAG n)
    (records : List (Fin graph.roots.length × Fin graph.nodeCount))
    (rows : List Row) (matched : RowsMatch graph rows) : RowsMatch (recordFamily graph records) rows := by
  refine ⟨matched.length_eq, ?_⟩
  intro index
  exact matched.node index

theorem recordFamily_rootIds (graph : DAG n)
    (records : List (Fin graph.roots.length × Fin graph.nodeCount)) :
    RootsMatch (recordFamily graph records) (recordRootIds records) := by
  simp only [RootsMatch, recordFamily, recordRootIds, List.map_map, Function.comp_def]

theorem classifiedRootIds (graph : DAG n) (heap : Array (Word width)) (valueBase : Nat) (healthy : Bool) :
    recordRootIds (classifyRecords heap valueBase healthy (rootRecordsFrom graph.roots.length 0 graph.roots)) =
      familyRootIds graph (positionFilter graph heap valueBase healthy) := by
  rw [classifyRecords_source]
  simp only [recordRootIds, familyRootIds, List.map_map, Function.comp_def]

/-- The semantic family equality is derived from the evaluated source table;
query constructors consume the directly projected root-ID stream. -/
theorem evaluatedFamily (graph : DAG n) (rows : List Row) (rawRoots : List Nat)
    (target : Channel n) (healthy : Bool) (capacity : 1 < 2 ^ width) :
    recordFamily graph (classifyRecords
      (evaluationHeap (packetHeaderHeap width n rows rawRoots) rows rawRoots (assignmentOfSet {target})
        (graph.evalTable (assignmentOfSet {target})))
      (channelHeap (packetHeaderHeap width n rows rawRoots) rows rawRoots (assignmentOfSet {target})).size
      healthy (rootRecordsFrom graph.roots.length 0 graph.roots)) =
    rootFamily graph (healthyPositions graph target healthy) := by
  rw [classifiedFamily, classified_source_positions graph rows rawRoots _ healthy capacity]
  rfl

theorem evaluatedRootIds (graph : DAG n) (rows : List Row) (rawRoots : List Nat)
    (target : Channel n) (healthy : Bool) (capacity : 1 < 2 ^ width) :
    recordRootIds (classifyRecords
      (evaluationHeap (packetHeaderHeap width n rows rawRoots) rows rawRoots (assignmentOfSet {target})
        (graph.evalTable (assignmentOfSet {target})))
      (channelHeap (packetHeaderHeap width n rows rawRoots) rows rawRoots (assignmentOfSet {target})).size
      healthy (rootRecordsFrom graph.roots.length 0 graph.roots)) =
    familyRootIds graph (healthyPositions graph target healthy) := by
  rw [classifiedRootIds, classified_source_positions graph rows rawRoots _ healthy capacity]
  rfl

end Controller.Cost.Forest

namespace Controller.Cost.Forest
open Controller.Decoder Controller.Decoder.DAG Controller.Cost.GateProgram
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestInputPrefixStored
open Controller.Cost.UniformDAGRun Controller.Cost.ForestZeroSourcePlan
open Controller.Cost.ForestZeroAdmissibleCaller Controller.Cost.ForestZeroCompile
variable {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]

/-- The selected occurrence stream is read from the executed node-value table.
Its semantic correspondence retains each original position, including repeated IDs. -/
theorem evaluated_records_source (graph : DAG n) (rows : List Row) (rawRoots : List Nat)
    (rootsMatch : RootsMatch graph rawRoots) (target : Channel n) (healthy : Bool) (capacity : 1 < 2 ^ width) :
    classifyRecords
      (evaluationHeap (packetHeaderHeap width n rows rawRoots) rows rawRoots (assignmentOfSet {target})
        (graph.evalTable (assignmentOfSet {target})))
      (channelHeap (packetHeaderHeap width n rows rawRoots) rows rawRoots (assignmentOfSet {target})).size
      healthy (rawRootRecords graph.nodeCount graph.roots.length rawRoots) =
    (healthyPositions graph target healthy).map (fun position => (position, graph.roots.get position)) := by
  rw [rawRootRecords_source graph rawRoots rootsMatch, classifyRecords_source,
    classified_source_positions graph rows rawRoots _ healthy capacity]
  rfl

private theorem recordFamily_eval (graph : DAG n)
    (records : List (Fin graph.roots.length × Fin graph.nodeCount))
    (assignment : Assignment n) (owner : Fin graph.nodeCount) :
    (recordFamily graph records).eval assignment owner = graph.eval assignment owner := by
  have same : ∀ rank : Nat, ∀ index : Fin graph.nodeCount, index.val = rank →
      (recordFamily graph records).eval assignment index = graph.eval assignment index := by
    intro rank
    induction rank using Nat.strong_induction_on with
    | h rank ih =>
      intro index rankEq
      rw [DAG.eval_eq (recordFamily graph records) assignment index, DAG.eval_eq graph assignment index]
      apply Gate.eval_congr
      · intro channel member; rfl
      · intro child member
        exact ih child.val (by rw [← rankEq]; exact child.isLt) (graph.childIndex index child) rfl
  exact same owner.val owner rfl

/-- Both candidate branches consume root IDs projected directly from the
classified records. The stored Boolean table determines their partition. -/
theorem evaluated_mixed_candidate_iff (graph : DAG n) (forest : graph.FormulaForest)
    (rows : List Row) (matched : RowsMatch graph rows) (rawRoots : List Nat)
    (rootsMatch : RootsMatch graph rawRoots)
    (weights : Channel n → W) (nonnegative : ∀ channel, 0 ≤ weights channel)
    (b : Nat) (target : Channel n) (heap : Array (Word width))
    (layout : ForestZeroDictionary.Layout (n + graph.nodeCount) heap.size)
    (capacity : 1 < 2 ^ width) :
    let evaluated := evaluationHeap (packetHeaderHeap width n rows rawRoots) rows rawRoots
      (assignmentOfSet {target}) (graph.evalTable (assignmentOfSet {target}))
    let nodeBase := (channelHeap (packetHeaderHeap width n rows rawRoots) rows rawRoots
      (assignmentOfSet {target})).size
    let records := rawRootRecords graph.nodeCount graph.roots.length rawRoots
    let positive := classifyRecords evaluated nodeBase false records
    let negative := classifyRecords evaluated nodeBase true records
    ((ForestWeightedIndexed.runAll (ForestWeightedIndexed.source n rows) weights b target
        (recordRootIds positive)).2.selected ≠ none ∨
      ∃ position : Fin (recordFamily graph negative).roots.length,
        Controller.CNF.Satisfiable (constructorFormula heap layout (empty (n + graph.nodeCount))
          (empty_coherent _) (zeroQuery width (recordFamily graph negative) rows (recordRootIds negative)
            (recordFamily_rows graph negative rows matched) b
            position target)
          n (Nat.le_add_right _ _))) ↔
      ∃ root ∈ graph.roots, ∃ K : Finset (Channel n), Admissible b target K ∧
        graph.eval (assignmentOfSet K) root ≠ graph.eval (assignmentOfSet {target}) root := by
  dsimp only
  let evaluated := evaluationHeap (packetHeaderHeap width n rows rawRoots) rows rawRoots
    (assignmentOfSet {target}) (graph.evalTable (assignmentOfSet {target}))
  let nodeBase := (channelHeap (packetHeaderHeap width n rows rawRoots) rows rawRoots
    (assignmentOfSet {target})).size
  let records := rawRootRecords graph.nodeCount graph.roots.length rawRoots
  let negative := classifyRecords evaluated nodeBase true records
  have positiveIds : recordRootIds (classifyRecords evaluated nodeBase false records) =
      familyRootIds graph (healthyPositions graph target false) := by
    have same := congrArg recordRootIds
      (evaluated_records_source graph rows rawRoots rootsMatch target false capacity)
    simpa only [recordRootIds, familyRootIds, List.map_map, Function.comp_def] using same
  rw [positiveIds]
  have negativeRoots : (recordFamily graph negative).roots =
      (rootFamily graph (healthyPositions graph target true)).roots := by
    have same := congrArg (fun values : List (Fin graph.roots.length × Fin graph.nodeCount) =>
      values.map Prod.snd) (evaluated_records_source graph rows rawRoots rootsMatch target true capacity)
    simpa only [recordFamily, rootFamily, List.map_map, Function.comp_def] using same
  have actualMeaning :
      (∃ position : Fin (recordFamily graph negative).roots.length,
        CNF.Satisfiable (constructorFormula heap layout (empty (n + graph.nodeCount)) (empty_coherent _)
          (zeroQuery width (recordFamily graph negative) rows (recordRootIds negative)
            (recordFamily_rows graph negative rows matched) b position target) n (Nat.le_add_right _ _))) ↔
      ∃ root ∈ (recordFamily graph negative).roots, ∃ K : Finset (Channel n),
        Admissible b target K ∧ graph.eval (assignmentOfSet K) root = false := by
    calc
      _ ↔ ∃ position : Fin (recordFamily graph negative).roots.length, ∃ K : Finset (Channel n),
          Admissible b target K ∧ graph.eval (assignmentOfSet K)
            ((recordFamily graph negative).roots.get position) = false := by
        simp_rw [ForestZeroOutputImage.zero_query_constructor_iff (recordFamily graph negative) forest.1, recordFamily_eval]
      _ ↔ _ := rootPosition_exists (recordFamily graph negative)
        (fun root : Fin graph.nodeCount => ∃ K : Finset (Channel n),
          Admissible b target K ∧ graph.eval (assignmentOfSet K) root = false)
  have canonicalMeaning :
      (∃ position : Fin (rootFamily graph (healthyPositions graph target true)).roots.length,
        CNF.Satisfiable (constructorFormula heap layout (empty (n + graph.nodeCount)) (empty_coherent _)
          (zeroQuery width (rootFamily graph (healthyPositions graph target true)) rows
            (familyRootIds graph (healthyPositions graph target true)) (rootFamily_rows graph _ rows matched)
            b position target) n (Nat.le_add_right _ _))) ↔
      ∃ root ∈ (rootFamily graph (healthyPositions graph target true)).roots, ∃ K : Finset (Channel n),
        Admissible b target K ∧ graph.eval (assignmentOfSet K) root = false := by
    calc
      _ ↔ ∃ position : Fin (rootFamily graph (healthyPositions graph target true)).roots.length,
          ∃ K : Finset (Channel n), Admissible b target K ∧ graph.eval (assignmentOfSet K)
            ((rootFamily graph (healthyPositions graph target true)).roots.get position) = false := by
        simp_rw [ForestZeroOutputImage.zero_query_constructor_iff _ (rootFamily_guarded graph forest.1 _), rootFamily_eval]
      _ ↔ _ := rootPosition_exists (rootFamily graph (healthyPositions graph target true))
        (fun root : Fin graph.nodeCount => ∃ K : Finset (Channel n),
          Admissible b target K ∧ graph.eval (assignmentOfSet K) root = false)
  have semantic :
      (∃ root ∈ (recordFamily graph negative).roots, ∃ K : Finset (Channel n),
        Admissible b target K ∧ graph.eval (assignmentOfSet K) root = false) ↔
      ∃ root ∈ (rootFamily graph (healthyPositions graph target true)).roots, ∃ K : Finset (Channel n),
        Admissible b target K ∧ graph.eval (assignmentOfSet K) root = false := by
    rw [negativeRoots]
  exact (or_congr Iff.rfl (actualMeaning.trans (semantic.trans canonicalMeaning.symm))).trans
    (mixed_candidate_iff graph forest rows matched weights nonnegative b target heap layout)

end Controller.Cost.Forest

namespace Controller.Cost.Forest
open Controller.Decoder Controller.Decoder.DAG Controller.Cost.GateProgram
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestInputPrefixStored
open Controller.Cost.UniformDAGRun Controller.Cost.ForestZeroSourcePlan
variable {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]

/-- The two subfamily workloads charge each declared occurrence once. Shared
node and incidence scans contribute only a constant number of source passes. -/
theorem classified_branch_work_bound (graph : DAG n) (forest : graph.FormulaForest)
    (rows : List Row) (matched : RowsMatch graph rows)
    (weights : Channel n → W) (b : Nat) (target : Channel n) :
    let positive := rootFamily graph (healthyPositions graph target false)
    let negative := rootFamily graph (healthyPositions graph target true)
    let weighted := (ForestWeightedIndexed.runAll (ForestWeightedIndexed.source n rows) weights b target
      (familyRootIds graph (healthyPositions graph target false))).2
    let queries := zeroQueries width negative rows (familyRootIds graph (healthyPositions graph target true))
      (rootFamily_rows graph _ rows matched) b target
    weighted.operations + weighted.arithmetic + (queries.map List.length).sum +
      (queries.map fun clauses => clauses.flatten.length).sum ≤
      n + 13 * graph.roots.length + 21 * graph.childIncidences + 7 * graph.guardIncidences := by
  dsimp only
  let positive := rootFamily graph (healthyPositions graph target false)
  let negative := rootFamily graph (healthyPositions graph target true)
  have positiveForest := rootFamily_forest graph forest (healthyPositions graph target false)
    (healthyPositions_nodup graph target false)
  have negativeForest := rootFamily_forest graph forest (healthyPositions graph target true)
    (healthyPositions_nodup graph target true)
  have positiveRows := rootFamily_rows graph (healthyPositions graph target false) rows matched
  have negativeRows := rootFamily_rows graph (healthyPositions graph target true) rows matched
  have operations := ForestWeightedIndexed.runAll_operations_bound positive positiveForest rows _
    positiveRows (rootFamily_rootIds graph _) weights b target
  have arithmetic := ForestWeightedIndexed.runAll_arithmetic_bound positive rows _
    positiveRows (rootFamily_rootIds graph _) positiveForest weights b target
  have queries := zero_queries_forest_bounds (width := width) negative rows
    (familyRootIds graph (healthyPositions graph target true)) negativeRows b target negativeForest
  have partition := healthyPositions_length_sum graph target
  dsimp only [positive, negative, rootFamily] at operations arithmetic queries
  simp only [List.length_map] at operations arithmetic queries
  change (ForestWeightedIndexed.runAll (ForestWeightedIndexed.source n rows) weights b target
    (familyRootIds graph (healthyPositions graph target false))).2.operations ≤
    4 * ((healthyPositions graph target false).length + graph.childIncidences) +
      2 * graph.guardIncidences at operations
  change (ForestWeightedIndexed.runAll (ForestWeightedIndexed.source n rows) weights b target
    (familyRootIds graph (healthyPositions graph target false))).2.arithmetic ≤
    n + 8 * ((healthyPositions graph target false).length + graph.childIncidences) +
      4 * graph.guardIncidences at arithmetic
  change ((zeroQueries width (rootFamily graph (healthyPositions graph target true)) rows
    (familyRootIds graph (healthyPositions graph target true)) (rootFamily_rows graph _ rows matched)
    b target).map List.length).sum ≤ 5 * (healthyPositions graph target true).length +
      3 * graph.childIncidences ∧
    ((zeroQueries width (rootFamily graph (healthyPositions graph target true)) rows
      (familyRootIds graph (healthyPositions graph target true)) (rootFamily_rows graph _ rows matched)
      b target).map fun clauses => clauses.flatten.length).sum ≤
      8 * (healthyPositions graph target true).length + 6 * graph.childIncidences +
        graph.guardIncidences at queries
  have rowsBound : ((zeroQueries width
      (rootFamily graph (healthyPositions graph target true)) rows
      (familyRootIds graph (healthyPositions graph target true)) (rootFamily_rows graph _ rows matched)
      b target).map List.length).sum ≤
      5 * (healthyPositions graph target true).length + 3 * graph.childIncidences := queries.1
  have literalsBound : ((zeroQueries width
      (rootFamily graph (healthyPositions graph target true)) rows
      (familyRootIds graph (healthyPositions graph target true)) (rootFamily_rows graph _ rows matched)
      b target).map fun clauses => clauses.flatten.length).sum ≤
      8 * (healthyPositions graph target true).length + 6 * graph.childIncidences +
        graph.guardIncidences := queries.2
  clear queries
  have combined := Nat.add_le_add
    (Nat.add_le_add (Nat.add_le_add operations arithmetic) rowsBound) literalsBound
  exact combined.trans (by omega)

end Controller.Cost.Forest

namespace Controller.Cost.Forest
open Controller Controller.Decoder Controller.Decoder.DAG Controller.Cost.GateProgram
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestZeroSourcePlan
open Controller.Cost.ForestZeroOutputImage Controller.Cost.ForestZeroAdmissibleCaller

/-- The zero branch emits an original-channel witness for an original declared
output. Its occurrence index is retained when the healthy-one family is formed. -/
theorem healthy_one_output_original (graph : DAG n) (forest : graph.FormulaForest)
    (rows : List Row) (matched : RowsMatch graph rows) (b : Nat) (positive : 0 < b)
    (bridge : Physical.Bridge n) (heap : Array (Word width))
    (layout : ForestZeroDictionary.Layout (n + graph.nodeCount) heap.size)
    (observed : List (Word width))
    (position : Fin (zeroQueries width (rootFamily graph (healthyPositions graph bridge.target true))
      rows (familyRootIds graph (healthyPositions graph bridge.target true))
      (rootFamily_rows graph _ rows matched) b bridge.target).length)
    (witness : QueryChannelWitness heap layout
      (zeroQueries width (rootFamily graph (healthyPositions graph bridge.target true))
        rows (familyRootIds graph (healthyPositions graph bridge.target true))
        (rootFamily_rows graph _ rows matched) b bridge.target)[position]
      n (Nat.le_add_right _ _) observed) :
    ∃ original : Fin graph.roots.length, ∃ K : Finset (Channel n),
      Admissible b bridge.target K ∧
      Physical.BridgeInputDetects bridge true graph.observations
        (Physical.realizeBridge bridge positive K) true ∧
      ∃ previous : List (Word width),
        observed = (List.finRange n).map (fun channel =>
          ForestZeroChannelEmit.bitWord width (assignmentOfSet K channel)) ++
          word width 1 :: previous := by
  let family := rootFamily graph (healthyPositions graph bridge.target true)
  obtain ⟨selected, K, admissible, zero, previous, emitted⟩ := zero_stream_output_witness
    family (rootFamily_guarded graph forest.1 _) rows _ (rootFamily_rows graph _ rows matched)
    b bridge.target heap layout observed position witness
  have member : family.roots.get selected ∈ family.roots := List.get_mem _ _
  have originalRoot := (healthyFamily_membership graph bridge.target true _).mp member
  obtain ⟨original, same⟩ := List.mem_iff_get.mp originalRoot.1
  refine ⟨original, K, admissible, ?_, previous, emitted⟩
  apply (Physical.realizeBridge_detects_iff bridge positive K admissible graph.observations).mpr
  refine ⟨original, ?_⟩
  have faulty : graph.eval (assignmentOfSet K) (family.roots.get selected) = false := by
    simpa only [family, rootFamily_eval] using zero
  change graph.eval (assignmentOfSet {bridge.target}) (graph.roots.get original) ≠
    graph.eval (assignmentOfSet K) (graph.roots.get original)
  rw [same, originalRoot.2, faulty]
  decide

end Controller.Cost.Forest
