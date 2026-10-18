module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestZeroSource
public import Controller.Cost.ForestZeroQuery
public import Controller.Cost.ForestNodeVisits
public import Controller.Cost.ForestGuardVisits
public import Mathlib.Data.List.FinRange

@[expose] public section

namespace Controller.Cost.ForestZeroReferenceCone
open Controller.Decoder Controller.Decoder.DAG Controller.CNF
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestZeroSource
open Controller.Cost.ForestZeroEmit Controller.Cost.ForestZeroQuery
open Controller.Cost.ForestZeroRows Controller.Decoder.ZeroSystem

/-- Ordered source references preserve the address of every child occurrence. -/
def childReferences (graph : DAG n) (rows : List Row) (owner : Fin graph.nodeCount) :=
  List.ofFn fun position : Fin (graph.node owner).children.length =>
    childReference graph rows owner position false

def guardReferences (graph : DAG n) (rows : List Row) (owner : Fin graph.nodeCount) :=
  List.ofFn fun position : Fin (graph.node owner).guardLabels.length =>
    guardReference graph rows owner position true

/-- Only an input row consumes its stored channel head; other shapes use the
incoming occurrence as an unused placeholder. -/
def headReference (graph : DAG n) (owner : Fin graph.nodeCount)
    (incoming : Reference (n + graph.nodeCount)) : Reference (n + graph.nodeCount) :=
  match graph.node owner with
  | .input channel => inputReference graph owner channel false
  | _ => incoming

def ownReferences (graph : DAG n) (rows : List Row) (rowsMatch : RowsMatch graph rows)
    (owner : Fin graph.nodeCount) (incoming : Reference (n + graph.nodeCount)) :=
  referenceClauses (rows[owner.val]'(by rw [rowsMatch.length_eq]; exact owner.isLt))
    incoming (headReference graph owner incoming) (childReferences graph rows owner)
    (guardReferences graph rows owner)

/-- A compile-time positional descent produces source-addressed clauses.
The graph correspondence is a proof specification; construction/access costs
are accounted separately and are not asserted constant-time here. -/
def referenceCone (graph : DAG n) (rows : List Row) (rowsMatch : RowsMatch graph rows)
    (owner : Fin graph.nodeCount) (incoming : Reference (n + graph.nodeCount))
    (tail : List (List (Reference (n + graph.nodeCount)))) : List (List (Reference (n + graph.nodeCount))) :=
  ownReferences graph rows rowsMatch owner incoming ++
    (List.finRange (graph.node owner).children.length).foldr (fun position acc =>
      referenceCone graph rows rowsMatch
        (graph.childIndex owner ((graph.node owner).children.get position))
        (childReference graph rows owner position false) acc) tail
termination_by owner.val
decreasing_by exact graph.childIndex_lt _ _

def rootReferenceCones (graph : DAG n) (rows : List Row) (rawRoots : List Nat)
    (rowsMatch : RowsMatch graph rows) : List (List (List (Reference (n + graph.nodeCount)))) :=
  List.ofFn fun position : Fin graph.roots.length =>
    referenceCone graph rows rowsMatch (graph.roots.get position)
      (rootReference graph rows rawRoots position false) []

/-- Physical source storage of each original child reference. -/
theorem childReferences_stored (graph : DAG n) (rows : List Row) (rawRoots : List Nat)
    (rowsMatch : RowsMatch graph rows) (owner : Fin graph.nodeCount) :
    ∀ reference ∈ childReferences graph rows owner,
      StoredReference (packetHeap width n rows rawRoots) n (packetHeap width n rows rawRoots).size reference := by
  intro reference member
  obtain ⟨position, equal⟩ := List.mem_ofFn.mp member
  subst reference
  exact child_stored graph rows rawRoots rowsMatch owner position false

theorem guardReferences_stored (graph : DAG n) (rows : List Row) (rawRoots : List Nat)
    (rowsMatch : RowsMatch graph rows) (owner : Fin graph.nodeCount) :
    ∀ reference ∈ guardReferences graph rows owner,
      StoredReference (packetHeap width n rows rawRoots) n (packetHeap width n rows rawRoots).size reference := by
  intro reference member
  obtain ⟨position, equal⟩ := List.mem_ofFn.mp member
  subst reference
  exact guard_stored graph rows rawRoots rowsMatch owner position true

/-- All declared occurrences remain separate query positions. -/
theorem rootReferenceCones_length (graph : DAG n) (rows : List Row) (rawRoots : List Nat)
    (rowsMatch : RowsMatch graph rows) :
    (rootReferenceCones graph rows rawRoots rowsMatch).length = graph.roots.length := by
  simp [rootReferenceCones]


/-- Signing changes only polarity and therefore preserves the fetched address. -/
theorem ownReferences_stored (graph : DAG n) (rows : List Row) (rawRoots : List Nat)
    (rowsMatch : RowsMatch graph rows) (owner : Fin graph.nodeCount)
    (incoming : Reference (n + graph.nodeCount))
    (incomingStored : StoredReference (packetHeap width n rows rawRoots) n
      (packetHeap width n rows rawRoots).size incoming) :
    ∀ clause ∈ ownReferences graph rows rowsMatch owner incoming, ∀ reference ∈ clause,
      StoredReference (packetHeap width n rows rawRoots) n (packetHeap width n rows rawRoots).size reference := by
  have childrenStored := childReferences_stored (width := width) graph rows rawRoots rowsMatch owner
  have guardsStored := guardReferences_stored (width := width) graph rows rawRoots rowsMatch owner
  have headStored : StoredReference (packetHeap width n rows rawRoots) n
      (packetHeap width n rows rawRoots).size (headReference graph owner incoming) := by
    cases equation : graph.node owner with
    | input channel =>
        simpa only [headReference, equation] using input_stored (width := width)
          graph rows rawRoots rowsMatch owner channel equation false
    | zero => simpa only [headReference, equation] using incomingStored
    | liveAnd left right => simpa only [headReference, equation] using incomingStored
    | disj children => simpa only [headReference, equation] using incomingStored
    | guard child labels => simpa only [headReference, equation] using incomingStored
  have signedStored : ∀ reference : Reference (n + graph.nodeCount), StoredReference (packetHeap width n rows rawRoots) n
      (packetHeap width n rows rawRoots).size reference → ∀ polarity,
      StoredReference (packetHeap width n rows rawRoots) n
        (packetHeap width n rows rawRoots).size (signed reference polarity) := by
    intro reference stored polarity
    exact signed_stored reference polarity stored
  intro clause clauseMember reference referenceMember
  unfold ownReferences referenceClauses at clauseMember
  split at clauseMember <;>
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
      List.mem_map, List.mem_append] at clauseMember referenceMember <;> aesop

/-- The generated clauses have exactly the original signed coordinates. -/
theorem ownReferences_exact (graph : DAG n) (rows : List Row)
    (rowsMatch : RowsMatch graph rows) (owner : Fin graph.nodeCount)
    (incoming : Reference (n + graph.nodeCount))
    (incomingCoordinate : incoming.coordinate.val = n + owner.val) :
    (ownReferences graph rows rowsMatch owner incoming).map (List.map sourceLiteralOf) =
      (graph.nodeClauses owner).map (List.map (sourceLiteral graph)) := by
  let row := rows[owner.val]'(by rw [rowsMatch.length_eq]; exact owner.isLt)
  have rowMatch : row.Matches (graph.node owner) := rowsMatch.node owner
  have headCoordinate : row.tag = 1 → (headReference graph owner incoming).coordinate.val = row.head := by
    intro tag
    cases equation : graph.node owner <;>
      simp_all [Row.Matches, headReference, inputReference, channelReference]
  have childCoordinates : (childReferences graph rows owner).map (fun reference => reference.coordinate.val) =
      row.children.map (fun child => n + child) := by
    rw [childReferences, List.map_ofFn]
    change (List.ofFn fun position : Fin (graph.node owner).children.length =>
      n + ((graph.node owner).children.get position).val) = _
    simp only [List.get_eq_getElem]
    rw [List.ofFn_getElem_eq_map (graph.node owner).children (fun child : Fin owner.val => n + child.val)]
    rw [rowMatch.2.2.1]
    simp only [List.map_map, Function.comp_def]
  have guardCoordinates : (guardReferences graph rows owner).map (fun reference => reference.coordinate.val) = row.guards := by
    rw [guardReferences, List.map_ofFn]
    change (List.ofFn fun position : Fin (graph.node owner).guardLabels.length =>
      ((graph.node owner).guardLabels.get position).val) = _
    simp only [List.get_eq_getElem]
    rw [List.ofFn_getElem_eq_map]
    exact rowMatch.2.2.2.symm
  exact (referenceClauses_exact n owner.val row incoming (headReference graph owner incoming)
    (childReferences graph rows owner) (guardReferences graph rows owner)
    incomingCoordinate headCoordinate childCoordinates guardCoordinates).trans
      (rowClauses_exact graph owner row rowMatch)


/-- Clause occurrence storage is positional and retains repeated addresses. -/
def ReferencesStored (heap : Array (Word width)) (channels sourceEnd : Nat)
    (clauses : List (List (Reference ambient))) : Prop :=
  ∀ clause ∈ clauses, ∀ reference ∈ clause, StoredReference heap channels sourceEnd reference

theorem ReferencesStored.append {heap : Array (Word width)} {channels sourceEnd : Nat}
    {first second : List (List (Reference ambient))}
    (before : ReferencesStored heap channels sourceEnd first)
    (after : ReferencesStored heap channels sourceEnd second) :
    ReferencesStored heap channels sourceEnd (first ++ second) := by
  intro clause member reference contained
  rcases List.mem_append.mp member with left | right
  · exact before clause left reference contained
  · exact after clause right reference contained

/-- Each recursive incoming reference is the child's original stream word. -/
theorem referenceCone_stored (graph : DAG n) (rows : List Row) (rawRoots : List Nat)
    (rowsMatch : RowsMatch graph rows) :
    ∀ (owner : Fin graph.nodeCount) (incoming : Reference (n + graph.nodeCount))
      (tail : List (List (Reference (n + graph.nodeCount)))),
    StoredReference (packetHeap width n rows rawRoots) n (packetHeap width n rows rawRoots).size incoming →
    ReferencesStored (packetHeap width n rows rawRoots) n (packetHeap width n rows rawRoots).size tail →
    ReferencesStored (packetHeap width n rows rawRoots) n (packetHeap width n rows rawRoots).size
      (referenceCone graph rows rowsMatch owner incoming tail) := by
  have claim : ∀ rank, ∀ owner : Fin graph.nodeCount, owner.val = rank →
      ∀ incoming tail,
      StoredReference (packetHeap width n rows rawRoots) n (packetHeap width n rows rawRoots).size incoming →
      ReferencesStored (packetHeap width n rows rawRoots) n (packetHeap width n rows rawRoots).size tail →
      ReferencesStored (packetHeap width n rows rawRoots) n (packetHeap width n rows rawRoots).size
        (referenceCone graph rows rowsMatch owner incoming tail) := by
    intro rank
    induction rank using Nat.strong_induction_on with
    | h rank ih =>
      intro owner ownerRank incoming tail incomingStored tailStored
      rw [referenceCone.eq_def]
      apply ReferencesStored.append
      · exact ownReferences_stored graph rows rawRoots rowsMatch owner incoming incomingStored
      · have foldStored : ∀ positions : List (Fin (graph.node owner).children.length),
            ∀ acc, ReferencesStored (packetHeap width n rows rawRoots) n (packetHeap width n rows rawRoots).size acc →
            ReferencesStored (packetHeap width n rows rawRoots) n (packetHeap width n rows rawRoots).size
              (positions.foldr (fun position rest => referenceCone graph rows rowsMatch
                (graph.childIndex owner ((graph.node owner).children.get position))
                (childReference graph rows owner position false) rest) acc) := by
          intro positions
          induction positions with
          | nil => intro acc stored; exact stored
          | cons position positions foldIH =>
              intro acc stored
              simp only [List.foldr_cons]
              exact ih _ (by have earlier := graph.childIndex_lt owner ((graph.node owner).children.get position); omega)
                _ rfl _ _ (child_stored graph rows rawRoots rowsMatch owner position false)
                (foldIH acc stored)
        exact foldStored _ tail tailStored
  intro owner incoming tail incomingStored tailStored
  exact claim owner.val owner rfl incoming tail incomingStored tailStored

theorem rootReferenceCones_stored (graph : DAG n) (rows : List Row) (rawRoots : List Nat)
    (rowsMatch : RowsMatch graph rows) (rootMatches : RootsMatch graph rawRoots) :
    ∀ query ∈ rootReferenceCones graph rows rawRoots rowsMatch,
      ReferencesStored (packetHeap width n rows rawRoots) n (packetHeap width n rows rawRoots).size query := by
  intro query member
  obtain ⟨position, equal⟩ := List.mem_ofFn.mp member
  subst query
  exact referenceCone_stored graph rows rawRoots rowsMatch _ _ []
    (root_stored graph rows rawRoots rootMatches position false)
    (by intro clause member; simp at member)

private theorem map_foldr {A B C : Type} (items : List A) (initial : List B)
    (transform : A → List B → List B) (target : A → List C → List C) (encode : B → C)
    (agrees : ∀ item acc, (transform item acc).map encode = target item (acc.map encode)) :
    (items.foldr transform initial).map encode = items.foldr target (initial.map encode) := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
      simp only [List.foldr_cons]
      rw [agrees, ih]

/-- Source-coordinate projection agrees with the exact typed original cone. -/
theorem referenceCone_exact (graph : DAG n) (rows : List Row) (rowsMatch : RowsMatch graph rows) :
    ∀ (owner : Fin graph.nodeCount) (incoming : Reference (n + graph.nodeCount))
      (tail : List (List (Reference (n + graph.nodeCount)))),
    incoming.coordinate.val = n + owner.val →
    (referenceCone graph rows rowsMatch owner incoming tail).map (List.map sourceLiteralOf) =
      typedCone graph owner (tail.map (List.map sourceLiteralOf)) := by
  have claim : ∀ rank, ∀ owner : Fin graph.nodeCount, owner.val = rank →
      ∀ incoming tail, incoming.coordinate.val = n + owner.val →
      (referenceCone graph rows rowsMatch owner incoming tail).map (List.map sourceLiteralOf) =
        typedCone graph owner (tail.map (List.map sourceLiteralOf)) := by
    intro rank
    induction rank using Nat.strong_induction_on with
    | h rank ih =>
      intro owner ownerRank incoming tail incomingCoordinate
      rw [referenceCone.eq_def, typedCone.eq_def, List.map_append,
        ownReferences_exact graph rows rowsMatch owner incoming incomingCoordinate]
      apply congrArg (List.append _)
      rw [map_foldr _ _ _ _ _ (by
        intro position acc
        exact ih _ (by have earlier := graph.childIndex_lt owner ((graph.node owner).children.get position); omega)
          _ rfl _ _ (by simp [childReference, nodeReference]))]
      rw [← List.foldr_map]
      have children : (List.finRange (graph.node owner).children.length).map
          (fun position => (graph.node owner).children.get position) = (graph.node owner).children := by
        rw [← List.ofFn_eq_map]
        simp only [List.get_eq_getElem]
        simpa using
          List.ofFn_getElem_eq_map (graph.node owner).children (fun child => child)
      have childIndices := congrArg (List.map (graph.childIndex owner)) children
      simp only [List.map_map, Function.comp_def] at childIndices
      rw [childIndices, List.foldr_map]
  intro owner incoming tail incomingCoordinate
  exact claim owner.val owner rfl incoming tail incomingCoordinate


/-- All original declared root occurrences produce their own exact cone query. -/
theorem rootReferenceCones_exact (graph : DAG n) (rows : List Row) (rawRoots : List Nat)
    (rowsMatch : RowsMatch graph rows) :
    (rootReferenceCones graph rows rawRoots rowsMatch).map (List.map (List.map sourceLiteralOf)) =
      graph.roots.map (fun owner => typedCone graph owner []) := by
  rw [rootReferenceCones, List.map_ofFn]
  have individual : (List.ofFn fun position : Fin graph.roots.length =>
      (referenceCone graph rows rowsMatch (graph.roots.get position)
        (rootReference graph rows rawRoots position false) []).map (List.map sourceLiteralOf)) =
      List.ofFn fun position : Fin graph.roots.length => typedCone graph (graph.roots.get position) [] := by
    apply congrArg List.ofFn
    funext position
    simpa only [List.map_nil] using referenceCone_exact graph rows rowsMatch _ _ []
      (by simp [rootReference, nodeReference])
  simp only [Function.comp_def]
  rw [individual]
  simp only [List.get_eq_getElem]
  exact List.ofFn_getElem_eq_map graph.roots (fun owner => typedCone graph owner [])

private theorem foldr_blocks (items : List α) (blocks : α → List β) (tail : List β) :
    items.foldr (fun item rest => blocks item ++ rest) tail = items.flatMap blocks ++ tail := by
  induction items with
  | nil => rfl
  | cons item rest ih => simp only [List.foldr_cons, List.flatMap_cons, ih, List.append_assoc]

/-- The source cone consists of one original row block for each actual visit. -/
theorem typedCone_visits (graph : DAG n) :
    ∀ owner tail, typedCone graph owner tail =
      (ForestNodeVisits.walkNodes graph owner).flatMap
        (fun node => (graph.nodeClauses node).map (List.map (sourceLiteral graph))) ++ tail := by
  have claim : ∀ rank, ∀ owner : Fin graph.nodeCount, owner.val = rank → ∀ tail,
      typedCone graph owner tail =
        (ForestNodeVisits.walkNodes graph owner).flatMap
          (fun node => (graph.nodeClauses node).map (List.map (sourceLiteral graph))) ++ tail := by
    intro rank
    induction rank using Nat.strong_induction_on with
    | h rank ih =>
      intro owner ownerRank tail
      rw [typedCone.eq_def, ForestNodeVisits.walkNodes.eq_def, List.flatMap_cons,
        List.flatMap_assoc, List.append_assoc]
      apply congrArg (List.append _)
      have steps : (fun child acc => typedCone graph (graph.childIndex owner child) acc) =
          (fun child acc => (ForestNodeVisits.walkNodes graph (graph.childIndex owner child)).flatMap
            (fun node => (graph.nodeClauses node).map (List.map (sourceLiteral graph))) ++ acc) := by
        funext child acc
        exact ih _ (by have earlier := graph.childIndex_lt owner child; omega) _ rfl acc
      rw [steps]
      exact foldr_blocks _ _ tail
  intro owner tail
  exact claim owner.val owner rfl tail

/-- One source node contributes only its own gate rows and signed incidences. -/
theorem node_row_bound (graph : DAG n) (owner : Fin graph.nodeCount) :
    (graph.nodeClauses owner).length ≤ 2 + (graph.node owner).children.length := by
  cases gate : graph.node owner <;>
    simp [DAG.nodeClauses, gate, Gate.children]

theorem node_literal_bound (graph : DAG n) (owner : Fin graph.nodeCount) :
    (graph.nodeClauses owner).flatten.length ≤
      4 + 2 * (graph.node owner).children.length + (graph.node owner).guardLabels.length := by
  cases gate : graph.node owner <;>
    simp [DAG.nodeClauses, gate, Gate.children, Gate.guardLabels, implicationClause, positiveClause,
      List.length_flatMap, Function.comp_def] <;> omega

private theorem sum_flatMap (items : List α) (children : α → List β) (charge : β → Nat) :
    ((items.flatMap children).map charge).sum =
      (items.map fun item => ((children item).map charge).sum).sum := by
  induction items with
  | nil => rfl
  | cons item rest ih => simp only [List.flatMap_cons, List.map_append, List.sum_append,
      List.map_cons, List.sum_cons, ih]

/-- A rooted traversal is a tree of positional occurrences even when terminal
identifiers repeat; each child occurrence adds one edge and one descendant. -/
theorem walk_child_balance (graph : DAG n) :
    ∀ owner, ((ForestNodeVisits.walkNodes graph owner).map fun node =>
      (graph.node node).children.length).sum + 1 = (ForestNodeVisits.walkNodes graph owner).length := by
  have claim : ∀ rank, ∀ owner : Fin graph.nodeCount, owner.val = rank →
      ((ForestNodeVisits.walkNodes graph owner).map fun node =>
        (graph.node node).children.length).sum + 1 = (ForestNodeVisits.walkNodes graph owner).length := by
    intro rank
    induction rank using Nat.strong_induction_on with
    | h rank ih =>
      intro owner ownerRank
      have summed : ∀ items : List (Fin owner.val),
          (items.map fun child => ((ForestNodeVisits.walkNodes graph (graph.childIndex owner child)).map
            fun node => (graph.node node).children.length).sum).sum + items.length =
          (items.map fun child => (ForestNodeVisits.walkNodes graph (graph.childIndex owner child)).length).sum := by
        intro items
        induction items with
        | nil => rfl
        | cons child rest tailIH =>
          have childIH := ih (graph.childIndex owner child).val
            (by have earlier := graph.childIndex_lt owner child; omega) (graph.childIndex owner child) rfl
          simp only [List.map_cons, List.sum_cons, List.length_cons]
          omega
      rw [ForestNodeVisits.walkNodes.eq_def, List.map_cons, List.sum_cons, List.length_cons,
        List.length_flatMap, sum_flatMap]
      have total := summed (graph.node owner).children
      omega
  intro owner
  exact claim owner.val owner rfl

private theorem sum_local_bounds (items : List α) (charge edge label : α → Nat)
    (bound : ∀ item ∈ items, charge item ≤ 4 + 2 * edge item + label item) :
    (items.map charge).sum ≤ 4 * items.length + 2 * (items.map edge).sum + (items.map label).sum := by
  induction items with
  | nil => simp
  | cons item rest ih =>
      have head := bound item (by simp)
      have tail := ih (by intro item inside; exact bound item (by simp [inside]))
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      omega

private theorem sum_row_bounds (items : List α) (charge edge : α → Nat)
    (bound : ∀ item ∈ items, charge item ≤ 2 + edge item) :
    (items.map charge).sum ≤ 2 * items.length + (items.map edge).sum := by
  induction items with
  | nil => simp
  | cons item rest ih =>
      have head := bound item (by simp)
      have tail := ih (by intro item inside; exact bound item (by simp [inside]))
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      omega

/-- Exact original row charging along the positional source cone. -/
theorem typedCone_row_bound (graph : DAG n) (owner : Fin graph.nodeCount) :
    (typedCone graph owner []).length ≤ 3 * (ForestNodeVisits.walkNodes graph owner).length := by
  rw [typedCone_visits]
  simp only [List.append_nil, List.length_flatMap, List.length_map]
  have rows := sum_row_bounds (ForestNodeVisits.walkNodes graph owner)
    (fun node => (graph.nodeClauses node).length) (fun node => (graph.node node).children.length)
    (by intro node inside; exact node_row_bound graph node)
  have edges := walk_child_balance graph owner
  omega

/-- Every literal is charged to its owning visit, its child incidence or its
original guard-label occurrence; the ambient channel count is absent. -/
theorem typedCone_literal_bound (graph : DAG n) (owner : Fin graph.nodeCount) :
    (typedCone graph owner []).flatten.length ≤
      6 * (ForestNodeVisits.walkNodes graph owner).length +
        ((ForestNodeVisits.walkNodes graph owner).map fun node => (graph.node node).guardLabels.length).sum := by
  rw [typedCone_visits]
  simp only [List.append_nil, List.length_flatten]
  rw [sum_flatMap]
  have literals := sum_local_bounds (ForestNodeVisits.walkNodes graph owner)
    (fun node => (graph.nodeClauses node).flatten.length) (fun node => (graph.node node).children.length)
    (fun node => (graph.node node).guardLabels.length)
    (by intro node inside; exact node_literal_bound graph node)
  have edges := walk_child_balance graph owner
  have mapped : ∀ node : Fin graph.nodeCount,
      (((graph.nodeClauses node).map (List.map (sourceLiteral graph))).map List.length).sum =
        (graph.nodeClauses node).flatten.length := by
    intro node
    simp [List.length_flatten, List.map_map, Function.comp_def]
  simp only [mapped]
  omega

/-- Guard event schedules visit each original guard word twice. -/
theorem walk_guard_balance (graph : DAG n) (guarded : graph.Guarded) :
    ∀ owner,
      2 * ((ForestNodeVisits.walkNodes graph owner).map fun node => (graph.node node).guardLabels.length).sum =
        (ForestGuardSchedule.walkEvents graph owner).length := by
  have claim : ∀ rank, ∀ owner : Fin graph.nodeCount, owner.val = rank →
      2 * ((ForestNodeVisits.walkNodes graph owner).map fun node => (graph.node node).guardLabels.length).sum =
        (ForestGuardSchedule.walkEvents graph owner).length := by
    intro rank
    induction rank using Nat.strong_induction_on with
    | h rank ih =>
      intro owner ownerRank
      have childBalance : ∀ child : Fin owner.val,
          2 * ((ForestNodeVisits.walkNodes graph (graph.childIndex owner child)).map
            fun node => (graph.node node).guardLabels.length).sum =
              (ForestGuardSchedule.walkEvents graph (graph.childIndex owner child)).length := by
        intro child
        exact ih _ (by have earlier := graph.childIndex_lt owner child; omega) _ rfl
      rw [ForestNodeVisits.walkNodes.eq_def, List.map_cons, List.sum_cons, sum_flatMap,
        ForestGuardSchedule.walkEvents.eq_def]
      cases gate : graph.node owner with
      | zero => simp [gate, Gate.children, Gate.guardLabels]
      | input channel => simp [gate, Gate.children, Gate.guardLabels]
      | liveAnd left right =>
          have impossible := guarded owner
          simp [Gate.IsGuarded, Gate.isLiveAnd, gate] at impossible
      | guard child labels =>
          have inner := childBalance child
          simp only [Gate.guardLabels] at inner
          simp only [Gate.guardLabels, Gate.children, List.map_cons, List.map_nil,
            List.sum_cons, List.sum_nil, List.length_append, List.length_map,
            List.length_reverse]
          omega
      | disj children =>
          have summed : ∀ items : List (Fin owner.val),
              2 * (items.map fun child => ((ForestNodeVisits.walkNodes graph (graph.childIndex owner child)).map
                fun node => (graph.node node).guardLabels.length).sum).sum =
                (items.flatMap fun child => ForestGuardSchedule.walkEvents graph (graph.childIndex owner child)).length := by
            intro items
            induction items with
            | nil => simp
            | cons child rest tail =>
                have inner := childBalance child
                simp only [List.map_cons, List.sum_cons, List.flatMap_cons, List.length_append]
                omega
          simpa only [gate, Gate.children, Gate.guardLabels, List.length_nil, Nat.zero_add] using summed children
  intro owner
  exact claim owner.val owner rfl

private theorem sum_linear (items : List α) (charge visits guards : α → Nat)
    (a b : Nat) (bound : ∀ item ∈ items, charge item ≤ a * visits item + b * guards item) :
    (items.map charge).sum ≤ a * (items.map visits).sum + b * (items.map guards).sum := by
  induction items with
  | nil => simp
  | cons item rest ih =>
      have head := bound item (by simp)
      have tail := ih (by intro current present; exact bound current (by simp [present]))
      simp only [List.map_cons, List.sum_cons, Nat.mul_add]
      omega

/-- The complete input row budget invokes the forest's rooted-visit bound. -/
theorem rootReferenceCones_row_bound (graph : DAG n) (rows : List Row) (rawRoots : List Nat)
    (rowsMatch : RowsMatch graph rows) (forest : graph.FormulaForest) :
    ((rootReferenceCones graph rows rawRoots rowsMatch).map List.length).sum ≤
      3 * (graph.roots.length + graph.childIncidences) := by
  have projection := congrArg (fun queries => (queries.map List.length).sum)
    (rootReferenceCones_exact graph rows rawRoots rowsMatch)
  simp only [List.map_map, Function.comp_def, List.length_map] at projection
  rw [projection]
  have bound := sum_linear graph.roots (fun owner => (typedCone graph owner []).length)
    (fun owner => (ForestNodeVisits.walkNodes graph owner).length) (fun _ => 0) 3 0
    (by intro owner present; simpa using typedCone_row_bound graph owner)
  have visits := ForestNodeVisits.root_node_count_le graph forest
  simp only [ForestNodeVisits.rootNodes, List.length_flatMap] at visits
  simp only [Nat.zero_mul, Nat.add_zero] at bound
  omega

/-- Guard fields are charged only at their original internal occurrence. -/
theorem root_guard_sum_bound (graph : DAG n) (forest : graph.FormulaForest) :
    (graph.roots.map fun owner => ((ForestNodeVisits.walkNodes graph owner).map
      fun node => (graph.node node).guardLabels.length).sum).sum ≤ graph.guardIncidences := by
  have balance : ∀ items : List (Fin graph.nodeCount),
      2 * (items.map fun owner => ((ForestNodeVisits.walkNodes graph owner).map
        fun node => (graph.node node).guardLabels.length).sum).sum =
      (items.flatMap (ForestGuardSchedule.walkEvents graph)).length := by
    intro items
    induction items with
    | nil => simp
    | cons owner rest ih =>
        have own := walk_guard_balance graph forest.1 owner
        simp only [List.map_cons, List.sum_cons, List.flatMap_cons, List.length_append]
        omega
  have actual := balance graph.roots
  have global := ForestGuardVisits.root_event_count_le graph forest
  simp only [ForestGuardSchedule.rootEvents] at global
  omega

/-- Original signed literals retain duplicate terminal incidences. Their total
is linear in the forest edges and guard positions, not channels times roots. -/
theorem rootReferenceCones_literal_bound (graph : DAG n) (rows : List Row) (rawRoots : List Nat)
    (rowsMatch : RowsMatch graph rows) (forest : graph.FormulaForest) :
    ((rootReferenceCones graph rows rawRoots rowsMatch).map fun clauses => clauses.flatten.length).sum ≤
      6 * (graph.roots.length + graph.childIncidences) + graph.guardIncidences := by
  have projection := congrArg (fun queries => (queries.map fun clauses => clauses.flatten.length).sum)
    (rootReferenceCones_exact graph rows rawRoots rowsMatch)
  simp only [List.map_map, Function.comp_def, List.length_flatten, List.length_map] at projection
  simp only [List.length_flatten] at ⊢
  rw [projection]
  have bound := sum_linear graph.roots (fun owner => (typedCone graph owner []).flatten.length)
    (fun owner => (ForestNodeVisits.walkNodes graph owner).length)
    (fun owner => ((ForestNodeVisits.walkNodes graph owner).map fun node => (graph.node node).guardLabels.length).sum)
    6 1 (by intro owner present; simpa using typedCone_literal_bound graph owner)
  have visits := ForestNodeVisits.root_node_count_le graph forest
  simp only [ForestNodeVisits.rootNodes, List.length_flatMap] at visits
  have guards := root_guard_sum_bound graph forest
  simp only [Nat.one_mul, List.length_flatten] at bound
  omega

end Controller.Cost.ForestZeroReferenceCone
