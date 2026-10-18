module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.FoldProjection
public import Controller.NativeProof.SourceRows

@[expose] public section

/-! Balanced source-fold witnesses retain the allocator's exact input occurrence
order and original producer rows. Unary source folds carry literal identity. -/
namespace Controller.NativeProof.SourceFoldProjection
open Controller.CNF Controller.Resolution Controller.Native
open Controller.NativeProof.FoldProjection

variable {v : ℕ} {state : State v}

def mapLiteral (rename : Nat → Fin v) (literal : Literal Nat) : Literal (Fin v) :=
  (rename literal.1, literal.2)

/-- Every certificate is an original clause occurrence of the given producer. -/
structure OriginalRows (state : State v) (rename : Nat → Fin v)
    (producer : Bounded.Producer Nat) where
  row : ∀ index : Fin producer.rows.length,
    Rows.Available state (Rows.mapClause rename producer.rows[index.val])

/-- The original input formula retains every producer block in stored order. -/
def originalRows (rename : Nat → Fin v) (producers : List (Bounded.Producer Nat))
    (owner : Fin producers.length) :
    OriginalRows (initialState (relabel rename (ofClauses (producers.flatMap Bounded.Producer.rows))))
      rename producers[owner.val] where
  row index := by
    let before := (producers.take owner.val).flatMap Bounded.Producer.rows
    let after := (producers.drop (owner.val + 1)).flatMap Bounded.Producer.rows
    have split : producers = producers.take owner.val ++
        [producers[owner.val]] ++ producers.drop (owner.val + 1) := by
      calc
        _ = producers.take (owner.val + 1) ++ producers.drop (owner.val + 1) :=
          (List.take_append_drop _ _).symm
        _ = _ := by rw [List.take_succ_eq_append_getElem owner.isLt]
    have clauses : producers.flatMap Bounded.Producer.rows =
        before ++ producers[owner.val].rows ++ after := by
      conv_lhs => rw [split]
      simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, before, after]
    rw [clauses]
    exact Rows.framedRow rename before _ after index

/-- A raw-source owner supplies original full-input rows, including assertions. -/
def sourceOriginalRows (parameters : Parameters) (rename : Nat → Fin v)
    (owner : Fin (SourceController.compile parameters).entries.length) :
    OriginalRows (initialState (relabel rename (SourceController.formula parameters)))
      rename (SourceController.compile parameters).entries[owner.val].producer where
  row index := SourceRows.fullProducerRow parameters rename owner index

/-- A forest is indexed by current raw handles and its ordered original leaves.
Trees stop at input handles; they do not unfold any preceding graph producer. -/
inductive RawForest (state : State v) (rename : Nat → Fin v) :
    List (Literal Nat) → List (Literal Nat) → Type
  | nil : RawForest state rename [] []
  | cons (handle : Literal Nat) (leaves : List (Literal Nat))
      (tree : AndTree state (mapLiteral rename handle) (leaves.map (mapLiteral rename)))
      {handles restLeaves : List (Literal Nat)}
      (rest : RawForest state rename handles restLeaves) :
      RawForest state rename (handle :: handles) (leaves ++ restLeaves)

def RawForest.nodes {rename : Nat → Fin v} {handles leaves : List (Literal Nat)} :
    RawForest state rename handles leaves → Nat
  | .nil => 0
  | .cons _ _ tree rest => tree.nodes + rest.nodes

theorem RawForest.nodes_leaves {rename : Nat → Fin v} {handles leaves : List (Literal Nat)}
    (forest : RawForest state rename handles leaves) :
    forest.nodes + handles.length = leaves.length := by
  induction forest with
  | nil => rfl
  | cons handle leaves tree rest ih =>
    have treeSize := tree.nodes_leaves
    simp only [List.length_map] at treeSize
    simp only [RawForest.nodes, List.length_cons, List.length_append]
    omega

/-- Initial input occurrences are leaves even when their raw handles repeat. -/
def initialForest (rename : Nat → Fin v) (inputs : List (Literal Nat)) :
    RawForest state rename inputs inputs :=
  match inputs with
  | [] => .nil
  | input :: rest => .cons input [input] (.leaf (mapLiteral rename input)) (initialForest rename rest)

/-- A singleton carries its exact existing tree and has no alias producer. -/
def singletonTree {rename : Nat → Fin v} {handle : Literal Nat} {leaves : List (Literal Nat)}
    (forest : RawForest state rename [handle] leaves) :
    AndTree state (mapLiteral rename handle) (leaves.map (mapLiteral rename)) := by
  cases forest with
  | cons handle first tree rest =>
    cases rest
    simpa only [List.append_nil] using tree

/-- Indexed original-row supply permits no selection from propositional
membership and keeps every source block's occurrence identity. -/
def RowSupply (state : State v) (rename : Nat → Fin v)
    (producers : List (Bounded.Producer Nat)) :=
  ∀ owner : Fin producers.length, OriginalRows state rename producers[owner.val]

def tailSupply {rename : Nat → Fin v} (producer : Bounded.Producer Nat)
    (producers : List (Bounded.Producer Nat))
    (supply : RowSupply state rename (producer :: producers)) :
    RowSupply state rename producers :=
  fun owner => supply ⟨owner.val + 1, by simpa only [List.length_cons] using Nat.succ_lt_succ owner.isLt⟩

/-- The three binary conjunction rows are exact original producer occurrences. -/
def binaryRows {rename : Nat → Fin v} (left right output : Literal Nat)
    (rows : OriginalRows state rename ⟨output, .and [left, right]⟩) :
    BinaryAndRows state (mapLiteral rename left) (mapLiteral rename right) (mapLiteral rename output) where
  leftRow := rows.row ⟨0, by change 0 < 3; decide⟩
  rightRow := rows.row ⟨1, by change 1 < 3; decide⟩
  longRow := rows.row ⟨2, by change 2 < 3; decide⟩

/-- Every adjacent pair becomes one tree node supplied by its actual original
producer. The singleton case carries the existing tree without an alias row. -/
def pairLayerForest {rename : Nat → Fin v} {handles leaves : List (Literal Nat)}
    (forest : RawForest state rename handles leaves) (lastID : Nat)
    (supply : RowSupply state rename
      (SourceSerialFold.pairLayer .conjunction lastID handles).producers) :
    RawForest state rename (SourceSerialFold.pairLayer .conjunction lastID handles).handles leaves := by
  match forest with
  | .nil => exact .nil
  | .cons left leftLeaves leftTree rest =>
    match rest with
    | .nil =>
      simpa only [SourceSerialFold.pairLayer, List.append_nil] using
        RawForest.cons left leftLeaves leftTree RawForest.nil
    | @RawForest.cons _ _ _ right rightLeaves rightTree tailHandles tailLeaves tail =>
      let producer : Bounded.Producer Nat := ⟨(lastID + 1, true), .and [left, right]⟩
      let restProducers := (SourceSerialFold.pairLayer .conjunction (lastID + 1) tailHandles).producers
      change RowSupply state rename (producer :: restProducers) at supply
      let original : OriginalRows state rename producer := supply ⟨0, by simp [List.length_cons]⟩
      let node : AndTree state (mapLiteral rename (lastID + 1, true))
          ((leftLeaves ++ rightLeaves).map (mapLiteral rename)) := by
        simpa only [List.map_append] using
          AndTree.node leftTree rightTree (mapLiteral rename (lastID + 1, true))
            (binaryRows left right (lastID + 1, true) original)
      let next := pairLayerForest tail (lastID + 1) (tailSupply producer restProducers supply)
      simpa only [SourceSerialFold.pairLayer, List.map_append, List.append_assoc] using
        RawForest.cons (lastID + 1, true) (leftLeaves ++ rightLeaves) node next

/-- Pairing charges exactly the newly represented original producer blocks. -/
theorem pairLayerForest_nodes {rename : Nat → Fin v} {handles leaves : List (Literal Nat)}
    (forest : RawForest state rename handles leaves) (lastID : Nat)
    (supply : RowSupply state rename
      (SourceSerialFold.pairLayer .conjunction lastID handles).producers) :
    (pairLayerForest forest lastID supply).nodes =
      forest.nodes + (SourceSerialFold.pairLayer .conjunction lastID handles).producers.length := by
  have oldSize := forest.nodes_leaves
  have newSize := (pairLayerForest forest lastID supply).nodes_leaves
  have handleCount := SourceSerialFold.pairLayer_length .conjunction lastID handles
  have producerCount := SourceSerialFold.pairLayer_producers .conjunction lastID handles
  omega

def prefixSupply {rename : Nat → Fin v} (before after : List (Bounded.Producer Nat))
    (supply : RowSupply state rename (before ++ after)) : RowSupply state rename before := by
  intro owner
  let index : Fin (before ++ after).length := ⟨owner.val, by simp only [List.length_append]; omega⟩
  simpa only [index, List.getElem_append_left owner.isLt] using supply index

def suffixSupply {rename : Nat → Fin v} (before after : List (Bounded.Producer Nat))
    (supply : RowSupply state rename (before ++ after)) : RowSupply state rename after := by
  intro owner
  let index : Fin (before ++ after).length := ⟨before.length + owner.val, by
    simp only [List.length_append]; omega⟩
  simpa only [index, List.getElem_append_right (by omega : before.length ≤ before.length + owner.val),
    Nat.add_sub_cancel_left] using supply index

/-- The balanced allocator contracts a nonempty forest to one root tree. Its
recursive row supply skips exactly the preceding layer's stored producers. -/
def allocateForest {rename : Nat → Fin v} {handles leaves : List (Literal Nat)}
    (forest : RawForest state rename handles leaves) (lastID : Nat) (nonempty : handles ≠ [])
    (supply : RowSupply state rename (SourceSerialFold.allocate .conjunction lastID handles).producers) :
    AndTree state (mapLiteral rename (SourceSerialFold.allocate .conjunction lastID handles).output)
      (leaves.map (mapLiteral rename)) := by
  match forest with
  | .nil => exact False.elim (nonempty rfl)
  | .cons left leftLeaves leftTree rest =>
    match rest with
    | .nil =>
      simpa only [SourceSerialFold.allocate_unary, List.append_nil] using leftTree
    | @RawForest.cons _ _ _ right rightLeaves rightTree tailHandles tailLeaves tail =>
      let layer := SourceSerialFold.pairLayer .conjunction lastID (left :: right :: tailHandles)
      let remaining := SourceSerialFold.allocate .conjunction layer.nextID layer.handles
      have expansion : SourceSerialFold.allocate .conjunction lastID (left :: right :: tailHandles) =
          { output := remaining.output, producers := layer.producers ++ remaining.producers,
            nextID := remaining.nextID } := by
        rw [SourceSerialFold.allocate]
      have producerEquality :
          (SourceSerialFold.allocate .conjunction lastID (left :: right :: tailHandles)).producers =
            layer.producers ++ remaining.producers :=
        congrArg SourceSerialFold.Result.producers expansion
      let normalizedSupply : RowSupply state rename (layer.producers ++ remaining.producers) :=
        Eq.mp (congrArg (RowSupply state rename) producerEquality) supply
      let paired := pairLayerForest
        (RawForest.cons left leftLeaves leftTree (RawForest.cons right rightLeaves rightTree tail))
        lastID (prefixSupply layer.producers remaining.producers normalizedSupply)
      have layerNonempty : layer.handles ≠ [] := by
        have size := SourceSerialFold.pairLayer_length .conjunction lastID (left :: right :: tailHandles)
        intro empty
        have zero : layer.handles.length = 0 := by rw [empty]; rfl
        simp only [List.length_cons] at size
        change layer.handles.length = _ at size
        omega
      let result := allocateForest paired layer.nextID layerNonempty
        (suffixSupply layer.producers remaining.producers normalizedSupply)
      rw [expansion]
      exact result
termination_by handles.length
decreasing_by
  have size := SourceSerialFold.pairLayer_length .conjunction lastID (left :: right :: tailHandles)
  simp only [List.length_cons] at size ⊢
  change (SourceSerialFold.pairLayer .conjunction lastID (left :: right :: tailHandles)).handles.length < _
  omega

/-- The complete nonempty raw fold is built from its own exact original input
formula, with no assumed derived implication or precomputed tree. -/
def rawAndTree (rename : Nat → Fin v) (lastID : Nat) (inputs : List (Literal Nat))
    (nonempty : inputs ≠ []) :
    AndTree (initialState (relabel rename (SourceSerialFold.formula
      (SourceSerialFold.allocate .conjunction lastID inputs))))
      (mapLiteral rename (SourceSerialFold.allocate .conjunction lastID inputs).output)
      (inputs.map (mapLiteral rename)) :=
  allocateForest (initialForest rename inputs) lastID nonempty
    (originalRows rename (SourceSerialFold.allocate .conjunction lastID inputs).producers)

theorem rawAndTree_nodes (rename : Nat → Fin v) (lastID : Nat) (inputs : List (Literal Nat))
    (nonempty : inputs ≠ []) :
    (rawAndTree rename lastID inputs nonempty).nodes =
      (SourceSerialFold.allocate .conjunction lastID inputs).producers.length := by
  have nodes := (rawAndTree rename lastID inputs nonempty).nodes_leaves
  have producers := SourceSerialFold.allocate_producers .conjunction lastID inputs
  have positive : inputs.length ≠ 0 := by
    intro zero
    exact nonempty (List.length_eq_zero_iff.mp zero)
  simp only [List.length_map] at nodes
  rw [ite_eq_right positive] at producers
  omega

/-- An explicit owner map binds the allocated producers to stored source
entries. The equality concerns producer data, never an assumed derived row. -/
def sourceSupply (parameters : Parameters) (rename : Nat → Fin v)
    (producers : List (Bounded.Producer Nat))
    (owners : Fin producers.length → Fin (SourceController.compile parameters).entries.length)
    (stored : ∀ index, (SourceController.compile parameters).entries[(owners index).val].producer = producers[index.val]) :
    RowSupply (initialState (relabel rename (SourceController.formula parameters))) rename producers :=
  fun index => stored index ▸ sourceOriginalRows parameters rename (owners index)

def sourceAndTree (parameters : Parameters) (rename : Nat → Fin v)
    (lastID : Nat) (inputs : List (Literal Nat)) (nonempty : inputs ≠ [])
    (owners : Fin (SourceSerialFold.allocate .conjunction lastID inputs).producers.length →
      Fin (SourceController.compile parameters).entries.length)
    (stored : ∀ index, (SourceController.compile parameters).entries[(owners index).val].producer =
      (SourceSerialFold.allocate .conjunction lastID inputs).producers[index.val]) :
    AndTree (initialState (relabel rename (SourceController.formula parameters)))
      (mapLiteral rename (SourceSerialFold.allocate .conjunction lastID inputs).output)
      (inputs.map (mapLiteral rename)) :=
  allocateForest (initialForest rename inputs) lastID nonempty
    (sourceSupply parameters rename _ owners stored)

/-- Empty conjunction allocation supplies its one actual unit occurrence. -/
def rawEmptyAnd (rename : Nat → Fin v) (lastID : Nat) :
    CompleteProjection (initialState (relabel rename (SourceSerialFold.formula
      (SourceSerialFold.allocate .conjunction lastID []))))
      ((Gate.and []).clauses (mapLiteral rename (lastID + 1, true))) 0 := by
  rw [SourceSerialFold.allocate_empty]
  let producer : Bounded.Producer Nat := ⟨(lastID + 1, true), .and []⟩
  let rows := originalRows rename [producer] ⟨0, by change 0 < 1; decide⟩
  exact emptyAndProjection (rows.row ⟨0, by change 0 < 1; decide⟩)

/-- OR folds are traversed as AND trees after literal polarity duality.
Every original OR producer retains its original clause IDs. -/
def dualLiteral (rename : Nat → Fin v) (literal : Literal Nat) : Literal (Fin v) :=
  negate (mapLiteral rename literal)

inductive RawOrForest (state : State v) (rename : Nat → Fin v) :
    List (Literal Nat) → List (Literal Nat) → Type
  | nil : RawOrForest state rename [] []
  | cons (handle : Literal Nat) (leaves : List (Literal Nat))
      (tree : AndTree state (dualLiteral rename handle) (leaves.map (dualLiteral rename)))
      {handles restLeaves : List (Literal Nat)}
      (rest : RawOrForest state rename handles restLeaves) :
      RawOrForest state rename (handle :: handles) (leaves ++ restLeaves)

def RawOrForest.nodes {rename : Nat → Fin v} {handles leaves : List (Literal Nat)} :
    RawOrForest state rename handles leaves → Nat
  | .nil => 0
  | .cons _ _ tree rest => tree.nodes + rest.nodes

theorem RawOrForest.nodes_leaves {rename : Nat → Fin v} {handles leaves : List (Literal Nat)}
    (forest : RawOrForest state rename handles leaves) :
    forest.nodes + handles.length = leaves.length := by
  induction forest with
  | nil => rfl
  | cons handle leaves tree rest ih =>
    have treeSize := tree.nodes_leaves
    simp only [List.length_map] at treeSize
    simp only [RawOrForest.nodes, List.length_cons, List.length_append]
    omega

/-- Initial input occurrences are leaves even when their raw handles repeat. -/
def initialOrForest (rename : Nat → Fin v) (inputs : List (Literal Nat)) :
    RawOrForest state rename inputs inputs :=
  match inputs with
  | [] => .nil
  | input :: rest => .cons input [input] (.leaf (dualLiteral rename input)) (initialOrForest rename rest)

/-- A singleton carries its exact existing tree and has no alias producer. -/
def singletonOrTree {rename : Nat → Fin v} {handle : Literal Nat} {leaves : List (Literal Nat)}
    (forest : RawOrForest state rename [handle] leaves) :
    AndTree state (dualLiteral rename handle) (leaves.map (dualLiteral rename)) := by
  cases forest with
  | cons handle first tree rest =>
    cases rest
    simpa only [List.append_nil] using tree

def binaryOrRows {rename : Nat → Fin v} (left right output : Literal Nat)
    (rows : OriginalRows state rename ⟨output, .or [left, right]⟩) :
    BinaryAndRows state (dualLiteral rename left) (dualLiteral rename right) (dualLiteral rename output) :=
  (show BinaryOrRows state (mapLiteral rename left) (mapLiteral rename right) (mapLiteral rename output) from
    { leftRow := rows.row ⟨0, by change 0 < 3; decide⟩
      rightRow := rows.row ⟨1, by change 1 < 3; decide⟩
      longRow := rows.row ⟨2, by change 2 < 3; decide⟩ }).dual

/-- Every adjacent pair becomes one tree node supplied by its actual original
producer. The singleton case carries the existing tree without an alias row. -/
def pairLayerOrForest {rename : Nat → Fin v} {handles leaves : List (Literal Nat)}
    (forest : RawOrForest state rename handles leaves) (lastID : Nat)
    (supply : RowSupply state rename
      (SourceSerialFold.pairLayer .disjunction lastID handles).producers) :
    RawOrForest state rename (SourceSerialFold.pairLayer .disjunction lastID handles).handles leaves := by
  match forest with
  | .nil => exact .nil
  | .cons left leftLeaves leftTree rest =>
    match rest with
    | .nil =>
      simpa only [SourceSerialFold.pairLayer, List.append_nil] using
        RawOrForest.cons left leftLeaves leftTree RawOrForest.nil
    | @RawOrForest.cons _ _ _ right rightLeaves rightTree tailHandles tailLeaves tail =>
      let producer : Bounded.Producer Nat := ⟨(lastID + 1, true), .or [left, right]⟩
      let restProducers := (SourceSerialFold.pairLayer .disjunction (lastID + 1) tailHandles).producers
      change RowSupply state rename (producer :: restProducers) at supply
      let original : OriginalRows state rename producer := supply ⟨0, by simp [List.length_cons]⟩
      let node : AndTree state (dualLiteral rename (lastID + 1, true))
          ((leftLeaves ++ rightLeaves).map (dualLiteral rename)) := by
        simpa only [List.map_append] using
          AndTree.node leftTree rightTree (dualLiteral rename (lastID + 1, true))
            (binaryOrRows left right (lastID + 1, true) original)
      let next := pairLayerOrForest tail (lastID + 1) (tailSupply producer restProducers supply)
      simpa only [SourceSerialFold.pairLayer, List.map_append, List.append_assoc] using
        RawOrForest.cons (lastID + 1, true) (leftLeaves ++ rightLeaves) node next

/-- Pairing charges exactly the newly represented original producer blocks. -/
theorem pairLayerOrForest_nodes {rename : Nat → Fin v} {handles leaves : List (Literal Nat)}
    (forest : RawOrForest state rename handles leaves) (lastID : Nat)
    (supply : RowSupply state rename
      (SourceSerialFold.pairLayer .disjunction lastID handles).producers) :
    (pairLayerOrForest forest lastID supply).nodes =
      forest.nodes + (SourceSerialFold.pairLayer .disjunction lastID handles).producers.length := by
  have oldSize := forest.nodes_leaves
  have newSize := (pairLayerOrForest forest lastID supply).nodes_leaves
  have handleCount := SourceSerialFold.pairLayer_length .disjunction lastID handles
  have producerCount := SourceSerialFold.pairLayer_producers .disjunction lastID handles
  omega

/-- The balanced allocator contracts a nonempty forest to one root tree. Its
recursive row supply skips exactly the preceding layer's stored producers. -/
def allocateOrForest {rename : Nat → Fin v} {handles leaves : List (Literal Nat)}
    (forest : RawOrForest state rename handles leaves) (lastID : Nat) (nonempty : handles ≠ [])
    (supply : RowSupply state rename (SourceSerialFold.allocate .disjunction lastID handles).producers) :
    AndTree state (dualLiteral rename (SourceSerialFold.allocate .disjunction lastID handles).output)
      (leaves.map (dualLiteral rename)) := by
  match forest with
  | .nil => exact False.elim (nonempty rfl)
  | .cons left leftLeaves leftTree rest =>
    match rest with
    | .nil =>
      simpa only [SourceSerialFold.allocate_unary, List.append_nil] using leftTree
    | @RawOrForest.cons _ _ _ right rightLeaves rightTree tailHandles tailLeaves tail =>
      let layer := SourceSerialFold.pairLayer .disjunction lastID (left :: right :: tailHandles)
      let remaining := SourceSerialFold.allocate .disjunction layer.nextID layer.handles
      have expansion : SourceSerialFold.allocate .disjunction lastID (left :: right :: tailHandles) =
          { output := remaining.output, producers := layer.producers ++ remaining.producers,
            nextID := remaining.nextID } := by
        rw [SourceSerialFold.allocate]
      have producerEquality :
          (SourceSerialFold.allocate .disjunction lastID (left :: right :: tailHandles)).producers =
            layer.producers ++ remaining.producers :=
        congrArg SourceSerialFold.Result.producers expansion
      let normalizedSupply : RowSupply state rename (layer.producers ++ remaining.producers) :=
        Eq.mp (congrArg (RowSupply state rename) producerEquality) supply
      let paired := pairLayerOrForest
        (RawOrForest.cons left leftLeaves leftTree (RawOrForest.cons right rightLeaves rightTree tail))
        lastID (prefixSupply layer.producers remaining.producers normalizedSupply)
      have layerNonempty : layer.handles ≠ [] := by
        have size := SourceSerialFold.pairLayer_length .disjunction lastID (left :: right :: tailHandles)
        intro empty
        have zero : layer.handles.length = 0 := by rw [empty]; rfl
        simp only [List.length_cons] at size
        change layer.handles.length = _ at size
        omega
      let result := allocateOrForest paired layer.nextID layerNonempty
        (suffixSupply layer.producers remaining.producers normalizedSupply)
      rw [expansion]
      exact result
termination_by handles.length
decreasing_by
  have size := SourceSerialFold.pairLayer_length .disjunction lastID (left :: right :: tailHandles)
  simp only [List.length_cons] at size ⊢
  change (SourceSerialFold.pairLayer .disjunction lastID (left :: right :: tailHandles)).handles.length < _
  omega

/-- The complete nonempty raw fold is built from its own exact original input
formula, with no assumed derived implication or precomputed tree. -/
def rawOrTree (rename : Nat → Fin v) (lastID : Nat) (inputs : List (Literal Nat))
    (nonempty : inputs ≠ []) :
    AndTree (initialState (relabel rename (SourceSerialFold.formula
      (SourceSerialFold.allocate .disjunction lastID inputs))))
      (dualLiteral rename (SourceSerialFold.allocate .disjunction lastID inputs).output)
      (inputs.map (dualLiteral rename)) :=
  allocateOrForest (initialOrForest rename inputs) lastID nonempty
    (originalRows rename (SourceSerialFold.allocate .disjunction lastID inputs).producers)

theorem rawOrTree_nodes (rename : Nat → Fin v) (lastID : Nat) (inputs : List (Literal Nat))
    (nonempty : inputs ≠ []) :
    (rawOrTree rename lastID inputs nonempty).nodes =
      (SourceSerialFold.allocate .disjunction lastID inputs).producers.length := by
  have nodes := (rawOrTree rename lastID inputs nonempty).nodes_leaves
  have producers := SourceSerialFold.allocate_producers .disjunction lastID inputs
  have positive : inputs.length ≠ 0 := by
    intro zero
    exact nonempty (List.length_eq_zero_iff.mp zero)
  simp only [List.length_map] at nodes
  rw [ite_eq_right positive] at producers
  omega

def sourceOrTree (parameters : Parameters) (rename : Nat → Fin v)
    (lastID : Nat) (inputs : List (Literal Nat)) (nonempty : inputs ≠ [])
    (owners : Fin (SourceSerialFold.allocate .disjunction lastID inputs).producers.length →
      Fin (SourceController.compile parameters).entries.length)
    (stored : ∀ index, (SourceController.compile parameters).entries[(owners index).val].producer =
      (SourceSerialFold.allocate .disjunction lastID inputs).producers[index.val]) :
    AndTree (initialState (relabel rename (SourceController.formula parameters)))
      (dualLiteral rename (SourceSerialFold.allocate .disjunction lastID inputs).output)
      (inputs.map (dualLiteral rename)) :=
  allocateOrForest (initialOrForest rename inputs) lastID nonempty
    (sourceSupply parameters rename _ owners stored)

def rawEmptyOr (rename : Nat → Fin v) (lastID : Nat) :
    CompleteProjection (initialState (relabel rename (SourceSerialFold.formula
      (SourceSerialFold.allocate .disjunction lastID []))))
      ((Gate.or []).clauses (mapLiteral rename (lastID + 1, true))) 0 := by
  rw [SourceSerialFold.allocate_empty]
  let producer : Bounded.Producer Nat := ⟨(lastID + 1, true), .or []⟩
  let rows := originalRows rename [producer] ⟨0, by change 0 < 1; decide⟩
  exact emptyOrProjection (rows.row ⟨0, by change 0 < 1; decide⟩)


/-! Original XOR rows for the replacement observations. The occurrence is
computed from the actual compiler cursor, including retained old observations. -/

private theorem differenceFold_entries {parameters : Parameters}
    (items : List (Fin parameters.decoder.roots.length))
    (cursor : SourceController.Cursor parameters) :
    ∃ suffix, (items.foldl (SourceController.newDifferenceStep parameters) cursor).entries =
      cursor.entries ++ suffix := by
  induction items generalizing cursor with
  | nil => exact ⟨[], by simp⟩
  | cons index rest ih =>
      obtain ⟨suffix, equality⟩ := ih (SourceController.newDifferenceStep parameters cursor index)
      refine ⟨⟨.native (.internal (.difference index)),
        ⟨(cursor.lastID + 1, true), .xor
          (cursor.slots (.internal (.decoder .healthy (parameters.decoder.roots.get index))))
          (cursor.slots (.internal (.decoder .faulty (parameters.decoder.roots.get index))))⟩⟩ :: suffix, ?_⟩
      simpa only [List.foldl_cons, SourceController.newDifferenceStep,
        SourceController.Cursor.emitNative, SourceController.Cursor.emit,
        SourceController.Cursor.assign, List.append_assoc, List.singleton_append] using equality

private theorem differenceFold_slot {parameters : Parameters}
    (items : List (Fin parameters.decoder.roots.length))
    (cursor : SourceController.Cursor parameters) (query : Variable parameters)
    (different : ∀ index ∈ items, query ≠ .internal (.difference index)) :
    (items.foldl (SourceController.newDifferenceStep parameters) cursor).slots query = cursor.slots query := by
  induction items generalizing cursor with
  | nil => rfl
  | cons index rest ih =>
      have head : query ≠ .internal (.difference index) := different index (by simp)
      have tail : ∀ next ∈ rest, query ≠ .internal (.difference next) := by
        intro next member
        exact different next (List.mem_cons_of_mem _ member)
      rw [List.foldl_cons, ih _ tail]
      simp [SourceController.newDifferenceStep, SourceController.Cursor.emitNative,
        SourceController.Cursor.emit, SourceController.Cursor.assign, head]

def observationStart (parameters : Parameters) : SourceController.Cursor parameters :=
  SourceController.attachDecoder parameters .faulty
    (SourceController.attachDecoder parameters .healthy
      (SourceController.originalObservations parameters (SourceController.controller parameters)))

def observationDifferenceBefore (parameters : Parameters)
    (index : Fin parameters.decoder.roots.length) : SourceController.Cursor parameters :=
  ((List.finRange parameters.decoder.roots.length).take index.val).foldl
    (SourceController.newDifferenceStep parameters) (observationStart parameters)

private theorem observationIndex_split (parameters : Parameters)
    (index : Fin parameters.decoder.roots.length) :
    List.finRange parameters.decoder.roots.length =
      (List.finRange parameters.decoder.roots.length).take index.val ++ index ::
        (List.finRange parameters.decoder.roots.length).drop (index.val + 1) := by
  have bound : index.val < (List.finRange parameters.decoder.roots.length).length := by
    simpa using index.isLt
  have split := List.take_append_drop index.val (List.finRange parameters.decoder.roots.length)
  rw [List.drop_eq_getElem_cons bound] at split
  simpa using split.symm

/-- The cursor after every replacement XOR and before the detected fold. -/
def observationFinal (parameters : Parameters) : SourceController.Cursor parameters :=
  (List.finRange parameters.decoder.roots.length).foldl
    (SourceController.newDifferenceStep parameters) (observationStart parameters)

private theorem compile_eq_foldNative (parameters : Parameters) :
    SourceController.compile parameters =
      (observationFinal parameters).foldNative (.internal .detected) .disjunction
        ((List.finRange parameters.decoder.roots.length).map fun output =>
          (observationFinal parameters).slots (.internal (.difference output))) := rfl

private theorem observationFinal_split (parameters : Parameters)
    (index : Fin parameters.decoder.roots.length) :
    observationFinal parameters =
      ((List.finRange parameters.decoder.roots.length).drop (index.val + 1)).foldl
        (SourceController.newDifferenceStep parameters)
        (SourceController.newDifferenceStep parameters (observationDifferenceBefore parameters index) index) := by
  have step : ∀ items : List (Fin parameters.decoder.roots.length),
      items = (List.finRange parameters.decoder.roots.length).take index.val ++ index ::
        (List.finRange parameters.decoder.roots.length).drop (index.val + 1) →
      items.foldl (SourceController.newDifferenceStep parameters) (observationStart parameters) =
        ((List.finRange parameters.decoder.roots.length).drop (index.val + 1)).foldl
          (SourceController.newDifferenceStep parameters)
          (SourceController.newDifferenceStep parameters (observationDifferenceBefore parameters index) index) := by
    intro items equality
    rw [equality, List.foldl_append, List.foldl_cons]
    rfl
  exact step _ (observationIndex_split parameters index)

private theorem compile_slots_of_ne_detected (parameters : Parameters)
    (query : Variable parameters) (different : query ≠ .internal .detected) :
    (SourceController.compile parameters).slots query = (observationFinal parameters).slots query := by
  rw [compile_eq_foldNative]
  simp only [SourceController.Cursor.foldNative, SourceController.Cursor.assign]
  exact Function.update_of_ne different _ _

private theorem observationDifference_retained (parameters : Parameters)
    (index : Fin parameters.decoder.roots.length) :
    ∃ suffix, (SourceController.compile parameters).entries =
      (SourceController.newDifferenceStep parameters (observationDifferenceBefore parameters index) index).entries ++
        suffix := by
  obtain ⟨suffix, equality⟩ := differenceFold_entries
    ((List.finRange parameters.decoder.roots.length).drop (index.val + 1))
    (SourceController.newDifferenceStep parameters (observationDifferenceBefore parameters index) index)
  rw [← observationFinal_split parameters index] at equality
  rw [compile_eq_foldNative]
  simp only [SourceController.Cursor.foldNative, SourceController.Cursor.assign]
  rw [equality, List.append_assoc]
  exact ⟨_, rfl⟩

def observationDifferenceOwner (parameters : Parameters)
    (index : Fin parameters.decoder.roots.length) : Fin (SourceController.compile parameters).entries.length :=
  ⟨(observationDifferenceBefore parameters index).entries.length, by
    obtain ⟨suffix, equality⟩ := observationDifference_retained parameters index
    rw [equality]
    simp only [SourceController.newDifferenceStep, SourceController.Cursor.emitNative,
      SourceController.Cursor.emit, SourceController.Cursor.assign, List.length_append,
      List.length_cons, List.length_nil]
    omega⟩

theorem observationDifference_producer (parameters : Parameters)
    (index : Fin parameters.decoder.roots.length) :
    (SourceController.compile parameters).entries[(observationDifferenceOwner parameters index).val].producer =
      (⟨((observationDifferenceBefore parameters index).lastID + 1, true),
        .xor
          ((observationDifferenceBefore parameters index).slots
            (.internal (.decoder .healthy (parameters.decoder.roots.get index))))
          ((observationDifferenceBefore parameters index).slots
            (.internal (.decoder .faulty (parameters.decoder.roots.get index))))⟩ : Bounded.Producer Nat) := by
  obtain ⟨suffix, equality⟩ := observationDifference_retained parameters index
  simp [observationDifferenceOwner, equality, SourceController.newDifferenceStep,
    SourceController.Cursor.emitNative, SourceController.Cursor.emit, SourceController.Cursor.assign]

theorem observationDifference_decoder_handle (parameters : Parameters)
    (index : Fin parameters.decoder.roots.length) (side : Side) (node : Fin parameters.decoder.nodeCount) :
    SourceController.sourceRoleMap parameters (.internal (.decoder side node)) =
      (observationDifferenceBefore parameters index).slots (.internal (.decoder side node)) := by
  have whole := differenceFold_slot (List.finRange parameters.decoder.roots.length)
    (observationStart parameters) (.internal (.decoder side node)) (by intro next member; simp)
  have initialPart := differenceFold_slot ((List.finRange parameters.decoder.roots.length).take index.val)
    (observationStart parameters) (.internal (.decoder side node)) (by intro next member; simp)
  have outer := compile_slots_of_ne_detected parameters (.internal (.decoder side node)) (by simp)
  exact outer.trans (whole.trans initialPart.symm)

theorem observationDifference_handle (parameters : Parameters)
    (index : Fin parameters.decoder.roots.length) :
    SourceController.sourceRoleMap parameters (.internal (.difference index)) =
      ((observationDifferenceBefore parameters index).lastID + 1, true) := by
  have distinct : index ∉ (List.finRange parameters.decoder.roots.length).drop (index.val + 1) := by
    have nodup := List.nodup_finRange parameters.decoder.roots.length
    rw [observationIndex_split parameters index] at nodup
    exact (List.nodup_cons.mp (List.nodup_append.mp nodup).2.1).1
  have outer := compile_slots_of_ne_detected parameters (.internal (.difference index)) (by simp)
  have later := differenceFold_slot ((List.finRange parameters.decoder.roots.length).drop (index.val + 1))
    (SourceController.newDifferenceStep parameters (observationDifferenceBefore parameters index) index)
    (.internal (.difference index)) (by
      intro next member equal
      have same : index = next := by simpa using equal
      exact distinct (same ▸ member))
  rw [← observationFinal_split parameters index] at later
  refine outer.trans (later.trans ?_)
  simp [SourceController.newDifferenceStep, SourceController.Cursor.emitNative,
    SourceController.Cursor.emit, SourceController.Cursor.assign]

/-- The four replacement XOR clauses are actual original-input occurrences,
with both decoder inputs and the difference output bound to final source roles. -/
def observationDifferenceOriginalRows (parameters : Parameters) (rename : Nat → Fin v)
    (index : Fin parameters.decoder.roots.length) :
    OriginalRows (initialState (relabel rename (SourceController.formula parameters))) rename
      ⟨SourceController.sourceRoleMap parameters (.internal (.difference index)),
        .xor
          (SourceController.sourceRoleMap parameters
            (.internal (.decoder .healthy (parameters.decoder.roots.get index))))
          (SourceController.sourceRoleMap parameters
            (.internal (.decoder .faulty (parameters.decoder.roots.get index))))⟩ := by
  have actual := sourceOriginalRows parameters rename (observationDifferenceOwner parameters index)
  rw [observationDifference_producer] at actual
  rw [observationDifference_handle parameters index,
    observationDifference_decoder_handle parameters index .healthy (parameters.decoder.roots.get index),
    observationDifference_decoder_handle parameters index .faulty (parameters.decoder.roots.get index)]
  exact actual

end Controller.NativeProof.SourceFoldProjection
