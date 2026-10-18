module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.SourceMixedScheduleFoundation

@[expose] public section

/-! Decoder certificates retain explicit original occurrence IDs. Their
additional original support is confined to the two actual decoder stages;
physical units and controller equations retain their existing support. -/
namespace Controller.NativeProof.SourceDecoderSchedule
open Controller.Native Controller.Native.SourceController Controller.CNF
open Controller.Resolution
open Controller.NativeProof.SourceMismatchBranch Controller.NativeProof.SourceFoldOccurrences
open Controller.NativeProof.SourceFoldOwners Controller.NativeProof.SourceCongruence
open Controller.NativeProof.SourceBusSchedule Controller.NativeProof.SourceMixedSchedule
open Controller.NativeProof.FoldProjection Controller.NativeProof.SourceFoldProjection
open Controller.NativeProof.SourceStageCongruence Controller.NativeProof.SourceBusAdvance
open Controller.NativeProof.SourceStagePolarity Controller.NativeProof.SourceMismatchHandles
variable {parameters : Parameters} {v : Nat}

/-- Only decoder emissions and their private fold or guard-chain nodes. -/
def DecoderOwner : Owner parameters → Prop
  | .native (.internal (.decoder _ _)) => True
  | .fold (.internal (.decoder _ _)) _ => True
  | .guard _ _ _ => True
  | _ => False

/-- The original ID is bound to an actual compiler occurrence in the selected
decoder stage. No observation owner or fourth assertion enters this extension. -/
def AllowedOriginal (rename : Nat → Fin v) (id : Nat) : Prop :=
  SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename id ∨
  ∃ side : Side, ∃ owner : Fin (compile parameters).entries.length,
    (decoderStart (parameters := parameters) side).entries.length ≤ owner.val ∧
    owner.val < (attachDecoder parameters side (decoderStart side)).entries.length ∧
    DecoderOwner (compile parameters).entries[owner.val].owner ∧
    ∃ index : Fin (compile parameters).entries[owner.val].producer.rows.length,
      id = (ownedRow rename owner index).id

theorem controller_original_allowed (rename : Nat → Fin v) (id : Nat)
    (original : SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename id) :
    AllowedOriginal (parameters := parameters) rename id := Or.inl original

theorem decoder_owner_native (side : Side) (node : Fin parameters.decoder.nodeCount) :
    DecoderOwner (parameters := parameters) (.native (.internal (.decoder side node))) := trivial

theorem decoder_owner_fold (side : Side) (node : Fin parameters.decoder.nodeCount) (index : Nat) :
    DecoderOwner (parameters := parameters) (.fold (.internal (.decoder side node)) index) := trivial

theorem decoder_owner_guard (side : Side) (node : Fin parameters.decoder.nodeCount) (index : Nat) :
    DecoderOwner (parameters := parameters) (.guard side node index) := trivial

theorem old_difference_excluded (index : Fin (parameters.buses + parameters.channels)) :
    ¬DecoderOwner (parameters := parameters) (.oldDifference index) := id

theorem old_detected_excluded (index : Nat) :
    ¬DecoderOwner (parameters := parameters) (.oldDetected index) := id

theorem new_difference_excluded (index : Fin parameters.decoder.roots.length) :
    ¬DecoderOwner (parameters := parameters) (.native (.internal (.difference index))) := id

theorem new_detected_excluded :
    ¬DecoderOwner (parameters := parameters) (.native (.internal .detected)) := id

theorem ownedRow_equation_bound (rename : Nat → Fin v)
    (owner : Fin (compile parameters).entries.length)
    (index : Fin (compile parameters).entries[owner.val].producer.rows.length) :
    (ownedRow rename owner index).id ≤ (equationRows (parameters := parameters)).length := by
  have split := SourceRows.sourceClauses_split parameters owner
  have indexBound := index.isLt
  have length := congrArg List.length split
  simp only [List.length_append] at length
  change (SourceRows.before parameters owner).length + index.val + 1 ≤ _
  unfold equationRows
  omega

theorem allowedOriginal_bound (rename : Nat → Fin v) (id : Nat)
    (allowed : AllowedOriginal (parameters := parameters) rename id) :
    id ≤ (equationRows (parameters := parameters)).length + 3 := by
  rcases allowed with original | ⟨side, owner, lower, upper, kind, index, same⟩
  · exact SourceMismatchBranch.allowedOriginal_bound rename id original
  · rw [same]
    have bound := ownedRow_equation_bound rename owner index
    omega

theorem detected_assertion_excluded (rename : Nat → Fin v) :
    ¬AllowedOriginal (parameters := parameters) rename
      ((equationRows (parameters := parameters)).length + 4) := by
  intro allowed
  have bound := allowedOriginal_bound rename _ allowed
  omega

theorem traceOriginalSupport_extend (rename : Nat → Fin v) (steps : List (Step v))
    (supported : TraceOriginalSupport (formula parameters).clauses.size
      (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename) steps) :
    TraceOriginalSupport (formula parameters).clauses.size
      (AllowedOriginal (parameters := parameters) rename) steps := by
  intro step member parent parentMember
  have original := supported step member parent parentMember
  exact ⟨fun bound => Or.inl (original.1 bound), original.2⟩

theorem emitOwner_kind (cursor : Cursor parameters) (slot : Controller.Native.Variable parameters)
    (gate : Gate Nat) (retained : EntriesBefore (cursor.emitNative slot gate) (compile parameters)) :
    (compile parameters).entries[(emitOwner cursor slot gate retained).val].owner = .native slot := by
  rcases retained with ⟨suffix, equality⟩
  simp [emitOwner, equality, Cursor.emitNative, Cursor.emit, Cursor.assign, List.getElem_append]

theorem decoderPosition_start_before (side : Side) (node : Fin parameters.decoder.nodeCount) :
    EntriesBefore (decoderStart (parameters := parameters) side) (decoderPositionBefore side node) := by
  apply foldl_before
  intro cursor index
  exact decoderNode_before side index cursor

theorem decoderPosition_end_before (side : Side) (node : Fin parameters.decoder.nodeCount) :
    EntriesBefore (decoderNode parameters side node (decoderPositionBefore side node))
      (attachDecoder parameters side (decoderStart side)) := by
  have bound : node.val < (List.finRange parameters.decoder.nodeCount).length := by simpa using node.isLt
  have split := positional_decomposition (List.finRange parameters.decoder.nodeCount) ⟨node.val, bound⟩
  have decomposition : List.finRange parameters.decoder.nodeCount =
      (List.finRange parameters.decoder.nodeCount).take node.val ++ node ::
        (List.finRange parameters.decoder.nodeCount).drop (node.val + 1) := by simpa using split
  unfold attachDecoder
  rw [decomposition]
  exact decoder_occurrence_before side (decoderStart side) _ _ node

theorem decoderEmitRow_allowed (rename : Nat → Fin v) (side : Side)
    (node : Fin parameters.decoder.nodeCount) (cursor : Cursor parameters) (gate : Gate Nat)
    (before : EntriesBefore (decoderStart (parameters := parameters) side) cursor)
    (after : EntriesBefore (cursor.emitNative (.internal (.decoder side node)) gate)
      (attachDecoder parameters side (decoderStart side)))
    (index : Fin (gate.clauses (cursor.lastID + 1, true)).length) :
    AllowedOriginal (parameters := parameters) rename
      ((emitRowsExact rename cursor (.internal (.decoder side node)) gate
        (after.trans (decoder_end_before_compile side))).row index).id := by
  let retained := after.trans (decoder_end_before_compile side)
  let owner := emitOwner cursor (.internal (.decoder side node)) gate retained
  have producer := emitOwner_producer cursor (.internal (.decoder side node)) gate retained
  have lower : (decoderStart (parameters := parameters) side).entries.length ≤ owner.val := by
    rcases before with ⟨suffix, equality⟩
    simp only [owner, emitOwner]
    rw [equality]
    simp only [List.length_append]
    omega
  have upper : owner.val < (attachDecoder parameters side (decoderStart side)).entries.length := by
    rcases after with ⟨suffix, equality⟩
    simp only [owner, emitOwner]
    rw [equality]
    simp only [Cursor.emitNative, Cursor.emit, Cursor.assign, List.length_append, List.length_cons, List.length_nil]
    omega
  have bound : index.val < (compile parameters).entries[owner.val].producer.rows.length := by
    rw [producer]
    exact index.isLt
  refine Or.inr ⟨side, owner, lower, upper, ?_, ⟨index.val, bound⟩, rfl⟩
  rw [emitOwner_kind]
  trivial

def decoderZeroRows (rename : Nat → Fin v) (side : Side)
    (node : Fin parameters.decoder.nodeCount) (shape : parameters.decoder.node node = .zero) :
    Controller.NativeProof.SourceFoldProjection.OriginalRows
      (initialState (relabel rename (formula parameters))) rename
      ⟨((decoderPositionBefore side node).lastID + 1, true), .or []⟩ := by
  apply emitRowsExact rename (decoderPositionBefore side node) (.internal (.decoder side node)) (.or [])
  simpa only [decoderNode, shape] using decoder_position_before_compile side node

theorem decoderZeroRows_allowed (rename : Nat → Fin v) (side : Side)
    (node : Fin parameters.decoder.nodeCount) (shape : parameters.decoder.node node = .zero)
    (index : Fin 1) :
    AllowedOriginal (parameters := parameters) rename
      ((decoderZeroRows rename side node shape).row ⟨index.val, by change index.val < 1; exact index.isLt⟩).id := by
  have after : EntriesBefore
      ((decoderPositionBefore side node).emitNative (.internal (.decoder side node)) (.or []))
      (attachDecoder parameters side (decoderStart side)) := by
    simpa only [decoderNode, shape] using decoderPosition_end_before side node
  simpa only [decoderZeroRows, emitRowsExact, ownedRow, emitOwner, SourceRows.before] using decoderEmitRow_allowed rename side node
    (decoderPositionBefore side node) (.or []) (decoderPosition_start_before side node) after
    ⟨index.val, by change index.val < 1; exact index.isLt⟩

open Controller.NativeProof.SourceFoldProvenance Controller.NativeProof.SourceFoldProjection

theorem foldOwner_kind (cursor final : Cursor parameters)
    (slot : Controller.Native.Variable parameters) (junction : Bounded.Junction)
    (inputs : List (Literal Nat)) (retained : EntriesBefore (cursor.foldNative slot junction inputs) final)
    (index : Fin (SourceSerialFold.allocate junction cursor.lastID inputs).producers.length) :
    final.entries[(SourceFoldOwners.foldOwner cursor final slot junction inputs retained index).val].owner = .fold slot index.val := by
  rcases retained with ⟨suffix, equality⟩
  have blockBound : index.val < ((SourceSerialFold.allocate junction cursor.lastID inputs).producers.zipIdx.map
      (fun pair => Entry.mk (.fold slot pair.2) pair.1)).length := by
    simpa only [List.length_map, List.length_zipIdx] using index.isLt
  simp [SourceFoldOwners.foldOwner, equality, Cursor.foldNative, Cursor.assign,
    List.getElem_append, List.getElem_map, blockBound, index.isLt, List.getElem_zipIdx]

theorem decoderFoldRows_allowed (rename : Nat → Fin v) (side : Side)
    (node : Fin parameters.decoder.nodeCount) (cursor : Cursor parameters)
    (junction : Bounded.Junction) (inputs : List (Literal Nat))
    (before : EntriesBefore (decoderStart (parameters := parameters) side) cursor)
    (after : EntriesBefore (cursor.foldNative (.internal (.decoder side node)) junction inputs)
      (attachDecoder parameters side (decoderStart side))) :
    SupplyOriginals (AllowedOriginal (parameters := parameters) rename)
      (foldRowsExact rename cursor (.internal (.decoder side node)) junction inputs
        (after.trans (decoder_end_before_compile side))) := by
  intro index rowIndex
  let retained := after.trans (decoder_end_before_compile side)
  let owner := SourceFoldOwners.foldOwner cursor (compile parameters) (.internal (.decoder side node)) junction inputs retained index
  have lower : (decoderStart (parameters := parameters) side).entries.length ≤ owner.val := by
    rcases before with ⟨suffix, equality⟩
    simp only [owner, SourceFoldOwners.foldOwner]
    rw [equality]
    simp only [List.length_append]
    omega
  have upper : owner.val < (attachDecoder parameters side (decoderStart side)).entries.length := by
    rcases after with ⟨suffix, equality⟩
    simp only [owner, SourceFoldOwners.foldOwner]
    rw [equality]
    simp only [Cursor.foldNative, Cursor.assign, List.length_append, List.length_map, List.length_zipIdx]
    have bound := index.isLt
    omega
  have producer := foldOwner_producer cursor (compile parameters)
    (.internal (.decoder side node)) junction inputs retained index
  have rowBound : rowIndex.val < (compile parameters).entries[owner.val].producer.rows.length := by
    rw [producer]
    exact rowIndex.isLt
  refine Or.inr ⟨side, owner, lower, upper, ?_, ⟨rowIndex.val, rowBound⟩, rfl⟩
  rw [foldOwner_kind]
  trivial

def decoderDisjunctionRowsExact (rename : Nat → Fin v) (side : Side)
    (node : Fin parameters.decoder.nodeCount) (children : List (Fin node.val))
    (shape : parameters.decoder.node node = .disj children) :
    RowSupply (initialState (relabel rename (formula parameters))) rename
      (SourceSerialFold.allocate .disjunction (decoderPositionBefore side node).lastID
        (children.map fun child => (decoderPositionBefore side node).slots
          (.internal (.decoder side (parameters.decoder.childIndex node child))))).producers := by
  apply foldRowsExact rename (decoderPositionBefore side node) (.internal (.decoder side node)) .disjunction
  simpa only [decoderNode, shape] using decoder_position_before_compile side node

theorem decoderDisjunctionRowsExact_allowed (rename : Nat → Fin v) (side : Side)
    (node : Fin parameters.decoder.nodeCount) (children : List (Fin node.val))
    (shape : parameters.decoder.node node = .disj children) :
    SupplyOriginals (AllowedOriginal (parameters := parameters) rename)
      (decoderDisjunctionRowsExact rename side node children shape) := by
  have after : EntriesBefore
      ((decoderPositionBefore side node).foldNative (.internal (.decoder side node)) .disjunction
        (children.map fun child => (decoderPositionBefore side node).slots
          (.internal (.decoder side (parameters.decoder.childIndex node child)))))
      (attachDecoder parameters side (decoderStart side)) := by
    simpa only [decoderNode, shape] using decoderPosition_end_before side node
  exact decoderFoldRows_allowed rename side node (decoderPositionBefore side node) .disjunction _
    (decoderPosition_start_before side node) after

open Controller.NativeProof.SourceQualifierOccurrences

def decoderGuardStep (side : Side) (node : Fin parameters.decoder.nodeCount)
    (state : Literal Nat × Cursor parameters) (pair : Fin parameters.channels × Nat) :
    Literal Nat × Cursor parameters :=
  state.2.emit (.guard side node pair.2)
    (.and [state.1, negate (state.2.slots (.internal (.qualifier side pair.1)))])

def decoderGuardBefore (side : Side) (node : Fin parameters.decoder.nodeCount)
    (child : Fin node.val) (labels : List (Fin parameters.channels)) (index : Fin labels.length) :
    Literal Nat × Cursor parameters :=
  ((labels.zipIdx).take index.val).foldl (decoderGuardStep side node)
    ((decoderPositionBefore side node).slots
      (.internal (.decoder side (parameters.decoder.childIndex node child))), decoderPositionBefore side node)

theorem decoderGuardBefore_start (side : Side) (node : Fin parameters.decoder.nodeCount)
    (child : Fin node.val) (labels : List (Fin parameters.channels)) (index : Fin labels.length) :
    EntriesBefore (decoderStart (parameters := parameters) side)
      (decoderGuardBefore side node child labels index).2 := by
  apply (decoderPosition_start_before side node).trans
  apply pairFoldl_before
  intro current pair
  exact emit_before current.2 _ _

theorem decoderGuardBefore_end (side : Side) (node : Fin parameters.decoder.nodeCount)
    (child : Fin node.val) (labels : List (Fin parameters.channels))
    (shape : parameters.decoder.node node = .guard child labels) (index : Fin labels.length) :
    EntriesBefore
      (decoderGuardStep side node (decoderGuardBefore side node child labels index)
        (labels[index.val], index.val)).2
      (attachDecoder parameters side (decoderStart side)) := by
  have bound : index.val < labels.zipIdx.length := by simpa only [List.length_zipIdx] using index.isLt
  have split := positional_decomposition labels.zipIdx ⟨index.val, bound⟩
  have decomposition : labels.zipIdx =
      labels.zipIdx.take index.val ++ (labels[index.val], index.val) ::
        labels.zipIdx.drop (index.val + 1) := by simpa only [List.getElem_zipIdx, Nat.zero_add] using split
  apply EntriesBefore.trans _ (decoderPosition_end_before side node)
  simp only [decoderNode, shape]
  change EntriesBefore _
    ((guardChain parameters side node
      ((decoderPositionBefore side node).slots
        (.internal (.decoder side (parameters.decoder.childIndex node child))))
      labels (decoderPositionBefore side node)).2.assign (.internal (.decoder side node)) _)
  apply EntriesBefore.trans _ (assign_before _ _ _)
  unfold guardChain
  change EntriesBefore _ (labels.zipIdx.foldl (decoderGuardStep side node) _).2
  rw [decomposition, List.foldl_append, List.foldl_cons]
  apply pairFoldl_before
  intro current pair
  exact emit_before current.2 _ _

theorem rawEmitOwner_kind (cursor : Cursor parameters) (owner : Owner parameters) (gate : Gate Nat)
    (retained : EntriesBefore (cursor.emit owner gate).2 (compile parameters)) :
    (compile parameters).entries[(rawEmitOwner cursor owner gate retained).val].owner = owner := by
  rcases retained with ⟨suffix, equality⟩
  simp [rawEmitOwner, equality, Cursor.emit, List.getElem_append]

def decoderGuardRows (rename : Nat → Fin v) (side : Side)
    (node : Fin parameters.decoder.nodeCount) (child : Fin node.val)
    (labels : List (Fin parameters.channels)) (shape : parameters.decoder.node node = .guard child labels)
    (index : Fin labels.length) :
    let current := decoderGuardBefore side node child labels index
    OriginalRows (initialState (relabel rename (formula parameters))) rename
      ⟨(current.2.lastID + 1, true),
        .and [current.1, negate (current.2.slots (.internal (.qualifier side labels[index.val])))]⟩ := by
  dsimp only
  exact rawEmitRows rename _ (.guard side node index.val) _
    ((decoderGuardBefore_end side node child labels shape index).trans (decoder_end_before_compile side))

theorem decoderGuardRows_allowed (rename : Nat → Fin v) (side : Side)
    (node : Fin parameters.decoder.nodeCount) (child : Fin node.val)
    (labels : List (Fin parameters.channels)) (shape : parameters.decoder.node node = .guard child labels)
    (index : Fin labels.length) (rowIndex : Fin 3) :
    AllowedOriginal (parameters := parameters) rename
      ((decoderGuardRows rename side node child labels shape index).row
        ⟨rowIndex.val, by change rowIndex.val < 3; exact rowIndex.isLt⟩).id := by
  let current := decoderGuardBefore side node child labels index
  let gate := Gate.and [current.1, negate (current.2.slots (.internal (.qualifier side labels[index.val])))]
  let retained : EntriesBefore (current.2.emit (.guard side node index.val) gate).2
      (compile parameters) := by
    simpa only [current, gate, decoderGuardStep] using
      (decoderGuardBefore_end side node child labels shape index).trans (decoder_end_before_compile side)
  let owner := rawEmitOwner current.2 (.guard side node index.val) gate retained
  have lower : (decoderStart (parameters := parameters) side).entries.length ≤ owner.val := by
    rcases decoderGuardBefore_start side node child labels index with ⟨suffix, equality⟩
    simp only [owner, rawEmitOwner]
    rw [equality]
    simp only [List.length_append]
    omega
  have upper : owner.val < (attachDecoder parameters side (decoderStart side)).entries.length := by
    rcases decoderGuardBefore_end side node child labels shape index with ⟨suffix, equality⟩
    simp only [owner, rawEmitOwner, current]
    rw [equality]
    simp only [decoderGuardStep, Cursor.emit, List.length_append, List.length_cons, List.length_nil]
    omega
  have producer := rawEmitOwner_producer current.2 (.guard side node index.val) gate retained
  have bound : rowIndex.val < (compile parameters).entries[owner.val].producer.rows.length := by
    rw [producer]
    change rowIndex.val < 3
    exact rowIndex.isLt
  refine Or.inr ⟨side, owner, lower, upper, ?_, ⟨rowIndex.val, bound⟩, rfl⟩
  dsimp only [owner]
  rw [rawEmitOwner_kind]
  trivial

open Controller.NativeProof.SourceFoldAggregateProvenance

def decoderDisjunctionTree (rename : Nat → Fin v) (side : Side)
    (node : Fin parameters.decoder.nodeCount) (children : List (Fin node.val))
    (shape : parameters.decoder.node node = .disj children) (nonempty : children ≠ []) :=
  allocateOrForest (initialOrForest (state := initialState (relabel rename (formula parameters))) rename
    (children.map fun child => (decoderPositionBefore side node).slots
      (.internal (.decoder side (parameters.decoder.childIndex node child)))))
    (decoderPositionBefore side node).lastID (by
      intro empty
      exact nonempty (List.map_eq_nil_iff.mp empty))
    (decoderDisjunctionRowsExact rename side node children shape)

theorem decoderDisjunctionTree_originals (rename : Nat → Fin v) (side : Side)
    (node : Fin parameters.decoder.nodeCount) (children : List (Fin node.val))
    (shape : parameters.decoder.node node = .disj children) (nonempty : children ≠ []) :
    TreeOriginals (AllowedOriginal (parameters := parameters) rename)
      (decoderDisjunctionTree rename side node children shape nonempty) := by
  apply allocateOrForest_originals
  · exact initialOrForest_originals _ _ _
  · exact decoderDisjunctionRowsExact_allowed rename side node children shape

def decoderLiveAndRows (rename : Nat → Fin v) (side : Side)
    (node : Fin parameters.decoder.nodeCount) (left right : Fin node.val)
    (shape : parameters.decoder.node node = .liveAnd left right) :
    OriginalRows (initialState (relabel rename (formula parameters))) rename
      ⟨((decoderPositionBefore side node).lastID + 1, true), .and
        [(decoderPositionBefore side node).slots (.internal (.decoder side (parameters.decoder.childIndex node left))),
         (decoderPositionBefore side node).slots (.internal (.decoder side (parameters.decoder.childIndex node right)))]⟩ := by
  apply emitRowsExact rename (decoderPositionBefore side node) (.internal (.decoder side node)) _
  simpa only [decoderNode, shape] using decoder_position_before_compile side node

theorem decoderLiveAndRows_allowed (rename : Nat → Fin v) (side : Side)
    (node : Fin parameters.decoder.nodeCount) (left right : Fin node.val)
    (shape : parameters.decoder.node node = .liveAnd left right) (index : Fin 3) :
    AllowedOriginal (parameters := parameters) rename
      ((decoderLiveAndRows rename side node left right shape).row
        ⟨index.val, by change index.val < 3; exact index.isLt⟩).id := by
  have after : EntriesBefore
      ((decoderPositionBefore side node).emitNative (.internal (.decoder side node)) (.and
        [(decoderPositionBefore side node).slots (.internal (.decoder side (parameters.decoder.childIndex node left))),
         (decoderPositionBefore side node).slots (.internal (.decoder side (parameters.decoder.childIndex node right)))]))
      (attachDecoder parameters side (decoderStart side)) := by
    simpa only [decoderNode, shape] using decoderPosition_end_before side node
  simpa only [decoderLiveAndRows, emitRowsExact, ownedRow, emitOwner, SourceRows.before] using decoderEmitRow_allowed rename side node
    (decoderPositionBefore side node) _ (decoderPosition_start_before side node) after
    ⟨index.val, by change index.val < 3; exact index.isLt⟩

open Controller.NativeProof.SourceRoleFrames Controller.NativeProof.SourceSlotFrames

theorem decoderNode_other (side : Side) (node : Fin parameters.decoder.nodeCount)
    (query : Controller.Native.Variable parameters) (cursor : Cursor parameters)
    (different : query ≠ .internal (.decoder side node)) :
    (decoderNode parameters side node cursor).slots query = cursor.slots query := by
  unfold decoderNode
  cases parameters.decoder.node node with
  | zero => exact SourceSlotFrames.emitNative_other _ _ _ _ different
  | input channel => exact SourceSlotFrames.assign_other _ _ _ _ different
  | disj children => exact SourceSlotFrames.foldNative_other _ _ _ _ _ different
  | guard child labels =>
      rw [SourceSlotFrames.assign_other _ _ _ _ different]
      exact SourceRoleFrames.guardChain_slot side node _ labels query cursor
  | liveAnd left right => exact SourceSlotFrames.emitNative_other _ _ _ _ different


theorem attachDecoder_other (side : Side) (query : Controller.Native.Variable parameters)
    (cursor : Cursor parameters)
    (different : ∀ node : Fin parameters.decoder.nodeCount, query ≠ .internal (.decoder side node)) :
    (attachDecoder parameters side cursor).slots query = cursor.slots query := by
  unfold attachDecoder
  exact SourceSlotFrames.foldl_slot _ query
    (fun current node => decoderNode_other side node query current (different node)) _ cursor

theorem decoderNode_qualifier (side querySide : Side)
    (node : Fin parameters.decoder.nodeCount) (channel : Fin parameters.channels)
    (cursor : Cursor parameters) :
    (decoderNode parameters side node cursor).slots (.internal (.qualifier querySide channel)) =
      cursor.slots (.internal (.qualifier querySide channel)) := by
  apply decoderNode_other
  simp

theorem attachDecoder_qualifier (side querySide : Side) (channel : Fin parameters.channels)
    (cursor : Cursor parameters) :
    (attachDecoder parameters side cursor).slots (.internal (.qualifier querySide channel)) =
      cursor.slots (.internal (.qualifier querySide channel)) := by
  apply attachDecoder_other
  intro node
  simp


/-- Directional pairs are stored against the actual two decoder cursors at a
topological position. The prefix contains the emitted proof rows only. -/
structure DecoderPairTable (rename : Nat → Fin v) (context : Clause (Fin v))
    (position : Nat) where
  prefixState : SourcePrefix (parameters := parameters) rename
  pairs : ∀ node : Fin parameters.decoder.nodeCount, node.val < position →
    DirectionPair prefixState.state context
      (mapLiteral rename ((((List.finRange parameters.decoder.nodeCount).take position).foldl
        (fun cursor next => decoderNode parameters .healthy next cursor) (decoderStart .healthy)).slots
        (.internal (.decoder .healthy node))))
      (mapLiteral rename ((((List.finRange parameters.decoder.nodeCount).take position).foldl
        (fun cursor next => decoderNode parameters .faulty next cursor) (decoderStart .faulty)).slots
        (.internal (.decoder .faulty node))))


def pairedZeroRows (state : State v) (context : Clause (Fin v))
    (left right : Literal (Fin v))
    (leftRow : Rows.Available state [negate left])
    (rightRow : Rows.Available state [negate right]) :
    DirectionPair state context left right := by
  refine ⟨.derived (retarget (ofRow leftRow) ?_), .derived (retarget (ofRow rightRow) ?_)⟩
  · intro literal member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    subst literal
    exact List.mem_append_right _ (by simp)
  · intro literal member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    subst literal
    exact List.mem_append_right _ (by simp)


theorem decoderInput_output (side : Side) (node : Fin parameters.decoder.nodeCount)
    (channel : Fin parameters.channels) (cursor : Cursor parameters)
    (shape : parameters.decoder.node node = .input channel) :
    (decoderNode parameters side node cursor).slots (.internal (.decoder side node)) =
      cursor.slots (.internal (.qualifier side channel)) := by
  simp only [decoderNode, shape, Cursor.assign]
  simp

theorem decoderZero_output (side : Side) (node : Fin parameters.decoder.nodeCount)
    (cursor : Cursor parameters) (shape : parameters.decoder.node node = .zero) :
    (decoderNode parameters side node cursor).slots (.internal (.decoder side node)) =
      (cursor.lastID + 1, true) := by
  simp [decoderNode, shape, Cursor.emitNative, Cursor.emit, Cursor.assign]

def decoderInputPair (rename : Nat → Fin v) (context : Clause (Fin v))
    (node : Fin parameters.decoder.nodeCount) (channel : Fin parameters.channels)
    (shape : parameters.decoder.node node = .input channel) (state : State v)
    (qualifiers : DirectionPair state context
      (mapLiteral rename ((decoderPositionBefore .healthy node).slots (.internal (.qualifier .healthy channel))))
      (mapLiteral rename ((decoderPositionBefore .faulty node).slots (.internal (.qualifier .faulty channel))))) :
    DirectionPair state context
      (mapLiteral rename ((decoderNode parameters .healthy node (decoderPositionBefore .healthy node)).slots
        (.internal (.decoder .healthy node))))
      (mapLiteral rename ((decoderNode parameters .faulty node (decoderPositionBefore .faulty node)).slots
        (.internal (.decoder .faulty node)))) := by
  simpa only [decoderInput_output _ _ _ _ shape] using qualifiers


def decoderChildPairs (rename : Nat → Fin v) (node : Fin parameters.decoder.nodeCount)
    (children : List (Fin node.val)) : List (Literal (Fin v) × Literal (Fin v)) :=
  children.map fun child =>
    (mapLiteral rename ((decoderPositionBefore .healthy node).slots
       (.internal (.decoder .healthy (parameters.decoder.childIndex node child)))),
     mapLiteral rename ((decoderPositionBefore .faulty node).slots
       (.internal (.decoder .faulty (parameters.decoder.childIndex node child)))))

theorem decoderChildPairs_nonempty (rename : Nat → Fin v) (node : Fin parameters.decoder.nodeCount)
    (children : List (Fin node.val)) (nonempty : children ≠ []) :
    decoderChildPairs rename node children ≠ [] := by
  intro empty
  exact nonempty (List.map_eq_nil_iff.mp empty)

def decoderChildPairDirection (rename : Nat → Fin v) (context : Clause (Fin v))
    (node : Fin parameters.decoder.nodeCount) (children : List (Fin node.val))
    (table : DecoderPairTable (parameters := parameters) rename context node.val)
    (pair : Literal (Fin v) × Literal (Fin v))
    (member : pair ∈ decoderChildPairs rename node children) :
    DirectionPair table.prefixState.state context pair.1 pair.2 := by
  let selected := FoldProjection.mappedChoice
    (fun child : Fin node.val =>
      (mapLiteral rename ((decoderPositionBefore .healthy node).slots
        (.internal (.decoder .healthy (parameters.decoder.childIndex node child)))),
       mapLiteral rename ((decoderPositionBefore .faulty node).slots
        (.internal (.decoder .faulty (parameters.decoder.childIndex node child))))))
    pair children member
  have actual := table.pairs (parameters.decoder.childIndex node selected.val) selected.val.isLt
  have same := selected.property.2
  simpa only [← same, decoderPositionBefore, decoderBefore, occurrenceCursor] using actual


open Controller.NativeProof.SourceBusAdvance

def decoderDisjunctionOutput (side : Side) (node : Fin parameters.decoder.nodeCount)
    (children : List (Fin node.val)) : Literal Nat :=
  (SourceSerialFold.allocate .disjunction (decoderPositionBefore side node).lastID
    (children.map fun child => (decoderPositionBefore side node).slots
      (.internal (.decoder side (parameters.decoder.childIndex node child))))).output

theorem decoderDisjunction_output (side : Side) (node : Fin parameters.decoder.nodeCount)
    (children : List (Fin node.val)) (shape : parameters.decoder.node node = .disj children) :
    (decoderNode parameters side node (decoderPositionBefore side node)).slots
      (.internal (.decoder side node)) = decoderDisjunctionOutput side node children := by
  simp [decoderNode, shape, Cursor.foldNative, Cursor.assign, decoderDisjunctionOutput]

def decoderDisjunctionLeftTree (rename : Nat → Fin v)
    (node : Fin parameters.decoder.nodeCount) (children : List (Fin node.val))
    (shape : parameters.decoder.node node = .disj children) (nonempty : children ≠ [])
    (prefixState : SourcePrefix (parameters := parameters) rename) :
    AndTree prefixState.state (negate (mapLiteral rename (decoderDisjunctionOutput .healthy node children)))
      (((decoderChildPairs rename node children).map Prod.fst).map negate) := by
  have actual := (decoderDisjunctionTree rename .healthy node children shape nonempty).afterTrace
    prefixState.state prefixState.steps prefixState.checked
  simpa only [decoderDisjunctionTree, decoderDisjunctionOutput, decoderChildPairs,
    List.map_map, Function.comp_def, dualLiteral] using actual

def decoderDisjunctionRightTree (rename : Nat → Fin v)
    (node : Fin parameters.decoder.nodeCount) (children : List (Fin node.val))
    (shape : parameters.decoder.node node = .disj children) (nonempty : children ≠ [])
    (prefixState : SourcePrefix (parameters := parameters) rename) :
    AndTree prefixState.state (negate (mapLiteral rename (decoderDisjunctionOutput .faulty node children)))
      (((decoderChildPairs rename node children).map Prod.snd).map negate) := by
  have actual := (decoderDisjunctionTree rename .faulty node children shape nonempty).afterTrace
    prefixState.state prefixState.steps prefixState.checked
  simpa only [decoderDisjunctionTree, decoderDisjunctionOutput, decoderChildPairs,
    List.map_map, Function.comp_def, dualLiteral] using actual

def pairedDecoderDisjunction (rename : Nat → Fin v) (context : Clause (Fin v))
    (node : Fin parameters.decoder.nodeCount) (children : List (Fin node.val))
    (shape : parameters.decoder.node node = .disj children) (nonempty : children ≠ [])
    (table : DecoderPairTable (parameters := parameters) rename context node.val) :
    PairedProjection table.prefixState.state context
      (mapLiteral rename (decoderDisjunctionOutput .healthy node children))
      (mapLiteral rename (decoderDisjunctionOutput .faulty node children))
      (12 * (decoderChildPairs rename node children).length) :=
  pairedOr table.prefixState.state context _ _ (decoderChildPairs rename node children)
    (decoderChildPairs_nonempty rename node children nonempty)
    (decoderDisjunctionLeftTree rename node children shape nonempty table.prefixState)
    (decoderDisjunctionRightTree rename node children shape nonempty table.prefixState)
    (fun pair member => decoderChildPairDirection rename context node children table pair member)

theorem pairedDecoderDisjunction_count (rename : Nat → Fin v) (context : Clause (Fin v))
    (node : Fin parameters.decoder.nodeCount) (children : List (Fin node.val))
    (shape : parameters.decoder.node node = .disj children) (nonempty : children ≠ [])
    (table : DecoderPairTable (parameters := parameters) rename context node.val) :
    (pairedDecoderDisjunction rename context node children shape nonempty table).steps.length ≤
      12 * children.length := by
  simpa only [decoderChildPairs, List.length_map] using
    (pairedDecoderDisjunction rename context node children shape nonempty table).count


open Controller.NativeProof.SourceStageCongruence Controller.NativeProof.SourceStagePolarity
open Controller.NativeProof.SourceMismatchHandles

def PrefixOriginalSupport (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename) : Prop :=
  TraceOriginalSupport (formula parameters).clauses.size
    (AllowedOriginal (parameters := parameters) rename) prefixState.steps

def ProjectionOriginalSupport (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    {target : Clause (Fin v)} {budget : Nat}
    (projection : SubclauseProjection prefixState.state target budget) : Prop :=
  TraceOriginalSupport (formula parameters).clauses.size
    (AllowedOriginal (parameters := parameters) rename) (prefixState.steps ++ projection.steps) ∧
  ResultOrigin (formula parameters).clauses.size
    (AllowedOriginal (parameters := parameters) rename)
    (prefixState.steps ++ projection.steps) projection.result.row.id

theorem allowed_native_count_le (rename : Nat → Fin v) (id : Nat)
    (allowed : AllowedOriginal (parameters := parameters) rename id) :
    id ≤ (formula parameters).clauses.size := by
  have bound := allowedOriginal_bound rename id allowed
  simp only [SourceRows.formula_as_rows, ofClauses, List.size_toArray, List.length_append,
    List.length_map, assertions, List.length_cons, List.length_nil] 
  unfold equationRows at bound
  omega

def GuardedTransferOrigin (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    {context : Clause (Fin v)} {input output : Literal (Fin v)}
    (transfer : GuardedTransfer prefixState.state context input output) : Prop :=
  match transfer with
  | .identity _ => True
  | .derived row => ResultOrigin (formula parameters).clauses.size
      (Controller.NativeProof.SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
      prefixState.steps row.row.id

def DirectionPairOrigin (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    {context : Clause (Fin v)} {input output : Literal (Fin v)}
    (pair : DirectionPair prefixState.state context input output) : Prop :=
  GuardedTransferOrigin rename prefixState pair.forward ∧
    GuardedTransferOrigin rename prefixState pair.backward

theorem GuardedTransferOrigin.afterTrace (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    {context : Clause (Fin v)} {input output : Literal (Fin v)}
    (transfer : GuardedTransfer prefixState.state context input output)
    (original : GuardedTransferOrigin rename prefixState transfer)
    (next : State v) (steps : List (Step v))
    (checked : runSteps prefixState.state steps = some next) :
    GuardedTransferOrigin rename (prefixState.extend next steps checked)
      (transfer.afterTrace next steps checked) := by
  cases transfer with
  | identity same => trivial
  | derived row =>
      change ResultOrigin (formula parameters).clauses.size
        (Controller.NativeProof.SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
        (prefixState.steps ++ steps) row.row.id
      exact resultOrigin_append_right (formula parameters).clauses.size
        (Controller.NativeProof.SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
        prefixState.steps steps row.row.id original

theorem DirectionPairOrigin.afterTrace (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    {context : Clause (Fin v)} {input output : Literal (Fin v)}
    (pair : DirectionPair prefixState.state context input output)
    (original : DirectionPairOrigin rename prefixState pair)
    (next : State v) (steps : List (Step v))
    (checked : runSteps prefixState.state steps = some next) :
    DirectionPairOrigin rename (prefixState.extend next steps checked)
      (pair.afterTrace next steps checked) :=
  ⟨GuardedTransferOrigin.afterTrace rename prefixState pair.forward original.1 next steps checked,
   GuardedTransferOrigin.afterTrace rename prefixState pair.backward original.2 next steps checked⟩



theorem guardedChain_supported (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (context : Clause (Fin v)) (root middle output : Literal (Fin v))
    (first : AvailableSubclause prefixState.state (context ++ [negate root, middle]))
    (second : AvailableSubclause prefixState.state (context ++ [negate middle, output]))
    (supported : PrefixOriginalSupport rename prefixState)
    (firstOrigin : ResultOrigin (formula parameters).clauses.size
      (Controller.NativeProof.SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
      prefixState.steps first.row.id)
    (secondOrigin : ResultOrigin (formula parameters).clauses.size
      (Controller.NativeProof.SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
      prefixState.steps second.row.id) :
    ProjectionOriginalSupport rename prefixState
      (guardedChain prefixState.state context root middle output first second) := by
  constructor
  · exact Controller.NativeProof.SourceFoldAggregateProvenance.appendMerge_origins_supported
      (formula parameters).clauses.size
      (Controller.NativeProof.SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
      prefixState.steps prefixState.state second.row.id first.row.id middle second.clause first.clause
      supported (allowed_native_count_le rename) secondOrigin firstOrigin second.row.bound first.row.bound
  · exact Controller.NativeProof.SourceFoldAggregateProvenance.merge_origins
      (formula parameters).clauses.size
      (Controller.NativeProof.SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
      prefixState.steps prefixState.state second.row.id first.row.id middle second.clause first.clause
      secondOrigin firstOrigin (prefix_native_count_le rename prefixState)

/-- An identity transfer reuses the directional row; a derived transfer performs
its actual contextual merge. Neither branch invents an alias premise. -/
theorem guardedFromRow_supported (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (context : Clause (Fin v)) (root input output : Literal (Fin v))
    (direction : AvailableSubclause prefixState.state [negate root, input])
    (transfer : GuardedTransfer prefixState.state context input output)
    (supported : PrefixOriginalSupport rename prefixState)
    (directionOrigin : ResultOrigin (formula parameters).clauses.size
      (Controller.NativeProof.SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
      prefixState.steps direction.row.id)
    (transferOrigin : GuardedTransferOrigin rename prefixState transfer) :
    ProjectionOriginalSupport rename prefixState
      (guardedFromRow prefixState.state context root input output direction transfer) := by
  cases transfer with
  | identity same =>
      subst output
      constructor
      · simpa only [guardedFromRow, ProjectionOriginalSupport, PrefixOriginalSupport, List.append_nil] using supported
      · simpa only [guardedFromRow, retarget, List.append_nil] using directionOrigin
  | derived row =>
      exact guardedChain_supported rename prefixState context root input output
        (retarget direction (fun literal member => List.mem_append_right _ member)) row
        supported directionOrigin transferOrigin



theorem dischargeInputs_nil_fields (state : State v) (target : Clause (Fin v))
    (conflict : AvailableSubclause state ([].map negate ++ target))
    (propagation : ∀ input ∈ ([] : List (Literal (Fin v))),
      AvailableSubclause state (target ++ [input])) :
    (dischargeInputs state [] target conflict propagation).steps = [] ∧
      (dischargeInputs state [] target conflict propagation).result.row.id = conflict.row.id := by
  constructor <;> rfl

theorem dischargeInputs_cons_fields (state : State v)
    (pivot : Literal (Fin v)) (rest target : Clause (Fin v))
    (conflict : AvailableSubclause state ((pivot :: rest).map negate ++ target))
    (propagation : ∀ input ∈ pivot :: rest,
      AvailableSubclause state (target ++ [input])) :
    let reason : AvailableSubclause state (pivot :: target) :=
      retarget (propagation pivot (by simp)) (by
        intro literal member
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member ⊢
        aesop)
    let adapted : AvailableSubclause state (negate pivot :: (rest.map negate ++ target)) := by
      simpa using conflict
    let joined := longMerge state pivot (rest.map negate ++ target) target adapted reason
    let merged := longMerge_result state pivot (rest.map negate ++ target) target adapted reason
    let nextConflict : AvailableSubclause joined.state (rest.map negate ++ target) :=
      retarget merged (by
        intro literal member
        simp only [List.mem_append] at member ⊢
        aesop)
    let nextPropagation : ∀ input ∈ rest, AvailableSubclause joined.state (target ++ [input]) :=
      fun input member => afterTrace (propagation input (by simp [member]))
        joined.state joined.steps (longMerge_run state pivot (rest.map negate ++ target) target adapted reason)
    let tail := dischargeInputs joined.state rest target nextConflict nextPropagation
    (dischargeInputs state (pivot :: rest) target conflict propagation).steps =
        joined.steps ++ tail.steps ∧
      (dischargeInputs state (pivot :: rest) target conflict propagation).result.row.id =
        tail.result.row.id := by
  constructor <;> rfl

theorem dischargeInputs_supported (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (remaining target : Clause (Fin v))
    (conflict : AvailableSubclause prefixState.state (remaining.map negate ++ target))
    (propagation : ∀ input ∈ remaining, AvailableSubclause prefixState.state (target ++ [input]))
    (supported : PrefixOriginalSupport rename prefixState)
    (conflictOrigin : ResultOrigin (formula parameters).clauses.size
      (Controller.NativeProof.SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
      prefixState.steps conflict.row.id)
    (propagationOrigins : ∀ input member, ResultOrigin (formula parameters).clauses.size
      (Controller.NativeProof.SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
      prefixState.steps (propagation input member).row.id) :
    ProjectionOriginalSupport rename prefixState
      (dischargeInputs prefixState.state remaining target conflict propagation) := by
  induction remaining generalizing prefixState with
  | nil =>
      have fields := dischargeInputs_nil_fields prefixState.state target conflict propagation
      unfold ProjectionOriginalSupport
      rw [fields.1, fields.2, List.append_nil]
      exact ⟨supported, conflictOrigin⟩
  | cons pivot rest ih =>
      let reason : AvailableSubclause prefixState.state (pivot :: target) :=
        retarget (propagation pivot (by simp)) (by
          intro literal member
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member ⊢
          aesop)
      let adapted : AvailableSubclause prefixState.state
          (negate pivot :: (rest.map negate ++ target)) := by simpa using conflict
      have adaptedId : adapted.row.id = conflict.row.id := by
        dsimp only [adapted]
        apply subclause_cast_id
        simp only [List.map_cons, List.cons_append]
      have adaptedOrigin : ResultOrigin (formula parameters).clauses.size
          (Controller.NativeProof.SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
          prefixState.steps adapted.row.id := by
        rw [adaptedId]
        exact conflictOrigin
      let joined := longMerge prefixState.state pivot (rest.map negate ++ target) target adapted reason
      have joinedRun := longMerge_run prefixState.state pivot
        (rest.map negate ++ target) target adapted reason
      have joinedSupport := longMerge_supported (formula parameters).clauses.size
        (Controller.NativeProof.SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
        prefixState.steps prefixState.state pivot (rest.map negate ++ target) target adapted reason
        supported (allowed_native_count_le rename) (prefix_native_count_le rename prefixState)
        adaptedOrigin (propagationOrigins pivot (by simp))
      let current := prefixState.extend joined.state joined.steps joinedRun
      let merged := longMerge_result prefixState.state pivot (rest.map negate ++ target) target adapted reason
      let nextConflict : AvailableSubclause joined.state (rest.map negate ++ target) :=
        retarget merged (by
          intro literal member
          simp only [List.mem_append] at member ⊢
          aesop)
      let nextPropagation : ∀ input ∈ rest, AvailableSubclause joined.state (target ++ [input]) :=
        fun input member => afterTrace (propagation input (by simp [member]))
          joined.state joined.steps joinedRun
      have nextOrigins : ∀ input member, ResultOrigin (formula parameters).clauses.size
          (Controller.NativeProof.SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
          current.steps (nextPropagation input member).row.id := by
        intro input member
        exact resultOrigin_append_right (formula parameters).clauses.size
          (Controller.NativeProof.SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
          prefixState.steps joined.steps (propagation input (by simp [member])).row.id
          (propagationOrigins input (by simp [member]))
      have tailSupport := ih current nextConflict nextPropagation
        joinedSupport.1 joinedSupport.2 nextOrigins
      have fields := dischargeInputs_cons_fields prefixState.state pivot rest target conflict propagation
      unfold ProjectionOriginalSupport at tailSupport ⊢
      constructor
      · rw [fields.1]
        simpa only [current, SourcePrefix.extend, List.append_assoc] using tailSupport.1
      · rw [fields.1, fields.2]
        simpa only [current, SourcePrefix.extend, List.append_assoc] using tailSupport.2

def PairPropagationOriginalSupport (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    {context : Clause (Fin v)} {root : Literal (Fin v)}
    {pairs : List (Literal (Fin v) × Literal (Fin v))}
    (actual : PairPropagation prefixState.state context root pairs) : Prop :=
  TraceOriginalSupport (formula parameters).clauses.size
    (Controller.NativeProof.SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
    (prefixState.steps ++ actual.steps) ∧
  ∀ pair member, ResultOrigin (formula parameters).clauses.size
    (Controller.NativeProof.SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
    (prefixState.steps ++ actual.steps) (actual.results pair member).row.id


theorem pairPropagationStep_steps {state : State v} {context : Clause (Fin v)}
    {root : Literal (Fin v)} {rest : List (Literal (Fin v) × Literal (Fin v))}
    (head : Literal (Fin v) × Literal (Fin v))
    (first : SubclauseProjection state (context ++ [negate root, head.2]) 1)
    (tail : PairPropagation first.state context root rest) :
    (pairPropagationStep head first tail).steps = first.steps ++ tail.steps := rfl

theorem pairPropagationStep_head_id {state : State v} {context : Clause (Fin v)}
    {root : Literal (Fin v)} {rest : List (Literal (Fin v) × Literal (Fin v))}
    (head : Literal (Fin v) × Literal (Fin v))
    (first : SubclauseProjection state (context ++ [negate root, head.2]) 1)
    (tail : PairPropagation first.state context root rest)
    (member : head ∈ head :: rest) :
    ((pairPropagationStep head first tail).results head member).row.id = first.result.row.id := by
  simp only [pairPropagationStep, subclause_dite_id, dite_eq_left rfl] <;> rfl

theorem pairPropagationStep_tail_id {state : State v} {context : Clause (Fin v)}
    {root : Literal (Fin v)} {rest : List (Literal (Fin v) × Literal (Fin v))}
    (head : Literal (Fin v) × Literal (Fin v))
    (first : SubclauseProjection state (context ++ [negate root, head.2]) 1)
    (tail : PairPropagation first.state context root rest)
    (pair : Literal (Fin v) × Literal (Fin v))
    (member : pair ∈ head :: rest) (different : pair ≠ head) :
    ((pairPropagationStep head first tail).results pair member).row.id =
      (tail.results pair ((List.mem_cons.mp member).resolve_left different)).row.id := by
  simp only [pairPropagationStep, subclause_dite_id, dite_eq_right different] <;> rfl


theorem pairPropagationStep_supported (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    {context : Clause (Fin v)} {root : Literal (Fin v)}
    {rest : List (Literal (Fin v) × Literal (Fin v))}
    (head : Literal (Fin v) × Literal (Fin v))
    (first : SubclauseProjection prefixState.state (context ++ [negate root, head.2]) 1)
    (tail : PairPropagation first.state context root rest)
    (firstSupport : ProjectionOriginalSupport rename prefixState first)
    (tailSupport : PairPropagationOriginalSupport rename
      (prefixState.extend first.state first.steps first.checked) tail) :
    PairPropagationOriginalSupport rename prefixState (pairPropagationStep head first tail) := by
  unfold PairPropagationOriginalSupport at tailSupport ⊢
  constructor
  · rw [pairPropagationStep_steps]
    simpa only [SourcePrefix.extend, List.append_assoc] using tailSupport.1
  · intro pair member
    rw [pairPropagationStep_steps]
    by_cases same : pair = head
    · subst pair
      rw [pairPropagationStep_head_id]
      have carried := resultOrigin_append_right (formula parameters).clauses.size
        (Controller.NativeProof.SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
        (prefixState.steps ++ first.steps) tail.steps first.result.row.id firstSupport.2
      simpa only [List.append_assoc] using carried
    · rw [pairPropagationStep_tail_id head first tail pair member same]
      simpa only [SourcePrefix.extend, List.append_assoc] using
        tailSupport.2 pair ((List.mem_cons.mp member).resolve_left same)


theorem propagatePairs_supported (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (context : Clause (Fin v)) (root : Literal (Fin v))
    (pairs : List (Literal (Fin v) × Literal (Fin v)))
    (directions : ∀ pair ∈ pairs, AvailableSubclause prefixState.state [negate root, pair.1])
    (transfers : ∀ pair ∈ pairs, GuardedTransfer prefixState.state context pair.1 pair.2)
    (supported : PrefixOriginalSupport rename prefixState)
    (directionOrigins : ∀ pair member, ResultOrigin (formula parameters).clauses.size
      (Controller.NativeProof.SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
      prefixState.steps (directions pair member).row.id)
    (transferOrigins : ∀ pair member, GuardedTransferOrigin rename prefixState (transfers pair member)) :
    PairPropagationOriginalSupport rename prefixState
      (propagatePairs prefixState.state context root pairs directions transfers) := by
  induction pairs generalizing prefixState with
  | nil =>
      constructor
      · simpa only [propagatePairs, PrefixOriginalSupport, List.append_nil] using supported
      · intro pair impossible
        exact False.elim (List.not_mem_nil impossible)
  | cons head rest ih =>
      let first := guardedFromRow prefixState.state context root head.1 head.2
        (directions head (by simp)) (transfers head (by simp))
      have firstSupport := guardedFromRow_supported rename prefixState context root head.1 head.2
        (directions head (by simp)) (transfers head (by simp)) supported
        (directionOrigins head (by simp)) (transferOrigins head (by simp))
      let current := prefixState.extend first.state first.steps first.checked
      let nextDirections := fun pair (member : pair ∈ rest) => afterTrace
        (directions pair (List.mem_cons_of_mem _ member)) first.state first.steps first.checked
      let nextTransfers := fun pair (member : pair ∈ rest) => GuardedTransfer.afterTrace
        (transfers pair (List.mem_cons_of_mem _ member)) first.state first.steps first.checked
      have nextDirectionOrigins : ∀ pair member, ResultOrigin (formula parameters).clauses.size
          (Controller.NativeProof.SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
          current.steps (nextDirections pair member).row.id := by
        intro pair member
        exact resultOrigin_append_right (formula parameters).clauses.size
          (Controller.NativeProof.SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
          prefixState.steps first.steps (directions pair (List.mem_cons_of_mem _ member)).row.id
          (directionOrigins pair (List.mem_cons_of_mem _ member))
      have nextTransferOrigins : ∀ pair member,
          GuardedTransferOrigin rename current (nextTransfers pair member) := by
        intro pair member
        exact GuardedTransferOrigin.afterTrace rename prefixState
          (transfers pair (List.mem_cons_of_mem _ member))
          (transferOrigins pair (List.mem_cons_of_mem _ member)) first.state first.steps first.checked
      let tail := propagatePairs first.state context root rest nextDirections nextTransfers
      have tailSupport := ih current nextDirections nextTransfers firstSupport.1
        nextDirectionOrigins nextTransferOrigins
      exact pairPropagationStep_supported rename prefixState head first tail firstSupport tailSupport




theorem GuardedTransferOrigin.dual (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    {context : Clause (Fin v)} {input output : Literal (Fin v)}
    (transfer : GuardedTransfer prefixState.state context input output)
    (original : GuardedTransferOrigin rename prefixState transfer) :
    GuardedTransferOrigin rename prefixState
      (Controller.NativeProof.SourceStagePolarity.GuardedTransfer.dual transfer) := by
  cases transfer with
  | identity same => trivial
  | derived row =>
      simpa only [GuardedTransferOrigin,
        Controller.NativeProof.SourceStagePolarity.GuardedTransfer.dual, retarget] using original


def NotRowsOriginalSupport (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    {input output : Literal (Fin v)}
    (rows : Controller.NativeProof.SourceStagePolarity.NotRows prefixState.state input output) : Prop :=
  ResultOrigin (formula parameters).clauses.size
    (Controller.NativeProof.SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
    prefixState.steps rows.positive.row.id ∧
  ResultOrigin (formula parameters).clauses.size
    (Controller.NativeProof.SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
    prefixState.steps rows.negative.row.id

theorem guardedNot_supported (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (context : Clause (Fin v)) (leftInput rightInput leftOut rightOut : Literal (Fin v))
    (left : Controller.NativeProof.SourceStagePolarity.NotRows prefixState.state leftInput leftOut)
    (right : Controller.NativeProof.SourceStagePolarity.NotRows prefixState.state rightInput rightOut)
    (transfer : GuardedTransfer prefixState.state context rightInput leftInput)
    (supported : PrefixOriginalSupport rename prefixState)
    (leftSupport : NotRowsOriginalSupport rename prefixState left)
    (rightSupport : NotRowsOriginalSupport rename prefixState right)
    (transferSupport : GuardedTransferOrigin rename prefixState transfer) :
    ProjectionOriginalSupport rename prefixState
      (Controller.NativeProof.SourceStagePolarity.guardedNot prefixState.state context
        leftInput rightInput leftOut rightOut left right transfer) := by
  let dual := Controller.NativeProof.SourceStagePolarity.GuardedTransfer.dual transfer
  let first := guardedFromRow prefixState.state context leftOut (negate leftInput) (negate rightInput)
    left.negative dual
  have firstSupport := guardedFromRow_supported rename prefixState context
    leftOut (negate leftInput) (negate rightInput) left.negative dual supported leftSupport.2
    (GuardedTransferOrigin.dual rename prefixState transfer transferSupport)
  let current := prefixState.extend first.state first.steps first.checked
  let rightRow := afterTrace right.positive first.state first.steps first.checked
  let adapted : AvailableSubclause first.state
      (context ++ [negate (negate rightInput), rightOut]) :=
    retarget rightRow (by
      intro literal member
      simp only [negate_negate, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member ⊢
      aesop)
  have adaptedOrigin : ResultOrigin (formula parameters).clauses.size
      (Controller.NativeProof.SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
      current.steps adapted.row.id :=
    resultOrigin_append_right (formula parameters).clauses.size
      (Controller.NativeProof.SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
      prefixState.steps first.steps right.positive.row.id rightSupport.1
  have secondSupport := guardedChain_supported rename current context leftOut (negate rightInput)
    rightOut first.result adapted firstSupport.1 firstSupport.2 adaptedOrigin
  simpa only [ProjectionOriginalSupport, Controller.NativeProof.SourceStagePolarity.guardedNot,
    current, SourcePrefix.extend, first, dual, rightRow, adapted, List.append_assoc] using secondSupport


def InputProjectionOriginalSupport (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    {root : Literal (Fin v)} {inputs : Clause (Fin v)} {budget : Nat}
    (actual : InputProjection prefixState.state root inputs budget) : Prop :=
  TraceOriginalSupport (formula parameters).clauses.size
    (Controller.NativeProof.SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
    (prefixState.steps ++ actual.steps) ∧
  ∀ input member, ResultOrigin (formula parameters).clauses.size
    (Controller.NativeProof.SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
    (prefixState.steps ++ actual.steps) (actual.results input member).row.id

theorem nonunaryTreeInputs_prefixed_supported (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    {root : Literal (Fin v)} {inputs : Clause (Fin v)}
    (tree : AndTree prefixState.state root inputs) (two : 2 ≤ inputs.length)
    (original : TreeOriginals
      (Controller.NativeProof.SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) tree)
    (supported : PrefixOriginalSupport rename prefixState) :
    InputProjectionOriginalSupport rename prefixState (nonunaryTreeInputs tree two) := by
  have actual := nonunaryTreeInputs_supported tree two (formula parameters).clauses.size
    (Controller.NativeProof.SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
    original (allowed_native_count_le rename) (prefix_native_count_le rename prefixState)
  constructor
  · exact traceOriginalSupport_append (formula parameters).clauses.size
      (Controller.NativeProof.SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
      prefixState.steps (nonunaryTreeInputs tree two).steps supported actual.1
  · intro input member
    exact resultOrigin_append_left (formula parameters).clauses.size
      (Controller.NativeProof.SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
      prefixState.steps (nonunaryTreeInputs tree two).steps
      ((nonunaryTreeInputs tree two).results input member).row.id (actual.2 input member)

theorem nonunaryAggregate_origin (originalCount : Nat) (allowed : Nat → Prop)
    (steps : List (Step v)) {state : State v} {output : Literal (Fin v)}
    {inputs : Clause (Fin v)} (certificate : AggregateCertificate state output inputs)
    (two : 2 ≤ inputs.length)
    (origin : Controller.NativeProof.SourceFoldAggregateProvenance.AggregateOrigin
      originalCount allowed steps certificate) :
    ResultOrigin originalCount allowed steps (nonunaryAggregate certificate two).row.id := by
  cases certificate with
  | identity => simp at two
  | derived row => exact origin


theorem guardedAnd_supported (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (context : Clause (Fin v)) (leftOut rightOut : Literal (Fin v))
    (pairs : List (Literal (Fin v) × Literal (Fin v))) (two : 2 ≤ pairs.length)
    (leftTree : AndTree prefixState.state leftOut (pairs.map Prod.fst))
    (rightTree : AndTree prefixState.state rightOut (pairs.map Prod.snd))
    (transfers : ∀ pair ∈ pairs, GuardedTransfer prefixState.state context pair.1 pair.2)
    (leftOriginal : TreeOriginals
      (Controller.NativeProof.SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) leftTree)
    (rightOriginal : TreeOriginals
      (Controller.NativeProof.SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) rightTree)
    (supported : PrefixOriginalSupport rename prefixState)
    (transferOrigins : ∀ pair member, GuardedTransferOrigin rename prefixState (transfers pair member)) :
    ProjectionOriginalSupport rename prefixState
      (guardedAnd prefixState.state context leftOut rightOut pairs two leftTree rightTree transfers) := by
  let first := nonunaryTreeInputs leftTree (by simpa using two)
  have firstSupport := nonunaryTreeInputs_prefixed_supported rename prefixState leftTree
    (by simpa using two) leftOriginal supported
  let firstPrefix := prefixState.extend first.state first.steps first.checked
  let reflected := rightTree.afterTrace first.state first.steps first.checked
  let second := projectTreeLong reflected
  have reflectedOriginal := treeOriginals_afterTrace
    (Controller.NativeProof.SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
    rightTree rightOriginal first.state first.steps first.checked
  have secondSupport := Controller.NativeProof.SourceFoldAggregateProvenance.projectTreeLong_supported
    first.state reflected (formula parameters).clauses.size
    (Controller.NativeProof.SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
    firstPrefix.steps reflectedOriginal firstSupport.1 (allowed_native_count_le rename)
    (prefix_native_count_le rename firstPrefix)
  let secondPrefix := firstPrefix.extend second.state second.steps second.checked
  let directions := fun pair (member : pair ∈ pairs) => afterTrace
    (first.results pair.1 (List.mem_map_of_mem (f := Prod.fst) member))
    second.state second.steps second.checked
  let currentTransfers := fun pair (member : pair ∈ pairs) =>
    GuardedTransfer.afterTrace
      (GuardedTransfer.afterTrace (transfers pair member) first.state first.steps first.checked)
      second.state second.steps second.checked
  have directionOrigins : ∀ pair member, ResultOrigin (formula parameters).clauses.size
      (Controller.NativeProof.SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
      secondPrefix.steps (directions pair member).row.id := by
    intro pair member
    exact resultOrigin_append_right (formula parameters).clauses.size
      (Controller.NativeProof.SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
      firstPrefix.steps second.steps
      (first.results pair.1 (List.mem_map_of_mem (f := Prod.fst) member)).row.id
      (firstSupport.2 pair.1 (List.mem_map_of_mem (f := Prod.fst) member))
  have currentOrigins : ∀ pair member,
      GuardedTransferOrigin rename secondPrefix (currentTransfers pair member) := by
    intro pair member
    have firstOrigin := GuardedTransferOrigin.afterTrace rename prefixState
      (transfers pair member) (transferOrigins pair member) first.state first.steps first.checked
    exact GuardedTransferOrigin.afterTrace rename firstPrefix
      (GuardedTransfer.afterTrace (transfers pair member) first.state first.steps first.checked)
      firstOrigin second.state second.steps second.checked
  let third := propagatePairs second.state context leftOut pairs directions currentTransfers
  have thirdSupport := propagatePairs_supported rename secondPrefix context leftOut pairs directions
    currentTransfers secondSupport.1 directionOrigins currentOrigins
  let thirdPrefix := secondPrefix.extend third.state third.steps third.checked
  let certificate := second.result.afterTrace third.state third.steps third.checked
  have certificateOrigin := Controller.NativeProof.SourceFoldAggregateProvenance.aggregateOrigin_afterTrace
    (formula parameters).clauses.size
    (Controller.NativeProof.SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
    secondPrefix.steps third.steps second.result third.state third.checked secondSupport.2
  let aggregate := nonunaryAggregate certificate (by simpa using two)
  have aggregateOrigin := nonunaryAggregate_origin (formula parameters).clauses.size
    (Controller.NativeProof.SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
    thirdPrefix.steps certificate (by simpa using two) certificateOrigin
  let target := context ++ [negate leftOut, rightOut]
  let conflict : AvailableSubclause third.state ((pairs.map Prod.snd).map negate ++ target) :=
    retarget aggregate (by
      intro literal member
      rcases List.mem_cons.mp member with equal | rest
      · subst literal
        simp [target]
      · exact List.mem_append_left _ rest)
  let propagations : ∀ input ∈ pairs.map Prod.snd,
      AvailableSubclause third.state (target ++ [input]) := fun input member =>
    let selected := mappedChoice Prod.snd input pairs member
    let row := third.results selected.val selected.property.1
    retarget row (by
      intro literal included
      have selectedEq := selected.property.2
      simp only [target, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at included ⊢
      aesop)
  have propagationOrigins : ∀ input member, ResultOrigin (formula parameters).clauses.size
      (Controller.NativeProof.SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
      thirdPrefix.steps (propagations input member).row.id := by
    intro input member
    let selected := mappedChoice Prod.snd input pairs member
    exact thirdSupport.2 selected.val selected.property.1
  have fourthSupport := dischargeInputs_supported rename thirdPrefix (pairs.map Prod.snd)
    target conflict propagations thirdSupport.1 aggregateOrigin propagationOrigins
  simpa only [ProjectionOriginalSupport, guardedAnd, firstPrefix, secondPrefix, thirdPrefix,
    SourcePrefix.extend, first, second, reflected, directions, currentTransfers, third, certificate,
    aggregate, target, conflict, propagations, List.append_assoc] using fourthSupport


/-- A guarded projection records both the exact accumulated checked trace
and the causal origin of its surviving directional certificate. -/
def GuardedProjectionOriginalSupport (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    {context : Clause (Fin v)} {input output : Literal (Fin v)} {budget : Nat}
    (projection : GuardedProjection prefixState.state context input output budget) : Prop :=
  PrefixOriginalSupport rename (prefixState.extend projection.state projection.steps projection.checked) ∧
    GuardedTransferOrigin rename
      (prefixState.extend projection.state projection.steps projection.checked) projection.result

/-- Both directions in the paired projection share the same final causal
prefix; the first direction is carried over the second direction's trace. -/
def PairedProjectionOriginalSupport (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    {context : Clause (Fin v)} {input output : Literal (Fin v)} {budget : Nat}
    (projection : PairedProjection prefixState.state context input output budget) : Prop :=
  PrefixOriginalSupport rename (prefixState.extend projection.state projection.steps projection.checked) ∧
    DirectionPairOrigin rename
      (prefixState.extend projection.state projection.steps projection.checked) projection.pair



def singletonTransfers (state : State v) (context : Clause (Fin v))
    (pair : Literal (Fin v) × Literal (Fin v))
    (transfer : GuardedTransfer state context pair.1 pair.2) :
    ∀ query ∈ [pair], GuardedTransfer state context query.1 query.2 := by
  intro query member
  have same : query = pair := by simpa only [List.mem_cons, List.not_mem_nil, or_false] using member
  subst query
  exact transfer

theorem GuardedTransferOrigin.same_steps (rename : Nat → Fin v)
    (state : State v) (before after : List (Step v)) (same : before = after)
    (beforeChecked : runSteps (initialState (relabel rename (formula parameters))) before = some state)
    (afterChecked : runSteps (initialState (relabel rename (formula parameters))) after = some state)
    {context : Clause (Fin v)} {input output : Literal (Fin v)}
    (transfer : GuardedTransfer state context input output)
    (original : GuardedTransferOrigin rename ⟨state, before, beforeChecked⟩ transfer) :
    GuardedTransferOrigin rename ⟨state, after, afterChecked⟩ transfer := by
  cases same
  exact original

theorem guardedAndPositive_supported (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (context : Clause (Fin v)) (leftOut rightOut : Literal (Fin v))
    (pairs : List (Literal (Fin v) × Literal (Fin v))) (nonempty : pairs ≠ [])
    (leftTree : AndTree prefixState.state leftOut (pairs.map Prod.fst))
    (rightTree : AndTree prefixState.state rightOut (pairs.map Prod.snd))
    (transfers : ∀ pair ∈ pairs, GuardedTransfer prefixState.state context pair.1 pair.2)
    (leftOriginal : TreeOriginals
      (Controller.NativeProof.SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) leftTree)
    (rightOriginal : TreeOriginals
      (Controller.NativeProof.SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) rightTree)
    (supported : PrefixOriginalSupport rename prefixState)
    (transferOrigins : ∀ pair member, GuardedTransferOrigin rename prefixState (transfers pair member)) :
    GuardedProjectionOriginalSupport rename prefixState
      (guardedAndPositive prefixState.state context leftOut rightOut pairs nonempty leftTree rightTree transfers) := by
  cases pairs with
  | nil => exact False.elim (nonempty rfl)
  | cons pair rest =>
      cases rest with
      | nil =>
          have leftEq := treeRoot_singleton (input := pair.1) leftTree (by simp) (by simp)
          have rightEq := treeRoot_singleton (input := pair.2) rightTree (by simp) (by simp)
          let transfer := transfers pair (by simp)
          have origin : GuardedTransferOrigin rename prefixState transfer := transferOrigins pair (by simp)
          have transfersEq : transfers = singletonTransfers prefixState.state context pair transfer := by
            funext query member
            have same : query = pair := by simpa only [List.mem_cons, List.not_mem_nil, or_false] using member
            subst query
            rfl
          rw [transfersEq]
          cases transferEq : transfer with
          | identity same =>
              simpa only [GuardedProjectionOriginalSupport, guardedAndPositive, singletonTransfers,
                SourcePrefix.extend, List.append_nil, GuardedTransferOrigin] using
                (show PrefixOriginalSupport rename prefixState ∧ True from ⟨supported, trivial⟩)
          | derived row =>
              rw [transferEq] at origin
              simpa only [GuardedProjectionOriginalSupport, guardedAndPositive, singletonTransfers,
                SourcePrefix.extend, List.append_nil, GuardedTransferOrigin, retarget] using
                (show PrefixOriginalSupport rename prefixState ∧
                  ResultOrigin (formula parameters).clauses.size
                    (Controller.NativeProof.SourceDecoderSchedule.AllowedOriginal
                      (parameters := parameters) rename) prefixState.steps row.row.id from
                  ⟨supported, origin⟩)
      | cons second rest =>
          have actual := guardedAnd_supported rename prefixState context leftOut rightOut
            (pair :: second :: rest) (by simp) leftTree rightTree transfers
            leftOriginal rightOriginal supported transferOrigins
          simpa only [GuardedProjectionOriginalSupport, guardedAndPositive,
            ProjectionOriginalSupport, PrefixOriginalSupport, SourcePrefix.extend,
            GuardedTransferOrigin] using actual



theorem treeOriginals_mpr {state : State v} {output : Literal (Fin v)}
    {before after : List (Literal (Fin v))} (same : before = after)
    (typeEqual : AndTree state output before = AndTree state output after)
    (tree : AndTree state output after) (allowed : Nat → Prop)
    (original : TreeOriginals allowed tree) :
    TreeOriginals allowed (Eq.mpr typeEqual tree) := by
  cases same
  have proofEqual : typeEqual = rfl := Subsingleton.elim _ _
  cases proofEqual
  exact original

theorem guardedTransferOrigin_mpr (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    {context : Clause (Fin v)} {input output nextInput nextOutput : Literal (Fin v)}
    (sameInput : input = nextInput) (sameOutput : output = nextOutput)
    (typeEqual : GuardedTransfer prefixState.state context nextInput nextOutput =
      GuardedTransfer prefixState.state context input output)
    (transfer : GuardedTransfer prefixState.state context input output)
    (original : GuardedTransferOrigin rename prefixState transfer) :
    GuardedTransferOrigin rename prefixState (Eq.mpr typeEqual transfer) := by
  cases sameInput
  cases sameOutput
  have proofEqual : typeEqual = rfl := Subsingleton.elim _ _
  cases proofEqual
  exact original

theorem pairedAnd_supported (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (context : Clause (Fin v)) (leftOut rightOut : Literal (Fin v))
    (pairs : List (Literal (Fin v) × Literal (Fin v))) (nonempty : pairs ≠ [])
    (leftTree : AndTree prefixState.state leftOut (pairs.map Prod.fst))
    (rightTree : AndTree prefixState.state rightOut (pairs.map Prod.snd))
    (transfers : ∀ pair ∈ pairs, DirectionPair prefixState.state context pair.1 pair.2)
    (leftOriginal : TreeOriginals
      (Controller.NativeProof.SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) leftTree)
    (rightOriginal : TreeOriginals
      (Controller.NativeProof.SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) rightTree)
    (supported : PrefixOriginalSupport rename prefixState)
    (transferOrigins : ∀ pair member, DirectionPairOrigin rename prefixState (transfers pair member)) :
    PairedProjectionOriginalSupport rename prefixState
      (pairedAnd prefixState.state context leftOut rightOut pairs nonempty leftTree rightTree transfers) := by
  let first := guardedAndPositive prefixState.state context leftOut rightOut pairs nonempty leftTree rightTree
    (fun pair member => (transfers pair member).forward)
  have firstSupport := guardedAndPositive_supported rename prefixState context leftOut rightOut
    pairs nonempty leftTree rightTree (fun pair member => (transfers pair member).forward)
    leftOriginal rightOriginal supported (fun pair member => (transferOrigins pair member).1)
  let current := prefixState.extend first.state first.steps first.checked
  let reversed := pairs.map Prod.swap
  have reversedNonempty : reversed ≠ [] := by
    intro empty
    exact nonempty (List.map_eq_nil_iff.mp empty)
  let nextLeft : AndTree first.state rightOut (reversed.map Prod.fst) := by
    simpa only [reversed, List.map_map, Function.comp_def, Prod.fst_swap] using
      rightTree.afterTrace first.state first.steps first.checked
  let nextRight : AndTree first.state leftOut (reversed.map Prod.snd) := by
    simpa only [reversed, List.map_map, Function.comp_def, Prod.snd_swap] using
      leftTree.afterTrace first.state first.steps first.checked
  let nextTransfers := fun pair (member : pair ∈ reversed) =>
    let selected := mappedChoice Prod.swap pair pairs member
    let old := (transfers selected.val selected.property.1).backward
    (show GuardedTransfer first.state context pair.1 pair.2 from by
      have same := selected.property.2
      simpa only [← same, Prod.fst_swap, Prod.snd_swap] using
        old.afterTrace first.state first.steps first.checked)
  have nextLeftOriginal : TreeOriginals
      (Controller.NativeProof.SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) nextLeft := by
    dsimp only [nextLeft]
    apply treeOriginals_mpr (by simp only [reversed, List.map_map, Function.comp_def, Prod.fst_swap])
    exact treeOriginals_afterTrace _ rightTree rightOriginal first.state first.steps first.checked
  have nextRightOriginal : TreeOriginals
      (Controller.NativeProof.SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) nextRight := by
    dsimp only [nextRight]
    apply treeOriginals_mpr (by simp only [reversed, List.map_map, Function.comp_def, Prod.snd_swap])
    exact treeOriginals_afterTrace _ leftTree leftOriginal first.state first.steps first.checked
  have nextOrigins : ∀ pair member, GuardedTransferOrigin rename current (nextTransfers pair member) := by
    intro pair member
    let selected := mappedChoice Prod.swap pair pairs member
    have carried := GuardedTransferOrigin.afterTrace rename prefixState
      (transfers selected.val selected.property.1).backward
      (transferOrigins selected.val selected.property.1).2 first.state first.steps first.checked
    have same := selected.property.2
    dsimp only [nextTransfers]
    apply guardedTransferOrigin_mpr rename current
      (by simpa only [Prod.fst_swap] using congrArg Prod.fst same)
      (by simpa only [Prod.snd_swap] using congrArg Prod.snd same)
    exact carried
  let second := guardedAndPositive first.state context rightOut leftOut reversed reversedNonempty
    nextLeft nextRight nextTransfers
  have secondSupport := guardedAndPositive_supported rename current context rightOut leftOut
    reversed reversedNonempty nextLeft nextRight nextTransfers nextLeftOriginal nextRightOriginal
    firstSupport.1 nextOrigins
  have forwardSupport := GuardedTransferOrigin.afterTrace rename current first.result firstSupport.2
    second.state second.steps second.checked
  have both : PrefixOriginalSupport rename (current.extend second.state second.steps second.checked) ∧
      DirectionPairOrigin rename (current.extend second.state second.steps second.checked)
        ⟨first.result.afterTrace second.state second.steps second.checked, second.result⟩ :=
    ⟨secondSupport.1, forwardSupport, secondSupport.2⟩
  let finished := prefixState.extend second.state (first.steps ++ second.steps) (by
    rw [runSteps_append, first.checked]
    exact second.checked)
  change PrefixOriginalSupport rename finished ∧ DirectionPairOrigin rename finished
    ⟨first.result.afterTrace second.state second.steps second.checked, second.result⟩
  constructor
  · simpa only [PrefixOriginalSupport, finished, current, SourcePrefix.extend,
      List.append_assoc] using secondSupport.1
  · constructor
    · exact GuardedTransferOrigin.same_steps rename second.state
        ((prefixState.steps ++ first.steps) ++ second.steps)
        (prefixState.steps ++ (first.steps ++ second.steps)) (List.append_assoc _ _ _)
        _ _ (first.result.afterTrace second.state second.steps second.checked) forwardSupport
    · exact GuardedTransferOrigin.same_steps rename second.state
        ((prefixState.steps ++ first.steps) ++ second.steps)
        (prefixState.steps ++ (first.steps ++ second.steps)) (List.append_assoc _ _ _)
        _ _ second.result secondSupport.2


def reverseNegatedTransfer {state : State v} {context : Clause (Fin v)}
    {left right : Literal (Fin v)}
    (transfer : GuardedTransfer state context (negate right) (negate left)) :
    GuardedTransfer state context left right := by
  cases transfer with
  | identity same => exact .identity (by simpa only [negate_negate] using congrArg negate same.symm)
  | derived row =>
      exact .derived (retarget row (by
        intro literal member
        simp only [negate_negate, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member ⊢
        aesop))

theorem reverseNegatedTransfer_supported (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    {context : Clause (Fin v)} {left right : Literal (Fin v)}
    (transfer : GuardedTransfer prefixState.state context (negate right) (negate left))
    (original : GuardedTransferOrigin rename prefixState transfer) :
    GuardedTransferOrigin rename prefixState (reverseNegatedTransfer transfer) := by
  cases transfer with
  | identity same => trivial
  | derived row => exact original


theorem treeOriginals_mp {state : State v} {output : Literal (Fin v)}
    {before after : List (Literal (Fin v))} (same : before = after)
    (typeEqual : AndTree state output before = AndTree state output after)
    (tree : AndTree state output before) (allowed : Nat → Prop)
    (original : TreeOriginals allowed tree) : TreeOriginals allowed (Eq.mp typeEqual tree) := by
  cases same
  have proofEqual : typeEqual = rfl := Subsingleton.elim _ _
  cases proofEqual
  exact original

theorem guardedOr_supported (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (context : Clause (Fin v)) (leftOut rightOut : Literal (Fin v))
    (pairs : List (Literal (Fin v) × Literal (Fin v))) (nonempty : pairs ≠ [])
    (leftTree : AndTree prefixState.state (negate leftOut) ((pairs.map Prod.fst).map negate))
    (rightTree : AndTree prefixState.state (negate rightOut) ((pairs.map Prod.snd).map negate))
    (transfers : ∀ pair ∈ pairs, GuardedTransfer prefixState.state context pair.1 pair.2)
    (leftOriginal : TreeOriginals
      (Controller.NativeProof.SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) leftTree)
    (rightOriginal : TreeOriginals
      (Controller.NativeProof.SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) rightTree)
    (supported : PrefixOriginalSupport rename prefixState)
    (transferOrigins : ∀ pair member, GuardedTransferOrigin rename prefixState (transfers pair member)) :
    GuardedProjectionOriginalSupport rename prefixState
      (guardedOr prefixState.state context leftOut rightOut pairs nonempty leftTree rightTree transfers) := by
  let reflected := pairs.map dualPair
  let reflectedLeft : AndTree prefixState.state (negate rightOut) (reflected.map Prod.fst) := by
    simpa only [reflected, List.map_map, dualPair, Function.comp_def] using rightTree
  let reflectedRight : AndTree prefixState.state (negate leftOut) (reflected.map Prod.snd) := by
    simpa only [reflected, List.map_map, dualPair, Function.comp_def] using leftTree
  let reflectedTransfers := fun pair (member : pair ∈ reflected) =>
    let selected := mappedChoice dualPair pair pairs member
    let transfer := GuardedTransfer.dual (transfers selected.val selected.property.1)
    (show GuardedTransfer prefixState.state context pair.1 pair.2 from by
      have equal := selected.property.2
      simpa only [← equal, dualPair] using transfer)
  have reflectedLeftOriginal : TreeOriginals
      (Controller.NativeProof.SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) reflectedLeft := by
    dsimp only [reflectedLeft]
    apply treeOriginals_mpr (by simp only [reflected, List.map_map, dualPair, Function.comp_def])
    apply treeOriginals_mp (by simp only [reflected, List.map_map, dualPair, Function.comp_def])
    exact rightOriginal
  have reflectedRightOriginal : TreeOriginals
      (Controller.NativeProof.SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) reflectedRight := by
    dsimp only [reflectedRight]
    apply treeOriginals_mpr (by simp only [reflected, List.map_map, dualPair, Function.comp_def])
    apply treeOriginals_mp (by simp only [reflected, List.map_map, dualPair, Function.comp_def])
    exact leftOriginal
  have reflectedOrigins : ∀ pair member,
      GuardedTransferOrigin rename prefixState (reflectedTransfers pair member) := by
    intro pair member
    let selected := mappedChoice dualPair pair pairs member
    have actual := GuardedTransferOrigin.dual rename prefixState
      (transfers selected.val selected.property.1) (transferOrigins selected.val selected.property.1)
    have equal := selected.property.2
    dsimp only [reflectedTransfers]
    apply guardedTransferOrigin_mpr rename prefixState
      (by simpa only [dualPair] using congrArg Prod.fst equal)
      (by simpa only [dualPair] using congrArg Prod.snd equal)
    exact actual
  let joined := guardedAndPositive prefixState.state context _ _ reflected
    (by intro empty; apply nonempty; exact List.map_eq_nil_iff.mp empty)
    reflectedLeft reflectedRight reflectedTransfers
  have joinedSupport := guardedAndPositive_supported rename prefixState context _ _ reflected
    (by intro empty; apply nonempty; exact List.map_eq_nil_iff.mp empty)
    reflectedLeft reflectedRight reflectedTransfers reflectedLeftOriginal reflectedRightOriginal
    supported reflectedOrigins
  change PrefixOriginalSupport rename
      (prefixState.extend joined.state joined.steps joined.checked) ∧
    GuardedTransferOrigin rename (prefixState.extend joined.state joined.steps joined.checked)
      (reverseNegatedTransfer joined.result)
  exact ⟨joinedSupport.1, reverseNegatedTransfer_supported rename
    (prefixState.extend joined.state joined.steps joined.checked) joined.result joinedSupport.2⟩

theorem pairedOr_supported (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (context : Clause (Fin v)) (leftOut rightOut : Literal (Fin v))
    (pairs : List (Literal (Fin v) × Literal (Fin v))) (nonempty : pairs ≠ [])
    (leftTree : AndTree prefixState.state (negate leftOut) ((pairs.map Prod.fst).map negate))
    (rightTree : AndTree prefixState.state (negate rightOut) ((pairs.map Prod.snd).map negate))
    (transfers : ∀ pair ∈ pairs, DirectionPair prefixState.state context pair.1 pair.2)
    (leftOriginal : TreeOriginals
      (Controller.NativeProof.SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) leftTree)
    (rightOriginal : TreeOriginals
      (Controller.NativeProof.SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) rightTree)
    (supported : PrefixOriginalSupport rename prefixState)
    (transferOrigins : ∀ pair member, DirectionPairOrigin rename prefixState (transfers pair member)) :
    PairedProjectionOriginalSupport rename prefixState
      (pairedOr prefixState.state context leftOut rightOut pairs nonempty leftTree rightTree transfers) := by
  let first := guardedOr prefixState.state context leftOut rightOut pairs nonempty leftTree rightTree
    (fun pair member => (transfers pair member).forward)
  have firstSupport := guardedOr_supported rename prefixState context leftOut rightOut
    pairs nonempty leftTree rightTree (fun pair member => (transfers pair member).forward)
    leftOriginal rightOriginal supported (fun pair member => (transferOrigins pair member).1)
  let current := prefixState.extend first.state first.steps first.checked
  let reversed := pairs.map Prod.swap
  have reversedNonempty : reversed ≠ [] := by
    intro empty
    exact nonempty (List.map_eq_nil_iff.mp empty)
  let nextLeft : AndTree first.state (negate rightOut) ((reversed.map Prod.fst).map negate) := by
    simpa only [reversed, List.map_map, Function.comp_def, Prod.fst_swap] using
      rightTree.afterTrace first.state first.steps first.checked
  let nextRight : AndTree first.state (negate leftOut) ((reversed.map Prod.snd).map negate) := by
    simpa only [reversed, List.map_map, Function.comp_def, Prod.snd_swap] using
      leftTree.afterTrace first.state first.steps first.checked
  let nextTransfers := fun pair (member : pair ∈ reversed) =>
    let selected := mappedChoice Prod.swap pair pairs member
    let old := (transfers selected.val selected.property.1).backward
    (show GuardedTransfer first.state context pair.1 pair.2 from by
      have same := selected.property.2
      simpa only [← same, Prod.fst_swap, Prod.snd_swap] using
        old.afterTrace first.state first.steps first.checked)
  have nextLeftOriginal : TreeOriginals
      (Controller.NativeProof.SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) nextLeft := by
    dsimp only [nextLeft]
    apply treeOriginals_mpr (by simp only [reversed, List.map_map, Function.comp_def, Prod.fst_swap])
    apply treeOriginals_mp (by simp only [reversed, List.map_map, Function.comp_def, Prod.fst_swap])
    exact treeOriginals_afterTrace _ rightTree rightOriginal first.state first.steps first.checked
  have nextRightOriginal : TreeOriginals
      (Controller.NativeProof.SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) nextRight := by
    dsimp only [nextRight]
    apply treeOriginals_mpr (by simp only [reversed, List.map_map, Function.comp_def, Prod.snd_swap])
    apply treeOriginals_mp (by simp only [reversed, List.map_map, Function.comp_def, Prod.snd_swap])
    exact treeOriginals_afterTrace _ leftTree leftOriginal first.state first.steps first.checked
  have nextOrigins : ∀ pair member, GuardedTransferOrigin rename current (nextTransfers pair member) := by
    intro pair member
    let selected := mappedChoice Prod.swap pair pairs member
    have carried := GuardedTransferOrigin.afterTrace rename prefixState
      (transfers selected.val selected.property.1).backward
      (transferOrigins selected.val selected.property.1).2 first.state first.steps first.checked
    have same := selected.property.2
    dsimp only [nextTransfers]
    apply guardedTransferOrigin_mpr rename current
      (by simpa only [Prod.fst_swap] using congrArg Prod.fst same)
      (by simpa only [Prod.snd_swap] using congrArg Prod.snd same)
    exact carried
  let second := guardedOr first.state context rightOut leftOut reversed reversedNonempty
    nextLeft nextRight nextTransfers
  have secondSupport := guardedOr_supported rename current context rightOut leftOut
    reversed reversedNonempty nextLeft nextRight nextTransfers nextLeftOriginal nextRightOriginal
    firstSupport.1 nextOrigins
  have forwardSupport := GuardedTransferOrigin.afterTrace rename current first.result firstSupport.2
    second.state second.steps second.checked
  have both : PrefixOriginalSupport rename (current.extend second.state second.steps second.checked) ∧
      DirectionPairOrigin rename (current.extend second.state second.steps second.checked)
        ⟨first.result.afterTrace second.state second.steps second.checked, second.result⟩ :=
    ⟨secondSupport.1, forwardSupport, secondSupport.2⟩
  let finished := prefixState.extend second.state (first.steps ++ second.steps) (by
    rw [runSteps_append, first.checked]
    exact second.checked)
  change PrefixOriginalSupport rename finished ∧ DirectionPairOrigin rename finished
    ⟨first.result.afterTrace second.state second.steps second.checked, second.result⟩
  constructor
  · simpa only [PrefixOriginalSupport, finished, current, SourcePrefix.extend,
      List.append_assoc] using secondSupport.1
  · constructor
    · exact GuardedTransferOrigin.same_steps rename second.state
        ((prefixState.steps ++ first.steps) ++ second.steps)
        (prefixState.steps ++ (first.steps ++ second.steps)) (List.append_assoc _ _ _)
        _ _ (first.result.afterTrace second.state second.steps second.checked) forwardSupport
    · exact GuardedTransferOrigin.same_steps rename second.state
        ((prefixState.steps ++ first.steps) ++ second.steps)
        (prefixState.steps ++ (first.steps ++ second.steps)) (List.append_assoc _ _ _)
        _ _ second.result secondSupport.2





theorem directionPairOrigin_mpr (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    {context : Clause (Fin v)} {input output nextInput nextOutput : Literal (Fin v)}
    (sameInput : input = nextInput) (sameOutput : output = nextOutput)
    (typeEqual : DirectionPair prefixState.state context nextInput nextOutput =
      DirectionPair prefixState.state context input output)
    (pair : DirectionPair prefixState.state context input output)
    (original : DirectionPairOrigin rename prefixState pair) :
    DirectionPairOrigin rename prefixState (Eq.mpr typeEqual pair) := by
  cases sameInput
  cases sameOutput
  have proofEqual : typeEqual = rfl := Subsingleton.elim _ _
  cases proofEqual
  exact original

def DecoderPairTableOriginalSupport (rename : Nat → Fin v) (context : Clause (Fin v))
    (position : Nat) (table : DecoderPairTable (parameters := parameters) rename context position) : Prop :=
  PrefixOriginalSupport rename table.prefixState ∧
  ∀ node bound, DirectionPairOrigin rename table.prefixState (table.pairs node bound)

theorem decoderChildPairDirection_supported (rename : Nat → Fin v)
    (context : Clause (Fin v)) (node : Fin parameters.decoder.nodeCount)
    (children : List (Fin node.val))
    (table : DecoderPairTable (parameters := parameters) rename context node.val)
    (pair : Literal (Fin v) × Literal (Fin v))
    (member : pair ∈ decoderChildPairs rename node children)
    (supported : DecoderPairTableOriginalSupport rename context node.val table) :
    DirectionPairOrigin rename table.prefixState
      (decoderChildPairDirection rename context node children table pair member) := by
  let selected := mappedChoice
    (fun child : Fin node.val =>
      (mapLiteral rename ((decoderPositionBefore .healthy node).slots
        (.internal (.decoder .healthy (parameters.decoder.childIndex node child)))),
       mapLiteral rename ((decoderPositionBefore .faulty node).slots
        (.internal (.decoder .faulty (parameters.decoder.childIndex node child))))))
    pair children member
  have actual := supported.2 (parameters.decoder.childIndex node selected.val) selected.val.isLt
  have same := selected.property.2
  dsimp only [decoderChildPairDirection]
  apply directionPairOrigin_mpr rename table.prefixState
    (congrArg Prod.fst same) (congrArg Prod.snd same)
  dsimp only [selected] at actual
  exact actual

theorem pairedDecoderDisjunction_supported (rename : Nat → Fin v)
    (context : Clause (Fin v)) (node : Fin parameters.decoder.nodeCount)
    (children : List (Fin node.val)) (shape : parameters.decoder.node node = .disj children)
    (nonempty : children ≠ [])
    (table : DecoderPairTable (parameters := parameters) rename context node.val)
    (supported : DecoderPairTableOriginalSupport rename context node.val table) :
    PairedProjectionOriginalSupport rename table.prefixState
      (pairedDecoderDisjunction rename context node children shape nonempty table) := by
  have leftOriginal : TreeOriginals (AllowedOriginal (parameters := parameters) rename)
      (decoderDisjunctionLeftTree rename node children shape nonempty table.prefixState) := by
    dsimp only [decoderDisjunctionLeftTree]
    apply treeOriginals_mpr (by
      simp only [decoderChildPairs, List.map_map, Function.comp_def, dualLiteral])
    apply treeOriginals_mp (by
      simp only [decoderDisjunctionTree, decoderChildPairs, List.map_map, Function.comp_def, dualLiteral])
    exact treeOriginals_afterTrace _
      (decoderDisjunctionTree rename .healthy node children shape nonempty)
      (decoderDisjunctionTree_originals rename .healthy node children shape nonempty)
      table.prefixState.state table.prefixState.steps table.prefixState.checked
  have rightOriginal : TreeOriginals (AllowedOriginal (parameters := parameters) rename)
      (decoderDisjunctionRightTree rename node children shape nonempty table.prefixState) := by
    dsimp only [decoderDisjunctionRightTree]
    apply treeOriginals_mpr (by
      simp only [decoderChildPairs, List.map_map, Function.comp_def, dualLiteral])
    apply treeOriginals_mp (by
      simp only [decoderDisjunctionTree, decoderChildPairs, List.map_map, Function.comp_def, dualLiteral])
    exact treeOriginals_afterTrace _
      (decoderDisjunctionTree rename .faulty node children shape nonempty)
      (decoderDisjunctionTree_originals rename .faulty node children shape nonempty)
      table.prefixState.state table.prefixState.steps table.prefixState.checked
  exact pairedOr_supported rename table.prefixState context _ _ (decoderChildPairs rename node children)
    (decoderChildPairs_nonempty rename node children nonempty)
    (decoderDisjunctionLeftTree rename node children shape nonempty table.prefixState)
    (decoderDisjunctionRightTree rename node children shape nonempty table.prefixState)
    (fun pair member => decoderChildPairDirection rename context node children table pair member)
    leftOriginal rightOriginal supported.1
    (fun pair member => decoderChildPairDirection_supported rename context node children table pair member supported)


end Controller.NativeProof.SourceDecoderSchedule
