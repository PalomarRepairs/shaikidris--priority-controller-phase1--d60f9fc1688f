module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestWitnessAccept
public import Controller.Cost.ForestWeightedReconstruction

@[expose] public section

/-! The weighted arithmetic boundary supplies the selected declared-root and
route-pointer words. Four actual instructions retain both in separate metadata
cells. The subsequent reader reconstructs the source root through the declared
root column; it never identifies a root by an empty positional route. These
blocks are composed with the once-only descriptor loop and assignment walker.
-/
namespace Controller.Cost.ForestWitnessMarshal
open Controller.Cost Controller.Cost.GateProgram Controller.Cost.ForestCounter
open Controller.Cost.ForestMarkerMachine Controller.Cost.ForestCursorReconstruct
open Controller.Cost.ForestCursorAllRoots Controller.Cost.ForestCursorAllRootsExecution
open Controller.Cost.ForestCursorProgram Controller.Cost.ForestCursorTraversal
open Controller.Decoder Controller.Decoder.DAG
variable {width n : ℕ}

def marshalCode (width rootCell bestCell : ℕ) : ForestCounter.Code width :=
  [.constant 0 (word width rootCell), .store 0 1,
   .constant 0 (word width bestCell), .store 0 2]

def marshaled (heap : Array (Word width)) (rootCell bestCell : ℕ)
    (root pointer : Word width) : Array (Word width) :=
  (heap.setIfInBounds rootCell root).setIfInBounds bestCell pointer

@[simp] theorem marshaled_size (heap : Array (Word width)) (rootCell bestCell : ℕ)
    (root pointer : Word width) : (marshaled heap rootCell bestCell root pointer).size = heap.size := by
  simp [marshaled]

theorem marshal_execution (program : Program width 4) (heap : Array (Word width))
    (base rootCell bestCell : ℕ) (address root pointer : Word width)
    (fits : base + 4 < 2 ^ width) (heapFits : heap.size ≤ 2 ^ width)
    (rootValid : rootCell < heap.size) (bestValid : bestCell < heap.size)
    (block : BlockAt program base (marshalCode width rootCell bestCell)) :
    Execution program (counterState heap base address root pointer)
      (counterState (marshaled heap rootCell bestCell root pointer) (base + 4)
        (word width bestCell) root pointer) 4 (5 + heap.size) := by
  have a := address_transition program heap base rootCell address root pointer (by omega)
    (by simpa only [marshalCode, List.getElem?_cons_zero, Nat.add_zero] using block 0 (by simp [marshalCode]))
  have b := store_transition program heap (base + 1) rootCell root pointer (by omega)
    (by omega) rootValid (by simpa [marshalCode] using block 1 (by simp [marshalCode]))
  have c := address_transition program (heap.set rootCell root) (base + 2) bestCell
    (word width rootCell) root pointer (by omega) (by simpa [marshalCode] using block 2 (by simp [marshalCode]))
  have d := store_temporary_transition program (heap.set rootCell root) (base + 3)
    bestCell root pointer (by omega) (by omega) (by simpa using bestValid)
    (by simpa [marshalCode] using block 3 (by simp [marshalCode]))
  simp only [Nat.add_assoc] at b c d
  have heapEq : marshaled heap rootCell bestCell root pointer =
      (heap.set rootCell root rootValid).set bestCell pointer (by simpa using bestValid) := by
    simp only [marshaled, Array.setIfInBounds_def, rootValid, dite_eq_left,
      Array.size_set, bestValid]
  have trace := Execution.cons a (Execution.cons b (Execution.cons c (Execution.cons d
    (Execution.refl (counterState ((heap.set rootCell root rootValid).set bestCell pointer (by simpa using bestValid))
      (base + 4) (word width bestCell) root pointer)))))
  simpa only [heapEq, counterState_liveWords, Array.size_set, Nat.zero_add, Nat.max_self] using trace

private theorem set_other (heap : Array (Word width)) (cell address : ℕ) (value : Word width)
    (different : address ≠ cell) : (heap.setIfInBounds cell value)[address]? = heap[address]? := by
  by_cases valid : cell < heap.size
  · rw [Array.setIfInBounds_def, dite_eq_left valid]
    exact Array.getElem?_set_ne valid (Ne.symm different)
  · simp [Array.setIfInBounds_def, valid]

/-- Both stores retain every source, descriptor and counter coordinate other
than their two explicit metadata addresses. -/
theorem marshaled_other (heap : Array (Word width)) (rootCell bestCell address : ℕ)
    (root pointer : Word width) (notRoot : address ≠ rootCell) (notBest : address ≠ bestCell) :
    (marshaled heap rootCell bestCell root pointer)[address]? = heap[address]? := by
  unfold marshaled
  exact (set_other _ bestCell address pointer notBest).trans (set_other _ rootCell address root notRoot)

private theorem advance (heap : Array (Word width)) (cursor : ℕ)
    (address loaded temporary : Word width) (fits : cursor < 2 ^ width) :
    (counterState heap cursor address loaded temporary).advance =
      counterState heap (cursor + 1) address loaded temporary := by
  unfold State.advance counterState
  rw [show (word width cursor).val = cursor from Nat.mod_eq_of_lt fits]

private theorem putAddress (heap : Array (Word width)) (cursor : ℕ)
    (address loaded temporary value : Word width) :
    (counterState heap cursor address loaded temporary).put 0 value =
      counterState heap cursor value loaded temporary := by
  unfold State.put counterState
  congr 1
  funext register
  by_cases zero : register = 0 <;> simp [zero]

/-- One actual fetched indirect read retains both other working registers. -/
theorem load_address_transition (program : Program width 4) (heap : Array (Word width))
    (cursor address : ℕ) (loaded temporary value : Word width)
    (pcFits : cursor < 2 ^ width) (addressFits : address < 2 ^ width)
    (valid : address < heap.size) (held : heap[address] = value)
    (fetched : program[cursor]? = some (.load 0 0)) :
    programStep program (counterState heap cursor (word width address) loaded temporary) =
      some (counterState heap (cursor + 1) value loaded temporary) := by
  unfold programStep
  rw [show (counterState heap cursor (word width address) loaded temporary).pc.val = cursor from
    Nat.mod_eq_of_lt pcFits, fetched]
  change step (.load (0 : Fin 4) 0) (counterState heap cursor (word width address) loaded temporary) = _
  simp only [step, counterState, Bool.false_eq_true, ite_false]
  change (if bound : (word width address).val < heap.size then
    some ((counterState heap cursor (word width address) loaded temporary).advance.put 0
      heap[(word width address).val]) else none) = _
  have valueEq : (word width address).val = address := Nat.mod_eq_of_lt addressFits
  rw [dite_eq_left (by simpa only [valueEq] using valid)]
  simp only [valueEq, held]
  rw [advance heap cursor _ loaded temporary pcFits, putAddress]
  rfl

/-- Read the persisted pointer before the sole descriptor reconstruction. -/
def pointerCode (width bestCell : ℕ) : ForestCounter.Code width :=
  [.constant 0 (word width bestCell), .load 0 0]

theorem pointer_execution (program : Program width 4) (heap : Array (Word width))
    (base bestCell : ℕ) (address loaded temporary pointer : Word width)
    (fits : base + 2 < 2 ^ width) (heapFits : heap.size ≤ 2 ^ width)
    (valid : bestCell < heap.size) (held : heap[bestCell] = pointer)
    (block : BlockAt program base (pointerCode width bestCell)) :
    Execution program (counterState heap base address loaded temporary)
      (counterState heap (base + 2) pointer loaded temporary) 2 (5 + heap.size) := by
  have a := address_transition program heap base bestCell address loaded temporary (by omega)
    (by simpa [pointerCode] using block 0 (by simp [pointerCode]))
  have b := load_address_transition program heap (base + 1) bestCell loaded temporary pointer
    (by omega) (by omega) valid held (by simpa [pointerCode] using block 1 (by simp [pointerCode]))
  simp only [Nat.add_assoc] at b
  simpa only [counterState_liveWords, Nat.zero_add, Nat.max_self] using
    Execution.cons a (Execution.cons b (Execution.refl
      (counterState heap (base + 2) pointer loaded temporary)))

/-- The actual stored declared-root ID indexes the loaded root column. -/
def rootCode (width rootCell rootBase : ℕ) : ForestCounter.Code width :=
  [.constant 0 (word width rootCell), .load 0 0,
   .constant 1 (word width rootBase), .add 0 0 1, .load 0 0]

theorem root_execution (program : Program width 4) (heap : Array (Word width))
    (base rootCell rootBase identifier : ℕ) (address loaded temporary node : Word width)
    (fits : base + 5 < 2 ^ width) (heapFits : heap.size ≤ 2 ^ width)
    (identifierFits : identifier < 2 ^ width) (rootBaseFits : rootBase < 2 ^ width)
    (cellValid : rootCell < heap.size) (sourceValid : identifier + rootBase < heap.size)
    (rootHeld : heap[rootCell] = word width identifier)
    (sourceHeld : heap[identifier + rootBase] = node)
    (block : BlockAt program base (rootCode width rootCell rootBase)) :
    Execution program (counterState heap base address loaded temporary)
      (counterState heap (base + 5) node (word width rootBase) temporary) 5 (5 + heap.size) := by
  have a := address_transition program heap base rootCell address loaded temporary (by omega)
    (by simpa [rootCode] using block 0 (by simp [rootCode]))
  have b := load_address_transition program heap (base + 1) rootCell loaded temporary (word width identifier)
    (by omega) (by omega) cellValid rootHeld (by simpa [rootCode] using block 1 (by simp [rootCode]))
  have c := constant_loaded_transition program heap (base + 2) (word width identifier)
    loaded temporary (word width rootBase) (by omega) (by simpa [rootCode] using block 2 (by simp [rootCode]))
  have d := add_address_transition program heap (base + 3) (word width identifier)
    (word width rootBase) temporary (by omega) (by simpa [rootCode] using block 3 (by simp [rootCode]))
  have identifierValue : (word width identifier).val = identifier := Nat.mod_eq_of_lt identifierFits
  have baseValue : (word width rootBase).val = rootBase := Nat.mod_eq_of_lt rootBaseFits
  simp only [identifierValue, baseValue] at d
  have e := load_address_transition program heap (base + 4) (identifier + rootBase)
    (word width rootBase) temporary node (by omega) (by omega) sourceValid sourceHeld
    (by simpa [rootCode] using block 4 (by simp [rootCode]))
  simp only [Nat.add_assoc] at b c d e
  have trace := Execution.cons a (Execution.cons b (Execution.cons c (Execution.cons d
    (Execution.cons e (Execution.refl
      (counterState heap (base + 5) node (word width rootBase) temporary))))))
  simpa only [counterState_liveWords, Nat.zero_add, Nat.max_self] using trace

/-- The two metadata words are read back from the actual store result. -/
theorem marshaled_pointer (heap : Array (Word width)) (rootCell bestCell : ℕ)
    (root pointer : Word width) (valid : bestCell < heap.size) :
    (marshaled heap rootCell bestCell root pointer)[bestCell]'
      (by simpa only [marshaled_size] using valid) = pointer := by
  have bound : bestCell < (heap.setIfInBounds rootCell root).size := by simpa using valid
  have stored : (marshaled heap rootCell bestCell root pointer)[bestCell]? = some pointer := by
    unfold marshaled
    rw [Array.setIfInBounds_def, dite_eq_left bound]
    simp only [Array.getElem?_set_self]
  rw [Array.getElem?_eq_getElem (by simpa only [marshaled_size] using valid)] at stored
  exact Option.some.inj stored

theorem marshaled_root (heap : Array (Word width)) (rootCell bestCell : ℕ)
    (root pointer : Word width) (valid : rootCell < heap.size) (different : rootCell ≠ bestCell) :
    (marshaled heap rootCell bestCell root pointer)[rootCell]'
      (by simpa only [marshaled_size] using valid) = root := by
  have retained := set_other (heap.setIfInBounds rootCell root) bestCell rootCell pointer different
  have first : (heap.setIfInBounds rootCell root)[rootCell]? = some root := by
    rw [Array.setIfInBounds_def, dite_eq_left valid]
    simp only [Array.getElem?_set_self]
  have current := retained.trans first
  rw [Array.getElem?_eq_getElem (by simp only [Array.size_setIfInBounds]; exact valid)] at current
  exact Option.some.inj current

/-- One fixed prelude persists root identity, reloads the selected pointer,
reconstructs exactly once, and finally reads the root node from the original
stored declared-root column. None of its loop code depends on route length. -/
def preludeCode (width base rootCell bestCell descriptorBase rootBase : ℕ) : ForestCounter.Code width :=
  marshalCode width rootCell bestCell ++ pointerCode width bestCell ++
    reconstructCode width (base + 6) descriptorBase ++ rootCode width rootCell rootBase

@[simp] theorem preludeCode_length (width base rootCell bestCell descriptorBase rootBase : ℕ) :
    (preludeCode width base rootCell bestCell descriptorBase rootBase).length = 25 := rfl

/-- Complete fetched prelude. The represented descriptors must be the rebased
once-materialized source store. The source-word premise is its actual retained
root-column cell, not a supplied evaluation or a positional-route oracle. -/
theorem prelude_execution (program : Program width 4) (heap : Array (Word width))
    (base rootCell bestCell rootBase identifier pointer : ℕ)
    (address node : Word width)
    (routes : RouteDescriptors width (marshaled heap rootCell bestCell
      (word width identifier) (word width pointer)))
    (fits : base + 25 < 2 ^ width) (heapFits : heap.size ≤ 2 ^ width)
    (rootValid : rootCell < heap.size) (bestValid : bestCell < heap.size)
    (different : rootCell ≠ bestCell)
    (identifierFits : identifier < 2 ^ width) (rootBaseFits : rootBase < 2 ^ width)
    (sourceValid : identifier + rootBase < heap.size)
    (sourceNotRoot : identifier + rootBase ≠ rootCell)
    (sourceNotBest : identifier + rootBase ≠ bestCell)
    (sourceHeld : heap[identifier + rootBase] = node)
    (countFits : routes.count < 2 ^ width) (bounded : pointer ≤ routes.count)
    (stack output : List (Word width))
    (block : BlockAt program base (preludeCode width base rootCell bestCell routes.base rootBase)) :
    ∃ finalTemporary,
      Execution program ((counterState heap base address (word width identifier)
        (word width pointer)).frame stack output)
        ((counterState (marshaled heap rootCell bestCell (word width identifier) (word width pointer))
          (base + 25) node (word width rootBase) finalTemporary).frame
          ((routes.route pointer).reverse.map (word width) ++ stack) output)
        (14 * (routes.route pointer).length + 12)
        (5 + heap.size + ((routes.route pointer).length + stack.length + output.length)) := by
  let current := marshaled heap rootCell bestCell (word width identifier) (word width pointer)
  have firstBlock : BlockAt program base (marshalCode width rootCell bestCell) :=
    BlockAt.prefix program base _ _ block
  have afterMarshal : BlockAt program (base + 4)
      (pointerCode width bestCell ++ reconstructCode width (base + 6) routes.base ++
        rootCode width rootCell rootBase) := by
    simpa [marshalCode, pointerCode, List.append_assoc] using
      BlockAt.suffix program base (marshalCode width rootCell bestCell) _ block
  have pointerBlock : BlockAt program (base + 4) (pointerCode width bestCell) :=
    BlockAt.prefix program (base + 4) _ _ afterMarshal
  have afterPointer : BlockAt program (base + 6)
      (reconstructCode width (base + 6) routes.base ++ rootCode width rootCell rootBase) := by
    simpa [pointerCode, reconstructCode, Nat.add_assoc] using
      BlockAt.suffix program (base + 4) (pointerCode width bestCell) _ afterMarshal
  have reconstructBlock : BlockAt program (base + 6)
      (reconstructCode width (base + 6) routes.base) :=
    BlockAt.prefix program (base + 6) _ _ afterPointer
  have rootBlock : BlockAt program (base + 20) (rootCode width rootCell rootBase) := by
    simpa only [reconstructCode_length, Nat.add_assoc] using
      BlockAt.suffix program (base + 6) (reconstructCode width (base + 6) routes.base) _ afterPointer
  have stored := (marshal_execution program heap base rootCell bestCell address
    (word width identifier) (word width pointer) (by omega) heapFits rootValid bestValid firstBlock).frame stack output
  have read := (pointer_execution program current (base + 4) bestCell (word width bestCell)
    (word width identifier) (word width pointer) (word width pointer) (by omega)
    (by simpa only [current, marshaled_size] using heapFits)
    (by simpa only [current, marshaled_size] using bestValid)
    (marshaled_pointer heap rootCell bestCell _ _ bestValid) pointerBlock).frame stack output
  obtain ⟨loaded, temporary, reconstructed⟩ := route_execution program current routes
    (base + 6) pointer countFits (by simpa only [current, marshaled_size] using heapFits)
    (by omega) reconstructBlock bounded (word width identifier) (word width pointer) stack output
  have preserved : current[identifier + rootBase]'
      (by simpa only [current, marshaled_size] using sourceValid) = node := by
    have retained := marshaled_other heap rootCell bestCell (identifier + rootBase)
      (word width identifier) (word width pointer) sourceNotRoot sourceNotBest
    rw [Array.getElem?_eq_getElem sourceValid,
      Array.getElem?_eq_getElem (by simpa only [current, marshaled_size] using sourceValid)] at retained
    exact (Option.some.inj retained).trans sourceHeld
  have root := (root_execution program current (base + 20) rootCell rootBase identifier
    (word width 0) loaded temporary node (by omega)
    (by simpa only [current, marshaled_size] using heapFits) identifierFits rootBaseFits
    (by simpa only [current, marshaled_size] using rootValid)
    (by simpa only [current, marshaled_size] using sourceValid)
    (marshaled_root heap rootCell bestCell _ _ rootValid different) preserved rootBlock).frame
      ((routes.route pointer).reverse.map (word width) ++ stack) output
  refine ⟨temporary, ?_⟩
  have joined := ((stored.append read).append reconstructed).append root
  convert joined using 1 <;>
    simp only [current, marshaled_size, State.frame_liveWords, counterState_liveWords,
      List.length_append, List.length_map, List.length_reverse] <;> omega

open Controller.Cost.ForestCursorExecution Controller.Cost.ForestWitnessWalk
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestCursorDescriptors
open Controller.Cost.ForestWeightedTagged Controller.Cost.ForestWeightedGlobal
open Controller.Cost.ForestWeightedPhysicalOptimal

/-- Metadata is inside the existing shared setup allocation, beyond both the
original source packet and the parent descriptor prefix. -/
def selectedHeap (width : ℕ) (packet : Array (Word width)) (graph : DAG n)
    (identifier pointer : ℕ) : Array (Word width) :=
  marshaled (setupHeap width packet graph) (provenanceCell packet graph)
    (setupLayout packet graph).best (word width identifier) (word width pointer)

theorem selected_frame (packet : Array (Word width)) (graph : DAG n)
    (records : GraphRecords width packet graph)
    (countFits : (buildRoots graph).count < 2 ^ width)
    (positionFits : ∀ entry ∈ (buildRoots graph).entries, entry.position < 2 ^ width)
    (identifier pointer : ℕ) :
    PersistentFrame graph (setupRecords width packet graph records)
      (setupRoutes width packet graph countFits positionFits)
      (selectedHeap width packet graph identifier pointer) := by
  refine ⟨by simp only [selectedHeap, marshaled_size], ?_⟩
  intro address present
  have before := setup_persistent_before width packet graph records countFits positionFits address present
  exact marshaled_other (setupHeap width packet graph) (provenanceCell packet graph)
    (setupLayout packet graph).best address (word width identifier) (word width pointer)
    (by simp only [provenanceCell]; omega) (by simp only [setupLayout]; omega)

def selectedRoutes (width : ℕ) (packet : Array (Word width)) (graph : DAG n)
    (records : GraphRecords width packet graph)
    (countFits : (buildRoots graph).count < 2 ^ width)
    (positionFits : ∀ entry ∈ (buildRoots graph).entries, entry.position < 2 ^ width)
    (identifier pointer : ℕ) : RouteDescriptors width (selectedHeap width packet graph identifier pointer) :=
  rebaseRoutes graph (setupRecords width packet graph records)
    (setupRoutes width packet graph countFits positionFits) _
    (selected_frame packet graph records countFits positionFits identifier pointer)

/-- This route is the original source-derived allocation route, even after the
candidate metadata stores. Empty routes retain their declared-root word. -/
theorem selected_route (packet : Array (Word width)) (graph : DAG n)
    (records : GraphRecords width packet graph)
    (countFits : (buildRoots graph).count < 2 ^ width)
    (positionFits : ∀ entry ∈ (buildRoots graph).entries, entry.position < 2 ^ width)
    (identifier pointer coordinate : ℕ) :
    (selectedRoutes width packet graph records countFits positionFits identifier pointer).route coordinate =
      (setupRoutes width packet graph countFits positionFits).route coordinate := rfl

/-- Every actual counter word stays zero through the metadata marshalling.
This derives reusable marker storage from the once-only setup itself. -/
theorem selected_marker_zero (packet : Array (Word width)) (graph : DAG n)
    (identifier pointer : ℕ) (channel : Channel n) :
    (selectedHeap width packet graph identifier pointer)[setupOffset packet graph + channel.val]'
      (by simp only [selectedHeap, marshaled_size, setupHeap_size]; unfold setupOffset; have := channel.isLt; omega) =
      boolWord width false := by
  have valid : setupOffset packet graph + channel.val < (setupHeap width packet graph).size := by
    rw [setupHeap_size]; unfold setupOffset; have := channel.isLt; omega
  have preserved := marshaled_other (setupHeap width packet graph) (provenanceCell packet graph)
    (setupLayout packet graph).best (setupOffset packet graph + channel.val)
    (word width identifier) (word width pointer)
    (by simp only [provenanceCell]; have := channel.isLt; omega)
    (by simp only [setupLayout]; have := channel.isLt; omega)
  rw [Array.getElem?_eq_getElem valid,
    Array.getElem?_eq_getElem (by simpa only [marshaled_size] using valid)] at preserved
  have zero := setup_zero width packet graph channel.val (by have := channel.isLt; omega)
  simpa only [selectedHeap, boolWord, Bool.false_eq_true, ite_false] using
    (Option.some.inj preserved).trans zero


/-- Metadata stores retain every source coordinate below the reused counter
region; this includes the arity/base columns absent from the descriptor frame. -/
theorem selected_prefix (packet : Array (Word width)) (graph : DAG n)
    (identifier pointer address : ℕ) (before : address < setupOffset packet graph) :
    (selectedHeap width packet graph identifier pointer)[address]? =
      (setupHeap width packet graph)[address]? := by
  exact marshaled_other _ (provenanceCell packet graph) (setupLayout packet graph).best address
    (word width identifier) (word width pointer)
    (by simp only [provenanceCell]; omega) (by simp only [setupLayout]; omega)

private theorem selected_read (packet : Array (Word width)) (graph : DAG n)
    (identifier pointer address : ℕ) (before : address < setupOffset packet graph)
    (valid : address < (setupHeap width packet graph).size) :
    (selectedHeap width packet graph identifier pointer)[address]'
      (by simpa only [selectedHeap, marshaled_size] using valid) =
      (setupHeap width packet graph)[address]'valid := by
  have same := selected_prefix packet graph identifier pointer address before
  rw [Array.getElem?_eq_getElem valid,
    Array.getElem?_eq_getElem (by simpa only [selectedHeap, marshaled_size] using valid)] at same
  exact Option.some.inj same

/-- The actual loaded declared-root cell survives descriptor allocation and both
metadata stores. Repeated roots and empty positional routes retain their IDs. -/
theorem selected_root_word (heap : Array (Word width)) (graph : DAG n)
    (rows : List Row) (roots : List ℕ) (matched : RootsMatch graph roots)
    (position : Fin graph.roots.length) (identifier pointer : ℕ) :
    let rootBase := heap.size + 6 * rows.length + (rowChildren rows).length + (rowGuards rows).length
    (selectedHeap width (cacheHeap width heap rows roots) graph identifier pointer)[position.val + rootBase]'
      (by
        have lengths : roots.length = graph.roots.length := by rw [matched, List.length_map]
        have bounded := position.isLt
        simp only [selectedHeap, marshaled_size, setupHeap_size, cacheHeap_size]
        omega) = word width (graph.roots.get position).val := by
  dsimp only
  have valid : position.val + (heap.size + 6 * rows.length + (rowChildren rows).length +
      (rowGuards rows).length) < (cacheHeap width heap rows roots).size := by
    have lengths : roots.length = graph.roots.length := by rw [matched, List.length_map]
    have bounded := position.isLt
    simp only [cacheHeap_size]; omega
  have retained := selected_prefix (cacheHeap width heap rows roots) graph identifier pointer
    (position.val + (heap.size + 6 * rows.length + (rowChildren rows).length +
      (rowGuards rows).length)) (by unfold setupOffset; omega)
  have allocated := setup_prefix width (cacheHeap width heap rows roots) graph _ valid
  have same := retained.trans allocated
  have stored := cache_declared_root_word heap graph rows roots matched position
  have finalValid : position.val + (heap.size + 6 * rows.length + (rowChildren rows).length +
      (rowGuards rows).length) < (selectedHeap width (cacheHeap width heap rows roots)
        graph identifier pointer).size := by
    simp only [selectedHeap, marshaled_size, setupHeap_size]; omega
  rw [Array.getElem?_eq_getElem finalValid, Array.getElem?_eq_getElem valid] at same
  exact (Option.some.inj same).trans (by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using stored)

/-- Rebase every actual source field, including the physical column words,
after the two selector stores. The same allocated counter region is reused. -/
def prefixSource (initial current : Array (Word width)) (graph : DAG n)
    (layout : ForestWitnessPath.Layout) (source : WalkSource width initial graph layout)
    (sizeEq : current.size = initial.size)
    (prefixEq : ∀ address, address < layout.markerBase → current[address]? = initial[address]?) :
    WalkSource width current graph layout := by
  have read (address : ℕ) (before : address < layout.markerBase) (valid : address < initial.size) :
      current[address]'(by rw [sizeEq]; exact valid) = initial[address]'valid := by
    have equality := prefixEq address before
    rw [Array.getElem?_eq_getElem valid,
      Array.getElem?_eq_getElem (by rw [sizeEq]; exact valid)] at equality
    exact Option.some.inj equality
  let records : GraphRecords width current graph := {
    recordBase := source.records.recordBase
    childBase := source.records.childBase
    guardBase := source.records.guardBase
    tagValid := fun node => by rw [sizeEq]; exact source.records.tagValid node
    tagWord := fun node => (read _ (source.tagBefore node) (source.records.tagValid node)).trans
      (source.records.tagWord node)
    headValid := fun node => by rw [sizeEq]; exact source.records.headValid node
    headWord := fun node head gate => (read _ (source.headBefore node) (source.records.headValid node)).trans
      (source.records.headWord node head gate)
    childValid := fun node position => by rw [sizeEq]; exact source.records.childValid node position
    childWord := fun node position => (read _ (source.childBefore node position)
      (source.records.childValid node position)).trans (source.records.childWord node position)
    guardValid := fun node position => by rw [sizeEq]; exact source.records.guardValid node position
    guardWord := fun node position => (read _ (source.guardBefore node position)
      (source.records.guardValid node position)).trans (source.records.guardWord node position) }
  exact {
    records := records
    header := source.header
    region := by rw [sizeEq]; exact source.region
    tagBefore := source.tagBefore
    headBefore := source.headBefore
    childBefore := source.childBefore
    guardBefore := source.guardBefore
    childColumnBefore := source.childColumnBefore
    guardColumnBefore := source.guardColumnBefore
    arityColumnBefore := source.arityColumnBefore
    childColumnWord := fun node => (read _ (source.childColumnBefore node)
      (by have := source.childColumnBefore node; have := source.region; omega)).trans
        (source.childColumnWord node)
    guardColumnWord := fun node => (read _ (source.guardColumnBefore node)
      (by have := source.guardColumnBefore node; have := source.region; omega)).trans
        (source.guardColumnWord node)
    arityColumnWord := fun node => (read _ (source.arityColumnBefore node)
      (by have := source.arityColumnBefore node; have := source.region; omega)).trans
        (source.arityColumnWord node)
    guardEndFits := source.guardEndFits }


/-- Instantiate the generic heap transport with the two actual selector stores. -/
def selectedSource (packet : Array (Word width)) (graph : DAG n)
    (layout : ForestWitnessPath.Layout)
    (source : WalkSource width (setupHeap width packet graph) graph layout)
    (marker : layout.markerBase = setupOffset packet graph)
    (identifier pointer : ℕ) :
    WalkSource width (selectedHeap width packet graph identifier pointer) graph layout :=
  prefixSource _ _ graph layout source (by simp only [selectedHeap, marshaled_size])
    (fun address before => selected_prefix packet graph identifier pointer address
      (by simpa only [← marker] using before))


/-- Abstract state accounting does not unfold the source allocator or the
shared descriptor compiler when instantiated by the full caller. -/
theorem ready_liveWords (heap : Array (Word width)) (cursor : ℕ)
    (address loaded temporary : Word width) (route : List ℕ)
    (stack output : List (Word width)) :
    ((counterState heap cursor address loaded temporary).frame
      (route.reverse.map (word width) ++ stack) output).liveWords =
      5 + heap.size + (route.length + stack.length + output.length) := by
  simp only [State.frame_liveWords, counterState_liveWords, List.length_append,
    List.length_map, List.length_reverse, Nat.add_assoc]

/-- A proof-level opaque name for the concrete entry frame. Source arrays
are not evaluated while an execution consumer inspects its register fields. -/
@[irreducible] def ready_state (heap : Array (Word width)) (cursor : ℕ)
    (root rootBase temporary : Word width) (route : List ℕ)
    (stack output : List (Word width)) : State width 4 :=
  (counterState heap cursor root rootBase temporary).frame (route.map (word width) ++ stack) output

theorem ready_state_eq (heap : Array (Word width)) (cursor : ℕ)
    (root rootBase temporary : Word width) (route : List ℕ)
    (stack output : List (Word width)) :
    ready_state heap cursor root rootBase temporary route stack output =
      (counterState heap cursor root rootBase temporary).frame (route.map (word width) ++ stack) output := by
  unfold ready_state
  rfl

theorem ready_state_heap (heap : Array (Word width)) (cursor : ℕ)
    (root rootBase temporary : Word width) (route : List ℕ)
    (stack output : List (Word width)) :
    (ready_state heap cursor root rootBase temporary route stack output).heap = heap := by
  rw [ready_state_eq]
  rfl

theorem ready_state_fields (heap : Array (Word width)) (cursor : ℕ)
    (root rootBase temporary : Word width) (route : List ℕ)
    (stack output : List (Word width)) :
    let state := ready_state heap cursor root rootBase temporary route stack output
    state.reg 0 = root ∧ state.stack = route.map (word width) ++ stack ∧
      state.pc = word width cursor ∧ state.halted = false ∧ state.output = output := by
  rw [ready_state_eq]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Transport source witnesses through an explicit heap field equality. Only
that equality is eliminated; no source-cache or descriptor builder is reduced. -/
theorem source_on_state (state : State width 4) (heap : Array (Word width))
    (graph : DAG n) (layout : ForestWitnessPath.Layout) (heapEq : state.heap = heap)
    (source : WalkSource width heap graph layout) (markers : MarkerCells source ∅)
    (countAddress : ℕ) (countBefore : countAddress < layout.markerBase)
    (stored : heap[countAddress]'(by have := source.region; omega) = word width n) :
    ∃ transported : WalkSource width state.heap graph layout,
      MarkerCells transported ∅ ∧
      state.heap[countAddress]'(by have := transported.region; omega) = word width n := by
  cases heapEq
  exact ⟨source, markers, stored⟩

/-- The actual original count header survives all once-only allocations and
both candidate stores. No reconstructed source length is a machine oracle. -/
theorem selected_count_word (heap : Array (Word width)) (graph : DAG n)
    (rows : List Row) (roots : List ℕ) (identifier pointer countAddress : ℕ)
    (countValid : countAddress < heap.size) (countWord : heap[countAddress] = word width n) :
    (selectedHeap width (cacheHeap width heap rows roots) graph identifier pointer)[countAddress]'
      (by simp only [selectedHeap, marshaled_size, setupHeap_size, cacheHeap_size]; omega) = word width n := by
  let packet := cacheHeap width heap rows roots
  have before : countAddress < setupOffset packet graph := by
    simp only [setupOffset, packet, cacheHeap_size]; omega
  have current := selected_prefix packet graph identifier pointer countAddress before
  have allocated := setup_prefix width packet graph countAddress
    (by simp only [packet, cacheHeap_size]; omega)
  have loaded := Controller.Cost.ForestCursorMaterialize.allocatedHeap_prefix width heap
    (serializedRows heap.size rows roots) countAddress countValid
  have equality := current.trans (allocated.trans loaded)
  rw [Array.getElem?_eq_getElem countValid,
    Array.getElem?_eq_getElem (by
      simp only [selectedHeap, marshaled_size, setupHeap_size, packet, cacheHeap_size]; omega)] at equality
  exact (Option.some.inj equality).trans countWord


/-- Package actual source and zero-counter geometry as proof witnesses, so the
fetched walk consumes an abstract validated source instead of repeatedly
reducing the allocator, cache constructor and source transport definitions. -/
theorem selected_ready_source (heap : Array (Word width)) (graph : DAG n)
    (rows : List Row) (roots : List ℕ) (matched : RowsMatch graph rows)
    (identifier pointer countAddress : ℕ) (countValid : countAddress < heap.size)
    (countWord : heap[countAddress] = word width n)
    (heapFits : (setupHeap width (cacheHeap width heap rows roots) graph).size ≤ 2 ^ width) :
    let packet := cacheHeap width heap rows roots
    let layout := ForestWitnessPath.packetLayout heap.size rows.length (setupOffset packet graph)
    ∃ source : WalkSource width (selectedHeap width packet graph identifier pointer) graph layout,
      MarkerCells source ∅ ∧ countAddress < layout.markerBase ∧
      (selectedHeap width packet graph identifier pointer)[countAddress]'
        (by simp only [selectedHeap, marshaled_size, setupHeap_size, packet, cacheHeap_size]; omega) = word width n := by
  dsimp only
  let packet := cacheHeap width heap rows roots
  let layout := ForestWitnessPath.packetLayout heap.size rows.length (setupOffset packet graph)
  let originalSource := loadedSource heap graph rows roots matched heapFits
  let source := selectedSource packet graph layout originalSource rfl identifier pointer
  have markers : MarkerCells source ∅ := by
    intro channel
    simpa only [source, layout, ForestWitnessPath.packetLayout, Finset.notMem_empty, decide_false] using
      selected_marker_zero packet graph identifier pointer channel
  refine ⟨source, markers, ?_, selected_count_word heap graph rows roots identifier pointer
    countAddress countValid countWord⟩
  simp only [layout, ForestWitnessPath.packetLayout, setupOffset, packet, cacheHeap_size]
  omega

variable {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]

/-- The full fixed caller suffix begins with the actual selected words, stores
them, reconstructs one source-derived route, reloads its declared root, and
emits one optimal assignment. Source allocation and weighted arithmetic are
separate, once-per-run contracts; neither is hidden in this suffix execution. -/
theorem selected_prelude_execution (program : Program width 4) (heap : Array (Word width))
    (graph : DAG n) (guarded : graph.Guarded) (rows : List Row) (roots : List ℕ)
    (matched : RowsMatch graph rows) (rootMatches : RootsMatch graph roots)
    (weights : Channel n → W) (nonnegative : ∀ channel, 0 ≤ weights channel)
    (b : ℕ) (target : Channel n) (candidate : Candidate W)
    (selected : (runGlobal graph weights b target).2.1.selected = some candidate)
    (countFits : (buildRoots graph).count < 2 ^ width)
    (positionFits : ∀ entry ∈ (buildRoots graph).entries, entry.position < 2 ^ width)
    (position : Fin graph.roots.length) (rootEq : candidate.root = position.val)
    (allocated : candidate.pointer ≤ (buildRoots graph).count)
    (base countAddress : ℕ) (address : Word width) (stack output : List (Word width))
    (countValid : countAddress < heap.size) (countWord : heap[countAddress] = word width n)
    (heapFits : (setupHeap width (cacheHeap width heap rows roots) graph).size ≤ 2 ^ width)
    (programFits : base + 92 < 2 ^ width)
    (block : BlockAt program base
      (preludeCode width base (provenanceCell (cacheHeap width heap rows roots) graph)
        (setupLayout (cacheHeap width heap rows roots) graph).best
        (setupRoutes width (cacheHeap width heap rows roots) graph countFits positionFits).base
        (heap.size + 6 * rows.length + (rowChildren rows).length + (rowGuards rows).length) ++
       ForestWitnessWalk.code width (base + 25)
        (ForestWitnessPath.packetLayout heap.size rows.length
          (setupOffset (cacheHeap width heap rows roots) graph)) countAddress)) :
    let packet := cacheHeap width heap rows roots
    let routes := selectedRoutes width packet graph (cacheRecords heap graph rows roots matched)
      countFits positionFits candidate.root candidate.pointer
    let rootBase := heap.size + 6 * rows.length + (rowChildren rows).length + (rowGuards rows).length
    ∃ temporary,
      Execution program
        ((counterState (setupHeap width packet graph) base address (word width candidate.root)
          (word width candidate.pointer)).frame stack output)
        ((counterState (selectedHeap width packet graph candidate.root candidate.pointer) (base + 25)
          (word width (graph.roots.get position).val) (word width rootBase) temporary).frame
          ((routes.route candidate.pointer).reverse.map (word width) ++ stack) output)
        (14 * (routes.route candidate.pointer).length + 12)
        (5 + (setupHeap width packet graph).size +
          ((routes.route candidate.pointer).length + stack.length + output.length)) := by
  dsimp only
  let packet := cacheHeap width heap rows roots
  let initialHeap := setupHeap width packet graph
  let layout := ForestWitnessPath.packetLayout heap.size rows.length (setupOffset packet graph)
  let records := cacheRecords heap graph rows roots matched
  let routes := selectedRoutes width packet graph records countFits positionFits candidate.root candidate.pointer
  let rootBase := heap.size + 6 * rows.length + (rowChildren rows).length + (rowGuards rows).length
  have rawLengths : roots.length = graph.roots.length := by rw [rootMatches, List.length_map]
  have rootValid : provenanceCell packet graph < initialHeap.size := by
    simp only [initialHeap, setupHeap_size, provenanceCell, setupOffset]; omega
  have bestValid : (setupLayout packet graph).best < initialHeap.size := by
    simp only [initialHeap, setupHeap_size, setupLayout, setupOffset]; omega
  have sourceValid : candidate.root + rootBase < packet.size := by
    have bound := position.isLt
    simp only [packet, cacheHeap_size, rootBase]; omega
  have packetLe : packet.size ≤ initialHeap.size := by simp only [initialHeap, setupHeap_size]; omega
  have initialFits : initialHeap.size ≤ 2 ^ width := heapFits
  have sourceInitialValid : candidate.root + rootBase < initialHeap.size :=
    Nat.lt_of_lt_of_le sourceValid packetLe
  have sourceFits : candidate.root + rootBase < 2 ^ width :=
    Nat.lt_of_lt_of_le sourceInitialValid initialFits
  have rootIdFits : candidate.root < 2 ^ width :=
    Nat.lt_of_le_of_lt (Nat.le_add_right _ _) sourceFits
  have rootBaseFits : rootBase < 2 ^ width :=
    Nat.lt_of_le_of_lt (Nat.le_add_left _ _) sourceFits
  have sourceHeld : initialHeap[candidate.root + rootBase]'sourceInitialValid =
      word width (graph.roots.get position).val := by
    have stored := cache_declared_root_word heap graph rows roots rootMatches position
    have retained := setup_prefix width packet graph (candidate.root + rootBase) sourceValid
    rw [Array.getElem?_eq_getElem sourceValid,
      Array.getElem?_eq_getElem sourceInitialValid] at retained
    exact (Option.some.inj retained).trans (by
      simpa only [rootEq, rootBase, packet, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using stored)
  have preludeBlock : BlockAt program base
      (preludeCode width base (provenanceCell packet graph) (setupLayout packet graph).best
        routes.base rootBase) := BlockAt.prefix program base _ _ block
  have walkBlock : BlockAt program (base + 25)
      (ForestWitnessWalk.code width (base + 25) layout countAddress) := by
    simpa only [preludeCode_length] using BlockAt.suffix program base _ _ block
  have pointerBound : candidate.pointer ≤ routes.count :=
    allocated
  obtain ⟨temporary, beforeWalk⟩ := prelude_execution program initialHeap base
    (provenanceCell packet graph) (setupLayout packet graph).best rootBase candidate.root candidate.pointer
    address (word width (graph.roots.get position).val) routes (by omega) heapFits rootValid bestValid
    (by simp only [provenanceCell, setupLayout]; omega) rootIdFits rootBaseFits (by omega)
    (by simp only [provenanceCell, setupOffset]; omega)
    (by simp only [setupLayout, setupOffset]; omega) sourceHeld countFits pointerBound stack output preludeBlock
  exact ⟨temporary, beforeWalk⟩

/-- The walk consumer is abstract over its validated physical source and
entry state. Concrete cache/setup transport is discharged separately. -/
theorem abstract_walk_execution (graph : DAG n) (node : Fin graph.nodeCount)
    (route : List ℕ) (head : Channel n) (blocked : Finset (Channel n))
    (path : RoutePath graph node route head blocked) (feasible : head ∉ blocked)
    (program : Program width 4) (state : State width 4) (layout : ForestWitnessPath.Layout)
    (source : WalkSource width state.heap graph layout) (markers : MarkerCells source ∅)
    (stack : List (Word width)) (base countAddress : ℕ)
    (countBefore : countAddress < layout.markerBase)
    (countWord : state.heap[countAddress]'(by have := source.region; omega) = word width n)
    (held : state.reg 0 = word width node.val)
    (positions : state.stack = route.map (word width) ++ stack)
    (pc : state.pc = word width base) (running : state.halted = false)
    (programFits : base + 67 < 2 ^ width) (heapFits : state.heap.size ≤ 2 ^ width)
    (block : BlockAt program base (ForestWitnessWalk.code width base layout countAddress)) :
    ∃ final ticks peak, Execution program state final ticks peak ∧
      ticks ≤ ForestWitnessAccept.sourceBudget graph graph.nodeCount + 10 * n + 4 ∧
      peak ≤ state.liveWords + n + 1 ∧ final.stack = stack ∧
      final.output = List.ofFn (fun channel : Channel n =>
        boolWord width (decide (channel ∈ fullUnblocked blocked))) ++ state.output ∧
      graph.eval (assignmentOfSet (fullUnblocked blocked)) node = true := by
  obtain ⟨walkTicks, cost⟩ := route_cost path
  obtain ⟨final, peak, execution, peakBound, _, finalStack, finalOutput, _, _, _, truth⟩ :=
    walk_and_emit cost feasible program state layout source markers stack base countAddress
      countBefore countWord held positions pc running programFits heapFits block
  have bound := (ForestWitnessAccept.routeCost_le_source graph cost).trans
    (ForestWitnessAccept.sourceBudget_mono graph (Nat.succ_le_of_lt node.isLt))
  refine ⟨final, walkTicks + 10 * n + 4, peak, execution, by omega,
    peakBound, finalStack, ?_, truth⟩
  simpa only [fullUnblocked, Finset.mem_sdiff, Finset.mem_univ, true_and, decide_not] using finalOutput

theorem selected_walk_execution (program : Program width 4) (heap : Array (Word width))
    (graph : DAG n) (guarded : graph.Guarded) (rows : List Row) (roots : List ℕ)
    (matched : RowsMatch graph rows) (rootMatches : RootsMatch graph roots)
    (weights : Channel n → W) (nonnegative : ∀ channel, 0 ≤ weights channel)
    (b : ℕ) (target : Channel n) (candidate : Candidate W)
    (selected : (runGlobal graph weights b target).2.1.selected = some candidate)
    (countFits : (buildRoots graph).count < 2 ^ width)
    (positionFits : ∀ entry ∈ (buildRoots graph).entries, entry.position < 2 ^ width)
    (position : Fin graph.roots.length) (head : Channel n) (blocked : Finset (Channel n))
    (path : RoutePath graph (graph.roots.get position)
      ((setupRoutes width (cacheHeap width heap rows roots) graph countFits positionFits).route candidate.pointer).reverse head blocked)
    (feasible : pathFeasible b target head blocked) (temporary : Word width)
    (base countAddress : ℕ) (address : Word width) (stack output : List (Word width))
    (countValid : countAddress < heap.size) (countWord : heap[countAddress] = word width n)
    (heapFits : (setupHeap width (cacheHeap width heap rows roots) graph).size ≤ 2 ^ width)
    (programFits : base + 92 < 2 ^ width)
    (block : BlockAt program base
      (preludeCode width base (provenanceCell (cacheHeap width heap rows roots) graph)
        (setupLayout (cacheHeap width heap rows roots) graph).best
        (setupRoutes width (cacheHeap width heap rows roots) graph countFits positionFits).base
        (heap.size + 6 * rows.length + (rowChildren rows).length + (rowGuards rows).length) ++
       ForestWitnessWalk.code width (base + 25)
        (ForestWitnessPath.packetLayout heap.size rows.length
          (setupOffset (cacheHeap width heap rows roots) graph)) countAddress)) :
    let packet := cacheHeap width heap rows roots
    let routes := selectedRoutes width packet graph (cacheRecords heap graph rows roots matched)
      countFits positionFits candidate.root candidate.pointer
    let rootBase := heap.size + 6 * rows.length + (rowChildren rows).length + (rowGuards rows).length
    let ready := ((counterState (selectedHeap width packet graph candidate.root candidate.pointer)
      (base + 25) (word width (graph.roots.get position).val) (word width rootBase) temporary).frame
        ((routes.route candidate.pointer).reverse.map (word width) ++ stack) output)
    ∃ final ticks peak,
      Execution program ready final ticks peak ∧
      ticks ≤ ForestWitnessAccept.sourceBudget graph graph.nodeCount + 10 * n + 4 ∧
      peak ≤ 5 + (setupHeap width packet graph).size +
        ((routes.route candidate.pointer).length + stack.length + output.length) + n + 1 ∧
      final.stack = stack ∧
      final.output = List.ofFn (fun channel : Channel n =>
        boolWord width (decide (channel ∈ fullUnblocked blocked))) ++ output ∧
      graph.eval (assignmentOfSet (fullUnblocked blocked)) (graph.roots.get position) = true := by
  let packet := cacheHeap width heap rows roots
  let initialHeap := setupHeap width packet graph
  let layout := ForestWitnessPath.packetLayout heap.size rows.length (setupOffset packet graph)
  let records := cacheRecords heap graph rows roots matched
  let routes := selectedRoutes width packet graph records countFits positionFits candidate.root candidate.pointer
  let rootBase := heap.size + 6 * rows.length + (rowChildren rows).length + (rowGuards rows).length
  have walkBlock : BlockAt program (base + 25)
      (ForestWitnessWalk.code width (base + 25) layout countAddress) := by
    simpa only [preludeCode_length] using BlockAt.suffix program base _ _ block
  let ready := ready_state (selectedHeap width packet graph candidate.root candidate.pointer)
    (base + 25) (word width (graph.roots.get position).val) (word width rootBase) temporary
    (routes.route candidate.pointer).reverse stack output
  obtain ⟨source, markers, countBefore, storedCount⟩ := selected_ready_source heap graph rows roots
    matched candidate.root candidate.pointer countAddress countValid countWord heapFits
  have readyHeap : ready.heap = selectedHeap width packet graph candidate.root candidate.pointer :=
    ready_state_heap _ _ _ _ _ _ _ _
  obtain ⟨readySource, readyMarkers, readyCount⟩ :=
    source_on_state ready _ graph layout readyHeap source markers countAddress countBefore storedCount
  obtain ⟨held, positions, readyPC, readyRunning, readyOutput⟩ :=
    ready_state_fields (selectedHeap width packet graph candidate.root candidate.pointer)
      (base + 25) (word width (graph.roots.get position).val) (word width rootBase) temporary
      (routes.route candidate.pointer).reverse stack output
  have routePath : RoutePath graph (graph.roots.get position)
      (routes.route candidate.pointer).reverse head blocked := path
  have readyFits : ready.heap.size ≤ 2 ^ width := by
    rw [readyHeap]
    exact (marshaled_size initialHeap (provenanceCell packet graph) (setupLayout packet graph).best
      (word width candidate.root) (word width candidate.pointer)).le.trans heapFits
  obtain ⟨final, walkTicks, walkPeak, afterWalk, costBound, peakBound, finalStack, finalOutput, truth⟩ :=
    abstract_walk_execution graph (graph.roots.get position) (routes.route candidate.pointer).reverse
      head blocked routePath feasible.1 program ready layout readySource readyMarkers stack (base + 25)
      countAddress countBefore readyCount held positions readyPC readyRunning (by omega) readyFits walkBlock
  have actualWalk : Execution program
      ((counterState (selectedHeap width packet graph candidate.root candidate.pointer)
        (base + 25) (word width (graph.roots.get position).val) (word width rootBase) temporary).frame
        ((routes.route candidate.pointer).reverse.map (word width) ++ stack) output)
      final walkTicks walkPeak := by
    simpa only [ready, ready_state_eq] using afterWalk
  refine ⟨final, walkTicks, walkPeak, actualWalk, costBound, ?_, finalStack, ?_, truth⟩
  · have words : ready.liveWords = 5 + initialHeap.size +
        ((routes.route candidate.pointer).length + stack.length + output.length) := by
      rw [show ready = _ from ready_state_eq _ _ _ _ _ _ _ _]
      exact (ready_liveWords (selectedHeap width packet graph candidate.root candidate.pointer)
        (base + 25) (word width (graph.roots.get position).val) (word width rootBase) temporary
        (routes.route candidate.pointer) stack output).trans
        (congrArg (fun size => 5 + size +
          ((routes.route candidate.pointer).length + stack.length + output.length))
          (marshaled_size initialHeap (provenanceCell packet graph) (setupLayout packet graph).best
            (word width candidate.root) (word width candidate.pointer)))
    simpa only [words] using peakBound
  · have outputEq : ready.output = output := readyOutput
    exact finalOutput.trans (congrArg (fun suffix =>
      List.ofFn (fun channel : Channel n =>
        boolWord width (decide (channel ∈ fullUnblocked blocked))) ++ suffix) outputEq)

theorem selected_emission (program : Program width 4) (heap : Array (Word width))
    (graph : DAG n) (guarded : graph.Guarded) (rows : List Row) (roots : List ℕ)
    (matched : RowsMatch graph rows) (rootMatches : RootsMatch graph roots)
    (weights : Channel n → W) (nonnegative : ∀ channel, 0 ≤ weights channel)
    (b : ℕ) (target : Channel n) (candidate : Candidate W)
    (selected : (runGlobal graph weights b target).2.1.selected = some candidate)
    (countFits : (buildRoots graph).count < 2 ^ width)
    (positionFits : ∀ entry ∈ (buildRoots graph).entries, entry.position < 2 ^ width)
    (base countAddress : ℕ) (address : Word width) (stack output : List (Word width))
    (countValid : countAddress < heap.size) (countWord : heap[countAddress] = word width n)
    (heapFits : (setupHeap width (cacheHeap width heap rows roots) graph).size ≤ 2 ^ width)
    (programFits : base + 92 < 2 ^ width)
    (block : BlockAt program base
      (preludeCode width base (provenanceCell (cacheHeap width heap rows roots) graph)
        (setupLayout (cacheHeap width heap rows roots) graph).best
        (setupRoutes width (cacheHeap width heap rows roots) graph countFits positionFits).base
        (heap.size + 6 * rows.length + (rowChildren rows).length + (rowGuards rows).length) ++
       ForestWitnessWalk.code width (base + 25)
        (ForestWitnessPath.packetLayout heap.size rows.length
          (setupOffset (cacheHeap width heap rows roots) graph)) countAddress)) :
    ∃ position : Fin graph.roots.length, candidate.root = position.val ∧
      ∃ blocked final ticks peak,
        Admissible b target (fullUnblocked blocked) ∧
        graph.eval (assignmentOfSet (fullUnblocked blocked)) (graph.roots.get position) = true ∧
        candidate.score = GenericWeight.total weights (fullUnblocked blocked) ∧
        (∀ other K, Admissible b target K →
          graph.eval (assignmentOfSet K) (graph.roots.get other) = true →
          GenericWeight.total weights K ≤ GenericWeight.total weights (fullUnblocked blocked)) ∧
        Execution program
          ((counterState (setupHeap width (cacheHeap width heap rows roots) graph) base address
            (word width candidate.root) (word width candidate.pointer)).frame stack output)
          final ticks peak ∧
        ticks ≤ 14 * (buildRoots graph).count + ForestWitnessAccept.sourceBudget graph graph.nodeCount +
          10 * n + 16 ∧
        peak ≤ 5 + (setupHeap width (cacheHeap width heap rows roots) graph).size +
          (buildRoots graph).count + stack.length + output.length + n + 1 ∧
        final.stack = stack ∧
        final.output = List.ofFn (fun channel : Channel n =>
          boolWord width (decide (channel ∈ fullUnblocked blocked))) ++ output := by
  let packet := cacheHeap width heap rows roots
  let initialHeap := setupHeap width packet graph
  let layout := ForestWitnessPath.packetLayout heap.size rows.length (setupOffset packet graph)
  let records := cacheRecords heap graph rows roots matched
  let routes := selectedRoutes width packet graph records countFits positionFits candidate.root candidate.pointer
  let rootBase := heap.size + 6 * rows.length + (rowChildren rows).length + (rowGuards rows).length
  obtain ⟨position, rootEq, head, blocked, path, feasible, score, optimal⟩ :=
    global_physical_optimal width packet graph guarded weights nonnegative b target countFits
      positionFits candidate selected
  have allocated := ForestWeightedReconstruction.selected_pointer_bound graph weights b target candidate selected
  obtain ⟨temporary, beforeWalk⟩ := selected_prelude_execution program heap graph guarded rows roots
    matched rootMatches weights nonnegative b target candidate selected countFits positionFits
    position rootEq allocated base countAddress address stack output countValid countWord heapFits programFits block
  have pointerBound : candidate.pointer ≤ routes.count := allocated
  obtain ⟨final, walkTicks, walkPeak, afterWalk, costBound, peakBound, finalStack, finalOutput, truth⟩ :=
    selected_walk_execution program heap graph guarded rows roots matched rootMatches weights nonnegative
      b target candidate selected countFits positionFits position head blocked path feasible temporary
      base countAddress address stack output countValid countWord heapFits programFits block
  have routeBound := reconstruction_bounds routes candidate.pointer pointerBound
  have joined := beforeWalk.append afterWalk
  refine ⟨position, rootEq, blocked, final, _, _,
    fullUnblocked_admissible b target head blocked feasible, truth, score, optimal, joined,
    ?_, ?_, finalStack, finalOutput⟩
  · change 14 * (routes.route candidate.pointer).length + 12 + walkTicks ≤
      14 * (buildRoots graph).count + ForestWitnessAccept.sourceBudget graph graph.nodeCount + 10 * n + 16
    have lengthBound : (routes.route candidate.pointer).length ≤ (buildRoots graph).count := routeBound.2
    omega
  · change max (5 + initialHeap.size +
        ((routes.route candidate.pointer).length + stack.length + output.length)) walkPeak ≤
      5 + initialHeap.size + (buildRoots graph).count + stack.length + output.length + n + 1
    change walkPeak ≤ 5 + initialHeap.size +
      ((routes.route candidate.pointer).length + stack.length + output.length) + n + 1 at peakBound
    have lengthBound : (routes.route candidate.pointer).length ≤ (buildRoots graph).count := routeBound.2
    apply max_le <;> omega

end Controller.Cost.ForestWitnessMarshal
