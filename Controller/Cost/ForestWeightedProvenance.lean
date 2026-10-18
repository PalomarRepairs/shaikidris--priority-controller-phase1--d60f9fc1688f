module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestWeightedSemantics

@[expose] public section

/-!
# Decoded provenance of the weighted source cursor

The final descriptor decoding is derived from the actual source allocation
scan. Mapping each selected pointer through that fixed decoding commutes with
strict-better selection and identifies its route and score with the production
weighted cursor. Physical representation is a separate finite-heap relation;
no route dictionary is constructed at runtime by these proofs.
-/
namespace Controller.Cost.ForestWeightedProvenance
open Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestCursorTraversal Controller.Cost.ForestWeightedTrace
open Controller.Cost.ForestWeightedTagged Controller.Cost.ForestCursorDescriptors
open Controller.Cost.ForestCursorCapturedProgram Controller.Cost.ForestCursorDescriptorSource
open Controller.Cost.ForestCursorAllRoots
variable {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]

def decodedCandidate (decode : ℕ → LeafRoute) (candidate : Candidate W) : LeafRoute × W :=
  (decode candidate.pointer, candidate.score)

def decodedState (decode : ℕ → LeafRoute) (state : TaggedState n W) : WeightedState n W :=
  (state.blocked, state.selected.map (decodedCandidate decode))

theorem choose_decoded (decode : ℕ → LeafRoute) (previous : Option (Candidate W))
    (root pointer : ℕ) (score : W) (route : LeafRoute) (same : decode pointer = route) :
    (choose previous ⟨root, pointer, score⟩).map (decodedCandidate decode) =
      match previous.map (decodedCandidate decode) with
      | none => some (route, score)
      | some old => if old.2 < score then some (route, score)
        else previous.map (decodedCandidate decode) := by
  cases previous with
  | none => simp [choose, decodedCandidate, same]
  | some old =>
      by_cases better : old.score < score <;> simp [choose, decodedCandidate, same, better]

theorem tagged_step_decoded (weights : Channel n → W) (root b : ℕ) (target : Channel n)
    (total : W) (decode : ℕ → LeafRoute) (state : TaggedState n W) (operation : CursorOp n)
    (leaf : ∀ owner route head, operation = .leaf owner route head → decode state.descriptors.current = route) :
    decodedState decode (taggedStep weights root b target total state operation) =
      weightedStep weights b target total (decodedState decode state) operation := by
  cases operation with
  | node owner => rfl
  | down owner position child => rfl
  | up => rfl
  | enter owner position channel => rfl
  | leave owner position channel => rfl
  | leaf owner route head =>
      have same := leaf owner route head rfl
      by_cases feasible : state.blocked.1 head = 0 ∧ (b ≠ 1 ∨ state.blocked.1 target = 0)
      · simp only [decodedState, taggedStep, weightedStep, keepBestGenericRoute, ite_eq_left feasible,
          choose_decoded decode state.selected root state.descriptors.current (total - state.blocked.2) route same]
        apply Prod.ext
        · rfl
        · exact (ite_eq_left feasible).symm
      · simp only [decodedState, taggedStep, weightedStep, keepBestGenericRoute, ite_eq_right feasible]
        apply Prod.ext
        · rfl
        · exact (ite_eq_right feasible).symm

private theorem captured_tail (root : ℕ) (state : Builder) (operation : CursorOp n)
    (rest : List (CursorOp n)) (pair : LeafRoute × ℕ)
    (present : pair ∈ capturePairs root (ForestCursorDescriptors.step root state operation) rest) :
    pair ∈ capturePairs root state (operation :: rest) := by
  cases operation with
  | node owner => exact present
  | down owner position child => exact present
  | up => exact present
  | enter owner position channel => exact present
  | leave owner position channel => exact present
  | leaf owner route head => exact List.mem_cons_of_mem _ present

/-- Fixed final decoding, rather than a mutable ghost route at each step,
identifies all selected candidates with their production cursor routes. -/
theorem tagged_trace_decoded (weights : Channel n → W) (root b : ℕ) (target : Channel n)
    (total : W) (decode : ℕ → LeafRoute) (operations : List (CursorOp n)) (state : TaggedState n W)
    (decoded : ∀ route pointer, (route, pointer) ∈ capturePairs root state.descriptors operations →
      decode pointer = route) :
    decodedState decode (runTaggedTrace weights root b target total operations state).1 =
      operations.foldl (weightedStep weights b target total) (decodedState decode state) := by
  induction operations generalizing state with
  | nil => rfl
  | cons operation rest ih =>
      have later : ∀ route pointer,
          (route, pointer) ∈ capturePairs root (ForestCursorDescriptors.step root state.descriptors operation) rest → decode pointer = route := by
        intro route pointer present
        exact decoded route pointer (captured_tail root state.descriptors operation rest _ present)
      have current : ∀ owner route head, operation = .leaf owner route head →
          decode state.descriptors.current = route := by
        intro owner route head equal
        subst operation
        exact decoded route state.descriptors.current List.mem_cons_self
      have next := ih (taggedStep weights root b target total state operation)
        (by simpa only [ForestWeightedSemantics.taggedStep_descriptors] using later)
      simp only [runTaggedTrace, List.foldl_cons]
      rw [next, tagged_step_decoded weights root b target total decode state operation current]

/-- The fixed decoding premise is discharged by the actual source-derived
allocation scan, including repeated input terminals and empty root routes. -/
theorem source_capture_decoded (graph : DAG n) (node : Fin graph.nodeCount) (root : ℕ)
    (state : Builder) (valid : Valid state) (initialDecode : ℕ → LeafRoute)
    (current : initialDecode state.current = []) (route : LeafRoute) (pointer : ℕ)
    (present : (route, pointer) ∈ capturePairs root state (cursorOps graph node [])) :
    routeScan root state initialDecode (cursorOps graph node []) pointer = route ∧
      pointer ≤ (scan root state (cursorOps graph node [])).count := by
  exact capturePairs_decoded root state valid initialDecode _
    (source_route_safe graph root node [] state valid initialDecode current) route pointer present

/-- The actual selected pointer's reversed final decoding is precisely the
production optimal forward route, with exactly the selected score. -/
theorem source_selected_route (graph : DAG n) (weights : Channel n → W) (node : Fin graph.nodeCount)
    (root b : ℕ) (target : Channel n) (state : Builder) (valid : Valid state)
    (initialDecode : ℕ → LeafRoute) (current : initialDecode state.current = []) :
    ((runTaggedTrace weights root b target (GenericWeight.total weights Finset.univ)
      (cursorOps graph node []) ⟨((fun _ => 0), 0), state, none⟩).1.selected).map
        (fun candidate => ((routeScan root state initialDecode (cursorOps graph node []) candidate.pointer).reverse,
          candidate.score)) = graph.bestGenericForwardLeafRoute weights b target node := by
  let decode := routeScan root state initialDecode (cursorOps graph node [])
  have decoded : ∀ route pointer, (route, pointer) ∈ capturePairs root state (cursorOps graph node []) →
      decode pointer = route := by
    intro route pointer present
    exact (source_capture_decoded graph node root state valid initialDecode current route pointer present).1
  have projected := tagged_trace_decoded weights root b target (GenericWeight.total weights Finset.univ)
    decode (cursorOps graph node []) ⟨((fun _ => 0), 0), state, none⟩ decoded
  rw [weighted_cursor_correct] at projected
  have reversed := congrArg (fun result : WeightedState n W =>
    result.2.map (fun pair => (pair.1.reverse, pair.2))) projected
  rw [← graph.bestGenericLeafRoute_eq]
  simpa [decodedState, decodedCandidate, decode, bestGenericLeafRoute, Option.map_map,
    Function.comp_def] using reversed

/-- Root identity is retained alongside the selected descriptor, and that
exact descriptor represents a feasible path with the returned weight. -/
theorem source_selected_sound (graph : DAG n) (weights : Channel n → W) (node : Fin graph.nodeCount)
    (root b : ℕ) (target : Channel n) (state : Builder) (valid : Valid state)
    (initialDecode : ℕ → LeafRoute) (current : initialDecode state.current = [])
    (candidate : Candidate W)
    (returned : (runTaggedTrace weights root b target (GenericWeight.total weights Finset.univ)
      (cursorOps graph node []) ⟨((fun _ => 0), 0), state, none⟩).1.selected = some candidate) :
    candidate.root = root ∧ candidate.pointer ≤ (scan root state (cursorOps graph node [])).count ∧
      ∃ head blocked, RoutePath graph node
        (routeScan root state initialDecode (cursorOps graph node []) candidate.pointer).reverse head blocked ∧
        pathFeasible b target head blocked ∧ candidate.score = GenericWeight.total weights (fullUnblocked blocked) := by
  have origin := ForestWeightedSemantics.selected_source_member weights root b target
    (GenericWeight.total weights Finset.univ) (cursorOps graph node [])
    ⟨((fun _ => 0), 0), state, none⟩ candidate returned
  have present : candidate ∈ ForestWeightedSemantics.proposals weights root b target
      (GenericWeight.total weights Finset.univ) (cursorOps graph node []) ⟨((fun _ => 0), 0), state, none⟩ := by
    rcases origin with fresh | impossible
    · exact fresh
    · cases impossible
  obtain ⟨rootEq, route, captured⟩ := ForestWeightedSemantics.proposals_captured weights root b target
    (GenericWeight.total weights Finset.univ) (cursorOps graph node [])
    ⟨((fun _ => 0), 0), state, none⟩ candidate present
  have bounded := (source_capture_decoded graph node root state valid initialDecode current route candidate.pointer captured).2
  have selected := source_selected_route graph weights node root b target state valid initialDecode current
  rw [returned, Option.map_some] at selected
  obtain ⟨head, blocked, path, feasible, score⟩ := graph.bestGenericForwardLeafRoute_sound weights b target node
    _ candidate.score selected.symm
  exact ⟨rootEq, bounded, head, blocked, path, feasible, score⟩

/-- A finite physical descriptor store can be substituted for the derived
source decoding. Representation is required only on allocated source IDs. -/
theorem physical_selected_sound (graph : DAG n) (weights : Channel n → W) (node : Fin graph.nodeCount)
    (root b : ℕ) (target : Channel n) (state : Builder) (valid : Valid state)
    (initialDecode : ℕ → LeafRoute) (current : initialDecode state.current = [])
    (routes : Controller.Cost.ForestCursorProgram.RouteDescriptors width heap)
    (represented : ∀ pointer ≤ (scan root state (cursorOps graph node [])).count,
      routes.route pointer = routeScan root state initialDecode (cursorOps graph node []) pointer)
    (candidate : Candidate W)
    (returned : (runTaggedTrace weights root b target (GenericWeight.total weights Finset.univ)
      (cursorOps graph node []) ⟨((fun _ => 0), 0), state, none⟩).1.selected = some candidate) :
    candidate.root = root ∧ ∃ head blocked, RoutePath graph node (routes.route candidate.pointer).reverse head blocked ∧
      pathFeasible b target head blocked ∧ candidate.score = GenericWeight.total weights (fullUnblocked blocked) := by
  obtain ⟨rootEq, bounded, head, blocked, path, feasible, score⟩ :=
    source_selected_sound graph weights node root b target state valid initialDecode current candidate returned
  exact ⟨rootEq, head, blocked, by simpa only [represented candidate.pointer bounded] using path, feasible, score⟩

/-- The returned weighted root pointer is decoded by the actual once-built
all-root physical store. No descriptor map or RootIndex is supplied by the
caller: prefix allocation and the final store derive the representation. -/
theorem setup_selected_sound (width : ℕ) (heap : Array (Word width)) (graph : DAG n)
    (weights : Channel n → W) (b : ℕ) (target : Channel n) (position : Fin graph.roots.length)
    (countFits : (buildRoots graph).count < 2 ^ width)
    (positionFits : ∀ entry ∈ (buildRoots graph).entries, entry.position < 2 ^ width)
    (candidate : Candidate W)
    (returned : (runTaggedTrace weights position.val b target (GenericWeight.total weights Finset.univ)
      (cursorOps graph (graph.roots.get position) [])
      ⟨((fun _ => 0), 0), beginRoot (ForestCursorAllRootsExecution.prefixBuilder graph position), none⟩).1.selected =
        some candidate) :
    candidate.root = position.val ∧ ∃ head blocked, RoutePath graph (graph.roots.get position)
      ((ForestCursorAllRootsExecution.setupRoutes width heap graph countFits positionFits).route candidate.pointer).reverse
        head blocked ∧ pathFeasible b target head blocked ∧
      candidate.score = GenericWeight.total weights (fullUnblocked blocked) := by
  let state := beginRoot (ForestCursorAllRootsExecution.prefixBuilder graph position)
  let decode := ForestCursorAllRootsExecution.prefixDecoder graph position
  have prefixValid : Valid (ForestCursorAllRootsExecution.prefixBuilder graph position) :=
    scanRoots_valid graph initial initial_valid _
  have valid : Valid state := beginRoot_valid _ prefixValid
  have prefixDecoded : Decodes (ForestCursorAllRootsExecution.prefixBuilder graph position) decode :=
    rootsDecoder_decodes graph initial initial_valid (fun _ => []) ⟨rfl, by simp [initial]⟩ _
  have current : decode state.current = [] := prefixDecoded.sentinel
  apply physical_selected_sound graph weights (graph.roots.get position) position.val b target
    state valid decode current
    (ForestCursorAllRootsExecution.setupRoutes width heap graph countFits positionFits) _ candidate returned
  intro pointer bounded
  change allDecoder graph pointer = routeScan position.val state decode
    (cursorOps graph (graph.roots.get position) []) pointer
  unfold allDecoder
  rw [ForestCursorAllRootsExecution.root_split graph position,
    ForestCursorAllRootsExecution.source_decoder_append]
  change rootsDecoder graph
    (scanRoot graph (ForestCursorAllRootsExecution.prefixBuilder graph position) position)
    (routeScan position.val state decode (cursorOps graph (graph.roots.get position) []))
    (ForestCursorAllRootsExecution.rootSuffix graph position) pointer = _
  exact rootsDecoder_preserves graph _ _ _ pointer bounded

end Controller.Cost.ForestWeightedProvenance
