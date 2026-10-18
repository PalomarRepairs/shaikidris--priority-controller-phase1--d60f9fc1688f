module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Decoder.ForestTraversal

@[expose] public section

/-!
# Ordered-weight forest traversal correctness

The forward-route specification transfers exact path invariants to the production
reversed-cursor traversal. Weights range over an ordered additive group, with an
explicit nonnegativity assumption in optimization statements. A cached-total
entry point lets a caller share the channel-weight sum across output roots.
-/

namespace Controller.Decoder.DAG

variable {n : ℕ} {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]

def foldGenericLeafRoutes {α : Type*} (graph : DAG n) (weights : Channel n → W)
    (index : Fin graph.nodeCount) (counters : (GuardCounters n × W)) (initial : α)
    (visit : LeafRoute → Channel n → (GuardCounters n × W) → α → α) :
    (GuardCounters n × W) × α :=
  match graph.node index with
  | .zero => (counters, initial)
  | .input head => (counters, visit [] head counters initial)
  | .disj refs =>
      (List.finRange refs.length).foldl (fun state position =>
        graph.foldGenericLeafRoutes weights (graph.childIndex index (refs.get position))
          state.1 state.2 (fun route head current accumulator =>
            visit (position.val :: route) head current accumulator)) (counters, initial)
  | .guard child labels =>
      let result := graph.foldGenericLeafRoutes weights (graph.childIndex index child)
        (enterGenericGuards weights counters labels) initial
        (fun route head current accumulator => visit (0 :: route) head current accumulator)
      (leaveGenericGuards weights result.1 labels, result.2)
  | .liveAnd _ _ => (counters, initial)
termination_by index.val
decreasing_by all_goals exact graph.childIndex_lt _ _

private theorem generic_foldl_counters_unchanged {α β S : Type*} (items : List β)
    (step : S × α → β → S × α)
    (base : S) (initial : S × α)
    (initialEqual : initial.1 = base)
    (preserved : ∀ state item, state.1 = base → (step state item).1 = base) :
    (items.foldl step initial).1 = base := by
  induction items generalizing initial with
  | nil => exact initialEqual
  | cons item rest ih => exact ih _ (preserved initial item initialEqual)

/-- A complete subtree visit restores both guard counts and blocked union weight. -/
theorem foldGenericLeafRoutes_restores {α : Type*} (graph : DAG n)
    (weights : Channel n → W) (index : Fin graph.nodeCount)
    (counters : (GuardCounters n × W)) (initial : α)
    (visit : LeafRoute → Channel n → (GuardCounters n × W) → α → α)
    (invariant : counters.2 = GenericWeight.total weights (blockedChannels counters.1)) :
    (graph.foldGenericLeafRoutes weights index counters initial visit).1 = counters := by
  have claim : ∀ bound : ℕ, ∀ current : Fin graph.nodeCount, current.val = bound →
      ∀ (state : (GuardCounters n × W)) (accumulator : α)
        (callback : LeafRoute → Channel n → (GuardCounters n × W) → α → α),
      state.2 = GenericWeight.total weights (blockedChannels state.1) →
      (graph.foldGenericLeafRoutes weights current state accumulator callback).1 = state := by
    intro bound
    induction bound using Nat.strong_induction_on with
    | h bound ih =>
      intro current currentBound state accumulator callback correct
      rw [foldGenericLeafRoutes]
      cases equation : graph.node current with
      | zero => rfl
      | input head => rfl
      | liveAnd left right => rfl
      | disj refs =>
          apply generic_foldl_counters_unchanged _ _ state (state, accumulator) rfl
          intro previous position equal
          have earlier : (graph.childIndex current (refs.get position)).val < bound := by
            simpa only [DAG.childIndex, currentBound] using (refs.get position).isLt
          rw [ih _ earlier _ rfl previous.1 previous.2 _ (by simpa only [equal] using correct)]
          exact equal
      | guard child labels =>
          have earlier : (graph.childIndex current child).val < bound := by
            simpa only [DAG.childIndex, currentBound] using child.isLt
          have restore := ih _ earlier _ rfl (enterGenericGuards weights state labels)
            accumulator (fun route head current accumulator => callback (0 :: route) head current accumulator)
            (enterGenericGuards_correct weights state labels correct)
          change leaveGenericGuards weights
            (graph.foldGenericLeafRoutes weights (graph.childIndex current child)
              (enterGenericGuards weights state labels) accumulator
              (fun route head current accumulator => callback (0 :: route) head current accumulator)).1
            labels = state
          rw [restore]
          exact leave_enterGenericGuards weights state labels correct
  exact claim index.val index rfl counters initial visit invariant

private theorem generic_foldl_state_invariant {α β : Type*} (items : List β)
    (step : (GuardCounters n × W) × α → β → (GuardCounters n × W) × α)
    (base : (GuardCounters n × W)) (P : α → Prop) (initial : (GuardCounters n × W) × α)
    (initialEqual : initial.1 = base) (initialValid : P initial.2)
    (preserved : ∀ state item, state.1 = base → P state.2 →
      (step state item).1 = base ∧ P (step state item).2) :
    (items.foldl step initial).1 = base ∧ P (items.foldl step initial).2 := by
  induction items generalizing initial with
  | nil => exact ⟨initialEqual, initialValid⟩
  | cons item rest ih =>
      obtain ⟨equal, valid⟩ := preserved initial item initialEqual initialValid
      exact ih _ equal valid

/-- Callback invariants need only be proved at genuine positive-leaf routes with
exact blocked unions. This transfers them to the executable fold. -/
theorem foldGenericLeafRoutes_preserves {α : Type*} (graph : DAG n)
    (weights : Channel n → W) (index : Fin graph.nodeCount)
    (counters : (GuardCounters n × W)) (initial : α)
    (visit : LeafRoute → Channel n → (GuardCounters n × W) → α → α)
    (P : α → Prop) (initialValid : P initial)
    (correct : counters.2 = GenericWeight.total weights (blockedChannels counters.1))
    (leafValid : ∀ route head blocked current,
      RoutePath graph index route head blocked →
      blockedChannels current.1 = blockedChannels counters.1 ∪ blocked →
      current.2 = GenericWeight.total weights (blockedChannels current.1) →
      ∀ accumulator, P accumulator → P (visit route head current accumulator)) :
    P (graph.foldGenericLeafRoutes weights index counters initial visit).2 := by
  have claim : ∀ bound : ℕ, ∀ current : Fin graph.nodeCount, current.val = bound →
      ∀ (state : (GuardCounters n × W)) (accumulator : α)
        (callback : LeafRoute → Channel n → (GuardCounters n × W) → α → α)
        (Q : α → Prop), Q accumulator →
      state.2 = GenericWeight.total weights (blockedChannels state.1) →
      (∀ route head blocked leafState, RoutePath graph current route head blocked →
        blockedChannels leafState.1 = blockedChannels state.1 ∪ blocked →
        leafState.2 = GenericWeight.total weights (blockedChannels leafState.1) →
        ∀ previous, Q previous → Q (callback route head leafState previous)) →
      Q (graph.foldGenericLeafRoutes weights current state accumulator callback).2 := by
    intro bound
    induction bound using Nat.strong_induction_on with
    | h bound ih =>
      intro current currentBound state accumulator callback Q valid invariant leaves
      rw [foldGenericLeafRoutes]
      cases equation : graph.node current with
      | zero => exact valid
      | liveAnd left right => exact valid
      | input head =>
          exact leaves [] head ∅ state (.input current head equation)
            (by simp) invariant accumulator valid
      | disj refs =>
          apply (generic_foldl_state_invariant (List.finRange refs.length) _ state Q
            (state, accumulator) rfl valid ?_).2
          intro previous position equal previousValid
          have earlier : (graph.childIndex current (refs.get position)).val < bound := by
            simpa only [DAG.childIndex, currentBound] using (refs.get position).isLt
          refine ⟨?_, ?_⟩
          · exact (graph.foldGenericLeafRoutes_restores weights _ previous.1 previous.2 _
              (by simpa only [equal] using invariant)).trans equal
          · apply ih _ earlier _ rfl previous.1 previous.2 _ Q previousValid
              (by simpa only [equal] using invariant)
            intro route head blocked leafState path union weight previousAccumulator previousAccumulatorValid
            apply leaves (position.val :: route) head blocked leafState
              (.disj current refs position route head blocked equation path)
              (by simpa only [equal] using union) weight previousAccumulator previousAccumulatorValid
      | guard child labels =>
          have earlier : (graph.childIndex current child).val < bound := by
            simpa only [DAG.childIndex, currentBound] using child.isLt
          apply ih _ earlier _ rfl (enterGenericGuards weights state labels) accumulator _ Q valid
            (enterGenericGuards_correct weights state labels invariant)
          intro route head blocked leafState path union weight previous previousValid
          apply leaves (0 :: route) head (labels.toFinset ∪ blocked) leafState
            (.guard current child labels route head blocked equation path) ?_ weight previous previousValid
          rw [enterGenericGuards_counters, blocked_enterGuards] at union
          simpa only [Finset.union_assoc] using union
  exact claim index.val index rfl counters initial visit P initialValid correct leafValid

private theorem generic_foldl_hits {α β : Type*} [DecidableEq β] (items : List β)
    (step : (GuardCounters n × W) × α → β → (GuardCounters n × W) × α)
    (base : (GuardCounters n × W)) (P : α → Prop) (chosen : β) (present : chosen ∈ items)
    (initial : (GuardCounters n × W) × α) (initialEqual : initial.1 = base)
    (restores : ∀ state item, state.1 = base → (step state item).1 = base)
    (preserves : ∀ state item, state.1 = base → P state.2 → P (step state item).2)
    (hits : ∀ state, state.1 = base → P (step state chosen).2) :
    P (items.foldl step initial).2 := by
  induction items generalizing initial with
  | nil => simp at present
  | cons item rest ih =>
      by_cases equal : item = chosen
      · subst item
        exact (generic_foldl_state_invariant rest step base P (step initial chosen)
          (restores initial chosen initialEqual) (hits initial initialEqual)
          (fun state item equal valid => ⟨restores state item equal,
            preserves state item equal valid⟩)).2
      · have tailPresent : chosen ∈ rest := by simpa [Ne.symm equal] using present
        exact ih tailPresent (step initial item) (restores initial item initialEqual)

/-- Every certified leaf occurrence is visited. An invariant established at that
occurrence and preserved by callbacks therefore holds after the entire fold. -/
theorem foldGenericLeafRoutes_hits {α : Type*} (graph : DAG n) (weights : Channel n → W)
    {index : Fin graph.nodeCount} {route : LeafRoute} {head : Channel n}
    {blocked : Finset (Channel n)} (path : RoutePath graph index route head blocked)
    (counters : (GuardCounters n × W)) (initial : α)
    (visit : LeafRoute → Channel n → (GuardCounters n × W) → α → α)
    (P : α → Prop)
    (correct : counters.2 = GenericWeight.total weights (blockedChannels counters.1))
    (preserved : ∀ route head current accumulator,
      P accumulator → P (visit route head current accumulator))
    (hit : ∀ current,
      blockedChannels current.1 = blockedChannels counters.1 ∪ blocked →
      current.2 = GenericWeight.total weights (blockedChannels current.1) →
      ∀ accumulator, P (visit route head current accumulator)) :
    P (graph.foldGenericLeafRoutes weights index counters initial visit).2 := by
  induction path generalizing counters initial visit with
  | input index head equation =>
      rw [foldGenericLeafRoutes, equation]
      exact hit counters (by simp) correct initial
  | disj index refs position route head blocked equation tail ih =>
      rw [foldGenericLeafRoutes, equation]
      apply generic_foldl_hits (List.finRange refs.length) _ counters P position
        (by simp) (counters, initial) rfl
      · intro previous child equal
        exact (graph.foldGenericLeafRoutes_restores weights _ previous.1 previous.2 _
          (by simpa only [equal] using correct)).trans equal
      · intro previous child equal previousValid
        apply graph.foldGenericLeafRoutes_preserves weights _ previous.1 previous.2 _ P previousValid
          (by simpa only [equal] using correct)
        intro childRoute childHead childBlocked current childPath union weight accumulator valid
        exact preserved (child.val :: childRoute) childHead current accumulator valid
      · intro previous equal
        apply ih previous.1 previous.2
          (fun childRoute childHead current accumulator =>
            visit (position.val :: childRoute) childHead current accumulator)
          (by simpa only [equal] using correct)
        · intro childRoute childHead current accumulator valid
          exact preserved (position.val :: childRoute) childHead current accumulator valid
        · intro current union weight accumulator
          exact hit current (by simpa only [equal] using union) weight accumulator
  | guard index child labels route head blocked equation tail ih =>
      rw [foldGenericLeafRoutes, equation]
      apply ih (enterGenericGuards weights counters labels) initial
        (fun childRoute childHead current accumulator =>
          visit (0 :: childRoute) childHead current accumulator)
        (enterGenericGuards_correct weights counters labels correct)
      · intro childRoute childHead current accumulator valid
        exact preserved (0 :: childRoute) childHead current accumulator valid
      · intro current union weight accumulator
        apply hit current ?_ weight accumulator
        rw [enterGenericGuards_counters, blocked_enterGuards] at union
        simpa only [Finset.union_assoc] using union



private theorem keepBestGenericRoute_preserves (b : ℕ) (target : Channel n) (total : W)
    (route : LeafRoute) (head : Channel n) (state : (GuardCounters n × W))
    (best : Option (LeafRoute × W)) (P : Option (LeafRoute × W) → Prop)
    (previousValid : P best)
    (newValid : state.1 head = 0 ∧ (b ≠ 1 ∨ state.1 target = 0) →
      P (some (route, total - state.2))) :
    P (keepBestGenericRoute b target total route head state best) := by
  unfold keepBestGenericRoute
  by_cases feasible : state.1 head = 0 ∧ (b ≠ 1 ∨ state.1 target = 0)
  · simp only [ite_eq_left feasible]
    cases best with
    | none => exact newValid feasible
    | some previous =>
        simp only
        by_cases improves : previous.2 < total - state.2
        · simpa only [ite_eq_left improves] using newValid feasible
        · simpa only [ite_eq_right improves] using previousValid
  · simpa only [ite_eq_right feasible] using previousValid

def GenericRouteScoreAtLeast (threshold : W) (best : Option (LeafRoute × W)) : Prop :=
  ∃ route score, best = some (route, score) ∧ threshold ≤ score

private theorem keepBestGenericRoute_monotone (b : ℕ) (target : Channel n) (total : W)
    (route : LeafRoute) (head : Channel n) (state : (GuardCounters n × W))
    (best : Option (LeafRoute × W)) (threshold : W)
    (good : GenericRouteScoreAtLeast threshold best) :
    GenericRouteScoreAtLeast threshold (keepBestGenericRoute b target total route head state best) := by
  obtain ⟨oldRoute, oldScore, equal, bound⟩ := good
  unfold keepBestGenericRoute
  by_cases feasible : state.1 head = 0 ∧ (b ≠ 1 ∨ state.1 target = 0)
  · simp only [ite_eq_left feasible, equal]
    by_cases improves : oldScore < total - state.2
    · exact ⟨route, total - state.2, by simp only [ite_eq_left improves], bound.trans (le_of_lt improves)⟩
    · exact ⟨oldRoute, oldScore, by simp only [ite_eq_right improves], bound⟩
  · exact ⟨oldRoute, oldScore, by simp only [ite_eq_right feasible, equal], bound⟩

private theorem keepBestGenericRoute_hits (b : ℕ) (target : Channel n) (total : W)
    (route : LeafRoute) (head : Channel n) (state : (GuardCounters n × W))
    (best : Option (LeafRoute × W))
    (feasible : state.1 head = 0 ∧ (b ≠ 1 ∨ state.1 target = 0)) :
    GenericRouteScoreAtLeast (total - state.2) (keepBestGenericRoute b target total route head state best) := by
  unfold keepBestGenericRoute
  rw [ite_eq_left feasible]
  cases best with
  | none => exact ⟨route, total - state.2, rfl, le_rfl⟩
  | some previous =>
      simp only
      by_cases improves : previous.2 < total - state.2
      · exact ⟨route, total - state.2, by simp only [ite_eq_left improves], le_rfl⟩
      · exact ⟨previous.1, previous.2, by simp only [ite_eq_right improves], le_of_not_gt improves⟩



theorem foldGenericLeafCursor_eq_fold {α : Type*} (graph : DAG n) (weights : Channel n → W)
    (index : Fin graph.nodeCount) (routePrefix : LeafRoute)
    (counters : (GuardCounters n × W)) (initial : α)
    (visit : LeafRoute → Channel n → (GuardCounters n × W) → α → α) :
    graph.foldGenericLeafCursor weights index routePrefix counters initial visit =
      graph.foldGenericLeafRoutes weights index counters initial
        (fun route head current accumulator => visit (route.reverse ++ routePrefix) head current accumulator) := by
  have claim : ∀ bound : ℕ, ∀ current : Fin graph.nodeCount, current.val = bound →
      ∀ (routePrefix : LeafRoute) (state : (GuardCounters n × W)) (accumulator : α)
        (callback : LeafRoute → Channel n → (GuardCounters n × W) → α → α),
      graph.foldGenericLeafCursor weights current routePrefix state accumulator callback =
        graph.foldGenericLeafRoutes weights current state accumulator
          (fun route head current accumulator =>
            callback (route.reverse ++ routePrefix) head current accumulator) := by
    intro bound
    induction bound using Nat.strong_induction_on with
    | h bound ih =>
      intro current currentBound routePrefix state accumulator callback
      rw [foldGenericLeafCursor, foldGenericLeafRoutes]
      cases equation : graph.node current with
      | zero => rfl
      | input head => simp
      | liveAnd left right => rfl
      | disj refs =>
          simp only []
          congr 1
          funext previous position
          have earlier : (graph.childIndex current (refs.get position)).val < bound := by
            simpa only [DAG.childIndex, currentBound] using (refs.get position).isLt
          rw [ih _ earlier _ rfl]
          congr 1
          funext route head current accumulator
          simp [List.reverse_cons, List.append_assoc]
      | guard child labels =>
          simp only []
          have earlier : (graph.childIndex current child).val < bound := by
            simpa only [DAG.childIndex, currentBound] using child.isLt
          rw [ih _ earlier _ rfl]
          simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
  exact claim index.val index rfl routePrefix counters initial visit

/-- Changing only the callback accumulator commutes with the traversal. -/
theorem foldGenericLeafRoutes_map {α β : Type*} (graph : DAG n) (weights : Channel n → W)
    (index : Fin graph.nodeCount) (counters : (GuardCounters n × W)) (initial : α)
    (first : LeafRoute → Channel n → (GuardCounters n × W) → α → α)
    (second : LeafRoute → Channel n → (GuardCounters n × W) → β → β)
    (f : α → β)
    (commutes : ∀ route head current accumulator,
      second route head current (f accumulator) = f (first route head current accumulator)) :
    graph.foldGenericLeafRoutes weights index counters (f initial) second =
      let result := graph.foldGenericLeafRoutes weights index counters initial first
      (result.1, f result.2) := by
  have claim : ∀ bound : ℕ, ∀ current : Fin graph.nodeCount, current.val = bound →
      ∀ state accumulator first second,
      (∀ route head leafState previous,
        second route head leafState (f previous) = f (first route head leafState previous)) →
      graph.foldGenericLeafRoutes weights current state (f accumulator) second =
        let result := graph.foldGenericLeafRoutes weights current state accumulator first
        (result.1, f result.2) := by
    intro bound
    induction bound using Nat.strong_induction_on with
    | h bound ih =>
      intro current currentBound state accumulator first second relation
      cases equation : graph.node current with
      | zero => simp only [foldGenericLeafRoutes, equation]
      | liveAnd left right => simp only [foldGenericLeafRoutes, equation]
      | input head => simp only [foldGenericLeafRoutes, equation, relation]
      | disj refs =>
          rw [foldGenericLeafRoutes.eq_def (graph := graph) (weights := weights)
            (index := current) (counters := state) (initial := f accumulator) (visit := second),
            foldGenericLeafRoutes.eq_def (graph := graph) (weights := weights)
            (index := current) (counters := state) (initial := accumulator) (visit := first)]
          simp only [equation]
          apply List.foldl_hom (fun previous : (GuardCounters n × W) × α => (previous.1, f previous.2))
            (init := (state, accumulator))
          intro previous position
          have earlier : (graph.childIndex current (refs.get position)).val < bound := by
            simpa only [DAG.childIndex, currentBound] using (refs.get position).isLt
          exact ih _ earlier _ rfl previous.1 previous.2 _ _
            (fun route head leafState previous => relation (position.val :: route) head leafState previous)
      | guard child labels =>
          have earlier : (graph.childIndex current child).val < bound := by
            simpa only [DAG.childIndex, currentBound] using child.isLt
          rw [foldGenericLeafRoutes.eq_def (graph := graph) (weights := weights)
            (index := current) (counters := state) (initial := f accumulator) (visit := second),
            foldGenericLeafRoutes.eq_def (graph := graph) (weights := weights)
            (index := current) (counters := state) (initial := accumulator) (visit := first)]
          simp only [equation]
          rw [ih _ earlier _ rfl _ accumulator _ _
            (fun route head leafState previous => relation (0 :: route) head leafState previous)]
  exact claim index.val index rfl counters initial first second commutes

private def reverseGenericBest (best : Option (LeafRoute × W)) : Option (LeafRoute × W) :=
  best.map fun result => (result.1.reverse, result.2)

@[simp] private theorem reverseGenericBest_reverseGenericBest (best : Option (LeafRoute × W)) :
    reverseGenericBest (reverseGenericBest best) = best := by
  cases best <;> simp [reverseGenericBest]

private theorem keepBestGenericRoute_reverse (b : ℕ) (target : Channel n) (total : W)
    (route : LeafRoute) (head : Channel n) (state : (GuardCounters n × W))
    (best : Option (LeafRoute × W)) :
    keepBestGenericRoute b target total route.reverse head state (reverseGenericBest best) =
      reverseGenericBest (keepBestGenericRoute b target total route head state best) := by
  by_cases feasible : state.1 head = 0 ∧ (b ≠ 1 ∨ state.1 target = 0)
  · cases best with
    | none => simp [keepBestGenericRoute, feasible, reverseGenericBest]
    | some previous =>
        simp only [reverseGenericBest, Option.map_some, keepBestGenericRoute, ite_eq_left feasible]
        split <;> rfl
  · simp [keepBestGenericRoute, feasible]



def bestGenericForwardLeafRoute (graph : DAG n) (weights : Channel n → W) (b : ℕ)
    (target : Channel n) (root : Fin graph.nodeCount) : Option (LeafRoute × W) :=
  (graph.foldGenericLeafRoutes weights root (fun _ => 0, 0) none
    (keepBestGenericRoute b target (GenericWeight.total weights Finset.univ))).2

/-- Reversed-routePrefix selection has exactly the semantic forward-route fold result. -/
theorem bestGenericLeafRoute_eq (graph : DAG n) (weights : Channel n → W) (b : ℕ)
    (target : Channel n) (root : Fin graph.nodeCount) :
    graph.bestGenericLeafRoute weights b target root = graph.bestGenericForwardLeafRoute weights b target root := by
  unfold bestGenericLeafRoute bestGenericForwardLeafRoute
  rw [foldGenericLeafCursor_eq_fold]
  simp only [List.append_nil]
  have transport := graph.foldGenericLeafRoutes_map weights root (fun _ => 0, 0) none
    (keepBestGenericRoute b target (GenericWeight.total weights Finset.univ))
    (fun route head current previous =>
      keepBestGenericRoute b target (GenericWeight.total weights Finset.univ) route.reverse head current previous)
    reverseGenericBest (keepBestGenericRoute_reverse b target (GenericWeight.total weights Finset.univ))
  have accumulator := congrArg Prod.snd transport
  simp only [reverseGenericBest, Option.map_none] at accumulator
  change reverseGenericBest _ = _
  rw [accumulator]
  exact reverseGenericBest_reverseGenericBest _

/-- A selected route certifies an admissible full-unblocked set and its exact score. -/
theorem bestGenericForwardLeafRoute_sound (graph : DAG n) (weights : Channel n → W) (b : ℕ)
    (target : Channel n) (root : Fin graph.nodeCount) (route : LeafRoute) (score : W)
    (selected : graph.bestGenericForwardLeafRoute weights b target root = some (route, score)) :
    ∃ head blocked, RoutePath graph root route head blocked ∧
      pathFeasible b target head blocked ∧
      score = GenericWeight.total weights (fullUnblocked blocked) := by
  let P : Option (LeafRoute × W) → Prop := fun best =>
    ∀ chosen value, best = some (chosen, value) →
      ∃ head blocked, RoutePath graph root chosen head blocked ∧
        pathFeasible b target head blocked ∧
        value = GenericWeight.total weights (fullUnblocked blocked)
  have initialValid : P none := by
    intro chosen value impossible
    cases impossible
  have valid : P (graph.bestGenericForwardLeafRoute weights b target root) := by
    apply graph.foldGenericLeafRoutes_preserves weights root (fun _ => 0, 0) none
      (keepBestGenericRoute b target (GenericWeight.total weights Finset.univ)) P initialValid
      (by simp [blockedChannels, GenericWeight.total])
    intro chosen head blocked state path union weight previous previousValid
    apply keepBestGenericRoute_preserves b target _ chosen head state previous P previousValid
    intro eligible
    have initialEmpty : blockedChannels (fun _ : Channel n => 0) = ∅ := by
      simp [blockedChannels]
    have exactBlocked : blockedChannels state.1 = blocked := by
      simpa only [initialEmpty, Finset.empty_union] using union
    have feasible : pathFeasible b target head blocked := by
      rw [← exactBlocked, pathFeasible_counter_iff]
      refine ⟨eligible.1, ?_⟩
      intro one
      rcases eligible.2 with many | targetZero
      · exact False.elim (many one)
      · exact targetZero
    intro resultRoute resultScore resultEqual
    have equal := Option.some.inj resultEqual
    have routeEqual : chosen = resultRoute := congrArg Prod.fst equal
    have scoreEqual : GenericWeight.total weights Finset.univ - state.2 = resultScore :=
      congrArg Prod.snd equal
    refine ⟨head, blocked, ?_, feasible, ?_⟩
    · simpa only [routeEqual] using path
    · rw [← scoreEqual, weight, exactBlocked, GenericWeight.fullUnblocked_total]
  exact valid route score selected

/-- Each feasible route supplies a lower bound on the final selected score. -/
theorem bestGenericForwardLeafRoute_dominates_path (graph : DAG n) (weights : Channel n → W) (b : ℕ)
    (target : Channel n) {root : Fin graph.nodeCount} {route : LeafRoute}
    {head : Channel n} {blocked : Finset (Channel n)}
    (path : RoutePath graph root route head blocked)
    (feasible : pathFeasible b target head blocked) :
    GenericRouteScoreAtLeast (GenericWeight.total weights (fullUnblocked blocked))
      (graph.bestGenericForwardLeafRoute weights b target root) := by
  apply graph.foldGenericLeafRoutes_hits weights path (fun _ => 0, 0) none
    (keepBestGenericRoute b target (GenericWeight.total weights Finset.univ))
    (GenericRouteScoreAtLeast (GenericWeight.total weights (fullUnblocked blocked)))
    (by simp [blockedChannels, GenericWeight.total])
  · intro chosen leaf current previous good
    exact keepBestGenericRoute_monotone b target _ chosen leaf current previous _ good
  · intro current union weight previous
    have exactBlocked : blockedChannels current.1 = blocked := by
      simpa [blockedChannels] using union
    have counterFeasible : current.1 head = 0 ∧ (b ≠ 1 ∨ current.1 target = 0) := by
      have translated := (pathFeasible_counter_iff b target head current.1).mp
        (by simpa only [exactBlocked] using feasible)
      refine ⟨translated.1, ?_⟩
      by_cases one : b = 1
      · exact Or.inr (translated.2 one)
      · exact Or.inl one
    have hit := keepBestGenericRoute_hits b target (GenericWeight.total weights Finset.univ)
      route head current previous counterFeasible
    rw [weight, exactBlocked, ← GenericWeight.fullUnblocked_total] at hit
    exact hit

/-- No admissible true set exceeds the score of a returned route. -/
theorem bestGenericForwardLeafRoute_optimal (graph : DAG n) (guarded : graph.Guarded)
    (weights : Channel n → W) (nonnegative : ∀ channel, 0 ≤ weights channel) (b : ℕ) (target : Channel n)
    (root : Fin graph.nodeCount) (route : LeafRoute) (score : W)
    (selected : graph.bestGenericForwardLeafRoute weights b target root = some (route, score))
    (K : Finset (Channel n)) (eligible : Admissible b target K)
    (value : graph.eval (assignmentOfSet K) root = true) :
    GenericWeight.total weights K ≤ score := by
  obtain ⟨head, blocked, path, feasible, fullEligible, fullTrue, dominates⟩ :=
    GenericWeight.exists_dominating_path graph guarded b target root weights nonnegative K eligible value
  obtain ⟨witness, routePath⟩ := path.exists_route
  obtain ⟨bestRoute, bestScore, actual, bound⟩ :=
    graph.bestGenericForwardLeafRoute_dominates_path weights b target routePath feasible
  have equal := Option.some.inj (selected.symm.trans actual)
  have scores : score = bestScore := congrArg Prod.snd equal
  exact dominates.trans (by simpa only [scores] using bound)

/-- Every admissible true valuation forces the fold to select a leaf. -/
theorem bestGenericForwardLeafRoute_exists (graph : DAG n) (guarded : graph.Guarded)
    (weights : Channel n → W) (nonnegative : ∀ channel, 0 ≤ weights channel) (b : ℕ) (target : Channel n)
    (root : Fin graph.nodeCount) (K : Finset (Channel n))
    (eligible : Admissible b target K)
    (value : graph.eval (assignmentOfSet K) root = true) :
    ∃ route score, graph.bestGenericForwardLeafRoute weights b target root = some (route, score) := by
  obtain ⟨head, blocked, path, feasible, fullEligible, fullTrue, dominates⟩ :=
    GenericWeight.exists_dominating_path graph guarded b target root weights nonnegative K eligible value
  obtain ⟨route, routePath⟩ := path.exists_route
  obtain ⟨bestRoute, bestScore, selected, bound⟩ :=
    graph.bestGenericForwardLeafRoute_dominates_path weights b target routePath feasible
  exact ⟨bestRoute, bestScore, selected⟩

/-- Reconstruct the guard union only for the selected route. -/
def bestGenericForwardLeafSet (graph : DAG n) (weights : Channel n → W) (b : ℕ)
    (target : Channel n) (root : Fin graph.nodeCount) : Option (Finset (Channel n)) := do
  let best ← graph.bestGenericForwardLeafRoute weights b target root
  let leaf ← graph.reconstructRoute root best.1
  pure (fullUnblocked leaf.2.toFinset)

/-- Every returned reconstructed set is a reachable true valuation at the root. -/
theorem bestGenericForwardLeafSet_sound (graph : DAG n) (weights : Channel n → W) (b : ℕ)
    (target : Channel n) (root : Fin graph.nodeCount) (K : Finset (Channel n))
    (returned : graph.bestGenericForwardLeafSet weights b target root = some K) :
    Admissible b target K ∧ graph.eval (assignmentOfSet K) root = true := by
  unfold bestGenericForwardLeafSet at returned
  cases selected : graph.bestGenericForwardLeafRoute weights b target root with
  | none => simp only [selected, Option.bind_none] at returned; cases returned
  | some best =>
      obtain ⟨head, blocked, path, feasible, score⟩ :=
        graph.bestGenericForwardLeafRoute_sound weights b target root best.1 best.2 selected
      obtain ⟨labels, readback, union⟩ := graph.reconstructRoute_of_path path
      simp [selected, readback] at returned
      have equal : fullUnblocked blocked = K := by
        simpa only [union] using returned
      rw [← equal]
      exact ⟨fullUnblocked_admissible b target head blocked feasible,
        path.livePath.fullUnblocked_true b target feasible⟩

/-- A detecting healthy-zero query obtains a reconstructed witness. -/
theorem bestGenericForwardLeafSet_exists (graph : DAG n) (guarded : graph.Guarded)
    (weights : Channel n → W) (nonnegative : ∀ channel, 0 ≤ weights channel) (b : ℕ) (target : Channel n)
    (root : Fin graph.nodeCount) (K : Finset (Channel n))
    (eligible : Admissible b target K)
    (value : graph.eval (assignmentOfSet K) root = true) :
    ∃ result, graph.bestGenericForwardLeafSet weights b target root = some result := by
  obtain ⟨route, score, selected⟩ := graph.bestGenericForwardLeafRoute_exists guarded weights nonnegative b target root K eligible value
  obtain ⟨head, blocked, path, feasible, exactScore⟩ :=
    graph.bestGenericForwardLeafRoute_sound weights b target root route score selected
  obtain ⟨labels, readback, union⟩ := graph.reconstructRoute_of_path path
  refine ⟨fullUnblocked labels.toFinset, ?_⟩
  simp [bestGenericForwardLeafSet, selected, readback]

/-- The returned full set maximizes nonnegative weights over all admissible true sets. -/
theorem bestGenericForwardLeafSet_optimal (graph : DAG n) (guarded : graph.Guarded)
    (weights : Channel n → W) (nonnegative : ∀ channel, 0 ≤ weights channel) (b : ℕ) (target : Channel n)
    (root : Fin graph.nodeCount) (result : Finset (Channel n))
    (returned : graph.bestGenericForwardLeafSet weights b target root = some result)
    (K : Finset (Channel n)) (eligible : Admissible b target K)
    (value : graph.eval (assignmentOfSet K) root = true) :
    GenericWeight.total weights K ≤ GenericWeight.total weights result := by
  unfold bestGenericForwardLeafSet at returned
  cases selected : graph.bestGenericForwardLeafRoute weights b target root with
  | none => simp only [selected, Option.bind_none] at returned; cases returned
  | some best =>
      obtain ⟨head, blocked, path, feasible, score⟩ :=
        graph.bestGenericForwardLeafRoute_sound weights b target root best.1 best.2 selected
      obtain ⟨labels, readback, union⟩ := graph.reconstructRoute_of_path path
      simp [selected, readback] at returned
      have equal : fullUnblocked blocked = result := by
        simpa only [union] using returned
      rw [← equal, ← score]
      exact graph.bestGenericForwardLeafRoute_optimal guarded weights nonnegative b target root best.1 best.2 selected K eligible value

/-- Exact failure characterization for a positive-root query. -/
theorem bestGenericForwardLeafSet_none_iff (graph : DAG n) (guarded : graph.Guarded)
    (weights : Channel n → W) (nonnegative : ∀ channel, 0 ≤ weights channel) (b : ℕ) (target : Channel n)
    (root : Fin graph.nodeCount) :
    graph.bestGenericForwardLeafSet weights b target root = none ↔
      ¬ ∃ K, Admissible b target K ∧ graph.eval (assignmentOfSet K) root = true := by
  constructor
  · intro absent ⟨K, eligible, value⟩
    obtain ⟨result, returned⟩ := graph.bestGenericForwardLeafSet_exists guarded weights nonnegative b target root K eligible value
    rw [absent] at returned
    cases returned
  · intro impossible
    cases returned : graph.bestGenericForwardLeafSet weights b target root with
    | none => rfl
    | some result =>
        obtain ⟨eligible, value⟩ := graph.bestGenericForwardLeafSet_sound weights b target root result returned
        exact False.elim (impossible ⟨result, eligible, value⟩)


/-- The production cursor reconstructs exactly the forward-route specification. -/
theorem bestGenericLeafSet_eq (graph : DAG n) (weights : Channel n → W) (b : ℕ)
    (target : Channel n) (root : Fin graph.nodeCount) :
    graph.bestGenericLeafSet weights b target root =
      graph.bestGenericForwardLeafSet weights b target root := by
  unfold bestGenericLeafSet bestGenericForwardLeafSet
  rw [bestGenericLeafRoute_eq]

/-- Every returned generic production witness is admissible and true. -/
theorem bestGenericLeafSet_sound (graph : DAG n) (weights : Channel n → W) (b : ℕ)
    (target : Channel n) (root : Fin graph.nodeCount) (K : Finset (Channel n))
    (returned : graph.bestGenericLeafSet weights b target root = some K) :
    Admissible b target K ∧ graph.eval (assignmentOfSet K) root = true := by
  rw [bestGenericLeafSet_eq] at returned
  exact graph.bestGenericForwardLeafSet_sound weights b target root K returned

/-- The executable production traversal maximizes arbitrary nonnegative weights. -/
theorem bestGenericLeafSet_optimal (graph : DAG n) (guarded : graph.Guarded)
    (weights : Channel n → W) (nonnegative : ∀ channel, 0 ≤ weights channel)
    (b : ℕ) (target : Channel n) (root : Fin graph.nodeCount) (result : Finset (Channel n))
    (returned : graph.bestGenericLeafSet weights b target root = some result)
    (K : Finset (Channel n)) (eligible : Admissible b target K)
    (value : graph.eval (assignmentOfSet K) root = true) :
    GenericWeight.total weights K ≤ GenericWeight.total weights result := by
  rw [bestGenericLeafSet_eq] at returned
  exact graph.bestGenericForwardLeafSet_optimal guarded weights nonnegative b target root result returned K eligible value

/-- Exact absence of an admissible true valuation for the generic production fold. -/
theorem bestGenericLeafSet_none_iff (graph : DAG n) (guarded : graph.Guarded)
    (weights : Channel n → W) (nonnegative : ∀ channel, 0 ≤ weights channel)
    (b : ℕ) (target : Channel n) (root : Fin graph.nodeCount) :
    graph.bestGenericLeafSet weights b target root = none ↔
      ¬ ∃ K, Admissible b target K ∧ graph.eval (assignmentOfSet K) root = true := by
  rw [bestGenericLeafSet_eq]
  exact graph.bestGenericForwardLeafSet_none_iff guarded weights nonnegative b target root

/-- A healthy-zero observation yields an optimal detecting set over all admissible
valuations for every nonnegative weight function in the supported ordered group. -/
theorem bestGenericLeafSet_healthyZero (graph : DAG n) (guarded : graph.Guarded)
    (weights : Channel n → W) (nonnegative : ∀ channel, 0 ≤ weights channel)
    (b : ℕ) (target : Channel n) (root : Fin graph.nodeCount)
    (healthy : graph.eval (assignmentOfSet {target}) root = false)
    (result : Finset (Channel n))
    (returned : graph.bestGenericLeafSet weights b target root = some result) :
    Admissible b target result ∧
      graph.eval (assignmentOfSet result) root ≠ graph.eval (assignmentOfSet {target}) root ∧
      ∀ K, Admissible b target K →
        graph.eval (assignmentOfSet K) root ≠ graph.eval (assignmentOfSet {target}) root →
        GenericWeight.total weights K ≤ GenericWeight.total weights result := by
  obtain ⟨eligible, value⟩ := graph.bestGenericLeafSet_sound weights b target root result returned
  refine ⟨eligible, by rw [value, healthy]; decide, ?_⟩
  intro K admissible differs
  have trueValue : graph.eval (assignmentOfSet K) root = true := by
    cases actual : graph.eval (assignmentOfSet K) root <;> simp_all
  exact graph.bestGenericLeafSet_optimal guarded weights nonnegative b target root result returned K admissible trueValue

/-- A caller can compute the total union weight once and reuse it for all roots. -/
def bestGenericLeafRouteAtTotal (graph : DAG n) (weights : Channel n → W) (total : W)
    (b : ℕ) (target : Channel n) (root : Fin graph.nodeCount) : Option (LeafRoute × W) :=
  ((graph.foldGenericLeafCursor weights root [] (fun _ => 0, 0) (none : Option (LeafRoute × W))
    (keepBestGenericRoute b target total)).2).map fun best => (best.1.reverse, best.2)

def bestGenericLeafSetAtTotal (graph : DAG n) (weights : Channel n → W) (total : W)
    (b : ℕ) (target : Channel n) (root : Fin graph.nodeCount) : Option (Finset (Channel n)) := do
  let best ← graph.bestGenericLeafRouteAtTotal weights total b target root
  let leaf ← graph.reconstructRoute root best.1
  pure (fullUnblocked leaf.2.toFinset)

/-- The cached-total kernel refines the public selector when the supplied total is exact. -/
theorem bestGenericLeafSetAtTotal_eq (graph : DAG n) (weights : Channel n → W) (total : W)
    (correct : total = GenericWeight.total weights Finset.univ)
    (b : ℕ) (target : Channel n) (root : Fin graph.nodeCount) :
    graph.bestGenericLeafSetAtTotal weights total b target root =
      graph.bestGenericLeafSet weights b target root := by
  subst total
  rfl

end Controller.Decoder.DAG
