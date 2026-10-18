module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestWeightedGlobal
public import Controller.Cost.ForestWeightedScore

@[expose] public section

/-!
# Global weighted-incumbent bounds

The actual shared-incumbent caller returns a source-derived root summary and
bounds every returned summary score. The summary fold preserves the earlier
complete candidate on ties. These algebraic statements use the caller's cached
total and introduce no extra runtime scans.
-/
namespace Controller.Cost.ForestWeightedOptimal
open Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestWeightedTagged Controller.Cost.ForestWeightedGlobal
open Controller.Cost.ForestWeightedTrace
variable {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]

theorem merge_none_iff (previous fresh : Option (Candidate W)) :
    merge previous fresh = none ↔ previous = none ∧ fresh = none := by
  cases fresh with
  | none => simp [merge]
  | some proposed =>
      cases previous with
      | none => simp [merge, choose]
      | some old =>
          by_cases better : old.score < proposed.score <;> simp [merge, choose, better]

theorem merge_previous_bound_any (previous result : Candidate W) (fresh : Option (Candidate W))
    (selected : merge (some previous) fresh = some result) : previous.score ≤ result.score := by
  cases fresh with
  | none =>
      have equal : previous = result := Option.some.inj selected
      subst result
      exact le_refl _
  | some proposed => exact merge_previous_bound previous proposed result selected

theorem summary_fold_member (items : List (Option (Candidate W))) (previous : Option (Candidate W))
    (result : Candidate W) (selected : items.foldl merge previous = some result) :
    previous = some result ∨ some result ∈ items := by
  induction items generalizing previous with
  | nil => exact Or.inl selected
  | cons first rest ih =>
      have later := ih (merge previous first) selected
      rcases later with current | present
      · rcases merge_member previous first result current with old | fresh
        · exact Or.inl old
        · exact Or.inr (List.mem_cons.mpr (Or.inl fresh.symm))
      · exact Or.inr (List.mem_cons_of_mem first present)

theorem summary_fold_previous_bound (items : List (Option (Candidate W)))
    (previous result : Candidate W) (selected : items.foldl merge (some previous) = some result) :
    previous.score ≤ result.score := by
  induction items generalizing previous with
  | nil =>
      have equal : previous = result := Option.some.inj selected
      subst result
      exact le_refl _
  | cons first rest ih =>
      obtain ⟨current, chosen⟩ : ∃ current, merge (some previous) first = some current := by
        cases choice : merge (some previous) first with
        | none => have impossible := (merge_none_iff _ _).mp choice; cases impossible.1
        | some current => exact ⟨current, rfl⟩
      have suffix : rest.foldl merge (some current) = some result := by
        simpa only [List.foldl_cons, chosen] using selected
      exact (merge_previous_bound_any previous current first chosen).trans (ih current suffix)

theorem summary_fold_dominates (items : List (Option (Candidate W)))
    (previous : Option (Candidate W)) (result candidate : Candidate W)
    (selected : items.foldl merge previous = some result) (present : some candidate ∈ items) :
    candidate.score ≤ result.score := by
  induction items generalizing previous with
  | nil => simp at present
  | cons first rest ih =>
      rcases List.mem_cons.mp present with equal | later
      · subst first
        obtain ⟨current, chosen⟩ : ∃ current, merge previous (some candidate) = some current := by
          cases choice : merge previous (some candidate) with
          | none => have impossible := (merge_none_iff _ _).mp choice; cases impossible.2
          | some current => exact ⟨current, rfl⟩
        have suffix : rest.foldl merge (some current) = some result := by
          simpa only [List.foldl_cons, chosen] using selected
        exact (merge_fresh_bound previous candidate current chosen).trans
          (summary_fold_previous_bound rest current result suffix)
      · exact ih (merge previous first) selected later

theorem summary_fold_none_iff (items : List (Option (Candidate W))) (previous : Option (Candidate W)) :
    items.foldl merge previous = none ↔ previous = none ∧ ∀ item ∈ items, item = none := by
  induction items generalizing previous with
  | nil => simp
  | cons first rest ih =>
      rw [List.foldl_cons, ih, merge_none_iff]
      constructor
      · rintro ⟨⟨old, current⟩, later⟩
        refine ⟨old, ?_⟩
        intro item present
        rcases List.mem_cons.mp present with equal | member
        · simpa only [equal] using current
        · exact later item member
      · rintro ⟨old, all⟩
        exact ⟨⟨old, all first List.mem_cons_self⟩,
          fun item present => all item (List.mem_cons_of_mem first present)⟩

def sourceSummaries (graph : DAG n) (weights : Channel n → W) (b : ℕ) (target : Channel n) :=
  rootSummaries graph weights b target (cacheTotal weights).1 (List.finRange graph.roots.length)
    ⟨((fun _ => 0), 0), Controller.Cost.ForestCursorDescriptors.initial, none⟩

theorem global_member (graph : DAG n) (weights : Channel n → W) (b : ℕ) (target : Channel n)
    (result : Candidate W) (selected : (runGlobal graph weights b target).2.1.selected = some result) :
    some result ∈ sourceSummaries graph weights b target := by
  rw [global_selected_summary] at selected
  rcases summary_fold_member _ none result selected with impossible | present
  · cases impossible
  · exact present

theorem global_dominates_summary (graph : DAG n) (weights : Channel n → W) (b : ℕ) (target : Channel n)
    (result candidate : Candidate W) (selected : (runGlobal graph weights b target).2.1.selected = some result)
    (present : some candidate ∈ sourceSummaries graph weights b target) : candidate.score ≤ result.score := by
  rw [global_selected_summary] at selected
  exact summary_fold_dominates _ none result candidate selected present

theorem global_none_iff_summaries (graph : DAG n) (weights : Channel n → W) (b : ℕ) (target : Channel n) :
    (runGlobal graph weights b target).2.1.selected = none ↔
      ∀ item ∈ sourceSummaries graph weights b target, item = none := by
  rw [global_selected_summary, summary_fold_none_iff]
  simp only [true_and, sourceSummaries]

private theorem zero_started (state : TaggedState n W)
    (zero : state.blocked = ((fun _ => 0), (0 : W))) :
    (⟨state.blocked, Controller.Cost.ForestCursorDescriptors.beginRoot state.descriptors, none⟩ :
      TaggedState n W) =
      ⟨((fun _ => 0), 0), Controller.Cost.ForestCursorDescriptors.beginRoot state.descriptors, none⟩ := by
  cases state with
  | mk blocked descriptors selected =>
      simp only at zero
      cases zero
      rfl

/-- Every admissible true valuation is bounded by an actual source-derived
fresh summary at its declared root, independently of descriptor allocation IDs. -/
theorem source_summary_exists (graph : DAG n) (guarded : graph.Guarded) (weights : Channel n → W)
    (nonnegative : ∀ channel, 0 ≤ weights channel) (b : ℕ) (target : Channel n)
    (positions : List (Fin graph.roots.length)) (state : TaggedState n W)
    (zero : state.blocked = ((fun _ => 0), (0 : W)))
    (position : Fin graph.roots.length) (present : position ∈ positions)
    (K : Finset (Channel n)) (eligible : Admissible b target K)
    (trueAt : graph.eval (assignmentOfSet K) (graph.roots.get position) = true) :
    ∃ candidate, some candidate ∈ rootSummaries graph weights b target
      (GenericWeight.total weights Finset.univ) positions state ∧
      GenericWeight.total weights K ≤ candidate.score := by
  induction positions generalizing state with
  | nil => simp at present
  | cons first rest ih =>
      let started : TaggedState n W :=
        ⟨((fun _ => 0), 0), Controller.Cost.ForestCursorDescriptors.beginRoot state.descriptors, none⟩
      let fresh := (runTaggedTrace weights first.val b target (GenericWeight.total weights Finset.univ)
        (Controller.Cost.ForestCursorTraversal.cursorOps graph (graph.roots.get first) []) started).1
      have summaries : rootSummaries graph weights b target (GenericWeight.total weights Finset.univ)
          (first :: rest) state = fresh.selected :: rootSummaries graph weights b target
            (GenericWeight.total weights Finset.univ) rest { fresh with selected := none } := by
        simp only [rootSummaries]
        rw [zero_started state zero]
      have restored : fresh.blocked = ((fun _ => 0), (0 : W)) := by
        have result := Controller.Cost.ForestWeightedSemantics.root_restores graph weights
          (graph.roots.get first) first.val b target (GenericWeight.total weights Finset.univ) started
          (by simp [started, blockedChannels, GenericWeight.total])
        exact result
      rcases List.mem_cons.mp present with same | later
      · subst position
        obtain ⟨route, score, selected⟩ := graph.bestGenericForwardLeafRoute_exists guarded weights nonnegative
          b target (graph.roots.get first) K eligible trueAt
        have projection := Controller.Cost.ForestWeightedScore.root_score graph weights first.val b target
          (graph.roots.get first) (Controller.Cost.ForestCursorDescriptors.beginRoot state.descriptors)
        rw [graph.bestGenericLeafRoute_eq, selected, Option.map_some] at projection
        cases chosen : fresh.selected with
        | none =>
            have impossible : (none : Option W) = some score := by
              simpa only [fresh, started, chosen, Option.map_none] using projection
            cases impossible
        | some candidate =>
            have sameScore : candidate.score = score := Option.some.inj (by
              simpa only [fresh, started, chosen, Option.map_some] using projection)
            refine ⟨candidate, ?_, ?_⟩
            · rw [summaries]
              exact List.mem_cons.mpr (Or.inl chosen.symm)
            · rw [sameScore]
              exact graph.bestGenericForwardLeafRoute_optimal guarded weights nonnegative b target
                (graph.roots.get first) route score selected K eligible trueAt
      · obtain ⟨candidate, member, bound⟩ := ih { fresh with selected := none } restored later
        refine ⟨candidate, ?_, bound⟩
        rw [summaries]
        exact List.mem_cons_of_mem fresh.selected member

/-- The actual global selected score bounds every admissible true set at every
output. The total is cached once in runGlobal; no fresh summary is reevaluated. -/
theorem global_optimal_bound (graph : DAG n) (guarded : graph.Guarded) (weights : Channel n → W)
    (nonnegative : ∀ channel, 0 ≤ weights channel) (b : ℕ) (target : Channel n)
    (result : Candidate W) (selected : (runGlobal graph weights b target).2.1.selected = some result)
    (position : Fin graph.roots.length) (K : Finset (Channel n))
    (eligible : Admissible b target K)
    (trueAt : graph.eval (assignmentOfSet K) (graph.roots.get position) = true) :
    GenericWeight.total weights K ≤ result.score := by
  obtain ⟨candidate, member, bound⟩ := source_summary_exists graph guarded weights nonnegative b target
    (List.finRange graph.roots.length)
    ⟨((fun _ => 0), 0), Controller.Cost.ForestCursorDescriptors.initial, none⟩ rfl
    position (by simp) K eligible trueAt
  have sourceMember : some candidate ∈ sourceSummaries graph weights b target := by
    simpa only [sourceSummaries, (cacheTotal_correct weights).1] using member
  exact bound.trans (global_dominates_summary graph weights b target result candidate selected sourceMember)

/-- Any admissible true output makes the actual shared caller nonempty. -/
theorem global_exists (graph : DAG n) (guarded : graph.Guarded) (weights : Channel n → W)
    (nonnegative : ∀ channel, 0 ≤ weights channel) (b : ℕ) (target : Channel n)
    (position : Fin graph.roots.length) (K : Finset (Channel n))
    (eligible : Admissible b target K)
    (trueAt : graph.eval (assignmentOfSet K) (graph.roots.get position) = true) :
    ∃ candidate, (runGlobal graph weights b target).2.1.selected = some candidate := by
  obtain ⟨candidate, member, bound⟩ := source_summary_exists graph guarded weights nonnegative b target
    (List.finRange graph.roots.length)
    ⟨((fun _ => 0), 0), Controller.Cost.ForestCursorDescriptors.initial, none⟩ rfl
    position (by simp) K eligible trueAt
  have sourceMember : some candidate ∈ sourceSummaries graph weights b target := by
    simpa only [sourceSummaries, (cacheTotal_correct weights).1] using member
  cases chosen : (runGlobal graph weights b target).2.1.selected with
  | none =>
      have impossible := (global_none_iff_summaries graph weights b target).mp chosen _ sourceMember
      cases impossible
  | some result => exact ⟨result, rfl⟩

/-- Every source-derived summary attains its score on an admissible true set.
The descriptor validity premise is propagated through the actual allocation
scan; no independently supplied list of feasible candidates is used. -/
theorem source_summary_sound (graph : DAG n) (weights : Channel n → W)
    (b : ℕ) (target : Channel n) (positions : List (Fin graph.roots.length))
    (state : TaggedState n W) (zero : state.blocked = ((fun _ => 0), (0 : W)))
    (valid : Controller.Cost.ForestCursorDescriptors.Valid state.descriptors)
    (candidate : Candidate W)
    (member : some candidate ∈ rootSummaries graph weights b target
      (GenericWeight.total weights Finset.univ) positions state) :
    ∃ position ∈ positions, candidate.root = position.val ∧
      ∃ K : Finset (Channel n), Admissible b target K ∧
        graph.eval (assignmentOfSet K) (graph.roots.get position) = true ∧
        candidate.score = GenericWeight.total weights K := by
  induction positions generalizing state with
  | nil => simp [rootSummaries] at member
  | cons first rest ih =>
      let started : TaggedState n W :=
        ⟨((fun _ => 0), 0), Controller.Cost.ForestCursorDescriptors.beginRoot state.descriptors, none⟩
      let fresh := (runTaggedTrace weights first.val b target (GenericWeight.total weights Finset.univ)
        (Controller.Cost.ForestCursorTraversal.cursorOps graph (graph.roots.get first) []) started).1
      have summaries : rootSummaries graph weights b target (GenericWeight.total weights Finset.univ)
          (first :: rest) state = fresh.selected :: rootSummaries graph weights b target
            (GenericWeight.total weights Finset.univ) rest { fresh with selected := none } := by
        simp only [rootSummaries]
        rw [zero_started state zero]
      rw [summaries] at member
      rcases List.mem_cons.mp member with chosen | later
      · have returned : fresh.selected = some candidate := chosen.symm
        obtain ⟨rootEq, bounded, head, blocked, path, feasible, score⟩ :=
          Controller.Cost.ForestWeightedProvenance.source_selected_sound graph weights
            (graph.roots.get first) first.val b target
            (Controller.Cost.ForestCursorDescriptors.beginRoot state.descriptors)
            (Controller.Cost.ForestCursorDescriptors.beginRoot_valid _ valid)
            (fun _ => []) rfl candidate returned
        exact ⟨first, List.mem_cons_self, rootEq, fullUnblocked blocked,
          fullUnblocked_admissible b target head blocked feasible,
          path.livePath.fullUnblocked_true b target feasible, score⟩
      · have restored : fresh.blocked = ((fun _ => 0), (0 : W)) :=
          Controller.Cost.ForestWeightedSemantics.root_restores graph weights
            (graph.roots.get first) first.val b target (GenericWeight.total weights Finset.univ) started
            (by simp [started, blockedChannels, GenericWeight.total])
        have descriptors : fresh.descriptors =
            Controller.Cost.ForestCursorDescriptors.scanRoot graph state.descriptors first :=
          Controller.Cost.ForestWeightedSemantics.tagged_trace_descriptors weights first.val b target
            (GenericWeight.total weights Finset.univ)
            (Controller.Cost.ForestCursorTraversal.cursorOps graph (graph.roots.get first) []) started
        have nextValid : Controller.Cost.ForestCursorDescriptors.Valid fresh.descriptors := by
          rw [descriptors]
          exact Controller.Cost.ForestCursorDescriptors.scanRoot_valid graph state.descriptors valid first
        obtain ⟨position, present, rootEq, K, eligible, trueAt, score⟩ :=
          ih { fresh with selected := none } restored nextValid later
        exact ⟨position, List.mem_cons_of_mem first present, rootEq, K, eligible, trueAt, score⟩

/-- A returned global score is attained by a true admissible valuation of
one declared output, with its declared root identity retained. -/
theorem global_sound (graph : DAG n) (weights : Channel n → W) (b : ℕ) (target : Channel n)
    (candidate : Candidate W)
    (selected : (runGlobal graph weights b target).2.1.selected = some candidate) :
    ∃ position : Fin graph.roots.length, candidate.root = position.val ∧
      ∃ K : Finset (Channel n), Admissible b target K ∧
        graph.eval (assignmentOfSet K) (graph.roots.get position) = true ∧
        candidate.score = GenericWeight.total weights K := by
  have member := global_member graph weights b target candidate selected
  have actual : some candidate ∈ rootSummaries graph weights b target
      (GenericWeight.total weights Finset.univ) (List.finRange graph.roots.length)
      ⟨((fun _ => 0), 0), Controller.Cost.ForestCursorDescriptors.initial, none⟩ := by
    simpa only [sourceSummaries, (cacheTotal_correct weights).1] using member
  obtain ⟨position, present, rootEq, K, eligible, trueAt, score⟩ :=
    source_summary_sound graph weights b target (List.finRange graph.roots.length)
      ⟨((fun _ => 0), 0), Controller.Cost.ForestCursorDescriptors.initial, none⟩ rfl
      Controller.Cost.ForestCursorDescriptors.initial_valid candidate actual
  exact ⟨position, rootEq, K, eligible, trueAt, score⟩

/-- The actual global caller returns none exactly when no declared output
has an admissible true valuation. This is the healthy-zero decision branch. -/
theorem global_none_iff (graph : DAG n) (guarded : graph.Guarded) (weights : Channel n → W)
    (nonnegative : ∀ channel, 0 ≤ weights channel) (b : ℕ) (target : Channel n) :
    (runGlobal graph weights b target).2.1.selected = none ↔
      ¬ ∃ (position : Fin graph.roots.length) (K : Finset (Channel n)),
        Admissible b target K ∧ graph.eval (assignmentOfSet K) (graph.roots.get position) = true := by
  constructor
  · intro empty
    rintro ⟨position, K, eligible, trueAt⟩
    obtain ⟨candidate, selected⟩ := global_exists graph guarded weights nonnegative b target
      position K eligible trueAt
    rw [empty] at selected
    cases selected
  · intro impossible
    cases selected : (runGlobal graph weights b target).2.1.selected with
    | none => rfl
    | some candidate =>
        obtain ⟨position, rootEq, K, eligible, trueAt, score⟩ :=
          global_sound graph weights b target candidate selected
        exact False.elim (impossible ⟨position, K, eligible, trueAt⟩)

/-- Every returned global score is attained and is maximal among all
admissible true valuations of all declared outputs. -/
theorem global_attains_optimum (graph : DAG n) (guarded : graph.Guarded) (weights : Channel n → W)
    (nonnegative : ∀ channel, 0 ≤ weights channel) (b : ℕ) (target : Channel n)
    (candidate : Candidate W)
    (selected : (runGlobal graph weights b target).2.1.selected = some candidate) :
    (∃ position : Fin graph.roots.length, candidate.root = position.val ∧
      ∃ K : Finset (Channel n), Admissible b target K ∧
        graph.eval (assignmentOfSet K) (graph.roots.get position) = true ∧
        candidate.score = GenericWeight.total weights K) ∧
    (∀ (position : Fin graph.roots.length) (K : Finset (Channel n)), Admissible b target K →
      graph.eval (assignmentOfSet K) (graph.roots.get position) = true →
      GenericWeight.total weights K ≤ candidate.score) :=
  ⟨global_sound graph weights b target candidate selected,
    fun position K eligible trueAt => global_optimal_bound graph guarded weights nonnegative
      b target candidate selected position K eligible trueAt⟩

end Controller.Cost.ForestWeightedOptimal
