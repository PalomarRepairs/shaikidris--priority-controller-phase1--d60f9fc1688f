module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestWeightedOptimal

@[expose] public section

/-! The selected global candidate retains its source-root allocation prefix.
The final once-materialized descriptor store decodes that exact candidate;
its score is attained on that path and dominates every admissible true set.
These are generic ordered-weight statements. Physical reconstruction and
weight bit complexity have separate resource contracts. -/
namespace Controller.Cost.ForestWeightedPhysicalOptimal
open Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestWeightedTagged Controller.Cost.ForestWeightedGlobal
open Controller.Cost.ForestWeightedOptimal Controller.Cost.ForestWeightedSemantics
open Controller.Cost.ForestCursorDescriptors Controller.Cost.ForestCursorTraversal
open Controller.Cost.ForestCursorAllRootsExecution
variable {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]

private theorem zero_started (state : TaggedState n W)
    (zero : state.blocked = ((fun _ => 0), (0 : W))) :
    (⟨state.blocked, beginRoot state.descriptors, none⟩ : TaggedState n W) =
      ⟨((fun _ => 0), 0), beginRoot state.descriptors, none⟩ := by
  cases state with
  | mk blocked descriptors selected =>
      simp only at zero
      cases zero
      rfl

/-- A selected fresh summary originates at an actual source-list position,
with the descriptor prefix produced by all preceding root scans. -/
theorem summary_origin (graph : DAG n) (weights : Channel n → W) (b : ℕ) (target : Channel n)
    (positions : List (Fin graph.roots.length)) (state : TaggedState n W)
    (zero : state.blocked = ((fun _ => 0), (0 : W))) (candidate : Candidate W)
    (member : some candidate ∈ rootSummaries graph weights b target
      (GenericWeight.total weights Finset.univ) positions state) :
    ∃ before position after, positions = before ++ position :: after ∧
      (runTaggedTrace weights position.val b target (GenericWeight.total weights Finset.univ)
        (cursorOps graph (graph.roots.get position) [])
        ⟨((fun _ => 0), 0), beginRoot (scanRoots graph state.descriptors before), none⟩).1.selected =
          some candidate := by
  induction positions generalizing state with
  | nil => simp [rootSummaries] at member
  | cons first rest ih =>
      let started : TaggedState n W :=
        ⟨((fun _ => 0), 0), beginRoot state.descriptors, none⟩
      let fresh := (runTaggedTrace weights first.val b target (GenericWeight.total weights Finset.univ)
        (cursorOps graph (graph.roots.get first) []) started).1
      have expansion : rootSummaries graph weights b target (GenericWeight.total weights Finset.univ)
          (first :: rest) state = fresh.selected :: rootSummaries graph weights b target
            (GenericWeight.total weights Finset.univ) rest { fresh with selected := none } := by
        simp only [rootSummaries]
        rw [zero_started state zero]
      rw [expansion] at member
      rcases List.mem_cons.mp member with chosen | later
      · exact ⟨[], first, rest, rfl, by simpa [scanRoots, started, fresh] using chosen.symm⟩
      · have restored : fresh.blocked = ((fun _ => 0), (0 : W)) :=
          root_restores graph weights (graph.roots.get first) first.val b target
            (GenericWeight.total weights Finset.univ) started
            (by simp [started, blockedChannels, GenericWeight.total])
        have descriptors : fresh.descriptors = scanRoot graph state.descriptors first :=
          tagged_trace_descriptors weights first.val b target (GenericWeight.total weights Finset.univ)
            (cursorOps graph (graph.roots.get first) []) started
        obtain ⟨before, position, after, split, returned⟩ :=
          ih { fresh with selected := none } restored later
        refine ⟨first :: before, position, after, by rw [split]; rfl, ?_⟩
        simpa only [scanRoots, List.foldl_cons, descriptors] using returned

/-- Declared root occurrence order fixes the exact allocation prefix. -/
theorem declared_prefix (graph : DAG n) (before : List (Fin graph.roots.length))
    (position : Fin graph.roots.length) (after : List (Fin graph.roots.length))
    (split : List.finRange graph.roots.length = before ++ position :: after) :
    before = rootPrefix graph position := by
  have bounded : before.length < (List.finRange graph.roots.length).length := by
    rw [split, List.length_append, List.length_cons]; omega
  have occurrence : (List.finRange graph.roots.length)[before.length]'bounded = position := by
    simp only [split, List.getElem_append_right (Nat.le_refl before.length),
      Nat.sub_self, List.getElem_cons_zero]
  have index : position.val = before.length := by
    have values := congrArg Fin.val occurrence
    simpa only [List.getElem_finRange, Fin.coe_cast] using values.symm
  have take := congrArg (List.take before.length) split
  have beforeEq : (List.finRange graph.roots.length).take before.length = before := by
    simpa using take
  simpa only [rootPrefix, index] using beforeEq.symm

/-- The actual global incumbent is decoded by the actual final shared store,
including candidates with the empty route and pointer zero. -/
theorem global_physical_sound (width : ℕ) (heap : Array (Word width)) (graph : DAG n)
    (weights : Channel n → W) (b : ℕ) (target : Channel n)
    (countFits : (buildRoots graph).count < 2 ^ width)
    (positionFits : ∀ entry ∈ (buildRoots graph).entries, entry.position < 2 ^ width)
    (candidate : Candidate W)
    (selected : (runGlobal graph weights b target).2.1.selected = some candidate) :
    ∃ position : Fin graph.roots.length, candidate.root = position.val ∧
      ∃ head blocked, RoutePath graph (graph.roots.get position)
        ((setupRoutes width heap graph countFits positionFits).route candidate.pointer).reverse head blocked ∧
        pathFeasible b target head blocked ∧
        candidate.score = GenericWeight.total weights (fullUnblocked blocked) := by
  have member := global_member graph weights b target candidate selected
  have actual : some candidate ∈ rootSummaries graph weights b target
      (GenericWeight.total weights Finset.univ) (List.finRange graph.roots.length)
      ⟨((fun _ => 0), 0), initial, none⟩ := by
    simpa only [sourceSummaries, (ForestWeightedTrace.cacheTotal_correct weights).1] using member
  obtain ⟨before, position, after, split, returned⟩ :=
    summary_origin graph weights b target _ ⟨((fun _ => 0), 0), initial, none⟩ rfl candidate actual
  have prefixEq := declared_prefix graph before position after split
  have canonical : (runTaggedTrace weights position.val b target (GenericWeight.total weights Finset.univ)
      (cursorOps graph (graph.roots.get position) [])
      ⟨((fun _ => 0), 0), beginRoot (prefixBuilder graph position), none⟩).1.selected = some candidate := by
    simpa only [prefixEq, prefixBuilder] using returned
  exact ⟨position, ForestWeightedProvenance.setup_selected_sound width heap graph weights b target
    position countFits positionFits candidate canonical⟩

/-- The exact physically decoded selected path attains the global optimum;
the output-root identity and pointer are those retained by the runtime scan. -/
theorem global_physical_optimal (width : ℕ) (heap : Array (Word width)) (graph : DAG n)
    (guarded : graph.Guarded) (weights : Channel n → W) (nonnegative : ∀ channel, 0 ≤ weights channel)
    (b : ℕ) (target : Channel n)
    (countFits : (buildRoots graph).count < 2 ^ width)
    (positionFits : ∀ entry ∈ (buildRoots graph).entries, entry.position < 2 ^ width)
    (candidate : Candidate W)
    (selected : (runGlobal graph weights b target).2.1.selected = some candidate) :
    ∃ position : Fin graph.roots.length, candidate.root = position.val ∧
      ∃ head blocked, RoutePath graph (graph.roots.get position)
        ((setupRoutes width heap graph countFits positionFits).route candidate.pointer).reverse head blocked ∧
        pathFeasible b target head blocked ∧
        candidate.score = GenericWeight.total weights (fullUnblocked blocked) ∧
        ∀ other K, Admissible b target K →
          graph.eval (assignmentOfSet K) (graph.roots.get other) = true →
          GenericWeight.total weights K ≤ GenericWeight.total weights (fullUnblocked blocked) := by
  obtain ⟨position, rootEq, head, blocked, path, feasible, score⟩ :=
    global_physical_sound width heap graph weights b target countFits positionFits candidate selected
  refine ⟨position, rootEq, head, blocked, path, feasible, score, ?_⟩
  intro other K eligible trueAt
  rw [← score]
  exact global_optimal_bound graph guarded weights nonnegative b target candidate selected other K eligible trueAt

end Controller.Cost.ForestWeightedPhysicalOptimal
