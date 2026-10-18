module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Boundaries.CriticalSets
public import Controller.Decoder.Detect
public import Controller.Cost.SharedZeroWitness
public import Controller.Cost.ForestOriginalSemantics
public import Controller.Cost.NativePhysicalRootGate

@[expose] public section

set_option maxRecDepth 10000

/-!
# Linear recovery of cycles and hidden critical sets

The healthy singleton selects one zero-system query. The cold forest driver
charges source loading, initialization, incidence processing and output; its
preparation traces account for validation and resident-code formation.

The physical witness record is the emitted channel vector, with a fixed
default-zero interpretation: target-or-membership enables, the target's first
request, and membership-controlled second requests. The controller interface
supplies its target and bus count. The bounds measure this sparse record.
-/

namespace Controller.Cost.CriticalSets

open Controller.Decoder Controller.Decoder.DAG Controller.Boundaries
open Controller.Cost.GateProgram Controller.Cost.ForestZeroAdmissibleCaller

variable {n : Nat}

noncomputable section

private theorem oneLayer_storedForest (graph : DAG n) (top : Fin graph.nodeCount)
    (guarded : graph.Guarded) (roots : graph.roots = [top])
    (maximum : ∀ index : Fin graph.nodeCount, index.val ≤ top.val)
    (terminal : ∀ parent : Fin graph.nodeCount, parent ≠ top →
      ∀ child ∈ (graph.node parent).children,
        (graph.node (graph.childIndex parent child)).isInternal = false)
    (distinct : (graph.node top).children.Nodup) : graph.StoredForest := by
  refine ⟨guarded, ?_⟩
  intro node internal
  rw [Nat.card_eq_fintype_card]
  apply Fintype.card_le_one_iff_subsingleton.mpr
  refine ⟨?_⟩
  intro first second
  apply Subtype.ext
  rcases first with ⟨first, firstRef⟩
  rcases second with ⟨second, secondRef⟩
  have parentTop : ∀ use : graph.ParentOccurrence,
      graph.refers (.inr use) = node → use.1 = top := by
    intro use reference
    by_contra different
    have zero := terminal use.1 different ((graph.node use.1).children.get use.2)
      (List.get_mem _ _)
    have same : graph.childIndex use.1 ((graph.node use.1).children.get use.2) = node := reference
    rw [same] at zero
    rw [internal] at zero
    contradiction
  have rootTop : ∀ position : Fin graph.roots.length, graph.refers (.inl position) = top := by
    intro position
    simp [DAG.refers, roots]
  cases first with
  | inl a =>
    cases second with
    | inl b =>
      have equal : a = b := by
        apply Fin.ext
        have length : graph.roots.length = 1 := by simp [roots]
        have aa := a.isLt
        have bb := b.isLt
        omega
      subst b
      rfl
    | inr b =>
      have root := rootTop a
      have ref := firstRef
      have last : node = top := root.symm.trans ref |>.symm
      have before := graph.childIndex_lt b.1 ((graph.node b.1).children.get b.2)
      have val := congrArg Fin.val secondRef
      simp only [DAG.refers, DAG.childIndex_val] at val
      have max := maximum b.1
      have nodeval := congrArg Fin.val last
      omega
  | inr a =>
    cases second with
    | inl b =>
      have root := rootTop b
      have ref := secondRef
      have last : node = top := root.symm.trans ref |>.symm
      have before := graph.childIndex_lt a.1 ((graph.node a.1).children.get a.2)
      have val := congrArg Fin.val firstRef
      simp only [DAG.refers, DAG.childIndex_val] at val
      have max := maximum a.1
      have nodeval := congrArg Fin.val last
      omega
    | inr b =>
      have ap := parentTop a firstRef
      have bp := parentTop b secondRef
      rcases a with ⟨aprent, apos⟩
      rcases b with ⟨bprent, bpos⟩
      dsimp at ap bp
      subst aprent
      subst bprent
      have equality : (graph.node top).children.get apos = (graph.node top).children.get bpos := by
        apply Fin.ext
        have same := congrArg Fin.val (firstRef.trans secondRef.symm)
        exact same
      have positions := distinct.injective_get equality
      subst bpos
      rfl

/-- The sole observation of the stored critical decoder. -/
def root (K : Finset (Channel n)) : Fin (criticalDAG K).nodeCount :=
  ⟨2 * n, by change 2 * n < 2 * n + 1; omega⟩

/-- Each cycle term is private to the final OR; shared channel leaves do not
violate the internal-occurrence forest promise. -/
theorem critical_forest (K : Finset (Channel n)) : (criticalDAG K).FormulaForest := by
  apply (criticalDAG K).storedForest_formulaForest
  apply oneLayer_storedForest (criticalDAG K) (root K) (criticalDAG_guarded K) rfl
  · intro index
    have bound := index.isLt
    change index.val < 2 * n + 1 at bound
    change index.val ≤ 2 * n
    omega
  · intro parent different child present
    by_cases input : parent.val < n
    · simp only [criticalDAG, dite_eq_left input, Gate.children] at present
      simp at present
    · by_cases term : parent.val < 2 * n
      · by_cases member : (⟨parent.val - n, by omega⟩ : Channel n) ∈ K
        · have same : child.val = parent.val - n := by
            have equal : child = ⟨parent.val - n, by omega⟩ := by
              simpa only [criticalDAG, dite_eq_right input, dite_eq_left term, ite_eq_left member,
                Gate.children, List.mem_singleton] using present
            exact congrArg Fin.val equal
          have small : child.val < n := by omega
          change ((criticalDAG K).node
            ⟨child.val, by change child.val < 2 * n + 1; omega⟩).isInternal = false
          simp only [criticalDAG, small, dite_true, Gate.isInternal]
        · simp only [criticalDAG, dite_eq_right input, dite_eq_left term, ite_eq_right member,
            Gate.children] at present
          simp at present
      · have last : parent = root K := by
          apply Fin.ext
          have bound := parent.isLt
          change parent.val < 2 * n + 1 at bound
          change parent.val = 2 * n
          omega
        exact False.elim (different last)
  · have notInput : ¬2 * n < n := by omega
    change ((criticalDAG K).node
      ⟨2 * n, by change 2 * n < 2 * n + 1; omega⟩).children.Nodup
    simp only [criticalDAG, notInput, dite_false, lt_self_iff_false, Gate.children]
    apply List.nodup_ofFn_ofInjective
    intro a b equal
    apply Fin.ext
    have values := congrArg Fin.val equal
    dsimp only at values
    omega

theorem healthy_one (b : Nat) (target : Channel n) (K : Finset (Channel n))
    (legal : K ∈ criticalSets b target) : criticalValue K {target} = true := by
  have different := ((mem_criticalSets b target K).mp legal).2
  have nonzero : criticalValue K {target} ≠ false := by
    intro zero
    exact different ((criticalValue_nonempty K {target} (by simp)).mp zero).symm
  cases value : criticalValue K {target} <;> simp_all

theorem healthy_root (b : Nat) (target : Channel n) (K : Finset (Channel n))
    (legal : K ∈ criticalSets b target) :
    (criticalDAG K).evalTable (assignmentOfSet {target}) (root K) = true := by
  rw [evalTable_eq_eval]
  exact (criticalDAG_eval K {target}).trans (healthy_one b target K legal)

/-- The detector's branch guard returns immediately, before enumerating heads. -/
theorem scanCandidates_none (b : Nat) (target : Channel n) (K : Finset (Channel n))
    (legal : K ∈ criticalSets b target) :
    (criticalDAG K).scanCandidates b target
      ((criticalDAG K).evalTable (assignmentOfSet {target})) = none := by
  have all : (criticalDAG K).roots.all
      ((criticalDAG K).evalTable (assignmentOfSet {target})) = true := by
    change ((criticalDAG K).evalTable (assignmentOfSet {target}) (root K) && true) = true
    simp [healthy_root b target K legal]
  simp only [DAG.scanCandidates, all, ↓reduceIte]

theorem zero_unique (b : Nat) (target : Channel n) (K L : Finset (Channel n))
    (admissible : Admissible b target L)
    (zero : (criticalDAG K).eval (assignmentOfSet L) (root K) = false) : L = K := by
  exact (criticalValue_nonempty K L admissible.1).mp ((criticalDAG_eval K L).symm.trans zero)

/-- The executable finite worklist returns the hidden set, rather than merely
some set with the same response. -/
theorem solveZero_exact (b : Nat) (target : Channel n) (K : Finset (Channel n))
    (legal : K ∈ criticalSets b target) :
    (criticalDAG K).solveZero b target (root K) ∅ ∅ = some K := by
  classical
  have admissible := ((mem_criticalSets b target K).mp legal).1
  have zero : (criticalDAG K).eval (assignmentOfSet K) (root K) = false :=
    (criticalDAG_eval K K).trans ((criticalValue_nonempty K K admissible.1).mpr rfl)
  cases returned : (criticalDAG K).solveZero b target (root K) ∅ ∅ with
  | none =>
      exact False.elim (((criticalDAG K).solveZero_none_iff (criticalDAG_guarded K)
        b target (root K) ∅ ∅).mp returned ⟨K, admissible, by simp [ExtendsFixed], zero⟩)
  | some L =>
      obtain ⟨adm, _, value⟩ := (criticalDAG K).solveZero_some (criticalDAG_guarded K)
        b target (root K) ∅ ∅ L returned
      rw [zero_unique b target K L adm value]

/-- The assembled functional detector takes exactly its one zero query. -/
theorem detectSet_exact (b : Nat) (target : Channel n) (K : Finset (Channel n))
    (legal : K ∈ criticalSets b target) :
    (criticalDAG K).detectSet b target true = some K := by
  rw [DAG.detectSet, ite_eq_left rfl]
  dsimp only
  rw [scanCandidates_none b target K legal]
  change firstSuccess ((criticalDAG K).zeroQuery b target
    ((criticalDAG K).evalTable (assignmentOfSet {target}))) [root K] = some K
  simp [firstSuccess, zeroQuery, healthy_root b target K legal, solveZero_exact b target K legal]

/-- An arbitrary cyclic successor and the literal modulo successor give the
same full-cycle observation. This identifies values, not stored layouts. -/
theorem full_cycle_value (L : Finset (Channel n)) :
    criticalValue Finset.univ L = moduloCycleValue L := by
  classical
  by_cases empty : L = ∅
  · subst L
    simp [moduloCycleValue]
  · have nonempty := Finset.nonempty_iff_ne_empty.mpr empty
    have sameZero := (criticalValue_nonempty Finset.univ L nonempty).trans
      (moduloCycle_unique_nonempty_zero L nonempty).symm
    cases left : criticalValue Finset.univ L <;>
      cases right : moduloCycleValue L <;> simp_all

theorem critical_observations (K : Finset (Channel n)) :
    (criticalDAG K).observations = criticalObservation K := by
  funext output assignment
  change Fin 1 at output
  have unique : output = 0 := Subsingleton.elim _ _
  subst output
  exact (criticalObservation_eq_dag K assignment).symm

open Controller.Cost.ForestRootProjection Controller.Cost.ForestIndexedOperands

/-- The forest driver evaluates and classifies the healthy output before
dispatching its sole negative query. No candidate-head tables are prepared. -/
def coldProgram (K : Finset (Channel n)) (b : Nat) (target : Channel n)
    (rows : List Row) (roots : List Nat) (matched : RowsMatch (criticalDAG K) rows) :
    Program (chosenMixedWidth (criticalDAG K)) 8 :=
  mixedResident (packetPrelude (classificationPrior (chosenMixedWidth (criticalDAG K))
    (criticalDAG K) rows roots (assignmentOfSet {target})))
    (healthyGraph (criticalDAG K) target false) (healthyGraph (criticalDAG K) target true)
    rows (healthyRootIds (criticalDAG K) target false) (healthyRootIds (criticalDAG K) target true)
    (Forest.rootFamily_rows (criticalDAG K) _ rows matched) (fun _ => (0 : Int)) b target
    (original_descriptor_capacity (criticalDAG K) (critical_forest K) target).1
    (original_descriptor_capacity (criticalDAG K) (critical_forest K) target).2

/-- Cold source loading, healthy evaluation, root dispatch, query construction,
initialization, incidence processing and exact channel output have one linear
bound. Source rows retain their full initialization charge. -/
theorem cold_recovery (K : Finset (Channel n)) (b : Nat) (bridge : Physical.Bridge n)
    (positive : 0 < b) (legal : K ∈ criticalSets b bridge.target)
    (rows : List Row) (roots : List Nat) (matched : RowsMatch (criticalDAG K) rows)
    (heads : UniformDAGSource.HeadsMatch (criticalDAG K) rows matched)
    (rootMatches : RootsMatch (criticalDAG K) roots)
    (rest output : List (Word (chosenMixedWidth (criticalDAG K))))
    (address loaded temporary : Word (chosenMixedWidth (criticalDAG K)))
    (saved : Fin 8 → Word (chosenMixedWidth (criticalDAG K))) :
    ∃ final ticks peak,
      Execution (coldProgram K b bridge.target rows roots matched)
        (classificationInitial (chosenMixedWidth (criticalDAG K)) (criticalDAG K) rows roots
          (assignmentOfSet {bridge.target}) bridge.target rest output address loaded temporary saved)
        final ticks peak ∧
      final.halted = true ∧ final.reg 4 = word (chosenMixedWidth (criticalDAG K)) 1 ∧
      ticks ≤ 57102 * n ∧ peak ≤ 2085 * n + rest.length + output.length ∧
      ∃ previous, final.output = List.ofFn (fun channel : Channel n =>
        boolWord (chosenMixedWidth (criticalDAG K)) (assignmentOfSet K channel)) ++ previous := by
  obtain ⟨answer, final, ticks, peak, storePeak, trace, halted, decision, time, space,
    operations, arithmetic, stored, total, meaning, witness⟩ :=
    ForestOriginalSemantics.original_physical_execution (criticalDAG K) (critical_forest K)
      b bridge positive rows roots matched heads rootMatches (fun _ => (0 : Int))
      (by intro _; rfl) rest output address loaded temporary saved
  have detects := critical_physical_realizer_detects bridge positive K legal
  rw [← critical_observations] at detects
  have accepted : answer = true := meaning.mpr ⟨_, true, detects⟩
  obtain ⟨found, admissible, detected, previous, emitted⟩ := witness accepted
  rw [critical_observations] at detected
  have only := critical_physical_detects_only_hidden bridge K legal _ true detected
  rw [(Physical.realizeBridge_spec bridge positive found admissible).2.2.2.2,
    setOfAssignment_assignmentOfSet] at only
  subst found
  subst answer
  have count : ForestRootProjection.forestSize (criticalDAG K) ≤ 12 * n := by
    have size := criticalDAG_countedSize_le K
    have npos := bridge.target.isLt
    rw [(criticalDAG K).countedSize_eq] at size
    unfold ForestRootProjection.forestSize
    omega
  have npos : 0 < n := Nat.zero_lt_of_lt bridge.target.isLt
  change ticks ≤ 4721 * ForestRootProjection.forestSize (criticalDAG K) + 450 at time
  change peak ≤ 169 * ForestRootProjection.forestSize (criticalDAG K) +
    57 + rest.length + output.length at space
  exact ⟨final, ticks, peak, trace, halted, decision, by omega, by omega, previous, emitted⟩

/-- The actual prepared zero-query execution emits exactly the hidden set.
The bound includes query construction, indexing, propagation and channel output;
the supplied resident source state is charged separately. -/
theorem prepared_execution (b : Nat) (target : Channel n) (K : Finset (Channel n))
    (legal : K ∈ criticalSets b target) (base slot : Nat)
    (program : Program width 8) (initial : State width 8)
    (sourceHeap : Array (Word width))
    (layout : ForestZeroDictionary.Layout (n + (criticalDAG K).nodeCount) initial.heap.size)
    (sourceEnd sourceEntry : Nat) (rest : List (Word width)) (dispatchEntry nextEntry : Nat)
    (plan : SourceQueryPlan (channels := n) program initial layout
      (SharedZeroSource.references (criticalDAG K) b target ∅ ∅ base slot (root K))
      sourceEnd (criticalDAG K).nodeCount sourceEntry rest (by omega) dispatchEntry nextEntry)
    (ready : QueryReady (ambient := n + (criticalDAG K).nodeCount) sourceHeap
      layout.tableBase layout.inverseBase sourceEntry rest initial) :
    ∃ final ticks peak,
      Execution program initial final ticks peak ∧
      final.pc = word width dispatchEntry ∧ final.halted = false ∧
      final.reg 4 = word width 1 ∧
      ticks ≤ 61243 * n ∧ peak ≤ initial.liveWords + 2418 * n ∧
      final.liveWords ≤ initial.liveWords + 2 * n ∧
      SharedZeroOutput.decode final.output n = K := by
  obtain ⟨answer, final, ticks, peak, trace, pc, running, decision, time, space, live,
    meaning, witness, _⟩ := SharedZeroWitness.execution (criticalDAG K) (criticalDAG_guarded K)
      b target ∅ ∅ (root K) base slot program initial sourceHeap layout sourceEnd sourceEntry
      rest dispatchEntry nextEntry plan ready
  have admissible := ((mem_criticalSets b target K).mp legal).1
  have accepted : answer = true := meaning.mpr ⟨K, admissible, by simp [ExtendsFixed],
    (criticalDAG_eval K K).trans ((criticalValue_nonempty K K admissible.1).mpr rfl)⟩
  obtain ⟨adm, _, value⟩ := witness accepted
  have exactSet := zero_unique b target K _ adm value
  have positive : 0 < n := Nat.zero_lt_of_lt target.isLt
  have size : (criticalDAG K).countedSize + 1 ≤ 13 * n := by
    have := criticalDAG_countedSize_le K
    omega
  subst answer
  refine ⟨final, ticks, peak, trace, pc, running, decision, ?_, ?_, ?_, exactSet⟩
  · omega
  · omega
  · simp only [↓reduceIte] at live
    omega

/-- The decoded machine output supplies the physical realizer's eligible set.
This is correctness of that construction, independent of its execution cost. -/
theorem decoded_physical_detects {b : Nat} (bridge : Physical.Bridge n)
    (buses : 0 < b) (K : Finset (Channel n))
    (legal : K ∈ criticalSets b bridge.target) (output : List (Word width))
    (recovered : SharedZeroOutput.decode output n = K) :
    Physical.BridgeInputDetects bridge true (criticalObservation K)
      (Physical.realizeBridge bridge buses (SharedZeroOutput.decode output n)) true := by
  rw [recovered]
  exact critical_physical_realizer_detects bridge buses K legal

/-- The emitted channel vector is a default-zero physical witness record.
The target and bus count are part of the supplied controller interface. -/
def descriptorInput {b : Nat} (bridge : Physical.Bridge n) (positive : 0 < b)
    (payload : List (Word width)) : Physical.PrimaryInput n b :=
  Physical.realizeBridge bridge positive (SharedZeroOutput.decode payload n)

theorem descriptor_enable {b : Nat} (bridge : Physical.Bridge n) (positive : 0 < b)
    (payload : List (Word width)) (channel : Channel n) :
    (descriptorInput bridge positive payload).enable channel =
      (decide (channel = bridge.target) || decide (payload[channel.val]? = some (word width 1))) := by
  simp [descriptorInput, Physical.realizeBridge, SharedZeroOutput.decode, assignmentOfSet,
    setOfAssignment]

theorem descriptor_requests {b : Nat} (bridge : Physical.Bridge n) (positive : 0 < b)
    (payload : List (Word width)) (bus : Fin b) (channel : Channel n) :
    (descriptorInput bridge positive payload).request bus channel =
      (if bus.val = 0 then decide (channel = bridge.target)
       else if bus.val = 1 then
         (!decide (payload[bridge.target.val]? = some (word width 1)) &&
           decide (payload[channel.val]? = some (word width 1))) else false) := by
  change Physical.realizeRequests bridge.target (SharedZeroOutput.decode payload n) b bus channel = _
  rw [NativePhysicalRootGate.request_value]
  simp only [SharedZeroOutput.decode, assignmentOfSet_setOfAssignment]

/-- The payload emitted by the machine already encodes every physical input
coordinate by the fixed sparse rule; expanding an n-by-b matrix is unnecessary. -/
theorem descriptor_detects {b : Nat} (bridge : Physical.Bridge n) (positive : 0 < b)
    (K : Finset (Channel n)) (legal : K ∈ criticalSets b bridge.target)
    (payload previous : List (Word width)) (fits : 1 < 2 ^ width)
    (encoded : payload = List.ofFn (fun channel => boolWord width (assignmentOfSet K channel)) ++ previous) :
    Physical.BridgeInputDetects bridge true (criticalObservation K)
      (descriptorInput bridge positive payload) true := by
  apply decoded_physical_detects bridge positive K legal payload
  rw [encoded]
  simpa only [List.ofFn_eq_map, boolWord, ForestZeroChannelEmit.bitWord,
    setOfAssignment_assignmentOfSet] using
    SharedZeroOutput.decode_prefix (assignmentOfSet K) previous fits

def forestProgram (graph : DAG n) (forest : graph.FormulaForest) (b : Nat) (target : Channel n)
    (rows : List Row) (roots : List Nat) (matched : RowsMatch graph rows) :
    Program (chosenMixedWidth graph) 8 :=
  mixedResident (packetPrelude (classificationPrior (chosenMixedWidth graph)
    graph rows roots (assignmentOfSet {target})))
    (healthyGraph graph target false) (healthyGraph graph target true)
    rows (healthyRootIds graph target false) (healthyRootIds graph target true)
    (Forest.rootFamily_rows graph _ rows matched) (fun _ => (0 : Int)) b target
    (original_descriptor_capacity graph forest target).1
    (original_descriptor_capacity graph forest target).2

theorem forest_cold_recovery (graph : DAG n) (forest : graph.FormulaForest)
    (b : Nat) (bridge : Physical.Bridge n) (positive : 0 < b) (K : Finset (Channel n))
    (detects : Physical.BridgeInputDetects bridge true graph.observations
      (Physical.realizeBridge bridge positive K) true)
    (unique : ∀ L, Admissible b bridge.target L →
      Physical.BridgeInputDetects bridge true graph.observations
        (Physical.realizeBridge bridge positive L) true → L = K)
    (small : forestSize graph ≤ 12 * n)
    (rows : List Row) (roots : List Nat) (matched : RowsMatch graph rows)
    (heads : UniformDAGSource.HeadsMatch graph rows matched) (rootMatches : RootsMatch graph roots)
    (rest output : List (Word (chosenMixedWidth graph)))
    (address loaded temporary : Word (chosenMixedWidth graph)) (saved : Fin 8 → Word (chosenMixedWidth graph)) :
    ∃ final ticks peak,
      Execution (forestProgram graph forest b bridge.target rows roots matched)
        (classificationInitial (chosenMixedWidth graph) graph rows roots (assignmentOfSet {bridge.target})
          bridge.target rest output address loaded temporary saved) final ticks peak ∧
      final.halted = true ∧ final.reg 4 = word (chosenMixedWidth graph) 1 ∧
      ticks ≤ 57102 * n ∧ peak ≤ 2085 * n + rest.length + output.length ∧
      programWords (forestProgram graph forest b bridge.target rows roots matched) + peak ≤
        44802 * n + rest.length + output.length ∧
      ∃ previous, final.output = List.ofFn (fun channel : Channel n =>
        boolWord (chosenMixedWidth graph) (assignmentOfSet K channel)) ++ previous := by
  obtain ⟨answer, final, ticks, peak, storePeak, trace, halted, decision, time, space,
    operations, arithmetic, stored, total, meaning, witness⟩ :=
    ForestOriginalSemantics.original_physical_execution graph forest b bridge positive rows roots
      matched heads rootMatches (fun _ => (0 : Int)) (by intro _; rfl)
      rest output address loaded temporary saved
  have accepted : answer = true := meaning.mpr ⟨_, true, detects⟩
  obtain ⟨found, admissible, detected, previous, emitted⟩ := witness accepted
  have equal := unique found admissible detected
  subst found
  subst answer
  have npos : 0 < n := Nat.zero_lt_of_lt bridge.target.isLt
  change ticks ≤ 4721 * forestSize graph + 450 at time
  change peak ≤ 169 * forestSize graph + 57 + rest.length + output.length at space
  change programWords (forestProgram graph forest b bridge.target rows roots matched) + peak + _ ≤ _ at total
  exact ⟨final, ticks, peak, trace, halted, decision, by omega, by omega, by omega, previous, emitted⟩

/-- The literal modulo-cycle source layout, with no chosen permutation. -/
def cycleDAG (n : Nat) : DAG n where
  nodeCount := 2 * n + 1
  node index := if input : index.val < n then .input ⟨index.val, input⟩
    else if term : index.val < 2 * n then
      let channel : Channel n := ⟨index.val - n, by omega⟩
      .guard ⟨channel.val, by dsimp [channel]; omega⟩ [finRotate n channel]
    else .disj (List.ofFn fun channel : Channel n => ⟨n + channel.val, by omega⟩)
  roots := [⟨2 * n, by omega⟩]

def cycleRoot (n : Nat) : Fin (cycleDAG n).nodeCount := ⟨2 * n, by change _ < 2 * n + 1; omega⟩

theorem cycle_guarded (n : Nat) : (cycleDAG n).Guarded := by
  intro index
  simp only [cycleDAG]
  split
  · rfl
  · split <;> rfl

theorem cycle_size (n : Nat) : (cycleDAG n).countedSize ≤ 8 * n + 4 := by
  classical
  have children (index : Fin (2 * n + 1)) :
      ((cycleDAG n).node index).children = ((criticalDAG (Finset.univ : Finset (Channel n))).node index).children := by
    by_cases input : index.val < n
    · simp [cycleDAG, criticalDAG, input]
    · by_cases term : index.val < 2 * n <;> simp [cycleDAG, criticalDAG, input, term, Gate.children]
  have guards (index : Fin (2 * n + 1)) :
      ((cycleDAG n).node index).guardLabels.length =
        ((criticalDAG (Finset.univ : Finset (Channel n))).node index).guardLabels.length := by
    by_cases input : index.val < n
    · simp [cycleDAG, criticalDAG, input]
    · by_cases term : index.val < 2 * n <;> simp [cycleDAG, criticalDAG, input, term, Gate.guardLabels]
  have childCounts : (cycleDAG n).childIncidences = (criticalDAG (Finset.univ : Finset (Channel n))).childIncidences := by
    unfold DAG.childIncidences
    apply congrArg (fun f : Fin (2 * n + 1) → Nat => (List.ofFn f).sum)
    funext index
    exact congrArg List.length (children index)
  have guardCounts : (cycleDAG n).guardIncidences = (criticalDAG (Finset.univ : Finset (Channel n))).guardIncidences := by
    unfold DAG.guardIncidences
    apply congrArg (fun f : Fin (2 * n + 1) → Nat => (List.ofFn f).sum)
    funext index
    exact guards index
  have size := criticalDAG_countedSize_le (Finset.univ : Finset (Channel n))
  rw [DAG.countedSize_eq] at size ⊢
  rw [childCounts, guardCounts]
  exact size

theorem cycle_forest (n : Nat) : (cycleDAG n).FormulaForest := by
  apply (cycleDAG n).storedForest_formulaForest
  apply oneLayer_storedForest (cycleDAG n) (cycleRoot n) (cycle_guarded n) rfl
  · intro index
    have bound := index.isLt
    change index.val < 2 * n + 1 at bound
    change index.val ≤ 2 * n
    omega
  · intro parent different child present
    by_cases input : parent.val < n
    · simp [cycleDAG, input, Gate.children] at present
    · by_cases term : parent.val < 2 * n
      · have equal : child = ⟨parent.val - n, by omega⟩ := by
          simpa only [cycleDAG, dite_eq_right input, dite_eq_left term, Gate.children, List.mem_singleton] using present
        have small : child.val < n := by
          have value := congrArg Fin.val equal
          dsimp only at value
          omega
        change ((cycleDAG n).node ⟨child.val, by change _ < 2 * n + 1; omega⟩).isInternal = false
        simp [cycleDAG, small, Gate.isInternal]
      · have equal : parent = cycleRoot n := by
          apply Fin.ext
          have bound := parent.isLt
          change parent.val < 2 * n + 1 at bound
          change parent.val = 2 * n
          omega
        exact False.elim (different equal)
  · have notInput : ¬ 2 * n < n := by omega
    change ((cycleDAG n).node ⟨2 * n, by change _ < 2 * n + 1; omega⟩).children.Nodup
    simp only [cycleDAG, notInput, dite_false, lt_self_iff_false, Gate.children]
    apply List.nodup_ofFn_ofInjective
    intro a b same
    apply Fin.ext
    have value := congrArg Fin.val same
    dsimp only at value
    omega

private theorem cycle_input (L : Finset (Channel n)) (i : Channel n) :
    (cycleDAG n).eval (assignmentOfSet L) ⟨i.val, by change _ < 2 * n + 1; omega⟩ = decide (i ∈ L) := by
  classical
  rw [DAG.eval_eq]
  simp [cycleDAG, i.isLt, Gate.eval, assignmentOfSet]

private theorem cycle_term (L : Finset (Channel n)) (i : Channel n) :
    (cycleDAG n).eval (assignmentOfSet L) ⟨n + i.val, by change _ < 2 * n + 1; omega⟩ =
      (decide (i ∈ L) && !decide (finRotate n i ∈ L)) := by
  classical
  rw [DAG.eval_eq]
  have notInput : ¬ n + i.val < n := by omega
  have term : n + i.val < 2 * n := by omega
  simp only [cycleDAG, notInput, dite_false, term, dite_true, Nat.add_sub_cancel_left,
    Gate.eval, List.any_cons, List.any_nil, Bool.or_false]
  change ((cycleDAG n).eval (assignmentOfSet L) ⟨i.val, by change _ < 2 * n + 1; omega⟩ &&
    !assignmentOfSet L (finRotate n i)) = _
  rw [cycle_input]
  rfl

theorem cycle_eval (L : Finset (Channel n)) :
    (cycleDAG n).eval (assignmentOfSet L) (cycleRoot n) = moduloCycleValue L := by
  classical
  rw [DAG.eval_eq]
  have notInput : ¬ 2 * n < n := by omega
  simp only [cycleRoot, cycleDAG, notInput, dite_false, lt_self_iff_false, Gate.eval]
  apply Bool.eq_iff_iff.mpr
  simp only [moduloCycleValue, List.any_eq_true, List.mem_ofFn]
  constructor
  · rintro ⟨value, ⟨i, rfl⟩, yes⟩
    exact ⟨_, ⟨i, rfl⟩, (cycle_term L i).symm ▸ yes⟩
  · rintro ⟨value, ⟨i, rfl⟩, yes⟩
    exact ⟨_, ⟨i, rfl⟩, (cycle_term L i) ▸ yes⟩

theorem bridge_two_channels (bridge : Physical.Bridge n) : 2 ≤ n := by
  obtain ⟨driver, member⟩ := bridge.drivers_nonempty
  by_contra small
  have same : driver = bridge.target := by
    apply Fin.ext
    have := driver.isLt
    have := bridge.target.isLt
    omega
  exact bridge.target_not_mem (same ▸ member)

theorem cycle_healthy (bridge : Physical.Bridge n) : moduloCycleValue {bridge.target} = true := by
  apply moduloCycle_small_nonempty_true _ (by simp)
  simp only [Finset.card_singleton]
  have := bridge_two_channels bridge
  omega

theorem cycle_detects_full {b : Nat} (bridge : Physical.Bridge n) (positive : 0 < b) :
    Physical.BridgeInputDetects bridge true (cycleDAG n).observations
      (Physical.realizeBridge bridge positive Finset.univ) true := by
  have admissible : Admissible b bridge.target (Finset.univ : Finset (Channel n)) :=
    ⟨⟨bridge.target, Finset.mem_univ _⟩, by simp⟩
  apply (Physical.realizeBridge_detects_iff bridge positive _ admissible _).mpr
  refine ⟨⟨0, by change 0 < 1; decide⟩, ?_⟩
  change (cycleDAG n).eval (assignmentOfSet {bridge.target}) (cycleRoot n) ≠
    (cycleDAG n).eval (assignmentOfSet Finset.univ) (cycleRoot n)
  have zero := (moduloCycle_unique_nonempty_zero (Finset.univ : Finset (Channel n))
    ⟨bridge.target, Finset.mem_univ _⟩).mpr rfl
  rw [cycle_eval, cycle_eval, cycle_healthy bridge, zero]
  decide

theorem cycle_unique {b : Nat} (bridge : Physical.Bridge n) (positive : 0 < b)
    (L : Finset (Channel n)) (admissible : Admissible b bridge.target L)
    (detects : Physical.BridgeInputDetects bridge true (cycleDAG n).observations
      (Physical.realizeBridge bridge positive L) true) : L = Finset.univ := by
  obtain ⟨index, different⟩ := (Physical.realizeBridge_detects_iff bridge positive L admissible _).mp detects
  change Fin 1 at index
  have only : index = ⟨0, by decide⟩ := Subsingleton.elim _ _
  subst index
  change (cycleDAG n).eval (assignmentOfSet {bridge.target}) (cycleRoot n) ≠
    (cycleDAG n).eval (assignmentOfSet L) (cycleRoot n) at different
  rw [cycle_eval, cycle_eval, cycle_healthy bridge] at different
  have zero : moduloCycleValue L = false := by
    cases value : moduloCycleValue L <;> simp_all
  exact (moduloCycle_unique_nonempty_zero L admissible.1).mp zero

/-- The actual literal-cycle driver returns all channels in one cold linear
run. Its emitted channel vector is the default-zero physical witness record. -/
theorem cycle_linear_recovery (b : Nat) (bridge : Physical.Bridge n) (positive : 0 < b)
    (rows : List Row) (roots : List Nat) (matched : RowsMatch (cycleDAG n) rows)
    (heads : UniformDAGSource.HeadsMatch (cycleDAG n) rows matched)
    (rootMatches : RootsMatch (cycleDAG n) roots)
    (address loaded temporary : Word (chosenMixedWidth (cycleDAG n)))
    (saved : Fin 8 → Word (chosenMixedWidth (cycleDAG n))) :
    ∃ final ticks peak,
      Execution (forestProgram (cycleDAG n) (cycle_forest n) b bridge.target rows roots matched)
        (classificationInitial (chosenMixedWidth (cycleDAG n)) (cycleDAG n) rows roots
          (assignmentOfSet {bridge.target}) bridge.target [] [] address loaded temporary saved) final ticks peak ∧
      final.halted = true ∧ final.reg 4 = word (chosenMixedWidth (cycleDAG n)) 1 ∧
      ticks ≤ 57102 * n ∧ peak ≤ 2085 * n ∧
      programWords (forestProgram (cycleDAG n) (cycle_forest n) b bridge.target rows roots matched) + peak ≤ 44802 * n ∧
      SharedZeroOutput.decode final.output n = Finset.univ ∧
      Physical.BridgeInputDetects bridge true (cycleDAG n).observations
        (descriptorInput bridge positive final.output) true := by
  have small : forestSize (cycleDAG n) ≤ 12 * n := by
    have bound := cycle_size n
    have positiveN := bridge.target.isLt
    rw [DAG.countedSize_eq] at bound
    unfold forestSize
    omega
  obtain ⟨final, ticks, peak, trace, halted, tag, time, space, resident, previous, output⟩ :=
    forest_cold_recovery (cycleDAG n) (cycle_forest n) b bridge positive Finset.univ
      (cycle_detects_full bridge positive) (fun L legal detects => cycle_unique bridge positive L legal detects)
      small rows roots matched heads rootMatches [] [] address loaded temporary saved
  have fits : 1 < 2 ^ chosenMixedWidth (cycleDAG n) := by
    have bound := chosenMixedCapacity (cycleDAG n)
    omega
  have decoded : SharedZeroOutput.decode final.output n = Finset.univ := by
    rw [output]
    simpa only [List.ofFn_eq_map, boolWord, ForestZeroChannelEmit.bitWord,
      setOfAssignment_assignmentOfSet] using
      SharedZeroOutput.decode_prefix (assignmentOfSet (Finset.univ : Finset (Channel n))) previous fits
  refine ⟨final, ticks, peak, trace, halted, tag, time, by simpa using space,
    by simpa using resident, decoded, ?_⟩
  unfold descriptorInput
  rw [decoded]
  exact cycle_detects_full bridge positive

/-- Complete hidden-family execution and sparse physical witness emission.
The code and all live words are linear in the declared channel count. -/
theorem critical_linear_recovery (b : Nat) (bridge : Physical.Bridge n) (positive : 0 < b)
    (K : Finset (Channel n)) (legal : K ∈ criticalSets b bridge.target)
    (rows : List Row) (roots : List Nat) (matched : RowsMatch (criticalDAG K) rows)
    (heads : UniformDAGSource.HeadsMatch (criticalDAG K) rows matched)
    (rootMatches : RootsMatch (criticalDAG K) roots)
    (address loaded temporary : Word (chosenMixedWidth (criticalDAG K)))
    (saved : Fin 8 → Word (chosenMixedWidth (criticalDAG K))) :
    ∃ final ticks peak,
      Execution (forestProgram (criticalDAG K) (critical_forest K) b bridge.target rows roots matched)
        (classificationInitial (chosenMixedWidth (criticalDAG K)) (criticalDAG K) rows roots
          (assignmentOfSet {bridge.target}) bridge.target [] [] address loaded temporary saved) final ticks peak ∧
      final.halted = true ∧ final.reg 4 = word (chosenMixedWidth (criticalDAG K)) 1 ∧
      ticks ≤ 57102 * n ∧ peak ≤ 2085 * n ∧
      programWords (forestProgram (criticalDAG K) (critical_forest K) b bridge.target rows roots matched) + peak ≤ 44802 * n ∧
      SharedZeroOutput.decode final.output n = K ∧
      Physical.BridgeInputDetects bridge true (criticalObservation K)
        (descriptorInput bridge positive final.output) true := by
  have detects := critical_physical_realizer_detects bridge positive K legal
  rw [← critical_observations] at detects
  have unique : ∀ L, Admissible b bridge.target L → Physical.BridgeInputDetects bridge true
      (criticalDAG K).observations (Physical.realizeBridge bridge positive L) true → L = K := by
    intro L admissible detected
    rw [critical_observations] at detected
    have equal := critical_physical_detects_only_hidden bridge K legal _ true detected
    rw [(Physical.realizeBridge_spec bridge positive L admissible).2.2.2.2,
      setOfAssignment_assignmentOfSet] at equal
    exact equal
  have small : forestSize (criticalDAG K) ≤ 12 * n := by
    have bound := criticalDAG_countedSize_le K
    have positiveN := bridge.target.isLt
    rw [DAG.countedSize_eq] at bound
    unfold forestSize
    omega
  obtain ⟨final, ticks, peak, trace, halted, tag, time, space, resident, previous, output⟩ :=
    forest_cold_recovery (criticalDAG K) (critical_forest K) b bridge positive K detects unique
      small rows roots matched heads rootMatches [] [] address loaded temporary saved
  have fits : 1 < 2 ^ chosenMixedWidth (criticalDAG K) := by
    have bound := chosenMixedCapacity (criticalDAG K)
    omega
  have decoded : SharedZeroOutput.decode final.output n = K := by
    rw [output]
    simpa only [List.ofFn_eq_map, boolWord, ForestZeroChannelEmit.bitWord,
      setOfAssignment_assignmentOfSet] using
      SharedZeroOutput.decode_prefix (assignmentOfSet K) previous fits
  exact ⟨final, ticks, peak, trace, halted, tag, time, by simpa using space,
    by simpa using resident, decoded, descriptor_detects bridge positive K legal _ previous fits output⟩

theorem healthy_one_branches (graph : DAG n) (target : Channel n)
    (all : ∀ position : Fin graph.roots.length,
      graph.eval (assignmentOfSet {target}) (graph.roots.get position) = true) :
    Forest.healthyPositions graph target false = [] ∧
      Forest.healthyPositions graph target true = List.finRange graph.roots.length := by
  constructor <;> unfold Forest.healthyPositions <;> simp_rw [all] <;> simp

theorem critical_one_query (b : Nat) (target : Channel n) (K : Finset (Channel n))
    (legal : K ∈ criticalSets b target) :
    Forest.healthyPositions (criticalDAG K) target false = [] ∧
      (Forest.healthyPositions (criticalDAG K) target true).length = 1 := by
  have branches := healthy_one_branches (criticalDAG K) target (by
    intro position
    change Fin 1 at position
    have only : position = ⟨0, by decide⟩ := Subsingleton.elim _ _
    subst position
    exact (criticalDAG_eval K {target}).trans (healthy_one b target K legal))
  exact ⟨branches.1, by rw [branches.2, List.length_finRange]; rfl⟩

theorem cycle_one_query (bridge : Physical.Bridge n) :
    Forest.healthyPositions (cycleDAG n) bridge.target false = [] ∧
      (Forest.healthyPositions (cycleDAG n) bridge.target true).length = 1 := by
  have branches := healthy_one_branches (cycleDAG n) bridge.target (by
    intro position
    change Fin 1 at position
    have only : position = ⟨0, by decide⟩ := Subsingleton.elim _ _
    subst position
    exact (cycle_eval {bridge.target}).trans (cycle_healthy bridge))
  exact ⟨branches.1, by rw [branches.2, List.length_finRange]; rfl⟩

open Controller.Cost.ForestWeightedIndexed Controller.Cost.ForestZeroResident

/-- Actual source validation, counter initialization, instruction-array and
backing-word formation, source-array formation and packet formation. -/
theorem forest_preparation (graph : DAG n) (forest : graph.FormulaForest)
    (b : Nat) (target : Channel n) (small : forestSize graph ≤ 12 * n)
    (rows : List Row) (roots : List Nat) (matched : RowsMatch graph rows)
    (rootMatches : RootsMatch graph roots) :
    let resident := forestProgram graph forest b target rows roots matched
    ∃ checks cells,
      SourceValidationTrace n 0 rows (sourceItems n rows) checks cells ∧
      CompilerArrayTrace.Trace (List.replicate n (0 : Nat)) #[] (Array.replicate n 0) n ∧
      cells ≤ sourceWords n rows ∧
      CompilerArrayTrace.Trace resident.toList #[] resident resident.size ∧
      BackingTrace resident.toList #[] (backing resident.toList #[]) (4 * resident.size) (4 * resident.size) ∧
      CompilerArrayTrace.Trace (sourceItems n rows) #[] (source n rows) rows.length ∧
      FormationTrace ((inputPacket n 0 rows roots).map (FieldInput.natural (width := chosenMixedWidth graph)))
        ((inputPacket n 0 rows roots).map (word (chosenMixedWidth graph))) (inputPacket n 0 rows roots).length ∧
      CompilerArrayTrace.Trace ((inputPacket n 0 rows roots).map (word (chosenMixedWidth graph))) #[]
        ((inputPacket n 0 rows roots).map (word (chosenMixedWidth graph))).toArray
        (inputPacket n 0 rows roots).length ∧
      checks + 9 * resident.size + rows.length + 2 * (inputPacket n 0 rows roots).length + n ≤ 94948 * n := by
  intro resident
  obtain ⟨checks, cells, validation, counters, bound, cellBound⟩ :=
    original_preparation_linear graph forest rows matched (fun _ => (0 : Int)) b target
  obtain ⟨instructions, backingWords, sourceArray, fields, packetArray, formationBound⟩ :=
    original_resident_formation graph forest rows roots matched rootMatches (fun _ => (0 : Int)) b target
  have positive : 0 < n := Nat.zero_lt_of_lt target.isLt
  change 9 * resident.size + rows.length + 2 * (inputPacket n 0 rows roots).length + n ≤ _ at formationBound
  exact ⟨checks, cells, validation, counters, cellBound, instructions, backingWords, sourceArray,
    fields, packetArray, by omega⟩

/-- A complete run binds the emitted physical descriptor to the cold RAM
execution and every charged preparation trace. -/
def RecoveryRun (graph : DAG n) (forest : graph.FormulaForest) (b : Nat)
    (bridge : Physical.Bridge n) (positive : 0 < b) (K : Finset (Channel n))
    (rows : List Row) (roots : List Nat) (matched : RowsMatch graph rows)
    (address loaded temporary : Word (chosenMixedWidth graph))
    (saved : Fin 8 → Word (chosenMixedWidth graph)) : Prop :=
  let resident := forestProgram graph forest b bridge.target rows roots matched
  ∃ final : Controller.Cost.State (chosenMixedWidth graph) 8, ∃ ticks peak checks cells : Nat,
  Execution resident
    (classificationInitial (chosenMixedWidth graph) graph rows roots (assignmentOfSet {bridge.target})
      bridge.target [] [] address loaded temporary saved) final ticks peak ∧
  final.halted = true ∧ final.reg 4 = word (chosenMixedWidth graph) 1 ∧
  SharedZeroOutput.decode final.output n = K ∧
  Physical.BridgeInputDetects bridge true graph.observations (descriptorInput bridge positive final.output) true ∧
  SourceValidationTrace n 0 rows (sourceItems n rows) checks cells ∧
  CompilerArrayTrace.Trace (List.replicate n (0 : Nat)) #[] (Array.replicate n 0) n ∧
  cells ≤ sourceWords n rows ∧
  CompilerArrayTrace.Trace resident.toList #[] resident resident.size ∧
  BackingTrace resident.toList #[] (backing resident.toList #[]) (4 * resident.size) (4 * resident.size) ∧
  CompilerArrayTrace.Trace (sourceItems n rows) #[] (source n rows) rows.length ∧
  FormationTrace ((inputPacket n 0 rows roots).map (FieldInput.natural (width := chosenMixedWidth graph)))
    ((inputPacket n 0 rows roots).map (word (chosenMixedWidth graph))) (inputPacket n 0 rows roots).length ∧
  CompilerArrayTrace.Trace ((inputPacket n 0 rows roots).map (word (chosenMixedWidth graph))) #[]
    ((inputPacket n 0 rows roots).map (word (chosenMixedWidth graph))).toArray (inputPacket n 0 rows roots).length ∧
  ticks ≤ 57102 * n ∧
  ticks + checks + 9 * resident.size + rows.length + 2 * (inputPacket n 0 rows roots).length + n ≤ 152050 * n ∧
  programWords resident + peak + 9 * resident.size + rows.length +
      2 * (inputPacket n 0 rows roots).length + n + cells + sourceWords n rows ≤ 140000 * n

theorem full_recovery (graph : DAG n) (forest : graph.FormulaForest)
    (b : Nat) (bridge : Physical.Bridge n) (positive : 0 < b) (K : Finset (Channel n))
    (detects : Physical.BridgeInputDetects bridge true graph.observations
      (Physical.realizeBridge bridge positive K) true)
    (unique : ∀ L, Admissible b bridge.target L → Physical.BridgeInputDetects bridge true graph.observations
      (Physical.realizeBridge bridge positive L) true → L = K)
    (small : forestSize graph ≤ 12 * n)
    (rows : List Row) (roots : List Nat) (matched : RowsMatch graph rows)
    (heads : UniformDAGSource.HeadsMatch graph rows matched) (rootMatches : RootsMatch graph roots)
    (address loaded temporary : Word (chosenMixedWidth graph)) (saved : Fin 8 → Word (chosenMixedWidth graph)) :
    RecoveryRun graph forest b bridge positive K rows roots matched address loaded temporary saved := by
  obtain ⟨final, ticks, peak, trace, halted, decision, time, space, resident, previous, output⟩ :=
    forest_cold_recovery graph forest b bridge positive K detects unique small rows roots matched heads
      rootMatches [] [] address loaded temporary saved
  obtain ⟨checks, cells, validation, counters, cellBound, instructions, backingWords, sourceArray, fields, packetArray, bound⟩ :=
    forest_preparation graph forest b bridge.target small rows roots matched rootMatches
  have fits : 1 < 2 ^ chosenMixedWidth graph := by have := chosenMixedCapacity graph; omega
  have decoded : SharedZeroOutput.decode final.output n = K := by
    rw [output]
    simpa only [List.ofFn_eq_map, boolWord, ForestZeroChannelEmit.bitWord,
      setOfAssignment_assignmentOfSet] using SharedZeroOutput.decode_prefix (assignmentOfSet K) previous fits
  have physical : Physical.BridgeInputDetects bridge true graph.observations
      (descriptorInput bridge positive final.output) true := by
    unfold descriptorInput
    rw [decoded]
    exact detects
  refine ⟨final, ticks, peak, checks, cells, trace, halted, decision, decoded, physical,
    validation, counters, cellBound, instructions, backingWords, sourceArray, fields, packetArray, time, ?_, ?_⟩
  · omega
  · simp only [List.length_nil, Nat.add_zero] at resident
    have footprint : sourceWords n rows ≤ 84 * n := by
      rw [sourceWords_exact graph rows matched]
      unfold forestSize at small
      omega
    omega

/-- Uniform complete critical-family recovery, with the actual supplied source
rows and a default-zero physical witness record. -/
theorem critical_complete (b : Nat) (bridge : Physical.Bridge n) (positive : 0 < b)
    (K : Finset (Channel n)) (legal : K ∈ criticalSets b bridge.target)
    (rows : List Row) (roots : List Nat) (matched : RowsMatch (criticalDAG K) rows)
    (heads : UniformDAGSource.HeadsMatch (criticalDAG K) rows matched)
    (rootMatches : RootsMatch (criticalDAG K) roots)
    (address loaded temporary : Word (chosenMixedWidth (criticalDAG K)))
    (saved : Fin 8 → Word (chosenMixedWidth (criticalDAG K))) :
    RecoveryRun (criticalDAG K) (critical_forest K) b bridge positive K
      rows roots matched address loaded temporary saved := by
  have detects := critical_physical_realizer_detects bridge positive K legal
  rw [← critical_observations] at detects
  apply full_recovery (criticalDAG K) (critical_forest K) b bridge positive K detects
    _ _ rows roots matched heads rootMatches address loaded temporary saved
  · intro L admissible detected
    rw [critical_observations] at detected
    have equal := critical_physical_detects_only_hidden bridge K legal _ true detected
    rw [(Physical.realizeBridge_spec bridge positive L admissible).2.2.2.2,
      setOfAssignment_assignmentOfSet] at equal
    exact equal
  · have bound := criticalDAG_countedSize_le K
    have positiveN := bridge.target.isLt
    rw [DAG.countedSize_eq] at bound
    unfold forestSize
    omega

theorem cycle_complete (b : Nat) (bridge : Physical.Bridge n) (positive : 0 < b)
    (rows : List Row) (roots : List Nat) (matched : RowsMatch (cycleDAG n) rows)
    (heads : UniformDAGSource.HeadsMatch (cycleDAG n) rows matched)
    (rootMatches : RootsMatch (cycleDAG n) roots)
    (address loaded temporary : Word (chosenMixedWidth (cycleDAG n)))
    (saved : Fin 8 → Word (chosenMixedWidth (cycleDAG n))) :
    RecoveryRun (cycleDAG n) (cycle_forest n) b bridge positive Finset.univ
      rows roots matched address loaded temporary saved := by
  apply full_recovery (cycleDAG n) (cycle_forest n) b bridge positive Finset.univ
    (cycle_detects_full bridge positive) (fun L legal detects => cycle_unique bridge positive L legal detects)
    _ rows roots matched heads rootMatches address loaded temporary saved
  have bound := cycle_size n
  have positiveN := bridge.target.isLt
  rw [DAG.countedSize_eq] at bound
  unfold forestSize
  omega

end
end Controller.Cost.CriticalSets
