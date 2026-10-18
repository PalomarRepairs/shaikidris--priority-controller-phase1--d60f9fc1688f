module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Extensions.MonotoneNativeDetector
public import Controller.Extensions.LiteralNativeDetector
public import Controller.Cost.SharedDetectorCold

public import Mathlib.Tactic.Ring

@[expose] public section

/-! Executable dispatch for the seven proper typed gate bases. The guarded
branch uses the shared detector; the other branches use the extremal-set or
literal-matrix detector and their native continuations. -/
namespace Controller.Extensions.ProperBasisDetector
open Controller.Decoder Controller.Decoder.DAG Controller.Cost Controller.Native Controller.Native.SourceController
open Controller.Cost.NativeSourceExecution Controller.Cost.UniformDAGSource Controller.Cost.UniformDAGRun
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestInputPrefixStored
open Controller.Extensions.GateBasis

inductive Kind where | guarded | monotone | literal
  deriving DecidableEq, Repr

def select (basis : Basis) : Kind :=
  if basis.conjunction = false then .guarded else if basis.negativeGuard = false then .monotone else .literal

def Valid (graph : DAG n) : Kind → Prop
  | .guarded => graph.Guarded
  | .monotone => NoNegativeGuards graph
  | .literal => NoDisjunction graph

theorem selected_valid (graph : DAG n) (basis : Basis) (uses : Uses graph basis) (proper : basis ≠ full) :
    Valid graph (select basis) := by
  unfold select
  split_ifs with conjunction guard
  · exact no_conjunction_guarded graph basis uses conjunction
  · exact no_guard graph basis uses guard
  · obtain missing | missing | missing := (proper_iff_missing basis).mp proper
    · exact no_disjunction graph basis uses missing
    · exact False.elim (conjunction missing)
    · exact False.elim (guard missing)

def Feasible (parameters : Parameters) : Prop :=
  ∃ root ∈ parameters.decoder.roots, ∃ K, Admissible parameters.buses parameters.bridge.target K ∧
    parameters.decoder.eval (assignmentOfSet K) root ≠ parameters.decoder.eval (assignmentOfSet {parameters.bridge.target}) root

abbrev coldWidth (parameters : Parameters) : Nat :=
  SharedDetectorLoop.Width parameters parameters.decoder (SharedDetectorCold.retained parameters parameters.decoder)

def coldInitial (parameters : Parameters) (rows : List Row) (roots : List Nat) : State (coldWidth parameters) 8 where
  reg _ := word _ 0
  heap := #[]
  stack := SharedDetectorCold.inputWords (coldWidth parameters) rows roots (assignmentOfSet {parameters.bridge.target}) ++
    word _ parameters.bridge.target.val ::
      (SharedRetainedCandidates.masks (coldWidth parameters)
        (assignmentOfSet (extensionBase parameters.buses parameters.bridge.target ∅))
        ((List.finRange parameters.channels).map (assignmentOfSet ∅)) ++ [])
  output := []
  pc := word _ 0
  halted := false

structure Machine where
  width : Nat
  program : Program width 8
  initial : State width 8
  accepted : State width 8 → Bool

def machine (parameters : Parameters) (kind : Kind) (rows : List Row) (roots : List Nat) : Machine :=
  match kind with
  | .guarded => ⟨coldWidth parameters, SharedDetectorCold.program parameters parameters.decoder ∅ ∅ rows roots,
      coldInitial parameters rows roots, fun state => state.reg 4 == word _ 1⟩
  | .monotone => ⟨MonotoneNativeDetector.Width parameters parameters.decoder,
      MonotoneNativeDetector.program parameters parameters.decoder rows roots,
      LiteralSourceConstruction.initial parameters.channels _ rows roots [] [], fun state => !state.output.isEmpty⟩
  | .literal => ⟨LiteralNativeDetector.Width parameters parameters.decoder,
      LiteralNativeDetector.program parameters parameters.decoder rows roots,
      LiteralSourceConstruction.initial parameters.channels _ rows roots [] [], fun state => !state.output.isEmpty⟩

def NativeOutput (parameters : Parameters) (final : State width 8) :
    Option (Finset (Channel parameters.channels)) → Prop
  | none => final.output = []
  | some K => final.output = (NativeRootLoad.words width
      (SourceLift.finite parameters (Physical.realizeBridge parameters.bridge parameters.positiveBuses K))).reverse ++ [] ∧
      Certificate.ModelCheck.check (formula parameters)
        (NativeRealizedChecked.decodeOutput final.output (compile parameters).toState.count) = true

theorem output_correct (parameters : Parameters) (final : State width 8)
    (answer : Option (Finset (Channel parameters.channels)))
    (meaning : answer = none ↔ ¬Feasible parameters) (output : NativeOutput parameters final answer) :
    ((!final.output.isEmpty) = true ↔ Feasible parameters) ∧
      ((!final.output.isEmpty) = true → Certificate.ModelCheck.check (formula parameters)
        (NativeRealizedChecked.decodeOutput final.output (compile parameters).toState.count) = true) := by
  have roots := (sourceCircuit parameters).roots_le
  have channelBound : parameters.channels ≤ SourceInitialIDs.rootCount parameters := by
    simp only [SourceInitialIDs.rootCount]; omega
  have channelPositive := parameters.bridge.target.isLt
  have countPositive : 0 < (compile parameters).toState.count := by omega
  cases answer with
  | none =>
    have impossible := meaning.mp rfl
    simp only [NativeOutput] at output
    simp [output, impossible]
  | some K =>
    have feasible : Feasible parameters := by
      by_contra no
      have := meaning.mpr no
      contradiction
    obtain ⟨out, checked⟩ := output
    have nonempty : (!final.output.isEmpty) = true := by
      rw [out]
      simp only [List.append_nil, Bool.not_eq_true', List.isEmpty_eq_false_iff, List.reverse_eq_nil_iff]
      intro empty
      have length := congrArg List.length empty
      simp only [List.length_reverse, NativeRootLoad.words_length, List.length_nil] at length
      omega
    exact ⟨by simp [nonempty, feasible], fun _ => checked⟩

theorem guarded_meaning (parameters : Parameters) :
    (∃ output : Fin parameters.decoder.roots.length, ∃ K, Admissible parameters.buses parameters.bridge.target K ∧
      ExtendsFixed ∅ ∅ K ∧ parameters.decoder.eval (assignmentOfSet {parameters.bridge.target}) parameters.decoder.roots[output.val] ≠
        parameters.decoder.eval (assignmentOfSet K) parameters.decoder.roots[output.val]) ↔ Feasible parameters := by
  constructor
  · rintro ⟨i, K, eligible, _, changes⟩
    exact ⟨_, List.getElem_mem i.isLt, K, eligible, changes.symm⟩
  · rintro ⟨root, member, K, eligible, changes⟩
    obtain ⟨i, eq⟩ := List.mem_iff_get.mp member
    change parameters.decoder.roots[i.val] = root at eq
    exact ⟨i, K, eligible, by simp [ExtendsFixed], by simpa only [eq] using changes.symm⟩

theorem word_boolean_eq (width : Nat) (room : 1 < 2 ^ width) (answer : Bool) :
    ((word width (if answer then 1 else 0)) == word width 1) = answer := by
  cases answer <;> simp [word, Nat.mod_eq_of_lt room]

set_option maxHeartbeats 2400000 in
/-- Each selected machine halts, decides detection, and emits a checked native
model when it accepts. The two dense branches cost O(nG+N); the guarded
branch is bounded here by O((n+q)G+N). All resident code is charged. -/
theorem execution (parameters : Parameters) (raw : parameters.layout = .raw) (drive : parameters.drive = true)
    (basis : Basis) (uses : Uses parameters.decoder basis) (proper : basis ≠ full)
    (rows : List Row) (roots : List Nat) (matched : RowsMatch parameters.decoder rows)
    (heads : HeadsMatch parameters.decoder rows matched) (rootMatches : RootsMatch parameters.decoder roots) :
    let selected := machine parameters (select basis) rows roots
    ∃ final ticks peak, Execution selected.program selected.initial final ticks peak ∧
      final.halted = true ∧
      ticks ≤ 10000 * ((parameters.channels + parameters.decoder.roots.length + 1) * (parameters.decoder.countedSize + 1)) +
        55 * (selectedSize parameters).total + 1 ∧
      programWords selected.program + peak ≤
        10000 * ((parameters.channels + 1) * (parameters.decoder.countedSize + 1)) + 400 * (selectedSize parameters).total ∧
      (selected.accepted final = true ↔ Feasible parameters) ∧
      (selected.accepted final = true → Certificate.ModelCheck.check (formula parameters)
        (NativeRealizedChecked.decodeOutput final.output (compile parameters).toState.count) = true) := by
  have valid := selected_valid parameters.decoder basis uses proper
  have graphSize := parameters.decoder.countedSize_eq
  have smallProduct : (parameters.channels + 1) * (parameters.decoder.countedSize + 1) ≤
      (parameters.channels + parameters.decoder.roots.length + 1) * (parameters.decoder.countedSize + 1) :=
    Nat.mul_le_mul_right _ (by omega)
  cases chosen : select basis with
  | monotone =>
    have noGuards : NoNegativeGuards parameters.decoder := by simpa only [chosen, Valid] using valid
    obtain ⟨final, ticks, peak, trace, time, space, halted, stack, out, meaning⟩ :=
      MonotoneNativeDetector.from_source parameters raw drive parameters.decoder noGuards rows roots matched heads rootMatches
        id (by intro i K; rfl) [] []
    have decision := output_correct parameters final _ meaning out
    simp only [List.length_nil, Nat.add_zero] at space
    simp only [chosen, machine]
    exact ⟨final, ticks, peak, trace, halted, by omega, by omega, decision⟩
  | literal =>
    have noOr : NoDisjunction parameters.decoder := by simpa only [chosen, Valid] using valid
    obtain ⟨final, ticks, peak, trace, time, space, halted, stack, out, meaning⟩ :=
      LiteralNativeDetector.from_source parameters raw drive parameters.decoder noOr rows roots matched heads rootMatches
        id (by intro i K; rfl) [] []
    have decision := output_correct parameters final _ meaning out
    simp only [List.length_nil, Nat.add_zero] at space
    simp only [chosen, machine]
    exact ⟨final, ticks, peak, trace, halted, by omega, by omega, decision⟩
  | guarded =>
    have guarded : parameters.decoder.Guarded := by simpa only [chosen, Valid] using valid
    obtain ⟨answer, final, ticks, peak, trace, halted, decision, time, space, meaning, checked⟩ :=
      SharedDetectorCold.execution parameters raw drive parameters.decoder guarded ∅ ∅ (by simp [FixedConsistent])
        rows roots matched heads rootMatches id (by intro i K; rfl) [] (coldInitial parameters rows roots)
        rfl rfl rfl rfl
    have widthRoom := SharedMachineCapacity.capacity (SharedDetectorCold.retained parameters parameters.decoder)
      parameters.decoder.countedSize (selectedSize parameters).total
    have oneFits : 1 < 2 ^ coldWidth parameters := by exact lt_trans (by omega) widthRoom
    have accepted : (final.reg 4 == word (coldWidth parameters) 1) = answer := by
      rw [decision]
      exact word_boolean_eq (coldWidth parameters) oneFits answer
    have sourceLength := SharedDetectorCold.inputWords_length (coldWidth parameters) parameters.decoder rows roots matched rootMatches
      (assignmentOfSet {parameters.bridge.target})
    have packet : SharedDetectorPrepared.packetSize parameters.decoder ≤ 7 * (parameters.decoder.countedSize + 1) := by
      simp only [SharedDetectorPrepared.packetSize, SharedDetectorPrepared.maskBase, SharedDetectorPrepared.rootBase]
      omega
    have initialLive : (coldInitial parameters rows roots).liveWords ≤ 20 * (parameters.decoder.countedSize + 1) := by
      simp only [coldInitial, State.liveWords, Array.size_empty, List.length_append, List.length_cons,
        SharedRetainedCandidates.masks_length, List.length_map, List.length_finRange, List.length_nil, sourceLength]
      omega
    have codeBound := SharedDetectorCold.program_words parameters parameters.decoder ∅ ∅ rows roots rootMatches
    have baseline : parameters.decoder.countedSize + 1 ≤ (parameters.channels + 1) * (parameters.decoder.countedSize + 1) :=
      le_mul_of_one_le_left (Nat.zero_le _) (by omega)
    have positive : 0 < parameters.decoder.countedSize + 1 := by omega
    simp only [chosen, machine]
    refine ⟨final, ticks, peak, trace, halted, ?_, by omega, ?_, ?_⟩
    · have cost : (if answer = true then 55 * (selectedSize parameters).total else 0) ≤ 55 * (selectedSize parameters).total := by split <;> omega
      have reassoc : (parameters.channels + parameters.decoder.roots.length + 1) * (5100 * (parameters.decoder.countedSize + 1)) =
          5100 * ((parameters.channels + parameters.decoder.roots.length + 1) * (parameters.decoder.countedSize + 1)) := by ring
      rw [reassoc] at time; omega
    · rw [accepted]
      exact meaning.trans (guarded_meaning parameters)
    · rw [accepted]
      exact checked

end Controller.Extensions.ProperBasisDetector
