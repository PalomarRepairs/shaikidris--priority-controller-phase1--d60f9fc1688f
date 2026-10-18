module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.SourceStagePolarity
public import Controller.NativeProof.SourceBusAdvance

@[expose] public section

/-! Native AND-tree unit and alias evaluation. Identity leaves reuse their
existing literal; all other outputs are obtained by ordinary resolution.
Known input units keep the same cofactor context through every merge. -/
namespace Controller.NativeProof.TreeUnits
open Controller.CNF Controller.Resolution
open Controller.NativeProof.FoldProjection Controller.NativeProof.SourceStageCongruence
open Controller.NativeProof.SourceStagePolarity
open Controller.NativeProof.SourceBusSchedule
open Controller.NativeProof.SourceBusAdvance
variable {v : Nat} {state : State v} {root : Literal (Fin v)}
variable {inputs : List (Literal (Fin v))}

/-- Lookup follows the concrete input list and checks literal identity, so an
alias never requires a choice operation in the emitted proof program. -/
def mappedUnit {α : Type} (items : List α) (handle : α → Literal (Fin v))
    (context : Clause (Fin v))
    (rows : ∀ item ∈ items, AvailableSubclause state (context ++ [handle item]))
    (input : Literal (Fin v)) (present : input ∈ items.map handle) :
    AvailableSubclause state (context ++ [input]) :=
  match items with
  | [] => False.elim (List.not_mem_nil present)
  | item :: rest => by
      by_cases equal : input = handle item
      · exact equal ▸ rows item (by simp)
      · exact mappedUnit rest handle context
          (fun old member => rows old (List.mem_cons_of_mem _ member)) input
          ((List.mem_cons.mp present).resolve_left equal)

def force (tree : AndTree state root inputs) (context : Clause (Fin v))
    (units : ∀ input ∈ inputs, AvailableSubclause state (context ++ [input])) :
    SubclauseProjection state (context ++ [root]) (2 * tree.nodes + inputs.length) := by
  cases tree with
  | leaf => exact ⟨state, [], rfl, units root (by simp), by simp⟩
  | @node leftRoot rightRoot leftInputs rightInputs left right _ rows =>
    let tree := AndTree.node left right root rows
    let projected := projectTreeLong tree
    have two : 2 ≤ (leftInputs ++ rightInputs).length := by
      have one := left.nodes_leaves
      have other := right.nodes_leaves
      simp only [List.length_append]
      omega
    let row := nonunaryAggregate projected.result two
    have count : projected.steps.length ≤ 2 * tree.nodes := projected.count
    have known : ∀ input ∈ leftInputs ++ rightInputs, AvailableSubclause projected.state (context ++ [input]) :=
      fun input member => afterTrace (units input member) projected.state projected.steps projected.checked
    let target := context ++ [root]
    let parent : AvailableSubclause projected.state ((leftInputs ++ rightInputs).map negate ++ target) :=
      retarget row (by
        intro literal member
        simp only [target, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member ⊢
        aesop)
    let eliminated := dischargeInputs projected.state (leftInputs ++ rightInputs) target parent (fun input member =>
      retarget (known input member) (by
        intro literal member
        simp only [target, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member ⊢
        aesop))
    refine ⟨eliminated.state, projected.steps ++ eliminated.steps, ?_, eliminated.result, ?_⟩
    · rw [runSteps_append, projected.checked]
      exact eliminated.checked
    · have final := eliminated.count
      dsimp only [tree] at count
      simp only [List.length_append] at final ⊢
      omega

def deny (tree : AndTree state root inputs) (context : Clause (Fin v))
    (input : Literal (Fin v)) (member : input ∈ inputs)
    (unit : AvailableSubclause state (context ++ [negate input])) :
    SubclauseProjection state (context ++ [negate root]) (2 * tree.nodes + 1) := by
  let projected := projectTreeInputs tree
  let unitNow := afterTrace unit projected.state projected.steps projected.checked
  match direction : projected.results input member with
  | .identity same =>
    exact ⟨projected.state, projected.steps, projected.checked,
      by simpa only [same] using unitNow, projected.count.trans (by omega)⟩
  | .derived row =>
    let left : AvailableSubclause projected.state (negate input :: context) :=
      retarget unitNow (by
        intro literal present
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at present ⊢
        aesop)
    let right : AvailableSubclause projected.state (input :: [negate root]) :=
      retarget row (by
        intro literal present
        simp only [List.mem_cons, List.not_mem_nil, or_false] at present ⊢
        aesop)
    let joined := longMerge projected.state input context [negate root] left right
    refine ⟨joined.state, projected.steps ++ joined.steps, ?_,
      longMerge_result _ _ _ _ _ _, ?_⟩
    · rw [runSteps_append, projected.checked]
      exact longMerge_run _ _ _ _ _ _
    · have first := projected.count
      have one : joined.steps.length ≤ 1 := longMerge_count _ _ _ _ _ _
      simp only [List.length_append]
      omega

/-- Carry a directional certificate under a fixed cofactor context. -/
def contextualDirection (context : Clause (Fin v))
    (certificate : DirectionalCertificate state root input) : GuardedTransfer state context root input :=
  match (generalizing := false) certificate with
  | .identity same => .identity same
  | .derived available => .derived (retarget available
      (fun _ member => List.mem_append_right context member))

/-- One chosen input is the only remaining live condition of the AND. -/
def reduceToInput (tree : AndTree state root inputs) (context : Clause (Fin v))
    (input : Literal (Fin v)) (member : input ∈ inputs)
    (units : ∀ other ∈ inputs, other ≠ input →
      AvailableSubclause state (context ++ [other])) :
    PairedProjection state context root input
      (4 * tree.nodes + inputs.length) := by
  cases tree with
  | leaf =>
    have same : root = input := (show input = root by simpa using member).symm
    exact ⟨state, [], rfl, ⟨.identity same, .identity same.symm⟩, by simp⟩
  | @node leftRoot rightRoot leftInputs rightInputs left right _ rows =>
    let tree := AndTree.node left right root rows
    let projected := projectTreeLong tree
    have two : 2 ≤ (leftInputs ++ rightInputs).length := by
      have one := left.nodes_leaves
      have other := right.nodes_leaves
      simp only [List.length_append]
      omega
    let row := nonunaryAggregate projected.result two
    let known : ∀ other ∈ leftInputs ++ rightInputs, other ≠ input →
        AvailableSubclause projected.state (context ++ [other]) := fun other present different =>
      afterTrace (units other present different) projected.state projected.steps projected.checked
    let rest := (leftInputs ++ rightInputs).filter fun other => other ≠ input
    let target := context ++ [negate input, root]
    let parent : AvailableSubclause projected.state (rest.map negate ++ target) := retarget row (by
      intro literal present
      rcases List.mem_cons.mp present with same | old
      · exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (by simp [same]))))
      · obtain ⟨other, listed, same⟩ := List.mem_map.mp old
        by_cases equal : other = input
        · subst other
          exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (by simp [same.symm]))))
        · exact List.mem_append.mpr (Or.inl (List.mem_map.mpr
            ⟨other, List.mem_filter.mpr ⟨listed, by simpa using equal⟩, same⟩)))
    let eliminated := dischargeInputs projected.state rest target parent (fun other listed =>
      retarget (known other (List.mem_filter.mp listed).1 (by simpa using (List.mem_filter.mp listed).2)) (by
        intro literal present
        simp only [target, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at present ⊢
        aesop))
    let treeNow := tree.afterTrace eliminated.state (projected.steps ++ eliminated.steps) (by
      rw [runSteps_append, projected.checked]
      exact eliminated.checked)
    let directions := projectTreeInputs treeNow
    let forward := contextualDirection context (directions.results input member)
    let backward : GuardedTransfer directions.state context input root :=
      .derived (afterTrace eliminated.result directions.state directions.steps directions.checked)
    refine ⟨directions.state, (projected.steps ++ eliminated.steps) ++ directions.steps, ?_,
      ⟨forward, backward⟩, ?_⟩
    · simp only [runSteps_append, projected.checked, Option.bind_some, eliminated.checked,
        directions.checked]
    · have first := projected.count
      have second := eliminated.count
      have third : directions.steps.length ≤ 2 * tree.nodes := by
        simpa only [treeNow, AndTree.afterTrace_nodes] using directions.count
      have filtered : rest.length ≤ (leftInputs ++ rightInputs).length := List.length_filter_le _ _
      dsimp only [tree] at first third
      simp only [List.length_append] at first third filtered ⊢
      omega

structure TransferProjection (start : State v) (context : Clause (Fin v))
    (input output : Literal (Fin v)) (budget : Nat) where
  state : State v
  steps : List (Step v)
  checked : runSteps start steps = some state
  result : GuardedTransfer state context input output
  count : steps.length ≤ budget

def compose (state : State v) (context : Clause (Fin v))
    (first : GuardedTransfer state context a b) (second : GuardedTransfer state context b c) :
    TransferProjection state context a c 1 := by
  cases first with
  | identity equal => exact ⟨state, [], rfl, equal ▸ second, by simp⟩
  | derived one =>
    cases second with
    | identity equal => exact ⟨state, [], rfl, equal ▸ .derived one, by simp⟩
    | derived two =>
      let joined := guardedChain state context a b c one two
      exact ⟨joined.state, joined.steps, joined.checked, .derived joined.result, joined.count⟩

def composePairs (state : State v) (context : Clause (Fin v))
    (first : DirectionPair state context a b) (second : DirectionPair state context b c) :
    PairedProjection state context a c 2 := by
  let forward := compose state context first.forward second.forward
  let backwards := compose forward.state context
    (second.backward.afterTrace forward.state forward.steps forward.checked)
    (first.backward.afterTrace forward.state forward.steps forward.checked)
  refine ⟨backwards.state, forward.steps ++ backwards.steps, ?_,
    ⟨forward.result.afterTrace backwards.state backwards.steps backwards.checked, backwards.result⟩, ?_⟩
  · rw [runSteps_append, forward.checked]
    exact backwards.checked
  · have one := forward.count
    have two := backwards.count
    simp only [List.length_append]
    omega

def forceFromCases (state : State v) (context : Clause (Fin v))
    (input output : Literal (Fin v))
    (positive : AvailableSubclause state (context ++ [input, output]))
    (negative : GuardedTransfer state context input output) :
    SubclauseProjection state (context ++ [output]) 1 := by
  cases negative with
  | identity same =>
    exact ⟨state, [], rfl, retarget positive (by
      intro literal member
      simpa only [same, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_self] using member), by simp⟩
  | derived row =>
    let left : AvailableSubclause state (input :: (context ++ [output])) := retarget positive (by
      intro literal member
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member ⊢
      aesop)
    let right : AvailableSubclause state (negate input :: (context ++ [output])) := retarget row (by
      intro literal member
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member ⊢
      aesop)
    let joined := longMerge state input (context ++ [output]) (context ++ [output]) right left
    exact ⟨joined.state, joined.steps, longMerge_run _ _ _ _ _ _,
      retarget (longMerge_result _ _ _ _ _ _) (by
        intro literal member
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member ⊢
        aesop), longMerge_count _ _ _ _ _ _⟩

def nonunaryLong (tree : AndTree state root inputs) (two : 2 ≤ inputs.length) :
    SubclauseProjection state (root :: inputs.map negate) (2 * tree.nodes) := by
  let projected := projectTreeLong tree
  exact ⟨projected.state, projected.steps, projected.checked,
    nonunaryAggregate projected.result two, projected.count⟩

theorem force_count_nodes (tree : AndTree state root inputs) (context : Clause (Fin v))
    (units : ∀ input ∈ inputs, AvailableSubclause state (context ++ [input])) :
    (force tree context units).steps.length ≤ 4 * tree.nodes := by
  cases tree with
  | leaf => simp [force, AndTree.nodes]
  | @node leftRoot rightRoot leftInputs rightInputs left right _ rows =>
    let tree := AndTree.node left right root rows
    have actual := (force tree context units).count
    have size : tree.nodes + 1 = (leftInputs ++ rightInputs).length := tree.nodes_leaves
    have positive : 0 < tree.nodes := by simp [tree, AndTree.nodes]
    generalize (force tree context units).steps.length = emitted at actual ⊢
    change emitted ≤ 4 * tree.nodes
    generalize tree.nodes = count at actual size positive ⊢
    omega

theorem deny_count_nodes (tree : AndTree state root inputs) (context : Clause (Fin v))
    (leaf : Literal (Fin v)) (member : leaf ∈ inputs)
    (unit : AvailableSubclause state (context ++ [negate leaf])) :
    (deny tree context leaf member unit).steps.length ≤ 3 * tree.nodes := by
  cases tree with
  | leaf =>
    have same : leaf = root := by simpa using member
    subst leaf
    simp [deny, projectTreeInputs, projectTreeInputsBelow, AndTree.nodes]
  | @node leftRoot rightRoot leftInputs rightInputs left right _ rows =>
    let tree := AndTree.node left right root rows
    have actual := (deny tree context leaf member unit).count
    have positive : 0 < tree.nodes := by simp [tree, AndTree.nodes]
    generalize (deny tree context leaf member unit).steps.length = emitted at actual ⊢
    change emitted ≤ 3 * tree.nodes
    generalize tree.nodes = count at actual positive ⊢
    omega

end Controller.NativeProof.TreeUnits
