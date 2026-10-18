module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Native.BoundedEncode
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

/-!
# Interface alias transport

The source interface defines a fresh W output by a unary AND of D. The
independent-W specification satisfies that alias equation after its D=d and
W=d units. This intermediate layout retains every named producer and all four
interface/discrepancy units. Producer-tree rearrangement and omitted unary
aliases require their own source-layout maps and count theorems.
-/

namespace Controller.Native.InterfaceAlias

inductive Root (n b : ℕ) where
  | enable (channel : Fin n)
  | request (bus : Fin b) (channel : Fin n)
  deriving DecidableEq, Repr

inductive Variable (parameters : Parameters) where
  | primary (role : Root parameters.channels parameters.buses)
  | internal (role : Internal parameters)
  | wire
  deriving DecidableEq, Repr

/-- The free W slot becomes a fresh defined slot; every other named slot is retained. -/
def slots (parameters : Parameters) : Controller.Native.Variable parameters ≃ Variable parameters where
  toFun
    | .primary (.enable channel) => .primary (.enable channel)
    | .primary (.request bus channel) => .primary (.request bus channel)
    | .primary .wire => .wire
    | .internal role => .internal role
  invFun
    | .primary (.enable channel) => .primary (.enable channel)
    | .primary (.request bus channel) => .primary (.request bus channel)
    | .wire => .primary .wire
    | .internal role => .internal role
  left_inv slot := by cases slot with
    | primary root => cases root <;> rfl
    | internal role => rfl
  right_inv slot := by cases slot with
    | primary root => cases root <;> rfl
    | internal role => rfl
    | wire => rfl

def wireBlock (parameters : Parameters) : CNF.Formula (Variable parameters) :=
  (CNF.Gate.and [(.internal .driver, true)]).block (.wire, true)

/-- Interface-alias layout before producer-tree and unary-alias optimizations. -/
def formula (parameters : Parameters) : CNF.Formula (Variable parameters) :=
  CNF.relabel (slots parameters) parameters.specificationFormula ++ wireBlock parameters

/-- Defining W as D is justified by both retained interface units. -/
theorem abstract_model_wire_eq_driver (parameters : Parameters)
    (assignment : Controller.Native.Variable parameters → Bool)
    (satisfied : CNF.Satisfies assignment parameters.specificationFormula) :
    assignment (.primary .wire) = assignment (.internal .driver) := by
  have assertions := ((CNF.satisfies_append _ _ _).mp satisfied).2
  have units := (CNF.satisfies_ofClauses assignment _).mp assertions
  have wire : assignment (.primary .wire) = parameters.drive := by
    have unit := units [(.primary .wire, parameters.drive)] (by
      simp [Parameters.assertions])
    simpa [CNF.ClauseHolds, CNF.LiteralHolds] using unit
  have driver : assignment (.internal .driver) = parameters.drive := by
    have unit := units [(.internal .driver, parameters.drive)] (by
      simp [Parameters.assertions])
    simpa [CNF.ClauseHolds, CNF.LiteralHolds] using unit
  exact wire.trans driver.symm

/-- The added source-interface gate is redundant only under the complete interface. -/
theorem satisfies_formula_iff (parameters : Parameters)
    (assignment : Variable parameters → Bool) :
    CNF.Satisfies assignment (formula parameters) ↔
      CNF.Satisfies (assignment ∘ slots parameters) parameters.specificationFormula := by
  rw [formula, CNF.satisfies_append, CNF.satisfies_relabel]
  constructor
  · exact And.left
  · intro model
    refine ⟨model, ?_⟩
    apply (CNF.Gate.block_correct assignment (.wire, true)
      (.and [(.internal .driver, true)])).mpr
    have equality := abstract_model_wire_eq_driver parameters (assignment ∘ slots parameters) model
    simpa [slots, Function.comp_def, CNF.literalValue, CNF.Gate.eval] using equality

instance (parameters : Parameters) : Fintype (Variable parameters) :=
  Fintype.ofEquiv (Controller.Native.Variable parameters) (slots parameters)

/-- The alias gate changes root classification while retaining the complete slot universe. -/
def variableSlots (parameters : Parameters) : List (Variable parameters) :=
  parameters.variableRoles.map (slots parameters)

theorem variableSlots_nodup (parameters : Parameters) : (variableSlots parameters).Nodup :=
  List.Nodup.map (slots parameters).injective parameters.variableRoles_nodup

theorem variableSlots_length (parameters : Parameters) :
    (variableSlots parameters).length = parameters.variableRoles.length := by simp [variableSlots]

/-- Fresh-W alias transport preserves full satisfiability under the retained interface. -/
theorem satisfiable_formula_iff (parameters : Parameters) :
    CNF.Satisfiable (formula parameters) ↔ CNF.Satisfiable parameters.specificationFormula := by
  constructor
  · rintro ⟨assignment, satisfied⟩
    exact ⟨assignment ∘ slots parameters, (satisfies_formula_iff parameters assignment).mp satisfied⟩
  · rintro ⟨assignment, satisfied⟩
    refine ⟨assignment ∘ (slots parameters).symm, ?_⟩
    apply (satisfies_formula_iff parameters _).mpr
    simpa [Function.comp_def] using satisfied

/-- Two complete unary-AND rows are added to the retained named-role specification. -/
theorem formula_rows (parameters : Parameters) :
    (formula parameters).clauses.size = parameters.specificationFormula.clauses.size + 2 := by
  simp [formula, wireBlock, Controller.CNF.OrderedFormula.Internal.clauses_append, CNF.relabel,
    Controller.CNF.OrderedFormula.relabel, CNF.Gate.block, CNF.Gate.clauses, CNF.ofClauses]

/-- The added unary-AND block contributes four stored literal incidences. -/
theorem formula_literals (parameters : Parameters) :
    Bounded.literalIncidences (formula parameters) =
      Bounded.literalIncidences parameters.specificationFormula + 4 := by
  simp [formula, wireBlock, Bounded.literalIncidences, Controller.CNF.OrderedFormula.Internal.clauses_append,
    CNF.relabel, Controller.CNF.OrderedFormula.relabel, Controller.CNF.OrderedFormula.Clause.relabel,
    CNF.Gate.block, CNF.Gate.clauses, CNF.ofClauses, Function.comp_def]

end Controller.Native.InterfaceAlias

namespace Controller.Native.SourceFold

/-- Source folds return a singleton input unchanged and create a constant for an empty list. -/
inductive Tree (α : Type*) where
  | unit
  | leaf (literal : CNF.Literal α)
  | join (left right : Tree α)
  deriving DecidableEq, Repr

def Tree.leaves : Tree α → List (CNF.Literal α)
  | .unit => []
  | .leaf literal => [literal]
  | .join left right => left.leaves ++ right.leaves

def Tree.nodeCount : Tree α → ℕ
  | .unit => 1
  | .leaf _ => 0
  | .join left right => left.nodeCount + right.nodeCount + 1

def Tree.unitCount : Tree α → ℕ
  | .unit => 1
  | .leaf _ => 0
  | .join left right => left.unitCount + right.unitCount

def Tree.eval (junction : Bounded.Junction) (assignment : α → Bool) : Tree α → Bool
  | .unit => junction.eval assignment []
  | .leaf literal => CNF.literalValue assignment literal
  | .join left right => junction.combine (left.eval junction assignment) (right.eval junction assignment)

theorem Tree.eval_leaves (tree : Tree α) (junction : Bounded.Junction) (assignment : α → Bool) :
    tree.eval junction assignment = junction.eval assignment tree.leaves := by
  induction tree with
  | unit => rfl
  | leaf literal => simp [eval, leaves]
  | join left right leftIH rightIH =>
      rw [eval, leaves, Bounded.Junction.eval_append, leftIH, rightIH]

/-- One literal iteration of the generator's adjacent-pair layer. -/
def pairLayer : List (Tree α) → List (Tree α)
  | left :: right :: rest => .join left right :: pairLayer rest
  | remaining => remaining

theorem pairLayer_length : ∀ trees : List (Tree α),
    (pairLayer trees).length = (trees.length + 1) / 2
  | [] => by simp [pairLayer]
  | [_] => by simp [pairLayer]
  | left :: right :: rest => by
      have previous := pairLayer_length rest
      simp only [pairLayer, List.length_cons]
      omega

theorem pairLayer_shorter (trees : List (Tree α)) (atLeastTwo : 2 ≤ trees.length) :
    (pairLayer trees).length < trees.length := by rw [pairLayer_length]; omega

theorem pairLayer_nonempty (trees : List (Tree α)) (nonempty : 0 < trees.length) :
    0 < (pairLayer trees).length := by rw [pairLayer_length]; omega

theorem pairLayer_leaves : ∀ trees : List (Tree α),
    (pairLayer trees).flatMap Tree.leaves = trees.flatMap Tree.leaves
  | [] => by simp [pairLayer]
  | [_] => by simp [pairLayer]
  | left :: right :: rest => by
      simp [pairLayer, Tree.leaves, pairLayer_leaves rest, List.append_assoc]

theorem pairLayer_nodes : ∀ trees : List (Tree α),
    ((pairLayer trees).map Tree.nodeCount).sum + (pairLayer trees).length =
      (trees.map Tree.nodeCount).sum + trees.length
  | [] => by simp [pairLayer]
  | [_] => by simp [pairLayer]
  | left :: right :: rest => by
      have previous := pairLayer_nodes rest
      simp only [pairLayer, List.map_cons, List.sum_cons, List.length_cons, Tree.nodeCount]
      omega

theorem pairLayer_units : ∀ trees : List (Tree α),
    ((pairLayer trees).map Tree.unitCount).sum = (trees.map Tree.unitCount).sum
  | [] => by simp [pairLayer]
  | [_] => by simp [pairLayer]
  | left :: right :: rest => by
      simp [pairLayer, Tree.unitCount, pairLayer_units rest, Nat.add_assoc]

/-- The source balanced loop, terminating because each nontrivial pair layer shrinks. -/
def balance (trees : List (Tree α)) : Tree α :=
  match trees with
  | [] => .unit
  | [tree] => tree
  | left :: right :: rest => balance (pairLayer (left :: right :: rest))
termination_by trees.length
decreasing_by exact pairLayer_shorter _ (by simp)

theorem balance_leaves (trees : List (Tree α)) :
    (balance trees).leaves = trees.flatMap Tree.leaves := by
  have ranked : ∀ height, ∀ trees : List (Tree α), trees.length = height →
      (balance trees).leaves = trees.flatMap Tree.leaves := by
    intro height
    induction height using Nat.strong_induction_on with
    | h height inductionHypothesis =>
        intro trees treeHeight
        cases trees with
        | nil => simp [balance, Tree.leaves]
        | cons left tail =>
            cases tail with
            | nil => simp [balance]
            | cons right rest =>
                rw [balance]
                exact (inductionHypothesis _ (by
                  have shorter := pairLayer_shorter (left :: right :: rest) (by simp)
                  simpa [treeHeight] using shorter) _ rfl).trans (pairLayer_leaves _)
  exact ranked trees.length trees rfl

theorem balance_nodes (trees : List (Tree α)) :
    (balance trees).nodeCount =
      if trees.length = 0 then 1 else (trees.map Tree.nodeCount).sum + trees.length - 1 := by
  have ranked : ∀ height, ∀ trees : List (Tree α), trees.length = height →
      (balance trees).nodeCount =
        if trees.length = 0 then 1 else (trees.map Tree.nodeCount).sum + trees.length - 1 := by
    intro height
    induction height using Nat.strong_induction_on with
    | h height inductionHypothesis =>
        intro trees treeHeight
        cases trees with
        | nil => simp [balance, Tree.nodeCount]
        | cons left tail =>
            cases tail with
            | nil => simp [balance]
            | cons right rest =>
                have shorter := pairLayer_shorter (left :: right :: rest) (by simp)
                have smaller := inductionHypothesis _ (by simpa [treeHeight] using shorter) _ rfl
                have positive := pairLayer_nonempty (left :: right :: rest) (by simp)
                have counts := pairLayer_nodes (left :: right :: rest)
                simp only [ite_eq_right (Nat.ne_of_gt positive)] at smaller
                rw [balance, smaller]
                rw [ite_eq_right (by simp)]
                exact congrArg (fun total : ℕ => total - 1) counts
  exact ranked trees.length trees rfl

theorem balance_units (trees : List (Tree α)) :
    (balance trees).unitCount =
      if trees.length = 0 then 1 else (trees.map Tree.unitCount).sum := by
  have ranked : ∀ height, ∀ trees : List (Tree α), trees.length = height →
      (balance trees).unitCount =
        if trees.length = 0 then 1 else (trees.map Tree.unitCount).sum := by
    intro height
    induction height using Nat.strong_induction_on with
    | h height inductionHypothesis =>
        intro trees treeHeight
        cases trees with
        | nil => simp [balance, Tree.unitCount]
        | cons left tail =>
            cases tail with
            | nil => simp [balance]
            | cons right rest =>
                have shorter := pairLayer_shorter (left :: right :: rest) (by simp)
                have smaller := inductionHypothesis _ (by simpa [treeHeight] using shorter) _ rfl
                have positive := pairLayer_nonempty (left :: right :: rest) (by simp)
                rw [balance, smaller, ite_eq_right (by omega), pairLayer_units]
                simp
  exact ranked trees.length trees rfl

def sourceTree (inputs : List (CNF.Literal α)) : Tree α := balance (inputs.map .leaf)

/-- Balanced source folds preserve all signed input incidences. -/
theorem sourceTree_eval (inputs : List (CNF.Literal α)) (junction : Bounded.Junction)
    (assignment : α → Bool) :
    (sourceTree inputs).eval junction assignment = junction.eval assignment inputs := by
  have leaves : (inputs.map Tree.leaf).flatMap Tree.leaves = inputs := by
    induction inputs with
    | nil => rfl
    | cons head tail inductionHypothesis => simp [Tree.leaves, inductionHypothesis]
  rw [Tree.eval_leaves, sourceTree, balance_leaves, leaves]

/-- The generator omits unary gates; zero arity retains its constant producer. -/
theorem sourceTree_nodes (inputs : List (CNF.Literal α)) :
    (sourceTree inputs).nodeCount = if inputs.length = 0 then 1 else inputs.length - 1 := by
  simp [sourceTree, balance_nodes, Tree.nodeCount, List.map_const', Function.comp_def]

theorem sourceTree_units (inputs : List (CNF.Literal α)) :
    (sourceTree inputs).unitCount = if inputs.length = 0 then 1 else 0 := by
  simp [sourceTree, balance_units, Tree.unitCount, List.map_const', Function.comp_def]

/-- Every internal tree occurrence receives its own value coordinate. -/
def Tree.Values : Tree α → Type
  | .unit => Bool
  | .leaf _ => PUnit
  | .join left right => left.Values × right.Values × Bool

def Tree.output (junction : Bounded.Junction) (original : α → Bool) :
    (tree : Tree α) → tree.Values → Bool
  | .unit, value => value
  | .leaf literal, _ => CNF.literalValue original literal
  | .join _ _, values => values.2.2

def Tree.Equations (junction : Bounded.Junction) (original : α → Bool) :
    (tree : Tree α) → tree.Values → Prop
  | .unit, value => value = junction.eval original []
  | .leaf _, _ => True
  | .join left right, values =>
      values.2.2 = junction.combine (left.output junction original values.1)
        (right.output junction original values.2.1) ∧
      left.Equations junction original values.1 ∧ right.Equations junction original values.2.1

def Tree.canonicalValues (junction : Bounded.Junction) (original : α → Bool) :
    (tree : Tree α) → tree.Values
  | .unit => junction.eval original []
  | .leaf _ => PUnit.unit
  | .join left right =>
      (left.canonicalValues junction original, right.canonicalValues junction original,
        junction.combine (left.eval junction original) (right.eval junction original))

theorem Tree.canonical_output (tree : Tree α) (junction : Bounded.Junction) (original : α → Bool) :
    tree.output junction original (tree.canonicalValues junction original) = tree.eval junction original := by
  cases tree <;> rfl

theorem Tree.canonical_satisfies (tree : Tree α) (junction : Bounded.Junction) (original : α → Bool) :
    tree.Equations junction original (tree.canonicalValues junction original) := by
  induction tree with
  | unit => rfl
  | leaf literal => trivial
  | join left right leftIH rightIH =>
      simp [Equations, canonicalValues, canonical_output, leftIH, rightIH]

theorem Tree.model_eq_canonical (tree : Tree α) (junction : Bounded.Junction) (original : α → Bool)
    (values : tree.Values) (equations : tree.Equations junction original values) :
    values = tree.canonicalValues junction original := by
  induction tree with
  | unit => exact equations
  | leaf literal => cases values; rfl
  | join left right leftIH rightIH =>
      rcases values with ⟨leftValues, rightValues, value⟩
      obtain ⟨defining, leftEquations, rightEquations⟩ := equations
      have leftEquality := leftIH leftValues leftEquations
      have rightEquality := rightIH rightValues rightEquations
      subst leftValues
      subst rightValues
      simp only [canonical_output] at defining
      subst value
      rfl

theorem Tree.unique_extension (tree : Tree α) (junction : Bounded.Junction) (original : α → Bool) :
    ∃! values : tree.Values, tree.Equations junction original values := by
  exact ⟨tree.canonicalValues junction original, tree.canonical_satisfies junction original,
    fun values equations => tree.model_eq_canonical junction original values equations⟩

/-- Balanced source outputs realize exactly the same complete producer equation. -/
theorem source_extension_iff (inputs : List (CNF.Literal α)) (junction : Bounded.Junction)
    (original : α → Bool) (principal : CNF.Literal α) :
    (∃ values : (sourceTree inputs).Values,
      (sourceTree inputs).Equations junction original values ∧
        CNF.literalValue original principal = (sourceTree inputs).output junction original values) ↔
      CNF.literalValue original principal = junction.eval original inputs := by
  constructor
  · rintro ⟨values, equations, principalEquation⟩
    rw [(sourceTree inputs).model_eq_canonical junction original values equations,
      Tree.canonical_output, sourceTree_eval] at principalEquation
    exact principalEquation
  · intro principalEquation
    refine ⟨(sourceTree inputs).canonicalValues junction original,
      (sourceTree inputs).canonical_satisfies junction original, ?_⟩
    simpa [Tree.canonical_output, sourceTree_eval] using principalEquation

/-- Sequential and balanced folds preserve the same fixed original signed producer models. -/
theorem sequential_balanced_extension_iff (inputs : List (CNF.Literal α))
    (junction : Bounded.Junction) (original : α → Bool) (principal : CNF.Literal α) :
    (∃ assignment : Bounded.LocalVariable α (inputs.length - 2) → Bool,
      (∀ slot, assignment (.original slot) = original slot) ∧
        CNF.Satisfies assignment
          (CNF.ofClauses ((Bounded.foldProducers junction inputs principal).flatMap Bounded.Producer.rows))) ↔
    (∃ values : (sourceTree inputs).Values,
      (sourceTree inputs).Equations junction original values ∧
        CNF.literalValue original principal = (sourceTree inputs).output junction original values) := by
  rw [Bounded.fold_extension_iff, source_extension_iff]

def Tree.rowCount : Tree α → ℕ
  | .unit => 1
  | .leaf _ => 0
  | .join left right => left.rowCount + right.rowCount + 3

def Tree.literalCount : Tree α → ℕ
  | .unit => 1
  | .leaf _ => 0
  | .join left right => left.literalCount + right.literalCount + 7

theorem Tree.rowCount_eq (tree : Tree α) :
    tree.rowCount + 2 * tree.unitCount = 3 * tree.nodeCount := by
  induction tree with
  | unit => rfl
  | leaf literal => rfl
  | join left right leftIH rightIH =>
      simp only [rowCount, unitCount, nodeCount]
      omega

theorem Tree.literalCount_eq (tree : Tree α) :
    tree.literalCount + 6 * tree.unitCount = 7 * tree.nodeCount := by
  induction tree with
  | unit => rfl
  | leaf literal => rfl
  | join left right leftIH rightIH =>
      simp only [literalCount, unitCount, nodeCount]
      omega

/-- Source folds allocate no unary block, unlike the retained-alias sequential layout. -/
theorem sourceTree_rows (inputs : List (CNF.Literal α)) :
    (sourceTree inputs).rowCount = if inputs.length = 0 then 1 else 3 * (inputs.length - 1) := by
  have identity := (sourceTree inputs).rowCount_eq
  rw [sourceTree_nodes, sourceTree_units] at identity
  split_ifs at identity ⊢ <;> omega

theorem sourceTree_literals (inputs : List (CNF.Literal α)) :
    (sourceTree inputs).literalCount = if inputs.length = 0 then 1 else 7 * (inputs.length - 1) := by
  have identity := (sourceTree inputs).literalCount_eq
  rw [sourceTree_nodes, sourceTree_units] at identity
  split_ifs at identity ⊢ <;> omega

def binaryBlock (junction : Bounded.Junction) : CNF.Formula (Fin 3) :=
  (junction.gate [(0, true), (1, true)]).block (2, true)

def binaryAssignment (left right output : Bool) (slot : Fin 3) : Bool :=
  if slot = 0 then left else if slot = 1 then right else output

theorem binaryBlock_correct (junction : Bounded.Junction) (left right output : Bool) :
    CNF.Satisfies (binaryAssignment left right output) (binaryBlock junction) ↔
      output = junction.combine left right := by
  rw [binaryBlock, CNF.Gate.block_correct]
  cases junction <;>
    simp [binaryAssignment, Bounded.Junction.gate, Bounded.Junction.combine,
      CNF.literalValue, CNF.Gate.eval]

theorem binaryBlock_row_sizes (junction : Bounded.Junction) :
    (binaryBlock junction).clauses.toList.map List.length = [2, 2, 3] := by
  cases junction <;>
    simp [binaryBlock, Bounded.Junction.gate, CNF.Gate.block, CNF.Gate.clauses, CNF.ofClauses]

/-- Every occurrence satisfies its complete local native block, including both implication directions. -/
def Tree.BlocksSatisfied (junction : Bounded.Junction) (original : α → Bool) :
    (tree : Tree α) → tree.Values → Prop
  | .unit, value =>
      CNF.Satisfies (fun (_ : Fin 1) => value) ((junction.gate []).block (0, true))
  | .leaf _, _ => True
  | .join left right, values =>
      CNF.Satisfies
        (binaryAssignment (left.output junction original values.1)
          (right.output junction original values.2.1) values.2.2) (binaryBlock junction) ∧
      left.BlocksSatisfied junction original values.1 ∧ right.BlocksSatisfied junction original values.2.1

theorem Tree.blocks_iff_equations (tree : Tree α) (junction : Bounded.Junction) (original : α → Bool)
    (values : tree.Values) :
    tree.BlocksSatisfied junction original values ↔ tree.Equations junction original values := by
  induction tree with
  | unit =>
      change Bool at values
      change CNF.Satisfies (fun (_ : Fin 1) => values) ((junction.gate []).block (0, true)) ↔
        values = junction.eval original []
      rw [CNF.Gate.block_correct]
      cases junction <;>
        simp [Bounded.Junction.eval, Bounded.Junction.gate, CNF.literalValue, CNF.Gate.eval]
  | leaf literal => rfl
  | join left right leftIH rightIH =>
      rw [BlocksSatisfied, binaryBlock_correct, Equations, leftIH, rightIH]

theorem Tree.unique_block_extension (tree : Tree α) (junction : Bounded.Junction) (original : α → Bool) :
    ∃! values : tree.Values, tree.BlocksSatisfied junction original values := by
  simpa only [blocks_iff_equations] using tree.unique_extension junction original

end Controller.Native.SourceFold

namespace Controller.Native.SourceSharing

theorem equation_model_physical (parameters : Parameters)
    (assignment : Controller.Native.Variable parameters → Bool)
    (satisfied : CNF.Satisfies assignment parameters.equationFormula) :
    assignment = parameters.physicalAssignment
      (parameters.primaryInput (fun primary => assignment (.primary primary)))
      (assignment (.primary .wire)) := by
  apply parameters.equation_model_unique assignment _ satisfied
    (parameters.physicalAssignment_satisfies_equations _ _)
  intro primary
  cases primary <;> rfl

/-- Source first-bus sharing is justified before the interface units are imposed. -/
theorem first_terms_shared (parameters : Parameters)
    (assignment : Controller.Native.Variable parameters → Bool)
    (satisfied : CNF.Satisfies assignment parameters.equationFormula)
    (channel : Fin parameters.channels) :
    assignment (.internal (.term .healthy parameters.firstBus channel)) =
      assignment (.internal (.term .faulty parameters.firstBus channel)) := by
  rw [equation_model_physical parameters assignment satisfied]
  simp [Parameters.physicalAssignment, Parameters.roleValue, Parameters.selectorRun_first_terms]

theorem first_absents_shared (parameters : Parameters)
    (assignment : Controller.Native.Variable parameters → Bool)
    (satisfied : CNF.Satisfies assignment parameters.equationFormula)
    (channel : Fin parameters.channels) :
    assignment (.internal (.absent .healthy parameters.firstBus channel)) =
      assignment (.internal (.absent .faulty parameters.firstBus channel)) := by
  rw [equation_model_physical parameters assignment satisfied]
  simp [Parameters.physicalAssignment, Parameters.roleValue, Parameters.selectorRun_first_terms]

/-- Source decoder input nodes may reuse their qualifier's signed handle. -/
theorem decoder_input_alias (parameters : Parameters)
    (assignment : Controller.Native.Variable parameters → Bool)
    (satisfied : CNF.Satisfies assignment parameters.equationFormula)
    (side : Side) (node : Fin parameters.decoder.nodeCount) (channel : Fin parameters.channels)
    (inputNode : parameters.decoder.node node = .input channel) :
    assignment (.internal (.decoder side node)) = assignment (.internal (.qualifier side channel)) := by
  have equation := (parameters.equationFormula_iff assignment).mp satisfied (.decoder side node)
  simpa [Parameters.gate, Parameters.decoderGate, inputNode, CNF.Gate.eval,
    Parameters.internal, Parameters.positive, CNF.literalValue] using equation

/-- Once an alias output is identified with its signed input, its complete block is redundant. -/
theorem alias_self_satisfied (input : CNF.Literal α) (assignment : α → Bool) :
    CNF.Satisfies assignment ((CNF.Gate.alias input).block input) :=
  (CNF.Gate.block_correct assignment input (.alias input)).mpr rfl

theorem drop_identified_alias (input : CNF.Literal α) (assignment : α → Bool) (suffix : CNF.Formula α) :
    CNF.Satisfies assignment ((CNF.Gate.alias input).block input ++ suffix) ↔
      CNF.Satisfies assignment suffix := by
  rw [CNF.satisfies_append]
  exact and_iff_right (alias_self_satisfied input assignment)

theorem identified_alias_rows (input : CNF.Literal α) :
    ((CNF.Gate.alias input).block input).clauses.size = 2 := by
  simp [CNF.Gate.block, CNF.Gate.clauses, CNF.ofClauses]

theorem identified_alias_literals (input : CNF.Literal α) :
    Bounded.literalIncidences ((CNF.Gate.alias input).block input) = 4 := by
  simp [Bounded.literalIncidences, CNF.Gate.block, CNF.Gate.clauses, CNF.ofClauses]

theorem raw_first_term_gate (parameters : Parameters) (raw : parameters.layout = .raw)
    (side : Side) (channel : Fin parameters.channels) :
    parameters.gate (.term side parameters.firstBus channel) =
      .and [parameters.enable channel, parameters.request parameters.firstBus channel] := by
  change parameters.termGate side parameters.firstBus channel = _
  unfold Parameters.termGate
  split
  · simp [Parameters.rawTermInputs, Parameters.firstBus, Fin.lt_def]
  · rename_i shared
    cases raw.symm.trans shared

def collapseFirstBus (parameters : Parameters) :
    Controller.Native.Variable parameters → Controller.Native.Variable parameters
  | .internal (.term .faulty bus channel) =>
      if bus = parameters.firstBus then .internal (.term .healthy bus channel)
      else .internal (.term .faulty bus channel)
  | .internal (.absent .faulty bus channel) =>
      if bus = parameters.firstBus then .internal (.absent .healthy bus channel)
      else .internal (.absent .faulty bus channel)
  | slot => slot

/-- The concrete source-sharing map preserves every full named equation model. -/
theorem model_invariant_collapse (parameters : Parameters)
    (assignment : Controller.Native.Variable parameters → Bool)
    (satisfied : CNF.Satisfies assignment parameters.equationFormula) :
    assignment ∘ collapseFirstBus parameters = assignment := by
  funext slot
  cases slot with
  | primary primary => rfl
  | internal role =>
      cases role <;> try rfl
      · rename_i side bus channel
        cases side
        · rfl
        · by_cases first : bus = parameters.firstBus
          · subst bus
            simpa [Function.comp_def, collapseFirstBus] using first_terms_shared parameters assignment satisfied channel
          · simp [collapseFirstBus, first]
      · rename_i side bus channel
        cases side
        · rfl
        · by_cases first : bus = parameters.firstBus
          · subst bus
            simpa [Function.comp_def, collapseFirstBus] using first_absents_shared parameters assignment satisfied channel
          · simp [collapseFirstBus, first]

def firstBusPairFormula (parameters : Parameters) (side : Side) (channel : Fin parameters.channels) :
    CNF.Formula (Controller.Native.Variable parameters) :=
  (CNF.Gate.and [parameters.enable channel, parameters.request parameters.firstBus channel]).block
      (parameters.internal (.term side parameters.firstBus channel)) ++
    (CNF.Gate.not (parameters.internal (.term side parameters.firstBus channel))).block
      (parameters.internal (.absent side parameters.firstBus channel))

/-- The shared pair consists of the actual raw-layout producers for these two roles. -/
theorem raw_firstBusPair (parameters : Parameters) (raw : parameters.layout = .raw)
    (side : Side) (channel : Fin parameters.channels) :
    (parameters.gate (.term side parameters.firstBus channel)).block
        (parameters.internal (.term side parameters.firstBus channel)) ++
      (parameters.gate (.absent side parameters.firstBus channel)).block
        (parameters.internal (.absent side parameters.firstBus channel)) =
      firstBusPairFormula parameters side channel := by
  rw [raw_first_term_gate parameters raw]
  rfl

/-- Identifying shared first-bus slots preserves satisfiability of the full asserted formula. -/
theorem satisfiable_collapse_iff (parameters : Parameters) :
    CNF.Satisfiable (CNF.relabel (collapseFirstBus parameters) parameters.specificationFormula) ↔
      CNF.Satisfiable parameters.specificationFormula := by
  constructor
  · rintro ⟨assignment, satisfied⟩
    exact ⟨assignment ∘ collapseFirstBus parameters,
      (CNF.satisfies_relabel _ _ _).mp satisfied⟩
  · rintro ⟨assignment, satisfied⟩
    refine ⟨assignment, (CNF.satisfies_relabel _ _ _).mpr ?_⟩
    have equations : CNF.Satisfies assignment parameters.equationFormula :=
      (CNF.satisfies_append assignment _ _).mp satisfied |>.1
    rw [model_invariant_collapse parameters assignment equations]
    exact satisfied

/-- The shared first-bus pair maps its complete original rows to the retained healthy pair. -/
theorem collapsed_firstBusPair (parameters : Parameters) (channel : Fin parameters.channels) :
    CNF.relabel (collapseFirstBus parameters) (firstBusPairFormula parameters .faulty channel) =
      firstBusPairFormula parameters .healthy channel := by
  simp [firstBusPairFormula, CNF.relabel, Controller.CNF.OrderedFormula.relabel,
    Controller.CNF.OrderedFormula.Internal.clauses_append, CNF.Gate.block, CNF.Gate.clauses, CNF.ofClauses,
    Controller.CNF.OrderedFormula.Clause.relabel, CNF.negate, Std.Sat.Literal.negate,
    Parameters.internal, Parameters.positive, Parameters.enable, Parameters.request,
    collapseFirstBus]
  rfl

/-- Duplicate mapped first-bus blocks may be removed while keeping the original healthy block. -/
theorem drop_collapsed_firstBusPair (parameters : Parameters) (channel : Fin parameters.channels)
    (assignment : Controller.Native.Variable parameters → Bool)
    (suffix : CNF.Formula (Controller.Native.Variable parameters)) :
    CNF.Satisfies assignment
      (firstBusPairFormula parameters .healthy channel ++
        CNF.relabel (collapseFirstBus parameters) (firstBusPairFormula parameters .faulty channel) ++ suffix) ↔
      CNF.Satisfies assignment (firstBusPairFormula parameters .healthy channel ++ suffix) := by
  rw [collapsed_firstBusPair]
  simp [CNF.satisfies_append]

/-- One source-shared channel removes one duplicate binary AND and one duplicate NOT producer. -/
def firstBusDuplicateRows (parameters : Parameters) : List (CNF.Clause (Controller.Native.Variable parameters)) :=
  (List.finRange parameters.channels).flatMap fun channel =>
    (CNF.Gate.and [parameters.enable channel, parameters.request parameters.firstBus channel]).clauses
      (parameters.internal (.term .faulty parameters.firstBus channel)) ++
    (CNF.Gate.not (parameters.internal (.term .faulty parameters.firstBus channel))).clauses
      (parameters.internal (.absent .faulty parameters.firstBus channel))

theorem firstBusDuplicateRows_length (parameters : Parameters) :
    (firstBusDuplicateRows parameters).length = 5 * parameters.channels := by
  simp [firstBusDuplicateRows, CNF.Gate.clauses, List.map_const', Nat.mul_comm]

private theorem sum_map_flatMap (items : List α) (rows : α → List β) (weight : β → ℕ) :
    ((items.flatMap rows).map weight).sum =
      (items.map fun item => ((rows item).map weight).sum).sum := by
  induction items with
  | nil => simp
  | cons head tail inductionHypothesis => simp [inductionHypothesis]

theorem firstBusDuplicateRows_literals (parameters : Parameters) :
    ((firstBusDuplicateRows parameters).map List.length).sum = 11 * parameters.channels := by
  simp [firstBusDuplicateRows, sum_map_flatMap, CNF.Gate.clauses, List.map_const', Nat.mul_comm]

def retainedRole (parameters : Parameters) : Internal parameters → Bool
  | .term .faulty bus _ | .absent .faulty bus _ => bus != parameters.firstBus
  | _ => true

def mappedRoleBlock (parameters : Parameters) (role : Internal parameters) :
    CNF.Formula (Controller.Native.Variable parameters) :=
  CNF.relabel (collapseFirstBus parameters)
    ((parameters.gate role).block (parameters.internal role))

def retainedEquationFormula (parameters : Parameters) :
    CNF.Formula (Controller.Native.Variable parameters) :=
  CNF.ofClauses ((parameters.roles.filter (retainedRole parameters)).flatMap fun role =>
    (mappedRoleBlock parameters role).clauses.toList)

private theorem retainedEquationFormula_iff (parameters : Parameters)
    (assignment : Controller.Native.Variable parameters → Bool) :
    CNF.Satisfies assignment (retainedEquationFormula parameters) ↔
      ∀ role, retainedRole parameters role = true →
        CNF.Satisfies assignment (mappedRoleBlock parameters role) := by
  simp only [retainedEquationFormula, CNF.satisfies_ofClauses]
  constructor
  · intro satisfied role retained row membership
    exact satisfied row (List.mem_flatMap.mpr
      ⟨role, List.mem_filter.mpr ⟨parameters.mem_roles role, retained⟩,
        by simpa using membership⟩)
  · intro satisfied row membership
    obtain ⟨role, retained, memberBlock⟩ := List.mem_flatMap.mp membership
    exact satisfied role (List.mem_filter.mp retained).2 row (by simpa using memberBlock)

theorem mapped_first_term (parameters : Parameters) (raw : parameters.layout = .raw)
    (channel : Fin parameters.channels) :
    mappedRoleBlock parameters (.term .faulty parameters.firstBus channel) =
      mappedRoleBlock parameters (.term .healthy parameters.firstBus channel) := by
  simp only [mappedRoleBlock, raw_first_term_gate parameters raw]
  simp [CNF.relabel, Controller.CNF.OrderedFormula.relabel, CNF.Gate.block, CNF.Gate.clauses, CNF.ofClauses,
    Controller.CNF.OrderedFormula.Clause.relabel, CNF.negate, Std.Sat.Literal.negate,
    Parameters.internal, Parameters.positive, Parameters.enable, Parameters.request, collapseFirstBus]

theorem mapped_first_absent (parameters : Parameters) (channel : Fin parameters.channels) :
    mappedRoleBlock parameters (.absent .faulty parameters.firstBus channel) =
      mappedRoleBlock parameters (.absent .healthy parameters.firstBus channel) := by
  simp [mappedRoleBlock, Parameters.gate, CNF.relabel, Controller.CNF.OrderedFormula.relabel,
    CNF.Gate.block, CNF.Gate.clauses, CNF.ofClauses, Controller.CNF.OrderedFormula.Clause.relabel,
    CNF.negate, Std.Sat.Literal.negate, Parameters.internal, Parameters.positive, collapseFirstBus]

/-- Every original producer has an explicit retained producer with identical mapped rows. -/
theorem retained_role_cover (parameters : Parameters) (raw : parameters.layout = .raw)
    (role : Internal parameters) :
    ∃ keptRole, retainedRole parameters keptRole = true ∧
      mappedRoleBlock parameters role = mappedRoleBlock parameters keptRole := by
  by_cases keep : retainedRole parameters role = true
  · exact ⟨role, keep, rfl⟩
  · cases role <;> simp [retainedRole] at keep
    · rename_i side bus channel
      cases side <;> simp [retainedRole] at keep
      subst bus
      exact ⟨.term .healthy parameters.firstBus channel, rfl, mapped_first_term parameters raw channel⟩
    · rename_i side bus channel
      cases side <;> simp [retainedRole] at keep
      subst bus
      exact ⟨.absent .healthy parameters.firstBus channel, rfl, mapped_first_absent parameters channel⟩

/-- All original collapsed equation rows are covered by the retained producers. -/
theorem retained_equations_iff (parameters : Parameters) (raw : parameters.layout = .raw)
    (assignment : Controller.Native.Variable parameters → Bool) :
    CNF.Satisfies assignment (retainedEquationFormula parameters) ↔
      CNF.Satisfies assignment (CNF.relabel (collapseFirstBus parameters) parameters.equationFormula) := by
  rw [retainedEquationFormula_iff, CNF.satisfies_relabel, parameters.equationFormula_iff]
  constructor
  · intro retained role
    have localRows : CNF.Satisfies assignment (mappedRoleBlock parameters role) := by
      obtain ⟨keptRole, keep, rows⟩ := retained_role_cover parameters raw role
      rw [rows]
      exact retained keptRole keep
    have equation := (CNF.Gate.block_correct _ _ _).mp
      ((CNF.satisfies_relabel _ _ _).mp localRows)
    simpa [Parameters.internal, Parameters.positive, CNF.literalValue] using equation
  · intro equations role _
    apply (CNF.satisfies_relabel _ _ _).mpr
    apply (CNF.Gate.block_correct _ _ _).mpr
    simpa [Parameters.internal, Parameters.positive, CNF.literalValue] using equations role

def retainedSpecificationFormula (parameters : Parameters) :
    CNF.Formula (Controller.Native.Variable parameters) :=
  retainedEquationFormula parameters ++
    CNF.relabel (collapseFirstBus parameters) parameters.assertionFormula

theorem retained_specification_iff (parameters : Parameters) (raw : parameters.layout = .raw)
    (assignment : Controller.Native.Variable parameters → Bool) :
    CNF.Satisfies assignment (retainedSpecificationFormula parameters) ↔
      CNF.Satisfies assignment
        (CNF.relabel (collapseFirstBus parameters) parameters.specificationFormula) := by
  rw [retainedSpecificationFormula, CNF.satisfies_append, retained_equations_iff parameters raw]
  simp only [CNF.satisfies_relabel, Parameters.specificationFormula, CNF.satisfies_append]

theorem retained_satisfiable_iff (parameters : Parameters) (raw : parameters.layout = .raw) :
    CNF.Satisfiable (retainedSpecificationFormula parameters) ↔
      CNF.Satisfiable parameters.specificationFormula := by
  rw [← satisfiable_collapse_iff]
  exact exists_congr (retained_specification_iff parameters raw)

end Controller.Native.SourceSharing

namespace Controller.Native.SourceObservation

/-- The source `build` observes every flag first, followed by every eligibility qualifier. -/
def oldOutputRoles (parameters : Parameters) (side : Side) : List (Internal parameters) :=
  (List.finRange parameters.buses).map (.flag side) ++
    (List.finRange parameters.channels).map (.qualifier side)

def oldPairs (parameters : Parameters) (sourceSlots : Controller.Native.Variable parameters → Fin base) :
    List (CNF.Literal (Fin base) × CNF.Literal (Fin base)) :=
  ((oldOutputRoles parameters .healthy).zip (oldOutputRoles parameters .faulty)).map fun pair =>
    ((sourceSlots (.internal pair.1), true), (sourceSlots (.internal pair.2), true))

theorem oldPairs_length (parameters : Parameters)
    (sourceSlots : Controller.Native.Variable parameters → Fin base) :
    (oldPairs parameters sourceSlots).length = parameters.buses + parameters.channels := by
  simp [oldPairs, oldOutputRoles]

def gateAt (pairs : List (CNF.Literal (Fin base) × CNF.Literal (Fin base))) (index : ℕ) :
    CNF.Gate (Fin base) :=
  match pairs[index]? with
  | some pair => .xor pair.1 pair.2
  | none => .constant false

def circuit (gates : ℕ → CNF.Gate (Fin base)) :
    (count : ℕ) → CNF.AcyclicCircuit base (base + count)
  | 0 => .roots
  | count + 1 =>
      let previous := circuit gates count
      previous.snoc ((gates count).relabel previous.rootIndex) true

theorem circuit_root_index (gates : ℕ → CNF.Gate (Fin base)) (count : ℕ) (index : Fin base) :
    ((circuit gates count).rootIndex index).val = index.val := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis => exact inductionHypothesis

/-- Source fresh IDs start immediately after all preceding controller-tail variables. -/
def sourceID (slot : Fin count) : ℕ := slot.val + 1

def differenceID (base index : ℕ) : ℕ := base + index + 1

theorem fresh_difference_id (index : ℕ) (slot : Fin base) :
    sourceID slot < differenceID base index := by
  simp only [sourceID, differenceID]
  omega

theorem difference_id_injective (base : ℕ) : Function.Injective (differenceID base) := by
  intro left right equality
  simp only [differenceID] at equality
  omega

def sourceProducer (gates : ℕ → CNF.Gate (Fin base)) (index : ℕ) : Bounded.Producer ℕ :=
  ⟨(differenceID base index, true), (gates index).relabel sourceID⟩

theorem gateAt_in_range (pairs : List (CNF.Literal (Fin base) × CNF.Literal (Fin base)))
    (index : Fin pairs.length) :
    gateAt pairs index.val = .xor pairs[index].1 pairs[index].2 := by
  simp [gateAt]

theorem old_xor_rows (parameters : Parameters)
    (sourceSlots : Controller.Native.Variable parameters → Fin base)
    (index : Fin (oldPairs parameters sourceSlots).length) :
    (sourceProducer (gateAt (oldPairs parameters sourceSlots)) index.val).rows.length = 4 := by
  simp [Bounded.Producer.rows, sourceProducer, gateAt_in_range _ index, CNF.Gate.relabel,
    CNF.Gate.clauses]

theorem old_xor_literals (parameters : Parameters)
    (sourceSlots : Controller.Native.Variable parameters → Fin base)
    (index : Fin (oldPairs parameters sourceSlots).length) :
    ((sourceProducer (gateAt (oldPairs parameters sourceSlots)) index.val).rows.map List.length).sum = 12 := by
  simp [Bounded.Producer.rows, sourceProducer, gateAt_in_range _ index, CNF.Gate.relabel,
    CNF.Gate.clauses]

private theorem relabel_block (map : α → β) (gate : CNF.Gate α) (output : CNF.Literal α) :
    CNF.relabel map (gate.block output) = (gate.relabel map).block (map output.1, output.2) := by
  cases gate <;>
    simp [CNF.relabel, Controller.CNF.OrderedFormula.relabel, CNF.Gate.block, CNF.Gate.clauses,
      CNF.Gate.relabel, CNF.ofClauses, Controller.CNF.OrderedFormula.Clause.relabel,
      CNF.negate, Std.Sat.Literal.negate, List.map_map, Function.comp_def]
  split <;> rfl

private theorem relabel_gate_comp (first : α → β) (second : β → γ) (gate : CNF.Gate α) :
    (gate.relabel first).relabel second = gate.relabel (second ∘ first) := by
  cases gate <;> simp [CNF.Gate.relabel, List.map_map, Function.comp_def]

/-- Each appended circuit gate has the exact fresh source ID and complete source producer rows. -/
theorem circuit_source_step (gates : ℕ → CNF.Gate (Fin base)) (count : ℕ) :
    CNF.relabel sourceID (circuit gates (count + 1)).formula =
      CNF.relabel sourceID (circuit gates count).formula ++
        (sourceProducer gates count).gate.block (sourceProducer gates count).output := by
  change CNF.relabel sourceID
      (CNF.relabel Fin.castSucc (circuit gates count).formula ++
        (((gates count).relabel (circuit gates count).rootIndex).relabel Fin.castSucc).block
          (Fin.last (base + count), true)) = _
  simp only [CNF.relabel, Controller.CNF.OrderedFormula.relabel_append, Controller.CNF.OrderedFormula.relabel_relabel]
  change CNF.relabel (sourceID ∘ Fin.castSucc) (circuit gates count).formula ++
      CNF.relabel sourceID
        ((((gates count).relabel (circuit gates count).rootIndex).relabel Fin.castSucc).block
          (Fin.last (base + count), true)) = _
  rw [relabel_block]
  have roots : sourceID ∘ Fin.castSucc ∘ (circuit gates count).rootIndex = sourceID := by
    funext index
    simp [sourceID, Function.comp_def, circuit_root_index]
  have oldSlots : sourceID ∘ Fin.castSucc = (sourceID : Fin (base + count) → ℕ) := rfl
  simp only [oldSlots]
  simp only [relabel_gate_comp, roots]
  rfl

def sourceFormula (gates : ℕ → CNF.Gate (Fin base)) : ℕ → CNF.Formula ℕ
  | 0 => Controller.CNF.OrderedFormula.empty
  | count + 1 => sourceFormula gates count ++
      (sourceProducer gates count).gate.block (sourceProducer gates count).output

/-- Circuit serialization preserves the source append order, every row, and its literal IDs. -/
theorem circuit_source_formula (gates : ℕ → CNF.Gate (Fin base)) (count : ℕ) :
    CNF.relabel sourceID (circuit gates count).formula = sourceFormula gates count := by
  induction count with
  | zero => simp [circuit, sourceFormula, CNF.AcyclicCircuit.formula, CNF.relabel]
  | succ count inductionHypothesis =>
      rw [circuit_source_step, inductionHypothesis]
      rfl

/-- The unused original observation XORs have one unique extension over every preceding assignment. -/
theorem old_xors_unique_extension (parameters : Parameters)
    (sourceSlots : Controller.Native.Variable parameters → Fin base)
    (assignment : Fin base → Bool) :
    ∃! extended, (circuit (gateAt (oldPairs parameters sourceSlots))
        (oldPairs parameters sourceSlots).length).rootValues extended = assignment ∧
      CNF.Satisfies extended (circuit (gateAt (oldPairs parameters sourceSlots))
        (oldPairs parameters sourceSlots).length).formula := by
  exact CNF.AcyclicCircuit.existsUnique_extension _ assignment

/-- Retaining the source's unused XOR producers neither removes nor duplicates an existing full model. -/
theorem old_xors_preserve_model (parameters : Parameters)
    (sourceSlots : Controller.Native.Variable parameters → Fin base)
    (assignment : Fin base → Bool) (priorFormula : CNF.FiniteFormula base) :
    (∃! extended, (circuit (gateAt (oldPairs parameters sourceSlots))
        (oldPairs parameters sourceSlots).length).rootValues extended = assignment ∧
      CNF.Satisfies extended
        ((circuit (gateAt (oldPairs parameters sourceSlots)) (oldPairs parameters sourceSlots).length).formula ++
          CNF.relabel (circuit (gateAt (oldPairs parameters sourceSlots))
            (oldPairs parameters sourceSlots).length).rootIndex priorFormula)) ↔
      CNF.Satisfies assignment priorFormula := by
  let attached := circuit (gateAt (oldPairs parameters sourceSlots)) (oldPairs parameters sourceSlots).length
  change (∃! extended, attached.rootValues extended = assignment ∧
    CNF.Satisfies extended (attached.formula ++ CNF.relabel attached.rootIndex priorFormula)) ↔ _
  constructor
  · rintro ⟨extended, ⟨roots, satisfied⟩, _⟩
    have prior := (CNF.satisfies_relabel _ _ _).mp ((CNF.satisfies_append _ _ _).mp satisfied).2
    change CNF.Satisfies (attached.rootValues extended) priorFormula at prior
    simpa only [roots] using prior
  · intro prior
    refine ⟨attached.evaluate assignment, ⟨attached.rootValues_evaluate assignment, ?_⟩, ?_⟩
    · apply (CNF.satisfies_append _ _ _).mpr
      refine ⟨attached.evaluate_satisfies assignment, (CNF.satisfies_relabel _ _ _).mpr ?_⟩
      change CNF.Satisfies (attached.rootValues (attached.evaluate assignment)) priorFormula
      rw [attached.rootValues_evaluate]
      exact prior
    · intro extended satisfied
      exact attached.eq_evaluate_of_satisfies assignment extended satisfied.1
        ((CNF.satisfies_append _ _ _).mp satisfied.2).1

end Controller.Native.SourceObservation

namespace Controller.Native.SourceInitialIDs

def rootCoordinates : InterfaceAlias.Root n b ≃ (Fin n ⊕ (Fin n × Fin b)) where
  toFun
    | .enable channel => .inl channel
    | .request bus channel => .inr (channel, bus)
  invFun
    | .inl channel => .enable channel
    | .inr pair => .request pair.2 pair.1
  left_inv root := by cases root <;> rfl
  right_inv coordinate := by cases coordinate <;> rfl

/-- Source roots enumerate requests by channel, then by bus. -/
def rootIndex : InterfaceAlias.Root n b ≃ Fin (n + n * b) :=
  rootCoordinates.trans ((Equiv.sumCongr (Equiv.refl (Fin n)) finProdFinEquiv).trans finSumFinEquiv)

def rootID (root : InterfaceAlias.Root n b) : ℕ := (rootIndex root).val + 1

theorem rootID_enable (channel : Fin n) : rootID (InterfaceAlias.Root.enable (b := b) channel) = channel.val + 1 := by
  rfl

theorem rootID_request (bus : Fin b) (channel : Fin n) :
    rootID (.request bus channel) = n + channel.val * b + bus.val + 1 := by
  simp [rootID, rootIndex, rootCoordinates, finProdFinEquiv, finSumFinEquiv,
    Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

theorem rootID_injective : Function.Injective (rootID (n := n) (b := b)) := by
  intro left right equal
  apply rootIndex.injective
  apply Fin.ext
  simp only [rootID] at equal
  omega

def rootCount (parameters : Parameters) : ℕ := parameters.channels + parameters.channels * parameters.buses

def firstTermID (parameters : Parameters) (channel : Fin parameters.channels) : ℕ :=
  rootCount parameters + channel.val + 1

def firstAbsentID (parameters : Parameters) (channel : Fin parameters.channels) : ℕ :=
  rootCount parameters + parameters.channels + channel.val + 1

/-- These two source arrays are allocated once and are reused by both controller tails. -/
def firstBusSlots (parameters : Parameters) :
    (Side × Bool × Fin parameters.channels) → ℕ
  | (_, false, channel) => firstTermID parameters channel
  | (_, true, channel) => firstAbsentID parameters channel

theorem firstBusSlots_shared (parameters : Parameters) (absent : Bool) (channel : Fin parameters.channels) :
    firstBusSlots parameters (.healthy, absent, channel) =
      firstBusSlots parameters (.faulty, absent, channel) := by
  cases absent <;> rfl

theorem firstTermID_fresh (parameters : Parameters) (channel : Fin parameters.channels)
    (root : InterfaceAlias.Root parameters.channels parameters.buses) :
    rootID root < firstTermID parameters channel := by
  have bound := (rootIndex root).isLt
  simp only [rootID, firstTermID, rootCount]
  omega

theorem firstAbsentID_fresh (parameters : Parameters) (channel earlier : Fin parameters.channels) :
    firstTermID parameters earlier < firstAbsentID parameters channel := by
  have bound := earlier.isLt
  simp only [firstTermID, firstAbsentID]
  omega

theorem firstBusSlots_same_side_injective (parameters : Parameters) (side : Side) :
    Function.Injective (fun pair : Bool × Fin parameters.channels => firstBusSlots parameters (side, pair)) := by
  intro left right equal
  rcases left with ⟨leftKind, leftChannel⟩
  rcases right with ⟨rightKind, rightChannel⟩
  cases leftKind <;> cases rightKind <;>
    simp only [firstBusSlots, firstTermID, firstAbsentID] at equal
  · congr 1
    apply Fin.ext
    omega
  · have := leftChannel.isLt
    omega
  · have := rightChannel.isLt
    omega
  · congr 1
    apply Fin.ext
    omega

end Controller.Native.SourceInitialIDs

namespace Controller.Native.SourceSerialFold

structure Layer where
  handles : List (CNF.Literal ℕ)
  producers : List (Bounded.Producer ℕ)
  nextID : ℕ

/-- The source loop allocates adjacent pairs from left to right and carries a singleton. -/
def pairLayer (junction : Bounded.Junction) (lastID : ℕ) : List (CNF.Literal ℕ) → Layer
  | [] => ⟨[], [], lastID⟩
  | [input] => ⟨[input], [], lastID⟩
  | left :: right :: tail =>
      let rest := pairLayer junction (lastID + 1) tail
      ⟨(lastID + 1, true) :: rest.handles,
        ⟨(lastID + 1, true), junction.gate [left, right]⟩ :: rest.producers, rest.nextID⟩

theorem pairLayer_length (junction : Bounded.Junction) (lastID : ℕ)
    (inputs : List (CNF.Literal ℕ)) :
    (pairLayer junction lastID inputs).handles.length = (inputs.length + 1) / 2 := by
  induction inputs using List.twoStepInduction generalizing lastID with
  | nil => simp [pairLayer]
  | singleton input => simp [pairLayer]
  | cons_cons left right tail inductionHypothesis _ =>
      simp only [pairLayer, List.length_cons, inductionHypothesis]
      omega

theorem pairLayer_producers (junction : Bounded.Junction) (lastID : ℕ)
    (inputs : List (CNF.Literal ℕ)) :
    (pairLayer junction lastID inputs).producers.length = inputs.length / 2 := by
  induction inputs using List.twoStepInduction generalizing lastID with
  | nil => simp [pairLayer]
  | singleton input => simp [pairLayer]
  | cons_cons left right tail inductionHypothesis _ =>
      simp only [pairLayer, List.length_cons, inductionHypothesis]
      omega

theorem pairLayer_nextID (junction : Bounded.Junction) (lastID : ℕ)
    (inputs : List (CNF.Literal ℕ)) :
    (pairLayer junction lastID inputs).nextID = lastID + inputs.length / 2 := by
  induction inputs using List.twoStepInduction generalizing lastID with
  | nil => simp [pairLayer]
  | singleton input => simp [pairLayer]
  | cons_cons left right tail inductionHypothesis _ =>
      simp only [pairLayer, List.length_cons, inductionHypothesis]
      omega

structure Result where
  output : CNF.Literal ℕ
  producers : List (Bounded.Producer ℕ)
  nextID : ℕ

/-- This is the source balanced fold, including its empty constant and omitted unary gate. -/
def allocate (junction : Bounded.Junction) (lastID : ℕ) (inputs : List (CNF.Literal ℕ)) : Result :=
  match inputs with
  | [] => ⟨(lastID + 1, true), [⟨(lastID + 1, true), junction.gate []⟩], lastID + 1⟩
  | [input] => ⟨input, [], lastID⟩
  | left :: right :: tail =>
      let layer := pairLayer junction lastID (left :: right :: tail)
      let rest := allocate junction layer.nextID layer.handles
      ⟨rest.output, layer.producers ++ rest.producers, rest.nextID⟩
termination_by inputs.length
decreasing_by
  rw [pairLayer_length]
  simp_all only [List.length_cons]
  omega

def formula (result : Result) : CNF.Formula ℕ :=
  CNF.ofClauses (result.producers.flatMap Bounded.Producer.rows)

/-- The retained old detected tree starts after the original observation XOR IDs. -/
def oldDetected (parameters : Parameters) (lastTailID : ℕ) : Result :=
  allocate .disjunction (lastTailID + parameters.buses + parameters.channels)
    ((List.range (parameters.buses + parameters.channels)).map fun index =>
      (SourceObservation.differenceID lastTailID index, true))

theorem allocate_empty (junction : Bounded.Junction) (lastID : ℕ) :
    allocate junction lastID [] =
      ⟨(lastID + 1, true), [⟨(lastID + 1, true), junction.gate []⟩], lastID + 1⟩ := by
  rw [allocate]

theorem allocate_unary (junction : Bounded.Junction) (lastID : ℕ) (input : CNF.Literal ℕ) :
    allocate junction lastID [input] = ⟨input, [], lastID⟩ := by
  rw [allocate]

def Equations (assignment : ℕ → Bool) (producers : List (Bounded.Producer ℕ)) : Prop :=
  ∀ producer ∈ producers, CNF.literalValue assignment producer.output = producer.gate.eval assignment

def HandlesBounded (lastID : ℕ) (inputs : List (CNF.Literal ℕ)) : Prop :=
  ∀ input ∈ inputs, 0 < input.1 ∧ input.1 ≤ lastID

/-- A source producer allocates exactly the next ID and reads only existing positive IDs. -/
inductive Ordered : ℕ → List (Bounded.Producer ℕ) → ℕ → Prop where
  | nil (lastID : ℕ) : Ordered lastID [] lastID
  | cons (bounded : HandlesBounded lastID gate.inputs)
      (rest : Ordered (lastID + 1) producers nextID) :
      Ordered lastID (⟨(lastID + 1, true), gate⟩ :: producers) nextID

theorem Ordered.monotone {lastID nextID : ℕ} {producers : List (Bounded.Producer ℕ)}
    (ordered : Ordered lastID producers nextID) : lastID ≤ nextID := by
  induction ordered with
  | nil => omega
  | cons _ _ inductionHypothesis => omega

theorem Ordered.append {firstID middleID lastID : ℕ}
    {first second : List (Bounded.Producer ℕ)}
    (left : Ordered firstID first middleID) (right : Ordered middleID second lastID) :
    Ordered firstID (first ++ second) lastID := by
  induction left with
  | nil => exact right
  | cons bounded rest inductionHypothesis => exact .cons bounded (inductionHypothesis right)

theorem pairLayer_ordered (junction : Bounded.Junction) (lastID : ℕ)
    (inputs : List (CNF.Literal ℕ)) (bounded : HandlesBounded lastID inputs) :
    Ordered lastID (pairLayer junction lastID inputs).producers (pairLayer junction lastID inputs).nextID ∧
      HandlesBounded (pairLayer junction lastID inputs).nextID (pairLayer junction lastID inputs).handles := by
  induction inputs using List.twoStepInduction generalizing lastID with
  | nil => exact ⟨.nil lastID, by simp [pairLayer, HandlesBounded]⟩
  | singleton input => exact ⟨.nil lastID, bounded⟩
  | cons_cons left right tail inductionHypothesis _ =>
      have tailBounded : HandlesBounded (lastID + 1) tail := by
        intro input membership
        have prior := bounded input (by simp [membership])
        exact ⟨prior.1, by omega⟩
      obtain ⟨ordered, outputs⟩ := inductionHypothesis (lastID + 1) tailBounded
      have localBounded : HandlesBounded lastID (junction.gate [left, right]).inputs := by
        cases junction <;> simpa [Bounded.Junction.gate, CNF.Gate.inputs, HandlesBounded] using
          (show HandlesBounded lastID [left, right] from fun input membership =>
            bounded input (by simp only [List.mem_cons] at membership ⊢; tauto))
      refine ⟨.cons localBounded ordered, ?_⟩
      intro input membership
      simp only [pairLayer, List.mem_cons] at membership
      rcases membership with rfl | membership
      · exact ⟨by omega, ordered.monotone⟩
      · exact outputs input membership

theorem pairLayer_eval (junction : Bounded.Junction) (lastID : ℕ)
    (inputs : List (CNF.Literal ℕ)) (assignment : ℕ → Bool)
    (equations : Equations assignment (pairLayer junction lastID inputs).producers) :
    junction.eval assignment (pairLayer junction lastID inputs).handles = junction.eval assignment inputs := by
  induction inputs using List.twoStepInduction generalizing lastID with
  | nil => rfl
  | singleton input => rfl
  | cons_cons left right tail inductionHypothesis _ =>
      have first := equations ⟨(lastID + 1, true), junction.gate [left, right]⟩ (by simp [pairLayer])
      have restEquations : Equations assignment (pairLayer junction (lastID + 1) tail).producers := by
        intro producer membership
        exact equations producer (by simp [pairLayer, membership])
      have rest := inductionHypothesis (lastID + 1) restEquations
      cases junction <;>
        simp only [Bounded.Junction.eval, Bounded.Junction.gate, pairLayer, CNF.Gate.eval,
          List.all_cons, List.any_cons, List.all_nil, List.any_nil, Bool.and_true, Bool.or_false] at first rest ⊢
      · rw [first, rest]
        simp [Bool.and_assoc]
      · rw [first, rest]
        simp [Bool.or_assoc]

theorem allocate_eval (junction : Bounded.Junction) (lastID : ℕ)
    (inputs : List (CNF.Literal ℕ)) (assignment : ℕ → Bool)
    (equations : Equations assignment (allocate junction lastID inputs).producers) :
    CNF.literalValue assignment (allocate junction lastID inputs).output = junction.eval assignment inputs := by
  have ranked : ∀ size, ∀ lastID inputs, inputs.length = size →
      Equations assignment (allocate junction lastID inputs).producers →
      CNF.literalValue assignment (allocate junction lastID inputs).output = junction.eval assignment inputs := by
    intro size
    induction size using Nat.strong_induction_on with
    | h size inductionHypothesis =>
        intro lastID inputs inputSize equations
        cases inputs with
        | nil =>
            have first := equations ⟨(lastID + 1, true), junction.gate []⟩ (by simp [allocate])
            simpa [allocate, Bounded.Junction.eval] using first
        | cons left tail =>
            cases tail with
            | nil => cases junction <;> simp [allocate, Bounded.Junction.eval, Bounded.Junction.gate, CNF.Gate.eval]
            | cons right rest =>
                let layer := pairLayer junction lastID (left :: right :: rest)
                have layerEquations : Equations assignment layer.producers := by
                  intro producer membership
                  exact equations producer (by simp [allocate, layer, membership])
                have restEquations : Equations assignment (allocate junction layer.nextID layer.handles).producers := by
                  intro producer membership
                  exact equations producer (by simp [allocate, layer, membership])
                have shorter : layer.handles.length < size := by
                  dsimp [layer]
                  rw [pairLayer_length]
                  simp only [List.length_cons]
                  simp only [List.length_cons] at inputSize
                  omega
                have result := inductionHypothesis layer.handles.length shorter layer.nextID layer.handles
                  rfl restEquations
                rw [allocate]
                change CNF.literalValue assignment (allocate junction layer.nextID layer.handles).output = _
                exact result.trans (pairLayer_eval junction lastID _ assignment layerEquations)
  exact ranked inputs.length lastID inputs rfl equations

theorem allocate_ordered (junction : Bounded.Junction) (lastID : ℕ)
    (inputs : List (CNF.Literal ℕ)) (bounded : HandlesBounded lastID inputs) :
    Ordered lastID (allocate junction lastID inputs).producers (allocate junction lastID inputs).nextID ∧
      HandlesBounded (allocate junction lastID inputs).nextID [(allocate junction lastID inputs).output] := by
  have ranked : ∀ size, ∀ lastID inputs, inputs.length = size → HandlesBounded lastID inputs →
      Ordered lastID (allocate junction lastID inputs).producers (allocate junction lastID inputs).nextID ∧
        HandlesBounded (allocate junction lastID inputs).nextID [(allocate junction lastID inputs).output] := by
    intro size
    induction size using Nat.strong_induction_on with
    | h size inductionHypothesis =>
        intro lastID inputs inputSize bounded
        cases inputs with
        | nil =>
            rw [allocate]
            refine ⟨.cons ?_ (.nil (lastID + 1)), ?_⟩
            · cases junction <;> simp [HandlesBounded, Bounded.Junction.gate, CNF.Gate.inputs]
            · simp [HandlesBounded]
        | cons left tail =>
            cases tail with
            | nil => simpa [allocate] using And.intro (Ordered.nil lastID) bounded
            | cons right rest =>
                let layer := pairLayer junction lastID (left :: right :: rest)
                obtain ⟨layerOrder, layerBounded⟩ := pairLayer_ordered junction lastID _ bounded
                have shorter : layer.handles.length < size := by
                  dsimp [layer]
                  rw [pairLayer_length]
                  simp only [List.length_cons]
                  simp only [List.length_cons] at inputSize
                  omega
                obtain ⟨restOrder, restBounded⟩ := inductionHypothesis _ shorter layer.nextID layer.handles rfl layerBounded
                rw [allocate]
                exact ⟨layerOrder.append restOrder, restBounded⟩
  exact ranked inputs.length lastID inputs rfl bounded

theorem Ordered.count {lastID nextID : ℕ} {producers : List (Bounded.Producer ℕ)}
    (ordered : Ordered lastID producers nextID) : nextID = lastID + producers.length := by
  induction ordered with
  | nil => simp
  | cons _ _ inductionHypothesis => simp only [List.length_cons]; omega

theorem allocate_producers (junction : Bounded.Junction) (lastID : ℕ)
    (inputs : List (CNF.Literal ℕ)) :
    (allocate junction lastID inputs).producers.length =
      if inputs.length = 0 then 1 else inputs.length - 1 := by
  have ranked : ∀ size, ∀ lastID inputs, inputs.length = size →
      (allocate junction lastID inputs).producers.length =
        if inputs.length = 0 then 1 else inputs.length - 1 := by
    intro size
    induction size using Nat.strong_induction_on with
    | h size inductionHypothesis =>
        intro lastID inputs inputSize
        cases inputs with
        | nil => simp [allocate]
        | cons left tail =>
            cases tail with
            | nil => simp [allocate]
            | cons right rest =>
                let layer := pairLayer junction lastID (left :: right :: rest)
                have length := pairLayer_length junction lastID (left :: right :: rest)
                have producerLength := pairLayer_producers junction lastID (left :: right :: rest)
                have positive : 0 < layer.handles.length := by
                  dsimp [layer]
                  rw [length]
                  simp only [List.length_cons]
                  omega
                have shorter : layer.handles.length < size := by
                  dsimp [layer]
                  rw [length]
                  simp only [List.length_cons]
                  simp only [List.length_cons] at inputSize
                  omega
                have smaller := inductionHypothesis _ shorter layer.nextID layer.handles rfl
                simp only [ite_eq_right (Nat.ne_of_gt positive)] at smaller
                rw [allocate]
                simp only [List.length_append]
                change layer.producers.length + (allocate junction layer.nextID layer.handles).producers.length = _
                have layerLength : layer.handles.length = ((left :: right :: rest).length + 1) / 2 := length
                have layerProducerLength : layer.producers.length = (left :: right :: rest).length / 2 := producerLength
                rw [smaller, layerLength, layerProducerLength, ite_eq_right (by simp)]
                simp only [List.length_cons]
                omega
  exact ranked inputs.length lastID inputs rfl

theorem oldDetected_producers (parameters : Parameters) (lastTailID : ℕ) :
    (oldDetected parameters lastTailID).producers.length = parameters.buses + parameters.channels - 1 := by
  rw [oldDetected, allocate_producers]
  simp only [List.length_map, List.length_range]
  rw [ite_eq_right (by have := parameters.positiveBuses; omega)]

def boundedIndex (positive : 0 < lastID) (source : ℕ) : Fin lastID :=
  if valid : 0 < source ∧ source ≤ lastID then ⟨source - 1, by omega⟩ else ⟨0, positive⟩

theorem boundedIndex_sourceID (positive : 0 < lastID) (source : ℕ)
    (valid : 0 < source ∧ source ≤ lastID) :
    SourceObservation.sourceID (boundedIndex positive source) = source := by
  simp [boundedIndex, valid, SourceObservation.sourceID]
  omega

def boundedGate (positive : 0 < lastID) (gate : CNF.Gate ℕ) : CNF.Gate (Fin lastID) :=
  gate.relabel (boundedIndex positive)

private theorem gate_relabel_fixed (map : α → α) (gate : CNF.Gate α)
    (fixed : ∀ literal ∈ gate.inputs, map literal.1 = literal.1) : gate.relabel map = gate := by
  have mapList : ∀ inputs : List (CNF.Literal α),
      (∀ literal ∈ inputs, map literal.1 = literal.1) →
      inputs.map (fun literal => (map literal.1, literal.2)) = inputs := by
    intro inputs fixed
    induction inputs with
    | nil => rfl
    | cons head tail inductionHypothesis =>
        simp only [List.map_cons]
        rw [fixed head (by simp), inductionHypothesis (fun literal membership => fixed literal (by simp [membership]))]
  cases gate with
  | and inputs => exact congrArg CNF.Gate.and (mapList inputs fixed)
  | or inputs => exact congrArg CNF.Gate.or (mapList inputs fixed)
  | xor left right =>
      simp [CNF.Gate.relabel, fixed left (by simp [CNF.Gate.inputs]), fixed right (by simp [CNF.Gate.inputs])]
  | «alias» input => simp [CNF.Gate.relabel, fixed input (by simp [CNF.Gate.inputs])]
  | not input => simp [CNF.Gate.relabel, fixed input (by simp [CNF.Gate.inputs])]
  | constant value => rfl

theorem boundedGate_source (positive : 0 < lastID) (gate : CNF.Gate ℕ)
    (bounded : HandlesBounded lastID gate.inputs) :
    (boundedGate positive gate).relabel SourceObservation.sourceID = gate := by
  have composition : (boundedGate positive gate).relabel SourceObservation.sourceID =
      gate.relabel (SourceObservation.sourceID ∘ boundedIndex positive) := by
    cases gate <;> simp [boundedGate, CNF.Gate.relabel, List.map_map, Function.comp_def]
  rw [composition]
  exact gate_relabel_fixed _ gate (fun literal membership => boundedIndex_sourceID positive literal.1 (bounded literal membership))

/-- The executable attachment uses precisely the source producer order. -/
def attach (positive : 0 < lastID) (previous : CNF.AcyclicCircuit roots lastID) :
    (producers : List (Bounded.Producer ℕ)) → CNF.AcyclicCircuit roots (lastID + producers.length)
  | [] => previous
  | producer :: tail => by
      have attached := attach (by omega)
        (previous.snoc (boundedGate positive producer.gate) true) tail
      convert attached using 1 <;> simp [List.length_cons, Nat.add_assoc, Nat.add_comm]

theorem allocated_unique_extension (junction : Bounded.Junction) (lastID : ℕ)
    (positive : 0 < lastID) (inputs : List (CNF.Literal ℕ))
    (assignment : Fin lastID → Bool) :
    ∃! extended,
      (attach positive (.roots : CNF.AcyclicCircuit lastID lastID)
        (allocate junction lastID inputs).producers).rootValues extended = assignment ∧
      CNF.Satisfies extended (attach positive (.roots : CNF.AcyclicCircuit lastID lastID)
        (allocate junction lastID inputs).producers).formula := by
  exact CNF.AcyclicCircuit.existsUnique_extension _ assignment

theorem allocated_preserve_model (junction : Bounded.Junction) (lastID : ℕ)
    (positive : 0 < lastID) (inputs : List (CNF.Literal ℕ))
    (assignment : Fin lastID → Bool) (priorFormula : CNF.FiniteFormula lastID) :
    (∃! extended,
      (attach positive (.roots : CNF.AcyclicCircuit lastID lastID)
        (allocate junction lastID inputs).producers).rootValues extended = assignment ∧
      CNF.Satisfies extended
        ((attach positive (.roots : CNF.AcyclicCircuit lastID lastID)
          (allocate junction lastID inputs).producers).formula ++
          CNF.relabel (attach positive (.roots : CNF.AcyclicCircuit lastID lastID)
            (allocate junction lastID inputs).producers).rootIndex priorFormula)) ↔
      CNF.Satisfies assignment priorFormula := by
  let attached := attach positive (.roots : CNF.AcyclicCircuit lastID lastID)
    (allocate junction lastID inputs).producers
  change (∃! extended, attached.rootValues extended = assignment ∧
    CNF.Satisfies extended (attached.formula ++ CNF.relabel attached.rootIndex priorFormula)) ↔ _
  constructor
  · rintro ⟨extended, ⟨roots, satisfied⟩, _⟩
    have prior := (CNF.satisfies_relabel _ _ _).mp ((CNF.satisfies_append _ _ _).mp satisfied).2
    change CNF.Satisfies (attached.rootValues extended) priorFormula at prior
    simpa only [roots] using prior
  · intro prior
    refine ⟨attached.evaluate assignment, ⟨attached.rootValues_evaluate assignment, ?_⟩, ?_⟩
    · apply (CNF.satisfies_append _ _ _).mpr
      refine ⟨attached.evaluate_satisfies assignment, (CNF.satisfies_relabel _ _ _).mpr ?_⟩
      change CNF.Satisfies (attached.rootValues (attached.evaluate assignment)) priorFormula
      rw [attached.rootValues_evaluate]
      exact prior
    · intro extended satisfied
      exact attached.eq_evaluate_of_satisfies assignment extended satisfied.1
        ((CNF.satisfies_append _ _ _).mp satisfied.2).1

structure State (roots : ℕ) where
  count : ℕ
  positive : 0 < count
  circuit : CNF.AcyclicCircuit roots count

def State.step (state : State roots) (producer : Bounded.Producer ℕ) : State roots :=
  ⟨state.count + 1, by have := state.positive; omega,
    state.circuit.snoc (boundedGate state.positive producer.gate) true⟩

def State.execute (state : State roots) (producers : List (Bounded.Producer ℕ)) : State roots :=
  producers.foldl State.step state

private theorem relabel_block (map : α → β) (gate : CNF.Gate α) (output : CNF.Literal α) :
    CNF.relabel map (gate.block output) = (gate.relabel map).block (map output.1, output.2) := by
  cases gate <;>
    simp [CNF.relabel, Controller.CNF.OrderedFormula.relabel, CNF.Gate.block, CNF.Gate.clauses,
      CNF.Gate.relabel, CNF.ofClauses, Controller.CNF.OrderedFormula.Clause.relabel,
      CNF.negate, Std.Sat.Literal.negate, List.map_map, Function.comp_def]
  split <;> rfl

private theorem relabel_gate_comp (first : α → β) (second : β → γ) (gate : CNF.Gate α) :
    (gate.relabel first).relabel second = gate.relabel (second ∘ first) := by
  cases gate <;> simp [CNF.Gate.relabel, List.map_map, Function.comp_def]

theorem State.source_step (state : State roots) (gate : CNF.Gate ℕ)
    (bounded : HandlesBounded state.count gate.inputs) :
    CNF.relabel SourceObservation.sourceID
      (state.step ⟨(state.count + 1, true), gate⟩).circuit.formula =
      CNF.relabel SourceObservation.sourceID state.circuit.formula ++ gate.block (state.count + 1, true) := by
  change CNF.relabel SourceObservation.sourceID
      (CNF.relabel Fin.castSucc state.circuit.formula ++
        ((boundedGate state.positive gate).relabel Fin.castSucc).block (Fin.last state.count, true)) = _
  simp only [CNF.relabel, Controller.CNF.OrderedFormula.relabel_append, Controller.CNF.OrderedFormula.relabel_relabel]
  change CNF.relabel (SourceObservation.sourceID ∘ Fin.castSucc) state.circuit.formula ++
      CNF.relabel SourceObservation.sourceID
        (((boundedGate state.positive gate).relabel Fin.castSucc).block (Fin.last state.count, true)) = _
  rw [relabel_block, relabel_gate_comp]
  change CNF.relabel SourceObservation.sourceID state.circuit.formula ++
      ((boundedGate state.positive gate).relabel SourceObservation.sourceID).block
        (state.count + 1, true) = _
  rw [boundedGate_source state.positive gate bounded]

theorem State.source_rows (state : State roots) (producers : List (Bounded.Producer ℕ))
    (ordered : Ordered state.count producers nextID) :
    CNF.relabel SourceObservation.sourceID (state.execute producers).circuit.formula =
      CNF.relabel SourceObservation.sourceID state.circuit.formula ++
        CNF.ofClauses (producers.flatMap Bounded.Producer.rows) := by
  induction producers generalizing state nextID with
  | nil => simp [State.execute, CNF.ofClauses, CNF.relabel, Controller.CNF.OrderedFormula.Internal.ext_iff,
      Controller.CNF.OrderedFormula.Internal.clauses_append]
  | cons producer tail inductionHypothesis =>
      cases ordered with
      | cons bounded rest =>
          change CNF.relabel SourceObservation.sourceID
            ((state.step _).execute tail).circuit.formula = _
          rw [inductionHypothesis _ rest, State.source_step state _ bounded]
          simp [List.flatMap_cons, Bounded.Producer.rows, CNF.Gate.block, CNF.ofClauses,
            Controller.CNF.OrderedFormula.Internal.ext_iff, Controller.CNF.OrderedFormula.Internal.clauses_append, Array.append_assoc]

theorem allocated_source_rows (junction : Bounded.Junction) (lastID : ℕ)
    (positive : 0 < lastID) (inputs : List (CNF.Literal ℕ))
    (bounded : HandlesBounded lastID inputs) :
    CNF.relabel SourceObservation.sourceID
      ((State.mk lastID positive (.roots : CNF.AcyclicCircuit lastID lastID)).execute
        (allocate junction lastID inputs).producers).circuit.formula = formula (allocate junction lastID inputs) := by
  rw [State.source_rows _ _ (allocate_ordered junction lastID inputs bounded).1]
  simp [formula, CNF.relabel, CNF.AcyclicCircuit.formula, Controller.CNF.OrderedFormula.Internal.ext_iff,
    Controller.CNF.OrderedFormula.Internal.clauses_append, Controller.CNF.OrderedFormula.empty, Controller.CNF.OrderedFormula.relabel]

def oldDifferenceInputs (parameters : Parameters) (lastTailID : ℕ) : List (CNF.Literal ℕ) :=
  (List.range (parameters.buses + parameters.channels)).map fun index =>
    (SourceObservation.differenceID lastTailID index, true)

theorem oldDifferenceInputs_bounded (parameters : Parameters) (lastTailID : ℕ) :
    HandlesBounded (lastTailID + parameters.buses + parameters.channels)
      (oldDifferenceInputs parameters lastTailID) := by
  intro input membership
  obtain ⟨index, memberRange, rfl⟩ := List.mem_map.mp membership
  have bound := List.mem_range.mp memberRange
  simp only [SourceObservation.differenceID]
  constructor <;> omega

def oldDetectedState (parameters : Parameters) (lastTailID : ℕ) :
    State (lastTailID + parameters.buses + parameters.channels) :=
  (State.mk (lastTailID + parameters.buses + parameters.channels)
    (by have := parameters.positiveBuses; omega) .roots).execute
      (oldDetected parameters lastTailID).producers

/-- Every retained old detected-tree row is the complete source block at its allocated ID. -/
theorem oldDetected_source_rows (parameters : Parameters) (lastTailID : ℕ) :
    CNF.relabel SourceObservation.sourceID (oldDetectedState parameters lastTailID).circuit.formula =
      formula (oldDetected parameters lastTailID) := by
  exact allocated_source_rows .disjunction _ _ _ (oldDifferenceInputs_bounded parameters lastTailID)

theorem oldDetected_unique_extension (parameters : Parameters) (lastTailID : ℕ)
    (assignment : Fin (lastTailID + parameters.buses + parameters.channels) → Bool) :
    ∃! extended, (oldDetectedState parameters lastTailID).circuit.rootValues extended = assignment ∧
      CNF.Satisfies extended (oldDetectedState parameters lastTailID).circuit.formula := by
  exact CNF.AcyclicCircuit.existsUnique_extension _ assignment

theorem oldDetected_preserve_model (parameters : Parameters) (lastTailID : ℕ)
    (assignment : Fin (lastTailID + parameters.buses + parameters.channels) → Bool)
    (priorFormula : CNF.FiniteFormula (lastTailID + parameters.buses + parameters.channels)) :
    (∃! extended, (oldDetectedState parameters lastTailID).circuit.rootValues extended = assignment ∧
      CNF.Satisfies extended ((oldDetectedState parameters lastTailID).circuit.formula ++
        CNF.relabel (oldDetectedState parameters lastTailID).circuit.rootIndex priorFormula)) ↔
      CNF.Satisfies assignment priorFormula := by
  let attached := (oldDetectedState parameters lastTailID).circuit
  change (∃! extended, attached.rootValues extended = assignment ∧
    CNF.Satisfies extended (attached.formula ++ CNF.relabel attached.rootIndex priorFormula)) ↔ _
  constructor
  · rintro ⟨extended, ⟨roots, satisfied⟩, _⟩
    have prior := (CNF.satisfies_relabel _ _ _).mp ((CNF.satisfies_append _ _ _).mp satisfied).2
    change CNF.Satisfies (attached.rootValues extended) priorFormula at prior
    simpa only [roots] using prior
  · intro prior
    refine ⟨attached.evaluate assignment, ⟨attached.rootValues_evaluate assignment, ?_⟩, ?_⟩
    · apply (CNF.satisfies_append _ _ _).mpr
      refine ⟨attached.evaluate_satisfies assignment, (CNF.satisfies_relabel _ _ _).mpr ?_⟩
      change CNF.Satisfies (attached.rootValues (attached.evaluate assignment)) priorFormula
      rw [attached.rootValues_evaluate]
      exact prior
    · intro extended satisfied
      exact attached.eq_evaluate_of_satisfies assignment extended satisfied.1
        ((CNF.satisfies_append _ _ _).mp satisfied.2).1

def oldXorState (parameters : Parameters)
    (sourceSlots : Controller.Native.Variable parameters → Fin base) : State base where
  count := base + (SourceObservation.oldPairs parameters sourceSlots).length
  positive := by rw [SourceObservation.oldPairs_length]; have := parameters.positiveBuses; omega
  circuit := SourceObservation.circuit
    (SourceObservation.gateAt (SourceObservation.oldPairs parameters sourceSlots))
    (SourceObservation.oldPairs parameters sourceSlots).length

/-- Both retained observation families are appended to the same preceding source circuit universe. -/
def combinedOldState (parameters : Parameters)
    (sourceSlots : Controller.Native.Variable parameters → Fin base) : State base :=
  (oldXorState parameters sourceSlots).execute (oldDetected parameters base).producers

theorem combined_old_source_rows (parameters : Parameters)
    (sourceSlots : Controller.Native.Variable parameters → Fin base) :
    CNF.relabel SourceObservation.sourceID (combinedOldState parameters sourceSlots).circuit.formula =
      SourceObservation.sourceFormula
          (SourceObservation.gateAt (SourceObservation.oldPairs parameters sourceSlots))
          (SourceObservation.oldPairs parameters sourceSlots).length ++
        formula (oldDetected parameters base) := by
  have ordered : Ordered (oldXorState parameters sourceSlots).count
      (oldDetected parameters base).producers (oldDetected parameters base).nextID := by
    simpa [oldXorState, SourceObservation.oldPairs_length, oldDetected, oldDifferenceInputs, Nat.add_assoc] using
      (allocate_ordered .disjunction (base + parameters.buses + parameters.channels)
        (oldDifferenceInputs parameters base) (oldDifferenceInputs_bounded parameters base)).1
  rw [combinedOldState, State.source_rows _ _ ordered]
  change CNF.relabel SourceObservation.sourceID
      (SourceObservation.circuit
        (SourceObservation.gateAt (SourceObservation.oldPairs parameters sourceSlots))
        (SourceObservation.oldPairs parameters sourceSlots).length).formula ++
      CNF.ofClauses ((oldDetected parameters base).producers.flatMap Bounded.Producer.rows) = _
  rw [SourceObservation.circuit_source_formula]
  rfl

theorem combined_old_unique_extension (parameters : Parameters)
    (sourceSlots : Controller.Native.Variable parameters → Fin base) (assignment : Fin base → Bool) :
    ∃! extended, (combinedOldState parameters sourceSlots).circuit.rootValues extended = assignment ∧
      CNF.Satisfies extended (combinedOldState parameters sourceSlots).circuit.formula := by
  exact CNF.AcyclicCircuit.existsUnique_extension _ assignment

theorem combined_old_preserve_model (parameters : Parameters)
    (sourceSlots : Controller.Native.Variable parameters → Fin base)
    (assignment : Fin base → Bool) (priorFormula : CNF.FiniteFormula base) :
    (∃! extended, (combinedOldState parameters sourceSlots).circuit.rootValues extended = assignment ∧
      CNF.Satisfies extended ((combinedOldState parameters sourceSlots).circuit.formula ++
        CNF.relabel (combinedOldState parameters sourceSlots).circuit.rootIndex priorFormula)) ↔
      CNF.Satisfies assignment priorFormula := by
  let attached := (combinedOldState parameters sourceSlots).circuit
  change (∃! extended, attached.rootValues extended = assignment ∧
    CNF.Satisfies extended (attached.formula ++ CNF.relabel attached.rootIndex priorFormula)) ↔ _
  constructor
  · rintro ⟨extended, ⟨roots, satisfied⟩, _⟩
    have prior := (CNF.satisfies_relabel _ _ _).mp ((CNF.satisfies_append _ _ _).mp satisfied).2
    change CNF.Satisfies (attached.rootValues extended) priorFormula at prior
    simpa only [roots] using prior
  · intro prior
    refine ⟨attached.evaluate assignment, ⟨attached.rootValues_evaluate assignment, ?_⟩, ?_⟩
    · apply (CNF.satisfies_append _ _ _).mpr
      refine ⟨attached.evaluate_satisfies assignment, (CNF.satisfies_relabel _ _ _).mpr ?_⟩
      change CNF.Satisfies (attached.rootValues (attached.evaluate assignment)) priorFormula
      rw [attached.rootValues_evaluate]
      exact prior
    · intro extended satisfied
      exact attached.eq_evaluate_of_satisfies assignment extended satisfied.1
        ((CNF.satisfies_append _ _ _).mp satisfied.2).1

end Controller.Native.SourceSerialFold

namespace Controller.Native.SourceController

inductive Owner (parameters : Parameters) where
  | native (slot : Controller.Native.Variable parameters)
  | fold (slot : Controller.Native.Variable parameters) (index : ℕ)
  | negatedFlag (side : Side) (bus : Fin parameters.buses)
  | oldDifference (index : Fin (parameters.buses + parameters.channels))
  | oldDetected (index : ℕ)
  | guard (side : Side) (node : Fin parameters.decoder.nodeCount) (index : ℕ)
  deriving DecidableEq, Repr

structure Entry (parameters : Parameters) where
  owner : Owner parameters
  producer : Bounded.Producer ℕ
  deriving DecidableEq, Repr

structure Cursor (parameters : Parameters) where
  entries : List (Entry parameters)
  slots : Controller.Native.Variable parameters → CNF.Literal ℕ
  assigned : List (Controller.Native.Variable parameters)
  negated : Side → Fin parameters.buses → CNF.Literal ℕ
  oldDifferences : Fin (parameters.buses + parameters.channels) → CNF.Literal ℕ
  oldDetected : CNF.Literal ℕ

def Cursor.lastID (cursor : Cursor parameters) : ℕ :=
  SourceInitialIDs.rootCount parameters + cursor.entries.length

def Cursor.assign (cursor : Cursor parameters) (slot : Controller.Native.Variable parameters)
    (handle : CNF.Literal ℕ) : Cursor parameters :=
  { cursor with slots := Function.update cursor.slots slot handle, assigned := cursor.assigned ++ [slot] }

def Cursor.emit (cursor : Cursor parameters) (owner : Owner parameters) (gate : CNF.Gate ℕ) :
    CNF.Literal ℕ × Cursor parameters :=
  let output := (cursor.lastID + 1, true)
  (output, { cursor with entries := cursor.entries ++ [⟨owner, ⟨output, gate⟩⟩] })

def Cursor.emitNative (cursor : Cursor parameters) (slot : Controller.Native.Variable parameters)
    (gate : CNF.Gate ℕ) : Cursor parameters :=
  let emitted := cursor.emit (.native slot) gate
  emitted.2.assign slot emitted.1

def Cursor.foldNative (cursor : Cursor parameters) (slot : Controller.Native.Variable parameters)
    (junction : Bounded.Junction) (inputs : List (CNF.Literal ℕ)) : Cursor parameters :=
  let allocated := SourceSerialFold.allocate junction cursor.lastID inputs
  let entries := allocated.producers.zipIdx.map fun pair =>
    Entry.mk (.fold slot pair.2) pair.1
  ({ cursor with entries := cursor.entries ++ entries }).assign slot allocated.output

def initial (parameters : Parameters) : Cursor parameters where
  entries := []
  slots
    | .primary (.enable channel) => (SourceInitialIDs.rootID (b := parameters.buses) (.enable channel), true)
    | .primary (.request bus channel) => (SourceInitialIDs.rootID (.request bus channel), true)
    | _ => (0, true)
  assigned :=
    (List.finRange parameters.channels).map (fun channel => .primary (.enable channel)) ++
      (List.finRange parameters.channels).flatMap fun channel =>
        (List.finRange parameters.buses).map fun bus => .primary (.request bus channel)
  negated := fun _ _ => (0, true)
  oldDifferences := fun _ => (0, true)
  oldDetected := (0, true)

/-- The first term and absent arrays are allocated once; both native copies use their handles. -/
def firstArrays (parameters : Parameters) : Cursor parameters :=
  let terms := (List.finRange parameters.channels).foldl (fun cursor channel =>
    let healthy := Controller.Native.Variable.internal (.term .healthy parameters.firstBus channel)
    let faulty := Controller.Native.Variable.internal (.term .faulty parameters.firstBus channel)
    let emitted := cursor.emitNative healthy
      (.and [cursor.slots (.primary (.enable channel)), cursor.slots (.primary (.request parameters.firstBus channel))])
    emitted.assign faulty (emitted.slots healthy)) (initial parameters)
  (List.finRange parameters.channels).foldl (fun cursor channel =>
    let healthy := Controller.Native.Variable.internal (.absent .healthy parameters.firstBus channel)
    let faulty := Controller.Native.Variable.internal (.absent .faulty parameters.firstBus channel)
    let emitted := cursor.emitNative healthy
      (.not (cursor.slots (.internal (.term .healthy parameters.firstBus channel))))
    emitted.assign faulty (emitted.slots healthy)) terms

/-- Balanced D/R folds, a fresh unary-AND W, and retained ternary first products follow source order. -/
def interface (parameters : Parameters) : Cursor parameters :=
  let first := firstArrays parameters
  let driver := first.foldNative (.internal .driver) .conjunction
    (parameters.bridge.drivers.sort.map fun channel =>
      first.slots (.internal (.absent .healthy parameters.firstBus channel)))
  let remaining := driver.foldNative (.internal .remaining) .conjunction
    (parameters.bridge.remaining.sort.map fun channel =>
      driver.slots (.internal (.absent .healthy parameters.firstBus channel)))
  let wire := remaining.emitNative (.primary .wire) (.and [remaining.slots (.internal .driver)])
  let healthyProduct := wire.emitNative (.internal (.firstProduct .healthy))
    (.and [wire.slots (.internal (.absent .healthy parameters.firstBus parameters.bridge.target)),
      wire.slots (.internal .driver), wire.slots (.internal .remaining)])
  let healthyFlag := healthyProduct.emitNative (.internal (.flag .healthy parameters.firstBus))
    (.not (healthyProduct.slots (.internal (.firstProduct .healthy))))
  let faultyProduct := healthyFlag.emitNative (.internal (.firstProduct .faulty))
    (.and [healthyFlag.slots (.primary .wire), healthyFlag.slots (.internal .driver),
      healthyFlag.slots (.internal .remaining)])
  faultyProduct.emitNative (.internal (.flag .faulty parameters.firstBus))
    (.not (faultyProduct.slots (.internal (.firstProduct .faulty))))

def initialMasks (parameters : Parameters) (side : Side) (cursor : Cursor parameters) : Cursor parameters :=
  (List.finRange parameters.channels).foldl (fun cursor channel =>
    cursor.emitNative (.internal (.mask side parameters.firstBus channel))
      (.xor (cursor.slots (.internal (.flag side parameters.firstBus)))
        (cursor.slots (.internal (.absent side parameters.firstBus channel))))) cursor

def laterBus (parameters : Parameters) (side : Side) (bus : Fin parameters.buses)
    (cursor : Cursor parameters) : Cursor parameters :=
  let terms := (List.finRange parameters.channels).foldl (fun cursor channel =>
    cursor.foldNative (.internal (.term side bus channel)) .conjunction
      ([cursor.slots (.primary (.enable channel)), cursor.slots (.primary (.request bus channel))] ++
        ((List.finRange parameters.buses).filter (fun earlier => earlier < bus)).map fun earlier =>
          cursor.slots (.internal (.mask side earlier channel)))) cursor
  let flag := terms.foldNative (.internal (.flag side bus)) .disjunction
    ((List.finRange parameters.channels).map fun channel => terms.slots (.internal (.term side bus channel)))
  (List.finRange parameters.channels).foldl (fun cursor channel =>
    let absent := cursor.emitNative (.internal (.absent side bus channel))
      (.not (cursor.slots (.internal (.term side bus channel))))
    absent.emitNative (.internal (.mask side bus channel))
      (.xor (absent.slots (.internal (.flag side bus))) (absent.slots (.internal (.absent side bus channel))))) flag

def negateFlags (parameters : Parameters) (side : Side) (cursor : Cursor parameters) : Cursor parameters :=
  (List.finRange parameters.buses).foldl (fun cursor bus =>
    let emitted := cursor.emit (.negatedFlag side bus) (.not (cursor.slots (.internal (.flag side bus))))
    { emitted.2 with negated := (Function.update emitted.2.negated side
      (Function.update (emitted.2.negated side) bus emitted.1)) }) cursor

def eligible (parameters : Parameters) (side : Side) (channel : Fin parameters.channels)
    (cursor : Cursor parameters) : Cursor parameters :=
  let guarded := (List.finRange parameters.buses).foldl (fun cursor bus =>
    cursor.emitNative (.internal (.qualifierGuard side bus channel))
      (.or [cursor.negated side bus, cursor.slots (.primary (.request bus channel))])) cursor
  guarded.foldNative (.internal (.qualifier side channel)) .conjunction
    (guarded.slots (.primary (.enable channel)) ::
      (List.finRange parameters.buses).map fun bus => guarded.slots (.internal (.qualifierGuard side bus channel)))

def tail (parameters : Parameters) (side : Side) (cursor : Cursor parameters) : Cursor parameters :=
  let masks := initialMasks parameters side cursor
  let stages := ((List.finRange parameters.buses).filter fun bus => bus.val != 0).foldl
    (fun cursor bus => laterBus parameters side bus cursor) masks
  let negated := negateFlags parameters side stages
  (List.finRange parameters.channels).foldl (fun cursor channel => eligible parameters side channel cursor) negated

/-- This derives the preceding source controller map; it takes no externally supplied role map. -/
def controller (parameters : Parameters) : Cursor parameters :=
  tail parameters .faulty (tail parameters .healthy (interface parameters))

def controllerRoleMap (parameters : Parameters) : Controller.Native.Variable parameters → CNF.Literal ℕ :=
  (controller parameters).slots

def originalObservations (parameters : Parameters) (cursor : Cursor parameters) : Cursor parameters :=
  let paired := (List.finRange (parameters.buses + parameters.channels)).foldl (fun cursor index =>
    let good := (SourceObservation.oldOutputRoles parameters .healthy)[index.val]?.getD .driver
    let bad := (SourceObservation.oldOutputRoles parameters .faulty)[index.val]?.getD .driver
    let emitted := cursor.emit (.oldDifference index)
      (.xor (cursor.slots (.internal good)) (cursor.slots (.internal bad)))
    { emitted.2 with oldDifferences := Function.update emitted.2.oldDifferences index emitted.1 }) cursor
  let allocated := SourceSerialFold.allocate .disjunction paired.lastID
    ((List.finRange (parameters.buses + parameters.channels)).map paired.oldDifferences)
  { paired with entries := paired.entries ++ (allocated.producers.zipIdx.map
      (fun pair => ⟨.oldDetected pair.2, pair.1⟩)), oldDetected := allocated.output }

def guardChain (parameters : Parameters) (side : Side) (node : Fin parameters.decoder.nodeCount)
    (child : CNF.Literal ℕ) (labels : List (Fin parameters.channels))
    (cursor : Cursor parameters) : CNF.Literal ℕ × Cursor parameters :=
  labels.zipIdx.foldl (fun state pair =>
    state.2.emit (.guard side node pair.2)
      (.and [state.1, CNF.negate (state.2.slots (.internal (.qualifier side pair.1)))])) (child, cursor)

def decoderNode (parameters : Parameters) (side : Side) (node : Fin parameters.decoder.nodeCount)
    (cursor : Cursor parameters) : Cursor parameters :=
  let slot := Controller.Native.Variable.internal (.decoder side node)
  match parameters.decoder.node node with
  | .zero => cursor.emitNative slot (.or [])
  | .input channel => cursor.assign slot (cursor.slots (.internal (.qualifier side channel)))
  | .disj children => cursor.foldNative slot .disjunction
      (children.map fun child => cursor.slots (.internal (.decoder side (parameters.decoder.childIndex node child))))
  | .guard child labels =>
      let guarded := guardChain parameters side node
        (cursor.slots (.internal (.decoder side (parameters.decoder.childIndex node child)))) labels cursor
      guarded.2.assign slot guarded.1
  | .liveAnd left right => cursor.emitNative slot (.and
      [cursor.slots (.internal (.decoder side (parameters.decoder.childIndex node left))),
        cursor.slots (.internal (.decoder side (parameters.decoder.childIndex node right)))])

/-- The native generator's accepted decoder grammar excludes live conjunction nodes. -/
def SourceCompatible (parameters : Parameters) : Prop :=
  ∀ node, match parameters.decoder.node node with
    | .liveAnd _ _ => False
    | _ => True

def attachDecoder (parameters : Parameters) (side : Side) (cursor : Cursor parameters) : Cursor parameters :=
  (List.finRange parameters.decoder.nodeCount).foldl (fun cursor node => decoderNode parameters side node cursor) cursor

def newObservations (parameters : Parameters) (cursor : Cursor parameters) : Cursor parameters :=
  let differences := (List.finRange parameters.decoder.roots.length).foldl (fun cursor output =>
    cursor.emitNative (.internal (.difference output)) (.xor
      (cursor.slots (.internal (.decoder .healthy (parameters.decoder.roots.get output))))
      (cursor.slots (.internal (.decoder .faulty (parameters.decoder.roots.get output)))))) cursor
  differences.foldNative (.internal .detected) .disjunction
    ((List.finRange parameters.decoder.roots.length).map fun output =>
      differences.slots (.internal (.difference output)))

/-- Source order retains the old observations before adding both native decoders and new observations. -/
def compile (parameters : Parameters) : Cursor parameters :=
  newObservations parameters (attachDecoder parameters .faulty
    (attachDecoder parameters .healthy (originalObservations parameters (controller parameters))))

/-- All principal source handles are derived from the parameters and source allocation routine. -/
def sourceRoleMap (parameters : Parameters) : Controller.Native.Variable parameters → CNF.Literal ℕ :=
  (compile parameters).slots

def equationFormula (parameters : Parameters) : CNF.Formula ℕ :=
  CNF.ofClauses ((compile parameters).entries.flatMap fun entry => entry.producer.rows)

def assertions (parameters : Parameters) : List (CNF.Literal ℕ) :=
  let slots := sourceRoleMap parameters
  [((slots (.internal (.absent .healthy parameters.firstBus parameters.bridge.target))).1, !parameters.drive),
    ((slots (.internal .driver)).1, parameters.drive),
    ((slots (.primary .wire)).1, parameters.drive), slots (.internal .detected)]

def formula (parameters : Parameters) : CNF.Formula ℕ :=
  equationFormula parameters ++ CNF.ofClauses ((assertions parameters).map fun literal => [literal])

theorem Cursor.assign_slots (cursor : Cursor parameters) (slot : Controller.Native.Variable parameters)
    (handle : CNF.Literal ℕ) : (cursor.assign slot handle).slots slot = handle := by
  simp [Cursor.assign]

theorem Cursor.assign_other (cursor : Cursor parameters) (slot other : Controller.Native.Variable parameters)
    (different : other ≠ slot) (handle : CNF.Literal ℕ) :
    (cursor.assign slot handle).slots other = cursor.slots other := by
  simp [Cursor.assign, different]

theorem Cursor.emit_lastID (cursor : Cursor parameters) (owner : Owner parameters) (gate : CNF.Gate ℕ) :
    (cursor.emit owner gate).2.lastID = cursor.lastID + 1 := by
  simp [Cursor.emit, Cursor.lastID, Nat.add_assoc]

theorem Cursor.assign_assigned (cursor : Cursor parameters) (slot : Controller.Native.Variable parameters)
    (handle : CNF.Literal ℕ) : (cursor.assign slot handle).assigned = cursor.assigned ++ [slot] := rfl

theorem Cursor.emitNative_assigned (cursor : Cursor parameters) (slot : Controller.Native.Variable parameters)
    (gate : CNF.Gate ℕ) : (cursor.emitNative slot gate).assigned = cursor.assigned ++ [slot] := rfl

theorem Cursor.foldNative_assigned (cursor : Cursor parameters) (slot : Controller.Native.Variable parameters)
    (junction : Bounded.Junction) (inputs : List (CNF.Literal ℕ)) :
    (cursor.foldNative slot junction inputs).assigned = cursor.assigned ++ [slot] := rfl

theorem assigned_foldl (items : List α) (step : Cursor parameters → α → Cursor parameters)
    (roles : α → List (Controller.Native.Variable parameters))
    (shape : ∀ cursor item, (step cursor item).assigned = cursor.assigned ++ roles item)
    (cursor : Cursor parameters) :
    (items.foldl step cursor).assigned = cursor.assigned ++ items.flatMap roles := by
  induction items generalizing cursor with
  | nil => simp
  | cons head tail inductionHypothesis =>
      rw [List.foldl_cons, inductionHypothesis, shape]
      simp [List.flatMap_cons, List.append_assoc]

private theorem flatMap_singleton (items : List α) (f : α → β) :
    items.flatMap (fun item => [f item]) = items.map f := by
  induction items with
  | nil => rfl
  | cons head tail inductionHypothesis => simp [inductionHypothesis]

def initialMaskRoles (parameters : Parameters) (side : Side) : List (Controller.Native.Variable parameters) :=
  (List.finRange parameters.channels).map fun channel => .internal (.mask side parameters.firstBus channel)

theorem initialMasks_assigned (parameters : Parameters) (side : Side) (cursor : Cursor parameters) :
    (initialMasks parameters side cursor).assigned = cursor.assigned ++ initialMaskRoles parameters side := by
  rw [initialMasks, assigned_foldl _ _ (fun channel => [.internal (.mask side parameters.firstBus channel)])
    (fun _ _ => rfl)]
  simp [initialMaskRoles, flatMap_singleton]

def firstArrayRoles (parameters : Parameters) : List (Controller.Native.Variable parameters) :=
  ((List.finRange parameters.channels).flatMap fun channel =>
    [.internal (.term .healthy parameters.firstBus channel), .internal (.term .faulty parameters.firstBus channel)]) ++
  ((List.finRange parameters.channels).flatMap fun channel =>
    [.internal (.absent .healthy parameters.firstBus channel), .internal (.absent .faulty parameters.firstBus channel)])

theorem firstArrays_assigned (parameters : Parameters) :
    (firstArrays parameters).assigned = (initial parameters).assigned ++ firstArrayRoles parameters := by
  unfold firstArrays
  rw [assigned_foldl _ _ (fun channel =>
      [.internal (.absent .healthy parameters.firstBus channel), .internal (.absent .faulty parameters.firstBus channel)])
    (fun _ _ => by simp [Cursor.emitNative, Cursor.emit, Cursor.assign, List.append_assoc])]
  rw [assigned_foldl _ _ (fun channel =>
      [.internal (.term .healthy parameters.firstBus channel), .internal (.term .faulty parameters.firstBus channel)])
    (fun _ _ => by simp [Cursor.emitNative, Cursor.emit, Cursor.assign, List.append_assoc])]
  simp [firstArrayRoles, List.append_assoc]

def interfaceRoles (parameters : Parameters) : List (Controller.Native.Variable parameters) :=
  [.internal .driver, .internal .remaining, .primary .wire,
    .internal (.firstProduct .healthy), .internal (.flag .healthy parameters.firstBus),
    .internal (.firstProduct .faulty), .internal (.flag .faulty parameters.firstBus)]

theorem interface_assigned (parameters : Parameters) :
    (interface parameters).assigned = (initial parameters).assigned ++
      firstArrayRoles parameters ++ interfaceRoles parameters := by
  simp only [interface, Cursor.emitNative_assigned, Cursor.foldNative_assigned, firstArrays_assigned]
  simp [interfaceRoles, List.append_assoc]

def laterBusRoles (parameters : Parameters) (side : Side) (bus : Fin parameters.buses) :
    List (Controller.Native.Variable parameters) :=
  ((List.finRange parameters.channels).map fun channel => .internal (.term side bus channel)) ++
    [.internal (.flag side bus)] ++
    ((List.finRange parameters.channels).flatMap fun channel =>
      [.internal (.absent side bus channel), .internal (.mask side bus channel)])

theorem laterBus_assigned (parameters : Parameters) (side : Side) (bus : Fin parameters.buses)
    (cursor : Cursor parameters) :
    (laterBus parameters side bus cursor).assigned = cursor.assigned ++ laterBusRoles parameters side bus := by
  unfold laterBus
  rw [assigned_foldl _ _ (fun channel => [.internal (.absent side bus channel), .internal (.mask side bus channel)])
    (fun _ _ => by simp [Cursor.emitNative, Cursor.emit, Cursor.assign, List.append_assoc]), Cursor.foldNative_assigned]
  rw [assigned_foldl _ _ (fun channel => [.internal (.term side bus channel)]) (fun _ _ => rfl)]
  simp [laterBusRoles, List.append_assoc, flatMap_singleton]

theorem negateFlags_assigned (parameters : Parameters) (side : Side) (cursor : Cursor parameters) :
    (negateFlags parameters side cursor).assigned = cursor.assigned := by
  rw [negateFlags, assigned_foldl _ _ (fun _ => []) (fun _ _ => by simp [Cursor.emit])]
  simp

def eligibleRoles (parameters : Parameters) (side : Side) (channel : Fin parameters.channels) :
    List (Controller.Native.Variable parameters) :=
  ((List.finRange parameters.buses).map fun bus => .internal (.qualifierGuard side bus channel)) ++
    [.internal (.qualifier side channel)]

theorem eligible_assigned (parameters : Parameters) (side : Side) (channel : Fin parameters.channels)
    (cursor : Cursor parameters) :
    (eligible parameters side channel cursor).assigned = cursor.assigned ++ eligibleRoles parameters side channel := by
  rw [eligible, Cursor.foldNative_assigned,
    assigned_foldl _ _ (fun bus => [.internal (.qualifierGuard side bus channel)]) (fun _ _ => rfl)]
  simp [eligibleRoles, List.append_assoc, flatMap_singleton]

def tailRoles (parameters : Parameters) (side : Side) : List (Controller.Native.Variable parameters) :=
  initialMaskRoles parameters side ++
    ((List.finRange parameters.buses).filter fun bus => bus.val != 0).flatMap
      (laterBusRoles parameters side) ++
    (List.finRange parameters.channels).flatMap (eligibleRoles parameters side)

theorem tail_assigned (parameters : Parameters) (side : Side) (cursor : Cursor parameters) :
    (tail parameters side cursor).assigned = cursor.assigned ++ tailRoles parameters side := by
  rw [tail, assigned_foldl _ _ (eligibleRoles parameters side) (fun cursor channel => eligible_assigned parameters side channel cursor),
    negateFlags_assigned,
    assigned_foldl _ _ (laterBusRoles parameters side) (fun cursor bus => laterBus_assigned parameters side bus cursor),
    initialMasks_assigned]
  simp [tailRoles, List.append_assoc]

theorem guardChain_assigned (parameters : Parameters) (side : Side) (node : Fin parameters.decoder.nodeCount)
    (child : CNF.Literal ℕ) (labels : List (Fin parameters.channels)) (cursor : Cursor parameters) :
    (guardChain parameters side node child labels cursor).2.assigned = cursor.assigned := by
  unfold guardChain
  generalize labels.zipIdx = items
  induction items generalizing child cursor with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp only [List.foldl_cons]
      rw [inductionHypothesis]
      rfl

theorem decoderNode_assigned (parameters : Parameters) (side : Side) (node : Fin parameters.decoder.nodeCount)
    (cursor : Cursor parameters) :
    (decoderNode parameters side node cursor).assigned = cursor.assigned ++ [.internal (.decoder side node)] := by
  unfold decoderNode
  cases parameters.decoder.node node <;> try rfl
  simp [Cursor.assign, guardChain_assigned]

theorem attachDecoder_assigned (parameters : Parameters) (side : Side) (cursor : Cursor parameters) :
    (attachDecoder parameters side cursor).assigned = cursor.assigned ++
      (List.finRange parameters.decoder.nodeCount).map (fun node => .internal (.decoder side node)) := by
  rw [attachDecoder, assigned_foldl _ _ (fun node => [.internal (.decoder side node)])
    (fun cursor node => decoderNode_assigned parameters side node cursor)]
  simp [flatMap_singleton]

theorem originalObservations_assigned (parameters : Parameters) (cursor : Cursor parameters) :
    (originalObservations parameters cursor).assigned = cursor.assigned := by
  unfold originalObservations
  rw [assigned_foldl _ _ (fun _ => []) (fun _ _ => by simp [Cursor.emit])]
  simp

theorem newObservations_assigned (parameters : Parameters) (cursor : Cursor parameters) :
    (newObservations parameters cursor).assigned = cursor.assigned ++
      (List.finRange parameters.decoder.roots.length).map (fun output => .internal (.difference output)) ++
        [.internal .detected] := by
  rw [newObservations, Cursor.foldNative_assigned,
    assigned_foldl _ _ (fun output => [.internal (.difference output)]) (fun _ _ => rfl)]
  simp [List.append_assoc, flatMap_singleton]

def assignedRoles (parameters : Parameters) : List (Controller.Native.Variable parameters) :=
  (initial parameters).assigned ++ firstArrayRoles parameters ++ interfaceRoles parameters ++
    tailRoles parameters .healthy ++ tailRoles parameters .faulty ++
    (List.finRange parameters.decoder.nodeCount).map (fun node => .internal (.decoder .healthy node)) ++
    (List.finRange parameters.decoder.nodeCount).map (fun node => .internal (.decoder .faulty node)) ++
    (List.finRange parameters.decoder.roots.length).map (fun output => .internal (.difference output)) ++
    [.internal .detected]

theorem compile_assigned (parameters : Parameters) : (compile parameters).assigned = assignedRoles parameters := by
  rw [compile, newObservations_assigned, attachDecoder_assigned, attachDecoder_assigned,
    originalObservations_assigned, controller, tail_assigned, tail_assigned, interface_assigned]
  simp [assignedRoles, List.append_assoc]

private theorem tail_mem_assigned (parameters : Parameters) (side : Side)
    (slot : Controller.Native.Variable parameters) (member : slot ∈ tailRoles parameters side) :
    slot ∈ assignedRoles parameters := by
  cases side <;> simp only [assignedRoles, List.mem_append] <;> tauto

private theorem later_mem_tail (parameters : Parameters) (side : Side) (bus : Fin parameters.buses)
    (nonfirst : bus ≠ parameters.firstBus) (slot : Controller.Native.Variable parameters)
    (member : slot ∈ laterBusRoles parameters side bus) : slot ∈ tailRoles parameters side := by
  have nonzero : bus.val ≠ 0 := by
    intro zero
    apply nonfirst
    apply Fin.ext
    simpa [Parameters.firstBus] using zero
  simp only [tailRoles, List.mem_append]
  apply Or.inl
  apply Or.inr
  exact List.mem_flatMap.mpr ⟨bus, by simp [nonzero], member⟩

theorem all_native_roles_assigned (parameters : Parameters) (raw : parameters.layout = .raw)
    (slot : Controller.Native.Variable parameters) : slot ∈ (compile parameters).assigned := by
  rw [compile_assigned]
  cases slot with
  | primary primary =>
      cases primary <;> simp [assignedRoles, initial, interfaceRoles]
  | internal role =>
      cases role with
      | driver => simp [assignedRoles, interfaceRoles]
      | remaining => simp [assignedRoles, interfaceRoles]
      | firstProduct side => cases side <;> simp [assignedRoles, interfaceRoles]
      | term side bus channel =>
          by_cases first : bus = parameters.firstBus
          · subst bus
            cases side <;> simp [assignedRoles, firstArrayRoles]
          · apply tail_mem_assigned parameters side
            apply later_mem_tail parameters side bus first
            simp [laterBusRoles]
      | absent side bus channel =>
          by_cases first : bus = parameters.firstBus
          · subst bus
            cases side <;> simp [assignedRoles, firstArrayRoles]
          · apply tail_mem_assigned parameters side
            apply later_mem_tail parameters side bus first
            simp [laterBusRoles]
      | flag side bus =>
          by_cases first : bus = parameters.firstBus
          · subst bus
            cases side <;> simp [assignedRoles, interfaceRoles]
          · apply tail_mem_assigned parameters side
            apply later_mem_tail parameters side bus first
            simp [laterBusRoles]
      | mask side bus channel =>
          apply tail_mem_assigned parameters side
          by_cases first : bus = parameters.firstBus
          · subst bus
            simp [tailRoles, initialMaskRoles]
          · apply later_mem_tail parameters side bus first
            simp [laterBusRoles]
      | active side bus channel =>
          have impossible := bus.isLt
          simp [raw, PrefixLayout.activeCount] at impossible
      | qualifierGuard side bus channel =>
          apply tail_mem_assigned parameters side
          simp [tailRoles, eligibleRoles]
      | qualifier side channel =>
          apply tail_mem_assigned parameters side
          simp [tailRoles, eligibleRoles]
      | decoder side node => cases side <;> simp [assignedRoles]
      | difference output => simp [assignedRoles]
      | detected => simp [assignedRoles]

inductive Variable (parameters : Parameters) where
  | root (role : InterfaceAlias.Root parameters.channels parameters.buses)
  | defined (index : Fin (compile parameters).entries.length)
  deriving DecidableEq

def variableCoordinates (parameters : Parameters) : Variable parameters ≃
    (InterfaceAlias.Root parameters.channels parameters.buses ⊕ Fin (compile parameters).entries.length) where
  toFun
    | .root role => .inl role
    | .defined index => .inr index
  invFun
    | .inl role => .root role
    | .inr index => .defined index
  left_inv coordinate := by cases coordinate <;> rfl
  right_inv coordinate := by cases coordinate <;> rfl

/-- Defined-variable coordinates include every stored producer, including private and unused gates. -/
def variableIndex (parameters : Parameters) : Variable parameters ≃ Fin (compile parameters).lastID :=
  (variableCoordinates parameters).trans
    ((Equiv.sumCongr SourceInitialIDs.rootIndex (Equiv.refl _)).trans finSumFinEquiv)

def variableID (parameters : Parameters) (coordinate : Variable parameters) : ℕ :=
  (variableIndex parameters coordinate).val + 1

theorem variableID_root (parameters : Parameters)
    (role : InterfaceAlias.Root parameters.channels parameters.buses) :
    variableID parameters (.root role) = SourceInitialIDs.rootID role := rfl

theorem variableID_defined (parameters : Parameters) (index : Fin (compile parameters).entries.length) :
    variableID parameters (.defined index) = SourceInitialIDs.rootCount parameters + index.val + 1 := rfl

theorem variableID_injective (parameters : Parameters) : Function.Injective (variableID parameters) := by
  intro left right equal
  apply (variableIndex parameters).injective
  apply Fin.ext
  simp only [variableID] at equal
  omega

theorem variableID_coverage (parameters : Parameters) (sourceID : ℕ)
    (positive : 0 < sourceID) (bounded : sourceID ≤ (compile parameters).lastID) :
    ∃! coordinate : Variable parameters, variableID parameters coordinate = sourceID := by
  let index : Fin (compile parameters).lastID := ⟨sourceID - 1, by omega⟩
  refine ⟨(variableIndex parameters).symm index, ?_, ?_⟩
  · simp [variableID, index]
    omega
  · intro coordinate equal
    apply (variableIndex parameters).injective
    apply Fin.ext
    simp only [variableID] at equal
    simp only [Equiv.apply_symm_apply, index]
    omega

def definedOwner (parameters : Parameters) (index : Fin (compile parameters).entries.length) : Owner parameters :=
  (compile parameters).entries[index].owner

theorem Cursor.foldNative_unary (cursor : Cursor parameters) (slot : Controller.Native.Variable parameters)
    (junction : Bounded.Junction) (input : CNF.Literal ℕ) :
    cursor.foldNative slot junction [input] = cursor.assign slot input := by
  simp [Cursor.foldNative, SourceSerialFold.allocate_unary]

theorem decoder_input_alias (parameters : Parameters) (side : Side) (node : Fin parameters.decoder.nodeCount)
    (channel : Fin parameters.channels) (cursor : Cursor parameters)
    (inputNode : parameters.decoder.node node = .input channel) :
    (decoderNode parameters side node cursor).slots (.internal (.decoder side node)) =
      cursor.slots (.internal (.qualifier side channel)) := by
  simp [decoderNode, inputNode, Cursor.assign]

theorem guardChain_empty (parameters : Parameters) (side : Side) (node : Fin parameters.decoder.nodeCount)
    (child : CNF.Literal ℕ) (cursor : Cursor parameters) :
    guardChain parameters side node child [] cursor = (child, cursor) := rfl

theorem assertions_length (parameters : Parameters) : (assertions parameters).length = 4 := rfl

end Controller.Native.SourceController

namespace Controller.Native.SourceSerialFold

/-- Consecutive allocation is independent of whether input handles have already been validated. -/
inductive Consecutive : ℕ → List (Bounded.Producer ℕ) → ℕ → Prop where
  | nil (lastID : ℕ) : Consecutive lastID [] lastID
  | cons (rest : Consecutive (lastID + 1) producers nextID) :
      Consecutive lastID (⟨(lastID + 1, true), gate⟩ :: producers) nextID

theorem Consecutive.count {lastID nextID : ℕ} {producers : List (Bounded.Producer ℕ)}
    (consecutive : Consecutive lastID producers nextID) : nextID = lastID + producers.length := by
  induction consecutive with
  | nil => simp
  | cons _ inductionHypothesis => simp only [List.length_cons]; omega

theorem Consecutive.append {firstID middleID lastID : ℕ}
    {first second : List (Bounded.Producer ℕ)}
    (left : Consecutive firstID first middleID) (right : Consecutive middleID second lastID) :
    Consecutive firstID (first ++ second) lastID := by
  induction left with
  | nil => exact right
  | cons rest inductionHypothesis => exact .cons (inductionHypothesis right)

theorem Consecutive.output {lastID nextID : ℕ} {producers : List (Bounded.Producer ℕ)}
    (consecutive : Consecutive lastID producers nextID) (index : Fin producers.length) :
    producers[index].output = (lastID + index.val + 1, true) := by
  induction consecutive with
  | nil => exact Fin.elim0 index
  | cons rest inductionHypothesis =>
      rcases index with ⟨index, bound⟩
      cases index with
      | zero => rfl
      | succ index =>
          have smaller := inductionHypothesis ⟨index, by simpa using bound⟩
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using smaller

theorem pairLayer_consecutive (junction : Bounded.Junction) (lastID : ℕ)
    (inputs : List (CNF.Literal ℕ)) :
    Consecutive lastID (pairLayer junction lastID inputs).producers (pairLayer junction lastID inputs).nextID := by
  induction inputs using List.twoStepInduction generalizing lastID with
  | nil => exact .nil lastID
  | singleton input => exact .nil lastID
  | cons_cons left right tail inductionHypothesis _ => exact .cons (inductionHypothesis (lastID + 1))

theorem allocate_consecutive (junction : Bounded.Junction) (lastID : ℕ)
    (inputs : List (CNF.Literal ℕ)) :
    Consecutive lastID (allocate junction lastID inputs).producers (allocate junction lastID inputs).nextID := by
  have ranked : ∀ size, ∀ lastID inputs, inputs.length = size →
      Consecutive lastID (allocate junction lastID inputs).producers (allocate junction lastID inputs).nextID := by
    intro size
    induction size using Nat.strong_induction_on with
    | h size inductionHypothesis =>
        intro lastID inputs inputSize
        cases inputs with
        | nil => rw [allocate]; exact .cons (.nil (lastID + 1))
        | cons left tail =>
            cases tail with
            | nil => rw [allocate]; exact .nil lastID
            | cons right rest =>
                let layer := pairLayer junction lastID (left :: right :: rest)
                have shorter : layer.handles.length < size := by
                  dsimp [layer]
                  rw [pairLayer_length]
                  simp only [List.length_cons]
                  simp only [List.length_cons] at inputSize
                  omega
                have smaller := inductionHypothesis _ shorter layer.nextID layer.handles rfl
                rw [allocate]
                exact (pairLayer_consecutive junction lastID _).append smaller
  exact ranked inputs.length lastID inputs rfl

end Controller.Native.SourceSerialFold

namespace Controller.Native.SourceController

def Cursor.Serial (cursor : Cursor parameters) : Prop :=
  SourceSerialFold.Consecutive (SourceInitialIDs.rootCount parameters)
    (cursor.entries.map Entry.producer) cursor.lastID

theorem Cursor.serial_assign (cursor : Cursor parameters) (slot : Controller.Native.Variable parameters)
    (handle : CNF.Literal ℕ) (serial : cursor.Serial) : (cursor.assign slot handle).Serial := serial

theorem Cursor.serial_emit (cursor : Cursor parameters) (owner : Owner parameters) (gate : CNF.Gate ℕ)
    (serial : cursor.Serial) : (cursor.emit owner gate).2.Serial := by
  have result := serial.append (SourceSerialFold.Consecutive.cons
    (gate := gate) (SourceSerialFold.Consecutive.nil (cursor.lastID + 1)))
  simpa [Cursor.Serial, Cursor.emit, Cursor.lastID, List.map_append, Nat.add_assoc] using result

theorem Cursor.serial_emitNative (cursor : Cursor parameters) (slot : Controller.Native.Variable parameters)
    (gate : CNF.Gate ℕ) (serial : cursor.Serial) : (cursor.emitNative slot gate).Serial :=
  Cursor.serial_assign _ _ _ (cursor.serial_emit _ _ serial)

private theorem foldEntries_producers (slot : Controller.Native.Variable parameters)
    (producers : List (Bounded.Producer ℕ)) :
    ((producers.zipIdx.map fun pair => Entry.mk (.fold slot pair.2) pair.1).map Entry.producer) = producers := by
  simp only [List.map_map]
  change producers.zipIdx.map Prod.fst = producers
  exact List.zipIdx_map_fst 0 producers

theorem Cursor.serial_foldNative (cursor : Cursor parameters) (slot : Controller.Native.Variable parameters)
    (junction : Bounded.Junction) (inputs : List (CNF.Literal ℕ)) (serial : cursor.Serial) :
    (cursor.foldNative slot junction inputs).Serial := by
  have allocated := SourceSerialFold.allocate_consecutive junction cursor.lastID inputs
  have result := serial.append allocated
  have count := result.count
  simp only [List.length_append, List.length_map] at count
  rw [Cursor.foldNative, Cursor.Serial]
  simp only [Cursor.assign, Cursor.lastID, List.map_append, foldEntries_producers,
    List.length_append, List.length_map, List.length_zipIdx]
  simp only [Cursor.lastID] at result count
  convert result using 1 <;> omega

theorem initial_serial (parameters : Parameters) : (initial parameters).Serial :=
  SourceSerialFold.Consecutive.nil _

theorem serial_foldl (items : List α) (step : Cursor parameters → α → Cursor parameters)
    (preserves : ∀ cursor item, cursor.Serial → (step cursor item).Serial)
    (cursor : Cursor parameters) (serial : cursor.Serial) : (items.foldl step cursor).Serial := by
  induction items generalizing cursor with
  | nil => exact serial
  | cons head tail inductionHypothesis => exact inductionHypothesis _ (preserves cursor head serial)

theorem firstArrays_serial (parameters : Parameters) : (firstArrays parameters).Serial := by
  unfold firstArrays
  apply serial_foldl
  · intro cursor channel serial
    exact Cursor.serial_assign _ _ _ (cursor.serial_emitNative _ _ serial)
  · apply serial_foldl
    · intro cursor channel serial
      exact Cursor.serial_assign _ _ _ (cursor.serial_emitNative _ _ serial)
    · exact initial_serial parameters

theorem interface_serial (parameters : Parameters) : (interface parameters).Serial := by
  unfold interface
  repeat first
    | apply Cursor.serial_emitNative
    | apply Cursor.serial_foldNative
    | exact firstArrays_serial parameters

theorem initialMasks_serial (parameters : Parameters) (side : Side) (cursor : Cursor parameters)
    (serial : cursor.Serial) : (initialMasks parameters side cursor).Serial := by
  apply serial_foldl
  · intro cursor channel serial
    exact cursor.serial_emitNative _ _ serial
  · exact serial

theorem laterBus_serial (parameters : Parameters) (side : Side) (bus : Fin parameters.buses)
    (cursor : Cursor parameters) (serial : cursor.Serial) : (laterBus parameters side bus cursor).Serial := by
  unfold laterBus
  apply serial_foldl
  · intro cursor channel serial
    exact Cursor.serial_emitNative _ _ _ (cursor.serial_emitNative _ _ serial)
  · apply Cursor.serial_foldNative
    apply serial_foldl
    · intro cursor channel serial
      exact cursor.serial_foldNative _ _ _ serial
    · exact serial

theorem negateFlags_serial (parameters : Parameters) (side : Side) (cursor : Cursor parameters)
    (serial : cursor.Serial) : (negateFlags parameters side cursor).Serial := by
  unfold negateFlags
  apply serial_foldl
  · intro cursor bus serial
    change (cursor.emit (.negatedFlag side bus) _).2.Serial
    exact cursor.serial_emit _ _ serial
  · exact serial

theorem eligible_serial (parameters : Parameters) (side : Side) (channel : Fin parameters.channels)
    (cursor : Cursor parameters) (serial : cursor.Serial) : (eligible parameters side channel cursor).Serial := by
  unfold eligible
  apply Cursor.serial_foldNative
  apply serial_foldl
  · intro cursor bus serial
    exact cursor.serial_emitNative _ _ serial
  · exact serial

theorem tail_serial (parameters : Parameters) (side : Side) (cursor : Cursor parameters)
    (serial : cursor.Serial) : (tail parameters side cursor).Serial := by
  unfold tail
  apply serial_foldl
  · intro cursor channel serial
    exact eligible_serial parameters side channel cursor serial
  · apply negateFlags_serial
    apply serial_foldl
    · intro cursor bus serial
      exact laterBus_serial parameters side bus cursor serial
    · exact initialMasks_serial parameters side cursor serial

theorem controller_serial (parameters : Parameters) : (controller parameters).Serial :=
  tail_serial parameters .faulty _ (tail_serial parameters .healthy _ (interface_serial parameters))

theorem guardChain_serial (parameters : Parameters) (side : Side) (node : Fin parameters.decoder.nodeCount)
    (child : CNF.Literal ℕ) (labels : List (Fin parameters.channels)) (cursor : Cursor parameters)
    (serial : cursor.Serial) : (guardChain parameters side node child labels cursor).2.Serial := by
  unfold guardChain
  generalize labels.zipIdx = items
  induction items generalizing child cursor with
  | nil => exact serial
  | cons head tail inductionHypothesis =>
      simp only [List.foldl_cons]
      apply inductionHypothesis
      exact cursor.serial_emit _ _ serial

theorem decoderNode_serial (parameters : Parameters) (side : Side) (node : Fin parameters.decoder.nodeCount)
    (cursor : Cursor parameters) (serial : cursor.Serial) : (decoderNode parameters side node cursor).Serial := by
  unfold decoderNode
  cases parameters.decoder.node node
  · exact cursor.serial_emitNative _ _ serial
  · exact cursor.serial_assign _ _ serial
  · exact cursor.serial_foldNative _ _ _ serial
  · apply Cursor.serial_assign
    exact guardChain_serial parameters side node _ _ cursor serial
  · exact cursor.serial_emitNative _ _ serial

theorem attachDecoder_serial (parameters : Parameters) (side : Side) (cursor : Cursor parameters)
    (serial : cursor.Serial) : (attachDecoder parameters side cursor).Serial := by
  unfold attachDecoder
  exact serial_foldl _ _ (fun cursor node serial => decoderNode_serial parameters side node cursor serial) cursor serial

theorem newObservations_serial (parameters : Parameters) (cursor : Cursor parameters)
    (serial : cursor.Serial) : (newObservations parameters cursor).Serial := by
  unfold newObservations
  apply Cursor.serial_foldNative
  exact serial_foldl _ _ (fun cursor output serial => cursor.serial_emitNative _ _ serial) cursor serial

private theorem entries_producers (owner : ℕ → Owner parameters) (producers : List (Bounded.Producer ℕ)) :
    ((producers.zipIdx.map fun pair => Entry.mk (owner pair.2) pair.1).map Entry.producer) = producers := by
  simp only [List.map_map]
  change producers.zipIdx.map Prod.fst = producers
  exact List.zipIdx_map_fst 0 producers

theorem Cursor.serial_appendFold (cursor : Cursor parameters) (junction : Bounded.Junction)
    (inputs : List (CNF.Literal ℕ)) (owner : ℕ → Owner parameters) (serial : cursor.Serial) :
    ({ cursor with entries := cursor.entries ++
      ((SourceSerialFold.allocate junction cursor.lastID inputs).producers.zipIdx.map
        (fun pair : Bounded.Producer ℕ × ℕ => Entry.mk (owner pair.2) pair.1)) } : Cursor parameters).Serial := by
  have allocated := SourceSerialFold.allocate_consecutive junction cursor.lastID inputs
  have result := serial.append allocated
  have count := result.count
  simp only [List.length_append, List.length_map] at count
  simp only [Cursor.Serial, Cursor.lastID, List.map_append, entries_producers,
    List.length_append, List.length_map, List.length_zipIdx]
  simp only [Cursor.lastID] at result count
  convert result using 1 <;> omega

theorem originalObservations_serial (parameters : Parameters) (cursor : Cursor parameters)
    (serial : cursor.Serial) : (originalObservations parameters cursor).Serial := by
  unfold originalObservations
  apply Cursor.serial_appendFold
  apply serial_foldl
  · intro cursor index serial
    change (cursor.emit (.oldDifference index) _).2.Serial
    exact cursor.serial_emit _ _ serial
  · exact serial

theorem compile_serial (parameters : Parameters) : (compile parameters).Serial :=
  newObservations_serial parameters _ (attachDecoder_serial parameters .faulty _
    (attachDecoder_serial parameters .healthy _ (originalObservations_serial parameters _ (controller_serial parameters))))

/-- Every actual producer output is its declared source variable ID, with positive phase. -/
theorem defined_output_correspondence (parameters : Parameters) (index : Fin (compile parameters).entries.length) :
    (compile parameters).entries[index].producer.output = (variableID parameters (.defined index), true) := by
  have output := (compile_serial parameters).output
    ⟨index.val, by simp⟩
  simpa [variableID_defined] using output

end Controller.Native.SourceController


namespace Controller.Native.SourceSerialFold

theorem Ordered.consecutive {firstID lastID : ℕ} {producers : List (Bounded.Producer ℕ)}
    (ordered : Ordered firstID producers lastID) : Consecutive firstID producers lastID := by
  induction ordered with
  | nil => exact .nil _
  | cons bounded rest inductionHypothesis => exact .cons inductionHypothesis

theorem State.execute_count (state : State roots) (producers : List (Bounded.Producer ℕ)) :
    (state.execute producers).count = state.count + producers.length := by
  induction producers generalizing state with
  | nil => simp [State.execute]
  | cons head tail inductionHypothesis =>
      change ((state.step head).execute tail).count = _
      rw [inductionHypothesis]
      simp [State.step, Nat.add_assoc, Nat.add_comm]

end Controller.Native.SourceSerialFold

namespace Controller.Native.SourceController

/-- Orderedness is stronger than consecutive IDs: every gate reads an already allocated handle. -/
def Cursor.Ordered (cursor : Cursor parameters) : Prop :=
  SourceSerialFold.Ordered (SourceInitialIDs.rootCount parameters)
    (cursor.entries.map Entry.producer) cursor.lastID

theorem Cursor.ordered_serial (cursor : Cursor parameters) (ordered : cursor.Ordered) : cursor.Serial :=
  ordered.consecutive

theorem Cursor.ordered_assign (cursor : Cursor parameters) (slot : Controller.Native.Variable parameters)
    (handle : CNF.Literal ℕ) (ordered : cursor.Ordered) : (cursor.assign slot handle).Ordered := ordered

theorem Cursor.ordered_emit (cursor : Cursor parameters) (owner : Owner parameters) (gate : CNF.Gate ℕ)
    (ordered : cursor.Ordered) (bounded : SourceSerialFold.HandlesBounded cursor.lastID gate.inputs) :
    (cursor.emit owner gate).2.Ordered := by
  have result := ordered.append (SourceSerialFold.Ordered.cons bounded
    (SourceSerialFold.Ordered.nil (cursor.lastID + 1)))
  simpa [Cursor.Ordered, Cursor.emit, Cursor.lastID, List.map_append, Nat.add_assoc] using result

theorem Cursor.ordered_emitNative (cursor : Cursor parameters) (slot : Controller.Native.Variable parameters)
    (gate : CNF.Gate ℕ) (ordered : cursor.Ordered)
    (bounded : SourceSerialFold.HandlesBounded cursor.lastID gate.inputs) :
    (cursor.emitNative slot gate).Ordered :=
  Cursor.ordered_assign _ _ _ (cursor.ordered_emit _ _ ordered bounded)

theorem Cursor.ordered_foldNative (cursor : Cursor parameters) (slot : Controller.Native.Variable parameters)
    (junction : Bounded.Junction) (inputs : List (CNF.Literal ℕ)) (ordered : cursor.Ordered)
    (bounded : SourceSerialFold.HandlesBounded cursor.lastID inputs) :
    (cursor.foldNative slot junction inputs).Ordered := by
  have allocated := (SourceSerialFold.allocate_ordered junction cursor.lastID inputs bounded).1
  have result := ordered.append allocated
  have count := result.consecutive.count
  simp only [List.length_append, List.length_map] at count
  rw [Cursor.foldNative, Cursor.Ordered]
  simp only [Cursor.assign, Cursor.lastID, List.map_append, foldEntries_producers,
    List.length_append, List.length_map, List.length_zipIdx]
  simp only [Cursor.lastID] at result count
  convert result using 1 <;> omega

theorem initial_ordered (parameters : Parameters) : (initial parameters).Ordered :=
  SourceSerialFold.Ordered.nil _

/-- Replay the actual retained producer list through N01; no unused producer is removed. -/
def Cursor.toState (cursor : Cursor parameters) : SourceSerialFold.State (SourceInitialIDs.rootCount parameters) :=
  (SourceSerialFold.State.mk (SourceInitialIDs.rootCount parameters)
    (by have positive := parameters.bridge.target.isLt; unfold SourceInitialIDs.rootCount; omega)
    .roots).execute (cursor.entries.map Entry.producer)

theorem Cursor.toState_count (cursor : Cursor parameters) : cursor.toState.count = cursor.lastID := by
  rw [Cursor.toState, SourceSerialFold.State.execute_count]
  simp [Cursor.lastID]

/-- This is row identity, including row order, signed literal IDs, private folds and old observations. -/
theorem Cursor.source_rows (cursor : Cursor parameters) (ordered : cursor.Ordered) :
    CNF.relabel SourceObservation.sourceID cursor.toState.circuit.formula =
      CNF.ofClauses (cursor.entries.flatMap fun entry => entry.producer.rows) := by
  unfold Cursor.Ordered at ordered
  rw [Cursor.toState]
  rw [SourceSerialFold.State.source_rows
    (SourceSerialFold.State.mk (SourceInitialIDs.rootCount parameters) _ .roots) _ ordered]
  simp [List.flatMap_map, CNF.relabel, CNF.AcyclicCircuit.formula,
    Controller.CNF.OrderedFormula.Internal.ext_iff, Controller.CNF.OrderedFormula.Internal.clauses_append,
    Controller.CNF.OrderedFormula.empty, Controller.CNF.OrderedFormula.relabel]

/-- A concrete source cursor has the unique N01 gate extension of its exact preceding root universe. -/
theorem Cursor.circuit_unique_extension (cursor : Cursor parameters)
    (assignment : Fin (SourceInitialIDs.rootCount parameters) → Bool) :
    ∃! extended, cursor.toState.circuit.rootValues extended = assignment ∧
      CNF.Satisfies extended cursor.toState.circuit.formula :=
  CNF.AcyclicCircuit.existsUnique_extension _ assignment

theorem compile_source_rows (parameters : Parameters) (ordered : (compile parameters).Ordered) :
    CNF.relabel SourceObservation.sourceID (compile parameters).toState.circuit.formula =
      equationFormula parameters :=
  Cursor.source_rows _ ordered

end Controller.Native.SourceController


namespace Controller.Native.SourceController

/-- Only assigned handles can be used as native dependencies; unassigned defaults remain zero. -/
def Cursor.AssignedBounded (cursor : Cursor parameters) : Prop :=
  ∀ slot ∈ cursor.assigned, 0 < (cursor.slots slot).1 ∧ (cursor.slots slot).1 ≤ cursor.lastID

theorem Cursor.assignedBounded_assign (cursor : Cursor parameters)
    (slot : Controller.Native.Variable parameters) (handle : CNF.Literal ℕ)
    (prior : cursor.AssignedBounded) (valid : 0 < handle.1 ∧ handle.1 ≤ cursor.lastID) :
    (cursor.assign slot handle).AssignedBounded := by
  intro other membership
  simp only [Cursor.assign_assigned, List.mem_append, List.mem_singleton] at membership
  by_cases equal : other = slot
  · subst other
    simpa [Cursor.assign, Cursor.lastID] using valid
  · rcases membership with membership | impossible
    · simpa [Cursor.assign, Cursor.lastID, equal] using prior other membership
    · exact False.elim (equal impossible)

theorem Cursor.assignedBounded_emit (cursor : Cursor parameters) (owner : Owner parameters)
    (gate : CNF.Gate ℕ) (prior : cursor.AssignedBounded) :
    (cursor.emit owner gate).2.AssignedBounded := by
  intro slot membership
  have valid := prior slot membership
  change 0 < (cursor.slots slot).1 ∧ (cursor.slots slot).1 ≤ (cursor.emit owner gate).2.lastID
  rw [Cursor.emit_lastID]
  exact ⟨valid.1, by omega⟩

theorem Cursor.assignedBounded_emitNative (cursor : Cursor parameters)
    (slot : Controller.Native.Variable parameters) (gate : CNF.Gate ℕ)
    (prior : cursor.AssignedBounded) : (cursor.emitNative slot gate).AssignedBounded := by
  apply Cursor.assignedBounded_assign
  · exact cursor.assignedBounded_emit _ _ prior
  · simp only [Cursor.emit, Cursor.lastID, List.length_append, List.length_singleton]
    constructor <;> omega

theorem Cursor.assignedBounded_foldNative (cursor : Cursor parameters)
    (slot : Controller.Native.Variable parameters) (junction : Bounded.Junction)
    (inputs : List (CNF.Literal ℕ)) (prior : cursor.AssignedBounded)
    (bounded : SourceSerialFold.HandlesBounded cursor.lastID inputs) :
    (cursor.foldNative slot junction inputs).AssignedBounded := by
  have allocated := SourceSerialFold.allocate_ordered junction cursor.lastID inputs bounded
  have count := allocated.1.consecutive.count
  have output := allocated.2 (SourceSerialFold.allocate junction cursor.lastID inputs).output (by simp)
  unfold Cursor.foldNative
  apply Cursor.assignedBounded_assign
  · intro old membership
    have valid := prior old membership
    change 0 < (cursor.slots old).1 ∧ (cursor.slots old).1 ≤ _
    simp only [Cursor.lastID, List.length_append, List.length_map, List.length_zipIdx]
    exact ⟨valid.1, by unfold Cursor.lastID at valid; omega⟩
  · simp only [Cursor.lastID, List.length_append, List.length_map, List.length_zipIdx]
    simp only [Cursor.lastID] at count output
    exact ⟨output.1, by omega⟩

theorem initial_assignedBounded (parameters : Parameters) : (initial parameters).AssignedBounded := by
  intro slot membership
  cases slot with
  | primary primary =>
      cases primary with
      | enable channel =>
          have bound := channel.isLt
          simp only [initial, SourceInitialIDs.rootID_enable, Cursor.lastID,
            SourceInitialIDs.rootCount, List.length_nil, Nat.add_zero]
          constructor <;> omega
      | request bus channel =>
          have bound := (SourceInitialIDs.rootIndex (InterfaceAlias.Root.request bus channel)).isLt
          change 0 < SourceInitialIDs.rootID (.request bus channel) ∧
            SourceInitialIDs.rootID (.request bus channel) ≤ _
          simp only [SourceInitialIDs.rootID, Cursor.lastID, initial,
            List.length_nil, Nat.add_zero, SourceInitialIDs.rootCount]
          constructor <;> omega
      | wire => simp [initial] at membership
  | internal role => simp [initial] at membership

end Controller.Native.SourceController


namespace Controller.Native.SourceController

/-- Bounded source IDs enumerate exactly the circuit's final finite variable universe. -/
theorem Cursor.sourceID_coverage (cursor : Cursor parameters) (source : ℕ)
    (positive : 0 < source) (bounded : source ≤ cursor.lastID) :
    ∃! coordinate : Fin cursor.toState.count, SourceObservation.sourceID coordinate = source := by
  have count := cursor.toState_count
  let coordinate : Fin cursor.toState.count := ⟨source - 1, by omega⟩
  refine ⟨coordinate, ?_, ?_⟩
  · simp only [SourceObservation.sourceID, coordinate]
    omega
  · intro other equal
    apply Fin.ext
    simp only [SourceObservation.sourceID] at equal
    dsimp [coordinate]
    omega

/-- Exact source-row identity also identifies models on the corresponding finite ID universe. -/
theorem Cursor.source_model_iff (cursor : Cursor parameters) (ordered : cursor.Ordered)
    (assignment : ℕ → Bool) :
    CNF.Satisfies (assignment ∘ SourceObservation.sourceID) cursor.toState.circuit.formula ↔
      CNF.Satisfies assignment (CNF.ofClauses (cursor.entries.flatMap fun entry => entry.producer.rows)) := by
  rw [← cursor.source_rows ordered]
  exact (CNF.satisfies_relabel SourceObservation.sourceID assignment cursor.toState.circuit.formula).symm

end Controller.Native.SourceController


namespace Controller.Native.SourceController

/-- The full retained source equation CNF asserts exactly each actual generated producer equation. -/
theorem equationFormula_iff (parameters : Parameters) (assignment : ℕ → Bool) :
    CNF.Satisfies assignment (equationFormula parameters) ↔
      ∀ entry ∈ (compile parameters).entries,
        CNF.literalValue assignment entry.producer.output = entry.producer.gate.eval assignment := by
  have source := Bounded.satisfies_producer_rows_iff
    ((compile parameters).entries.map Entry.producer) assignment
  simpa [equationFormula, List.flatMap_map] using source

end Controller.Native.SourceController


namespace Controller.Native.SourceController

/-- Initial physical roots remain available at every allocation stage. -/
def Cursor.PrimaryAssigned (cursor : Cursor parameters) : Prop :=
  (∀ channel, .primary (.enable channel) ∈ cursor.assigned) ∧
    (∀ bus channel, .primary (.request bus channel) ∈ cursor.assigned)

structure Cursor.Ready (cursor : Cursor parameters) : Prop where
  ordered : cursor.Ordered
  bounded : cursor.AssignedBounded
  primary : cursor.PrimaryAssigned

theorem Cursor.ready_assign (cursor : Cursor parameters)
    (slot : Controller.Native.Variable parameters) (handle : CNF.Literal ℕ)
    (ready : cursor.Ready) (valid : 0 < handle.1 ∧ handle.1 ≤ cursor.lastID) :
    (cursor.assign slot handle).Ready := by
  refine ⟨cursor.ordered_assign _ _ ready.ordered,
    cursor.assignedBounded_assign _ _ ready.bounded valid, ?_⟩
  constructor
  · intro channel
    rw [Cursor.assign_assigned]
    exact List.mem_append_left _ (ready.primary.1 channel)
  · intro bus channel
    rw [Cursor.assign_assigned]
    exact List.mem_append_left _ (ready.primary.2 bus channel)

theorem Cursor.ready_emitNative (cursor : Cursor parameters)
    (slot : Controller.Native.Variable parameters) (gate : CNF.Gate ℕ)
    (ready : cursor.Ready) (inputs : SourceSerialFold.HandlesBounded cursor.lastID gate.inputs) :
    (cursor.emitNative slot gate).Ready := by
  refine ⟨cursor.ordered_emitNative _ _ ready.ordered inputs,
    cursor.assignedBounded_emitNative _ _ ready.bounded, ?_⟩
  constructor
  · intro channel
    rw [Cursor.emitNative_assigned]
    exact List.mem_append_left _ (ready.primary.1 channel)
  · intro bus channel
    rw [Cursor.emitNative_assigned]
    exact List.mem_append_left _ (ready.primary.2 bus channel)

theorem Cursor.ready_foldNative (cursor : Cursor parameters)
    (slot : Controller.Native.Variable parameters) (junction : Bounded.Junction)
    (inputs : List (CNF.Literal ℕ)) (ready : cursor.Ready)
    (bounded : SourceSerialFold.HandlesBounded cursor.lastID inputs) :
    (cursor.foldNative slot junction inputs).Ready := by
  refine ⟨cursor.ordered_foldNative _ _ _ ready.ordered bounded,
    cursor.assignedBounded_foldNative _ _ _ ready.bounded bounded, ?_⟩
  constructor
  · intro channel
    rw [Cursor.foldNative_assigned]
    exact List.mem_append_left _ (ready.primary.1 channel)
  · intro bus channel
    rw [Cursor.foldNative_assigned]
    exact List.mem_append_left _ (ready.primary.2 bus channel)

theorem initial_ready (parameters : Parameters) : (initial parameters).Ready := by
  refine ⟨initial_ordered parameters, initial_assignedBounded parameters, ?_⟩
  constructor <;> intros <;> simp [initial]

theorem ready_foldl (items : List α) (step : Cursor parameters → α → Cursor parameters)
    (preserves : ∀ cursor item, cursor.Ready → (step cursor item).Ready)
    (cursor : Cursor parameters) (ready : cursor.Ready) : (items.foldl step cursor).Ready := by
  induction items generalizing cursor with
  | nil => exact ready
  | cons head tail inductionHypothesis => exact inductionHypothesis _ (preserves cursor head ready)

/-- This is the first loop of `firstArrays`, with no independently supplied ID map. -/
def firstTermStep (parameters : Parameters) (cursor : Cursor parameters)
    (channel : Fin parameters.channels) : Cursor parameters :=
  let healthy := Controller.Native.Variable.internal (.term .healthy parameters.firstBus channel)
  let faulty := Controller.Native.Variable.internal (.term .faulty parameters.firstBus channel)
  let emitted := cursor.emitNative healthy
    (.and [cursor.slots (.primary (.enable channel)), cursor.slots (.primary (.request parameters.firstBus channel))])
  emitted.assign faulty (emitted.slots healthy)

def firstTerms (parameters : Parameters) : Cursor parameters :=
  (List.finRange parameters.channels).foldl (firstTermStep parameters) (initial parameters)

theorem firstTermStep_ready (parameters : Parameters) (cursor : Cursor parameters)
    (channel : Fin parameters.channels) (ready : cursor.Ready) :
    (firstTermStep parameters cursor channel).Ready := by
  have enable := ready.bounded (.primary (.enable channel)) (ready.primary.1 channel)
  have request := ready.bounded (.primary (.request parameters.firstBus channel))
    (ready.primary.2 parameters.firstBus channel)
  have inputs : SourceSerialFold.HandlesBounded cursor.lastID
      (CNF.Gate.and [cursor.slots (.primary (.enable channel)),
        cursor.slots (.primary (.request parameters.firstBus channel))]).inputs := by
    intro handle member
    simp only [CNF.Gate.inputs, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact enable
    · exact request
  let healthy := Controller.Native.Variable.internal (.term .healthy parameters.firstBus channel)
  let emitted := cursor.emitNative healthy
    (.and [cursor.slots (.primary (.enable channel)), cursor.slots (.primary (.request parameters.firstBus channel))])
  have emittedReady : emitted.Ready := cursor.ready_emitNative healthy _ ready inputs
  apply emitted.ready_assign _ _ emittedReady
  exact emittedReady.bounded healthy (by simp [emitted, Cursor.emitNative_assigned])

theorem firstTerms_ready (parameters : Parameters) : (firstTerms parameters).Ready :=
  ready_foldl _ _ (fun cursor channel ready => firstTermStep_ready parameters cursor channel ready)
    _ (initial_ready parameters)

theorem firstTerms_assigned (parameters : Parameters) :
    (firstTerms parameters).assigned = (initial parameters).assigned ++
      (List.finRange parameters.channels).flatMap (fun channel =>
        [.internal (.term .healthy parameters.firstBus channel), .internal (.term .faulty parameters.firstBus channel)]) := by
  unfold firstTerms
  apply assigned_foldl
  intro cursor channel
  simp [firstTermStep, Cursor.emitNative, Cursor.emit, Cursor.assign, List.append_assoc]

/-- The old source definition and the separately checked first-loop stage are identical. -/
theorem firstArrays_eq (parameters : Parameters) :
    firstArrays parameters =
      (List.finRange parameters.channels).foldl (fun cursor channel =>
        let healthy := Controller.Native.Variable.internal (.absent .healthy parameters.firstBus channel)
        let faulty := Controller.Native.Variable.internal (.absent .faulty parameters.firstBus channel)
        let emitted := cursor.emitNative healthy
          (.not (cursor.slots (.internal (.term .healthy parameters.firstBus channel))))
        emitted.assign faulty (emitted.slots healthy)) (firstTerms parameters) := rfl

end Controller.Native.SourceController


namespace Controller.Native.SourceController

def firstAbsentStep (parameters : Parameters) (cursor : Cursor parameters)
    (channel : Fin parameters.channels) : Cursor parameters :=
  let healthy := Controller.Native.Variable.internal (.absent .healthy parameters.firstBus channel)
  let faulty := Controller.Native.Variable.internal (.absent .faulty parameters.firstBus channel)
  let emitted := cursor.emitNative healthy
    (.not (cursor.slots (.internal (.term .healthy parameters.firstBus channel))))
  emitted.assign faulty (emitted.slots healthy)

theorem firstAbsentStep_assigned (parameters : Parameters) (cursor : Cursor parameters)
    (channel : Fin parameters.channels) :
    (firstAbsentStep parameters cursor channel).assigned = cursor.assigned ++
      [.internal (.absent .healthy parameters.firstBus channel),
        .internal (.absent .faulty parameters.firstBus channel)] := by
  simp [firstAbsentStep, Cursor.emitNative, Cursor.emit, Cursor.assign, List.append_assoc]

theorem firstAbsentStep_ready (parameters : Parameters) (cursor : Cursor parameters)
    (channel : Fin parameters.channels) (ready : cursor.Ready)
    (available : .internal (.term .healthy parameters.firstBus channel) ∈ cursor.assigned) :
    (firstAbsentStep parameters cursor channel).Ready := by
  have term := ready.bounded (.internal (.term .healthy parameters.firstBus channel)) available
  have inputs : SourceSerialFold.HandlesBounded cursor.lastID
      (CNF.Gate.not (cursor.slots (.internal (.term .healthy parameters.firstBus channel)))).inputs := by
    intro handle member
    simp only [CNF.Gate.inputs, List.mem_singleton] at member
    subst handle
    exact term
  let healthy := Controller.Native.Variable.internal (.absent .healthy parameters.firstBus channel)
  let emitted := cursor.emitNative healthy
    (.not (cursor.slots (.internal (.term .healthy parameters.firstBus channel))))
  have emittedReady : emitted.Ready := cursor.ready_emitNative healthy _ ready inputs
  apply emitted.ready_assign _ _ emittedReady
  exact emittedReady.bounded healthy (by simp [emitted, Cursor.emitNative_assigned])

/-- Both first-bus copies share actual allocated handles, and every source read is already valid. -/
theorem firstArrays_ready (parameters : Parameters) : (firstArrays parameters).Ready := by
  have startTerms : ∀ channel, .internal (.term .healthy parameters.firstBus channel) ∈
      (firstTerms parameters).assigned := by
    intro channel
    rw [firstTerms_assigned]
    apply List.mem_append_right
    exact List.mem_flatMap.mpr ⟨channel, by simp, by simp⟩
  have preserves : ∀ items : List (Fin parameters.channels), ∀ cursor : Cursor parameters,
      cursor.Ready → (∀ channel, .internal (.term .healthy parameters.firstBus channel) ∈ cursor.assigned) →
      (items.foldl (firstAbsentStep parameters) cursor).Ready ∧
        (∀ channel, .internal (.term .healthy parameters.firstBus channel) ∈
          (items.foldl (firstAbsentStep parameters) cursor).assigned) := by
    intro items
    induction items with
    | nil => intro cursor ready available; exact ⟨ready, available⟩
    | cons head tail inductionHypothesis =>
        intro cursor ready available
        apply inductionHypothesis
        · exact firstAbsentStep_ready parameters cursor head ready (available head)
        · intro channel
          rw [firstAbsentStep_assigned]
          exact List.mem_append_left _ (available channel)
  rw [firstArrays_eq]
  change ((List.finRange parameters.channels).foldl (firstAbsentStep parameters) (firstTerms parameters)).Ready
  exact (preserves _ _ (firstTerms_ready parameters) startTerms).1

end Controller.Native.SourceController


namespace Controller.Native.SourceController

theorem Cursor.ready_inputs (cursor : Cursor parameters) (ready : cursor.Ready)
    (roles : List (Controller.Native.Variable parameters))
    (available : ∀ role ∈ roles, role ∈ cursor.assigned) :
    SourceSerialFold.HandlesBounded cursor.lastID (roles.map cursor.slots) := by
  intro handle membership
  obtain ⟨role, memberRole, rfl⟩ := List.mem_map.mp membership
  exact ready.bounded role (available role memberRole)

theorem Cursor.ready_emitNative_of_roles (cursor : Cursor parameters) (ready : cursor.Ready)
    (slot : Controller.Native.Variable parameters) (gate : CNF.Gate ℕ)
    (roles : List (Controller.Native.Variable parameters))
    (inputs : gate.inputs = roles.map cursor.slots)
    (available : ∀ role ∈ roles, role ∈ cursor.assigned) :
    (cursor.emitNative slot gate).Ready := by
  apply cursor.ready_emitNative _ _ ready
  rw [inputs]
  exact cursor.ready_inputs ready roles available

theorem Cursor.ready_foldNative_of_roles (cursor : Cursor parameters) (ready : cursor.Ready)
    (slot : Controller.Native.Variable parameters) (junction : Bounded.Junction)
    (roles : List (Controller.Native.Variable parameters))
    (available : ∀ role ∈ roles, role ∈ cursor.assigned) :
    (cursor.foldNative slot junction (roles.map cursor.slots)).Ready :=
  cursor.ready_foldNative slot junction _ ready (cursor.ready_inputs ready roles available)

/-- Interface allocation reads the shared first-array handles; W remains a fresh defined producer. -/
theorem interface_ready (parameters : Parameters) : (interface parameters).Ready := by
  let first := firstArrays parameters
  have firstReady : first.Ready := firstArrays_ready parameters
  have firstAbsent : ∀ channel, .internal (.absent .healthy parameters.firstBus channel) ∈ first.assigned := by
    intro channel
    simp [first, firstArrays_assigned, firstArrayRoles]
  let driverRoles := parameters.bridge.drivers.sort.map fun channel =>
    Controller.Native.Variable.internal (.absent .healthy parameters.firstBus channel)
  let driver := first.foldNative (.internal .driver) .conjunction (driverRoles.map first.slots)
  have driverReady : driver.Ready := by
    apply first.ready_foldNative_of_roles firstReady
    intro role membership
    obtain ⟨channel, memberChannel, rfl⟩ := List.mem_map.mp membership
    exact firstAbsent channel
  let remainingRoles := parameters.bridge.remaining.sort.map fun channel =>
    Controller.Native.Variable.internal (.absent .healthy parameters.firstBus channel)
  let remaining := driver.foldNative (.internal .remaining) .conjunction (remainingRoles.map driver.slots)
  have remainingReady : remaining.Ready := by
    apply driver.ready_foldNative_of_roles driverReady
    intro role membership
    obtain ⟨channel, memberChannel, rfl⟩ := List.mem_map.mp membership
    rw [Cursor.foldNative_assigned]
    exact List.mem_append_left _ (firstAbsent channel)
  let wire := remaining.emitNative (.primary .wire) (.and [remaining.slots (.internal .driver)])
  have wireReady : wire.Ready := by
    apply remaining.ready_emitNative_of_roles remainingReady _ _ [.internal .driver] rfl
    intro role member
    simp only [List.mem_singleton] at member
    subst role
    simp [remaining, driver, Cursor.foldNative_assigned]
  let healthyProduct := wire.emitNative (.internal (.firstProduct .healthy))
    (.and [wire.slots (.internal (.absent .healthy parameters.firstBus parameters.bridge.target)),
      wire.slots (.internal .driver), wire.slots (.internal .remaining)])
  have healthyProductReady : healthyProduct.Ready := by
    apply wire.ready_emitNative_of_roles wireReady _ _
      [.internal (.absent .healthy parameters.firstBus parameters.bridge.target),
        .internal .driver, .internal .remaining] rfl
    intro role member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · simp only [wire, remaining, driver, Cursor.emitNative_assigned, Cursor.foldNative_assigned,
        List.mem_append, List.mem_singleton]
      exact Or.inl (Or.inl (Or.inl (firstAbsent _)))
    · simp [wire, remaining, driver, Cursor.emitNative_assigned, Cursor.foldNative_assigned]
    · simp [wire, remaining, Cursor.emitNative_assigned, Cursor.foldNative_assigned]
  let healthyFlag := healthyProduct.emitNative (.internal (.flag .healthy parameters.firstBus))
    (.not (healthyProduct.slots (.internal (.firstProduct .healthy))))
  have healthyFlagReady : healthyFlag.Ready := by
    apply healthyProduct.ready_emitNative_of_roles healthyProductReady _ _
      [.internal (.firstProduct .healthy)] rfl
    intro role member
    simp only [List.mem_singleton] at member
    subst role
    simp [healthyProduct, Cursor.emitNative_assigned]
  let faultyProduct := healthyFlag.emitNative (.internal (.firstProduct .faulty))
    (.and [healthyFlag.slots (.primary .wire), healthyFlag.slots (.internal .driver),
      healthyFlag.slots (.internal .remaining)])
  have faultyProductReady : faultyProduct.Ready := by
    apply healthyFlag.ready_emitNative_of_roles healthyFlagReady _ _
      [.primary .wire, .internal .driver, .internal .remaining] rfl
    intro role member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;>
      simp [healthyFlag, healthyProduct, wire, remaining, driver,
        Cursor.emitNative_assigned, Cursor.foldNative_assigned]
  have lastReady := faultyProduct.ready_emitNative_of_roles faultyProductReady
    (.internal (.flag .faulty parameters.firstBus))
    (.not (faultyProduct.slots (.internal (.firstProduct .faulty))))
    [.internal (.firstProduct .faulty)] rfl (by
      intro role member
      simp only [List.mem_singleton] at member
      subst role
      simp [faultyProduct, Cursor.emitNative_assigned])
  simpa only [interface, first, driver, driverRoles, remaining, remainingRoles, wire,
    healthyProduct, healthyFlag, faultyProduct, List.map_map, Function.comp_def] using lastReady

end Controller.Native.SourceController


namespace Controller.Native.SourceController

/-- The initial mask loop uses only the shared first absent array and this side's first flag. -/
def Cursor.FirstAvailable (cursor : Cursor parameters) (side : Side) : Prop :=
  (.internal (.flag side parameters.firstBus) ∈ cursor.assigned) ∧
    (∀ channel, .internal (.absent side parameters.firstBus channel) ∈ cursor.assigned)

theorem Cursor.firstAvailable_emitNative (cursor : Cursor parameters) (side : Side)
    (slot : Controller.Native.Variable parameters) (gate : CNF.Gate ℕ)
    (available : cursor.FirstAvailable side) : (cursor.emitNative slot gate).FirstAvailable side := by
  constructor
  · rw [Cursor.emitNative_assigned]
    exact List.mem_append_left _ available.1
  · intro channel
    rw [Cursor.emitNative_assigned]
    exact List.mem_append_left _ (available.2 channel)

theorem interface_firstAvailable (parameters : Parameters) (side : Side) :
    (interface parameters).FirstAvailable side := by
  constructor
  · cases side <;> simp [interface_assigned, interfaceRoles]
  · intro channel
    cases side <;> simp [interface_assigned, firstArrayRoles]

theorem initialMasks_ready (parameters : Parameters) (side : Side) (cursor : Cursor parameters)
    (ready : cursor.Ready) (available : cursor.FirstAvailable side) :
    (initialMasks parameters side cursor).Ready ∧
      (initialMasks parameters side cursor).FirstAvailable side := by
  have invariant : ∀ items : List (Fin parameters.channels), ∀ state : Cursor parameters,
      state.Ready → state.FirstAvailable side →
      (items.foldl (fun state channel => state.emitNative (.internal (.mask side parameters.firstBus channel))
        (.xor (state.slots (.internal (.flag side parameters.firstBus)))
          (state.slots (.internal (.absent side parameters.firstBus channel))))) state).Ready ∧
      (items.foldl (fun state channel => state.emitNative (.internal (.mask side parameters.firstBus channel))
        (.xor (state.slots (.internal (.flag side parameters.firstBus)))
          (state.slots (.internal (.absent side parameters.firstBus channel))))) state).FirstAvailable side := by
    intro items
    induction items with
    | nil => intro state ready available; exact ⟨ready, available⟩
    | cons head tail inductionHypothesis =>
        intro state ready available
        apply inductionHypothesis
        · apply state.ready_emitNative_of_roles ready _ _
            [.internal (.flag side parameters.firstBus), .internal (.absent side parameters.firstBus head)] rfl
          intro role member
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl
          · exact available.1
          · exact available.2 head
        · exact state.firstAvailable_emitNative side _ _ available
  exact invariant _ _ ready available

/-- This stage begins at the derived concrete interface, rather than an externally supplied map. -/
theorem interface_initialMasks_ready (parameters : Parameters) (side : Side) :
    (initialMasks parameters side (interface parameters)).Ready :=
  (initialMasks_ready parameters side _ (interface_ready parameters)
    (interface_firstAvailable parameters side)).1

theorem initialMasks_all_masks_assigned (parameters : Parameters) (side : Side)
    (cursor : Cursor parameters) (channel : Fin parameters.channels) :
    .internal (.mask side parameters.firstBus channel) ∈ (initialMasks parameters side cursor).assigned := by
  simp [initialMasks_assigned, initialMaskRoles]

end Controller.Native.SourceController


namespace Controller.Native.SourceController

/-- The source term at bus b reads every already assigned mask from a smaller bus. -/
def Cursor.MasksBefore (cursor : Cursor parameters) (side : Side) (bus : Fin parameters.buses) : Prop :=
  ∀ earlier, earlier < bus → ∀ channel, .internal (.mask side earlier channel) ∈ cursor.assigned

theorem Cursor.masksBefore_foldNative (cursor : Cursor parameters) (side : Side)
    (bus : Fin parameters.buses) (slot : Controller.Native.Variable parameters)
    (junction : Bounded.Junction) (inputs : List (CNF.Literal ℕ))
    (before : cursor.MasksBefore side bus) : (cursor.foldNative slot junction inputs).MasksBefore side bus := by
  intro earlier smaller channel
  rw [Cursor.foldNative_assigned]
  exact List.mem_append_left _ (before earlier smaller channel)

def laterTermStep (parameters : Parameters) (side : Side) (bus : Fin parameters.buses)
    (cursor : Cursor parameters) (channel : Fin parameters.channels) : Cursor parameters :=
  cursor.foldNative (.internal (.term side bus channel)) .conjunction
    ([cursor.slots (.primary (.enable channel)), cursor.slots (.primary (.request bus channel))] ++
      ((List.finRange parameters.buses).filter (fun earlier => earlier < bus)).map fun earlier =>
        cursor.slots (.internal (.mask side earlier channel)))

def laterTerms (parameters : Parameters) (side : Side) (bus : Fin parameters.buses)
    (cursor : Cursor parameters) : Cursor parameters :=
  (List.finRange parameters.channels).foldl (laterTermStep parameters side bus) cursor

theorem laterTermStep_ready (parameters : Parameters) (side : Side) (bus : Fin parameters.buses)
    (cursor : Cursor parameters) (channel : Fin parameters.channels) (ready : cursor.Ready)
    (before : cursor.MasksBefore side bus) :
    (laterTermStep parameters side bus cursor channel).Ready ∧
      (laterTermStep parameters side bus cursor channel).MasksBefore side bus := by
  refine ⟨?_, cursor.masksBefore_foldNative side bus _ _ _ before⟩
  apply cursor.ready_foldNative _ _ _ ready
  intro handle membership
  simp only [List.mem_append] at membership
  rcases membership with membership | membership
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
    rcases membership with rfl | rfl
    · exact ready.bounded _ (ready.primary.1 channel)
    · exact ready.bounded _ (ready.primary.2 bus channel)
  · obtain ⟨earlier, earlierMember, rfl⟩ := List.mem_map.mp membership
    have smaller : earlier < bus := by simpa using (List.mem_filter.mp earlierMember).2
    exact ready.bounded _ (before earlier smaller channel)

theorem laterTerms_ready (parameters : Parameters) (side : Side) (bus : Fin parameters.buses)
    (cursor : Cursor parameters) (ready : cursor.Ready) (before : cursor.MasksBefore side bus) :
    (laterTerms parameters side bus cursor).Ready ∧
      (laterTerms parameters side bus cursor).MasksBefore side bus := by
  have invariant : ∀ items : List (Fin parameters.channels), ∀ state : Cursor parameters,
      state.Ready → state.MasksBefore side bus →
      (items.foldl (laterTermStep parameters side bus) state).Ready ∧
        (items.foldl (laterTermStep parameters side bus) state).MasksBefore side bus := by
    intro items
    induction items with
    | nil => intro state ready before; exact ⟨ready, before⟩
    | cons head tail inductionHypothesis =>
        intro state ready before
        have step := laterTermStep_ready parameters side bus state head ready before
        exact inductionHypothesis _ step.1 step.2
  exact invariant _ _ ready before

theorem laterTerms_assigned (parameters : Parameters) (side : Side) (bus : Fin parameters.buses)
    (cursor : Cursor parameters) :
    (laterTerms parameters side bus cursor).assigned = cursor.assigned ++
      (List.finRange parameters.channels).map (fun channel => .internal (.term side bus channel)) := by
  unfold laterTerms
  rw [assigned_foldl _ _ (fun channel => [.internal (.term side bus channel)]) (fun _ _ => rfl)]
  rw [flatMap_singleton]

/-- The second half of a bus reads all current terms and the newly allocated current flag. -/
def Cursor.CurrentBusAvailable (cursor : Cursor parameters) (side : Side) (bus : Fin parameters.buses) : Prop :=
  (.internal (.flag side bus) ∈ cursor.assigned) ∧
    (∀ channel, .internal (.term side bus channel) ∈ cursor.assigned)

def laterAbsentMaskStep (parameters : Parameters) (side : Side) (bus : Fin parameters.buses)
    (cursor : Cursor parameters) (channel : Fin parameters.channels) : Cursor parameters :=
  let absent := cursor.emitNative (.internal (.absent side bus channel))
    (.not (cursor.slots (.internal (.term side bus channel))))
  absent.emitNative (.internal (.mask side bus channel))
    (.xor (absent.slots (.internal (.flag side bus))) (absent.slots (.internal (.absent side bus channel))))

theorem laterAbsentMaskStep_assigned (parameters : Parameters) (side : Side) (bus : Fin parameters.buses)
    (cursor : Cursor parameters) (channel : Fin parameters.channels) :
    (laterAbsentMaskStep parameters side bus cursor channel).assigned = cursor.assigned ++
      [.internal (.absent side bus channel), .internal (.mask side bus channel)] := by
  simp [laterAbsentMaskStep, Cursor.emitNative_assigned, List.append_assoc]

theorem laterAbsentMaskStep_ready (parameters : Parameters) (side : Side) (bus : Fin parameters.buses)
    (cursor : Cursor parameters) (channel : Fin parameters.channels) (ready : cursor.Ready)
    (available : cursor.CurrentBusAvailable side bus) :
    (laterAbsentMaskStep parameters side bus cursor channel).Ready ∧
      (laterAbsentMaskStep parameters side bus cursor channel).CurrentBusAvailable side bus := by
  let absent := cursor.emitNative (.internal (.absent side bus channel))
    (.not (cursor.slots (.internal (.term side bus channel))))
  have absentReady : absent.Ready := by
    apply cursor.ready_emitNative_of_roles ready _ _ [.internal (.term side bus channel)] rfl
    intro role member
    simp only [List.mem_singleton] at member
    subst role
    exact available.2 channel
  refine ⟨?_, ?_⟩
  · apply absent.ready_emitNative_of_roles absentReady _ _
      [.internal (.flag side bus), .internal (.absent side bus channel)] rfl
    intro role member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · rw [Cursor.emitNative_assigned]
      exact List.mem_append_left _ available.1
    · simp [absent, Cursor.emitNative_assigned]
  · constructor
    · rw [laterAbsentMaskStep_assigned]
      exact List.mem_append_left _ available.1
    · intro other
      rw [laterAbsentMaskStep_assigned]
      exact List.mem_append_left _ (available.2 other)

theorem laterBus_ready (parameters : Parameters) (side : Side) (bus : Fin parameters.buses)
    (cursor : Cursor parameters) (ready : cursor.Ready) (before : cursor.MasksBefore side bus) :
    (laterBus parameters side bus cursor).Ready := by
  let terms := laterTerms parameters side bus cursor
  have termsReady : terms.Ready := (laterTerms_ready parameters side bus cursor ready before).1
  have allTerms : ∀ channel, .internal (.term side bus channel) ∈ terms.assigned := by
    intro channel
    simp [terms, laterTerms_assigned]
  let flag := terms.foldNative (.internal (.flag side bus)) .disjunction
    ((List.finRange parameters.channels).map fun channel => terms.slots (.internal (.term side bus channel)))
  have flagReady : flag.Ready := by
    apply terms.ready_foldNative _ _ _ termsReady
    intro handle membership
    obtain ⟨channel, memberChannel, rfl⟩ := List.mem_map.mp membership
    exact termsReady.bounded _ (allTerms channel)
  have flagAvailable : flag.CurrentBusAvailable side bus := by
    constructor
    · simp [flag, Cursor.foldNative_assigned]
    · intro channel
      rw [Cursor.foldNative_assigned]
      exact List.mem_append_left _ (allTerms channel)
  have invariant : ∀ items : List (Fin parameters.channels), ∀ state : Cursor parameters,
      state.Ready → state.CurrentBusAvailable side bus →
      (items.foldl (laterAbsentMaskStep parameters side bus) state).Ready ∧
        (items.foldl (laterAbsentMaskStep parameters side bus) state).CurrentBusAvailable side bus := by
    intro items
    induction items with
    | nil => intro state ready available; exact ⟨ready, available⟩
    | cons head tail inductionHypothesis =>
        intro state ready available
        have step := laterAbsentMaskStep_ready parameters side bus state head ready available
        exact inductionHypothesis _ step.1 step.2
  have final := (invariant (List.finRange parameters.channels) flag flagReady flagAvailable).1
  exact final

theorem laterBus_all_masks_assigned (parameters : Parameters) (side : Side) (bus : Fin parameters.buses)
    (cursor : Cursor parameters) (channel : Fin parameters.channels) :
    .internal (.mask side bus channel) ∈ (laterBus parameters side bus cursor).assigned := by
  simp [laterBus_assigned, laterBusRoles]

end Controller.Native.SourceController


namespace Controller.Native.SourceController

theorem laterBus_preserves_assigned (parameters : Parameters) (side : Side)
    (bus : Fin parameters.buses) (cursor : Cursor parameters)
    (role : Controller.Native.Variable parameters) (available : role ∈ cursor.assigned) :
    role ∈ (laterBus parameters side bus cursor).assigned := by
  rw [laterBus_assigned]
  exact List.mem_append_left _ available

/-- Remaining masks may be absent only when their bus is still in the increasing work list. -/
def Cursor.MaskCoverage (cursor : Cursor parameters) (side : Side)
    (buses : List (Fin parameters.buses)) : Prop :=
  ∀ bus ∈ buses, ∀ earlier, earlier < bus → ∀ channel,
    .internal (.mask side earlier channel) ∈ cursor.assigned ∨ earlier ∈ buses

/-- An increasing bus traversal converts the work-list coverage invariant into actual prior reads. -/
theorem orderedBuses_ready (parameters : Parameters) (side : Side)
    (buses : List (Fin parameters.buses)) (ascending : buses.Pairwise (· < ·))
    (cursor : Cursor parameters) (ready : cursor.Ready) (coverage : cursor.MaskCoverage side buses) :
    (buses.foldl (fun cursor bus => laterBus parameters side bus cursor) cursor).Ready := by
  have ranked : ∀ items : List (Fin parameters.buses), items.Pairwise (· < ·) →
      ∀ state : Cursor parameters, state.Ready → state.MaskCoverage side items →
      (items.foldl (fun state bus => laterBus parameters side bus state) state).Ready := by
    intro items
    induction items with
    | nil => intro ascending state ready coverage; exact ready
    | cons head tail inductionHypothesis =>
        intro ascending state ready coverage
        obtain ⟨headSmaller, tailAscending⟩ := List.pairwise_cons.mp ascending
        have before : state.MasksBefore side head := by
          intro earlier smaller channel
          rcases coverage head (by simp) earlier smaller channel with available | membership
          · exact available
          · simp only [List.mem_cons] at membership
            rcases membership with equal | memberTail
            · subst earlier
              exact False.elim ((lt_irrefl head) smaller)
            · exact False.elim ((lt_asymm smaller) (headSmaller earlier memberTail))
        have nextReady := laterBus_ready parameters side head state ready before
        have nextCoverage : (laterBus parameters side head state).MaskCoverage side tail := by
          intro bus memberTail earlier smaller channel
          rcases coverage bus (List.mem_cons_of_mem head memberTail) earlier smaller channel with available | membership
          · exact Or.inl (laterBus_preserves_assigned parameters side head state _ available)
          · simp only [List.mem_cons] at membership
            rcases membership with equal | memberRest
            · subst earlier
              exact Or.inl (laterBus_all_masks_assigned parameters side head state channel)
            · exact Or.inr memberRest
        exact inductionHypothesis tailAscending _ nextReady nextCoverage
  exact ranked buses ascending cursor ready coverage

/-- This is precisely the source's positive-bus work list, with zero omitted. -/
def positiveBuses (parameters : Parameters) : List (Fin parameters.buses) :=
  (List.finRange parameters.buses).filter fun bus => bus.val != 0

theorem positiveBuses_ascending (parameters : Parameters) :
    (positiveBuses parameters).Pairwise (· < ·) :=
  List.Pairwise.filter _ (List.pairwise_lt_finRange parameters.buses)

theorem initialMasks_positiveCoverage (parameters : Parameters) (side : Side)
    (cursor : Cursor parameters) :
    (initialMasks parameters side cursor).MaskCoverage side (positiveBuses parameters) := by
  intro bus memberBus earlier smaller channel
  by_cases zero : earlier.val = 0
  · have first : earlier = parameters.firstBus := by
      apply Fin.ext
      simp [Parameters.firstBus, zero]
    subst earlier
    exact Or.inl (initialMasks_all_masks_assigned parameters side cursor channel)
  · apply Or.inr
    simp [positiveBuses, zero]

/-- Every source later-bus read is now justified by its actual earlier mask-producing stage. -/
theorem initialMasks_laterBuses_ready (parameters : Parameters) (side : Side)
    (cursor : Cursor parameters) (ready : cursor.Ready) (available : cursor.FirstAvailable side) :
    ((positiveBuses parameters).foldl (fun cursor bus => laterBus parameters side bus cursor)
      (initialMasks parameters side cursor)).Ready :=
  orderedBuses_ready parameters side _ (positiveBuses_ascending parameters) _
    (initialMasks_ready parameters side cursor ready available).1
    (initialMasks_positiveCoverage parameters side cursor)

end Controller.Native.SourceController


namespace Controller.Native.SourceController

/-- Every principal bus flag used by the auxiliary negation stage is present. -/
def Cursor.FlagsAvailable (cursor : Cursor parameters) (side : Side) : Prop :=
  ∀ bus, .internal (.flag side bus) ∈ cursor.assigned

theorem initialMasks_laterBuses_flags (parameters : Parameters) (side : Side)
    (cursor : Cursor parameters) (available : cursor.FirstAvailable side) :
    ((positiveBuses parameters).foldl (fun cursor bus => laterBus parameters side bus cursor)
      (initialMasks parameters side cursor)).FlagsAvailable side := by
  intro bus
  rw [assigned_foldl _ _ (laterBusRoles parameters side)
    (fun cursor bus => laterBus_assigned parameters side bus cursor)]
  by_cases zero : bus.val = 0
  · have first : bus = parameters.firstBus := by
      apply Fin.ext
      simp [Parameters.firstBus, zero]
    subst bus
    apply List.mem_append_left
    rw [initialMasks_assigned]
    exact List.mem_append_left _ available.1
  · apply List.mem_append_right
    apply List.mem_flatMap.mpr
    refine ⟨bus, ?_, ?_⟩
    · simp [positiveBuses, zero]
    · simp [laterBusRoles]

theorem Cursor.ready_emit (cursor : Cursor parameters) (owner : Owner parameters)
    (gate : CNF.Gate ℕ) (ready : cursor.Ready)
    (inputs : SourceSerialFold.HandlesBounded cursor.lastID gate.inputs) :
    (cursor.emit owner gate).2.Ready :=
  ⟨cursor.ordered_emit _ _ ready.ordered inputs,
    cursor.assignedBounded_emit _ _ ready.bounded, ready.primary⟩

/-- Exact retained source step: a private NOT producer and its auxiliary handle update. -/
def negateFlagStep (parameters : Parameters) (side : Side)
    (cursor : Cursor parameters) (bus : Fin parameters.buses) : Cursor parameters :=
  let emitted := cursor.emit (.negatedFlag side bus)
    (.not (cursor.slots (.internal (.flag side bus))))
  { emitted.2 with negated := (Function.update emitted.2.negated side
      (Function.update (emitted.2.negated side) bus emitted.1)) }

theorem negateFlags_eq (parameters : Parameters) (side : Side) (cursor : Cursor parameters) :
    negateFlags parameters side cursor =
      (List.finRange parameters.buses).foldl (negateFlagStep parameters side) cursor := rfl

theorem negateFlagStep_lastID (parameters : Parameters) (side : Side)
    (cursor : Cursor parameters) (bus : Fin parameters.buses) :
    (negateFlagStep parameters side cursor bus).lastID = cursor.lastID + 1 := by
  simp [negateFlagStep, Cursor.emit, Cursor.lastID, Nat.add_assoc]

theorem negateFlagStep_ready (parameters : Parameters) (side : Side)
    (cursor : Cursor parameters) (bus : Fin parameters.buses)
    (ready : cursor.Ready) (flags : cursor.FlagsAvailable side) :
    (negateFlagStep parameters side cursor bus).Ready ∧
      (negateFlagStep parameters side cursor bus).FlagsAvailable side := by
  have emitted := cursor.ready_emit (.negatedFlag side bus)
    (.not (cursor.slots (.internal (.flag side bus)))) ready (by
      intro handle member
      simp only [CNF.Gate.inputs, List.mem_singleton] at member
      subst handle
      exact ready.bounded _ (flags bus))
  exact ⟨⟨emitted.ordered, emitted.bounded, emitted.primary⟩, flags⟩

/-- A private negated-flag handle is positive and within the actual retained producer prefix. -/
def Cursor.NegatedBound (cursor : Cursor parameters) (side : Side)
    (bus : Fin parameters.buses) : Prop :=
  0 < (cursor.negated side bus).1 ∧ (cursor.negated side bus).1 ≤ cursor.lastID

theorem negateFlagStep_bound (parameters : Parameters) (side : Side)
    (cursor : Cursor parameters) (bus other : Fin parameters.buses)
    (valid : cursor.NegatedBound side other ∨ other = bus) :
    (negateFlagStep parameters side cursor bus).NegatedBound side other := by
  rw [Cursor.NegatedBound, negateFlagStep_lastID]
  by_cases equal : other = bus
  · subst other
    simp [negateFlagStep, Cursor.emit]
  · have prior : cursor.NegatedBound side other := valid.resolve_right equal
    have upper := prior.2
    simpa [negateFlagStep, Cursor.emit, equal, Cursor.NegatedBound] using
      (show 0 < (cursor.negated side other).1 ∧
        (cursor.negated side other).1 ≤ cursor.lastID + 1 from
        ⟨prior.1, by omega⟩)

/-- A processed bus supplies its handle; each subsequent source step preserves that bound. -/
theorem negateList_ready_bounds (parameters : Parameters) (side : Side)
    (buses : List (Fin parameters.buses)) (cursor : Cursor parameters)
    (ready : cursor.Ready) (flags : cursor.FlagsAvailable side) :
    (buses.foldl (negateFlagStep parameters side) cursor).Ready ∧
      (buses.foldl (negateFlagStep parameters side) cursor).FlagsAvailable side ∧
      (∀ bus, cursor.NegatedBound side bus ∨ bus ∈ buses →
        (buses.foldl (negateFlagStep parameters side) cursor).NegatedBound side bus) := by
  have invariant : ∀ items : List (Fin parameters.buses), ∀ state : Cursor parameters,
      state.Ready → state.FlagsAvailable side →
      (items.foldl (negateFlagStep parameters side) state).Ready ∧
      (items.foldl (negateFlagStep parameters side) state).FlagsAvailable side ∧
      (∀ bus, state.NegatedBound side bus ∨ bus ∈ items →
        (items.foldl (negateFlagStep parameters side) state).NegatedBound side bus) := by
    intro items
    induction items with
    | nil =>
        intro state ready flags
        refine ⟨ready, flags, ?_⟩
        intro bus valid
        exact valid.resolve_right (by simp)
    | cons head tail inductionHypothesis =>
        intro state ready flags
        have next := negateFlagStep_ready parameters side state head ready flags
        have rest := inductionHypothesis _ next.1 next.2
        refine ⟨rest.1, rest.2.1, ?_⟩
        intro bus valid
        apply rest.2.2
        rcases valid with prior | member
        · exact Or.inl (negateFlagStep_bound parameters side state head bus (Or.inl prior))
        · simp only [List.mem_cons] at member
          rcases member with equal | memberTail
          · exact Or.inl (negateFlagStep_bound parameters side state head bus (Or.inr equal))
          · exact Or.inr memberTail
  exact invariant buses cursor ready flags

/-- The auxiliary map is read-ready only after every actual bus has been processed. -/
def Cursor.NegatedAvailable (cursor : Cursor parameters) (side : Side) : Prop :=
  ∀ bus, cursor.NegatedBound side bus

theorem negateFlags_ready (parameters : Parameters) (side : Side)
    (cursor : Cursor parameters) (ready : cursor.Ready) (flags : cursor.FlagsAvailable side) :
    (negateFlags parameters side cursor).Ready ∧
      (negateFlags parameters side cursor).NegatedAvailable side := by
  rw [negateFlags_eq]
  have result := negateList_ready_bounds parameters side (List.finRange parameters.buses)
    cursor ready flags
  refine ⟨result.1, ?_⟩
  intro bus
  exact result.2.2 bus (Or.inr (by simp))

end Controller.Native.SourceController


namespace Controller.Native.SourceController

theorem Cursor.negatedAvailable_emitNative (cursor : Cursor parameters) (side : Side)
    (slot : Controller.Native.Variable parameters) (gate : CNF.Gate ℕ)
    (available : cursor.NegatedAvailable side) :
    (cursor.emitNative slot gate).NegatedAvailable side := by
  intro bus
  have valid := available bus
  change 0 < (cursor.negated side bus).1 ∧ (cursor.negated side bus).1 ≤ _
  simp only [Cursor.emitNative, Cursor.assign, Cursor.emit, Cursor.lastID,
    List.length_append, List.length_singleton]
  unfold Cursor.NegatedBound Cursor.lastID at valid
  exact ⟨valid.1, by omega⟩

theorem Cursor.negatedAvailable_foldNative (cursor : Cursor parameters) (side : Side)
    (slot : Controller.Native.Variable parameters) (junction : Bounded.Junction)
    (inputs : List (CNF.Literal ℕ)) (available : cursor.NegatedAvailable side) :
    (cursor.foldNative slot junction inputs).NegatedAvailable side := by
  intro bus
  have valid := available bus
  change 0 < (cursor.negated side bus).1 ∧ (cursor.negated side bus).1 ≤ _
  simp only [Cursor.foldNative, Cursor.assign, Cursor.lastID,
    List.length_append, List.length_map, List.length_zipIdx]
  unfold Cursor.NegatedBound Cursor.lastID at valid
  exact ⟨valid.1, by omega⟩

/-- Exact source OR step consumes a shared private NOT flag and a physical request role. -/
def eligibleGuardStep (parameters : Parameters) (side : Side)
    (channel : Fin parameters.channels) (cursor : Cursor parameters)
    (bus : Fin parameters.buses) : Cursor parameters :=
  cursor.emitNative (.internal (.qualifierGuard side bus channel))
    (.or [cursor.negated side bus, cursor.slots (.primary (.request bus channel))])

theorem eligibleGuardStep_ready (parameters : Parameters) (side : Side)
    (channel : Fin parameters.channels) (cursor : Cursor parameters)
    (bus : Fin parameters.buses) (ready : cursor.Ready)
    (available : cursor.NegatedAvailable side) :
    (eligibleGuardStep parameters side channel cursor bus).Ready ∧
      (eligibleGuardStep parameters side channel cursor bus).NegatedAvailable side := by
  constructor
  · apply cursor.ready_emitNative _ _ ready
    intro handle member
    simp only [CNF.Gate.inputs, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact available bus
    · exact ready.bounded _ (ready.primary.2 bus channel)
  · exact cursor.negatedAvailable_emitNative side _ _ available

theorem eligible_ready (parameters : Parameters) (side : Side)
    (channel : Fin parameters.channels) (cursor : Cursor parameters)
    (ready : cursor.Ready) (available : cursor.NegatedAvailable side) :
    (eligible parameters side channel cursor).Ready ∧
      (eligible parameters side channel cursor).NegatedAvailable side := by
  let guarded := (List.finRange parameters.buses).foldl
    (eligibleGuardStep parameters side channel) cursor
  have invariant : ∀ items : List (Fin parameters.buses), ∀ state : Cursor parameters,
      state.Ready → state.NegatedAvailable side →
      (items.foldl (eligibleGuardStep parameters side channel) state).Ready ∧
        (items.foldl (eligibleGuardStep parameters side channel) state).NegatedAvailable side := by
    intro items
    induction items with
    | nil => intro state ready available; exact ⟨ready, available⟩
    | cons head tail inductionHypothesis =>
        intro state ready available
        have next := eligibleGuardStep_ready parameters side channel state head ready available
        exact inductionHypothesis _ next.1 next.2
  have guardState := invariant (List.finRange parameters.buses) cursor ready available
  have guardRoles : ∀ bus, .internal (.qualifierGuard side bus channel) ∈ guarded.assigned := by
    intro bus
    dsimp [guarded]
    rw [assigned_foldl _ _ (fun bus => [.internal (.qualifierGuard side bus channel)])
      (fun _ _ => rfl)]
    simp [flatMap_singleton]
  have outputReady : (guarded.foldNative (.internal (.qualifier side channel)) .conjunction
      (guarded.slots (.primary (.enable channel)) ::
        (List.finRange parameters.buses).map fun bus =>
          guarded.slots (.internal (.qualifierGuard side bus channel)))).Ready := by
    apply guarded.ready_foldNative _ _ _ guardState.1
    intro handle member
    simp only [List.mem_cons] at member
    rcases member with rfl | member
    · exact guardState.1.bounded _ (guardState.1.primary.1 channel)
    · obtain ⟨bus, _, rfl⟩ := List.mem_map.mp member
      exact guardState.1.bounded _ (guardRoles bus)
  exact ⟨outputReady, guarded.negatedAvailable_foldNative side _ _ _ guardState.2⟩

end Controller.Native.SourceController


namespace Controller.Native.SourceController

/-- Source tail read validity includes every bus, every shared negation and every qualifier. -/
theorem tail_ready (parameters : Parameters) (side : Side)
    (cursor : Cursor parameters) (ready : cursor.Ready) (first : cursor.FirstAvailable side) :
    (tail parameters side cursor).Ready := by
  let stages := (positiveBuses parameters).foldl
    (fun cursor bus => laterBus parameters side bus cursor) (initialMasks parameters side cursor)
  have stagesReady : stages.Ready := initialMasks_laterBuses_ready parameters side cursor ready first
  have flags : stages.FlagsAvailable side := initialMasks_laterBuses_flags parameters side cursor first
  have negated := negateFlags_ready parameters side stages stagesReady flags
  have invariant : ∀ items : List (Fin parameters.channels), ∀ state : Cursor parameters,
      state.Ready → state.NegatedAvailable side →
      (items.foldl (fun cursor channel => eligible parameters side channel cursor) state).Ready := by
    intro items
    induction items with
    | nil => intro state ready available; exact ready
    | cons head tail inductionHypothesis =>
        intro state ready available
        have next := eligible_ready parameters side head state ready available
        exact inductionHypothesis _ next.1 next.2
  exact invariant (List.finRange parameters.channels) _ negated.1 negated.2

theorem tail_firstAvailable (parameters : Parameters) (side other : Side)
    (cursor : Cursor parameters) (first : cursor.FirstAvailable other) :
    (tail parameters side cursor).FirstAvailable other := by
  constructor
  · rw [tail_assigned]
    exact List.mem_append_left _ first.1
  · intro channel
    rw [tail_assigned]
    exact List.mem_append_left _ (first.2 channel)

/-- Both original controller copies consume their actual source-order handle prefixes. -/
theorem controller_ready (parameters : Parameters) : (controller parameters).Ready := by
  apply tail_ready parameters .faulty
  · exact tail_ready parameters .healthy _ (interface_ready parameters)
      (interface_firstAvailable parameters .healthy)
  · exact tail_firstAvailable parameters .healthy .faulty _
      (interface_firstAvailable parameters .faulty)

end Controller.Native.SourceController


namespace Controller.Native.SourceController

theorem controller_assigned (parameters : Parameters) :
    (controller parameters).assigned = (interface parameters).assigned ++
      tailRoles parameters .healthy ++ tailRoles parameters .faulty := by
  rw [controller, tail_assigned, tail_assigned]

private theorem controller_tail_member (parameters : Parameters) (side : Side)
    (role : Controller.Native.Variable parameters) (member : role ∈ tailRoles parameters side) :
    role ∈ (controller parameters).assigned := by
  cases side <;> simp only [controller_assigned, List.mem_append] <;> tauto

theorem controller_flags_assigned (parameters : Parameters) (side : Side)
    (bus : Fin parameters.buses) :
    .internal (.flag side bus) ∈ (controller parameters).assigned := by
  by_cases first : bus = parameters.firstBus
  · subst bus
    have member := (interface_firstAvailable parameters side).1
    rw [controller_assigned]
    exact List.mem_append_left _ (List.mem_append_left _ member)
  · apply controller_tail_member parameters side
    have nonzero : bus.val ≠ 0 := by
      intro zero
      apply first
      apply Fin.ext
      simpa [Parameters.firstBus] using zero
    simp only [tailRoles, List.mem_append]
    apply Or.inl
    apply Or.inr
    exact List.mem_flatMap.mpr ⟨bus, by simp [nonzero], by simp [laterBusRoles]⟩

theorem controller_qualifiers_assigned (parameters : Parameters) (side : Side)
    (channel : Fin parameters.channels) :
    .internal (.qualifier side channel) ∈ (controller parameters).assigned := by
  apply controller_tail_member parameters side
  simp only [tailRoles, List.mem_append]
  apply Or.inr
  exact List.mem_flatMap.mpr ⟨channel, by simp, by simp [eligibleRoles]⟩

/-- The exact retained observation-role lists have no unassigned entries. -/
def Cursor.OldOutputsAvailable (cursor : Cursor parameters) : Prop :=
  ∀ side role, role ∈ SourceObservation.oldOutputRoles parameters side →
    .internal role ∈ cursor.assigned

theorem controller_oldOutputsAvailable (parameters : Parameters) :
    (controller parameters).OldOutputsAvailable := by
  intro side role member
  simp only [SourceObservation.oldOutputRoles, List.mem_append] at member
  rcases member with flags | qualifiers
  · obtain ⟨bus, _, rfl⟩ := List.mem_map.mp flags
    exact controller_flags_assigned parameters side bus
  · obtain ⟨channel, _, rfl⟩ := List.mem_map.mp qualifiers
    exact controller_qualifiers_assigned parameters side channel

theorem oldOutput_lookup_member (parameters : Parameters) (side : Side)
    (index : Fin (parameters.buses + parameters.channels)) :
    (SourceObservation.oldOutputRoles parameters side)[index.val]?.getD .driver ∈
      SourceObservation.oldOutputRoles parameters side := by
  have bound : index.val < (SourceObservation.oldOutputRoles parameters side).length := by
    simpa [SourceObservation.oldOutputRoles] using index.isLt
  rw [List.getElem?_eq_getElem bound]
  exact List.getElem_mem bound

/-- One exact retained XOR step; its private output is stored without assigning a native slot. -/
def oldDifferenceStep (parameters : Parameters) (cursor : Cursor parameters)
    (index : Fin (parameters.buses + parameters.channels)) : Cursor parameters :=
  let good := (SourceObservation.oldOutputRoles parameters .healthy)[index.val]?.getD .driver
  let bad := (SourceObservation.oldOutputRoles parameters .faulty)[index.val]?.getD .driver
  let emitted := cursor.emit (.oldDifference index)
    (.xor (cursor.slots (.internal good)) (cursor.slots (.internal bad)))
  { emitted.2 with oldDifferences := Function.update emitted.2.oldDifferences index emitted.1 }

theorem oldDifferenceStep_ready (parameters : Parameters) (cursor : Cursor parameters)
    (index : Fin (parameters.buses + parameters.channels)) (ready : cursor.Ready)
    (available : cursor.OldOutputsAvailable) :
    (oldDifferenceStep parameters cursor index).Ready ∧
      (oldDifferenceStep parameters cursor index).OldOutputsAvailable := by
  have emitted := cursor.ready_emit (.oldDifference index)
    (.xor (cursor.slots (.internal ((SourceObservation.oldOutputRoles parameters .healthy)[index.val]?.getD .driver)))
      (cursor.slots (.internal ((SourceObservation.oldOutputRoles parameters .faulty)[index.val]?.getD .driver)))) ready (by
    intro handle member
    simp only [CNF.Gate.inputs, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact ready.bounded _ (available _ _ (oldOutput_lookup_member parameters .healthy index))
    · exact ready.bounded _ (available _ _ (oldOutput_lookup_member parameters .faulty index)))
  exact ⟨⟨emitted.ordered, emitted.bounded, emitted.primary⟩, available⟩

end Controller.Native.SourceController


namespace Controller.Native.SourceController

def Cursor.OldDifferenceBound (cursor : Cursor parameters)
    (index : Fin (parameters.buses + parameters.channels)) : Prop :=
  0 < (cursor.oldDifferences index).1 ∧ (cursor.oldDifferences index).1 ≤ cursor.lastID

theorem oldDifferenceStep_lastID (parameters : Parameters) (cursor : Cursor parameters)
    (index : Fin (parameters.buses + parameters.channels)) :
    (oldDifferenceStep parameters cursor index).lastID = cursor.lastID + 1 := by
  simp [oldDifferenceStep, Cursor.emit, Cursor.lastID, Nat.add_assoc]

theorem oldDifferenceStep_bound (parameters : Parameters) (cursor : Cursor parameters)
    (index other : Fin (parameters.buses + parameters.channels))
    (valid : cursor.OldDifferenceBound other ∨ other = index) :
    (oldDifferenceStep parameters cursor index).OldDifferenceBound other := by
  rw [Cursor.OldDifferenceBound, oldDifferenceStep_lastID]
  by_cases equal : other = index
  · subst other
    simp [oldDifferenceStep, Cursor.emit]
  · have prior : cursor.OldDifferenceBound other := valid.resolve_right equal
    have upper := prior.2
    simpa [oldDifferenceStep, Cursor.emit, equal, Cursor.OldDifferenceBound] using
      (show 0 < (cursor.oldDifferences other).1 ∧
        (cursor.oldDifferences other).1 ≤ cursor.lastID + 1 from ⟨prior.1, by omega⟩)

def pairedOldOutputs (parameters : Parameters) (cursor : Cursor parameters) : Cursor parameters :=
  (List.finRange (parameters.buses + parameters.channels)).foldl
    (oldDifferenceStep parameters) cursor

theorem pairedOldOutputs_ready (parameters : Parameters) (cursor : Cursor parameters)
    (ready : cursor.Ready) (available : cursor.OldOutputsAvailable) :
    (pairedOldOutputs parameters cursor).Ready ∧
      (∀ index, (pairedOldOutputs parameters cursor).OldDifferenceBound index) := by
  have invariant : ∀ items : List (Fin (parameters.buses + parameters.channels)),
      ∀ state : Cursor parameters, state.Ready → state.OldOutputsAvailable →
      (items.foldl (oldDifferenceStep parameters) state).Ready ∧
      (items.foldl (oldDifferenceStep parameters) state).OldOutputsAvailable ∧
      (∀ index, state.OldDifferenceBound index ∨ index ∈ items →
        (items.foldl (oldDifferenceStep parameters) state).OldDifferenceBound index) := by
    intro items
    induction items with
    | nil =>
        intro state ready available
        refine ⟨ready, available, ?_⟩
        intro index valid
        exact valid.resolve_right (by simp)
    | cons head tail inductionHypothesis =>
        intro state ready available
        have next := oldDifferenceStep_ready parameters state head ready available
        have rest := inductionHypothesis _ next.1 next.2
        refine ⟨rest.1, rest.2.1, ?_⟩
        intro index valid
        apply rest.2.2
        rcases valid with prior | member
        · exact Or.inl (oldDifferenceStep_bound parameters state head index (Or.inl prior))
        · simp only [List.mem_cons] at member
          rcases member with equal | memberTail
          · exact Or.inl (oldDifferenceStep_bound parameters state head index (Or.inr equal))
          · exact Or.inr memberTail
  have result := invariant (List.finRange (parameters.buses + parameters.channels)) cursor ready available
  refine ⟨result.1, ?_⟩
  intro index
  exact result.2.2 index (Or.inr (by simp))

/-- Retaining old observations reads all stored private XORs and preserves their exact fold rows. -/
theorem originalObservations_ready (parameters : Parameters) (cursor : Cursor parameters)
    (ready : cursor.Ready) (available : cursor.OldOutputsAvailable) :
    (originalObservations parameters cursor).Ready := by
  let paired := pairedOldOutputs parameters cursor
  let inputs := (List.finRange (parameters.buses + parameters.channels)).map paired.oldDifferences
  have state := pairedOldOutputs_ready parameters cursor ready available
  have bounds : SourceSerialFold.HandlesBounded paired.lastID inputs := by
    intro handle member
    obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
    exact state.2 index
  have ordered := paired.ordered_foldNative (.internal .detected) .disjunction inputs
    state.1.ordered bounds
  refine ⟨?_, ?_, ?_⟩
  · let allocated := SourceSerialFold.allocate .disjunction paired.lastID inputs
    let retained : List (Entry parameters) := allocated.producers.zipIdx.map
      (fun pair => ⟨.oldDetected pair.2, pair.1⟩)
    change SourceSerialFold.Ordered (SourceInitialIDs.rootCount parameters)
      ((paired.entries ++ retained).map Entry.producer)
      (SourceInitialIDs.rootCount parameters + (paired.entries ++ retained).length)
    simpa [Cursor.Ordered, Cursor.foldNative, Cursor.assign, Cursor.lastID, retained, allocated,
      List.map_append, List.map_map, Function.comp_def] using ordered
  · intro role member
    have prior := state.1.bounded role member
    change 0 < (paired.slots role).1 ∧ (paired.slots role).1 ≤ _
    simp only [originalObservations, Cursor.lastID, List.length_append, List.length_map,
      List.length_zipIdx]
    change 0 < (paired.slots role).1 ∧
      (paired.slots role).1 ≤ SourceInitialIDs.rootCount parameters +
        (paired.entries.length + (SourceSerialFold.allocate .disjunction paired.lastID inputs).producers.length)
    have upper := prior.2
    change (paired.slots role).1 ≤ paired.lastID at upper
    unfold Cursor.lastID at upper
    exact ⟨prior.1, by omega⟩
  · exact state.1.primary

theorem controller_originalObservations_ready (parameters : Parameters) :
    (originalObservations parameters (controller parameters)).Ready :=
  originalObservations_ready parameters _ (controller_ready parameters)
    (controller_oldOutputsAvailable parameters)

end Controller.Native.SourceController


namespace Controller.Native.SourceController

/-- Decoder primary leaves refer to the already generated eligibility qualifiers. -/
def Cursor.QualifiersAvailable (cursor : Cursor parameters) (side : Side) : Prop :=
  ∀ channel, .internal (.qualifier side channel) ∈ cursor.assigned

theorem controller_originalObservations_qualifiers (parameters : Parameters) (side : Side) :
    (originalObservations parameters (controller parameters)).QualifiersAvailable side := by
  intro channel
  rw [originalObservations_assigned]
  exact controller_qualifiers_assigned parameters side channel

theorem Cursor.qualifiersAvailable_assign (cursor : Cursor parameters) (side : Side)
    (slot : Controller.Native.Variable parameters) (handle : CNF.Literal ℕ)
    (available : cursor.QualifiersAvailable side) :
    (cursor.assign slot handle).QualifiersAvailable side := by
  intro channel
  rw [Cursor.assign_assigned]
  exact List.mem_append_left _ (available channel)

theorem Cursor.qualifiersAvailable_emitNative (cursor : Cursor parameters) (side : Side)
    (slot : Controller.Native.Variable parameters) (gate : CNF.Gate ℕ)
    (available : cursor.QualifiersAvailable side) :
    (cursor.emitNative slot gate).QualifiersAvailable side := by
  intro channel
  rw [Cursor.emitNative_assigned]
  exact List.mem_append_left _ (available channel)

theorem Cursor.qualifiersAvailable_foldNative (cursor : Cursor parameters) (side : Side)
    (slot : Controller.Native.Variable parameters) (junction : Bounded.Junction)
    (inputs : List (CNF.Literal ℕ)) (available : cursor.QualifiersAvailable side) :
    (cursor.foldNative slot junction inputs).QualifiersAvailable side := by
  intro channel
  rw [Cursor.foldNative_assigned]
  exact List.mem_append_left _ (available channel)

/-- Retained private guard chains carry a positive bounded child through every signed read. -/
theorem guardChain_ready (parameters : Parameters) (side : Side)
    (node : Fin parameters.decoder.nodeCount) (child : CNF.Literal ℕ)
    (labels : List (Fin parameters.channels)) (cursor : Cursor parameters)
    (ready : cursor.Ready) (available : cursor.QualifiersAvailable side)
    (bounded : 0 < child.1 ∧ child.1 ≤ cursor.lastID) :
    (guardChain parameters side node child labels cursor).2.Ready ∧
      (guardChain parameters side node child labels cursor).2.QualifiersAvailable side ∧
      (0 < (guardChain parameters side node child labels cursor).1.1 ∧
        (guardChain parameters side node child labels cursor).1.1 ≤
          (guardChain parameters side node child labels cursor).2.lastID) := by
  have invariant : ∀ items : List (Fin parameters.channels × ℕ),
      ∀ handle : CNF.Literal ℕ, ∀ state : Cursor parameters,
      state.Ready → state.QualifiersAvailable side →
      (0 < handle.1 ∧ handle.1 ≤ state.lastID) →
      let result := items.foldl (fun result pair => result.2.emit (.guard side node pair.2)
        (.and [result.1, CNF.negate (result.2.slots (.internal (.qualifier side pair.1)))])) (handle, state)
      result.2.Ready ∧ result.2.QualifiersAvailable side ∧
        (0 < result.1.1 ∧ result.1.1 ≤ result.2.lastID) := by
    intro items
    induction items with
    | nil => intro handle state ready available bounded; exact ⟨ready, available, bounded⟩
    | cons head tail inductionHypothesis =>
        intro handle state ready available bounded
        let gate := CNF.Gate.and [handle, CNF.negate (state.slots (.internal (.qualifier side head.1)))]
        let emitted := state.emit (.guard side node head.2) gate
        have inputs : SourceSerialFold.HandlesBounded state.lastID gate.inputs := by
          intro input member
          simp only [gate, CNF.Gate.inputs, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl
          · exact bounded
          · simpa [CNF.negate, Std.Sat.Literal.negate] using ready.bounded _ (available head.1)
        have nextReady : emitted.2.Ready := state.ready_emit _ _ ready inputs
        have nextAvailable : emitted.2.QualifiersAvailable side := available
        have nextBound : 0 < emitted.1.1 ∧ emitted.1.1 ≤ emitted.2.lastID := by
          simp [emitted, Cursor.emit, Cursor.lastID, Nat.add_assoc]
        exact inductionHypothesis _ _ nextReady nextAvailable nextBound
  exact invariant labels.zipIdx child cursor ready available bounded

end Controller.Native.SourceController


namespace Controller.Native.SourceController

/-- Actual decoder dependencies are earlier indices of this source table. -/
def Cursor.DecoderBefore (cursor : Cursor parameters) (side : Side)
    (node : Fin parameters.decoder.nodeCount) : Prop :=
  ∀ child : Fin parameters.decoder.nodeCount, child < node →
    .internal (.decoder side child) ∈ cursor.assigned

/-- One source node consumes its intrinsic earlier references; input and empty-guard aliases emit no gate. -/
theorem decoderNode_ready (parameters : Parameters) (side : Side)
    (node : Fin parameters.decoder.nodeCount) (cursor : Cursor parameters)
    (ready : cursor.Ready) (available : cursor.QualifiersAvailable side)
    (before : cursor.DecoderBefore side node) :
    (decoderNode parameters side node cursor).Ready ∧
      (decoderNode parameters side node cursor).QualifiersAvailable side := by
  have childBound : ∀ child : Fin node.val,
      0 < (cursor.slots (.internal (.decoder side (parameters.decoder.childIndex node child)))).1 ∧
      (cursor.slots (.internal (.decoder side (parameters.decoder.childIndex node child)))).1 ≤ cursor.lastID := by
    intro child
    exact ready.bounded _ (before _ child.isLt)
  unfold decoderNode
  cases equation : parameters.decoder.node node with
  | zero =>
      exact ⟨cursor.ready_emitNative _ _ ready (by intro input member; simp [CNF.Gate.inputs] at member),
        cursor.qualifiersAvailable_emitNative side _ _ available⟩
  | input channel =>
      exact ⟨cursor.ready_assign _ _ ready (ready.bounded _ (available channel)),
        cursor.qualifiersAvailable_assign side _ _ available⟩
  | disj children =>
      constructor
      · apply cursor.ready_foldNative _ _ _ ready
        intro input member
        obtain ⟨child, _, rfl⟩ := List.mem_map.mp member
        exact childBound child
      · exact cursor.qualifiersAvailable_foldNative side _ _ _ available
  | guard child labels =>
      have result := guardChain_ready parameters side node _ labels cursor ready available (childBound child)
      exact ⟨Cursor.ready_assign _ _ _ result.1 result.2.2,
        Cursor.qualifiersAvailable_assign _ side _ _ result.2.1⟩
  | liveAnd left right =>
      constructor
      · apply cursor.ready_emitNative _ _ ready
        intro input member
        simp only [CNF.Gate.inputs, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · exact childBound left
        · exact childBound right
      · exact cursor.qualifiersAvailable_emitNative side _ _ available

end Controller.Native.SourceController


namespace Controller.Native.SourceController

def Cursor.DecoderCoverage (cursor : Cursor parameters) (side : Side)
    (nodes : List (Fin parameters.decoder.nodeCount)) : Prop :=
  ∀ node ∈ nodes, ∀ child, child < node →
    .internal (.decoder side child) ∈ cursor.assigned ∨ child ∈ nodes

theorem orderedDecoder_ready (parameters : Parameters) (side : Side)
    (nodes : List (Fin parameters.decoder.nodeCount)) (ascending : nodes.Pairwise (· < ·))
    (cursor : Cursor parameters) (ready : cursor.Ready)
    (available : cursor.QualifiersAvailable side) (coverage : cursor.DecoderCoverage side nodes) :
    (nodes.foldl (fun cursor node => decoderNode parameters side node cursor) cursor).Ready ∧
      (nodes.foldl (fun cursor node => decoderNode parameters side node cursor) cursor).QualifiersAvailable side := by
  have invariant : ∀ items : List (Fin parameters.decoder.nodeCount), items.Pairwise (· < ·) →
      ∀ state : Cursor parameters, state.Ready → state.QualifiersAvailable side →
      state.DecoderCoverage side items →
      (items.foldl (fun cursor node => decoderNode parameters side node cursor) state).Ready ∧
      (items.foldl (fun cursor node => decoderNode parameters side node cursor) state).QualifiersAvailable side := by
    intro items
    induction items with
    | nil => intro ascending state ready available coverage; exact ⟨ready, available⟩
    | cons head tail inductionHypothesis =>
        intro ascending state ready available coverage
        obtain ⟨headSmaller, tailAscending⟩ := List.pairwise_cons.mp ascending
        have before : state.DecoderBefore side head := by
          intro child smaller
          rcases coverage head (by simp) child smaller with assigned | member
          · exact assigned
          · simp only [List.mem_cons] at member
            rcases member with equal | memberTail
            · subst child
              exact False.elim ((lt_irrefl head) smaller)
            · exact False.elim ((lt_asymm smaller) (headSmaller child memberTail))
        have next := decoderNode_ready parameters side head state ready available before
        have nextCoverage : (decoderNode parameters side head state).DecoderCoverage side tail := by
          intro node memberTail child smaller
          rcases coverage node (List.mem_cons_of_mem head memberTail) child smaller with assigned | member
          · apply Or.inl
            rw [decoderNode_assigned]
            exact List.mem_append_left _ assigned
          · simp only [List.mem_cons] at member
            rcases member with equal | memberTail
            · subst child
              apply Or.inl
              simp [decoderNode_assigned]
            · exact Or.inr memberTail
        exact inductionHypothesis tailAscending _ next.1 next.2 nextCoverage
  exact invariant nodes ascending cursor ready available coverage

/-- Intrinsic child indices and finRange source order make both decoder traversals read-valid. -/
theorem attachDecoder_ready (parameters : Parameters) (side : Side) (cursor : Cursor parameters)
    (ready : cursor.Ready) (available : cursor.QualifiersAvailable side) :
    (attachDecoder parameters side cursor).Ready := by
  apply (orderedDecoder_ready parameters side (List.finRange parameters.decoder.nodeCount)
    (List.pairwise_lt_finRange parameters.decoder.nodeCount) cursor ready available ?_).1
  intro node member child smaller
  exact Or.inr (by simp)

theorem attachDecoder_qualifiersAvailable (parameters : Parameters) (side other : Side)
    (cursor : Cursor parameters) (available : cursor.QualifiersAvailable other) :
    (attachDecoder parameters side cursor).QualifiersAvailable other := by
  intro channel
  rw [attachDecoder_assigned]
  exact List.mem_append_left _ (available channel)

end Controller.Native.SourceController


namespace Controller.Native.SourceController

def Cursor.DecoderAvailable (cursor : Cursor parameters) (side : Side) : Prop :=
  ∀ node : Fin parameters.decoder.nodeCount, .internal (.decoder side node) ∈ cursor.assigned

theorem attachDecoder_all_assigned (parameters : Parameters) (side : Side)
    (cursor : Cursor parameters) : (attachDecoder parameters side cursor).DecoderAvailable side := by
  intro node
  simp [attachDecoder_assigned]

theorem attachDecoder_decoderAvailable (parameters : Parameters) (side other : Side)
    (cursor : Cursor parameters) (available : cursor.DecoderAvailable other) :
    (attachDecoder parameters side cursor).DecoderAvailable other := by
  intro node
  rw [attachDecoder_assigned]
  exact List.mem_append_left _ (available node)

def newDifferenceStep (parameters : Parameters) (cursor : Cursor parameters)
    (output : Fin parameters.decoder.roots.length) : Cursor parameters :=
  cursor.emitNative (.internal (.difference output)) (.xor
    (cursor.slots (.internal (.decoder .healthy (parameters.decoder.roots.get output))))
    (cursor.slots (.internal (.decoder .faulty (parameters.decoder.roots.get output)))))

theorem newDifferenceStep_ready (parameters : Parameters) (cursor : Cursor parameters)
    (output : Fin parameters.decoder.roots.length) (ready : cursor.Ready)
    (healthy : cursor.DecoderAvailable .healthy) (faulty : cursor.DecoderAvailable .faulty) :
    (newDifferenceStep parameters cursor output).Ready ∧
      (newDifferenceStep parameters cursor output).DecoderAvailable .healthy ∧
      (newDifferenceStep parameters cursor output).DecoderAvailable .faulty := by
  refine ⟨?_, ?_, ?_⟩
  · apply cursor.ready_emitNative _ _ ready
    intro handle member
    simp only [CNF.Gate.inputs, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact ready.bounded _ (healthy _)
    · exact ready.bounded _ (faulty _)
  · intro node
    rw [newDifferenceStep, Cursor.emitNative_assigned]
    exact List.mem_append_left _ (healthy node)
  · intro node
    rw [newDifferenceStep, Cursor.emitNative_assigned]
    exact List.mem_append_left _ (faulty node)

/-- The exact replacement-output list retains repeated roots and handles an empty detected OR. -/
theorem newObservations_ready (parameters : Parameters) (cursor : Cursor parameters)
    (ready : cursor.Ready) (healthy : cursor.DecoderAvailable .healthy)
    (faulty : cursor.DecoderAvailable .faulty) : (newObservations parameters cursor).Ready := by
  let differences := (List.finRange parameters.decoder.roots.length).foldl
    (newDifferenceStep parameters) cursor
  have invariant : ∀ items : List (Fin parameters.decoder.roots.length), ∀ state : Cursor parameters,
      state.Ready → state.DecoderAvailable .healthy → state.DecoderAvailable .faulty →
      (items.foldl (newDifferenceStep parameters) state).Ready ∧
      (items.foldl (newDifferenceStep parameters) state).DecoderAvailable .healthy ∧
      (items.foldl (newDifferenceStep parameters) state).DecoderAvailable .faulty := by
    intro items
    induction items with
    | nil => intro state ready healthy faulty; exact ⟨ready, healthy, faulty⟩
    | cons head tail inductionHypothesis =>
        intro state ready healthy faulty
        have next := newDifferenceStep_ready parameters state head ready healthy faulty
        exact inductionHypothesis _ next.1 next.2.1 next.2.2
  have final := invariant (List.finRange parameters.decoder.roots.length) cursor ready healthy faulty
  have allDifferences : ∀ output, .internal (.difference output) ∈ differences.assigned := by
    intro output
    dsimp [differences]
    rw [assigned_foldl _ _ (fun output => [.internal (.difference output)]) (fun _ _ => rfl)]
    simp [flatMap_singleton]
  have result := differences.ready_foldNative (.internal .detected) .disjunction
    ((List.finRange parameters.decoder.roots.length).map fun output =>
      differences.slots (.internal (.difference output))) final.1 (by
        intro handle member
        obtain ⟨output, _, rfl⟩ := List.mem_map.mp member
        exact final.1.bounded _ (allDifferences output))
  exact result

/-- Every actual retained source producer reads an already allocated source handle. -/
theorem compile_ready (parameters : Parameters) : (compile parameters).Ready := by
  let old := originalObservations parameters (controller parameters)
  have oldReady : old.Ready := controller_originalObservations_ready parameters
  let healthy := attachDecoder parameters .healthy old
  have healthyReady : healthy.Ready := attachDecoder_ready parameters .healthy old oldReady
    (controller_originalObservations_qualifiers parameters .healthy)
  let faulty := attachDecoder parameters .faulty healthy
  have faultyReady : faulty.Ready := attachDecoder_ready parameters .faulty healthy healthyReady
    (attachDecoder_qualifiersAvailable parameters .healthy .faulty old
      (controller_originalObservations_qualifiers parameters .faulty))
  exact newObservations_ready parameters faulty faultyReady
    (attachDecoder_decoderAvailable parameters .faulty .healthy healthy
      (attachDecoder_all_assigned parameters .healthy old))
    (attachDecoder_all_assigned parameters .faulty healthy)

theorem compile_ordered (parameters : Parameters) : (compile parameters).Ordered :=
  (compile_ready parameters).ordered

/-- Exact complete row identity has no supplied Ordered certificate or external source-ID map. -/
theorem compile_source_rows_unconditional (parameters : Parameters) :
    CNF.relabel SourceObservation.sourceID (compile parameters).toState.circuit.formula =
      equationFormula parameters := compile_source_rows parameters (compile_ordered parameters)

theorem compile_source_model_iff (parameters : Parameters) (assignment : ℕ → Bool) :
    CNF.Satisfies (assignment ∘ SourceObservation.sourceID)
      (compile parameters).toState.circuit.formula ↔
      CNF.Satisfies assignment (equationFormula parameters) :=
  Cursor.source_model_iff _ (compile_ordered parameters) assignment

end Controller.Native.SourceController


namespace Controller.Native.SourceController

/-- Every retained interface/detection assertion refers to a positive actual finite source ID. -/
theorem compile_assertions_bounded (parameters : Parameters) :
    SourceSerialFold.HandlesBounded (compile parameters).lastID (assertions parameters) := by
  intro handle member
  simp only [assertions, sourceRoleMap, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact (compile_ready parameters).bounded _ (by
      simp [compile_assigned, assignedRoles, firstArrayRoles])
  · exact (compile_ready parameters).bounded _ (by
      simp [compile_assigned, assignedRoles, interfaceRoles])
  · exact (compile_ready parameters).bounded _ (by
      simp [compile_assigned, assignedRoles, interfaceRoles])
  · exact (compile_ready parameters).bounded _ (by simp [compile_assigned, assignedRoles])

end Controller.Native.SourceController


namespace Controller.Native.SourceController

/-- Physical enable/request slots retain their exact initial source IDs and positive signs. -/
def Cursor.RootsExact (cursor : Cursor parameters) : Prop :=
  (∀ channel, cursor.slots (.primary (.enable channel)) =
    (SourceInitialIDs.rootID (b := parameters.buses) (.enable channel), true)) ∧
  (∀ bus channel, cursor.slots (.primary (.request bus channel)) =
    (SourceInitialIDs.rootID (.request bus channel), true))

theorem initial_rootsExact (parameters : Parameters) : (initial parameters).RootsExact :=
  ⟨fun _ => rfl, fun _ _ => rfl⟩

theorem Cursor.rootsExact_emit (cursor : Cursor parameters) (owner : Owner parameters)
    (gate : CNF.Gate ℕ) (exactRoots : cursor.RootsExact) :
    (cursor.emit owner gate).2.RootsExact := exactRoots

theorem Cursor.rootsExact_assign_internal (cursor : Cursor parameters) (role : Internal parameters)
    (handle : CNF.Literal ℕ) (exactRoots : cursor.RootsExact) :
    (cursor.assign (.internal role) handle).RootsExact := by
  constructor
  · intro channel
    simpa [Cursor.assign] using exactRoots.1 channel
  · intro bus channel
    simpa [Cursor.assign] using exactRoots.2 bus channel

theorem Cursor.rootsExact_assign_wire (cursor : Cursor parameters) (handle : CNF.Literal ℕ)
    (exactRoots : cursor.RootsExact) : (cursor.assign (.primary .wire) handle).RootsExact := by
  constructor
  · intro channel
    simpa [Cursor.assign] using exactRoots.1 channel
  · intro bus channel
    simpa [Cursor.assign] using exactRoots.2 bus channel

theorem Cursor.rootsExact_emitNative_internal (cursor : Cursor parameters) (role : Internal parameters)
    (gate : CNF.Gate ℕ) (exactRoots : cursor.RootsExact) :
    (cursor.emitNative (.internal role) gate).RootsExact :=
  Cursor.rootsExact_assign_internal _ _ _ (cursor.rootsExact_emit _ _ exactRoots)

theorem Cursor.rootsExact_emitNative_wire (cursor : Cursor parameters) (gate : CNF.Gate ℕ)
    (exactRoots : cursor.RootsExact) : (cursor.emitNative (.primary .wire) gate).RootsExact :=
  Cursor.rootsExact_assign_wire _ _ (cursor.rootsExact_emit _ _ exactRoots)

theorem Cursor.rootsExact_foldNative_internal (cursor : Cursor parameters) (role : Internal parameters)
    (junction : Bounded.Junction) (inputs : List (CNF.Literal ℕ))
    (exactRoots : cursor.RootsExact) :
    (cursor.foldNative (.internal role) junction inputs).RootsExact := by
  constructor
  · intro channel
    simpa [Cursor.foldNative, Cursor.assign] using exactRoots.1 channel
  · intro bus channel
    simpa [Cursor.foldNative, Cursor.assign] using exactRoots.2 bus channel

theorem rootsExact_foldl (items : List α) (step : Cursor parameters → α → Cursor parameters)
    (preserves : ∀ cursor item, cursor.RootsExact → (step cursor item).RootsExact)
    (cursor : Cursor parameters) (exactRoots : cursor.RootsExact) :
    (items.foldl step cursor).RootsExact := by
  induction items generalizing cursor with
  | nil => exact exactRoots
  | cons head tail inductionHypothesis => exact inductionHypothesis _ (preserves cursor head exactRoots)

theorem firstTermStep_rootsExact (parameters : Parameters) (cursor : Cursor parameters)
    (channel : Fin parameters.channels) (exactRoots : cursor.RootsExact) :
    (firstTermStep parameters cursor channel).RootsExact :=
  Cursor.rootsExact_assign_internal _ _ _
    (cursor.rootsExact_emitNative_internal _ _ exactRoots)

theorem firstAbsentStep_rootsExact (parameters : Parameters) (cursor : Cursor parameters)
    (channel : Fin parameters.channels) (exactRoots : cursor.RootsExact) :
    (firstAbsentStep parameters cursor channel).RootsExact :=
  Cursor.rootsExact_assign_internal _ _ _
    (cursor.rootsExact_emitNative_internal _ _ exactRoots)

theorem firstArrays_rootsExact (parameters : Parameters) : (firstArrays parameters).RootsExact := by
  have terms : (firstTerms parameters).RootsExact := rootsExact_foldl _ _
    (firstTermStep_rootsExact parameters) _ (initial_rootsExact parameters)
  exact rootsExact_foldl _ (firstAbsentStep parameters)
    (firstAbsentStep_rootsExact parameters) _ terms

end Controller.Native.SourceController


namespace Controller.Native.SourceController

theorem interface_rootsExact (parameters : Parameters) : (interface parameters).RootsExact := by
  unfold interface
  apply Cursor.rootsExact_emitNative_internal
  apply Cursor.rootsExact_emitNative_internal
  apply Cursor.rootsExact_emitNative_internal
  apply Cursor.rootsExact_emitNative_internal
  apply Cursor.rootsExact_emitNative_wire
  apply Cursor.rootsExact_foldNative_internal
  apply Cursor.rootsExact_foldNative_internal
  exact firstArrays_rootsExact parameters

theorem initialMasks_rootsExact (parameters : Parameters) (side : Side)
    (cursor : Cursor parameters) (exactRoots : cursor.RootsExact) :
    (initialMasks parameters side cursor).RootsExact :=
  rootsExact_foldl _ _ (fun state channel roots => state.rootsExact_emitNative_internal _ _ roots)
    cursor exactRoots

theorem laterBus_rootsExact (parameters : Parameters) (side : Side) (bus : Fin parameters.buses)
    (cursor : Cursor parameters) (exactRoots : cursor.RootsExact) :
    (laterBus parameters side bus cursor).RootsExact := by
  unfold laterBus
  apply rootsExact_foldl
  · intro state channel roots
    apply Cursor.rootsExact_emitNative_internal
    exact state.rootsExact_emitNative_internal _ _ roots
  · apply Cursor.rootsExact_foldNative_internal
    exact rootsExact_foldl _ _
      (fun state channel roots => state.rootsExact_foldNative_internal _ _ _ roots) cursor exactRoots

theorem negateFlags_rootsExact (parameters : Parameters) (side : Side)
    (cursor : Cursor parameters) (exactRoots : cursor.RootsExact) :
    (negateFlags parameters side cursor).RootsExact := by
  rw [negateFlags_eq]
  exact rootsExact_foldl _ (negateFlagStep parameters side)
    (fun state bus roots => roots) cursor exactRoots

theorem eligible_rootsExact (parameters : Parameters) (side : Side)
    (channel : Fin parameters.channels) (cursor : Cursor parameters) (exactRoots : cursor.RootsExact) :
    (eligible parameters side channel cursor).RootsExact := by
  unfold eligible
  apply Cursor.rootsExact_foldNative_internal
  exact rootsExact_foldl _ _
    (fun state bus roots => state.rootsExact_emitNative_internal _ _ roots) cursor exactRoots

theorem tail_rootsExact (parameters : Parameters) (side : Side)
    (cursor : Cursor parameters) (exactRoots : cursor.RootsExact) :
    (tail parameters side cursor).RootsExact := by
  unfold tail
  apply rootsExact_foldl
  · intro state channel roots
    exact eligible_rootsExact parameters side channel state roots
  · apply negateFlags_rootsExact
    apply rootsExact_foldl
    · intro state bus roots
      exact laterBus_rootsExact parameters side bus state roots
    · exact initialMasks_rootsExact parameters side cursor exactRoots

theorem controller_rootsExact (parameters : Parameters) : (controller parameters).RootsExact :=
  tail_rootsExact parameters .faulty _
    (tail_rootsExact parameters .healthy _ (interface_rootsExact parameters))

theorem originalObservations_rootsExact (parameters : Parameters)
    (cursor : Cursor parameters) (exactRoots : cursor.RootsExact) :
    (originalObservations parameters cursor).RootsExact := by
  have paired : (pairedOldOutputs parameters cursor).RootsExact :=
    rootsExact_foldl _ (oldDifferenceStep parameters)
      (fun state index roots => roots) cursor exactRoots
  exact paired

/-- All principal handles survive the private signed-guard chain unchanged. -/
theorem guardChain_slots (parameters : Parameters) (side : Side) (node : Fin parameters.decoder.nodeCount)
    (child : CNF.Literal ℕ) (labels : List (Fin parameters.channels)) (cursor : Cursor parameters) :
    (guardChain parameters side node child labels cursor).2.slots = cursor.slots := by
  unfold guardChain
  generalize labels.zipIdx = items
  induction items generalizing child cursor with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp only [List.foldl_cons]
      rw [inductionHypothesis]
      rfl

theorem decoderNode_rootsExact (parameters : Parameters) (side : Side)
    (node : Fin parameters.decoder.nodeCount) (cursor : Cursor parameters)
    (exactRoots : cursor.RootsExact) : (decoderNode parameters side node cursor).RootsExact := by
  unfold decoderNode
  cases equation : parameters.decoder.node node with
  | zero => exact cursor.rootsExact_emitNative_internal _ _ exactRoots
  | input channel => exact cursor.rootsExact_assign_internal _ _ exactRoots
  | disj children => exact cursor.rootsExact_foldNative_internal _ _ _ exactRoots
  | guard child labels =>
      apply Cursor.rootsExact_assign_internal
      constructor
      · intro channel
        rw [guardChain_slots]
        exact exactRoots.1 channel
      · intro bus channel
        rw [guardChain_slots]
        exact exactRoots.2 bus channel
  | liveAnd left right => exact cursor.rootsExact_emitNative_internal _ _ exactRoots

theorem attachDecoder_rootsExact (parameters : Parameters) (side : Side)
    (cursor : Cursor parameters) (exactRoots : cursor.RootsExact) :
    (attachDecoder parameters side cursor).RootsExact :=
  rootsExact_foldl _ _ (fun state node roots => decoderNode_rootsExact parameters side node state roots)
    cursor exactRoots

theorem newObservations_rootsExact (parameters : Parameters)
    (cursor : Cursor parameters) (exactRoots : cursor.RootsExact) :
    (newObservations parameters cursor).RootsExact := by
  unfold newObservations
  apply Cursor.rootsExact_foldNative_internal
  exact rootsExact_foldl _ _
    (fun state output roots => state.rootsExact_emitNative_internal _ _ roots) cursor exactRoots

/-- The full source allocation never renumbers, negates or overwrites a physical input slot. -/
theorem compile_rootsExact (parameters : Parameters) : (compile parameters).RootsExact :=
  newObservations_rootsExact parameters _ (attachDecoder_rootsExact parameters .faulty _
    (attachDecoder_rootsExact parameters .healthy _
      (originalObservations_rootsExact parameters _ (controller_rootsExact parameters))))

theorem sourceRoleMap_enable (parameters : Parameters) (channel : Fin parameters.channels) :
    sourceRoleMap parameters (.primary (.enable channel)) =
      (SourceInitialIDs.rootID (b := parameters.buses) (.enable channel), true) :=
  (compile_rootsExact parameters).1 channel

theorem sourceRoleMap_request (parameters : Parameters) (bus : Fin parameters.buses)
    (channel : Fin parameters.channels) :
    sourceRoleMap parameters (.primary (.request bus channel)) =
      (SourceInitialIDs.rootID (.request bus channel), true) :=
  (compile_rootsExact parameters).2 bus channel

end Controller.Native.SourceController
