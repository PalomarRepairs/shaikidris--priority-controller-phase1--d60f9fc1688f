module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.List.Count
public import Mathlib.Data.List.Dedup
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.List.NodupEquivFin
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Order.WellFounded
public import Mathlib.SetTheory.Cardinal.Finite
public import Std.Sat.CNF

@[expose] public section

/-!
# Dual-Horn models and vertex covers in priority controllers

Clauses retain literal occurrences and ordered formula rows. The reductions
count eligible qualifier sets over the entire declared variable universe,
including unused variables and isolated vertices. Physical detections refer
to the specified primary-input bridge interface. The decoder graph, clause
semantics, size measure and physical equations are given below.
-/

/- Definitions from Controller.CNF.Basic. -/
namespace Controller.CNF
abbrev OrderedFormula.Clause (α : Type u) := List (Std.Sat.Literal α)
structure OrderedFormula (α : Type u) where
  clauses : Array (OrderedFormula.Clause α)

abbrev Literal (α : Type*) := Std.Sat.Literal α
abbrev Clause (α : Type*) := Controller.CNF.OrderedFormula.Clause α
abbrev Formula (α : Type*) := Controller.CNF.OrderedFormula α
abbrev FiniteFormula (v : Nat) := Formula (Fin v)
abbrev negate (l : Literal α) : Literal α := Std.Sat.Literal.negate l
def LiteralHolds (a : α → Bool) (l : Literal α) : Prop := a l.1 = l.2
def ClauseHolds (a : α → Bool) (c : Clause α) : Prop :=
  ∃ l, l ∈ c ∧ LiteralHolds a l
def Satisfies (a : α → Bool) (f : Formula α) : Prop :=
  ∀ c, c ∈ f.clauses → ClauseHolds a c
end Controller.CNF

/- Definitions from Controller.Horn.DualHorn. -/
namespace Controller.Horn
open CNF
def Tautological (c : Clause α) : Prop := ∃ l, l ∈ c ∧ negate l ∈ c
def NegativeUnique (c : Clause α) : Prop :=
  ∀ l ∈ c, ∀ k ∈ c, l.2 = false → k.2 = false → l.1 = k.1
def DualHornClause (c : Clause α) : Prop := Tautological c ∨ NegativeUnique c
def DualHorn (f : Formula α) : Prop := ∀ c ∈ f.clauses, DualHornClause c
end Controller.Horn

/- Definitions from Controller.Horn.Rules. -/
namespace Controller.Horn.Worklist
open CNF
/-- An inert row, a positive clause, or a rule with one negative head. -/
inductive Rule (α : Type*) where
  | skip
  | positive (positive : List α)
  | negative (head : α) (positive : List α)
  deriving DecidableEq, Repr
namespace Rule
end Rule
variable [DecidableEq α]
/-- Distinct variables of one polarity, retaining one list occurrence of each. -/
def signedLabels (clause : Clause α) (polarity : Bool) : List α :=
  ((clause.filter fun literal => decide (literal.2 = polarity)).map Prod.fst).dedup
/-- A finite executable test for a literal together with its negation. -/
def tautologyCheck (clause : Clause α) : Bool :=
  clause.any fun literal => clause.contains (negate literal)
/-- Normalize one row; correctness for non-tautologies uses the dual-Horn restriction. -/
def compileClause (clause : Clause α) : Rule α :=
  if tautologyCheck clause then .skip
  else match signedLabels clause false with
    | [] => .positive (signedLabels clause true)
    | head :: _ => .negative head (signedLabels clause true)
end Controller.Horn.Worklist

/- Definitions from Controller.Basic.Assignments. -/
namespace Controller
abbrev Channel (n : ℕ) := Fin n
abbrev Assignment (n : ℕ) := Channel n → Bool
def assignmentOfSet {n : ℕ} (K : Finset (Channel n)) : Assignment n :=
  fun i => decide (i ∈ K)
def setOfAssignment {n : ℕ} (a : Assignment n) : Finset (Channel n) :=
  Finset.univ.filter (fun i => a i = true)
end Controller

/- Definitions from Controller.Basic.Admissible. -/
namespace Controller
/-- Physical image restriction; positive bus count is imposed by the physical model. -/
def Admissible {n : ℕ} (b : ℕ) (t : Channel n) (K : Finset (Channel n)) : Prop :=
  K.Nonempty ∧ (b = 1 → t ∈ K)
end Controller

/- Definitions from Controller.Basic.Sizes. -/
namespace Controller
/-- Incidences are charged with multiplicity; roots include repeated outputs. -/
structure DecoderSize where
  channels : ℕ
  nodes : ℕ
  children : ℕ
  guards : ℕ
  roots : ℕ
  deriving Repr, DecidableEq
def DecoderSize.total (s : DecoderSize) : ℕ :=
  s.channels + s.nodes + s.children + s.guards + s.roots
end Controller

/- Definitions from Controller.Decoder.Syntax. -/
namespace Controller.Decoder
/-- A gate whose live children are among the preceding `available` nodes. -/
inductive Gate (n available : ℕ) where
  | zero : Gate n available
  | input (channel : Channel n) : Gate n available
  | disj (children : List (Fin available)) : Gate n available
  | guard (child : Fin available) (labels : List (Channel n)) : Gate n available
  | liveAnd (left right : Fin available) : Gate n available
  deriving DecidableEq, Repr
namespace Gate
variable {n available : ℕ}
/-- Live child references, with their original multiplicities. -/
def children : Gate n available → List (Fin available)
  | .zero => []
  | .input _ => []
  | .disj refs => refs
  | .guard child _ => [child]
  | .liveAnd left right => [left, right]
/-- Negative channel incidences belonging to this gate itself. -/
def guardLabels : Gate n available → List (Channel n)
  | .guard _ labels => labels
  | _ => []
/-- Whether this represented node is a binary conjunction of two live children. -/
def isLiveAnd : Gate n available → Bool
  | .liveAnd _ _ => true
  | _ => false
/-- The original guarded language excludes the live-AND constructor. -/
def IsGuarded (gate : Gate n available) : Prop := gate.isLiveAnd = false
/-- Evaluate one gate using channel values and values for the earlier nodes. -/
def eval (gate : Gate n available) (assignment : Assignment n)
    (earlier : Fin available → Bool) : Bool :=
  match gate with
  | .zero => false
  | .input channel => assignment channel
  | .disj refs => refs.any earlier
  | .guard child labels => earlier child && !(labels.any assignment)
  | .liveAnd left right => earlier left && earlier right
end Gate
/-- A finite topological table with an explicit ordered list of observed roots. -/
structure DAG (n : ℕ) where
  nodeCount : ℕ
  node : (index : Fin nodeCount) → Gate n index.val
  roots : List (Fin nodeCount)
namespace DAG
variable {n : ℕ}
/-- Embed an earlier-node reference in the complete node-index type. -/
def childIndex (graph : DAG n) (parent : Fin graph.nodeCount)
    (child : Fin parent.val) : Fin graph.nodeCount :=
  ⟨child.val, Nat.lt_trans child.isLt parent.isLt⟩
theorem childIndex_lt (graph : DAG n) (parent : Fin graph.nodeCount)
    (child : Fin parent.val) : (graph.childIndex parent child).val < parent.val :=
  child.isLt
/-- All represented nodes belong to the original guarded language. -/
def Guarded (graph : DAG n) : Prop := ∀ index, (graph.node index).IsGuarded
/-- Child occurrences in the stored table; shared references remain occurrences. -/
def childIncidences (graph : DAG n) : ℕ :=
  (List.ofFn fun index : Fin graph.nodeCount => (graph.node index).children.length).sum
/-- Negative channel occurrences in the stored table. -/
def guardIncidences (graph : DAG n) : ℕ :=
  (List.ofFn fun index : Fin graph.nodeCount => (graph.node index).guardLabels.length).sum
/-- Size components for the common decoder resource interface. -/
def size (graph : DAG n) : DecoderSize where
  channels := n
  nodes := graph.nodeCount
  children := graph.childIncidences
  guards := graph.guardIncidences
  roots := graph.roots.length
/-- Decoder size charges channels, nodes, child, guard and root incidences. -/
def countedSize (graph : DAG n) : ℕ := graph.size.total
end DAG
end Controller.Decoder

/- Definitions from Controller.Decoder.Eval. -/
namespace Controller.Decoder
namespace Gate
variable {n available : ℕ}
end Gate
namespace DAG
variable {n : ℕ}
/-- Evaluate a represented node by recursion on its topological index. -/
def eval (graph : DAG n) (assignment : Assignment n) (index : Fin graph.nodeCount) : Bool :=
  (graph.node index).eval assignment (fun child =>
    graph.eval assignment (graph.childIndex index child))
termination_by index.val
decreasing_by exact graph.childIndex_lt index child
end DAG
end Controller.Decoder

/- Definitions from Controller.Physical.Controller. -/
namespace Controller.Physical
/-- Independent enable and request inputs of a controller with at least one bus.
The request arguments are bus, then channel. -/
structure PrimaryInput (n b : ℕ) where
  positiveBuses : 0 < b
  enable : Assignment n
  request : Fin b → Assignment n
/-- The first bus, whose existence is part of the physical input type. -/
def PrimaryInput.firstBus {n b : ℕ} (input : PrimaryInput n b) : Fin b :=
  ⟨0, input.positiveBuses⟩
/-- The Boolean OR of all channel values; the empty OR is false. -/
def anyTrue {n : ℕ} (a : Assignment n) : Bool :=
  decide (∃ i, a i = true)
/-- The local request after all preceding masks have been applied. -/
def stageTerms {n : ℕ} (active request : Assignment n) : Assignment n :=
  fun i => active i && request i
/-- The healthy flag selected by the local requests. -/
def stageFlag {n : ℕ} (active request : Assignment n) : Bool :=
  anyTrue (stageTerms active request)
/-- The source's XOR mask, including its negated local-request input. -/
def stageMask {n : ℕ} (flag : Bool) (terms : Assignment n) : Assignment n :=
  fun i => flag ^^ !(terms i)
/-- Add the current literal XOR mask to the accumulated enable-and-mask value. -/
def nextActive {n : ℕ} (active request : Assignment n) (flag : Bool) : Assignment n :=
  fun i => active i && stageMask flag (stageTerms active request) i
/-- A dimension-indexed trace of the literal selector recurrence. -/
structure SelectorRun (n b : ℕ) where
  flags : Fin b → Bool
  activeBefore : Fin b → Assignment n
  terms : Fin b → Assignment n
  masks : Fin b → Assignment n
  finalActive : Assignment n
/-- Execute the literal recurrence. An override supplies only the first flag.
The zero-bus case is used for suffix induction, not as a physical controller. -/
def runMasks {n : ℕ} : (b : ℕ) → Assignment n → (Fin b → Assignment n) →
    Option Bool → SelectorRun n b
  | 0, active, _, _ =>
      { flags := Fin.elim0
        activeBefore := Fin.elim0
        terms := Fin.elim0
        masks := Fin.elim0
        finalActive := active }
  | b + 1, active, request, override =>
      let flag := override.getD (stageFlag active (request 0))
      let rest := runMasks b (nextActive active (request 0) flag)
        (fun j => request j.succ) none
      { flags := Fin.cases flag rest.flags
        activeBefore := Fin.cases active rest.activeBefore
        terms := Fin.cases (stageTerms active (request 0)) rest.terms
        masks := Fin.cases (stageMask flag (stageTerms active (request 0))) rest.masks
        finalActive := rest.finalActive }
/-- A qualifier requires enablement and every request whose bus flag is true. -/
def qualifiers {n b : ℕ} (enable : Assignment n) (request : Fin b → Assignment n)
    (flags : Fin b → Bool) : Assignment n :=
  fun i => enable i && decide (∀ j, flags j = true → request j i = true)
/-- The completely healthy selector trace. -/
def healthyRun {n b : ℕ} (input : PrimaryInput n b) : SelectorRun n b :=
  runMasks b input.enable input.request none
/-- A trace with an explicitly supplied first flag and otherwise healthy stages. -/
def runFromFirst {n b : ℕ} (input : PrimaryInput n b) (first : Bool) : SelectorRun n b :=
  runMasks b input.enable input.request (some first)
/-- Healthy qualifiers, computed independently of the final accumulated mask. -/
def healthyQualifiers {n b : ℕ} (input : PrimaryInput n b) : Assignment n :=
  qualifiers input.enable input.request (healthyRun input).flags
/-- Qualifiers under a supplied first flag and the literal ensuing recurrence. -/
def qualifiersFromFirst {n b : ℕ} (input : PrimaryInput n b) (first : Bool) : Assignment n :=
  qualifiers input.enable input.request (runFromFirst input first).flags
/-- Observations are arbitrary Boolean functions of the qualifier vector. -/
def ObservationsDiffer {n q : ℕ} (outputs : Fin q → Assignment n → Bool)
    (healthy faulty : Assignment n) : Prop :=
  ∃ k, outputs k healthy ≠ outputs k faulty
end Controller.Physical

/- Definitions from Controller.Physical.Faults. -/
namespace Controller.Physical
/-- A target and a nonempty disjoint driver set for the bridge interface. -/
structure Bridge (n : ℕ) where
  target : Channel n
  drivers : Finset (Channel n)
  drivers_nonempty : drivers.Nonempty
  target_not_mem : target ∉ drivers
/-- Channels outside the target and driver group. This set may be empty. -/
def Bridge.remaining {n : ℕ} (bridge : Bridge n) : Finset (Channel n) :=
  Finset.univ \ insert bridge.target bridge.drivers
/-- The enabled first-bus request on each channel. -/
def firstTerms {n b : ℕ} (input : PrimaryInput n b) : Assignment n :=
  stageTerms input.enable (input.request input.firstBus)
/-- The negated target request at the bridge interface. -/
def bridgeU {n b : ℕ} (bridge : Bridge n) (input : PrimaryInput n b) : Bool :=
  !(firstTerms input bridge.target)
/-- All driver first requests are absent. -/
def bridgeD {n b : ℕ} (bridge : Bridge n) (input : PrimaryInput n b) : Bool :=
  decide (∀ i ∈ bridge.drivers, firstTerms input i = false)
/-- All remaining first requests are absent, with empty conjunction true. -/
def bridgeR {n b : ℕ} (bridge : Bridge n) (input : PrimaryInput n b) : Bool :=
  decide (∀ i ∈ bridge.remaining, firstTerms input i = false)
/-- The recovered Boolean interface equations, including the raw wire value. -/
def BridgeInterfaceSatisfied {n b : ℕ} (bridge : Bridge n) (input : PrimaryInput n b)
    (drive wire : Bool) : Prop :=
  bridgeU bridge input = !drive ∧ bridgeD bridge input = drive ∧ wire = drive
/-- The faulty first flag; later stages retain their original recurrence. -/
def bridgeFirstFlag {n b : ℕ} (bridge : Bridge n) (input : PrimaryInput n b)
    (wire : Bool) : Bool :=
  !(wire && bridgeD bridge input && bridgeR bridge input)
/-- The faulty qualifier vector defined by the actual first-flag replacement. -/
def bridgeQualifiers {n b : ℕ} (bridge : Bridge n) (input : PrimaryInput n b)
    (wire : Bool) : Assignment n :=
  qualifiersFromFirst input (bridgeFirstFlag bridge input wire)
/-- Interface activation and output change for one physical input. -/
def BridgeInputDetects {n b q : ℕ} (bridge : Bridge n) (drive : Bool)
    (outputs : Fin q → Assignment n → Bool) (input : PrimaryInput n b)
    (wire : Bool) : Prop :=
  BridgeInterfaceSatisfied bridge input drive wire ∧
    ObservationsDiffer outputs (healthyQualifiers input) (bridgeQualifiers bridge input wire)
/-- A bridge is detectable when an actual interface-satisfying input changes an observation. -/
def BridgeDetectable {n b q : ℕ} (bridge : Bridge n) (drive : Bool)
    (outputs : Fin q → Assignment n → Bool) : Prop :=
  ∃ input : PrimaryInput n b, ∃ wire, BridgeInputDetects bridge drive outputs input wire
end Controller.Physical

/- Definitions from Controller.Physical.Realize. -/
namespace Controller.Physical
/-- The suffix is zero except for the desired set on its first bus when the
target is absent. A zero-length suffix needs no bus index. -/
def realizeTailRequests {n : ℕ} (target : Channel n) (K : Finset (Channel n)) :
    (b : ℕ) → Fin b → Assignment n
  | 0 => Fin.elim0
  | _ + 1 => Fin.cases (if target ∈ K then (fun _ => false) else assignmentOfSet K)
      (fun _ _ => false)
/-- The first request singles out the target, followed by the realizing suffix. -/
def realizeRequests {n : ℕ} (target : Channel n) (K : Finset (Channel n)) :
    (b : ℕ) → Fin b → Assignment n
  | 0 => Fin.elim0
  | b + 1 => Fin.cases (assignmentOfSet {target}) (realizeTailRequests target K b)
/-- Explicit primary inputs for the drive-one image construction. -/
def realizeBridge {n b : ℕ} (bridge : Bridge n) (hb : 0 < b)
    (K : Finset (Channel n)) : PrimaryInput n b where
  positiveBuses := hb
  enable := assignmentOfSet (insert bridge.target K)
  request := realizeRequests bridge.target K b
end Controller.Physical

/- Definitions from Controller.Reductions.DualHornDecoder. -/
namespace Controller.Reductions.DualHorn
open Controller.CNF Controller.Decoder Controller.Horn.Worklist
def sourceChannel (i : Fin n) : Channel (n + 2) := ⟨i.val, by omega⟩
def targetChannel (n : ℕ) : Channel (n + 2) := ⟨n, by omega⟩
def helperChannel (n : ℕ) : Channel (n + 2) := ⟨n + 1, by omega⟩
def channelRule (rule : Rule (Fin n)) : Rule (Channel (n + 2)) :=
  match rule with
  | .skip => .skip
  | .positive labels => .positive (labels.map sourceChannel)
  | .negative head labels => .negative (sourceChannel head) (labels.map sourceChannel)
/-- Term zero is the helper guard; subsequent terms retain source row order. -/
def storedRule (formula : FiniteFormula n) (term : Fin (formula.clauses.size + 1)) :
    Rule (Channel (n + 2)) :=
  if first : term.val = 0 then .negative (targetChannel n) [helperChannel n]
  else channelRule (compileClause formula.clauses[term.val - 1])
def violationGate (rule : Rule (Channel (n + 2))) (available : ℕ)
    (inputBound : n + 2 ≤ available) : Gate (n + 2) available :=
  match rule with
  | .skip => .zero
  | .positive labels => .guard ⟨n, by omega⟩ labels
  | .negative head labels => .guard ⟨head.val, by omega⟩ labels
/-- Explicit stored topological construction; no gate producer is assumed. -/
def decoder (formula : FiniteFormula n) : DAG (n + 2) where
  nodeCount := n + formula.clauses.size + 4
  node := fun index =>
    if input : index.val < n + 2 then .input ⟨index.val, input⟩
    else if term : index.val < n + formula.clauses.size + 3 then
      violationGate (storedRule formula ⟨index.val - (n + 2), by omega⟩)
        index.val (by omega)
    else .disj (List.ofFn fun row : Fin (formula.clauses.size + 1) =>
      ⟨n + 2 + row.val, by omega⟩)
  roots := [⟨n + formula.clauses.size + 3, by omega⟩]
end Controller.Reductions.DualHorn

/- Definitions from Controller.Reductions.DualHornModels. -/
namespace Controller.Reductions.DualHorn
open Controller.CNF Controller.Decoder
theorem helper_ne_target : helperChannel n ≠ targetChannel n := by
  intro same
  have equal := congrArg Fin.val same
  simp only [helperChannel, targetChannel] at equal
  omega
/-- One bus and one helper driver suffice for the source-model reduction. -/
def modelBridge (n : ℕ) : Physical.Bridge (n + 2) where
  target := targetChannel n
  drivers := {helperChannel n}
  drivers_nonempty := by simp
  target_not_mem := by
    simp only [Finset.mem_singleton]
    exact Ne.symm helper_ne_target
/-- The sole observed coordinate is the actual stored decoder root. -/
def modelObservation (formula : FiniteFormula n) :
    Fin 1 → Assignment (n + 2) → Bool := fun _ values =>
  (decoder formula).eval values
    ⟨n + formula.clauses.size + 3, by change n + formula.clauses.size + 3 < n + formula.clauses.size + 4; omega⟩
end Controller.Reductions.DualHorn

/- Definitions from Controller.Reductions.DualHornSize. -/
open scoped BigOperators
namespace Controller.Reductions.DualHorn
open Controller.CNF Controller.Decoder Controller.Horn.Worklist
/-- Raw literal incidences retain duplicates and the entire declared row table. -/
def sourceLiteralIncidences (formula : FiniteFormula n) : ℕ :=
  (List.ofFn fun row : Fin formula.clauses.size => formula.clauses[row].length).sum
end Controller.Reductions.DualHorn

/- Definitions from Controller.Decoder.Cone. -/
namespace Controller.Decoder
namespace Gate
variable {n a b : ℕ}
end Gate
namespace DAG
variable {n : ℕ}
/-- The stored node identities in the syntactic cone of one root. -/
def cone (graph : DAG n) (root : Fin graph.nodeCount) : Finset (Fin graph.nodeCount) :=
  insert root ((graph.node root).children.toFinset.biUnion fun child =>
    graph.cone (graph.childIndex root child))
termination_by root.val
decreasing_by exact graph.childIndex_lt root child
/-- The union of the supplied output cones; repeated roots remain in the root list. -/
def cones (graph : DAG n) (roots : List (Fin graph.nodeCount)) : Finset (Fin graph.nodeCount) :=
  roots.toFinset.biUnion graph.cone
namespace Selection
variable {graph : DAG n}
end Selection
end DAG
end Controller.Decoder

/- Definitions from Controller.Decoder.Forest. -/
namespace Controller.Decoder
namespace Gate
def isInternal : Gate n available → Bool
  | .zero | .input _ => false
  | .disj _ | .guard _ _ | .liveAnd _ _ => true
end Gate
namespace DAG
variable {n : ℕ}
/-- Positions, rather than endpoints, retain repeated child references. -/
abbrev ParentOccurrence (graph : DAG n) :=
  Σ parent : Fin graph.nodeCount, Fin (graph.node parent).children.length
abbrev StoredOccurrence (graph : DAG n) :=
  Fin graph.roots.length ⊕ graph.ParentOccurrence
def refers (graph : DAG n) : graph.StoredOccurrence → Fin graph.nodeCount
  | .inl rootPosition => graph.roots.get rootPosition
  | .inr childPosition => graph.childIndex childPosition.1
      ((graph.node childPosition.1).children.get childPosition.2)
def parentRetained (graph : DAG n) (nodes : Finset (Fin graph.nodeCount)) :
    graph.StoredOccurrence → Prop
  | .inl _ => True
  | .inr childPosition => childPosition.1 ∈ nodes
abbrev ActiveUses (graph : DAG n) (nodes : Finset (Fin graph.nodeCount))
    (node : Fin graph.nodeCount) :=
  {occurrence : graph.StoredOccurrence //
    graph.parentRetained nodes occurrence ∧ graph.refers occurrence = node}
/-- Exact manuscript promise; irrelevant stored parents contribute no uses. -/
def FormulaForest (graph : DAG n) : Prop :=
  graph.Guarded ∧ ∀ node, (graph.node node).isInternal = true →
    Nat.card (graph.ActiveUses (graph.cones graph.roots) node) ≤ 1
namespace Selection
variable {graph : DAG n}
end Selection
end DAG
end Controller.Decoder

/- Definitions from Controller.Reductions.GraphCover. -/
namespace Controller.Reductions
open Decoder
/-- Each unordered edge is listed once, with its endpoints in increasing order.
The declared vertex universe includes isolated vertices. -/
structure EnumeratedGraph (n m : ℕ) where
  left : Fin m → Fin n
  right : Fin m → Fin n
  ordered : ∀ e, (left e).val < (right e).val
  unique : Function.Injective (fun e => (left e, right e))
namespace EnumeratedGraph
variable {n m : ℕ} (J : EnumeratedGraph n m)
def IsCover (C : Finset (Fin n)) : Prop :=
  ∀ e, J.left e ∈ C ∨ J.right e ∈ C
end EnumeratedGraph
variable {n m : ℕ}
def coverTarget (n : ℕ) : Channel (n + 1) := Fin.last n
def coverSet (C : Finset (Fin n)) : Finset (Channel (n + 1)) :=
  insert (coverTarget n) (C.image Fin.castSucc)
/-- Literal source formula on eligible sets. -/
def coverValue (J : EnumeratedGraph n m) (K : Finset (Channel (n + 1))) : Bool :=
  (List.ofFn fun e : Fin m => decide (coverTarget n ∈ K) &&
    !(decide ((J.left e).castSucc ∈ K) || decide ((J.right e).castSucc ∈ K))).any id
/-- One target input, one two-guard node per edge, and one final OR. -/
def coverDAG (J : EnumeratedGraph n m) : DAG (n + 1) where
  nodeCount := m + 2
  node := fun index =>
    if first : index.val = 0 then .input (coverTarget n)
    else if term : index.val < m + 1 then
      let e : Fin m := ⟨index.val - 1, by omega⟩
      .guard ⟨0, by omega⟩ [(J.left e).castSucc, (J.right e).castSucc]
    else .disj (List.ofFn fun e : Fin m => ⟨e.val + 1, by omega⟩)
  roots := [⟨m + 1, by omega⟩]
abbrev Covers (J : EnumeratedGraph n m) := {C : Finset (Fin n) // J.IsCover C}
abbrev CoverDetections (J : EnumeratedGraph n m) :=
  {K : Finset (Channel (n + 1)) // Admissible 1 (coverTarget n) K ∧
    coverValue J K ≠ coverValue J {coverTarget n}}
noncomputable instance coversFintype (J : EnumeratedGraph n m) : Fintype (Covers J) :=
  Fintype.ofFinite _
noncomputable instance coverDetectionsFintype (J : EnumeratedGraph n m) :
    Fintype (CoverDetections J) := Fintype.ofFinite _
/-- Any declared vertex may be the one bridge driver. -/
def coverBridge (driver : Fin n) : Physical.Bridge (n + 1) where
  target := coverTarget n
  drivers := {driver.castSucc}
  drivers_nonempty := by simp
  target_not_mem := by
    simp only [Finset.mem_singleton]
    intro equal
    have values := congrArg Fin.val equal
    change n = driver.val at values
    omega
def coverObservation (J : EnumeratedGraph n m) :
    Fin 1 → Assignment (n + 1) → Bool := fun _ a => coverValue J (setOfAssignment a)
end Controller.Reductions

open Controller Controller.CNF Controller.Decoder Controller.Reductions Controller.Reductions.DualHorn in
/-- Every dual-Horn formula has a satisfying assignment exactly when its constructed one-bus bridge is physically detectable. -/
theorem Controller.Reductions.DualHorn.model_bridge_detectable_iff (formula : FiniteFormula n)
    (horn : Controller.Horn.DualHorn formula) :
    Physical.BridgeDetectable (b := 1) (modelBridge n) true (modelObservation formula) ↔
      ∃ values : Fin n → Bool, Satisfies values formula := by
  sorry

open Controller Controller.CNF Controller.Decoder Controller.Reductions Controller.Reductions.DualHorn in
/-- The dual-Horn decoder has counted size at most ten times one plus the declared variable count, row count and literal-incidence count. -/
theorem Controller.Reductions.DualHorn.decoder_size_linear (formula : FiniteFormula n) :
    (decoder formula).countedSize ≤
      10 * (1 + n + formula.clauses.size + sourceLiteralIncidences formula) := by
  sorry

open Controller Controller.CNF Controller.Decoder Controller.Reductions Controller.Reductions.DualHorn in
/-- The dual-Horn construction is a guarded formula forest, with a single retained use of each active child occurrence. -/
theorem Controller.Reductions.DualHorn.decoder_formulaForest (formula : FiniteFormula n) : (decoder formula).FormulaForest := by
  sorry

open Controller Controller.CNF Controller.Decoder Controller.Reductions Controller.Reductions.DualHorn in
/-- The vertex-cover decoder has counted size linear in the declared vertices and enumerated edges. -/
theorem Controller.Reductions.coverDAG_size_linear (J : EnumeratedGraph n m) (edge : Fin m) :
    (coverDAG J).countedSize ≤ 14 * (n + m) := by
  sorry

open Controller Controller.CNF Controller.Decoder Controller.Reductions Controller.Reductions.DualHorn in
/-- The number of eligible detecting qualifier sets equals the number of vertex covers, including choices at isolated vertices. -/
theorem Controller.Reductions.cover_detection_count (J : EnumeratedGraph n m) (edge : Fin m) :
    Fintype.card (CoverDetections J) = Fintype.card (Covers J) := by
  sorry

open Controller Controller.CNF Controller.Decoder Controller.Reductions Controller.Reductions.DualHorn in
/-- Every physical detection of the constructed bridge yields a vertex cover from its faulty qualifier set. -/
theorem Controller.Reductions.cover_physical_detects_only_covers (J : EnumeratedGraph n m) (edge : Fin m)
    (driver : Fin n) (input : Physical.PrimaryInput (n + 1) 1) (wire : Bool)
    (detects : Physical.BridgeInputDetects (coverBridge driver) true
      (coverObservation J) input wire) :
    ∃ C, J.IsCover C ∧
      setOfAssignment (Physical.bridgeQualifiers (coverBridge driver) input wire) = coverSet C := by
  sorry

open Controller Controller.CNF Controller.Decoder Controller.Reductions Controller.Reductions.DualHorn in
/-- The canonical realization of an eligible qualifier set detects exactly when that set consists of the target and a vertex cover. -/
theorem Controller.Reductions.cover_realizer_detects_iff (J : EnumeratedGraph n m) (edge : Fin m)
    (driver : Fin n) (K : Finset (Channel (n + 1)))
    (legal : Admissible 1 (coverTarget n) K) :
    Physical.BridgeInputDetects (coverBridge driver) true (coverObservation J)
      (Physical.realizeBridge (coverBridge driver) (by decide : 0 < 1) K) true ↔
      ∃ C, J.IsCover C ∧ K = coverSet C := by
  sorry
