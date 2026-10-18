module
public import Lean.Elab.Tactic.Omega
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.List.Count
public import Mathlib.Data.List.Dedup
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.List.Forall2
public import Mathlib.Data.List.Induction
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.List.NodupEquivFin
public import Mathlib.Data.List.Perm.Subperm
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Vector.Basic
public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Logic.Relation
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Order.Preorder.Finite
public import Mathlib.Order.SuccPred.LinearLocallyFinite
public import Mathlib.Order.SuccPred.Tree
public import Mathlib.Order.WellFounded
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Std.Sat.CNF
@[expose] public section
noncomputable section
/-!
# Critical sets, query, width and backdoor obstructions
The grammar, state transitions, resource measures and mathematical predicates
are explicit. Definition holes identify only implementation witnesses; the
selected universal theorems constrain their executions or returned results.
The selected statements retain the exact assumptions of the proof library.
-/
namespace Controller
abbrev Channel (n : ℕ) := Fin n
abbrev Assignment (n : ℕ) := Channel n → Bool
def assignmentOfSet {n : ℕ} (K : Finset (Channel n)) : Assignment n := fun i => decide (i ∈ K)
def setOfAssignment {n : ℕ} (a : Assignment n) : Finset (Channel n) := Finset.univ.filter (fun i => a i = true)
end Controller
namespace Controller
structure NativeSize where
  (variableCount : ℕ) (clauses : ℕ) (literals : ℕ)
  deriving Repr, DecidableEq
end Controller
namespace Controller.Decoder
inductive Gate (n available : ℕ) where
  | zero : Gate n available | input (channel : Channel n) : Gate n available | disj (children : List (Fin available)) : Gate n available | guard (child : Fin available) (labels : List (Channel n)) : Gate n available | liveAnd (left right : Fin available) : Gate n available
  deriving DecidableEq, Repr
namespace Gate
variable {n available : ℕ}
def children : Gate n available → List (Fin available) | .zero => [] | .input _ => [] | .disj refs => refs | .guard child _ => [child] | .liveAnd left right => [left, right]
def guardLabels : Gate n available → List (Channel n) | .guard _ labels => labels | _ => []
def isLiveAnd : Gate n available → Bool | .liveAnd _ _ => true | _ => false
def IsGuarded (gate : Gate n available) : Prop := gate.isLiveAnd = false
def eval (gate : Gate n available) (assignment : Assignment n) (earlier : Fin available → Bool) : Bool :=
  match gate with
  | .zero => false
  | .input channel => assignment channel
  | .disj refs => refs.any earlier
  | .guard child labels => earlier child && !(labels.any assignment)
  | .liveAnd left right => earlier left && earlier right
end Gate
structure DAG (n : ℕ) where
  (nodeCount : ℕ) (node : (index : Fin nodeCount) → Gate n index.val) (roots : List (Fin nodeCount))
namespace DAG
variable {n : ℕ}
def childIndex (graph : DAG n) (parent : Fin graph.nodeCount) (child : Fin parent.val) : Fin graph.nodeCount := ⟨child.val, Nat.lt_trans child.isLt parent.isLt⟩
@[simp] theorem childIndex_val (graph : DAG n) (parent : Fin graph.nodeCount) (child : Fin parent.val) : (graph.childIndex parent child).val = child.val := rfl
theorem childIndex_lt (graph : DAG n) (parent : Fin graph.nodeCount) (child : Fin parent.val) : (graph.childIndex parent child).val < parent.val := child.isLt
def Guarded (graph : DAG n) : Prop := ∀ index, (graph.node index).IsGuarded
def childIncidences (graph : DAG n) : ℕ := (List.ofFn fun index : Fin graph.nodeCount => (graph.node index).children.length).sum
def guardIncidences (graph : DAG n) : ℕ := (List.ofFn fun index : Fin graph.nodeCount => (graph.node index).guardLabels.length).sum
end DAG
end Controller.Decoder
namespace Controller.Decoder
namespace DAG
variable {n : ℕ}
def eval (graph : DAG n) (assignment : Assignment n) (index : Fin graph.nodeCount) : Bool :=
  (graph.node index).eval assignment (fun child => graph.eval assignment (graph.childIndex index child))
termination_by index.val
decreasing_by exact graph.childIndex_lt index child
end DAG
end Controller.Decoder
namespace Controller
def Admissible {n : ℕ} (b : ℕ) (t : Channel n) (K : Finset (Channel n)) : Prop := K.Nonempty ∧ (b = 1 → t ∈ K)
end Controller
namespace Controller.Physical
structure PrimaryInput (n b : ℕ) where
  (positiveBuses : 0 < b) (enable : Assignment n) (request : Fin b → Assignment n)
def PrimaryInput.firstBus {n b : ℕ} (input : PrimaryInput n b) : Fin b := ⟨0, input.positiveBuses⟩
def anyTrue {n : ℕ} (a : Assignment n) : Bool := decide (∃ i, a i = true)
def stageTerms {n : ℕ} (active request : Assignment n) : Assignment n := fun i => active i && request i
def stageFlag {n : ℕ} (active request : Assignment n) : Bool := anyTrue (stageTerms active request)
def stageMask {n : ℕ} (flag : Bool) (terms : Assignment n) : Assignment n := fun i => flag ^^ !(terms i)
def nextActive {n : ℕ} (active request : Assignment n) (flag : Bool) : Assignment n := fun i => active i && stageMask flag (stageTerms active request) i
structure SelectorRun (n b : ℕ) where
  (flags : Fin b → Bool) (activeBefore : Fin b → Assignment n) (terms : Fin b → Assignment n) (masks : Fin b → Assignment n) (finalActive : Assignment n)
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
def qualifiers {n b : ℕ} (enable : Assignment n) (request : Fin b → Assignment n) (flags : Fin b → Bool) : Assignment n := fun i => enable i && decide (∀ j, flags j = true → request j i = true)
def healthyRun {n b : ℕ} (input : PrimaryInput n b) : SelectorRun n b := runMasks b input.enable input.request none
def runFromFirst {n b : ℕ} (input : PrimaryInput n b) (first : Bool) : SelectorRun n b := runMasks b input.enable input.request (some first)
def healthyQualifiers {n b : ℕ} (input : PrimaryInput n b) : Assignment n := qualifiers input.enable input.request (healthyRun input).flags
def qualifiersFromFirst {n b : ℕ} (input : PrimaryInput n b) (first : Bool) : Assignment n := qualifiers input.enable input.request (runFromFirst input first).flags
def ObservationsDiffer {n q : ℕ} (outputs : Fin q → Assignment n → Bool) (healthy faulty : Assignment n) : Prop := ∃ k, outputs k healthy ≠ outputs k faulty
end Controller.Physical
namespace Controller.Physical
structure Bridge (n : ℕ) where
  (target : Channel n) (drivers : Finset (Channel n)) (drivers_nonempty : drivers.Nonempty) (target_not_mem : target ∉ drivers)
def Bridge.remaining {n : ℕ} (bridge : Bridge n) : Finset (Channel n) := Finset.univ \ insert bridge.target bridge.drivers
def firstTerms {n b : ℕ} (input : PrimaryInput n b) : Assignment n := stageTerms input.enable (input.request input.firstBus)
def bridgeU {n b : ℕ} (bridge : Bridge n) (input : PrimaryInput n b) : Bool := !(firstTerms input bridge.target)
def bridgeD {n b : ℕ} (bridge : Bridge n) (input : PrimaryInput n b) : Bool := decide (∀ i ∈ bridge.drivers, firstTerms input i = false)
def bridgeR {n b : ℕ} (bridge : Bridge n) (input : PrimaryInput n b) : Bool := decide (∀ i ∈ bridge.remaining, firstTerms input i = false)
def BridgeInterfaceSatisfied {n b : ℕ} (bridge : Bridge n) (input : PrimaryInput n b) (drive wire : Bool) : Prop := bridgeU bridge input = !drive ∧ bridgeD bridge input = drive ∧ wire = drive
def bridgeFirstFlag {n b : ℕ} (bridge : Bridge n) (input : PrimaryInput n b) (wire : Bool) : Bool := !(wire && bridgeD bridge input && bridgeR bridge input)
def bridgeQualifiers {n b : ℕ} (bridge : Bridge n) (input : PrimaryInput n b) (wire : Bool) : Assignment n := qualifiersFromFirst input (bridgeFirstFlag bridge input wire)
def BridgeInputDetects {n b q : ℕ} (bridge : Bridge n) (drive : Bool) (outputs : Fin q → Assignment n → Bool) (input : PrimaryInput n b) (wire : Bool) : Prop := BridgeInterfaceSatisfied bridge input drive wire ∧ ObservationsDiffer outputs (healthyQualifiers input) (bridgeQualifiers bridge input wire)
end Controller.Physical
namespace Controller.Physical
def realizeTailRequests {n : ℕ} (target : Channel n) (K : Finset (Channel n)) :
    (b : ℕ) → Fin b → Assignment n
  | 0 => Fin.elim0
  | _ + 1 => Fin.cases (if target ∈ K then (fun _ => false) else assignmentOfSet K)
      (fun _ _ => false)
def realizeRequests {n : ℕ} (target : Channel n) (K : Finset (Channel n)) :
    (b : ℕ) → Fin b → Assignment n
  | 0 => Fin.elim0
  | b + 1 => Fin.cases (assignmentOfSet {target}) (realizeTailRequests target K b)
def realizeBridge {n b : ℕ} (bridge : Bridge n) (hb : 0 < b) (K : Finset (Channel n)) : PrimaryInput n b where
  positiveBuses := hb; enable := assignmentOfSet (insert bridge.target K); request := realizeRequests bridge.target K b
end Controller.Physical
namespace Controller.Boundaries
open Decoder
variable {n : ℕ}
noncomputable def successor (K : Finset (Channel n)) : Equiv.Perm (Channel n) := Classical.choose K.exists_cycleOn
noncomputable def criticalValue (K L : Finset (Channel n)) : Bool := by { classical{ exact (List.ofFn fun i : Channel n => if i ∈ K then decide (i ∈ L) && !decide (successor K i ∈ L) else decide (i ∈ L)).any id } }
noncomputable def criticalDAG (K : Finset (Channel n)) : DAG n := by
  classical
  exact {
    nodeCount := 2 * n + 1
    node := fun index =>
      if hi : index.val < n then .input ⟨index.val, hi⟩
      else if ht : index.val < 2 * n then
        let channel : Channel n := ⟨index.val - n, by omega⟩
        if channel ∈ K then .guard ⟨channel.val, by dsimp [channel]; omega⟩ [successor K channel]
        else .input channel
      else .disj (List.ofFn fun channel : Channel n => ⟨n + channel.val, by omega⟩)
    roots := [⟨2 * n, by omega⟩] }
theorem criticalDAG_guarded (K : Finset (Channel n)) : (criticalDAG K).Guarded := by { classical{ intro index; simp only [criticalDAG]; split; · { rfl }; · { split; · { split <;> rfl }; · { rfl } } } }
def criticalSets (b : ℕ) (t : Channel n) : Finset (Finset (Channel n)) :=
  if b = 1 then (((Finset.univ.erase t).powerset.image (insert t)).erase {t})
  else (Finset.univ.powerset.erase ∅).erase {t}
noncomputable def criticalObservation (K : Finset (Channel n)) : Fin 1 → Assignment n → Bool := fun _ assignment => criticalValue K (setOfAssignment assignment)
/-- physical test list lower bound: Critical sets, query, width and backdoor obstructions. -/
theorem physical_test_list_lower_bound {b : ℕ} (bridge : Physical.Bridge n) (tests : List (Physical.PrimaryInput n b)) (covers : ∀ K ∈ criticalSets b bridge.target, ∃ input ∈ tests, Physical.BridgeInputDetects bridge true (criticalObservation K) input true) : (criticalSets b bridge.target).card ≤ tests.length := by sorry
/-- criticalSets card one: Critical sets, query, width and backdoor obstructions. -/
theorem criticalSets_card_one (t : Channel n) : (criticalSets 1 t).card = 2 ^ (n - 1) - 1 := by sorry
/-- criticalSets card many: Critical sets, query, width and backdoor obstructions. -/
theorem criticalSets_card_many (b : ℕ) (hb : 2 ≤ b) (t : Channel n) : (criticalSets b t).card = 2 ^ n - 2 := by { sorry }
end Controller.Boundaries
namespace Controller.CNF
abbrev OrderedFormula.Clause (α : Type u) := List (Std.Sat.Literal α)
structure OrderedFormula (α : Type u) where
  (clauses : Array (OrderedFormula.Clause α))
namespace OrderedFormula
def empty : OrderedFormula α := ⟨#[]⟩
def Clause.eval (a : α → Bool) (c : Clause α) : Bool := c.any fun (i, n) => a i == n
def eval (a : α → Bool) (f : OrderedFormula α) : Bool := f.clauses.all fun c => c.eval a
def append (left right : OrderedFormula α) : OrderedFormula α := ⟨left.clauses ++ right.clauses⟩
instance : Append (OrderedFormula α) := ⟨append⟩
def Clause.relabel (r : α → β) (c : Clause α) : Clause β := c.map (fun (i, n) => (r i, n))
def relabel (r : α → β) (f : OrderedFormula α) : OrderedFormula β := ⟨f.clauses.map (Clause.relabel r)⟩
def toStd (f : OrderedFormula α) : Std.Sat.CNF α := ⟨f.clauses.map Std.Sat.CNF.Clause.ofLiterals⟩
end OrderedFormula
abbrev Literal (α : Type*) := Std.Sat.Literal α
abbrev Clause (α : Type*) := Controller.CNF.OrderedFormula.Clause α
abbrev Formula (α : Type*) := Controller.CNF.OrderedFormula α
abbrev negate (l : Literal α) : Literal α := Std.Sat.Literal.negate l
def ofClauses (cs : List (Clause α)) : Formula α := ⟨cs.toArray⟩
end Controller.CNF
namespace Controller.CNF
abbrev relabel (r : α → β) (f : Formula α) : Formula β := Controller.CNF.OrderedFormula.relabel r f
end Controller.CNF
namespace Controller.Cost
abbrev Word (width : Nat) := Fin (2 ^ width)
def word (width value : Nat) : Word width := ⟨value % (2 ^ width), Nat.mod_lt _ (Nat.two_pow_pos width)⟩
structure State (width registers : Nat) where
  (reg : Fin registers → Word width) (heap : Array (Word width)) (stack : List (Word width)) (output : List (Word width)) (pc : Word width) (halted : Bool)
def State.liveWords (s : State width registers) : Nat := registers + s.heap.size + s.stack.length + s.output.length + 1
inductive Instruction (width registers : Nat) where
  | constant (dst : Fin registers) (value : Word width) | copy (dst src : Fin registers) | add (dst left right : Fin registers) | xor (dst left right : Fin registers) | load (dst address : Fin registers) | store (address src : Fin registers) | allocate (src : Fin registers) | release | push (src : Fin registers) | pop (dst : Fin registers) | emit (src : Fin registers) | branchZero (src : Fin registers) (target : Word width) | halt
def State.put (s : State width registers) (dst : Fin registers) (value : Word width) : State width registers := { s with reg := fun i => if i = dst then value else s.reg i }
def State.advance (s : State width registers) : State width registers := { s with pc := word width (s.pc.val + 1) }
def step (instruction : Instruction width registers) (s : State width registers) : Option (State width registers) :=
  if s.halted then none else
  let next := s.advance
  match instruction with
  | .constant dst value => some (next.put dst value)
  | .copy dst src => some (next.put dst (s.reg src))
  | .add dst left right => some (next.put dst (word width ((s.reg left).val + (s.reg right).val)))
  | .xor dst left right => some (next.put dst (word width (Nat.xor (s.reg left).val (s.reg right).val)))
  | .load dst address =>
      if h : (s.reg address).val < s.heap.size then some (next.put dst s.heap[(s.reg address).val]) else none
  | .store address src =>
      if h : (s.reg address).val < s.heap.size then some { next with heap := s.heap.set (s.reg address).val (s.reg src) } else none
  | .allocate src =>
      if s.heap.size < 2 ^ width then some { next with heap := s.heap.push (s.reg src) }
      else none
  | .release => if s.heap.isEmpty then none else some { next with heap := s.heap.pop }
  | .push src => some { next with stack := s.reg src :: s.stack }
  | .pop dst => match s.stack with
      | [] => none
      | value :: rest => some { next.put dst value with stack := rest }
  | .emit src => some { next with output := s.reg src :: s.output }
  | .branchZero src target => some (if (s.reg src).val = 0 then { next with pc := target } else next)
  | .halt => some { next with halted := true }
abbrev Program (width registers : Nat) := Array (Instruction width registers)
def programWords (p : Program width registers) : Nat := 4 * p.size
def programStep (p : Program width registers) (s : State width registers) : Option (State width registers) := do
  let instruction ← p[s.pc.val]?
  step instruction s
inductive Execution (p : Program width registers) :
  State width registers → State width registers → Nat → Nat → Prop where
  | refl (s) : Execution p s s 0 s.liveWords | cons {s middle final ticks peak} (transition : programStep p s = some middle) (rest : Execution p middle final ticks peak) : Execution p s final (ticks + 1) (max s.liveWords peak)
end Controller.Cost
namespace Controller.Decoder
namespace DAG
variable {n : ℕ}
def cone (graph : DAG n) (root : Fin graph.nodeCount) : Finset (Fin graph.nodeCount) :=
  insert root ((graph.node root).children.toFinset.biUnion fun child => graph.cone (graph.childIndex root child))
termination_by root.val
decreasing_by exact graph.childIndex_lt root child
def cones (graph : DAG n) (roots : List (Fin graph.nodeCount)) : Finset (Fin graph.nodeCount) := roots.toFinset.biUnion graph.cone
end DAG
end Controller.Decoder
namespace Controller.Cost
def boolWord (width : Nat) (value : Bool) : Word width := word width (if value then 1 else 0)
end Controller.Cost
namespace Controller.Decoder
namespace Gate
def isInternal : Gate n available → Bool | .zero | .input _ => false | .disj _ | .guard _ _ | .liveAnd _ _ => true
end Gate
namespace DAG
variable {n : ℕ}
abbrev ParentOccurrence (graph : DAG n) := Σ parent : Fin graph.nodeCount, Fin (graph.node parent).children.length
abbrev StoredOccurrence (graph : DAG n) := Fin graph.roots.length ⊕ graph.ParentOccurrence
instance storedOccurrenceFintype (graph : DAG n) : Fintype graph.StoredOccurrence := by { dsimp [StoredOccurrence, ParentOccurrence]; infer_instance }
def refers (graph : DAG n) : graph.StoredOccurrence → Fin graph.nodeCount | .inl rootPosition => graph.roots.get rootPosition | .inr childPosition => graph.childIndex childPosition.1 ((graph.node childPosition.1).children.get childPosition.2)
def parentRetained (graph : DAG n) (nodes : Finset (Fin graph.nodeCount)) : graph.StoredOccurrence → Prop | .inl _ => True | .inr childPosition => childPosition.1 ∈ nodes
abbrev StoredUses (graph : DAG n) (node : Fin graph.nodeCount) := {occurrence : graph.StoredOccurrence // graph.refers occurrence = node}
abbrev ActiveUses (graph : DAG n) (nodes : Finset (Fin graph.nodeCount)) (node : Fin graph.nodeCount) :=
  {occurrence : graph.StoredOccurrence //
    graph.parentRetained nodes occurrence ∧ graph.refers occurrence = node}
noncomputable instance storedUsesFintype (graph : DAG n) (node : Fin graph.nodeCount) : Fintype (graph.StoredUses node) := Fintype.ofFinite _
def FormulaForest (graph : DAG n) : Prop := graph.Guarded ∧ ∀ node, (graph.node node).isInternal = true → Nat.card (graph.ActiveUses (graph.cones graph.roots) node) ≤ 1
def StoredForest (graph : DAG n) : Prop := graph.Guarded ∧ ∀ node, (graph.node node).isInternal = true → Nat.card (graph.StoredUses node) ≤ 1
theorem storedForest_formulaForest (graph : DAG n) (forest : graph.StoredForest) : graph.FormulaForest := by { refine ⟨forest.1, ?_⟩; intro node internal; have injective : Function.Injective (fun use : graph.ActiveUses (graph.cones graph.roots) node => (⟨use.val, use.property.2⟩ : graph.StoredUses node)) := by { intro first second equal; exact Subtype.ext (congrArg (fun use : graph.StoredUses node => use.val) equal) }; exact (Nat.card_le_card_of_injective _ injective).trans (forest.2 node internal) }
end DAG
end Controller.Decoder
namespace Controller.Cost.ForestCounter
open Controller.Decoder
def counterState (heap : Array (Word width)) (cursor : Nat) (address counter increment : Word width) : State width 4 where
  reg := fun register => if register = 0 then address else if register = 1 then counter
    else if register = 2 then increment else word width 0
  heap := heap; stack := []; output := []; pc := word width cursor; halted := false
end Controller.Cost.ForestCounter
namespace Controller.Cost
def State.frame (s : State width registers) (stack output : List (Word width)) : State width registers := { s with stack := s.stack ++ stack, output := s.output ++ output }
end Controller.Cost
namespace Controller.Cost.ForestIndexedOperands
open Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestCounter
def countSource (items : List α) (before : ℕ) : ℕ :=
  match items with
  | [] => before
  | _ :: rest => countSource rest (before + 1)
structure Row where
  (tag : ℕ) (head : ℕ) (children : List ℕ) (guards : List ℕ)
  deriving DecidableEq, Repr
def Row.Matches (row : Row) (gate : Gate n available) : Prop :=
  row.tag = (match gate with
    | .zero => 0 | .input _ => 1 | .disj _ => 2 | .guard _ _ => 3 | .liveAnd _ _ => 4) ∧
  (∀ channel, gate = .input channel → row.head = channel.val) ∧
  row.children = gate.children.map Fin.val ∧ row.guards = gate.guardLabels.map Fin.val
def rowHeaders (rows : List Row) : List ℕ := rows.flatMap (fun row => [row.tag, row.head])
def rowArities (rows : List Row) : List ℕ := rows.flatMap (fun row => [countSource row.children 0, countSource row.guards 0])
def rowChildren (rows : List Row) : List ℕ := rows.flatMap Row.children
def rowGuards (rows : List Row) : List ℕ := rows.flatMap Row.guards
structure RowsMatch (graph : DAG n) (rows : List Row) : Prop where
  (length_eq : rows.length = graph.nodeCount)
  node : ∀ index : Fin graph.nodeCount, (rows[index.val]'(by { rw [length_eq]; exact index.isLt })).Matches (graph.node index)
def rowBases : List Row → ℕ → ℕ → List ℕ | [], _, _ => [] | row :: rest, childCursor, guardCursor => childCursor :: guardCursor :: rowBases rest (childCursor + countSource row.children 0) (guardCursor + countSource row.guards 0)
def serializedRows (heapOffset : ℕ) (rows : List Row) (roots : List ℕ) : List ℕ :=
  let children := rowChildren rows
  let guards := rowGuards rows
  rowHeaders rows ++ rowBases rows (heapOffset + 6 * rows.length)
    (heapOffset + 6 * rows.length + children.length) ++ rowArities rows ++
    children ++ guards ++ roots
def RootsMatch (graph : DAG n) (roots : List ℕ) : Prop := roots = graph.roots.map Fin.val
def globalHeader (channels : ℕ) (rows : List Row) (roots : List ℕ) : List ℕ := [channels, countSource rows 0, countSource (rowChildren rows) 0, countSource (rowGuards rows) 0, countSource roots 0]
def inputPacket (channels heapOffset : ℕ) (rows : List Row) (roots : List ℕ) : List ℕ := globalHeader channels rows roots ++ serializedRows (heapOffset + 5) rows roots
end Controller.Cost.ForestIndexedOperands
namespace Controller.Cost.UniformDAGSource
open Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestIndexedOperands
def typedHead (gate : Gate n available) : ℕ :=
  match gate with
  | .input channel => channel.val
  | .guard child _ => child.val
  | .liveAnd left _ => left.val
  | _ => 0
structure HeadsMatch (graph : DAG n) (rows : List Row)
  (matched : RowsMatch graph rows) : Prop where
  head : ∀ node : Fin graph.nodeCount,
    (rows[node.val]'(by { rw [matched.length_eq]; exact node.isLt })).head =
      typedHead (graph.node node)
end Controller.Cost.UniformDAGSource
namespace Controller.Cost.RegisterWiden
open Controller.Cost
def widenState (state : State width 4) (saved : Fin 8 → Word width) : State width 8 :=
  { reg := fun register => if small : register.val < 4 then
      state.reg ⟨register.val, small⟩ else saved register
    heap := state.heap, stack := state.stack, output := state.output,
    pc := state.pc, halted := state.halted }
end Controller.Cost.RegisterWiden
namespace Controller.Cost.SharedZeroOutput
open Controller.CNF Controller.Decoder Controller.Decoder.DAG
def decode (observed : List (Word width)) (channels : Nat) : Finset (Fin channels) := setOfAssignment (fun channel => decide (observed[channel.val]? = some (word width 1)))
end Controller.Cost.SharedZeroOutput
namespace Controller.Cost.CompilerArrayTrace
inductive Trace {α : Type} : List α → Array α → Array α → Nat → Prop
  | nil (initial : Array α) : Trace [] initial initial 0 | cons (head : α) (rest : List α) (initial result : Array α) (count : Nat) (next : Trace rest (initial.push head) result count) : Trace (head :: rest) initial result (count + 1)
end Controller.Cost.CompilerArrayTrace
namespace Controller.Cost.ForestWeightedIndexed
open Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestIndexedOperands
variable {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]
def boundedIds (bound : Nat) : List Nat → Option (List (Fin bound)) | [] => some [] | value :: rest => if valid : value < bound then (boundedIds bound rest).map (⟨value, valid⟩ :: ·) else none
def decodeRow (n owner : Nat) (row : Row) : Option (Gate n owner) :=
  match row.tag with
  | 0 => some .zero
  | 1 => if valid : row.head < n then some (.input ⟨row.head, valid⟩) else none
  | 2 => (boundedIds owner row.children).map Gate.disj
  | 3 => do
      let children ← boundedIds owner row.children
      let labels ← boundedIds n row.guards
      match children with
      | [child] => some (.guard child labels)
      | _ => none
  | 4 => do
      let children ← boundedIds owner row.children
      match children with
      | [first, second] => some (.liveAnd first second)
      | _ => none
  | _ => none
abbrev Source (n : Nat) := Array (Option (Sigma fun owner : Nat => Gate n owner))
def sourceItems (n : Nat) (rows : List Row) : List (Option (Sigma fun owner : Nat => Gate n owner)) := rows.zipIdx.map fun item => (decodeRow n item.2 item.1).map (Sigma.mk item.2)
def source (n : Nat) (rows : List Row) : Source n := (sourceItems n rows).toArray
end Controller.Cost.ForestWeightedIndexed
namespace Controller.Cost.ForestWeightedIndexed
inductive IdValidationTrace (bound : Nat) : List Nat → Option (List (Fin bound)) → Nat → Nat → Prop
  | nil : IdValidationTrace bound [] (some []) 0 0 | valid (value : Nat) (valid : value < bound) (rest : List Nat) (result : Option (List (Fin bound))) (checks cells : Nat) (next : IdValidationTrace bound rest result checks cells) : IdValidationTrace bound (value :: rest) (result.map (⟨value, valid⟩ :: ·)) (checks + 1) (cells + if result.isSome then 1 else 0) | invalid (value : Nat) (invalid : ¬ value < bound) (rest : List Nat) : IdValidationTrace bound (value :: rest) none 1 0
end Controller.Cost.ForestWeightedIndexed
namespace Controller.Cost.ForestWeightedIndexed
open Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestIndexedOperands
inductive RowValidationTrace (n owner : Nat) (row : Row) : Option (Gate n owner) → Nat → Nat → Prop
  | zero (kind : row.tag = 0) : RowValidationTrace n owner row (some .zero) 1 1 | input (kind : row.tag = 1) : RowValidationTrace n owner row (if valid : row.head < n then some (.input ⟨row.head, valid⟩) else none) 2 1 | disj (kind : row.tag = 2) (result : Option (List (Fin owner))) (checks cells : Nat) (trace : IdValidationTrace owner row.children result checks cells) : RowValidationTrace n owner row (result.map Gate.disj) (checks + 1) (cells + 1) | guardAbsent (kind : row.tag = 3) (checks cells : Nat) (trace : IdValidationTrace owner row.children none checks cells) : RowValidationTrace n owner row none (checks + 1) cells | guardPresent (kind : row.tag = 3) (children : List (Fin owner)) (labels : Option (List (Fin n))) (childChecks childCells guardChecks guardCells : Nat) (childTrace : IdValidationTrace owner row.children (some children) childChecks childCells) (guardTrace : IdValidationTrace n row.guards labels guardChecks guardCells) : RowValidationTrace n owner row (labels.bind fun guards => match children with | [child] => some (.guard child guards) | _ => none) (childChecks + guardChecks + 2) (childCells + guardCells + 1)
  | liveAnd (kind : row.tag = 4) (children : Option (List (Fin owner))) (checks cells : Nat) (trace : IdValidationTrace owner row.children children checks cells) : RowValidationTrace n owner row (children.bind fun list => match list with | [first, second] => some (.liveAnd first second) | _ => none) (checks + 2) (cells + 1) | unsupported (kind : 5 ≤ row.tag) : RowValidationTrace n owner row none 1 0
end Controller.Cost.ForestWeightedIndexed
namespace Controller.Cost.ForestWeightedIndexed
open Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestIndexedOperands
inductive SourceValidationTrace (n : Nat) : Nat → List Row →
  List (Option (Sigma fun rank : Nat => Gate n rank)) → Nat → Nat → Prop
  | nil (owner : Nat) : SourceValidationTrace n owner [] [] 0 0 | cons (owner : Nat) (row : Row) (rest : List Row) (result : Option (Gate n owner)) (rows : List (Option (Sigma fun rank : Nat => Gate n rank))) (checks cells laterChecks laterCells : Nat) (decoded : RowValidationTrace n owner row result checks cells) (next : SourceValidationTrace n (owner + 1) rest rows laterChecks laterCells) : SourceValidationTrace n owner (row :: rest) (result.map (Sigma.mk owner) :: rows) (checks + 1 + laterChecks) (cells + 1 + laterCells)
end Controller.Cost.ForestWeightedIndexed
namespace Controller.Cost.ForestWeightedIndexed
open Controller.Decoder Controller.Decoder.DAG Controller.Cost.ForestIndexedOperands
def decodedWords (item : Option (Sigma fun owner : Nat => Gate n owner)) : Nat :=
  match item with
  | none => 0
  | some ⟨_, gate⟩ => 6 + 2 * gate.children.length + 2 * gate.guardLabels.length
def sourceWords (n : Nat) (rows : List Row) : Nat := ((sourceItems n rows).map fun item => 1 + decodedWords item).sum
end Controller.Cost.ForestWeightedIndexed
namespace Controller.Cost.ForestZeroResident
open Controller.Cost
def instructionFields (instruction : Instruction width registers) : List (Word width) :=
  match instruction with
  | .constant dst value => [word width 0, word width dst.val, value, word width 0]
  | .copy dst src => [word width 1, word width dst.val, word width src.val, word width 0]
  | .add dst left right => [word width 2, word width dst.val, word width left.val, word width right.val]
  | .xor dst left right => [word width 3, word width dst.val, word width left.val, word width right.val]
  | .load dst address => [word width 4, word width dst.val, word width address.val, word width 0]
  | .store address src => [word width 5, word width address.val, word width src.val, word width 0]
  | .allocate src => [word width 6, word width src.val, word width 0, word width 0]
  | .release => [word width 7, word width 0, word width 0, word width 0]
  | .push src => [word width 8, word width src.val, word width 0, word width 0]
  | .pop dst => [word width 9, word width dst.val, word width 0, word width 0]
  | .emit src => [word width 10, word width src.val, word width 0, word width 0]
  | .branchZero src target => [word width 11, word width src.val, target, word width 0]
  | .halt => [word width 12, word width 0, word width 0, word width 0]
inductive FieldInput (width : Nat) where
  | natural (value : Nat) | existing (value : Word width)
def instructionInputs (instruction : Instruction width registers) : List (FieldInput width) :=
  match instruction with
  | .constant dst value => [.natural 0, .natural dst.val, .existing value, .natural 0]
  | .copy dst src => [.natural 1, .natural dst.val, .natural src.val, .natural 0]
  | .add dst left right => [.natural 2, .natural dst.val, .natural left.val, .natural right.val]
  | .xor dst left right => [.natural 3, .natural dst.val, .natural left.val, .natural right.val]
  | .load dst address => [.natural 4, .natural dst.val, .natural address.val, .natural 0]
  | .store address src => [.natural 5, .natural address.val, .natural src.val, .natural 0]
  | .allocate src => [.natural 6, .natural src.val, .natural 0, .natural 0]
  | .release => [.natural 7, .natural 0, .natural 0, .natural 0]
  | .push src => [.natural 8, .natural src.val, .natural 0, .natural 0]
  | .pop dst => [.natural 9, .natural dst.val, .natural 0, .natural 0]
  | .emit src => [.natural 10, .natural src.val, .natural 0, .natural 0]
  | .branchZero src target => [.natural 11, .natural src.val, .existing target, .natural 0]
  | .halt => [.natural 12, .natural 0, .natural 0, .natural 0]
inductive FormationTrace : List (FieldInput width) → List (Word width) → Nat → Prop
  | nil : FormationTrace [] [] 0 | natural (number rest fields count) (next : FormationTrace rest fields count) : FormationTrace (.natural number :: rest) (word width number :: fields) (count + 1) | existing (value rest fields count) (next : FormationTrace rest fields count) : FormationTrace (.existing value :: rest) (value :: fields) (count + 1)
inductive BackingTrace : List (Instruction width registers) → Array (Word width) →
  Array (Word width) → Nat → Nat → Prop
  | nil (initial) : BackingTrace [] initial initial 0 0 | cons (instruction rest initial next final formed written) (formation : FormationTrace (instructionInputs instruction) (instructionFields instruction) 4) (fields : CompilerArrayTrace.Trace (instructionFields instruction) initial next 4) (remaining : BackingTrace rest next final formed written) : BackingTrace (instruction :: rest) initial final (formed + 4) (written + 4)
def backing : List (Instruction width registers) → Array (Word width) → Array (Word width) | [], initial => initial | instruction :: rest, initial => backing rest ((instructionFields instruction).toArrayAux initial)
end Controller.Cost.ForestZeroResident
namespace Controller.Decoder.DAG
def observations (graph : Controller.Decoder.DAG n) : Fin graph.roots.length → Controller.Assignment n → Bool := fun index assignment => graph.eval assignment (graph.roots.get index)
end Controller.Decoder.DAG
namespace Controller.Cost.ForestRootProjection
open Controller Controller.Cost Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestWeightedIndexed
open Controller.Cost.ForestIndexedOperands
variable {width n : Nat} {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]
def classificationInitial (width : Nat) (graph : DAG n) (rows : List Row) (roots : List Nat) (assignment : Channel n → Bool) (target : Channel n) (rest output : List (Word width)) (address loaded temporary : Word width) (saved : Fin 8 → Word width) : Controller.Cost.State width 8 := RegisterWiden.widenState ((ForestCounter.counterState (#[] : Array (Word width)) 0 address loaded temporary).frame ((inputPacket n 0 rows roots).map (word width) ++ List.ofFn (fun channel => boolWord width (assignment channel)) ++ (word width target.val :: rest)) output) saved
end Controller.Cost.ForestRootProjection
namespace Controller.Cost.ForestRootProjection
open Controller Controller.Cost Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestIndexedOperands
open Controller.Cost.ForestWeightedIndexed
variable {n : Nat} {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]
def forestSize (graph : DAG n) : Nat := n + graph.nodeCount + graph.roots.length + graph.childIncidences + graph.guardIncidences
def chosenMixedWidth (graph : DAG n) : Nat := Nat.log 2 (10000 * (forestSize graph + 1)) + 1
end Controller.Cost.ForestRootProjection
namespace Controller.CNF
inductive Gate (α : Type*) where
  | and (inputs : List (Literal α)) | or (inputs : List (Literal α)) | xor (left right : Literal α) | alias (input : Literal α) | not (input : Literal α) | constant (value : Bool)
  deriving DecidableEq, Repr
namespace Gate
def inputs : Gate α → List (Literal α) | .and ls | .or ls => ls | .xor l r => [l, r] | .alias l | .not l => [l] | .constant _ => []
def clauses (out : Literal α) : Gate α → List (Clause α) | .and ls => ls.map (fun l => [negate out, l]) ++ [out :: ls.map negate] | .or ls => ls.map (fun l => [out, negate l]) ++ [negate out :: ls] | .xor l r => [[l, r, negate out], [negate l, negate r, negate out], [l, negate r, out], [negate l, r, out]] | .alias l => [[negate out, l], [out, negate l]] | .not l => [[out, l], [negate out, negate l]] | .constant b => [[if b then out else negate out]]
def relabel (r : α → β) : Gate α → Gate β | .and ls => .and (ls.map (fun l => (r l.1, l.2))) | .or ls => .or (ls.map (fun l => (r l.1, l.2))) | .xor l k => .xor (r l.1, l.2) (r k.1, k.2) | .alias l => .alias (r l.1, l.2) | .not l => .not (r l.1, l.2) | .constant b => .constant b
end Gate
end Controller.CNF
namespace Controller.Native
inductive Side where
  | healthy | faulty
  deriving DecidableEq, Repr
def Side.all : List Side := [.healthy, .faulty]
@[simp] theorem Side.mem_all (side : Side) : side ∈ Side.all := by cases side <;> simp [Side.all]
inductive PrefixLayout where
  | raw | shared
  deriving DecidableEq, Repr
def PrefixLayout.activeCount : PrefixLayout → ℕ → ℕ | .raw, _ => 0 | .shared, buses => buses
inductive PrimaryRole (n b : ℕ) where
  | enable (channel : Fin n) | request (bus : Fin b) (channel : Fin n) | wire
  deriving DecidableEq, Repr
inductive Role (layout : PrefixLayout) (n b m q : ℕ) where
  | driver | remaining | firstProduct (side : Side) | term (side : Side) (bus : Fin b) (channel : Fin n) | absent (side : Side) (bus : Fin b) (channel : Fin n) | flag (side : Side) (bus : Fin b) | mask (side : Side) (bus : Fin b) (channel : Fin n) | active (side : Side) (bus : Fin (layout.activeCount b)) (channel : Fin n) | qualifierGuard (side : Side) (bus : Fin b) (channel : Fin n) | qualifier (side : Side) (channel : Fin n) | decoder (side : Side) (node : Fin m) | difference (output : Fin q) | detected
  deriving DecidableEq, Repr
structure Parameters where
  (channels : ℕ) (buses : ℕ) (positiveBuses : 0 < buses) (bridge : Physical.Bridge channels) (decoder : Decoder.DAG channels) (layout : PrefixLayout) (drive : Bool)
abbrev Internal (parameters : Parameters) := Role parameters.layout parameters.channels parameters.buses parameters.decoder.nodeCount parameters.decoder.roots.length
inductive Variable (parameters : Parameters) where
  | primary (role : PrimaryRole parameters.channels parameters.buses) | internal (role : Internal parameters)
  deriving DecidableEq, Repr
abbrev Lit (parameters : Parameters) := CNF.Literal (Variable parameters)
namespace Parameters
def positive (slot : Variable parameters) : Lit parameters := (slot, true)
def negative (slot : Variable parameters) : Lit parameters := (slot, false)
def enable (parameters : Parameters) (channel : Fin parameters.channels) : Lit parameters := positive (.primary (.enable channel))
def request (parameters : Parameters) (bus : Fin parameters.buses) (channel : Fin parameters.channels) : Lit parameters := positive (.primary (.request bus channel))
def internal (parameters : Parameters) (role : Internal parameters) : Lit parameters := positive (.internal role)
def firstBus (parameters : Parameters) : Fin parameters.buses := ⟨0, parameters.positiveBuses⟩
def targetAbsent (parameters : Parameters) : Lit parameters := internal parameters (.absent .healthy parameters.firstBus parameters.bridge.target)
def primaryRoles (parameters : Parameters) : List (PrimaryRole parameters.channels parameters.buses) := (List.finRange parameters.channels).map .enable ++ (List.finRange parameters.buses).flatMap (fun bus => (List.finRange parameters.channels).map (.request bus)) ++ [.wire]
def roles (parameters : Parameters) : List (Internal parameters) := [.driver, .remaining] ++ Side.all.map .firstProduct ++ Side.all.flatMap (fun side => (List.finRange parameters.buses).flatMap fun bus => (List.finRange parameters.channels).map (.term side bus)) ++ Side.all.flatMap (fun side => (List.finRange parameters.buses).flatMap fun bus => (List.finRange parameters.channels).map (.absent side bus)) ++ Side.all.flatMap (fun side => (List.finRange parameters.buses).map (.flag side)) ++ Side.all.flatMap (fun side => (List.finRange parameters.buses).flatMap fun bus => (List.finRange parameters.channels).map (.mask side bus)) ++ Side.all.flatMap (fun side => (List.finRange (parameters.layout.activeCount parameters.buses)).flatMap fun bus => (List.finRange parameters.channels).map (.active side bus)) ++ Side.all.flatMap (fun side => (List.finRange parameters.buses).flatMap fun bus => (List.finRange parameters.channels).map (.qualifierGuard side bus)) ++ Side.all.flatMap (fun side => (List.finRange parameters.channels).map (.qualifier side)) ++ Side.all.flatMap (fun side => (List.finRange parameters.decoder.nodeCount).map (.decoder side)) ++ (List.finRange parameters.decoder.roots.length).map .difference ++ [.detected]
@[simp] theorem mem_primaryRoles (parameters : Parameters) (role) :
    role ∈ parameters.primaryRoles := by { cases role <;> simp [primaryRoles] }
@[simp] theorem mem_roles (parameters : Parameters) (role) : role ∈ parameters.roles := by cases role <;> simp [roles]
def variableRoles (parameters : Parameters) : List (Variable parameters) := parameters.primaryRoles.map .primary ++ parameters.roles.map .internal
@[simp] theorem mem_variableRoles (parameters : Parameters) (slot : Variable parameters) :
    slot ∈ parameters.variableRoles := by { cases slot <;> simp [variableRoles] }
def decoderGate (parameters : Parameters) (side : Side) (index : Fin parameters.decoder.nodeCount) : CNF.Gate (Variable parameters) :=
  match parameters.decoder.node index with
  | .zero => .or []
  | .input channel => .alias (internal parameters (.qualifier side channel))
  | .disj children => .or (children.map fun child => internal parameters (.decoder side (parameters.decoder.childIndex index child)))
  | .guard child labels => .and
      (internal parameters (.decoder side (parameters.decoder.childIndex index child)) ::
        labels.map fun channel => negative (.internal (.qualifier side channel)))
  | .liveAnd left right => .and
      [internal parameters (.decoder side (parameters.decoder.childIndex index left)), internal parameters (.decoder side (parameters.decoder.childIndex index right))]
def rawTermInputs (parameters : Parameters) (side : Side) (bus : Fin parameters.buses) (channel : Fin parameters.channels) : List (Lit parameters) := [enable parameters channel, request parameters bus channel] ++ ((List.finRange parameters.buses).filter (fun earlier => earlier < bus)).map (fun earlier => internal parameters (.mask side earlier channel))
def termGate (parameters : Parameters) (side : Side) (bus : Fin parameters.buses) (channel : Fin parameters.channels) : CNF.Gate (Variable parameters) :=
  match layoutEquation : parameters.layout with
  | .raw => .and (rawTermInputs parameters side bus channel)
  | .shared => .and
      [internal parameters (.active side ⟨bus.val, by { simpa [layoutEquation, PrefixLayout.activeCount] using bus.isLt }⟩ channel), request parameters bus channel]
def activeGate (parameters : Parameters) (side : Side) (bus : Fin (parameters.layout.activeCount parameters.buses)) (channel : Fin parameters.channels) : CNF.Gate (Variable parameters) :=
  match layoutEquation : parameters.layout with
  | .raw => False.elim (Nat.not_lt_zero bus.val (by { simpa [layoutEquation, PrefixLayout.activeCount] using bus.isLt }))
  | .shared =>
      if first : bus.val = 0 then .alias (enable parameters channel)
      else .and
        [internal parameters (.active side ⟨bus.val - 1, by { omega }⟩ channel),
          internal parameters (.mask side ⟨bus.val - 1, by { have bound : bus.val < parameters.buses := by { simpa [layoutEquation, PrefixLayout.activeCount] using bus.isLt }; omega }⟩ channel)]
def gate (parameters : Parameters) : Internal parameters → CNF.Gate (Variable parameters)
  | .driver => .and (parameters.bridge.drivers.sort.map fun channel => internal parameters (.absent .healthy parameters.firstBus channel))
  | .remaining => .and (parameters.bridge.remaining.sort.map fun channel => internal parameters (.absent .healthy parameters.firstBus channel))
  | .firstProduct side => .and
      [match side with
       | .healthy => targetAbsent parameters
       | .faulty => positive (.primary .wire),
       internal parameters .driver, internal parameters .remaining]
  | .term side bus channel => termGate parameters side bus channel
  | .absent side bus channel => .not (internal parameters (.term side bus channel))
  | .flag side bus =>
      if bus.val = 0 then .not (internal parameters (.firstProduct side))
      else .or ((List.finRange parameters.channels).map fun channel => internal parameters (.term side bus channel))
  | .mask side bus channel => .xor (internal parameters (.flag side bus))
      (internal parameters (.absent side bus channel))
  | .active side bus channel => activeGate parameters side bus channel
  | .qualifierGuard side bus channel => .or
      [negative (.internal (.flag side bus)), request parameters bus channel]
  | .qualifier side channel => .and
      (enable parameters channel :: (List.finRange parameters.buses).map fun bus => internal parameters (.qualifierGuard side bus channel))
  | .decoder side index => decoderGate parameters side index
  | .difference output => .xor
      (internal parameters (.decoder .healthy (parameters.decoder.roots.get output)))
      (internal parameters (.decoder .faulty (parameters.decoder.roots.get output)))
  | .detected => .or ((List.finRange parameters.decoder.roots.length).map fun output => internal parameters (.difference output))
def assertions (parameters : Parameters) : List (Lit parameters) := [(parameters.targetAbsent.1, !parameters.drive), (.internal .driver, parameters.drive), (.primary .wire, parameters.drive), internal parameters .detected]
def equationClauses (parameters : Parameters) : List (CNF.Clause (Variable parameters)) := parameters.roles.flatMap fun role => (parameters.gate role).clauses (internal parameters role)
def equationFormula (parameters : Parameters) : CNF.Formula (Variable parameters) := CNF.ofClauses parameters.equationClauses
def assertionFormula (parameters : Parameters) : CNF.Formula (Variable parameters) := CNF.ofClauses (parameters.assertions.map fun literal => [literal])
def specificationFormula (parameters : Parameters) : CNF.Formula (Variable parameters) := parameters.equationFormula ++ parameters.assertionFormula
end Parameters
end Controller.Native
namespace Controller.Native.Bounded
inductive Junction where
  | conjunction | disjunction
  deriving DecidableEq, Repr
def Junction.gate (junction : Junction) (inputs : List (CNF.Literal α)) : CNF.Gate α :=
  match junction with
  | .conjunction => .and inputs
  | .disjunction => .or inputs
def auxiliaryCount : CNF.Gate α → ℕ | .and inputs | .or inputs => inputs.length - 2 | _ => 0
inductive LocalVariable (α : Type*) (count : ℕ) where
  | original (slot : α) | auxiliary (index : Fin count)
  deriving DecidableEq, Repr
def originalLiteral (literal : CNF.Literal α) : CNF.Literal (LocalVariable α count) := (.original literal.1, literal.2)
structure Producer (α : Type*) where
  (output : CNF.Literal α) (gate : CNF.Gate α)
  deriving DecidableEq, Repr
def Producer.rows (producer : Producer α) : List (CNF.Clause α) := producer.gate.clauses producer.output
def Producer.relabel (map : α → β) (producer : Producer α) : Producer β where
  output := (map producer.output.1, producer.output.2); gate := producer.gate.relabel map
def foldOutput (inputs : List (CNF.Literal α)) (output : CNF.Literal α) (index : Fin (inputs.length - 1)) : CNF.Literal (LocalVariable α (inputs.length - 2)) := if privateOutput : index.val < inputs.length - 2 then (.auxiliary ⟨index.val, privateOutput⟩, true) else originalLiteral output
def foldInputs (inputs : List (CNF.Literal α)) (atLeastTwo : 2 ≤ inputs.length) (index : Fin (inputs.length - 1)) : List (CNF.Literal (LocalVariable α (inputs.length - 2))) :=
  [if first : index.val = 0 then
      originalLiteral (inputs.get ⟨0, by { omega }⟩)
    else (.auxiliary ⟨index.val - 1, by { have := index.isLt; omega }⟩, true),
    originalLiteral (inputs.get ⟨index.val + 1, by { have := index.isLt; omega }⟩)]
def foldProducers (junction : Junction) (inputs : List (CNF.Literal α)) (output : CNF.Literal α) : List (Producer (LocalVariable α (inputs.length - 2))) :=
  if empty : inputs.length = 0 then [{ output := originalLiteral output, gate := junction.gate [] }]
  else if unary : inputs.length = 1 then
    [{ output := originalLiteral output, gate := .alias (originalLiteral (inputs.get ⟨0, by { omega }⟩)) }]
  else
    (List.finRange (inputs.length - 1)).map fun index =>
      { output := foldOutput inputs output index
        gate := junction.gate (foldInputs inputs (by { omega }) index) }
def expand (output : CNF.Literal α) :
    (gate : CNF.Gate α) → List (Producer (LocalVariable α (auxiliaryCount gate)))
  | .and inputs => foldProducers .conjunction inputs output
  | .or inputs => foldProducers .disjunction inputs output
  | .xor left right =>
      [{ output := originalLiteral output, gate := .xor (originalLiteral left) (originalLiteral right) }]
  | .alias input => [{ output := originalLiteral output, gate := .alias (originalLiteral input) }]
  | .not input => [{ output := originalLiteral output, gate := .not (originalLiteral input) }]
  | .constant value => [{ output := originalLiteral output, gate := .constant value }]
def rows (output : CNF.Literal α) (gate : CNF.Gate α) : List (CNF.Clause (LocalVariable α (auxiliaryCount gate))) := (expand output gate).flatMap Producer.rows
def foldProducerCount (arity : ℕ) : ℕ := max 1 (arity - 1)
theorem foldProducers_length (junction : Junction) (inputs : List (CNF.Literal α)) (output : CNF.Literal α) : (foldProducers junction inputs output).length = foldProducerCount inputs.length := by { unfold foldProducers; split; · { rename_i empty; simp [foldProducerCount, empty] }; · { split; · { rename_i unary; simp [foldProducerCount, unary] }; · { rename_i nonempty nonunary; simp only [List.length_map, List.length_finRange, foldProducerCount]; omega } } }
def expansionProducerCount : CNF.Gate α → ℕ | .and inputs | .or inputs => foldProducerCount inputs.length | _ => 1
theorem expand_length (gate : CNF.Gate α) (output : CNF.Literal α) : (expand output gate).length = expansionProducerCount gate := by { cases gate with | and inputs => { exact foldProducers_length .conjunction inputs output } | or inputs => { exact foldProducers_length .disjunction inputs output } | xor left right | «alias» left | not left | constant left => { simp [expand, expansionProducerCount] } }
inductive GlobalVariable (parameters : Parameters) where
  | original (slot : Controller.Native.Variable parameters) | auxiliary (owner : Internal parameters) (index : Fin (auxiliaryCount (parameters.gate owner)))
  deriving DecidableEq
def localSlots (parameters : Parameters) (owner : Internal parameters) : LocalVariable (Controller.Native.Variable parameters) (auxiliaryCount (parameters.gate owner)) → GlobalVariable parameters | .original slot => .original slot | .auxiliary index => .auxiliary owner index
def globalVariables (parameters : Parameters) : List (GlobalVariable parameters) := parameters.variableRoles.map GlobalVariable.original ++ parameters.roles.flatMap fun owner => (List.finRange (auxiliaryCount (parameters.gate owner))).map (.auxiliary owner)
@[simp] theorem mem_globalVariables (parameters : Parameters) (slot : GlobalVariable parameters) :
    slot ∈ globalVariables parameters := by { cases slot with | original original => { apply List.mem_append_left; exact List.mem_map.mpr ⟨original, parameters.mem_variableRoles original, rfl⟩ } | auxiliary owner index => { apply List.mem_append_right; exact List.mem_flatMap.mpr ⟨owner, parameters.mem_roles owner, List.mem_map.mpr ⟨index, by { simp }, rfl⟩⟩ } }
instance (parameters : Parameters) : Fintype (GlobalVariable parameters) := Fintype.ofList (globalVariables parameters) (mem_globalVariables parameters)
def producerFormula (parameters : Parameters) (owner : Internal parameters) : CNF.Formula (GlobalVariable parameters) := CNF.relabel (localSlots parameters owner) (CNF.ofClauses (rows (parameters.internal owner) (parameters.gate owner)))
def globalEquationFormula (parameters : Parameters) : CNF.Formula (GlobalVariable parameters) := parameters.roles.foldr (fun owner suffix => producerFormula parameters owner ++ suffix) Controller.CNF.OrderedFormula.empty
def globalFormula (parameters : Parameters) : CNF.Formula (GlobalVariable parameters) := globalEquationFormula parameters ++ CNF.relabel GlobalVariable.original parameters.assertionFormula
def literalIncidences (formula : CNF.Formula α) : ℕ := (formula.clauses.toList.map List.length).sum
end Controller.Native.Bounded
set_option maxRecDepth 10000
namespace Controller.Cost.CriticalSets
open Controller.Decoder Controller.Decoder.DAG Controller.Boundaries
variable {n : Nat}
noncomputable section
theorem oneLayer_storedForest (graph : DAG n) (top : Fin graph.nodeCount) (guarded : graph.Guarded) (roots : graph.roots = [top]) (maximum : ∀ index : Fin graph.nodeCount, index.val ≤ top.val) (terminal : ∀ parent : Fin graph.nodeCount, parent ≠ top → ∀ child ∈ (graph.node parent).children, (graph.node (graph.childIndex parent child)).isInternal = false) (distinct : (graph.node top).children.Nodup) : graph.StoredForest := by { refine ⟨guarded, ?_⟩; intro node internal; rw [Nat.card_eq_fintype_card]; apply Fintype.card_le_one_iff_subsingleton.mpr; refine ⟨?_⟩; intro first second; apply Subtype.ext; rcases first with ⟨first, firstRef⟩; rcases second with ⟨second, secondRef⟩; have parentTop : ∀ use : graph.ParentOccurrence, graph.refers (.inr use) = node → use.1 = top := by { intro use reference; by_contra different; have zero := terminal use.1 different ((graph.node use.1).children.get use.2) (List.get_mem _ _); have same : graph.childIndex use.1 ((graph.node use.1).children.get use.2) = node := reference; rw [same] at zero; rw [internal] at zero; contradiction }; have rootTop : ∀ position : Fin graph.roots.length, graph.refers (.inl position) = top := by { intro position; simp [DAG.refers, roots] }; cases first with | inl a => { cases second with | inl b => { have equal : a = b := by { apply Fin.ext; have length : graph.roots.length = 1 := by { simp [roots] }; have aa := a.isLt; have bb := b.isLt; omega }; subst b; rfl } | inr b => { have root := rootTop a; have ref := firstRef; have last : node = top := root.symm.trans ref |>.symm; have before := graph.childIndex_lt b.1 ((graph.node b.1).children.get b.2); have val := congrArg Fin.val secondRef; simp only [DAG.refers, DAG.childIndex_val] at val; have max := maximum b.1; have nodeval := congrArg Fin.val last; omega } } | inr a => { cases second with | inl b => { have root := rootTop b; have ref := secondRef; have last : node = top := root.symm.trans ref |>.symm; have before := graph.childIndex_lt a.1 ((graph.node a.1).children.get a.2); have val := congrArg Fin.val firstRef; simp only [DAG.refers, DAG.childIndex_val] at val; have max := maximum a.1; have nodeval := congrArg Fin.val last; omega } | inr b => { have ap := parentTop a firstRef; have bp := parentTop b secondRef; rcases a with ⟨aprent, apos⟩; rcases b with ⟨bprent, bpos⟩; dsimp at ap bp; subst aprent; subst bprent; have equality : (graph.node top).children.get apos = (graph.node top).children.get bpos := by { apply Fin.ext; have same := congrArg Fin.val (firstRef.trans secondRef.symm); exact same }; have positions := distinct.injective_get equality; subst bpos; rfl } } }
def root (K : Finset (Channel n)) : Fin (criticalDAG K).nodeCount := ⟨2 * n, by { change 2 * n < 2 * n + 1; omega }⟩
theorem critical_forest (K : Finset (Channel n)) : (criticalDAG K).FormulaForest := by { apply (criticalDAG K).storedForest_formulaForest; apply oneLayer_storedForest (criticalDAG K) (root K) (criticalDAG_guarded K) rfl; · { intro index; have bound := index.isLt; change index.val < 2 * n + 1 at bound; change index.val ≤ 2 * n; omega }; · { intro parent different child present; by_cases input : parent.val < n; · { simp only [criticalDAG, dite_eq_left input, Gate.children] at present; simp at present }; · { by_cases term : parent.val < 2 * n; · { by_cases member : (⟨parent.val - n, by { omega }⟩ : Channel n) ∈ K; · { have same : child.val = parent.val - n := by { have equal : child = ⟨parent.val - n, by { omega }⟩ := by { simpa only [criticalDAG, dite_eq_right input, dite_eq_left term, ite_eq_left member, Gate.children, List.mem_singleton] using present }; exact congrArg Fin.val equal }; have small : child.val < n := by { omega }; change ((criticalDAG K).node ⟨child.val, by { change child.val < 2 * n + 1; omega }⟩).isInternal = false; simp only [criticalDAG, small, dite_true, Gate.isInternal] }; · { simp only [criticalDAG, dite_eq_right input, dite_eq_left term, ite_eq_right member, Gate.children] at present; simp at present } }; · { have last : parent = root K := by { apply Fin.ext; have bound := parent.isLt; change parent.val < 2 * n + 1 at bound; change parent.val = 2 * n; omega }; exact False.elim (different last) } } }; · { have notInput : ¬2 * n < n := by { omega }; change ((criticalDAG K).node ⟨2 * n, by { change 2 * n < 2 * n + 1; omega }⟩).children.Nodup; simp only [criticalDAG, notInput, dite_false, lt_self_iff_false, Gate.children]; apply List.nodup_ofFn_ofInjective; intro a b equal; apply Fin.ext; have values := congrArg Fin.val equal; dsimp only at values; omega } }
open Controller.Cost.ForestRootProjection Controller.Cost.ForestIndexedOperands
def descriptorInput {b : Nat} (bridge : Physical.Bridge n) (positive : 0 < b) (payload : List (Word width)) : Physical.PrimaryInput n b := Physical.realizeBridge bridge positive (SharedZeroOutput.decode payload n)
noncomputable def forestProgram : {n : ℕ} → (graph : Controller.Decoder.DAG n) → graph.FormulaForest → ℕ → Controller.Channel n → (rows : List.{0} Controller.Cost.ForestIndexedOperands.Row) → List.{0} ℕ → Controller.Cost.ForestIndexedOperands.RowsMatch graph rows → Controller.Cost.Program (Controller.Cost.ForestRootProjection.chosenMixedWidth graph) 8 := by { sorry }
def cycleDAG (n : Nat) : DAG n where
  nodeCount := 2 * n + 1
  node index := if input : index.val < n then .input ⟨index.val, input⟩
    else if term : index.val < 2 * n then
      let channel : Channel n := ⟨index.val - n, by { omega }⟩
      .guard ⟨channel.val, by { dsimp [channel]; omega }⟩ [finRotate n channel]
    else .disj (List.ofFn fun channel : Channel n => ⟨n + channel.val, by { omega }⟩)
  roots := [⟨2 * n, by { omega }⟩]
def cycleRoot (n : Nat) : Fin (cycleDAG n).nodeCount := ⟨2 * n, by { change _ < 2 * n + 1; omega }⟩
theorem cycle_guarded (n : Nat) : (cycleDAG n).Guarded := by { intro index; simp only [cycleDAG]; split; · { rfl }; · { split <;> rfl } }
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
/-- cycle unique: Critical sets, query, width and backdoor obstructions. -/
theorem cycle_unique {b : Nat} (bridge : Physical.Bridge n) (positive : 0 < b) (L : Finset (Channel n)) (admissible : Admissible b bridge.target L) (detects : Physical.BridgeInputDetects bridge true (cycleDAG n).observations (Physical.realizeBridge bridge positive L) true) : L = Finset.univ := by { sorry }
open Controller.Cost.ForestWeightedIndexed Controller.Cost.ForestZeroResident
def RecoveryRun (graph : DAG n) (forest : graph.FormulaForest) (b : Nat) (bridge : Physical.Bridge n) (positive : 0 < b) (K : Finset (Channel n)) (rows : List Row) (roots : List Nat) (matched : RowsMatch graph rows) (address loaded temporary : Word (chosenMixedWidth graph)) (saved : Fin 8 → Word (chosenMixedWidth graph)) : Prop :=
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
/-- critical complete: Critical sets, query, width and backdoor obstructions. -/
theorem critical_complete (b : Nat) (bridge : Physical.Bridge n) (positive : 0 < b) (K : Finset (Channel n)) (legal : K ∈ criticalSets b bridge.target) (rows : List Row) (roots : List Nat) (matched : RowsMatch (criticalDAG K) rows) (heads : UniformDAGSource.HeadsMatch (criticalDAG K) rows matched) (rootMatches : RootsMatch (criticalDAG K) roots) (address loaded temporary : Word (chosenMixedWidth (criticalDAG K))) (saved : Fin 8 → Word (chosenMixedWidth (criticalDAG K))) : RecoveryRun (criticalDAG K) (critical_forest K) b bridge positive K rows roots matched address loaded temporary saved := by sorry
/-- cycle complete: Critical sets, query, width and backdoor obstructions. -/
theorem cycle_complete (b : Nat) (bridge : Physical.Bridge n) (positive : 0 < b) (rows : List Row) (roots : List Nat) (matched : RowsMatch (cycleDAG n) rows) (heads : UniformDAGSource.HeadsMatch (cycleDAG n) rows matched) (rootMatches : RootsMatch (cycleDAG n) roots) (address loaded temporary : Word (chosenMixedWidth (cycleDAG n))) (saved : Fin 8 → Word (chosenMixedWidth (cycleDAG n))) : RecoveryRun (cycleDAG n) (cycle_forest n) b bridge positive Finset.univ rows roots matched address loaded temporary saved := by { sorry }
end
end Controller.Cost.CriticalSets
namespace Controller.Boundaries
variable {n : ℕ}
def bottomValue (L : Finset (Channel n)) : Bool := decide L.Nonempty
inductive QueryTree (Query : Type*) where
  | answer (detectable : Bool) | ask (query : Query) (onFalse onTrue : QueryTree Query)
namespace QueryTree
variable {Query : Type*}
def run (oracle : Query → Bool) : QueryTree Query → Bool | .answer result => result | .ask query onFalse onTrue => if oracle query then onTrue.run oracle else onFalse.run oracle
def budget : QueryTree Query → ℕ | .answer _ => 0 | .ask _ onFalse onTrue => 1 + max onFalse.budget onTrue.budget
end QueryTree
def CorrectOnCriticalFamily (tree : QueryTree (Finset (Channel n))) (b : ℕ) (t : Channel n) : Prop := tree.run bottomValue = false ∧ ∀ K ∈ criticalSets b t, tree.run (criticalValue K) = true
/-- deterministic one bus: Critical sets, query, width and backdoor obstructions. -/
theorem deterministic_one_bus (tree : QueryTree (Finset (Channel n))) (t : Channel n) (correct : CorrectOnCriticalFamily tree 1 t) : 2 ^ (n - 1) - 1 ≤ tree.budget := by sorry
/-- deterministic many buses: Critical sets, query, width and backdoor obstructions. -/
theorem deterministic_many_buses (tree : QueryTree (Finset (Channel n))) (b : ℕ) (hb : 2 ≤ b) (t : Channel n) (correct : CorrectOnCriticalFamily tree b t) : 2 ^ n - 2 ≤ tree.budget := by sorry
/-- randomized mixture lower bound: Critical sets, query, width and backdoor obstructions. -/
theorem randomized_mixture_lower_bound {Coins : Type*} [Fintype Coins] (trees : Coins → QueryTree (Finset (Channel n))) (weight : Coins → ℝ) (nonnegative : ∀ coin, 0 ≤ weight coin) (normalized : ∑ coin, weight coin = 1) (b : ℕ) (t : Channel n) (r : ℕ) (budget : ∀ coin, (trees coin).budget ≤ r) (bottomCorrect : (2 / 3 : ℝ) ≤ ∑ coin, weight coin * (if (trees coin).run bottomValue = false then 1 else 0)) (hiddenCorrect : ∀ K ∈ criticalSets b t, (2 / 3 : ℝ) ≤ ∑ coin, weight coin * (if (trees coin).run (criticalValue K) = true then 1 else 0)) : (criticalSets b t).card ≤ 3 * r := by sorry
end Controller.Boundaries
namespace Controller.Graph
variable {V W : Type} [DecidableEq V] [DecidableEq W]
structure TreeDecomposition (G : SimpleGraph V) where
  (tree : RootedTree) (finite : Fintype tree) (bag : tree → Finset V) (home : V → tree) (home_mem : ∀ v, v ∈ bag (home v)) (above_home : ∀ v i, v ∈ bag i → home v ≤ i) (interval : ∀ v i j, v ∈ bag i → home v ≤ j → j ≤ i → v ∈ bag j) (edge : ∀ ⦃u v⦄, G.Adj u v → ∃ i, u ∈ bag i ∧ v ∈ bag i)
namespace TreeDecomposition
variable {G : SimpleGraph V} (D : TreeDecomposition G)
def Capacity (k : ℕ) : Prop := ∀ i, (D.bag i).card ≤ k
end TreeDecomposition
def HasTreeCapacity (G : SimpleGraph V) (k : ℕ) : Prop := ∃ D : TreeDecomposition G, D.Capacity k
def TreewidthLE (G : SimpleGraph V) (w : ℕ) : Prop := HasTreeCapacity G (w + 1)
end Controller.Graph
namespace Controller.Graph
variable {V S : Type} [Fintype V] [DecidableEq V] [Fintype S] [DecidableEq S]
structure NetSystem (V S : Type) where
  (net : S → Finset V)
namespace NetSystem
variable (H : NetSystem V S)
def crossing (order : V ≃ Fin (Fintype.card V)) (cut : ℕ) : Finset S := Finset.univ.filter fun s => (∃ u ∈ H.net s, (order u).val < cut) ∧ (∃ v ∈ H.net s, cut ≤ (order v).val)
def CutBound (order : V ≃ Fin (Fintype.card V)) (k : ℕ) : Prop := ∀ cut, (H.crossing order cut).card ≤ k
def NetCutwidthLE (k : ℕ) : Prop := ∃ order, H.CutBound order k
end NetSystem
structure CircuitLayout (Input Gate Output Signal : Type) where
  (producer : Signal → Input ⊕ Gate) (consumers : Signal → Finset (Gate ⊕ Output))
namespace CircuitLayout
variable {Input Gate Output Signal : Type}
def inputVertex : Input ⊕ Gate → Input ⊕ Gate ⊕ Output | .inl i => .inl i | .inr g => .inr (.inl g)
def consumerVertex : Gate ⊕ Output → Input ⊕ Gate ⊕ Output := Sum.inr
def wireGraph (L : CircuitLayout Input Gate Output Signal) : SimpleGraph (Input ⊕ Gate ⊕ Output) where
  Adj x y := x ≠ y ∧ ∃ s c, c ∈ L.consumers s ∧
    ((x = inputVertex (L.producer s) ∧ y = consumerVertex c) ∨
     (y = inputVertex (L.producer s) ∧ x = consumerVertex c))
  symm := ⟨by { rintro x y ⟨ne, s, c, hc, edge⟩; exact ⟨ne.symm, s, c, hc, edge.symm⟩ }⟩
  loopless := ⟨fun _ h => h.1 rfl⟩
def nets [DecidableEq Input] [DecidableEq Gate] [DecidableEq Output] (L : CircuitLayout Input Gate Output Signal) : NetSystem (Input ⊕ Gate ⊕ Output) Signal where
  net s := insert (inputVertex (L.producer s)) ((L.consumers s).image consumerVertex)
noncomputable def blockInputs [Fintype Signal] [DecidableEq Gate] (L : CircuitLayout Input Gate Output Signal) (block : Finset Gate) : Finset Signal := by
  classical
  exact Finset.univ.filter fun s =>
    (∃ g ∈ block, Sum.inl g ∈ L.consumers s) ∧
      (match L.producer s with | .inl _ => True | .inr g => g ∉ block)
end CircuitLayout
end Controller.Graph
namespace Controller.Graph
variable {V : Type} [DecidableEq V]
def clausePrimal (clauses : List (Controller.CNF.Clause V)) : SimpleGraph V where
  Adj u v := u ≠ v ∧ ∃ row ∈ clauses, u ∈ row.map Prod.fst ∧ v ∈ row.map Prod.fst
  symm := ⟨by { intro u v h; obtain ⟨ne, row, hr, hu, hv⟩ := h; exact ⟨ne.symm, row, hr, hv, hu⟩ }⟩
  loopless := ⟨by { intro v h; exact h.1 rfl }⟩
namespace NativeWidth
open Controller.Native
open Controller.Native.Parameters
variable (p : Parameters)
def clauses : List (CNF.Clause (Variable p)) := p.equationClauses ++ p.assertions.map (fun literal => [literal])
def primal : SimpleGraph (Variable p) := clausePrimal (clauses p)
/-- primal treewidth lower: Critical sets, query, width and backdoor obstructions. -/
theorem primal_treewidth_lower (w : ℕ) (bound : TreewidthLE (primal p) w) : min p.channels p.buses ≤ w := by { sorry }
abbrev EquationAddress := (role : Internal p) × Fin ((p.gate role).clauses (internal p role)).length
abbrev RowAddress := EquationAddress p ⊕ Fin p.assertions.length
abbrev IncidenceVertex := Variable p ⊕ RowAddress p
def rowClause : RowAddress p → CNF.Clause (Variable p) | .inl ⟨role, index⟩ => ((p.gate role).clauses (internal p role))[index.val] | .inr index => [p.assertions[index.val]]
def incidenceAdj : IncidenceVertex p → IncidenceVertex p → Prop | .inl v, .inr row => v ∈ (rowClause p row).map Prod.fst | .inr row, .inl v => v ∈ (rowClause p row).map Prod.fst | _, _ => False
def incidence : SimpleGraph (IncidenceVertex p) where
  Adj := incidenceAdj p
  symm := ⟨by intro u v h; cases u <;> cases v <;> exact h⟩
  loopless := ⟨by intro v h; cases v <;> exact h⟩
/-- incidence treewidth lower: Critical sets, query, width and backdoor obstructions. -/
theorem incidence_treewidth_lower (w : ℕ) (bound : TreewidthLE (incidence p) w) : min p.channels p.buses ≤ w := by { sorry }
end NativeWidth
end Controller.Graph
namespace Controller.Boundaries.Backdoors
open Controller
variable {α : Type*} [DecidableEq α]
def HornClause (clause : CNF.Clause α) : Prop := ∀ left ∈ clause, ∀ right ∈ clause, left.2 = true → right.2 = true → left.1 = right.1
def TwoClause (clause : CNF.Clause α) : Prop := ∀ first ∈ clause, ∀ second ∈ clause, ∀ third ∈ clause, first = second ∨ first = third ∨ second = third
def Horn (formula : List (CNF.Clause α)) : Prop := ∀ clause ∈ formula, HornClause clause
def TwoCNF (formula : List (CNF.Clause α)) : Prop := ∀ clause ∈ formula, TwoClause clause
def renameLiteral (phase : α → Bool) (literal : CNF.Literal α) : CNF.Literal α := (literal.1, if phase literal.1 then !literal.2 else literal.2)
def renameClause (phase : α → Bool) (clause : CNF.Clause α) := clause.map (renameLiteral phase)
def RenamableHorn (formula : List (CNF.Clause α)) : Prop := ∃ phase : α → Bool, Horn (formula.map (renameClause phase))
inductive BaseClass where
  | horn | renamableHorn | twoCNF
  deriving DecidableEq
def InClass (target : BaseClass) (formula : List (CNF.Clause α)) : Prop :=
  match target with
  | .horn => Horn formula
  | .renamableHorn => RenamableHorn formula
  | .twoCNF => TwoCNF formula
def deleteClause (backdoor : Finset α) (clause : CNF.Clause α) := clause.filter fun literal => literal.1 ∉ backdoor
def delete (backdoor : Finset α) (formula : List (CNF.Clause α)) := formula.map (deleteClause backdoor)
def restrictClause (backdoor : Finset α) (assignment : α → Bool) (clause : CNF.Clause α) : Option (CNF.Clause α) := if ∃ literal ∈ clause, literal.1 ∈ backdoor ∧ assignment literal.1 = literal.2 then none else some (deleteClause backdoor clause)
def restrict (backdoor : Finset α) (assignment : α → Bool) (formula : List (CNF.Clause α)) := formula.filterMap (restrictClause backdoor assignment)
def DeletionBackdoor (target : BaseClass) (formula : List (CNF.Clause α)) (backdoor : Finset α) : Prop := InClass target (delete backdoor formula)
def StrongBackdoor (target : BaseClass) (formula : List (CNF.Clause α)) (backdoor : Finset α) : Prop := ∀ assignment : α → Bool, InClass target (restrict backdoor assignment formula)
open Native
open Native.Bounded
/-- native backdoor lower bound: Critical sets, query, width and backdoor obstructions. -/
theorem native_backdoor_lower_bound (parameters : Parameters) (target : BaseClass) (backdoor : Finset (GlobalVariable parameters)) (valid : DeletionBackdoor target (globalFormula parameters).clauses.toList backdoor ∨ StrongBackdoor target (globalFormula parameters).clauses.toList backdoor) : parameters.buses ≤ backdoor.card := by sorry
/-- specification backdoor lower bound: Critical sets, query, width and backdoor obstructions. -/
theorem specification_backdoor_lower_bound (parameters : Parameters) (target : BaseClass) (backdoor : Finset (Variable parameters)) (valid : DeletionBackdoor target parameters.specificationFormula.clauses.toList backdoor ∨ StrongBackdoor target parameters.specificationFormula.clauses.toList backdoor) : parameters.buses ≤ backdoor.card := by { sorry }
end Controller.Boundaries.Backdoors
namespace Controller.Graph.BoundedCircuit
open Controller.Native Controller.Native.Parameters Controller.Native.Bounded
theorem expansion_length {α : Type*} (g : CNF.Gate α) (output : CNF.Literal α) : (expand output g).length = auxiliaryCount g + 1 := by { rw [expand_length]; cases g <;> simp only [expansionProducerCount, auxiliaryCount, foldProducerCount] <;> omega }
abbrev Gate (p : Parameters) := Σ owner : Internal p, Fin (auxiliaryCount (p.gate owner) + 1)
instance (p : Parameters) : Fintype (Gate p) := by
  letI : Fintype (Internal p) := Fintype.ofList p.roles p.mem_roles
  exact inferInstanceAs (Fintype (Σ owner : Internal p, Fin (auxiliaryCount (p.gate owner) + 1)))
def gateList (p : Parameters) (owner : Internal p) : List (Producer (GlobalVariable p)) := (expand (p.internal owner) (p.gate owner)).map (Producer.relabel (localSlots p owner))
theorem gateList_length (p : Parameters) (owner : Internal p) : (gateList p owner).length = auxiliaryCount (p.gate owner) + 1 := by { simp only [gateList, List.length_map, expansion_length] }
def producer (p : Parameters) (g : Gate p) : Producer (GlobalVariable p) := (gateList p g.1)[g.2.val]'(by { rw [gateList_length]; exact g.2.isLt })
def output (p : Parameters) (g : Gate p) : GlobalVariable p := if h : g.2.val < auxiliaryCount (p.gate g.1) then .auxiliary g.1 ⟨g.2.val, h⟩ else .original (.internal g.1)
def principal (p : Parameters) (owner : Internal p) : Gate p := ⟨owner, Fin.last (auxiliaryCount (p.gate owner))⟩
def privateGate (p : Parameters) (owner : Internal p) (index : Fin (auxiliaryCount (p.gate owner))) : Gate p := ⟨owner, index.castSucc⟩
def producerSlot (p : Parameters) : GlobalVariable p → PrimaryRole p.channels p.buses ⊕ Gate p | .original (.primary input) => .inl input | .original (.internal owner) => .inr (principal p owner) | .auxiliary owner index => .inr (privateGate p owner index)
noncomputable def layout (p : Parameters) : CircuitLayout (PrimaryRole p.channels p.buses) (Gate p) Unit (GlobalVariable p) where
  producer := producerSlot p
  consumers s :=
    (Finset.univ.filter (fun g => s ∈ (producer p g).gate.inputs.map Prod.fst)).image Sum.inl ∪
      if s = .original (.internal .detected) then {Sum.inr ()} else ∅
abbrev Vertex (p : Parameters) := PrimaryRole p.channels p.buses ⊕ Gate p ⊕ Unit
instance (p : Parameters) : Fintype (Vertex p) := by
  letI : Fintype (PrimaryRole p.channels p.buses) := Fintype.ofList p.primaryRoles p.mem_primaryRoles
  exact inferInstanceAs (Fintype (PrimaryRole p.channels p.buses ⊕ Gate p ⊕ Unit))
end Controller.Graph.BoundedCircuit
namespace Controller.Graph
variable {V B : Type} [Fintype V] [DecidableEq V] [DecidableEq B]
section Quotient
variable {A B V : Type} [DecidableEq A] [DecidableEq B] [DecidableEq V]
def blockGraph (G : SimpleGraph A) (partition : A → B) : SimpleGraph B where
  Adj b c := b ≠ c ∧ ∃ x y, partition x = b ∧ partition y = c ∧ G.Adj x y
  symm := ⟨by { rintro b c ⟨ne, x, y, hx, hy, edge⟩; exact ⟨ne.symm, y, x, hy, hx, edge.symm⟩ }⟩
  loopless := ⟨fun _ h => h.1 rfl⟩
end Quotient
namespace CircuitLayout
variable {Input Gate Signal Owner Block : Type} [DecidableEq Gate] [DecidableEq Owner] [Fintype Signal] [Fintype Gate]
noncomputable def gateBlock [DecidableEq Block] (partition : Gate → Block) (b : Block) : Finset Gate := Finset.univ.filter fun g => partition g = b
end CircuitLayout
end Controller.Graph
namespace Controller.Reductions
open Decoder
structure EnumeratedGraph (n m : ℕ) where
  (left : Fin m → Fin n) (right : Fin m → Fin n) (ordered : ∀ e, (left e).val < (right e).val) (unique : Function.Injective (fun e => (left e, right e)))
namespace EnumeratedGraph
variable {n m : ℕ} (J : EnumeratedGraph n m)
def Adj (u v : Fin n) : Prop := ∃ e, (J.left e = u ∧ J.right e = v) ∨ (J.left e = v ∧ J.right e = u)
def graph : SimpleGraph (Fin n) where
  Adj := J.Adj
  symm := by { constructor; rintro u v ⟨e, h | h⟩; · { exact ⟨e, Or.inr h⟩ }; · { exact ⟨e, Or.inl h⟩ } }
  loopless := by { constructor; rintro u ⟨e, h | h⟩ <;> have ho := J.ordered e <;> rw [h.1, h.2] at ho <;> omega }
end EnumeratedGraph
variable {n m : ℕ}
def coverTarget (n : ℕ) : Channel (n + 1) := Fin.last n
def coverDAG (J : EnumeratedGraph n m) : DAG (n + 1) where
  nodeCount := m + 2
  node := fun index =>
    if first : index.val = 0 then .input (coverTarget n)
    else if term : index.val < m + 1 then
      let e : Fin m := ⟨index.val - 1, by { omega }⟩
      .guard ⟨0, by { omega }⟩ [(J.left e).castSucc, (J.right e).castSucc]
    else .disj (List.ofFn fun e : Fin m => ⟨e.val + 1, by { omega }⟩)
  roots := [⟨m + 1, by { omega }⟩]
def coverBridge (driver : Fin n) : Physical.Bridge (n + 1) where
  target := coverTarget n; drivers := {driver.castSucc}
  drivers_nonempty := by { simp }
  target_not_mem := by { simp only [Finset.mem_singleton]; intro equal; have values := congrArg Fin.val equal; change n = driver.val at values; omega }
end Controller.Reductions
namespace Controller.Counting
open Reductions
variable {n m : ℕ}
def coverParameters (J : EnumeratedGraph n m) (driver : Fin n) (layout : Native.PrefixLayout) : Native.Parameters where
  channels := n + 1; buses := 1
  positiveBuses := by { decide }
  bridge := coverBridge driver; decoder := coverDAG J; layout := layout; drive := true
end Controller.Counting
namespace Controller.Graph
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
noncomputable def outerBoundary (G : SimpleGraph V) (U : Finset V) : Finset V := by { classical{ exact Finset.univ.filter fun v => v ∉ U ∧ ∃ u ∈ U, G.Adj u v } }
def VertexExpansion (G : SimpleGraph V) (c : ℕ) : Prop := 0 < c ∧ ∀ U : Finset V, 2 * U.card ≤ Fintype.card V → U.card ≤ c * (outerBoundary G U).card
namespace BoundedCover
open Controller.Reductions Controller.Counting Controller.Native Controller.Native.Parameters
open Controller.Native.Bounded Controller.Decoder
variable {n m : ℕ} (J : EnumeratedGraph n m) (driver : Fin n) (layout : PrefixLayout)
def primal : SimpleGraph (GlobalVariable (coverParameters J driver layout)) := clausePrimal (globalFormula (coverParameters J driver layout)).clauses.toList
noncomputable def neighbors (v : Fin n) : Finset (Fin n) := by { classical{ exact Finset.univ.filter fun u => J.graph.Adj v u } }
def size : Controller.NativeSize where
  variableCount := (globalVariables (coverParameters J driver layout)).length; clauses := (globalFormula (coverParameters J driver layout)).clauses.size; literals := literalIncidences (globalFormula (coverParameters J driver layout))
def variableLiteralSize : ℕ := (size J driver layout).variableCount + (size J driver layout).literals
end BoundedCover
end Controller.Graph
namespace Controller.Graph.CoverCircuit
open Controller.Reductions Controller.Counting Controller.Native Controller.Native.Parameters
open Controller.Native.Bounded Controller.Graph.BoundedCircuit
variable {n m : ℕ} (J : EnumeratedGraph n m) (driver : Fin n) (layout : PrefixLayout)
abbrev parameters := coverParameters J driver layout
def gateGraph : SimpleGraph (Gate (parameters J driver layout)) where
  Adj g h := g ≠ h ∧
    (output _ g ∈ (producer _ h).gate.inputs.map Prod.fst ∨
     output _ h ∈ (producer _ g).gate.inputs.map Prod.fst)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩; loopless := ⟨fun _ h => h.1 rfl⟩
noncomputable def portGraph : SimpleGraph (Vertex (parameters J driver layout)) := (BoundedCircuit.layout (parameters J driver layout)).wireGraph
end Controller.Graph.CoverCircuit
namespace Controller.Graph
namespace ClauseOccurrence
variable {V : Type} [DecidableEq V] (clauses : List (CNF.Clause V))
abbrev Vertex := V ⊕ Fin clauses.length
def incidence : SimpleGraph (Vertex clauses) where
  Adj x y := match x, y with
    | .inl v, .inr i | .inr i, .inl v => v ∈ (clauses.get i).map Prod.fst
    | _, _ => False
  symm := ⟨by { intro x y h; cases x <;> cases y <;> exact h }⟩
  loopless := ⟨by { intro x; cases x <;> simp }⟩
end ClauseOccurrence
namespace CoverCircuit
open Controller.Reductions Controller.Counting Controller.Native Controller.Native.Parameters
open Controller.Native.Bounded Controller.Graph.BoundedCircuit
variable {n m : ℕ} (J : EnumeratedGraph n m) (driver : Fin n) (layout : PrefixLayout)
def incidenceGraph := ClauseOccurrence.incidence (globalFormula (parameters J driver layout)).clauses.toList
end CoverCircuit
end Controller.Graph
namespace Controller.Graph.CoverCircuit
open Controller.Reductions Controller.Counting Controller.Native Controller.Native.Parameters
open Controller.Native.Bounded Controller.Graph.BoundedCircuit
variable {n m : ℕ} (J : EnumeratedGraph n m) (driver : Fin n) (layout : PrefixLayout)
noncomputable def fullNets := (BoundedCircuit.layout (parameters J driver layout)).nets
/-- linear width obstruction: Critical sets, query, width and backdoor obstructions. -/
theorem linear_width_obstruction (c D : ℕ) (expansion : VertexExpansion J.graph c)
    (degree : ∀ v, (BoundedCover.neighbors J v).card ≤ D) :
    let N := BoundedCover.variableLiteralSize J driver layout
    let C := 12000*c*(D+1)
    (∀ w, TreewidthLE (portGraph J driver layout) w → N ≤ C*(w+1)) ∧
    (∀ w, TreewidthLE (BoundedCover.primal J driver layout) w → N ≤ C*(w+1)) ∧
    (∀ w, TreewidthLE (incidenceGraph J driver layout) w → N ≤ C*(w+1)) ∧
    (∀ k, (fullNets J driver layout).NetCutwidthLE k → N ≤ C*(D+4)*k) ∧
    (∀ (Block : Type) [DecidableEq Block] (partition : Gate (parameters J driver layout) → Block)
      K w, (∀ b, ((BoundedCircuit.layout (parameters J driver layout)).blockInputs
        (CircuitLayout.gateBlock partition b)).card ≤ K) →
      TreewidthLE (blockGraph (gateGraph J driver layout) partition) w → N ≤ C*(K*(w+1))) := by { sorry }
end Controller.Graph.CoverCircuit
