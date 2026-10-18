module
public meta import Lean.Elab.Tactic.ElabTerm
public meta import Lean.Elab.Command
public meta import Lean.Meta.Match.Match
meta import all Lean.Meta.Match.Match
public meta import Lean.Meta.Constructions.SparseCasesOn
meta import all Lean.Meta.Constructions.SparseCasesOn
public meta import Lean.Meta.Tactic.AuxLemma

public import Lean.Elab.Tactic.Omega
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Algebra.Order.Group.Nat
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
public import Mathlib.Data.List.Sublists
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Vector.Basic
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Logic.Relation
public import Mathlib.Order.WellFounded
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.ClearExcept
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Std.Sat.CNF
/- Preserve source-module names and module-local elaboration caches when
   flattening definitions. Every declaration is still checked by Lean. -/
open Lean Elab Command in
elab "source_context " source:str : command => do
  let root := (← getOptions).get `sourceContextRoot ""
  if root.isEmpty then
    let original := (← getEnv).mainModule
    modifyScope fun scope => { scope with opts := scope.opts.set `sourceContextRoot original.toString }
  modifyEnv fun env =>
    let env := env.setMainModule source.getString.toName
    let env := Meta.auxLemmasExt.setState env {}
    let env := (private_decl% Lean.Meta.Match.matcherExt).setState env {}
    (private_decl% Lean.Meta.sparseCasesOnCacheExt).setState env {}
open Lean Elab Command in
elab "end_source_context" : command => do
  let root := (← getOptions).get `sourceContextRoot ""
  if root.isEmpty then throwError "missing original Challenge module"
  modifyEnv (·.setMainModule root.toName)

set_option backward.privateInPublic true
open Lean Elab Tactic in
elab "source_exact " proof:term : tactic => withoutExporting <| Lean.Meta.withTransparency .all do
  evalTactic (← `(tactic| exact $proof))
@[expose] public section
noncomputable section
/-!
# Bounded live conjunction and proper-basis algorithms
The grammar, state transitions, resource measures and mathematical predicates
are explicit. Definition holes identify only implementation witnesses; the
selected universal theorems constrain their executions or returned results.
The selected statements retain the exact assumptions of the proof library.
-/
/- Source-exported auxiliary proofs; addDecl checks every complete proof. -/
open Lean Elab Command in
run_cmd do
  let e0 : Lean.Expr := .sort (Lean.Level.succ (Lean.Level.param `u_1)); let e1 : Lean.Expr := .const (`AddMonoidWithOne) ([Lean.Level.param `u_1]); let e2 : Lean.Expr := .bvar 0; let e3 : Lean.Expr := .app e1 e2; let e4 : Lean.Expr := .const (`PartialOrder) ([Lean.Level.param `u_1]); let e5 : Lean.Expr := .bvar 1; let e6 : Lean.Expr := .app e4 e5; let e7 : Lean.Expr := .const (`ZeroLEOneClass) ([Lean.Level.param `u_1]); let e8 : Lean.Expr := .bvar 2; let e9 : Lean.Expr := .app e7 e8; let e10 : Lean.Expr := .const (`AddZero.toZero) ([Lean.Level.param `u_1]); let e11 : Lean.Expr := .app e10 e8; let e12 : Lean.Expr := .const (`AddZeroClass.toAddZero) ([Lean.Level.param `u_1]); let e13 : Lean.Expr := .app e12 e8; let e14 : Lean.Expr := .const (`AddMonoid.toAddZeroClass) ([Lean.Level.param `u_1]); let e15 : Lean.Expr := .app e14 e8; let e16 : Lean.Expr := .const (`AddMonoidWithOne.toAddMonoid) ([Lean.Level.param `u_1]); let e17 : Lean.Expr := .app e16 e8; let e18 : Lean.Expr := .app e17 e5; let e19 : Lean.Expr := .app e15 e18; let e20 : Lean.Expr := .app e13 e19; let e21 : Lean.Expr := .app e11 e20; let e22 : Lean.Expr := .app e9 e21; let e23 : Lean.Expr := .const (`AddMonoidWithOne.toOne) ([Lean.Level.param `u_1]); let e24 : Lean.Expr := .app e23 e8; let e25 : Lean.Expr := .app e24 e5; let e26 : Lean.Expr := .app e22 e25; let e27 : Lean.Expr := .const (`Preorder.toLE) ([Lean.Level.param `u_1]); let e28 : Lean.Expr := .app e27 e8; let e29 : Lean.Expr := .const (`PartialOrder.toPreorder) ([Lean.Level.param `u_1]); let e30 : Lean.Expr := .app e29 e8; let e31 : Lean.Expr := .app e30 e2; let e32 : Lean.Expr := .app e28 e31; let e33 : Lean.Expr := .app e26 e32; let e34 : Lean.Expr := .const (`NeZero) ([Lean.Level.param `u_1]); let e35 : Lean.Expr := .bvar 3; let e36 : Lean.Expr := .app e34 e35; let e37 : Lean.Expr := .app e10 e35; let e38 : Lean.Expr := .app e12 e35; let e39 : Lean.Expr := .app e14 e35; let e40 : Lean.Expr := .app e16 e35; let e41 : Lean.Expr := .app e40 e8; let e42 : Lean.Expr := .app e39 e41; let e43 : Lean.Expr := .app e38 e42; let e44 : Lean.Expr := .app e37 e43; let e45 : Lean.Expr := .app e36 e44; let e46 : Lean.Expr := .const (`OfNat.ofNat) ([Lean.Level.param `u_1]); let e47 : Lean.Expr := .app e46 e35; let e48 : Lean.Expr := .lit (Lean.Literal.natVal 1); let e49 : Lean.Expr := .app e47 e48; let e50 : Lean.Expr := .const (`One.toOfNat1) ([Lean.Level.param `u_1]); let e51 : Lean.Expr := .app e50 e35; let e52 : Lean.Expr := .app e23 e35; let e53 : Lean.Expr := .app e52 e8; let e54 : Lean.Expr := .app e51 e53; let e55 : Lean.Expr := .app e49 e54; let e56 : Lean.Expr := .app e45 e55; let e57 : Lean.Expr := .const (`AddLeftMono) ([Lean.Level.param `u_1]); let e58 : Lean.Expr := .bvar 4; let e59 : Lean.Expr := .app e57 e58; let e60 : Lean.Expr := .const (`AddSemigroup.toAdd) ([Lean.Level.param `u_1]); let e61 : Lean.Expr := .app e60 e58; let e62 : Lean.Expr := .const (`AddMonoid.toAddSemigroup) ([Lean.Level.param `u_1]); let e63 : Lean.Expr := .app e62 e58; let e64 : Lean.Expr := .app e16 e58; let e65 : Lean.Expr := .app e64 e35; let e66 : Lean.Expr := .app e63 e65; let e67 : Lean.Expr := .app e61 e66; let e68 : Lean.Expr := .app e59 e67; let e69 : Lean.Expr := .app e27 e58; let e70 : Lean.Expr := .app e29 e58; let e71 : Lean.Expr := .app e70 e8; let e72 : Lean.Expr := .app e69 e71; let e73 : Lean.Expr := .app e68 e72; let e74 : Lean.Expr := .const (`Eq) ([Lean.Level.succ (Lean.Level.zero)]); let e75 : Lean.Expr := .sort (Lean.Level.zero); let e76 : Lean.Expr := .app e74 e75; let e77 : Lean.Expr := .const (`LT.lt) ([Lean.Level.param `u_1]); let e78 : Lean.Expr := .bvar 5; let e79 : Lean.Expr := .app e77 e78; let e80 : Lean.Expr := .const (`Preorder.toLT) ([Lean.Level.param `u_1]); let e81 : Lean.Expr := .app e80 e78; let e82 : Lean.Expr := .app e29 e78; let e83 : Lean.Expr := .app e82 e35; let e84 : Lean.Expr := .app e81 e83; let e85 : Lean.Expr := .app e79 e84; let e86 : Lean.Expr := .app e46 e78; let e87 : Lean.Expr := .lit (Lean.Literal.natVal 0); let e88 : Lean.Expr := .app e86 e87; let e89 : Lean.Expr := .const (`Zero.toOfNat0) ([Lean.Level.param `u_1]); let e90 : Lean.Expr := .app e89 e78; let e91 : Lean.Expr := .app e10 e78; let e92 : Lean.Expr := .app e12 e78; let e93 : Lean.Expr := .app e14 e78; let e94 : Lean.Expr := .app e16 e78; let e95 : Lean.Expr := .app e94 e58; let e96 : Lean.Expr := .app e93 e95; let e97 : Lean.Expr := .app e92 e96; let e98 : Lean.Expr := .app e91 e97; let e99 : Lean.Expr := .app e90 e98; let e100 : Lean.Expr := .app e88 e99; let e101 : Lean.Expr := .app e85 e100; let e102 : Lean.Expr := .lit (Lean.Literal.natVal 2); let e103 : Lean.Expr := .app e86 e102; let e104 : Lean.Expr := .const (`instOfNatAtLeastTwo) ([Lean.Level.param `u_1]); let e105 : Lean.Expr := .app e104 e78; let e106 : Lean.Expr := .app e105 e102; let e107 : Lean.Expr := .const (`AddMonoidWithOne.toNatCast) ([Lean.Level.param `u_1]); let e108 : Lean.Expr := .app e107 e78; let e109 : Lean.Expr := .app e108 e58; let e110 : Lean.Expr := .app e106 e109; let e111 : Lean.Expr := .const (`Nat.instAtLeastTwoHAddOfNat) ([]); let e112 : Lean.Expr := .const (`OfNat.ofNat) ([Lean.Level.zero]); let e113 : Lean.Expr := .const (`Nat) ([]); let e114 : Lean.Expr := .app e112 e113; let e115 : Lean.Expr := .app e114 e48; let e116 : Lean.Expr := .const (`instOfNatNat) ([]); let e117 : Lean.Expr := .app e116 e48; let e118 : Lean.Expr := .app e115 e117; let e119 : Lean.Expr := .app e111 e118; let e120 : Lean.Expr := .const (`Nat.instNeZeroSucc) ([]); let e121 : Lean.Expr := .app e114 e87; let e122 : Lean.Expr := .app e116 e87; let e123 : Lean.Expr := .app e121 e122; let e124 : Lean.Expr := .app e120 e123; let e125 : Lean.Expr := .app e119 e124; let e126 : Lean.Expr := .app e110 e125; let e127 : Lean.Expr := .app e103 e126; let e128 : Lean.Expr := .app e101 e127; let e129 : Lean.Expr := .app e76 e128; let e130 : Lean.Expr := .const (`True) ([]); let e131 : Lean.Expr := .app e129 e130; let e132 : Lean.Expr := .forallE .anonymous e73 e131 (Lean.BinderInfo.instImplicit); let e133 : Lean.Expr := .forallE .anonymous e56 e132 (Lean.BinderInfo.instImplicit); let e134 : Lean.Expr := .forallE .anonymous e33 e133 (Lean.BinderInfo.instImplicit); let e135 : Lean.Expr := .forallE .anonymous e6 e134 (Lean.BinderInfo.instImplicit); let e136 : Lean.Expr := .forallE .anonymous e3 e135 (Lean.BinderInfo.instImplicit); let e137 : Lean.Expr := .forallE .anonymous e0 e136 (Lean.BinderInfo.implicit); let e138 : Lean.Expr := .const (`eq_true) ([]); let e139 : Lean.Expr := .app e138 e128; let e140 : Lean.Expr := .const (`zero_lt_two) ([Lean.Level.param `u_1]); let e141 : Lean.Expr := .app e140 e78; let e142 : Lean.Expr := .app e141 e58; let e143 : Lean.Expr := .app e142 e35; let e144 : Lean.Expr := .app e143 e8; let e145 : Lean.Expr := .app e144 e5; let e146 : Lean.Expr := .app e145 e2; let e147 : Lean.Expr := .app e139 e146; let e148 : Lean.Expr := .lam .anonymous e73 e147 (Lean.BinderInfo.instImplicit); let e149 : Lean.Expr := .lam .anonymous e56 e148 (Lean.BinderInfo.instImplicit); let e150 : Lean.Expr := .lam .anonymous e33 e149 (Lean.BinderInfo.instImplicit); let e151 : Lean.Expr := .lam .anonymous e6 e150 (Lean.BinderInfo.instImplicit); let e152 : Lean.Expr := .lam .anonymous e3 e151 (Lean.BinderInfo.instImplicit); let e153 : Lean.Expr := .lam .anonymous e0 e152 (Lean.BinderInfo.implicit); let fact : Lean.TheoremVal := { name := `zero_lt_two._simp_1, levelParams := [`u_1], type := e137, value := e153 }; if let some old := (← getEnv).toKernelEnv.find? fact.name then unless old == .thmInfo fact do throwError "conflicting Source auxiliary fact" else liftCoreM <| addDecl (.thmDecl fact)
open Lean Elab Command in
run_cmd do
  let e0 : Lean.Expr := .const (`Nat) ([]); let e1 : Lean.Expr := .const (`Eq) ([Lean.Level.succ (Lean.Level.zero)]); let e2 : Lean.Expr := .sort (Lean.Level.zero); let e3 : Lean.Expr := .app e1 e2; let e4 : Lean.Expr := .const (`LT.lt) ([Lean.Level.zero]); let e5 : Lean.Expr := .app e4 e0; let e6 : Lean.Expr := .const (`instLTNat) ([]); let e7 : Lean.Expr := .app e5 e6; let e8 : Lean.Expr := .bvar 0; let e9 : Lean.Expr := .app e7 e8; let e10 : Lean.Expr := .const (`HAdd.hAdd) ([Lean.Level.zero, Lean.Level.zero, Lean.Level.zero]); let e11 : Lean.Expr := .app e10 e0; let e12 : Lean.Expr := .app e11 e0; let e13 : Lean.Expr := .app e12 e0; let e14 : Lean.Expr := .const (`instHAdd) ([Lean.Level.zero]); let e15 : Lean.Expr := .app e14 e0; let e16 : Lean.Expr := .const (`instAddNat) ([]); let e17 : Lean.Expr := .app e15 e16; let e18 : Lean.Expr := .app e13 e17; let e19 : Lean.Expr := .app e18 e8; let e20 : Lean.Expr := .const (`OfNat.ofNat) ([Lean.Level.zero]); let e21 : Lean.Expr := .app e20 e0; let e22 : Lean.Expr := .lit (Lean.Literal.natVal 1); let e23 : Lean.Expr := .app e21 e22; let e24 : Lean.Expr := .const (`instOfNatNat) ([]); let e25 : Lean.Expr := .app e24 e22; let e26 : Lean.Expr := .app e23 e25; let e27 : Lean.Expr := .app e19 e26; let e28 : Lean.Expr := .app e9 e27; let e29 : Lean.Expr := .app e3 e28; let e30 : Lean.Expr := .const (`True) ([]); let e31 : Lean.Expr := .app e29 e30; let e32 : Lean.Expr := .forallE .anonymous e0 e31 (Lean.BinderInfo.default); let e33 : Lean.Expr := .const (`eq_true) ([]); let e34 : Lean.Expr := .app e33 e28; let e35 : Lean.Expr := .const (`Nat.lt_add_one) ([]); let e36 : Lean.Expr := .app e35 e8; let e37 : Lean.Expr := .app e34 e36; let e38 : Lean.Expr := .lam .anonymous e0 e37 (Lean.BinderInfo.default); let fact : Lean.TheoremVal := { name := `Nat.lt_add_one._simp_1, levelParams := [], type := e32, value := e38 }; if let some old := (← getEnv).toKernelEnv.find? fact.name then unless old == .thmInfo fact do throwError "conflicting Source auxiliary fact" else liftCoreM <| addDecl (.thmDecl fact)
source_context "Controller.Basic.Assignments"
namespace Controller
abbrev Channel (n : ℕ) := Fin n
abbrev Assignment (n : ℕ) := Channel n → Bool
def assignmentOfSet {n : ℕ} (K : Finset (Channel n)) : Assignment n := fun i => decide (i ∈ K)
def setOfAssignment {n : ℕ} (a : Assignment n) : Finset (Channel n) := Finset.univ.filter (fun i => a i = true)
end Controller
source_context "Controller.Basic.Sizes"
namespace Controller
structure DecoderSize where
  (channels : ℕ) (nodes : ℕ) (children : ℕ) (guards : ℕ) (roots : ℕ)
  deriving Repr, DecidableEq
def DecoderSize.total (s : DecoderSize) : ℕ := s.channels + s.nodes + s.children + s.guards + s.roots
structure NativeSize where
  (variableCount : ℕ) (clauses : ℕ) (literals : ℕ)
  deriving Repr, DecidableEq
def NativeSize.total (s : NativeSize) : ℕ := s.variableCount + s.clauses + s.literals
end Controller
source_context "Controller.Decoder.Syntax"
namespace Controller.Decoder
inductive Gate (n available : ℕ) where
  | zero : Gate n available | input (channel : Channel n) : Gate n available | disj (children : List (Fin available)) : Gate n available | guard (child : Fin available) (labels : List (Channel n)) : Gate n available | liveAnd (left right : Fin available) : Gate n available
  deriving DecidableEq, Repr
namespace Gate
variable {n available : ℕ}
def children : Gate n available → List (Fin available) | .zero => [] | .input _ => [] | .disj refs => refs | .guard child _ => [child] | .liveAnd left right => [left, right]
def guardLabels : Gate n available → List (Channel n) | .guard _ labels => labels | _ => []
def isLiveAnd : Gate n available → Bool | .liveAnd _ _ => true | _ => false
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
theorem childIndex_lt (graph : DAG n) (parent : Fin graph.nodeCount) (child : Fin parent.val) : (graph.childIndex parent child).val < parent.val := child.isLt
def childIncidences (graph : DAG n) : ℕ := @List.sum Nat instAddNat (@Zero.ofOfNat0 Nat (instOfNatNat (nat_lit 0))) (List.ofFn fun index : Fin graph.nodeCount => (graph.node index).children.length)
def guardIncidences (graph : DAG n) : ℕ := @List.sum Nat instAddNat (@Zero.ofOfNat0 Nat (instOfNatNat (nat_lit 0))) (List.ofFn fun index : Fin graph.nodeCount => (graph.node index).guardLabels.length)
def liveAndNodes (graph : DAG n) : Finset (Fin graph.nodeCount) := Finset.univ.filter fun index => (graph.node index).isLiveAnd = true
def liveAndCount (graph : DAG n) : ℕ := graph.liveAndNodes.card
def size (graph : DAG n) : DecoderSize where
  channels := n; nodes := graph.nodeCount; children := graph.childIncidences; guards := graph.guardIncidences; roots := graph.roots.length
def countedSize (graph : DAG n) : ℕ := graph.size.total
end DAG
namespace Gate
def IsGuarded (gate : Gate n available) : Prop := gate.isLiveAnd = false
end Gate
namespace DAG
def Guarded (graph : DAG n) : Prop := ∀ index, (graph.node index).IsGuarded
end DAG
end Controller.Decoder
source_context "Controller.Decoder.Eval"
namespace Controller.Decoder
namespace DAG
variable {n : ℕ}
def eval (graph : DAG n) (assignment : Assignment n) (index : Fin graph.nodeCount) : Bool :=
  (graph.node index).eval assignment (fun child => graph.eval assignment (graph.childIndex index child))
termination_by index.val
decreasing_by exact graph.childIndex_lt index child
def evalPrefix (graph : DAG n) (assignment : Assignment n) :
    (length : ℕ) → length ≤ graph.nodeCount → Fin length → Bool
  | 0, _ => Fin.elim0
  | length + 1, bound =>
      let earlier := graph.evalPrefix assignment length
        (Nat.le_trans (Nat.le_succ length) bound)
      let gate := graph.node ⟨length, Nat.lt_of_lt_of_le (Nat.lt_succ_self length) bound⟩
      Fin.lastCases (gate.eval assignment earlier) earlier
def evalTable (graph : DAG n) (assignment : Assignment n) : Fin graph.nodeCount → Bool := graph.evalPrefix assignment graph.nodeCount (Nat.le_refl graph.nodeCount)
end DAG
end Controller.Decoder
source_context "Controller.Basic.Admissible"
namespace Controller
def Admissible {n : ℕ} (b : ℕ) (t : Channel n) (K : Finset (Channel n)) : Prop := K.Nonempty ∧ (b = 1 → t ∈ K)
end Controller
source_context "Controller.Extensions.Support"
namespace Controller.Decoder
namespace DAG
/-- exists small true support: Bounded live conjunction and proper-basis algorithms. -/
theorem exists_small_true_support (graph : DAG n) (K : Finset (Channel n)) (root : Fin graph.nodeCount) (active : graph.eval (assignmentOfSet K) root = true) (k : ℕ) (bound : graph.liveAndCount ≤ k) : ∃ support : Finset (Channel n), support ⊆ K ∧ support.Nonempty ∧ support.card ≤ k + 1 ∧ graph.eval (assignmentOfSet support) root = true := by sorry
/-- exists small target support: Bounded live conjunction and proper-basis algorithms. -/
theorem exists_small_target_support (graph : DAG n) (K : Finset (Channel n)) (root : Fin graph.nodeCount) (active : graph.eval (assignmentOfSet K) root = true) (target : Channel n) (targetIn : target ∈ K) (k : ℕ) (bound : graph.liveAndCount ≤ k) (busCount : ℕ) : ∃ support : Finset (Channel n), support ⊆ K ∧ target ∈ support ∧ support.card ≤ k + 2 ∧ Admissible busCount target support ∧ graph.eval (assignmentOfSet support) root = true := by sorry
end DAG
end Controller.Decoder
source_context "Controller.Decoder.Cone"
namespace Controller.Decoder
namespace DAG
variable {n : ℕ}
def cone (graph : DAG n) (root : Fin graph.nodeCount) : Finset (Fin graph.nodeCount) :=
  insert root ((graph.node root).children.toFinset.biUnion fun child => graph.cone (graph.childIndex root child))
termination_by root.val
decreasing_by exact graph.childIndex_lt root child
def ChildClosed (graph : DAG n) (nodes : Finset (Fin graph.nodeCount)) : Prop := ∀ parent ∈ nodes, ∀ child ∈ (graph.node parent).children, graph.childIndex parent child ∈ nodes
end DAG
end Controller.Decoder
source_context "Controller.Extensions.Expansion"
namespace Controller.Decoder
namespace Gate
def resolve (gate : Gate n available) (choice : Bool) : Gate n available :=
  match gate with
  | .liveAnd left right => .guard (if choice then right else left) []
  | other => other
end Gate
namespace DAG
abbrev Selector (graph : DAG n) (nodes : Finset (Fin graph.nodeCount)) := {index // index ∈ nodes ∩ graph.liveAndNodes} → Bool
noncomputable def selectedChoice (graph : DAG n) (nodes : Finset (Fin graph.nodeCount)) (selector : graph.Selector nodes) (index : Fin graph.nodeCount) : Bool := by
  classical
  exact if h : index ∈ nodes ∩ graph.liveAndNodes then selector ⟨index, h⟩ else false
@[reducible] noncomputable def expansion (graph : DAG n) (nodes : Finset (Fin graph.nodeCount))
    (selector : graph.Selector nodes) : DAG n where
  nodeCount := graph.nodeCount
  node index := (graph.node index).resolve (graph.selectedChoice nodes selector index)
  roots := graph.roots
/-- expansion identity: Bounded live conjunction and proper-basis algorithms. -/
theorem expansion_identity (graph : DAG n) (nodes : Finset (Fin graph.nodeCount)) (closed : graph.ChildClosed nodes) (a : Assignment n) (index : Fin graph.nodeCount) (member : index ∈ nodes) : graph.eval a index = true ↔ ∀ selector : graph.Selector nodes, (graph.expansion nodes selector).eval a index = true := by sorry
/-- cone expansion identity: Bounded live conjunction and proper-basis algorithms. -/
theorem cone_expansion_identity (graph : DAG n) (a : Assignment n) (root : Fin graph.nodeCount) : graph.eval a root = true ↔ ∀ selector : graph.Selector (graph.cone root), (graph.expansion (graph.cone root) selector).eval a root = true := by sorry
/-- global selector count: Bounded live conjunction and proper-basis algorithms. -/
theorem global_selector_count (graph : DAG n) : Fintype.card (graph.Selector Finset.univ) = 2 ^ graph.liveAndCount := by sorry
end DAG
end Controller.Decoder
source_context "Controller.Cost.Model"
namespace Controller.Cost
abbrev Word (width : Nat) := Fin (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@instPowNat.{0} Nat instNatPowNat)) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) width)
def word (width value : Nat) : Word width := ⟨value % ((@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@instPowNat Nat instNatPowNat)) 2 width)), Nat.mod_lt _ (Nat.two_pow_pos width)⟩
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
      if s.heap.size < (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@instPowNat Nat instNatPowNat)) 2 width) then some { next with heap := s.heap.push (s.reg src) }
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
source_context "Controller.Decoder.Raw"
namespace Controller.Decoder
inductive RawGate where
  | zero | input (channel : ℕ) | disj (children : List ℕ) | guard (child : ℕ) (labels : List ℕ) | liveAnd (left right : ℕ)
  deriving DecidableEq, Repr
namespace RawGate
def ofGate (gate : Gate n m) : RawGate :=
  match gate with
  | .zero => .zero
  | .input channel => .input channel.val
  | .disj refs => .disj (refs.map Fin.val)
  | .guard child labels => .guard child.val (labels.map Fin.val)
  | .liveAnd left right => .liveAnd left.val right.val
end RawGate
end Controller.Decoder
source_context "Controller.Cost.Decoder"
namespace Controller.Cost
def boolWord (width : Nat) (value : Bool) : Word width := word width (if value then 1 else 0)
end Controller.Cost
source_context "Controller.CNF.Basic"
namespace Controller.CNF
abbrev Literal (α : Type*) := Std.Sat.Literal α
abbrev OrderedFormula.Clause (α : Type u) : Type u := List (Literal α)
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
abbrev Clause (α : Type*) := Controller.CNF.OrderedFormula.Clause α
abbrev Formula (α : Type*) := Controller.CNF.OrderedFormula α
abbrev negate (l : Literal α) : Literal α := Std.Sat.Literal.negate l
def ofClauses (cs : List (Clause α)) : Formula α := ⟨cs.toArray⟩
end Controller.CNF
source_context "Controller.Cost.ForestCursorMaterialize"
namespace Controller.Cost.ForestCursorMaterialize
open Controller.Decoder Controller.Decoder.DAG
def allocatedHeap (width : ℕ) (heap : Array (Word width)) (values : List ℕ) : Array (Word width) := heap ++ (values.map (word width)).toArray
end Controller.Cost.ForestCursorMaterialize
source_context "Controller.Cost.ForestIndexedOperands"
namespace Controller.Cost.ForestIndexedOperands
open Controller.Decoder Controller.Decoder.DAG
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
  node : ∀ index : Fin graph.nodeCount, (rows[index.val]'(by rw [length_eq]; exact index.isLt)).Matches (graph.node index)
def rowBases : List Row → ℕ → ℕ → List ℕ | [], _, _ => [] | row :: rest, childCursor, guardCursor => childCursor :: guardCursor :: rowBases rest (childCursor + countSource row.children 0) (guardCursor + countSource row.guards 0)
def serializedRows (heapOffset : ℕ) (rows : List Row) (roots : List ℕ) : List ℕ :=
  let children := rowChildren rows
  let guards := rowGuards rows
  rowHeaders rows ++ rowBases rows (heapOffset + 6 * rows.length)
    (heapOffset + 6 * rows.length + children.length) ++ rowArities rows ++
    children ++ guards ++ roots
def cacheHeap (width : ℕ) (heap : Array (Word width)) (rows : List Row) (roots : List ℕ) : Array (Word width) := Controller.Cost.ForestCursorMaterialize.allocatedHeap width heap (serializedRows heap.size rows roots)
def RootsMatch (graph : DAG n) (roots : List ℕ) : Prop := roots = graph.roots.map Fin.val
def globalHeader (channels : ℕ) (rows : List Row) (roots : List ℕ) : List ℕ := [channels, countSource rows 0, countSource (rowChildren rows) 0, countSource (rowGuards rows) 0, countSource roots 0]
def inputPacket (channels heapOffset : ℕ) (rows : List Row) (roots : List ℕ) : List ℕ := globalHeader channels rows roots ++ serializedRows (heapOffset + 5) rows roots
end Controller.Cost.ForestIndexedOperands
source_context "Controller.Cost.ForestInputStored"
namespace Controller.Cost.ForestInputStored
open Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestIndexedOperands
def withValues (heap : Array (Word width)) (values : Fin m → Bool) : Array (Word width) := heap ++ (List.ofFn (fun id => boolWord width (values id))).toArray
end Controller.Cost.ForestInputStored
source_context "Controller.Cost.ForestInputPrefixStored"
namespace Controller.Cost.ForestInputPrefixStored
open Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestInputStored
def channelHeap (heap : Array (Word width)) (rows : List Row) (roots : List ℕ) (channels : Channel n → Bool) : Array (Word width) := withValues (cacheHeap width heap rows roots) channels
end Controller.Cost.ForestInputPrefixStored
source_context "Controller.Cost.UniformDAGSource"
namespace Controller.Cost.UniformDAGSource
open Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestInputStored
open Controller.Cost.ForestInputPrefixStored
def typedHead (gate : Gate n available) : ℕ :=
  match gate with
  | .input channel => channel.val
  | .guard child _ => child.val
  | .liveAnd left _ => left.val
  | _ => 0
structure HeadsMatch (graph : DAG n) (rows : List Row)
  (matched : RowsMatch graph rows) : Prop where
  head : ∀ node : Fin graph.nodeCount,
    (rows[node.val]'(by rw [matched.length_eq]; exact node.isLt)).head =
      typedHead (graph.node node)
end Controller.Cost.UniformDAGSource
source_context "Controller.Cost.UniformDAGRun"
namespace Controller.Cost.UniformDAGRun
open Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestInputPrefixStored
open Controller.Cost.UniformDAGSource
def packetHeaderHeap (width channels : ℕ) (rows : List Row) (roots : List ℕ) : Array (Word width) := ((globalHeader channels rows roots).map (word width)).toArray
end Controller.Cost.UniformDAGRun
source_context "Controller.Cost.RawNumberingCounts"
namespace Controller.Cost.RawNumberingCounts
open Controller.Decoder Controller.Cost.ForestIndexedOperands
variable {n : Nat}
def rowOfGate : RawGate → Row | .zero => ⟨0, 0, [], []⟩ | .input channel => ⟨1, channel, [], []⟩ | .disj children => ⟨2, 0, children, []⟩ | .guard child labels => ⟨3, child, [child], labels⟩ | .liveAnd left right => ⟨4, left, [left, right], []⟩
end Controller.Cost.RawNumberingCounts
source_context "Controller.Cost.UniformDAGOutputs"
namespace Controller.Cost.UniformDAGOutputs
open Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestInputPrefixStored
open Controller.Cost.UniformDAGSource
open Controller.Cost.UniformDAGRun
def rowsOfGraph (graph : DAG n) : List Row := List.ofFn (fun node => RawNumberingCounts.rowOfGate (RawGate.ofGate (graph.node node)))
end Controller.Cost.UniformDAGOutputs
source_context "Controller.Decoder.Extend"
namespace Controller.Decoder
variable {n : ℕ}
def extensionBase (b : ℕ) (target : Channel n) (T : Finset (Channel n)) : Finset (Channel n) := if b = 1 then insert target T else T
end Controller.Decoder
source_context "Controller.CNF.Gates"
namespace Controller.CNF
inductive Gate (α : Type*) where
  | and (inputs : List (Literal α)) | or (inputs : List (Literal α)) | xor (left right : Literal α) | alias (input : Literal α) | not (input : Literal α) | constant (value : Bool)
  deriving DecidableEq, Repr
namespace Gate
def inputs : Gate α → List (Literal α)
  | .and ls | .or ls => ls
  | .xor l r => [l, r]
  | .alias l | .not l => [l]
  | .constant _ => []
def clauses (out : Literal α) : Gate α → List (Clause α) | .and ls => ls.map (fun l => [negate out, l]) ++ [out :: ls.map negate] | .or ls => ls.map (fun l => [out, negate l]) ++ [negate out :: ls] | .xor l r => [[l, r, negate out], [negate l, negate r, negate out], [l, negate r, out], [negate l, r, out]] | .alias l => [[negate out, l], [out, negate l]] | .not l => [[out, l], [negate out, negate l]] | .constant b => [[if b then out else negate out]]
def relabel (r : α → β) : Gate α → Gate β | .and ls => .and (ls.map (fun l => (r l.1, l.2))) | .or ls => .or (ls.map (fun l => (r l.1, l.2))) | .xor l k => .xor (r l.1, l.2) (r k.1, k.2) | .alias l => .alias (r l.1, l.2) | .not l => .not (r l.1, l.2) | .constant b => .constant b
end Gate
end Controller.CNF
source_context "Controller.CNF.Tseitin"
namespace Controller.CNF
inductive AcyclicCircuit (r : Nat) : Nat → Type where
  | roots : AcyclicCircuit r r | snoc {v : Nat} (previous : AcyclicCircuit r v) (gate : Gate (Fin v)) (phase : Bool) : AcyclicCircuit r (v + 1)
end Controller.CNF
source_context "Controller.Cost.NativeCircuitSize"
namespace Controller.Cost.NativeCircuitSize
open Controller.CNF
def literalCount.{u_1} {α : Type u_1} (formula : Controller.CNF.Formula.{u_1} α) : Nat := @List.sum.{0} Nat instAddNat (@AddZero.toZero.{0} Nat (@AddZeroClass.toAddZero.{0} Nat (@AddMonoid.toAddZeroClass.{0} Nat Nat.instAddMonoid))) (@List.map.{u_1, 0} (List.{u_1} (Controller.CNF.Literal.{u_1} α)) Nat (@List.length.{u_1} (Controller.CNF.Literal.{u_1} α)) (@Array.toList.{u_1} (Controller.CNF.OrderedFormula.Clause.{u_1} α) (@Controller.CNF.OrderedFormula.clauses.{u_1} α formula)))
end Controller.Cost.NativeCircuitSize
source_context "Controller.Physical.Controller"
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
def runFromFirst {n b : ℕ} (input : PrimaryInput n b) (first : Bool) : SelectorRun n b := runMasks b input.enable input.request (some first)
def qualifiersFromFirst {n b : ℕ} (input : PrimaryInput n b) (first : Bool) : Assignment n := qualifiers input.enable input.request (runFromFirst input first).flags
end Controller.Physical
source_context "Controller.Physical.Faults"
namespace Controller.Physical
structure Bridge (n : ℕ) where
  (target : Channel n) (drivers : Finset (Channel n)) (drivers_nonempty : drivers.Nonempty) (target_not_mem : target ∉ drivers)
def Bridge.remaining {n : ℕ} (bridge : Bridge n) : Finset (Channel n) := Finset.univ \ insert bridge.target bridge.drivers
def firstTerms {n b : ℕ} (input : PrimaryInput n b) : Assignment n := stageTerms input.enable (input.request input.firstBus)
def bridgeD {n b : ℕ} (bridge : Bridge n) (input : PrimaryInput n b) : Bool := decide (∀ i ∈ bridge.drivers, firstTerms input i = false)
def bridgeR {n b : ℕ} (bridge : Bridge n) (input : PrimaryInput n b) : Bool := decide (∀ i ∈ bridge.remaining, firstTerms input i = false)
def bridgeFirstFlag {n b : ℕ} (bridge : Bridge n) (input : PrimaryInput n b) (wire : Bool) : Bool := !(wire && bridgeD bridge input && bridgeR bridge input)
def bridgeQualifiers {n b : ℕ} (bridge : Bridge n) (input : PrimaryInput n b) (wire : Bool) : Assignment n := qualifiersFromFirst input (bridgeFirstFlag bridge input wire)
end Controller.Physical
source_context "Controller.Native.Encode"
namespace Controller.Native
inductive Side where
  | healthy | faulty
  deriving DecidableEq, Repr
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
namespace Parameters
def firstBus (parameters : Parameters) : Fin parameters.buses := ⟨0, parameters.positiveBuses⟩
end Parameters
end Controller.Native
source_context "Controller.Native.BoundedEncode"
namespace Controller.Native.Bounded
inductive Junction where
  | conjunction | disjunction
  deriving DecidableEq, Repr
def Junction.gate (junction : Junction) (inputs : List (CNF.Literal α)) : CNF.Gate α :=
  match junction with
  | .conjunction => .and inputs
  | .disjunction => .or inputs
structure Producer (α : Type*) where
  (output : CNF.Literal α) (gate : CNF.Gate α)
  deriving DecidableEq, Repr
def Producer.rows (producer : Producer α) : List (CNF.Clause α) := producer.gate.clauses producer.output
end Controller.Native.Bounded
source_context "Controller.Native.LayoutTransport"
namespace Controller.Native.InterfaceAlias
inductive Root (n b : ℕ) where
  | enable (channel : Fin n) | request (bus : Fin b) (channel : Fin n)
  deriving DecidableEq, Repr
end Controller.Native.InterfaceAlias
namespace Controller.Native.SourceObservation
def oldOutputRoles (parameters : Parameters) (side : Side) : List (Internal parameters) := (List.finRange parameters.buses).map (.flag side) ++ (List.finRange parameters.channels).map (.qualifier side)
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
def rootIndex : InterfaceAlias.Root n b ≃ Fin (n + n * b) := rootCoordinates.trans ((Equiv.sumCongr (Equiv.refl (Fin n)) finProdFinEquiv).trans finSumFinEquiv)
def rootID (root : InterfaceAlias.Root n b) : ℕ := (rootIndex root).val + 1
def rootCount (parameters : Parameters) : ℕ := parameters.channels + parameters.channels * parameters.buses
end Controller.Native.SourceInitialIDs
namespace Controller.Native.SourceSerialFold
structure Layer where
  (handles : List (CNF.Literal ℕ)) (producers : List (Bounded.Producer ℕ)) (nextID : ℕ)
def pairLayer (junction : Bounded.Junction) (lastID : ℕ) : List (CNF.Literal ℕ) → Layer
  | [] => ⟨[], [], lastID⟩
  | [input] => ⟨[input], [], lastID⟩
  | left :: right :: tail =>
      let rest := pairLayer junction (lastID + 1) tail
      ⟨(lastID + 1, true) :: rest.handles, ⟨(lastID + 1, true), junction.gate [left, right]⟩ :: rest.producers, rest.nextID⟩
theorem pairLayer_length (junction : Bounded.Junction) (lastID : ℕ) (inputs : List (CNF.Literal ℕ)) : (pairLayer junction lastID inputs).handles.length = (inputs.length + 1) / 2 := by
  induction inputs using List.twoStepInduction generalizing lastID with
  | nil => simp (disch := source_exact (@of_eq_true
  (@LT.lt.{0} Nat (@Preorder.toLT.{0} Nat (@PartialOrder.toPreorder.{0} Nat Nat.instPartialOrder))
    (@OfNat.ofNat.{0} Nat (nat_lit 0)
      (@Zero.toOfNat0.{0} Nat
        (@AddZero.toZero.{0} Nat
          (@AddZeroClass.toAddZero.{0} Nat
            (@AddMonoid.toAddZeroClass.{0} Nat (@AddMonoidWithOne.toAddMonoid.{0} Nat Nat.instAddMonoidWithOne))))))
    (@OfNat.ofNat.{0} Nat (nat_lit 2)
      (@instOfNatAtLeastTwo.{0} Nat (nat_lit 2) (@AddMonoidWithOne.toNatCast.{0} Nat Nat.instAddMonoidWithOne)
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
  (@zero_lt_two._simp_1.{0} Nat Nat.instAddMonoidWithOne Nat.instPartialOrder Nat.instZeroLEOneClass
    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@IsOrderedAddMonoid.toAddLeftMono.{0} Nat Nat.instAddCommMonoid Nat.instPreorder Nat.instIsOrderedAddMonoid)))) [pairLayer]
  | singleton input => simp (disch := source_exact (@of_eq_true
  (@LT.lt.{0} Nat (@Preorder.toLT.{0} Nat (@PartialOrder.toPreorder.{0} Nat Nat.instPartialOrder))
    (@OfNat.ofNat.{0} Nat (nat_lit 0)
      (@Zero.toOfNat0.{0} Nat
        (@AddZero.toZero.{0} Nat
          (@AddZeroClass.toAddZero.{0} Nat
            (@AddMonoid.toAddZeroClass.{0} Nat (@AddMonoidWithOne.toAddMonoid.{0} Nat Nat.instAddMonoidWithOne))))))
    (@OfNat.ofNat.{0} Nat (nat_lit 2)
      (@instOfNatAtLeastTwo.{0} Nat (nat_lit 2) (@AddMonoidWithOne.toNatCast.{0} Nat Nat.instAddMonoidWithOne)
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
  (@zero_lt_two._simp_1.{0} Nat Nat.instAddMonoidWithOne Nat.instPartialOrder Nat.instZeroLEOneClass
    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@IsOrderedAddMonoid.toAddLeftMono.{0} Nat Nat.instAddCommMonoid Nat.instPreorder Nat.instIsOrderedAddMonoid)))) [pairLayer]
  | cons_cons left right tail inductionHypothesis _ =>
      simp only [pairLayer, List.length_cons, inductionHypothesis]
      omega
structure Result where
  (output : CNF.Literal ℕ) (producers : List (Bounded.Producer ℕ)) (nextID : ℕ)
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
def boundedIndex (positive : 0 < lastID) (source : ℕ) : Fin lastID := if valid : 0 < source ∧ source ≤ lastID then ⟨source - 1, by omega⟩ else ⟨0, positive⟩
def boundedGate (positive : 0 < lastID) (gate : CNF.Gate ℕ) : CNF.Gate (Fin lastID) := gate.relabel (boundedIndex positive)
structure State (roots : ℕ) where
  (count : ℕ) (positive : 0 < count) (circuit : CNF.AcyclicCircuit roots count)
def State.step (state : State roots) (producer : Bounded.Producer ℕ) : State roots :=
  ⟨state.count + 1, by have := state.positive; omega, state.circuit.snoc (boundedGate state.positive producer.gate) true⟩
def State.execute (state : State roots) (producers : List (Bounded.Producer ℕ)) : State roots := producers.foldl State.step state
end Controller.Native.SourceSerialFold
namespace Controller.Native.SourceController
inductive Owner (parameters : Parameters) where
  | native (slot : Controller.Native.Variable parameters) | fold (slot : Controller.Native.Variable parameters) (index : ℕ) | negatedFlag (side : Side) (bus : Fin parameters.buses) | oldDifference (index : Fin (parameters.buses + parameters.channels)) | oldDetected (index : ℕ) | guard (side : Side) (node : Fin parameters.decoder.nodeCount) (index : ℕ)
  deriving DecidableEq, Repr
structure Entry (parameters : Parameters) where
  (owner : Owner parameters) (producer : Bounded.Producer ℕ)
  deriving DecidableEq, Repr
structure Cursor (parameters : Parameters) where
  (entries : List (Entry parameters)) (slots : Controller.Native.Variable parameters → CNF.Literal ℕ) (assigned : List (Controller.Native.Variable parameters)) (negated : Side → Fin parameters.buses → CNF.Literal ℕ) (oldDifferences : Fin (parameters.buses + parameters.channels) → CNF.Literal ℕ) (oldDetected : CNF.Literal ℕ)
def Cursor.lastID (cursor : Cursor parameters) : ℕ := SourceInitialIDs.rootCount parameters + cursor.entries.length
def Cursor.assign (cursor : Cursor parameters) (slot : Controller.Native.Variable parameters) (handle : CNF.Literal ℕ) : Cursor parameters := { cursor with slots := Function.update cursor.slots slot handle, assigned := cursor.assigned ++ [slot] }
def Cursor.emit (cursor : Cursor parameters) (owner : Owner parameters) (gate : CNF.Gate ℕ) : CNF.Literal ℕ × Cursor parameters :=
  let output := (cursor.lastID + 1, true)
  (output, { cursor with entries := cursor.entries ++ [⟨owner, ⟨output, gate⟩⟩] })
def Cursor.emitNative (cursor : Cursor parameters) (slot : Controller.Native.Variable parameters) (gate : CNF.Gate ℕ) : Cursor parameters :=
  let emitted := cursor.emit (.native slot) gate
  emitted.2.assign slot emitted.1
def Cursor.foldNative (cursor : Cursor parameters) (slot : Controller.Native.Variable parameters) (junction : Bounded.Junction) (inputs : List (CNF.Literal ℕ)) : Cursor parameters :=
  let allocated := SourceSerialFold.allocate junction cursor.lastID inputs
  let entries := allocated.producers.zipIdx.map fun pair => Entry.mk (.fold slot pair.2) pair.1
  ({ cursor with entries := cursor.entries ++ entries }).assign slot allocated.output
def initial (parameters : Parameters) : Cursor parameters where
  entries := []
  slots
    | .primary (.enable channel) => (SourceInitialIDs.rootID (b := parameters.buses) (.enable channel), true)
    | .primary (.request bus channel) => (SourceInitialIDs.rootID (.request bus channel), true)
    | _ => (0, true)
  assigned :=
    (List.finRange parameters.channels).map (fun channel => .primary (.enable channel)) ++
      (List.finRange parameters.channels).flatMap fun channel => (List.finRange parameters.buses).map fun bus => .primary (.request bus channel)
  negated := fun _ _ => (0, true); oldDifferences := fun _ => (0, true); oldDetected := (0, true)
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
def interface (parameters : Parameters) : Cursor parameters :=
  let first := firstArrays parameters
  let driver := first.foldNative (.internal .driver) .conjunction
    (parameters.bridge.drivers.sort.map fun channel => first.slots (.internal (.absent .healthy parameters.firstBus channel)))
  let remaining := driver.foldNative (.internal .remaining) .conjunction
    (parameters.bridge.remaining.sort.map fun channel => driver.slots (.internal (.absent .healthy parameters.firstBus channel)))
  let wire := remaining.emitNative (.primary .wire) (.and [remaining.slots (.internal .driver)])
  let healthyProduct := wire.emitNative (.internal (.firstProduct .healthy))
    (.and [wire.slots (.internal (.absent .healthy parameters.firstBus parameters.bridge.target)), wire.slots (.internal .driver), wire.slots (.internal .remaining)])
  let healthyFlag := healthyProduct.emitNative (.internal (.flag .healthy parameters.firstBus))
    (.not (healthyProduct.slots (.internal (.firstProduct .healthy))))
  let faultyProduct := healthyFlag.emitNative (.internal (.firstProduct .faulty))
    (.and [healthyFlag.slots (.primary .wire), healthyFlag.slots (.internal .driver), healthyFlag.slots (.internal .remaining)])
  faultyProduct.emitNative (.internal (.flag .faulty parameters.firstBus))
    (.not (faultyProduct.slots (.internal (.firstProduct .faulty))))
def initialMasks (parameters : Parameters) (side : Side) (cursor : Cursor parameters) : Cursor parameters := (List.finRange parameters.channels).foldl (fun cursor channel => cursor.emitNative (.internal (.mask side parameters.firstBus channel)) (.xor (cursor.slots (.internal (.flag side parameters.firstBus))) (cursor.slots (.internal (.absent side parameters.firstBus channel))))) cursor
def laterBus (parameters : Parameters) (side : Side) (bus : Fin parameters.buses) (cursor : Cursor parameters) : Cursor parameters :=
  let terms := (List.finRange parameters.channels).foldl (fun cursor channel =>
    cursor.foldNative (.internal (.term side bus channel)) .conjunction
      ([cursor.slots (.primary (.enable channel)), cursor.slots (.primary (.request bus channel))] ++
        ((List.finRange parameters.buses).filter (fun earlier => earlier < bus)).map fun earlier => cursor.slots (.internal (.mask side earlier channel)))) cursor
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
def eligible (parameters : Parameters) (side : Side) (channel : Fin parameters.channels) (cursor : Cursor parameters) : Cursor parameters :=
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
def controller (parameters : Parameters) : Cursor parameters := tail parameters .faulty (tail parameters .healthy (interface parameters))
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
def guardChain (parameters : Parameters) (side : Side) (node : Fin parameters.decoder.nodeCount) (child : CNF.Literal ℕ) (labels : List (Fin parameters.channels)) (cursor : Cursor parameters) : CNF.Literal ℕ × Cursor parameters := labels.zipIdx.foldl (fun state pair => state.2.emit (.guard side node pair.2) (.and [state.1, CNF.negate (state.2.slots (.internal (.qualifier side pair.1)))])) (child, cursor)
def decoderNode (parameters : Parameters) (side : Side) (node : Fin parameters.decoder.nodeCount) (cursor : Cursor parameters) : Cursor parameters :=
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
      [cursor.slots (.internal (.decoder side (parameters.decoder.childIndex node left))), cursor.slots (.internal (.decoder side (parameters.decoder.childIndex node right)))])
def attachDecoder (parameters : Parameters) (side : Side) (cursor : Cursor parameters) : Cursor parameters := (List.finRange parameters.decoder.nodeCount).foldl (fun cursor node => decoderNode parameters side node cursor) cursor
def newObservations (parameters : Parameters) (cursor : Cursor parameters) : Cursor parameters :=
  let differences := (List.finRange parameters.decoder.roots.length).foldl (fun cursor output =>
    cursor.emitNative (.internal (.difference output)) (.xor
      (cursor.slots (.internal (.decoder .healthy (parameters.decoder.roots.get output))))
      (cursor.slots (.internal (.decoder .faulty (parameters.decoder.roots.get output)))))) cursor
  differences.foldNative (.internal .detected) .disjunction
    ((List.finRange parameters.decoder.roots.length).map fun output => differences.slots (.internal (.difference output)))
def compile (parameters : Parameters) : Cursor parameters := newObservations parameters (attachDecoder parameters .faulty (attachDecoder parameters .healthy (originalObservations parameters (controller parameters))))
def sourceRoleMap (parameters : Parameters) : Controller.Native.Variable parameters → CNF.Literal ℕ := (compile parameters).slots
def equationFormula (parameters : Parameters) : CNF.Formula ℕ := CNF.ofClauses ((compile parameters).entries.flatMap fun entry => entry.producer.rows)
def assertions (parameters : Parameters) : List (CNF.Literal ℕ) :=
  let slots := sourceRoleMap parameters
  [((slots (.internal (.absent .healthy parameters.firstBus parameters.bridge.target))).1, !parameters.drive),
    ((slots (.internal .driver)).1, parameters.drive),
    ((slots (.primary .wire)).1, parameters.drive), slots (.internal .detected)]
def formula (parameters : Parameters) : CNF.Formula ℕ := equationFormula parameters ++ CNF.ofClauses ((assertions parameters).map fun literal => [literal])
end Controller.Native.SourceController
namespace Controller.Native.SourceController
def Cursor.toState (cursor : Cursor parameters) : SourceSerialFold.State (SourceInitialIDs.rootCount parameters) :=
  (SourceSerialFold.State.mk (SourceInitialIDs.rootCount parameters)
    (by have positive := parameters.bridge.target.isLt; unfold SourceInitialIDs.rootCount; omega)
    .roots).execute (cursor.entries.map Entry.producer)
end Controller.Native.SourceController
namespace Controller.Native.SourceController
source_context "Controller.Native.SourceTransport"
def sourceInput (parameters : Parameters) (assignment : ℕ → Bool) : Physical.PrimaryInput parameters.channels parameters.buses where
  positiveBuses := parameters.positiveBuses; enable := fun channel => assignment (SourceInitialIDs.rootID (b := parameters.buses) (.enable channel)); request := fun bus channel => assignment (SourceInitialIDs.rootID (.request bus channel))
end Controller.Native.SourceController
source_context "Controller.Certificate.ModelCheck"
namespace Controller.Certificate.ModelCheck
open Controller
def check (formula : CNF.Formula α) (assignment : α → Bool) : Bool := Controller.CNF.OrderedFormula.eval assignment formula
end Controller.Certificate.ModelCheck
source_context "Controller.Cost.NativeSourceExecution"
namespace Controller.Cost.NativeSourceExecution
open Controller.CNF Controller.Native Controller.Native.SourceController
def selectedSize (parameters : Parameters) : NativeSize where
  variableCount := (compile parameters).toState.count; clauses := (formula parameters).clauses.size; literals := NativeCircuitSize.literalCount (formula parameters)
end Controller.Cost.NativeSourceExecution
source_context "Controller.Cost.NativeRealizedChecked"
namespace Controller.Cost.NativeRealizedChecked
open Controller.Cost.NativeSourceExecution
open Controller.Native Controller.Native.SourceController
def decodeOutput (output : List (Word width)) (count source : Nat) : Bool := if 0 < source ∧ source ≤ count then ((output[count - source]?).getD (word width 0)).val == 1 else false
end Controller.Cost.NativeRealizedChecked
source_context "Controller.Cost.SharedRetainedCandidates"
namespace Controller.Cost.SharedRetainedCandidates
open Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestIndexedOperands Controller.Cost.UniformDAGSource
open Controller.Cost.UniformDAGRun Controller.Cost.ForestInputPrefixStored
open Controller.Cost.ForestInputStored
def masks (width : Nat) (baseline : Assignment n) (flags : List Bool) : List (Word width) := (List.finRange n).map (fun channel => boolWord width (baseline channel)) ++ flags.map (boolWord width)
end Controller.Cost.SharedRetainedCandidates
source_context "Controller.Cost.SharedMachineCapacity"
namespace Controller.Cost.SharedMachineCapacity
open Controller.Native Controller.Native.SourceController
open Controller.Cost.NativeSourceExecution
open Controller.Decoder
def wordWidth (retained graphSize nativeSize : Nat) : Nat := Nat.log2 (retained + graphSize + nativeSize + 1) + 18
end Controller.Cost.SharedMachineCapacity
source_context "Controller.Cost.SharedDetectorLoop"
namespace Controller.Cost.SharedDetectorLoop
open Controller.Native Controller.Native.SourceController Controller.Decoder
open Controller.Cost.NativeSourceExecution
abbrev Width (parameters : Parameters) (graph : DAG parameters.channels) (retained : Nat) := SharedMachineCapacity.wordWidth retained graph.countedSize (selectedSize parameters).total
end Controller.Cost.SharedDetectorLoop
source_context "Controller.Extensions.BoundedAnd"
namespace Controller.Extensions.BoundedAnd
open Controller.Decoder Controller.Decoder.DAG
open scoped BigOperators
def supportCount (n k : ℕ) : ℕ := ∑ j ∈ Finset.range (min (k + 1) n + 1), n.choose j
end Controller.Extensions.BoundedAnd
source_context "Controller.Extensions.GateBasis"
namespace Controller.Extensions.GateBasis
open Controller.Decoder Controller.Decoder.DAG
structure Basis where
  (disjunction : Bool) (conjunction : Bool) (negativeGuard : Bool)
  deriving DecidableEq, Repr
def full : Basis := ⟨true, true, true⟩
def Allows (B : Basis) : Gate n available → Prop | .zero | .input _ => True | .disj refs => refs.length ≤ 1 ∨ B.disjunction = true | .guard _ labels => labels = [] ∨ B.negativeGuard = true | .liveAnd _ _ => B.conjunction = true
def Uses (graph : DAG n) (B : Basis) : Prop := ∀ i, Allows B (graph.node i)
def NoNegativeGuards (graph : DAG n) : Prop := ∀ i, (graph.node i).guardLabels = []
def NoDisjunction (graph : DAG n) : Prop := ∀ i, match graph.node i with | .disj refs => refs.length ≤ 1 | _ => True
end Controller.Extensions.GateBasis
source_context "Controller.Extensions.LiteralSourceConstruction"
namespace Controller.Extensions.LiteralSourceConstruction
open Controller.Decoder Controller.Decoder.DAG Controller.Cost
open Controller.Cost.ForestIndexedOperands Controller.Cost.UniformDAGSource
open Controller.Cost.UniformDAGRun Controller.Cost.ForestInputPrefixStored
open Controller.Cost.ForestInputStored
def initial (n width : Nat) (rows : List Row) (roots : List Nat) (caller output : List (Word width)) : State width 8 where
  reg _ := word width 0; heap := channelHeap (packetHeaderHeap width n rows roots) rows roots (fun _ : Fin n => false); stack := caller; output := output; pc := word width 0; halted := false
end Controller.Extensions.LiteralSourceConstruction
source_context "Controller.Cost.SharedDetectorCold"
namespace Controller.Cost.SharedDetectorCold
open Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestIndexedOperands Controller.Cost.UniformDAGSource
open Controller.Cost.UniformDAGRun Controller.Cost.ForestInputPrefixStored
open Controller.Native Controller.Native.SourceController Controller.Cost.NativeSourceExecution
def inputWords (width : Nat) (rows : List Row) (roots : List Nat) (values : Assignment n) : List (Word width) := (inputPacket n 0 rows roots).map (word width) ++ List.ofFn (fun channel => boolWord width (values channel))
section Code
variable (parameters : Parameters) (graph : DAG parameters.channels) (T F : Finset (Fin parameters.channels))
def retained : Nat := 480 * (graph.countedSize + 1) + 77 * (selectedSize parameters).total + 1300
noncomputable def program : (parameters : Controller.Native.Parameters) → (graph : Controller.Decoder.DAG parameters.channels) → Finset.{0} (Fin parameters.channels) → Finset.{0} (Fin parameters.channels) → List.{0} Controller.Cost.ForestIndexedOperands.Row → List.{0} ℕ → Controller.Cost.Program (Controller.Cost.SharedDetectorLoop.Width parameters graph (Controller.Cost.SharedDetectorCold.retained parameters graph)) 8 := by sorry
open Lean Elab Command in
run_cmd modifyEnv (fun env => Lean.setDefHeightOverride env `Controller.Cost.SharedDetectorCold.program 39)
end Code
end Controller.Cost.SharedDetectorCold
source_context "Controller.Extensions.BoundedNativeCold"
namespace Controller.Extensions.BoundedNativeCold
open Controller Controller.Decoder Controller.Decoder.DAG Controller.Cost
open Controller.Native Controller.Native.SourceController Controller.Cost.NativeSourceExecution
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestInputStored
def timeBound (parameters : Parameters) (k : Nat) : Nat :=
  (if parameters.decoder.roots.all (parameters.decoder.evalTable (assignmentOfSet {parameters.bridge.target}))
    then 0 else (100*(parameters.decoder.countedSize+1)+50)*BoundedAnd.supportCount parameters.channels k)+
    (7000*(parameters.decoder.countedSize+1)+90)*2^k*parameters.decoder.roots.length+
    7000*(parameters.decoder.countedSize+1)+100*(selectedSize parameters).total
end Controller.Extensions.BoundedNativeCold
source_context "Controller.Extensions.BoundedNativeDetector"
namespace Controller.Extensions.BoundedNativeDetector
open Controller Controller.Decoder Controller.Decoder.DAG Controller.Cost
open Controller.Native Controller.Native.SourceController Controller.Cost.NativeSourceExecution
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestInputStored
noncomputable def program : Controller.Native.Parameters → (width : ℕ) → ℕ → Controller.Cost.Program width 8 := by sorry
def width (parameters : Parameters) : Nat := SharedMachineCapacity.wordWidth 0 parameters.decoder.countedSize (selectedSize parameters).total
def Detects (parameters : Parameters) : Prop :=
  parameters.drive = true ∧ ∃ root ∈ parameters.decoder.roots, ∃ K,
    Admissible parameters.buses parameters.bridge.target K ∧
    parameters.decoder.eval (assignmentOfSet K) root ≠
      parameters.decoder.eval (assignmentOfSet {parameters.bridge.target}) root
end Controller.Extensions.BoundedNativeDetector
source_context "Controller.Extensions.BoundedNativeComplete"
namespace Controller.Extensions.BoundedNativeComplete
open Controller Controller.Decoder Controller.Decoder.DAG Controller.Cost
open Controller.Native Controller.Native.SourceController Controller.Cost.NativeSourceExecution
def initial (parameters : Parameters) : State (BoundedNativeDetector.width parameters) 8 where
  reg _ := word _ 0; heap := #[]
  stack := SharedDetectorCold.inputWords _ (UniformDAGOutputs.rowsOfGraph parameters.decoder)
    (parameters.decoder.roots.map Fin.val) (assignmentOfSet {parameters.bridge.target})
  output := []; pc := word _ 0; halted := false
def emittedSet (parameters : Parameters) (final : State wordWidth 8) : Finset (Channel parameters.channels) :=
  let assignment := NativeRealizedChecked.decodeOutput final.output (compile parameters).toState.count
  let input := sourceInput parameters assignment
  setOfAssignment (Physical.bridgeQualifiers parameters.bridge input (Physical.bridgeD parameters.bridge input))
/-- emitted witness: Bounded live conjunction and proper-basis algorithms. -/
theorem emitted_witness (parameters : Parameters) (raw : parameters.layout = .raw) (drive : parameters.drive = true) (final : State wordWidth 8) (checked : Certificate.ModelCheck.check (formula parameters) (NativeRealizedChecked.decodeOutput final.output (compile parameters).toState.count) = true) : Admissible parameters.buses parameters.bridge.target (emittedSet parameters final) ∧ ∃ root ∈ parameters.decoder.roots, parameters.decoder.eval (assignmentOfSet (emittedSet parameters final)) root ≠ parameters.decoder.eval (assignmentOfSet {parameters.bridge.target}) root := by sorry
/-- execution: Bounded live conjunction and proper-basis algorithms. -/
theorem execution (parameters : Parameters) (raw : parameters.layout = .raw) (k : Nat) (andBound : parameters.decoder.liveAndCount ≤ k) : ∃ final ticks peak, Execution (BoundedNativeDetector.program parameters (BoundedNativeDetector.width parameters) k) (initial parameters) final ticks peak ∧ final.halted = true ∧ (final.reg 4 = word _ 1 ↔ BoundedNativeDetector.Detects parameters) ∧ ticks ≤ BoundedNativeCold.timeBound parameters k ∧ peak ≤ 900*(parameters.decoder.countedSize+1)+3*(selectedSize parameters).total+30 ∧ programWords (BoundedNativeDetector.program parameters (BoundedNativeDetector.width parameters) k) ≤ 13600*(parameters.decoder.countedSize+1)+272*(selectedSize parameters).total ∧ (final.reg 4 = word _ 1 → Certificate.ModelCheck.check (formula parameters) (NativeRealizedChecked.decodeOutput final.output (compile parameters).toState.count) = true) ∧ (final.reg 4 = word _ 1 → Admissible parameters.buses parameters.bridge.target (emittedSet parameters final) ∧ ∃ root ∈ parameters.decoder.roots, parameters.decoder.eval (assignmentOfSet (emittedSet parameters final)) root ≠ parameters.decoder.eval (assignmentOfSet {parameters.bridge.target}) root) := by sorry
/-- xp time: Bounded live conjunction and proper-basis algorithms. -/
theorem xp_time (parameters : Parameters) (k : Nat) : BoundedNativeCold.timeBound parameters k ≤ 15000*((k+2)*(parameters.decoder.countedSize+1)^(k+1)+ (parameters.decoder.countedSize+1)*2^k)*(parameters.decoder.countedSize+1)+100*(selectedSize parameters).total := by sorry
/-- one and time: Bounded live conjunction and proper-basis algorithms. -/
theorem one_and_time (parameters : Parameters) : BoundedNativeCold.timeBound parameters 1 ≤ 360000*(parameters.channels^2+parameters.decoder.roots.length)*parameters.decoder.countedSize+ 100*(selectedSize parameters).total := by sorry
/-- healthy one time: Bounded live conjunction and proper-basis algorithms. -/
theorem healthy_one_time (parameters : Parameters) (k : Nat) (healthy : parameters.decoder.roots.all (parameters.decoder.evalTable (assignmentOfSet {parameters.bridge.target})) = true) : BoundedNativeCold.timeBound parameters k ≤ 15000*(2^k+1)*(parameters.decoder.countedSize+1)^2+100*(selectedSize parameters).total := by sorry
end Controller.Extensions.BoundedNativeComplete
source_context "Controller.Extensions.MonotoneNativeDetector"
namespace Controller.Extensions.MonotoneNativeDetector
open Controller.Decoder Controller.Decoder.DAG Controller.Cost Controller.Native Controller.Native.SourceController
open Controller.Cost.NativeSourceExecution Controller.Cost.ForestIndexedOperands
open Controller.Cost.ForestInputPrefixStored Controller.Cost.UniformDAGRun Controller.Cost.UniformDAGSource
open Controller.Extensions.LiteralSourceConstruction (initial)
def Width (parameters : Parameters) (graph : DAG parameters.channels) : Nat := SharedMachineCapacity.wordWidth 0 ((parameters.channels + 1) * (graph.countedSize + 1)) (selectedSize parameters).total
noncomputable def program : (parameters : Controller.Native.Parameters) → (graph : Controller.Decoder.DAG parameters.channels) → List.{0} Controller.Cost.ForestIndexedOperands.Row → List.{0} ℕ → Controller.Cost.Program (Controller.Extensions.MonotoneNativeDetector.Width parameters graph) 8 := by sorry
end Controller.Extensions.MonotoneNativeDetector
source_context "Controller.Extensions.LiteralNativeDetector"
namespace Controller.Extensions.LiteralNativeDetector
open Controller.Decoder Controller.Decoder.DAG Controller.Cost Controller.Native Controller.Native.SourceController
open Controller.Cost.NativeSourceExecution Controller.Cost.ForestIndexedOperands
open Controller.Cost.ForestInputPrefixStored Controller.Cost.UniformDAGRun Controller.Cost.UniformDAGSource
open Controller.Extensions.LiteralSourceConstruction (initial)
def Width (parameters : Parameters) (graph : DAG parameters.channels) : Nat := SharedMachineCapacity.wordWidth 0 ((parameters.channels + 1) * (graph.countedSize + 1)) (selectedSize parameters).total
noncomputable def program : (parameters : Controller.Native.Parameters) → (graph : Controller.Decoder.DAG parameters.channels) → List.{0} Controller.Cost.ForestIndexedOperands.Row → List.{0} ℕ → Controller.Cost.Program (Controller.Extensions.LiteralNativeDetector.Width parameters graph) 8 := by sorry
end Controller.Extensions.LiteralNativeDetector
source_context "Controller.Extensions.ProperBasisDetector"
namespace Controller.Extensions.ProperBasisDetector
open Controller.Decoder Controller.Decoder.DAG Controller.Cost Controller.Native Controller.Native.SourceController
open Controller.Cost.NativeSourceExecution Controller.Cost.UniformDAGSource Controller.Cost.UniformDAGRun
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestInputPrefixStored
open Controller.Extensions.GateBasis
inductive Kind where | guarded | monotone | literal
  deriving DecidableEq, Repr
def select (basis : Basis) : Kind := if basis.conjunction = false then .guarded else if basis.negativeGuard = false then .monotone else .literal
def Valid (graph : DAG n) : Kind → Prop
  | .guarded => graph.Guarded
  | .monotone => NoNegativeGuards graph
  | .literal => NoDisjunction graph

def Feasible (parameters : Parameters) : Prop :=
  ∃ root ∈ parameters.decoder.roots, ∃ K, Admissible parameters.buses parameters.bridge.target K ∧
    parameters.decoder.eval (assignmentOfSet K) root ≠ parameters.decoder.eval (assignmentOfSet {parameters.bridge.target}) root
abbrev coldWidth (parameters : Parameters) : Nat := SharedDetectorLoop.Width parameters parameters.decoder (SharedDetectorCold.retained parameters parameters.decoder)
def coldInitial (parameters : Parameters) (rows : List Row) (roots : List Nat) : State (coldWidth parameters) 8 where
  reg _ := word _ 0; heap := #[]
  stack := SharedDetectorCold.inputWords (coldWidth parameters) rows roots (assignmentOfSet {parameters.bridge.target}) ++
    word _ parameters.bridge.target.val ::
      (SharedRetainedCandidates.masks (coldWidth parameters)
        (assignmentOfSet (extensionBase parameters.buses parameters.bridge.target ∅))
        ((List.finRange parameters.channels).map (assignmentOfSet ∅)) ++ [])
  output := []; pc := word _ 0; halted := false
structure Machine where
  (width : Nat) (program : Program width 8) (initial : State width 8) (accepted : State width 8 → Bool)
def machine (parameters : Parameters) (kind : Kind) (rows : List Row) (roots : List Nat) : Machine :=
  match kind with
  | .guarded => ⟨coldWidth parameters, SharedDetectorCold.program parameters parameters.decoder ∅ ∅ rows roots, coldInitial parameters rows roots, fun state => state.reg 4 == word _ 1⟩
  | .monotone => ⟨MonotoneNativeDetector.Width parameters parameters.decoder,
      MonotoneNativeDetector.program parameters parameters.decoder rows roots,
      LiteralSourceConstruction.initial parameters.channels _ rows roots [] [], fun state => !state.output.isEmpty⟩
  | .literal => ⟨LiteralNativeDetector.Width parameters parameters.decoder,
      LiteralNativeDetector.program parameters parameters.decoder rows roots,
      LiteralSourceConstruction.initial parameters.channels _ rows roots [] [], fun state => !state.output.isEmpty⟩
end Controller.Extensions.ProperBasisDetector
source_context "Controller.Extensions.ProperBasisComplete"
namespace Controller.Extensions.ProperBasisComplete
open Controller.Decoder Controller.Cost Controller.Native Controller.Native.SourceController
open Controller.Cost.NativeSourceExecution Controller.Cost.ForestIndexedOperands
open Controller.Cost.UniformDAGSource Controller.Cost.UniformDAGRun Controller.Cost.ForestInputPrefixStored
open Controller.Extensions.ProperBasisDetector Controller.Extensions.GateBasis
def disabled : Machine where
  width := 4; program := #[.halt]; initial := ⟨fun _ => word 4 0, #[], [], [], word 4 0, false⟩; accepted _ := false
def detector (parameters : Parameters) (basis : Basis) (rows : List Row) (roots : List Nat) : Machine := if parameters.drive then machine parameters (select basis) rows roots else disabled
/-- execution: Bounded live conjunction and proper-basis algorithms. -/
theorem execution (parameters : Parameters) (raw : parameters.layout = .raw)
    (basis : Basis) (uses : Uses parameters.decoder basis) (proper : basis ≠ full)
    (rows : List Row) (roots : List Nat) (matched : RowsMatch parameters.decoder rows)
    (heads : HeadsMatch parameters.decoder rows matched) (rootMatches : RootsMatch parameters.decoder roots) :
    let selected := detector parameters basis rows roots
    ∃ final ticks peak, Execution selected.program selected.initial final ticks peak ∧
      final.halted = true ∧
      ticks ≤ 10000 * ((parameters.channels + parameters.decoder.roots.length + 1) * (parameters.decoder.countedSize + 1)) +
        55 * (selectedSize parameters).total + 1 ∧
      programWords selected.program + peak ≤
        10000 * ((parameters.channels + 1) * (parameters.decoder.countedSize + 1)) + 400 * (selectedSize parameters).total ∧
      (selected.accepted final = true ↔ parameters.drive = true ∧ Feasible parameters) ∧
      (selected.accepted final = true → Certificate.ModelCheck.check (formula parameters)
        (NativeRealizedChecked.decodeOutput final.output (compile parameters).toState.count) = true) := by
  sorry
end Controller.Extensions.ProperBasisComplete

end_source_context
