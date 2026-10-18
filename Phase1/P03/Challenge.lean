module
public meta import Lean.Elab.Tactic.ElabTerm
public meta import Lean.Elab.Command
public meta import Lean.Meta.Match.Match
meta import all Lean.Meta.Match.Match
public meta import Lean.Meta.Tactic.AuxLemma

public import Lean.Elab.Tactic.Omega
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.BooleanAlgebra
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
public import Mathlib.Data.Vector.Basic
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Order.WellFounded
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.ClearExcept
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.IntervalCases
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
    (private_decl% Lean.Meta.Match.matcherExt).setState env {}
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
# Canonical enumeration, termination and streaming delay
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
def FixedConsistent {n : ℕ} (T F : Finset (Channel n)) : Prop := Disjoint T F
end Controller source_context "Controller.Basic.Sizes" namespace Controller
structure DecoderSize where
  (channels : ℕ) (nodes : ℕ) (children : ℕ) (guards : ℕ) (roots : ℕ)
  deriving Repr, DecidableEq
def DecoderSize.total (s : DecoderSize) : ℕ := s.channels + s.nodes + s.children + s.guards + s.roots
structure NativeSize where
  (variableCount : ℕ) (clauses : ℕ) (literals : ℕ)
  deriving Repr, DecidableEq
def NativeSize.total (s : NativeSize) : ℕ := s.variableCount + s.clauses + s.literals
end Controller source_context "Controller.Cost.Model" namespace Controller.Cost
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
end Controller.Cost source_context "Controller.Decoder.Syntax" namespace Controller.Decoder
inductive Gate (n available : ℕ) where
  | zero : Gate n available | input (channel : Channel n) : Gate n available | disj (children : List (Fin available)) : Gate n available | guard (child : Fin available) (labels : List (Channel n)) : Gate n available | liveAnd (left right : Fin available) : Gate n available
  deriving DecidableEq, Repr
namespace Gate
variable {n available : ℕ}
def children : Gate n available → List (Fin available) | .zero => [] | .input _ => [] | .disj refs => refs | .guard child _ => [child] | .liveAnd left right => [left, right]
def guardLabels : Gate n available → List (Channel n) | .guard _ labels => labels | _ => []
def isLiveAnd : Gate n available → Bool | .liveAnd _ _ => true | _ => false
def IsGuarded (gate : Gate n available) : Prop := gate.isLiveAnd = false
def eval (gate : Gate n available) (assignment : Assignment n) (earlier : Fin available → Bool) : Bool := match gate with | .zero => false | .input channel => assignment channel | .disj refs => refs.any earlier | .guard child labels => earlier child && !(labels.any assignment) | .liveAnd left right => earlier left && earlier right
end Gate
structure DAG (n : ℕ) where
  (nodeCount : ℕ) (node : (index : Fin nodeCount) → Gate n index.val) (roots : List (Fin nodeCount))
namespace DAG
variable {n : ℕ}
def childIndex (graph : DAG n) (parent : Fin graph.nodeCount) (child : Fin parent.val) : Fin graph.nodeCount := ⟨child.val, Nat.lt_trans child.isLt parent.isLt⟩
theorem childIndex_lt (graph : DAG n) (parent : Fin graph.nodeCount) (child : Fin parent.val) : (graph.childIndex parent child).val < parent.val := child.isLt
def Guarded (graph : DAG n) : Prop := ∀ index, (graph.node index).IsGuarded
def childIncidences (graph : DAG n) : ℕ := @List.sum Nat instAddNat (@Zero.ofOfNat0 Nat (instOfNatNat (nat_lit 0))) (List.ofFn fun index : Fin graph.nodeCount => (graph.node index).children.length)
def guardIncidences (graph : DAG n) : ℕ := @List.sum Nat instAddNat (@Zero.ofOfNat0 Nat (instOfNatNat (nat_lit 0))) (List.ofFn fun index : Fin graph.nodeCount => (graph.node index).guardLabels.length)
def size (graph : DAG n) : DecoderSize where
  channels := n; nodes := graph.nodeCount; children := graph.childIncidences; guards := graph.guardIncidences; roots := graph.roots.length
def countedSize (graph : DAG n) : ℕ := graph.size.total
end DAG
end Controller.Decoder source_context "Controller.Decoder.Eval" namespace Controller.Decoder
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
end Controller.Decoder source_context "Controller.Cost.Decoder" namespace Controller.Cost
def boolWord (width : Nat) (value : Bool) : Word width := word width (if value then 1 else 0)
end Controller.Cost source_context "Controller.Basic.Admissible" namespace Controller
def Admissible {n : ℕ} (b : ℕ) (t : Channel n) (K : Finset (Channel n)) : Prop := K.Nonempty ∧ (b = 1 → t ∈ K)
end Controller source_context "Controller.CNF.Basic" namespace Controller.CNF
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
abbrev FiniteFormula (v : Nat) := Formula (Fin v)
abbrev negate (l : Literal α) : Literal α := Std.Sat.Literal.negate l
def ofClauses (cs : List (Clause α)) : Formula α := ⟨cs.toArray⟩
end Controller.CNF source_context "Controller.Horn.GreatestModel" namespace Controller.Horn
open CNF
def forceFalse [DecidableEq α] (current : α → Bool) (i : α) : α → Bool := fun j => if j = i then false else current j
end Controller.Horn source_context "Controller.Decoder.ZeroSystem" namespace Controller.Decoder.ZeroSystem
open CNF
def positiveClause (entries : List α) : Clause α := entries.map (fun v => (v, true))
def implicationClause (premise : α) (alternatives : List α) : Clause α := (premise, false) :: positiveClause alternatives
end Controller.Decoder.ZeroSystem
namespace Controller.Decoder.DAG
open CNF ZeroSystem
variable {n : ℕ}
abbrev ZeroVar (graph : DAG n) := Channel n ⊕ Fin graph.nodeCount
def nodeClauses (graph : DAG n) (index : Fin graph.nodeCount) : List (Clause graph.ZeroVar) := match graph.node index with | .zero => [implicationClause (.inr index) []] | .input channel => [implicationClause (.inl channel) [.inr index], implicationClause (.inr index) [.inl channel]] | .disj refs => refs.map fun child => implicationClause (.inr (graph.childIndex index child)) [.inr index] | .guard child labels => [implicationClause (.inr (graph.childIndex index child)) (labels.map Sum.inl ++ [.inr index])] | .liveAnd left right => [[(.inr (graph.childIndex index left), false), (.inr (graph.childIndex index right), false), (.inr index, true)]]
def forwardClauses (graph : DAG n) : List (Clause graph.ZeroVar) := (List.finRange graph.nodeCount).flatMap graph.nodeClauses
end Controller.Decoder.DAG
namespace Controller.Decoder.DAG
open CNF ZeroSystem
variable {n : ℕ}
def trueUnitClauses (graph : DAG n) (T : Finset (Channel n)) : List (Clause graph.ZeroVar) := ((List.finRange n).filter fun channel => decide (channel ∈ T)).map fun channel => positiveClause [.inl channel]
def falseUnitClauses (graph : DAG n) (F : Finset (Channel n)) : List (Clause graph.ZeroVar) := ((List.finRange n).filter fun channel => decide (channel ∈ F)).map fun channel => implicationClause (.inl channel) []
def channelClauses (graph : DAG n) (b : ℕ) (target : Channel n) (T F : Finset (Channel n)) : List (Clause graph.ZeroVar) := (([positiveClause ((List.finRange n).map Sum.inl)] ++ (if b = 1 then [positiveClause [.inl target]] else [])) ++ graph.trueUnitClauses T) ++ graph.falseUnitClauses F
def zeroSystem (graph : DAG n) (b : ℕ) (target : Channel n) (root : Fin graph.nodeCount) (T F : Finset (Channel n)) : Formula graph.ZeroVar := ofClauses ((graph.forwardClauses ++ graph.channelClauses b target T F) ++ [implicationClause (.inr root) []])
def zeroChannelSet (graph : DAG n) (assignment : graph.ZeroVar → Bool) : Finset (Channel n) := setOfAssignment (fun channel => assignment (.inl channel))
end Controller.Decoder.DAG source_context "Controller.Horn.Rules" namespace Controller.Horn.Worklist
open CNF
inductive Rule (α : Type*) where
  | skip | positive (positive : List α) | negative (head : α) (positive : List α)
  deriving DecidableEq, Repr
namespace Rule
def positives : Rule α → List α | .skip => [] | .positive labels => labels | .negative _ labels => labels
def Holds (assignment : α → Bool) : Rule α → Prop
  | .skip => True
  | .positive labels => ∃ label ∈ labels, assignment label = true
  | .negative head labels => assignment head = false ∨ ∃ label ∈ labels, assignment label = true
end Rule
variable [DecidableEq α]
def signedLabels (clause : Clause α) (polarity : Bool) : List α := ((clause.filter fun literal => decide (literal.2 = polarity)).map Prod.fst).dedup
def tautologyCheck (clause : Clause α) : Bool := clause.any fun literal => clause.contains (negate literal)
def compileClause (clause : Clause α) : Rule α := if tautologyCheck clause then .skip else match signedLabels clause false with | [] => .positive (signedLabels clause true) | head :: _ => .negative head (signedLabels clause true)
def compileFormula (formula : Formula α) : Array (Rule α) := formula.clauses.map compileClause
@[simp] theorem compileFormula_size (formula : Formula α) :
    (compileFormula formula).size = formula.clauses.size := by simp [compileFormula]
end Controller.Horn.Worklist source_context "Controller.Horn.IndexedState" namespace Controller.Horn.Worklist
abbrev RuleTable (n m : Nat) := Vector (Rule (Fin n)) m
def normalizedTable (formula : CNF.Formula (Fin n)) : RuleTable n formula.clauses.size := ⟨compileFormula formula, compileFormula_size formula⟩
def Normalized (rules : RuleTable n m) : Prop := ∀ row : Fin m, (rules[row.val]).positives.Nodup
def positiveIncidences (rules : RuleTable n m) : List (Fin n × Fin m) := (List.finRange m).flatMap fun row => (rules[row.val]).positives.map fun label => (label, row)
def bucketIncidences : List (Fin n × Fin m) → Vector (List (Fin m)) n
  | [] => Vector.replicate n []
  | (label, row) :: rest =>
      let table := bucketIncidences rest
      table.set label.val (row :: table[label.val]) label.isLt
def occurrences (rules : RuleTable n m) : Vector (List (Fin m)) n := bucketIncidences (positiveIncidences rules)
theorem countP_forceFalse [DecidableEq α] (labels : List α) (noDuplicates : labels.Nodup) (assignment : α → Bool) (label : α) : labels.countP (forceFalse assignment label) = labels.countP assignment - if label ∈ labels ∧ assignment label = true then 1 else 0 := by
  calc
    labels.countP (forceFalse assignment label) = (labels.erase label).countP assignment := by
      rw [noDuplicates.erase_eq_filter, List.countP_filter]
      apply List.countP_congr
      intro current _
      by_cases equal : current = label <;> simp [forceFalse, equal]
    _ = _ := List.countP_erase assignment labels label
structure CountedState (n m : Nat) where
  (values : Vector Bool n) (counts : Vector Nat m)
namespace CountedState
def assignment (state : CountedState n m) : Fin n → Bool := fun label => state.values[label.val]
def initial (rules : RuleTable n m) : CountedState n m where
  values := Vector.replicate n true; counts := Vector.ofFn fun row => (rules[row.val]).positives.length
end CountedState
def decrementRows : List (Fin m) → Vector Nat m → Vector Nat m | [], counts => counts | row :: rest, counts => decrementRows rest (counts.set row.val (counts[row.val] - 1) row.isLt)
namespace CountedState
def turnOff (index : Vector (List (Fin m)) n) (state : CountedState n m) (label : Fin n) : CountedState n m where
  values := state.values.set label.val false label.isLt; counts := decrementRows index[label.val] state.counts
@[simp] theorem turnOff_assignment (index : Vector (List (Fin m)) n)
    (state : CountedState n m) (label : Fin n) :
    (turnOff index state label).assignment = forceFalse state.assignment label := by
  funext current
  simp only [assignment, turnOff, Vector.getElem_set, forceFalse]
  by_cases equal : current = label
  · subst current
    simp
  · have unequalValues : label.val ≠ current.val :=
      fun same => equal (Fin.ext same.symm)
    simp [equal, unequalValues]
end CountedState
end Controller.Horn.Worklist source_context "Controller.Horn.Worklist" namespace Controller.Horn.Worklist
def Models (rules : RuleTable n m) (assignment : Fin n → Bool) : Prop := ∀ row : Fin m, (rules[row.val]).Holds assignment
structure Agenda (m : Nat) where
  (fired : Vector Bool m) (pending : List (Fin m)) (failed : Bool)
namespace Agenda
def empty (m : Nat) : Agenda m where
  fired := Vector.replicate m false; pending := []; failed := false
def schedule (rules : RuleTable n m) (counted : CountedState n m) (row : Fin m) (agenda : Agenda m) : Agenda m :=
  if counted.counts[row.val] = 0 ∧ agenda.fired[row.val] = false then
    match rules[row.val] with
    | .skip => agenda
    | .positive _ => { agenda with fired := agenda.fired.set row.val true row.isLt, failed := true }
    | .negative _ _ =>
        { agenda with
          fired := agenda.fired.set row.val true row.isLt
          pending := row :: agenda.pending }
  else agenda
def scheduleRows (rules : RuleTable n m) (counted : CountedState n m) : List (Fin m) → Agenda m → Agenda m | [], agenda => agenda | row :: rest, agenda => scheduleRows rules counted rest (schedule rules counted row agenda)
end Agenda
structure State (n m : Nat) where
  (counted : CountedState n m) (agenda : Agenda m)
namespace State
def initial (rules : RuleTable n m) : State n m where
  counted := CountedState.initial rules
  agenda := Agenda.scheduleRows rules (CountedState.initial rules) (List.finRange m)
    (Agenda.empty m)
def propagate (rules : RuleTable n m) (index : Vector (List (Fin m)) n) (state : State n m) (head : Fin n) (rest : List (Fin m)) : State n m :=
  let counted := state.counted.turnOff index head
  let agenda := { state.agenda with pending := rest }
  { counted := counted, agenda := Agenda.scheduleRows rules counted index[head.val] agenda }
def discard (state : State n m) (rest : List (Fin m)) : State n m := { state with agenda := { state.agenda with pending := rest } }
def remaining (state : State n m) : Nat := (List.finRange n).countP state.counted.assignment
theorem propagate_remaining_lt (rules : RuleTable n m) (index : Vector (List (Fin m)) n) (state : State n m) (head : Fin n) (rest : List (Fin m)) (wasTrue : state.counted.assignment head = true) : remaining (propagate rules index state head rest) < remaining state := by
  have positive : 0 < remaining state := List.countP_pos_iff.mpr ⟨head, List.mem_finRange head, wasTrue⟩
  change (List.finRange n).countP (state.counted.turnOff index head).assignment < remaining state
  rw [CountedState.turnOff_assignment, countP_forceFalse _ (List.nodup_finRange n)]
  simp only [List.mem_finRange, wasTrue, and_self, ite_true]
  exact Nat.sub_lt positive (by decide)
def run (rules : RuleTable n m) (index : Vector (List (Fin m)) n) (state : State n m) : Option (Vector Bool n) :=
  if state.agenda.failed then none
  else match pendingEquation : state.agenda.pending with
    | [] => some state.counted.values
    | row :: rest =>
      match rules[row.val] with
      | .negative head _ =>
        if wasTrue : state.counted.assignment head = true then run rules index (propagate rules index state head rest)
        else run rules index (discard state rest)
      | _ => run rules index (discard state rest)
termination_by (remaining state, state.agenda.pending.length)
decreasing_by
  all_goals first
    | exact Prod.Lex.left _ _ (propagate_remaining_lt rules index state head rest wasTrue)
    | apply Prod.Lex.right
      simp only [discard, pendingEquation, List.length_cons, Nat.lt_add_one._simp_1]
end State
def solveRules (rules : RuleTable n m) : Option (Vector Bool n) :=
  let index := occurrences rules
  State.run rules index (State.initial rules)
end Controller.Horn.Worklist source_context "Controller.Horn.WorklistCorrect" namespace Controller.Horn.Worklist
open CNF
def solveFormula (formula : Formula (Fin n)) : Option (Vector Bool n) := solveRules (normalizedTable formula)
end Controller.Horn.Worklist source_context "Controller.CNF.Relabel" namespace Controller.CNF
abbrev relabel (r : α → β) (f : Formula α) : Formula β := Controller.CNF.OrderedFormula.relabel r f
end Controller.CNF source_context "Controller.Decoder.Detect" namespace Controller.Decoder
namespace DAG
def zeroIndex (graph : DAG n) : graph.ZeroVar ≃ Fin (n + graph.nodeCount) := finSumFinEquiv
def finiteZeroSystem (graph : DAG n) (b : Nat) (target : Channel n) (root : Fin graph.nodeCount) (T F : Finset (Channel n)) : CNF.FiniteFormula (n + graph.nodeCount) := CNF.relabel graph.zeroIndex (graph.zeroSystem b target root T F)
def solveZero (graph : DAG n) (b : Nat) (target : Channel n) (root : Fin graph.nodeCount) (T F : Finset (Channel n)) : Option (Finset (Channel n)) := (Horn.Worklist.solveFormula (graph.finiteZeroSystem b target root T F)).map (fun values => graph.zeroChannelSet (fun coordinate => values[(graph.zeroIndex coordinate).val]))
def firstSuccess (query : α → Option β) : List α → Option β | [] => none | head :: tail => match query head with | some value => some value | none => firstSuccess query tail
end DAG
end Controller.Decoder source_context "Controller.Cost.ForestCursorMaterialize" namespace Controller.Cost.ForestCursorMaterialize
open Controller.Decoder Controller.Decoder.DAG
def allocatedHeap (width : ℕ) (heap : Array (Word width)) (values : List ℕ) : Array (Word width) := heap ++ (values.map (word width)).toArray
end Controller.Cost.ForestCursorMaterialize source_context "Controller.Cost.ForestIndexedOperands" namespace Controller.Cost.ForestIndexedOperands
open Controller.Decoder Controller.Decoder.DAG
def countSource (items : List α) (before : ℕ) : ℕ := match items with | [] => before | _ :: rest => countSource rest (before + 1)
structure Row where
  (tag : ℕ) (head : ℕ) (children : List ℕ) (guards : List ℕ)
  deriving DecidableEq, Repr
def Row.Matches (row : Row) (gate : Gate n available) : Prop := row.tag = (match gate with | .zero => 0 | .input _ => 1 | .disj _ => 2 | .guard _ _ => 3 | .liveAnd _ _ => 4) ∧ (∀ channel, gate = .input channel → row.head = channel.val) ∧ row.children = gate.children.map Fin.val ∧ row.guards = gate.guardLabels.map Fin.val
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
end Controller.Cost.ForestIndexedOperands source_context "Controller.Cost.ForestInputStored" namespace Controller.Cost.ForestInputStored
open Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestIndexedOperands
def withValues (heap : Array (Word width)) (values : Fin m → Bool) : Array (Word width) := heap ++ (List.ofFn (fun id => boolWord width (values id))).toArray
end Controller.Cost.ForestInputStored source_context "Controller.Cost.ForestInputPrefixStored" namespace Controller.Cost.ForestInputPrefixStored
open Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestInputStored
def channelHeap (heap : Array (Word width)) (rows : List Row) (roots : List ℕ) (channels : Channel n → Bool) : Array (Word width) := withValues (cacheHeap width heap rows roots) channels
end Controller.Cost.ForestInputPrefixStored source_context "Controller.Cost.UniformDAGSource" namespace Controller.Cost.UniformDAGSource
open Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestInputStored
open Controller.Cost.ForestInputPrefixStored
def typedHead (gate : Gate n available) : ℕ := match gate with | .input channel => channel.val | .guard child _ => child.val | .liveAnd left _ => left.val | _ => 0
structure HeadsMatch (graph : DAG n) (rows : List Row)
  (matched : RowsMatch graph rows) : Prop where
  head : ∀ node : Fin graph.nodeCount,
    (rows[node.val]'(by rw [matched.length_eq]; exact node.isLt)).head =
      typedHead (graph.node node)
end Controller.Cost.UniformDAGSource source_context "Controller.Cost.UniformDAGRun" namespace Controller.Cost.UniformDAGRun
open Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestInputPrefixStored
open Controller.Cost.UniformDAGSource
def packetHeaderHeap (width channels : ℕ) (rows : List Row) (roots : List ℕ) : Array (Word width) := ((globalHeader channels rows roots).map (word width)).toArray
end Controller.Cost.UniformDAGRun source_context "Controller.Decoder.Extend" namespace Controller.Decoder
variable {n : ℕ}
instance fixedConsistentDecidable (T F : Finset (Channel n)) : Decidable (FixedConsistent T F) := Finset.decidableDisjoint T F
def extensionBase (b : ℕ) (target : Channel n) (T : Finset (Channel n)) : Finset (Channel n) := if b = 1 then insert target T else T
def extensionCandidates (b : ℕ) (target : Channel n) (T F : Finset (Channel n)) : List (Finset (Channel n)) :=
  let base := extensionBase b target T
  base :: ((List.finRange n).filter fun head => head ∉ base ∧ head ∉ F).map
    (fun head => insert head base)
namespace DAG
def extensionTrueQuery (graph : DAG n) (healthy : Fin graph.nodeCount → Bool) (candidate : Finset (Channel n)) : Option (Finset (Channel n)) :=
  let values := graph.evalTable (assignmentOfSet candidate)
  if graph.roots.any (fun root => !healthy root && values root) then some candidate else none
def extensionZeroQuery (graph : DAG n) (b : ℕ) (target : Channel n) (healthy : Fin graph.nodeCount → Bool) (T F : Finset (Channel n)) (root : Fin graph.nodeCount) : Option (Finset (Channel n)) := if healthy root then graph.solveZero b target root T F else none
def extendSet (graph : DAG n) (b : ℕ) (target : Channel n) (drive : Bool) (T F : Finset (Channel n)) : Option (Finset (Channel n)) :=
  if drive then
    if FixedConsistent (extensionBase b target T) F then
      let healthy := graph.evalTable (assignmentOfSet {target})
      match firstSuccess (graph.extensionTrueQuery healthy) (extensionCandidates b target T F) with
      | some K => some K
      | none => firstSuccess (graph.extensionZeroQuery b target healthy T F) graph.roots
    else none
  else none
end DAG
end Controller.Decoder source_context "Controller.CNF.Gates" namespace Controller.CNF
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
end Controller.CNF source_context "Controller.CNF.Tseitin" namespace Controller.CNF
inductive AcyclicCircuit (r : Nat) : Nat → Type where
  | roots : AcyclicCircuit r r | snoc {v : Nat} (previous : AcyclicCircuit r v) (gate : Gate (Fin v)) (phase : Bool) : AcyclicCircuit r (v + 1)
end Controller.CNF source_context "Controller.Cost.NativeCircuitSize" namespace Controller.Cost.NativeCircuitSize
open Controller.CNF
def literalCount.{u_1} {α : Type u_1} (formula : Controller.CNF.Formula.{u_1} α) : Nat := @List.sum.{0} Nat instAddNat (@AddZero.toZero.{0} Nat (@AddZeroClass.toAddZero.{0} Nat (@AddMonoid.toAddZeroClass.{0} Nat Nat.instAddMonoid))) (@List.map.{u_1, 0} (List.{u_1} (Controller.CNF.Literal.{u_1} α)) Nat (@List.length.{u_1} (Controller.CNF.Literal.{u_1} α)) (@Array.toList.{u_1} (Controller.CNF.OrderedFormula.Clause.{u_1} α) (@Controller.CNF.OrderedFormula.clauses.{u_1} α formula)))
end Controller.Cost.NativeCircuitSize source_context "Controller.Physical.Controller" namespace Controller.Physical
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
end Controller.Physical source_context "Controller.Physical.Faults" namespace Controller.Physical
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
end Controller.Physical source_context "Controller.Native.Encode" namespace Controller.Native
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
def primaryRoles (parameters : Parameters) : List (PrimaryRole parameters.channels parameters.buses) := (List.finRange parameters.channels).map .enable ++ (List.finRange parameters.buses).flatMap (fun bus => (List.finRange parameters.channels).map (.request bus)) ++ [.wire]
def primaryAssignment {n b : ℕ} (input : Physical.PrimaryInput n b) (wire : Bool) :
    PrimaryRole n b → Bool
  | .enable channel => input.enable channel
  | .request bus channel => input.request bus channel
  | .wire => wire
end Parameters
end Controller.Native source_context "Controller.Native.BoundedEncode" namespace Controller.Native.Bounded
inductive Junction where
  | conjunction | disjunction
  deriving DecidableEq, Repr
def Junction.gate (junction : Junction) (inputs : List (CNF.Literal α)) : CNF.Gate α := match junction with | .conjunction => .and inputs | .disjunction => .or inputs
structure Producer (α : Type*) where
  (output : CNF.Literal α) (gate : CNF.Gate α)
  deriving DecidableEq, Repr
def Producer.rows (producer : Producer α) : List (CNF.Clause α) := producer.gate.clauses producer.output
end Controller.Native.Bounded
source_context "Controller.Native.LayoutTransport"
section
attribute [local instance 2000] Nat.instPartialOrder
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
end source_context "Controller.Physical.Realize" namespace Controller.Physical
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
end Controller.Physical source_context "Controller.Cost.NativeSourceExecution" namespace Controller.Cost.NativeSourceExecution
open Controller.CNF Controller.Native Controller.Native.SourceController
def selectedSize (parameters : Parameters) : NativeSize where
  variableCount := (compile parameters).toState.count; clauses := (formula parameters).clauses.size; literals := NativeCircuitSize.literalCount (formula parameters)
end Controller.Cost.NativeSourceExecution source_context "Controller.Cost.SharedRetainedCandidates" namespace Controller.Cost.SharedRetainedCandidates
open Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestIndexedOperands Controller.Cost.UniformDAGSource
open Controller.Cost.UniformDAGRun Controller.Cost.ForestInputPrefixStored
open Controller.Cost.ForestInputStored
def masks (width : Nat) (baseline : Assignment n) (flags : List Bool) : List (Word width) := (List.finRange n).map (fun channel => boolWord width (baseline channel)) ++ flags.map (boolWord width)
end Controller.Cost.SharedRetainedCandidates source_context "Controller.Cost.SharedMachineCapacity" namespace Controller.Cost.SharedMachineCapacity
open Controller.Native Controller.Native.SourceController
open Controller.Cost.NativeSourceExecution
open Controller.Decoder
def wordWidth (retained graphSize nativeSize : Nat) : Nat := Nat.log2 (retained + graphSize + nativeSize + 1) + 18
end Controller.Cost.SharedMachineCapacity source_context "Controller.Cost.SharedDetectorPrepared" namespace Controller.Cost.SharedDetectorPrepared
open Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestIndexedOperands Controller.Cost.UniformDAGSource
open Controller.Cost.UniformDAGRun Controller.Cost.ForestInputPrefixStored Controller.Cost.ForestInputStored
open Controller.Native Controller.Native.SourceController
section Layout
variable {n : Nat}
def rootBase (graph : DAG n) : Nat := 5 + 6 * graph.nodeCount + graph.childIncidences + graph.guardIncidences
def maskBase (graph : DAG n) : Nat := rootBase graph + graph.roots.length
def packetSize (graph : DAG n) : Nat := maskBase graph + n
end Layout
end Controller.Cost.SharedDetectorPrepared source_context "Controller.Cost.EnumerationUniformScan" namespace Controller.Cost.EnumerationUniformScan
open Controller.Native Controller.Native.SourceController Controller.Decoder
open Controller.Cost.NativeSourceExecution
variable {trueBase falseBase : Nat}
abbrev Width (parameters : Parameters) (graph : DAG parameters.channels) (retained : Nat) := SharedMachineCapacity.wordWidth retained graph.countedSize (selectedSize parameters).total
end Controller.Cost.EnumerationUniformScan source_context "Controller.Decoder.Enumerate" namespace Controller.Decoder
namespace Enumeration
def Before (first second : Finset (Channel n)) : Prop := ∃ channel : Channel n, channel ∉ first ∧ channel ∈ second ∧ ∀ earlier : Channel n, earlier.val < channel.val → (earlier ∈ first ↔ earlier ∈ second)
def fixedTrue (depth : ℕ) (partialSet : Finset (Channel n)) : Finset (Channel n) := partialSet.filter (fun channel => channel.val < depth)
def fixedFalse (depth : ℕ) (partialSet : Finset (Channel n)) : Finset (Channel n) := Finset.univ.filter (fun channel => channel.val < depth ∧ channel ∉ partialSet)
def Detecting (graph : DAG n) (busCount : ℕ) (target : Channel n) (drive : Bool) (K : Finset (Channel n)) : Prop :=
  drive = true ∧ Admissible busCount target K ∧
    ∃ root ∈ graph.roots, graph.eval (assignmentOfSet K) root ≠ graph.eval (assignmentOfSet {target}) root
def query (graph : DAG n) (busCount : ℕ) (target : Channel n) (drive : Bool) (depth : ℕ) (partialSet : Finset (Channel n)) : Bool := (graph.extendSet busCount target drive (fixedTrue depth partialSet) (fixedFalse depth partialSet)).isSome
structure Completed (n : ℕ) where
  (eligible : Finset (Channel n)) (tests : ℕ)
def complete (graph : DAG n) (busCount : ℕ) (target : Channel n) (drive : Bool)
    (depth : ℕ) (partialSet : Finset (Channel n)) : ℕ → Completed n
  | 0 => ⟨partialSet, 0⟩
  | fuel + 1 =>
    if lower : depth < n then
      let child : Channel n := ⟨depth, lower⟩
      let nextPrefix := if query graph busCount target drive (depth + 1) partialSet then partialSet else insert child partialSet
      let result := complete graph busCount target drive (depth + 1) nextPrefix fuel
      ⟨result.eligible, result.tests + 1⟩
    else ⟨partialSet, 0⟩
structure SearchResult (n : ℕ) where
  (output : Option (Finset (Channel n))) (tests : ℕ)
def seek (graph : DAG n) (busCount : ℕ) (target : Channel n) (drive : Bool)
    (previous : Finset (Channel n)) : ℕ → SearchResult n
  | 0 => ⟨none, 0⟩
  | cursor + 1 =>
    if lower : cursor < n then
      let channel : Channel n := ⟨cursor, lower⟩
      if channel ∈ previous then seek graph busCount target drive previous cursor
      else
        let partialSet := insert channel (fixedTrue cursor previous)
        if query graph busCount target drive (cursor + 1) partialSet then
          let result := complete graph busCount target drive (cursor + 1) partialSet
            (n - (cursor + 1))
          ⟨some result.eligible, result.tests + 1⟩
        else
          let result := seek graph busCount target drive previous cursor
          ⟨result.output, result.tests + 1⟩
    else seek graph busCount target drive previous cursor
inductive State (n : ℕ) where
  | initial | after (previous : Finset (Channel n)) | exhausted
structure NextResult (n : ℕ) where
  (output : Option (Finset (Channel n))) (continuation : State n) (tests : ℕ)
def Least (predicate : Finset (Channel n) → Prop) : Option (Finset (Channel n)) → Prop
  | none => ¬∃ K, predicate K
  | some result => predicate result ∧ ∀ K, predicate K → result = K ∨ Before result K
def next (graph : DAG n) (busCount : ℕ) (target : Channel n) (drive : Bool) (state : State n) : NextResult n :=
  let result : SearchResult n := match state with
    | .initial => if query graph busCount target drive 0 ∅ then
        let completed := complete graph busCount target drive 0 ∅ n
        ⟨some completed.eligible, completed.tests + 1⟩ else ⟨none, 1⟩
    | .after previous => seek graph busCount target drive previous n
    | .exhausted => ⟨none, 0⟩
  ⟨result.output, match result.output with | none => .exhausted | some K => .after K, result.tests⟩
def trace (graph : DAG n) (busCount : ℕ) (target : Channel n) (drive : Bool) :
    ℕ → State n → List (Finset (Channel n))
  | 0, _ => []
  | fuel + 1, state =>
    let result := next graph busCount target drive state
    match result.output with
    | none => []
    | some K => K :: trace graph busCount target drive fuel result.continuation
def observations (graph : DAG n) : Fin graph.roots.length → Assignment n → Bool := fun output a => graph.eval a (graph.roots.get output)
end Enumeration
end Controller.Decoder source_context "Controller.Cost.EnumerationMasks" namespace Controller.Cost.EnumerationMasks
open Controller.Decoder Controller.Decoder.Enumeration
variable {n : ℕ}
def masksOf (width : Nat) (B F : Finset (Channel n)) : List (Word width) := SharedRetainedCandidates.masks width (assignmentOfSet B) ((List.finRange n).map (assignmentOfSet F))
def maskList (width b : Nat) (t : Channel n) (d : Nat) (P : Finset (Channel n)) : List (Word width) := masksOf width (extensionBase b t (fixedTrue d P)) (fixedFalse d P)
end Controller.Cost.EnumerationMasks source_context "Controller.Cost.EnumerationStreamEmit" namespace Controller.Cost.EnumerationStreamEmit
def workingWords (state : State width 8) : Nat := 9 + state.heap.size + state.stack.length
end Controller.Cost.EnumerationStreamEmit source_context "Controller.Cost.EnumerationCanonicalEmit" namespace Controller.Cost.EnumerationCanonicalEmit
open Controller.Decoder Controller.Native Controller.Native.Parameters Controller.Physical
abbrev Coordinates (parameters : Parameters) : Nat := parameters.channels + parameters.buses * parameters.channels + 1
noncomputable def code : Controller.Native.Parameters → (width : ℕ) → ℕ → ℕ → List.{0} (Controller.Cost.Instruction width 8) := by sorry
def words (parameters : Parameters) (width : Nat) (K : Finset (Channel parameters.channels)) : List (Word width) := parameters.primaryRoles.map (fun role => boolWord width (primaryAssignment (realizeBridge parameters.bridge parameters.positiveBuses K) true role))
open Lean Elab Command in
run_cmd modifyEnv (fun env => Lean.setDefHeightOverride env `Controller.Cost.EnumerationCanonicalEmit.code 14)
end Controller.Cost.EnumerationCanonicalEmit source_context "Controller.Cost.EnumerationPrefixOracle" namespace Controller.Cost.EnumerationPrefixOracle
open Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestIndexedOperands Controller.Cost.UniformDAGSource Controller.Cost.UniformDAGRun
open Controller.Cost.ForestInputPrefixStored Controller.Cost.ForestInputStored
open Controller.Native Controller.Native.SourceController Controller.Cost.NativeSourceExecution
abbrev Width (parameters : Parameters) (graph : DAG parameters.channels) (retained : Nat) := EnumerationUniformScan.Width parameters graph retained
def packet (parameters : Parameters) (width : Nat) (rows : List Row) (roots : List Nat) : Array (Word width) :=
  channelHeap (packetHeaderHeap width parameters.channels rows roots) rows roots
    (assignmentOfSet {parameters.bridge.target})
end Controller.Cost.EnumerationPrefixOracle source_context "Controller.Cost.EnumerationDriverCode" namespace Controller.Cost.EnumerationDriverCode
open Controller.Decoder Controller.Native
structure Labels where
  (start : Nat) (call : Nat) (restore : Nat) (dispatch : Nat) (seekPost : Nat) (seekFail : Nat) (initialPost : Nat) (completePost : Nat) (completeRepair : Nat) (descend : Nat) (forcedDescend : Nat) (seek : Nat) (seekForced : Nat) (seekTry : Nat) (emit : Nat) (halt : Nat) (oracle : Nat)
def emitLength (parameters : Parameters) (graph : DAG parameters.channels) (width : Nat) : Nat := (EnumerationCanonicalEmit.code parameters width 0 (SharedDetectorPrepared.packetSize graph)).length
def labels (parameters : Parameters) (graph : DAG parameters.channels) (width entry : Nat) : Labels :=
  let call := entry + 4 * parameters.channels + 6
  let restore := call + 22
  let dispatch := restore + 4 * parameters.channels + 2
  let seekPost := dispatch + 6
  let seekFail := seekPost + 5
  let initialPost := seekFail + 6
  let completePost := initialPost + 3
  let completeRepair := completePost + 5
  let descend := completeRepair + 12
  let forcedDescend := descend + 10 + (if parameters.buses = 1 then 3 else 0)
  let seek := forcedDescend + 4
  let seekForced := seek + 19 + (if parameters.buses = 1 then 3 else 0)
  let seekTry := seekForced + 6
  let emit := seekTry + 11
  let halt := emit + emitLength parameters graph width + 2
  { start := entry, call, restore, dispatch, seekPost, seekFail, initialPost, completePost, completeRepair, descend, forcedDescend, seek, seekForced, seekTry, emit, halt, oracle := halt + 1 }
end Controller.Cost.EnumerationDriverCode source_context "Controller.Cost.EnumerationDriverPrefix" namespace Controller.Cost.EnumerationDriverPrefix
open Controller.Decoder Controller.Decoder.Enumeration Controller.Native
structure Ready (parameters : Parameters) (packet : Array (Word width))
  (depth cursor : Nat) (partialSet : Finset (Fin parameters.channels)) (state : State width 8) : Prop where
  (heap : state.heap = packet ++ (EnumerationMasks.maskList width parameters.buses parameters.bridge.target depth partialSet).toArray) (counter : state.reg 3 = word width cursor) (stack : state.stack = []) (running : state.halted = false)
end Controller.Cost.EnumerationDriverPrefix source_context "Controller.Cost.EnumerationDriverQuery" namespace Controller.Cost.EnumerationDriverQuery
open Controller.Decoder Controller.Decoder.Enumeration Controller.Native
open Controller.Cost.EnumerationDriverPrefix
abbrev budget (parameters : Parameters) (graph : DAG parameters.channels) : Nat := 24 * parameters.channels + 16 + (parameters.channels + graph.roots.length + 1) * (8000 * (graph.countedSize + 1))
end Controller.Cost.EnumerationDriverQuery source_context "Controller.Cost.EnumerationWorkingTrace" namespace Controller.Cost.EnumerationWorkingTrace
open Controller.Cost.EnumerationStreamEmit
inductive WorkingExecution (program : Program width 8) :
  State width 8 → State width 8 → Nat → Nat → Prop where
  | refl (state) : WorkingExecution program state state 0 (workingWords state) | cons {state middle final ticks peak} (transition : programStep program state = some middle) (rest : WorkingExecution program middle final ticks peak) : WorkingExecution program state final (ticks + 1) (max (workingWords state) peak)
end Controller.Cost.EnumerationWorkingTrace source_context "Controller.Cost.EnumerationDriverCapacity" namespace Controller.Cost.EnumerationDriverCapacity
open Controller.Decoder Controller.Native Controller.Native.SourceController
open Controller.Cost.NativeSourceExecution
open Controller.Cost.EnumerationDriverQuery
def retained (parameters : Parameters) (graph : DAG parameters.channels) : Nat := 10000 * (graph.countedSize + EnumerationCanonicalEmit.Coordinates parameters + 1)
abbrev Width (parameters : Parameters) (graph : DAG parameters.channels) : Nat := EnumerationPrefixOracle.Width parameters graph (retained parameters graph)
end Controller.Cost.EnumerationDriverCapacity source_context "Controller.Cost.EnumerationDriverStart" namespace Controller.Cost.EnumerationDriverStart
open Controller.Decoder Controller.Decoder.Enumeration Controller.Native
open Controller.Cost.EnumerationDriverPrefix Controller.Cost.EnumerationDriverQuery
def Endpoint (parameters : Parameters) (packet : Array (Word width)) (emit : Nat) (result : Option (Finset (Fin parameters.channels))) (state : State width 8) : Prop := match result with | none => state.halted = true | some K => Ready parameters packet parameters.channels parameters.channels K state ∧ state.pc = word width emit
end Controller.Cost.EnumerationDriverStart source_context "Controller.Cost.EnumerationDriverNext" namespace Controller.Cost.EnumerationDriverNext
open Controller.Decoder Controller.Decoder.Enumeration Controller.Native
open Controller.Cost.EnumerationDriverPrefix Controller.Cost.EnumerationDriverQuery
open Controller.Cost.EnumerationStreamEmit Controller.Cost.EnumerationWorkingTrace
def delay (parameters : Parameters) (graph : DAG parameters.channels) : Nat := (2 * parameters.channels + 1) * (budget parameters graph + 100)
def space (graph : DAG n) : Nat := 258 * (graph.countedSize + 1)
def Runtime (parameters : Parameters) (graph : DAG parameters.channels) (packet : Array (Word width)) (start seek : Nat) : Enumeration.State parameters.channels → State width 8 → Prop | .initial, state => state.heap = packet ∧ state.stack = [] ∧ state.halted = false ∧ state.pc = word width start | .after previous, state => Ready parameters packet parameters.channels parameters.channels previous state ∧ state.pc = word width seek ∧ Detecting graph parameters.buses parameters.bridge.target parameters.drive previous | .exhausted, state => state.halted = true ∧ workingWords state ≤ space graph
end Controller.Cost.EnumerationDriverNext source_context "Controller.Cost.EnumerationDriverStream" namespace Controller.Cost.EnumerationDriverStream
open Controller.Decoder Controller.Decoder.Enumeration Controller.Native
open Controller.Cost.EnumerationDriverPrefix Controller.Cost.EnumerationDriverQuery
open Controller.Cost.EnumerationStreamEmit Controller.Cost.EnumerationWorkingTrace
open Controller.Cost.EnumerationDriverNext
def words (parameters : Parameters) (width : Nat) (results : List (Finset (Fin parameters.channels))) : List (Word width) := results.flatMap (EnumerationCanonicalEmit.words parameters width)
def emitBudget (parameters : Parameters) : Nat := 5 + 4 * EnumerationCanonicalEmit.Coordinates parameters
end Controller.Cost.EnumerationDriverStream source_context "Controller.Cost.Enumeration" namespace Controller.Cost.Enumeration
open Controller.Decoder Controller.Native
open Controller.Cost.EnumerationStreamEmit Controller.Cost.EnumerationWorkingTrace
abbrev Width (parameters : Parameters) (graph : DAG parameters.channels) := EnumerationDriverCapacity.Width parameters graph
noncomputable def program : (parameters : Controller.Native.Parameters) → (graph : Controller.Decoder.DAG parameters.channels) → List.{0} Controller.Cost.ForestIndexedOperands.Row → List.{0} ℕ → Controller.Cost.Program (Controller.Cost.EnumerationDriverCapacity.Width parameters graph) 8 := by sorry
def initial (parameters : Parameters) (graph : DAG parameters.channels) (rows : List ForestIndexedOperands.Row) (roots : List Nat) : State (Width parameters graph) 8 where
  reg := fun _ => word (Width parameters graph) 0; heap := EnumerationPrefixOracle.packet parameters (Width parameters graph) rows roots; stack := []; output := []; pc := word (Width parameters graph) 0; halted := false
def results (parameters : Parameters) (graph : DAG parameters.channels) := Decoder.Enumeration.trace graph parameters.buses parameters.bridge.target parameters.drive (2 ^ parameters.channels + 1) .initial
/-- results exact: Canonical enumeration, termination and streaming delay. -/
theorem results_exact (parameters : Parameters) (graph : DAG parameters.channels) (guarded : graph.Guarded) : (results parameters graph).Nodup ∧ (results parameters graph).Pairwise Decoder.Enumeration.Before ∧ ∀ K, K ∈ results parameters graph ↔ Decoder.Enumeration.Detecting graph parameters.buses parameters.bridge.target parameters.drive K := by sorry
/-- canonical result detects: Canonical enumeration, termination and streaming delay. -/
theorem canonical_result_detects (parameters : Parameters) (graph : DAG parameters.channels) (guarded : graph.Guarded) (K : Finset (Fin parameters.channels)) (member : K ∈ results parameters graph) : Controller.Physical.BridgeInputDetects parameters.bridge true (Decoder.Enumeration.observations graph) (Controller.Physical.realizeBridge parameters.bridge parameters.positiveBuses K) true := by sorry
/-- delay bound: Canonical enumeration, termination and streaming delay. -/
theorem delay_bound (parameters : Parameters) (graph : DAG parameters.channels) : EnumerationDriverNext.delay parameters graph ≤ 100000 * parameters.channels * (parameters.channels + graph.roots.length) * graph.countedSize := by sorry
/-- program words bound: Canonical enumeration, termination and streaming delay. -/
theorem program_words_bound (parameters : Parameters) (graph : DAG parameters.channels) (rows : List ForestIndexedOperands.Row) (roots : List Nat) (rootMatches : ForestIndexedOperands.RootsMatch graph roots) : programWords (program parameters graph rows roots) ≤ 4 * (8 * parameters.channels + 129 + 6 * EnumerationCanonicalEmit.Coordinates parameters + 610 * (graph.countedSize + 1) + 1609) := by sorry
/-- execution: Canonical enumeration, termination and streaming delay. -/
theorem execution (parameters : Parameters) (graph : DAG parameters.channels) (guarded : graph.Guarded) (rows : List ForestIndexedOperands.Row) (roots : List Nat) (matched : ForestIndexedOperands.RowsMatch graph rows) (heads : UniformDAGSource.HeadsMatch graph rows matched) (rootMatches : ForestIndexedOperands.RootsMatch graph roots) : ∃ final ticks peak, WorkingExecution (program parameters graph rows roots) (initial parameters graph rows roots) final ticks peak ∧ ticks ≤ (2 ^ parameters.channels + 1) * EnumerationDriverNext.delay parameters graph + (results parameters graph).length * EnumerationDriverStream.emitBudget parameters ∧ peak ≤ 258 * (graph.countedSize + 1) ∧ final.halted = true ∧ final.output = (EnumerationDriverStream.words parameters (Width parameters graph) (results parameters graph)).reverse ∧ ∃ livePeak, Execution (program parameters graph rows roots) (initial parameters graph rows roots) final ticks livePeak := by sorry
/-- iterator delay: Canonical enumeration, termination and streaming delay. -/
theorem iterator_delay (parameters : Parameters) (graph : DAG parameters.channels) (guarded : graph.Guarded) (rows : List ForestIndexedOperands.Row) (roots : List Nat) (matched : ForestIndexedOperands.RowsMatch graph rows) (heads : UniformDAGSource.HeadsMatch graph rows matched) (rootMatches : ForestIndexedOperands.RootsMatch graph roots) (logical : Decoder.Enumeration.State parameters.channels) (state : State (Width parameters graph) 8) (runtime : EnumerationDriverNext.Runtime parameters graph (EnumerationPrefixOracle.packet parameters (Width parameters graph) rows roots) 0 (EnumerationDriverCode.labels parameters graph (Width parameters graph) 0).seek logical state) : ∃ final ticks peak, WorkingExecution (program parameters graph rows roots) state final ticks peak ∧ ticks ≤ 100000 * parameters.channels * (parameters.channels + graph.roots.length) * graph.countedSize ∧ peak ≤ 258 * (graph.countedSize + 1) ∧ final.output = state.output ∧ EnumerationDriverStart.Endpoint parameters (EnumerationPrefixOracle.packet parameters (Width parameters graph) rows roots) (EnumerationDriverCode.labels parameters graph (Width parameters graph) 0).emit (Decoder.Enumeration.next graph parameters.buses parameters.bridge.target parameters.drive logical).output final := by sorry
end Controller.Cost.Enumeration

end_source_context
