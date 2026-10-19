module
meta import all Lean.Environment
public meta import Lean.Elab.Command
public meta import Lean.Elab.Tactic.Basic
public meta import Lean.Util.FoldConsts
public meta import Lean.Meta.Match.Match
meta import all Lean.Meta.Match.Match
public meta import Lean.Meta.Constructions.SparseCasesOn
meta import all Lean.Meta.Constructions.SparseCasesOn
public meta import Lean.Meta.Tactic.AuxLemma

public import Lean.Elab.Tactic.Omega
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Nat.Log
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.IntervalCases
public import Std.Sat.CNF
open Lean in
meta partial def sourceDependencyOrder (infos : Std.HashMap Name ConstantInfo) (name : Name) : StateM (NameSet × Array Name) Unit := do
  if (← get).1.contains name then return
  let some info := infos[name]? | return
  modify fun (seen, order) => (seen.insert name, order)
  let used := info.type.foldConsts #[] fun n ns => ns.push n
  let used := (info.value? (allowOpaque := true)).map (fun value => value.foldConsts used fun n ns => ns.push n) |>.getD used
  for dependency in used do sourceDependencyOrder infos dependency
  modify fun (seen, order) => (seen, order.push name)
open Lean Elab Command in
elab "ctx " source:str : command => do
  let root := (← getOptions).get `sourceContextRoot ""
  if root.isEmpty then
    let original := (← getEnv).mainModule
    modifyScope fun scope => { scope with opts := scope.opts.set `sourceContextRoot original.toString }
  let checked := (← getEnv).toKernelEnv
  let mut env ← getEnv
  let locals := checked.constants.toList.filter fun (name, _) => env.getModuleIdxFor? name |>.isNone
  env := { env with base.private.constants := checked.constants, base.public.constants := checked.constants, asyncConstsMap := default, localRealizationCtxMap := {} }
  env := env.setMainModule ("Controller." ++ source.getString).toName
  env := Meta.auxLemmasExt.setState env {}
  env := (private_decl% Lean.Meta.Match.matcherExt).setState env {}
  env := (private_decl% Lean.Meta.sparseCasesOnCacheExt).setState env {}
  let infos := locals.foldl (fun table (name, info) => table.insert name info) ({} : Std.HashMap Name ConstantInfo)
  let (_, (_, order)) := (locals.forM fun (name, _) => sourceDependencyOrder infos name).run ({}, #[])
  for name in order do env ← env.enableRealizationsForConst (← getOptions) name
  setEnv env
open Lean Elab Command in
elab "end_ctx" : command => do
  let root := (← getOptions).get `sourceContextRoot ""
  if root.isEmpty then throwError "missing original Challenge module"
  modifyEnv (·.setMainModule root.toName)

open Lean Elab Tactic in
elab "source_aux_index " index:num : tactic => do
  let current ← getDeclNGen
  unless current.parentIdxs == [1] do throwError "unexpected source auxiliary scope"
  setDeclNGen { current with idx := index.getNat }
/- Omit editor states, preserving checked proof terms. -/
open Lean Elab Tactic in
elab "compact_proof " t:tacticSeq : tactic => withEnableInfoTree false (evalTactic t)
@[expose] public section
noncomputable section
ctx "Basic.Assignments"
namespace Controller
/-!
# Formula-forest execution and maximum weight
The grammar,state transitions,resource measures and mathematical predicates
are explicit. Definition holes identify only implementation witnesses;the
selected universal theorems constrain their executions or returned results.
The selected statements retain the exact assumptions of the proof library.
-/
section
abbrev Channel (n:ℕ):=Fin n
abbrev Assignment (n:ℕ):=Channel n→ Bool
def assignmentOfSet {n:ℕ} (K:Finset (Channel n)):Assignment n:=fun i=> decide (i ∈ K)
end ctx "Cost.Model" namespace Cost
abbrev Word (width : Nat) := Fin (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@instPowNat.{0} Nat instNatPowNat)) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) width)
def word (width value:Nat):Word width:= ⟨value % ((@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@instPowNat Nat instNatPowNat)) 2 width)),Nat.mod_lt _ (Nat.two_pow_pos width)⟩
structure State (width registers:Nat) where
  (reg:Fin registers→ Word width) (heap:Array (Word width)) (stack:List (Word width)) (output:List (Word width)) (pc:Word width) (halted:Bool)
def State.liveWords (s:State width registers):Nat:=registers+s.heap.size+s.stack.length+s.output.length+1
inductive Instruction (width registers:Nat) where
  | constant (dst:Fin registers) (value:Word width) | copy (dst src:Fin registers) | add (dst left right:Fin registers) | xor (dst left right:Fin registers) | load (dst address:Fin registers) | store (address src:Fin registers) | allocate (src:Fin registers) | release | push (src:Fin registers) | pop (dst:Fin registers) | emit (src:Fin registers) | branchZero (src:Fin registers) (target:Word width) | halt
def Instruction.arithmeticOps : Instruction width registers → Nat
  | .add .. | .xor .. => 1 | _ => 0
def State.put (s:State width registers) (dst:Fin registers) (value:Word width):State width registers:= { s with reg:=fun i=> if i=dst then value else s.reg i}
def State.advance (s:State width registers):State width registers:= { s with pc:=word width (s.pc.val+1)}
def step (instruction:Instruction width registers) (s:State width registers):Option (State width registers):=
  if s.halted then none else
  let next:=s.advance
  match instruction with
  | .constant dst value=> some (next.put dst value)
  | .copy dst src=> some (next.put dst (s.reg src))
  | .add dst left right=> some (next.put dst (word width ((s.reg left).val+ (s.reg right).val)))
  | .xor dst left right=> some (next.put dst (word width (Nat.xor (s.reg left).val (s.reg right).val)))
  | .load dst address=>
      if h: (s.reg address).val < s.heap.size then some (next.put dst s.heap[(s.reg address).val]) else none
  | .store address src=>
      if h: (s.reg address).val < s.heap.size then some { next with heap:=s.heap.set (s.reg address).val (s.reg src)} else none
  | .allocate src=>
      if s.heap.size < (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@instPowNat Nat instNatPowNat)) 2 width) then some { next with heap:=s.heap.push (s.reg src)}
      else none
  | .release=> if s.heap.isEmpty then none else some { next with heap:=s.heap.pop}
  | .push src=> some { next with stack:=s.reg src::s.stack}
  | .pop dst=> match s.stack with
      | []=> none
      | value::rest=> some { next.put dst value with stack:=rest}
  | .emit src=> some { next with output:=s.reg src::s.output}
  | .branchZero src target=> some (if (s.reg src).val=0 then { next with pc:=target} else next)
  | .halt=> some { next with halted:=true}
abbrev Program (width registers:Nat):=Array (Instruction width registers)
def programWords (p:Program width registers):Nat:=4*p.size
def programStep (p:Program width registers) (s:State width registers):Option (State width registers):=do
  let instruction ← p[s.pc.val]?
  step instruction s
inductive Execution (p:Program width registers):
  State width registers→ State width registers→ Nat→ Nat→ Prop where
  | refl (s):Execution p s s 0 s.liveWords | cons {s middle final ticks peak} (transition:programStep p s=some middle) (rest:Execution p middle final ticks peak):Execution p s final (ticks+1) (max s.liveWords peak)
end Cost ctx "Decoder.Syntax" namespace Decoder
inductive Gate (n available:ℕ) where
  | zero:Gate n available | input (channel:Channel n):Gate n available | disj (children:List (Fin available)):Gate n available | guard (child:Fin available) (labels:List (Channel n)):Gate n available | liveAnd (left right:Fin available):Gate n available
  deriving DecidableEq,Repr
namespace Gate
variable {n available:ℕ}
def children:Gate n available→ List (Fin available) | .zero=> [] | .input _=> [] | .disj refs=> refs | .guard child _=> [child] | .liveAnd left right=> [left,right]
def guardLabels:Gate n available→ List (Channel n) | .guard _ labels=> labels | _=> []
def isLiveAnd:Gate n available→ Bool | .liveAnd _ _=> true | _=> false
def IsGuarded (gate:Gate n available):Prop:=gate.isLiveAnd=false
def eval (gate:Gate n available) (assignment:Assignment n) (earlier:Fin available→ Bool):Bool:=
  match gate with
  | .zero=> false
  | .input channel=> assignment channel
  | .disj refs=> refs.any earlier
  | .guard child labels=> earlier child && !(labels.any assignment)
  | .liveAnd left right=> earlier left && earlier right
end Gate
structure DAG (n:ℕ) where
  (nodeCount:ℕ) (node: (index:Fin nodeCount)→ Gate n index.val) (roots:List (Fin nodeCount))
namespace DAG
variable {n:ℕ}
def childIndex (g0:DAG n) (parent:Fin g0.nodeCount) (child:Fin parent.val):Fin g0.nodeCount:= ⟨child.val,Nat.lt_trans child.isLt parent.isLt⟩
theorem childIndex_lt (g0:DAG n) (parent:Fin g0.nodeCount) (child:Fin parent.val): (g0.childIndex parent child).val < parent.val:=child.isLt
def Guarded (g0:DAG n):Prop:= ∀ index, (g0.node index).IsGuarded
def childIncidences (g0:DAG n):ℕ := @List.sum Nat instAddNat (@Zero.ofOfNat0 Nat (instOfNatNat (nat_lit 0))) (List.ofFn fun index:Fin g0.nodeCount=> (g0.node index).children.length)
def guardIncidences (g0:DAG n):ℕ := @List.sum Nat instAddNat (@Zero.ofOfNat0 Nat (instOfNatNat (nat_lit 0))) (List.ofFn fun index:Fin g0.nodeCount=> (g0.node index).guardLabels.length)
end DAG end Decoder ctx "Decoder.Eval" namespace Decoder
namespace DAG
variable {n:ℕ}
def eval (g0:DAG n) (assignment:Assignment n) (index:Fin g0.nodeCount):Bool:=
  (g0.node index).eval assignment (fun child=> g0.eval assignment (g0.childIndex index child))
termination_by index.val
decreasing_by exact g0.childIndex_lt index child
end DAG end Decoder ctx "Decoder.Cone" namespace Decoder
namespace DAG
variable {n:ℕ}
def cone (g0:DAG n) (root:Fin g0.nodeCount):Finset (Fin g0.nodeCount):=
  insert root ((g0.node root).children.toFinset.biUnion fun child=> g0.cone (g0.childIndex root child))
termination_by root.val
decreasing_by exact g0.childIndex_lt root child
theorem cone_eq (g0:DAG n) (root:Fin g0.nodeCount):g0.cone root=insert root ((g0.node root).children.toFinset.biUnion fun child=> g0.cone (g0.childIndex root child)):=by { rw [cone]}
@[simp] theorem self_mem_cone (g0:DAG n) (root:Fin g0.nodeCount):
    root ∈ g0.cone root:=by { rw [cone_eq];exact Finset.mem_insert_self _ _}
theorem cone_child_subset (g0:DAG n) (parent:Fin g0.nodeCount) (child:Fin parent.val) (membership:child ∈ (g0.node parent).children):g0.cone (g0.childIndex parent child) ⊆ g0.cone parent:=by { intro index indexMembership;rw [cone_eq];exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨child,by { simpa using membership},indexMembership⟩)}
def ChildClosed (g0:DAG n) (nodes:Finset (Fin g0.nodeCount)):Prop:= ∀ parent ∈ nodes, ∀ child ∈ (g0.node parent).children,g0.childIndex parent child ∈ nodes
theorem cone_childClosed (g0:DAG n) (root:Fin g0.nodeCount):g0.ChildClosed (g0.cone root):=by { intro parent hm0 child hc0;rw [cone_eq] at hm0;rcases Finset.mem_insert.mp hm0 with equality | membership; · { subst parent;exact g0.cone_child_subset root child hc0 (g0.self_mem_cone (g0.childIndex root child))}; · { obtain ⟨earlier,earlierMembership,hm0⟩ :=Finset.mem_biUnion.mp membership;exact g0.cone_child_subset root earlier (by { simpa using earlierMembership}) (g0.cone_childClosed (g0.childIndex root earlier) parent hm0 child hc0)}}
termination_by root.val
decreasing_by exact g0.childIndex_lt root earlier
def cones (g0:DAG n) (roots:List (Fin g0.nodeCount)):Finset (Fin g0.nodeCount):=roots.toFinset.biUnion g0.cone
theorem root_mem_cones (g0:DAG n) (roots:List (Fin g0.nodeCount)) (root:Fin g0.nodeCount) (membership:root ∈ roots):root ∈ g0.cones roots:=by { exact Finset.mem_biUnion.mpr ⟨root,by { simpa using membership},g0.self_mem_cone root⟩ }
theorem cones_childClosed (g0:DAG n) (roots:List (Fin g0.nodeCount)):g0.ChildClosed (g0.cones roots):=by { intro parent hm0 child hc0;obtain ⟨root,rootMembership,hm0⟩ :=Finset.mem_biUnion.mp hm0;exact Finset.mem_biUnion.mpr ⟨root,rootMembership,g0.cone_childClosed root parent hm0 child hc0⟩ }
end DAG end Decoder ctx "Cost.Decoder" namespace Cost
def boolWord (width:Nat) (value:Bool):Word width:=word width (if value then 1 else 0)
end Cost
section
ctx "Basic.Admissible"
def Admissible {n:ℕ} (b:ℕ) (t:Channel n) (K:Finset (Channel n)):Prop:=K.Nonempty∧ (b=1→ t ∈ K)
end ctx "Decoder.Forest" namespace Decoder
namespace Gate
def isInternal:Gate n available→ Bool | .zero | .input _=> false | .disj _ | .guard _ _ | .liveAnd _ _=> true
end Gate
namespace DAG
variable {n:ℕ}
abbrev ParentOccurrence (g0:DAG n):=Σ parent:Fin g0.nodeCount,Fin (g0.node parent).children.length
abbrev StoredOccurrence (g0:DAG n):=Fin g0.roots.length ⊕ g0.ParentOccurrence
instance storedOccurrenceFintype (g0:DAG n):Fintype g0.StoredOccurrence:=by { dsimp [StoredOccurrence,ParentOccurrence];infer_instance}
def refers (g0:DAG n):g0.StoredOccurrence→ Fin g0.nodeCount | .inl rootPosition=> g0.roots.get rootPosition | .inr cp0=> g0.childIndex cp0.1 ((g0.node cp0.1).children.get cp0.2)
def parentRetained (g0:DAG n) (nodes:Finset (Fin g0.nodeCount)):g0.StoredOccurrence→ Prop | .inl _=> True | .inr cp0=> cp0.1 ∈ nodes
abbrev ActiveUses (g0:DAG n) (nodes:Finset (Fin g0.nodeCount)) (node:Fin g0.nodeCount):=
  {occurrence:g0.StoredOccurrence //
    g0.parentRetained nodes occurrence∧ g0.refers occurrence=node}
noncomputable instance activeUsesFintype (g0:DAG n) (nodes:Finset (Fin g0.nodeCount)) (node:Fin g0.nodeCount):Fintype (g0.ActiveUses nodes node):=Fintype.ofFinite _
def FormulaForest (g0:DAG n):Prop:=g0.Guarded∧ ∀ node, (g0.node node).isInternal=true→ Nat.card (g0.ActiveUses (g0.cones g0.roots) node)≤ 1
end DAG end Decoder ctx "Decoder.ForestWeight" namespace Decoder
variable {n:ℕ}
abbrev GuardCounters (n:ℕ):=Channel n→ ℕ
namespace GenericWeight
variable {W:Type*} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]
def total (ws0:Channel n→ W) (K:Finset (Channel n)):W:= ∑ channel ∈ K,ws0 channel
end GenericWeight
end Decoder ctx "Decoder.ForestTraversal" namespace Decoder
variable {n:ℕ}
abbrev LeafRoute:=List ℕ
end Decoder ctx "Cost.ForestCounter" namespace Cost.ForestCounter
open Decoder
def counterState (heap:Array (Word width)) (cursor:Nat) (address counter increment:Word width):State width 4 where
  reg:=fun register=> if register=0 then address else if register=1 then counter
    else if register=2 then increment else word width 0
  heap:=heap;stack:= [];output:= [];pc:=word width cursor;halted:=false
end Cost.ForestCounter ctx "Cost.Frames" namespace Cost
def State.frame (s:State width registers) (stack output:List (Word width)):State width registers:= { s with stack:=s.stack++stack,output:=s.output++output}
end Cost ctx "Cost.ForestGuardSchedule" namespace Cost.ForestGuardSchedule
open Decoder Cost.ForestCounter
inductive GuardEvent (n:ℕ) where
  | enter (channel:Channel n) | leave (channel:Channel n)
  deriving DecidableEq,Repr
def walkEvents (g0:DAG n) (index:Fin g0.nodeCount):List (GuardEvent n):=
  match g0.node index with
  | .zero | .input _ | .liveAnd _ _=> []
  | .disj children=> children.flatMap fun child=> walkEvents g0 (g0.childIndex index child)
  | .guard child labels=>
      labels.map GuardEvent.enter++walkEvents g0 (g0.childIndex index child)++
        labels.reverse.map GuardEvent.leave
termination_by index.val
decreasing_by all_goals exact g0.childIndex_lt _ _
def rootEvents (g0:DAG n):List (GuardEvent n):=g0.roots.flatMap (walkEvents g0)
end Cost.ForestGuardSchedule ctx "Cost.ForestOccurrences" namespace Cost.ForestOccurrences
open Decoder
variable {n:ℕ}
theorem active_use_unique (g0:DAG n) (fr0:g0.FormulaForest) (node:Fin g0.nodeCount) (internal: (g0.node node).isInternal=true) (f0 s0:g0.ActiveUses (g0.cones g0.roots) node):f0=s0:=by
  have cardinality:Fintype.card (g0.ActiveUses (g0.cones g0.roots) node)≤ 1:=by simpa only [Nat.card_eq_fintype_card] using fr0.2 node internal
  letI:Subsingleton (g0.ActiveUses (g0.cones g0.roots) node):=Fintype.card_le_one_iff_subsingleton.mp cardinality
  exact Subsingleton.elim f0 s0
theorem active_occurrence_unique (g0:DAG n) (fr0:g0.FormulaForest) (node:Fin g0.nodeCount) (internal: (g0.node node).isInternal=true) (f0 s0:g0.StoredOccurrence) (firstActive:g0.parentRetained (g0.cones g0.roots) f0) (secondActive:g0.parentRetained (g0.cones g0.roots) s0) (firstRefers:g0.refers f0=node) (secondRefers:g0.refers s0=node):f0=s0:=by { have he0:=active_use_unique g0 fr0 node internal ⟨f0,firstActive,firstRefers⟩ ⟨s0,secondActive,secondRefers⟩;exact congrArg Subtype.val he0}
theorem parent_internal (g0:DAG n) (parent:Fin g0.nodeCount) (position:Fin (g0.node parent).children.length): (g0.node parent).isInternal=true:=by { have valid:=position.isLt;cases equation:g0.node parent <;> simp_all [Gate.children,Gate.isInternal]}
inductive RootedPath (g0:DAG n):
  Fin g0.nodeCount→ List g0.StoredOccurrence→ Prop where
  | root (position:Fin g0.roots.length):RootedPath g0 (g0.roots.get position) [.inl position] | child (parent:Fin g0.nodeCount) (position:Fin (g0.node parent).children.length) (ar0:List g0.StoredOccurrence) (path:RootedPath g0 parent ar0):RootedPath g0 (g0.childIndex parent ((g0.node parent).children.get position)) (.inr ⟨parent,position⟩ ::ar0)
namespace RootedPath
theorem endpoint_mem_cones {g0:DAG n} {node:Fin g0.nodeCount} {route:List g0.StoredOccurrence} (path:RootedPath g0 node route):node ∈ g0.cones g0.roots:=by { induction path with | root position=> { exact g0.root_mem_cones g0.roots _ (List.get_mem _ _)} | child parent position ar0 path ih=> { exact g0.cones_childClosed g0.roots parent ih _ (List.get_mem _ _)}}
theorem nonempty {g0:DAG n} {node:Fin g0.nodeCount} {route:List g0.StoredOccurrence} (path:RootedPath g0 node route):route ≠ []:=by { cases path <;> simp}
theorem unique_internal (g0:DAG n) (fr0:g0.FormulaForest): ∀ (node:Fin g0.nodeCount) (f0 s0:List g0.StoredOccurrence), (g0.node node).isInternal=true→ RootedPath g0 node f0→ RootedPath g0 node s0→ f0=s0:=by compact_proof { have claim: ∀ rank:ℕ, ∀ (firstNode secondNode:Fin g0.nodeCount),g0.nodeCount - firstNode.val=rank→ firstNode=secondNode→ ∀ (f0 s0:List g0.StoredOccurrence), (g0.node firstNode).isInternal=true→ RootedPath g0 firstNode f0→ RootedPath g0 secondNode s0→ f0=s0:=by { intro rank;induction rank using Nat.strong_induction_on with | h rank ih=> { intro firstNode secondNode rankEquation heq0 f0 s0 internal firstPath secondPath;cases firstPath with | root fp0=> { cases secondPath with | root sp0=> { have positions:=active_occurrence_unique g0 fr0 _ internal (.inl fp0) (.inl sp0) trivial trivial rfl heq0.symm;have he0:=Sum.inl.inj positions;cases he0;rfl} | child parent position ar0 path=> { have positions:=active_occurrence_unique g0 fr0 _ internal (.inl fp0) (.inr ⟨parent,position⟩) trivial (path.endpoint_mem_cones) rfl heq0.symm;cases positions}} | child pa0 fp0 firstPrefix firstPath=> { cases secondPath with | root sp0=> { have positions:=active_occurrence_unique g0 fr0 _ internal (.inr ⟨pa0,fp0⟩) (.inl sp0) firstPath.endpoint_mem_cones trivial rfl heq0.symm;cases positions} | child pb0 sp0 secondPrefix secondPath=> { have positions:=active_occurrence_unique g0 fr0 _ internal (.inr ⟨pa0,fp0⟩) (.inr ⟨pb0,sp0⟩) firstPath.endpoint_mem_cones secondPath.endpoint_mem_cones rfl heq0.symm;have parentEqual:pa0=pb0:=congrArg Sigma.fst (Sum.inr.inj positions);subst pb0;have positionEqual:fp0=sp0:=by { exact congrArg (fun pair:g0.ParentOccurrence=> pair.2.val) (Sum.inr.inj positions) |> Fin.ext};subst sp0;have decrease:g0.nodeCount - pa0.val < rank:=by { have earlier:=g0.childIndex_lt pa0 ((g0.node pa0).children.get fp0);omega};have prefixes:=ih _ decrease pa0 pa0 rfl rfl firstPrefix secondPrefix (parent_internal g0 pa0 fp0) firstPath secondPath;exact congrArg (List.cons (.inr ⟨pa0,fp0⟩)) prefixes}}}};intro node f0 s0 internal firstPath secondPath;exact claim _ node node rfl rfl f0 s0 internal firstPath secondPath}
end RootedPath
end Cost.ForestOccurrences ctx "Cost.ForestGuardCharging" namespace Cost.ForestGuardCharging
open Decoder Cost.ForestOccurrences
variable {n:ℕ}
abbrev GuardPosition (g0:DAG n):=Σ node:Fin g0.nodeCount,Fin (g0.node node).guardLabels.length
abbrev GuardKey (g0:DAG n):=GuardPosition g0 × Bool
instance guardKeyFintype (g0:DAG n):Fintype (GuardKey g0):=by { dsimp [GuardKey,GuardPosition];infer_instance}
structure GuardVisit (g0:DAG n) where
  (node:Fin g0.nodeCount) (route:List g0.StoredOccurrence) (rooted:RootedPath g0 node route) (position:Fin (g0.node node).guardLabels.length) (phase:Bool)
theorem guard_internal (g0:DAG n) (node:Fin g0.nodeCount) (position:Fin (g0.node node).guardLabels.length): (g0.node node).isInternal=true:=by { have valid:=position.isLt;cases equation:g0.node node <;> simp_all [Gate.guardLabels,Gate.isInternal]}
def GuardVisit.key {g0:DAG n} (visit:GuardVisit g0):GuardKey g0:= (⟨visit.node,visit.position⟩,visit.phase)
theorem key_injective (g0:DAG n) (fr0:g0.FormulaForest):Function.Injective (GuardVisit.key (g0:=g0)):=by compact_proof { intro f0 s0 he0;cases f0 with | mk firstNode firstRoute firstPath fp0 firstPhase=> { cases s0 with | mk secondNode secondRoute secondPath sp0 secondPhase=> { have nodes:firstNode=secondNode:=congrArg (fun key:GuardKey g0=> key.1.1) he0;subst secondNode;have positions:fp0=sp0:=Fin.ext (congrArg (fun key:GuardKey g0=> key.1.2.val) he0);subst sp0;have phases:firstPhase=secondPhase:=congrArg (fun key:GuardKey g0=> key.2) he0;subst secondPhase;have routes:=RootedPath.unique_internal g0 fr0 firstNode firstRoute secondRoute (guard_internal g0 firstNode fp0) firstPath secondPath;subst secondRoute;rfl}}}
theorem key_card (g0:DAG n):Nat.card (GuardKey g0)=2*g0.guardIncidences:=by { simp only [GuardKey,GuardPosition,Nat.card_prod,Nat.card_sigma,Nat.card_fin,Nat.card_eq_fintype_card,Fintype.card_bool];simp [DAG.guardIncidences,List.sum_ofFn,Nat.mul_comm]}
theorem visit_card_le (g0:DAG n) (fr0:g0.FormulaForest):Nat.card (GuardVisit g0)≤ 2*g0.guardIncidences:=by { have bounded:=Nat.card_le_card_of_injective (GuardVisit.key (g0:=g0)) (key_injective g0 fr0);exact bounded.trans_eq (key_card g0)}
end Cost.ForestGuardCharging ctx "Cost.ForestGuardVisits" namespace Cost.ForestGuardVisits
open Decoder Cost.ForestOccurrences
open Cost.ForestGuardCharging Cost.ForestGuardSchedule
variable {n:ℕ}
def ownVisits (g0:DAG n) (node:Fin g0.nodeCount) (route:List g0.StoredOccurrence) (rooted:RootedPath g0 node route) (phase:Bool):List (GuardVisit g0):=List.ofFn fun position:Fin (g0.node node).guardLabels.length=> ⟨node,route,rooted,position,phase⟩
theorem own_route (g0:DAG n) (node:Fin g0.nodeCount) (route:List g0.StoredOccurrence) (rooted:RootedPath g0 node route) (phase:Bool) (visit:GuardVisit g0) (hp0:visit ∈ ownVisits g0 node route rooted phase):visit.route=route:=by { obtain ⟨position,he0⟩ :=List.mem_ofFn.mp hp0;cases he0;rfl}
theorem own_phase (g0:DAG n) (node:Fin g0.nodeCount) (route:List g0.StoredOccurrence) (rooted:RootedPath g0 node route) (phase:Bool) (visit:GuardVisit g0) (hp0:visit ∈ ownVisits g0 node route rooted phase):visit.phase=phase:=by { obtain ⟨position,he0⟩ :=List.mem_ofFn.mp hp0;cases he0;rfl}
theorem own_nodup (g0:DAG n) (node:Fin g0.nodeCount) (route:List g0.StoredOccurrence) (rooted:RootedPath g0 node route) (phase:Bool): (ownVisits g0 node route rooted phase).Nodup:=by { apply List.nodup_ofFn_ofInjective;intro f0 s0 he0;exact Fin.ext (congrArg (fun visit:GuardVisit g0=> visit.position.val) he0)}
def walkGhost (g0:DAG n) (node:Fin g0.nodeCount) (route:List g0.StoredOccurrence) (rooted:RootedPath g0 node route):List (GuardVisit g0):=
  ownVisits g0 node route rooted false++
    (List.ofFn fun position:Fin (g0.node node).children.length=>
      walkGhost g0 (g0.childIndex node ((g0.node node).children.get position))
        (.inr ⟨node,position⟩ ::route) (RootedPath.child node position route rooted)).flatten++
    (ownVisits g0 node route rooted true).reverse
termination_by node.val
decreasing_by all_goals exact g0.childIndex_lt _ _
theorem route_suffix (g0:DAG n): ∀ (node:Fin g0.nodeCount) (route:List g0.StoredOccurrence) (rooted:RootedPath g0 node route) (visit:GuardVisit g0),visit ∈ walkGhost g0 node route rooted→ route <:+visit.route:=by compact_proof { have claim: ∀ rank:ℕ, ∀ (node:Fin g0.nodeCount),node.val=rank→ ∀ (route:List g0.StoredOccurrence) (rooted:RootedPath g0 node route) (visit:GuardVisit g0),visit ∈ walkGhost g0 node route rooted→ route <:+visit.route:=by { intro rank;induction rank using Nat.strong_induction_on with | h rank ih=> { intro node value route rooted visit hp0;rw [walkGhost.eq_def] at hp0;rcases List.mem_append.mp hp0 with before | after; · { rcases List.mem_append.mp before with own | ds0; · { rw [own_route g0 node route rooted false visit own]}; · { obtain ⟨block,hb0,hv0⟩ :=List.mem_flatten.mp ds0;obtain ⟨position,he0⟩ :=List.mem_ofFn.mp hb0;subst block;have suffix:=ih ((g0.node node).children.get position).val (by { have earlier:=g0.childIndex_lt node ((g0.node node).children.get position);omega}) _ rfl _ _ visit hv0;exact (List.suffix_cons _ route).trans suffix}}; · { have own:=List.mem_reverse.mp after;rw [own_route g0 node route rooted true visit own]}}};intro node route rooted visit hp0;exact claim node.val node rfl route rooted visit hp0}
theorem equal_length_suffix {f0 s0 whole:List α} (sa0:f0 <:+whole) (sb0:s0 <:+whole) (lengths:f0.length=s0.length):f0=s0:=by { exact (List.suffix_of_suffix_length_le sa0 sb0 lengths.le).eq_of_length lengths}
def childrenGhost (g0:DAG n) (node:Fin g0.nodeCount) (route:List g0.StoredOccurrence) (rooted:RootedPath g0 node route):List (GuardVisit g0):= (List.ofFn fun position:Fin (g0.node node).children.length=> walkGhost g0 (g0.childIndex node ((g0.node node).children.get position)) (.inr ⟨node,position⟩ ::route) (RootedPath.child node position route rooted)).flatten
theorem own_children_disjoint (g0:DAG n) (node:Fin g0.nodeCount) (route:List g0.StoredOccurrence) (rooted:RootedPath g0 node route) (phase:Bool):List.Disjoint (ownVisits g0 node route rooted phase) (childrenGhost g0 node route rooted):=by compact_proof { apply List.disjoint_left.mpr;intro visit ownPresent ds0;have ownRoute:=own_route g0 node route rooted phase visit ownPresent;obtain ⟨block,hb0,hv0⟩ :=List.mem_flatten.mp ds0;obtain ⟨position,he0⟩ :=List.mem_ofFn.mp hb0;subst block;have suffix:=route_suffix g0 _ _ _ visit hv0;have lengths:=suffix.length_le;rw [ownRoute] at lengths;simp only [List.length_cons] at lengths;omega}
theorem child_blocks_disjoint (g0:DAG n) (node:Fin g0.nodeCount) (route:List g0.StoredOccurrence) (rooted:RootedPath g0 node route) (f0 s0:Fin (g0.node node).children.length) (different:f0 ≠ s0):List.Disjoint (walkGhost g0 (g0.childIndex node ((g0.node node).children.get f0)) (.inr ⟨node,f0⟩ ::route) (RootedPath.child node f0 route rooted)) (walkGhost g0 (g0.childIndex node ((g0.node node).children.get s0)) (.inr ⟨node,s0⟩ ::route) (RootedPath.child node s0 route rooted)):=by
  apply List.disjoint_left.mpr
  intro visit ha0 hbb0
  have sa0:=route_suffix g0 _ _ _ visit ha0
  have sb0:=route_suffix g0 _ _ _ visit hbb0
  have routes:=equal_length_suffix sa0 sb0 rfl
  have heads:= (List.cons.inj routes).1
  have positions:f0=s0:=Fin.ext
    (congrArg (fun occurrence:g0.StoredOccurrence=> match occurrence with | .inl _=> 0 | .inr pair=> pair.2.val) heads)
  exact different positions
theorem walk_nodup (g0:DAG n): ∀ (node:Fin g0.nodeCount) (route:List g0.StoredOccurrence) (rooted:RootedPath g0 node route), (walkGhost g0 node route rooted).Nodup:=by compact_proof { classical{ have claim: ∀ rank:ℕ, ∀ (node:Fin g0.nodeCount),node.val=rank→ ∀ (route:List g0.StoredOccurrence) (rooted:RootedPath g0 node route), (walkGhost g0 node route rooted).Nodup:=by { intro rank;induction rank using Nat.strong_induction_on with | h rank ih=> { intro node value route rooted;have childrenNodup: (childrenGhost g0 node route rooted).Nodup:=by { apply List.nodup_flatten.mpr;constructor; · { intro block hb0;obtain ⟨position,he0⟩ :=List.mem_ofFn.mp hb0;subst block;exact ih ((g0.node node).children.get position).val (by { have earlier:=g0.childIndex_lt node ((g0.node node).children.get position);omega}) _ rfl _ _}; · { apply List.pairwise_ofFn.mpr;intro f0 s0 before;exact child_blocks_disjoint g0 node route rooted f0 s0 (ne_of_lt before)}};have beginningNodup:=List.nodup_append'.mpr ⟨own_nodup g0 node route rooted false,childrenNodup,own_children_disjoint g0 node route rooted false⟩;have endsNodup: ((ownVisits g0 node route rooted true).reverse).Nodup:=List.nodup_reverse.mpr (own_nodup g0 node route rooted true);have disjoint:List.Disjoint (ownVisits g0 node route rooted false++childrenGhost g0 node route rooted) (ownVisits g0 node route rooted true).reverse:=by { apply List.disjoint_left.mpr;intro visit hp0 endPresent;have endOwn:=List.mem_reverse.mp endPresent;rcases List.mem_append.mp hp0 with own | descendant; · { have firstPhase:=own_phase g0 node route rooted false visit own;have secondPhase:=own_phase g0 node route rooted true visit endOwn;simp_all}; · { exact List.disjoint_left.mp (own_children_disjoint g0 node route rooted true) endOwn descendant}};have joined:=List.nodup_append'.mpr ⟨beginningNodup,endsNodup,disjoint⟩;rw [walkGhost.eq_def];exact joined}};intro node route rooted;exact claim node.val node rfl route rooted}}
def rootGhost (g0:DAG n):List (GuardVisit g0):= (List.ofFn fun position:Fin g0.roots.length=> walkGhost g0 (g0.roots.get position) [.inl position] (RootedPath.root position)).flatten
theorem root_nodup (g0:DAG n): (rootGhost g0).Nodup:=by { classical{ apply List.nodup_flatten.mpr;constructor; · { intro block hp0;obtain ⟨position,he0⟩ :=List.mem_ofFn.mp hp0;subst block;exact walk_nodup g0 _ _ _}; · { apply List.pairwise_ofFn.mpr;intro f0 s0 before;apply List.disjoint_left.mpr;intro visit ha0 hbb0;have sa0:=route_suffix g0 _ _ _ visit ha0;have sb0:=route_suffix g0 _ _ _ visit hbb0;have routes:=equal_length_suffix sa0 sb0 rfl;have positions:f0=s0:=Sum.inl.inj (List.cons.inj routes).1;exact (ne_of_lt before) positions}}}
theorem root_length_le (g0:DAG n) (fr0:g0.FormulaForest): (rootGhost g0).length≤ 2*g0.guardIncidences:=by
  classical
  letI:Finite (GuardVisit g0):=Finite.of_injective
    (GuardVisit.key (g0:=g0)) (key_injective g0 fr0)
  letI:Fintype (GuardVisit g0):=Fintype.ofFinite _
  have bound: (rootGhost g0).length≤ Nat.card (GuardVisit g0):=by simpa only [Nat.card_eq_fintype_card] using (root_nodup g0).length_le_card
  exact bound.trans (visit_card_le g0 fr0)
def event {g0:DAG n} (visit:GuardVisit g0):GuardEvent n:=if visit.phase then .leave ((g0.node visit.node).guardLabels.get visit.position) else .enter ((g0.node visit.node).guardLabels.get visit.position)
theorem own_events (g0:DAG n) (node:Fin g0.nodeCount) (route:List g0.StoredOccurrence) (rooted:RootedPath g0 node route) (phase:Bool): (ownVisits g0 node route rooted phase).map event=if phase then (g0.node node).guardLabels.map GuardEvent.leave else (g0.node node).guardLabels.map GuardEvent.enter:=by { cases phase with | false=> { rw [ownVisits,List.map_ofFn];exact List.ofFn_getElem_eq_map _ GuardEvent.enter} | true=> { rw [ownVisits,List.map_ofFn];exact List.ofFn_getElem_eq_map _ GuardEvent.leave}}
theorem walk_events (g0:DAG n) (guarded:g0.Guarded): ∀ (node:Fin g0.nodeCount) (route:List g0.StoredOccurrence) (rooted:RootedPath g0 node route), (walkGhost g0 node route rooted).map event=walkEvents g0 node:=by compact_proof { have claim: ∀ rank:ℕ, ∀ (node:Fin g0.nodeCount),node.val=rank→ ∀ (route:List g0.StoredOccurrence) (rooted:RootedPath g0 node route), (walkGhost g0 node route rooted).map event=walkEvents g0 node:=by { intro rank;induction rank using Nat.strong_induction_on with | h rank ih=> { intro node value route rooted;have ds0: (childrenGhost g0 node route rooted).map event= (List.ofFn fun position:Fin (g0.node node).children.length=> walkEvents g0 (g0.childIndex node ((g0.node node).children.get position))).flatten:=by { simp only [childrenGhost,List.map_flatten,List.map_ofFn];apply congrArg List.flatten;apply congrArg List.ofFn;funext position;exact ih ((g0.node node).children.get position).val (by { have earlier:=g0.childIndex_lt node ((g0.node node).children.get position);omega}) _ rfl _ _};rw [walkGhost.eq_def];change ((ownVisits g0 node route rooted false++childrenGhost g0 node route rooted)++ (ownVisits g0 node route rooted true).reverse).map event=_;rw [List.map_append,List.map_append,List.map_reverse,own_events,own_events,ds0];rw [walkEvents.eq_def];have permitted:=guarded node;cases equation:g0.node node with | zero=> { simp [equation,Gate.guardLabels,Gate.children]} | input coordinate=> { simp [equation,Gate.guardLabels,Gate.children]} | disj children=> { simp [equation,Gate.guardLabels,Gate.children,List.flatMap];exact congrArg List.flatten (List.ofFn_getElem_eq_map children (fun child=> walkEvents g0 (g0.childIndex node child)))} | guard child labels=> { simp [equation,Gate.guardLabels,Gate.children,List.ofFn_succ,List.map_reverse]} | liveAnd left right=> { simp [equation,Gate.IsGuarded,Gate.isLiveAnd] at permitted}}};intro node route rooted;exact claim node.val node rfl route rooted}
theorem root_events (g0:DAG n) (guarded:g0.Guarded): (rootGhost g0).map event=rootEvents g0:=by { simp only [rootGhost,List.map_flatten,List.map_ofFn,Function.comp_apply,rootEvents];have mapped: (List.ofFn fun position:Fin g0.roots.length=> (walkGhost g0 (g0.roots.get position) [.inl position] (RootedPath.root position)).map event)=List.ofFn fun position:Fin g0.roots.length=> walkEvents g0 (g0.roots.get position):=by { apply congrArg List.ofFn;funext position;exact walk_events g0 guarded _ _ _};change (List.ofFn fun position:Fin g0.roots.length=> (walkGhost g0 (g0.roots.get position) [.inl position] (RootedPath.root position)).map event).flatten=g0.roots.flatMap (walkEvents g0);rw [mapped];exact congrArg List.flatten (List.ofFn_getElem_eq_map g0.roots (walkEvents g0))}
theorem root_event_count_le (g0:DAG n) (fr0:g0.FormulaForest): (rootEvents g0).length≤ 2*g0.guardIncidences:=by
  have counts:=congrArg List.length (root_events g0 fr0.1)
  simp only [List.length_map] at counts
  rw [← counts]
  exact root_length_le g0 fr0
end Cost.ForestGuardVisits ctx "Cost.ForestGuardAccumulator" namespace Cost.ForestGuardAccumulator
open Decoder Cost.ForestGuardSchedule
variable {n:ℕ}
theorem stored_occurrence_card (g0:DAG n):Nat.card g0.StoredOccurrence=g0.roots.length+g0.childIncidences:=by { simp only [DAG.StoredOccurrence,DAG.ParentOccurrence,Nat.card_sum,Nat.card_sigma,Nat.card_fin,Nat.card_eq_fintype_card];simp [DAG.childIncidences,List.sum_ofFn]}
theorem rooted_route_eq_of_incoming (g0:DAG n) (fr0:g0.FormulaForest) (firstNode secondNode:Fin g0.nodeCount) (firstRoute secondRoute:List g0.StoredOccurrence) (firstPath:Cost.ForestOccurrences.RootedPath g0 firstNode firstRoute) (secondPath:Cost.ForestOccurrences.RootedPath g0 secondNode secondRoute) (incoming:firstRoute.head? =secondRoute.head?):firstRoute=secondRoute:=by compact_proof { cases firstPath with | root fp0=> { cases secondPath with | root sp0=> { simp only [List.head?_cons,Option.some.injEq,Sum.inl.injEq] at incoming;cases incoming;rfl} | child parent position ar0 path=> { simp only [List.head?_cons,Option.some.injEq] at incoming;cases incoming}} | child pa0 fp0 firstAncestor firstAncestorPath=> { cases secondPath with | root sp0=> { simp only [List.head?_cons,Option.some.injEq] at incoming;cases incoming} | child pb0 sp0 secondAncestor secondAncestorPath=> { have positions: (⟨pa0,fp0⟩ :g0.ParentOccurrence)= ⟨pb0,sp0⟩ :=by { exact Sum.inr.inj (Option.some.inj incoming)};have parents:pa0=pb0:=congrArg Sigma.fst positions;subst pb0;have childPositions:fp0=sp0:=Fin.ext (congrArg (fun position:g0.ParentOccurrence=> position.2.val) positions);subst sp0;have ancestors:=Cost.ForestOccurrences.RootedPath.unique_internal g0 fr0 pa0 firstAncestor secondAncestor (Cost.ForestOccurrences.parent_internal g0 pa0 fp0) firstAncestorPath secondAncestorPath;rw [ancestors]}}}
structure NodeVisit (g0:DAG n) where
  (node:Fin g0.nodeCount) (route:List g0.StoredOccurrence) (rooted:Cost.ForestOccurrences.RootedPath g0 node route)
def NodeVisit.incoming {g0:DAG n} (visit:NodeVisit g0):g0.StoredOccurrence:=visit.route.head visit.rooted.nonempty
theorem incoming_refers (g0:DAG n) (visit:NodeVisit g0):g0.refers visit.incoming=visit.node:=by { cases visit with | mk node route rooted=> { cases rooted <;> rfl}}
theorem incoming_injective (g0:DAG n) (fr0:g0.FormulaForest):Function.Injective (NodeVisit.incoming (g0:=g0)):=by compact_proof {
  intro f0 s0 he0
  have nodes:f0.node=s0.node:=by
    rw [← incoming_refers g0 f0, ← incoming_refers g0 s0]
    exact congrArg g0.refers he0
  cases f0 with
  | mk firstNode firstRoute firstPath=>
    cases s0 with
    | mk secondNode secondRoute secondPath=>
      dsimp only at nodes
      subst secondNode
      have routes:=rooted_route_eq_of_incoming g0 fr0 firstNode firstNode
        firstRoute secondRoute firstPath secondPath (by
          rw [List.head?_eq_some_head firstPath.nonempty,List.head?_eq_some_head secondPath.nonempty]
          exact congrArg some he0)
      subst secondRoute
      rfl
}
theorem node_visit_card_le (g0:DAG n) (fr0:g0.FormulaForest):Nat.card (NodeVisit g0)≤ g0.roots.length+g0.childIncidences:=by { exact (Nat.card_le_card_of_injective (NodeVisit.incoming (g0:=g0)) (incoming_injective g0 fr0)).trans_eq (stored_occurrence_card g0)}
end Cost.ForestGuardAccumulator ctx "Cost.ForestNodeVisits" namespace Cost.ForestNodeVisits
open Decoder Cost.ForestOccurrences
open Cost.ForestGuardAccumulator
variable {n:ℕ}
def walkGhost (g0:DAG n) (node:Fin g0.nodeCount) (route:List g0.StoredOccurrence) (rooted:RootedPath g0 node route):List (NodeVisit g0):=
  ⟨node,route,rooted⟩ ::
    (List.ofFn fun position:Fin (g0.node node).children.length=>
      walkGhost g0 (g0.childIndex node ((g0.node node).children.get position))
        (.inr ⟨node,position⟩ ::route) (RootedPath.child node position route rooted)).flatten
termination_by node.val
decreasing_by all_goals exact g0.childIndex_lt _ _
theorem route_suffix (g0:DAG n): ∀ (node:Fin g0.nodeCount) (route:List g0.StoredOccurrence) (rooted:RootedPath g0 node route) (visit:NodeVisit g0),visit ∈ walkGhost g0 node route rooted→ route <:+visit.route:=by compact_proof { have claim: ∀ rank:ℕ, ∀ (node:Fin g0.nodeCount),node.val=rank→ ∀ (route:List g0.StoredOccurrence) (rooted:RootedPath g0 node route) (visit:NodeVisit g0),visit ∈ walkGhost g0 node route rooted→ route <:+visit.route:=by { intro rank;induction rank using Nat.strong_induction_on with | h rank ih=> { intro node value route rooted visit hp0;rw [walkGhost.eq_def] at hp0;rcases List.mem_cons.mp hp0 with he0 | descendant; · { subst visit;exact List.suffix_refl route}; · { obtain ⟨block,hb0,hv0⟩ :=List.mem_flatten.mp descendant;obtain ⟨position,he0⟩ :=List.mem_ofFn.mp hb0;subst block;have suffix:=ih ((g0.node node).children.get position).val (by { have earlier:=g0.childIndex_lt node ((g0.node node).children.get position);omega}) _ rfl _ _ visit hv0;exact (List.suffix_cons _ route).trans suffix}}};intro node route rooted visit hp0;exact claim node.val node rfl route rooted visit hp0}
private theorem equal_length_suffix {f0 s0 whole:List α} (sa0:f0 <:+whole) (sb0:s0 <:+whole) (lengths:f0.length=s0.length):f0=s0:= (List.suffix_of_suffix_length_le sa0 sb0 lengths.le).eq_of_length lengths
def childrenGhost (g0:DAG n) (node:Fin g0.nodeCount) (route:List g0.StoredOccurrence) (rooted:RootedPath g0 node route):List (NodeVisit g0):= (List.ofFn fun position:Fin (g0.node node).children.length=> walkGhost g0 (g0.childIndex node ((g0.node node).children.get position)) (.inr ⟨node,position⟩ ::route) (RootedPath.child node position route rooted)).flatten
theorem own_not_mem_children (g0:DAG n) (node:Fin g0.nodeCount) (route:List g0.StoredOccurrence) (rooted:RootedPath g0 node route): (⟨node,route,rooted⟩ :NodeVisit g0) ∉ childrenGhost g0 node route rooted:=by { intro hp0;obtain ⟨block,hb0,ownPresent⟩ :=List.mem_flatten.mp hp0;obtain ⟨position,he0⟩ :=List.mem_ofFn.mp hb0;subst block;have suffix:=route_suffix g0 _ _ _ _ ownPresent;have lengths:=suffix.length_le;simp only [List.length_cons] at lengths;omega}
theorem child_blocks_disjoint (g0:DAG n) (node:Fin g0.nodeCount) (route:List g0.StoredOccurrence) (rooted:RootedPath g0 node route) (f0 s0:Fin (g0.node node).children.length) (different:f0 ≠ s0):List.Disjoint (walkGhost g0 (g0.childIndex node ((g0.node node).children.get f0)) (.inr ⟨node,f0⟩ ::route) (RootedPath.child node f0 route rooted)) (walkGhost g0 (g0.childIndex node ((g0.node node).children.get s0)) (.inr ⟨node,s0⟩ ::route) (RootedPath.child node s0 route rooted)):=by
  apply List.disjoint_left.mpr
  intro visit ha0 hbb0
  have sa0:=route_suffix g0 _ _ _ visit ha0
  have sb0:=route_suffix g0 _ _ _ visit hbb0
  have routes:=equal_length_suffix sa0 sb0 rfl
  have heads:= (List.cons.inj routes).1
  have positions:f0=s0:=Fin.ext
    (congrArg (fun occurrence:g0.StoredOccurrence=> match occurrence with | .inl _=> 0 | .inr pair=> pair.2.val) heads)
  exact different positions
theorem walk_nodup (g0:DAG n): ∀ (node:Fin g0.nodeCount) (route:List g0.StoredOccurrence) (rooted:RootedPath g0 node route), (walkGhost g0 node route rooted).Nodup:=by compact_proof { classical{ have claim: ∀ rank:ℕ, ∀ (node:Fin g0.nodeCount),node.val=rank→ ∀ (route:List g0.StoredOccurrence) (rooted:RootedPath g0 node route), (walkGhost g0 node route rooted).Nodup:=by { intro rank;induction rank using Nat.strong_induction_on with | h rank ih=> { intro node value route rooted;have childrenNodup: (childrenGhost g0 node route rooted).Nodup:=by { apply List.nodup_flatten.mpr;constructor; · { intro block hb0;obtain ⟨position,he0⟩ :=List.mem_ofFn.mp hb0;subst block;exact ih ((g0.node node).children.get position).val (by { have earlier:=g0.childIndex_lt node ((g0.node node).children.get position);omega}) _ rfl _ _}; · { apply List.pairwise_ofFn.mpr;intro f0 s0 before;exact child_blocks_disjoint g0 node route rooted f0 s0 (ne_of_lt before)}};rw [walkGhost.eq_def];exact List.nodup_cons.mpr ⟨own_not_mem_children g0 node route rooted,childrenNodup⟩ }};intro node route rooted;exact claim node.val node rfl route rooted}}
def rootGhost (g0:DAG n):List (NodeVisit g0):= (List.ofFn fun position:Fin g0.roots.length=> walkGhost g0 (g0.roots.get position) [.inl position] (RootedPath.root position)).flatten
theorem root_nodup (g0:DAG n): (rootGhost g0).Nodup:=by { classical{ apply List.nodup_flatten.mpr;constructor; · { intro block hp0;obtain ⟨position,he0⟩ :=List.mem_ofFn.mp hp0;subst block;exact walk_nodup g0 _ _ _}; · { apply List.pairwise_ofFn.mpr;intro f0 s0 before;apply List.disjoint_left.mpr;intro visit ha0 hbb0;have sa0:=route_suffix g0 _ _ _ visit ha0;have sb0:=route_suffix g0 _ _ _ visit hbb0;have routes:=equal_length_suffix sa0 sb0 rfl;have positions:f0=s0:=Sum.inl.inj (List.cons.inj routes).1;exact (ne_of_lt before) positions}}}
theorem root_length_le (g0:DAG n) (fr0:g0.FormulaForest): (rootGhost g0).length≤ g0.roots.length+g0.childIncidences:=by
  classical
  letI:Finite (NodeVisit g0):=Finite.of_injective
    (NodeVisit.incoming (g0:=g0)) (incoming_injective g0 fr0)
  letI:Fintype (NodeVisit g0):=Fintype.ofFinite _
  have bound: (rootGhost g0).length≤ Nat.card (NodeVisit g0):=by simpa only [Nat.card_eq_fintype_card] using (root_nodup g0).length_le_card
  exact bound.trans (node_visit_card_le g0 fr0)
def walkNodes (g0:DAG n) (node:Fin g0.nodeCount):List (Fin g0.nodeCount):=
  node:: (g0.node node).children.flatMap (fun child=> walkNodes g0 (g0.childIndex node child))
termination_by node.val
decreasing_by all_goals exact g0.childIndex_lt _ _
theorem walk_nodes (g0:DAG n): ∀ (node:Fin g0.nodeCount) (route:List g0.StoredOccurrence) (rooted:RootedPath g0 node route), (walkGhost g0 node route rooted).map NodeVisit.node=walkNodes g0 node:=by compact_proof { have claim: ∀ rank:ℕ, ∀ (node:Fin g0.nodeCount),node.val=rank→ ∀ (route:List g0.StoredOccurrence) (rooted:RootedPath g0 node route), (walkGhost g0 node route rooted).map NodeVisit.node=walkNodes g0 node:=by { intro rank;induction rank using Nat.strong_induction_on with | h rank ih=> { intro node value route rooted;rw [walkGhost.eq_def,walkNodes.eq_def,List.map_cons,List.map_flatten,List.map_ofFn];apply congrArg (List.cons node);have mapped: (List.ofFn fun position:Fin (g0.node node).children.length=> (walkGhost g0 (g0.childIndex node ((g0.node node).children.get position)) (.inr ⟨node,position⟩ ::route) (RootedPath.child node position route rooted)).map NodeVisit.node)=List.ofFn fun position:Fin (g0.node node).children.length=> walkNodes g0 (g0.childIndex node ((g0.node node).children.get position)):=by { apply congrArg List.ofFn;funext position;exact ih ((g0.node node).children.get position).val (by { have earlier:=g0.childIndex_lt node ((g0.node node).children.get position);omega}) _ rfl _ _};change (List.ofFn fun position:Fin (g0.node node).children.length=> (walkGhost g0 (g0.childIndex node ((g0.node node).children.get position)) (.inr ⟨node,position⟩ ::route) (RootedPath.child node position route rooted)).map NodeVisit.node).flatten=_;rw [mapped];exact congrArg List.flatten (List.ofFn_getElem_eq_map (g0.node node).children (fun child=> walkNodes g0 (g0.childIndex node child)))}};intro node route rooted;exact claim node.val node rfl route rooted}
def rootNodes (g0:DAG n):List (Fin g0.nodeCount):=g0.roots.flatMap (walkNodes g0)
theorem root_nodes (g0:DAG n): (rootGhost g0).map NodeVisit.node=rootNodes g0:=by { simp only [rootGhost,rootNodes,List.map_flatten,List.map_ofFn];have mapped: (List.ofFn fun position:Fin g0.roots.length=> (walkGhost g0 (g0.roots.get position) [.inl position] (RootedPath.root position)).map NodeVisit.node)=List.ofFn fun position:Fin g0.roots.length=> walkNodes g0 (g0.roots.get position):=by { apply congrArg List.ofFn;funext position;exact walk_nodes g0 _ _ _};change (List.ofFn fun position:Fin g0.roots.length=> (walkGhost g0 (g0.roots.get position) [.inl position] (RootedPath.root position)).map NodeVisit.node).flatten=_;rw [mapped];exact congrArg List.flatten (List.ofFn_getElem_eq_map g0.roots (walkNodes g0))}
theorem root_node_count_le (g0:DAG n) (fr0:g0.FormulaForest): (rootNodes g0).length≤ g0.roots.length+g0.childIncidences:=by
  have counts:=congrArg List.length (root_nodes g0)
  simp only [List.length_map] at counts
  rw [← counts]
  exact root_length_le g0 fr0
end Cost.ForestNodeVisits ctx "Cost.ForestCursorTraversal" namespace Cost.ForestCursorTraversal
open Decoder Decoder.DAG
open Cost.ForestCounter
inductive CursorOp (n:ℕ) where
  | node (index:ℕ) | down (parent position child:ℕ) | up | enter (owner position:ℕ) (channel:Channel n) | leave (owner position:ℕ) (channel:Channel n) | leaf (owner:ℕ) (route:LeafRoute) (head:Channel n)
  deriving DecidableEq
def cursorOps (g0:DAG n) (node:Fin g0.nodeCount) (routePrefix:LeafRoute):List (CursorOp n):=
  .node node.val::match g0.node node with
  | .zero=> []
  | .input head=> [.leaf node.val routePrefix head]
  | .disj refs=> (List.finRange refs.length).flatMap fun position=>
      let child:=g0.childIndex node (refs.get position)
      [.down node.val position.val child.val]++cursorOps g0 child (position.val::routePrefix)++ [.up]
  | .guard child labels=>
      (List.finRange labels.length).map (fun position=> .enter node.val position.val (labels.get position))++
        [.down node.val 0 (g0.childIndex node child).val]++
        cursorOps g0 (g0.childIndex node child) (0::routePrefix)++ [.up]++
        (List.finRange labels.length).reverse.map (fun position=> .leave node.val position.val (labels.get position))
  | .liveAnd _ _=> []
termination_by node.val
decreasing_by all_goals exact g0.childIndex_lt _ _
end Cost.ForestCursorTraversal ctx "Cost.ForestCursorDescriptors" namespace Cost.ForestCursorDescriptors
open Decoder Decoder.DAG
open Cost.ForestCursorTraversal
structure ParentEntry where
  (identifier:ℕ) (parent:ℕ) (position:ℕ)
  deriving DecidableEq,Repr
structure LeafEntry where
  (root:ℕ) (owner:ℕ) (pointer:ℕ) (head:ℕ)
  deriving DecidableEq,Repr
structure Builder where
  (count:ℕ) (current:ℕ) (parents:List ℕ) (entries:List ParentEntry) (leaves:List LeafEntry)
  deriving Repr
def initial:Builder:= ⟨0,0, [], [], []⟩
def beginRoot (state:Builder):Builder:= { state with current:=0,parents:= []}
def step (root:ℕ) (state:Builder) (operation:CursorOp n):Builder:=
  match operation with
  | .down _ position _=>
      { state with
        count:=state.count+1
        current:=state.count+1
        parents:=state.current::state.parents
        entries:= ⟨state.count+1,state.current,position⟩ ::state.entries}
  | .up=> { state with current:=state.parents.headD 0,parents:=state.parents.tail}
  | .leaf owner _ head=> { state with leaves:= ⟨root,owner,state.current,head.val⟩ ::state.leaves}
  | _=> state
def scan (root:ℕ) (state:Builder) (operations:List (CursorOp n)):Builder:=operations.foldl (step root) state
structure Valid (state:Builder):Prop where
  (count:state.entries.length=state.count) (current:state.current≤ state.count) (parents: ∀ parent ∈ state.parents,parent≤ state.count) (entries: ∀ entry ∈ state.entries,0 < entry.identifier∧ entry.parent < entry.identifier∧ entry.identifier≤ state.count) (leaves: ∀ leaf ∈ state.leaves,leaf.pointer≤ state.count)
theorem initial_valid:Valid initial:=by { refine ⟨rfl,by { simp [initial]}, ?_, ?_, ?_⟩ <;> simp [initial]}
theorem beginRoot_valid (state:Builder) (valid:Valid state):Valid (beginRoot state):=by { exact ⟨valid.count,Nat.zero_le _,by { simp [beginRoot]},valid.entries,valid.leaves⟩ }
theorem step_valid (root:ℕ) (state:Builder) (valid:Valid state) (operation:CursorOp n):Valid (step root state operation):=by compact_proof { cases operation with | down owner position child=> { refine ⟨by { simpa [step] using congrArg Nat.succ valid.count},by { simp [step]}, ?_, ?_, ?_⟩; · { intro parent hp0;rcases List.mem_cons.mp hp0 with he0 | earlier; · { subst parent;exact Nat.le_trans valid.current (Nat.le_succ _)}; · { exact Nat.le_trans (valid.parents parent earlier) (Nat.le_succ _)}}; · { intro entry hp0;rcases List.mem_cons.mp hp0 with he0 | earlier; · { subst entry;exact ⟨by { simp},by { simpa using Nat.lt_succ_of_le valid.current},by { simp [step]}⟩ }; · { obtain ⟨positive,parentEarlier,bounded⟩ :=valid.entries entry earlier;exact ⟨positive,parentEarlier,Nat.le_trans bounded (Nat.le_succ _)⟩ }}; · { intro leaf hp0;exact Nat.le_trans (valid.leaves leaf hp0) (Nat.le_succ _)}} | up=> { refine ⟨valid.count, ?_, ?_,valid.entries,valid.leaves⟩; · { cases he0:state.parents with | nil=> { simp [step,he0]} | cons parent rest=> { simpa [step,he0] using valid.parents parent (by { rw [he0];exact List.mem_cons_self})}}; · { intro parent hp0;exact valid.parents parent (List.mem_of_mem_tail hp0)}} | leaf owner route head=> { refine ⟨valid.count,valid.current,valid.parents,valid.entries, ?_⟩;intro leaf hp0;rcases List.mem_cons.mp hp0 with he0 | earlier; · { subst leaf;exact valid.current}; · { exact valid.leaves leaf earlier}} | node owner=> { exact valid} | enter owner position channel=> { exact valid} | leave owner position channel=> { exact valid}}
theorem scan_valid (root:ℕ) (state:Builder) (valid:Valid state) (operations:List (CursorOp n)):Valid (scan root state operations):=by { induction operations generalizing state with | nil=> { exact valid} | cons operation rest ih=> { exact ih _ (step_valid root state valid operation)}}
def extendRoute (route : ℕ → LeafRoute) (identifier parent position : ℕ) : ℕ → LeafRoute :=
  fun pointer => if pointer = identifier then position :: route parent else route pointer
def routeStep (state : Builder) (route : ℕ → LeafRoute) (operation : CursorOp n) : ℕ → LeafRoute :=
  match operation with | .down _ position _ => extendRoute route (state.count + 1) state.current position | _ => route
def isDown:CursorOp n→ ℕ | .down _ _ _=> 1 | _=> 0
def allocations (operations:List (CursorOp n)):ℕ:= (operations.map isDown).sum
theorem step_count (root:ℕ) (state:Builder) (operation:CursorOp n): (step root state operation).count=state.count+isDown operation:=by { cases operation <;> simp [step,isDown]}
theorem scan_count (root:ℕ) (state:Builder) (operations:List (CursorOp n)): (scan root state operations).count=state.count+allocations operations:=by { induction operations generalizing state with | nil=> { simp [scan,allocations]} | cons operation rest ih=> { change (scan root (step root state operation) rest).count=_;rw [ih,step_count];simp [allocations,Nat.add_assoc]}}
theorem source_root_count (g0:DAG n) (position:Fin g0.roots.length) (state:Builder): (scan position.val (beginRoot state) (cursorOps g0 (g0.roots.get position) [])).count=state.count+allocations (cursorOps g0 (g0.roots.get position) []):=scan_count position.val (beginRoot state) _
def scanRoot (g0:DAG n) (state:Builder) (position:Fin g0.roots.length):Builder:=scan position.val (beginRoot state) (cursorOps g0 (g0.roots.get position) [])
def scanRoots (g0:DAG n) (state:Builder) (positions:List (Fin g0.roots.length)):Builder:=positions.foldl (scanRoot g0) state
def buildRoots (g0:DAG n):Builder:=scanRoots g0 initial (List.finRange g0.roots.length)
theorem scanRoot_valid (g0:DAG n) (state:Builder) (valid:Valid state) (position:Fin g0.roots.length):Valid (scanRoot g0 state position):=scan_valid position.val (beginRoot state) (beginRoot_valid state valid) _
theorem scanRoots_valid (g0:DAG n) (state:Builder) (valid:Valid state) (positions:List (Fin g0.roots.length)):Valid (scanRoots g0 state positions):=by { induction positions generalizing state with | nil=> { exact valid} | cons position rest ih=> { exact ih _ (scanRoot_valid g0 state valid position)}}
theorem buildRoots_valid (g0:DAG n):Valid (buildRoots g0):=scanRoots_valid g0 initial initial_valid _
theorem scanRoots_count (g0:DAG n) (state:Builder) (positions:List (Fin g0.roots.length)): (scanRoots g0 state positions).count=state.count+ (positions.map fun position=> allocations (cursorOps g0 (g0.roots.get position) [])).sum:=by { induction positions generalizing state with | nil=> { simp [scanRoots]} | cons position rest ih=> { change (scanRoots g0 (scanRoot g0 state position) rest).count=_;rw [ih];change (scan position.val (beginRoot state) _).count+_=_;rw [source_root_count];simp [Nat.add_assoc]}}
theorem buildRoots_count (g0:DAG n): (buildRoots g0).entries.length= ((List.finRange g0.roots.length).map fun position=> allocations (cursorOps g0 (g0.roots.get position) [])).sum:=by { rw [(buildRoots_valid g0).count];simpa [buildRoots,initial] using scanRoots_count g0 initial (List.finRange g0.roots.length)}
end Cost.ForestCursorDescriptors ctx "Cost.ForestIndexedOperands" namespace Cost.ForestIndexedOperands
open Decoder Decoder.DAG
open Cost.ForestCounter Cost.ForestCursorTraversal
def countSource (items:List α) (before:ℕ):ℕ:=
  match items with
  | []=> before
  | _::rest=> countSource rest (before+1)
structure Row where
  (tag:ℕ) (head:ℕ) (children:List ℕ) (guards:List ℕ)
  deriving DecidableEq,Repr
def Row.Matches (row:Row) (gate:Gate n available):Prop:=
  row.tag= (match gate with
    | .zero=> 0 | .input _=> 1 | .disj _=> 2 | .guard _ _=> 3 | .liveAnd _ _=> 4)∧
  (∀ channel,gate= .input channel→ row.head=channel.val)∧
  row.children=gate.children.map Fin.val∧ row.guards=gate.guardLabels.map Fin.val
def rowHeaders (rows:List Row):List ℕ:=rows.flatMap (fun row=> [row.tag,row.head])
def rowArities (rows:List Row):List ℕ:=rows.flatMap (fun row=> [countSource row.children 0,countSource row.guards 0])
def rowChildren (rows:List Row):List ℕ:=rows.flatMap Row.children
def rowGuards (rows:List Row):List ℕ:=rows.flatMap Row.guards
structure RowsMatch (g0:DAG n) (rows:List Row):Prop where
  (length_eq:rows.length=g0.nodeCount)
  node: ∀ index:Fin g0.nodeCount, (rows[index.val]'(by { rw [length_eq];exact index.isLt})).Matches (g0.node index)
def rowBases:List Row→ ℕ→ ℕ→ List ℕ | [],_,_=> [] | row::rest,childCursor,guardCursor=> childCursor::guardCursor::rowBases rest (childCursor+countSource row.children 0) (guardCursor+countSource row.guards 0)
def serializedRows (heapOffset:ℕ) (rows:List Row) (roots:List ℕ):List ℕ:=
  let children:=rowChildren rows
  let guards:=rowGuards rows
  rowHeaders rows++rowBases rows (heapOffset+6*rows.length)
    (heapOffset+6*rows.length+children.length)++rowArities rows++
    children++guards++roots
def RootsMatch (g0:DAG n) (roots:List ℕ):Prop:=roots=g0.roots.map Fin.val
def globalHeader (channels:ℕ) (rows:List Row) (roots:List ℕ):List ℕ:= [channels,countSource rows 0,countSource (rowChildren rows) 0,countSource (rowGuards rows) 0,countSource roots 0]
def inputPacket (channels heapOffset:ℕ) (rows:List Row) (roots:List ℕ):List ℕ:=globalHeader channels rows roots++serializedRows (heapOffset+5) rows roots
end Cost.ForestIndexedOperands ctx "Cost.UniformDAGSource" namespace Cost.UniformDAGSource
open Decoder Decoder.DAG
open Cost.ForestIndexedOperands
def typedHead (gate:Gate n available):ℕ:=
  match gate with
  | .input channel=> channel.val
  | .guard child _=> child.val
  | .liveAnd left _=> left.val
  | _=> 0
structure HeadsMatch (g0:DAG n) (rows:List Row)
  (matched:RowsMatch g0 rows):Prop where
  head: ∀ node:Fin g0.nodeCount,
    (rows[node.val]'(by { rw [matched.length_eq];exact node.isLt})).head=
      typedHead (g0.node node)
end Cost.UniformDAGSource ctx "Cost.RegisterWiden" namespace Cost.RegisterWiden
open Cost
def widenState (state:State width 4) (saved:Fin 8→ Word width):State width 8:=
  { reg:=fun register=> if small:register.val < 4 then
      state.reg ⟨register.val,small⟩ else saved register
    heap:=state.heap,stack:=state.stack,output:=state.output,
    pc:=state.pc,halted:=state.halted}
end Cost.RegisterWiden ctx "Cost.ForestCursorAllRootsExecution" namespace Cost.ForestCursorAllRootsExecution
open Decoder Decoder.DAG
open Cost.ForestCounter
open Cost.ForestCursorTraversal
open Cost.ForestGuardSchedule
open Cost.ForestCursorDescriptors
def rootOperations (g0:DAG n) (positions:List (Fin g0.roots.length)):ℕ:= (positions.map fun position=> (cursorOps g0 (g0.roots.get position) []).length).sum
end Cost.ForestCursorAllRootsExecution ctx "Cost.ForestCursorCharging" namespace Cost.ForestCursorCharging
open Decoder Decoder.DAG Cost.ForestCursorTraversal
open Cost.ForestGuardSchedule
open Cost.ForestCounter
def operationBudget (g0:DAG n) (node:Fin g0.nodeCount):ℕ:=
  match g0.node node with
  | .zero | .liveAnd _ _=> 1
  | .input _=> 2
  | .disj refs=> 1+ (refs.map fun child=> 2+operationBudget g0 (g0.childIndex node child)).sum
  | .guard child labels=> 3+2*labels.length+operationBudget g0 (g0.childIndex node child)
termination_by node.val
decreasing_by all_goals exact g0.childIndex_lt _ _
theorem cursor_length (g0 : DAG n) (node : Fin g0.nodeCount) (route : LeafRoute) :
    (cursorOps g0 node route).length = operationBudget g0 node := by compact_proof {
  have claim : ∀ rank : ℕ, ∀ current : Fin g0.nodeCount, current.val = rank →
      ∀ route, (cursorOps g0 current route).length = operationBudget g0 current := by
    intro rank
    induction rank using Nat.strong_induction_on with
    | h rank ih =>
      intro current he0 route
      rw [cursorOps, operationBudget]
      cases equation : g0.node current with
      | zero => simp
      | input head => simp
      | liveAnd left right => simp
      | guard child labels =>
          have below := ih (g0.childIndex current child).val
            (by have earlier := g0.childIndex_lt current child; source_aux_index 2; omega)
            (g0.childIndex current child) rfl (0 :: route)
          simp only [List.length_cons, List.length_append, List.length_map, List.length_reverse,
            List.length_finRange, List.length_nil, below]
          omega
      | disj refs =>
          have counts : ((List.finRange refs.length).map fun position =>
              2 + (cursorOps g0 (g0.childIndex current (refs.get position)) (position.val :: route)).length) =
              refs.map (fun child => 2 + operationBudget g0 (g0.childIndex current child)) := by
            calc
              _ = (List.finRange refs.length).map (fun position =>
                  2 + operationBudget g0 (g0.childIndex current (refs.get position))) := by
                apply List.map_congr_left
                intro position hp0
                rw [ih (g0.childIndex current (refs.get position)).val
                  (by have earlier := g0.childIndex_lt current (refs.get position); omega)
                  (g0.childIndex current (refs.get position)) rfl]
              _ = _ := by
                simpa only [List.map_map, Function.comp_def] using
                  congrArg (List.map (fun child => 2 + operationBudget g0 (g0.childIndex current child)))
                    (List.map_get_finRange refs)
          simp only [List.length_cons, List.length_flatMap, List.length_append,
            List.length_singleton, List.length_nil, Nat.zero_add]
          have same : ((List.finRange refs.length).map fun position =>
              (1 + (cursorOps g0 (g0.childIndex current (refs.get position)) (position.val :: route)).length) + 1) =
              (List.finRange refs.length).map (fun position =>
                2 + (cursorOps g0 (g0.childIndex current (refs.get position)) (position.val :: route)).length) := by
            apply List.map_congr_left
            intro position hp0
            omega
          simp only [Nat.add_assoc] at same ⊢
          rw [same, counts]
          omega
  exact claim node.val node rfl route
}
private theorem map_sum_bound (items:List α) (f0 s0:α→ ℕ) (bound: ∀ item ∈ items,f0 item≤ s0 item): (items.map f0).sum≤ (items.map s0).sum:=by { induction items with | nil=> { simp} | cons item rest ih=> { have head:=bound item List.mem_cons_self;have tail:=ih (fun current hp0=> bound current (List.mem_cons_of_mem item hp0));simp only [List.map_cons,List.sum_cons];omega}}
private theorem sum_budget (items:List α) (nodes guards:α→ ℕ): (items.map fun item=> 4*nodes item+guards item).sum=4* (items.map nodes).sum+ (items.map guards).sum:=by { induction items with | nil=> { simp} | cons item rest ih=> { simp only [List.map_cons,List.sum_cons,ih];omega}}
theorem operationBudget_bound (g0 : DAG n) (node : Fin g0.nodeCount) :
    operationBudget g0 node + 2 ≤
      4 * (ForestNodeVisits.walkNodes g0 node).length + (walkEvents g0 node).length := by compact_proof {
  have claim : ∀ rank : ℕ, ∀ current : Fin g0.nodeCount, current.val = rank →
      operationBudget g0 current + 2 ≤
        4 * (ForestNodeVisits.walkNodes g0 current).length + (walkEvents g0 current).length := by
    intro rank
    induction rank using Nat.strong_induction_on with
    | h rank ih =>
      intro current he0
      have below : ∀ child : Fin current.val,
          operationBudget g0 (g0.childIndex current child) + 2 ≤
            4 * (ForestNodeVisits.walkNodes g0 (g0.childIndex current child)).length +
              (walkEvents g0 (g0.childIndex current child)).length := by
        intro child
        exact ih child.val (by have earlier := g0.childIndex_lt current child; omega)
          (g0.childIndex current child) rfl
      rw [operationBudget, ForestNodeVisits.walkNodes, walkEvents]
      cases equation : g0.node current with
      | zero => simp [Gate.children]
      | input head => simp [Gate.children]
      | liveAnd left right =>
          simp only [Gate.children, List.length_cons]
          source_aux_index 4
          omega
      | guard child labels =>
          have bounded := below child
          simp only [Gate.children, List.flatMap_cons, List.flatMap_nil, List.append_nil,
            List.length_cons, List.length_append, List.length_map, List.length_reverse]
          omega
      | disj refs =>
          have bounded := map_sum_bound refs
            (fun child => 2 + operationBudget g0 (g0.childIndex current child))
            (fun child => 4 * (ForestNodeVisits.walkNodes g0 (g0.childIndex current child)).length +
              (walkEvents g0 (g0.childIndex current child)).length)
            (fun child hp0 => by have currentBound := below child; omega)
          rw [sum_budget] at bounded
          simp only [Gate.children, List.length_cons, List.length_flatMap]
          omega
  exact claim node.val node rfl
}
def allRootBudget (g0:DAG n):ℕ:= (g0.roots.map (operationBudget g0)).sum
theorem all_root_budget_bound (g0:DAG n) (fr0:g0.FormulaForest):allRootBudget g0≤ 4* (g0.roots.length+g0.childIncidences)+2*g0.guardIncidences:=by { have bounded:=map_sum_bound g0.roots (operationBudget g0) (fun root=> 4* (ForestNodeVisits.walkNodes g0 root).length+ (walkEvents g0 root).length) (fun root hp0=> by { have currentBound:=operationBudget_bound g0 root;omega});rw [sum_budget] at bounded;have nodes:=ForestNodeVisits.root_node_count_le g0 fr0;have guards:=ForestGuardVisits.root_event_count_le g0 fr0;simp only [ForestNodeVisits.rootNodes,rootEvents,List.length_flatMap] at nodes guards;unfold allRootBudget;omega}
end Cost.ForestCursorCharging ctx "Cost.ForestCursorWholeProgram" namespace Cost.ForestCursorWholeProgram
open Decoder Decoder.DAG
open Cost.ForestCounter
open Cost.ForestCursorTraversal
open Cost.ForestGuardSchedule
open Cost.ForestCursorDescriptors
open Cost.ForestCursorAllRootsExecution
private theorem allocations_le_length (operations:List (CursorOp n)):allocations operations≤ operations.length:=by { induction operations with | nil=> { simp [allocations]} | cons operation rest ih=> { cases operation <;> simp only [allocations,List.map_cons,List.sum_cons,isDown,List.length_cons] at* <;> omega}}
private theorem map_sum_bound (items:List α) (f0 s0:α→ ℕ) (bound: ∀ item ∈ items,f0 item≤ s0 item): (items.map f0).sum≤ (items.map s0).sum:=by { induction items with | nil=> { simp} | cons item rest ih=> { have head:=bound item List.mem_cons_self;have tail:=ih (fun current hp0=> bound current (List.mem_cons_of_mem item hp0));simp only [List.map_cons,List.sum_cons];omega}}
theorem descriptor_count_le_operations (g0:DAG n): (buildRoots g0).count≤ rootOperations g0 (List.finRange g0.roots.length):=by
  rw [← (buildRoots_valid g0).count,buildRoots_count]
  exact map_sum_bound _ _ _ (fun position _=> allocations_le_length _)
theorem rootOperations_total (g0:DAG n):rootOperations g0 (List.finRange g0.roots.length)=ForestCursorCharging.allRootBudget g0:=by { unfold rootOperations ForestCursorCharging.allRootBudget;simp only [ForestCursorCharging.cursor_length];have same:=congrArg (List.map (ForestCursorCharging.operationBudget g0)) (List.map_get_finRange g0.roots);simpa only [List.map_map,Function.comp_def] using congrArg List.sum same}
end Cost.ForestCursorWholeProgram ctx "Cost.ForestWeightedTagged" namespace Cost.ForestWeightedTagged
open Decoder Decoder.DAG
open Cost.ForestCursorTraversal
variable {W:Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]
structure Candidate (W:Type) where
  (root:ℕ) (pointer:ℕ) (score:W)
  deriving Repr
def choose (previous:Option (Candidate W)) (proposed:Candidate W):Option (Candidate W):=
  match previous with
  | none=> some proposed
  | some old=> if old.score < proposed.score then some proposed else previous
structure TaggedState (n:ℕ) (W:Type) where
  (blocked:GuardCounters n × W) (descriptors:ForestCursorDescriptors.Builder) (selected:Option (Candidate W))
end Cost.ForestWeightedTagged ctx "Cost.ForestWeightedDirect" namespace Cost.ForestWeightedDirect
open Decoder Decoder.DAG
open Cost.ForestCursorTraversal
open Cost.ForestWeightedTagged
variable {W:Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]
structure State (n:ℕ) (W:Type) where
  (data:TaggedState n W) (operations:ℕ) (arithmetic:ℕ)
def arithmeticCount (b:ℕ) (target:Channel n) (state:TaggedState n W):CursorOp n→ ℕ
  | .enter _ _ channel=> if state.blocked.1 channel=0 then 1 else 0
  | .leave _ _ channel=> if state.blocked.1 channel=1 then 1 else 0
  | .leaf _ _ head=>
      if state.blocked.1 head=0∧ (b ≠ 1∨ state.blocked.1 target=0) then match state.selected with | none=> 1 | some _=> 2
      else 0
  | _=> 0
end Cost.ForestWeightedDirect ctx "Cost.ForestWeightedIndexed" namespace Cost.ForestWeightedIndexed
open Decoder Decoder.DAG
open Cost.ForestIndexedOperands Cost.ForestWeightedTagged
open Cost.ForestCursorTraversal
variable {W:Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]
def boundedIds (bound:Nat):List Nat→ Option (List (Fin bound)) | []=> some [] | value::rest=> if valid:value < bound then (boundedIds bound rest).map (⟨value,valid⟩ :: ·) else none
def decodeRow (n owner:Nat) (row:Row):Option (Gate n owner):=
  match row.tag with
  | 0=> some .zero
  | 1=> if valid:row.head < n then some (.input ⟨row.head,valid⟩) else none
  | 2=> (boundedIds owner row.children).map Gate.disj
  | 3=> do
      let children ← boundedIds owner row.children
      let labels ← boundedIds n row.guards
      match children with
      | [child]=> some (.guard child labels)
      | _=> none
  | 4=> do
      let children ← boundedIds owner row.children
      match children with
      | [f0,s0]=> some (.liveAnd f0 s0)
      | _=> none
  | _=> none
abbrev Source (n:Nat):=Array (Option (Sigma fun owner:Nat=> Gate n owner))
def sourceItems (n:Nat) (rows:List Row):List (Option (Sigma fun owner:Nat=> Gate n owner)):=rows.zipIdx.map fun item=> (decodeRow n item.2 item.1).map (Sigma.mk item.2)
def source (n:Nat) (rows:List Row):Source n:= (sourceItems n rows).toArray
def readNode (table:Source n) (owner:Nat):Gate n owner:=
  match table[owner]? with
  | some (some ⟨rank,gate⟩)=> if same:rank=owner then same ▸ gate else .zero
  | _=> .zero
structure State (n:Nat) (W:Type) where
  (counters:Array Nat) (blockedWeight:W) (descriptors:ForestCursorDescriptors.Builder) (selected:Option (Candidate W)) (operations:Nat) (arithmetic:Nat)
def arrayView (counts:Array Nat) (channel:Channel n):Nat:=counts[channel.val]?.getD 0
def counter (state:State n W):Channel n→ Nat:=arrayView state.counters
def view (state:State n W):ForestWeightedDirect.State n W:= ⟨⟨(counter state,state.blockedWeight),state.descriptors,state.selected⟩,state.operations,state.arithmetic⟩
def emit (ws0:Channel n→ W) (total:W) (root b:Nat) (target:Channel n) (state:State n W) (operation:CursorOp n):State n W:=
  let next:= { state with
    descriptors:=ForestCursorDescriptors.step root state.descriptors operation
    operations:=state.operations+1
    arithmetic:=state.arithmetic+ForestWeightedDirect.arithmeticCount b target (view state).data operation}
  match operation with
  | .enter _ _ channel=>
      { next with
        counters:=state.counters.setIfInBounds channel.val (counter state channel+1)
        blockedWeight:=if counter state channel=0 then state.blockedWeight+ws0 channel else state.blockedWeight}
  | .leave _ _ channel=>
      { next with
        counters:=state.counters.setIfInBounds channel.val (counter state channel - 1)
        blockedWeight:=if counter state channel=1 then state.blockedWeight - ws0 channel else state.blockedWeight}
  | .leaf _ _ head=>
      if counter state head=0∧ (b ≠ 1∨ counter state target=0) then { next with selected:=choose state.selected ⟨root,state.descriptors.current,total - state.blockedWeight⟩ }
      else next
  | _=> next
def runNode (table:Source n) (ws0:Channel n→ W) (total:W) (root b:Nat) (target:Channel n) (owner:Nat) (state:State n W):State n W:=
  let entered:=emit ws0 total root b target state (.node owner)
  match readNode table owner with
  | .zero=> entered
  | .liveAnd _ _=> entered
  | .input head=> emit ws0 total root b target entered (.leaf owner [] head)
  | .disj children=> children.zipIdx.foldl (fun current item=>
      let down:=emit ws0 total root b target current (.down owner item.2 item.1.val)
      let visited:=runNode table ws0 total root b target item.1.val down
      emit ws0 total root b target visited .up) entered
  | .guard child labels=>
      let indexed:=labels.zipIdx
      let guarded:=indexed.foldl (fun current item=> emit ws0 total root b target current (.enter owner item.2 item.1)) entered
      let down:=emit ws0 total root b target guarded (.down owner 0 child.val)
      let visited:=runNode table ws0 total root b target child.val down
      let up:=emit ws0 total root b target visited .up
      indexed.reverse.foldl (fun current item=> emit ws0 total root b target current (.leave owner item.2 item.1)) up
termination_by owner
decreasing_by all_goals exact Fin.isLt _
def runRoots (table:Source n) (ws0:Channel n→ W) (total:W) (b:Nat) (target:Channel n) (roots:List Nat) (state:State n W):State n W:=
  roots.zipIdx.foldl (fun current item=>
    runNode table ws0 total item.2 b target item.1
      { current with descriptors:=ForestCursorDescriptors.beginRoot current.descriptors}) state
def runAll (table:Source n) (ws0:Channel n→ W) (b:Nat) (target:Channel n) (roots:List Nat):W × State n W:=
  let total:= (List.finRange n).foldl (fun value channel=> value+ws0 channel) 0
  (total,runRoots table ws0 total b target roots
    ⟨Array.replicate n 0,0,ForestCursorDescriptors.initial,none,0,n⟩)
end Cost.ForestWeightedIndexed
namespace Cost.ForestWeightedIndexed
open Decoder Decoder.DAG
open Cost.ForestCursorDescriptors Cost.ForestCursorTraversal
variable {W:Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]
def liveCells (state:State n W):Nat:=state.counters.size+4*state.descriptors.entries.length+5*state.descriptors.leaves.length+2*state.descriptors.parents.length+9
def startRoot (state:State n W):State n W:= { state with descriptors:=beginRoot state.descriptors}
end Cost.ForestWeightedIndexed
namespace Cost.ForestWeightedIndexed
open Decoder Decoder.DAG
open Cost.ForestCursorTraversal
variable {W:Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]
inductive StoreTrace (ws0:Channel n→ W) (total:W) (b:Nat) (target:Channel n):
  State n W→ State n W→ Nat→ Prop
  | refl (state:State n W):StoreTrace ws0 total b target state state (liveCells state) | operation (state:State n W) (root:Nat) (operation:CursorOp n):StoreTrace ws0 total b target state (emit ws0 total root b target state operation) (max (liveCells state) (liveCells (emit ws0 total root b target state operation))) | root (state:State n W):StoreTrace ws0 total b target state (startRoot state) (liveCells state) | append {f0 middle last:State n W} {left right:Nat} (earlier:StoreTrace ws0 total b target f0 middle left) (later:StoreTrace ws0 total b target middle last right):StoreTrace ws0 total b target f0 last (max left right)
end Cost.ForestWeightedIndexed
namespace Cost.ForestWeightedIndexed
open Decoder Decoder.DAG
def controlFrame (gate:Gate n owner):Nat:=12+4*gate.children.length+6*gate.guardLabels.length
def controlBudget (table:Source n):Nat→ Nat | 0=> 0 | owner+1=> controlBudget table owner+controlFrame (readNode table owner)
end Cost.ForestWeightedIndexed
namespace Cost.ForestWeightedIndexed
open Decoder Decoder.DAG Cost.ForestIndexedOperands
def decodedWords (item:Option (Sigma fun owner:Nat=> Gate n owner)):Nat:=
  match item with
  | none=> 0
  | some ⟨_,gate⟩ => 6+2*gate.children.length+2*gate.guardLabels.length
def sourceWords (n:Nat) (rows:List Row):Nat:= ((sourceItems n rows).map fun item=> 1+decodedWords item).sum
end Cost.ForestWeightedIndexed ctx "Physical.Controller" namespace Physical
structure PrimaryInput (n b:ℕ) where
  (positiveBuses:0 < b) (enable:Assignment n) (request:Fin b→ Assignment n)
def PrimaryInput.firstBus {n b:ℕ} (input:PrimaryInput n b):Fin b:= ⟨0,input.positiveBuses⟩
def anyTrue {n:ℕ} (a:Assignment n):Bool:=decide (∃ i,a i=true)
def stageTerms {n:ℕ} (active request:Assignment n):Assignment n:=fun i=> active i && request i
def stageFlag {n:ℕ} (active request:Assignment n):Bool:=anyTrue (stageTerms active request)
def stageMask {n:ℕ} (flag:Bool) (terms:Assignment n):Assignment n:=fun i=> flag ^^ !(terms i)
def nextActive {n:ℕ} (active request:Assignment n) (flag:Bool):Assignment n:=fun i=> active i && stageMask flag (stageTerms active request) i
structure SelectorRun (n b:ℕ) where
  (flags:Fin b→ Bool) (activeBefore:Fin b→ Assignment n) (terms:Fin b→ Assignment n) (masks:Fin b→ Assignment n) (finalActive:Assignment n)
def runMasks {n:ℕ}: (b:ℕ)→ Assignment n→ (Fin b→ Assignment n)→
    Option Bool→ SelectorRun n b
  | 0,active,_,_=>
      { flags:=Fin.elim0
        activeBefore:=Fin.elim0
        terms:=Fin.elim0
        masks:=Fin.elim0
        finalActive:=active}
  | b+1,active,request,override=>
      let flag:=override.getD (stageFlag active (request 0))
      let rest:=runMasks b (nextActive active (request 0) flag)
        (fun j=> request j.succ) none
      { flags:=Fin.cases flag rest.flags
        activeBefore:=Fin.cases active rest.activeBefore
        terms:=Fin.cases (stageTerms active (request 0)) rest.terms
        masks:=Fin.cases (stageMask flag (stageTerms active (request 0))) rest.masks
        finalActive:=rest.finalActive}
def qualifiers {n b:ℕ} (enable:Assignment n) (request:Fin b→ Assignment n) (flags:Fin b→ Bool):Assignment n:=fun i=> enable i && decide (∀ j,flags j=true→ request j i=true)
def healthyRun {n b:ℕ} (input:PrimaryInput n b):SelectorRun n b:=runMasks b input.enable input.request none
def runFromFirst {n b:ℕ} (input:PrimaryInput n b) (f0:Bool):SelectorRun n b:=runMasks b input.enable input.request (some f0)
def healthyQualifiers {n b:ℕ} (input:PrimaryInput n b):Assignment n:=qualifiers input.enable input.request (healthyRun input).flags
def qualifiersFromFirst {n b:ℕ} (input:PrimaryInput n b) (f0:Bool):Assignment n:=qualifiers input.enable input.request (runFromFirst input f0).flags
def ObservationsDiffer {n q:ℕ} (outputs:Fin q→ Assignment n→ Bool) (healthy faulty:Assignment n):Prop:= ∃ k,outputs k healthy ≠ outputs k faulty
end Physical ctx "Physical.Faults" namespace Physical
structure Bridge (n:ℕ) where
  (target:Channel n) (drivers:Finset (Channel n)) (drivers_nonempty:drivers.Nonempty) (target_not_mem:target ∉ drivers)
def Bridge.remaining {n:ℕ} (bridge:Bridge n):Finset (Channel n):=Finset.univ \ insert bridge.target bridge.drivers
def firstTerms {n b:ℕ} (input:PrimaryInput n b):Assignment n:=stageTerms input.enable (input.request input.firstBus)
def bridgeU {n b:ℕ} (bridge:Bridge n) (input:PrimaryInput n b):Bool:= !(firstTerms input bridge.target)
def bridgeD {n b:ℕ} (bridge:Bridge n) (input:PrimaryInput n b):Bool:=decide (∀ i ∈ bridge.drivers,firstTerms input i=false)
def bridgeR {n b:ℕ} (bridge:Bridge n) (input:PrimaryInput n b):Bool:=decide (∀ i ∈ bridge.remaining,firstTerms input i=false)
def BridgeInterfaceSatisfied {n b:ℕ} (bridge:Bridge n) (input:PrimaryInput n b) (drive wire:Bool):Prop:=bridgeU bridge input= !drive∧ bridgeD bridge input=drive∧ wire=drive
def bridgeFirstFlag {n b:ℕ} (bridge:Bridge n) (input:PrimaryInput n b) (wire:Bool):Bool:= !(wire && bridgeD bridge input && bridgeR bridge input)
def bridgeQualifiers {n b:ℕ} (bridge:Bridge n) (input:PrimaryInput n b) (wire:Bool):Assignment n:=qualifiersFromFirst input (bridgeFirstFlag bridge input wire)
def BridgeInputDetects {n b q:ℕ} (bridge:Bridge n) (drive:Bool) (outputs:Fin q→ Assignment n→ Bool) (input:PrimaryInput n b) (wire:Bool):Prop:=BridgeInterfaceSatisfied bridge input drive wire∧ ObservationsDiffer outputs (healthyQualifiers input) (bridgeQualifiers bridge input wire)
def BridgeDetectable {n b q:ℕ} (bridge:Bridge n) (drive:Bool) (outputs:Fin q→ Assignment n→ Bool):Prop:= ∃ input:PrimaryInput n b, ∃ wire,BridgeInputDetects bridge drive outputs input wire
end Physical ctx "Physical.Realize" namespace Physical
def realizeTailRequests {n:ℕ} (target:Channel n) (K:Finset (Channel n)):
    (b:ℕ)→ Fin b→ Assignment n
  | 0=> Fin.elim0
  | _+1=> Fin.cases (if target ∈ K then (fun _=> false) else assignmentOfSet K)
      (fun _ _=> false)
def realizeRequests {n:ℕ} (target:Channel n) (K:Finset (Channel n)):
    (b:ℕ)→ Fin b→ Assignment n
  | 0=> Fin.elim0
  | b+1=> Fin.cases (assignmentOfSet {target}) (realizeTailRequests target K b)
def realizeBridge {n b:ℕ} (bridge:Bridge n) (hb:0 < b) (K:Finset (Channel n)):PrimaryInput n b where
  positiveBuses:=hb;enable:=assignmentOfSet (insert bridge.target K);request:=realizeRequests bridge.target K b
end Physical ctx "Physical.DetectCorrect" namespace Decoder.DAG
def observations (g0:Decoder.DAG n):Fin g0.roots.length→ Assignment n→ Bool:=fun index assignment=> g0.eval assignment (g0.roots.get index)
end Decoder.DAG ctx "Cost.Forest" namespace Cost.Forest
open Decoder Decoder.DAG
@[reducible] def rootFamily (g0:DAG n) (positions:List (Fin g0.roots.length)):DAG n:= ⟨g0.nodeCount,g0.node,positions.map g0.roots.get⟩
theorem rootFamily_guarded (g0:DAG n) (guarded:g0.Guarded) (positions:List (Fin g0.roots.length)): (rootFamily g0 positions).Guarded:=guarded
private theorem rootFamily_cone (g0:DAG n) (positions:List (Fin g0.roots.length)) (owner:Fin g0.nodeCount): (rootFamily g0 positions).cone owner=g0.cone owner:=by
  have sameCone: ∀ rank:Nat, ∀ index:Fin g0.nodeCount,index.val=rank→
      (rootFamily g0 positions).cone index=g0.cone index:=by
    intro rank
    induction rank using Nat.strong_induction_on with
    | h rank ih=>
      intro index rankEq
      rw [DAG.cone_eq (rootFamily g0 positions) index,DAG.cone_eq g0 index]
      apply congrArg (fun set:Finset (Fin g0.nodeCount)=> insert index set)
      apply Finset.biUnion_congr (by rfl)
      intro child member
      have earlier:child.val < rank:=by rw [← rankEq];exact child.isLt
      exact ih child.val earlier (g0.childIndex index child) rfl
  exact sameCone owner.val owner rfl
theorem rootFamily_cones_subset (g0:DAG n) (positions:List (Fin g0.roots.length)): (rootFamily g0 positions).cones (rootFamily g0 positions).roots ⊆ g0.cones g0.roots:=by { intro owner hp0;obtain ⟨root,member,coneMember⟩ :=Finset.mem_biUnion.mp hp0;change root ∈ (positions.map g0.roots.get).toFinset at member;have listMember:=List.mem_toFinset.mp member;obtain ⟨position,positionMember,same⟩ :=List.mem_map.mp listMember;have coneEq:=rootFamily_cone g0 positions (root:Fin g0.nodeCount);have originalMember:owner ∈ g0.cone root:=by { exact coneEq ▸ coneMember};subst root;exact Finset.mem_biUnion.mpr ⟨g0.roots.get position,List.mem_toFinset.mpr (List.get_mem _ _),originalMember⟩ }
def rootFamilyUse (g0:DAG n) (positions:List (Fin g0.roots.length)) (owner:Fin g0.nodeCount): (rootFamily g0 positions).ActiveUses ((rootFamily g0 positions).cones (rootFamily g0 positions).roots) owner→ g0.ActiveUses (g0.cones g0.roots) owner:=by
  intro use
  rcases use with ⟨occurrence,retained,same⟩
  cases occurrence with
  | inl position=>
    let source:Fin positions.length:= ⟨position.val,by simpa [rootFamily] using position.isLt⟩
    refine ⟨.inl (positions.get source),trivial, ?_⟩
    simpa only [DAG.refers,rootFamily,List.get_eq_getElem,List.getElem_map] using same
  | inr child=>
    refine ⟨.inr child,rootFamily_cones_subset g0 positions retained, ?_⟩
    exact same
theorem rootFamilyUse_injective (g0:DAG n) (positions:List (Fin g0.roots.length)) (unique:positions.Nodup) (owner:Fin g0.nodeCount):Function.Injective (rootFamilyUse g0 positions owner):=by compact_proof { intro f0 s0 same;apply Subtype.ext;have actual:=congrArg Subtype.val same;cases f0 with | mk f0 validFirst=> { cases s0 with | mk s0 validSecond=> { rcases validFirst with ⟨retainedFirst,refersFirst⟩;rcases validSecond with ⟨retainedSecond,refersSecond⟩;cases f0 <;> cases s0 <;> simp only [rootFamilyUse] at actual; · { apply congrArg Sum.inl;apply Fin.ext;have equality:=Sum.inl.inj actual;have positionsEqual:=unique.get_inj_iff.mp equality;exact congrArg (fun index:Fin positions.length=> index.val) positionsEqual}; · { cases actual}; · { cases actual}; · { exact congrArg Sum.inr (Sum.inr.inj actual)}}}}
theorem rootFamily_forest (g0:DAG n) (fr0:g0.FormulaForest) (positions:List (Fin g0.roots.length)) (unique:positions.Nodup): (rootFamily g0 positions).FormulaForest:=by { refine ⟨rootFamily_guarded g0 fr0.1 positions, ?_⟩;intro owner internal;exact (Nat.card_le_card_of_injective _ (rootFamilyUse_injective g0 positions unique owner)).trans (fr0.2 owner internal)}
end Cost.Forest
namespace Cost.Forest
open Decoder Decoder.DAG Cost.ForestIndexedOperands
theorem rootFamily_rows (g0:DAG n) (positions:List (Fin g0.roots.length)) (rows:List Row) (matched:RowsMatch g0 rows):RowsMatch (rootFamily g0 positions) rows:=by { refine ⟨matched.length_eq, ?_⟩;intro index;exact matched.node index}
def familyRootIds (g0:DAG n) (positions:List (Fin g0.roots.length)):List Nat:=positions.map (fun position=> (g0.roots.get position).val)
def healthyPositions (g0:DAG n) (target:Channel n) (healthy:Bool):List (Fin g0.roots.length):=
  (List.finRange g0.roots.length).filter
    (fun position=> g0.eval (assignmentOfSet {target}) (g0.roots.get position)==healthy)
end Cost.Forest
namespace Cost.Forest
open Decoder Decoder.DAG
theorem healthyPositions_nodup (g0:DAG n) (target:Channel n) (healthy:Bool): (healthyPositions g0 target healthy).Nodup:= (List.nodup_finRange _).filter _
theorem healthyPositions_length_le (g0:DAG n) (target:Channel n) (healthy:Bool): (healthyPositions g0 target healthy).length≤ g0.roots.length:=by { simpa only [healthyPositions,List.length_finRange] using List.length_filter_le (fun position=> g0.eval (assignmentOfSet { target}) (g0.roots.get position)==healthy) (List.finRange g0.roots.length)}
end Cost.Forest ctx "Cost.ForestRootProjection" namespace Cost.ForestRootProjection
open Cost.ForestCursorDescriptors
open Cost Decoder Decoder.DAG
open Cost.ForestWeightedIndexed Cost.ForestWeightedTagged
open Cost.ForestIndexedOperands
variable {width n:Nat} {W:Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]
noncomputable def mixedResident: {width n:ℕ}→ {W:Type}→ [AddCommGroup.{0} W]→ [LinearOrder.{0} W]→ Cost.Program width 8→ (positiveGraph negativeGraph:Decoder.DAG n)→ (rows:List.{0} Cost.ForestIndexedOperands.Row)→ List.{0} ℕ→ List.{0} ℕ→ Cost.ForestIndexedOperands.RowsMatch negativeGraph rows→ (Channel n→ W)→ ℕ→ Channel n→ LT.lt.{0} (Cost.ForestCursorDescriptors.buildRoots positiveGraph).count (HPow.hPow.{0,0,0} 2 width)→ (∀ (entry:Cost.ForestCursorDescriptors.ParentEntry),Membership.mem.{0,0} (Cost.ForestCursorDescriptors.buildRoots positiveGraph).entries entry→ LT.lt.{0} entry.position (HPow.hPow.{0,0,0} 2 width))→ Cost.Program width 8:=by { sorry}
end Cost.ForestRootProjection
namespace Cost.ForestRootProjection
open Cost
variable {width:Nat}
noncomputable def packetPrelude: {width:ℕ}→ Cost.Program width 8→ Cost.Program width 8:=by { sorry}
end Cost.ForestRootProjection
namespace Cost.ForestRootProjection
open Controller Cost Decoder Decoder.DAG
open Cost.ForestIndexedOperands
variable {width n:Nat}
noncomputable def classificationPrior: {n:ℕ}→ (width:ℕ)→ Decoder.DAG n→ List.{0} Cost.ForestIndexedOperands.Row→ List.{0} ℕ→ (Channel n→ Bool)→ Cost.Program width 8:=by { sorry}
end Cost.ForestRootProjection
namespace Cost.ForestRootProjection
open Cost.ForestCursorDescriptors
open Controller Cost Decoder Decoder.DAG
open Cost.ForestWeightedIndexed Cost.ForestWeightedTagged
open Cost.ForestIndexedOperands
variable {width n:Nat} {W:Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]
def classificationInitial (width:Nat) (g0:DAG n) (rows:List Row) (roots:List Nat) (assignment:Channel n→ Bool) (target:Channel n) (rest output:List (Word width)) (address loaded temporary:Word width) (saved:Fin 8→ Word width):Cost.State width 8:=RegisterWiden.widenState ((ForestCounter.counterState (#[]:Array (Word width)) 0 address loaded temporary).frame ((inputPacket n 0 rows roots).map (word width)++List.ofFn (fun channel=> boolWord width (assignment channel))++ (word width target.val::rest)) output) saved
end Cost.ForestRootProjection
namespace Cost.ForestRootProjection
open Cost Decoder Decoder.DAG
open Cost.ForestCursorTraversal Cost.ForestCursorDescriptors
variable {n:Nat}
def DownBound (limit:Nat):CursorOp n→ Prop | .down _ position _=> position < limit | _=> True
theorem node_children_le_incidence (g0:DAG n) (node:Fin g0.nodeCount): (g0.node node).children.length≤ g0.childIncidences:=by { rw [DAG.childIncidences,List.sum_ofFn];exact Finset.single_le_sum (f:=fun index:Fin g0.nodeCount=> (g0.node index).children.length) (fun index _=> Nat.zero_le _) (Finset.mem_univ node)}
theorem cursor_down_bound (g0:DAG n) (node:Fin g0.nodeCount) (route:LeafRoute): ∀ operation ∈ cursorOps g0 node route,DownBound g0.childIncidences operation:=by compact_proof { have claim: ∀ rank:Nat, ∀ owner:Fin g0.nodeCount,owner.val=rank→ ∀ route:LeafRoute, ∀ operation ∈ cursorOps g0 owner route,DownBound g0.childIncidences operation:=by { intro rank;induction rank using Nat.strong_induction_on with | h rank ih=> { intro owner rankEq route;rw [cursorOps];intro operation member;rcases List.mem_cons.mp member with rfl | member; · { trivial};cases nodeEq:g0.node owner with | zero=> { simp only [nodeEq,List.not_mem_nil] at member} | input head=> { simp only [nodeEq,List.mem_singleton] at member;subst operation;trivial} | liveAnd f0 s0=> { simp only [nodeEq,List.not_mem_nil] at member} | disj refs=> { simp only [nodeEq] at member;obtain ⟨position,_,occurrence⟩ :=List.mem_flatMap.mp member;simp only [List.singleton_append,List.mem_cons,List.mem_append,List.mem_singleton,List.not_mem_nil,or_false,or_assoc] at occurrence;rcases occurrence with rfl | childMember | rfl; · { have lengthBound:=node_children_le_incidence g0 owner;simp only [nodeEq,Gate.children] at lengthBound;exact position.isLt.trans_le lengthBound}; · { exact ih (g0.childIndex owner (refs.get position)).val (by { have earlier:=g0.childIndex_lt owner (refs.get position);omega}) (g0.childIndex owner (refs.get position)) rfl _ operation childMember}; · { trivial}} | guard child labels=> { simp only [nodeEq,List.mem_append,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false,or_assoc] at member;rcases member with entered | rfl | childMember | rfl | exited; · { obtain ⟨position,_,same⟩ :=List.mem_map.mp entered;subst operation;trivial}; · { have lengthBound:=node_children_le_incidence g0 owner;simp only [nodeEq,Gate.children,List.length_cons,List.length_nil] at lengthBound;change 0 < g0.childIncidences;omega}; · { exact ih (g0.childIndex owner child).val (by { have earlier:=g0.childIndex_lt owner child;omega}) (g0.childIndex owner child) rfl _ operation childMember}; · { trivial}; · { obtain ⟨position,_,same⟩ :=List.mem_map.mp exited;subst operation;trivial}}}};exact claim node.val node rfl route}
def PositionsBound (limit:Nat) (builder:Builder):Prop:= ∀ entry ∈ builder.entries,entry.position < limit
theorem descriptor_step_positions (limit root:Nat) (builder:Builder) (bounded:PositionsBound limit builder) (operation:CursorOp n) (source:DownBound limit operation):PositionsBound limit (ForestCursorDescriptors.step root builder operation):=by compact_proof { cases operation with | down owner position child=> { intro entry member;rcases List.mem_cons.mp member with rfl | old; · { exact source}; · { exact bounded entry old}} | node owner=> { exact bounded} | up=> { exact bounded} | enter owner position channel=> { exact bounded} | leave owner position channel=> { exact bounded} | leaf owner route head=> { exact bounded}}
theorem descriptor_scan_positions (limit root:Nat) (builder:Builder) (bounded:PositionsBound limit builder) (operations:List (CursorOp n)) (source: ∀ operation ∈ operations,DownBound limit operation):PositionsBound limit (scan root builder operations):=by { induction operations generalizing builder with | nil=> { exact bounded} | cons operation rest ih=> { exact ih (ForestCursorDescriptors.step root builder operation) (descriptor_step_positions limit root builder bounded operation (source operation List.mem_cons_self)) (fun later member=> source later (List.mem_cons_of_mem operation member))}}
theorem descriptor_roots_positions (g0:DAG n) (builder:Builder) (bounded:PositionsBound g0.childIncidences builder) (positions:List (Fin g0.roots.length)):PositionsBound g0.childIncidences (scanRoots g0 builder positions):=by { induction positions generalizing builder with | nil=> { exact bounded} | cons position rest ih=> { apply ih;exact descriptor_scan_positions g0.childIncidences position.val (beginRoot builder) bounded (cursorOps g0 (g0.roots.get position) []) (cursor_down_bound g0 _ [])}}
theorem buildRoots_position_bound (g0:DAG n): ∀ entry ∈ (buildRoots g0).entries,entry.position < g0.childIncidences:=by { exact descriptor_roots_positions g0 initial (by { intro entry member;cases member}) _}
end Cost.ForestRootProjection
namespace Cost.ForestRootProjection
open Controller Cost Decoder Decoder.DAG
open Cost.ForestCursorDescriptors Cost.ForestIndexedOperands
open Cost.ForestWeightedIndexed Cost.ForestWeightedTagged
variable {width n:Nat} {W:Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]
def healthyGraph (g0:DAG n) (target:Channel n) (healthy:Bool):DAG n:=Forest.rootFamily g0 (Forest.healthyPositions g0 target healthy)
def healthyRootIds (g0:DAG n) (target:Channel n) (healthy:Bool):List Nat:=Forest.familyRootIds g0 (Forest.healthyPositions g0 target healthy)
end Cost.ForestRootProjection
namespace Cost.ForestRootProjection
open Cost Decoder Decoder.DAG
open Cost.ForestCursorDescriptors Cost.ForestIndexedOperands
variable {n:Nat}
theorem healthy_geometry (g0:DAG n) (target:Channel n) (healthy:Bool): (healthyGraph g0 target healthy).nodeCount=g0.nodeCount∧ (healthyGraph g0 target healthy).childIncidences=g0.childIncidences∧ (healthyGraph g0 target healthy).guardIncidences=g0.guardIncidences∧ (healthyGraph g0 target healthy).roots.length= (Forest.healthyPositions g0 target healthy).length∧ (healthyRootIds g0 target healthy).length= (Forest.healthyPositions g0 target healthy).length:=by { exact ⟨rfl,rfl,rfl,by { simp only [healthyGraph,Forest.rootFamily,List.length_map]},by { simp only [healthyRootIds,Forest.familyRootIds,List.length_map]}⟩ }
theorem actual_descriptor_count_bound (g0:DAG n) (fr0:g0.FormulaForest): (buildRoots g0).count≤ 4* (g0.roots.length+g0.childIncidences)+2*g0.guardIncidences:=by { have count:=ForestCursorWholeProgram.descriptor_count_le_operations g0;rw [ForestCursorWholeProgram.rootOperations_total] at count;exact count.trans (ForestCursorCharging.all_root_budget_bound g0 fr0)}
end Cost.ForestRootProjection
namespace Cost.ForestRootProjection
open Controller Cost Decoder Decoder.DAG
open Cost.ForestCursorDescriptors Cost.ForestIndexedOperands
open Cost.ForestWeightedIndexed Cost.ForestWeightedTagged
variable {n:Nat} {W:Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]
def forestSize (g0:DAG n):Nat:=n+g0.nodeCount+g0.roots.length+g0.childIncidences+g0.guardIncidences
def chosenMixedWidth (g0:DAG n):Nat:=Nat.log 2 (10000* (forestSize g0+1))+1
theorem chosenMixedCapacity (g0:DAG n):10000* (forestSize g0+1) < 2 ^ chosenMixedWidth g0:=Nat.lt_pow_succ_log_self (by { decide}:1 < 2) _
theorem original_descriptor_capacity (g0:DAG n) (fr0:g0.FormulaForest) (target:Channel n): (buildRoots (healthyGraph g0 target false)).count < 2 ^ chosenMixedWidth g0∧ ∀ entry ∈ (buildRoots (healthyGraph g0 target false)).entries,entry.position < 2 ^ chosenMixedWidth g0:=by compact_proof { have cap:=chosenMixedCapacity g0;have geometry:=healthy_geometry g0 target false;have positiveForest:=Forest.rootFamily_forest g0 fr0 (Forest.healthyPositions g0 target false) (Forest.healthyPositions_nodup g0 target false);have count:=actual_descriptor_count_bound (healthyGraph g0 target false) positiveForest;have rootCount:=Forest.healthyPositions_length_le g0 target false;simp only [geometry.2.1,geometry.2.2.1,geometry.2.2.2.1] at count;unfold forestSize at cap;constructor; · { omega}; · { intro entry member;have bound:=buildRoots_position_bound (healthyGraph g0 target false) entry member;rw [geometry.2.1] at bound;omega}}
end Cost.ForestRootProjection ctx "Cost.ForestOriginalSemantics" namespace Cost.ForestOriginalSemantics
open Controller Decoder Decoder.DAG Cost
open Cost.ForestRootProjection Cost.ForestIndexedOperands
open Cost.ForestWeightedIndexed Cost.ForestWeightedTagged
variable {n:Nat} {W:Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]
/-- original physical execution: Formula-forest execution and maximum weight. -/
theorem original_physical_execution (g0:DAG n) (fr0:g0.FormulaForest) (b:Nat) (bridge:Physical.Bridge n) (hb:0 < b) (rows:List Row) (originalRoots:List Nat) (originalMatched:RowsMatch g0 rows) (heads:UniformDAGSource.HeadsMatch g0 rows originalMatched) (originalRootsMatch:RootsMatch g0 originalRoots) (ws0:Channel n→ W) (nonnegative: ∀ channel,0≤ ws0 channel) (rest output:List (Word (chosenMixedWidth g0))) (address loaded temporary:Word (chosenMixedWidth g0)) (saved:Fin 8→ Word (chosenMixedWidth g0)): ∃ answer:Bool, ∃ final ticks peak storePeak,Execution (mixedResident (packetPrelude (classificationPrior (chosenMixedWidth g0) g0 rows originalRoots (assignmentOfSet {bridge.target}))) (healthyGraph g0 bridge.target false) (healthyGraph g0 bridge.target true) rows (healthyRootIds g0 bridge.target false) (healthyRootIds g0 bridge.target true) (Forest.rootFamily_rows g0 (Forest.healthyPositions g0 bridge.target true) rows originalMatched) ws0 b bridge.target (original_descriptor_capacity g0 fr0 bridge.target).1 (original_descriptor_capacity g0 fr0 bridge.target).2) (classificationInitial (chosenMixedWidth g0) g0 rows originalRoots (assignmentOfSet {bridge.target}) bridge.target rest output address loaded temporary saved) final ticks peak∧ final.halted=true∧ final.reg 4=word (chosenMixedWidth g0) (if answer then 1 else 0)∧ ticks≤ 4721* (n+g0.nodeCount+g0.roots.length+g0.childIncidences+g0.guardIncidences)+450∧ peak≤ 169* (n+g0.nodeCount+g0.roots.length+g0.childIncidences+g0.guardIncidences)+57+rest.length+output.length∧ (runAll (source n rows) ws0 b bridge.target (healthyRootIds g0 bridge.target false)).2.operations≤ 4*forestSize g0∧ (runAll (source n rows) ws0 b bridge.target (healthyRootIds g0 bridge.target false)).2.arithmetic≤ 8*forestSize g0∧ StoreTrace ws0 (runAll (source n rows) ws0 b bridge.target (healthyRootIds g0 bridge.target false)).1 b bridge.target ⟨Array.replicate n 0,0,ForestCursorDescriptors.initial,none,0,n⟩ (runAll (source n rows) ws0 b bridge.target (healthyRootIds g0 bridge.target false)).2 storePeak∧ programWords (mixedResident (packetPrelude (classificationPrior (chosenMixedWidth g0) g0 rows originalRoots (assignmentOfSet {bridge.target}))) (healthyGraph g0 bridge.target false) (healthyGraph g0 bridge.target true) rows (healthyRootIds g0 bridge.target false) (healthyRootIds g0 bridge.target true) (Forest.rootFamily_rows g0 (Forest.healthyPositions g0 bridge.target true) rows originalMatched) ws0 b bridge.target (original_descriptor_capacity g0 fr0 bridge.target).1 (original_descriptor_capacity g0 fr0 bridge.target).2)+peak+ (storePeak+sourceWords n rows+controlBudget (source n rows) g0.nodeCount+ (6*g0.nodeCount+2*g0.childIncidences+2*g0.guardIncidences+2* (healthyGraph g0 bridge.target false).roots.length+5)+6* (healthyGraph g0 bridge.target false).roots.length+7)≤ 3558*forestSize g0+2106+rest.length+output.length∧ (answer=true↔ Physical.BridgeDetectable (b:=b) bridge true g0.observations)∧ (answer=true→ ∃ K:Finset (Channel n),Admissible b bridge.target K∧ Physical.BridgeInputDetects bridge true g0.observations (Physical.realizeBridge bridge hb K) true∧ ∃ previous:List (Word (chosenMixedWidth g0)),final.output=List.ofFn (fun channel:Channel n=> boolWord (chosenMixedWidth g0) (assignmentOfSet K channel))++previous):=by { sorry}
end Cost.ForestOriginalSemantics ctx "Optimization.Weights" namespace Optimization.Weights
open Controller Decoder Decoder.DAG
variable {n:ℕ} {W:Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]
open Cost Cost.ForestIndexedOperands
/-- forest maximum weight: Formula-forest execution and maximum weight. -/
theorem forest_maximum_weight (g0:DAG n) (guarded:g0.Guarded) (fr0:g0.FormulaForest) (rows:List Row) (roots:List Nat) (matched:RowsMatch g0 rows) (rootsMatch:RootsMatch g0 roots) (ws0:Channel n→ W) (nonnegative: ∀ channel,0≤ ws0 channel) (b:ℕ) (target:Channel n) (candidate:ForestWeightedTagged.Candidate W) (selected: (ForestWeightedIndexed.view (ForestWeightedIndexed.runAll (ForestWeightedIndexed.source n rows) ws0 b target roots).2).data.selected=some candidate): (∀ (position:Fin g0.roots.length) (K:Finset (Channel n)),Admissible b target K→ g0.eval (assignmentOfSet K) (g0.roots.get position)=true→ GenericWeight.total ws0 K≤ candidate.score)∧ (ForestWeightedIndexed.runAll (ForestWeightedIndexed.source n rows) ws0 b target roots).2.operations≤ 4* (g0.roots.length+g0.childIncidences)+2*g0.guardIncidences∧ (ForestWeightedIndexed.runAll (ForestWeightedIndexed.source n rows) ws0 b target roots).2.arithmetic≤ n+8* (g0.roots.length+g0.childIncidences)+4*g0.guardIncidences:=by { sorry}
end Optimization.Weights
end Controller

end_ctx
