module
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
@[expose] public section
noncomputable section
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
end
namespace Cost
abbrev Word (width:Nat):=Fin (2 ^ width)
def word (width value:Nat):Word width:= ⟨value % (2 ^ width),Nat.mod_lt _ (Nat.two_pow_pos width)⟩
structure State (width registers:Nat) where
  (reg:Fin registers→ Word width) (heap:Array (Word width)) (stack:List (Word width)) (output:List (Word width)) (pc:Word width) (halted:Bool)
def State.liveWords (s:State width registers):Nat:=registers+s.heap.size+s.stack.length+s.output.length+1
inductive Instruction (width registers:Nat) where
  | constant (dst:Fin registers) (value:Word width) | copy (dst src:Fin registers) | add (dst left right:Fin registers) | xor (dst left right:Fin registers) | load (dst address:Fin registers) | store (address src:Fin registers) | allocate (src:Fin registers) | release | push (src:Fin registers) | pop (dst:Fin registers) | emit (src:Fin registers) | branchZero (src:Fin registers) (target:Word width) | halt
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
      if s.heap.size < 2 ^ width then some { next with heap:=s.heap.push (s.reg src)}
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
end Cost
namespace Decoder
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
def childIndex (graph:DAG n) (parent:Fin graph.nodeCount) (child:Fin parent.val):Fin graph.nodeCount:= ⟨child.val,Nat.lt_trans child.isLt parent.isLt⟩
theorem childIndex_lt (graph:DAG n) (parent:Fin graph.nodeCount) (child:Fin parent.val): (graph.childIndex parent child).val < parent.val:=child.isLt
def Guarded (graph:DAG n):Prop:= ∀ index, (graph.node index).IsGuarded
def childIncidences (graph:DAG n):ℕ:= (List.ofFn fun index:Fin graph.nodeCount=> (graph.node index).children.length).sum
def guardIncidences (graph:DAG n):ℕ:= (List.ofFn fun index:Fin graph.nodeCount=> (graph.node index).guardLabels.length).sum
end DAG
end Decoder
namespace Decoder
namespace DAG
variable {n:ℕ}
def eval (graph:DAG n) (assignment:Assignment n) (index:Fin graph.nodeCount):Bool:=
  (graph.node index).eval assignment (fun child=> graph.eval assignment (graph.childIndex index child))
termination_by index.val
decreasing_by exact graph.childIndex_lt index child
end DAG
end Decoder
namespace Decoder
namespace DAG
variable {n:ℕ}
def cone (graph:DAG n) (root:Fin graph.nodeCount):Finset (Fin graph.nodeCount):=
  insert root ((graph.node root).children.toFinset.biUnion fun child=> graph.cone (graph.childIndex root child))
termination_by root.val
decreasing_by exact graph.childIndex_lt root child
theorem cone_eq (graph:DAG n) (root:Fin graph.nodeCount):graph.cone root=insert root ((graph.node root).children.toFinset.biUnion fun child=> graph.cone (graph.childIndex root child)):=by { rw [cone]}
@[simp] theorem self_mem_cone (graph:DAG n) (root:Fin graph.nodeCount):
    root ∈ graph.cone root:=by { rw [cone_eq];exact Finset.mem_insert_self _ _}
theorem cone_child_subset (graph:DAG n) (parent:Fin graph.nodeCount) (child:Fin parent.val) (membership:child ∈ (graph.node parent).children):graph.cone (graph.childIndex parent child) ⊆ graph.cone parent:=by { intro index indexMembership;rw [cone_eq];exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨child,by { simpa using membership},indexMembership⟩)}
def ChildClosed (graph:DAG n) (nodes:Finset (Fin graph.nodeCount)):Prop:= ∀ parent ∈ nodes, ∀ child ∈ (graph.node parent).children,graph.childIndex parent child ∈ nodes
theorem cone_childClosed (graph:DAG n) (root:Fin graph.nodeCount):graph.ChildClosed (graph.cone root):=by { intro parent parentMembership child childMembership;rw [cone_eq] at parentMembership;rcases Finset.mem_insert.mp parentMembership with equality | membership; · { subst parent;exact graph.cone_child_subset root child childMembership (graph.self_mem_cone (graph.childIndex root child))}; · { obtain ⟨earlier,earlierMembership,parentMembership⟩ :=Finset.mem_biUnion.mp membership;exact graph.cone_child_subset root earlier (by { simpa using earlierMembership}) (graph.cone_childClosed (graph.childIndex root earlier) parent parentMembership child childMembership)}}
termination_by root.val
decreasing_by exact graph.childIndex_lt root earlier
def cones (graph:DAG n) (roots:List (Fin graph.nodeCount)):Finset (Fin graph.nodeCount):=roots.toFinset.biUnion graph.cone
theorem root_mem_cones (graph:DAG n) (roots:List (Fin graph.nodeCount)) (root:Fin graph.nodeCount) (membership:root ∈ roots):root ∈ graph.cones roots:=by { exact Finset.mem_biUnion.mpr ⟨root,by { simpa using membership},graph.self_mem_cone root⟩ }
theorem cones_childClosed (graph:DAG n) (roots:List (Fin graph.nodeCount)):graph.ChildClosed (graph.cones roots):=by { intro parent parentMembership child childMembership;obtain ⟨root,rootMembership,parentMembership⟩ :=Finset.mem_biUnion.mp parentMembership;exact Finset.mem_biUnion.mpr ⟨root,rootMembership,graph.cone_childClosed root parent parentMembership child childMembership⟩ }
end DAG
end Decoder
namespace Cost
def boolWord (width:Nat) (value:Bool):Word width:=word width (if value then 1 else 0)
end Cost
section
def Admissible {n:ℕ} (b:ℕ) (t:Channel n) (K:Finset (Channel n)):Prop:=K.Nonempty∧ (b=1→ t ∈ K)
end
namespace Decoder
namespace Gate
def isInternal:Gate n available→ Bool | .zero | .input _=> false | .disj _ | .guard _ _ | .liveAnd _ _=> true
end Gate
namespace DAG
variable {n:ℕ}
abbrev ParentOccurrence (graph:DAG n):=Σ parent:Fin graph.nodeCount,Fin (graph.node parent).children.length
abbrev StoredOccurrence (graph:DAG n):=Fin graph.roots.length ⊕ graph.ParentOccurrence
instance storedOccurrenceFintype (graph:DAG n):Fintype graph.StoredOccurrence:=by { dsimp [StoredOccurrence,ParentOccurrence];infer_instance}
def refers (graph:DAG n):graph.StoredOccurrence→ Fin graph.nodeCount | .inl rootPosition=> graph.roots.get rootPosition | .inr childPosition=> graph.childIndex childPosition.1 ((graph.node childPosition.1).children.get childPosition.2)
def parentRetained (graph:DAG n) (nodes:Finset (Fin graph.nodeCount)):graph.StoredOccurrence→ Prop | .inl _=> True | .inr childPosition=> childPosition.1 ∈ nodes
abbrev ActiveUses (graph:DAG n) (nodes:Finset (Fin graph.nodeCount)) (node:Fin graph.nodeCount):=
  {occurrence:graph.StoredOccurrence //
    graph.parentRetained nodes occurrence∧ graph.refers occurrence=node}
noncomputable instance activeUsesFintype (graph:DAG n) (nodes:Finset (Fin graph.nodeCount)) (node:Fin graph.nodeCount):Fintype (graph.ActiveUses nodes node):=Fintype.ofFinite _
def FormulaForest (graph:DAG n):Prop:=graph.Guarded∧ ∀ node, (graph.node node).isInternal=true→ Nat.card (graph.ActiveUses (graph.cones graph.roots) node)≤ 1
end DAG
end Decoder
namespace Decoder
variable {n:ℕ}
abbrev GuardCounters (n:ℕ):=Channel n→ ℕ
namespace GenericWeight
variable {W:Type*} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]
def total (weights:Channel n→ W) (K:Finset (Channel n)):W:= ∑ channel ∈ K,weights channel
end GenericWeight
end Decoder
namespace Decoder
variable {n:ℕ}
abbrev LeafRoute:=List ℕ
end Decoder
namespace Cost.ForestCounter
open Decoder
def counterState (heap:Array (Word width)) (cursor:Nat) (address counter increment:Word width):State width 4 where
  reg:=fun register=> if register=0 then address else if register=1 then counter
    else if register=2 then increment else word width 0
  heap:=heap;stack:= [];output:= [];pc:=word width cursor;halted:=false
end Cost.ForestCounter
namespace Cost
def State.frame (s:State width registers) (stack output:List (Word width)):State width registers:= { s with stack:=s.stack++stack,output:=s.output++output}
end Cost
namespace Cost.ForestGuardSchedule
open Decoder Cost.ForestCounter
inductive GuardEvent (n:ℕ) where
  | enter (channel:Channel n) | leave (channel:Channel n)
  deriving DecidableEq,Repr
def walkEvents (graph:DAG n) (index:Fin graph.nodeCount):List (GuardEvent n):=
  match graph.node index with
  | .zero | .input _ | .liveAnd _ _=> []
  | .disj children=> children.flatMap fun child=> walkEvents graph (graph.childIndex index child)
  | .guard child labels=>
      labels.map GuardEvent.enter++walkEvents graph (graph.childIndex index child)++
        labels.reverse.map GuardEvent.leave
termination_by index.val
decreasing_by all_goals exact graph.childIndex_lt _ _
def rootEvents (graph:DAG n):List (GuardEvent n):=graph.roots.flatMap (walkEvents graph)
end Cost.ForestGuardSchedule
namespace Cost.ForestOccurrences
open Decoder
variable {n:ℕ}
theorem active_use_unique (graph:DAG n) (forest:graph.FormulaForest) (node:Fin graph.nodeCount) (internal: (graph.node node).isInternal=true) (first second:graph.ActiveUses (graph.cones graph.roots) node):first=second:=by
  have cardinality:Fintype.card (graph.ActiveUses (graph.cones graph.roots) node)≤ 1:=by simpa only [Nat.card_eq_fintype_card] using forest.2 node internal
  letI:Subsingleton (graph.ActiveUses (graph.cones graph.roots) node):=Fintype.card_le_one_iff_subsingleton.mp cardinality
  exact Subsingleton.elim first second
theorem active_occurrence_unique (graph:DAG n) (forest:graph.FormulaForest) (node:Fin graph.nodeCount) (internal: (graph.node node).isInternal=true) (first second:graph.StoredOccurrence) (firstActive:graph.parentRetained (graph.cones graph.roots) first) (secondActive:graph.parentRetained (graph.cones graph.roots) second) (firstRefers:graph.refers first=node) (secondRefers:graph.refers second=node):first=second:=by { have equal:=active_use_unique graph forest node internal ⟨first,firstActive,firstRefers⟩ ⟨second,secondActive,secondRefers⟩;exact congrArg Subtype.val equal}
theorem parent_internal (graph:DAG n) (parent:Fin graph.nodeCount) (position:Fin (graph.node parent).children.length): (graph.node parent).isInternal=true:=by { have valid:=position.isLt;cases equation:graph.node parent <;> simp_all [Gate.children,Gate.isInternal]}
inductive RootedPath (graph:DAG n):
  Fin graph.nodeCount→ List graph.StoredOccurrence→ Prop where
  | root (position:Fin graph.roots.length):RootedPath graph (graph.roots.get position) [.inl position] | child (parent:Fin graph.nodeCount) (position:Fin (graph.node parent).children.length) (ancestorRoute:List graph.StoredOccurrence) (path:RootedPath graph parent ancestorRoute):RootedPath graph (graph.childIndex parent ((graph.node parent).children.get position)) (.inr ⟨parent,position⟩ ::ancestorRoute)
namespace RootedPath
theorem endpoint_mem_cones {graph:DAG n} {node:Fin graph.nodeCount} {route:List graph.StoredOccurrence} (path:RootedPath graph node route):node ∈ graph.cones graph.roots:=by { induction path with | root position=> { exact graph.root_mem_cones graph.roots _ (List.get_mem _ _)} | child parent position ancestorRoute path ih=> { exact graph.cones_childClosed graph.roots parent ih _ (List.get_mem _ _)}}
theorem nonempty {graph:DAG n} {node:Fin graph.nodeCount} {route:List graph.StoredOccurrence} (path:RootedPath graph node route):route ≠ []:=by { cases path <;> simp}
theorem unique_internal (graph:DAG n) (forest:graph.FormulaForest): ∀ (node:Fin graph.nodeCount) (first second:List graph.StoredOccurrence), (graph.node node).isInternal=true→ RootedPath graph node first→ RootedPath graph node second→ first=second:=by { have claim: ∀ rank:ℕ, ∀ (firstNode secondNode:Fin graph.nodeCount),graph.nodeCount - firstNode.val=rank→ firstNode=secondNode→ ∀ (first second:List graph.StoredOccurrence), (graph.node firstNode).isInternal=true→ RootedPath graph firstNode first→ RootedPath graph secondNode second→ first=second:=by { intro rank;induction rank using Nat.strong_induction_on with | h rank ih=> { intro firstNode secondNode rankEquation endpointEqual first second internal firstPath secondPath;cases firstPath with | root firstPosition=> { cases secondPath with | root secondPosition=> { have positions:=active_occurrence_unique graph forest _ internal (.inl firstPosition) (.inl secondPosition) trivial trivial rfl endpointEqual.symm;have equal:=Sum.inl.inj positions;cases equal;rfl} | child parent position ancestorRoute path=> { have positions:=active_occurrence_unique graph forest _ internal (.inl firstPosition) (.inr ⟨parent,position⟩) trivial (path.endpoint_mem_cones) rfl endpointEqual.symm;cases positions}} | child firstParent firstPosition firstPrefix firstPath=> { cases secondPath with | root secondPosition=> { have positions:=active_occurrence_unique graph forest _ internal (.inr ⟨firstParent,firstPosition⟩) (.inl secondPosition) firstPath.endpoint_mem_cones trivial rfl endpointEqual.symm;cases positions} | child secondParent secondPosition secondPrefix secondPath=> { have positions:=active_occurrence_unique graph forest _ internal (.inr ⟨firstParent,firstPosition⟩) (.inr ⟨secondParent,secondPosition⟩) firstPath.endpoint_mem_cones secondPath.endpoint_mem_cones rfl endpointEqual.symm;have parentEqual:firstParent=secondParent:=congrArg Sigma.fst (Sum.inr.inj positions);subst secondParent;have positionEqual:firstPosition=secondPosition:=by { exact congrArg (fun pair:graph.ParentOccurrence=> pair.2.val) (Sum.inr.inj positions) |> Fin.ext};subst secondPosition;have decrease:graph.nodeCount - firstParent.val < rank:=by { have earlier:=graph.childIndex_lt firstParent ((graph.node firstParent).children.get firstPosition);omega};have prefixes:=ih _ decrease firstParent firstParent rfl rfl firstPrefix secondPrefix (parent_internal graph firstParent firstPosition) firstPath secondPath;exact congrArg (List.cons (.inr ⟨firstParent,firstPosition⟩)) prefixes}}}};intro node first second internal firstPath secondPath;exact claim _ node node rfl rfl first second internal firstPath secondPath}
end RootedPath
end Cost.ForestOccurrences
namespace Cost.ForestGuardCharging
open Decoder Cost.ForestOccurrences
variable {n:ℕ}
abbrev GuardPosition (graph:DAG n):=Σ node:Fin graph.nodeCount,Fin (graph.node node).guardLabels.length
abbrev GuardKey (graph:DAG n):=GuardPosition graph × Bool
instance guardKeyFintype (graph:DAG n):Fintype (GuardKey graph):=by { dsimp [GuardKey,GuardPosition];infer_instance}
structure GuardVisit (graph:DAG n) where
  (node:Fin graph.nodeCount) (route:List graph.StoredOccurrence) (rooted:RootedPath graph node route) (position:Fin (graph.node node).guardLabels.length) (phase:Bool)
theorem guard_internal (graph:DAG n) (node:Fin graph.nodeCount) (position:Fin (graph.node node).guardLabels.length): (graph.node node).isInternal=true:=by { have valid:=position.isLt;cases equation:graph.node node <;> simp_all [Gate.guardLabels,Gate.isInternal]}
def GuardVisit.key {graph:DAG n} (visit:GuardVisit graph):GuardKey graph:= (⟨visit.node,visit.position⟩,visit.phase)
theorem key_injective (graph:DAG n) (forest:graph.FormulaForest):Function.Injective (GuardVisit.key (graph:=graph)):=by { intro first second equal;cases first with | mk firstNode firstRoute firstPath firstPosition firstPhase=> { cases second with | mk secondNode secondRoute secondPath secondPosition secondPhase=> { have nodes:firstNode=secondNode:=congrArg (fun key:GuardKey graph=> key.1.1) equal;subst secondNode;have positions:firstPosition=secondPosition:=Fin.ext (congrArg (fun key:GuardKey graph=> key.1.2.val) equal);subst secondPosition;have phases:firstPhase=secondPhase:=congrArg (fun key:GuardKey graph=> key.2) equal;subst secondPhase;have routes:=RootedPath.unique_internal graph forest firstNode firstRoute secondRoute (guard_internal graph firstNode firstPosition) firstPath secondPath;subst secondRoute;rfl}}}
theorem key_card (graph:DAG n):Nat.card (GuardKey graph)=2*graph.guardIncidences:=by { simp only [GuardKey,GuardPosition,Nat.card_prod,Nat.card_sigma,Nat.card_fin,Nat.card_eq_fintype_card,Fintype.card_bool];simp [DAG.guardIncidences,List.sum_ofFn,Nat.mul_comm]}
theorem visit_card_le (graph:DAG n) (forest:graph.FormulaForest):Nat.card (GuardVisit graph)≤ 2*graph.guardIncidences:=by { have bounded:=Nat.card_le_card_of_injective (GuardVisit.key (graph:=graph)) (key_injective graph forest);exact bounded.trans_eq (key_card graph)}
end Cost.ForestGuardCharging
namespace Cost.ForestGuardVisits
open Decoder Cost.ForestOccurrences
open Cost.ForestGuardCharging Cost.ForestGuardSchedule
variable {n:ℕ}
def ownVisits (graph:DAG n) (node:Fin graph.nodeCount) (route:List graph.StoredOccurrence) (rooted:RootedPath graph node route) (phase:Bool):List (GuardVisit graph):=List.ofFn fun position:Fin (graph.node node).guardLabels.length=> ⟨node,route,rooted,position,phase⟩
theorem own_route (graph:DAG n) (node:Fin graph.nodeCount) (route:List graph.StoredOccurrence) (rooted:RootedPath graph node route) (phase:Bool) (visit:GuardVisit graph) (present:visit ∈ ownVisits graph node route rooted phase):visit.route=route:=by { obtain ⟨position,equal⟩ :=List.mem_ofFn.mp present;cases equal;rfl}
theorem own_phase (graph:DAG n) (node:Fin graph.nodeCount) (route:List graph.StoredOccurrence) (rooted:RootedPath graph node route) (phase:Bool) (visit:GuardVisit graph) (present:visit ∈ ownVisits graph node route rooted phase):visit.phase=phase:=by { obtain ⟨position,equal⟩ :=List.mem_ofFn.mp present;cases equal;rfl}
theorem own_nodup (graph:DAG n) (node:Fin graph.nodeCount) (route:List graph.StoredOccurrence) (rooted:RootedPath graph node route) (phase:Bool): (ownVisits graph node route rooted phase).Nodup:=by { apply List.nodup_ofFn_ofInjective;intro first second equal;exact Fin.ext (congrArg (fun visit:GuardVisit graph=> visit.position.val) equal)}
def walkGhost (graph:DAG n) (node:Fin graph.nodeCount) (route:List graph.StoredOccurrence) (rooted:RootedPath graph node route):List (GuardVisit graph):=
  ownVisits graph node route rooted false++
    (List.ofFn fun position:Fin (graph.node node).children.length=>
      walkGhost graph (graph.childIndex node ((graph.node node).children.get position))
        (.inr ⟨node,position⟩ ::route) (RootedPath.child node position route rooted)).flatten++
    (ownVisits graph node route rooted true).reverse
termination_by node.val
decreasing_by all_goals exact graph.childIndex_lt _ _
theorem route_suffix (graph:DAG n): ∀ (node:Fin graph.nodeCount) (route:List graph.StoredOccurrence) (rooted:RootedPath graph node route) (visit:GuardVisit graph),visit ∈ walkGhost graph node route rooted→ route <:+visit.route:=by { have claim: ∀ rank:ℕ, ∀ (node:Fin graph.nodeCount),node.val=rank→ ∀ (route:List graph.StoredOccurrence) (rooted:RootedPath graph node route) (visit:GuardVisit graph),visit ∈ walkGhost graph node route rooted→ route <:+visit.route:=by { intro rank;induction rank using Nat.strong_induction_on with | h rank ih=> { intro node value route rooted visit present;rw [walkGhost.eq_def] at present;rcases List.mem_append.mp present with before | after; · { rcases List.mem_append.mp before with own | descendants; · { rw [own_route graph node route rooted false visit own]}; · { obtain ⟨block,blockPresent,visitPresent⟩ :=List.mem_flatten.mp descendants;obtain ⟨position,equal⟩ :=List.mem_ofFn.mp blockPresent;subst block;have suffix:=ih ((graph.node node).children.get position).val (by { have earlier:=graph.childIndex_lt node ((graph.node node).children.get position);omega}) _ rfl _ _ visit visitPresent;exact (List.suffix_cons _ route).trans suffix}}; · { have own:=List.mem_reverse.mp after;rw [own_route graph node route rooted true visit own]}}};intro node route rooted visit present;exact claim node.val node rfl route rooted visit present}
theorem equal_length_suffix {first second whole:List α} (firstSuffix:first <:+whole) (secondSuffix:second <:+whole) (lengths:first.length=second.length):first=second:=by { exact (List.suffix_of_suffix_length_le firstSuffix secondSuffix lengths.le).eq_of_length lengths}
def childrenGhost (graph:DAG n) (node:Fin graph.nodeCount) (route:List graph.StoredOccurrence) (rooted:RootedPath graph node route):List (GuardVisit graph):= (List.ofFn fun position:Fin (graph.node node).children.length=> walkGhost graph (graph.childIndex node ((graph.node node).children.get position)) (.inr ⟨node,position⟩ ::route) (RootedPath.child node position route rooted)).flatten
theorem own_children_disjoint (graph:DAG n) (node:Fin graph.nodeCount) (route:List graph.StoredOccurrence) (rooted:RootedPath graph node route) (phase:Bool):List.Disjoint (ownVisits graph node route rooted phase) (childrenGhost graph node route rooted):=by { apply List.disjoint_left.mpr;intro visit ownPresent descendants;have ownRoute:=own_route graph node route rooted phase visit ownPresent;obtain ⟨block,blockPresent,visitPresent⟩ :=List.mem_flatten.mp descendants;obtain ⟨position,equal⟩ :=List.mem_ofFn.mp blockPresent;subst block;have suffix:=route_suffix graph _ _ _ visit visitPresent;have lengths:=suffix.length_le;rw [ownRoute] at lengths;simp only [List.length_cons] at lengths;omega}
theorem child_blocks_disjoint (graph:DAG n) (node:Fin graph.nodeCount) (route:List graph.StoredOccurrence) (rooted:RootedPath graph node route) (first second:Fin (graph.node node).children.length) (different:first ≠ second):List.Disjoint (walkGhost graph (graph.childIndex node ((graph.node node).children.get first)) (.inr ⟨node,first⟩ ::route) (RootedPath.child node first route rooted)) (walkGhost graph (graph.childIndex node ((graph.node node).children.get second)) (.inr ⟨node,second⟩ ::route) (RootedPath.child node second route rooted)):=by
  apply List.disjoint_left.mpr
  intro visit firstPresent secondPresent
  have firstSuffix:=route_suffix graph _ _ _ visit firstPresent
  have secondSuffix:=route_suffix graph _ _ _ visit secondPresent
  have routes:=equal_length_suffix firstSuffix secondSuffix rfl
  have heads:= (List.cons.inj routes).1
  have positions:first=second:=Fin.ext
    (congrArg (fun occurrence:graph.StoredOccurrence=> match occurrence with | .inl _=> 0 | .inr pair=> pair.2.val) heads)
  exact different positions
theorem walk_nodup (graph:DAG n): ∀ (node:Fin graph.nodeCount) (route:List graph.StoredOccurrence) (rooted:RootedPath graph node route), (walkGhost graph node route rooted).Nodup:=by { classical{ have claim: ∀ rank:ℕ, ∀ (node:Fin graph.nodeCount),node.val=rank→ ∀ (route:List graph.StoredOccurrence) (rooted:RootedPath graph node route), (walkGhost graph node route rooted).Nodup:=by { intro rank;induction rank using Nat.strong_induction_on with | h rank ih=> { intro node value route rooted;have childrenNodup: (childrenGhost graph node route rooted).Nodup:=by { apply List.nodup_flatten.mpr;constructor; · { intro block blockPresent;obtain ⟨position,equal⟩ :=List.mem_ofFn.mp blockPresent;subst block;exact ih ((graph.node node).children.get position).val (by { have earlier:=graph.childIndex_lt node ((graph.node node).children.get position);omega}) _ rfl _ _}; · { apply List.pairwise_ofFn.mpr;intro first second before;exact child_blocks_disjoint graph node route rooted first second (ne_of_lt before)}};have beginningNodup:=List.nodup_append'.mpr ⟨own_nodup graph node route rooted false,childrenNodup,own_children_disjoint graph node route rooted false⟩;have endsNodup: ((ownVisits graph node route rooted true).reverse).Nodup:=List.nodup_reverse.mpr (own_nodup graph node route rooted true);have disjoint:List.Disjoint (ownVisits graph node route rooted false++childrenGhost graph node route rooted) (ownVisits graph node route rooted true).reverse:=by { apply List.disjoint_left.mpr;intro visit present endPresent;have endOwn:=List.mem_reverse.mp endPresent;rcases List.mem_append.mp present with own | descendant; · { have firstPhase:=own_phase graph node route rooted false visit own;have secondPhase:=own_phase graph node route rooted true visit endOwn;simp_all}; · { exact List.disjoint_left.mp (own_children_disjoint graph node route rooted true) endOwn descendant}};have joined:=List.nodup_append'.mpr ⟨beginningNodup,endsNodup,disjoint⟩;rw [walkGhost.eq_def];exact joined}};intro node route rooted;exact claim node.val node rfl route rooted}}
def rootGhost (graph:DAG n):List (GuardVisit graph):= (List.ofFn fun position:Fin graph.roots.length=> walkGhost graph (graph.roots.get position) [.inl position] (RootedPath.root position)).flatten
theorem root_nodup (graph:DAG n): (rootGhost graph).Nodup:=by { classical{ apply List.nodup_flatten.mpr;constructor; · { intro block present;obtain ⟨position,equal⟩ :=List.mem_ofFn.mp present;subst block;exact walk_nodup graph _ _ _}; · { apply List.pairwise_ofFn.mpr;intro first second before;apply List.disjoint_left.mpr;intro visit firstPresent secondPresent;have firstSuffix:=route_suffix graph _ _ _ visit firstPresent;have secondSuffix:=route_suffix graph _ _ _ visit secondPresent;have routes:=equal_length_suffix firstSuffix secondSuffix rfl;have positions:first=second:=Sum.inl.inj (List.cons.inj routes).1;exact (ne_of_lt before) positions}}}
theorem root_length_le (graph:DAG n) (forest:graph.FormulaForest): (rootGhost graph).length≤ 2*graph.guardIncidences:=by
  classical
  letI:Finite (GuardVisit graph):=Finite.of_injective
    (GuardVisit.key (graph:=graph)) (key_injective graph forest)
  letI:Fintype (GuardVisit graph):=Fintype.ofFinite _
  have bound: (rootGhost graph).length≤ Nat.card (GuardVisit graph):=by simpa only [Nat.card_eq_fintype_card] using (root_nodup graph).length_le_card
  exact bound.trans (visit_card_le graph forest)
def event {graph:DAG n} (visit:GuardVisit graph):GuardEvent n:=if visit.phase then .leave ((graph.node visit.node).guardLabels.get visit.position) else .enter ((graph.node visit.node).guardLabels.get visit.position)
theorem own_events (graph:DAG n) (node:Fin graph.nodeCount) (route:List graph.StoredOccurrence) (rooted:RootedPath graph node route) (phase:Bool): (ownVisits graph node route rooted phase).map event=if phase then (graph.node node).guardLabels.map GuardEvent.leave else (graph.node node).guardLabels.map GuardEvent.enter:=by { cases phase with | false=> { rw [ownVisits,List.map_ofFn];exact List.ofFn_getElem_eq_map _ GuardEvent.enter} | true=> { rw [ownVisits,List.map_ofFn];exact List.ofFn_getElem_eq_map _ GuardEvent.leave}}
theorem walk_events (graph:DAG n) (guarded:graph.Guarded): ∀ (node:Fin graph.nodeCount) (route:List graph.StoredOccurrence) (rooted:RootedPath graph node route), (walkGhost graph node route rooted).map event=walkEvents graph node:=by { have claim: ∀ rank:ℕ, ∀ (node:Fin graph.nodeCount),node.val=rank→ ∀ (route:List graph.StoredOccurrence) (rooted:RootedPath graph node route), (walkGhost graph node route rooted).map event=walkEvents graph node:=by { intro rank;induction rank using Nat.strong_induction_on with | h rank ih=> { intro node value route rooted;have descendants: (childrenGhost graph node route rooted).map event= (List.ofFn fun position:Fin (graph.node node).children.length=> walkEvents graph (graph.childIndex node ((graph.node node).children.get position))).flatten:=by { simp only [childrenGhost,List.map_flatten,List.map_ofFn];apply congrArg List.flatten;apply congrArg List.ofFn;funext position;exact ih ((graph.node node).children.get position).val (by { have earlier:=graph.childIndex_lt node ((graph.node node).children.get position);omega}) _ rfl _ _};rw [walkGhost.eq_def];change ((ownVisits graph node route rooted false++childrenGhost graph node route rooted)++ (ownVisits graph node route rooted true).reverse).map event=_;rw [List.map_append,List.map_append,List.map_reverse,own_events,own_events,descendants];rw [walkEvents.eq_def];have permitted:=guarded node;cases equation:graph.node node with | zero=> { simp [equation,Gate.guardLabels,Gate.children]} | input coordinate=> { simp [equation,Gate.guardLabels,Gate.children]} | disj children=> { simp [equation,Gate.guardLabels,Gate.children,List.flatMap];exact congrArg List.flatten (List.ofFn_getElem_eq_map children (fun child=> walkEvents graph (graph.childIndex node child)))} | guard child labels=> { simp [equation,Gate.guardLabels,Gate.children,List.ofFn_succ,List.map_reverse]} | liveAnd left right=> { simp [equation,Gate.IsGuarded,Gate.isLiveAnd] at permitted}}};intro node route rooted;exact claim node.val node rfl route rooted}
theorem root_events (graph:DAG n) (guarded:graph.Guarded): (rootGhost graph).map event=rootEvents graph:=by { simp only [rootGhost,List.map_flatten,List.map_ofFn,Function.comp_apply,rootEvents];have mapped: (List.ofFn fun position:Fin graph.roots.length=> (walkGhost graph (graph.roots.get position) [.inl position] (RootedPath.root position)).map event)=List.ofFn fun position:Fin graph.roots.length=> walkEvents graph (graph.roots.get position):=by { apply congrArg List.ofFn;funext position;exact walk_events graph guarded _ _ _};change (List.ofFn fun position:Fin graph.roots.length=> (walkGhost graph (graph.roots.get position) [.inl position] (RootedPath.root position)).map event).flatten=graph.roots.flatMap (walkEvents graph);rw [mapped];exact congrArg List.flatten (List.ofFn_getElem_eq_map graph.roots (walkEvents graph))}
theorem root_event_count_le (graph:DAG n) (forest:graph.FormulaForest): (rootEvents graph).length≤ 2*graph.guardIncidences:=by
  have counts:=congrArg List.length (root_events graph forest.1)
  simp only [List.length_map] at counts
  rw [← counts]
  exact root_length_le graph forest
end Cost.ForestGuardVisits
namespace Cost.ForestGuardAccumulator
open Decoder Cost.ForestGuardSchedule
variable {n:ℕ}
theorem stored_occurrence_card (graph:DAG n):Nat.card graph.StoredOccurrence=graph.roots.length+graph.childIncidences:=by { simp only [DAG.StoredOccurrence,DAG.ParentOccurrence,Nat.card_sum,Nat.card_sigma,Nat.card_fin,Nat.card_eq_fintype_card];simp [DAG.childIncidences,List.sum_ofFn]}
theorem rooted_route_eq_of_incoming (graph:DAG n) (forest:graph.FormulaForest) (firstNode secondNode:Fin graph.nodeCount) (firstRoute secondRoute:List graph.StoredOccurrence) (firstPath:Cost.ForestOccurrences.RootedPath graph firstNode firstRoute) (secondPath:Cost.ForestOccurrences.RootedPath graph secondNode secondRoute) (incoming:firstRoute.head? =secondRoute.head?):firstRoute=secondRoute:=by { cases firstPath with | root firstPosition=> { cases secondPath with | root secondPosition=> { simp only [List.head?_cons,Option.some.injEq,Sum.inl.injEq] at incoming;cases incoming;rfl} | child parent position ancestorRoute path=> { simp only [List.head?_cons,Option.some.injEq] at incoming;cases incoming}} | child firstParent firstPosition firstAncestor firstAncestorPath=> { cases secondPath with | root secondPosition=> { simp only [List.head?_cons,Option.some.injEq] at incoming;cases incoming} | child secondParent secondPosition secondAncestor secondAncestorPath=> { have positions: (⟨firstParent,firstPosition⟩ :graph.ParentOccurrence)= ⟨secondParent,secondPosition⟩ :=by { exact Sum.inr.inj (Option.some.inj incoming)};have parents:firstParent=secondParent:=congrArg Sigma.fst positions;subst secondParent;have childPositions:firstPosition=secondPosition:=Fin.ext (congrArg (fun position:graph.ParentOccurrence=> position.2.val) positions);subst secondPosition;have ancestors:=Cost.ForestOccurrences.RootedPath.unique_internal graph forest firstParent firstAncestor secondAncestor (Cost.ForestOccurrences.parent_internal graph firstParent firstPosition) firstAncestorPath secondAncestorPath;rw [ancestors]}}}
structure NodeVisit (graph:DAG n) where
  (node:Fin graph.nodeCount) (route:List graph.StoredOccurrence) (rooted:Cost.ForestOccurrences.RootedPath graph node route)
def NodeVisit.incoming {graph:DAG n} (visit:NodeVisit graph):graph.StoredOccurrence:=visit.route.head visit.rooted.nonempty
theorem incoming_refers (graph:DAG n) (visit:NodeVisit graph):graph.refers visit.incoming=visit.node:=by { cases visit with | mk node route rooted=> { cases rooted <;> rfl}}
theorem incoming_injective (graph:DAG n) (forest:graph.FormulaForest):Function.Injective (NodeVisit.incoming (graph:=graph)):=by
  intro first second equal
  have nodes:first.node=second.node:=by
    rw [← incoming_refers graph first, ← incoming_refers graph second]
    exact congrArg graph.refers equal
  cases first with
  | mk firstNode firstRoute firstPath=>
    cases second with
    | mk secondNode secondRoute secondPath=>
      dsimp only at nodes
      subst secondNode
      have routes:=rooted_route_eq_of_incoming graph forest firstNode firstNode
        firstRoute secondRoute firstPath secondPath (by
          rw [List.head?_eq_some_head firstPath.nonempty,List.head?_eq_some_head secondPath.nonempty]
          exact congrArg some equal)
      subst secondRoute
      rfl
theorem node_visit_card_le (graph:DAG n) (forest:graph.FormulaForest):Nat.card (NodeVisit graph)≤ graph.roots.length+graph.childIncidences:=by { exact (Nat.card_le_card_of_injective (NodeVisit.incoming (graph:=graph)) (incoming_injective graph forest)).trans_eq (stored_occurrence_card graph)}
end Cost.ForestGuardAccumulator
namespace Cost.ForestNodeVisits
open Decoder Cost.ForestOccurrences
open Cost.ForestGuardAccumulator
variable {n:ℕ}
def walkGhost (graph:DAG n) (node:Fin graph.nodeCount) (route:List graph.StoredOccurrence) (rooted:RootedPath graph node route):List (NodeVisit graph):=
  ⟨node,route,rooted⟩ ::
    (List.ofFn fun position:Fin (graph.node node).children.length=>
      walkGhost graph (graph.childIndex node ((graph.node node).children.get position))
        (.inr ⟨node,position⟩ ::route) (RootedPath.child node position route rooted)).flatten
termination_by node.val
decreasing_by all_goals exact graph.childIndex_lt _ _
theorem route_suffix (graph:DAG n): ∀ (node:Fin graph.nodeCount) (route:List graph.StoredOccurrence) (rooted:RootedPath graph node route) (visit:NodeVisit graph),visit ∈ walkGhost graph node route rooted→ route <:+visit.route:=by { have claim: ∀ rank:ℕ, ∀ (node:Fin graph.nodeCount),node.val=rank→ ∀ (route:List graph.StoredOccurrence) (rooted:RootedPath graph node route) (visit:NodeVisit graph),visit ∈ walkGhost graph node route rooted→ route <:+visit.route:=by { intro rank;induction rank using Nat.strong_induction_on with | h rank ih=> { intro node value route rooted visit present;rw [walkGhost.eq_def] at present;rcases List.mem_cons.mp present with equal | descendant; · { subst visit;exact List.suffix_refl route}; · { obtain ⟨block,blockPresent,visitPresent⟩ :=List.mem_flatten.mp descendant;obtain ⟨position,equal⟩ :=List.mem_ofFn.mp blockPresent;subst block;have suffix:=ih ((graph.node node).children.get position).val (by { have earlier:=graph.childIndex_lt node ((graph.node node).children.get position);omega}) _ rfl _ _ visit visitPresent;exact (List.suffix_cons _ route).trans suffix}}};intro node route rooted visit present;exact claim node.val node rfl route rooted visit present}
theorem equal_length_suffix {first second whole:List α} (firstSuffix:first <:+whole) (secondSuffix:second <:+whole) (lengths:first.length=second.length):first=second:= (List.suffix_of_suffix_length_le firstSuffix secondSuffix lengths.le).eq_of_length lengths
def childrenGhost (graph:DAG n) (node:Fin graph.nodeCount) (route:List graph.StoredOccurrence) (rooted:RootedPath graph node route):List (NodeVisit graph):= (List.ofFn fun position:Fin (graph.node node).children.length=> walkGhost graph (graph.childIndex node ((graph.node node).children.get position)) (.inr ⟨node,position⟩ ::route) (RootedPath.child node position route rooted)).flatten
theorem own_not_mem_children (graph:DAG n) (node:Fin graph.nodeCount) (route:List graph.StoredOccurrence) (rooted:RootedPath graph node route): (⟨node,route,rooted⟩ :NodeVisit graph) ∉ childrenGhost graph node route rooted:=by { intro present;obtain ⟨block,blockPresent,ownPresent⟩ :=List.mem_flatten.mp present;obtain ⟨position,equal⟩ :=List.mem_ofFn.mp blockPresent;subst block;have suffix:=route_suffix graph _ _ _ _ ownPresent;have lengths:=suffix.length_le;simp only [List.length_cons] at lengths;omega}
theorem child_blocks_disjoint (graph:DAG n) (node:Fin graph.nodeCount) (route:List graph.StoredOccurrence) (rooted:RootedPath graph node route) (first second:Fin (graph.node node).children.length) (different:first ≠ second):List.Disjoint (walkGhost graph (graph.childIndex node ((graph.node node).children.get first)) (.inr ⟨node,first⟩ ::route) (RootedPath.child node first route rooted)) (walkGhost graph (graph.childIndex node ((graph.node node).children.get second)) (.inr ⟨node,second⟩ ::route) (RootedPath.child node second route rooted)):=by
  apply List.disjoint_left.mpr
  intro visit firstPresent secondPresent
  have firstSuffix:=route_suffix graph _ _ _ visit firstPresent
  have secondSuffix:=route_suffix graph _ _ _ visit secondPresent
  have routes:=equal_length_suffix firstSuffix secondSuffix rfl
  have heads:= (List.cons.inj routes).1
  have positions:first=second:=Fin.ext
    (congrArg (fun occurrence:graph.StoredOccurrence=> match occurrence with | .inl _=> 0 | .inr pair=> pair.2.val) heads)
  exact different positions
theorem walk_nodup (graph:DAG n): ∀ (node:Fin graph.nodeCount) (route:List graph.StoredOccurrence) (rooted:RootedPath graph node route), (walkGhost graph node route rooted).Nodup:=by { classical{ have claim: ∀ rank:ℕ, ∀ (node:Fin graph.nodeCount),node.val=rank→ ∀ (route:List graph.StoredOccurrence) (rooted:RootedPath graph node route), (walkGhost graph node route rooted).Nodup:=by { intro rank;induction rank using Nat.strong_induction_on with | h rank ih=> { intro node value route rooted;have childrenNodup: (childrenGhost graph node route rooted).Nodup:=by { apply List.nodup_flatten.mpr;constructor; · { intro block blockPresent;obtain ⟨position,equal⟩ :=List.mem_ofFn.mp blockPresent;subst block;exact ih ((graph.node node).children.get position).val (by { have earlier:=graph.childIndex_lt node ((graph.node node).children.get position);omega}) _ rfl _ _}; · { apply List.pairwise_ofFn.mpr;intro first second before;exact child_blocks_disjoint graph node route rooted first second (ne_of_lt before)}};rw [walkGhost.eq_def];exact List.nodup_cons.mpr ⟨own_not_mem_children graph node route rooted,childrenNodup⟩ }};intro node route rooted;exact claim node.val node rfl route rooted}}
def rootGhost (graph:DAG n):List (NodeVisit graph):= (List.ofFn fun position:Fin graph.roots.length=> walkGhost graph (graph.roots.get position) [.inl position] (RootedPath.root position)).flatten
theorem root_nodup (graph:DAG n): (rootGhost graph).Nodup:=by { classical{ apply List.nodup_flatten.mpr;constructor; · { intro block present;obtain ⟨position,equal⟩ :=List.mem_ofFn.mp present;subst block;exact walk_nodup graph _ _ _}; · { apply List.pairwise_ofFn.mpr;intro first second before;apply List.disjoint_left.mpr;intro visit firstPresent secondPresent;have firstSuffix:=route_suffix graph _ _ _ visit firstPresent;have secondSuffix:=route_suffix graph _ _ _ visit secondPresent;have routes:=equal_length_suffix firstSuffix secondSuffix rfl;have positions:first=second:=Sum.inl.inj (List.cons.inj routes).1;exact (ne_of_lt before) positions}}}
theorem root_length_le (graph:DAG n) (forest:graph.FormulaForest): (rootGhost graph).length≤ graph.roots.length+graph.childIncidences:=by
  classical
  letI:Finite (NodeVisit graph):=Finite.of_injective
    (NodeVisit.incoming (graph:=graph)) (incoming_injective graph forest)
  letI:Fintype (NodeVisit graph):=Fintype.ofFinite _
  have bound: (rootGhost graph).length≤ Nat.card (NodeVisit graph):=by simpa only [Nat.card_eq_fintype_card] using (root_nodup graph).length_le_card
  exact bound.trans (node_visit_card_le graph forest)
def walkNodes (graph:DAG n) (node:Fin graph.nodeCount):List (Fin graph.nodeCount):=
  node:: (graph.node node).children.flatMap (fun child=> walkNodes graph (graph.childIndex node child))
termination_by node.val
decreasing_by all_goals exact graph.childIndex_lt _ _
theorem walk_nodes (graph:DAG n): ∀ (node:Fin graph.nodeCount) (route:List graph.StoredOccurrence) (rooted:RootedPath graph node route), (walkGhost graph node route rooted).map NodeVisit.node=walkNodes graph node:=by { have claim: ∀ rank:ℕ, ∀ (node:Fin graph.nodeCount),node.val=rank→ ∀ (route:List graph.StoredOccurrence) (rooted:RootedPath graph node route), (walkGhost graph node route rooted).map NodeVisit.node=walkNodes graph node:=by { intro rank;induction rank using Nat.strong_induction_on with | h rank ih=> { intro node value route rooted;rw [walkGhost.eq_def,walkNodes.eq_def,List.map_cons,List.map_flatten,List.map_ofFn];apply congrArg (List.cons node);have mapped: (List.ofFn fun position:Fin (graph.node node).children.length=> (walkGhost graph (graph.childIndex node ((graph.node node).children.get position)) (.inr ⟨node,position⟩ ::route) (RootedPath.child node position route rooted)).map NodeVisit.node)=List.ofFn fun position:Fin (graph.node node).children.length=> walkNodes graph (graph.childIndex node ((graph.node node).children.get position)):=by { apply congrArg List.ofFn;funext position;exact ih ((graph.node node).children.get position).val (by { have earlier:=graph.childIndex_lt node ((graph.node node).children.get position);omega}) _ rfl _ _};change (List.ofFn fun position:Fin (graph.node node).children.length=> (walkGhost graph (graph.childIndex node ((graph.node node).children.get position)) (.inr ⟨node,position⟩ ::route) (RootedPath.child node position route rooted)).map NodeVisit.node).flatten=_;rw [mapped];exact congrArg List.flatten (List.ofFn_getElem_eq_map (graph.node node).children (fun child=> walkNodes graph (graph.childIndex node child)))}};intro node route rooted;exact claim node.val node rfl route rooted}
def rootNodes (graph:DAG n):List (Fin graph.nodeCount):=graph.roots.flatMap (walkNodes graph)
theorem root_nodes (graph:DAG n): (rootGhost graph).map NodeVisit.node=rootNodes graph:=by { simp only [rootGhost,rootNodes,List.map_flatten,List.map_ofFn];have mapped: (List.ofFn fun position:Fin graph.roots.length=> (walkGhost graph (graph.roots.get position) [.inl position] (RootedPath.root position)).map NodeVisit.node)=List.ofFn fun position:Fin graph.roots.length=> walkNodes graph (graph.roots.get position):=by { apply congrArg List.ofFn;funext position;exact walk_nodes graph _ _ _};change (List.ofFn fun position:Fin graph.roots.length=> (walkGhost graph (graph.roots.get position) [.inl position] (RootedPath.root position)).map NodeVisit.node).flatten=_;rw [mapped];exact congrArg List.flatten (List.ofFn_getElem_eq_map graph.roots (walkNodes graph))}
theorem root_node_count_le (graph:DAG n) (forest:graph.FormulaForest): (rootNodes graph).length≤ graph.roots.length+graph.childIncidences:=by
  have counts:=congrArg List.length (root_nodes graph)
  simp only [List.length_map] at counts
  rw [← counts]
  exact root_length_le graph forest
end Cost.ForestNodeVisits
namespace Cost.ForestCursorTraversal
open Decoder Decoder.DAG
open Cost.ForestCounter
inductive CursorOp (n:ℕ) where
  | node (index:ℕ) | down (parent position child:ℕ) | up | enter (owner position:ℕ) (channel:Channel n) | leave (owner position:ℕ) (channel:Channel n) | leaf (owner:ℕ) (route:LeafRoute) (head:Channel n)
  deriving DecidableEq
def cursorOps (graph:DAG n) (node:Fin graph.nodeCount) (routePrefix:LeafRoute):List (CursorOp n):=
  .node node.val::match graph.node node with
  | .zero=> []
  | .input head=> [.leaf node.val routePrefix head]
  | .disj refs=> (List.finRange refs.length).flatMap fun position=>
      let child:=graph.childIndex node (refs.get position)
      [.down node.val position.val child.val]++cursorOps graph child (position.val::routePrefix)++ [.up]
  | .guard child labels=>
      (List.finRange labels.length).map (fun position=> .enter node.val position.val (labels.get position))++
        [.down node.val 0 (graph.childIndex node child).val]++
        cursorOps graph (graph.childIndex node child) (0::routePrefix)++ [.up]++
        (List.finRange labels.length).reverse.map (fun position=> .leave node.val position.val (labels.get position))
  | .liveAnd _ _=> []
termination_by node.val
decreasing_by all_goals exact graph.childIndex_lt _ _
end Cost.ForestCursorTraversal
namespace Cost.ForestCursorDescriptors
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
theorem step_valid (root:ℕ) (state:Builder) (valid:Valid state) (operation:CursorOp n):Valid (step root state operation):=by { cases operation with | down owner position child=> { refine ⟨by { simpa [step] using congrArg Nat.succ valid.count},by { simp [step]}, ?_, ?_, ?_⟩; · { intro parent present;rcases List.mem_cons.mp present with equal | earlier; · { subst parent;exact Nat.le_trans valid.current (Nat.le_succ _)}; · { exact Nat.le_trans (valid.parents parent earlier) (Nat.le_succ _)}}; · { intro entry present;rcases List.mem_cons.mp present with equal | earlier; · { subst entry;exact ⟨by { simp},by { simpa using Nat.lt_succ_of_le valid.current},by { simp [step]}⟩ }; · { obtain ⟨positive,parentEarlier,bounded⟩ :=valid.entries entry earlier;exact ⟨positive,parentEarlier,Nat.le_trans bounded (Nat.le_succ _)⟩ }}; · { intro leaf present;exact Nat.le_trans (valid.leaves leaf present) (Nat.le_succ _)}} | up=> { refine ⟨valid.count, ?_, ?_,valid.entries,valid.leaves⟩; · { cases equal:state.parents with | nil=> { simp [step,equal]} | cons parent rest=> { simpa [step,equal] using valid.parents parent (by { rw [equal];exact List.mem_cons_self})}}; · { intro parent present;exact valid.parents parent (List.mem_of_mem_tail present)}} | leaf owner route head=> { refine ⟨valid.count,valid.current,valid.parents,valid.entries, ?_⟩;intro leaf present;rcases List.mem_cons.mp present with equal | earlier; · { subst leaf;exact valid.current}; · { exact valid.leaves leaf earlier}} | node owner=> { exact valid} | enter owner position channel=> { exact valid} | leave owner position channel=> { exact valid}}
theorem scan_valid (root:ℕ) (state:Builder) (valid:Valid state) (operations:List (CursorOp n)):Valid (scan root state operations):=by { induction operations generalizing state with | nil=> { exact valid} | cons operation rest ih=> { exact ih _ (step_valid root state valid operation)}}
def isDown:CursorOp n→ ℕ | .down _ _ _=> 1 | _=> 0
def allocations (operations:List (CursorOp n)):ℕ:= (operations.map isDown).sum
theorem step_count (root:ℕ) (state:Builder) (operation:CursorOp n): (step root state operation).count=state.count+isDown operation:=by { cases operation <;> simp [step,isDown]}
theorem scan_count (root:ℕ) (state:Builder) (operations:List (CursorOp n)): (scan root state operations).count=state.count+allocations operations:=by { induction operations generalizing state with | nil=> { simp [scan,allocations]} | cons operation rest ih=> { change (scan root (step root state operation) rest).count=_;rw [ih,step_count];simp [allocations,Nat.add_assoc]}}
theorem source_root_count (graph:DAG n) (position:Fin graph.roots.length) (state:Builder): (scan position.val (beginRoot state) (cursorOps graph (graph.roots.get position) [])).count=state.count+allocations (cursorOps graph (graph.roots.get position) []):=scan_count position.val (beginRoot state) _
def scanRoot (graph:DAG n) (state:Builder) (position:Fin graph.roots.length):Builder:=scan position.val (beginRoot state) (cursorOps graph (graph.roots.get position) [])
def scanRoots (graph:DAG n) (state:Builder) (positions:List (Fin graph.roots.length)):Builder:=positions.foldl (scanRoot graph) state
def buildRoots (graph:DAG n):Builder:=scanRoots graph initial (List.finRange graph.roots.length)
theorem scanRoot_valid (graph:DAG n) (state:Builder) (valid:Valid state) (position:Fin graph.roots.length):Valid (scanRoot graph state position):=scan_valid position.val (beginRoot state) (beginRoot_valid state valid) _
theorem scanRoots_valid (graph:DAG n) (state:Builder) (valid:Valid state) (positions:List (Fin graph.roots.length)):Valid (scanRoots graph state positions):=by { induction positions generalizing state with | nil=> { exact valid} | cons position rest ih=> { exact ih _ (scanRoot_valid graph state valid position)}}
theorem buildRoots_valid (graph:DAG n):Valid (buildRoots graph):=scanRoots_valid graph initial initial_valid _
theorem scanRoots_count (graph:DAG n) (state:Builder) (positions:List (Fin graph.roots.length)): (scanRoots graph state positions).count=state.count+ (positions.map fun position=> allocations (cursorOps graph (graph.roots.get position) [])).sum:=by { induction positions generalizing state with | nil=> { simp [scanRoots]} | cons position rest ih=> { change (scanRoots graph (scanRoot graph state position) rest).count=_;rw [ih];change (scan position.val (beginRoot state) _).count+_=_;rw [source_root_count];simp [Nat.add_assoc]}}
theorem buildRoots_count (graph:DAG n): (buildRoots graph).entries.length= ((List.finRange graph.roots.length).map fun position=> allocations (cursorOps graph (graph.roots.get position) [])).sum:=by { rw [(buildRoots_valid graph).count];simpa [buildRoots,initial] using scanRoots_count graph initial (List.finRange graph.roots.length)}
end Cost.ForestCursorDescriptors
namespace Cost.ForestIndexedOperands
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
structure RowsMatch (graph:DAG n) (rows:List Row):Prop where
  (length_eq:rows.length=graph.nodeCount)
  node: ∀ index:Fin graph.nodeCount, (rows[index.val]'(by { rw [length_eq];exact index.isLt})).Matches (graph.node index)
def rowBases:List Row→ ℕ→ ℕ→ List ℕ | [],_,_=> [] | row::rest,childCursor,guardCursor=> childCursor::guardCursor::rowBases rest (childCursor+countSource row.children 0) (guardCursor+countSource row.guards 0)
def serializedRows (heapOffset:ℕ) (rows:List Row) (roots:List ℕ):List ℕ:=
  let children:=rowChildren rows
  let guards:=rowGuards rows
  rowHeaders rows++rowBases rows (heapOffset+6*rows.length)
    (heapOffset+6*rows.length+children.length)++rowArities rows++
    children++guards++roots
def RootsMatch (graph:DAG n) (roots:List ℕ):Prop:=roots=graph.roots.map Fin.val
def globalHeader (channels:ℕ) (rows:List Row) (roots:List ℕ):List ℕ:= [channels,countSource rows 0,countSource (rowChildren rows) 0,countSource (rowGuards rows) 0,countSource roots 0]
def inputPacket (channels heapOffset:ℕ) (rows:List Row) (roots:List ℕ):List ℕ:=globalHeader channels rows roots++serializedRows (heapOffset+5) rows roots
end Cost.ForestIndexedOperands
namespace Cost.UniformDAGSource
open Decoder Decoder.DAG
open Cost.ForestIndexedOperands
def typedHead (gate:Gate n available):ℕ:=
  match gate with
  | .input channel=> channel.val
  | .guard child _=> child.val
  | .liveAnd left _=> left.val
  | _=> 0
structure HeadsMatch (graph:DAG n) (rows:List Row)
  (matched:RowsMatch graph rows):Prop where
  head: ∀ node:Fin graph.nodeCount,
    (rows[node.val]'(by { rw [matched.length_eq];exact node.isLt})).head=
      typedHead (graph.node node)
end Cost.UniformDAGSource
namespace Cost.RegisterWiden
open Cost
def widenState (state:State width 4) (saved:Fin 8→ Word width):State width 8:=
  { reg:=fun register=> if small:register.val < 4 then
      state.reg ⟨register.val,small⟩ else saved register
    heap:=state.heap,stack:=state.stack,output:=state.output,
    pc:=state.pc,halted:=state.halted}
end Cost.RegisterWiden
namespace Cost.ForestCursorAllRootsExecution
open Decoder Decoder.DAG
open Cost.ForestCounter
open Cost.ForestCursorTraversal
open Cost.ForestGuardSchedule
open Cost.ForestCursorDescriptors
def rootOperations (graph:DAG n) (positions:List (Fin graph.roots.length)):ℕ:= (positions.map fun position=> (cursorOps graph (graph.roots.get position) []).length).sum
end Cost.ForestCursorAllRootsExecution
namespace Cost.ForestCursorCharging
open Decoder Decoder.DAG Cost.ForestCursorTraversal
open Cost.ForestGuardSchedule
open Cost.ForestCounter
def operationBudget (graph:DAG n) (node:Fin graph.nodeCount):ℕ:=
  match graph.node node with
  | .zero | .liveAnd _ _=> 1
  | .input _=> 2
  | .disj refs=> 1+ (refs.map fun child=> 2+operationBudget graph (graph.childIndex node child)).sum
  | .guard child labels=> 3+2*labels.length+operationBudget graph (graph.childIndex node child)
termination_by node.val
decreasing_by all_goals exact graph.childIndex_lt _ _
theorem cursor_length (graph:DAG n) (node:Fin graph.nodeCount) (route:LeafRoute): (cursorOps graph node route).length=operationBudget graph node:=by
  have claim: ∀ rank:ℕ, ∀ current:Fin graph.nodeCount,current.val=rank→
      ∀ route, (cursorOps graph current route).length=operationBudget graph current:=by
    intro rank
    induction rank using Nat.strong_induction_on with
    | h rank ih=>
      intro current equal route
      rw [cursorOps,operationBudget]
      cases equation:graph.node current with
      | zero=> simp
      | input head=> simp
      | liveAnd left right=> simp
      | guard child labels=>
          have below:=ih (graph.childIndex current child).val
            (by have earlier:=graph.childIndex_lt current child;omega)
            (graph.childIndex current child) rfl (0::route)
          simp only [List.length_cons,List.length_append,List.length_map,List.length_reverse,List.length_finRange,List.length_nil,below]
          omega
      | disj refs=>
          have counts: ((List.finRange refs.length).map fun position=>
              2+ (cursorOps graph (graph.childIndex current (refs.get position)) (position.val::route)).length)=
              refs.map (fun child=> 2+operationBudget graph (graph.childIndex current child)):=by
            calc
              _= (List.finRange refs.length).map (fun position=>
                  2+operationBudget graph (graph.childIndex current (refs.get position))):=by
                apply List.map_congr_left
                intro position present
                rw [ih (graph.childIndex current (refs.get position)).val
                  (by have earlier:=graph.childIndex_lt current (refs.get position);omega)
                  (graph.childIndex current (refs.get position)) rfl]
              _=_:=by
                simpa only [List.map_map,Function.comp_def] using
                  congrArg (List.map (fun child=> 2+operationBudget graph (graph.childIndex current child)))
                    (List.map_get_finRange refs)
          simp only [List.length_cons,List.length_flatMap,List.length_append,List.length_singleton,List.length_nil,Nat.zero_add]
          have same: ((List.finRange refs.length).map fun position=>
              (1+ (cursorOps graph (graph.childIndex current (refs.get position)) (position.val::route)).length)+1)=
              (List.finRange refs.length).map (fun position=> 2+ (cursorOps graph (graph.childIndex current (refs.get position)) (position.val::route)).length):=by
            apply List.map_congr_left
            intro position present
            omega
          simp only [Nat.add_assoc] at same ⊢
          rw [same,counts]
          omega
  exact claim node.val node rfl route
theorem map_sum_bound (items:List α) (first second:α→ ℕ) (bound: ∀ item ∈ items,first item≤ second item): (items.map first).sum≤ (items.map second).sum:=by { induction items with | nil=> { simp} | cons item rest ih=> { have head:=bound item List.mem_cons_self;have tail:=ih (fun current present=> bound current (List.mem_cons_of_mem item present));simp only [List.map_cons,List.sum_cons];omega}}
theorem sum_budget (items:List α) (nodes guards:α→ ℕ): (items.map fun item=> 4*nodes item+guards item).sum=4* (items.map nodes).sum+ (items.map guards).sum:=by { induction items with | nil=> { simp} | cons item rest ih=> { simp only [List.map_cons,List.sum_cons,ih];omega}}
theorem operationBudget_bound (graph:DAG n) (node:Fin graph.nodeCount):operationBudget graph node+2≤ 4* (ForestNodeVisits.walkNodes graph node).length+ (walkEvents graph node).length:=by { have claim: ∀ rank:ℕ, ∀ current:Fin graph.nodeCount,current.val=rank→ operationBudget graph current+2≤ 4* (ForestNodeVisits.walkNodes graph current).length+ (walkEvents graph current).length:=by { intro rank;induction rank using Nat.strong_induction_on with | h rank ih=> { intro current equal;have below: ∀ child:Fin current.val,operationBudget graph (graph.childIndex current child)+2≤ 4* (ForestNodeVisits.walkNodes graph (graph.childIndex current child)).length+ (walkEvents graph (graph.childIndex current child)).length:=by { intro child;exact ih child.val (by { have earlier:=graph.childIndex_lt current child;omega}) (graph.childIndex current child) rfl};rw [operationBudget,ForestNodeVisits.walkNodes,walkEvents];cases equation:graph.node current with | zero=> { simp [Gate.children]} | input head=> { simp [Gate.children]} | liveAnd left right=> { simp only [Gate.children,List.length_cons];omega} | guard child labels=> { have bounded:=below child;simp only [Gate.children,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.length_cons,List.length_append,List.length_map,List.length_reverse];omega} | disj refs=> { have bounded:=map_sum_bound refs (fun child=> 2+operationBudget graph (graph.childIndex current child)) (fun child=> 4* (ForestNodeVisits.walkNodes graph (graph.childIndex current child)).length+ (walkEvents graph (graph.childIndex current child)).length) (fun child present=> by { have currentBound:=below child;omega});rw [sum_budget] at bounded;simp only [Gate.children,List.length_cons,List.length_flatMap];omega}}};exact claim node.val node rfl}
def allRootBudget (graph:DAG n):ℕ:= (graph.roots.map (operationBudget graph)).sum
theorem all_root_budget_bound (graph:DAG n) (forest:graph.FormulaForest):allRootBudget graph≤ 4* (graph.roots.length+graph.childIncidences)+2*graph.guardIncidences:=by { have bounded:=map_sum_bound graph.roots (operationBudget graph) (fun root=> 4* (ForestNodeVisits.walkNodes graph root).length+ (walkEvents graph root).length) (fun root present=> by { have currentBound:=operationBudget_bound graph root;omega});rw [sum_budget] at bounded;have nodes:=ForestNodeVisits.root_node_count_le graph forest;have guards:=ForestGuardVisits.root_event_count_le graph forest;simp only [ForestNodeVisits.rootNodes,rootEvents,List.length_flatMap] at nodes guards;unfold allRootBudget;omega}
end Cost.ForestCursorCharging
namespace Cost.ForestCursorWholeProgram
open Decoder Decoder.DAG
open Cost.ForestCounter
open Cost.ForestCursorTraversal
open Cost.ForestGuardSchedule
open Cost.ForestCursorDescriptors
open Cost.ForestCursorAllRootsExecution
theorem allocations_le_length (operations:List (CursorOp n)):allocations operations≤ operations.length:=by { induction operations with | nil=> { simp [allocations]} | cons operation rest ih=> { cases operation <;> simp only [allocations,List.map_cons,List.sum_cons,isDown,List.length_cons] at* <;> omega}}
theorem map_sum_bound (items:List α) (first second:α→ ℕ) (bound: ∀ item ∈ items,first item≤ second item): (items.map first).sum≤ (items.map second).sum:=by { induction items with | nil=> { simp} | cons item rest ih=> { have head:=bound item List.mem_cons_self;have tail:=ih (fun current present=> bound current (List.mem_cons_of_mem item present));simp only [List.map_cons,List.sum_cons];omega}}
theorem descriptor_count_le_operations (graph:DAG n): (buildRoots graph).count≤ rootOperations graph (List.finRange graph.roots.length):=by
  rw [← (buildRoots_valid graph).count,buildRoots_count]
  exact map_sum_bound _ _ _ (fun position _=> allocations_le_length _)
theorem rootOperations_total (graph:DAG n):rootOperations graph (List.finRange graph.roots.length)=ForestCursorCharging.allRootBudget graph:=by { unfold rootOperations ForestCursorCharging.allRootBudget;simp only [ForestCursorCharging.cursor_length];have same:=congrArg (List.map (ForestCursorCharging.operationBudget graph)) (List.map_get_finRange graph.roots);simpa only [List.map_map,Function.comp_def] using congrArg List.sum same}
end Cost.ForestCursorWholeProgram
namespace Cost.ForestWeightedTagged
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
end Cost.ForestWeightedTagged
namespace Cost.ForestWeightedDirect
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
end Cost.ForestWeightedDirect
namespace Cost.ForestWeightedIndexed
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
      | [first,second]=> some (.liveAnd first second)
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
def emit (weights:Channel n→ W) (total:W) (root b:Nat) (target:Channel n) (state:State n W) (operation:CursorOp n):State n W:=
  let next:= { state with
    descriptors:=ForestCursorDescriptors.step root state.descriptors operation
    operations:=state.operations+1
    arithmetic:=state.arithmetic+ForestWeightedDirect.arithmeticCount b target (view state).data operation}
  match operation with
  | .enter _ _ channel=>
      { next with
        counters:=state.counters.setIfInBounds channel.val (counter state channel+1)
        blockedWeight:=if counter state channel=0 then state.blockedWeight+weights channel else state.blockedWeight}
  | .leave _ _ channel=>
      { next with
        counters:=state.counters.setIfInBounds channel.val (counter state channel - 1)
        blockedWeight:=if counter state channel=1 then state.blockedWeight - weights channel else state.blockedWeight}
  | .leaf _ _ head=>
      if counter state head=0∧ (b ≠ 1∨ counter state target=0) then { next with selected:=choose state.selected ⟨root,state.descriptors.current,total - state.blockedWeight⟩ }
      else next
  | _=> next
def runNode (table:Source n) (weights:Channel n→ W) (total:W) (root b:Nat) (target:Channel n) (owner:Nat) (state:State n W):State n W:=
  let entered:=emit weights total root b target state (.node owner)
  match readNode table owner with
  | .zero=> entered
  | .liveAnd _ _=> entered
  | .input head=> emit weights total root b target entered (.leaf owner [] head)
  | .disj children=> children.zipIdx.foldl (fun current item=>
      let down:=emit weights total root b target current (.down owner item.2 item.1.val)
      let visited:=runNode table weights total root b target item.1.val down
      emit weights total root b target visited .up) entered
  | .guard child labels=>
      let indexed:=labels.zipIdx
      let guarded:=indexed.foldl (fun current item=> emit weights total root b target current (.enter owner item.2 item.1)) entered
      let down:=emit weights total root b target guarded (.down owner 0 child.val)
      let visited:=runNode table weights total root b target child.val down
      let up:=emit weights total root b target visited .up
      indexed.reverse.foldl (fun current item=> emit weights total root b target current (.leave owner item.2 item.1)) up
termination_by owner
decreasing_by all_goals exact Fin.isLt _
def runRoots (table:Source n) (weights:Channel n→ W) (total:W) (b:Nat) (target:Channel n) (roots:List Nat) (state:State n W):State n W:=
  roots.zipIdx.foldl (fun current item=>
    runNode table weights total item.2 b target item.1
      { current with descriptors:=ForestCursorDescriptors.beginRoot current.descriptors}) state
def runAll (table:Source n) (weights:Channel n→ W) (b:Nat) (target:Channel n) (roots:List Nat):W × State n W:=
  let total:= (List.finRange n).foldl (fun value channel=> value+weights channel) 0
  (total,runRoots table weights total b target roots
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
inductive StoreTrace (weights:Channel n→ W) (total:W) (b:Nat) (target:Channel n):
  State n W→ State n W→ Nat→ Prop
  | refl (state:State n W):StoreTrace weights total b target state state (liveCells state) | operation (state:State n W) (root:Nat) (operation:CursorOp n):StoreTrace weights total b target state (emit weights total root b target state operation) (max (liveCells state) (liveCells (emit weights total root b target state operation))) | root (state:State n W):StoreTrace weights total b target state (startRoot state) (liveCells state) | append {first middle last:State n W} {left right:Nat} (earlier:StoreTrace weights total b target first middle left) (later:StoreTrace weights total b target middle last right):StoreTrace weights total b target first last (max left right)
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
end Cost.ForestWeightedIndexed
namespace Physical
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
def runFromFirst {n b:ℕ} (input:PrimaryInput n b) (first:Bool):SelectorRun n b:=runMasks b input.enable input.request (some first)
def healthyQualifiers {n b:ℕ} (input:PrimaryInput n b):Assignment n:=qualifiers input.enable input.request (healthyRun input).flags
def qualifiersFromFirst {n b:ℕ} (input:PrimaryInput n b) (first:Bool):Assignment n:=qualifiers input.enable input.request (runFromFirst input first).flags
def ObservationsDiffer {n q:ℕ} (outputs:Fin q→ Assignment n→ Bool) (healthy faulty:Assignment n):Prop:= ∃ k,outputs k healthy ≠ outputs k faulty
end Physical
namespace Physical
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
end Physical
namespace Physical
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
end Physical
namespace Decoder.DAG
def observations (graph:Decoder.DAG n):Fin graph.roots.length→ Assignment n→ Bool:=fun index assignment=> graph.eval assignment (graph.roots.get index)
end Decoder.DAG
namespace Cost.Forest
open Decoder Decoder.DAG
@[reducible] def rootFamily (graph:DAG n) (positions:List (Fin graph.roots.length)):DAG n:= ⟨graph.nodeCount,graph.node,positions.map graph.roots.get⟩
theorem rootFamily_guarded (graph:DAG n) (guarded:graph.Guarded) (positions:List (Fin graph.roots.length)): (rootFamily graph positions).Guarded:=guarded
theorem rootFamily_cone (graph:DAG n) (positions:List (Fin graph.roots.length)) (owner:Fin graph.nodeCount): (rootFamily graph positions).cone owner=graph.cone owner:=by
  have sameCone: ∀ rank:Nat, ∀ index:Fin graph.nodeCount,index.val=rank→
      (rootFamily graph positions).cone index=graph.cone index:=by
    intro rank
    induction rank using Nat.strong_induction_on with
    | h rank ih=>
      intro index rankEq
      rw [DAG.cone_eq (rootFamily graph positions) index,DAG.cone_eq graph index]
      apply congrArg (fun set:Finset (Fin graph.nodeCount)=> insert index set)
      apply Finset.biUnion_congr (by rfl)
      intro child member
      have earlier:child.val < rank:=by rw [← rankEq];exact child.isLt
      exact ih child.val earlier (graph.childIndex index child) rfl
  exact sameCone owner.val owner rfl
theorem rootFamily_cones_subset (graph:DAG n) (positions:List (Fin graph.roots.length)): (rootFamily graph positions).cones (rootFamily graph positions).roots ⊆ graph.cones graph.roots:=by { intro owner present;obtain ⟨root,member,coneMember⟩ :=Finset.mem_biUnion.mp present;change root ∈ (positions.map graph.roots.get).toFinset at member;have listMember:=List.mem_toFinset.mp member;obtain ⟨position,positionMember,same⟩ :=List.mem_map.mp listMember;have coneEq:=rootFamily_cone graph positions (root:Fin graph.nodeCount);have originalMember:owner ∈ graph.cone root:=by { exact coneEq ▸ coneMember};subst root;exact Finset.mem_biUnion.mpr ⟨graph.roots.get position,List.mem_toFinset.mpr (List.get_mem _ _),originalMember⟩ }
def rootFamilyUse (graph:DAG n) (positions:List (Fin graph.roots.length)) (owner:Fin graph.nodeCount): (rootFamily graph positions).ActiveUses ((rootFamily graph positions).cones (rootFamily graph positions).roots) owner→ graph.ActiveUses (graph.cones graph.roots) owner:=by
  intro use
  rcases use with ⟨occurrence,retained,same⟩
  cases occurrence with
  | inl position=>
    let source:Fin positions.length:= ⟨position.val,by simpa [rootFamily] using position.isLt⟩
    refine ⟨.inl (positions.get source),trivial, ?_⟩
    simpa only [DAG.refers,rootFamily,List.get_eq_getElem,List.getElem_map] using same
  | inr child=>
    refine ⟨.inr child,rootFamily_cones_subset graph positions retained, ?_⟩
    exact same
theorem rootFamilyUse_injective (graph:DAG n) (positions:List (Fin graph.roots.length)) (unique:positions.Nodup) (owner:Fin graph.nodeCount):Function.Injective (rootFamilyUse graph positions owner):=by { intro first second same;apply Subtype.ext;have actual:=congrArg Subtype.val same;cases first with | mk first validFirst=> { cases second with | mk second validSecond=> { rcases validFirst with ⟨retainedFirst,refersFirst⟩;rcases validSecond with ⟨retainedSecond,refersSecond⟩;cases first <;> cases second <;> simp only [rootFamilyUse] at actual; · { apply congrArg Sum.inl;apply Fin.ext;have equality:=Sum.inl.inj actual;have positionsEqual:=unique.get_inj_iff.mp equality;exact congrArg (fun index:Fin positions.length=> index.val) positionsEqual}; · { cases actual}; · { cases actual}; · { exact congrArg Sum.inr (Sum.inr.inj actual)}}}}
theorem rootFamily_forest (graph:DAG n) (forest:graph.FormulaForest) (positions:List (Fin graph.roots.length)) (unique:positions.Nodup): (rootFamily graph positions).FormulaForest:=by { refine ⟨rootFamily_guarded graph forest.1 positions, ?_⟩;intro owner internal;exact (Nat.card_le_card_of_injective _ (rootFamilyUse_injective graph positions unique owner)).trans (forest.2 owner internal)}
end Cost.Forest
namespace Cost.Forest
open Decoder Decoder.DAG Cost.ForestIndexedOperands
theorem rootFamily_rows (graph:DAG n) (positions:List (Fin graph.roots.length)) (rows:List Row) (matched:RowsMatch graph rows):RowsMatch (rootFamily graph positions) rows:=by { refine ⟨matched.length_eq, ?_⟩;intro index;exact matched.node index}
def familyRootIds (graph:DAG n) (positions:List (Fin graph.roots.length)):List Nat:=positions.map (fun position=> (graph.roots.get position).val)
def healthyPositions (graph:DAG n) (target:Channel n) (healthy:Bool):List (Fin graph.roots.length):=
  (List.finRange graph.roots.length).filter
    (fun position=> graph.eval (assignmentOfSet {target}) (graph.roots.get position)==healthy)
end Cost.Forest
namespace Cost.Forest
open Decoder Decoder.DAG
theorem healthyPositions_nodup (graph:DAG n) (target:Channel n) (healthy:Bool): (healthyPositions graph target healthy).Nodup:= (List.nodup_finRange _).filter _
theorem healthyPositions_length_le (graph:DAG n) (target:Channel n) (healthy:Bool): (healthyPositions graph target healthy).length≤ graph.roots.length:=by { simpa only [healthyPositions,List.length_finRange] using List.length_filter_le (fun position=> graph.eval (assignmentOfSet { target}) (graph.roots.get position)==healthy) (List.finRange graph.roots.length)}
end Cost.Forest
namespace Cost.ForestRootProjection
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
def classificationInitial (width:Nat) (graph:DAG n) (rows:List Row) (roots:List Nat) (assignment:Channel n→ Bool) (target:Channel n) (rest output:List (Word width)) (address loaded temporary:Word width) (saved:Fin 8→ Word width):Cost.State width 8:=RegisterWiden.widenState ((ForestCounter.counterState (#[]:Array (Word width)) 0 address loaded temporary).frame ((inputPacket n 0 rows roots).map (word width)++List.ofFn (fun channel=> boolWord width (assignment channel))++ (word width target.val::rest)) output) saved
end Cost.ForestRootProjection
namespace Cost.ForestRootProjection
open Cost Decoder Decoder.DAG
open Cost.ForestCursorTraversal Cost.ForestCursorDescriptors
variable {n:Nat}
def DownBound (limit:Nat):CursorOp n→ Prop | .down _ position _=> position < limit | _=> True
theorem node_children_le_incidence (graph:DAG n) (node:Fin graph.nodeCount): (graph.node node).children.length≤ graph.childIncidences:=by { rw [DAG.childIncidences,List.sum_ofFn];exact Finset.single_le_sum (f:=fun index:Fin graph.nodeCount=> (graph.node index).children.length) (fun index _=> Nat.zero_le _) (Finset.mem_univ node)}
theorem cursor_down_bound (graph:DAG n) (node:Fin graph.nodeCount) (route:LeafRoute): ∀ operation ∈ cursorOps graph node route,DownBound graph.childIncidences operation:=by { have claim: ∀ rank:Nat, ∀ owner:Fin graph.nodeCount,owner.val=rank→ ∀ route:LeafRoute, ∀ operation ∈ cursorOps graph owner route,DownBound graph.childIncidences operation:=by { intro rank;induction rank using Nat.strong_induction_on with | h rank ih=> { intro owner rankEq route;rw [cursorOps];intro operation member;rcases List.mem_cons.mp member with rfl | member; · { trivial};cases nodeEq:graph.node owner with | zero=> { simp only [nodeEq,List.not_mem_nil] at member} | input head=> { simp only [nodeEq,List.mem_singleton] at member;subst operation;trivial} | liveAnd first second=> { simp only [nodeEq,List.not_mem_nil] at member} | disj refs=> { simp only [nodeEq] at member;obtain ⟨position,_,occurrence⟩ :=List.mem_flatMap.mp member;simp only [List.singleton_append,List.mem_cons,List.mem_append,List.mem_singleton,List.not_mem_nil,or_false,or_assoc] at occurrence;rcases occurrence with rfl | childMember | rfl; · { have lengthBound:=node_children_le_incidence graph owner;simp only [nodeEq,Gate.children] at lengthBound;exact position.isLt.trans_le lengthBound}; · { exact ih (graph.childIndex owner (refs.get position)).val (by { have earlier:=graph.childIndex_lt owner (refs.get position);omega}) (graph.childIndex owner (refs.get position)) rfl _ operation childMember}; · { trivial}} | guard child labels=> { simp only [nodeEq,List.mem_append,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false,or_assoc] at member;rcases member with entered | rfl | childMember | rfl | exited; · { obtain ⟨position,_,same⟩ :=List.mem_map.mp entered;subst operation;trivial}; · { have lengthBound:=node_children_le_incidence graph owner;simp only [nodeEq,Gate.children,List.length_cons,List.length_nil] at lengthBound;change 0 < graph.childIncidences;omega}; · { exact ih (graph.childIndex owner child).val (by { have earlier:=graph.childIndex_lt owner child;omega}) (graph.childIndex owner child) rfl _ operation childMember}; · { trivial}; · { obtain ⟨position,_,same⟩ :=List.mem_map.mp exited;subst operation;trivial}}}};exact claim node.val node rfl route}
def PositionsBound (limit:Nat) (builder:Builder):Prop:= ∀ entry ∈ builder.entries,entry.position < limit
theorem descriptor_step_positions (limit root:Nat) (builder:Builder) (bounded:PositionsBound limit builder) (operation:CursorOp n) (source:DownBound limit operation):PositionsBound limit (ForestCursorDescriptors.step root builder operation):=by { cases operation with | down owner position child=> { intro entry member;rcases List.mem_cons.mp member with rfl | old; · { exact source}; · { exact bounded entry old}} | node owner=> { exact bounded} | up=> { exact bounded} | enter owner position channel=> { exact bounded} | leave owner position channel=> { exact bounded} | leaf owner route head=> { exact bounded}}
theorem descriptor_scan_positions (limit root:Nat) (builder:Builder) (bounded:PositionsBound limit builder) (operations:List (CursorOp n)) (source: ∀ operation ∈ operations,DownBound limit operation):PositionsBound limit (scan root builder operations):=by { induction operations generalizing builder with | nil=> { exact bounded} | cons operation rest ih=> { exact ih (ForestCursorDescriptors.step root builder operation) (descriptor_step_positions limit root builder bounded operation (source operation List.mem_cons_self)) (fun later member=> source later (List.mem_cons_of_mem operation member))}}
theorem descriptor_roots_positions (graph:DAG n) (builder:Builder) (bounded:PositionsBound graph.childIncidences builder) (positions:List (Fin graph.roots.length)):PositionsBound graph.childIncidences (scanRoots graph builder positions):=by { induction positions generalizing builder with | nil=> { exact bounded} | cons position rest ih=> { apply ih;exact descriptor_scan_positions graph.childIncidences position.val (beginRoot builder) bounded (cursorOps graph (graph.roots.get position) []) (cursor_down_bound graph _ [])}}
theorem buildRoots_position_bound (graph:DAG n): ∀ entry ∈ (buildRoots graph).entries,entry.position < graph.childIncidences:=by { exact descriptor_roots_positions graph initial (by { intro entry member;cases member}) _}
end Cost.ForestRootProjection
namespace Cost.ForestRootProjection
open Controller Cost Decoder Decoder.DAG
open Cost.ForestCursorDescriptors Cost.ForestIndexedOperands
open Cost.ForestWeightedIndexed Cost.ForestWeightedTagged
variable {width n:Nat} {W:Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]
def healthyGraph (graph:DAG n) (target:Channel n) (healthy:Bool):DAG n:=Forest.rootFamily graph (Forest.healthyPositions graph target healthy)
def healthyRootIds (graph:DAG n) (target:Channel n) (healthy:Bool):List Nat:=Forest.familyRootIds graph (Forest.healthyPositions graph target healthy)
end Cost.ForestRootProjection
namespace Cost.ForestRootProjection
open Cost Decoder Decoder.DAG
open Cost.ForestCursorDescriptors Cost.ForestIndexedOperands
variable {n:Nat}
theorem healthy_geometry (graph:DAG n) (target:Channel n) (healthy:Bool): (healthyGraph graph target healthy).nodeCount=graph.nodeCount∧ (healthyGraph graph target healthy).childIncidences=graph.childIncidences∧ (healthyGraph graph target healthy).guardIncidences=graph.guardIncidences∧ (healthyGraph graph target healthy).roots.length= (Forest.healthyPositions graph target healthy).length∧ (healthyRootIds graph target healthy).length= (Forest.healthyPositions graph target healthy).length:=by { exact ⟨rfl,rfl,rfl,by { simp only [healthyGraph,Forest.rootFamily,List.length_map]},by { simp only [healthyRootIds,Forest.familyRootIds,List.length_map]}⟩ }
theorem actual_descriptor_count_bound (graph:DAG n) (forest:graph.FormulaForest): (buildRoots graph).count≤ 4* (graph.roots.length+graph.childIncidences)+2*graph.guardIncidences:=by { have count:=ForestCursorWholeProgram.descriptor_count_le_operations graph;rw [ForestCursorWholeProgram.rootOperations_total] at count;exact count.trans (ForestCursorCharging.all_root_budget_bound graph forest)}
end Cost.ForestRootProjection
namespace Cost.ForestRootProjection
open Controller Cost Decoder Decoder.DAG
open Cost.ForestCursorDescriptors Cost.ForestIndexedOperands
open Cost.ForestWeightedIndexed Cost.ForestWeightedTagged
variable {n:Nat} {W:Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]
def forestSize (graph:DAG n):Nat:=n+graph.nodeCount+graph.roots.length+graph.childIncidences+graph.guardIncidences
def chosenMixedWidth (graph:DAG n):Nat:=Nat.log 2 (10000* (forestSize graph+1))+1
theorem chosenMixedCapacity (graph:DAG n):10000* (forestSize graph+1) < 2 ^ chosenMixedWidth graph:=Nat.lt_pow_succ_log_self (by { decide}:1 < 2) _
theorem original_descriptor_capacity (graph:DAG n) (forest:graph.FormulaForest) (target:Channel n): (buildRoots (healthyGraph graph target false)).count < 2 ^ chosenMixedWidth graph∧ ∀ entry ∈ (buildRoots (healthyGraph graph target false)).entries,entry.position < 2 ^ chosenMixedWidth graph:=by { have cap:=chosenMixedCapacity graph;have geometry:=healthy_geometry graph target false;have positiveForest:=Forest.rootFamily_forest graph forest (Forest.healthyPositions graph target false) (Forest.healthyPositions_nodup graph target false);have count:=actual_descriptor_count_bound (healthyGraph graph target false) positiveForest;have rootCount:=Forest.healthyPositions_length_le graph target false;simp only [geometry.2.1,geometry.2.2.1,geometry.2.2.2.1] at count;unfold forestSize at cap;constructor; · { omega}; · { intro entry member;have bound:=buildRoots_position_bound (healthyGraph graph target false) entry member;rw [geometry.2.1] at bound;omega}}
end Cost.ForestRootProjection
namespace Cost.ForestOriginalSemantics
open Controller Decoder Decoder.DAG Cost
open Cost.ForestRootProjection Cost.ForestIndexedOperands
open Cost.ForestWeightedIndexed Cost.ForestWeightedTagged
variable {n:Nat} {W:Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]
/-- original physical execution: Formula-forest execution and maximum weight. -/
theorem original_physical_execution (graph:DAG n) (forest:graph.FormulaForest) (b:Nat) (bridge:Physical.Bridge n) (hb:0 < b) (rows:List Row) (originalRoots:List Nat) (originalMatched:RowsMatch graph rows) (heads:UniformDAGSource.HeadsMatch graph rows originalMatched) (originalRootsMatch:RootsMatch graph originalRoots) (weights:Channel n→ W) (nonnegative: ∀ channel,0≤ weights channel) (rest output:List (Word (chosenMixedWidth graph))) (address loaded temporary:Word (chosenMixedWidth graph)) (saved:Fin 8→ Word (chosenMixedWidth graph)): ∃ answer:Bool, ∃ final ticks peak storePeak,Execution (mixedResident (packetPrelude (classificationPrior (chosenMixedWidth graph) graph rows originalRoots (assignmentOfSet {bridge.target}))) (healthyGraph graph bridge.target false) (healthyGraph graph bridge.target true) rows (healthyRootIds graph bridge.target false) (healthyRootIds graph bridge.target true) (Forest.rootFamily_rows graph (Forest.healthyPositions graph bridge.target true) rows originalMatched) weights b bridge.target (original_descriptor_capacity graph forest bridge.target).1 (original_descriptor_capacity graph forest bridge.target).2) (classificationInitial (chosenMixedWidth graph) graph rows originalRoots (assignmentOfSet {bridge.target}) bridge.target rest output address loaded temporary saved) final ticks peak∧ final.halted=true∧ final.reg 4=word (chosenMixedWidth graph) (if answer then 1 else 0)∧ ticks≤ 4721* (n+graph.nodeCount+graph.roots.length+graph.childIncidences+graph.guardIncidences)+450∧ peak≤ 169* (n+graph.nodeCount+graph.roots.length+graph.childIncidences+graph.guardIncidences)+57+rest.length+output.length∧ (runAll (source n rows) weights b bridge.target (healthyRootIds graph bridge.target false)).2.operations≤ 4*forestSize graph∧ (runAll (source n rows) weights b bridge.target (healthyRootIds graph bridge.target false)).2.arithmetic≤ 8*forestSize graph∧ StoreTrace weights (runAll (source n rows) weights b bridge.target (healthyRootIds graph bridge.target false)).1 b bridge.target ⟨Array.replicate n 0,0,ForestCursorDescriptors.initial,none,0,n⟩ (runAll (source n rows) weights b bridge.target (healthyRootIds graph bridge.target false)).2 storePeak∧ programWords (mixedResident (packetPrelude (classificationPrior (chosenMixedWidth graph) graph rows originalRoots (assignmentOfSet {bridge.target}))) (healthyGraph graph bridge.target false) (healthyGraph graph bridge.target true) rows (healthyRootIds graph bridge.target false) (healthyRootIds graph bridge.target true) (Forest.rootFamily_rows graph (Forest.healthyPositions graph bridge.target true) rows originalMatched) weights b bridge.target (original_descriptor_capacity graph forest bridge.target).1 (original_descriptor_capacity graph forest bridge.target).2)+peak+ (storePeak+sourceWords n rows+controlBudget (source n rows) graph.nodeCount+ (6*graph.nodeCount+2*graph.childIncidences+2*graph.guardIncidences+2* (healthyGraph graph bridge.target false).roots.length+5)+6* (healthyGraph graph bridge.target false).roots.length+7)≤ 3558*forestSize graph+2106+rest.length+output.length∧ (answer=true↔ Physical.BridgeDetectable (b:=b) bridge true graph.observations)∧ (answer=true→ ∃ K:Finset (Channel n),Admissible b bridge.target K∧ Physical.BridgeInputDetects bridge true graph.observations (Physical.realizeBridge bridge hb K) true∧ ∃ previous:List (Word (chosenMixedWidth graph)),final.output=List.ofFn (fun channel:Channel n=> boolWord (chosenMixedWidth graph) (assignmentOfSet K channel))++previous):=by { sorry}
end Cost.ForestOriginalSemantics
namespace Optimization.Weights
open Controller Decoder Decoder.DAG
variable {n:ℕ} {W:Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]
open Cost Cost.ForestIndexedOperands
/-- forest maximum weight: Formula-forest execution and maximum weight. -/
theorem forest_maximum_weight (graph:DAG n) (guarded:graph.Guarded) (forest:graph.FormulaForest) (rows:List Row) (roots:List Nat) (matched:RowsMatch graph rows) (rootsMatch:RootsMatch graph roots) (weights:Channel n→ W) (nonnegative: ∀ channel,0≤ weights channel) (b:ℕ) (target:Channel n) (candidate:ForestWeightedTagged.Candidate W) (selected: (ForestWeightedIndexed.view (ForestWeightedIndexed.runAll (ForestWeightedIndexed.source n rows) weights b target roots).2).data.selected=some candidate): (∀ (position:Fin graph.roots.length) (K:Finset (Channel n)),Admissible b target K→ graph.eval (assignmentOfSet K) (graph.roots.get position)=true→ GenericWeight.total weights K≤ candidate.score)∧ (ForestWeightedIndexed.runAll (ForestWeightedIndexed.source n rows) weights b target roots).2.operations≤ 4* (graph.roots.length+graph.childIncidences)+2*graph.guardIncidences∧ (ForestWeightedIndexed.runAll (ForestWeightedIndexed.source n rows) weights b target roots).2.arithmetic≤ n+8* (graph.roots.length+graph.childIncidences)+4*graph.guardIncidences:=by { sorry}
end Optimization.Weights
end Controller
