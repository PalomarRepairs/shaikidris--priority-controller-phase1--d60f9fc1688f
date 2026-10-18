module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Finset.Card
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
public import Mathlib.Data.List.Forall2
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.List.NodupEquivFin
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Order.WellFounded
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Std.Sat.CNF
@[expose] public section
noncomputable section
/-!
# Ordinary resolution and observation wrappers
The grammar, state transitions, resource measures and mathematical predicates
are explicit. Definition holes identify only implementation witnesses; the
selected universal theorems constrain their executions or returned results.
The selected statements retain the exact assumptions of the proof library.
-/
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
abbrev FiniteFormula (v : Nat) := Formula (Fin v)
abbrev negate (l : Literal α) : Literal α := Std.Sat.Literal.negate l
def LiteralHolds (a : α → Bool) (l : Literal α) : Prop := a l.1 = l.2
def ClauseHolds (a : α → Bool) (c : Clause α) : Prop := ∃ l, l ∈ c ∧ LiteralHolds a l
def Satisfies (a : α → Bool) (f : Formula α) : Prop := ∀ c, c ∈ f.clauses → ClauseHolds a c
def Satisfiable (f : Formula α) : Prop := ∃ a, Satisfies a f
def Unsatisfiable (f : Formula α) : Prop := ¬Satisfiable f
def normalizeClause [DecidableEq α] (c : Clause α) : Clause α := c.eraseDups
def ofClauses (cs : List (Clause α)) : Formula α := ⟨cs.toArray⟩
end Controller.CNF
namespace Controller.CNF
abbrev relabel (r : α → β) (f : Formula α) : Formula β := Controller.CNF.OrderedFormula.relabel r f
end Controller.CNF
namespace Controller.CNF
inductive Gate (α : Type*) where
  | and (inputs : List (Literal α)) | or (inputs : List (Literal α)) | xor (left right : Literal α) | alias (input : Literal α) | not (input : Literal α) | constant (value : Bool)
  deriving DecidableEq, Repr
namespace Gate
def clauses (out : Literal α) : Gate α → List (Clause α) | .and ls => ls.map (fun l => [negate out, l]) ++ [out :: ls.map negate] | .or ls => ls.map (fun l => [out, negate l]) ++ [negate out :: ls] | .xor l r => [[l, r, negate out], [negate l, negate r, negate out], [l, negate r, out], [negate l, r, out]] | .alias l => [[negate out, l], [out, negate l]] | .not l => [[out, l], [negate out, negate l]] | .constant b => [[if b then out else negate out]]
end Gate
end Controller.CNF
namespace Controller
abbrev Channel (n : ℕ) := Fin n
end Controller
namespace Controller.Decoder
inductive Gate (n available : ℕ) where
  | zero : Gate n available | input (channel : Channel n) : Gate n available | disj (children : List (Fin available)) : Gate n available | guard (child : Fin available) (labels : List (Channel n)) : Gate n available | liveAnd (left right : Fin available) : Gate n available
  deriving DecidableEq, Repr
namespace Gate
variable {n available : ℕ}
def isLiveAnd : Gate n available → Bool | .liveAnd _ _ => true | _ => false
def IsGuarded (gate : Gate n available) : Prop := gate.isLiveAnd = false
end Gate
structure DAG (n : ℕ) where
  (nodeCount : ℕ) (node : (index : Fin nodeCount) → Gate n index.val) (roots : List (Fin nodeCount))
namespace DAG
variable {n : ℕ}
def childIndex (graph : DAG n) (parent : Fin graph.nodeCount) (child : Fin parent.val) : Fin graph.nodeCount := ⟨child.val, Nat.lt_trans child.isLt parent.isLt⟩
theorem childIndex_lt (graph : DAG n) (parent : Fin graph.nodeCount) (child : Fin parent.val) : (graph.childIndex parent child).val < parent.val := child.isLt
def Guarded (graph : DAG n) : Prop := ∀ index, (graph.node index).IsGuarded
end DAG
end Controller.Decoder
namespace Controller.Physical
structure Bridge (n : ℕ) where
  (target : Channel n) (drivers : Finset (Channel n)) (drivers_nonempty : drivers.Nonempty) (target_not_mem : target ∉ drivers)
def Bridge.remaining {n : ℕ} (bridge : Bridge n) : Finset (Channel n) := Finset.univ \ insert bridge.target bridge.drivers
end Controller.Physical
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
namespace Controller.Resolution
open CNF
abbrev Rows (v : Nat) := Nat → Option (Clause (Fin v))
structure State (v : Nat) where
  (rows : Rows v) (lastId : Nat)
structure Step (v : Nat) where
  (id : Nat) (left : Nat) (right : Nat) (pivot : Literal (Fin v)) (clause : Clause (Fin v))
  deriving DecidableEq, Repr
structure Trace (v : Nat) where
  (originalClauseCount : Nat) (steps : List (Step v)) (finalClauseId : Nat)
  deriving DecidableEq, Repr
def initialState (f : FiniteFormula v) : State v := ⟨fun id => if id = 0 then none else f.clauses[id - 1]?, f.clauses.size⟩
def insertRow (state : State v) (id : Nat) (c : Clause (Fin v)) : State v := ⟨fun j => if j = id then some c else state.rows j, id⟩
def resolvent (pivot : Literal (Fin v)) (left right : Clause (Fin v)) : Clause (Fin v) := normalizeClause ((left.filter (fun l => decide (l ≠ negate pivot))) ++ (right.filter (fun l => decide (l ≠ pivot))))
def ExactRule (pivot : Literal (Fin v)) (left right out : Clause (Fin v)) : Prop := negate pivot ∈ left ∧ pivot ∈ right ∧ out.Nodup ∧ out.toFinset = (resolvent pivot left right).toFinset
instance (pivot : Literal (Fin v)) (left right out : Clause (Fin v)) : Decidable (ExactRule pivot left right out) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))
def StepOK (state : State v) (step : Step v) (left right : Clause (Fin v)) : Prop := state.lastId < step.id ∧ step.left < step.id ∧ step.right < step.id ∧ ExactRule step.pivot left right step.clause
instance (state : State v) (step : Step v) (left right : Clause (Fin v)) : Decidable (StepOK state step left right) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))
def applyStep (state : State v) (step : Step v) : Option (State v) :=
  match state.rows step.left, state.rows step.right with
  | some left, some right => if StepOK state step left right then some (insertRow state step.id step.clause) else none
  | _, _ => none
def runSteps : State v → List (Step v) → Option (State v)
  | state, [] => some state
  | state, step :: steps =>
    match applyStep state step with
    | none => none
    | some next => runSteps next steps
def check (f : FiniteFormula v) (trace : Trace v) : Bool :=
  if trace.originalClauseCount = f.clauses.size then
    match runSteps (initialState f) trace.steps with
    | none => false
    | some state =>
      match state.rows trace.finalClauseId with
      | none => false
      | some c => c.isEmpty
  else false
end Controller.Resolution
namespace Controller.NativeProof.Rows
open Controller.CNF Controller.Resolution
def mapClause (rename : α → Fin v) (clause : Clause α) : Clause (Fin v) := clause.map (fun literal => (rename literal.1, literal.2))
structure Available (state : State v) (clause : Clause (Fin v)) where
  (id : Nat) (present : state.rows id = some clause) (bound : id ≤ state.lastId)
end Controller.NativeProof.Rows
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
  | nil => simp [pairLayer]
  | singleton input => simp [pairLayer]
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
namespace Controller.NativeProof.SourceFoldOccurrences
open Controller.Native Controller.Native.SourceController Controller.CNF
variable {parameters : Parameters}
def decoderStart (side : Side) : Cursor parameters :=
  match side with
  | .healthy => originalObservations parameters (controller parameters)
  | .faulty => attachDecoder parameters .healthy
      (originalObservations parameters (controller parameters))
end Controller.NativeProof.SourceFoldOccurrences
namespace Controller.NativeProof.SourceStageCongruence
open Controller.Native Controller.Native.SourceController Controller.CNF
open Controller.Resolution
open Controller.NativeProof.SourceFoldOccurrences
variable {parameters : Parameters} {v : Nat}
structure SourcePrefix (rename : Nat → Fin v) where
  (state : State v) (steps : List (Step v)) (checked : runSteps (initialState (relabel rename (SourceController.formula parameters))) steps = some state)
end Controller.NativeProof.SourceStageCongruence
namespace Controller.NativeProof.Compiler
open Controller.CNF Controller.Resolution
open Controller.Native Controller.Native.SourceController
open Controller.NativeProof.SourceStageCongruence
variable {parameters : Parameters} {v : Nat}
structure Refutation (rename : Nat → Fin v) where
  proofPrefix : SourcePrefix (parameters := parameters) rename
  (empty : Rows.Available proofPrefix.state [])
def Refutation.trace {rename : Nat → Fin v} (result : Refutation (parameters := parameters) rename) : Trace v := ⟨(formula parameters).clauses.size, result.proofPrefix.steps, result.empty.id⟩
def supported (parameters : Parameters) : Bool := (parameters.layout == .raw) && (List.finRange parameters.decoder.nodeCount).all (fun node => !(parameters.decoder.node node).isLiveAnd)
def variableCount (parameters : Parameters) : Nat := (SourceController.compile parameters).lastID + 1
def canonicalRename (parameters : Parameters) : Nat → Fin (variableCount parameters) :=
  let count := variableCount parameters
  fun source => ⟨source % count, Nat.mod_lt _ (by unfold count variableCount; omega)⟩
def nativeFormula (parameters : Parameters) : FiniteFormula (variableCount parameters) :=
  let count := variableCount parameters
  relabel (fun source => ⟨source % count, Nat.mod_lt _ (by unfold count variableCount; omega)⟩) (formula parameters)
end Controller.NativeProof.Compiler
namespace Controller.Cost.NativeResolution
open Controller Controller.CNF Controller.Resolution
open Controller.Native Controller.Native.SourceController
open Controller.NativeProof
open Controller.NativeProof.SourceStageCongruence
set_option maxRecDepth 8192
section FullPrefix
open Controller.NativeProof
open Controller.NativeProof.Compiler
variable {parameters : Parameters} {v : Nat}
noncomputable def compactRefute : {parameters : Controller.Native.Parameters} → {v : ℕ} → (rename : ℕ → Fin v) → Eq.{1} parameters.layout Controller.Native.PrefixLayout.raw → parameters.decoder.Guarded → Controller.CNF.Unsatisfiable.{0} (Controller.Native.SourceController.formula parameters) → Controller.NativeProof.Compiler.Refutation (parameters := parameters) rename := by sorry
end FullPrefix
/-- canonical derived literal storage: Ordinary resolution and observation wrappers. -/
theorem canonical_derived_literal_storage (parameters : Parameters) (raw : parameters.layout = .raw)
    (guarded : parameters.decoder.Guarded) (unsat : Unsatisfiable (formula parameters)) :
    let result := compactRefute (NativeProof.Compiler.canonicalRename parameters) raw guarded unsat
    (result.proofPrefix.steps.map fun step => step.clause.length).sum ≤
      200000 * (NativeProof.Compiler.variableCount parameters) ^ 4 := by
  sorry
noncomputable def compactNativeCompile : (parameters : Controller.Native.Parameters) → Option.{0} (Controller.Resolution.Trace (Controller.NativeProof.Compiler.variableCount parameters)) := by sorry
/-- compactNativeCompile complete: Ordinary resolution and observation wrappers. -/
theorem compactNativeCompile_complete (parameters : Parameters) (raw : parameters.layout = .raw) (guarded : parameters.decoder.Guarded) (unsat : Unsatisfiable (formula parameters)) : ∃ trace, compactNativeCompile parameters = some trace ∧ check (NativeProof.Compiler.nativeFormula parameters) trace = true ∧ trace.steps.length ≤ 100000 * (NativeProof.Compiler.variableCount parameters) ^ 3 := by sorry
/-- compactNativeCompile checked: Ordinary resolution and observation wrappers. -/
theorem compactNativeCompile_checked (parameters : Parameters) (trace : Trace (NativeProof.Compiler.variableCount parameters)) (returned : compactNativeCompile parameters = some trace) : check (NativeProof.Compiler.nativeFormula parameters) trace = true ∧ trace.steps.length ≤ 100000 * (NativeProof.Compiler.variableCount parameters) ^ 3 := by sorry
def nativeEncodedSize (parameters : Parameters) : Nat := NativeProof.Compiler.variableCount parameters + ((NativeProof.Compiler.nativeFormula parameters).clauses.toList.map List.length).sum
/-- native refutation encoded cubic: Ordinary resolution and observation wrappers. -/
theorem native_refutation_encoded_cubic (parameters : Parameters) (raw : parameters.layout = .raw) (guarded : parameters.decoder.Guarded) (unsat : Unsatisfiable (formula parameters)) : ∃ result : NativeProof.Compiler.Refutation (parameters := parameters) (NativeProof.Compiler.canonicalRename parameters), check (NativeProof.Compiler.nativeFormula parameters) result.trace = true ∧ result.proofPrefix.steps.length ≤ 100000 * nativeEncodedSize parameters ^ 3 := by sorry
end Controller.Cost.NativeResolution
namespace Controller.Native.ObservationProjection
open CNF
inductive RequirementTree (ρ : Type*) where
  | leaf (observation : ρ) | branch (left right : RequirementTree ρ)
def RequirementTree.leaves : RequirementTree ρ → List ρ | .leaf i => [i] | .branch left right => left.leaves ++ right.leaves
def RequirementTree.atPath (tree : RequirementTree ρ) : List Bool → Option (RequirementTree ρ)
  | [] => some tree
  | false :: rest => match tree with
    | .leaf _ => none
    | .branch left _ => left.atPath rest
  | true :: rest => match tree with
    | .leaf _ => none
    | .branch _ right => right.atPath rest
inductive PrivateActivity (ι ρ : Type*) where
  | internal (activity : ι) | observed (observation : ρ) | tree (path : List Bool)
def RequirementTree.root (tree : RequirementTree ρ) (path : List Bool) : PrivateActivity ι ρ :=
  match tree with
  | .leaf i => .observed i
  | .branch _ _ => .tree path
structure OptionalClause (σ ι ρ : Type*) where
  (premise : ι) (alternatives : List (PrivateActivity ι ρ)) (signals : Clause σ)
structure OptionalWrapper (σ ι ρ : Type*) where
  (tree : RequirementTree ρ) (distinctLeaves : tree.leaves.Nodup) (observedPairs : ρ → Literal σ × Literal σ) (internalPairs : ι → Literal σ × Literal σ) (clauses : List (OptionalClause σ ι ρ))
def guardRows (activity : α) (pair : Literal σ × Literal σ) : List (Clause (Sum σ α)) := [[(Sum.inr activity, false), (Sum.inl pair.1.1, pair.1.2), (Sum.inl pair.2.1, pair.2.2)], [(Sum.inr activity, false), (Sum.inl pair.1.1, !pair.1.2), (Sum.inl pair.2.1, !pair.2.2)]]
def requirementRow (parent left right : α) : Clause (Sum σ α) := [(Sum.inr parent, false), (Sum.inr left, true), (Sum.inr right, true)]
def RequirementTree.rows (tree : RequirementTree ρ) (path : List Bool) : List (Clause (Sum σ (PrivateActivity ι ρ))) :=
  match tree with
  | .leaf _ => []
  | .branch left right =>
      requirementRow (.tree path) (left.root (path ++ [false])) (right.root (path ++ [true])) ::
        left.rows (path ++ [false]) ++ right.rows (path ++ [true])
def OptionalClause.clause (clause : OptionalClause σ ι ρ) : Clause (Sum σ (PrivateActivity ι ρ)) := (Sum.inr (.internal clause.premise), false) :: (clause.alternatives.map (fun alternative => (Sum.inr alternative, true)) ++ clause.signals.map (fun literal => (Sum.inl literal.1, literal.2)))
end Controller.Native.ObservationProjection
namespace Controller.NativeProof.Wrapper
open Controller.CNF Controller.Resolution
open Controller.Native.ObservationProjection
open Controller.NativeProof.SourceStageCongruence
variable {v : Nat}
def optionalRows (wrapper : OptionalWrapper σ (Fin internalCount) ρ) : List (Clause (Sum σ (PrivateActivity (Fin internalCount) ρ))) := ((List.finRange internalCount).flatMap fun i => guardRows (.internal i) (wrapper.internalPairs i)) ++ (wrapper.tree.leaves.flatMap fun i => guardRows (.observed i) (wrapper.observedPairs i)) ++ wrapper.clauses.map OptionalClause.clause ++ wrapper.tree.rows [] ++ [[(Sum.inr (wrapper.tree.root []), true)]] deriving instance DecidableEq for PrivateActivity
open Controller.Native Controller.Native.SourceController
def retainedIndex (parameters : Parameters) (index : Nat) : Prop := index < (controller parameters).entries.length ∨ ((SourceFoldOccurrences.decoderStart (parameters := parameters) .healthy).entries.length ≤ index ∧ index < (attachDecoder parameters .healthy (SourceFoldOccurrences.decoderStart .healthy)).entries.length) ∨ ((SourceFoldOccurrences.decoderStart (parameters := parameters) .faulty).entries.length ≤ index ∧ index < (attachDecoder parameters .faulty (SourceFoldOccurrences.decoderStart .faulty)).entries.length)
instance (parameters : Parameters) (index : Nat) : Decidable (retainedIndex parameters index) := inferInstanceAs (Decidable (_ ∨ (_ ∧ _) ∨ (_ ∧ _)))
def nativeCoreEntries (parameters : Parameters) : List (Entry parameters) := ((List.finRange (compile parameters).entries.length).filter (fun owner => decide (retainedIndex parameters owner.val))).map (fun owner => (compile parameters).entries[owner.val])
def nativeCoreRows (parameters : Parameters) : List (Clause Nat) := ((nativeCoreEntries parameters).flatMap (fun entry => entry.producer.rows)) ++ ((assertions parameters).take 3).map (fun literal => [literal])
def nativePair (parameters : Parameters) (output : Fin parameters.decoder.roots.length) : Literal Nat × Literal Nat := (sourceRoleMap parameters (.internal (.decoder .healthy (parameters.decoder.roots.get output))), sourceRoleMap parameters (.internal (.decoder .faulty (parameters.decoder.roots.get output))))
def taggedCoreRows (parameters : Parameters) {α : Type} : List (Clause (Sum Nat α)) := (nativeCoreRows parameters).map (fun clause => clause.map (fun literal => (Sum.inl literal.1, literal.2)))
def optionalInputRows (parameters : Parameters) (wrapper : OptionalWrapper Nat (Fin internalCount) (Fin parameters.decoder.roots.length)) := taggedCoreRows parameters ++ optionalRows wrapper
def optionalFiniteInput (parameters : Parameters) (wrapper : OptionalWrapper Nat (Fin internalCount) (Fin parameters.decoder.roots.length)) (rename : Sum Nat (PrivateActivity (Fin internalCount) (Fin parameters.decoder.roots.length)) → Fin v) : FiniteFormula v := ofClauses ((optionalInputRows parameters wrapper).map (Rows.mapClause rename))
end Controller.NativeProof.Wrapper
namespace Controller.NativeProof.Wrapper
open Controller.CNF Controller.Resolution Controller.Native Controller.Native.SourceController
open Controller.Native.ObservationProjection
variable {internalCount : Nat}
abbrev WrapperLabel (parameters : Parameters) (internalCount : Nat) := Sum Nat (PrivateActivity (Fin internalCount) (Fin parameters.decoder.roots.length)) local instance (parameters : Parameters) : BEq (WrapperLabel parameters internalCount) := ⟨fun first second => decide (first = second)⟩
def canonicalWrapperLabels (parameters : Parameters) (wrapper : OptionalWrapper Nat (Fin internalCount) (Fin parameters.decoder.roots.length)) : List (WrapperLabel parameters internalCount) := ((optionalInputRows parameters wrapper).flatMap (fun clause => clause.map Prod.fst)).dedup
def canonicalWrapperCount (parameters : Parameters) (wrapper : OptionalWrapper Nat (Fin internalCount) (Fin parameters.decoder.roots.length)) : Nat := (canonicalWrapperLabels parameters wrapper).length + 1
def canonicalLabelIndex (parameters : Parameters) (labels : List (WrapperLabel parameters internalCount)) (label : WrapperLabel parameters internalCount) : Fin (labels.length + 1) := ⟨labels.idxOf label, Nat.lt_succ_of_le List.idxOf_le_length⟩
def canonicalOptionalInput (parameters : Parameters) (wrapper : OptionalWrapper Nat (Fin internalCount) (Fin parameters.decoder.roots.length)) : FiniteFormula (canonicalWrapperCount parameters wrapper) :=
  let labels := canonicalWrapperLabels parameters wrapper
  optionalFiniteInput parameters wrapper (fun label => canonicalLabelIndex parameters labels label)
end Controller.NativeProof.Wrapper
namespace Controller.NativeProof.Wrapper
open Controller.CNF Controller.Resolution Controller.Native Controller.Native.SourceController
open Controller.Native.ObservationProjection
open Controller.NativeProof.SourceStageCongruence
variable {internalCount v : Nat}
def selectedInputRows (parameters : Parameters) (wrapper : OptionalWrapper Nat (Fin internalCount) (Fin parameters.decoder.roots.length)) (selected : List (Fin parameters.decoder.roots.length)) := optionalInputRows parameters wrapper ++ [selected.map (fun output => (Sum.inr (.observed output), true))]
def selectedFiniteInput (parameters : Parameters) (wrapper : OptionalWrapper Nat (Fin internalCount) (Fin parameters.decoder.roots.length)) (selected : List (Fin parameters.decoder.roots.length)) (rename : WrapperLabel parameters internalCount → Fin v) : FiniteFormula v := ofClauses ((selectedInputRows parameters wrapper selected).map (Rows.mapClause rename))
def canonicalSelectedInput (parameters : Parameters) (wrapper : OptionalWrapper Nat (Fin internalCount) (Fin parameters.decoder.roots.length)) (selected : List (Fin parameters.decoder.roots.length)) : FiniteFormula (canonicalWrapperCount parameters wrapper) :=
  let labels := canonicalWrapperLabels parameters wrapper
  selectedFiniteInput parameters wrapper selected (fun label => canonicalLabelIndex parameters labels label)
end Controller.NativeProof.Wrapper
namespace Controller.NativeProof.Wrapper
open Controller.CNF Controller.Resolution Controller.Native Controller.Native.SourceController
open Controller.Native.ObservationProjection
variable {internalCount : Nat}
def declaredActivity {ρ : Type} [BEq ρ] (wrapper : OptionalWrapper Nat (Fin internalCount) ρ) : PrivateActivity (Fin internalCount) ρ → Bool
  | .internal _ => true
  | .observed output => wrapper.tree.leaves.contains output
  | .tree path => match wrapper.tree.atPath path with
    | some (.branch _ _) => true
    | _ => false
def wrapperSupported (parameters : Parameters) (wrapper : OptionalWrapper Nat (Fin internalCount) (Fin parameters.decoder.roots.length)) : Bool := Compiler.supported parameters && ((wrapper.tree.leaves.all (fun output => decide (wrapper.observedPairs output = nativePair parameters output))) && wrapper.clauses.all (fun clause => clause.alternatives.all (declaredActivity wrapper)))
end Controller.NativeProof.Wrapper
namespace Controller.Cost.WrapperResolution
open Controller.CNF Controller.Resolution
open Controller.NativeProof
open Controller.NativeProof.Wrapper
variable {a u v : Nat}
section CoreSize
open Controller.Native Controller.Native.SourceController
open Controller.NativeProof.SourceFoldOccurrences
def nativeCoreSize (parameters : Parameters) (observed : Nat) : Nat := SourceInitialIDs.rootCount parameters + (nativeCoreEntries parameters).length + ((nativeCoreRows parameters).map List.length).sum + 2 * observed
end CoreSize
section WrapperSize
open Controller.Native Controller.Native.SourceController Controller.Native.ObservationProjection
variable {internalCount : Nat}
def wrapperSize (parameters : Parameters) (wrapper : OptionalWrapper Nat (Fin internalCount) (Fin parameters.decoder.roots.length)) : Nat := (optionalRows wrapper).length + ((optionalRows wrapper).map List.length).sum
def selectedWrapperSize (parameters : Parameters) (wrapper : OptionalWrapper Nat (Fin internalCount) (Fin parameters.decoder.roots.length)) (selected : List (Fin parameters.decoder.roots.length)) : Nat := wrapperSize parameters wrapper + 1 + selected.length
end WrapperSize
section Runtime
open Controller.Native Controller.Native.ObservationProjection
variable {internalCount : Nat}
noncomputable def runOptional : {internalCount : ℕ} → (parameters : Controller.Native.Parameters) → (wrapper : Controller.Native.ObservationProjection.OptionalWrapper.{0, 0, 0} ℕ (Fin internalCount) (Fin (List.length.{0} parameters.decoder.roots))) → Option.{0} (Controller.Resolution.Trace (Controller.NativeProof.Wrapper.canonicalWrapperCount parameters wrapper)) := by sorry
noncomputable def runSelected : {internalCount : ℕ} → (parameters : Controller.Native.Parameters) → (wrapper : Controller.Native.ObservationProjection.OptionalWrapper.{0, 0, 0} ℕ (Fin internalCount) (Fin (List.length.{0} parameters.decoder.roots))) → List.{0} (Fin (List.length.{0} parameters.decoder.roots)) → Option.{0} (Controller.Resolution.Trace (Controller.NativeProof.Wrapper.canonicalWrapperCount parameters wrapper)) := by sorry
/-- runOptional checked: Ordinary resolution and observation wrappers. -/
theorem runOptional_checked (parameters : Parameters) (wrapper : OptionalWrapper Nat (Fin internalCount) (Fin parameters.decoder.roots.length)) (trace : Trace (canonicalWrapperCount parameters wrapper)) (returned : runOptional parameters wrapper = some trace) : check (canonicalOptionalInput parameters wrapper) trace = true := by sorry
/-- runSelected checked: Ordinary resolution and observation wrappers. -/
theorem runSelected_checked (parameters : Parameters) (wrapper : OptionalWrapper Nat (Fin internalCount) (Fin parameters.decoder.roots.length)) (selected : List (Fin parameters.decoder.roots.length)) (trace : Trace (canonicalWrapperCount parameters wrapper)) (returned : runSelected parameters wrapper selected = some trace) : check (canonicalSelectedInput parameters wrapper selected) trace = true := by sorry
/-- runOptional complete cubic: Ordinary resolution and observation wrappers. -/
theorem runOptional_complete_cubic (parameters : Parameters) (wrapper : OptionalWrapper Nat (Fin internalCount) (Fin parameters.decoder.roots.length)) (accepted : wrapperSupported parameters wrapper = true) (unsat : Unsatisfiable (canonicalOptionalInput parameters wrapper)) : ∃ trace, runOptional parameters wrapper = some trace ∧ check (canonicalOptionalInput parameters wrapper) trace = true ∧ trace.steps.length ≤ 1000000 * (nativeCoreSize parameters wrapper.tree.leaves.length) ^ 3 + 5 * wrapperSize parameters wrapper := by sorry
/-- runSelected complete cubic: Ordinary resolution and observation wrappers. -/
theorem runSelected_complete_cubic (parameters : Parameters) (wrapper : OptionalWrapper Nat (Fin internalCount) (Fin parameters.decoder.roots.length)) (accepted : wrapperSupported parameters wrapper = true) (selected : List (Fin parameters.decoder.roots.length)) (nonempty : selected ≠ []) (leaves : ∀ output ∈ selected, output ∈ wrapper.tree.leaves) (unsat : Unsatisfiable (canonicalSelectedInput parameters wrapper selected)) : ∃ trace, runSelected parameters wrapper selected = some trace ∧ check (canonicalSelectedInput parameters wrapper selected) trace = true ∧ trace.steps.length ≤ 1000000 * (nativeCoreSize parameters selected.dedup.length) ^ 3 + 5 * selectedWrapperSize parameters wrapper selected := by sorry
end Runtime
end Controller.Cost.WrapperResolution
