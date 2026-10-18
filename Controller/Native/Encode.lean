module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.CNF.Tseitin
public import Controller.Decoder.Foundation
public import Controller.Physical.CandidateInvariant
public import Controller.Physical.BridgeCofactors
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Native bridge roles and complete gate equations

Every enable, request and the interface wire `W` is a separate free root.
Healthy and faulty copies share those roots and use identical decoder syntax.
The two selector layouts differ in whether each local request rebuilds its
mask prefix or reads a shared accumulated-prefix wire. Their sizes are kept
separate. The gate table is the specification consumed by bounded gate-block
expansion; its n-ary rows are not assigned the bounded-layout row count.
-/

namespace Controller.Native

inductive Side where
  | healthy
  | faulty
  deriving DecidableEq, Repr

def Side.all : List Side := [.healthy, .faulty]

@[simp] theorem Side.mem_all (side : Side) : side ∈ Side.all := by
  cases side <;> simp [Side.all]

inductive PrefixLayout where
  | raw
  | shared
  deriving DecidableEq, Repr

/-- Raw prefixes allocate no accumulated-prefix outputs. -/
def PrefixLayout.activeCount : PrefixLayout → ℕ → ℕ
  | .raw, _ => 0
  | .shared, buses => buses

inductive PrimaryRole (n b : ℕ) where
  | enable (channel : Fin n)
  | request (bus : Fin b) (channel : Fin n)
  | wire
  deriving DecidableEq, Repr

/-- Every constructor is a distinct internal output role. -/
inductive Role (layout : PrefixLayout) (n b m q : ℕ) where
  | driver
  | remaining
  | firstProduct (side : Side)
  | term (side : Side) (bus : Fin b) (channel : Fin n)
  | absent (side : Side) (bus : Fin b) (channel : Fin n)
  | flag (side : Side) (bus : Fin b)
  | mask (side : Side) (bus : Fin b) (channel : Fin n)
  | active (side : Side) (bus : Fin (layout.activeCount b)) (channel : Fin n)
  | qualifierGuard (side : Side) (bus : Fin b) (channel : Fin n)
  | qualifier (side : Side) (channel : Fin n)
  | decoder (side : Side) (node : Fin m)
  | difference (output : Fin q)
  | detected
  deriving DecidableEq, Repr

structure Parameters where
  channels : ℕ
  buses : ℕ
  positiveBuses : 0 < buses
  bridge : Physical.Bridge channels
  decoder : Decoder.DAG channels
  layout : PrefixLayout
  drive : Bool

abbrev Internal (parameters : Parameters) :=
  Role parameters.layout parameters.channels parameters.buses
    parameters.decoder.nodeCount parameters.decoder.roots.length

inductive Variable (parameters : Parameters) where
  | primary (role : PrimaryRole parameters.channels parameters.buses)
  | internal (role : Internal parameters)
  deriving DecidableEq, Repr

abbrev Lit (parameters : Parameters) := CNF.Literal (Variable parameters)

namespace Parameters

def positive (slot : Variable parameters) : Lit parameters := (slot, true)

def negative (slot : Variable parameters) : Lit parameters := (slot, false)

def enable (parameters : Parameters) (channel : Fin parameters.channels) : Lit parameters :=
  positive (.primary (.enable channel))

def request (parameters : Parameters) (bus : Fin parameters.buses)
    (channel : Fin parameters.channels) : Lit parameters := positive (.primary (.request bus channel))

def internal (parameters : Parameters) (role : Internal parameters) : Lit parameters :=
  positive (.internal role)

def firstBus (parameters : Parameters) : Fin parameters.buses := ⟨0, parameters.positiveBuses⟩

def targetAbsent (parameters : Parameters) : Lit parameters :=
  internal parameters (.absent .healthy parameters.firstBus parameters.bridge.target)

/-- An explicit ordered list of all primary roles, with `W` counted once. -/
def primaryRoles (parameters : Parameters) : List (PrimaryRole parameters.channels parameters.buses) :=
  (List.finRange parameters.channels).map .enable ++
    (List.finRange parameters.buses).flatMap (fun bus =>
      (List.finRange parameters.channels).map (.request bus)) ++ [.wire]

/-- The native gate table enumerates outputs once; rows within each block keep their order. -/
def roles (parameters : Parameters) : List (Internal parameters) :=
  [.driver, .remaining] ++ Side.all.map .firstProduct ++
    Side.all.flatMap (fun side =>
      (List.finRange parameters.buses).flatMap fun bus =>
        (List.finRange parameters.channels).map (.term side bus)) ++
    Side.all.flatMap (fun side =>
      (List.finRange parameters.buses).flatMap fun bus =>
        (List.finRange parameters.channels).map (.absent side bus)) ++
    Side.all.flatMap (fun side => (List.finRange parameters.buses).map (.flag side)) ++
    Side.all.flatMap (fun side =>
      (List.finRange parameters.buses).flatMap fun bus =>
        (List.finRange parameters.channels).map (.mask side bus)) ++
    Side.all.flatMap (fun side =>
      (List.finRange (parameters.layout.activeCount parameters.buses)).flatMap fun bus =>
        (List.finRange parameters.channels).map (.active side bus)) ++
    Side.all.flatMap (fun side =>
      (List.finRange parameters.buses).flatMap fun bus =>
        (List.finRange parameters.channels).map (.qualifierGuard side bus)) ++
    Side.all.flatMap (fun side => (List.finRange parameters.channels).map (.qualifier side)) ++
    Side.all.flatMap (fun side =>
      (List.finRange parameters.decoder.nodeCount).map (.decoder side)) ++
    (List.finRange parameters.decoder.roots.length).map .difference ++ [.detected]

@[simp] theorem mem_primaryRoles (parameters : Parameters) (role) :
    role ∈ parameters.primaryRoles := by
  cases role <;> simp [primaryRoles]

@[simp] theorem mem_roles (parameters : Parameters) (role) : role ∈ parameters.roles := by
  cases role <;> simp [roles]

/-- The complete declared universe includes all primary and internal roles. -/
def variableRoles (parameters : Parameters) : List (Variable parameters) :=
  parameters.primaryRoles.map .primary ++ parameters.roles.map .internal

@[simp] theorem mem_variableRoles (parameters : Parameters) (slot : Variable parameters) :
    slot ∈ parameters.variableRoles := by
  cases slot <;> simp [variableRoles]

instance (parameters : Parameters) : Fintype (Variable parameters) :=
  Fintype.ofList parameters.variableRoles (mem_variableRoles parameters)

/-- The same abstract decoder gate is wired to the corresponding qualifier copy. -/
def decoderGate (parameters : Parameters) (side : Side)
    (index : Fin parameters.decoder.nodeCount) : CNF.Gate (Variable parameters) :=
  match parameters.decoder.node index with
  | .zero => .or []
  | .input channel => .alias (internal parameters (.qualifier side channel))
  | .disj children => .or (children.map fun child =>
      internal parameters (.decoder side (parameters.decoder.childIndex index child)))
  | .guard child labels => .and
      (internal parameters (.decoder side (parameters.decoder.childIndex index child)) ::
        labels.map fun channel => negative (.internal (.qualifier side channel)))
  | .liveAnd left right => .and
      [internal parameters (.decoder side (parameters.decoder.childIndex index left)),
        internal parameters (.decoder side (parameters.decoder.childIndex index right))]

/-- The raw layout rebuilds the enable/request/prior-mask conjunction at each stage. -/
def rawTermInputs (parameters : Parameters) (side : Side) (bus : Fin parameters.buses)
    (channel : Fin parameters.channels) : List (Lit parameters) :=
  [enable parameters channel, request parameters bus channel] ++
    ((List.finRange parameters.buses).filter (fun earlier => earlier < bus)).map
      (fun earlier => internal parameters (.mask side earlier channel))

/-- The shared layout reads the separately defined prefix accumulator. -/
def termGate (parameters : Parameters) (side : Side) (bus : Fin parameters.buses)
    (channel : Fin parameters.channels) : CNF.Gate (Variable parameters) :=
  match layoutEquation : parameters.layout with
  | .raw => .and (rawTermInputs parameters side bus channel)
  | .shared => .and
      [internal parameters (.active side ⟨bus.val, by simpa [layoutEquation, PrefixLayout.activeCount] using bus.isLt⟩ channel),
        request parameters bus channel]

/-- Define only the shared layout's actual accumulator roles. -/
def activeGate (parameters : Parameters) (side : Side)
    (bus : Fin (parameters.layout.activeCount parameters.buses))
    (channel : Fin parameters.channels) : CNF.Gate (Variable parameters) :=
  match layoutEquation : parameters.layout with
  | .raw => False.elim (Nat.not_lt_zero bus.val (by simpa [layoutEquation, PrefixLayout.activeCount] using bus.isLt))
  | .shared =>
      if first : bus.val = 0 then .alias (enable parameters channel)
      else .and
        [internal parameters (.active side ⟨bus.val - 1, by omega⟩ channel),
          internal parameters (.mask side ⟨bus.val - 1, by
            have bound : bus.val < parameters.buses := by
              simpa [layoutEquation, PrefixLayout.activeCount] using bus.isLt
            omega⟩ channel)]

/-- The actual native gate defining each role, with no primary-input assertions. -/
def gate (parameters : Parameters) : Internal parameters → CNF.Gate (Variable parameters)
  | .driver => .and (parameters.bridge.drivers.sort.map fun channel =>
      internal parameters (.absent .healthy parameters.firstBus channel))
  | .remaining => .and (parameters.bridge.remaining.sort.map fun channel =>
      internal parameters (.absent .healthy parameters.firstBus channel))
  | .firstProduct side => .and
      [match side with
       | .healthy => targetAbsent parameters
       | .faulty => positive (.primary .wire),
       internal parameters .driver, internal parameters .remaining]
  | .term side bus channel => termGate parameters side bus channel
  | .absent side bus channel => .not (internal parameters (.term side bus channel))
  | .flag side bus =>
      if bus.val = 0 then .not (internal parameters (.firstProduct side))
      else .or ((List.finRange parameters.channels).map fun channel =>
        internal parameters (.term side bus channel))
  | .mask side bus channel => .xor (internal parameters (.flag side bus))
      (internal parameters (.absent side bus channel))
  | .active side bus channel => activeGate parameters side bus channel
  | .qualifierGuard side bus channel => .or
      [negative (.internal (.flag side bus)), request parameters bus channel]
  | .qualifier side channel => .and
      (enable parameters channel :: (List.finRange parameters.buses).map fun bus =>
        internal parameters (.qualifierGuard side bus channel))
  | .decoder side index => decoderGate parameters side index
  | .difference output => .xor
      (internal parameters (.decoder .healthy (parameters.decoder.roots.get output)))
      (internal parameters (.decoder .faulty (parameters.decoder.roots.get output)))
  | .detected => .or ((List.finRange parameters.decoder.roots.length).map fun output =>
      internal parameters (.difference output))

/-- The four and only four assertions: the drive interface and an observed discrepancy. -/
def assertions (parameters : Parameters) : List (Lit parameters) :=
  [(parameters.targetAbsent.1, !parameters.drive),
    (.internal .driver, parameters.drive), (.primary .wire, parameters.drive),
    internal parameters .detected]

def equationClauses (parameters : Parameters) : List (CNF.Clause (Variable parameters)) :=
  parameters.roles.flatMap fun role => (parameters.gate role).clauses (internal parameters role)

def equationFormula (parameters : Parameters) : CNF.Formula (Variable parameters) :=
  CNF.ofClauses parameters.equationClauses

def assertionFormula (parameters : Parameters) : CNF.Formula (Variable parameters) :=
  CNF.ofClauses (parameters.assertions.map fun literal => [literal])

/-- Complete equation rows followed by the four explicit assertion rows. -/
def specificationFormula (parameters : Parameters) : CNF.Formula (Variable parameters) :=
  parameters.equationFormula ++ parameters.assertionFormula

/-- A strict dependency rank for all actual native output roles. -/
def rank (parameters : Parameters) : Internal parameters → ℕ
  | .driver | .remaining => 3
  | .firstProduct _ => 4
  | .term _ bus _ => 8 * bus.val + 1
  | .absent _ bus _ => 8 * bus.val + 2
  | .flag _ bus => 8 * bus.val + 5
  | .mask _ bus _ => 8 * bus.val + 6
  | .active _ bus _ => 8 * bus.val
  | .qualifierGuard _ _ _ => 8 * parameters.buses + 1
  | .qualifier _ _ => 8 * parameters.buses + 2
  | .decoder _ index => 8 * parameters.buses + 3 + index.val
  | .difference _ => 8 * parameters.buses + 3 + parameters.decoder.nodeCount
  | .detected => 8 * parameters.buses + 4 + parameters.decoder.nodeCount

def primaryAssignment {n b : ℕ} (input : Physical.PrimaryInput n b) (wire : Bool) :
    PrimaryRole n b → Bool
  | .enable channel => input.enable channel
  | .request bus channel => input.request bus channel
  | .wire => wire

/-- Read every independent primary slot; unused enables and requests are retained. -/
def primaryInput (parameters : Parameters) (roots : PrimaryRole parameters.channels parameters.buses → Bool) :
    Physical.PrimaryInput parameters.channels parameters.buses where
  positiveBuses := parameters.positiveBuses
  enable := fun channel => roots (.enable channel)
  request := fun bus channel => roots (.request bus channel)

def selectorRun (parameters : Parameters) (input : Physical.PrimaryInput parameters.channels parameters.buses)
    (wire : Bool) : Side → Physical.SelectorRun parameters.channels parameters.buses
  | .healthy => Physical.healthyRun input
  | .faulty => Physical.runFromFirst input (Physical.bridgeFirstFlag parameters.bridge input wire)

def qualifiers (parameters : Parameters) (input : Physical.PrimaryInput parameters.channels parameters.buses)
    (wire : Bool) (side : Side) : Assignment parameters.channels :=
  Physical.qualifiers input.enable input.request (parameters.selectorRun input wire side).flags

/-- The concrete physical semantics assigned to every named output role. -/
def roleValue (parameters : Parameters) (input : Physical.PrimaryInput parameters.channels parameters.buses)
    (wire : Bool) : Internal parameters → Bool
  | .driver => Physical.bridgeD parameters.bridge input
  | .remaining => Physical.bridgeR parameters.bridge input
  | .firstProduct side =>
      (match side with | .healthy => Physical.bridgeU parameters.bridge input | .faulty => wire) &&
        Physical.bridgeD parameters.bridge input && Physical.bridgeR parameters.bridge input
  | .term side bus channel => (parameters.selectorRun input wire side).terms bus channel
  | .absent side bus channel => !(parameters.selectorRun input wire side).terms bus channel
  | .flag side bus => (parameters.selectorRun input wire side).flags bus
  | .mask side bus channel => (parameters.selectorRun input wire side).masks bus channel
  | .active side bus channel =>
      match layoutEquation : parameters.layout with
      | .raw => False.elim (Nat.not_lt_zero bus.val (by
          simpa [layoutEquation, PrefixLayout.activeCount] using bus.isLt))
      | .shared => (parameters.selectorRun input wire side).activeBefore
          ⟨bus.val, by simpa [layoutEquation, PrefixLayout.activeCount] using bus.isLt⟩ channel
  | .qualifierGuard side bus channel =>
      !(parameters.selectorRun input wire side).flags bus || input.request bus channel
  | .qualifier side channel => parameters.qualifiers input wire side channel
  | .decoder side index => parameters.decoder.eval (parameters.qualifiers input wire side) index
  | .difference output =>
      parameters.decoder.eval (parameters.qualifiers input wire .healthy) (parameters.decoder.roots.get output) ^^
        parameters.decoder.eval (parameters.qualifiers input wire .faulty) (parameters.decoder.roots.get output)
  | .detected => parameters.decoder.roots.any fun root =>
      parameters.decoder.eval (parameters.qualifiers input wire .healthy) root ^^
        parameters.decoder.eval (parameters.qualifiers input wire .faulty) root

/-- A shared accumulator role denotes the physical prefix at the same bus. -/
theorem roleValue_active_shared (parameters : Parameters)
    (input : Physical.PrimaryInput parameters.channels parameters.buses) (wire : Bool)
    (side : Side) (bus : Fin (parameters.layout.activeCount parameters.buses))
    (channel : Fin parameters.channels) (shared : parameters.layout = .shared) :
    parameters.roleValue input wire (.active side bus channel) =
      (parameters.selectorRun input wire side).activeBefore
        ⟨bus.val, by simpa [shared, PrefixLayout.activeCount] using bus.isLt⟩ channel := by
  rcases parameters with ⟨n, b, positive, bridge, decoder, layout, drive⟩
  cases layout with
  | raw => cases shared
  | shared => rfl

def physicalAssignment (parameters : Parameters)
    (input : Physical.PrimaryInput parameters.channels parameters.buses) (wire : Bool) :
    Variable parameters → Bool
  | .primary role => primaryAssignment input wire role
  | .internal role => parameters.roleValue input wire role

/-- Output functions use exactly the decoder's stored root incidences. -/
def observations (parameters : Parameters) :
    Fin parameters.decoder.roots.length → Assignment parameters.channels → Bool :=
  fun output assignment => parameters.decoder.eval assignment (parameters.decoder.roots.get output)


@[simp] theorem literalValue_positive (assignment : Variable parameters → Bool)
    (slot : Variable parameters) :
    CNF.literalValue assignment (positive slot) = assignment slot := by
  simp [CNF.literalValue, positive]

@[simp] theorem literalValue_negative (assignment : Variable parameters → Bool)
    (slot : Variable parameters) :
    CNF.literalValue assignment (negative slot) = !assignment slot := by
  simp [CNF.literalValue, negative]

/-- Conjunction and disjunction preserve agreement on their actual input incidences. -/
private theorem gate_eval_congr (producer : CNF.Gate α) (left right : α → Bool)
    (agreement : ∀ literal ∈ producer.inputs,
      CNF.literalValue left literal = CNF.literalValue right literal) :
    producer.eval left = producer.eval right := by
  cases producer with
  | and inputs =>
      apply Bool.eq_iff_iff.mpr
      simp only [CNF.Gate.eval, List.all_eq_true]
      constructor
      · intro satisfied literal membership
        rw [← agreement literal membership]
        exact satisfied literal membership
      · intro satisfied literal membership
        rw [agreement literal membership]
        exact satisfied literal membership
  | or inputs =>
      apply Bool.eq_iff_iff.mpr
      simp only [CNF.Gate.eval, List.any_eq_true]
      constructor
      · rintro ⟨literal, membership, satisfied⟩
        exact ⟨literal, membership, (agreement literal membership).symm.trans satisfied⟩
      · rintro ⟨literal, membership, satisfied⟩
        exact ⟨literal, membership, (agreement literal membership).trans satisfied⟩
  | xor leftInput rightInput =>
      simp only [CNF.Gate.eval]
      rw [agreement leftInput (by simp [CNF.Gate.inputs]),
        agreement rightInput (by simp [CNF.Gate.inputs])]
  | «alias» input => exact agreement input (by simp [CNF.Gate.inputs])
  | not input => exact congrArg Bool.not (agreement input (by simp [CNF.Gate.inputs]))
  | constant value => rfl

/-- Complete rows impose exactly one defining equation for each internal role. -/
theorem equationFormula_iff (parameters : Parameters) (assignment : Variable parameters → Bool) :
    CNF.Satisfies assignment parameters.equationFormula ↔
      ∀ role, assignment (.internal role) = (parameters.gate role).eval assignment := by
  constructor
  · intro satisfied role
    have localRows : CNF.Satisfies assignment
        ((parameters.gate role).block (internal parameters role)) := by
      rw [CNF.Gate.block, CNF.satisfies_ofClauses]
      intro row membership
      exact (CNF.satisfies_ofClauses assignment parameters.equationClauses).mp satisfied row
        (List.mem_flatMap.mpr ⟨role, mem_roles parameters role, membership⟩)
    simpa [internal] using
      (CNF.Gate.block_correct assignment (internal parameters role) (parameters.gate role)).mp localRows
  · intro equations
    rw [equationFormula, CNF.satisfies_ofClauses]
    intro row membership
    obtain ⟨role, _, memberBlock⟩ := List.mem_flatMap.mp membership
    have localRows := (CNF.Gate.block_correct assignment (internal parameters role)
      (parameters.gate role)).mpr (by simpa [internal] using equations role)
    exact (CNF.satisfies_ofClauses assignment
      ((parameters.gate role).clauses (internal parameters role))).mp localRows row memberBlock

private theorem runMasks_flags_none {n : ℕ} (b : ℕ) (active : Assignment n)
    (requests : Fin b → Assignment n) (bus : Fin b) :
    (Physical.runMasks b active requests none).flags bus =
      Physical.anyTrue ((Physical.runMasks b active requests none).terms bus) := by
  induction b generalizing active with
  | zero => exact Fin.elim0 bus
  | succ b inductionHypothesis =>
      refine Fin.cases ?_ (fun next => ?_) bus
      · rfl
      · exact inductionHypothesis _ _ next

private theorem runMasks_flags_after_first {n : ℕ} (b : ℕ) (active : Assignment n)
    (requests : Fin b → Assignment n) (override : Option Bool)
    (bus : Fin b) (nonfirst : bus.val ≠ 0) :
    (Physical.runMasks b active requests override).flags bus =
      Physical.anyTrue ((Physical.runMasks b active requests override).terms bus) := by
  cases b with
  | zero => exact Fin.elim0 bus
  | succ b =>
      revert nonfirst
      refine Fin.cases ?_ (fun next => ?_) bus
      · intro impossible
        exact (impossible rfl).elim
      · intro _
        exact runMasks_flags_none b _ _ next

/-- A local request is the literal enable/request/prior-mask conjunction. -/
theorem selectorRun_terms_true_iff (parameters : Parameters)
    (input : Physical.PrimaryInput parameters.channels parameters.buses) (wire : Bool)
    (side : Side) (bus : Fin parameters.buses) (channel : Fin parameters.channels) :
    (parameters.selectorRun input wire side).terms bus channel = true ↔
      input.enable channel = true ∧ input.request bus channel = true ∧
        ∀ earlier : Fin parameters.buses, earlier < bus →
          (parameters.selectorRun input wire side).masks earlier channel = true := by
  cases side <;> exact Physical.runMasks_terms_true_iff ..

/-- Both copies have the same first local requests, before any overridden flag is read. -/
theorem selectorRun_first_terms (parameters : Parameters)
    (input : Physical.PrimaryInput parameters.channels parameters.buses) (wire : Bool)
    (side : Side) (channel : Fin parameters.channels) :
    (parameters.selectorRun input wire side).terms parameters.firstBus channel =
      Physical.firstTerms input channel := by
  apply Bool.eq_iff_iff.mpr
  rw [selectorRun_terms_true_iff]
  simp [firstBus, Physical.firstTerms, Physical.stageTerms, Physical.PrimaryInput.firstBus, Fin.lt_def]

private theorem selectorRun_prefix_true_iff (parameters : Parameters)
    (input : Physical.PrimaryInput parameters.channels parameters.buses) (wire : Bool)
    (side : Side) (bus : Fin parameters.buses) (channel : Fin parameters.channels) :
    (parameters.selectorRun input wire side).activeBefore bus channel = true ↔
      input.enable channel = true ∧ ∀ earlier : Fin parameters.buses, earlier < bus →
        (parameters.selectorRun input wire side).masks earlier channel = true := by
  cases side <;> exact Physical.runMasks_activeBefore_true_iff ..

private theorem selectorRun_prefix_first (parameters : Parameters)
    (input : Physical.PrimaryInput parameters.channels parameters.buses) (wire : Bool)
    (side : Side) (bus : Fin parameters.buses) (channel : Fin parameters.channels)
    (first : bus.val = 0) :
    (parameters.selectorRun input wire side).activeBefore bus channel = input.enable channel := by
  apply Bool.eq_iff_iff.mpr
  rw [selectorRun_prefix_true_iff]
  have noEarlier : ∀ earlier : Fin parameters.buses, ¬earlier < bus := by
    intro earlier
    change ¬earlier.val < bus.val
    omega
  simp [noEarlier]

private theorem selectorRun_prefix_step (parameters : Parameters)
    (input : Physical.PrimaryInput parameters.channels parameters.buses) (wire : Bool)
    (side : Side) (bus previous : Fin parameters.buses) (channel : Fin parameters.channels)
    (adjacent : bus.val = previous.val + 1) :
    (parameters.selectorRun input wire side).activeBefore bus channel =
      ((parameters.selectorRun input wire side).activeBefore previous channel &&
        (parameters.selectorRun input wire side).masks previous channel) := by
  apply Bool.eq_iff_iff.mpr
  rw [selectorRun_prefix_true_iff, Bool.and_eq_true, selectorRun_prefix_true_iff]
  constructor
  · rintro ⟨enabled, priorMasks⟩
    refine ⟨⟨enabled, fun earlier before => priorMasks earlier ?_⟩, priorMasks previous ?_⟩
    · change earlier.val < bus.val
      have : earlier.val < previous.val := before
      omega
    · change previous.val < bus.val
      omega
  · rintro ⟨⟨enabled, priorMasks⟩, lastMask⟩
    refine ⟨enabled, fun earlier before => ?_⟩
    by_cases same : earlier = previous
    · simpa [same] using lastMask
    · apply priorMasks earlier
      have before' : earlier.val < bus.val := before
      have different : earlier.val ≠ previous.val := fun equality => same (Fin.ext equality)
      change earlier.val < previous.val
      omega

private theorem termGate_correct (parameters : Parameters)
    (input : Physical.PrimaryInput parameters.channels parameters.buses) (wire : Bool)
    (side : Side) (bus : Fin parameters.buses) (channel : Fin parameters.channels) :
    parameters.roleValue input wire (.term side bus channel) =
      (parameters.termGate side bus channel).eval (parameters.physicalAssignment input wire) := by
  unfold termGate
  split
  · apply Bool.eq_iff_iff.mpr
    simp only [roleValue, selectorRun_terms_true_iff, CNF.Gate.eval, rawTermInputs,
      List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
      List.all_map, Function.comp_def, List.all_eq_true, List.mem_filter, List.mem_finRange, true_and,
      decide_eq_true_eq, internal, enable, request, literalValue_positive,
      physicalAssignment, primaryAssignment]
    exact and_assoc.symm
  · rename_i shared
    have equation : (parameters.selectorRun input wire side).terms bus =
        Physical.stageTerms ((parameters.selectorRun input wire side).activeBefore bus)
          (input.request bus) := by
      cases side <;> exact Physical.runMasks_terms_eq ..
    change (parameters.selectorRun input wire side).terms bus channel = _
    simp only [CNF.Gate.eval, List.all_cons, List.all_nil, Bool.and_true,
      internal, request, literalValue_positive, physicalAssignment, primaryAssignment]
    rw [roleValue_active_shared parameters input wire side _ channel shared]
    exact congrFun equation channel

private theorem activeGate_correct (parameters : Parameters)
    (input : Physical.PrimaryInput parameters.channels parameters.buses) (wire : Bool)
    (side : Side) (bus : Fin (parameters.layout.activeCount parameters.buses))
    (channel : Fin parameters.channels) :
    parameters.roleValue input wire (.active side bus channel) =
      (parameters.activeGate side bus channel).eval (parameters.physicalAssignment input wire) := by
  unfold activeGate
  split
  · rename_i raw
    have := bus.isLt
    simp [raw, PrefixLayout.activeCount] at this
  · rename_i shared
    rw [roleValue_active_shared parameters input wire side bus channel shared]
    split
    · rename_i first
      simpa [CNF.Gate.eval, enable, physicalAssignment, primaryAssignment] using
        selectorRun_prefix_first parameters input wire side
          ⟨bus.val, by simpa [shared, PrefixLayout.activeCount] using bus.isLt⟩ channel first
    · rename_i nonfirst
      have bound : bus.val < parameters.buses := by
        simpa [shared, PrefixLayout.activeCount] using bus.isLt
      simp only [CNF.Gate.eval, List.all_cons, List.all_nil, Bool.and_true,
        internal, literalValue_positive, physicalAssignment]
      rw [roleValue_active_shared parameters input wire side _ channel shared]
      change (parameters.selectorRun input wire side).activeBefore ⟨bus.val, bound⟩ channel =
        ((parameters.selectorRun input wire side).activeBefore ⟨bus.val - 1, by omega⟩ channel &&
          (parameters.selectorRun input wire side).masks ⟨bus.val - 1, by omega⟩ channel)
      apply selectorRun_prefix_step
      dsimp
      omega

private theorem decoderGate_correct (parameters : Parameters)
    (input : Physical.PrimaryInput parameters.channels parameters.buses) (wire : Bool)
    (side : Side) (index : Fin parameters.decoder.nodeCount) :
    parameters.roleValue input wire (.decoder side index) =
      (parameters.decoderGate side index).eval (parameters.physicalAssignment input wire) := by
  have equation := parameters.decoder.eval_eq (parameters.qualifiers input wire side) index
  rw [roleValue, equation]
  unfold decoderGate
  cases parameters.decoder.node index with
  | zero => rfl
  | input channel => simp [Decoder.Gate.eval, CNF.Gate.eval, internal, physicalAssignment, roleValue]
  | disj children => simp [Decoder.Gate.eval, CNF.Gate.eval, internal, physicalAssignment, roleValue, List.any_map, Function.comp_def]
  | guard child labels =>
      simp only [Decoder.Gate.eval, CNF.Gate.eval, List.all_cons, List.all_map,
        internal, literalValue_positive, physicalAssignment, roleValue]
      congr 1
      apply Bool.eq_iff_iff.mpr
      simp [List.all_eq_true, List.any_eq_false, Function.comp_def, physicalAssignment, roleValue]
  | liveAnd left right =>
      simp [Decoder.Gate.eval, CNF.Gate.eval, internal, physicalAssignment, roleValue]

/-- The canonical valuation satisfies every native producer, for all free root values. -/
theorem roleValue_gate (parameters : Parameters)
    (input : Physical.PrimaryInput parameters.channels parameters.buses) (wire : Bool)
    (role : Internal parameters) :
    parameters.roleValue input wire role =
      (parameters.gate role).eval (parameters.physicalAssignment input wire) := by
  cases role with
  | driver =>
      apply Bool.eq_iff_iff.mpr
      simp [gate, roleValue, CNF.Gate.eval, List.all_eq_true, internal,
        physicalAssignment, selectorRun_first_terms, Physical.bridgeD]
  | remaining =>
      apply Bool.eq_iff_iff.mpr
      simp [gate, roleValue, CNF.Gate.eval, List.all_eq_true, internal,
        physicalAssignment, selectorRun_first_terms, Physical.bridgeR]
  | firstProduct side =>
      cases side <;>
        simp [gate, roleValue, CNF.Gate.eval, targetAbsent, internal, physicalAssignment,
          primaryAssignment, selectorRun_first_terms, Physical.bridgeU, Bool.and_assoc]
  | term side bus channel => exact termGate_correct parameters input wire side bus channel
  | absent side bus channel => simp [gate, roleValue, CNF.Gate.eval, internal, physicalAssignment]
  | flag side bus =>
      simp only [gate]
      split
      · rename_i first
        have equality : bus = parameters.firstBus := Fin.ext first
        subst bus
        cases side with
        | healthy =>
            simpa [roleValue, CNF.Gate.eval, internal, physicalAssignment, selectorRun, firstBus,
              Physical.PrimaryInput.firstBus] using
              (Physical.healthyRun_firstFlag input).trans
                (Physical.firstFlag_eq_cofactor parameters.bridge input)
        | faulty =>
            simpa [roleValue, CNF.Gate.eval, internal, physicalAssignment, selectorRun, firstBus,
              Physical.PrimaryInput.firstBus, Physical.bridgeFirstFlag] using
              Physical.runFromFirst_firstFlag input (Physical.bridgeFirstFlag parameters.bridge input wire)
      · rename_i nonfirst
        have equation : (parameters.selectorRun input wire side).flags bus =
            Physical.anyTrue ((parameters.selectorRun input wire side).terms bus) := by
          cases side <;> exact runMasks_flags_after_first _ _ _ _ bus nonfirst
        rw [roleValue, equation]
        apply Bool.eq_iff_iff.mpr
        simp [CNF.Gate.eval, internal, physicalAssignment, roleValue, List.any_eq_true]
  | mask side bus channel =>
      have equation : (parameters.selectorRun input wire side).masks bus =
          Physical.stageMask ((parameters.selectorRun input wire side).flags bus)
            ((parameters.selectorRun input wire side).terms bus) := by
        cases side <;> exact Physical.runMasks_masks_eq ..
      simpa [gate, roleValue, CNF.Gate.eval, internal, physicalAssignment,
        Physical.stageMask] using congrFun equation channel
  | active side bus channel => exact activeGate_correct parameters input wire side bus channel
  | qualifierGuard side bus channel =>
      simp [gate, roleValue, CNF.Gate.eval, request, physicalAssignment, primaryAssignment]
  | qualifier side channel =>
      apply Bool.eq_iff_iff.mpr
      simp only [gate, roleValue, CNF.Gate.eval, List.all_cons, List.all_map, Function.comp_def,
        Bool.and_eq_true, List.all_eq_true, List.mem_finRange, forall_const,
        internal, enable, literalValue_positive, physicalAssignment, primaryAssignment,
        qualifiers, Physical.qualifiers_eq_true]
      apply and_congr Iff.rfl
      apply forall_congr'
      intro bus
      cases (parameters.selectorRun input wire side).flags bus <;> simp
  | decoder side index => exact decoderGate_correct parameters input wire side index
  | difference output => simp [gate, roleValue, CNF.Gate.eval, internal, physicalAssignment]
  | detected =>
      apply Bool.eq_iff_iff.mpr
      simp only [gate, roleValue, CNF.Gate.eval, List.any_map, Function.comp_def, internal,
        literalValue_positive, physicalAssignment, List.any_eq_true, List.mem_finRange, true_and]
      constructor
      · rintro ⟨root, membership, value⟩
        obtain ⟨index, rfl⟩ := List.mem_iff_get.mp membership
        exact ⟨index, value⟩
      · rintro ⟨index, value⟩
        exact ⟨_, List.get_mem .., value⟩

/-- Native equations admit a model for every complete enable/request/W assignment. -/
theorem physicalAssignment_satisfies_equations (parameters : Parameters)
    (input : Physical.PrimaryInput parameters.channels parameters.buses) (wire : Bool) :
    CNF.Satisfies (parameters.physicalAssignment input wire) parameters.equationFormula :=
  (equationFormula_iff parameters _).mpr (parameters.roleValue_gate input wire)


/-- Primary slots are unrestricted leaves; internal dependencies have smaller rank. -/
def Earlier (parameters : Parameters) (parent : Internal parameters) (literal : Lit parameters) : Prop :=
  match literal.1 with
  | .primary _ => True
  | .internal child => parameters.rank child < parameters.rank parent

/-- The displayed rank checks the actual inputs of every native producer. -/
theorem gate_inputs_earlier (parameters : Parameters) (role : Internal parameters) :
    ∀ literal ∈ (parameters.gate role).inputs, parameters.Earlier role literal := by
  intro literal membership
  cases role with
  | driver =>
      change literal ∈ (parameters.bridge.drivers.sort.map fun channel =>
        internal parameters (.absent .healthy parameters.firstBus channel)) at membership
      obtain ⟨channel, _, rfl⟩ := List.mem_map.mp membership
      simp [Earlier, internal, positive, rank, firstBus]
  | remaining =>
      change literal ∈ (parameters.bridge.remaining.sort.map fun channel =>
        internal parameters (.absent .healthy parameters.firstBus channel)) at membership
      obtain ⟨channel, _, rfl⟩ := List.mem_map.mp membership
      simp [Earlier, internal, positive, rank, firstBus]
  | firstProduct side =>
      cases side <;>
        simp only [gate, CNF.Gate.inputs, List.mem_cons, List.not_mem_nil, or_false] at membership <;>
        rcases membership with rfl | rfl | rfl <;>
        simp [Earlier, internal, positive, targetAbsent, rank, firstBus]
  | term side bus channel =>
      change literal ∈ (parameters.termGate side bus channel).inputs at membership
      unfold termGate at membership
      split at membership
      · simp only [CNF.Gate.inputs, rawTermInputs, List.mem_append, List.mem_cons,
          List.not_mem_nil, or_false, List.mem_map, List.mem_filter, List.mem_finRange,
          true_and, decide_eq_true_eq] at membership
        rcases membership with (rfl | rfl) | ⟨earlier, before, rfl⟩
        · simp [Earlier, enable, positive]
        · simp [Earlier, request, positive]
        · simp only [Earlier, internal, positive, rank]
          have bound : earlier.val < bus.val := before
          omega
      · simp only [CNF.Gate.inputs, List.mem_cons, List.not_mem_nil, or_false] at membership
        rcases membership with rfl | rfl
        · simp [Earlier, internal, positive, rank]
        · simp [Earlier, request, positive]
  | absent side bus channel =>
      simp only [gate, CNF.Gate.inputs, List.mem_singleton] at membership
      subst literal
      simp [Earlier, internal, positive, rank]
  | flag side bus =>
      by_cases first : bus.val = 0
      · simp only [gate, first, ite_eq_left, CNF.Gate.inputs, List.mem_singleton] at membership
        subst literal
        simp [Earlier, internal, positive, rank]
      · change literal ∈ (parameters.gate (.flag side bus)).inputs at membership
        simp only [gate, first, CNF.Gate.inputs] at membership
        obtain ⟨channel, _, rfl⟩ := List.mem_map.mp membership
        simp [Earlier, internal, positive, rank]
  | mask side bus channel =>
      simp only [gate, CNF.Gate.inputs, List.mem_cons, List.not_mem_nil, or_false] at membership
      rcases membership with rfl | rfl <;> simp [Earlier, internal, positive, rank]
  | active side bus channel =>
      change literal ∈ (parameters.activeGate side bus channel).inputs at membership
      unfold activeGate at membership
      split at membership
      · rename_i raw
        have := bus.isLt
        simp [raw, PrefixLayout.activeCount] at this
      · split at membership
        · simp only [CNF.Gate.inputs, List.mem_singleton] at membership
          subst literal
          simp [Earlier, enable, positive]
        · rename_i nonfirst
          simp only [CNF.Gate.inputs, List.mem_cons, List.not_mem_nil, or_false] at membership
          rcases membership with rfl | rfl <;>
            simp only [Earlier, internal, positive, rank] <;> omega
  | qualifierGuard side bus channel =>
      simp only [gate, CNF.Gate.inputs, List.mem_cons, List.not_mem_nil, or_false] at membership
      rcases membership with rfl | rfl
      · simp only [Earlier, negative, rank]
        have bound := bus.isLt
        omega
      · simp [Earlier, request, positive]
  | qualifier side channel =>
      simp only [gate, CNF.Gate.inputs, List.mem_cons, List.mem_map] at membership
      rcases membership with rfl | ⟨bus, _, rfl⟩
      · simp [Earlier, enable, positive]
      · simp [Earlier, internal, positive, rank]
  | decoder side index =>
      change literal ∈ (parameters.decoderGate side index).inputs at membership
      unfold decoderGate at membership
      cases nodeEquation : parameters.decoder.node index with
      | zero => simp [nodeEquation, CNF.Gate.inputs] at membership
      | input channel =>
          simp only [nodeEquation, CNF.Gate.inputs, List.mem_singleton] at membership
          subst literal
          simp [Earlier, internal, positive, rank]
          omega
      | disj children =>
          simp only [nodeEquation, CNF.Gate.inputs, List.mem_map] at membership
          obtain ⟨child, _, rfl⟩ := membership
          simp only [Earlier, internal, positive, rank]
          have earlier := parameters.decoder.childIndex_lt index child
          omega
      | guard child labels =>
          simp only [nodeEquation, CNF.Gate.inputs, List.mem_cons, List.mem_map] at membership
          rcases membership with rfl | ⟨channel, _, rfl⟩
          · simp only [Earlier, internal, positive, rank]
            have earlier := parameters.decoder.childIndex_lt index child
            omega
          · simp only [Earlier, negative, rank]
            omega
      | liveAnd left right =>
          simp only [nodeEquation, CNF.Gate.inputs, List.mem_cons, List.not_mem_nil, or_false] at membership
          have leftEarlier := parameters.decoder.childIndex_lt index left
          have rightEarlier := parameters.decoder.childIndex_lt index right
          rcases membership with rfl | rfl <;>
            simp only [Earlier, internal, positive, rank] <;> omega
  | difference output =>
      simp only [gate, CNF.Gate.inputs, List.mem_cons, List.not_mem_nil, or_false] at membership
      have bound := (parameters.decoder.roots.get output).isLt
      rcases membership with rfl | rfl <;>
        simp only [Earlier, internal, positive, rank] <;> omega
  | detected =>
      simp only [gate, CNF.Gate.inputs, List.mem_map] at membership
      obtain ⟨output, _, rfl⟩ := membership
      simp [Earlier, internal, positive, rank]

/-- Complete equation models agreeing at every free root agree everywhere. -/
theorem equation_model_unique (parameters : Parameters) (left right : Variable parameters → Bool)
    (leftModel : CNF.Satisfies left parameters.equationFormula)
    (rightModel : CNF.Satisfies right parameters.equationFormula)
    (roots : ∀ primary, left (.primary primary) = right (.primary primary)) : left = right := by
  have leftEquations := (parameters.equationFormula_iff left).mp leftModel
  have rightEquations := (parameters.equationFormula_iff right).mp rightModel
  have sameInternal : ∀ role, left (.internal role) = right (.internal role) := by
    intro role
    have ranked : ∀ height, ∀ role, parameters.rank role = height →
        left (.internal role) = right (.internal role) := by
      intro height
      induction height using Nat.strong_induction_on with
      | h height inductionHypothesis =>
          intro parent parentRank
          rw [leftEquations, rightEquations]
          apply gate_eval_congr
          intro literal membership
          have earlier := parameters.gate_inputs_earlier parent literal membership
          rcases literal with ⟨slot, phase⟩
          have value : left slot = right slot := by
            cases slot with
            | primary primary => exact roots primary
            | internal child =>
                exact inductionHypothesis (parameters.rank child)
                  (by simpa [Earlier, parentRank] using earlier) child rfl
          simp only [CNF.literalValue, value]
    exact ranked (parameters.rank role) role rfl
  funext slot
  cases slot with
  | primary primary => exact roots primary
  | internal role => exact sameInternal role

/-- All primary slots, including the independent interface wire, extend uniquely. -/
theorem equations_unique_extension (parameters : Parameters)
    (roots : PrimaryRole parameters.channels parameters.buses → Bool) :
    ∃! assignment : Variable parameters → Bool,
      (∀ primary, assignment (.primary primary) = roots primary) ∧
        CNF.Satisfies assignment parameters.equationFormula := by
  let input := parameters.primaryInput roots
  let assignment := parameters.physicalAssignment input (roots .wire)
  have rootValues : ∀ primary, assignment (.primary primary) = roots primary := by
    intro primary
    cases primary <;> rfl
  have satisfies := parameters.physicalAssignment_satisfies_equations input (roots .wire)
  refine ⟨assignment, ⟨rootValues, satisfies⟩, ?_⟩
  intro other properties
  exact parameters.equation_model_unique other assignment properties.2 satisfies
    (fun primary => (properties.1 primary).trans (rootValues primary).symm)

/-- Exactly the interface and output-change conditions remain after gate evaluation. -/
theorem physicalAssignment_assertions_iff (parameters : Parameters)
    (input : Physical.PrimaryInput parameters.channels parameters.buses) (wire : Bool) :
    CNF.Satisfies (parameters.physicalAssignment input wire) parameters.assertionFormula ↔
      Physical.BridgeInputDetects parameters.bridge parameters.drive parameters.observations input wire := by
  simp only [assertionFormula, CNF.satisfies_ofClauses, List.forall_mem_map,
    CNF.clauseHolds_cons, CNF.clauseHolds_nil, or_false, assertions,
    List.forall_mem_cons, CNF.LiteralHolds,
    targetAbsent, internal, positive, physicalAssignment, roleValue]
  simp only [List.not_mem_nil, false_implies, implies_true, and_true] 
  rw [selectorRun_first_terms]
  change (Physical.bridgeU parameters.bridge input = !parameters.drive ∧
    Physical.bridgeD parameters.bridge input = parameters.drive ∧ wire = parameters.drive ∧
    parameters.decoder.roots.any (fun root =>
      parameters.decoder.eval (parameters.qualifiers input wire .healthy) root ^^
        parameters.decoder.eval (parameters.qualifiers input wire .faulty) root) = true) ↔ _
  unfold Physical.BridgeInputDetects Physical.BridgeInterfaceSatisfied Physical.ObservationsDiffer
  rw [List.any_eq_true]
  have changed : (∃ root ∈ parameters.decoder.roots,
      (parameters.decoder.eval (parameters.qualifiers input wire .healthy) root ^^
        parameters.decoder.eval (parameters.qualifiers input wire .faulty) root) = true) ↔
      ∃ index, parameters.observations index (Physical.healthyQualifiers input) ≠
        parameters.observations index (Physical.bridgeQualifiers parameters.bridge input wire) := by
    constructor
    · rintro ⟨root, membership, value⟩
      obtain ⟨index, rfl⟩ := List.mem_iff_get.mp membership
      refine ⟨index, ?_⟩
      simpa [Bool.xor_iff_ne, observations, qualifiers, selectorRun, Physical.healthyQualifiers,
        Physical.bridgeQualifiers, Physical.qualifiersFromFirst] using value
    · rintro ⟨index, value⟩
      refine ⟨parameters.decoder.roots.get index, List.get_mem _ index, ?_⟩
      simpa [Bool.xor_iff_ne, observations, qualifiers, selectorRun, Physical.healthyQualifiers,
        Physical.bridgeQualifiers, Physical.qualifiersFromFirst] using value
  rw [changed]
  constructor
  · rintro ⟨target, drivers, freeWire, difference⟩
    exact ⟨⟨target, drivers, freeWire⟩, difference⟩
  · rintro ⟨⟨target, drivers, freeWire⟩, difference⟩
    exact ⟨target, drivers, freeWire, difference⟩

/-- Lifting is equivalent to physical detection with exactly these fixed primary inputs. -/
theorem specification_extension_iff (parameters : Parameters)
    (input : Physical.PrimaryInput parameters.channels parameters.buses) (wire : Bool) :
    (∃ assignment : Variable parameters → Bool,
      (∀ primary, assignment (.primary primary) = primaryAssignment input wire primary) ∧
        CNF.Satisfies assignment parameters.specificationFormula) ↔
      Physical.BridgeInputDetects parameters.bridge parameters.drive parameters.observations input wire := by
  constructor
  · rintro ⟨assignment, roots, satisfied⟩
    obtain ⟨equations, assertions⟩ := CNF.satisfies_append _ _ _ |>.mp satisfied
    have equality := parameters.equation_model_unique assignment
      (parameters.physicalAssignment input wire) equations
      (parameters.physicalAssignment_satisfies_equations input wire) roots
    subst assignment
    exact (parameters.physicalAssignment_assertions_iff input wire).mp assertions
  · intro detection
    refine ⟨parameters.physicalAssignment input wire, fun _ => rfl, ?_⟩
    exact (CNF.satisfies_append _ _ _).mpr
      ⟨parameters.physicalAssignment_satisfies_equations input wire,
        (parameters.physicalAssignment_assertions_iff input wire).mpr detection⟩

/-- Every detecting primary assignment has exactly one complete native extension. -/
theorem specification_unique_extension (parameters : Parameters)
    (input : Physical.PrimaryInput parameters.channels parameters.buses) (wire : Bool)
    (detects : Physical.BridgeInputDetects parameters.bridge parameters.drive parameters.observations input wire) :
    ∃! assignment : Variable parameters → Bool,
      (∀ primary, assignment (.primary primary) = primaryAssignment input wire primary) ∧
        CNF.Satisfies assignment parameters.specificationFormula := by
  obtain ⟨assignment, roots, satisfied⟩ :=
    (parameters.specification_extension_iff input wire).mpr detects
  refine ⟨assignment, ⟨roots, satisfied⟩, ?_⟩
  intro other properties
  exact parameters.equation_model_unique other assignment
    ((CNF.satisfies_append _ _ _).mp properties.2).1
    ((CNF.satisfies_append _ _ _).mp satisfied).1
    (fun primary => (properties.1 primary).trans (roots primary).symm)


/-- Every enable, every request and the independent wire are counted. -/
theorem primaryRoles_length (parameters : Parameters) :
    parameters.primaryRoles.length = parameters.channels + parameters.buses * parameters.channels + 1 := by
  simp [primaryRoles, List.map_const', Nat.add_assoc]

/-- Exact named-producer count, before replacing n-ary gates by binary folds. -/
theorem roles_length (parameters : Parameters) :
    parameters.roles.length = 5 + 8 * parameters.buses * parameters.channels +
      2 * parameters.buses + 2 * (parameters.layout.activeCount parameters.buses) * parameters.channels +
      2 * parameters.channels + 2 * parameters.decoder.nodeCount + parameters.decoder.roots.length := by
  simp only [roles, Side.all, List.length_append, List.length_cons, List.length_nil,
    List.length_map, List.length_flatMap, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, List.length_finRange, List.map_const', List.sum_replicate_nat]
  ring

/-- Raw layout count includes each independently rebuilt prefix conjunction. -/
theorem roles_length_raw (parameters : Parameters) (raw : parameters.layout = .raw) :
    parameters.roles.length = 5 + 8 * parameters.buses * parameters.channels +
      2 * parameters.buses + 2 * parameters.channels + 2 * parameters.decoder.nodeCount +
      parameters.decoder.roots.length := by
  simpa [raw, PrefixLayout.activeCount] using parameters.roles_length

/-- Shared layout allocates one explicit prefix accumulator per copy, bus and channel. -/
theorem roles_length_shared (parameters : Parameters) (shared : parameters.layout = .shared) :
    parameters.roles.length = 5 + 10 * parameters.buses * parameters.channels +
      2 * parameters.buses + 2 * parameters.channels + 2 * parameters.decoder.nodeCount +
      parameters.decoder.roots.length := by
  rw [parameters.roles_length, shared]
  simp only [PrefixLayout.activeCount]
  ring

/-- Specification row counts keep every complete block incidence and every assertion row. -/
theorem specificationFormula_rows (parameters : Parameters) :
    parameters.specificationFormula.clauses.size =
      (parameters.roles.map (fun role =>
        ((parameters.gate role).clauses (internal parameters role)).length)).sum + 4 := by
  simp [specificationFormula, equationFormula, equationClauses, assertionFormula,
    assertions, CNF.ofClauses, Controller.CNF.OrderedFormula.Internal.clauses_append]


/-- Every satisfying assignment projects to the physical controller input at its free slots. -/
theorem specification_model_projects (parameters : Parameters)
    (assignment : Variable parameters → Bool)
    (satisfied : CNF.Satisfies assignment parameters.specificationFormula) :
    Physical.BridgeInputDetects parameters.bridge parameters.drive parameters.observations
      (parameters.primaryInput (fun primary => assignment (.primary primary)))
      (assignment (.primary .wire)) := by
  apply (parameters.specification_extension_iff _ _).mp
  refine ⟨assignment, ?_, satisfied⟩
  intro primary
  cases primary <;> rfl

/-- Satisfiability of the named native specification is exactly physical detectability. -/
theorem specification_satisfiable_iff (parameters : Parameters) :
    CNF.Satisfiable parameters.specificationFormula ↔
      Physical.BridgeDetectable (b := parameters.buses) parameters.bridge parameters.drive
        parameters.observations := by
  constructor
  · rintro ⟨assignment, satisfied⟩
    exact ⟨_, _, parameters.specification_model_projects assignment satisfied⟩
  · rintro ⟨input, wire, detects⟩
    obtain ⟨assignment, _, satisfied⟩ := (parameters.specification_extension_iff input wire).mpr detects
    exact ⟨assignment, satisfied⟩


private theorem nodup_grid {α : Type*} {b n : ℕ} (makeRole : Fin b → Fin n → α)
    (injective : ∀ b₁ i₁ b₂ i₂, makeRole b₁ i₁ = makeRole b₂ i₂ → b₁ = b₂ ∧ i₁ = i₂) :
    ((List.finRange b).flatMap fun bus =>
      (List.finRange n).map (makeRole bus)).Nodup := by
  rw [List.nodup_flatMap]
  constructor
  · intro bus _
    exact List.Nodup.map (fun left right equality => (injective _ _ _ _ equality).2)
      (List.nodup_finRange n)
  · apply (List.nodup_finRange b).imp
    intro left right different value leftMember rightMember
    obtain ⟨leftChannel, _, rfl⟩ := List.mem_map.mp leftMember
    obtain ⟨rightChannel, _, equality⟩ := List.mem_map.mp rightMember
    exact different (injective _ _ _ _ equality.symm).1

/-- The explicit primary enumeration never identifies two enable/request/W roles. -/
theorem primaryRoles_nodup (parameters : Parameters) : parameters.primaryRoles.Nodup := by
  have enables : ((List.finRange parameters.channels).map
      (PrimaryRole.enable : Fin parameters.channels → PrimaryRole parameters.channels parameters.buses)).Nodup :=
    List.Nodup.map (by intro left right equality; cases equality; rfl) (List.nodup_finRange _)
  have requests := nodup_grid (PrimaryRole.request (n := parameters.channels) (b := parameters.buses))
    (by intro b₁ i₁ b₂ i₂ equality; cases equality; exact ⟨rfl, rfl⟩)
  simp [primaryRoles, List.nodup_append, enables, requests, forall_and, or_imp, forall_exists_index]
  grind

/-- Each named producer output occurs once, independently of accidental Boolean equalities. -/
theorem roles_nodup (parameters : Parameters) : parameters.roles.Nodup := by
  have terms (side : Side) := nodup_grid
    (Role.term (layout := parameters.layout) (n := parameters.channels)
      (b := parameters.buses) (m := parameters.decoder.nodeCount)
      (q := parameters.decoder.roots.length) side)
    (by intro b₁ i₁ b₂ i₂ equality; cases equality; exact ⟨rfl, rfl⟩)
  have absents (side : Side) := nodup_grid
    (Role.absent (layout := parameters.layout) (n := parameters.channels)
      (b := parameters.buses) (m := parameters.decoder.nodeCount)
      (q := parameters.decoder.roots.length) side)
    (by intro b₁ i₁ b₂ i₂ equality; cases equality; exact ⟨rfl, rfl⟩)
  have masks (side : Side) := nodup_grid
    (Role.mask (layout := parameters.layout) (n := parameters.channels)
      (b := parameters.buses) (m := parameters.decoder.nodeCount)
      (q := parameters.decoder.roots.length) side)
    (by intro b₁ i₁ b₂ i₂ equality; cases equality; exact ⟨rfl, rfl⟩)
  have active (side : Side) := nodup_grid
    (Role.active (layout := parameters.layout) (n := parameters.channels)
      (b := parameters.buses) (m := parameters.decoder.nodeCount)
      (q := parameters.decoder.roots.length) side)
    (by intro b₁ i₁ b₂ i₂ equality; cases equality; exact ⟨rfl, rfl⟩)
  have guards (side : Side) := nodup_grid
    (Role.qualifierGuard (layout := parameters.layout) (n := parameters.channels)
      (b := parameters.buses) (m := parameters.decoder.nodeCount)
      (q := parameters.decoder.roots.length) side)
    (by intro b₁ i₁ b₂ i₂ equality; cases equality; exact ⟨rfl, rfl⟩)
  have flags (side : Side) : ((List.finRange parameters.buses).map
      (Role.flag (layout := parameters.layout) (n := parameters.channels)
        (m := parameters.decoder.nodeCount) (q := parameters.decoder.roots.length) side)).Nodup :=
    List.Nodup.map (by intro left right equality; cases equality; rfl) (List.nodup_finRange _)
  have qualifiers (side : Side) : ((List.finRange parameters.channels).map
      (Role.qualifier (layout := parameters.layout) (b := parameters.buses)
        (m := parameters.decoder.nodeCount) (q := parameters.decoder.roots.length) side)).Nodup :=
    List.Nodup.map (by intro left right equality; cases equality; rfl) (List.nodup_finRange _)
  have decoders (side : Side) : ((List.finRange parameters.decoder.nodeCount).map
      (Role.decoder (layout := parameters.layout) (n := parameters.channels)
        (b := parameters.buses) (q := parameters.decoder.roots.length) side)).Nodup :=
    List.Nodup.map (by intro left right equality; cases equality; rfl) (List.nodup_finRange _)
  have differences : ((List.finRange parameters.decoder.roots.length).map
      (Role.difference (layout := parameters.layout) (n := parameters.channels)
        (b := parameters.buses) (m := parameters.decoder.nodeCount))).Nodup :=
    List.Nodup.map (by intro left right equality; cases equality; rfl) (List.nodup_finRange _)
  simp [roles, Side.all, List.nodup_append, terms, absents, masks, active,
    guards, flags, qualifiers, decoders, differences]
  repeat' apply And.intro
  all_goals grind (splits := 100)

/-- The free and defined variable universes are disjoint by construction. -/
theorem primary_ne_internal (parameters : Parameters)
    (primary : PrimaryRole parameters.channels parameters.buses) (role : Internal parameters) :
    (Variable.primary primary : Variable parameters) ≠ .internal role := by simp


/-- The declared ordered universe allocates each free and defined variable once. -/
theorem variableRoles_nodup (parameters : Parameters) : parameters.variableRoles.Nodup := by
  have primaries : (parameters.primaryRoles.map (Variable.primary (parameters := parameters))).Nodup :=
    List.Nodup.map (by intro left right equality; cases equality; rfl) parameters.primaryRoles_nodup
  have internals : (parameters.roles.map (Variable.internal (parameters := parameters))).Nodup :=
    List.Nodup.map (by intro left right equality; cases equality; rfl) parameters.roles_nodup
  simp [variableRoles, List.nodup_append, primaries, internals]

/-- Exact declared variable count; unused primary slots are not discarded. -/
theorem variableRoles_length (parameters : Parameters) :
    parameters.variableRoles.length = parameters.channels + parameters.buses * parameters.channels + 1 +
      parameters.roles.length := by
  simp [variableRoles, parameters.primaryRoles_length]

end Parameters
end Controller.Native
