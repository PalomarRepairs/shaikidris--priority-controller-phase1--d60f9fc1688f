module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Native.LayoutTransport
public import Controller.CNF.Relabel
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section


namespace Controller.Native.SourceController

/-- Assigned principal handles denote their supplied named values. Unassigned defaults have no meaning. -/
def Cursor.NamedValues (cursor : Cursor parameters) (assignment : ℕ → Bool)
    (values : Controller.Native.Variable parameters → Bool) : Prop :=
  ∀ slot ∈ cursor.assigned, CNF.literalValue assignment (cursor.slots slot) = values slot

/-- Equations for every actual source entry, including private balanced-fold and retained observation entries. -/
def Cursor.Equations (cursor : Cursor parameters) (assignment : ℕ → Bool) : Prop :=
  ∀ entry ∈ cursor.entries,
    CNF.literalValue assignment entry.producer.output = entry.producer.gate.eval assignment

theorem Cursor.namedValues_assign (cursor : Cursor parameters)
    (assignment : ℕ → Bool) (values : Controller.Native.Variable parameters → Bool)
    (slot : Controller.Native.Variable parameters) (handle : CNF.Literal ℕ)
    (prior : cursor.NamedValues assignment values)
    (value : CNF.literalValue assignment handle = values slot) :
    (cursor.assign slot handle).NamedValues assignment values := by
  intro other membership
  simp only [Cursor.assign_assigned, List.mem_append, List.mem_singleton] at membership
  by_cases equal : other = slot
  · subst other
    simpa [Cursor.assign] using value
  · rcases membership with member | impossible
    · simpa [Cursor.assign, equal] using prior other member
    · exact False.elim (equal impossible)

theorem Cursor.namedValues_emit (cursor : Cursor parameters)
    (assignment : ℕ → Bool) (values : Controller.Native.Variable parameters → Bool)
    (owner : Owner parameters) (gate : CNF.Gate ℕ)
    (prior : cursor.NamedValues assignment values) :
    (cursor.emit owner gate).2.NamedValues assignment values := prior

theorem Cursor.equations_emit_prior (cursor : Cursor parameters)
    (assignment : ℕ → Bool) (owner : Owner parameters) (gate : CNF.Gate ℕ)
    (equations : (cursor.emit owner gate).2.Equations assignment) :
    cursor.Equations assignment := by
  intro entry membership
  exact equations entry (by simp [Cursor.emit, membership])

theorem Cursor.equations_emit_output (cursor : Cursor parameters)
    (assignment : ℕ → Bool) (owner : Owner parameters) (gate : CNF.Gate ℕ)
    (equations : (cursor.emit owner gate).2.Equations assignment) :
    CNF.literalValue assignment (cursor.emit owner gate).1 = gate.eval assignment := by
  exact equations ⟨owner, ⟨(cursor.lastID + 1, true), gate⟩⟩ (by simp [Cursor.emit])

theorem Cursor.namedValues_emitNative (cursor : Cursor parameters)
    (assignment : ℕ → Bool) (values : Controller.Native.Variable parameters → Bool)
    (slot : Controller.Native.Variable parameters) (gate : CNF.Gate ℕ)
    (prior : cursor.NamedValues assignment values)
    (equations : (cursor.emitNative slot gate).Equations assignment)
    (value : gate.eval assignment = values slot) :
    (cursor.emitNative slot gate).NamedValues assignment values := by
  apply Cursor.namedValues_assign
  · exact cursor.namedValues_emit assignment values (.native slot) gate prior
  · exact (cursor.equations_emit_output assignment (.native slot) gate equations).trans value

theorem Cursor.equations_foldNative (cursor : Cursor parameters)
    (assignment : ℕ → Bool) (slot : Controller.Native.Variable parameters)
    (junction : Bounded.Junction) (inputs : List (CNF.Literal ℕ))
    (equations : (cursor.foldNative slot junction inputs).Equations assignment) :
    SourceSerialFold.Equations assignment
      (SourceSerialFold.allocate junction cursor.lastID inputs).producers := by
  let allocated := SourceSerialFold.allocate junction cursor.lastID inputs
  let appended : List (Entry parameters) := allocated.producers.zipIdx.map
    (fun pair => Entry.mk (.fold slot pair.2) pair.1)
  have projected : appended.map Entry.producer = allocated.producers := by
    simp only [appended, List.map_map]
    change allocated.producers.zipIdx.map Prod.fst = allocated.producers
    exact List.zipIdx_map_fst 0 allocated.producers
  intro producer membership
  rw [← projected] at membership
  obtain ⟨entry, entryMember, same⟩ := List.mem_map.mp membership
  subst producer
  exact equations entry (by change entry ∈ cursor.entries ++ appended; simp [entryMember])

theorem Cursor.namedValues_foldNative (cursor : Cursor parameters)
    (assignment : ℕ → Bool) (values : Controller.Native.Variable parameters → Bool)
    (slot : Controller.Native.Variable parameters) (junction : Bounded.Junction)
    (inputs : List (CNF.Literal ℕ))
    (prior : cursor.NamedValues assignment values)
    (equations : (cursor.foldNative slot junction inputs).Equations assignment)
    (value : junction.eval assignment inputs = values slot) :
    (cursor.foldNative slot junction inputs).NamedValues assignment values := by
  apply Cursor.namedValues_assign
  · exact prior
  · exact (SourceSerialFold.allocate_eval junction cursor.lastID inputs assignment
      (cursor.equations_foldNative assignment slot junction inputs equations)).trans value

/-- This extracts the exact producer equations from the source CNF, without assuming recognition or physical values. -/
theorem compile_equations_of_satisfied (parameters : Parameters) (assignment : ℕ → Bool)
    (satisfied : CNF.Satisfies assignment (equationFormula parameters)) :
    (compile parameters).Equations assignment :=
  (equationFormula_iff parameters assignment).mp satisfied

/-- Root loading establishes named physical values only for the actually allocated enable/request roots. -/
theorem initial_namedValues (parameters : Parameters) (assignment : ℕ → Bool)
    (values : Controller.Native.Variable parameters → Bool)
    (enable : ∀ channel, assignment (SourceInitialIDs.rootID (b := parameters.buses)
      (.enable channel)) = values (.primary (.enable channel)))
    (request : ∀ bus channel, assignment (SourceInitialIDs.rootID (.request bus channel)) =
      values (.primary (.request bus channel))) :
    (initial parameters).NamedValues assignment values := by
  intro slot membership
  simp only [initial, List.mem_append, List.mem_map, List.mem_flatMap] at membership
  rcases membership with ⟨channel, _, equal⟩ | ⟨channel, _, bus, _, equal⟩
  · subst slot
    simpa [initial, CNF.literalValue] using enable channel
  · subst slot
    simpa [initial, CNF.literalValue] using request bus channel

/-- Stable principal root IDs recover the same physical input at the complete source cursor. -/
theorem compile_primary_physical (parameters : Parameters) (assignment : ℕ → Bool)
    (input : Physical.PrimaryInput parameters.channels parameters.buses) (wire : Bool)
    (enable : ∀ channel, assignment (SourceInitialIDs.rootID (b := parameters.buses)
      (.enable channel)) = input.enable channel)
    (request : ∀ bus channel, assignment (SourceInitialIDs.rootID (.request bus channel)) =
      input.request bus channel) :
    (∀ channel, CNF.literalValue assignment (sourceRoleMap parameters (.primary (.enable channel))) =
      parameters.physicalAssignment input wire (.primary (.enable channel))) ∧
    (∀ bus channel, CNF.literalValue assignment (sourceRoleMap parameters (.primary (.request bus channel))) =
      parameters.physicalAssignment input wire (.primary (.request bus channel))) := by
  constructor
  · intro channel
    rw [sourceRoleMap_enable]
    simpa [CNF.literalValue, Parameters.physicalAssignment, Parameters.primaryAssignment] using enable channel
  · intro bus channel
    rw [sourceRoleMap_request]
    simpa [CNF.literalValue, Parameters.physicalAssignment, Parameters.primaryAssignment] using request bus channel

/-- The shared first term is evaluated once and transports both native-copy values. -/
theorem firstTermStep_namedValues (parameters : Parameters) (cursor : Cursor parameters)
    (channel : Fin parameters.channels) (assignment : ℕ → Bool)
    (input : Physical.PrimaryInput parameters.channels parameters.buses) (wire : Bool)
    (prior : cursor.NamedValues assignment (parameters.physicalAssignment input wire))
    (primary : cursor.PrimaryAssigned)
    (equations : (firstTermStep parameters cursor channel).Equations assignment) :
    (firstTermStep parameters cursor channel).NamedValues assignment
      (parameters.physicalAssignment input wire) := by
  let healthy := Controller.Native.Variable.internal (.term .healthy parameters.firstBus channel)
  let faulty := Controller.Native.Variable.internal (.term .faulty parameters.firstBus channel)
  let gate := CNF.Gate.and [cursor.slots (.primary (.enable channel)),
    cursor.slots (.primary (.request parameters.firstBus channel))]
  let emitted := cursor.emitNative healthy gate
  have gateValue : gate.eval assignment = parameters.physicalAssignment input wire healthy := by
    simp only [gate, CNF.Gate.eval, List.all_cons, List.all_nil, Bool.and_true]
    rw [prior _ (primary.1 channel), prior _ (primary.2 parameters.firstBus channel)]
    simp only [healthy, Parameters.physicalAssignment, Parameters.primaryAssignment, Parameters.roleValue]
    rw [Parameters.selectorRun_first_terms]
    rfl
  have emittedValues : emitted.NamedValues assignment (parameters.physicalAssignment input wire) :=
    cursor.namedValues_emitNative assignment _ healthy gate prior equations gateValue
  apply Cursor.namedValues_assign
  · exact emittedValues
  · have value := emittedValues healthy (by simp [emitted, Cursor.emitNative_assigned])
    simpa [healthy, faulty, Parameters.physicalAssignment, Parameters.roleValue,
      Parameters.selectorRun_first_terms] using value

/-- Producer equations restrict to any retained allocation prefix; private entries are included. -/
theorem Cursor.equations_of_entries_subset (before after : Cursor parameters)
    (assignment : ℕ → Bool) (subset : ∀ entry ∈ before.entries, entry ∈ after.entries)
    (equations : after.Equations assignment) : before.Equations assignment := by
  intro entry membership
  exact equations entry (subset entry membership)

theorem Cursor.equations_assign_prior (cursor : Cursor parameters) (assignment : ℕ → Bool)
    (slot : Controller.Native.Variable parameters) (handle : CNF.Literal ℕ)
    (equations : (cursor.assign slot handle).Equations assignment) :
    cursor.Equations assignment := equations

theorem Cursor.equations_foldNative_prior (cursor : Cursor parameters) (assignment : ℕ → Bool)
    (slot : Controller.Native.Variable parameters) (junction : Bounded.Junction)
    (inputs : List (CNF.Literal ℕ))
    (equations : (cursor.foldNative slot junction inputs).Equations assignment) :
    cursor.Equations assignment := by
  intro entry membership
  exact equations entry (by simp [Cursor.foldNative, Cursor.assign, membership])

/-- The shared first absence producer transports both copies' values from the healthy term handle. -/
theorem firstAbsentStep_namedValues (parameters : Parameters) (cursor : Cursor parameters)
    (channel : Fin parameters.channels) (assignment : ℕ → Bool)
    (input : Physical.PrimaryInput parameters.channels parameters.buses) (wire : Bool)
    (prior : cursor.NamedValues assignment (parameters.physicalAssignment input wire))
    (termAssigned : .internal (.term .healthy parameters.firstBus channel) ∈ cursor.assigned)
    (equations : (firstAbsentStep parameters cursor channel).Equations assignment) :
    (firstAbsentStep parameters cursor channel).NamedValues assignment
      (parameters.physicalAssignment input wire) := by
  let healthy := Controller.Native.Variable.internal (.absent .healthy parameters.firstBus channel)
  let faulty := Controller.Native.Variable.internal (.absent .faulty parameters.firstBus channel)
  let gate := CNF.Gate.not (cursor.slots (.internal (.term .healthy parameters.firstBus channel)))
  let emitted := cursor.emitNative healthy gate
  have gateValue : gate.eval assignment = parameters.physicalAssignment input wire healthy := by
    simp only [gate, CNF.Gate.eval]
    rw [prior _ termAssigned]
    rfl
  have emittedValues : emitted.NamedValues assignment (parameters.physicalAssignment input wire) :=
    cursor.namedValues_emitNative assignment _ healthy gate prior equations gateValue
  apply Cursor.namedValues_assign
  · exact emittedValues
  · have value := emittedValues healthy (by simp [emitted, Cursor.emitNative_assigned])
    simpa [healthy, faulty, Parameters.physicalAssignment, Parameters.roleValue,
      Parameters.selectorRun_first_terms] using value

/-- The four decoder constructors consumed by the direct native source generator. -/
inductive SourceGate (channels available : ℕ) where
  | zero
  | input (channel : Fin channels)
  | disj (children : List (Fin available))
  | guard (child : Fin available) (labels : List (Fin channels))
  deriving DecidableEq, Repr

def SourceGate.toDecoder : SourceGate channels available → Decoder.Gate channels available
  | .zero => .zero
  | .input channel => .input channel
  | .disj children => .disj children
  | .guard child labels => .guard child labels

/-- Grammar compatibility means precisely representability in the original four source constructors. -/
theorem sourceCompatible_iff_sourceGates (parameters : Parameters) :
    SourceCompatible parameters ↔ ∀ node, ∃ source : SourceGate parameters.channels node.val,
      source.toDecoder = parameters.decoder.node node := by
  constructor
  · intro compatible node
    cases equation : parameters.decoder.node node with
    | zero => exact ⟨.zero, rfl⟩
    | input channel => exact ⟨.input channel, rfl⟩
    | disj children => exact ⟨.disj children, rfl⟩
    | guard child labels => exact ⟨.guard child labels, rfl⟩
    | liveAnd left right =>
        have impossible := compatible node
        simp [equation] at impossible
  · intro representable node
    obtain ⟨source, equation⟩ := representable node
    rw [← equation]
    cases source <;> trivial

/-- Original source identification uses its raw mask-prefix layout and accepted four-constructor decoder grammar. -/
def SourceGrammarAccepted (parameters : Parameters) : Prop :=
  parameters.layout = .raw ∧ SourceCompatible parameters

/-- The bridge structure already enforces the source generator's minimum channel count. -/
theorem source_channels_at_least_two (parameters : Parameters) : 2 ≤ parameters.channels := by
  obtain ⟨driver, member⟩ := parameters.bridge.drivers_nonempty
  have different : driver ≠ parameters.bridge.target := by
    intro same
    rw [same] at member
    exact parameters.bridge.target_not_mem member
  by_contra small
  have driverZero : driver.val = 0 := by omega
  have targetZero : parameters.bridge.target.val = 0 := by omega
  exact different (Fin.ext (driverZero.trans targetZero.symm))

/-- Allocation-prefix inclusion through an actual ordered source loop. -/
theorem entries_foldl_contains (items : List α) (step : Cursor parameters → α → Cursor parameters)
    (extendsEntries : ∀ cursor item entry, entry ∈ cursor.entries → entry ∈ (step cursor item).entries)
    (cursor : Cursor parameters) :
    ∀ entry ∈ cursor.entries, entry ∈ (items.foldl step cursor).entries := by
  induction items generalizing cursor with
  | nil => exact fun _ membership => membership
  | cons head tail inductionHypothesis =>
      intro entry membership
      exact inductionHypothesis (step cursor head) entry (extendsEntries cursor head entry membership)

/-- A semantic invariant can be carried through a source loop using equations from its final retained prefix. -/
theorem equations_foldl_induction (items : List α) (step : Cursor parameters → α → Cursor parameters)
    (property : Cursor parameters → Prop) (assignment : ℕ → Bool)
    (extendsEntries : ∀ cursor item entry, entry ∈ cursor.entries → entry ∈ (step cursor item).entries)
    (preserves : ∀ cursor item, property cursor → (step cursor item).Equations assignment →
      property (step cursor item))
    (cursor : Cursor parameters) (initialProperty : property cursor)
    (equations : (items.foldl step cursor).Equations assignment) :
    property (items.foldl step cursor) := by
  induction items generalizing cursor with
  | nil => exact initialProperty
  | cons head tail inductionHypothesis =>
      have nextEquations : (step cursor head).Equations assignment :=
        Cursor.equations_of_entries_subset _ _ assignment
          (entries_foldl_contains tail step extendsEntries (step cursor head)) equations
      exact inductionHypothesis (step cursor head)
        (preserves cursor head initialProperty nextEquations) equations

theorem firstTermStep_entries_contains (parameters : Parameters) (cursor : Cursor parameters)
    (channel : Fin parameters.channels) (entry : Entry parameters) (membership : entry ∈ cursor.entries) :
    entry ∈ (firstTermStep parameters cursor channel).entries := by
  simp [firstTermStep, Cursor.emitNative, Cursor.emit, Cursor.assign, membership]

theorem firstAbsentStep_entries_contains (parameters : Parameters) (cursor : Cursor parameters)
    (channel : Fin parameters.channels) (entry : Entry parameters) (membership : entry ∈ cursor.entries) :
    entry ∈ (firstAbsentStep parameters cursor channel).entries := by
  simp [firstAbsentStep, Cursor.emitNative, Cursor.emit, Cursor.assign, membership]

/-- The entire actual first-term loop realizes the physical first terms, with both aliases retained. -/
theorem firstTerms_namedValues (parameters : Parameters) (assignment : ℕ → Bool)
    (input : Physical.PrimaryInput parameters.channels parameters.buses) (wire : Bool)
    (enable : ∀ channel, assignment (SourceInitialIDs.rootID (b := parameters.buses)
      (.enable channel)) = input.enable channel)
    (request : ∀ bus channel, assignment (SourceInitialIDs.rootID (.request bus channel)) =
      input.request bus channel)
    (equations : (firstTerms parameters).Equations assignment) :
    (firstTerms parameters).NamedValues assignment (parameters.physicalAssignment input wire) := by
  let property := fun cursor : Cursor parameters =>
    cursor.NamedValues assignment (parameters.physicalAssignment input wire) ∧ cursor.PrimaryAssigned
  have initialValues : (initial parameters).NamedValues assignment (parameters.physicalAssignment input wire) :=
    initial_namedValues parameters assignment _
      (by simpa [Parameters.physicalAssignment, Parameters.primaryAssignment] using enable)
      (by simpa [Parameters.physicalAssignment, Parameters.primaryAssignment] using request)
  have result := equations_foldl_induction (List.finRange parameters.channels)
    (firstTermStep parameters) property assignment (firstTermStep_entries_contains parameters)
    (fun cursor channel prior equations => by
      refine ⟨firstTermStep_namedValues parameters cursor channel assignment input wire prior.1 prior.2 equations, ?_⟩
      constructor
      · intro other
        simpa [firstTermStep, Cursor.emitNative_assigned, Cursor.assign_assigned] using
          List.mem_append_left [.internal (.term .faulty parameters.firstBus channel)]
            (List.mem_append_left [.internal (.term .healthy parameters.firstBus channel)] (prior.2.1 other))
      · intro bus other
        simpa [firstTermStep, Cursor.emitNative_assigned, Cursor.assign_assigned] using
          List.mem_append_left [.internal (.term .faulty parameters.firstBus channel)]
            (List.mem_append_left [.internal (.term .healthy parameters.firstBus channel)] (prior.2.2 bus other)))
    (initial parameters) ⟨initialValues, (initial_ready parameters).primary⟩ equations
  exact result.1

/-- Both complete shared first arrays have their physical values under the actual retained source equations. -/
theorem firstArrays_namedValues (parameters : Parameters) (assignment : ℕ → Bool)
    (input : Physical.PrimaryInput parameters.channels parameters.buses) (wire : Bool)
    (enable : ∀ channel, assignment (SourceInitialIDs.rootID (b := parameters.buses)
      (.enable channel)) = input.enable channel)
    (request : ∀ bus channel, assignment (SourceInitialIDs.rootID (.request bus channel)) =
      input.request bus channel)
    (equations : (firstArrays parameters).Equations assignment) :
    (firstArrays parameters).NamedValues assignment (parameters.physicalAssignment input wire) := by
  have eqArrays : firstArrays parameters =
      (List.finRange parameters.channels).foldl (firstAbsentStep parameters) (firstTerms parameters) := rfl
  rw [eqArrays] at equations ⊢
  have termEquations : (firstTerms parameters).Equations assignment :=
    Cursor.equations_of_entries_subset _ _ assignment
      (entries_foldl_contains _ _ (firstAbsentStep_entries_contains parameters) _) equations
  have startTerms : ∀ channel, .internal (.term .healthy parameters.firstBus channel) ∈
      (firstTerms parameters).assigned := by
    intro channel
    rw [firstTerms_assigned]
    apply List.mem_append_right
    exact List.mem_flatMap.mpr ⟨channel, by simp, by simp⟩
  let property := fun cursor : Cursor parameters =>
    cursor.NamedValues assignment (parameters.physicalAssignment input wire) ∧
      (∀ channel, .internal (.term .healthy parameters.firstBus channel) ∈ cursor.assigned)
  have result := equations_foldl_induction (List.finRange parameters.channels)
    (firstAbsentStep parameters) property assignment (firstAbsentStep_entries_contains parameters)
    (fun cursor channel prior equations => by
      refine ⟨firstAbsentStep_namedValues parameters cursor channel assignment input wire prior.1
        (prior.2 channel) equations, ?_⟩
      intro other
      rw [firstAbsentStep_assigned]
      exact List.mem_append_left _ (prior.2 other))
    (firstTerms parameters) ⟨firstTerms_namedValues parameters assignment input wire enable request termEquations,
      startTerms⟩ equations
  exact result.1

/-- Balanced source conjunctions and disjunctions respect the named-value invariant on their actual input incidences. -/
theorem Cursor.junction_eval_named (cursor : Cursor parameters) (assignment : ℕ → Bool)
    (values : Controller.Native.Variable parameters → Bool) (junction : Bounded.Junction)
    (roles : List (Controller.Native.Variable parameters))
    (prior : cursor.NamedValues assignment values)
    (assigned : ∀ role ∈ roles, role ∈ cursor.assigned) :
    junction.eval assignment (roles.map cursor.slots) =
      junction.eval values (roles.map fun role => (role, true)) := by
  cases junction with
  | conjunction =>
      apply Bool.eq_iff_iff.mpr
      simp only [Bounded.Junction.eval, Bounded.Junction.gate, CNF.Gate.eval, List.all_map, Function.comp_def, List.all_eq_true]
      constructor
      · intro satisfied role member
        have value := prior role (assigned role member)
        have equal : values role = true := by
          rw [← value]
          exact satisfied role member
        simpa [CNF.literalValue] using equal
      · intro satisfied role member
        rw [prior role (assigned role member)]
        simpa [CNF.literalValue] using satisfied role member
  | disjunction =>
      apply Bool.eq_iff_iff.mpr
      simp only [Bounded.Junction.eval, Bounded.Junction.gate, CNF.Gate.eval, List.any_map, Function.comp_def, List.any_eq_true]
      constructor
      · rintro ⟨role, member, satisfied⟩
        refine ⟨role, member, ?_⟩
        have equal : values role = true := by
          rw [← prior role (assigned role member)]
          exact satisfied
        simpa [CNF.literalValue] using equal
      · rintro ⟨role, member, satisfied⟩
        refine ⟨role, member, ?_⟩
        rw [prior role (assigned role member)]
        simpa [CNF.literalValue] using satisfied

/-- The actual balanced driver fold has the physical bridge-driver value. -/
theorem driverFold_namedValues (parameters : Parameters) (cursor : Cursor parameters)
    (assignment : ℕ → Bool) (input : Physical.PrimaryInput parameters.channels parameters.buses)
    (wire : Bool) (prior : cursor.NamedValues assignment (parameters.physicalAssignment input wire))
    (absents : ∀ channel, .internal (.absent .healthy parameters.firstBus channel) ∈ cursor.assigned)
    (equations : (cursor.foldNative (.internal .driver) .conjunction
      (parameters.bridge.drivers.sort.map fun channel =>
        cursor.slots (.internal (.absent .healthy parameters.firstBus channel)))).Equations assignment) :
    (cursor.foldNative (.internal .driver) .conjunction
      (parameters.bridge.drivers.sort.map fun channel =>
        cursor.slots (.internal (.absent .healthy parameters.firstBus channel)))).NamedValues assignment
      (parameters.physicalAssignment input wire) := by
  let roles : List (Controller.Native.Variable parameters) := parameters.bridge.drivers.sort.map
    fun channel => .internal (.absent .healthy parameters.firstBus channel)
  apply Cursor.namedValues_foldNative
  · exact prior
  · exact equations
  · have value := cursor.junction_eval_named assignment (parameters.physicalAssignment input wire)
      .conjunction roles prior (by
        intro role member
        obtain ⟨channel, _, equal⟩ := List.mem_map.mp member
        subst role
        exact absents channel)
    simp only [roles, List.map_map, Function.comp_def] at value
    rw [value]
    simpa [roles, Bounded.Junction.eval, Bounded.Junction.gate, CNF.Gate.eval, Parameters.gate, Parameters.internal, Parameters.positive, Parameters.physicalAssignment,
      List.map_map, Function.comp_def] using (parameters.roleValue_gate input wire .driver).symm

/-- The actual balanced remaining-channel fold has the physical bridge-remaining value, including the empty group. -/
theorem remainingFold_namedValues (parameters : Parameters) (cursor : Cursor parameters)
    (assignment : ℕ → Bool) (input : Physical.PrimaryInput parameters.channels parameters.buses)
    (wire : Bool) (prior : cursor.NamedValues assignment (parameters.physicalAssignment input wire))
    (absents : ∀ channel, .internal (.absent .healthy parameters.firstBus channel) ∈ cursor.assigned)
    (equations : (cursor.foldNative (.internal .remaining) .conjunction
      (parameters.bridge.remaining.sort.map fun channel =>
        cursor.slots (.internal (.absent .healthy parameters.firstBus channel)))).Equations assignment) :
    (cursor.foldNative (.internal .remaining) .conjunction
      (parameters.bridge.remaining.sort.map fun channel =>
        cursor.slots (.internal (.absent .healthy parameters.firstBus channel)))).NamedValues assignment
      (parameters.physicalAssignment input wire) := by
  let roles : List (Controller.Native.Variable parameters) := parameters.bridge.remaining.sort.map
    fun channel => .internal (.absent .healthy parameters.firstBus channel)
  apply Cursor.namedValues_foldNative
  · exact prior
  · exact equations
  · have value := cursor.junction_eval_named assignment (parameters.physicalAssignment input wire)
      .conjunction roles prior (by
        intro role member
        obtain ⟨channel, _, equal⟩ := List.mem_map.mp member
        subst role
        exact absents channel)
    simp only [roles, List.map_map, Function.comp_def] at value
    rw [value]
    simpa [roles, Bounded.Junction.eval, Bounded.Junction.gate, CNF.Gate.eval, Parameters.gate, Parameters.internal, Parameters.positive, Parameters.physicalAssignment,
      List.map_map, Function.comp_def] using (parameters.roleValue_gate input wire .remaining).symm

/-- The fresh unary-AND wire producer denotes the physical wire exactly when wire equals the bridge-driver value. -/
theorem wireEmit_namedValues (parameters : Parameters) (cursor : Cursor parameters)
    (assignment : ℕ → Bool) (input : Physical.PrimaryInput parameters.channels parameters.buses)
    (wire : Bool) (prior : cursor.NamedValues assignment (parameters.physicalAssignment input wire))
    (driver : .internal .driver ∈ cursor.assigned)
    (wireDriver : wire = Physical.bridgeD parameters.bridge input)
    (equations : (cursor.emitNative (.primary .wire)
      (.and [cursor.slots (.internal .driver)])).Equations assignment) :
    (cursor.emitNative (.primary .wire) (.and [cursor.slots (.internal .driver)])).NamedValues assignment
      (parameters.physicalAssignment input wire) := by
  apply Cursor.namedValues_emitNative
  · exact prior
  · exact equations
  · simp only [CNF.Gate.eval, List.all_cons, List.all_nil, Bool.and_true]
    rw [prior _ driver]
    simpa [Parameters.physicalAssignment, Parameters.primaryAssignment, Parameters.roleValue] using wireDriver.symm

/-- Actual producer equations restrict across a native assignment-and-emission operation. -/
theorem Cursor.equations_emitNative_prior (cursor : Cursor parameters) (assignment : ℕ → Bool)
    (slot : Controller.Native.Variable parameters) (gate : CNF.Gate ℕ)
    (equations : (cursor.emitNative slot gate).Equations assignment) :
    cursor.Equations assignment := cursor.equations_emit_prior assignment (.native slot) gate equations

/-- A native conjunction consumer transports the actual source gate, using its exact listed principal dependencies. -/
theorem nativeAndEmit_namedValues (parameters : Parameters) (cursor : Cursor parameters)
    (assignment : ℕ → Bool) (input : Physical.PrimaryInput parameters.channels parameters.buses)
    (wire : Bool) (role : Internal parameters) (roles : List (Controller.Native.Variable parameters))
    (nativeGate : parameters.gate role = .and (roles.map fun slot => (slot, true)))
    (prior : cursor.NamedValues assignment (parameters.physicalAssignment input wire))
    (assigned : ∀ slot ∈ roles, slot ∈ cursor.assigned)
    (equations : (cursor.emitNative (.internal role) (.and (roles.map cursor.slots))).Equations assignment) :
    (cursor.emitNative (.internal role) (.and (roles.map cursor.slots))).NamedValues assignment
      (parameters.physicalAssignment input wire) := by
  apply Cursor.namedValues_emitNative
  · exact prior
  · exact equations
  · have value := cursor.junction_eval_named assignment (parameters.physicalAssignment input wire)
      .conjunction roles prior assigned
    have semantic := parameters.roleValue_gate input wire role
    rw [nativeGate] at semantic
    exact value.trans semantic.symm

/-- A native negation consumer transports the exact source NOT producer. -/
theorem nativeNotEmit_namedValues (parameters : Parameters) (cursor : Cursor parameters)
    (assignment : ℕ → Bool) (input : Physical.PrimaryInput parameters.channels parameters.buses)
    (wire : Bool) (role : Internal parameters) (child : Controller.Native.Variable parameters)
    (nativeGate : parameters.gate role = .not (child, true))
    (prior : cursor.NamedValues assignment (parameters.physicalAssignment input wire))
    (assigned : child ∈ cursor.assigned)
    (equations : (cursor.emitNative (.internal role) (.not (cursor.slots child))).Equations assignment) :
    (cursor.emitNative (.internal role) (.not (cursor.slots child))).NamedValues assignment
      (parameters.physicalAssignment input wire) := by
  apply Cursor.namedValues_emitNative
  · exact prior
  · exact equations
  · have semantic := parameters.roleValue_gate input wire role
    rw [nativeGate] at semantic
    simp only [CNF.Gate.eval]
    rw [prior child assigned]
    simpa [CNF.Gate.eval, CNF.literalValue, Parameters.physicalAssignment] using semantic.symm

/-- The complete concrete bridge interface transports physical values with the actual wire-equals-driver constraint. -/
theorem interface_namedValues (parameters : Parameters) (assignment : ℕ → Bool)
    (input : Physical.PrimaryInput parameters.channels parameters.buses) (wire : Bool)
    (enable : ∀ channel, assignment (SourceInitialIDs.rootID (b := parameters.buses)
      (.enable channel)) = input.enable channel)
    (request : ∀ bus channel, assignment (SourceInitialIDs.rootID (.request bus channel)) =
      input.request bus channel)
    (wireDriver : wire = Physical.bridgeD parameters.bridge input)
    (equations : (interface parameters).Equations assignment) :
    (interface parameters).NamedValues assignment (parameters.physicalAssignment input wire) := by
  let first := firstArrays parameters
  let driver := first.foldNative (.internal .driver) .conjunction
    (parameters.bridge.drivers.sort.map fun channel => first.slots (.internal (.absent .healthy parameters.firstBus channel)))
  let remaining := driver.foldNative (.internal .remaining) .conjunction
    (parameters.bridge.remaining.sort.map fun channel => driver.slots (.internal (.absent .healthy parameters.firstBus channel)))
  let wireCursor := remaining.emitNative (.primary .wire) (.and [remaining.slots (.internal .driver)])
  let healthyProduct := wireCursor.emitNative (.internal (.firstProduct .healthy))
    (.and [wireCursor.slots (.internal (.absent .healthy parameters.firstBus parameters.bridge.target)),
      wireCursor.slots (.internal .driver), wireCursor.slots (.internal .remaining)])
  let healthyFlag := healthyProduct.emitNative (.internal (.flag .healthy parameters.firstBus))
    (.not (healthyProduct.slots (.internal (.firstProduct .healthy))))
  let faultyProduct := healthyFlag.emitNative (.internal (.firstProduct .faulty))
    (.and [healthyFlag.slots (.primary .wire), healthyFlag.slots (.internal .driver), healthyFlag.slots (.internal .remaining)])
  have faultyProductEq : faultyProduct.Equations assignment :=
    Cursor.equations_emitNative_prior _ assignment _ _ equations
  have healthyFlagEq : healthyFlag.Equations assignment :=
    Cursor.equations_emitNative_prior _ assignment _ _ faultyProductEq
  have healthyProductEq : healthyProduct.Equations assignment :=
    Cursor.equations_emitNative_prior _ assignment _ _ healthyFlagEq
  have wireEq : wireCursor.Equations assignment :=
    Cursor.equations_emitNative_prior _ assignment _ _ healthyProductEq
  have remainingEq : remaining.Equations assignment :=
    Cursor.equations_emitNative_prior _ assignment _ _ wireEq
  have driverEq : driver.Equations assignment :=
    Cursor.equations_foldNative_prior _ assignment _ _ _ remainingEq
  have firstEq : first.Equations assignment :=
    Cursor.equations_foldNative_prior _ assignment _ _ _ driverEq
  have firstValues := firstArrays_namedValues parameters assignment input wire enable request firstEq
  have firstAbsents : ∀ channel, .internal (.absent .healthy parameters.firstBus channel) ∈ first.assigned := by
    intro channel
    simp [first, firstArrays_assigned, firstArrayRoles]
  have driverValues : driver.NamedValues assignment (parameters.physicalAssignment input wire) :=
    driverFold_namedValues parameters first assignment input wire firstValues firstAbsents driverEq
  have remainingValues : remaining.NamedValues assignment (parameters.physicalAssignment input wire) :=
    remainingFold_namedValues parameters driver assignment input wire driverValues (by
      intro channel
      exact List.mem_append_left _ (firstAbsents channel)) remainingEq
  have wireValues : wireCursor.NamedValues assignment (parameters.physicalAssignment input wire) :=
    wireEmit_namedValues parameters remaining assignment input wire remainingValues
      (by simp [remaining, driver, Cursor.foldNative_assigned]) wireDriver wireEq
  have healthyProductValues : healthyProduct.NamedValues assignment (parameters.physicalAssignment input wire) := by
    apply nativeAndEmit_namedValues parameters wireCursor assignment input wire (.firstProduct .healthy)
      [.internal (.absent .healthy parameters.firstBus parameters.bridge.target), .internal .driver, .internal .remaining]
    · rfl
    · exact wireValues
    · intro slot member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (firstAbsents _)))
      · simp [wireCursor, remaining, driver, Cursor.emitNative_assigned, Cursor.foldNative_assigned]
      · simp [wireCursor, remaining, Cursor.emitNative_assigned, Cursor.foldNative_assigned]
    · exact healthyProductEq
  have healthyFlagValues : healthyFlag.NamedValues assignment (parameters.physicalAssignment input wire) := by
    apply nativeNotEmit_namedValues parameters healthyProduct assignment input wire
      (.flag .healthy parameters.firstBus) (.internal (.firstProduct .healthy))
    · simp [Parameters.gate, Parameters.firstBus, Parameters.internal, Parameters.positive]
    · exact healthyProductValues
    · simp [healthyProduct, Cursor.emitNative_assigned]
    · exact healthyFlagEq
  have faultyProductValues : faultyProduct.NamedValues assignment (parameters.physicalAssignment input wire) := by
    apply nativeAndEmit_namedValues parameters healthyFlag assignment input wire (.firstProduct .faulty)
      [.primary .wire, .internal .driver, .internal .remaining]
    · rfl
    · exact healthyFlagValues
    · intro slot member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl <;>
        simp [healthyFlag, healthyProduct, wireCursor, remaining, driver,
          Cursor.emitNative_assigned, Cursor.foldNative_assigned]
    · exact faultyProductEq
  apply nativeNotEmit_namedValues parameters faultyProduct assignment input wire
    (.flag .faulty parameters.firstBus) (.internal (.firstProduct .faulty))
  · simp [Parameters.gate, Parameters.firstBus, Parameters.internal, Parameters.positive]
  · exact faultyProductValues
  · simp [faultyProduct, Cursor.emitNative_assigned]
  · exact equations

/-- The exact source XOR producer transports a named native XOR role. -/
theorem nativeXorEmit_namedValues (parameters : Parameters) (cursor : Cursor parameters)
    (assignment : ℕ → Bool) (input : Physical.PrimaryInput parameters.channels parameters.buses)
    (wire : Bool) (role : Internal parameters) (left right : Controller.Native.Variable parameters)
    (nativeGate : parameters.gate role = .xor (left, true) (right, true))
    (prior : cursor.NamedValues assignment (parameters.physicalAssignment input wire))
    (leftAssigned : left ∈ cursor.assigned) (rightAssigned : right ∈ cursor.assigned)
    (equations : (cursor.emitNative (.internal role)
      (.xor (cursor.slots left) (cursor.slots right))).Equations assignment) :
    (cursor.emitNative (.internal role) (.xor (cursor.slots left) (cursor.slots right))).NamedValues assignment
      (parameters.physicalAssignment input wire) := by
  apply Cursor.namedValues_emitNative
  · exact prior
  · exact equations
  · have semantic := parameters.roleValue_gate input wire role
    rw [nativeGate] at semantic
    simp only [CNF.Gate.eval]
    rw [prior left leftAssigned, prior right rightAssigned]
    simpa [CNF.Gate.eval, CNF.literalValue, Parameters.physicalAssignment] using semantic.symm

/-- The entire actual initial-mask loop transports physical masks while preserving the first-input availability invariant. -/
theorem initialMasks_namedValues (parameters : Parameters) (side : Side) (cursor : Cursor parameters)
    (assignment : ℕ → Bool) (input : Physical.PrimaryInput parameters.channels parameters.buses)
    (wire : Bool) (prior : cursor.NamedValues assignment (parameters.physicalAssignment input wire))
    (available : cursor.FirstAvailable side)
    (equations : (initialMasks parameters side cursor).Equations assignment) :
    (initialMasks parameters side cursor).NamedValues assignment (parameters.physicalAssignment input wire) ∧
      (initialMasks parameters side cursor).FirstAvailable side := by
  let step := fun state : Cursor parameters => fun channel : Fin parameters.channels =>
    state.emitNative (.internal (.mask side parameters.firstBus channel))
      (.xor (state.slots (.internal (.flag side parameters.firstBus)))
        (state.slots (.internal (.absent side parameters.firstBus channel))))
  let property := fun state : Cursor parameters =>
    state.NamedValues assignment (parameters.physicalAssignment input wire) ∧ state.FirstAvailable side
  apply equations_foldl_induction (List.finRange parameters.channels) step property assignment
  · intro state channel entry member
    simp [step, Cursor.emitNative, Cursor.emit, Cursor.assign, member]
  · intro state channel invariants stageEquations
    refine ⟨?_, state.firstAvailable_emitNative side _ _ invariants.2⟩
    apply nativeXorEmit_namedValues parameters state assignment input wire
      (.mask side parameters.firstBus channel) (.internal (.flag side parameters.firstBus))
      (.internal (.absent side parameters.firstBus channel))
    · rfl
    · exact invariants.1
    · exact invariants.2.1
    · exact invariants.2.2 channel
    · exact stageEquations
  · exact ⟨prior, available⟩
  · exact equations

/-- An exact listed native conjunction transports through the source balanced allocator. -/
theorem nativeAndFold_namedValues (parameters : Parameters) (cursor : Cursor parameters)
    (assignment : ℕ → Bool) (input : Physical.PrimaryInput parameters.channels parameters.buses)
    (wire : Bool) (role : Internal parameters) (roles : List (Controller.Native.Variable parameters))
    (nativeGate : parameters.gate role = .and (roles.map fun slot => (slot, true)))
    (prior : cursor.NamedValues assignment (parameters.physicalAssignment input wire))
    (assigned : ∀ slot ∈ roles, slot ∈ cursor.assigned)
    (equations : (cursor.foldNative (.internal role) .conjunction (roles.map cursor.slots)).Equations assignment) :
    (cursor.foldNative (.internal role) .conjunction (roles.map cursor.slots)).NamedValues assignment
      (parameters.physicalAssignment input wire) := by
  apply Cursor.namedValues_foldNative
  · exact prior
  · exact equations
  · have value := cursor.junction_eval_named assignment (parameters.physicalAssignment input wire)
      .conjunction roles prior assigned
    have semantic := parameters.roleValue_gate input wire role
    rw [nativeGate] at semantic
    exact value.trans semantic.symm

/-- The later source term consumes precisely its enable/request and all earlier mask incidences in the direct raw layout. -/
theorem laterTermStep_namedValues (parameters : Parameters) (side : Side) (bus : Fin parameters.buses)
    (cursor : Cursor parameters) (channel : Fin parameters.channels) (assignment : ℕ → Bool)
    (input : Physical.PrimaryInput parameters.channels parameters.buses) (wire : Bool)
    (raw : parameters.layout = .raw)
    (prior : cursor.NamedValues assignment (parameters.physicalAssignment input wire))
    (primary : cursor.PrimaryAssigned) (before : cursor.MasksBefore side bus)
    (equations : (laterTermStep parameters side bus cursor channel).Equations assignment) :
    (laterTermStep parameters side bus cursor channel).NamedValues assignment
      (parameters.physicalAssignment input wire) := by
  let roles : List (Controller.Native.Variable parameters) :=
    [.primary (.enable channel), .primary (.request bus channel)] ++
      ((List.finRange parameters.buses).filter (fun earlier => earlier < bus)).map
        fun earlier => .internal (.mask side earlier channel)
  have inputs : ([cursor.slots (.primary (.enable channel)), cursor.slots (.primary (.request bus channel))] ++
      ((List.finRange parameters.buses).filter (fun earlier => earlier < bus)).map
        fun earlier => cursor.slots (.internal (.mask side earlier channel))) = roles.map cursor.slots := by
    simp [roles, List.map_map, Function.comp_def]
  unfold laterTermStep
  rw [inputs]
  apply nativeAndFold_namedValues parameters cursor assignment input wire (.term side bus channel) roles
  · simp only [Parameters.gate, Parameters.termGate]
    split <;> rename_i layoutEquation
    · simp [Parameters.rawTermInputs, roles, Parameters.enable, Parameters.request,
        Parameters.internal, Parameters.positive, List.map_map, Function.comp_def]
    · simp [raw] at layoutEquation
  · exact prior
  · intro role member
    simp only [roles, List.mem_append] at member
    rcases member with member | member
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact primary.1 channel
      · exact primary.2 bus channel
    · obtain ⟨earlier, earlierMember, equal⟩ := List.mem_map.mp member
      subst role
      exact before earlier (by simpa using (List.mem_filter.mp earlierMember).2) channel
  · simpa only [laterTermStep, inputs] using equations

/-- Later-bus absent and mask producers jointly transport their exact physical values. -/
theorem laterAbsentMaskStep_namedValues (parameters : Parameters) (side : Side) (bus : Fin parameters.buses)
    (cursor : Cursor parameters) (channel : Fin parameters.channels) (assignment : ℕ → Bool)
    (input : Physical.PrimaryInput parameters.channels parameters.buses) (wire : Bool)
    (prior : cursor.NamedValues assignment (parameters.physicalAssignment input wire))
    (available : cursor.CurrentBusAvailable side bus)
    (equations : (laterAbsentMaskStep parameters side bus cursor channel).Equations assignment) :
    (laterAbsentMaskStep parameters side bus cursor channel).NamedValues assignment
      (parameters.physicalAssignment input wire) := by
  let absent := cursor.emitNative (.internal (.absent side bus channel))
    (.not (cursor.slots (.internal (.term side bus channel))))
  have absentEquations : absent.Equations assignment :=
    Cursor.equations_emitNative_prior _ assignment _ _ equations
  have absentValues : absent.NamedValues assignment (parameters.physicalAssignment input wire) := by
    apply nativeNotEmit_namedValues parameters cursor assignment input wire
      (.absent side bus channel) (.internal (.term side bus channel))
    · rfl
    · exact prior
    · exact available.2 channel
    · exact absentEquations
  apply nativeXorEmit_namedValues parameters absent assignment input wire (.mask side bus channel)
    (.internal (.flag side bus)) (.internal (.absent side bus channel))
  · rfl
  · exact absentValues
  · exact List.mem_append_left _ available.1
  · simp [absent, Cursor.emitNative_assigned]
  · exact equations

/-- The actual complete later-term loop transports all physical terms in the direct raw layout. -/
theorem laterTerms_namedValues (parameters : Parameters) (side : Side) (bus : Fin parameters.buses)
    (cursor : Cursor parameters) (assignment : ℕ → Bool)
    (input : Physical.PrimaryInput parameters.channels parameters.buses) (wire : Bool)
    (raw : parameters.layout = .raw)
    (prior : cursor.NamedValues assignment (parameters.physicalAssignment input wire))
    (primary : cursor.PrimaryAssigned) (before : cursor.MasksBefore side bus)
    (equations : (laterTerms parameters side bus cursor).Equations assignment) :
    (laterTerms parameters side bus cursor).NamedValues assignment (parameters.physicalAssignment input wire) ∧
      (laterTerms parameters side bus cursor).PrimaryAssigned ∧
      (laterTerms parameters side bus cursor).MasksBefore side bus := by
  let property := fun state : Cursor parameters =>
    state.NamedValues assignment (parameters.physicalAssignment input wire) ∧
      state.PrimaryAssigned ∧ state.MasksBefore side bus
  apply equations_foldl_induction (List.finRange parameters.channels) (laterTermStep parameters side bus)
    property assignment
  · intro state channel entry member
    simp [laterTermStep, Cursor.foldNative, Cursor.assign, member]
  · intro state channel invariants stageEquations
    refine ⟨laterTermStep_namedValues parameters side bus state channel assignment input wire raw
      invariants.1 invariants.2.1 invariants.2.2 stageEquations, ?_, ?_⟩
    · constructor
      · intro other
        exact List.mem_append_left _ (invariants.2.1.1 other)
      · intro bus other
        exact List.mem_append_left _ (invariants.2.1.2 bus other)
    · exact state.masksBefore_foldNative side bus _ _ _ invariants.2.2
  · exact ⟨prior, primary, before⟩
  · exact equations

/-- Native disjunction roles transport through the exact source balanced OR allocator. -/
theorem nativeOrFold_namedValues (parameters : Parameters) (cursor : Cursor parameters)
    (assignment : ℕ → Bool) (input : Physical.PrimaryInput parameters.channels parameters.buses)
    (wire : Bool) (role : Internal parameters) (roles : List (Controller.Native.Variable parameters))
    (nativeGate : parameters.gate role = .or (roles.map fun slot => (slot, true)))
    (prior : cursor.NamedValues assignment (parameters.physicalAssignment input wire))
    (assigned : ∀ slot ∈ roles, slot ∈ cursor.assigned)
    (equations : (cursor.foldNative (.internal role) .disjunction (roles.map cursor.slots)).Equations assignment) :
    (cursor.foldNative (.internal role) .disjunction (roles.map cursor.slots)).NamedValues assignment
      (parameters.physicalAssignment input wire) := by
  apply Cursor.namedValues_foldNative
  · exact prior
  · exact equations
  · have value := cursor.junction_eval_named assignment (parameters.physicalAssignment input wire)
      .disjunction roles prior assigned
    have semantic := parameters.roleValue_gate input wire role
    rw [nativeGate] at semantic
    exact value.trans semantic.symm

/-- The later-bus source flag is exactly the physical OR of that bus's current terms. -/
theorem laterFlagFold_namedValues (parameters : Parameters) (side : Side) (bus : Fin parameters.buses)
    (cursor : Cursor parameters) (assignment : ℕ → Bool)
    (input : Physical.PrimaryInput parameters.channels parameters.buses) (wire : Bool)
    (positive : 0 < bus.val)
    (prior : cursor.NamedValues assignment (parameters.physicalAssignment input wire))
    (terms : ∀ channel, .internal (.term side bus channel) ∈ cursor.assigned)
    (equations : (cursor.foldNative (.internal (.flag side bus)) .disjunction
      ((List.finRange parameters.channels).map fun channel => cursor.slots (.internal (.term side bus channel)))).Equations assignment) :
    (cursor.foldNative (.internal (.flag side bus)) .disjunction
      ((List.finRange parameters.channels).map fun channel => cursor.slots (.internal (.term side bus channel)))).NamedValues
      assignment (parameters.physicalAssignment input wire) := by
  let roles : List (Controller.Native.Variable parameters) :=
    (List.finRange parameters.channels).map fun channel => .internal (.term side bus channel)
  have inputs : ((List.finRange parameters.channels).map fun channel =>
      cursor.slots (.internal (.term side bus channel))) = roles.map cursor.slots := by
    simp [roles, List.map_map, Function.comp_def]
  rw [inputs]
  apply nativeOrFold_namedValues parameters cursor assignment input wire (.flag side bus) roles
  · have notFirst : bus.val ≠ 0 := by omega
    simp [Parameters.gate, notFirst, roles, Parameters.internal, Parameters.positive,
      List.map_map, Function.comp_def]
  · exact prior
  · intro role member
    obtain ⟨channel, _, equal⟩ := List.mem_map.mp member
    subst role
    exact terms channel
  · simpa only [inputs] using equations

theorem laterAbsentMaskStep_entries_contains (parameters : Parameters) (side : Side) (bus : Fin parameters.buses)
    (cursor : Cursor parameters) (channel : Fin parameters.channels) (entry : Entry parameters)
    (membership : entry ∈ cursor.entries) :
    entry ∈ (laterAbsentMaskStep parameters side bus cursor channel).entries := by
  simp [laterAbsentMaskStep, Cursor.emitNative, Cursor.emit, Cursor.assign, membership]

/-- A complete actual later bus transports its physical terms, flag, absent array and masks. -/
theorem laterBus_namedValues (parameters : Parameters) (side : Side) (bus : Fin parameters.buses)
    (cursor : Cursor parameters) (assignment : ℕ → Bool)
    (input : Physical.PrimaryInput parameters.channels parameters.buses) (wire : Bool)
    (raw : parameters.layout = .raw) (positive : 0 < bus.val)
    (prior : cursor.NamedValues assignment (parameters.physicalAssignment input wire))
    (primary : cursor.PrimaryAssigned) (before : cursor.MasksBefore side bus)
    (equations : (laterBus parameters side bus cursor).Equations assignment) :
    (laterBus parameters side bus cursor).NamedValues assignment (parameters.physicalAssignment input wire) := by
  let terms := laterTerms parameters side bus cursor
  let flag := terms.foldNative (.internal (.flag side bus)) .disjunction
    ((List.finRange parameters.channels).map fun channel => terms.slots (.internal (.term side bus channel)))
  let final := (List.finRange parameters.channels).foldl (laterAbsentMaskStep parameters side bus) flag
  change final.Equations assignment at equations
  change final.NamedValues assignment (parameters.physicalAssignment input wire)
  have flagEquations : flag.Equations assignment :=
    Cursor.equations_of_entries_subset _ _ assignment
      (entries_foldl_contains _ _ (laterAbsentMaskStep_entries_contains parameters side bus) flag) equations
  have termsEquations : terms.Equations assignment :=
    Cursor.equations_foldNative_prior _ assignment _ _ _ flagEquations
  have termsValues := (laterTerms_namedValues parameters side bus cursor assignment input wire raw
    prior primary before termsEquations).1
  have allTerms : ∀ channel, .internal (.term side bus channel) ∈ terms.assigned := by
    intro channel
    simp [terms, laterTerms_assigned]
  have flagValues : flag.NamedValues assignment (parameters.physicalAssignment input wire) :=
    laterFlagFold_namedValues parameters side bus terms assignment input wire positive termsValues allTerms flagEquations
  have flagAvailable : flag.CurrentBusAvailable side bus := by
    constructor
    · simp [flag, Cursor.foldNative_assigned]
    · intro channel
      exact List.mem_append_left _ (allTerms channel)
  let property := fun state : Cursor parameters =>
    state.NamedValues assignment (parameters.physicalAssignment input wire) ∧
      state.CurrentBusAvailable side bus
  have result := equations_foldl_induction (List.finRange parameters.channels)
    (laterAbsentMaskStep parameters side bus) property assignment
    (laterAbsentMaskStep_entries_contains parameters side bus)
    (fun state channel invariants stageEquations => by
      refine ⟨laterAbsentMaskStep_namedValues parameters side bus state channel assignment input wire
        invariants.1 invariants.2 stageEquations, ?_⟩
      constructor
      · rw [laterAbsentMaskStep_assigned]
        exact List.mem_append_left _ invariants.2.1
      · intro other
        rw [laterAbsentMaskStep_assigned]
        exact List.mem_append_left _ (invariants.2.2 other)) flag ⟨flagValues, flagAvailable⟩ equations
  exact result.1

/-- Retained observation XORs are private allocations and preserve every assigned native value. -/
theorem oldDifferenceStep_namedValues (parameters : Parameters) (cursor : Cursor parameters)
    (index : Fin (parameters.buses + parameters.channels)) (assignment : ℕ → Bool)
    (values : Controller.Native.Variable parameters → Bool)
    (prior : cursor.NamedValues assignment values) :
    (oldDifferenceStep parameters cursor index).NamedValues assignment values := prior

/-- A retained source observation XOR has exactly the physical value of the corresponding old output pair. -/
theorem oldDifferenceStep_value (parameters : Parameters) (cursor : Cursor parameters)
    (index : Fin (parameters.buses + parameters.channels)) (assignment : ℕ → Bool)
    (input : Physical.PrimaryInput parameters.channels parameters.buses) (wire : Bool)
    (prior : cursor.NamedValues assignment (parameters.physicalAssignment input wire))
    (available : cursor.OldOutputsAvailable)
    (equations : (oldDifferenceStep parameters cursor index).Equations assignment) :
    CNF.literalValue assignment ((oldDifferenceStep parameters cursor index).oldDifferences index) =
      (parameters.roleValue input wire
        ((SourceObservation.oldOutputRoles parameters .healthy)[index.val]?.getD .driver) ^^
       parameters.roleValue input wire
        ((SourceObservation.oldOutputRoles parameters .faulty)[index.val]?.getD .driver)) := by
  let good := (SourceObservation.oldOutputRoles parameters .healthy)[index.val]?.getD .driver
  let bad := (SourceObservation.oldOutputRoles parameters .faulty)[index.val]?.getD .driver
  let gate := CNF.Gate.xor (cursor.slots (.internal good)) (cursor.slots (.internal bad))
  have output := cursor.equations_emit_output assignment (.oldDifference index) gate equations
  have goodValue := prior (.internal good) (available .healthy good (oldOutput_lookup_member parameters .healthy index))
  have badValue := prior (.internal bad) (available .faulty bad (oldOutput_lookup_member parameters .faulty index))
  simp only [gate, CNF.Gate.eval] at output
  rw [goodValue, badValue] at output
  simpa [oldDifferenceStep, good, bad, gate, Cursor.emit, Parameters.physicalAssignment] using output

/-- A source loop whose operations preserve assigned named values preserves them on the complete traversal. -/
theorem namedValues_foldl (items : List α) (step : Cursor parameters → α → Cursor parameters)
    (assignment : ℕ → Bool) (values : Controller.Native.Variable parameters → Bool)
    (preserves : ∀ cursor item, cursor.NamedValues assignment values →
      (step cursor item).NamedValues assignment values)
    (cursor : Cursor parameters) (prior : cursor.NamedValues assignment values) :
    (items.foldl step cursor).NamedValues assignment values := by
  induction items generalizing cursor with
  | nil => exact prior
  | cons head tail inductionHypothesis =>
      exact inductionHypothesis (step cursor head) (preserves cursor head prior)

/-- The complete retained old-observation block preserves all physical principal values. -/
theorem originalObservations_namedValues (parameters : Parameters) (cursor : Cursor parameters)
    (assignment : ℕ → Bool) (values : Controller.Native.Variable parameters → Bool)
    (prior : cursor.NamedValues assignment values) :
    (originalObservations parameters cursor).NamedValues assignment values := by
  have paired : (pairedOldOutputs parameters cursor).NamedValues assignment values :=
    namedValues_foldl _ (oldDifferenceStep parameters) assignment values
      (fun state index values => oldDifferenceStep_namedValues parameters state index assignment _ values) cursor prior
  exact paired

/-- Every allocated private negated-flag handle carries the physical negated flag; zero defaults impose no value. -/
def Cursor.NegatedValues (cursor : Cursor parameters) (side : Side) (assignment : ℕ → Bool)
    (input : Physical.PrimaryInput parameters.channels parameters.buses) (wire : Bool) : Prop :=
  ∀ bus, 0 < (cursor.negated side bus).1 →
    CNF.literalValue assignment (cursor.negated side bus) = !parameters.roleValue input wire (.flag side bus)

/-- The exact private flag-negation producer establishes its physical auxiliary value. -/
theorem negateFlagStep_value (parameters : Parameters) (side : Side)
    (cursor : Cursor parameters) (bus : Fin parameters.buses) (assignment : ℕ → Bool)
    (input : Physical.PrimaryInput parameters.channels parameters.buses) (wire : Bool)
    (prior : cursor.NamedValues assignment (parameters.physicalAssignment input wire))
    (flag : .internal (.flag side bus) ∈ cursor.assigned)
    (equations : (negateFlagStep parameters side cursor bus).Equations assignment) :
    CNF.literalValue assignment ((negateFlagStep parameters side cursor bus).negated side bus) =
      !parameters.roleValue input wire (.flag side bus) := by
  have output := cursor.equations_emit_output assignment (.negatedFlag side bus)
    (.not (cursor.slots (.internal (.flag side bus)))) equations
  simp only [CNF.Gate.eval] at output
  rw [prior _ flag] at output
  simpa [negateFlagStep, Cursor.emit, Parameters.physicalAssignment] using output

/-- Updating a private negated-flag slot preserves all previously allocated physical negations. -/
theorem negateFlagStep_negatedValues (parameters : Parameters) (side : Side)
    (cursor : Cursor parameters) (bus : Fin parameters.buses) (assignment : ℕ → Bool)
    (input : Physical.PrimaryInput parameters.channels parameters.buses) (wire : Bool)
    (prior : cursor.NamedValues assignment (parameters.physicalAssignment input wire))
    (negated : cursor.NegatedValues side assignment input wire)
    (flag : .internal (.flag side bus) ∈ cursor.assigned)
    (equations : (negateFlagStep parameters side cursor bus).Equations assignment) :
    (negateFlagStep parameters side cursor bus).NegatedValues side assignment input wire := by
  intro other positive
  by_cases same : other = bus
  · subst other
    exact negateFlagStep_value parameters side cursor bus assignment input wire prior flag equations
  · have unchanged : (negateFlagStep parameters side cursor bus).negated side other = cursor.negated side other := by
      simp [negateFlagStep, Cursor.emit, same]
    rw [unchanged] at positive ⊢
    exact negated other positive

/-- The complete private-negation loop preserves principal values and sound allocated auxiliary negations. -/
theorem negateFlags_namedValues (parameters : Parameters) (side : Side)
    (cursor : Cursor parameters) (assignment : ℕ → Bool)
    (input : Physical.PrimaryInput parameters.channels parameters.buses) (wire : Bool)
    (prior : cursor.NamedValues assignment (parameters.physicalAssignment input wire))
    (flags : cursor.FlagsAvailable side)
    (negated : cursor.NegatedValues side assignment input wire)
    (equations : (negateFlags parameters side cursor).Equations assignment) :
    (negateFlags parameters side cursor).NamedValues assignment (parameters.physicalAssignment input wire) ∧
      (negateFlags parameters side cursor).FlagsAvailable side ∧
      (negateFlags parameters side cursor).NegatedValues side assignment input wire := by
  rw [negateFlags_eq] at equations ⊢
  let property := fun state : Cursor parameters =>
    state.NamedValues assignment (parameters.physicalAssignment input wire) ∧
      state.FlagsAvailable side ∧ state.NegatedValues side assignment input wire
  apply equations_foldl_induction (List.finRange parameters.buses) (negateFlagStep parameters side)
    property assignment
  · intro state bus entry member
    simp [negateFlagStep, Cursor.emit, member]
  · intro state bus invariants stageEquations
    refine ⟨invariants.1, invariants.2.1, ?_⟩
    exact negateFlagStep_negatedValues parameters side state bus assignment input wire
      invariants.1 invariants.2.2 (invariants.2.1 bus) stageEquations
  · exact ⟨prior, flags, negated⟩
  · exact equations

/-- The actual eligibility OR consumes a sound private negated flag and the physical request root. -/
theorem eligibleGuardStep_namedValues (parameters : Parameters) (side : Side)
    (channel : Fin parameters.channels) (cursor : Cursor parameters) (bus : Fin parameters.buses)
    (assignment : ℕ → Bool) (input : Physical.PrimaryInput parameters.channels parameters.buses) (wire : Bool)
    (prior : cursor.NamedValues assignment (parameters.physicalAssignment input wire))
    (requestAssigned : .primary (.request bus channel) ∈ cursor.assigned)
    (available : cursor.NegatedAvailable side)
    (negated : cursor.NegatedValues side assignment input wire)
    (equations : (eligibleGuardStep parameters side channel cursor bus).Equations assignment) :
    (eligibleGuardStep parameters side channel cursor bus).NamedValues assignment
      (parameters.physicalAssignment input wire) := by
  apply Cursor.namedValues_emitNative
  · exact prior
  · exact equations
  · simp only [CNF.Gate.eval, List.any_cons, List.any_nil, Bool.or_false]
    rw [negated bus (available bus).1, prior _ requestAssigned]
    rfl

theorem laterBus_entries_contains (parameters : Parameters) (side : Side) (bus : Fin parameters.buses)
    (cursor : Cursor parameters) (entry : Entry parameters) (membership : entry ∈ cursor.entries) :
    entry ∈ (laterBus parameters side bus cursor).entries := by
  let terms := laterTerms parameters side bus cursor
  have termMember : entry ∈ terms.entries :=
    entries_foldl_contains _ (laterTermStep parameters side bus)
      (fun state channel entry member => by simp [laterTermStep, Cursor.foldNative, Cursor.assign, member])
      cursor entry membership
  let flag := terms.foldNative (.internal (.flag side bus)) .disjunction
    ((List.finRange parameters.channels).map fun channel => terms.slots (.internal (.term side bus channel)))
  have flagMember : entry ∈ flag.entries := List.mem_append_left _ termMember
  exact entries_foldl_contains _ (laterAbsentMaskStep parameters side bus)
    (laterAbsentMaskStep_entries_contains parameters side bus) flag entry flagMember

/-- The entire increasing positive-bus source traversal transports physical values without guessing earlier masks. -/
theorem orderedBuses_namedValues (parameters : Parameters) (side : Side)
    (buses : List (Fin parameters.buses)) (ascending : buses.Pairwise (· < ·))
    (positive : ∀ bus ∈ buses, 0 < bus.val) (cursor : Cursor parameters) (assignment : ℕ → Bool)
    (input : Physical.PrimaryInput parameters.channels parameters.buses) (wire : Bool)
    (raw : parameters.layout = .raw)
    (prior : cursor.NamedValues assignment (parameters.physicalAssignment input wire))
    (primary : cursor.PrimaryAssigned) (coverage : cursor.MaskCoverage side buses)
    (equations : (buses.foldl (fun state bus => laterBus parameters side bus state) cursor).Equations assignment) :
    (buses.foldl (fun state bus => laterBus parameters side bus state) cursor).NamedValues assignment
      (parameters.physicalAssignment input wire) := by
  induction buses generalizing cursor with
  | nil => exact prior
  | cons head tail inductionHypothesis =>
      obtain ⟨headSmaller, tailAscending⟩ := List.pairwise_cons.mp ascending
      have before : cursor.MasksBefore side head := by
        intro earlier smaller channel
        rcases coverage head (by simp) earlier smaller channel with available | membership
        · exact available
        · simp only [List.mem_cons] at membership
          rcases membership with equal | memberTail
          · subst earlier
            exact False.elim ((lt_irrefl head) smaller)
          · exact False.elim ((lt_asymm smaller) (headSmaller earlier memberTail))
      let next := laterBus parameters side head cursor
      have nextEquations : next.Equations assignment :=
        Cursor.equations_of_entries_subset _ _ assignment
          (entries_foldl_contains tail (fun state bus => laterBus parameters side bus state)
            (fun state bus => laterBus_entries_contains parameters side bus state) next) equations
      have nextValues : next.NamedValues assignment (parameters.physicalAssignment input wire) :=
        laterBus_namedValues parameters side head cursor assignment input wire raw
          (positive head (by simp)) prior primary before nextEquations
      have nextPrimary : next.PrimaryAssigned := by
        constructor
        · intro channel
          exact laterBus_preserves_assigned parameters side head cursor _ (primary.1 channel)
        · intro bus channel
          exact laterBus_preserves_assigned parameters side head cursor _ (primary.2 bus channel)
      have nextCoverage : next.MaskCoverage side tail := by
        intro bus memberTail earlier smaller channel
        rcases coverage bus (List.mem_cons_of_mem head memberTail) earlier smaller channel with available | membership
        · exact Or.inl (laterBus_preserves_assigned parameters side head cursor _ available)
        · simp only [List.mem_cons] at membership
          rcases membership with equal | memberRest
          · subst earlier
            exact Or.inl (laterBus_all_masks_assigned parameters side head cursor channel)
          · exact Or.inr memberRest
      exact inductionHypothesis tailAscending
        (fun bus member => positive bus (List.mem_cons_of_mem head member)) next nextValues nextPrimary nextCoverage equations

/-- Exact physical transport through all initial masks and all positive source buses. -/
theorem initialMasks_laterBuses_namedValues (parameters : Parameters) (side : Side)
    (cursor : Cursor parameters) (assignment : ℕ → Bool)
    (input : Physical.PrimaryInput parameters.channels parameters.buses) (wire : Bool)
    (raw : parameters.layout = .raw)
    (prior : cursor.NamedValues assignment (parameters.physicalAssignment input wire))
    (primary : cursor.PrimaryAssigned) (first : cursor.FirstAvailable side)
    (equations : ((positiveBuses parameters).foldl (fun state bus => laterBus parameters side bus state)
      (initialMasks parameters side cursor)).Equations assignment) :
    ((positiveBuses parameters).foldl (fun state bus => laterBus parameters side bus state)
      (initialMasks parameters side cursor)).NamedValues assignment (parameters.physicalAssignment input wire) := by
  have masksEquations : (initialMasks parameters side cursor).Equations assignment :=
    Cursor.equations_of_entries_subset _ _ assignment
      (entries_foldl_contains _ (fun state bus => laterBus parameters side bus state)
        (fun state bus => laterBus_entries_contains parameters side bus state) _) equations
  have masksValues := (initialMasks_namedValues parameters side cursor assignment input wire prior first masksEquations).1
  have masksPrimary : (initialMasks parameters side cursor).PrimaryAssigned := by
    constructor
    · intro channel
      rw [initialMasks_assigned]
      exact List.mem_append_left _ (primary.1 channel)
    · intro bus channel
      rw [initialMasks_assigned]
      exact List.mem_append_left _ (primary.2 bus channel)
  apply orderedBuses_namedValues parameters side _ (positiveBuses_ascending parameters)
  · intro bus member
    have nonzero : bus.val ≠ 0 := by simpa [positiveBuses] using member
    omega
  · exact raw
  · exact masksValues
  · exact masksPrimary
  · exact initialMasks_positiveCoverage parameters side cursor
  · exact equations

/-- The complete source eligibility computation realizes its physical qualifier and preserves auxiliary negations. -/
theorem eligible_namedValues (parameters : Parameters) (side : Side) (channel : Fin parameters.channels)
    (cursor : Cursor parameters) (assignment : ℕ → Bool)
    (input : Physical.PrimaryInput parameters.channels parameters.buses) (wire : Bool)
    (prior : cursor.NamedValues assignment (parameters.physicalAssignment input wire))
    (primary : cursor.PrimaryAssigned) (available : cursor.NegatedAvailable side)
    (negated : cursor.NegatedValues side assignment input wire)
    (equations : (eligible parameters side channel cursor).Equations assignment) :
    (eligible parameters side channel cursor).NamedValues assignment (parameters.physicalAssignment input wire) ∧
      (eligible parameters side channel cursor).PrimaryAssigned ∧
      (eligible parameters side channel cursor).NegatedAvailable side ∧
      (eligible parameters side channel cursor).NegatedValues side assignment input wire := by
  let guarded := (List.finRange parameters.buses).foldl (eligibleGuardStep parameters side channel) cursor
  have guardEquations : guarded.Equations assignment :=
    Cursor.equations_foldNative_prior _ assignment _ _ _ equations
  let property := fun state : Cursor parameters =>
    state.NamedValues assignment (parameters.physicalAssignment input wire) ∧
      state.PrimaryAssigned ∧ state.NegatedAvailable side ∧ state.NegatedValues side assignment input wire
  have guards := equations_foldl_induction (List.finRange parameters.buses)
    (eligibleGuardStep parameters side channel) property assignment
    (fun state bus entry member => by
      simp [eligibleGuardStep, Cursor.emitNative, Cursor.emit, Cursor.assign, member])
    (fun state bus invariants stageEquations => by
      refine ⟨eligibleGuardStep_namedValues parameters side channel state bus assignment input wire
        invariants.1 (invariants.2.1.2 bus channel) invariants.2.2.1 invariants.2.2.2 stageEquations, ?_, ?_, ?_⟩
      · constructor
        · intro other
          exact List.mem_append_left _ (invariants.2.1.1 other)
        · intro bus other
          exact List.mem_append_left _ (invariants.2.1.2 bus other)
      · exact state.negatedAvailable_emitNative side _ _ invariants.2.2.1
      · exact invariants.2.2.2)
    cursor ⟨prior, primary, available, negated⟩ guardEquations
  have guardRoles : ∀ bus, .internal (.qualifierGuard side bus channel) ∈ guarded.assigned := by
    intro bus
    dsimp [guarded]
    rw [assigned_foldl _ _ (fun bus => [.internal (.qualifierGuard side bus channel)]) (fun _ _ => rfl)]
    simp only [List.mem_append, List.mem_flatMap, List.mem_singleton]
    exact Or.inr ⟨bus, by simp, rfl⟩
  let roles : List (Controller.Native.Variable parameters) := .primary (.enable channel) ::
    (List.finRange parameters.buses).map fun bus => .internal (.qualifierGuard side bus channel)
  have inputs : (guarded.slots (.primary (.enable channel)) ::
      (List.finRange parameters.buses).map fun bus => guarded.slots (.internal (.qualifierGuard side bus channel))) =
      roles.map guarded.slots := by simp [roles, List.map_map, Function.comp_def]
  have outputValues : (eligible parameters side channel cursor).NamedValues assignment
      (parameters.physicalAssignment input wire) := by
    unfold eligible
    change (guarded.foldNative (.internal (.qualifier side channel)) .conjunction
      (guarded.slots (.primary (.enable channel)) ::
        (List.finRange parameters.buses).map fun bus => guarded.slots (.internal (.qualifierGuard side bus channel)))).NamedValues
      assignment (parameters.physicalAssignment input wire)
    rw [inputs]
    apply nativeAndFold_namedValues parameters guarded assignment input wire (.qualifier side channel) roles
    · simp [Parameters.gate, roles, Parameters.enable, Parameters.internal, Parameters.positive,
        List.map_map, Function.comp_def]
    · exact guards.1
    · intro role member
      simp only [roles, List.mem_cons] at member
      rcases member with rfl | member
      · exact guards.2.1.1 channel
      · obtain ⟨bus, _, equal⟩ := List.mem_map.mp member
        subst role
        exact guardRoles bus
    · change (guarded.foldNative (.internal (.qualifier side channel)) .conjunction
        (guarded.slots (.primary (.enable channel)) ::
          (List.finRange parameters.buses).map fun bus => guarded.slots (.internal (.qualifierGuard side bus channel)))).Equations assignment at equations
      rw [inputs] at equations
      exact equations
  refine ⟨outputValues, ?_, ?_, ?_⟩
  · constructor
    · intro other
      rw [eligible_assigned]
      exact List.mem_append_left _ (primary.1 other)
    · intro bus other
      rw [eligible_assigned]
      exact List.mem_append_left _ (primary.2 bus other)
  · exact guarded.negatedAvailable_foldNative side _ _ _ guards.2.2.1
  · exact guards.2.2.2

/-- A source loop of operations that do not alter auxiliary negation handles preserves that complete map. -/
theorem negated_foldl (items : List α) (step : Cursor parameters → α → Cursor parameters)
    (preserves : ∀ state item, (step state item).negated = state.negated)
    (cursor : Cursor parameters) : (items.foldl step cursor).negated = cursor.negated := by
  induction items generalizing cursor with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      exact (inductionHypothesis (step cursor head)).trans (preserves cursor head)

theorem initialMasks_negated (parameters : Parameters) (side : Side) (cursor : Cursor parameters) :
    (initialMasks parameters side cursor).negated = cursor.negated :=
  negated_foldl (List.finRange parameters.channels)
    (fun state channel => state.emitNative (.internal (.mask side parameters.firstBus channel))
      (.xor (state.slots (.internal (.flag side parameters.firstBus)))
        (state.slots (.internal (.absent side parameters.firstBus channel))))) (fun _ _ => rfl) cursor

theorem laterTerms_negated (parameters : Parameters) (side : Side) (bus : Fin parameters.buses)
    (cursor : Cursor parameters) : (laterTerms parameters side bus cursor).negated = cursor.negated :=
  negated_foldl (List.finRange parameters.channels) (laterTermStep parameters side bus) (fun _ _ => rfl) cursor

theorem laterBus_negated (parameters : Parameters) (side : Side) (bus : Fin parameters.buses)
    (cursor : Cursor parameters) : (laterBus parameters side bus cursor).negated = cursor.negated := by
  let terms := laterTerms parameters side bus cursor
  let flag := terms.foldNative (.internal (.flag side bus)) .disjunction
    ((List.finRange parameters.channels).map fun channel => terms.slots (.internal (.term side bus channel)))
  have final : ((List.finRange parameters.channels).foldl (laterAbsentMaskStep parameters side bus) flag).negated =
      flag.negated := negated_foldl (List.finRange parameters.channels)
        (laterAbsentMaskStep parameters side bus) (fun _ _ => rfl) flag
  exact final.trans (laterTerms_negated parameters side bus cursor)

theorem eligible_negated (parameters : Parameters) (side : Side) (channel : Fin parameters.channels)
    (cursor : Cursor parameters) : (eligible parameters side channel cursor).negated = cursor.negated :=
  negated_foldl (List.finRange parameters.buses) (eligibleGuardStep parameters side channel) (fun _ _ => rfl) cursor

theorem initialMasks_laterBuses_negated (parameters : Parameters) (side : Side) (cursor : Cursor parameters) :
    ((positiveBuses parameters).foldl (fun state bus => laterBus parameters side bus state)
      (initialMasks parameters side cursor)).negated = cursor.negated :=
  (negated_foldl (positiveBuses parameters) (fun state bus => laterBus parameters side bus state)
    (fun state bus => laterBus_negated parameters side bus state) (initialMasks parameters side cursor)).trans
      (initialMasks_negated parameters side cursor)

/-- Private negation and eligibility operations retain all existing source entries. -/
theorem negateFlagStep_entries_contains (parameters : Parameters) (side : Side)
    (cursor : Cursor parameters) (bus : Fin parameters.buses) (entry : Entry parameters)
    (membership : entry ∈ cursor.entries) :
    entry ∈ (negateFlagStep parameters side cursor bus).entries := by
  simp [negateFlagStep, Cursor.emit, membership]

theorem eligibleGuardStep_entries_contains (parameters : Parameters) (side : Side) (channel : Fin parameters.channels)
    (cursor : Cursor parameters) (bus : Fin parameters.buses) (entry : Entry parameters)
    (membership : entry ∈ cursor.entries) :
    entry ∈ (eligibleGuardStep parameters side channel cursor bus).entries := by
  simp [eligibleGuardStep, Cursor.emitNative, Cursor.emit, Cursor.assign, membership]

theorem eligible_entries_contains (parameters : Parameters) (side : Side) (channel : Fin parameters.channels)
    (cursor : Cursor parameters) (entry : Entry parameters) (membership : entry ∈ cursor.entries) :
    entry ∈ (eligible parameters side channel cursor).entries := by
  have guarded := entries_foldl_contains (List.finRange parameters.buses) (eligibleGuardStep parameters side channel)
    (eligibleGuardStep_entries_contains parameters side channel) cursor entry membership
  exact List.mem_append_left _ guarded

/-- Complete direct-source tail semantics: sorted buses, private negations, and every physical qualifier. -/
theorem tail_namedValues (parameters : Parameters) (side : Side) (cursor : Cursor parameters)
    (assignment : ℕ → Bool) (input : Physical.PrimaryInput parameters.channels parameters.buses) (wire : Bool)
    (raw : parameters.layout = .raw) (ready : cursor.Ready)
    (prior : cursor.NamedValues assignment (parameters.physicalAssignment input wire))
    (first : cursor.FirstAvailable side) (negated : cursor.NegatedValues side assignment input wire)
    (equations : (tail parameters side cursor).Equations assignment) :
    (tail parameters side cursor).NamedValues assignment (parameters.physicalAssignment input wire) := by
  let stages := (positiveBuses parameters).foldl (fun state bus => laterBus parameters side bus state)
    (initialMasks parameters side cursor)
  let negatedCursor := negateFlags parameters side stages
  let final := (List.finRange parameters.channels).foldl (fun state channel => eligible parameters side channel state)
    negatedCursor
  change final.Equations assignment at equations
  change final.NamedValues assignment (parameters.physicalAssignment input wire)
  have negationEquations : negatedCursor.Equations assignment :=
    Cursor.equations_of_entries_subset _ _ assignment
      (entries_foldl_contains _ (fun state channel => eligible parameters side channel state)
        (fun state channel => eligible_entries_contains parameters side channel state) negatedCursor) equations
  have stagesEquations : stages.Equations assignment := by
    apply Cursor.equations_of_entries_subset stages negatedCursor assignment
    · exact entries_foldl_contains _ (negateFlagStep parameters side)
        (negateFlagStep_entries_contains parameters side) stages
    · exact negationEquations
  have stagesValues : stages.NamedValues assignment (parameters.physicalAssignment input wire) :=
    initialMasks_laterBuses_namedValues parameters side cursor assignment input wire raw prior ready.primary first stagesEquations
  have stagesReady : stages.Ready := initialMasks_laterBuses_ready parameters side cursor ready first
  have stagesFlags : stages.FlagsAvailable side := initialMasks_laterBuses_flags parameters side cursor first
  have stagesNegated : stages.NegatedValues side assignment input wire := by
    intro bus positive
    have frame := initialMasks_laterBuses_negated parameters side cursor
    change 0 < (stages.negated side bus).1 at positive
    change CNF.literalValue assignment (stages.negated side bus) = _
    rw [frame] at positive ⊢
    exact negated bus positive
  have negationValues := negateFlags_namedValues parameters side stages assignment input wire
    stagesValues stagesFlags stagesNegated negationEquations
  have negationReady := negateFlags_ready parameters side stages stagesReady stagesFlags
  let property := fun state : Cursor parameters =>
    state.NamedValues assignment (parameters.physicalAssignment input wire) ∧
      state.PrimaryAssigned ∧ state.NegatedAvailable side ∧ state.NegatedValues side assignment input wire
  have result := equations_foldl_induction (List.finRange parameters.channels)
    (fun state channel => eligible parameters side channel state) property assignment
    (fun state channel => eligible_entries_contains parameters side channel state)
    (fun state channel invariants stageEquations => eligible_namedValues parameters side channel state assignment input wire
      invariants.1 invariants.2.1 invariants.2.2.1 invariants.2.2.2 stageEquations)
    negatedCursor ⟨negationValues.1, negationReady.1.primary, negationReady.2, negationValues.2.2⟩ equations
  exact result.1

theorem firstArrays_negated (parameters : Parameters) :
    (firstArrays parameters).negated = (initial parameters).negated := by
  have terms : (firstTerms parameters).negated = (initial parameters).negated :=
    negated_foldl _ (firstTermStep parameters) (fun _ _ => rfl) _
  have absent : (firstArrays parameters).negated = (firstTerms parameters).negated :=
    negated_foldl _ (firstAbsentStep parameters) (fun _ _ => rfl) _
  exact absent.trans terms

theorem interface_negated (parameters : Parameters) :
    (interface parameters).negated = (initial parameters).negated := firstArrays_negated parameters

/-- A source loop preserving one other-side auxiliary map preserves that map on the complete traversal. -/
theorem negatedSide_foldl (items : List α) (step : Cursor parameters → α → Cursor parameters)
    (other : Side) (preserves : ∀ state item, (step state item).negated other = state.negated other)
    (cursor : Cursor parameters) : (items.foldl step cursor).negated other = cursor.negated other := by
  induction items generalizing cursor with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      exact (inductionHypothesis (step cursor head)).trans (preserves cursor head)

/-- A controller tail never allocates or overwrites the other copy's private negation handles. -/
theorem tail_negated_other (parameters : Parameters) (side other : Side) (different : other ≠ side)
    (cursor : Cursor parameters) : (tail parameters side cursor).negated other = cursor.negated other := by
  let stages := (positiveBuses parameters).foldl (fun state bus => laterBus parameters side bus state)
    (initialMasks parameters side cursor)
  have flags : (negateFlags parameters side stages).negated other = stages.negated other :=
    negatedSide_foldl _ (negateFlagStep parameters side) other
      (fun state bus => by simp [negateFlagStep, Cursor.emit, different]) stages
  have eligibility : (tail parameters side cursor).negated other =
      (negateFlags parameters side stages).negated other :=
    negatedSide_foldl _ (fun state channel => eligible parameters side channel state) other
      (fun state channel => congrFun (eligible_negated parameters side channel state) other) _
  exact eligibility.trans (flags.trans (congrFun (initialMasks_laterBuses_negated parameters side cursor) other))

/-- Every source tail retains every previously generated producer entry. -/
theorem tail_entries_contains (parameters : Parameters) (side : Side) (cursor : Cursor parameters)
    (entry : Entry parameters) (membership : entry ∈ cursor.entries) :
    entry ∈ (tail parameters side cursor).entries := by
  let masks := initialMasks parameters side cursor
  have masksMember : entry ∈ masks.entries := entries_foldl_contains _
    (fun state channel => state.emitNative (.internal (.mask side parameters.firstBus channel))
      (.xor (state.slots (.internal (.flag side parameters.firstBus)))
        (state.slots (.internal (.absent side parameters.firstBus channel)))))
    (fun state channel entry member => by simp [Cursor.emitNative, Cursor.emit, Cursor.assign, member])
    cursor entry membership
  let stages := (positiveBuses parameters).foldl (fun state bus => laterBus parameters side bus state) masks
  have stagesMember : entry ∈ stages.entries := entries_foldl_contains (positiveBuses parameters)
    (fun state bus => laterBus parameters side bus state)
    (fun state bus => laterBus_entries_contains parameters side bus state) masks entry masksMember
  let negated := negateFlags parameters side stages
  have negatedMember : entry ∈ negated.entries := entries_foldl_contains _
    (negateFlagStep parameters side) (negateFlagStep_entries_contains parameters side) stages entry stagesMember
  exact entries_foldl_contains _ (fun state channel => eligible parameters side channel state)
    (fun state channel => eligible_entries_contains parameters side channel state) negated entry negatedMember

/-- Both complete direct-source controller copies realize their physical named values. -/
theorem controller_namedValues (parameters : Parameters) (assignment : ℕ → Bool)
    (input : Physical.PrimaryInput parameters.channels parameters.buses) (wire : Bool)
    (raw : parameters.layout = .raw)
    (enable : ∀ channel, assignment (SourceInitialIDs.rootID (b := parameters.buses)
      (.enable channel)) = input.enable channel)
    (request : ∀ bus channel, assignment (SourceInitialIDs.rootID (.request bus channel)) = input.request bus channel)
    (wireDriver : wire = Physical.bridgeD parameters.bridge input)
    (equations : (controller parameters).Equations assignment) :
    (controller parameters).NamedValues assignment (parameters.physicalAssignment input wire) := by
  let healthy := tail parameters .healthy (interface parameters)
  have healthyEquations : healthy.Equations assignment := Cursor.equations_of_entries_subset _ _ assignment
    (tail_entries_contains parameters .faulty healthy) equations
  have interfaceEquations : (interface parameters).Equations assignment := Cursor.equations_of_entries_subset _ _ assignment
    (tail_entries_contains parameters .healthy _) healthyEquations
  have interfaceValues := interface_namedValues parameters assignment input wire enable request wireDriver interfaceEquations
  have healthyNegated : (interface parameters).NegatedValues .healthy assignment input wire := by
    intro bus positive
    rw [interface_negated] at positive
    simp [initial] at positive
  have healthyValues : healthy.NamedValues assignment (parameters.physicalAssignment input wire) :=
    tail_namedValues parameters .healthy _ assignment input wire raw (interface_ready parameters) interfaceValues
      (interface_firstAvailable parameters .healthy) healthyNegated healthyEquations
  have faultyFirst : healthy.FirstAvailable .faulty :=
    tail_firstAvailable parameters .healthy .faulty _ (interface_firstAvailable parameters .faulty)
  have faultyNegated : healthy.NegatedValues .faulty assignment input wire := by
    intro bus positive
    have frame := tail_negated_other parameters .healthy .faulty (by decide) (interface parameters)
    change 0 < (healthy.negated .faulty bus).1 at positive
    rw [frame, interface_negated] at positive
    simp [initial] at positive
  exact tail_namedValues parameters .faulty healthy assignment input wire raw
    (tail_ready parameters .healthy _ (interface_ready parameters) (interface_firstAvailable parameters .healthy))
    healthyValues faultyFirst faultyNegated equations

/-- Physical input recovered exclusively from the actual allocated source enable/request root IDs. -/
def sourceInput (parameters : Parameters) (assignment : ℕ → Bool) :
    Physical.PrimaryInput parameters.channels parameters.buses where
  positiveBuses := parameters.positiveBuses
  enable := fun channel => assignment (SourceInitialIDs.rootID (b := parameters.buses) (.enable channel))
  request := fun bus channel => assignment (SourceInitialIDs.rootID (.request bus channel))

/-- Actual source equations determine every controller value from its loaded physical roots; no wire value is supplied. -/
theorem controller_namedValues_from_source (parameters : Parameters) (assignment : ℕ → Bool)
    (raw : parameters.layout = .raw) (equations : (controller parameters).Equations assignment) :
    (controller parameters).NamedValues assignment (parameters.physicalAssignment (sourceInput parameters assignment)
      (Physical.bridgeD parameters.bridge (sourceInput parameters assignment))) :=
  controller_namedValues parameters assignment (sourceInput parameters assignment) _ raw
    (fun _ => rfl) (fun _ _ => rfl) rfl equations

/-- The actual retained controller equations force source W = source D, through the fresh unary-AND wire producer. -/
theorem controller_source_wire_eq_driver (parameters : Parameters) (assignment : ℕ → Bool)
    (raw : parameters.layout = .raw) (equations : (controller parameters).Equations assignment) :
    CNF.literalValue assignment ((controller parameters).slots (.primary .wire)) =
      CNF.literalValue assignment ((controller parameters).slots (.internal .driver)) := by
  have values := controller_namedValues_from_source parameters assignment raw equations
  have wireAssigned : .primary .wire ∈ (controller parameters).assigned := by
    simp [controller_assigned, interface_assigned, interfaceRoles]
  have driverAssigned : .internal .driver ∈ (controller parameters).assigned := by
    simp [controller_assigned, interface_assigned, interfaceRoles]
  rw [values _ wireAssigned, values _ driverAssigned]
  rfl

/-- Private signed decoder guard producers preserve every assigned physical principal value. -/
theorem guardChain_namedValues (parameters : Parameters) (side : Side) (node : Fin parameters.decoder.nodeCount)
    (child : CNF.Literal ℕ) (labels : List (Fin parameters.channels)) (cursor : Cursor parameters)
    (assignment : ℕ → Bool) (values : Controller.Native.Variable parameters → Bool)
    (prior : cursor.NamedValues assignment values) :
    (guardChain parameters side node child labels cursor).2.NamedValues assignment values := by
  intro slot membership
  rw [guardChain_assigned] at membership
  rw [guardChain_slots]
  exact prior slot membership

/-- Every signed-guard traversal retains the exact preceding producer entries. -/
theorem guardItems_entries_contains (parameters : Parameters) (side : Side) (node : Fin parameters.decoder.nodeCount)
    (items : List (Fin parameters.channels × ℕ)) (child : CNF.Literal ℕ) (cursor : Cursor parameters) :
    ∀ entry ∈ cursor.entries, entry ∈
      (items.foldl (fun state pair => state.2.emit (.guard side node pair.2)
        (.and [state.1, CNF.negate (state.2.slots (.internal (.qualifier side pair.1)))])) (child, cursor)).2.entries := by
  induction items generalizing child cursor with
  | nil => exact fun _ member => member
  | cons head tail inductionHypothesis =>
      intro entry member
      let emitted := cursor.emit (.guard side node head.2)
        (.and [child, CNF.negate (cursor.slots (.internal (.qualifier side head.1)))])
      apply inductionHypothesis emitted.1 emitted.2 entry
      simp [emitted, Cursor.emit, member]

/-- Exact signed source guard semantics, retaining repeated labels and their source order. -/
theorem guardItems_value (parameters : Parameters) (side : Side) (node : Fin parameters.decoder.nodeCount)
    (items : List (Fin parameters.channels × ℕ)) (child : CNF.Literal ℕ) (cursor : Cursor parameters)
    (assignment : ℕ → Bool) (input : Physical.PrimaryInput parameters.channels parameters.buses) (wire : Bool)
    (prior : cursor.NamedValues assignment (parameters.physicalAssignment input wire))
    (available : cursor.QualifiersAvailable side)
    (equations : (items.foldl (fun state pair => state.2.emit (.guard side node pair.2)
      (.and [state.1, CNF.negate (state.2.slots (.internal (.qualifier side pair.1)))])) (child, cursor)).2.Equations assignment) :
    CNF.literalValue assignment
      ((items.foldl (fun state pair => state.2.emit (.guard side node pair.2)
        (.and [state.1, CNF.negate (state.2.slots (.internal (.qualifier side pair.1)))])) (child, cursor)).1) =
      (CNF.literalValue assignment child && items.all (fun pair => !parameters.qualifiers input wire side pair.1)) := by
  induction items generalizing child cursor with
  | nil => simp
  | cons head tail inductionHypothesis =>
      let gate := CNF.Gate.and [child, CNF.negate (cursor.slots (.internal (.qualifier side head.1)))]
      let emitted := cursor.emit (.guard side node head.2) gate
      have emittedEquations : emitted.2.Equations assignment :=
        Cursor.equations_of_entries_subset _ _ assignment
          (guardItems_entries_contains parameters side node tail emitted.1 emitted.2) equations
      have output := cursor.equations_emit_output assignment (.guard side node head.2) gate emittedEquations
      simp only [gate, CNF.Gate.eval, List.all_cons, List.all_nil, Bool.and_true, CNF.literalValue_negate] at output
      rw [prior _ (available head.1)] at output
      have rest := inductionHypothesis emitted.1 emitted.2 prior available equations
      simp only [List.foldl_cons]
      rw [rest, output]
      simp [List.all_cons, Parameters.physicalAssignment, Parameters.roleValue, Bool.and_assoc]

/-- The actual decoder guard chain evaluates to its child and the exact list of negative channel guards. -/
theorem guardChain_value (parameters : Parameters) (side : Side) (node : Fin parameters.decoder.nodeCount)
    (child : CNF.Literal ℕ) (labels : List (Fin parameters.channels)) (cursor : Cursor parameters)
    (assignment : ℕ → Bool) (input : Physical.PrimaryInput parameters.channels parameters.buses) (wire : Bool)
    (prior : cursor.NamedValues assignment (parameters.physicalAssignment input wire))
    (available : cursor.QualifiersAvailable side)
    (equations : (guardChain parameters side node child labels cursor).2.Equations assignment) :
    CNF.literalValue assignment (guardChain parameters side node child labels cursor).1 =
      (CNF.literalValue assignment child && labels.all (fun channel => !parameters.qualifiers input wire side channel)) := by
  have value := guardItems_value parameters side node labels.zipIdx child cursor assignment input wire prior available equations
  have projected := congrArg (fun items : List (Fin parameters.channels) =>
    items.all (fun channel => !parameters.qualifiers input wire side channel)) (List.zipIdx_map_fst 0 labels)
  simp only [List.all_map, Function.comp_def] at projected
  simpa only [guardChain, projected] using value

/-- Every actual source decoder-node constructor transports its physical named value from already allocated dependencies. -/
theorem decoderNode_namedValues (parameters : Parameters) (side : Side) (node : Fin parameters.decoder.nodeCount)
    (cursor : Cursor parameters) (assignment : ℕ → Bool)
    (input : Physical.PrimaryInput parameters.channels parameters.buses) (wire : Bool)
    (prior : cursor.NamedValues assignment (parameters.physicalAssignment input wire))
    (available : cursor.QualifiersAvailable side) (before : cursor.DecoderBefore side node)
    (equations : (decoderNode parameters side node cursor).Equations assignment) :
    (decoderNode parameters side node cursor).NamedValues assignment (parameters.physicalAssignment input wire) := by
  have childAssigned : ∀ child : Fin node.val,
      .internal (.decoder side (parameters.decoder.childIndex node child)) ∈ cursor.assigned := by
    intro child
    exact before _ child.isLt
  unfold decoderNode at equations ⊢
  cases equation : parameters.decoder.node node with
  | zero =>
      simp only [equation] at equations
      dsimp only at equations ⊢
      apply Cursor.namedValues_emitNative
      · exact prior
      · exact equations
      · have semantic := parameters.roleValue_gate input wire (.decoder side node)
        simpa [Parameters.gate, Parameters.decoderGate, equation, CNF.Gate.eval,
          Parameters.physicalAssignment] using semantic.symm
  | input channel =>
      simp only [equation] at equations
      dsimp only at equations ⊢
      apply Cursor.namedValues_assign
      · exact prior
      · have semantic := parameters.roleValue_gate input wire (.decoder side node)
        have qualifier := prior (.internal (.qualifier side channel)) (available channel)
        rw [qualifier]
        simpa [Parameters.gate, Parameters.decoderGate, equation, CNF.Gate.eval,
          Parameters.internal, Parameters.positive, CNF.literalValue, Parameters.physicalAssignment] using semantic.symm
  | disj children =>
      simp only [equation] at equations
      dsimp only at equations ⊢
      let roles : List (Controller.Native.Variable parameters) := children.map fun child =>
        .internal (.decoder side (parameters.decoder.childIndex node child))
      have inputs : (children.map fun child => cursor.slots (.internal (.decoder side (parameters.decoder.childIndex node child)))) =
          roles.map cursor.slots := by simp [roles, List.map_map, Function.comp_def]
      rw [inputs]
      apply nativeOrFold_namedValues parameters cursor assignment input wire (.decoder side node) roles
      · simp [Parameters.gate, Parameters.decoderGate, equation, roles, Parameters.internal,
          Parameters.positive, List.map_map, Function.comp_def]
      · exact prior
      · intro role member
        obtain ⟨child, _, equal⟩ := List.mem_map.mp member
        subst role
        exact childAssigned child
      · simpa only [decoderNode, equation, inputs] using equations
  | guard child labels =>
      simp only [equation] at equations
      dsimp only at equations ⊢
      let childRole := Controller.Native.Variable.internal (.decoder side (parameters.decoder.childIndex node child))
      let guarded := guardChain parameters side node (cursor.slots childRole) labels cursor
      have guardedEquations : guarded.2.Equations assignment := equations
      have guardedValues : guarded.2.NamedValues assignment (parameters.physicalAssignment input wire) :=
        guardChain_namedValues parameters side node _ labels cursor assignment _ prior
      have guardValue := guardChain_value parameters side node (cursor.slots childRole) labels cursor assignment input wire
        prior available guardedEquations
      rw [prior _ (childAssigned child)] at guardValue
      have semantic : parameters.physicalAssignment input wire (.internal (.decoder side node)) =
          (parameters.physicalAssignment input wire childRole &&
            labels.all (fun channel => !parameters.qualifiers input wire side channel)) := by
        have native := parameters.roleValue_gate input wire (.decoder side node)
        simpa [Parameters.gate, Parameters.decoderGate, equation, CNF.Gate.eval,
          Parameters.internal, Parameters.positive, Parameters.negative, CNF.literalValue,
          Parameters.physicalAssignment, Parameters.roleValue, childRole,
          List.all_map, Function.comp_def] using native
      apply Cursor.namedValues_assign
      · exact guardedValues
      · exact guardValue.trans semantic.symm
  | liveAnd left right =>
      simp only [equation] at equations
      dsimp only at equations ⊢
      apply nativeAndEmit_namedValues parameters cursor assignment input wire (.decoder side node)
        [.internal (.decoder side (parameters.decoder.childIndex node left)),
          .internal (.decoder side (parameters.decoder.childIndex node right))]
      · simp [Parameters.gate, Parameters.decoderGate, equation, Parameters.internal, Parameters.positive]
      · exact prior
      · intro role member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · exact childAssigned left
        · exact childAssigned right
      · exact equations

theorem decoderNode_entries_contains (parameters : Parameters) (side : Side) (node : Fin parameters.decoder.nodeCount)
    (cursor : Cursor parameters) (entry : Entry parameters) (membership : entry ∈ cursor.entries) :
    entry ∈ (decoderNode parameters side node cursor).entries := by
  unfold decoderNode
  cases equation : parameters.decoder.node node with
  | zero => simp [Cursor.emitNative, Cursor.emit, Cursor.assign, membership]
  | input channel => exact membership
  | disj children => simp [Cursor.foldNative, Cursor.assign, membership]
  | guard child labels =>
      exact guardItems_entries_contains parameters side node labels.zipIdx _ cursor entry membership
  | liveAnd left right => simp [Cursor.emitNative, Cursor.emit, Cursor.assign, membership]

/-- A complete source decoder traversal transports its physical function using intrinsic earlier-child order. -/
theorem orderedDecoder_namedValues (parameters : Parameters) (side : Side)
    (nodes : List (Fin parameters.decoder.nodeCount)) (ascending : nodes.Pairwise (· < ·))
    (cursor : Cursor parameters) (assignment : ℕ → Bool)
    (input : Physical.PrimaryInput parameters.channels parameters.buses) (wire : Bool)
    (ready : cursor.Ready) (prior : cursor.NamedValues assignment (parameters.physicalAssignment input wire))
    (available : cursor.QualifiersAvailable side) (coverage : cursor.DecoderCoverage side nodes)
    (equations : (nodes.foldl (fun state node => decoderNode parameters side node state) cursor).Equations assignment) :
    (nodes.foldl (fun state node => decoderNode parameters side node state) cursor).NamedValues assignment
      (parameters.physicalAssignment input wire) := by
  induction nodes generalizing cursor with
  | nil => exact prior
  | cons head tail inductionHypothesis =>
      obtain ⟨headSmaller, tailAscending⟩ := List.pairwise_cons.mp ascending
      have before : cursor.DecoderBefore side head := by
        intro child smaller
        rcases coverage head (by simp) child smaller with assigned | member
        · exact assigned
        · simp only [List.mem_cons] at member
          rcases member with equal | memberTail
          · subst child
            exact False.elim ((lt_irrefl head) smaller)
          · exact False.elim ((lt_asymm smaller) (headSmaller child memberTail))
      let next := decoderNode parameters side head cursor
      have nextEquations : next.Equations assignment := Cursor.equations_of_entries_subset _ _ assignment
        (entries_foldl_contains tail (fun state node => decoderNode parameters side node state)
          (fun state node => decoderNode_entries_contains parameters side node state) next) equations
      have nextValues := decoderNode_namedValues parameters side head cursor assignment input wire prior available before nextEquations
      have nextReady := decoderNode_ready parameters side head cursor ready available before
      have nextCoverage : next.DecoderCoverage side tail := by
        intro node memberTail child smaller
        rcases coverage node (List.mem_cons_of_mem head memberTail) child smaller with assigned | member
        · apply Or.inl
          rw [decoderNode_assigned]
          exact List.mem_append_left _ assigned
        · simp only [List.mem_cons] at member
          rcases member with equal | memberTail
          · subst child
            apply Or.inl
            change .internal (.decoder side head) ∈ (decoderNode parameters side head cursor).assigned
            rw [decoderNode_assigned]
            exact List.mem_append_right _ (by simp)
          · exact Or.inr memberTail
      exact inductionHypothesis tailAscending next nextReady.1 nextValues nextReady.2 nextCoverage equations

/-- Both aliases and real producers in the complete source decoder table carry their physical named values. -/
theorem attachDecoder_namedValues (parameters : Parameters) (side : Side) (cursor : Cursor parameters)
    (assignment : ℕ → Bool) (input : Physical.PrimaryInput parameters.channels parameters.buses) (wire : Bool)
    (ready : cursor.Ready) (prior : cursor.NamedValues assignment (parameters.physicalAssignment input wire))
    (available : cursor.QualifiersAvailable side)
    (equations : (attachDecoder parameters side cursor).Equations assignment) :
    (attachDecoder parameters side cursor).NamedValues assignment (parameters.physicalAssignment input wire) := by
  apply orderedDecoder_namedValues parameters side (List.finRange parameters.decoder.nodeCount)
    (List.pairwise_lt_finRange parameters.decoder.nodeCount) cursor assignment input wire ready prior available
  · intro node member child smaller
    exact Or.inr (by simp)
  · exact equations

/-- Each replacement XOR transports the exact supplied observation-root pair, including repeated roots. -/
theorem newDifferenceStep_namedValues (parameters : Parameters) (cursor : Cursor parameters)
    (output : Fin parameters.decoder.roots.length) (assignment : ℕ → Bool)
    (input : Physical.PrimaryInput parameters.channels parameters.buses) (wire : Bool)
    (prior : cursor.NamedValues assignment (parameters.physicalAssignment input wire))
    (healthy : cursor.DecoderAvailable .healthy) (faulty : cursor.DecoderAvailable .faulty)
    (equations : (newDifferenceStep parameters cursor output).Equations assignment) :
    (newDifferenceStep parameters cursor output).NamedValues assignment (parameters.physicalAssignment input wire) := by
  apply nativeXorEmit_namedValues parameters cursor assignment input wire (.difference output)
    (.internal (.decoder .healthy (parameters.decoder.roots.get output)))
    (.internal (.decoder .faulty (parameters.decoder.roots.get output)))
  · simp [Parameters.gate, Parameters.internal, Parameters.positive]
  · exact prior
  · exact healthy _
  · exact faulty _
  · exact equations

/-- Complete replacement observations carry the physical detecting function, including its empty-output case. -/
theorem newObservations_namedValues (parameters : Parameters) (cursor : Cursor parameters)
    (assignment : ℕ → Bool) (input : Physical.PrimaryInput parameters.channels parameters.buses) (wire : Bool)
    (prior : cursor.NamedValues assignment (parameters.physicalAssignment input wire))
    (healthy : cursor.DecoderAvailable .healthy) (faulty : cursor.DecoderAvailable .faulty)
    (equations : (newObservations parameters cursor).Equations assignment) :
    (newObservations parameters cursor).NamedValues assignment (parameters.physicalAssignment input wire) := by
  let differences := (List.finRange parameters.decoder.roots.length).foldl (newDifferenceStep parameters) cursor
  have differenceEquations : differences.Equations assignment :=
    Cursor.equations_foldNative_prior _ assignment _ _ _ equations
  let property := fun state : Cursor parameters =>
    state.NamedValues assignment (parameters.physicalAssignment input wire) ∧
      state.DecoderAvailable .healthy ∧ state.DecoderAvailable .faulty
  have allValues := equations_foldl_induction (List.finRange parameters.decoder.roots.length)
    (newDifferenceStep parameters) property assignment
    (fun state output entry member => by simp [newDifferenceStep, Cursor.emitNative, Cursor.emit, Cursor.assign, member])
    (fun state output invariants stageEquations => by
      refine ⟨newDifferenceStep_namedValues parameters state output assignment input wire
        invariants.1 invariants.2.1 invariants.2.2 stageEquations, ?_, ?_⟩
      · intro node
        exact List.mem_append_left _ (invariants.2.1 node)
      · intro node
        exact List.mem_append_left _ (invariants.2.2 node)) cursor ⟨prior, healthy, faulty⟩ differenceEquations
  have allDifferences : ∀ output, .internal (.difference output) ∈ differences.assigned := by
    intro output
    dsimp [differences]
    rw [assigned_foldl _ _ (fun output => [.internal (.difference output)]) (fun _ _ => rfl)]
    simp only [List.mem_append, List.mem_flatMap, List.mem_singleton]
    exact Or.inr ⟨output, by simp, rfl⟩
  let roles : List (Controller.Native.Variable parameters) :=
    (List.finRange parameters.decoder.roots.length).map fun output => .internal (.difference output)
  have inputs : ((List.finRange parameters.decoder.roots.length).map fun output =>
      differences.slots (.internal (.difference output))) = roles.map differences.slots := by
    simp [roles, List.map_map, Function.comp_def]
  change (differences.foldNative (.internal .detected) .disjunction
    ((List.finRange parameters.decoder.roots.length).map fun output => differences.slots (.internal (.difference output)))).NamedValues
      assignment (parameters.physicalAssignment input wire)
  rw [inputs]
  apply nativeOrFold_namedValues parameters differences assignment input wire .detected roles
  · simp [Parameters.gate, roles, Parameters.internal, Parameters.positive, List.map_map, Function.comp_def]
  · exact allValues.1
  · intro role member
    obtain ⟨output, _, equal⟩ := List.mem_map.mp member
    subst role
    exact allDifferences output
  · change (differences.foldNative (.internal .detected) .disjunction
      ((List.finRange parameters.decoder.roots.length).map fun output => differences.slots (.internal (.difference output)))).Equations assignment at equations
    rw [inputs] at equations
    exact equations

theorem oldDifferenceStep_entries_contains (parameters : Parameters) (cursor : Cursor parameters)
    (index : Fin (parameters.buses + parameters.channels)) (entry : Entry parameters)
    (membership : entry ∈ cursor.entries) : entry ∈ (oldDifferenceStep parameters cursor index).entries := by
  simp [oldDifferenceStep, Cursor.emit, membership]

theorem originalObservations_entries_contains (parameters : Parameters) (cursor : Cursor parameters)
    (entry : Entry parameters) (membership : entry ∈ cursor.entries) :
    entry ∈ (originalObservations parameters cursor).entries := by
  have paired := entries_foldl_contains (List.finRange (parameters.buses + parameters.channels))
    (oldDifferenceStep parameters) (oldDifferenceStep_entries_contains parameters) cursor entry membership
  exact List.mem_append_left _ paired

theorem attachDecoder_entries_contains (parameters : Parameters) (side : Side) (cursor : Cursor parameters)
    (entry : Entry parameters) (membership : entry ∈ cursor.entries) :
    entry ∈ (attachDecoder parameters side cursor).entries :=
  entries_foldl_contains (List.finRange parameters.decoder.nodeCount)
    (fun state node => decoderNode parameters side node state)
    (fun state node => decoderNode_entries_contains parameters side node state) cursor entry membership

theorem newObservations_entries_contains (parameters : Parameters) (cursor : Cursor parameters)
    (entry : Entry parameters) (membership : entry ∈ cursor.entries) :
    entry ∈ (newObservations parameters cursor).entries := by
  have differences := entries_foldl_contains (List.finRange parameters.decoder.roots.length)
    (newDifferenceStep parameters)
    (fun state output entry member => by simp [newDifferenceStep, Cursor.emitNative, Cursor.emit, Cursor.assign, member])
    cursor entry membership
  exact List.mem_append_left _ differences

/-- The complete actual raw source program determines every assigned principal value from its physical root input. -/
theorem compile_namedValues_from_source (parameters : Parameters) (assignment : ℕ → Bool)
    (raw : parameters.layout = .raw) (equations : (compile parameters).Equations assignment) :
    (compile parameters).NamedValues assignment (parameters.physicalAssignment (sourceInput parameters assignment)
      (Physical.bridgeD parameters.bridge (sourceInput parameters assignment))) := by
  let input := sourceInput parameters assignment
  let wire := Physical.bridgeD parameters.bridge input
  let old := originalObservations parameters (controller parameters)
  let healthy := attachDecoder parameters .healthy old
  let faulty := attachDecoder parameters .faulty healthy
  have faultyEquations : faulty.Equations assignment := Cursor.equations_of_entries_subset _ _ assignment
    (newObservations_entries_contains parameters faulty) equations
  have healthyEquations : healthy.Equations assignment := Cursor.equations_of_entries_subset _ _ assignment
    (attachDecoder_entries_contains parameters .faulty healthy) faultyEquations
  have oldEquations : old.Equations assignment := Cursor.equations_of_entries_subset _ _ assignment
    (attachDecoder_entries_contains parameters .healthy old) healthyEquations
  have controllerEquations : (controller parameters).Equations assignment := Cursor.equations_of_entries_subset _ _ assignment
    (originalObservations_entries_contains parameters _) oldEquations
  have controllerValues := controller_namedValues_from_source parameters assignment raw controllerEquations
  have oldValues : old.NamedValues assignment (parameters.physicalAssignment input wire) :=
    originalObservations_namedValues parameters _ assignment _ controllerValues
  have oldReady : old.Ready := controller_originalObservations_ready parameters
  have healthyValues : healthy.NamedValues assignment (parameters.physicalAssignment input wire) :=
    attachDecoder_namedValues parameters .healthy old assignment input wire oldReady oldValues
      (controller_originalObservations_qualifiers parameters .healthy) healthyEquations
  have healthyReady : healthy.Ready := attachDecoder_ready parameters .healthy old oldReady
    (controller_originalObservations_qualifiers parameters .healthy)
  have faultyQualifiers : healthy.QualifiersAvailable .faulty := attachDecoder_qualifiersAvailable parameters .healthy .faulty old
    (controller_originalObservations_qualifiers parameters .faulty)
  have faultyValues : faulty.NamedValues assignment (parameters.physicalAssignment input wire) :=
    attachDecoder_namedValues parameters .faulty healthy assignment input wire healthyReady healthyValues faultyQualifiers faultyEquations
  exact newObservations_namedValues parameters faulty assignment input wire faultyValues
    (attachDecoder_decoderAvailable parameters .faulty .healthy healthy (attachDecoder_all_assigned parameters .healthy old))
    (attachDecoder_all_assigned parameters .faulty healthy) equations

/-- Every source equation model has exactly the native physical principal interpretation recovered from its checked root IDs. -/
theorem sourceRoleMap_physical_of_equation_model (parameters : Parameters) (assignment : ℕ → Bool)
    (raw : parameters.layout = .raw) (satisfied : CNF.Satisfies assignment (equationFormula parameters))
    (slot : Controller.Native.Variable parameters) :
    CNF.literalValue assignment (sourceRoleMap parameters slot) =
      parameters.physicalAssignment (sourceInput parameters assignment)
        (Physical.bridgeD parameters.bridge (sourceInput parameters assignment)) slot :=
  compile_namedValues_from_source parameters assignment raw (compile_equations_of_satisfied parameters assignment satisfied)
    slot (all_native_roles_assigned parameters raw slot)

/-- Full source equation models force actual source W = source D; physical flags and wire are not inputs. -/
theorem source_wire_eq_driver_of_equation_model (parameters : Parameters) (assignment : ℕ → Bool)
    (raw : parameters.layout = .raw) (satisfied : CNF.Satisfies assignment (equationFormula parameters)) :
    CNF.literalValue assignment (sourceRoleMap parameters (.primary .wire)) =
      CNF.literalValue assignment (sourceRoleMap parameters (.internal .driver)) := by
  rw [sourceRoleMap_physical_of_equation_model parameters assignment raw satisfied,
    sourceRoleMap_physical_of_equation_model parameters assignment raw satisfied]
  rfl


/-- Rephasing an actual positive source role transports the corresponding native assertion. -/
theorem source_asserted_role_holds_iff (parameters : Parameters) (assignment : ℕ → Bool)
    (raw : parameters.layout = .raw) (satisfied : CNF.Satisfies assignment (equationFormula parameters))
    (positive : ∀ slot, (sourceRoleMap parameters slot).2 = true)
    (slot : Controller.Native.Variable parameters) (phase : Bool) :
    CNF.LiteralHolds assignment ((sourceRoleMap parameters slot).1, phase) ↔
      CNF.LiteralHolds
        (parameters.physicalAssignment (sourceInput parameters assignment)
          (Physical.bridgeD parameters.bridge (sourceInput parameters assignment))) (slot, phase) := by
  have physical := sourceRoleMap_physical_of_equation_model parameters assignment raw satisfied slot
  have value : assignment (sourceRoleMap parameters slot).1 =
      parameters.physicalAssignment (sourceInput parameters assignment)
        (Physical.bridgeD parameters.bridge (sourceInput parameters assignment)) slot := by
    simpa [CNF.literalValue, positive slot] using physical
  simp only [CNF.LiteralHolds]
  rw [value]

/-- Once positive source phases are established, the four assertions have exactly the physical interface and observation meaning. -/
theorem source_assertions_physical_iff (parameters : Parameters) (assignment : ℕ → Bool)
    (raw : parameters.layout = .raw) (satisfied : CNF.Satisfies assignment (equationFormula parameters))
    (positive : ∀ slot, (sourceRoleMap parameters slot).2 = true) :
    CNF.Satisfies assignment (CNF.ofClauses ((assertions parameters).map fun literal => [literal])) ↔
      Physical.BridgeInputDetects parameters.bridge parameters.drive parameters.observations
        (sourceInput parameters assignment) (Physical.bridgeD parameters.bridge (sourceInput parameters assignment)) := by
  have interface := parameters.physicalAssignment_assertions_iff (sourceInput parameters assignment)
    (Physical.bridgeD parameters.bridge (sourceInput parameters assignment))
  rw [← interface]
  simp only [Parameters.assertionFormula, CNF.satisfies_ofClauses, List.forall_mem_map,
    CNF.clauseHolds_cons, CNF.clauseHolds_nil, or_false, assertions, Parameters.assertions,
    List.forall_mem_cons, Parameters.targetAbsent, Parameters.internal,
    Parameters.positive]
  have detected : sourceRoleMap parameters (.internal .detected) =
      ((sourceRoleMap parameters (.internal .detected)).1, true) := by
    exact Prod.ext rfl (positive _)
  rw [detected]
  simp only [source_asserted_role_holds_iff parameters assignment raw satisfied positive]
  simp


/-- Full actual source models are precisely source equation models satisfying the recovered physical detection condition. -/
theorem source_formula_physical_iff_of_positive (parameters : Parameters) (assignment : ℕ → Bool)
    (raw : parameters.layout = .raw) (positive : ∀ slot, (sourceRoleMap parameters slot).2 = true) :
    CNF.Satisfies assignment (formula parameters) ↔
      CNF.Satisfies assignment (equationFormula parameters) ∧
        Physical.BridgeInputDetects parameters.bridge parameters.drive parameters.observations
          (sourceInput parameters assignment) (Physical.bridgeD parameters.bridge (sourceInput parameters assignment)) := by
  rw [formula, CNF.satisfies_append]
  constructor
  · rintro ⟨equations, assertions⟩
    exact ⟨equations, (source_assertions_physical_iff parameters assignment raw equations positive).mp assertions⟩
  · rintro ⟨equations, detects⟩
    exact ⟨equations, (source_assertions_physical_iff parameters assignment raw equations positive).mpr detects⟩

end Controller.Native.SourceController


namespace Controller.Native.SourceSerialFold

def PositiveHandles (inputs : List (CNF.Literal ℕ)) : Prop := ∀ input ∈ inputs, input.2 = true

theorem pairLayer_positive (junction : Bounded.Junction) (lastID : ℕ) (inputs : List (CNF.Literal ℕ))
    (positive : PositiveHandles inputs) : PositiveHandles (pairLayer junction lastID inputs).handles := by
  induction inputs using List.twoStepInduction generalizing lastID with
  | nil => simp [PositiveHandles, pairLayer]
  | singleton input => simpa [PositiveHandles, pairLayer] using positive
  | cons_cons left right tail inductionHypothesis _ =>
      have tailPositive : PositiveHandles tail := fun input member => positive input (by simp [member])
      have rest := inductionHypothesis (lastID + 1) tailPositive
      intro input member
      simp only [pairLayer, List.mem_cons] at member
      rcases member with rfl | member
      · rfl
      · exact rest input member

theorem allocate_positive (junction : Bounded.Junction) (lastID : ℕ) (inputs : List (CNF.Literal ℕ))
    (positive : PositiveHandles inputs) : (allocate junction lastID inputs).output.2 = true := by
  have ranked : ∀ size, ∀ lastID inputs, inputs.length = size → PositiveHandles inputs →
      (allocate junction lastID inputs).output.2 = true := by
    intro size
    induction size using Nat.strong_induction_on with
    | h size inductionHypothesis =>
        intro lastID inputs inputSize positive
        cases inputs with
        | nil => simp [allocate]
        | cons left tail =>
            cases tail with
            | nil => simpa [allocate] using positive left (by simp)
            | cons right rest =>
                let layer := pairLayer junction lastID (left :: right :: rest)
                have shorter : layer.handles.length < size := by
                  dsimp [layer]
                  rw [pairLayer_length]
                  simp only [List.length_cons] at inputSize ⊢
                  omega
                have phase := inductionHypothesis layer.handles.length shorter layer.nextID layer.handles rfl
                  (pairLayer_positive junction lastID _ positive)
                rw [allocate]
                exact phase
  exact ranked inputs.length lastID inputs rfl positive

end Controller.Native.SourceSerialFold

namespace Controller.Native.SourceController

/-- Principal source handles have positive phase, including unassigned zero placeholders. -/
def Cursor.PositiveSlots (cursor : Cursor parameters) : Prop := ∀ slot, (cursor.slots slot).2 = true

theorem initial_positiveSlots (parameters : Parameters) : (initial parameters).PositiveSlots := by
  intro slot
  cases slot with
  | primary role => cases role <;> rfl
  | internal role => rfl

theorem Cursor.positiveSlots_assign (cursor : Cursor parameters)
    (slot : Controller.Native.Variable parameters) (handle : CNF.Literal ℕ)
    (prior : cursor.PositiveSlots) (positive : handle.2 = true) : (cursor.assign slot handle).PositiveSlots := by
  intro other
  by_cases same : other = slot
  · subst other
    simpa [Cursor.assign] using positive
  · rw [Cursor.assign_other cursor slot other same]
    exact prior other

theorem Cursor.positiveSlots_emitNative (cursor : Cursor parameters)
    (slot : Controller.Native.Variable parameters) (gate : CNF.Gate ℕ)
    (prior : cursor.PositiveSlots) : (cursor.emitNative slot gate).PositiveSlots :=
  Cursor.positiveSlots_assign _ slot _ prior rfl

theorem Cursor.positiveSlots_foldNative (cursor : Cursor parameters)
    (slot : Controller.Native.Variable parameters) (junction : Bounded.Junction) (inputs : List (CNF.Literal ℕ))
    (prior : cursor.PositiveSlots) (positive : SourceSerialFold.PositiveHandles inputs) :
    (cursor.foldNative slot junction inputs).PositiveSlots :=
  Cursor.positiveSlots_assign _ slot _ prior (SourceSerialFold.allocate_positive junction cursor.lastID inputs positive)

theorem Cursor.positiveSlots_foldNative_of_roles (cursor : Cursor parameters)
    (slot : Controller.Native.Variable parameters) (junction : Bounded.Junction)
    (roles : List (Controller.Native.Variable parameters)) (prior : cursor.PositiveSlots) :
    (cursor.foldNative slot junction (roles.map cursor.slots)).PositiveSlots := by
  apply cursor.positiveSlots_foldNative slot junction _ prior
  intro input member
  obtain ⟨role, _, equal⟩ := List.mem_map.mp member
  subst input
  exact prior role


/-- Positive principal handles are preserved by each finite source traversal. -/
theorem positiveSlots_foldl (items : List α) (step : Cursor parameters → α → Cursor parameters)
    (preserves : ∀ cursor item, cursor.PositiveSlots → (step cursor item).PositiveSlots)
    (cursor : Cursor parameters) (prior : cursor.PositiveSlots) :
    (items.foldl step cursor).PositiveSlots := by
  induction items generalizing cursor with
  | nil => exact prior
  | cons head tail inductionHypothesis =>
      exact inductionHypothesis (step cursor head) (preserves cursor head prior)

theorem firstArrays_positiveSlots (parameters : Parameters) : (firstArrays parameters).PositiveSlots := by
  let terms := (List.finRange parameters.channels).foldl (fun cursor channel =>
    let healthy := Controller.Native.Variable.internal (.term .healthy parameters.firstBus channel)
    let faulty := Controller.Native.Variable.internal (.term .faulty parameters.firstBus channel)
    let emitted := cursor.emitNative healthy
      (.and [cursor.slots (.primary (.enable channel)), cursor.slots (.primary (.request parameters.firstBus channel))])
    emitted.assign faulty (emitted.slots healthy)) (initial parameters)
  have termPositive : terms.PositiveSlots := by
    apply positiveSlots_foldl _ _ _ _ (initial_positiveSlots parameters)
    intro cursor channel prior
    let emitted := cursor.emitNative (.internal (.term .healthy parameters.firstBus channel))
      (.and [cursor.slots (.primary (.enable channel)), cursor.slots (.primary (.request parameters.firstBus channel))])
    have positive : emitted.PositiveSlots := cursor.positiveSlots_emitNative _ _ prior
    exact emitted.positiveSlots_assign _ _ positive (positive _)
  change ((List.finRange parameters.channels).foldl _ terms).PositiveSlots
  apply positiveSlots_foldl _ _ _ _ termPositive
  intro cursor channel prior
  let emitted := cursor.emitNative (.internal (.absent .healthy parameters.firstBus channel))
    (.not (cursor.slots (.internal (.term .healthy parameters.firstBus channel))))
  have positive : emitted.PositiveSlots := cursor.positiveSlots_emitNative _ _ prior
  exact emitted.positiveSlots_assign _ _ positive (positive _)

theorem interface_positiveSlots (parameters : Parameters) : (interface parameters).PositiveSlots := by
  let first := firstArrays parameters
  let driver := first.foldNative (.internal .driver) .conjunction
    (parameters.bridge.drivers.sort.map fun channel => first.slots (.internal (.absent .healthy parameters.firstBus channel)))
  have firstPositive := firstArrays_positiveSlots parameters
  have driverPositive : driver.PositiveSlots := by
    apply first.positiveSlots_foldNative _ _ _ firstPositive
    intro literal member
    obtain ⟨channel, _, equal⟩ := List.mem_map.mp member
    subst literal
    exact firstPositive _
  let remaining := driver.foldNative (.internal .remaining) .conjunction
    (parameters.bridge.remaining.sort.map fun channel => driver.slots (.internal (.absent .healthy parameters.firstBus channel)))
  have remainingPositive : remaining.PositiveSlots := by
    apply driver.positiveSlots_foldNative _ _ _ driverPositive
    intro literal member
    obtain ⟨channel, _, equal⟩ := List.mem_map.mp member
    subst literal
    exact driverPositive _
  dsimp only [interface]
  apply Cursor.positiveSlots_emitNative
  apply Cursor.positiveSlots_emitNative
  apply Cursor.positiveSlots_emitNative
  apply Cursor.positiveSlots_emitNative
  apply Cursor.positiveSlots_emitNative
  exact remainingPositive

theorem initialMasks_positiveSlots (parameters : Parameters) (side : Side)
    (cursor : Cursor parameters) (prior : cursor.PositiveSlots) :
    (initialMasks parameters side cursor).PositiveSlots := by
  apply positiveSlots_foldl _ _ _ _ prior
  intro state channel positive
  exact state.positiveSlots_emitNative _ _ positive

theorem laterBus_positiveSlots (parameters : Parameters) (side : Side) (bus : Fin parameters.buses)
    (cursor : Cursor parameters) (prior : cursor.PositiveSlots) :
    (laterBus parameters side bus cursor).PositiveSlots := by
  let terms := (List.finRange parameters.channels).foldl (fun cursor channel =>
    cursor.foldNative (.internal (.term side bus channel)) .conjunction
      ([cursor.slots (.primary (.enable channel)), cursor.slots (.primary (.request bus channel))] ++
        ((List.finRange parameters.buses).filter (fun earlier => earlier < bus)).map fun earlier =>
          cursor.slots (.internal (.mask side earlier channel)))) cursor
  have termsPositive : terms.PositiveSlots := by
    apply positiveSlots_foldl _ _ _ _ prior
    intro state channel positive
    apply state.positiveSlots_foldNative _ _ _ positive
    intro literal member
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with (rfl | rfl) | member
    · exact positive _
    · exact positive _
    · obtain ⟨earlier, _, equal⟩ := List.mem_map.mp member
      subst literal
      exact positive _
  let flag := terms.foldNative (.internal (.flag side bus)) .disjunction
    ((List.finRange parameters.channels).map fun channel => terms.slots (.internal (.term side bus channel)))
  have flagPositive : flag.PositiveSlots := by
    apply terms.positiveSlots_foldNative _ _ _ termsPositive
    intro literal member
    obtain ⟨channel, _, equal⟩ := List.mem_map.mp member
    subst literal
    exact termsPositive _
  change ((List.finRange parameters.channels).foldl _ flag).PositiveSlots
  apply positiveSlots_foldl _ _ _ _ flagPositive
  intro state channel positive
  apply Cursor.positiveSlots_emitNative
  exact state.positiveSlots_emitNative _ _ positive

theorem negateFlags_positiveSlots (parameters : Parameters) (side : Side)
    (cursor : Cursor parameters) (prior : cursor.PositiveSlots) :
    (negateFlags parameters side cursor).PositiveSlots := by
  apply positiveSlots_foldl _ _ _ _ prior
  intro state bus positive
  exact positive

theorem eligible_positiveSlots (parameters : Parameters) (side : Side) (channel : Fin parameters.channels)
    (cursor : Cursor parameters) (prior : cursor.PositiveSlots) :
    (eligible parameters side channel cursor).PositiveSlots := by
  let guarded := (List.finRange parameters.buses).foldl (fun cursor bus =>
    cursor.emitNative (.internal (.qualifierGuard side bus channel))
      (.or [cursor.negated side bus, cursor.slots (.primary (.request bus channel))])) cursor
  have guardedPositive : guarded.PositiveSlots := by
    apply positiveSlots_foldl _ _ _ _ prior
    intro state bus positive
    exact state.positiveSlots_emitNative _ _ positive
  apply guarded.positiveSlots_foldNative _ _ _ guardedPositive
  intro literal member
  simp only [List.mem_cons] at member
  rcases member with rfl | member
  · exact guardedPositive _
  · obtain ⟨bus, _, equal⟩ := List.mem_map.mp member
    subst literal
    exact guardedPositive _

theorem tail_positiveSlots (parameters : Parameters) (side : Side)
    (cursor : Cursor parameters) (prior : cursor.PositiveSlots) :
    (tail parameters side cursor).PositiveSlots := by
  apply positiveSlots_foldl _ _
    (fun state channel positive => eligible_positiveSlots parameters side channel state positive)
  apply negateFlags_positiveSlots
  apply positiveSlots_foldl _ _
    (fun state bus positive => laterBus_positiveSlots parameters side bus state positive)
  exact initialMasks_positiveSlots parameters side cursor prior

theorem controller_positiveSlots (parameters : Parameters) : (controller parameters).PositiveSlots :=
  tail_positiveSlots parameters .faulty _
    (tail_positiveSlots parameters .healthy _ (interface_positiveSlots parameters))


/-- Retained private observations allocate no principal slot updates. -/
theorem originalObservations_positiveSlots (parameters : Parameters)
    (cursor : Cursor parameters) (prior : cursor.PositiveSlots) :
    (originalObservations parameters cursor).PositiveSlots := by
  have paired : ((List.finRange (parameters.buses + parameters.channels)).foldl (fun cursor index =>
    let good := (SourceObservation.oldOutputRoles parameters .healthy)[index.val]?.getD .driver
    let bad := (SourceObservation.oldOutputRoles parameters .faulty)[index.val]?.getD .driver
    let emitted := cursor.emit (.oldDifference index)
      (.xor (cursor.slots (.internal good)) (cursor.slots (.internal bad)))
    { emitted.2 with oldDifferences := Function.update emitted.2.oldDifferences index emitted.1 }) cursor).PositiveSlots := by
      apply positiveSlots_foldl _ _ _ _ prior
      intro state index positive
      exact positive
  exact paired

theorem guardItems_positive (parameters : Parameters) (side : Side) (node : Fin parameters.decoder.nodeCount)
    (items : List (Fin parameters.channels × ℕ)) (child : CNF.Literal ℕ) (cursor : Cursor parameters)
    (prior : cursor.PositiveSlots) (childPositive : child.2 = true) :
    let guarded := items.foldl (fun state pair => state.2.emit (.guard side node pair.2)
      (.and [state.1, CNF.negate (state.2.slots (.internal (.qualifier side pair.1)))])) (child, cursor)
    guarded.2.PositiveSlots ∧ guarded.1.2 = true := by
  induction items generalizing child cursor with
  | nil => exact ⟨prior, childPositive⟩
  | cons head tail inductionHypothesis =>
      exact inductionHypothesis _ _ prior rfl

theorem guardChain_positive (parameters : Parameters) (side : Side) (node : Fin parameters.decoder.nodeCount)
    (child : CNF.Literal ℕ) (labels : List (Fin parameters.channels)) (cursor : Cursor parameters)
    (prior : cursor.PositiveSlots) (childPositive : child.2 = true) :
    (guardChain parameters side node child labels cursor).2.PositiveSlots ∧
      (guardChain parameters side node child labels cursor).1.2 = true :=
  guardItems_positive parameters side node labels.zipIdx child cursor prior childPositive

theorem decoderNode_positiveSlots (parameters : Parameters) (side : Side) (node : Fin parameters.decoder.nodeCount)
    (cursor : Cursor parameters) (prior : cursor.PositiveSlots) :
    (decoderNode parameters side node cursor).PositiveSlots := by
  unfold decoderNode
  cases equation : parameters.decoder.node node with
  | zero => exact cursor.positiveSlots_emitNative _ _ prior
  | input channel => exact cursor.positiveSlots_assign _ _ prior (prior _)
  | disj children =>
      apply cursor.positiveSlots_foldNative _ _ _ prior
      intro literal member
      obtain ⟨child, _, equal⟩ := List.mem_map.mp member
      subst literal
      exact prior _
  | guard child labels =>
      have guarded := guardChain_positive parameters side node _ labels cursor prior
        (prior (.internal (.decoder side (parameters.decoder.childIndex node child))))
      exact Cursor.positiveSlots_assign _ _ _ guarded.1 guarded.2
  | liveAnd left right => exact cursor.positiveSlots_emitNative _ _ prior

theorem attachDecoder_positiveSlots (parameters : Parameters) (side : Side)
    (cursor : Cursor parameters) (prior : cursor.PositiveSlots) :
    (attachDecoder parameters side cursor).PositiveSlots :=
  positiveSlots_foldl _ _ (fun state node positive => decoderNode_positiveSlots parameters side node state positive) cursor prior

theorem newObservations_positiveSlots (parameters : Parameters)
    (cursor : Cursor parameters) (prior : cursor.PositiveSlots) :
    (newObservations parameters cursor).PositiveSlots := by
  let differences := (List.finRange parameters.decoder.roots.length).foldl (fun cursor output =>
    cursor.emitNative (.internal (.difference output)) (.xor
      (cursor.slots (.internal (.decoder .healthy (parameters.decoder.roots.get output))))
      (cursor.slots (.internal (.decoder .faulty (parameters.decoder.roots.get output)))))) cursor
  have differencePositive : differences.PositiveSlots := by
    apply positiveSlots_foldl _ _ _ _ prior
    intro state output positive
    exact state.positiveSlots_emitNative _ _ positive
  apply differences.positiveSlots_foldNative _ _ _ differencePositive
  intro literal member
  obtain ⟨output, _, equal⟩ := List.mem_map.mp member
  subst literal
  exact differencePositive _

/-- Every principal source handle, including all four asserted roles, has positive phase. -/
theorem compile_positiveSlots (parameters : Parameters) : (compile parameters).PositiveSlots :=
  newObservations_positiveSlots parameters _
    (attachDecoder_positiveSlots parameters .faulty _
      (attachDecoder_positiveSlots parameters .healthy _
        (originalObservations_positiveSlots parameters _ (controller_positiveSlots parameters))))

theorem sourceRoleMap_positive (parameters : Parameters) (slot : Controller.Native.Variable parameters) :
    (sourceRoleMap parameters slot).2 = true := compile_positiveSlots parameters slot

end Controller.Native.SourceController


namespace Controller.Native.SourceController

/-- The actual source assertion rows have exactly the recovered physical detection semantics. -/
theorem source_assertions_physical_exact_iff (parameters : Parameters) (assignment : ℕ → Bool)
    (raw : parameters.layout = .raw) (equations : CNF.Satisfies assignment (equationFormula parameters)) :
    CNF.Satisfies assignment (CNF.ofClauses ((assertions parameters).map fun literal => [literal])) ↔
      Physical.BridgeInputDetects parameters.bridge parameters.drive parameters.observations
        (sourceInput parameters assignment) (Physical.bridgeD parameters.bridge (sourceInput parameters assignment)) :=
  source_assertions_physical_iff parameters assignment raw equations (sourceRoleMap_positive parameters)

/-- Full raw source models are exactly equation models detecting the fault on their root-loaded physical input. -/
theorem source_formula_physical_iff (parameters : Parameters) (assignment : ℕ → Bool)
    (raw : parameters.layout = .raw) :
    CNF.Satisfies assignment (formula parameters) ↔
      CNF.Satisfies assignment (equationFormula parameters) ∧
        Physical.BridgeInputDetects parameters.bridge parameters.drive parameters.observations
          (sourceInput parameters assignment) (Physical.bridgeD parameters.bridge (sourceInput parameters assignment)) :=
  source_formula_physical_iff_of_positive parameters assignment raw (sourceRoleMap_positive parameters)

/-- Every actual raw source model yields a physical detecting input without external flag, wire, or literal-phase assumptions. -/
theorem source_model_implies_physical_detection (parameters : Parameters) (assignment : ℕ → Bool)
    (raw : parameters.layout = .raw) (model : CNF.Satisfies assignment (formula parameters)) :
    Physical.BridgeInputDetects parameters.bridge parameters.drive parameters.observations
      (sourceInput parameters assignment) (Physical.bridgeD parameters.bridge (sourceInput parameters assignment)) :=
  ((source_formula_physical_iff parameters assignment raw).mp model).2

end Controller.Native.SourceController


namespace Controller.Native.SourceController

/-- A finite allocated source assignment extends to natural IDs with a fixed value outside its declared universe. -/
def sourceFiniteExtension (assignment : Fin count → Bool) (source : ℕ) : Bool :=
  if valid : 0 < source ∧ source ≤ count then assignment ⟨source - 1, by omega⟩ else false

theorem sourceFiniteExtension_sourceID (assignment : Fin count → Bool) (index : Fin count) :
    sourceFiniteExtension assignment (SourceObservation.sourceID index) = assignment index := by
  have valid : 0 < SourceObservation.sourceID index ∧ SourceObservation.sourceID index ≤ count := by
    simp only [SourceObservation.sourceID]
    omega
  rw [sourceFiniteExtension, dite_eq_left valid]
  congr 1

theorem source_root_index_val (circuit : CNF.AcyclicCircuit roots count) (index : Fin roots) :
    (circuit.rootIndex index).val = index.val := by
  induction circuit with
  | roots => rfl
  | snoc prior gate phase inductionHypothesis => exact inductionHypothesis

/-- Actual ordered source equations extend every assignment of precisely their allocated input roots. -/
theorem Cursor.exists_source_equation_extension (cursor : Cursor parameters) (ordered : cursor.Ordered)
    (roots : Fin (SourceInitialIDs.rootCount parameters) → Bool) :
    ∃ assignment : ℕ → Bool,
      (∀ index, assignment (index.val + 1) = roots index) ∧
        CNF.Satisfies assignment (CNF.ofClauses (cursor.entries.flatMap fun entry => entry.producer.rows)) := by
  obtain ⟨finite, ⟨rootValues, equations⟩, _⟩ := cursor.circuit_unique_extension roots
  let assignment := sourceFiniteExtension finite
  have restriction : assignment ∘ SourceObservation.sourceID = finite := by
    funext index
    exact sourceFiniteExtension_sourceID finite index
  refine ⟨assignment, ?_, ?_⟩
  · intro index
    have identity : SourceObservation.sourceID (cursor.toState.circuit.rootIndex index) = index.val + 1 := by
      simp only [SourceObservation.sourceID, source_root_index_val]
    calc
      assignment (index.val + 1) = assignment (SourceObservation.sourceID (cursor.toState.circuit.rootIndex index)) := by rw [identity]
      _ = finite (cursor.toState.circuit.rootIndex index) := sourceFiniteExtension_sourceID finite _
      _ = roots index := congrFun rootValues index
  · apply (cursor.source_model_iff ordered assignment).mp
    rw [restriction]
    exact equations

/-- The complete source compiler has a producer-equation model for every exact source root assignment. -/
theorem compile_exists_source_equation_extension (parameters : Parameters)
    (roots : Fin (SourceInitialIDs.rootCount parameters) → Bool) :
    ∃ assignment : ℕ → Bool,
      (∀ index, assignment (index.val + 1) = roots index) ∧ CNF.Satisfies assignment (equationFormula parameters) :=
  (compile parameters).exists_source_equation_extension (compile_ordered parameters) roots


/-- Two models with the same allocated roots agree on every declared source variable; unused natural IDs are outside the claim. -/
theorem Cursor.source_equation_unique_on_allocated (cursor : Cursor parameters) (ordered : cursor.Ordered)
    (left right : ℕ → Bool)
    (leftModel : CNF.Satisfies left (CNF.ofClauses (cursor.entries.flatMap fun entry => entry.producer.rows)))
    (rightModel : CNF.Satisfies right (CNF.ofClauses (cursor.entries.flatMap fun entry => entry.producer.rows)))
    (sameRoots : ∀ index : Fin (SourceInitialIDs.rootCount parameters), left (index.val + 1) = right (index.val + 1))
    (source : ℕ) (positive : 0 < source) (bounded : source ≤ cursor.lastID) : left source = right source := by
  let leftFinite : Fin cursor.toState.count → Bool := left ∘ SourceObservation.sourceID
  let rightFinite : Fin cursor.toState.count → Bool := right ∘ SourceObservation.sourceID
  have leftFiniteModel := (cursor.source_model_iff ordered left).mpr leftModel
  have rightFiniteModel := (cursor.source_model_iff ordered right).mpr rightModel
  have sameFiniteRoots : cursor.toState.circuit.rootValues leftFinite = cursor.toState.circuit.rootValues rightFinite := by
    funext index
    simpa only [CNF.AcyclicCircuit.rootValues, Function.comp_apply, leftFinite, rightFinite,
      SourceObservation.sourceID, source_root_index_val] using sameRoots index
  have leftEvaluation := CNF.AcyclicCircuit.eq_evaluate_of_satisfies cursor.toState.circuit
    (cursor.toState.circuit.rootValues rightFinite) leftFinite sameFiniteRoots leftFiniteModel
  have rightEvaluation := CNF.AcyclicCircuit.eq_evaluate_of_satisfies cursor.toState.circuit
    (cursor.toState.circuit.rootValues rightFinite) rightFinite rfl rightFiniteModel
  have equal := leftEvaluation.trans rightEvaluation.symm
  let index : Fin cursor.toState.count := ⟨source - 1, by rw [cursor.toState_count]; omega⟩
  have same := congrFun equal index
  have identity : SourceObservation.sourceID index = source := by
    simp only [SourceObservation.sourceID, index]
    omega
  simpa only [leftFinite, rightFinite, Function.comp_apply, identity] using same


/-- Physical source roots contain exactly enables and channel-major requests, with no wire or zero slot. -/
def sourcePhysicalRoots (parameters : Parameters)
    (input : Physical.PrimaryInput parameters.channels parameters.buses)
    (index : Fin (SourceInitialIDs.rootCount parameters)) : Bool :=
  match SourceInitialIDs.rootIndex.symm index with
  | .enable channel => input.enable channel
  | .request bus channel => input.request bus channel

theorem sourcePhysicalRoots_at_root (parameters : Parameters)
    (input : Physical.PrimaryInput parameters.channels parameters.buses)
    (root : InterfaceAlias.Root parameters.channels parameters.buses) :
    sourcePhysicalRoots parameters input (SourceInitialIDs.rootIndex root) =
      (match root with | .enable channel => input.enable channel | .request bus channel => input.request bus channel) := by
  simp only [sourcePhysicalRoots, Equiv.symm_apply_apply]

/-- Every physical enable/request input has an actual source producer-equation model with precisely those root values. -/
theorem compile_exists_source_equation_model_physical_roots (parameters : Parameters)
    (input : Physical.PrimaryInput parameters.channels parameters.buses) :
    ∃ assignment : ℕ → Bool, CNF.Satisfies assignment (equationFormula parameters) ∧
      (∀ channel, assignment (SourceInitialIDs.rootID (b := parameters.buses) (.enable channel)) = input.enable channel) ∧
      (∀ bus channel, assignment (SourceInitialIDs.rootID (.request bus channel)) = input.request bus channel) := by
  obtain ⟨assignment, rootValues, equations⟩ := compile_exists_source_equation_extension parameters (sourcePhysicalRoots parameters input)
  refine ⟨assignment, equations, ?_, ?_⟩
  · intro channel
    exact (rootValues (SourceInitialIDs.rootIndex (.enable channel))).trans
      (sourcePhysicalRoots_at_root parameters input (.enable channel))
  · intro bus channel
    exact (rootValues (SourceInitialIDs.rootIndex (.request bus channel))).trans
      (sourcePhysicalRoots_at_root parameters input (.request bus channel))

end Controller.Native.SourceController


namespace Controller.Native.SourceController

/-- The checked source root IDs recover exactly the supplied physical input; proof fields carry no extra root. -/
theorem sourceInput_eq_physical_of_roots (parameters : Parameters) (assignment : ℕ → Bool)
    (input : Physical.PrimaryInput parameters.channels parameters.buses)
    (enables : ∀ channel, assignment (SourceInitialIDs.rootID (b := parameters.buses) (.enable channel)) = input.enable channel)
    (requests : ∀ bus channel, assignment (SourceInitialIDs.rootID (.request bus channel)) = input.request bus channel) :
    sourceInput parameters assignment = input := by
  have enableEqual : (sourceInput parameters assignment).enable = input.enable := funext enables
  have requestEqual : (sourceInput parameters assignment).request = input.request := funext (fun bus => funext (requests bus))
  cases input
  dsimp only [sourceInput] at enableEqual requestEqual ⊢
  rw [enableEqual, requestEqual]

/-- A fixed physical input admits an actual source model exactly when it detects the fault. -/
theorem source_models_for_physical_input_iff (parameters : Parameters) (raw : parameters.layout = .raw)
    (input : Physical.PrimaryInput parameters.channels parameters.buses) :
    (∃ assignment : ℕ → Bool, sourceInput parameters assignment = input ∧ CNF.Satisfies assignment (formula parameters)) ↔
      Physical.BridgeInputDetects parameters.bridge parameters.drive parameters.observations input
        (Physical.bridgeD parameters.bridge input) := by
  constructor
  · rintro ⟨assignment, loaded, model⟩
    have detects := source_model_implies_physical_detection parameters assignment raw model
    simpa only [loaded] using detects
  · intro detects
    obtain ⟨assignment, equations, enables, requests⟩ := compile_exists_source_equation_model_physical_roots parameters input
    have loaded := sourceInput_eq_physical_of_roots parameters assignment input enables requests
    refine ⟨assignment, loaded, (source_formula_physical_iff parameters assignment raw).mpr ⟨equations, ?_⟩⟩
    simpa only [loaded] using detects

/-- Existential SAT projection for the complete actual raw source formula. -/
theorem source_satisfiable_iff_physical_detection (parameters : Parameters) (raw : parameters.layout = .raw) :
    CNF.Satisfiable (formula parameters) ↔
      ∃ input : Physical.PrimaryInput parameters.channels parameters.buses,
        Physical.BridgeInputDetects parameters.bridge parameters.drive parameters.observations input
          (Physical.bridgeD parameters.bridge input) := by
  constructor
  · rintro ⟨assignment, model⟩
    exact ⟨sourceInput parameters assignment, source_model_implies_physical_detection parameters assignment raw model⟩
  · rintro ⟨input, detects⟩
    obtain ⟨assignment, _, model⟩ := (source_models_for_physical_input_iff parameters raw input).mpr detects
    exact ⟨assignment, model⟩

/-- Fixed physical input models agree on every allocated source ID; slot0 and unused natural IDs are excluded. -/
theorem source_models_unique_on_allocated (parameters : Parameters) (raw : parameters.layout = .raw)
    (input : Physical.PrimaryInput parameters.channels parameters.buses) (left right : ℕ → Bool)
    (leftInput : sourceInput parameters left = input) (rightInput : sourceInput parameters right = input)
    (leftModel : CNF.Satisfies left (formula parameters)) (rightModel : CNF.Satisfies right (formula parameters))
    (source : ℕ) (positive : 0 < source) (bounded : source ≤ (compile parameters).lastID) : left source = right source := by
  have sameSourceRoots : ∀ root : InterfaceAlias.Root parameters.channels parameters.buses,
      left (SourceInitialIDs.rootID root) = right (SourceInitialIDs.rootID root) := by
    intro root
    cases root with
    | enable channel =>
        have leftValue := congrArg (fun physical : Physical.PrimaryInput parameters.channels parameters.buses => physical.enable channel) leftInput
        have rightValue := congrArg (fun physical : Physical.PrimaryInput parameters.channels parameters.buses => physical.enable channel) rightInput
        exact leftValue.trans rightValue.symm
    | request bus channel =>
        have leftValue := congrArg (fun physical : Physical.PrimaryInput parameters.channels parameters.buses => physical.request bus channel) leftInput
        have rightValue := congrArg (fun physical : Physical.PrimaryInput parameters.channels parameters.buses => physical.request bus channel) rightInput
        exact leftValue.trans rightValue.symm
  apply Cursor.source_equation_unique_on_allocated (compile parameters) (compile_ordered parameters) left right
    ((source_formula_physical_iff parameters left raw).mp leftModel).1
    ((source_formula_physical_iff parameters right raw).mp rightModel).1
    _ source positive bounded
  intro index
  let rootEquivalence := SourceInitialIDs.rootIndex (n := parameters.channels) (b := parameters.buses)
  have values := sameSourceRoots (rootEquivalence.symm index)
  have identity : rootEquivalence (rootEquivalence.symm index) = index := rootEquivalence.apply_symm_apply index
  change left ((rootEquivalence (rootEquivalence.symm index)).val + 1) =
    right ((rootEquivalence (rootEquivalence.symm index)).val + 1) at values
  rw [identity] at values
  exact values

end Controller.Native.SourceController


namespace Controller.Native.SourceSerialFold

/-- Clause rows are counted with every stored producer and duplicate occurrence retained. -/
def producerRowCount (producer : Bounded.Producer ℕ) : ℕ := producer.rows.length

/-- Literal count means total occurrences, including repeated signed literals. -/
def producerLiteralCount (producer : Bounded.Producer ℕ) : ℕ := (producer.rows.map List.length).sum

def rowCount (producers : List (Bounded.Producer ℕ)) : ℕ := (producers.map producerRowCount).sum

def literalCount (producers : List (Bounded.Producer ℕ)) : ℕ := (producers.map producerLiteralCount).sum

def foldRowCount (arity : ℕ) : ℕ := if arity = 0 then 1 else 3 * (arity - 1)
def foldLiteralCount (arity : ℕ) : ℕ := if arity = 0 then 1 else 7 * (arity - 1)

theorem rowCount_append (left right : List (Bounded.Producer ℕ)) :
    rowCount (left ++ right) = rowCount left + rowCount right := by
  simp [rowCount, List.map_append, List.sum_append]

theorem literalCount_append (left right : List (Bounded.Producer ℕ)) :
    literalCount (left ++ right) = literalCount left + literalCount right := by
  simp [literalCount, List.map_append, List.sum_append]

theorem rowCount_cons (head : Bounded.Producer ℕ) (tail : List (Bounded.Producer ℕ)) :
    rowCount (head :: tail) = producerRowCount head + rowCount tail := rfl

theorem literalCount_cons (head : Bounded.Producer ℕ) (tail : List (Bounded.Producer ℕ)) :
    literalCount (head :: tail) = producerLiteralCount head + literalCount tail := rfl

theorem rowCount_source_rows (producers : List (Bounded.Producer ℕ)) :
    rowCount producers = (producers.flatMap Bounded.Producer.rows).length := by
  induction producers with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp only [rowCount_cons, producerRowCount, List.flatMap_cons, List.length_append, inductionHypothesis]

theorem literalCount_source_rows (producers : List (Bounded.Producer ℕ)) :
    literalCount producers = ((producers.flatMap Bounded.Producer.rows).map List.length).sum := by
  induction producers with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp only [literalCount_cons, producerLiteralCount, List.flatMap_cons, List.map_append,
        List.sum_append, inductionHypothesis]

theorem binary_producer_rows (junction : Bounded.Junction) (output left right : CNF.Literal ℕ) :
    producerRowCount ⟨output, junction.gate [left, right]⟩ = 3 := by
  cases junction <;> rfl

theorem binary_producer_literals (junction : Bounded.Junction) (output left right : CNF.Literal ℕ) :
    producerLiteralCount ⟨output, junction.gate [left, right]⟩ = 7 := by
  cases junction <;> rfl

theorem empty_producer_rows (junction : Bounded.Junction) (output : CNF.Literal ℕ) :
    producerRowCount ⟨output, junction.gate []⟩ = 1 := by
  cases junction <;> rfl

theorem empty_producer_literals (junction : Bounded.Junction) (output : CNF.Literal ℕ) :
    producerLiteralCount ⟨output, junction.gate []⟩ = 1 := by
  cases junction <;> rfl

theorem pairLayer_rowCount (junction : Bounded.Junction) (lastID : ℕ) (inputs : List (CNF.Literal ℕ)) :
    rowCount (pairLayer junction lastID inputs).producers = 3 * (inputs.length / 2) := by
  induction inputs using List.twoStepInduction generalizing lastID with
  | nil => simp [pairLayer, rowCount]
  | singleton input => simp [pairLayer, rowCount]
  | cons_cons left right tail inductionHypothesis _ =>
      change producerRowCount ⟨(lastID + 1, true), junction.gate [left, right]⟩ +
        rowCount (pairLayer junction (lastID + 1) tail).producers = _
      rw [binary_producer_rows, inductionHypothesis]
      simp only [List.length_cons]
      omega

theorem pairLayer_literalCount (junction : Bounded.Junction) (lastID : ℕ) (inputs : List (CNF.Literal ℕ)) :
    literalCount (pairLayer junction lastID inputs).producers = 7 * (inputs.length / 2) := by
  induction inputs using List.twoStepInduction generalizing lastID with
  | nil => simp [pairLayer, literalCount]
  | singleton input => simp [pairLayer, literalCount]
  | cons_cons left right tail inductionHypothesis _ =>
      change producerLiteralCount ⟨(lastID + 1, true), junction.gate [left, right]⟩ +
        literalCount (pairLayer junction (lastID + 1) tail).producers = _
      rw [binary_producer_literals, inductionHypothesis]
      simp only [List.length_cons]
      omega

/-- Exact concrete serial balanced-fold row and literal counts, including the empty constant and unary alias. -/
theorem allocate_row_literal_counts (junction : Bounded.Junction) (lastID : ℕ) (inputs : List (CNF.Literal ℕ)) :
    rowCount (allocate junction lastID inputs).producers = foldRowCount inputs.length ∧
      literalCount (allocate junction lastID inputs).producers = foldLiteralCount inputs.length := by
  have ranked : ∀ size, ∀ lastID inputs, inputs.length = size →
      rowCount (allocate junction lastID inputs).producers = foldRowCount inputs.length ∧
        literalCount (allocate junction lastID inputs).producers = foldLiteralCount inputs.length := by
    intro size
    induction size using Nat.strong_induction_on with
    | h size inductionHypothesis =>
        intro lastID inputs inputSize
        cases inputs with
        | nil =>
            rw [allocate]
            simp [rowCount, literalCount, empty_producer_rows, empty_producer_literals,
              foldRowCount, foldLiteralCount]
        | cons left tail =>
            cases tail with
            | nil => simp [allocate, rowCount, literalCount, foldRowCount, foldLiteralCount]
            | cons right rest =>
                let layer := pairLayer junction lastID (left :: right :: rest)
                have layerLength : layer.handles.length = ((left :: right :: rest).length + 1) / 2 :=
                  pairLayer_length junction lastID _
                have layerPositive : 0 < layer.handles.length := by
                  rw [layerLength]
                  simp only [List.length_cons]
                  omega
                have shorter : layer.handles.length < size := by
                  rw [layerLength]
                  simp only [List.length_cons] at inputSize ⊢
                  omega
                have smaller := inductionHypothesis layer.handles.length shorter layer.nextID layer.handles rfl
                have layerRows : rowCount layer.producers = 3 * ((left :: right :: rest).length / 2) :=
                  pairLayer_rowCount junction lastID _
                have layerLiterals : literalCount layer.producers = 7 * ((left :: right :: rest).length / 2) :=
                  pairLayer_literalCount junction lastID _
                have nonempty : (left :: right :: rest).length ≠ 0 := by simp
                constructor
                · rw [allocate]
                  change rowCount (layer.producers ++ (allocate junction layer.nextID layer.handles).producers) = _
                  rw [rowCount_append, smaller.1, layerRows]
                  simp only [foldRowCount, ite_eq_right (Nat.ne_of_gt layerPositive), ite_eq_right nonempty]
                  rw [layerLength]
                  simp only [List.length_cons]
                  omega
                · rw [allocate]
                  change literalCount (layer.producers ++ (allocate junction layer.nextID layer.handles).producers) = _
                  rw [literalCount_append, smaller.2, layerLiterals]
                  simp only [foldLiteralCount, ite_eq_right (Nat.ne_of_gt layerPositive), ite_eq_right nonempty]
                  rw [layerLength]
                  simp only [List.length_cons]
                  omega
  exact ranked inputs.length lastID inputs rfl

theorem allocate_source_rows_count (junction : Bounded.Junction) (lastID : ℕ) (inputs : List (CNF.Literal ℕ)) :
    ((allocate junction lastID inputs).producers.flatMap Bounded.Producer.rows).length =
      if inputs.length = 0 then 1 else 3 * (inputs.length - 1) := by
  rw [← rowCount_source_rows]
  exact (allocate_row_literal_counts junction lastID inputs).1

theorem allocate_source_literal_count (junction : Bounded.Junction) (lastID : ℕ) (inputs : List (CNF.Literal ℕ)) :
    (((allocate junction lastID inputs).producers.flatMap Bounded.Producer.rows).map List.length).sum =
      if inputs.length = 0 then 1 else 7 * (inputs.length - 1) := by
  rw [← literalCount_source_rows]
  exact (allocate_row_literal_counts junction lastID inputs).2

end Controller.Native.SourceSerialFold

namespace Controller.Native.SourceController

/-- Number of stored producer equations, including private and unused observations. -/
def Cursor.sourceProducerCount (cursor : Cursor parameters) : ℕ := cursor.entries.length

def Cursor.sourceRowCount (cursor : Cursor parameters) : ℕ :=
  SourceSerialFold.rowCount (cursor.entries.map Entry.producer)

def Cursor.sourceLiteralCount (cursor : Cursor parameters) : ℕ :=
  SourceSerialFold.literalCount (cursor.entries.map Entry.producer)

theorem counted_entries_producers (owner : ℕ → Owner parameters) (producers : List (Bounded.Producer ℕ)) :
    ((producers.zipIdx.map fun pair => Entry.mk (owner pair.2) pair.1).map Entry.producer) = producers := by
  simp only [List.map_map]
  change producers.zipIdx.map Prod.fst = producers
  exact List.zipIdx_map_fst 0 producers

theorem Cursor.sourceProducerCount_assign (cursor : Cursor parameters) (slot : Controller.Native.Variable parameters)
    (handle : CNF.Literal ℕ) : (cursor.assign slot handle).sourceProducerCount = cursor.sourceProducerCount := rfl

theorem Cursor.sourceRowCount_assign (cursor : Cursor parameters) (slot : Controller.Native.Variable parameters)
    (handle : CNF.Literal ℕ) : (cursor.assign slot handle).sourceRowCount = cursor.sourceRowCount := rfl

theorem Cursor.sourceLiteralCount_assign (cursor : Cursor parameters) (slot : Controller.Native.Variable parameters)
    (handle : CNF.Literal ℕ) : (cursor.assign slot handle).sourceLiteralCount = cursor.sourceLiteralCount := rfl

theorem Cursor.sourceProducerCount_emit (cursor : Cursor parameters) (owner : Owner parameters) (gate : CNF.Gate ℕ) :
    (cursor.emit owner gate).2.sourceProducerCount = cursor.sourceProducerCount + 1 := by
  simp [Cursor.emit, Cursor.sourceProducerCount]

theorem Cursor.sourceRowCount_emit (cursor : Cursor parameters) (owner : Owner parameters) (gate : CNF.Gate ℕ) :
    (cursor.emit owner gate).2.sourceRowCount = cursor.sourceRowCount +
      SourceSerialFold.producerRowCount ⟨(cursor.lastID + 1, true), gate⟩ := by
  simp [Cursor.emit, Cursor.sourceRowCount, SourceSerialFold.rowCount,
    List.map_append, List.sum_append]

theorem Cursor.sourceLiteralCount_emit (cursor : Cursor parameters) (owner : Owner parameters) (gate : CNF.Gate ℕ) :
    (cursor.emit owner gate).2.sourceLiteralCount = cursor.sourceLiteralCount +
      SourceSerialFold.producerLiteralCount ⟨(cursor.lastID + 1, true), gate⟩ := by
  simp [Cursor.emit, Cursor.sourceLiteralCount, SourceSerialFold.literalCount,
    List.map_append, List.sum_append]

theorem Cursor.sourceProducerCount_emitNative (cursor : Cursor parameters)
    (slot : Controller.Native.Variable parameters) (gate : CNF.Gate ℕ) :
    (cursor.emitNative slot gate).sourceProducerCount = cursor.sourceProducerCount + 1 :=
  cursor.sourceProducerCount_emit (.native slot) gate

theorem Cursor.sourceRowCount_emitNative (cursor : Cursor parameters)
    (slot : Controller.Native.Variable parameters) (gate : CNF.Gate ℕ) :
    (cursor.emitNative slot gate).sourceRowCount = cursor.sourceRowCount +
      SourceSerialFold.producerRowCount ⟨(cursor.lastID + 1, true), gate⟩ :=
  cursor.sourceRowCount_emit (.native slot) gate

theorem Cursor.sourceLiteralCount_emitNative (cursor : Cursor parameters)
    (slot : Controller.Native.Variable parameters) (gate : CNF.Gate ℕ) :
    (cursor.emitNative slot gate).sourceLiteralCount = cursor.sourceLiteralCount +
      SourceSerialFold.producerLiteralCount ⟨(cursor.lastID + 1, true), gate⟩ :=
  cursor.sourceLiteralCount_emit (.native slot) gate

theorem Cursor.sourceProducerCount_foldNative (cursor : Cursor parameters)
    (slot : Controller.Native.Variable parameters) (junction : Bounded.Junction) (inputs : List (CNF.Literal ℕ)) :
    (cursor.foldNative slot junction inputs).sourceProducerCount = cursor.sourceProducerCount +
      (if inputs.length = 0 then 1 else inputs.length - 1) := by
  simp only [Cursor.foldNative, Cursor.assign, Cursor.sourceProducerCount, List.length_append,
    List.length_map, List.length_zipIdx, SourceSerialFold.allocate_producers]

theorem Cursor.sourceRowCount_foldNative (cursor : Cursor parameters)
    (slot : Controller.Native.Variable parameters) (junction : Bounded.Junction) (inputs : List (CNF.Literal ℕ)) :
    (cursor.foldNative slot junction inputs).sourceRowCount = cursor.sourceRowCount +
      SourceSerialFold.foldRowCount inputs.length := by
  change SourceSerialFold.rowCount ((cursor.entries ++
    ((SourceSerialFold.allocate junction cursor.lastID inputs).producers.zipIdx.map
      fun pair => Entry.mk (.fold slot pair.2) pair.1)).map Entry.producer) = _
  rw [List.map_append, SourceSerialFold.rowCount_append, counted_entries_producers,
    (SourceSerialFold.allocate_row_literal_counts junction cursor.lastID inputs).1]
  rfl

theorem Cursor.sourceLiteralCount_foldNative (cursor : Cursor parameters)
    (slot : Controller.Native.Variable parameters) (junction : Bounded.Junction) (inputs : List (CNF.Literal ℕ)) :
    (cursor.foldNative slot junction inputs).sourceLiteralCount = cursor.sourceLiteralCount +
      SourceSerialFold.foldLiteralCount inputs.length := by
  change SourceSerialFold.literalCount ((cursor.entries ++
    ((SourceSerialFold.allocate junction cursor.lastID inputs).producers.zipIdx.map
      fun pair => Entry.mk (.fold slot pair.2) pair.1)).map Entry.producer) = _
  rw [List.map_append, SourceSerialFold.literalCount_append, counted_entries_producers,
    (SourceSerialFold.allocate_row_literal_counts junction cursor.lastID inputs).2]
  rfl

/-- A finite source traversal adds its exact producer costs without deduplicating the stored schedule. -/
theorem sourceProducerCount_foldl (items : List α) (step : Cursor parameters → α → Cursor parameters)
    (cost : α → ℕ) (increment : ∀ cursor item, (step cursor item).sourceProducerCount = cursor.sourceProducerCount + cost item)
    (cursor : Cursor parameters) :
    (items.foldl step cursor).sourceProducerCount = cursor.sourceProducerCount + (items.map cost).sum := by
  induction items generalizing cursor with
  | nil => simp
  | cons head tail inductionHypothesis =>
      rw [List.foldl_cons, inductionHypothesis, increment]
      simp [List.map_cons, List.sum_cons, Nat.add_assoc]

theorem sourceRowCount_foldl (items : List α) (step : Cursor parameters → α → Cursor parameters)
    (cost : α → ℕ) (increment : ∀ cursor item, (step cursor item).sourceRowCount = cursor.sourceRowCount + cost item)
    (cursor : Cursor parameters) :
    (items.foldl step cursor).sourceRowCount = cursor.sourceRowCount + (items.map cost).sum := by
  induction items generalizing cursor with
  | nil => simp
  | cons head tail inductionHypothesis =>
      rw [List.foldl_cons, inductionHypothesis, increment]
      simp [List.map_cons, List.sum_cons, Nat.add_assoc]

theorem sourceLiteralCount_foldl (items : List α) (step : Cursor parameters → α → Cursor parameters)
    (cost : α → ℕ) (increment : ∀ cursor item, (step cursor item).sourceLiteralCount = cursor.sourceLiteralCount + cost item)
    (cursor : Cursor parameters) :
    (items.foldl step cursor).sourceLiteralCount = cursor.sourceLiteralCount + (items.map cost).sum := by
  induction items generalizing cursor with
  | nil => simp
  | cons head tail inductionHypothesis =>
      rw [List.foldl_cons, inductionHypothesis, increment]
      simp [List.map_cons, List.sum_cons, Nat.add_assoc]

end Controller.Native.SourceController

namespace Controller.Native.SourceController

theorem sourceCount_constant_sum (items : List α) (cost : ℕ) :
    (items.map (fun _ => cost)).sum = items.length * cost := by
  induction items with
  | nil => simp
  | cons head tail inductionHypothesis =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, inductionHypothesis,
        Nat.add_mul, Nat.one_mul]
      omega

theorem firstTermStep_sourceProducerCount (parameters : Parameters) (cursor : Cursor parameters)
    (channel : Fin parameters.channels) :
    (firstTermStep parameters cursor channel).sourceProducerCount = cursor.sourceProducerCount + 1 := by
  unfold firstTermStep
  rw [Cursor.sourceProducerCount_assign, Cursor.sourceProducerCount_emitNative]

theorem firstTermStep_sourceRowCount (parameters : Parameters) (cursor : Cursor parameters)
    (channel : Fin parameters.channels) :
    (firstTermStep parameters cursor channel).sourceRowCount = cursor.sourceRowCount + 3 := by
  unfold firstTermStep
  rw [Cursor.sourceRowCount_assign, Cursor.sourceRowCount_emitNative]
  rfl

theorem firstTermStep_sourceLiteralCount (parameters : Parameters) (cursor : Cursor parameters)
    (channel : Fin parameters.channels) :
    (firstTermStep parameters cursor channel).sourceLiteralCount = cursor.sourceLiteralCount + 7 := by
  unfold firstTermStep
  rw [Cursor.sourceLiteralCount_assign, Cursor.sourceLiteralCount_emitNative]
  rfl

theorem firstAbsentStep_sourceProducerCount (parameters : Parameters) (cursor : Cursor parameters)
    (channel : Fin parameters.channels) :
    (firstAbsentStep parameters cursor channel).sourceProducerCount = cursor.sourceProducerCount + 1 := by
  unfold firstAbsentStep
  rw [Cursor.sourceProducerCount_assign, Cursor.sourceProducerCount_emitNative]

theorem firstAbsentStep_sourceRowCount (parameters : Parameters) (cursor : Cursor parameters)
    (channel : Fin parameters.channels) :
    (firstAbsentStep parameters cursor channel).sourceRowCount = cursor.sourceRowCount + 2 := by
  unfold firstAbsentStep
  rw [Cursor.sourceRowCount_assign, Cursor.sourceRowCount_emitNative]
  rfl

theorem firstAbsentStep_sourceLiteralCount (parameters : Parameters) (cursor : Cursor parameters)
    (channel : Fin parameters.channels) :
    (firstAbsentStep parameters cursor channel).sourceLiteralCount = cursor.sourceLiteralCount + 4 := by
  unfold firstAbsentStep
  rw [Cursor.sourceLiteralCount_assign, Cursor.sourceLiteralCount_emitNative]
  rfl

theorem firstTerms_sourceProducerCount (parameters : Parameters) :
    (firstTerms parameters).sourceProducerCount = parameters.channels := by
  unfold firstTerms
  rw [sourceProducerCount_foldl _ _ (fun _ => 1) (firstTermStep_sourceProducerCount parameters), sourceCount_constant_sum]
  simp [Cursor.sourceProducerCount, initial]

theorem firstTerms_sourceRowCount (parameters : Parameters) :
    (firstTerms parameters).sourceRowCount = 3 * parameters.channels := by
  unfold firstTerms
  rw [sourceRowCount_foldl _ _ (fun _ => 3) (firstTermStep_sourceRowCount parameters), sourceCount_constant_sum]
  simp [Cursor.sourceRowCount, initial, SourceSerialFold.rowCount, Nat.mul_comm]

theorem firstTerms_sourceLiteralCount (parameters : Parameters) :
    (firstTerms parameters).sourceLiteralCount = 7 * parameters.channels := by
  unfold firstTerms
  rw [sourceLiteralCount_foldl _ _ (fun _ => 7) (firstTermStep_sourceLiteralCount parameters), sourceCount_constant_sum]
  simp [Cursor.sourceLiteralCount, initial, SourceSerialFold.literalCount, Nat.mul_comm]

/-- The shared source first arrays allocate each term and absent producer once, with faulty-copy aliases. -/
theorem firstArrays_source_counts (parameters : Parameters) :
    (firstArrays parameters).sourceProducerCount = 2 * parameters.channels ∧
      (firstArrays parameters).sourceRowCount = 5 * parameters.channels ∧
      (firstArrays parameters).sourceLiteralCount = 11 * parameters.channels := by
  constructor
  · change ((List.finRange parameters.channels).foldl (firstAbsentStep parameters) (firstTerms parameters)).sourceProducerCount = _
    rw [sourceProducerCount_foldl _ _ (fun _ => 1) (firstAbsentStep_sourceProducerCount parameters),
      firstTerms_sourceProducerCount, sourceCount_constant_sum]
    simp only [List.length_finRange, Nat.mul_one]
    omega
  · constructor
    · change ((List.finRange parameters.channels).foldl (firstAbsentStep parameters) (firstTerms parameters)).sourceRowCount = _
      rw [sourceRowCount_foldl _ _ (fun _ => 2) (firstAbsentStep_sourceRowCount parameters),
        firstTerms_sourceRowCount, sourceCount_constant_sum]
      simp only [List.length_finRange]
      omega
    · change ((List.finRange parameters.channels).foldl (firstAbsentStep parameters) (firstTerms parameters)).sourceLiteralCount = _
      rw [sourceLiteralCount_foldl _ _ (fun _ => 4) (firstAbsentStep_sourceLiteralCount parameters),
        firstTerms_sourceLiteralCount, sourceCount_constant_sum]
      simp only [List.length_finRange]
      omega

end Controller.Native.SourceController


namespace Controller.Native.SourceController

/-- The source allocator aliases a unary fold, while retaining an empty-fold constant. -/
def sourceFoldProducerCount (arity : ℕ) : ℕ := if arity = 0 then 1 else arity - 1

/-- Exact source interface costs, retaining its unary wire producer and ternary products. -/
theorem interface_sourceProducerCount (parameters : Parameters) :
    (interface parameters).sourceProducerCount = 2 * parameters.channels +
      sourceFoldProducerCount parameters.bridge.drivers.sort.length +
      sourceFoldProducerCount parameters.bridge.remaining.sort.length + 5 := by
  unfold interface
  simp only [Cursor.sourceProducerCount_emitNative, Cursor.sourceProducerCount_foldNative,
    List.length_map]
  rw [(firstArrays_source_counts parameters).1]
  simp only [sourceFoldProducerCount]

theorem interface_sourceRowCount (parameters : Parameters) :
    (interface parameters).sourceRowCount = 5 * parameters.channels +
      SourceSerialFold.foldRowCount parameters.bridge.drivers.sort.length +
      SourceSerialFold.foldRowCount parameters.bridge.remaining.sort.length + 14 := by
  unfold interface
  simp only [Cursor.sourceRowCount_emitNative, Cursor.sourceRowCount_foldNative,
    List.length_map]
  rw [(firstArrays_source_counts parameters).2.1]
  simp [SourceSerialFold.producerRowCount, Bounded.Producer.rows, CNF.Gate.clauses,
    Nat.add_assoc]

theorem interface_sourceLiteralCount (parameters : Parameters) :
    (interface parameters).sourceLiteralCount = 11 * parameters.channels +
      SourceSerialFold.foldLiteralCount parameters.bridge.drivers.sort.length +
      SourceSerialFold.foldLiteralCount parameters.bridge.remaining.sort.length + 32 := by
  unfold interface
  simp only [Cursor.sourceLiteralCount_emitNative, Cursor.sourceLiteralCount_foldNative,
    List.length_map]
  rw [(firstArrays_source_counts parameters).2.2]
  simp [SourceSerialFold.producerLiteralCount, Bounded.Producer.rows, CNF.Gate.clauses,
    Nat.add_assoc]

end Controller.Native.SourceController


namespace Controller.Native.SourceController

/-- Every initial source mask is a retained XOR producer. -/
theorem initialMasks_sourceProducerCount (parameters : Parameters) (side : Side)
    (cursor : Cursor parameters) :
    (initialMasks parameters side cursor).sourceProducerCount = cursor.sourceProducerCount + parameters.channels := by
  unfold initialMasks
  rw [sourceProducerCount_foldl _ _ (fun _ => 1) (by
    intro current channel
    exact current.sourceProducerCount_emitNative _ _), sourceCount_constant_sum]
  simp

theorem initialMasks_sourceRowCount (parameters : Parameters) (side : Side)
    (cursor : Cursor parameters) :
    (initialMasks parameters side cursor).sourceRowCount = cursor.sourceRowCount + 4 * parameters.channels := by
  unfold initialMasks
  rw [sourceRowCount_foldl _ _ (fun _ => 4) (by
    intro current channel
    rw [Cursor.sourceRowCount_emitNative]
    rfl), sourceCount_constant_sum]
  simp [Nat.mul_comm]

theorem initialMasks_sourceLiteralCount (parameters : Parameters) (side : Side)
    (cursor : Cursor parameters) :
    (initialMasks parameters side cursor).sourceLiteralCount = cursor.sourceLiteralCount + 12 * parameters.channels := by
  unfold initialMasks
  rw [sourceLiteralCount_foldl _ _ (fun _ => 12) (by
    intro current channel
    rw [Cursor.sourceLiteralCount_emitNative]
    rfl), sourceCount_constant_sum]
  simp [Nat.mul_comm]

end Controller.Native.SourceController


namespace Controller.Native.SourceController

/-- The actual source term arity counts every earlier-bus mask occurrence. -/
def sourceLaterTermArity (parameters : Parameters) (bus : Fin parameters.buses) : ℕ :=
  2 + ((List.finRange parameters.buses).filter (fun earlier => earlier < bus)).length

theorem laterTermStep_source_counts (parameters : Parameters) (side : Side)
    (bus : Fin parameters.buses) (cursor : Cursor parameters) (channel : Fin parameters.channels) :
    (laterTermStep parameters side bus cursor channel).sourceProducerCount = cursor.sourceProducerCount +
      sourceFoldProducerCount (sourceLaterTermArity parameters bus) ∧
    (laterTermStep parameters side bus cursor channel).sourceRowCount = cursor.sourceRowCount +
      SourceSerialFold.foldRowCount (sourceLaterTermArity parameters bus) ∧
    (laterTermStep parameters side bus cursor channel).sourceLiteralCount = cursor.sourceLiteralCount +
      SourceSerialFold.foldLiteralCount (sourceLaterTermArity parameters bus) := by
  unfold laterTermStep
  constructor
  · rw [Cursor.sourceProducerCount_foldNative]
    simp [sourceFoldProducerCount, sourceLaterTermArity, Nat.add_comm]
  · constructor
    · rw [Cursor.sourceRowCount_foldNative]
      simp only [List.length_append, List.length_cons, List.length_nil, List.length_map,
        sourceLaterTermArity]
    · rw [Cursor.sourceLiteralCount_foldNative]
      simp only [List.length_append, List.length_cons, List.length_nil, List.length_map,
        sourceLaterTermArity]

theorem laterTerms_source_counts (parameters : Parameters) (side : Side)
    (bus : Fin parameters.buses) (cursor : Cursor parameters) :
    (laterTerms parameters side bus cursor).sourceProducerCount = cursor.sourceProducerCount +
      parameters.channels * sourceFoldProducerCount (sourceLaterTermArity parameters bus) ∧
    (laterTerms parameters side bus cursor).sourceRowCount = cursor.sourceRowCount +
      parameters.channels * SourceSerialFold.foldRowCount (sourceLaterTermArity parameters bus) ∧
    (laterTerms parameters side bus cursor).sourceLiteralCount = cursor.sourceLiteralCount +
      parameters.channels * SourceSerialFold.foldLiteralCount (sourceLaterTermArity parameters bus) := by
  unfold laterTerms
  constructor
  · rw [sourceProducerCount_foldl _ _ (fun _ => sourceFoldProducerCount (sourceLaterTermArity parameters bus))
      (fun current channel => (laterTermStep_source_counts parameters side bus current channel).1),
      sourceCount_constant_sum, List.length_finRange]
  · constructor
    · rw [sourceRowCount_foldl _ _ (fun _ => SourceSerialFold.foldRowCount (sourceLaterTermArity parameters bus))
        (fun current channel => (laterTermStep_source_counts parameters side bus current channel).2.1),
        sourceCount_constant_sum, List.length_finRange]
    · rw [sourceLiteralCount_foldl _ _ (fun _ => SourceSerialFold.foldLiteralCount (sourceLaterTermArity parameters bus))
        (fun current channel => (laterTermStep_source_counts parameters side bus current channel).2.2),
        sourceCount_constant_sum, List.length_finRange]

end Controller.Native.SourceController


namespace Controller.Native.SourceController

/-- A later-bus absent value and mask retain one NOT and one XOR producer per channel. -/
theorem laterAbsentMaskStep_source_counts (parameters : Parameters) (side : Side)
    (bus : Fin parameters.buses) (cursor : Cursor parameters) (channel : Fin parameters.channels) :
    (laterAbsentMaskStep parameters side bus cursor channel).sourceProducerCount = cursor.sourceProducerCount + 2 ∧
    (laterAbsentMaskStep parameters side bus cursor channel).sourceRowCount = cursor.sourceRowCount + 6 ∧
    (laterAbsentMaskStep parameters side bus cursor channel).sourceLiteralCount = cursor.sourceLiteralCount + 16 := by
  unfold laterAbsentMaskStep
  constructor
  · simp only [Cursor.sourceProducerCount_emitNative, Nat.add_assoc]
  · constructor
    · simp only [Cursor.sourceRowCount_emitNative]
      simp [SourceSerialFold.producerRowCount, Bounded.Producer.rows, CNF.Gate.clauses, Nat.add_assoc]
    · simp only [Cursor.sourceLiteralCount_emitNative]
      simp [SourceSerialFold.producerLiteralCount, Bounded.Producer.rows, CNF.Gate.clauses, Nat.add_assoc]

theorem laterBus_sourceProducerCount (parameters : Parameters) (side : Side)
    (bus : Fin parameters.buses) (cursor : Cursor parameters) :
    (laterBus parameters side bus cursor).sourceProducerCount = cursor.sourceProducerCount +
      parameters.channels * sourceFoldProducerCount (sourceLaterTermArity parameters bus) +
      sourceFoldProducerCount parameters.channels + 2 * parameters.channels := by
  change ((List.finRange parameters.channels).foldl (laterAbsentMaskStep parameters side bus)
    ((laterTerms parameters side bus cursor).foldNative (.internal (.flag side bus)) .disjunction
      ((List.finRange parameters.channels).map fun channel =>
        (laterTerms parameters side bus cursor).slots (.internal (.term side bus channel))))).sourceProducerCount = _
  rw [sourceProducerCount_foldl _ _ (fun _ => 2)
    (fun current channel => (laterAbsentMaskStep_source_counts parameters side bus current channel).1),
    Cursor.sourceProducerCount_foldNative, (laterTerms_source_counts parameters side bus cursor).1,
    sourceCount_constant_sum]
  simp [List.length_map, List.length_finRange, sourceFoldProducerCount, Nat.mul_comm, Nat.add_assoc]

theorem laterBus_sourceRowCount (parameters : Parameters) (side : Side)
    (bus : Fin parameters.buses) (cursor : Cursor parameters) :
    (laterBus parameters side bus cursor).sourceRowCount = cursor.sourceRowCount +
      parameters.channels * SourceSerialFold.foldRowCount (sourceLaterTermArity parameters bus) +
      SourceSerialFold.foldRowCount parameters.channels + 6 * parameters.channels := by
  change ((List.finRange parameters.channels).foldl (laterAbsentMaskStep parameters side bus)
    ((laterTerms parameters side bus cursor).foldNative (.internal (.flag side bus)) .disjunction
      ((List.finRange parameters.channels).map fun channel =>
        (laterTerms parameters side bus cursor).slots (.internal (.term side bus channel))))).sourceRowCount = _
  rw [sourceRowCount_foldl _ _ (fun _ => 6)
    (fun current channel => (laterAbsentMaskStep_source_counts parameters side bus current channel).2.1),
    Cursor.sourceRowCount_foldNative, (laterTerms_source_counts parameters side bus cursor).2.1,
    sourceCount_constant_sum]
  simp [List.length_map, List.length_finRange, Nat.mul_comm, Nat.add_assoc]

theorem laterBus_sourceLiteralCount (parameters : Parameters) (side : Side)
    (bus : Fin parameters.buses) (cursor : Cursor parameters) :
    (laterBus parameters side bus cursor).sourceLiteralCount = cursor.sourceLiteralCount +
      parameters.channels * SourceSerialFold.foldLiteralCount (sourceLaterTermArity parameters bus) +
      SourceSerialFold.foldLiteralCount parameters.channels + 16 * parameters.channels := by
  change ((List.finRange parameters.channels).foldl (laterAbsentMaskStep parameters side bus)
    ((laterTerms parameters side bus cursor).foldNative (.internal (.flag side bus)) .disjunction
      ((List.finRange parameters.channels).map fun channel =>
        (laterTerms parameters side bus cursor).slots (.internal (.term side bus channel))))).sourceLiteralCount = _
  rw [sourceLiteralCount_foldl _ _ (fun _ => 16)
    (fun current channel => (laterAbsentMaskStep_source_counts parameters side bus current channel).2.2),
    Cursor.sourceLiteralCount_foldNative, (laterTerms_source_counts parameters side bus cursor).2.2,
    sourceCount_constant_sum]
  simp [List.length_map, List.length_finRange, Nat.mul_comm, Nat.add_assoc]

end Controller.Native.SourceController

namespace Controller.Native.SourceController

theorem negateFlagStep_source_counts (parameters : Parameters) (side : Side)
    (cursor : Cursor parameters) (bus : Fin parameters.buses) :
    (negateFlagStep parameters side cursor bus).sourceProducerCount = cursor.sourceProducerCount + 1 ∧
    (negateFlagStep parameters side cursor bus).sourceRowCount = cursor.sourceRowCount + 2 ∧
    (negateFlagStep parameters side cursor bus).sourceLiteralCount = cursor.sourceLiteralCount + 4 := by
  constructor
  · change (cursor.emit (.negatedFlag side bus)
          (.not (cursor.slots (.internal (.flag side bus))))).2.sourceProducerCount = _
    exact cursor.sourceProducerCount_emit _ _
  · constructor
    · change (cursor.emit (.negatedFlag side bus)
          (.not (cursor.slots (.internal (.flag side bus))))).2.sourceRowCount = _
      rw [Cursor.sourceRowCount_emit]
      rfl
    · change (cursor.emit (.negatedFlag side bus)
          (.not (cursor.slots (.internal (.flag side bus))))).2.sourceLiteralCount = _
      rw [Cursor.sourceLiteralCount_emit]
      rfl

theorem negateFlags_source_counts (parameters : Parameters) (side : Side)
    (cursor : Cursor parameters) :
    (negateFlags parameters side cursor).sourceProducerCount = cursor.sourceProducerCount + 1 * parameters.buses ∧
    (negateFlags parameters side cursor).sourceRowCount = cursor.sourceRowCount + 2 * parameters.buses ∧
    (negateFlags parameters side cursor).sourceLiteralCount = cursor.sourceLiteralCount + 4 * parameters.buses := by
  rw [negateFlags_eq]
  constructor
  · rw [sourceProducerCount_foldl _ _ (fun _ => 1)
      (fun current bus => (negateFlagStep_source_counts parameters side current bus).1),
      sourceCount_constant_sum]
    simp [Nat.mul_comm]
  · constructor
    · rw [sourceRowCount_foldl _ _ (fun _ => 2)
        (fun current bus => (negateFlagStep_source_counts parameters side current bus).2.1),
        sourceCount_constant_sum]
      simp [Nat.mul_comm]
    · rw [sourceLiteralCount_foldl _ _ (fun _ => 4)
        (fun current bus => (negateFlagStep_source_counts parameters side current bus).2.2),
        sourceCount_constant_sum]
      simp [Nat.mul_comm]

theorem eligibleGuardStep_source_counts (parameters : Parameters) (side : Side)
    (channel : Fin parameters.channels) (cursor : Cursor parameters) (bus : Fin parameters.buses) :
    (eligibleGuardStep parameters side channel cursor bus).sourceProducerCount = cursor.sourceProducerCount + 1 ∧
    (eligibleGuardStep parameters side channel cursor bus).sourceRowCount = cursor.sourceRowCount + 3 ∧
    (eligibleGuardStep parameters side channel cursor bus).sourceLiteralCount = cursor.sourceLiteralCount + 7 := by
  unfold eligibleGuardStep
  constructor
  · exact cursor.sourceProducerCount_emitNative _ _
  · constructor
    · rw [Cursor.sourceRowCount_emitNative]
      rfl
    · rw [Cursor.sourceLiteralCount_emitNative]
      rfl

end Controller.Native.SourceController


namespace Controller.Native.SourceController

/-- The source qualifier allocates all bus guards and the balanced enable-and-guards fold. -/
theorem eligible_source_counts (parameters : Parameters) (side : Side)
    (channel : Fin parameters.channels) (cursor : Cursor parameters) :
    (eligible parameters side channel cursor).sourceProducerCount = cursor.sourceProducerCount + 2 * parameters.buses ∧
    (eligible parameters side channel cursor).sourceRowCount = cursor.sourceRowCount + 6 * parameters.buses ∧
    (eligible parameters side channel cursor).sourceLiteralCount = cursor.sourceLiteralCount + 14 * parameters.buses := by
  let guarded := (List.finRange parameters.buses).foldl (eligibleGuardStep parameters side channel) cursor
  have producerCount : guarded.sourceProducerCount = cursor.sourceProducerCount + parameters.buses := by
    dsimp only [guarded]
    rw [sourceProducerCount_foldl _ _ (fun _ => 1)
      (fun current bus => (eligibleGuardStep_source_counts parameters side channel current bus).1),
      sourceCount_constant_sum]
    simp
  have rowCount : guarded.sourceRowCount = cursor.sourceRowCount + 3 * parameters.buses := by
    dsimp only [guarded]
    rw [sourceRowCount_foldl _ _ (fun _ => 3)
      (fun current bus => (eligibleGuardStep_source_counts parameters side channel current bus).2.1),
      sourceCount_constant_sum]
    simp [Nat.mul_comm]
  have literalCount : guarded.sourceLiteralCount = cursor.sourceLiteralCount + 7 * parameters.buses := by
    dsimp only [guarded]
    rw [sourceLiteralCount_foldl _ _ (fun _ => 7)
      (fun current bus => (eligibleGuardStep_source_counts parameters side channel current bus).2.2),
      sourceCount_constant_sum]
    simp [Nat.mul_comm]
  change (guarded.foldNative (.internal (.qualifier side channel)) .conjunction
      (guarded.slots (.primary (.enable channel)) ::
        (List.finRange parameters.buses).map fun bus => guarded.slots (.internal (.qualifierGuard side bus channel)))).sourceProducerCount = _ ∧
    (guarded.foldNative (.internal (.qualifier side channel)) .conjunction
      (guarded.slots (.primary (.enable channel)) ::
        (List.finRange parameters.buses).map fun bus => guarded.slots (.internal (.qualifierGuard side bus channel)))).sourceRowCount = _ ∧
    (guarded.foldNative (.internal (.qualifier side channel)) .conjunction
      (guarded.slots (.primary (.enable channel)) ::
        (List.finRange parameters.buses).map fun bus => guarded.slots (.internal (.qualifierGuard side bus channel)))).sourceLiteralCount = _
  constructor
  · rw [Cursor.sourceProducerCount_foldNative, producerCount]
    simp [List.length_finRange] <;> omega
  · constructor
    · rw [Cursor.sourceRowCount_foldNative, rowCount]
      simp [SourceSerialFold.foldRowCount, List.length_finRange] <;> omega
    · rw [Cursor.sourceLiteralCount_foldNative, literalCount]
      simp [SourceSerialFold.foldLiteralCount, List.length_finRange] <;> omega

end Controller.Native.SourceController

namespace Controller.Native.SourceController

def sourceTailProducerCost (parameters : Parameters) : ℕ :=
  1 * parameters.channels +
    ((((List.finRange parameters.buses).filter (fun bus => bus.val != 0)).map fun bus =>
      parameters.channels * sourceFoldProducerCount (sourceLaterTermArity parameters bus) +
        sourceFoldProducerCount parameters.channels + 2 * parameters.channels)).sum +
    1 * parameters.buses + parameters.channels * (2 * parameters.buses)

def sourceTailRowCost (parameters : Parameters) : ℕ :=
  4 * parameters.channels +
    ((((List.finRange parameters.buses).filter (fun bus => bus.val != 0)).map fun bus =>
      parameters.channels * SourceSerialFold.foldRowCount (sourceLaterTermArity parameters bus) +
        SourceSerialFold.foldRowCount parameters.channels + 6 * parameters.channels)).sum +
    2 * parameters.buses + parameters.channels * (6 * parameters.buses)

def sourceTailLiteralCost (parameters : Parameters) : ℕ :=
  12 * parameters.channels +
    ((((List.finRange parameters.buses).filter (fun bus => bus.val != 0)).map fun bus =>
      parameters.channels * SourceSerialFold.foldLiteralCount (sourceLaterTermArity parameters bus) +
        SourceSerialFold.foldLiteralCount parameters.channels + 16 * parameters.channels)).sum +
    4 * parameters.buses + parameters.channels * (14 * parameters.buses)

/-- Exact concrete tail totals retain the ordered positive-bus traversal and all its fold occurrences. -/
theorem tail_source_counts (parameters : Parameters) (side : Side) (cursor : Cursor parameters) :
    (tail parameters side cursor).sourceProducerCount = cursor.sourceProducerCount + sourceTailProducerCost parameters ∧
    (tail parameters side cursor).sourceRowCount = cursor.sourceRowCount + sourceTailRowCost parameters ∧
    (tail parameters side cursor).sourceLiteralCount = cursor.sourceLiteralCount + sourceTailLiteralCost parameters := by
  unfold tail
  constructor
  · rw [sourceProducerCount_foldl _ _ (fun _ => 2 * parameters.buses)
      (fun current channel => (eligible_source_counts parameters side channel current).1),
      (negateFlags_source_counts parameters side _).1,
      sourceProducerCount_foldl _ _ (fun bus => parameters.channels * sourceFoldProducerCount (sourceLaterTermArity parameters bus) +
        sourceFoldProducerCount parameters.channels + 2 * parameters.channels)
        (fun current bus => by simpa only [Nat.add_assoc] using
          laterBus_sourceProducerCount parameters side bus current),
      initialMasks_sourceProducerCount, sourceCount_constant_sum]
    simp [sourceTailProducerCost, Nat.add_assoc]
  · constructor
    · rw [sourceRowCount_foldl _ _ (fun _ => 6 * parameters.buses)
        (fun current channel => (eligible_source_counts parameters side channel current).2.1),
        (negateFlags_source_counts parameters side _).2.1,
        sourceRowCount_foldl _ _ (fun bus => parameters.channels * SourceSerialFold.foldRowCount (sourceLaterTermArity parameters bus) +
          SourceSerialFold.foldRowCount parameters.channels + 6 * parameters.channels)
          (fun current bus => by simpa only [Nat.add_assoc] using
          laterBus_sourceRowCount parameters side bus current),
        initialMasks_sourceRowCount, sourceCount_constant_sum]
      simp [sourceTailRowCost, Nat.add_assoc]
    · rw [sourceLiteralCount_foldl _ _ (fun _ => 14 * parameters.buses)
        (fun current channel => (eligible_source_counts parameters side channel current).2.2),
        (negateFlags_source_counts parameters side _).2.2,
        sourceLiteralCount_foldl _ _ (fun bus => parameters.channels * SourceSerialFold.foldLiteralCount (sourceLaterTermArity parameters bus) +
          SourceSerialFold.foldLiteralCount parameters.channels + 16 * parameters.channels)
          (fun current bus => by simpa only [Nat.add_assoc] using
          laterBus_sourceLiteralCount parameters side bus current),
        initialMasks_sourceLiteralCount, sourceCount_constant_sum]
      simp [sourceTailLiteralCost, Nat.add_assoc]

end Controller.Native.SourceController

namespace Controller.Native.SourceController

def sourceControllerProducerCost (parameters : Parameters) : ℕ :=
  2 * parameters.channels + sourceFoldProducerCount parameters.bridge.drivers.sort.length +
    sourceFoldProducerCount parameters.bridge.remaining.sort.length + 5 + 2 * sourceTailProducerCost parameters

def sourceControllerRowCost (parameters : Parameters) : ℕ :=
  5 * parameters.channels + SourceSerialFold.foldRowCount parameters.bridge.drivers.sort.length +
    SourceSerialFold.foldRowCount parameters.bridge.remaining.sort.length + 14 + 2 * sourceTailRowCost parameters

def sourceControllerLiteralCost (parameters : Parameters) : ℕ :=
  11 * parameters.channels + SourceSerialFold.foldLiteralCount parameters.bridge.drivers.sort.length +
    SourceSerialFold.foldLiteralCount parameters.bridge.remaining.sort.length + 32 + 2 * sourceTailLiteralCost parameters

/-- Both concrete controller tails use the same count schedule and share the first-array/interface prefix. -/
theorem controller_source_counts (parameters : Parameters) :
    (controller parameters).sourceProducerCount = sourceControllerProducerCost parameters ∧
    (controller parameters).sourceRowCount = sourceControllerRowCost parameters ∧
    (controller parameters).sourceLiteralCount = sourceControllerLiteralCost parameters := by
  unfold controller
  constructor
  · rw [(tail_source_counts parameters .faulty _).1,
      (tail_source_counts parameters .healthy _).1, interface_sourceProducerCount]
    simp only [sourceControllerProducerCost]
    omega
  · constructor
    · rw [(tail_source_counts parameters .faulty _).2.1,
        (tail_source_counts parameters .healthy _).2.1, interface_sourceRowCount]
      simp only [sourceControllerRowCost]
      omega
    · rw [(tail_source_counts parameters .faulty _).2.2,
        (tail_source_counts parameters .healthy _).2.2, interface_sourceLiteralCount]
      simp only [sourceControllerLiteralCost]
      omega

end Controller.Native.SourceController


namespace Controller.Native.SourceController

theorem oldDifferenceStep_source_counts (parameters : Parameters) (cursor : Cursor parameters)
    (index : Fin (parameters.buses + parameters.channels)) :
    (oldDifferenceStep parameters cursor index).sourceProducerCount = cursor.sourceProducerCount + 1 ∧
    (oldDifferenceStep parameters cursor index).sourceRowCount = cursor.sourceRowCount + 4 ∧
    (oldDifferenceStep parameters cursor index).sourceLiteralCount = cursor.sourceLiteralCount + 12 := by
  constructor
  · change (cursor.emit (.oldDifference index) (.xor _ _)).2.sourceProducerCount = _
    exact cursor.sourceProducerCount_emit _ _
  · constructor
    · change (cursor.emit (.oldDifference index) (.xor _ _)).2.sourceRowCount = _
      rw [Cursor.sourceRowCount_emit]
      rfl
    · change (cursor.emit (.oldDifference index) (.xor _ _)).2.sourceLiteralCount = _
      rw [Cursor.sourceLiteralCount_emit]
      rfl

theorem pairedOldOutputs_source_counts (parameters : Parameters) (cursor : Cursor parameters) :
    (pairedOldOutputs parameters cursor).sourceProducerCount = cursor.sourceProducerCount + (parameters.buses + parameters.channels) ∧
    (pairedOldOutputs parameters cursor).sourceRowCount = cursor.sourceRowCount + 4 * (parameters.buses + parameters.channels) ∧
    (pairedOldOutputs parameters cursor).sourceLiteralCount = cursor.sourceLiteralCount + 12 * (parameters.buses + parameters.channels) := by
  unfold pairedOldOutputs
  constructor
  · rw [sourceProducerCount_foldl _ _ (fun _ => 1)
      (fun current index => (oldDifferenceStep_source_counts parameters current index).1), sourceCount_constant_sum]
    simp
  · constructor
    · rw [sourceRowCount_foldl _ _ (fun _ => 4)
        (fun current index => (oldDifferenceStep_source_counts parameters current index).2.1), sourceCount_constant_sum]
      simp [Nat.mul_comm]
    · rw [sourceLiteralCount_foldl _ _ (fun _ => 12)
        (fun current index => (oldDifferenceStep_source_counts parameters current index).2.2), sourceCount_constant_sum]
      simp [Nat.mul_comm]

/-- The unused original observations remain allocated and contribute their full XOR-and-OR costs. -/
theorem originalObservations_source_counts (parameters : Parameters) (cursor : Cursor parameters) :
    (originalObservations parameters cursor).sourceProducerCount = cursor.sourceProducerCount +
      (parameters.buses + parameters.channels) + sourceFoldProducerCount (parameters.buses + parameters.channels) ∧
    (originalObservations parameters cursor).sourceRowCount = cursor.sourceRowCount +
      4 * (parameters.buses + parameters.channels) + SourceSerialFold.foldRowCount (parameters.buses + parameters.channels) ∧
    (originalObservations parameters cursor).sourceLiteralCount = cursor.sourceLiteralCount +
      12 * (parameters.buses + parameters.channels) + SourceSerialFold.foldLiteralCount (parameters.buses + parameters.channels) := by
  let paired := pairedOldOutputs parameters cursor
  let inputs := (List.finRange (parameters.buses + parameters.channels)).map paired.oldDifferences
  let allocated := SourceSerialFold.allocate .disjunction paired.lastID inputs
  constructor
  · change (paired.entries ++ (allocated.producers.zipIdx.map
      (fun pair : Bounded.Producer ℕ × ℕ => Entry.mk (parameters := parameters) (.oldDetected pair.2) pair.1))).length = _
    simp only [List.length_append, List.length_map, List.length_zipIdx]
    change paired.sourceProducerCount + allocated.producers.length = _
    rw [(pairedOldOutputs_source_counts parameters cursor).1]
    simp [allocated, inputs, SourceSerialFold.allocate_producers, sourceFoldProducerCount]
  · constructor
    · change SourceSerialFold.rowCount ((paired.entries ++ (allocated.producers.zipIdx.map
        (fun pair : Bounded.Producer ℕ × ℕ => Entry.mk (parameters := parameters) (.oldDetected pair.2) pair.1))).map Entry.producer) = _
      rw [List.map_append, SourceSerialFold.rowCount_append, counted_entries_producers,
        (SourceSerialFold.allocate_row_literal_counts .disjunction paired.lastID inputs).1]
      change paired.sourceRowCount + SourceSerialFold.foldRowCount inputs.length = _
      rw [(pairedOldOutputs_source_counts parameters cursor).2.1]
      simp [inputs]
    · change SourceSerialFold.literalCount ((paired.entries ++ (allocated.producers.zipIdx.map
        (fun pair : Bounded.Producer ℕ × ℕ => Entry.mk (parameters := parameters) (.oldDetected pair.2) pair.1))).map Entry.producer) = _
      rw [List.map_append, SourceSerialFold.literalCount_append, counted_entries_producers,
        (SourceSerialFold.allocate_row_literal_counts .disjunction paired.lastID inputs).2]
      change paired.sourceLiteralCount + SourceSerialFold.foldLiteralCount inputs.length = _
      rw [(pairedOldOutputs_source_counts parameters cursor).2.2]
      simp [inputs]

end Controller.Native.SourceController


namespace Controller.Native.SourceController

theorem sourceCount_pair_foldl (metric : Cursor parameters → ℕ) (items : List α)
    (step : (CNF.Literal ℕ × Cursor parameters) → α → (CNF.Literal ℕ × Cursor parameters))
    (cost : ℕ) (increment : ∀ state item, metric (step state item).2 = metric state.2 + cost)
    (state : CNF.Literal ℕ × Cursor parameters) :
    metric (items.foldl step state).2 = metric state.2 + items.length * cost := by
  induction items generalizing state with
  | nil => simp
  | cons head tail inductionHypothesis =>
      rw [List.foldl_cons, inductionHypothesis, increment]
      simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

/-- Each stored guard occurrence allocates one binary AND, including repeated channel labels. -/
theorem guardChain_source_counts (parameters : Parameters) (side : Side)
    (node : Fin parameters.decoder.nodeCount) (child : CNF.Literal ℕ)
    (labels : List (Fin parameters.channels)) (cursor : Cursor parameters) :
    (guardChain parameters side node child labels cursor).2.sourceProducerCount = cursor.sourceProducerCount + labels.length ∧
    (guardChain parameters side node child labels cursor).2.sourceRowCount = cursor.sourceRowCount + 3 * labels.length ∧
    (guardChain parameters side node child labels cursor).2.sourceLiteralCount = cursor.sourceLiteralCount + 7 * labels.length := by
  unfold guardChain
  constructor
  · rw [sourceCount_pair_foldl Cursor.sourceProducerCount _ _ 1 (by
      intro state pair
      exact state.2.sourceProducerCount_emit _ _)]
    simp
  · constructor
    · rw [sourceCount_pair_foldl Cursor.sourceRowCount _ _ 3 (by
        intro state pair
        rw [Cursor.sourceRowCount_emit]
        rfl)]
      simp [Nat.mul_comm]
    · rw [sourceCount_pair_foldl Cursor.sourceLiteralCount _ _ 7 (by
        intro state pair
        rw [Cursor.sourceLiteralCount_emit]
        rfl)]
      simp [Nat.mul_comm]

end Controller.Native.SourceController

namespace Controller.Native.SourceController

def sourceDecoderNodeProducerCost (parameters : Parameters) (node : Fin parameters.decoder.nodeCount) : ℕ :=
  match parameters.decoder.node node with
  | .zero => 1
  | .input _ => 0
  | .disj children => sourceFoldProducerCount children.length
  | .guard _ labels => 1 * labels.length
  | .liveAnd _ _ => 1

def sourceDecoderNodeRowCost (parameters : Parameters) (node : Fin parameters.decoder.nodeCount) : ℕ :=
  match parameters.decoder.node node with
  | .zero => 1
  | .input _ => 0
  | .disj children => SourceSerialFold.foldRowCount children.length
  | .guard _ labels => 3 * labels.length
  | .liveAnd _ _ => 3

def sourceDecoderNodeLiteralCost (parameters : Parameters) (node : Fin parameters.decoder.nodeCount) : ℕ :=
  match parameters.decoder.node node with
  | .zero => 1
  | .input _ => 0
  | .disj children => SourceSerialFold.foldLiteralCount children.length
  | .guard _ labels => 7 * labels.length
  | .liveAnd _ _ => 7

/-- Every actual decoder node has its exact source allocation cost, including private guard occurrences. -/
theorem decoderNode_source_counts (parameters : Parameters) (side : Side)
    (node : Fin parameters.decoder.nodeCount) (cursor : Cursor parameters) :
    (decoderNode parameters side node cursor).sourceProducerCount = cursor.sourceProducerCount + sourceDecoderNodeProducerCost parameters node ∧
    (decoderNode parameters side node cursor).sourceRowCount = cursor.sourceRowCount + sourceDecoderNodeRowCost parameters node ∧
    (decoderNode parameters side node cursor).sourceLiteralCount = cursor.sourceLiteralCount + sourceDecoderNodeLiteralCost parameters node := by
  unfold decoderNode
  cases equation : parameters.decoder.node node with
  | zero =>
      simp [sourceDecoderNodeProducerCost, sourceDecoderNodeRowCost, sourceDecoderNodeLiteralCost,
        equation, Cursor.sourceProducerCount_emitNative, Cursor.sourceRowCount_emitNative,
        Cursor.sourceLiteralCount_emitNative, SourceSerialFold.producerRowCount,
        SourceSerialFold.producerLiteralCount, Bounded.Producer.rows, CNF.Gate.clauses]
  | input channel =>
      simp [sourceDecoderNodeProducerCost, sourceDecoderNodeRowCost, sourceDecoderNodeLiteralCost,
        equation, Cursor.sourceProducerCount_assign, Cursor.sourceRowCount_assign, Cursor.sourceLiteralCount_assign]
  | disj children =>
      simp [sourceDecoderNodeProducerCost, sourceDecoderNodeRowCost, sourceDecoderNodeLiteralCost,
        equation, Cursor.sourceProducerCount_foldNative, Cursor.sourceRowCount_foldNative,
        Cursor.sourceLiteralCount_foldNative, sourceFoldProducerCount]
  | guard child labels =>
      simpa only [sourceDecoderNodeProducerCost, sourceDecoderNodeRowCost, sourceDecoderNodeLiteralCost,
        equation, Cursor.sourceProducerCount_assign, Cursor.sourceRowCount_assign,
        Cursor.sourceLiteralCount_assign, Nat.one_mul] using
        guardChain_source_counts parameters side node
          (cursor.slots (.internal (.decoder side (parameters.decoder.childIndex node child)))) labels cursor
  | liveAnd left right =>
      simp [sourceDecoderNodeProducerCost, sourceDecoderNodeRowCost, sourceDecoderNodeLiteralCost,
        equation, Cursor.sourceProducerCount_emitNative, Cursor.sourceRowCount_emitNative,
        Cursor.sourceLiteralCount_emitNative, SourceSerialFold.producerRowCount,
        SourceSerialFold.producerLiteralCount, Bounded.Producer.rows, CNF.Gate.clauses]

def sourceDecoderProducerCost (parameters : Parameters) : ℕ :=
  ((List.finRange parameters.decoder.nodeCount).map (sourceDecoderNodeProducerCost parameters)).sum

def sourceDecoderRowCost (parameters : Parameters) : ℕ :=
  ((List.finRange parameters.decoder.nodeCount).map (sourceDecoderNodeRowCost parameters)).sum

def sourceDecoderLiteralCost (parameters : Parameters) : ℕ :=
  ((List.finRange parameters.decoder.nodeCount).map (sourceDecoderNodeLiteralCost parameters)).sum

theorem attachDecoder_source_counts (parameters : Parameters) (side : Side) (cursor : Cursor parameters) :
    (attachDecoder parameters side cursor).sourceProducerCount = cursor.sourceProducerCount + sourceDecoderProducerCost parameters ∧
    (attachDecoder parameters side cursor).sourceRowCount = cursor.sourceRowCount + sourceDecoderRowCost parameters ∧
    (attachDecoder parameters side cursor).sourceLiteralCount = cursor.sourceLiteralCount + sourceDecoderLiteralCost parameters := by
  unfold attachDecoder
  constructor
  · exact sourceProducerCount_foldl _ _ _
      (fun current node => (decoderNode_source_counts parameters side node current).1) cursor
  · constructor
    · exact sourceRowCount_foldl _ _ _
        (fun current node => (decoderNode_source_counts parameters side node current).2.1) cursor
    · exact sourceLiteralCount_foldl _ _ _
        (fun current node => (decoderNode_source_counts parameters side node current).2.2) cursor

end Controller.Native.SourceController


namespace Controller.Native.SourceController

theorem newDifferenceStep_source_counts (parameters : Parameters) (cursor : Cursor parameters)
    (output : Fin parameters.decoder.roots.length) :
    (newDifferenceStep parameters cursor output).sourceProducerCount = cursor.sourceProducerCount + 1 ∧
    (newDifferenceStep parameters cursor output).sourceRowCount = cursor.sourceRowCount + 4 ∧
    (newDifferenceStep parameters cursor output).sourceLiteralCount = cursor.sourceLiteralCount + 12 := by
  unfold newDifferenceStep
  constructor
  · exact cursor.sourceProducerCount_emitNative _ _
  · constructor
    · rw [Cursor.sourceRowCount_emitNative]
      rfl
    · rw [Cursor.sourceLiteralCount_emitNative]
      rfl

/-- Replacement observations retain all XORs and allocate a false detected constant when there are no roots. -/
theorem newObservations_source_counts (parameters : Parameters) (cursor : Cursor parameters) :
    (newObservations parameters cursor).sourceProducerCount = cursor.sourceProducerCount +
      parameters.decoder.roots.length + sourceFoldProducerCount parameters.decoder.roots.length ∧
    (newObservations parameters cursor).sourceRowCount = cursor.sourceRowCount +
      4 * parameters.decoder.roots.length + SourceSerialFold.foldRowCount parameters.decoder.roots.length ∧
    (newObservations parameters cursor).sourceLiteralCount = cursor.sourceLiteralCount +
      12 * parameters.decoder.roots.length + SourceSerialFold.foldLiteralCount parameters.decoder.roots.length := by
  let differences := (List.finRange parameters.decoder.roots.length).foldl (newDifferenceStep parameters) cursor
  have producerCount : differences.sourceProducerCount = cursor.sourceProducerCount + parameters.decoder.roots.length := by
    dsimp only [differences]
    rw [sourceProducerCount_foldl _ _ (fun _ => 1)
      (fun current output => (newDifferenceStep_source_counts parameters current output).1), sourceCount_constant_sum]
    simp
  have rowCount : differences.sourceRowCount = cursor.sourceRowCount + 4 * parameters.decoder.roots.length := by
    dsimp only [differences]
    rw [sourceRowCount_foldl _ _ (fun _ => 4)
      (fun current output => (newDifferenceStep_source_counts parameters current output).2.1), sourceCount_constant_sum]
    simp [Nat.mul_comm]
  have literalCount : differences.sourceLiteralCount = cursor.sourceLiteralCount + 12 * parameters.decoder.roots.length := by
    dsimp only [differences]
    rw [sourceLiteralCount_foldl _ _ (fun _ => 12)
      (fun current output => (newDifferenceStep_source_counts parameters current output).2.2), sourceCount_constant_sum]
    simp [Nat.mul_comm]
  constructor
  · change (differences.foldNative (.internal .detected) .disjunction
      ((List.finRange parameters.decoder.roots.length).map fun output =>
        differences.slots (.internal (.difference output)))).sourceProducerCount = _
    rw [Cursor.sourceProducerCount_foldNative, producerCount]
    simp [sourceFoldProducerCount]
  · constructor
    · change (differences.foldNative (.internal .detected) .disjunction
        ((List.finRange parameters.decoder.roots.length).map fun output =>
          differences.slots (.internal (.difference output)))).sourceRowCount = _
      rw [Cursor.sourceRowCount_foldNative, rowCount]
      simp
    · change (differences.foldNative (.internal .detected) .disjunction
        ((List.finRange parameters.decoder.roots.length).map fun output =>
          differences.slots (.internal (.difference output)))).sourceLiteralCount = _
      rw [Cursor.sourceLiteralCount_foldNative, literalCount]
      simp

end Controller.Native.SourceController

namespace Controller.Native.SourceController

def sourceCompileProducerCost (parameters : Parameters) : ℕ :=
  sourceControllerProducerCost parameters + 1 * (parameters.buses + parameters.channels) +
    sourceFoldProducerCount (parameters.buses + parameters.channels) + 2 * sourceDecoderProducerCost parameters +
    1 * parameters.decoder.roots.length + sourceFoldProducerCount parameters.decoder.roots.length

def sourceCompileRowCost (parameters : Parameters) : ℕ :=
  sourceControllerRowCost parameters + 4 * (parameters.buses + parameters.channels) +
    SourceSerialFold.foldRowCount (parameters.buses + parameters.channels) + 2 * sourceDecoderRowCost parameters +
    4 * parameters.decoder.roots.length + SourceSerialFold.foldRowCount parameters.decoder.roots.length

def sourceCompileLiteralCost (parameters : Parameters) : ℕ :=
  sourceControllerLiteralCost parameters + 12 * (parameters.buses + parameters.channels) +
    SourceSerialFold.foldLiteralCount (parameters.buses + parameters.channels) + 2 * sourceDecoderLiteralCost parameters +
    12 * parameters.decoder.roots.length + SourceSerialFold.foldLiteralCount parameters.decoder.roots.length

/-- Exact complete source counts retain the old observation circuit and both decoder attachments. -/
theorem compile_source_counts (parameters : Parameters) :
    (compile parameters).sourceProducerCount = sourceCompileProducerCost parameters ∧
    (compile parameters).sourceRowCount = sourceCompileRowCost parameters ∧
    (compile parameters).sourceLiteralCount = sourceCompileLiteralCost parameters := by
  unfold compile
  constructor
  · rw [(newObservations_source_counts parameters _).1,
      (attachDecoder_source_counts parameters .faulty _).1,
      (attachDecoder_source_counts parameters .healthy _).1,
      (originalObservations_source_counts parameters _).1, (controller_source_counts parameters).1]
    simp only [sourceCompileProducerCost]
    omega
  · constructor
    · rw [(newObservations_source_counts parameters _).2.1,
        (attachDecoder_source_counts parameters .faulty _).2.1,
        (attachDecoder_source_counts parameters .healthy _).2.1,
        (originalObservations_source_counts parameters _).2.1, (controller_source_counts parameters).2.1]
      simp only [sourceCompileRowCost]
      omega
    · rw [(newObservations_source_counts parameters _).2.2,
        (attachDecoder_source_counts parameters .faulty _).2.2,
        (attachDecoder_source_counts parameters .healthy _).2.2,
        (originalObservations_source_counts parameters _).2.2, (controller_source_counts parameters).2.2]
      simp only [sourceCompileLiteralCost]
      omega

/-- The allocated source universe consists of the initial positive roots and every stored producer output. -/
theorem compile_lastID_source_count (parameters : Parameters) :
    (compile parameters).lastID = SourceInitialIDs.rootCount parameters + sourceCompileProducerCost parameters := by
  change SourceInitialIDs.rootCount parameters + (compile parameters).sourceProducerCount = _
  rw [(compile_source_counts parameters).1]

end Controller.Native.SourceController


namespace Controller.Native.SourceController

theorem equationFormula_source_rows (parameters : Parameters) :
    (equationFormula parameters).clauses.size = (compile parameters).sourceRowCount := by
  simp [equationFormula, CNF.ofClauses, Cursor.sourceRowCount,
    SourceSerialFold.rowCount_source_rows, List.flatMap_map]

theorem equationFormula_source_literals (parameters : Parameters) :
    (((equationFormula parameters).clauses.toList).map List.length).sum =
      (compile parameters).sourceLiteralCount := by
  simp [equationFormula, CNF.ofClauses, Cursor.sourceLiteralCount,
    SourceSerialFold.literalCount_source_rows, List.flatMap_map]

/-- The four source assertion units add four stored rows and no producer outputs. -/
theorem formula_source_rows (parameters : Parameters) :
    (formula parameters).clauses.size = sourceCompileRowCost parameters + 4 := by
  simp only [formula, Controller.CNF.OrderedFormula.Internal.clauses_append, Array.size_append]
  rw [equationFormula_source_rows, (compile_source_counts parameters).2.1]
  simp [CNF.ofClauses, assertions]

theorem formula_source_literals (parameters : Parameters) :
    (((formula parameters).clauses.toList).map List.length).sum = sourceCompileLiteralCost parameters + 4 := by
  simp only [formula, Controller.CNF.OrderedFormula.Internal.clauses_append, Array.toList_append,
    List.map_append, List.sum_append]
  rw [equationFormula_source_literals, (compile_source_counts parameters).2.2]
  simp [CNF.ofClauses, assertions]

/-- The declared finite source variable universe has one coordinate per positive allocated ID. -/
theorem sourceVariable_card (parameters : Parameters) :
    Nat.card (Variable parameters) = SourceInitialIDs.rootCount parameters + sourceCompileProducerCost parameters := by
  calc
    Nat.card (Variable parameters) = Nat.card (Fin (compile parameters).lastID) :=
      Nat.card_congr (variableIndex parameters)
    _ = SourceInitialIDs.rootCount parameters + sourceCompileProducerCost parameters := by
      simp [compile_lastID_source_count]

end Controller.Native.SourceController


namespace Controller.Native.SourceController

/-- Finite models count only positive allocated IDs, by restricting an actual source CNF model. -/
def SourceFiniteModelValues (parameters : Parameters)
    (values : Fin (compile parameters).lastID → Bool) : Prop :=
  ∃ assignment : ℕ → Bool,
    (∀ index, values index = assignment (SourceObservation.sourceID index)) ∧
      CNF.Satisfies assignment (formula parameters)

abbrev SourceFiniteModels (parameters : Parameters) :=
  {values : Fin (compile parameters).lastID → Bool // SourceFiniteModelValues parameters values}

/-- A physical-input fiber contains finite allocated source models with that exact recovered input. -/
def SourceFiniteModelValuesFor (parameters : Parameters)
    (input : Physical.PrimaryInput parameters.channels parameters.buses)
    (values : Fin (compile parameters).lastID → Bool) : Prop :=
  ∃ assignment : ℕ → Bool,
    (∀ index, values index = assignment (SourceObservation.sourceID index)) ∧
      sourceInput parameters assignment = input ∧ CNF.Satisfies assignment (formula parameters)

abbrev SourceFiniteModelsFor (parameters : Parameters)
    (input : Physical.PrimaryInput parameters.channels parameters.buses) :=
  {values : Fin (compile parameters).lastID → Bool // SourceFiniteModelValuesFor parameters input values}

abbrev SourceDetectingInputs (parameters : Parameters) :=
  {input : Physical.PrimaryInput parameters.channels parameters.buses //
    Physical.BridgeInputDetects parameters.bridge parameters.drive parameters.observations input
      (Physical.bridgeD parameters.bridge input)}

theorem sourceFiniteModelsFor_nonempty_iff (parameters : Parameters) (raw : parameters.layout = .raw)
    (input : Physical.PrimaryInput parameters.channels parameters.buses) :
    Nonempty (SourceFiniteModelsFor parameters input) ↔
      Physical.BridgeInputDetects parameters.bridge parameters.drive parameters.observations input
        (Physical.bridgeD parameters.bridge input) := by
  constructor
  · rintro ⟨values⟩
    rcases values.property with ⟨assignment, _, loaded, model⟩
    exact (source_models_for_physical_input_iff parameters raw input).mp ⟨assignment, loaded, model⟩
  · intro detects
    obtain ⟨assignment, loaded, model⟩ := (source_models_for_physical_input_iff parameters raw input).mpr detects
    exact ⟨⟨fun index => assignment (SourceObservation.sourceID index), assignment, (fun _ => rfl), loaded, model⟩⟩

theorem sourceFiniteModelsFor_subsingleton (parameters : Parameters) (raw : parameters.layout = .raw)
    (input : Physical.PrimaryInput parameters.channels parameters.buses) :
    Subsingleton (SourceFiniteModelsFor parameters input) := by
  refine ⟨?_⟩
  intro left right
  apply Subtype.ext
  funext index
  rcases left.property with ⟨leftAssignment, leftRestriction, leftLoaded, leftModel⟩
  rcases right.property with ⟨rightAssignment, rightRestriction, rightLoaded, rightModel⟩
  have positive : 0 < SourceObservation.sourceID index := by simp [SourceObservation.sourceID]
  have bounded : SourceObservation.sourceID index ≤ (compile parameters).lastID := by
    simpa only [SourceObservation.sourceID] using Nat.succ_le_of_lt index.isLt
  have equal := source_models_unique_on_allocated parameters raw input leftAssignment rightAssignment
    leftLoaded rightLoaded leftModel rightModel (SourceObservation.sourceID index) positive bounded
  exact (leftRestriction index).trans (equal.trans (rightRestriction index).symm)

/-- A detecting physical input has exactly one finite allocated source model. -/
theorem sourceFiniteModelsFor_card_one (parameters : Parameters) (raw : parameters.layout = .raw)
    (input : Physical.PrimaryInput parameters.channels parameters.buses)
    (detects : Physical.BridgeInputDetects parameters.bridge parameters.drive parameters.observations input
      (Physical.bridgeD parameters.bridge input)) :
    Nat.card (SourceFiniteModelsFor parameters input) = 1 :=
  Nat.card_eq_one_iff_unique.mpr ⟨sourceFiniteModelsFor_subsingleton parameters raw input,
    (sourceFiniteModelsFor_nonempty_iff parameters raw input).mpr detects⟩

/-- A non-detecting physical input has no finite allocated source model. -/
theorem sourceFiniteModelsFor_card_zero (parameters : Parameters) (raw : parameters.layout = .raw)
    (input : Physical.PrimaryInput parameters.channels parameters.buses)
    (fails : ¬ Physical.BridgeInputDetects parameters.bridge parameters.drive parameters.observations input
      (Physical.bridgeD parameters.bridge input)) :
    Nat.card (SourceFiniteModelsFor parameters input) = 0 := by
  apply Nat.card_eq_zero.mpr
  left
  refine ⟨fun value => ?_⟩
  exact fails ((sourceFiniteModelsFor_nonempty_iff parameters raw input).mp ⟨value⟩)

end Controller.Native.SourceController


namespace Controller.Native.SourceController

/-- Agreement on the finite declared coordinates determines every physical root read. -/
theorem sourceInput_eq_of_finite_restrictions (parameters : Parameters) (left right : ℕ → Bool)
    (agreement : ∀ index : Fin (compile parameters).lastID,
      left (SourceObservation.sourceID index) = right (SourceObservation.sourceID index)) :
    sourceInput parameters left = sourceInput parameters right := by
  have rootEquality : ∀ root : InterfaceAlias.Root parameters.channels parameters.buses,
      left (SourceInitialIDs.rootID root) = right (SourceInitialIDs.rootID root) := by
    intro root
    let rootIndex := SourceInitialIDs.rootIndex root
    have rootBound : rootIndex.val < SourceInitialIDs.rootCount parameters := rootIndex.isLt
    let index : Fin (compile parameters).lastID := ⟨rootIndex.val, by
      change rootIndex.val < SourceInitialIDs.rootCount parameters + (compile parameters).entries.length
      omega⟩
    simpa only [SourceObservation.sourceID, SourceInitialIDs.rootID, rootIndex, index] using agreement index
  apply sourceInput_eq_physical_of_roots parameters left (sourceInput parameters right)
  · intro channel
    exact rootEquality (.enable channel)
  · intro bus channel
    exact rootEquality (.request bus channel)

noncomputable def sourceFiniteModelWitness (parameters : Parameters) (values : SourceFiniteModels parameters) : ℕ → Bool :=
  Classical.choose values.property

theorem sourceFiniteModelWitness_restriction (parameters : Parameters) (values : SourceFiniteModels parameters)
    (index : Fin (compile parameters).lastID) :
    values.val index = sourceFiniteModelWitness parameters values (SourceObservation.sourceID index) :=
  (Classical.choose_spec values.property).1 index

theorem sourceFiniteModelWitness_model (parameters : Parameters) (values : SourceFiniteModels parameters) :
    CNF.Satisfies (sourceFiniteModelWitness parameters values) (formula parameters) :=
  (Classical.choose_spec values.property).2

noncomputable def sourceDetectingInputWitness (parameters : Parameters) (raw : parameters.layout = .raw)
    (input : SourceDetectingInputs parameters) : ℕ → Bool :=
  Classical.choose ((source_models_for_physical_input_iff parameters raw input.val).mpr input.property)

theorem sourceDetectingInputWitness_loaded (parameters : Parameters) (raw : parameters.layout = .raw)
    (input : SourceDetectingInputs parameters) :
    sourceInput parameters (sourceDetectingInputWitness parameters raw input) = input.val :=
  (Classical.choose_spec ((source_models_for_physical_input_iff parameters raw input.val).mpr input.property)).1

theorem sourceDetectingInputWitness_model (parameters : Parameters) (raw : parameters.layout = .raw)
    (input : SourceDetectingInputs parameters) :
    CNF.Satisfies (sourceDetectingInputWitness parameters raw input) (formula parameters) :=
  (Classical.choose_spec ((source_models_for_physical_input_iff parameters raw input.val).mpr input.property)).2

noncomputable def sourceFiniteModelToDetecting (parameters : Parameters) (raw : parameters.layout = .raw)
    (values : SourceFiniteModels parameters) : SourceDetectingInputs parameters :=
  ⟨sourceInput parameters (sourceFiniteModelWitness parameters values),
    source_model_implies_physical_detection parameters (sourceFiniteModelWitness parameters values) raw
      (sourceFiniteModelWitness_model parameters values)⟩

noncomputable def sourceFiniteModelOfDetecting (parameters : Parameters) (raw : parameters.layout = .raw)
    (input : SourceDetectingInputs parameters) : SourceFiniteModels parameters :=
  ⟨fun index => sourceDetectingInputWitness parameters raw input (SourceObservation.sourceID index),
    sourceDetectingInputWitness parameters raw input, (fun _ => rfl),
    sourceDetectingInputWitness_model parameters raw input⟩

/-- Finite allocated source models correspond bijectively to detecting physical inputs, with no extra wire root. -/
noncomputable def sourceFiniteModelsEquivDetectingInputs (parameters : Parameters) (raw : parameters.layout = .raw) :
    SourceFiniteModels parameters ≃ SourceDetectingInputs parameters where
  toFun := sourceFiniteModelToDetecting parameters raw
  invFun := sourceFiniteModelOfDetecting parameters raw
  left_inv := by
    intro values
    apply Subtype.ext
    funext index
    let input := sourceFiniteModelToDetecting parameters raw values
    let original := sourceFiniteModelWitness parameters values
    let replacement := sourceDetectingInputWitness parameters raw input
    change replacement (SourceObservation.sourceID index) = values.val index
    have originalLoaded : sourceInput parameters original = input.val := rfl
    have replacementLoaded : sourceInput parameters replacement = input.val :=
      sourceDetectingInputWitness_loaded parameters raw input
    have positive : 0 < SourceObservation.sourceID index := by simp [SourceObservation.sourceID]
    have bounded : SourceObservation.sourceID index ≤ (compile parameters).lastID := by
      simpa only [SourceObservation.sourceID] using Nat.succ_le_of_lt index.isLt
    have equal := source_models_unique_on_allocated parameters raw input.val replacement original
      replacementLoaded originalLoaded (sourceDetectingInputWitness_model parameters raw input)
      (sourceFiniteModelWitness_model parameters values) (SourceObservation.sourceID index) positive bounded
    exact equal.trans (sourceFiniteModelWitness_restriction parameters values index).symm
  right_inv := by
    intro input
    apply Subtype.ext
    change sourceInput parameters (sourceFiniteModelWitness parameters (sourceFiniteModelOfDetecting parameters raw input)) = input.val
    have agreement : ∀ index : Fin (compile parameters).lastID,
        sourceFiniteModelWitness parameters (sourceFiniteModelOfDetecting parameters raw input) (SourceObservation.sourceID index) =
          sourceDetectingInputWitness parameters raw input (SourceObservation.sourceID index) := by
      intro index
      exact (sourceFiniteModelWitness_restriction parameters (sourceFiniteModelOfDetecting parameters raw input) index).symm
    exact (sourceInput_eq_of_finite_restrictions parameters _ _ agreement).trans
      (sourceDetectingInputWitness_loaded parameters raw input)

/-- Total finite source model count equals the number of detecting physical inputs. -/
theorem sourceFiniteModels_card_detectingInputs (parameters : Parameters) (raw : parameters.layout = .raw) :
    Nat.card (SourceFiniteModels parameters) = Nat.card (SourceDetectingInputs parameters) :=
  Nat.card_congr (sourceFiniteModelsEquivDetectingInputs parameters raw)

end Controller.Native.SourceController


namespace Controller.Native.SourceController

/-- Complete independent-W models, after the D and W interface units are imposed. -/
def IndependentWireModels (parameters : Parameters) :=
  { assignment : Controller.Native.Variable parameters → Bool //
    CNF.Satisfies assignment parameters.specificationFormula }

noncomputable def independentWireModelToDetecting (parameters : Parameters)
    (model : IndependentWireModels parameters) : SourceDetectingInputs parameters := by
  let input := parameters.primaryInput (fun role => model.val (.primary role))
  have detects := parameters.specification_model_projects model.val model.property
  have wire : model.val (.primary .wire) = Physical.bridgeD parameters.bridge input :=
    detects.1.2.2.trans detects.1.2.1.symm
  exact ⟨input, by simpa only [wire] using detects⟩

noncomputable def independentWireModelOfDetecting (parameters : Parameters)
    (input : SourceDetectingInputs parameters) : IndependentWireModels parameters :=
  ⟨parameters.physicalAssignment input.val (Physical.bridgeD parameters.bridge input.val),
    (CNF.satisfies_append _ _ _).mpr
      ⟨parameters.physicalAssignment_satisfies_equations _ _,
        (parameters.physicalAssignment_assertions_iff _ _).mpr input.property⟩⟩

/-- The independent wire contributes no additional model multiplicity after activation. -/
noncomputable def independentWireModelsEquivDetectingInputs (parameters : Parameters) :
    IndependentWireModels parameters ≃ SourceDetectingInputs parameters where
  toFun := independentWireModelToDetecting parameters
  invFun := independentWireModelOfDetecting parameters
  left_inv := by
    intro model
    apply Subtype.ext
    let input := parameters.primaryInput (fun role => model.val (.primary role))
    have detects := parameters.specification_model_projects model.val model.property
    have wire : model.val (.primary .wire) = Physical.bridgeD parameters.bridge input :=
      detects.1.2.2.trans detects.1.2.1.symm
    have equations := (CNF.satisfies_append _ _ _).mp model.property |>.1
    apply parameters.equation_model_unique _ _
      (parameters.physicalAssignment_satisfies_equations _ _) equations
    intro role
    cases role with
    | enable channel => rfl
    | request bus channel => rfl
    | wire => exact wire.symm
  right_inv := by
    intro input
    apply Subtype.ext
    change parameters.primaryInput (fun role =>
      parameters.physicalAssignment input.val (Physical.bridgeD parameters.bridge input.val) (.primary role)) = input.val
    cases input.val
    rfl

/-- Full-model transport compares layouts with different free and defined coordinates. -/
noncomputable def independentWireModelsEquivSourceFiniteModels (parameters : Parameters)
    (raw : parameters.layout = .raw) :
    IndependentWireModels parameters ≃ SourceFiniteModels parameters :=
  (independentWireModelsEquivDetectingInputs parameters).trans
    (sourceFiniteModelsEquivDetectingInputs parameters raw).symm

theorem independentWireModels_card_sourceFiniteModels (parameters : Parameters)
    (raw : parameters.layout = .raw) :
    Nat.card (IndependentWireModels parameters) = Nat.card (SourceFiniteModels parameters) :=
  Nat.card_congr (independentWireModelsEquivSourceFiniteModels parameters raw)

/-- The source generator record retains every producer and the ordered final units. -/
structure OrderedSourceRecord where
  variableCount : ℕ
  producers : List (Bounded.Producer ℕ)
  units : List (CNF.Literal ℕ)

def orderedSourceRecord (parameters : Parameters) : OrderedSourceRecord :=
  ⟨(compile parameters).lastID, (compile parameters).entries.map Entry.producer,
    assertions parameters⟩

def OrderedSourceRecord.rows (record : OrderedSourceRecord) : List (CNF.Clause ℕ) :=
  record.producers.flatMap Bounded.Producer.rows ++ record.units.map (fun literal => [literal])

/-- Exact row order, with retained old observations and repeated literals intact. -/
theorem orderedSourceRecord_rows (parameters : Parameters) :
    (orderedSourceRecord parameters).rows = (formula parameters).clauses.toList := by
  simp [orderedSourceRecord, OrderedSourceRecord.rows, formula, equationFormula,
    CNF.ofClauses, Controller.CNF.OrderedFormula.Internal.clauses_append, List.flatMap_map]

theorem orderedSourceRecord_variableCount (parameters : Parameters) :
    (orderedSourceRecord parameters).variableCount =
      SourceInitialIDs.rootCount parameters + sourceCompileProducerCost parameters :=
  compile_lastID_source_count parameters

/-- The independent-W count includes its separate wire root; the source count does not. -/
theorem distinct_layout_variable_counts (parameters : Parameters) :
    parameters.variableRoles.length = parameters.channels + parameters.buses * parameters.channels + 1 +
      parameters.roles.length ∧
    (orderedSourceRecord parameters).variableCount = SourceInitialIDs.rootCount parameters +
      sourceCompileProducerCost parameters :=
  ⟨parameters.variableRoles_length, orderedSourceRecord_variableCount parameters⟩

/-- External signed source coordinates are indexed by the image of each allocated ID.
No coordinate for source ID zero or unused Nat IDs is counted. -/
def SignedSourceFiniteModelValues (parameters : Parameters) (rename : ℕ ≃ ℕ)
    (phase : ℕ → Bool) (values : Fin (compile parameters).lastID → Bool) : Prop :=
  ∃ assignment : ℕ → Bool,
    (∀ index, values index = assignment (rename (SourceObservation.sourceID index))) ∧
    CNF.Satisfies assignment (CNF.signedRelabel rename phase (formula parameters))

def SignedSourceFiniteModels (parameters : Parameters) (rename : ℕ ≃ ℕ) (phase : ℕ → Bool) :=
  { values : Fin (compile parameters).lastID → Bool //
    SignedSourceFiniteModelValues parameters rename phase values }

theorem signedSourceFiniteModelValues_iff (parameters : Parameters) (rename : ℕ ≃ ℕ)
    (phase : ℕ → Bool) (values : Fin (compile parameters).lastID → Bool) :
    SignedSourceFiniteModelValues parameters rename phase values ↔
      SourceFiniteModelValues parameters (fun index => values index == phase (SourceObservation.sourceID index)) := by
  constructor
  · rintro ⟨assignment, restriction, model⟩
    refine ⟨CNF.signedPullback rename phase assignment, ?_,
      (CNF.satisfies_signedRelabel rename phase assignment _).mp model⟩
    intro index
    simp only [CNF.signedPullback, restriction index]
  · rintro ⟨assignment, restriction, model⟩
    let external := fun id => assignment (rename.symm id) == phase (rename.symm id)
    refine ⟨external, ?_, ?_⟩
    · intro index
      simp only [external, Equiv.symm_apply_apply]
      change values index = (assignment (SourceObservation.sourceID index) == phase (SourceObservation.sourceID index))
      have equal := restriction index
      cases hval : values index <;> cases hphase : phase (SourceObservation.sourceID index) <;>
        simp_all
    · rw [CNF.satisfies_signedRelabel, CNF.signedPullback_inverse]
      exact model

/-- Signed variable permutations preserve the complete finite source-model count. -/
noncomputable def signedSourceFiniteModelsEquiv (parameters : Parameters) (rename : ℕ ≃ ℕ)
    (phase : ℕ → Bool) : SignedSourceFiniteModels parameters rename phase ≃ SourceFiniteModels parameters where
  toFun values := ⟨fun index => values.val index == phase (SourceObservation.sourceID index),
    (signedSourceFiniteModelValues_iff parameters rename phase values.val).mp values.property⟩
  invFun values := ⟨fun index => values.val index == phase (SourceObservation.sourceID index), by
    apply (signedSourceFiniteModelValues_iff parameters rename phase _).mpr
    have equal : (fun index => (values.val index == phase (SourceObservation.sourceID index)) ==
      phase (SourceObservation.sourceID index)) = values.val := by
      funext index
      cases values.val index <;> cases phase (SourceObservation.sourceID index) <;> rfl
    rw [equal]
    exact values.property⟩
  left_inv := by
    intro values
    apply Subtype.ext
    funext index
    change ((values.val index == phase (SourceObservation.sourceID index)) == phase (SourceObservation.sourceID index)) = values.val index
    cases values.val index <;> cases phase (SourceObservation.sourceID index) <;> rfl
  right_inv := by
    intro values
    apply Subtype.ext
    funext index
    change ((values.val index == phase (SourceObservation.sourceID index)) == phase (SourceObservation.sourceID index)) = values.val index
    cases values.val index <;> cases phase (SourceObservation.sourceID index) <;> rfl

theorem signedSourceFiniteModels_card (parameters : Parameters) (rename : ℕ ≃ ℕ)
    (phase : ℕ → Bool) :
    Nat.card (SignedSourceFiniteModels parameters rename phase) = Nat.card (SourceFiniteModels parameters) :=
  Nat.card_congr (signedSourceFiniteModelsEquiv parameters rename phase)

/-- The asserted independent-W model set transports to a signed external source layout. -/
noncomputable def independentWireModelsEquivSignedSourceFiniteModels (parameters : Parameters)
    (raw : parameters.layout = .raw) (rename : ℕ ≃ ℕ) (phase : ℕ → Bool) :
    IndependentWireModels parameters ≃ SignedSourceFiniteModels parameters rename phase :=
  (independentWireModelsEquivSourceFiniteModels parameters raw).trans
    (signedSourceFiniteModelsEquiv parameters rename phase).symm

end Controller.Native.SourceController

namespace Controller.CNF

/-- Literal and row permutation preserves occurrences without normalizing duplicates. -/
def PermutedClauseRows (before after : List (Clause α)) : Prop :=
  ∃ middle : List (Clause α), List.Forall₂ List.Perm before middle ∧ middle.Perm after

theorem clauseHolds_of_perm (assignment : α → Bool) {before after : Clause α}
    (permutation : before.Perm after) : ClauseHolds assignment before ↔ ClauseHolds assignment after :=
  clauseHolds_congr (fun literal => permutation.mem_iff)

theorem satisfies_permutedClauseRows (assignment : α → Bool)
    {before after : List (Clause α)} (permutation : PermutedClauseRows before after) :
    Satisfies assignment (ofClauses before) ↔ Satisfies assignment (ofClauses after) := by
  rcases permutation with ⟨middle, pairwise, rows⟩
  have matched : (∀ clause ∈ before, ClauseHolds assignment clause) ↔
      (∀ clause ∈ middle, ClauseHolds assignment clause) := by
    clear rows
    induction pairwise with
    | nil => simp
    | @cons left right tail₁ tail₂ head rest ih =>
      simpa only [List.forall_mem_cons] using
        and_congr (clauseHolds_of_perm assignment head) ih
  have reordered : (∀ clause ∈ middle, ClauseHolds assignment clause) ↔
      (∀ clause ∈ after, ClauseHolds assignment clause) := by
    constructor
    · intro h clause membership
      exact h clause (rows.mem_iff.mpr membership)
    · intro h clause membership
      exact h clause (rows.mem_iff.mp membership)
  simpa only [Satisfies, ofClauses, List.mem_toArray] using matched.trans reordered

theorem permutedClauseRows_counts {before after : List (Clause α)}
    (permutation : PermutedClauseRows before after) :
    before.length = after.length ∧ (before.map List.length).sum = (after.map List.length).sum := by
  rcases permutation with ⟨middle, pairwise, rows⟩
  have literalCounts : (before.map List.length).sum = (middle.map List.length).sum := by
    clear rows
    induction pairwise with
    | nil => rfl
    | cons head rest ih => simpa only [List.map_cons, List.sum_cons, head.length_eq, ih]
  exact ⟨pairwise.length_eq.trans rows.length_eq,
    literalCounts.trans (rows.map List.length).sum_eq⟩

end Controller.CNF


namespace Controller.Native.SourceController

/-- Independent-W bounded models include each producer's private binary-fold coordinates. -/
def BoundedIndependentWireModels (parameters : Parameters) :=
  { assignment : Bounded.GlobalVariable parameters → Bool //
    CNF.Satisfies assignment (Bounded.globalFormula parameters) }

/-- Bounded private outputs neither remove nor multiply asserted independent-W models. -/
noncomputable def boundedIndependentWireModelsEquiv (parameters : Parameters) :
    BoundedIndependentWireModels parameters ≃ IndependentWireModels parameters where
  toFun model := ⟨fun slot => model.val (.original slot),
    Bounded.global_model_projects parameters model.val model.property⟩
  invFun model := ⟨Bounded.globalAssignment parameters model.val,
    Bounded.globalAssignment_satisfies parameters model.val model.property⟩
  left_inv := by
    intro model
    apply Subtype.ext
    exact (Bounded.global_model_eq_assignment parameters model.val model.property).symm
  right_inv := by
    intro model
    apply Subtype.ext
    rfl

/-- Full independent-W bounded models transport to the actual source's allocated IDs. -/
noncomputable def boundedIndependentWireModelsEquivSignedSource (parameters : Parameters)
    (raw : parameters.layout = .raw) (rename : ℕ ≃ ℕ) (phase : ℕ → Bool) :
    BoundedIndependentWireModels parameters ≃ SignedSourceFiniteModels parameters rename phase :=
  (boundedIndependentWireModelsEquiv parameters).trans
    (independentWireModelsEquivSignedSourceFiniteModels parameters raw rename phase)

theorem boundedIndependentWireModels_card_signedSource (parameters : Parameters)
    (raw : parameters.layout = .raw) (rename : ℕ ≃ ℕ) (phase : ℕ → Bool) :
    Nat.card (BoundedIndependentWireModels parameters) =
      Nat.card (SignedSourceFiniteModels parameters rename phase) :=
  Nat.card_congr (boundedIndependentWireModelsEquivSignedSource parameters raw rename phase)

/-- Exact layout counts are retained separately from the full-model equivalence. -/
theorem bounded_and_source_exact_counts (parameters : Parameters) :
    (Bounded.globalVariables parameters).length = parameters.variableRoles.length +
      (parameters.roles.map fun owner => Bounded.auxiliaryCount (parameters.gate owner)).sum ∧
    (Bounded.globalFormula parameters).clauses.size =
      (parameters.roles.map fun owner => Bounded.expansionRowCount (parameters.gate owner)).sum + 4 ∧
    Bounded.literalIncidences (Bounded.globalFormula parameters) =
      (parameters.roles.map fun owner => Bounded.expansionLiteralCount (parameters.gate owner)).sum + 4 ∧
    (compile parameters).lastID = SourceInitialIDs.rootCount parameters + sourceCompileProducerCost parameters ∧
    (formula parameters).clauses.size = sourceCompileRowCost parameters + 4 ∧
    ((formula parameters).clauses.toList.map List.length).sum = sourceCompileLiteralCost parameters + 4 := by
  exact ⟨Bounded.globalVariables_length parameters, Bounded.globalFormula_rows parameters,
    Bounded.globalFormula_literals parameters, compile_lastID_source_count parameters,
    formula_source_rows parameters, formula_source_literals parameters⟩

end Controller.Native.SourceController
