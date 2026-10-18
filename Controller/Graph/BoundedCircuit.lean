module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Graph.NetWidth
public import Controller.Native.BoundedEncode

@[expose] public section

/-! The complete native binary circuit, with one gate for each emitted
producer. Signals retain the declared original and private auxiliary slots;
connections retain their actual signed input occurrences. -/
namespace Controller.Graph.BoundedCircuit
open Controller.Native Controller.Native.Parameters Controller.Native.Bounded

theorem expansion_length {α : Type*} (g : CNF.Gate α) (output : CNF.Literal α) :
    (expand output g).length = auxiliaryCount g + 1 := by
  rw [expand_length]
  cases g <;> simp only [expansionProducerCount, auxiliaryCount, foldProducerCount] <;> omega

theorem fold_output {α : Type*} (junction : Junction) (inputs : List (CNF.Literal α))
    (output : CNF.Literal α) (i : Fin (foldProducers junction inputs output).length) :
    ((foldProducers junction inputs output)[i.val]).output =
      if h : i.val < inputs.length - 2 then (LocalVariable.auxiliary ⟨i.val, h⟩, true)
      else originalLiteral output := by
  by_cases empty : inputs.length = 0
  · have zero : i.val = 0 := by
      have bound := i.isLt
      simp only [foldProducers, dite_eq_left empty, List.length_singleton] at bound
      omega
    simp [foldProducers, empty, zero]
  · by_cases unary : inputs.length = 1
    · have zero : i.val = 0 := by
        have bound := i.isLt
        simp only [foldProducers, dite_eq_right empty, dite_eq_left unary, List.length_singleton] at bound
        omega
      simp [foldProducers, unary, zero]
    · simp only [foldProducers, dite_eq_right empty, dite_eq_right unary, List.getElem_map,
        List.getElem_finRange, foldOutput, Fin.val_cast]

theorem expansion_output {α : Type*} (g : CNF.Gate α) (output : CNF.Literal α)
    (i : Fin (expand output g).length) :
    ((expand output g)[i.val]).output =
      if h : i.val < auxiliaryCount g then (LocalVariable.auxiliary ⟨i.val, h⟩, true)
      else originalLiteral output := by
  cases g with
  | and inputs => exact fold_output .conjunction inputs output i
  | or inputs => exact fold_output .disjunction inputs output i
  | xor left right | «alias» left | not left | constant left =>
    have zero : i.val = 0 := by
      have bound := i.isLt
      simp only [expand, List.length_singleton] at bound
      omega
    simp [expand, auxiliaryCount, zero]

/-- Local positions are exactly the private prefix slots followed by the
principal output. Empty and unary producers still contribute one gate. -/
abbrev Gate (p : Parameters) := Σ owner : Internal p, Fin (auxiliaryCount (p.gate owner) + 1)

instance (p : Parameters) : Fintype (Gate p) := by
  letI : Fintype (Internal p) := Fintype.ofList p.roles p.mem_roles
  exact inferInstanceAs (Fintype (Σ owner : Internal p, Fin (auxiliaryCount (p.gate owner) + 1)))

def gateList (p : Parameters) (owner : Internal p) : List (Producer (GlobalVariable p)) :=
  (expand (p.internal owner) (p.gate owner)).map (Producer.relabel (localSlots p owner))

theorem gateList_length (p : Parameters) (owner : Internal p) :
    (gateList p owner).length = auxiliaryCount (p.gate owner) + 1 := by
  simp only [gateList, List.length_map, expansion_length]

def producer (p : Parameters) (g : Gate p) : Producer (GlobalVariable p) :=
  (gateList p g.1)[g.2.val]'(by rw [gateList_length]; exact g.2.isLt)

def output (p : Parameters) (g : Gate p) : GlobalVariable p :=
  if h : g.2.val < auxiliaryCount (p.gate g.1) then .auxiliary g.1 ⟨g.2.val, h⟩
  else .original (.internal g.1)

set_option backward.isDefEq.respectTransparency false in
theorem producer_output (p : Parameters) (g : Gate p) :
    (producer p g).output = (output p g, true) := by
  have indexBound : g.2.val < (expand (p.internal g.1) (p.gate g.1)).length := by
    rw [expansion_length]
    exact g.2.isLt
  unfold producer gateList
  simp only [List.getElem_map, Producer.relabel]
  have eq := expansion_output (p.gate g.1) (p.internal g.1)
    ⟨g.2.val, by rw [expansion_length]; exact g.2.isLt⟩
  change (localSlots p g.1 ((expand (p.internal g.1) (p.gate g.1))[g.2.val]).output.1,
    ((expand (p.internal g.1) (p.gate g.1))[g.2.val]).output.2) = _
  rw [eq]
  unfold output
  split <;> simp [localSlots, originalLiteral, internal, positive]

def principal (p : Parameters) (owner : Internal p) : Gate p :=
  ⟨owner, Fin.last (auxiliaryCount (p.gate owner))⟩

def privateGate (p : Parameters) (owner : Internal p)
    (index : Fin (auxiliaryCount (p.gate owner))) : Gate p := ⟨owner, index.castSucc⟩

@[simp] theorem output_principal (p : Parameters) (owner : Internal p) :
    output p (principal p owner) = .original (.internal owner) := by
  simp [output, principal]

@[simp] theorem output_private (p : Parameters) (owner : Internal p)
    (index : Fin (auxiliaryCount (p.gate owner))) :
    output p (privateGate p owner index) = .auxiliary owner index := by
  simp [output, privateGate, index.isLt]

def producerSlot (p : Parameters) : GlobalVariable p → PrimaryRole p.channels p.buses ⊕ Gate p
  | .original (.primary input) => .inl input
  | .original (.internal owner) => .inr (principal p owner)
  | .auxiliary owner index => .inr (privateGate p owner index)

def signal (p : Parameters) : PrimaryRole p.channels p.buses ⊕ Gate p → GlobalVariable p
  | .inl input => .original (.primary input)
  | .inr g => output p g

@[simp] theorem signal_producerSlot (p : Parameters) (s : GlobalVariable p) :
    signal p (producerSlot p s) = s := by
  cases s with
  | original slot => cases slot <;> simp [producerSlot, signal]
  | auxiliary owner index => simp [producerSlot, signal]

@[simp] theorem producerSlot_signal (p : Parameters) (s : PrimaryRole p.channels p.buses ⊕ Gate p) :
    producerSlot p (signal p s) = s := by
  cases s with
  | inl input => rfl
  | inr g =>
    obtain ⟨owner, index⟩ := g
    simp only [signal, output]
    split
    next privateOutput =>
      simp only [producerSlot, privateGate]
      exact congrArg (fun i : Fin (auxiliaryCount (p.gate owner) + 1) =>
        (Sum.inr ⟨owner, i⟩ : PrimaryRole p.channels p.buses ⊕ Gate p)) (Fin.ext rfl)
    next principalOutput =>
      have last : index.val = auxiliaryCount (p.gate owner) := by have bound := index.isLt; omega
      simp only [producerSlot, principal]
      exact congrArg (fun i : Fin (auxiliaryCount (p.gate owner) + 1) =>
        (Sum.inr ⟨owner, i⟩ : PrimaryRole p.channels p.buses ⊕ Gate p)) (Fin.ext last.symm)

/-- Primary ports and actual emitted gate outputs exhaust the declared signal
universe bijectively; no dummy gate is assigned to a primary port. -/
def signalEquiv (p : Parameters) :
    (PrimaryRole p.channels p.buses ⊕ Gate p) ≃ GlobalVariable p where
  toFun := signal p
  invFun := producerSlot p
  left_inv := producerSlot_signal p
  right_inv := signal_producerSlot p

theorem output_injective (p : Parameters) : Function.Injective (output p) := by
  intro g h eq
  exact Sum.inr.inj ((signalEquiv p).injective eq)

def allProducers (p : Parameters) : List (Producer (GlobalVariable p)) :=
  p.roles.flatMap (gateList p)

theorem producer_mem (p : Parameters) (g : Gate p) : producer p g ∈ allProducers p := by
  exact List.mem_flatMap.mpr ⟨g.1, p.mem_roles g.1, List.getElem_mem ..⟩

theorem mem_allProducers (p : Parameters) (r : Producer (GlobalVariable p)) :
    r ∈ allProducers p ↔ ∃ g, producer p g = r := by
  constructor
  · intro member
    obtain ⟨owner, _, member⟩ := List.mem_flatMap.mp member
    obtain ⟨i, hi, eq⟩ := List.getElem_of_mem member
    refine ⟨⟨owner, ⟨i, ?_⟩⟩, eq⟩
    simpa only [gateList_length] using hi
  · rintro ⟨g, rfl⟩
    exact producer_mem p g

/-- An emitted producer is determined by its allocated output signal. -/
theorem producer_eq_of_mem (p : Parameters) (g : Gate p)
    (r : Producer (GlobalVariable p)) (member : r ∈ allProducers p)
    (same : r.output.1 = output p g) : producer p g = r := by
  obtain ⟨h, rfl⟩ := (mem_allProducers p r).mp member
  have eq : h = g := output_injective p (by simpa only [producer_output] using same)
  subst h
  rfl

/-- The emitted order retains the owner and local expansion position. -/
def gateAddresses (p : Parameters) : List (Gate p) :=
  p.roles.flatMap fun owner =>
    (List.finRange (auxiliaryCount (p.gate owner) + 1)).map (Sigma.mk owner)

theorem gateAddresses_nodup (p : Parameters) : (gateAddresses p).Nodup := by
  rw [gateAddresses, List.nodup_flatMap]
  constructor
  · intro owner _
    exact List.Nodup.map (by intro a b h; cases h; rfl) (List.nodup_finRange _)
  · apply p.roles_nodup.imp
    intro a b different value ha hb
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
    obtain ⟨j, _, eq⟩ := List.mem_map.mp hb
    exact different (congrArg Sigma.fst eq.symm)

theorem allProducers_addressed (p : Parameters) :
    allProducers p = (gateAddresses p).map (producer p) := by
  unfold allProducers gateAddresses
  rw [List.map_flatMap]
  apply congrArg (List.flatMap · p.roles)
  funext owner
  rw [List.map_map]
  apply List.ext_getElem
  · simp [gateList_length]
  · intro i hi hj
    simp [producer, Function.comp_def]

/-- Each actual producer output occurs once in the emitted list. -/
theorem producer_outputs_nodup (p : Parameters) :
    ((allProducers p).map (fun r => r.output.1)).Nodup := by
  rw [allProducers_addressed, List.map_map]
  have eq : (fun g => (producer p g).output.1) = output p := by
    funext g
    simp only [producer_output]
  change ((gateAddresses p).map (fun g => (producer p g).output.1)).Nodup
  rw [eq]
  exact (gateAddresses_nodup p).map (output_injective p)

noncomputable def layout (p : Parameters) :
    CircuitLayout (PrimaryRole p.channels p.buses) (Gate p) Unit (GlobalVariable p) where
  producer := producerSlot p
  consumers s :=
    (Finset.univ.filter (fun g => s ∈ (producer p g).gate.inputs.map Prod.fst)).image Sum.inl ∪
      if s = .original (.internal .detected) then {Sum.inr ()} else ∅

@[simp] theorem layout_connection (p : Parameters) (s : GlobalVariable p) (g : Gate p) :
    Sum.inl g ∈ (layout p).consumers s ↔ s ∈ (producer p g).gate.inputs.map Prod.fst := by
  classical
  by_cases detected : s = .original (.internal .detected) <;> simp [layout, detected]

theorem layout_signed_connection (p : Parameters) (s : GlobalVariable p) (g : Gate p) :
    Sum.inl g ∈ (layout p).consumers s ↔
      ∃ phase, (s, phase) ∈ (producer p g).gate.inputs := by
  rw [layout_connection]
  simp only [List.mem_map]
  constructor
  · rintro ⟨⟨v, phase⟩, member, rfl⟩
    exact ⟨phase, member⟩
  · rintro ⟨phase, member⟩
    exact ⟨(s, phase), member, rfl⟩

@[simp] theorem layout_output_connection (p : Parameters) (s : GlobalVariable p) :
    Sum.inr () ∈ (layout p).consumers s ↔ s = .original (.internal .detected) := by
  classical
  by_cases detected : s = .original (.internal .detected) <;> simp [layout, detected]

theorem layout_producer (p : Parameters) (g : Gate p) :
    (layout p).producer (producer p g).output.1 = .inr g := by
  rw [producer_output]
  exact producerSlot_signal p (.inr g)

@[simp] theorem layout_primary_producer (p : Parameters)
    (input : PrimaryRole p.channels p.buses) :
    (layout p).producer (.original (.primary input)) = .inl input := rfl

/-- A gate-arity-independent target type permits rewriting the source gate
without transporting a dependent auxiliary-slot type. -/
def addressedProducers {α β : Type*} (original : α → β) (aux : ℕ → β)
    (out : CNF.Literal α) (g : CNF.Gate α) : List (Producer β) :=
  (expand out g).map (Producer.relabel fun x =>
    match x with | .original v => original v | .auxiliary i => aux i.val)

def auxiliaryAt (p : Parameters) (owner : Internal p) (i : ℕ) : GlobalVariable p :=
  if h : i < auxiliaryCount (p.gate owner) then .auxiliary owner ⟨i, h⟩
  else .original (.internal owner)

set_option backward.isDefEq.respectTransparency false in
theorem gateList_addressed (p : Parameters) (owner : Internal p) :
    gateList p owner = addressedProducers GlobalVariable.original (auxiliaryAt p owner)
      (p.internal owner) (p.gate owner) := by
  unfold gateList addressedProducers
  apply congrArg (fun rename => (expand (p.internal owner) (p.gate owner)).map
    (Producer.relabel rename))
  funext x
  cases x with
  | original v => rfl
  | auxiliary i => simp [localSlots, auxiliaryAt, i.isLt]

theorem relabel_inputs_length {α β : Type*} (f : α → β) (g : CNF.Gate α) :
    (g.relabel f).inputs.length = g.inputs.length := by
  cases g <;> simp [CNF.Gate.relabel, CNF.Gate.inputs]

theorem producer_binary (p : Parameters) (g : Gate p) :
    (producer p g).gate.inputs.length ≤ 2 := by
  have member : producer p g ∈ gateList p g.1 := List.getElem_mem ..
  obtain ⟨r, member, eq⟩ := List.mem_map.mp member
  rw [← eq]
  change (r.gate.relabel (localSlots p g.1)).inputs.length ≤ 2
  rw [relabel_inputs_length]
  exact expand_bounded _ _ r member

theorem rows_relabel {α β : Type*} (f : α → β) (r : Producer α) :
    (r.relabel f).rows = r.rows.map (Controller.CNF.OrderedFormula.Clause.relabel f) := by
  obtain ⟨out, g⟩ := r
  cases g <;>
    simp [Producer.relabel, Producer.rows, CNF.Gate.relabel, CNF.Gate.clauses,
      Controller.CNF.OrderedFormula.Clause.relabel, List.map_map, Function.comp_def,
      CNF.negate, Std.Sat.Literal.negate];
    split <;> rfl

theorem gateList_rows (p : Parameters) (owner : Internal p) :
    (gateList p owner).flatMap Producer.rows = (producerFormula p owner).clauses.toList := by
  simp [gateList, producerFormula, CNF.relabel, Controller.CNF.OrderedFormula.relabel, CNF.ofClauses, rows,
    List.flatMap_map, List.map_flatMap, rows_relabel]

/-- Equality is of ordered row lists, including repeated occurrences. -/
theorem equation_rows (p : Parameters) :
    (allProducers p).flatMap Producer.rows = (globalEquationFormula p).clauses.toList := by
  have fold (owners : List (Internal p)) :
      (owners.flatMap (gateList p)).flatMap Producer.rows =
        (owners.foldr (fun owner suffix => producerFormula p owner ++ suffix)
          Controller.CNF.OrderedFormula.empty).clauses.toList := by
    induction owners with
    | nil => rfl
    | cons owner tail ih =>
      simp only [List.flatMap_cons, List.foldr_cons, List.flatMap_append,
        Controller.CNF.OrderedFormula.Internal.clauses_append, Array.toList_append, gateList_rows, ih]
  exact fold p.roles

/-- Defining gate rows followed by the four original assertion occurrences
reconstruct the actual complete bounded native formula. -/
theorem complete_rows (p : Parameters) :
    (allProducers p).flatMap Producer.rows ++
      p.assertions.map (fun literal => [(GlobalVariable.original literal.1, literal.2)]) =
        (globalFormula p).clauses.toList := by
  simp only [globalFormula, Controller.CNF.OrderedFormula.Internal.clauses_append, Array.toList_append,
    equation_rows, CNF.relabel, Controller.CNF.OrderedFormula.relabel, assertionFormula,
    CNF.ofClauses, Array.toList_map]
  congr 1

/-- Primary ports, gate vertices, and the distinguished output port. -/
abbrev Vertex (p : Parameters) := PrimaryRole p.channels p.buses ⊕ Gate p ⊕ Unit

instance (p : Parameters) : Fintype (Vertex p) := by
  letI : Fintype (PrimaryRole p.channels p.buses) :=
    Fintype.ofList p.primaryRoles p.mem_primaryRoles
  exact inferInstanceAs (Fintype (PrimaryRole p.channels p.buses ⊕ Gate p ⊕ Unit))

def gateVertex (p : Parameters) (g : Gate p) : Vertex p := .inr (.inl g)

theorem gateVertex_injective (p : Parameters) : Function.Injective (gateVertex p) := by
  intro g h eq
  exact Sum.inl.inj (Sum.inr.inj eq)

theorem gateVertex_mem_net (p : Parameters) (g : Gate p) (s : GlobalVariable p) :
    gateVertex p g ∈ (layout p).nets.net s ↔
      s = output p g ∨ s ∈ (producer p g).gate.inputs.map Prod.fst := by
  have source : gateVertex p g = CircuitLayout.inputVertex ((layout p).producer s) ↔
      s = output p g := by
    have injective : Function.Injective
        (CircuitLayout.inputVertex (Input := PrimaryRole p.channels p.buses)
          (Gate := Gate p) (Output := Unit)) := by
      intro x y eq
      cases x <;> cases y <;> simp_all [CircuitLayout.inputVertex]
    constructor
    · intro eq
      have slots : producerSlot p s = .inr g := injective eq.symm
      calc
        s = signal p (producerSlot p s) := (signal_producerSlot p s).symm
        _ = output p g := by rw [slots]; rfl
    · intro eq
      subst s
      have slots : (layout p).producer (output p g) = .inr g := by
        simpa only [producer_output] using layout_producer p g
      rw [slots]; rfl
  change gateVertex p g ∈ insert _ ((layout p).consumers s |>.image CircuitLayout.consumerVertex) ↔ _
  rw [Finset.mem_insert, source]
  have consumer : gateVertex p g ∈ ((layout p).consumers s).image CircuitLayout.consumerVertex ↔
      Sum.inl g ∈ (layout p).consumers s := by
    simp only [Finset.mem_image, CircuitLayout.consumerVertex, gateVertex, Sum.inr.injEq,
      exists_eq_right]
  rw [consumer, layout_connection]

end Controller.Graph.BoundedCircuit
