module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Physical.Controller

@[expose] public section

/-!
# Physical bridge and qualifier-only stuck-at faults

Bridge activation is a predicate on independent primary inputs and an explicit
interface wire. The stuck-at model changes only one occurrence in a final
qualifier, using the unchanged healthy selector flags.
-/

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

/-- The remaining group is exactly the set of channels in neither other role. -/
@[simp] theorem Bridge.mem_remaining {n : ℕ} (bridge : Bridge n) (i : Channel n) :
    i ∈ bridge.remaining ↔ i ≠ bridge.target ∧ i ∉ bridge.drivers := by
  simp [Bridge.remaining]

/-- A one-channel controller cannot contain a legal bridge driver. -/
theorem no_bridge_one (bridge : Bridge 1) : False := by
  obtain ⟨i, hi⟩ := bridge.drivers_nonempty
  have heq : i = bridge.target := Subsingleton.elim _ _
  exact bridge.target_not_mem (heq ▸ hi)

/-- A legal target and disjoint nonempty driver group require two channels. -/
theorem Bridge.two_le {n : ℕ} (bridge : Bridge n) : 2 ≤ n := by
  obtain ⟨i, hi⟩ := bridge.drivers_nonempty
  by_contra hn
  have hi_bound := i.isLt
  have ht_bound := bridge.target.isLt
  have hval : i.val = bridge.target.val := by omega
  exact bridge.target_not_mem ((Fin.ext hval) ▸ hi)

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

/-- Override only the indicated active-high request occurrence used by a qualifier.
The supplied stuck value is that of the active-low branch, so the replacement is its negation. -/
def stuckRequests {n b : ℕ} (input : PrimaryInput n b) (target : Channel n)
    (bus : Fin b) (stuck : Bool) : Fin b → Assignment n :=
  fun j i => if i = target ∧ j = bus then !stuck else input.request j i

/-- The faulty qualifier vector uses unchanged healthy flags. -/
def stuckQualifiers {n b : ℕ} (input : PrimaryInput n b) (target : Channel n)
    (bus : Fin b) (stuck : Bool) : Assignment n :=
  qualifiers input.enable (stuckRequests input target bus stuck) (healthyRun input).flags

/-- The distinguished-channel qualifier observation, with empty ordinary OR false. -/
def qualifierOutput {n : ℕ} (distinguished : Channel n) (h : Assignment n) : Bool :=
  !h distinguished && decide (∃ i, i ≠ distinguished ∧ h i = true)

/-- Activation of an active-low stuck value is equality of the healthy active-high request. -/
def StuckActivated {n b : ℕ} (input : PrimaryInput n b) (target : Channel n)
    (bus : Fin b) (stuck : Bool) : Prop :=
  input.request bus target = stuck

/-- Detectability of the specified qualifier occurrence, with selector occurrences unchanged. -/
def StuckDetectable {n b : ℕ} (distinguished target : Channel n) (bus : Fin b)
    (stuck : Bool) : Prop :=
  ∃ input : PrimaryInput n b,
    StuckActivated input target bus stuck ∧
      qualifierOutput distinguished (healthyQualifiers input) ≠
        qualifierOutput distinguished (stuckQualifiers input target bus stuck)

/-- Every non-target qualifier is unchanged by the branch-local stuck fault. -/
theorem stuckQualifiers_eq_of_ne {n b : ℕ} (input : PrimaryInput n b)
    (target i : Channel n) (bus : Fin b) (stuck : Bool) (hi : i ≠ target) :
    stuckQualifiers input target bus stuck i = healthyQualifiers input i := by
  simp [stuckQualifiers, healthyQualifiers, qualifiers, stuckRequests, hi]

/-- With one channel the ordinary-channel OR is empty, for every qualifier vector. -/
@[simp] theorem qualifierOutput_one (distinguished : Channel 1) (h : Assignment 1) :
    qualifierOutput distinguished h = false := by
  have hn : ¬ ∃ i : Channel 1, i ≠ distinguished ∧ h i = true := by
    rintro ⟨i, hi, _⟩
    exact hi (Subsingleton.elim _ _)
  simp [qualifierOutput, hn]

/-- Every qualifier-only stuck fault on a one-channel controller is undetectable. -/
theorem not_stuckDetectable_one {b : ℕ} (distinguished target : Channel 1)
    (bus : Fin b) (stuck : Bool) : ¬ StuckDetectable distinguished target bus stuck := by
  simp [StuckDetectable]

end Controller.Physical
