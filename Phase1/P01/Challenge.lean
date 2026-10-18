module

public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Finset.BooleanAlgebra

@[expose] public section

/-!
# Exact fault images in a priority controller

Primary enable and request bits are independent. The selector uses its literal
XOR-mask recurrence; the final qualifiers are computed from the resulting flags.
A legal bridge has a target and a disjoint nonempty driver set. The first flag
is the only selector occurrence changed by this bridge interface.

The results give the exact drive-one qualifier-set image, rule out drive-zero
detection, and characterize discrepancy under arbitrary Boolean observations.
They also identify the global nonemptiness obstruction and classify a specified
qualifier-only stuck-at occurrence. Bus positivity and fault activation remain
explicit. No algorithmic complexity or arbitrary-CNF recognition is asserted.
-/

namespace Controller

/-- An index among the n declared channels, including unused channels. -/
abbrev Channel (n : ℕ) := Fin n

/-- A Boolean qualifier value at each declared channel. -/
abbrev Assignment (n : ℕ) := Channel n → Bool

/-- The Boolean indicator of a finite qualifier set. -/
def assignmentOfSet {n : ℕ} (K : Finset (Channel n)) : Assignment n :=
  fun i => decide (i ∈ K)
/-- Physical image restriction; positive bus count is imposed by the physical model. -/
def Admissible {n : ℕ} (b : ℕ) (t : Channel n) (K : Finset (Channel n)) : Prop :=
  K.Nonempty ∧ (b = 1 → t ∈ K)

end Controller

namespace Controller.Physical

/-- Independent enable and request inputs of a controller with at least one bus.
The request arguments are bus, then channel. -/
structure PrimaryInput (n b : ℕ) where
  positiveBuses : 0 < b
  enable : Assignment n
  request : Fin b → Assignment n

/-- The first bus, whose existence is part of the physical input type. -/
def PrimaryInput.firstBus {n b : ℕ} (input : PrimaryInput n b) : Fin b :=
  ⟨0, input.positiveBuses⟩

/-- The Boolean OR of all channel values; the empty OR is false. -/
def anyTrue {n : ℕ} (a : Assignment n) : Bool :=
  decide (∃ i, a i = true)

/-- The local request after all preceding masks have been applied. -/
def stageTerms {n : ℕ} (active request : Assignment n) : Assignment n :=
  fun i => active i && request i

/-- The healthy flag selected by the local requests. -/
def stageFlag {n : ℕ} (active request : Assignment n) : Bool :=
  anyTrue (stageTerms active request)

/-- The source's XOR mask, including its negated local-request input. -/
def stageMask {n : ℕ} (flag : Bool) (terms : Assignment n) : Assignment n :=
  fun i => flag ^^ !(terms i)

/-- Add the current literal XOR mask to the accumulated enable-and-mask value. -/
def nextActive {n : ℕ} (active request : Assignment n) (flag : Bool) : Assignment n :=
  fun i => active i && stageMask flag (stageTerms active request) i

/-- A dimension-indexed trace of the literal selector recurrence. -/
structure SelectorRun (n b : ℕ) where
  flags : Fin b → Bool
  activeBefore : Fin b → Assignment n
  terms : Fin b → Assignment n
  masks : Fin b → Assignment n
  finalActive : Assignment n

/-- Execute the literal recurrence. An override supplies only the first flag.
The zero-bus case is used for suffix induction, not as a physical controller. -/
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

/-- A qualifier requires enablement and every request whose bus flag is true. -/
def qualifiers {n b : ℕ} (enable : Assignment n) (request : Fin b → Assignment n)
    (flags : Fin b → Bool) : Assignment n :=
  fun i => enable i && decide (∀ j, flags j = true → request j i = true)

/-- The completely healthy selector trace. -/
def healthyRun {n b : ℕ} (input : PrimaryInput n b) : SelectorRun n b :=
  runMasks b input.enable input.request none

/-- A trace with an explicitly supplied first flag and otherwise healthy stages. -/
def runFromFirst {n b : ℕ} (input : PrimaryInput n b) (first : Bool) : SelectorRun n b :=
  runMasks b input.enable input.request (some first)

/-- Healthy qualifiers, computed independently of the final accumulated mask. -/
def healthyQualifiers {n b : ℕ} (input : PrimaryInput n b) : Assignment n :=
  qualifiers input.enable input.request (healthyRun input).flags

/-- Qualifiers under a supplied first flag and the literal ensuing recurrence. -/
def qualifiersFromFirst {n b : ℕ} (input : PrimaryInput n b) (first : Bool) : Assignment n :=
  qualifiers input.enable input.request (runFromFirst input first).flags

/-- Observations are arbitrary Boolean functions of the qualifier vector. -/
def ObservationsDiffer {n q : ℕ} (outputs : Fin q → Assignment n → Bool)
    (healthy faulty : Assignment n) : Prop :=
  ∃ k, outputs k healthy ≠ outputs k faulty
/-- A target and a nonempty disjoint driver set for the bridge interface. -/
structure Bridge (n : ℕ) where
  target : Channel n
  drivers : Finset (Channel n)
  drivers_nonempty : drivers.Nonempty
  target_not_mem : target ∉ drivers

/-- Channels outside the target and driver group. This set may be empty. -/
def Bridge.remaining {n : ℕ} (bridge : Bridge n) : Finset (Channel n) :=
  Finset.univ \ insert bridge.target bridge.drivers

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
/-- A qualifier vector is nonzero when at least one channel is eligible. -/
def Nonzero {n : ℕ} (h : Assignment n) : Prop := ∃ i, h i = true

/-- A row indexed only by the coordinates in a supplied scope. -/
abbrev LocalAssignment {n : ℕ} (scope : Finset (Channel n)) :=
  {i : Channel n // i ∈ scope} → Bool

/-- Restrict a global qualifier vector to precisely the supplied coordinates. -/
def projectAssignment {n : ℕ} (scope : Finset (Channel n)) (h : Assignment n) :
    LocalAssignment scope := fun i => h i.val

end Controller.Physical

open Controller Controller.Physical in
/-- For positive bus count, the activated drive-one bridge image is exactly the healthy target singleton paired with an admissible faulty set. Every admitted pair has a primary-input realization. -/
theorem Controller.Physical.separated_drive_one_set_pair_image_iff {n b : ℕ} (bridge : Bridge n) (hb : 0 < b)
    (H K : Finset (Channel n)) :
    (∃ input : PrimaryInput n b, ∃ wire : Bool,
      BridgeInterfaceSatisfied bridge input true wire ∧
      stageFlag input.enable (input.request input.firstBus) ≠ bridgeFirstFlag bridge input wire ∧
      healthyQualifiers input = assignmentOfSet H ∧
      bridgeQualifiers bridge input wire = assignmentOfSet K) ↔
      H = {bridge.target} ∧ Admissible b bridge.target K := by
  sorry

open Controller Controller.Physical in
/-- No interface-satisfying primary input detects a drive-zero bridge, for any family of qualifier observations. -/
theorem Controller.Physical.not_bridgeDetectable_drive_zero {n b q : ℕ} (bridge : Bridge n)
    (outputs : Fin q → Assignment n → Bool) :
    ¬ BridgeDetectable (b := b) bridge false outputs := by
  sorry

open Controller Controller.Physical in
/-- A bridge is detectable exactly for drive one and an admissible qualifier set whose observation differs from the healthy target singleton. -/
theorem Controller.Physical.bridge_detectable_iff_exists_output {n b q : ℕ} (bridge : Bridge n) (hb : 0 < b)
    (drive : Bool) (outputs : Fin q → Assignment n → Bool) :
    BridgeDetectable (b := b) bridge drive outputs ↔
      drive = true ∧ ∃ K : Finset (Channel n), Admissible b bridge.target K ∧
        ∃ k : Fin q, outputs k (assignmentOfSet K) ≠ outputs k (assignmentOfSet {bridge.target}) := by
  sorry

open Controller Controller.Physical in
/-- Every Boolean row on a proper subset of channels extends to a nonzero full qualifier assignment. -/
theorem Controller.Physical.proper_projection_full {n : ℕ} (scope : Finset (Channel n))
    (hproper : scope ≠ Finset.univ) (row : LocalAssignment scope) :
    ∃ h : Assignment n, Nonzero h ∧ projectAssignment scope h = row := by
  sorry

open Controller Controller.Physical in
/-- Any family of proper-coordinate relations valid on every nonzero assignment also accepts the zero assignment; such relations cannot express global nonemptiness. -/
theorem Controller.Physical.valid_local_relations_accept_zero {n : ℕ} {ι : Type*}
    (scopes : ι → Finset (Channel n)) (proper : ∀ a, scopes a ≠ Finset.univ)
    (relations : (a : ι) → LocalAssignment (scopes a) → Prop)
    (valid : ∀ h : Assignment n, Nonzero h → ∀ a,
      relations a (projectAssignment (scopes a) h)) :
    ∀ a, relations a (projectAssignment (scopes a) (fun _ => false)) := by
  sorry

open Controller Controller.Physical in
/-- For the qualifier-only stuck-at occurrence with unchanged selector flags, detection is possible exactly with at least two channels and either stuck value true or the distinguished target channel. -/
theorem Controller.Physical.stuck_detectable_iff {n b : ℕ} (distinguished target : Channel n)
    (bus : Fin b) (stuck : Bool) :
    StuckDetectable distinguished target bus stuck ↔
      2 ≤ n ∧ (stuck = true ∨ target = distinguished) := by
  sorry
