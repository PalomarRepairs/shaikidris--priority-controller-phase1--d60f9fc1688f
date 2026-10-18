module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.EnumerationEmissionOperands
public import Controller.Cost.EnumerationMasks
public import Controller.Cost.EnumerationMaskWrite
public import Controller.Physical.Realize

@[expose] public section

/-! Fixed primary-coordinate emission plan for the canonical realizing input.
The completed prefix supplies its actual set bits in the baseline region. -/
namespace Controller.Cost.EnumerationCanonicalCoordinates
open Controller.Decoder Controller.Native Controller.Native.Parameters Controller.Physical
open Controller.Cost.GateProgram Controller.Cost.EnumerationEmissionOperands

def operand (parameters : Parameters) (base : Nat) : PrimaryRole parameters.channels parameters.buses → Operand
  | .enable channel => if channel = parameters.bridge.target then .literal true else .cell (base + channel.val)
  | .request bus channel =>
    if bus.val = 0 then .literal (decide (channel = parameters.bridge.target))
    else if bus.val = 1 then .masked (base + channel.val) else .literal false
  | .wire => .literal true

def operands (parameters : Parameters) (base : Nat) : List Operand :=
  parameters.primaryRoles.map (operand parameters base)

@[simp] theorem operands_length (parameters : Parameters) (base : Nat) :
    (operands parameters base).length = parameters.channels + parameters.buses * parameters.channels + 1 := by
  simp only [operands, List.length_map, primaryRoles_length]

theorem requests_coordinates (target : Channel n) (K : Finset (Channel n))
    (bus : Fin b) (channel : Channel n) :
    realizeRequests target K b bus channel =
      if bus.val = 0 then assignmentOfSet {target} channel
      else if bus.val = 1 then (if target ∈ K then false else assignmentOfSet K channel) else false := by
  cases b with
  | zero => exact Fin.elim0 bus
  | succ b =>
    refine Fin.cases ?_ (fun suffix => ?_) bus
    · simp [realizeRequests]
    · cases b with
      | zero => exact Fin.elim0 suffix
      | succ b =>
        refine Fin.cases ?_ (fun later => ?_) suffix
        · simp only [realizeRequests, realizeTailRequests, Fin.cases_succ, Fin.cases_zero]
          by_cases member : target ∈ K <;> simp [member]
        · have beyond : later.val + 1 + 1 ≠ 1 := by omega
          simp only [realizeRequests, realizeTailRequests, Fin.cases_succ]
          simp [Fin.val_succ]

def Stored (parameters : Parameters) (heap : Array (Word width)) (base : Nat)
    (K : Finset (Channel parameters.channels)) : Prop :=
  ∀ channel : Channel parameters.channels,
    heap[base + channel.val]? = some (boolWord width (decide (channel ∈ K)))

private theorem stored_value (parameters : Parameters) (heap : Array (Word width)) (base : Nat)
    (K : Finset (Channel parameters.channels)) (stored : Stored parameters heap base K)
    (channel : Channel parameters.channels) :
    EnumerationStreamEmit.heapValue heap (base + channel.val) = boolWord width (decide (channel ∈ K)) := by
  simp [EnumerationStreamEmit.heapValue, stored channel]

theorem operand_value (parameters : Parameters) (heap : Array (Word width)) (base : Nat)
    (K : Finset (Channel parameters.channels)) (stored : Stored parameters heap base K)
    (role : PrimaryRole parameters.channels parameters.buses) :
    value heap (decide (parameters.bridge.target ∈ K)) (operand parameters base role) =
      boolWord width (primaryAssignment (realizeBridge parameters.bridge parameters.positiveBuses K) true role) := by
  cases role with
  | enable channel =>
    by_cases target : channel = parameters.bridge.target
    · subst channel
      simp [operand, value, primaryAssignment, realizeBridge, assignmentOfSet]
    · simp [operand, target, value, stored_value parameters heap base K stored channel,
        primaryAssignment, realizeBridge, assignmentOfSet]
  | request bus channel =>
    rw [show primaryAssignment (realizeBridge parameters.bridge parameters.positiveBuses K) true
        (.request bus channel) = realizeRequests parameters.bridge.target K parameters.buses bus channel from rfl,
      requests_coordinates]
    by_cases first : bus.val = 0
    · simp [operand, first, value, assignmentOfSet]
    · by_cases second : bus.val = 1
      · by_cases member : parameters.bridge.target ∈ K
        · simp [operand, second, value, member]
        · simp [operand, second, value, member,
            stored_value parameters heap base K stored channel, assignmentOfSet]
      · simp [operand, first, second, value]
  | wire => rfl

theorem operands_value (parameters : Parameters) (heap : Array (Word width)) (base : Nat)
    (K : Finset (Channel parameters.channels)) (stored : Stored parameters heap base K) :
    (operands parameters base).map (value heap (decide (parameters.bridge.target ∈ K))) =
      parameters.primaryRoles.map (fun role => boolWord width
        (primaryAssignment (realizeBridge parameters.bridge parameters.positiveBuses K) true role)) := by
  unfold operands
  rw [List.map_map]
  apply List.map_congr_left
  intro role _
  exact operand_value parameters heap base K stored role

theorem operands_valid (parameters : Parameters) (heap : Array (Word width)) (base : Nat)
    (room : base + parameters.channels ≤ heap.size) :
    ∀ item ∈ operands parameters base, Valid heap item := by
  intro item member
  obtain ⟨role, _, rfl⟩ := List.mem_map.mp member
  cases role with
  | enable channel =>
    simp only [operand]
    split
    · trivial
    · change base + channel.val < heap.size
      have := channel.isLt; omega
  | request bus channel =>
    simp only [operand]
    split
    · trivial
    · split
      · change base + channel.val < heap.size
        have := channel.isLt; omega
      · trivial
  | wire => trivial

/-- An eligible completed prefix supplies the actual result bits to the emitter. -/
theorem completed_stored (parameters : Parameters) (heap : Array (Word width)) (base : Nat)
    (K : Finset (Channel parameters.channels)) (forced : parameters.buses = 1 → parameters.bridge.target ∈ K)
    (stored : EnumerationMaskWrite.Stored heap base
      (EnumerationMasks.maskList width parameters.buses parameters.bridge.target parameters.channels K)) :
    Stored parameters heap base K := by
  intro channel
  have cell := stored channel.val (by simp only [EnumerationMasks.maskList_length]; have := channel.isLt; omega)
  have expected := EnumerationMasks.result_baseline (width := width) (b := parameters.buses)
    (t := parameters.bridge.target) K forced channel
  rw [List.getElem?_eq_getElem (by simp only [EnumerationMasks.maskList_length]; have := channel.isLt; omega)] at expected
  exact cell.trans (congrArg some (Option.some.inj expected))

end Controller.Cost.EnumerationCanonicalCoordinates
