module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.NativeSourceComplete
public import Controller.Physical.Realize

@[expose] public section

/-! The physical-input realizer uses native constant, alias and two-input AND
blocks. Their inputs reference the supplied channel-set membership table. -/
namespace Controller.Cost.NativePhysicalRootGate
open Controller.CNF Controller.Native Controller.Native.SourceController

variable {n b : Nat}

def gate (target : Channel n) : InterfaceAlias.Root n b → Gate (Fin n)
  | .enable channel => if channel = target then .constant true else .alias (channel, true)
  | .request bus channel =>
      if bus.val = 0 then .constant (decide (channel = target))
      else if bus.val = 1 then .and [(target, false), (channel, true)]
      else .constant false

theorem request_value (target : Channel n) (K : Finset (Channel n))
    (bus : Fin b) (channel : Channel n) :
    Physical.realizeRequests target K b bus channel =
      (if bus.val = 0 then decide (channel = target)
       else if bus.val = 1 then (!assignmentOfSet K target && assignmentOfSet K channel) else false) := by
  cases b with
  | zero => exact Fin.elim0 bus
  | succ b =>
    refine Fin.cases ?_ (fun tail => ?_) bus
    · simp [Physical.realizeRequests, assignmentOfSet]
    · cases b with
      | zero => exact Fin.elim0 tail
      | succ b =>
        refine Fin.cases ?_ (fun rest => ?_) tail
        · simp only [Physical.realizeRequests, Fin.cases_succ, Physical.realizeTailRequests, Fin.cases_zero]
          by_cases present : target ∈ K <;>
            simp [assignmentOfSet, present]
        · simp [Physical.realizeRequests, Physical.realizeTailRequests]

theorem gate_value (bridge : Physical.Bridge n) (positive : 0 < b)
    (K : Finset (Channel n)) (root : InterfaceAlias.Root n b) :
    (gate bridge.target root).eval (assignmentOfSet K) =
      (match root with
       | .enable channel => (Physical.realizeBridge bridge positive K).enable channel
       | .request bus channel => (Physical.realizeBridge bridge positive K).request bus channel) := by
  cases root with
  | enable channel =>
    by_cases same : channel = bridge.target <;>
      simp [gate, same, Gate.eval, literalValue, Physical.realizeBridge, assignmentOfSet]
  | request bus channel =>
    change (gate bridge.target (.request bus channel)).eval (assignmentOfSet K) =
      (Physical.realizeBridge bridge positive K).request bus channel
    rw [show (Physical.realizeBridge bridge positive K).request bus channel =
      Physical.realizeRequests bridge.target K b bus channel from rfl, request_value]
    by_cases first : bus.val = 0 <;> by_cases second : bus.val = 1 <;>
      simp [gate, first, second, Gate.eval, literalValue]

def sourceGate (parameters : Parameters) (index : Fin (SourceInitialIDs.rootCount parameters)) :
    Gate (Fin parameters.channels) := gate parameters.bridge.target
    ((SourceInitialIDs.rootIndex (n := parameters.channels) (b := parameters.buses)).symm index)

theorem sourceGate_value (parameters : Parameters) (K : Finset (Channel parameters.channels))
    (index : Fin (SourceInitialIDs.rootCount parameters)) :
    (sourceGate parameters index).eval (assignmentOfSet K) =
      sourcePhysicalRoots parameters (Physical.realizeBridge parameters.bridge parameters.positiveBuses K) index := by
  let root : InterfaceAlias.Root parameters.channels parameters.buses :=
    (SourceInitialIDs.rootIndex (n := parameters.channels) (b := parameters.buses)).symm index
  have observed := sourcePhysicalRoots_at_root parameters
    (Physical.realizeBridge parameters.bridge parameters.positiveBuses K) root
  have indexBack : SourceInitialIDs.rootIndex root = index := Equiv.apply_symm_apply _ index
  rw [indexBack] at observed
  change (gate parameters.bridge.target root).eval (assignmentOfSet K) = _
  have evaluated := gate_value parameters.bridge parameters.positiveBuses K root
  cases discriminator : root <;> simp only [discriminator] at evaluated observed ⊢ <;>
    exact evaluated.trans observed.symm


theorem code_length_le (target : Channel n) (root : InterfaceAlias.Root n b)
    (width base entry : Nat) :
    (NativeGateExecution.code width base entry true (gate target root)).length ≤ 16 := by
  cases root with
  | enable channel =>
    by_cases same : channel = target <;>
      simp [gate, same, NativeGateExecution.code]
  | request bus channel =>
    by_cases first : bus.val = 0 <;> by_cases second : bus.val = 1 <;>
      simp [gate, first, second, NativeGateExecution.code]

end Controller.Cost.NativePhysicalRootGate
