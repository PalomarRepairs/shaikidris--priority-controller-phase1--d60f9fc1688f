module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Extensions.BoundedNativeDetector

public import Mathlib.Tactic.Ring

@[expose] public section

/-! The bounded-AND detector has a concrete word width, canonical original
input, complete termination and semantic acceptance, checked native output,
and explicit bounds for runtime, live storage and resident instructions. -/
namespace Controller.Extensions.BoundedNativeComplete
open Controller Controller.Decoder Controller.Decoder.DAG Controller.Cost
open Controller.Native Controller.Native.SourceController Controller.Cost.NativeSourceExecution

def initial (parameters : Parameters) : State (BoundedNativeDetector.width parameters) 8 where
  reg _ := word _ 0
  heap := #[]
  stack := SharedDetectorCold.inputWords _ (UniformDAGOutputs.rowsOfGraph parameters.decoder)
    (parameters.decoder.roots.map Fin.val) (assignmentOfSet {parameters.bridge.target})
  output := []
  pc := word _ 0
  halted := false

theorem input_space (parameters : Parameters) :
    (initial parameters).liveWords ≤ 7*parameters.decoder.countedSize+14 := by
  have length := SharedDetectorCold.inputWords_length (BoundedNativeDetector.width parameters) parameters.decoder
    _ _ (UniformDAGOutputs.rowsOfGraph_match parameters.decoder) rfl (assignmentOfSet {parameters.bridge.target})
  have bound := SupportColdPrepare.packet_bound parameters.decoder
  simp only [initial,State.liveWords,List.length_nil,Nat.add_zero,Array.size_empty]
  omega

/-- The eligible set recovered from the actual emitted physical input. -/
def emittedSet (parameters : Parameters) (final : State wordWidth 8) : Finset (Channel parameters.channels) :=
  let assignment := NativeRealizedChecked.decodeOutput final.output (compile parameters).toState.count
  let input := sourceInput parameters assignment
  setOfAssignment (Physical.bridgeQualifiers parameters.bridge input (Physical.bridgeD parameters.bridge input))

theorem emitted_witness (parameters : Parameters) (raw : parameters.layout = .raw) (drive : parameters.drive = true)
    (final : State wordWidth 8)
    (checked : Certificate.ModelCheck.check (formula parameters)
      (NativeRealizedChecked.decodeOutput final.output (compile parameters).toState.count) = true) :
    Admissible parameters.buses parameters.bridge.target (emittedSet parameters final) ∧
      ∃ root ∈ parameters.decoder.roots,
        parameters.decoder.eval (assignmentOfSet (emittedSet parameters final)) root ≠
          parameters.decoder.eval (assignmentOfSet {parameters.bridge.target}) root := by
  let assignment := NativeRealizedChecked.decodeOutput final.output (compile parameters).toState.count
  let input := sourceInput parameters assignment
  let wire := Physical.bridgeD parameters.bridge input
  have detects := source_model_implies_physical_detection parameters assignment raw
    ((Certificate.ModelCheck.check_iff _ _).mp checked)
  obtain ⟨interface,differs⟩ := detects
  rw [drive] at interface
  have changed : Physical.stageFlag input.enable (input.request input.firstBus) ≠
      Physical.bridgeFirstFlag parameters.bridge input wire := by
    intro equal
    exact Physical.no_observation_change_of_firstFlag_eq parameters.bridge input wire parameters.observations equal differs
  obtain ⟨healthy,eligible⟩ := Physical.separated_drive_one_image parameters.bridge input interface changed
  obtain ⟨output,different⟩ := differs
  refine ⟨eligible,parameters.decoder.roots.get output,List.get_mem _ _,?_⟩
  change parameters.decoder.eval (assignmentOfSet (setOfAssignment (Physical.bridgeQualifiers parameters.bridge input wire)))
      (parameters.decoder.roots.get output) ≠ _
  rw [assignmentOfSet_setOfAssignment]
  change parameters.decoder.eval (Physical.healthyQualifiers input) (parameters.decoder.roots.get output) ≠
    parameters.decoder.eval (Physical.bridgeQualifiers parameters.bridge input wire) (parameters.decoder.roots.get output) at different
  rw [healthy] at different
  exact different.symm

set_option maxHeartbeats 1800000 in
theorem execution (parameters : Parameters) (raw : parameters.layout = .raw)
    (k : Nat) (andBound : parameters.decoder.liveAndCount ≤ k) :
    ∃ final ticks peak,
      Execution (BoundedNativeDetector.program parameters (BoundedNativeDetector.width parameters) k)
        (initial parameters) final ticks peak ∧ final.halted = true ∧
      (final.reg 4 = word _ 1 ↔ BoundedNativeDetector.Detects parameters) ∧
      ticks ≤ BoundedNativeCold.timeBound parameters k ∧
      peak ≤ 900*(parameters.decoder.countedSize+1)+3*(selectedSize parameters).total+30 ∧
      programWords (BoundedNativeDetector.program parameters (BoundedNativeDetector.width parameters) k) ≤
        13600*(parameters.decoder.countedSize+1)+272*(selectedSize parameters).total ∧
      (final.reg 4 = word _ 1 → Certificate.ModelCheck.check (formula parameters)
        (NativeRealizedChecked.decodeOutput final.output (compile parameters).toState.count) = true) ∧
      (final.reg 4 = word _ 1 → Admissible parameters.buses parameters.bridge.target (emittedSet parameters final) ∧
        ∃ root ∈ parameters.decoder.roots,
          parameters.decoder.eval (assignmentOfSet (emittedSet parameters final)) root ≠
            parameters.decoder.eval (assignmentOfSet {parameters.bridge.target}) root) := by
  have room := BoundedNativeDetector.capacity parameters
  obtain ⟨final,ticks,peak,trace,halted,decision,time,space,words,checked,_⟩ :=
    BoundedNativeDetector.execution parameters raw k andBound room (initial parameters) [] rfl
      (by simp only [initial,List.append_nil]) rfl rfl
  have accepts := BoundedNativeDetector.acceptance_iff parameters k andBound (by omega) final decision
  have startSpace := input_space parameters
  have actualCheck : final.reg 4 = word _ 1 → Certificate.ModelCheck.check (formula parameters)
      (NativeRealizedChecked.decodeOutput final.output (compile parameters).toState.count) = true := by
    intro accepted
    apply checked
    have semantic := SupportStream.detectSet_none_iff parameters.decoder k andBound parameters.buses parameters.bridge.target parameters.drive
    apply Option.ne_none_iff_isSome.mp
    intro none
    exact (semantic.mp none) (accepts.mp accepted)
  exact ⟨final,ticks,peak,trace,halted,accepts,time,by omega,words,actualCheck,
    fun accepted => emitted_witness parameters raw (accepts.mp accepted).1 final (actualCheck accepted)⟩

theorem time_bound (parameters : Parameters) (k : Nat) :
    BoundedNativeCold.timeBound parameters k ≤
      15000*(BoundedAnd.supportCount parameters.channels k+parameters.decoder.roots.length*2^k)*
        (parameters.decoder.countedSize+1)+100*(selectedSize parameters).total := by
  have positive : 0<BoundedAnd.supportCount parameters.channels k := by
    rw [← SupportStream.leaves_eq_supportCount]
    exact SupportStream.leaves_positive _ _
  have conditional : (if parameters.decoder.roots.all (parameters.decoder.evalTable (assignmentOfSet {parameters.bridge.target}))
      then 0 else (100*(parameters.decoder.countedSize+1)+50)*BoundedAnd.supportCount parameters.channels k) ≤
      (100*(parameters.decoder.countedSize+1)+50)*BoundedAnd.supportCount parameters.channels k := by split <;> omega
  have absorb := Nat.mul_le_mul_left parameters.decoder.countedSize (by omega :
    1 ≤ BoundedAnd.supportCount parameters.channels k)
  have support := Nat.mul_le_mul_right (BoundedAnd.supportCount parameters.channels k)
    (by omega : 100*(parameters.decoder.countedSize+1)+50 ≤ 150*(parameters.decoder.countedSize+1))
  have root := Nat.mul_le_mul_right (2^k*parameters.decoder.roots.length)
    (by omega : 7000*(parameters.decoder.countedSize+1)+90 ≤ 7090*(parameters.decoder.countedSize+1))
  unfold BoundedNativeCold.timeBound
  nlinarith [Nat.zero_le (parameters.decoder.countedSize*BoundedAnd.supportCount parameters.channels k),
    Nat.zero_le ((parameters.decoder.countedSize+1)*parameters.decoder.roots.length*2^k)]

/-- For fixed k the runtime is polynomial in the input size, plus native output. -/
theorem xp_time (parameters : Parameters) (k : Nat) :
    BoundedNativeCold.timeBound parameters k ≤
      15000*((k+2)*(parameters.decoder.countedSize+1)^(k+1)+
        (parameters.decoder.countedSize+1)*2^k)*(parameters.decoder.countedSize+1)+100*(selectedSize parameters).total := by
  have size := parameters.decoder.countedSize_eq
  have support := BoundedAnd.supportCount_polynomial parameters.channels k
  have power := Nat.pow_le_pow_left (by omega : parameters.channels+1 ≤ parameters.decoder.countedSize+1) (k+1)
  have supports : BoundedAnd.supportCount parameters.channels k ≤
      (k+2)*(parameters.decoder.countedSize+1)^(k+1) := support.trans (Nat.mul_le_mul_left _ power)
  have roots := Nat.mul_le_mul_right (2^k) (by omega : parameters.decoder.roots.length ≤ parameters.decoder.countedSize+1)
  exact (time_bound parameters k).trans (Nat.add_le_add_right
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.add_le_add supports roots))) _)

/-- With one live conjunction the support contribution is quadratic in n. -/
theorem one_and_time (parameters : Parameters) :
    BoundedNativeCold.timeBound parameters 1 ≤
      360000*(parameters.channels^2+parameters.decoder.roots.length)*parameters.decoder.countedSize+
        100*(selectedSize parameters).total := by
  have size := parameters.decoder.countedSize_eq
  have positive := parameters.bridge.target.isLt
  have support := BoundedAnd.supportCount_polynomial parameters.channels 1
  norm_num at support
  have first := time_bound parameters 1
  norm_num at first
  have quad : BoundedAnd.supportCount parameters.channels 1 ≤ 12*parameters.channels^2 := by nlinarith
  have count : BoundedAnd.supportCount parameters.channels 1+parameters.decoder.roots.length*2 ≤
      12*(parameters.channels^2+parameters.decoder.roots.length) := by omega
  have graph : parameters.decoder.countedSize+1 ≤ 2*parameters.decoder.countedSize := by omega
  calc
    _ ≤ 15000*(12*(parameters.channels^2+parameters.decoder.roots.length))*(2*parameters.decoder.countedSize)+
        100*(selectedSize parameters).total := first.trans (Nat.add_le_add_right (Nat.mul_le_mul
          (Nat.mul_le_mul_left _ count) graph) _)
    _ = _ := by ring

/-- Healthy-one-only observations skip channel supports, giving an FPT bound. -/
theorem healthy_one_query_time (parameters : Parameters) (k : Nat)
    (healthy : parameters.decoder.roots.all (parameters.decoder.evalTable (assignmentOfSet {parameters.bridge.target})) = true) :
    BoundedNativeCold.timeBound parameters k ≤
      15000*(parameters.decoder.roots.length*2^k+1)*(parameters.decoder.countedSize+1)+100*(selectedSize parameters).total := by
  have coefficient := Nat.mul_le_mul_right (2^k*parameters.decoder.roots.length)
    (by omega : 7000*(parameters.decoder.countedSize+1)+90 ≤ 7090*(parameters.decoder.countedSize+1))
  unfold BoundedNativeCold.timeBound
  rw [ite_eq_left healthy]
  nlinarith [Nat.zero_le ((parameters.decoder.countedSize+1)*2^k*parameters.decoder.roots.length)]

theorem healthy_one_nonempty_time (parameters : Parameters) (k : Nat)
    (healthy : parameters.decoder.roots.all (parameters.decoder.evalTable (assignmentOfSet {parameters.bridge.target})) = true)
    (nonempty : 0<parameters.decoder.roots.length) :
    BoundedNativeCold.timeBound parameters k ≤
      30000*(parameters.decoder.roots.length*2^k)*(parameters.decoder.countedSize+1)+100*(selectedSize parameters).total := by
  have positive := Nat.two_pow_pos k
  have lower : 1 ≤ parameters.decoder.roots.length*2^k := by nlinarith
  have count : parameters.decoder.roots.length*2^k+1 ≤ 2*(parameters.decoder.roots.length*2^k) := by omega
  calc
    _ ≤ 15000*(2*(parameters.decoder.roots.length*2^k))*(parameters.decoder.countedSize+1)+100*(selectedSize parameters).total :=
      (healthy_one_query_time parameters k healthy).trans
        (Nat.add_le_add_right (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ count)) _)
    _ = _ := by ring

theorem healthy_one_time (parameters : Parameters) (k : Nat)
    (healthy : parameters.decoder.roots.all (parameters.decoder.evalTable (assignmentOfSet {parameters.bridge.target})) = true) :
    BoundedNativeCold.timeBound parameters k ≤
      15000*(2^k+1)*(parameters.decoder.countedSize+1)^2+100*(selectedSize parameters).total := by
  have size := parameters.decoder.countedSize_eq
  have roots : parameters.decoder.roots.length ≤ parameters.decoder.countedSize+1 := by omega
  have product := Nat.mul_le_mul_left ((7000*(parameters.decoder.countedSize+1)+90)*2^k) roots
  have coefficient := Nat.mul_le_mul_right (2^k*(parameters.decoder.countedSize+1))
    (by omega : 7000*(parameters.decoder.countedSize+1)+90 ≤ 7090*(parameters.decoder.countedSize+1))
  unfold BoundedNativeCold.timeBound
  rw [ite_eq_left healthy]
  nlinarith [Nat.zero_le (parameters.decoder.countedSize*2^k),
    Nat.zero_le (parameters.decoder.countedSize^2*2^k),Nat.zero_le (parameters.decoder.countedSize^2)]

end Controller.Extensions.BoundedNativeComplete
