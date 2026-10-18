module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.NativePhysicalRootGate

@[expose] public section

/-! Physical root producers execute against the supplied channel membership
prefix and append one physical root per source interface coordinate. -/
namespace Controller.Cost.NativeRootBuilder
open Controller.Cost.GateProgram Controller.Cost.NativeCircuitExecution Controller.CNF

variable {channelCount : Nat}

def PrefixStored (heap : Array (Word width)) (base : Nat) (values : Fin channelCount → Bool) : Prop :=
  ∀ index : Fin channelCount, ∃ valid : base + index.val < heap.size,
    heap[base + index.val]'valid = boolWord width (values index)

theorem PrefixStored.push (heap : Array (Word width)) (base : Nat)
    (values : Fin channelCount → Bool) (stored : PrefixStored heap base values) (value : Word width) :
    PrefixStored (heap.push value) base values := by
  intro index
  obtain ⟨valid, cell⟩ := stored index
  refine ⟨by simp only [Array.size_push]; omega, ?_⟩
  rw [Array.getElem_push_lt valid]
  exact cell

def code (width base entry : Nat) : List (Gate (Fin channelCount)) → List (Instruction width 4)
  | [] => []
  | gate :: rest => NativeGateExecution.code width base entry true gate ++
      code width base (entry + (NativeGateExecution.code width base entry true gate).length) rest

theorem code_length_le (width base entry : Nat) (gates : List (Gate (Fin channelCount)))
    (budget : ∀ gate ∈ gates, ∀ position,
      (NativeGateExecution.code width base position true gate).length ≤ 16) :
    (code width base entry gates).length ≤ 16 * gates.length := by
  induction gates generalizing entry with
  | nil => simp [code]
  | cons gate rest ih =>
    have first := budget gate (by simp) entry
    have tail := ih (entry + (NativeGateExecution.code width base entry true gate).length)
      (fun other member position => budget other (List.mem_cons_of_mem gate member) position)
    simp only [code, List.length_append, List.length_cons]
    omega

def resultWords (width : Nat) (values : Fin channelCount → Bool)
    (gates : List (Gate (Fin channelCount))) : List (Word width) :=
  gates.map (fun gate => boolWord width (gate.eval values))

set_option maxHeartbeats 3000000 in
theorem execution (resident : Program width 4) (state : State width 4)
    (values : Fin channelCount → Bool) (gates : List (Gate (Fin channelCount))) (base entry : Nat)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + (code width base entry gates).length < 2 ^ width)
    (boolFits : 1 < 2 ^ width) (heapFits : state.heap.size + gates.length < 2 ^ width)
    (stored : PrefixStored state.heap base values)
    (physical : BlockAt resident entry (code width base entry gates)) :
    ∃ final ticks, Execution resident state final ticks (state.liveWords + gates.length) ∧
      ticks ≤ (code width base entry gates).length ∧
      final.heap = state.heap ++ (resultWords width values gates).toArray ∧
      PrefixStored final.heap base values ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry + (code width base entry gates).length) ∧ final.halted = false := by
  induction gates generalizing state entry with
  | nil =>
    refine ⟨state, 0, ?_, by simp [code], ?_, stored, rfl, rfl, ?_, running⟩
    · simpa using Execution.refl (p := resident) state
    · simp [resultWords]
    · simpa only [code, List.length_nil, Nat.add_zero] using position
  | cons gate rest ih =>
    have currentBlock : BlockAt resident entry (NativeGateExecution.code width base entry true gate) :=
      BlockAt.prefix _ _ _ _ physical
    have currentStored : NativeGateFold.Stored state.heap values base gate.inputs := by
      intro literal _
      exact stored literal.1
    obtain ⟨middle, gateTicks, gateTrace, gateBound, middleHeap,
      middleStack, middleOutput, middlePC, middleRunning⟩ :=
      NativeGateExecution.execution resident state values gate true base entry position running
        (by simp only [code, List.length_append] at room; omega) boolFits
        (by omega) currentStored currentBlock
    have middleHeap' : middle.heap = state.heap.push (boolWord width (gate.eval values)) := by
      simpa using middleHeap
    have middleStored : PrefixStored middle.heap base values := by
      rw [middleHeap']
      exact PrefixStored.push state.heap base values stored _
    have restBlock : BlockAt resident
        (entry + (NativeGateExecution.code width base entry true gate).length)
        (code width base (entry + (NativeGateExecution.code width base entry true gate).length) rest) :=
      BlockAt.suffix _ _ _ _ physical
    obtain ⟨final, restTicks, restTrace, restBound, finalHeap,
      finalStored, finalStack, finalOutput, finalPC, finalRunning⟩ :=
      ih middle (entry + (NativeGateExecution.code width base entry true gate).length) middlePC middleRunning
        (by simpa only [code, List.length_append, Nat.add_assoc] using room)
        (by rw [middleHeap']; simp only [Array.size_push]; simp only [List.length_cons] at heapFits; omega)
        middleStored restBlock
    have middleLive : middle.liveWords = state.liveWords + 1 := by
      simp only [State.liveWords, middleHeap', middleStack, middleOutput, Array.size_push]
      omega
    refine ⟨final, gateTicks + restTicks, ?_, ?_, ?_, finalStored,
      finalStack.trans middleStack, finalOutput.trans middleOutput, ?_, finalRunning⟩
    · have peakEq : max (state.liveWords + 1) (middle.liveWords + rest.length) =
          state.liveWords + (gate :: rest).length := by rw [middleLive]; simp only [List.length_cons]; omega
      simpa only [peakEq] using gateTrace.append restTrace
    · simpa only [code, List.length_append] using Nat.add_le_add gateBound restBound
    · rw [finalHeap, middleHeap']
      apply Array.toList_inj.mp
      simp [resultWords, List.append_assoc]
    · simpa only [code, List.length_append, Nat.add_assoc] using finalPC

theorem appended_table (heap : Array (Word width)) (values : Fin rootCount → Bool) :
    TableStored (heap ++ (NativeRootLoad.words width values).toArray) heap.size values := by
  refine ⟨by simp, ?_⟩
  intro index
  have valid : heap.size + index.val < (heap ++ (NativeRootLoad.words width values).toArray).size := by
    simp only [Array.size_append, List.size_toArray, NativeRootLoad.words_length]
    omega
  refine ⟨valid, ?_⟩
  rw [Array.getElem_append_right (by omega)]
  obtain ⟨_, cell⟩ := (NativeRootLoad.table width values).2 index
  simpa only [Nat.add_sub_cancel_left, Nat.zero_add] using cell

open Controller.Native Controller.Native.SourceController

def sourceGates (parameters : Parameters) : List (Gate (Fin parameters.channels)) :=
  List.ofFn (NativePhysicalRootGate.sourceGate parameters)

@[simp] theorem sourceGates_length (parameters : Parameters) :
    (sourceGates parameters).length = SourceInitialIDs.rootCount parameters := by simp [sourceGates]

theorem source_code_length_le (parameters : Parameters) (width entry : Nat) :
    (code width 0 entry (sourceGates parameters)).length ≤ 16 * SourceInitialIDs.rootCount parameters := by
  apply (code_length_le width 0 entry (sourceGates parameters) ?_).trans_eq
    (by rw [sourceGates_length])
  intro producer member position
  obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
  exact NativePhysicalRootGate.code_length_le parameters.bridge.target
    ((SourceInitialIDs.rootIndex (n := parameters.channels) (b := parameters.buses)).symm index) width 0 position

theorem source_result_words (parameters : Parameters) (K : Finset (Channel parameters.channels)) (width : Nat) :
    resultWords width (assignmentOfSet K) (sourceGates parameters) =
      NativeRootLoad.words width (sourcePhysicalRoots parameters
        (Physical.realizeBridge parameters.bridge parameters.positiveBuses K)) := by
  simp only [resultWords, sourceGates, List.map_ofFn, NativeRootLoad.words]
  apply congrArg List.ofFn
  funext index
  simp only [Function.comp_apply]
  rw [NativePhysicalRootGate.sourceGate_value]

theorem source_execution (parameters : Parameters) (K : Finset (Channel parameters.channels))
    (resident : Program width 4) (state : State width 4) (entry : Nat)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + (code width 0 entry (sourceGates parameters)).length < 2 ^ width)
    (boolFits : 1 < 2 ^ width)
    (heapFits : state.heap.size + SourceInitialIDs.rootCount parameters < 2 ^ width)
    (stored : PrefixStored state.heap 0 (assignmentOfSet K))
    (physical : BlockAt resident entry (code width 0 entry (sourceGates parameters))) :
    ∃ final ticks, Execution resident state final ticks (state.liveWords + SourceInitialIDs.rootCount parameters) ∧
      ticks ≤ 16 * SourceInitialIDs.rootCount parameters ∧
      final.heap = state.heap ++ (NativeRootLoad.words width
        (sourcePhysicalRoots parameters (Physical.realizeBridge parameters.bridge parameters.positiveBuses K))).toArray ∧
      PrefixStored final.heap 0 (assignmentOfSet K) ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry + (code width 0 entry (sourceGates parameters)).length) ∧ final.halted = false := by
  obtain ⟨final, ticks, trace, bound, heap, retained, stack, output, pc, running⟩ :=
    execution resident state (assignmentOfSet K) (sourceGates parameters) 0 entry position running room
      boolFits (by simpa only [sourceGates_length] using heapFits) stored physical
  refine ⟨final, ticks, ?_, bound.trans (source_code_length_le parameters width entry), ?_, retained, stack, output, pc, running⟩
  · simpa only [sourceGates_length] using trace
  · simpa only [source_result_words] using heap

end Controller.Cost.NativeRootBuilder
