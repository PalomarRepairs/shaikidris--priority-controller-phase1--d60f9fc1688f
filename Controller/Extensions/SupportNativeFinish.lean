module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Extensions.BasisNativeFinish

@[expose] public section

/-! The support continuation records acceptance in register four before the
low-register native evaluator. Evaluation and emission preserve that register,
and the final fetched halt retains the acceptance tag. -/
namespace Controller.Extensions.SupportNativeFinish
open Controller Controller.Decoder Controller.Native Controller.Native.SourceController
open Controller.Cost Controller.Cost.NativeSourceExecution Controller.Cost.GateProgram
open Controller.Cost.RawTransferLoops

def code (parameters : Parameters) (width base entry : Nat) : List (Instruction width 8) :=
  [.constant 4 (word width 1)] ++ BasisNativeFinish.code parameters width base (entry+1)

theorem code_bound (parameters : Parameters) :
    (code parameters width base entry).length ≤ 34*(selectedSize parameters).total+2 := by
  have bound := BasisNativeFinish.code_bound parameters width base (entry+1)
  simp only [code,List.length_append,List.length_singleton]
  omega

set_option maxHeartbeats 1800000 in
theorem execution (parameters : Parameters) (raw : parameters.layout = .raw)
    (K : Finset (Channel parameters.channels)) (eligible : Admissible parameters.buses parameters.bridge.target K)
    (drive : parameters.drive = true)
    (differs : ∃ output, parameters.observations output (assignmentOfSet {parameters.bridge.target}) ≠
      parameters.observations output (assignmentOfSet K))
    (resident : Program width 8) (state : State width 8) (entry : Nat) (suffix : List (Word width))
    (position : state.pc = word width entry) (running : state.halted = false)
    (input : state.stack = LiteralWitnessReturn.words width K ++ suffix)
    (room : entry+(code parameters width state.heap.size entry).length<2^width)
    (boolFits : 1<2^width) (tableRoom : state.heap.size+parameters.channels+(compile parameters).toState.count<2^width)
    (present : SharedRootRead.BlockAt resident entry (code parameters width state.heap.size entry)) :
    ∃ final ticks peak, Execution resident state final ticks peak ∧
      ticks ≤ 34*(selectedSize parameters).total+2 ∧ peak ≤ state.liveWords+2*(selectedSize parameters).total ∧
      final.stack = suffix ∧ final.halted = true ∧ final.reg 4 = word width 1 ∧
      Certificate.ModelCheck.check (formula parameters)
        (NativeRealizedChecked.decodeOutput final.output (compile parameters).toState.count) = true := by
  have nativeAt := SharedDetectorAssembly.block_right resident entry _ _ present
  simp only [List.length_singleton] at nativeAt
  obtain ⟨tagged,tag,tp,tv,th,ts,tout,tr,_⟩ :=
    SharedEvaluationReclaim.constant_execution resident entry 1 4 state position running
      (by simp only [code,List.length_append,List.length_singleton] at room; omega)
      (by simpa [code] using present 0 (by simp [code]))
  have firstAt := SharedDetectorAssembly.block_left resident (entry+1) _ _ nativeAt
  have restAt := SharedDetectorAssembly.block_right resident (entry+1) _ _ nativeAt
  simp only [List.length_map] at restAt
  have emitAt := SharedDetectorAssembly.block_left resident _ _ _ restAt
  have haltAt := SharedDetectorAssembly.block_right resident _ _ _ restAt
  simp only [List.length_map,OutputProgram.emitCode_length,NativeRealizedCore.addresses_length] at haltAt
  have physical : ForestZeroCallerWiden.WidenedBlockAt resident (entry+1)
      (NativeRetainedExecution.code parameters width state.heap.size (entry+1)) := by
    intro i below
    simpa only [List.getElem?_map] using firstAt i (by simpa only [List.length_map] using below)
  have codeLength := BasisNativeFinish.code_length parameters width state.heap.size (entry+1)
  have bounds := code_bound (width := width) (base := state.heap.size) (entry := entry) parameters
  have fullRoom : entry+1+(BasisNativeFinish.code parameters width state.heap.size (entry+1)).length<2^width := by
    simpa only [code,List.length_append,List.length_singleton,Nat.add_assoc,Nat.add_comm] using room
  obtain ⟨built,bt,build,btime,table,bs,bo,bp,br,_,high⟩ :=
    NativeRetainedCaller.execution parameters K resident tagged (entry+1) suffix tp tr
      (by simpa only [BasisNativeFinish.words_eq,ts] using input)
      (by rw [th]; omega) boolFits (by rw [th]; exact tableRoom)
      (by simpa only [th] using physical)
  rw [th] at table bp
  have nativeEmit : ForestZeroCallerWiden.WidenedBlockAt resident
      (entry+1+(NativeRetainedExecution.code parameters width state.heap.size (entry+1)).length)
      (OutputProgram.emitCode width (NativeRealizedCore.addresses (state.heap.size+parameters.channels)
        (compile parameters).toState.count)) := by
    intro i below
    simpa only [List.getElem?_map] using emitAt i (by simpa only [List.length_map] using below)
  obtain ⟨emitted,emit,eh,es,eo,ep,er,frame⟩ :=
    NativeRetainedEmit.execution resident built (state.heap.size+parameters.channels) _ _ table
      bp br (by omega) (by have exactSize := table.1; omega) nativeEmit
  let final := { emitted.advance with halted := true }
  have haltFetch : resident[(entry+1+(NativeRetainedExecution.code parameters width state.heap.size (entry+1)).length)+
      3*(compile parameters).toState.count]? = some .halt := by
    simpa only [Nat.add_zero,List.getElem?_cons_zero] using haltAt 0 (by simp)
  have haltStep : step (.halt : Instruction width 8) emitted = some final := by simp [step,er,final]
  have haltTrace := SharedDetectorSteps.single resident emitted final _ _ ep (by omega) haltFetch haltStep
  have finalLive : final.liveWords = emitted.liveWords := rfl
  have tagLive : tagged.liveWords = state.liveWords := by simp only [State.liveWords,th,ts,tout]
  have roots := (sourceCircuit parameters).roots_le
  have channels : parameters.channels ≤ SourceInitialIDs.rootCount parameters := by simp only [SourceInitialIDs.rootCount]; omega
  have variableBound : (compile parameters).toState.count ≤ (selectedSize parameters).total := by
    simp only [selectedSize,NativeSize.total]; omega
  have out : final.output = (NativeRootLoad.words width
      (SourceLift.finite parameters (Physical.realizeBridge parameters.bridge parameters.positiveBuses K))).reverse ++ state.output := by
    simp only [final,State.advance,eo,bo,tout]
  refine ⟨final,_,_,tag.append ((build.append emit).append haltTrace),by omega,?_,
    by simpa only [final,State.advance,es,bs] using rfl,rfl,?_,?_⟩
  · have builtLive := Execution.final_storage_le build
    have emitLive := Execution.final_storage_le emit
    simp only [tagLive,finalLive,tagLive] at *
    omega
  · exact (frame 4 (by decide)).trans ((high 4 (by decide)).trans tv)
  · rw [out,NativeRealizedChecked.output_decodes _ _ boolFits]
    exact SourceLift.eligible_checked parameters raw K eligible drive differs

end Controller.Extensions.SupportNativeFinish
