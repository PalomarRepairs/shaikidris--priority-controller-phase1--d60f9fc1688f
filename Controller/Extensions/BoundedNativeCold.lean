module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Extensions.BoundedNativePrepared
public import Controller.Extensions.SupportColdPrepare

@[expose] public section

/-! The complete bounded-AND detector consumes the original encoded DAG and
singleton channel vector from an empty heap, computes the healthy table,
searches both discrepancy directions, and halts with a checked native model
on acceptance. All phases belong to one fetched instruction image. -/
namespace Controller.Extensions.BoundedNativeCold
open Controller Controller.Decoder Controller.Decoder.DAG Controller.Cost
open Controller.Native Controller.Native.SourceController Controller.Cost.NativeSourceExecution
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestInputStored
open Controller.Cost.SharedDetectorAssembly Controller.Cost.RawAdapterProgram

def code (parameters : Parameters) (width : Nat) (rows : List Row) (roots : List Nat) (k : Nat)
    (reference : Fin parameters.decoder.nodeCount) : List (Instruction width 8) :=
  let cold := SupportColdPrepare.code width parameters.decoder rows roots
  cold ++ ResidentSegment.code cold.length (BoundedNativePrepared.code parameters width rows roots k reference)

theorem code_bound (parameters : Parameters) (rows : List Row) (roots : List Nat) (k : Nat)
    (reference : Fin parameters.decoder.nodeCount) (matched : RowsMatch parameters.decoder rows)
    (rootMatches : RootsMatch parameters.decoder roots) :
    (code parameters width rows roots k reference).length ≤
      3400*(parameters.decoder.countedSize+1)+68*(selectedSize parameters).total := by
  have cold := SupportColdPrepare.code_bound (width := width) parameters.decoder rows roots matched rootMatches
  have driver := BoundedNativePrepared.code_bound (width := width) parameters rows roots k reference matched rootMatches
  simp only [code,List.length_append,ResidentSegment.code_length]
  omega

def timeBound (parameters : Parameters) (k : Nat) : Nat :=
  (if parameters.decoder.roots.all (parameters.decoder.evalTable (assignmentOfSet {parameters.bridge.target}))
    then 0 else (100*(parameters.decoder.countedSize+1)+50)*BoundedAnd.supportCount parameters.channels k)+
    (7000*(parameters.decoder.countedSize+1)+90)*2^k*parameters.decoder.roots.length+
    7000*(parameters.decoder.countedSize+1)+100*(selectedSize parameters).total

set_option maxHeartbeats 2000000 in
theorem execution (parameters : Parameters) (raw : parameters.layout = .raw) (drive : parameters.drive = true)
    (rows : List Row) (roots : List Nat) (matched : RowsMatch parameters.decoder rows)
    (heads : UniformDAGSource.HeadsMatch parameters.decoder rows matched)
    (rootMatches : RootsMatch parameters.decoder roots) (k : Nat) (andBound : parameters.decoder.liveAndCount ≤ k)
    (reference : Fin parameters.decoder.nodeCount)
    (capacity : 131072*(parameters.decoder.countedSize+(selectedSize parameters).total+1)<2^width)
    (state : State width 8) (suffix : List (Word width))
    (empty : state.heap = #[])
    (input : state.stack = SharedDetectorCold.inputWords width rows roots (assignmentOfSet {parameters.bridge.target}) ++ suffix)
    (position : state.pc = word width 0) (running : state.halted = false) :
    ∃ final ticks peak, Execution (code parameters width rows roots k reference).toArray state final ticks peak ∧
      final.halted = true ∧ final.reg 4 = word width
        (if (SupportStream.detectSet parameters.decoder k parameters.buses parameters.bridge.target parameters.drive).isSome then 1 else 0) ∧
      ticks ≤ timeBound parameters k ∧ peak ≤ state.liveWords+800*(parameters.decoder.countedSize+1)+
        3*(selectedSize parameters).total+12 ∧
      programWords (code parameters width rows roots k reference).toArray ≤
        13600*(parameters.decoder.countedSize+1)+272*(selectedSize parameters).total ∧
      ((SupportStream.detectSet parameters.decoder k parameters.buses parameters.bridge.target parameters.drive).isSome = true →
        Certificate.ModelCheck.check (formula parameters)
          (NativeRealizedChecked.decodeOutput final.output (compile parameters).toState.count) = true) ∧
      (SupportStream.detectSet parameters.decoder k parameters.buses parameters.bridge.target parameters.drive = none →
        final.output = state.output) := by
  let resident := (code parameters width rows roots k reference).toArray
  let cold := SupportColdPrepare.code width parameters.decoder rows roots
  let driver := BoundedNativePrepared.code parameters width rows roots k reference
  have wholeBound := code_bound (width := width) parameters rows roots k reference matched rootMatches
  have present : SharedRootRead.BlockAt resident 0 (code parameters width rows roots k reference) := by
    intro offset below
    simp only [resident,List.getElem?_toArray,Nat.zero_add]
  have coldAt := block_left resident 0 _ _ present
  have driverAt := block_right resident 0 _ _ present
  simp only [Nat.zero_add] at driverAt
  obtain ⟨prepared,ct,cp,prepare,ctime,cspace,heap,stack,output,pc,active⟩ :=
    SupportColdPrepare.execution resident state parameters.decoder rows roots matched heads rootMatches parameters.bridge.target
      suffix empty position running input (by omega) coldAt
  obtain ⟨emitted,dt,dp,detect,halted,decision,dtime,dspace,checked,unchanged⟩ :=
    BoundedNativePrepared.execution parameters raw drive rows roots matched heads rootMatches k andBound reference
      (by omega) { prepared with pc := word width 0 } heap rfl active
  have moved := ResidentSegment.execution resident driver cold.length prepared emitted dt dp pc driverAt
    (by change cold.length+driver.length<2^width
        have bound : cold.length+driver.length ≤ 3400*(parameters.decoder.countedSize+1)+68*(selectedSize parameters).total := by
          simpa only [code,List.length_append,ResidentSegment.code_length] using wholeBound
        omega) detect
  have suffixBound : suffix.length+state.output.length ≤ state.liveWords := by
    simp only [State.liveWords,input,List.length_append]
    omega
  have words := Nat.mul_le_mul_left 4 wholeBound
  refine ⟨relocatedState cold.length emitted,ct+dt,max cp dp,prepare.append moved,halted,decision,
    by change ct+dt ≤ timeBound parameters k; unfold timeBound; omega,?_,?_,checked,?_⟩
  · change dp ≤ _ at dspace
    rw [stack,output] at dspace
    omega
  · simpa only [programWords,List.size_toArray,← Nat.mul_assoc,Nat.reduceMul,Nat.mul_add] using words
  · intro none
    exact (unchanged none).trans output

end Controller.Extensions.BoundedNativeCold
