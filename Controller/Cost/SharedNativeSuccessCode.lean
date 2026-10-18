module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedWorklistCode
public import Controller.Cost.SharedMachineCapacity

public import Mathlib.Tactic.FinCases

@[expose] public section

namespace Controller.Cost.SharedNativeSuccessCode
open Controller.Cost.GateProgram Controller.Native Controller.Native.SourceController
open Controller.Cost.NativeCircuitExecution Controller.Cost.NativeSourceExecution

abbrev nativeEntry (entry : Nat) := entry + 43

def outputEntry (parameters : Parameters) (width base entry : Nat) : Nat :=
  SharedZeroNativeComplete.emitEntry parameters width base (nativeEntry entry)

def done (parameters : Parameters) (width base entry : Nat) : Nat :=
  outputEntry parameters width base entry + 3 * (compile parameters).toState.count + 7

def prelude (width entry : Nat) : List (Instruction width 8) :=
  ForestZeroAdmissibleCaller.projectionConstantsCode width |>.toList |>.append
    ((ForestZeroAdmissibleCaller.channelPrepareCode width).toList ++
    SharedRegisterStack.saveCode (List.finRange 8) ++
    (ForestZeroChannelPush.code width (entry + 29) (nativeEntry entry)).toList)

def suffix (parameters : Parameters) (width base entry returnPC : Nat) : List (Instruction width 8) :=
  (OutputProgram.emitCode width (NativeRealizedCore.addresses (base + parameters.channels) (compile parameters).toState.count)).map
    RegisterWiden.widenInstruction ++
  (SharedEvaluationReclaim.code width (outputEntry parameters width base entry + 3 * (compile parameters).toState.count)
    (done parameters width base entry) (parameters.channels + (compile parameters).toState.count)).toList ++
  SharedRegisterStack.restoreCode (List.finRange 8).reverse ++
  (ForestZeroReclaim.setupCode width).toList ++
  (ForestZeroReclaim.code width (done parameters width base entry + 11) returnPC).toList

@[irreducible] def code (parameters : Parameters) (width base entry returnPC : Nat) : List (Instruction width 8) :=
  prelude width entry ++
  (NativeRetainedExecution.code parameters width base (nativeEntry entry)).map RegisterWiden.widenInstruction ++
  suffix parameters width base entry returnPC

@[simp] theorem prelude_length : (prelude width entry).length = 43 := by
  simp [prelude, ForestZeroAdmissibleCaller.projectionConstantsCode, ForestZeroAdmissibleCaller.channelPrepareCode,
    SharedRegisterStack.saveCode, ForestZeroChannelPush.code]

theorem segment (program : Program width 8) (entry : Nat)
    (before block after : List (Instruction width 8))
    (present : SharedRootRead.BlockAt program entry (before ++ block ++ after)) :
    SharedRootRead.BlockAt program (entry + before.length) block := by
  intro offset bound
  have found := present (before.length + offset) (by simp; omega)
  rw [show (entry + before.length) + offset = entry + (before.length + offset) by omega]
  simpa [List.getElem?_append, bound, show ¬before.length + offset < before.length by omega] using found

theorem native_at (parameters : Parameters) (program : Program width 8) (base entry returnPC : Nat)
    (present : SharedRootRead.BlockAt program entry (code parameters width base entry returnPC)) :
    ForestZeroCallerWiden.WidenedBlockAt program (nativeEntry entry)
      (NativeRetainedExecution.code parameters width base (nativeEntry entry)) := by
  unfold code at present
  have block := segment program entry _ _ _ present
  simp only [prelude_length] at block
  intro offset bound
  have found := block offset (by simpa using bound)
  simpa only [List.getElem?_map] using found


@[simp] theorem suffix_length : (suffix parameters width base entry returnPC).length =
    3 * (compile parameters).toState.count + 22 := by
  simp [suffix, SharedRegisterStack.restoreCode, ForestZeroReclaim.setupCode, ForestZeroReclaim.code,
    NativeRealizedCore.addresses]

theorem code_length : (code parameters width base entry returnPC).length =
    (NativeRetainedExecution.code parameters width base (nativeEntry entry)).length +
      3 * (compile parameters).toState.count + 65 := by
  simp [code]
  omega

theorem suffix_at (parameters : Parameters) (program : Program width 8) (base entry returnPC : Nat)
    (present : SharedRootRead.BlockAt program entry (code parameters width base entry returnPC)) :
    SharedRootRead.BlockAt program (outputEntry parameters width base entry)
      (suffix parameters width base entry returnPC) := by
  have prepared : SharedRootRead.BlockAt program entry
      ((prelude width entry ++
        (NativeRetainedExecution.code parameters width base (nativeEntry entry)).map RegisterWiden.widenInstruction) ++
        suffix parameters width base entry returnPC ++ []) := by
    simpa [code, List.append_assoc] using present
  have found := segment program entry _ _ _ prepared
  simpa [outputEntry, SharedZeroNativeComplete.emitEntry, Nat.add_assoc] using found

theorem emit_at (parameters : Parameters) (program : Program width 8) (base entry returnPC : Nat)
    (present : SharedRootRead.BlockAt program entry (code parameters width base entry returnPC)) :
    ForestZeroCallerWiden.WidenedBlockAt program (outputEntry parameters width base entry)
      (OutputProgram.emitCode width (NativeRealizedCore.addresses (base + parameters.channels) (compile parameters).toState.count)) := by
  have tail := suffix_at parameters program base entry returnPC present
  have block : SharedRootRead.BlockAt program (outputEntry parameters width base entry + 0)
      ((OutputProgram.emitCode width (NativeRealizedCore.addresses (base + parameters.channels) (compile parameters).toState.count)).map
        RegisterWiden.widenInstruction) :=
    segment program (outputEntry parameters width base entry) [] _ _ (by simpa [suffix] using tail)
  intro offset bound
  simpa only [Nat.add_zero, List.getElem?_map] using block offset (by simpa using bound)


theorem release_at (parameters : Parameters) (program : Program width 8) (base entry returnPC : Nat)
    (present : SharedRootRead.BlockAt program entry (code parameters width base entry returnPC)) :
    RawTransferLoops.CodeAt program
      (outputEntry parameters width base entry + 3 * (compile parameters).toState.count)
      (SharedEvaluationReclaim.code width (outputEntry parameters width base entry + 3 * (compile parameters).toState.count)
        (done parameters width base entry) (parameters.channels + (compile parameters).toState.count)) := by
  have tail := suffix_at parameters program base entry returnPC present
  have block := segment program (outputEntry parameters width base entry)
    ((OutputProgram.emitCode width (NativeRealizedCore.addresses (base + parameters.channels) (compile parameters).toState.count)).map
      RegisterWiden.widenInstruction)
    (SharedEvaluationReclaim.code width (outputEntry parameters width base entry + 3 * (compile parameters).toState.count)
      (done parameters width base entry) (parameters.channels + (compile parameters).toState.count)).toList
    (SharedRegisterStack.restoreCode (List.finRange 8).reverse ++ (ForestZeroReclaim.setupCode width).toList ++
      (ForestZeroReclaim.code width (done parameters width base entry + 11) returnPC).toList)
    (by simpa [suffix, List.append_assoc] using tail)
  intro phase
  have found := block phase.val (by simpa using phase.isLt)
  simpa [NativeRealizedCore.addresses] using found

theorem restore_at (parameters : Parameters) (program : Program width 8) (base entry returnPC : Nat)
    (present : SharedRootRead.BlockAt program entry (code parameters width base entry returnPC)) :
    SharedRootRead.BlockAt program (done parameters width base entry)
      (SharedRegisterStack.restoreCode (List.finRange 8).reverse) := by
  have tail := suffix_at parameters program base entry returnPC present
  have block := segment program (outputEntry parameters width base entry)
    (((OutputProgram.emitCode width (NativeRealizedCore.addresses (base + parameters.channels) (compile parameters).toState.count)).map
      RegisterWiden.widenInstruction) ++
    (SharedEvaluationReclaim.code width (outputEntry parameters width base entry + 3 * (compile parameters).toState.count)
      (done parameters width base entry) (parameters.channels + (compile parameters).toState.count)).toList)
    (SharedRegisterStack.restoreCode (List.finRange 8).reverse)
    ((ForestZeroReclaim.setupCode width).toList ++
      (ForestZeroReclaim.code width (done parameters width base entry + 11) returnPC).toList)
    (by simpa [suffix, List.append_assoc] using tail)
  simpa [done, NativeRealizedCore.addresses, Nat.add_assoc] using block


structure PreludePhysical (program : Program width 8) (entry : Nat) : Prop where
  constants : ∀ phase : Fin 2, program[entry + phase.val]? =
    (ForestZeroAdmissibleCaller.projectionConstantsCode width)[phase.val]?
  preparation : ∀ phase : Fin 19, program[entry + 2 + phase.val]? =
    (ForestZeroAdmissibleCaller.channelPrepareCode width)[phase.val]?
  saved : SharedRootRead.BlockAt program (entry + 21) (SharedRegisterStack.saveCode (List.finRange 8))
  projection : ForestZeroChannelPush.CodeAt program (entry + 29) (nativeEntry entry)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem prelude_at (parameters : Parameters) (program : Program width 8) (base entry returnPC : Nat)
    (present : SharedRootRead.BlockAt program entry (code parameters width base entry returnPC)) :
    PreludePhysical program entry := by
  have block : SharedRootRead.BlockAt program (entry + 0) (prelude width entry) :=
    segment program entry [] _ _ (by simpa [code] using present)
  have fetched : ∀ offset, offset < 43 → program[entry + offset]? = (prelude width entry)[offset]? := by
    intro offset bound
    simpa using block offset (by simpa using bound)
  constructor
  · intro phase
    fin_cases phase <;> rw [fetched _ (by omega)] <;>
      simp [prelude, ForestZeroAdmissibleCaller.projectionConstantsCode]
  · intro phase
    fin_cases phase <;> simp only [Nat.add_assoc, Nat.reduceAdd] <;> rw [fetched _ (by omega)] <;>
      simp [prelude, List.getElem?_append, ForestZeroAdmissibleCaller.projectionConstantsCode,
        ForestZeroAdmissibleCaller.channelPrepareCode]
  · intro offset bound
    have small : offset < 8 := by simpa [SharedRegisterStack.saveCode] using bound
    interval_cases offset <;> simp only [Nat.add_assoc, Nat.reduceAdd] <;> rw [fetched _ (by omega)] <;>
      simp [prelude, List.getElem?_append, ForestZeroAdmissibleCaller.projectionConstantsCode,
        ForestZeroAdmissibleCaller.channelPrepareCode, SharedRegisterStack.saveCode, List.finRange] <;> rfl
  · intro phase
    fin_cases phase <;> simp only [Nat.add_assoc, Nat.reduceAdd] <;> rw [fetched _ (by omega)] <;>
      simp [prelude, List.getElem?_append, ForestZeroAdmissibleCaller.projectionConstantsCode,
        ForestZeroAdmissibleCaller.channelPrepareCode, SharedRegisterStack.saveCode, ForestZeroChannelPush.code, nativeEntry]


theorem cleanup_at (parameters : Parameters) (program : Program width 8) (base entry returnPC : Nat)
    (present : SharedRootRead.BlockAt program entry (code parameters width base entry returnPC)) :
    (∀ phase : Fin 3, program[done parameters width base entry + 8 + phase.val]? =
      (ForestZeroReclaim.setupCode width)[phase.val]?) ∧
    ForestZeroReclaim.At program (done parameters width base entry + 11) returnPC := by
  have tail := suffix_at parameters program base entry returnPC present
  have block := segment program (outputEntry parameters width base entry)
    (((OutputProgram.emitCode width (NativeRealizedCore.addresses (base + parameters.channels) (compile parameters).toState.count)).map
      RegisterWiden.widenInstruction) ++
      (SharedEvaluationReclaim.code width (outputEntry parameters width base entry + 3 * (compile parameters).toState.count)
        (done parameters width base entry) (parameters.channels + (compile parameters).toState.count)).toList ++
      SharedRegisterStack.restoreCode (List.finRange 8).reverse)
    ((ForestZeroReclaim.setupCode width).toList ++
      (ForestZeroReclaim.code width (done parameters width base entry + 11) returnPC).toList) []
    (by simpa [suffix, List.append_assoc] using tail)
  have fetched : ∀ offset, offset < 7 → program[done parameters width base entry + 8 + offset]? =
      ((ForestZeroReclaim.setupCode width).toList ++
        (ForestZeroReclaim.code width (done parameters width base entry + 11) returnPC).toList)[offset]? := by
    intro offset bound
    have found := block offset (by simpa [ForestZeroReclaim.setupCode, ForestZeroReclaim.code] using bound)
    simpa [done, SharedRegisterStack.restoreCode, NativeRealizedCore.addresses, Nat.add_assoc] using found
  constructor
  · intro phase
    fin_cases phase <;> rw [fetched _ (by omega)] <;>
      simp [ForestZeroReclaim.setupCode, List.getElem?_append]
  · intro phase
    have position : done parameters width base entry + 11 + phase.val =
        done parameters width base entry + 8 + (3 + phase.val) := by omega
    rw [position, fetched (3 + phase.val) (by have := phase.isLt; omega)]
    fin_cases phase <;> simp [ForestZeroReclaim.setupCode, ForestZeroReclaim.code, List.getElem?_append]


theorem execution (parameters : Parameters) (resident : Program width 8) (state : State width 8)
    (entry returnPC offBase nodes keep count : Nat) (dictionary : ForestZeroCompile.Dictionary ambient)
    (layout : ForestZeroDictionary.Layout ambient state.heap.size)
    (represented : ForestZeroDictionary.Represented state.heap layout dictionary)
    (ambientEq : ambient = parameters.channels + nodes)
    (adjacent : layout.inverseBase = layout.tableBase + ambient)
    (within : parameters.channels ≤ ambient) (queue : List (Fin dictionary.coordinates.size))
    (fifo : Controller.Horn.WorklistMark.Stored queue offBase state.heap)
    (position : state.pc = word width entry) (running : state.halted = false)
    (channelCell : state.heap[0]? = some (word width parameters.channels))
    (nodeCell : state.heap[1]? = some (word width nodes))
    (headerRoom : 1 < state.heap.size) (offRoom : offBase + 1 < 2 ^ width)
    (nativeHeap : state.heap.size + parameters.channels + (compile parameters).toState.count < 2 ^ width)
    (room : entry + (code parameters width state.heap.size entry returnPC).length < 2 ^ width)
    (present : SharedRootRead.BlockAt resident entry (code parameters width state.heap.size entry returnPC))
    (rest : List (Word width))
    (saved : state.stack = word width count :: word width layout.inverseBase ::
      word width dictionary.coordinates.size :: word width offBase :: rest)
    (allocated : state.heap.size = keep + count) :
    let K := setOfAssignment (SharedZeroNative.channels parameters dictionary queue within)
    ∃ final ticks peak, Execution resident state final ticks peak ∧
      ticks ≤ 55 * (selectedSize parameters).total + 4 * count + 46 ∧
      peak ≤ state.liveWords + 3 * (selectedSize parameters).total + 8 ∧
      final.heap.size = keep ∧
      final.stack = word width layout.inverseBase :: word width dictionary.coordinates.size :: word width offBase :: rest ∧
      final.output = (NativeRootLoad.words width
        (SourceLift.finite parameters (Physical.realizeBridge parameters.bridge parameters.positiveBuses K))).reverse ++ state.output ∧
      final.pc = word width returnPC ∧ final.halted = false ∧
      ForestZeroBackendFrame.PrefixFrame keep state.heap final.heap := by
  have positive : 0 < parameters.channels := by
    have := parameters.bridge.target.isLt
    omega
  have countBound := ForestZeroDictionary.count_le_ambient dictionary represented.coherent
  have tableBound := layout.tableBound
  have countFits : dictionary.coordinates.size + 1 < 2 ^ width := by omega
  have channelsFit : parameters.channels + 1 < 2 ^ width := by omega
  have countFit : count < 2 ^ width := by omega
  have entryProof := prelude_at parameters resident state.heap.size entry returnPC present
  have cleanupProof := cleanup_at parameters resident state.heap.size entry returnPC present
  have nativeLength := code_length (parameters := parameters) (width := width) (base := state.heap.size)
    (entry := entry) (returnPC := returnPC)
  simp only [nativeEntry] at nativeLength
  have endpoint : done parameters width state.heap.size entry + 15 =
      entry + (code parameters width state.heap.size entry returnPC).length := by
    simp only [done, outputEntry, SharedZeroNativeComplete.emitEntry, nativeEntry]
    omega
  have endRoom : done parameters width state.heap.size entry + 15 < 2 ^ width := by omega
  exact SharedZeroNativePrepared.terminal_execution parameters resident state entry (entry + 21) (entry + 29)
    (nativeEntry entry) offBase (done parameters width state.heap.size entry) nodes dictionary layout represented
    ambientEq adjacent within queue fifo countFits position running (by omega) entryProof.saved
    (by omega) (restore_at parameters resident state.heap.size entry returnPC present) rfl channelCell nodeCell
    headerRoom offRoom (by unfold done outputEntry SharedZeroNativeComplete.emitEntry nativeEntry at endRoom; omega)
    entryProof.constants entryProof.preparation channelsFit (by omega)
    (by unfold done outputEntry SharedZeroNativeComplete.emitEntry nativeEntry at endRoom; omega)
    entryProof.projection
    (by unfold done outputEntry SharedZeroNativeComplete.emitEntry at endRoom; omega)
    nativeHeap (native_at parameters resident state.heap.size entry returnPC present)
    (by simpa only [done, outputEntry] using (show done parameters width state.heap.size entry < 2 ^ width from by omega))
    (emit_at parameters resident state.heap.size entry returnPC present)
    (release_at parameters resident state.heap.size entry returnPC present)
    keep count rest returnPC cleanupProof.1 cleanupProof.2 endRoom countFit saved allocated

end Controller.Cost.SharedNativeSuccessCode
