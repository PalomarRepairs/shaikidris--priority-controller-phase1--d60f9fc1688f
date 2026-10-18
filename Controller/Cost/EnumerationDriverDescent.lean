module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.EnumerationDriverPrefix

@[expose] public section

/-! Fetched descent control before the actual prefix oracle: depth/target tests
and the free false-child mask update use fixed branch addresses. -/
namespace Controller.Cost.EnumerationDriverDescent
open Controller.Decoder Controller.Native Controller.Cost.GateProgram Controller.Cost.RawTransferLoops
open Controller.Cost.SharedDetectorAssembly Controller.Cost.EnumerationDriverPrefix

def checks (parameters : Parameters) (width emit forced : Nat) : List (Instruction width 8) :=
  (SharedTagCompare.code width emit parameters.channels 3).toList ++
    (if parameters.buses = 1 then (SharedTagCompare.code width forced parameters.bridge.target.val 3).toList else [])

@[simp] theorem checks_length : (checks parameters width emit forced).length = 3 + (if parameters.buses = 1 then 3 else 0) := by
  by_cases one : parameters.buses = 1 <;> simp [checks, one]

private theorem pass_checks (parameters : Parameters) (program : Program width 8) (state : State width 8)
    (entry emit forced depth : Nat) (position : state.pc = word width entry) (running : state.halted = false)
    (held : state.reg 3 = word width depth) (lower : depth < parameters.channels)
    (free : ¬(parameters.buses = 1 ∧ parameters.bridge.target.val = depth))
    (fits : parameters.channels < 2 ^ width) (room : entry + (checks parameters width emit forced).length < 2 ^ width)
    (present : SharedRootRead.BlockAt program entry (checks parameters width emit forced)) :
    ∃ final, Execution program state final (checks parameters width emit forced).length state.liveWords ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry + (checks parameters width emit forced).length) ∧ final.halted = false ∧
      (∀ register : Fin 8, register ≠ 0 → final.reg register = state.reg register) := by
  have headAt := block_left program entry (SharedTagCompare.code width emit parameters.channels 3).toList
    (if parameters.buses = 1 then (SharedTagCompare.code width forced parameters.bridge.target.val 3).toList else []) present
  obtain ⟨tested, first, heap, stack, output, pc, active, frame⟩ :=
    SharedTagCompare.execution program state entry emit parameters.channels depth 3 (by decide) position running
      (by rw [checks_length] at room; omega) fits (by omega) held
      (by intro phase; simpa only [Array.getElem?_toList] using headAt phase.val (by simpa using phase.isLt))
  have nextPC : tested.pc = word width (entry + 3) := by
    simpa only [ite_eq_right (by omega : depth ≠ parameters.channels)] using pc
  by_cases one : parameters.buses = 1
  · have tailAt := block_right program entry (SharedTagCompare.code width emit parameters.channels 3).toList
      (if parameters.buses = 1 then (SharedTagCompare.code width forced parameters.bridge.target.val 3).toList else []) present
    simp only [one, ite_true, Array.length_toList, SharedTagCompare.code_size] at tailAt
    have different : depth ≠ parameters.bridge.target.val := fun same => free ⟨one, same.symm⟩
    obtain ⟨final, second, finalHeap, finalStack, finalOutput, finalPC, finalRunning, finalFrame⟩ :=
      SharedTagCompare.execution program tested (entry + 3) forced parameters.bridge.target.val depth 3 (by decide)
        nextPC active (by rw [checks_length, ite_eq_left one] at room; omega)
        (by have := parameters.bridge.target.isLt; omega) (by omega) ((frame 3 (by decide)).trans held)
        (by intro phase; simpa only [Array.getElem?_toList] using tailAt phase.val (by simpa using phase.isLt))
    have testedLive : tested.liveWords = state.liveWords := by simp only [State.liveWords, heap, stack, output]
    refine ⟨final, ?_, finalHeap.trans heap, finalStack.trans stack, finalOutput.trans output, ?_, finalRunning, ?_⟩
    · simpa only [checks_length, ite_eq_left one, testedLive, Nat.max_self, Nat.reduceAdd] using first.append second
    · simpa only [ite_eq_right different, checks_length, ite_eq_left one, Nat.add_assoc, Nat.reduceAdd] using finalPC
    · intro register notZero; rw [finalFrame register notZero, frame register notZero]
  · refine ⟨tested, ?_, heap, stack, output, ?_, active, frame⟩
    · simpa only [checks_length, ite_eq_right one, Nat.add_zero] using first
    · simpa only [checks_length, ite_eq_right one, Nat.add_zero] using nextPC

def freeCode (parameters : Parameters) (width packetSize emit forced call : Nat) : List (Instruction width 8) :=
  checks parameters width emit forced ++ EnumerationDriverControl.selectCode width (packetSize + parameters.channels) true 1 call

theorem free_entry (parameters : Parameters) (program : Program width 8) (state : State width 8)
    (entry emit forced call depth : Nat) (packet : Array (Word width)) (partialSet : Finset (Fin parameters.channels))
    (ready : Ready parameters packet depth depth partialSet state) (bounded : Enumeration.Bounded depth partialSet)
    (lower : depth < parameters.channels) (free : ¬(parameters.buses = 1 ∧ parameters.bridge.target.val = depth))
    (position : state.pc = word width entry) (fits : parameters.channels < 2 ^ width)
    (heapFits : state.heap.size < 2 ^ width) (room : entry + (freeCode parameters width packet.size emit forced call).length < 2 ^ width)
    (present : SharedRootRead.BlockAt program entry (freeCode parameters width packet.size emit forced call)) :
    ∃ final, Execution program state final (10 + (if parameters.buses = 1 then 3 else 0)) state.liveWords ∧
      Ready parameters packet (depth + 1) depth partialSet final ∧
      final.pc = word width call ∧ final.reg 5 = word width 1 ∧ final.output = state.output := by
  have checkAt := block_left program entry (checks parameters width emit forced)
    (EnumerationDriverControl.selectCode width (packet.size + parameters.channels) true 1 call) present
  have selectAt := block_right program entry (checks parameters width emit forced)
    (EnumerationDriverControl.selectCode width (packet.size + parameters.channels) true 1 call) present
  obtain ⟨tested, first, heap, stack, output, pc, running, frame⟩ :=
    pass_checks parameters program state entry emit forced depth position ready.running ready.counter lower free fits
      (by simp only [freeCode, List.length_append] at room; omega) checkAt
  have testReady : Ready parameters packet depth depth partialSet tested :=
    ⟨heap.trans ready.heap, (frame 3 (by decide)).trans ready.counter, stack.trans ready.stack, running⟩
  obtain ⟨final, second, finalReady, finalPC, finalMode, finalOutput⟩ :=
    EnumerationDriverPrefix.false_child_entry parameters program tested (entry + (checks parameters width emit forced).length)
      call depth packet partialSet testReady bounded lower pc
      (by simpa only [heap] using heapFits)
      (by simp only [freeCode, List.length_append, EnumerationDriverControl.selectCode_length] at room; omega) selectAt
  have testedLive : tested.liveWords = state.liveWords := by simp only [State.liveWords, heap, stack, output]
  refine ⟨final, ?_, finalReady, finalPC, finalMode, finalOutput.trans output⟩
  · have joined := first.append second
    rw [testedLive, Nat.max_self, checks_length] at joined
    convert joined using 1; omega

/-- At full depth, the first fixed comparison reaches model emission without
entering either mask mutation or the oracle. -/
theorem leaf_entry (parameters : Parameters) (program : Program width 8) (state : State width 8)
    (entry emit forced call : Nat) (packet : Array (Word width)) (partialSet : Finset (Fin parameters.channels))
    (ready : Ready parameters packet parameters.channels parameters.channels partialSet state)
    (position : state.pc = word width entry) (fits : parameters.channels < 2 ^ width) (room : entry + 3 < 2 ^ width)
    (present : SharedRootRead.BlockAt program entry (freeCode parameters width packet.size emit forced call)) :
    ∃ final, Execution program state final 3 state.liveWords ∧
      Ready parameters packet parameters.channels parameters.channels partialSet final ∧
      final.pc = word width emit ∧ final.output = state.output := by
  have checksAt := block_left program entry (checks parameters width emit forced)
    (EnumerationDriverControl.selectCode width (packet.size + parameters.channels) true 1 call) present
  have headAt := block_left program entry (SharedTagCompare.code width emit parameters.channels 3).toList
    (if parameters.buses = 1 then (SharedTagCompare.code width forced parameters.bridge.target.val 3).toList else []) checksAt
  obtain ⟨final, trace, heap, stack, output, pc, running, frame⟩ :=
    SharedTagCompare.execution program state entry emit parameters.channels parameters.channels 3 (by decide)
      position ready.running room fits fits ready.counter
      (by intro phase; simpa only [Array.getElem?_toList] using headAt phase.val (by simpa using phase.isLt))
  refine ⟨final, trace, ⟨heap.trans ready.heap, (frame 3 (by decide)).trans ready.counter, stack.trans ready.stack, running⟩, ?_, output⟩
  simpa using pc

/-- The forced target takes the second fixed comparison and the existing
four-instruction increment tail, with no false-child query. -/
theorem forced_entry (parameters : Parameters) (program : Program width 8) (state : State width 8)
    (entry emit forced call descend depth : Nat) (packet : Array (Word width)) (partialSet : Finset (Fin parameters.channels))
    (ready : Ready parameters packet depth depth partialSet state) (bounded : Enumeration.Bounded depth partialSet)
    (lower : depth < parameters.channels) (one : parameters.buses = 1) (target : parameters.bridge.target.val = depth)
    (position : state.pc = word width entry) (fits : parameters.channels < 2 ^ width)
    (room : entry + 6 < 2 ^ width) (forcedRoom : forced + 4 < 2 ^ width)
    (present : SharedRootRead.BlockAt program entry (freeCode parameters width packet.size emit forced call))
    (forcedAt : SharedRootRead.BlockAt program forced (EnumerationDriverControl.incrementCode width descend)) :
    ∃ final, Execution program state final 10 state.liveWords ∧
      Ready parameters packet (depth + 1) (depth + 1) (insert ⟨depth, lower⟩ partialSet) final ∧
      final.pc = word width descend ∧ final.output = state.output := by
  have checksAt := block_left program entry (checks parameters width emit forced)
    (EnumerationDriverControl.selectCode width (packet.size + parameters.channels) true 1 call) present
  have headAt := block_left program entry (SharedTagCompare.code width emit parameters.channels 3).toList
    (if parameters.buses = 1 then (SharedTagCompare.code width forced parameters.bridge.target.val 3).toList else []) checksAt
  have targetAt := block_right program entry (SharedTagCompare.code width emit parameters.channels 3).toList
    (if parameters.buses = 1 then (SharedTagCompare.code width forced parameters.bridge.target.val 3).toList else []) checksAt
  simp only [one, ite_true, Array.length_toList, SharedTagCompare.code_size] at targetAt
  obtain ⟨tested, first, heap, stack, output, pc, running, frame⟩ :=
    SharedTagCompare.execution program state entry emit parameters.channels depth 3 (by decide) position ready.running
      (by omega) fits (by omega) ready.counter
      (by intro phase; simpa only [Array.getElem?_toList] using headAt phase.val (by simpa using phase.isLt))
  have nextPC : tested.pc = word width (entry + 3) := by
    simpa only [ite_eq_right (by omega : depth ≠ parameters.channels)] using pc
  obtain ⟨selected, second, selectedHeap, selectedStack, selectedOutput, selectedPC, selectedRunning, selectedFrame⟩ :=
    SharedTagCompare.execution program tested (entry + 3) forced parameters.bridge.target.val depth 3 (by decide)
      nextPC running (by omega) (by have := parameters.bridge.target.isLt; omega) (by omega)
      ((frame 3 (by decide)).trans ready.counter)
      (by intro phase; simpa only [Array.getElem?_toList] using targetAt phase.val (by simpa using phase.isLt))
  have selectedReady : Ready parameters packet depth depth partialSet selected :=
    ⟨selectedHeap.trans (heap.trans ready.heap), (selectedFrame 3 (by decide)).trans ((frame 3 (by decide)).trans ready.counter),
      selectedStack.trans (stack.trans ready.stack), selectedRunning⟩
  obtain ⟨final, third, finalReady, finalPC, finalOutput⟩ :=
    EnumerationDriverPrefix.forced_entry parameters program selected forced descend depth packet partialSet selectedReady bounded lower one target
      (by simpa only [ite_eq_left target.symm] using selectedPC) (by omega) forcedRoom forcedAt
  have live1 : tested.liveWords = state.liveWords := by simp only [State.liveWords, heap, stack, output]
  have live2 : selected.liveWords = state.liveWords := by
    simp only [State.liveWords, selectedHeap, selectedStack, selectedOutput, heap, stack, output]
  refine ⟨final, ?_, finalReady, finalPC, finalOutput.trans (selectedOutput.trans output)⟩
  simpa only [live1, live2, Nat.max_self, Nat.reduceAdd] using first.append (second.append third)


end Controller.Cost.EnumerationDriverDescent
