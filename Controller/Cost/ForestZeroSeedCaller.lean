module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestZeroSeedReady
public import Controller.Cost.ForestZeroSeedFrame
public import Controller.Horn.WorklistAccept

@[expose] public section

/-! The actual source-relative initialization, full original-row seed scan and
FIFO entry retain the caller's immutable source prefix. -/
namespace Controller.Cost.ForestZeroSeedCaller
open Controller.Cost Controller.Cost.ForestZeroBackendFrame
open Controller.Horn.WorklistMark Controller.Horn.WorklistFIFO
open Controller.Horn.WorklistPropagation Controller.Horn.WorklistOutcome
open Controller.Horn.WorklistPropagationStep Controller.Horn.WorklistStorage
open Controller.Horn.WorklistAccept
variable {width n : Nat}

theorem seed_to_fifo (prefixSize : Nat) (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base entry fetch : Nat) (program : Program width 8)
    (queue : List (Fin n)) (fired : Fin clauses.length → Bool) (state : State width 8)
    (seed : Controller.Horn.WorklistSeedRun.ScanInvariant clauses recordStart recordEnd base entry
      clauses.length queue fired state)
    (separated : base + 5 * n + 4 ≤ recordStart)
    (present : ∀ phase : Fin 4, program[entry + phase.val]? =
      (headSetupCode (n := n) width base fetch)[phase.val]?)
    (capacity : entry + 4 < 2 ^ width) (prefixBound : prefixSize ≤ state.heap.size)
    (prefixBelow : prefixSize ≤ base) :
    ∃ final, Execution program state final 4 state.liveWords ∧
      Controller.Horn.WorklistFIFORun.Ready clauses recordStart recordEnd base fetch queue 0 fired final ∧
      ProcessedComplete clauses recordStart queue 0 none [] fired ∧
      FiredMeaning clauses queue fired ∧ Controller.Horn.WorklistSeed.QueueForced clauses queue ∧
      final.heap.size = state.heap.size ∧ final.stack = state.stack ∧ final.output = state.output ∧ PrefixFrame prefixSize state.heap final.heap := by
  have headBound : headSlot (n := n) base < state.heap.size := by
    have := seed.fifo.fits
    unfold headSlot
    omega
  obtain ⟨final, trace, heap, pc, running, row, zero, one, decrement, size, stack, output⟩ :=
    head_setup_execution program base entry fetch state present seed.position seed.running seed.zero
      capacity headBound seed.room
  have originalRows : ∀ index : Fin clauses.length,
      Controller.Horn.WorklistStorage.MutableStored (Controller.Horn.Worklist.compileClause clauses[index.val])
        (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val)
        (remaining (Controller.Horn.Worklist.compileClause clauses[index.val]) (queue.take 0)) (fired index) state.heap := by
    intro index
    simpa [remaining] using seed.rows index
  obtain ⟨spine, fifo, rows⟩ := head_store_frame clauses recordStart recordEnd base queue
    (fun index => remaining (Controller.Horn.Worklist.compileClause clauses[index.val]) (queue.take 0))
    fired state.heap (word width (queueStart (n := n) base)) seed.spine seed.fifo originalRows separated
  have firedZero : FiredZero clauses recordStart queue 0 none [] fired := by
    intro index marked
    simpa [remaining, processedForRow] using seed.firedEmpty index marked
  have headValue : final.heap[headSlot (n := n) base]? = some (word width (queueStart (n := n) base + 0)) := by
    rw [heap]
    simp
  have tailValue : final.heap[Controller.Horn.WorklistBucketReady.tailSlot (n := n) base]? =
      some (word width (queueStart (n := n) base + queue.length)) := by
    rw [heap]
    exact (Array.getElem?_set_ne headBound (by unfold headSlot Controller.Horn.WorklistBucketReady.tailSlot; omega)).trans seed.tail
  have retained : PrefixFrame prefixSize state.heap final.heap := by
    rw [heap]
    exact Controller.Cost.ForestZeroBackendFrame.store state.heap (headSlot (n := n) base)
      (word width (queueStart (n := n) base)) headBound
      (by unfold headSlot; omega) prefixBound
  refine ⟨final, trace, ?_, ?_, seed.firedHead, seed.forced, size, stack, output, retained⟩
  · refine ⟨?_, ?_, Nat.zero_le _, ?_, firedZero, headValue, tailValue,
      zero.trans seed.zero, one.trans seed.one, decrement.trans seed.decrement,
      pc, running, ?_⟩
    · simpa only [heap] using spine
    · simpa only [heap] using fifo
    · intro index; simpa only [heap] using rows index
    · simpa only [size] using seed.room
  · intro index enabled countZero
    apply seed.complete index index.isLt enabled
    simpa [processedForRow, remaining] using countZero

theorem initialized_scan_execution (prefixSize : Nat) (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordHeader recordStart recordEnd base entry scan done conflict : Nat)
    (state : State width 8) (program : Program width 8)
    (physical : Controller.Horn.IndexScan.PhysicalIndex clauses recordStart recordEnd base
      (Controller.Horn.IndexScan.occurrences clauses recordStart).length state.heap)
    (header : Controller.Horn.SourceScan.CursorStored recordEnd recordHeader state.heap)
    (fifo : Stored ([] : List (Fin n)) base state.heap)
    (separated : base + 5 * n + 4 ≤ recordStart)
    (setupAt : ∀ phase : Fin 10, program[entry + phase.val]? =
      (Controller.Cost.ForestZeroSeedSetup.code (n := n) width base recordHeader recordStart scan)[phase.val]?)
    (scanAt : Controller.Horn.WorklistSeed.At (n := n) program base scan done conflict)
    (position : state.pc = word width entry) (running : state.halted = false)
    (zero : state.reg 2 = word width 0) (one : state.reg 5 = word width 1)
    (room : state.heap.size < 2 ^ width) (setupCapacity : entry + 10 < 2 ^ width)
    (scanCapacity : scan + 47 < 2 ^ width)
    (prefixBound : prefixSize ≤ state.heap.size) (prefixBelow : prefixSize ≤ base) :
    ∃ queue fired final ticks,
      queue.length ≤ n ∧ ticks ≤ 36 * clauses.length + 3 * queue.length + 14 ∧
      Execution program state final ticks state.liveWords ∧
      final.heap.size = state.heap.size ∧ final.stack = state.stack ∧ final.output = state.output ∧
      PrefixFrame prefixSize state.heap final.heap ∧
      ((final.pc = word width conflict ∧ final.halted = false ∧
        ¬ ∃ assignment : Fin n → Bool, ∀ row : Fin clauses.length,
          (Controller.Horn.Worklist.compileClause clauses[row.val]).Holds assignment) ∨
        Controller.Horn.WorklistSeedRun.ScanInvariant clauses recordStart recordEnd base done
          clauses.length queue fired final) := by
  obtain ⟨middle, first, initial, size, stack, output, firstFrame⟩ :=
    Controller.Cost.ForestZeroSeedReady.initial_scan_execution prefixSize clauses
      recordHeader recordStart recordEnd base entry scan state program physical header fifo separated
      setupAt position running zero one room setupCapacity prefixBound prefixBelow
  obtain ⟨queue, fired, final, ticks, _, queueBound, cost, last, finalSize, finalStack,
      finalOutput, lastFrame, result⟩ :=
    Controller.Cost.ForestZeroSeedFrame.scan_execution prefixSize clauses recordStart recordEnd base
      scan done conflict program scanAt separated scanCapacity clauses.length prefixBelow
      0 [] (fun _ => false) middle (by omega) initial (by simpa only [size] using prefixBound)
  have middleLive : middle.liveWords = state.liveWords := by
    unfold State.liveWords
    rw [size, stack, output]
  refine ⟨queue, fired, final, 10 + ticks, queueBound, ?_, ?_, finalSize.trans size,
    finalStack.trans stack, finalOutput.trans output,
    Controller.Cost.ForestZeroBackendFrame.trans firstFrame lastFrame, result⟩
  · simp only [List.length_nil, Nat.sub_zero] at cost
    omega
  · simpa only [middleLive, Nat.max_self] using first.append last

theorem initialized_fifo_execution (prefixSize : Nat) (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordHeader recordStart recordEnd base entry scan done conflict : Nat)
    (state : State width 8) (program : Program width 8)
    (physical : Controller.Horn.IndexScan.PhysicalIndex clauses recordStart recordEnd base
      (Controller.Horn.IndexScan.occurrences clauses recordStart).length state.heap)
    (header : Controller.Horn.SourceScan.CursorStored recordEnd recordHeader state.heap)
    (fifo : Stored ([] : List (Fin n)) base state.heap)
    (separated : base + 5 * n + 4 ≤ recordStart)
    (setupAt : ∀ phase : Fin 10, program[entry + phase.val]? =
      (Controller.Cost.ForestZeroSeedSetup.code (n := n) width base recordHeader recordStart scan)[phase.val]?)
    (scanAt : Controller.Horn.WorklistSeed.At (n := n) program base scan done conflict)
    (position : state.pc = word width entry) (running : state.halted = false)
    (zero : state.reg 2 = word width 0) (one : state.reg 5 = word width 1)
    (room : state.heap.size < 2 ^ width) (setupCapacity : entry + 10 < 2 ^ width)
    (scanCapacity : scan + 47 < 2 ^ width)
    (prefixBound : prefixSize ≤ state.heap.size) (prefixBelow : prefixSize ≤ base)
    (fetch : Nat)
    (headAt : ∀ phase : Fin 4, program[done + phase.val]? =
      (headSetupCode (n := n) width base fetch)[phase.val]?)
    (headCapacity : done + 4 < 2 ^ width) :
    ∃ queue fired final ticks,
      queue.length ≤ n ∧ ticks ≤ 36 * clauses.length + 3 * queue.length + 18 ∧
      Execution program state final ticks state.liveWords ∧
      final.heap.size = state.heap.size ∧ final.stack = state.stack ∧ final.output = state.output ∧
      PrefixFrame prefixSize state.heap final.heap ∧
      ((final.pc = word width conflict ∧ final.halted = false ∧
        ¬ ∃ assignment : Fin n → Bool, ∀ row : Fin clauses.length,
          (Controller.Horn.Worklist.compileClause clauses[row.val]).Holds assignment) ∨
        (Controller.Horn.WorklistFIFORun.Ready clauses recordStart recordEnd base fetch queue 0 fired final ∧
          ProcessedComplete clauses recordStart queue 0 none [] fired ∧ FiredMeaning clauses queue fired ∧
          Controller.Horn.WorklistSeed.QueueForced clauses queue)) := by
  obtain ⟨queue, fired, middle, ticks, queueBound, cost, first, size, stack, output, firstFrame, outcome⟩ :=
    initialized_scan_execution prefixSize clauses recordHeader recordStart recordEnd base entry scan done conflict
      state program physical header fifo separated setupAt scanAt position running zero one room
      setupCapacity scanCapacity prefixBound prefixBelow
  rcases outcome with failed | ready
  · exact ⟨queue, fired, middle, ticks, queueBound, by omega, first, size, stack, output, firstFrame, Or.inl failed⟩
  · obtain ⟨final, last, finalReady, complete, meaning, forced, finalSize, finalStack, finalOutput, lastFrame⟩ :=
      seed_to_fifo prefixSize clauses recordStart recordEnd base done fetch program queue fired middle ready
        separated headAt headCapacity (by simpa only [size] using prefixBound) prefixBelow
    have middleLive : middle.liveWords = state.liveWords := by
      unfold State.liveWords
      rw [size, stack, output]
    refine ⟨queue, fired, final, ticks + 4, queueBound, by omega, ?_, finalSize.trans size,
      finalStack.trans stack, finalOutput.trans output,
      Controller.Cost.ForestZeroBackendFrame.trans firstFrame lastFrame,
      Or.inr ⟨finalReady, complete, meaning, forced⟩⟩
    simpa only [middleLive, Nat.max_self] using first.append last

end Controller.Cost.ForestZeroSeedCaller
