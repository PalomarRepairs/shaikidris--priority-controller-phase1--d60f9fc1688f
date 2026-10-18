module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestZeroSeedSetup

@[expose] public section

/-! Source-relative seed initialization constructs the actual initial scan
invariant from original stored rows, completed physical links and empty scratch. -/
namespace Controller.Cost.ForestZeroSeedReady
open Controller.Cost Controller.Horn.WorklistSeed Controller.Horn.WorklistMark
open Controller.Horn.WorklistBucketReady Controller.Horn.WorklistSeedRun
variable {width n : Nat}

theorem initial_scan_execution (prefixSize : Nat) (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordHeader recordStart recordEnd base entry scan : Nat) (state : State width 8) (program : Program width 8)
    (physical : Controller.Horn.IndexScan.PhysicalIndex clauses recordStart recordEnd base
      (Controller.Horn.IndexScan.occurrences clauses recordStart).length state.heap)
    (header : Controller.Horn.SourceScan.CursorStored recordEnd recordHeader state.heap)
    (fifo : Stored ([] : List (Fin n)) base state.heap)
    (separated : base + 5 * n + 4 ≤ recordStart)
    (present : ∀ phase : Fin 10, program[entry + phase.val]? =
      (Controller.Cost.ForestZeroSeedSetup.code (n := n) width base recordHeader recordStart scan)[phase.val]?)
    (position : state.pc = word width entry) (running : state.halted = false)
    (zero : state.reg 2 = word width 0) (one : state.reg 5 = word width 1)
    (room : state.heap.size < 2 ^ width) (capacity : entry + 10 < 2 ^ width)
    (prefixBound : prefixSize ≤ state.heap.size) (prefixBase : prefixSize ≤ base) :
    ∃ final, Execution program state final 10 state.liveWords ∧
      ScanInvariant clauses recordStart recordEnd base scan 0 [] (fun _ => false) final ∧
      final.heap.size = state.heap.size ∧ final.stack = state.stack ∧ final.output = state.output ∧ Controller.Cost.ForestZeroBackendFrame.PrefixFrame prefixSize state.heap final.heap := by
  have headBound : Controller.Horn.WorklistFIFO.headSlot (n := n) base < state.heap.size := by
    have fits := fifo.fits
    unfold Controller.Horn.WorklistFIFO.headSlot
    omega
  have tailBound : tailSlot (n := n) base < state.heap.size := by have fits := fifo.fits; unfold tailSlot; omega
  have spine := Controller.Horn.WorklistPropagation.spine_of_index clauses recordStart recordEnd base state.heap physical
  have rows : ∀ row : Fin clauses.length,
      Controller.Horn.WorklistStorage.MutableStored (Controller.Horn.Worklist.compileClause clauses[row.val])
        (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart row.val)
        (Controller.Horn.Worklist.compileClause clauses[row.val]).positives.length false state.heap := by
    intro row
    exact Controller.Horn.WorklistStorage.initial (physical.records row)
  obtain ⟨final, trace, cursor, finalZero, finalOne, decrement, heap, size, stack, output, pc, live⟩ :=
    Controller.Cost.ForestZeroSeedSetup.setup_execution program base recordHeader recordStart recordEnd entry scan state present position running zero
      header.bound header.value headBound tailBound room capacity
  let firstHeap := state.heap.set (Controller.Horn.WorklistFIFO.headSlot (n := n) base) (word width recordEnd) headBound
  have firstFrame := scratch_header_frame clauses recordStart recordEnd base
    (Controller.Horn.WorklistFIFO.headSlot (n := n) base) state.heap []
    (fun row => (Controller.Horn.Worklist.compileClause clauses[row.val]).positives.length) (fun _ => false)
    spine fifo rows headBound (by unfold Controller.Horn.WorklistFIFO.headSlot; omega)
    (by unfold Controller.Horn.WorklistFIFO.headSlot; omega)
    (by unfold Controller.Horn.WorklistFIFO.headSlot queueStart; omega) (word width recordEnd)
  have secondFrame := scratch_header_frame clauses recordStart recordEnd base (tailSlot (n := n) base)
    firstHeap [] (fun row => (Controller.Horn.Worklist.compileClause clauses[row.val]).positives.length) (fun _ => false)
    firstFrame.1 firstFrame.2.1 firstFrame.2.2 (by simpa [firstHeap] using tailBound)
    (by unfold tailSlot; omega) (by unfold tailSlot; omega) (by unfold tailSlot queueStart; omega)
    (word width (queueStart (n := n) base))
  have headerValue : final.heap[Controller.Horn.WorklistFIFO.headSlot (n := n) base]? = some (word width recordEnd) := by
    rw [heap]
    rw [Array.getElem?_set_ne (by simpa using tailBound)
      (by unfold tailSlot Controller.Horn.WorklistFIFO.headSlot; omega)]
    exact Array.getElem?_set_self headBound
  have tailValue : final.heap[tailSlot (n := n) base]? = some (word width (queueStart (n := n) base)) := by
    rw [heap]
    exact Array.getElem?_set_self (by simpa using tailBound)
  have retained : Controller.Cost.ForestZeroBackendFrame.PrefixFrame prefixSize state.heap final.heap := by
    rw [heap]
    exact Controller.Cost.ForestZeroSeedSetup.heap_frame prefixSize base state.heap recordEnd headBound tailBound prefixBound prefixBase
  refine ⟨final, trace, ?_, size, stack, output, retained⟩
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, headerValue, ?_, ?_,
    finalZero.trans zero, finalOne.trans one, decrement, pc, live, by omega⟩
  · simpa only [heap, firstHeap] using secondFrame.1
  · simpa only [heap, firstHeap] using secondFrame.2.1
  · intro row; simpa only [heap, firstHeap] using secondFrame.2.2 row
  · intro row bound; rfl
  · intro row before; omega
  · intro assignment models label member; exact False.elim (List.not_mem_nil member)
  · intro row marked; exact False.elim (Bool.false_ne_true marked)
  · intro row marked; exact False.elim (Bool.false_ne_true marked)
  · simpa only [List.length_nil, Nat.add_zero] using tailValue
  · simpa [Controller.Horn.NormalizeLoop.recordOffset] using cursor


end Controller.Cost.ForestZeroSeedReady
