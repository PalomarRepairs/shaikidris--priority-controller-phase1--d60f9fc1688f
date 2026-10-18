module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestZeroHeaderBridge

@[expose] public section

/-! The actual save, full incidence scan, and restore sequence retains the original caller source. -/
namespace Controller.Cost.ForestZeroHeaderCaller
open Controller.Cost Controller.Cost.ForestZeroBackendFrame
open Controller.Cost.ForestZeroHeaderBridge Controller.Horn

theorem wrapped_index_execution (prefixSize : Nat) (program : Program width 8)
    (clauses : List (Controller.CNF.Clause (Fin n)))
    (entry recordHeader recordStart recordEnd base : Nat) (state : State width 8)
    (savePresent : SaveAt program entry recordHeader)
    (indexPresent : Controller.Horn.IndexScan.At (n := n) program (entry + 7) base recordStart)
    (restorePresent : RestoreAt program (entry + 39))
    (physical : IndexScan.PhysicalIndex clauses recordStart recordEnd base 0 state.heap)
    (queryHeader : Controller.Horn.SourceScan.CursorStored recordEnd recordHeader state.heap)
    (position : state.pc = word width entry) (running : state.halted = false)
    (zero : state.reg 2 = word width 0) (one : state.reg 5 = word width 1)
    (positiveBase : 0 < base) (prefixBound : prefixSize ≤ state.heap.size)
    (prefixBase : prefixSize ≤ base) (nonzeroPrefix : 0 < prefixSize)
    (capacity : entry + 42 < 2 ^ width)
    (room : state.heap.size + 2 * (IndexScan.occurrences clauses recordStart).length < 2 ^ width) :
    ∃ final, Execution program state final
      (16 * (IndexScan.occurrences clauses recordStart).length + 18 * clauses.length + 16)
      (state.liveWords + 2 * (IndexScan.occurrences clauses recordStart).length + 1) ∧
      IndexScan.PhysicalIndex clauses recordStart recordEnd base
        (IndexScan.occurrences clauses recordStart).length final.heap ∧
      PrefixFrame prefixSize state.heap final.heap ∧ final.stack = state.stack ∧
      final.output = state.output ∧
      final.heap.size = state.heap.size + 2 * (IndexScan.occurrences clauses recordStart).length ∧
      final.reg 7 = word width final.heap.size ∧ final.reg 2 = word width 0 ∧
      final.reg 5 = word width 1 ∧ final.pc = word width (entry + 42) ∧ final.halted = false := by
  have bound : 0 < state.heap.size := by omega
  obtain ⟨saved, first, savedHeap, savedStack, savedOutput, savedPosition, savedRunning, savedRegs⟩ :=
    save_execution program entry recordHeader recordEnd state savePresent position running bound queryHeader
      (by omega) (by omega)
  have savedSize : saved.heap.size = state.heap.size := by rw [savedHeap]; simp
  have savedPhysical : IndexScan.PhysicalIndex clauses recordStart recordEnd base 0 saved.heap := by
    rw [savedHeap]
    exact source_header_index clauses recordStart recordEnd base 0 (word width recordEnd) state.heap physical positiveBase bound
  have savedHeader : Controller.Horn.SourceScan.CursorStored recordEnd 0 saved.heap := by
    refine ⟨by omega, ?_⟩
    have cell : saved.heap[0]? = some (word width recordEnd) := by simp [savedHeap]
    rw [Array.getElem?_eq_getElem (show 0 < saved.heap.size by omega)] at cell
    exact Option.some.inj cell
  obtain ⟨indexed, second, result, indexedPrefix⟩ := ForestZeroIndexFrame.all_rows prefixSize program clauses
    recordStart recordEnd base (entry + 7) saved indexPresent savedPhysical savedHeader positiveBase savedPosition savedRunning
    ((savedRegs 2 (by decide) (by decide)).trans zero)
    ((savedRegs 5 (by decide) (by decide)).trans one)
    (by omega) (by rw [savedSize]; exact room) (by omega) prefixBase nonzeroPrefix
  have indexedBound : 0 < indexed.heap.size := by have := result.growth; omega
  have finalTrace := restore_execution program (entry + 39) indexed (state.heap[0]'bound) state.stack
    restorePresent (by simpa [Nat.add_assoc] using result.position) result.running
    (result.stack.trans savedStack) indexedBound (by omega)
  let final := restored indexed (state.heap[0]'bound) state.stack indexedBound
  have originalPrefix : PrefixFrame prefixSize state.heap final.heap := by
    apply restore_prefix prefixSize state.heap (word width recordEnd) (state.heap[0]'bound) bound
      indexed state.stack indexedBound rfl
    simpa only [savedHeap] using indexedPrefix
  have savedLive : saved.liveWords = state.liveWords + 1 := by
    unfold State.liveWords
    rw [savedSize, savedStack, savedOutput]
    simp
    omega
  have indexedLive : indexed.liveWords = saved.liveWords +
      2 * (IndexScan.occurrences clauses recordStart).length := by
    unfold State.liveWords
    rw [result.growth, result.stack, result.output]
    omega
  have finalSize : final.heap.size = indexed.heap.size := by simp [final, restored]
  have finalRegister (register : Fin 8) (not3 : register ≠ 3) (not4 : register ≠ 4) :
      final.reg register = indexed.reg register := by
    simp [final, restored, addressed, popped, State.advance, State.put, not3, not4]
  refine ⟨final, ?_, ?_, originalPrefix, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have trace := (first.append second).append finalTrace
    rw [savedLive, indexedLive, savedLive] at trace
    convert trace using 1 <;> omega
  · exact source_header_index clauses recordStart recordEnd base
      (IndexScan.occurrences clauses recordStart).length (state.heap[0]'bound) indexed.heap
      result.physical positiveBase indexedBound
  · exact result.output.trans savedOutput
  · rw [finalSize, result.growth, savedSize]
  · rw [finalRegister 7 (by decide) (by decide), finalSize]
    exact result.allocationHeld
  · exact (finalRegister 2 (by decide) (by decide)).trans
      (result.zero.trans ((savedRegs 2 (by decide) (by decide)).trans zero))
  · exact (finalRegister 5 (by decide) (by decide)).trans
      (result.one.trans ((savedRegs 5 (by decide) (by decide)).trans one))
  · have pc39 : indexed.pc.val = entry + 39 := by
      rw [result.position]
      change ((entry + 7 + 32) % 2 ^ width) = entry + 39
      rw [Nat.mod_eq_of_lt (by omega)]
    simp [final, restored, addressed, popped, State.advance, State.put, word, pc39,
      Nat.add_assoc, Nat.mod_eq_of_lt (show entry + 40 < 2 ^ width by omega),
      Nat.mod_eq_of_lt (show entry + 41 < 2 ^ width by omega)]
  · simpa [final, restored, addressed, popped, State.advance, State.put] using result.running

end Controller.Cost.ForestZeroHeaderCaller
