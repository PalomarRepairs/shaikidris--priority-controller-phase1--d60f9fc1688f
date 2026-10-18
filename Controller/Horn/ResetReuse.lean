module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Horn.RowScan

@[expose] public section

/-!
# Reset endpoint for scratch reuse

The fetched touched-pointer traversal preserves the concrete common register
convention and the caller's stack and output. These endpoint facts permit the
next source row to reuse the mark buffers after its normalized rule is copied.
-/
namespace Controller.Horn.ResetReuse

open Controller.Cost Controller.Horn.ResetPointer Controller.Horn.ResetTouched
open Controller.Horn.Worklist.IndexedNormalize

/-- The complete physical reset exposes its actual continuation registers.
Its pointer loop is the checked configured machine framed by the caller's
stack and output, rather than an arbitrary state transport assumption. -/
theorem reset_execution (destination : Program width 8) (entry header base pointer limit : Nat)
    (setupAt : SetupAt destination entry header base)
    (loopAt : ResetPointer.CodeAt destination (entry + 3) limit)
    (state : State width 8) (marks : Marks n) (labels : List (Fin n))
    (marked : MarkStorage.Stored marks base state.heap)
    (stored : LabelsStored labels pointer state.heap) (ends : pointer + labels.length = limit)
    (separate : base + 2 * n ≤ pointer)
    (headerBound : header < state.heap.size)
    (headerValue : state.heap[header]'headerBound = word width pointer)
    (position : state.pc = word width entry) (zero : state.reg 2 = word width 0)
    (one : state.reg 5 = MarkStorage.encode width true)
    (decrement : state.reg 6 = word width (2 ^ width - 1)) (running : state.halted = false)
    (capacity : entry + 14 < 2 ^ width) (heapFits : state.heap.size < 2 ^ width) :
    ∃ final : State width 8,
      Execution destination state final (11 * labels.length + 6) state.liveWords ∧
      MarkStorage.Stored (Marks.clear labels marks) base final.heap ∧
      final.heap.size = state.heap.size ∧ Frame n base state.heap final.heap ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry + 14) ∧
      final.reg 2 = word width 0 ∧ final.reg 5 = MarkStorage.encode width true ∧
      final.reg 6 = word width (2 ^ width - 1) ∧ final.halted = false ∧
      final.liveWords = state.liveWords := by
  have setup := setup_execution destination entry header base pointer setupAt state position running
    (by omega) headerBound (headerBound.trans heapFits) headerValue
  obtain ⟨finalHeap, finalLabel, finalAddress, loop, cleared, size, frame⟩ :=
    ResetPointer.execution destination (entry + 3) limit loopAt labels state.heap marks base pointer
      (state.reg 1).val (state.reg 3).val (state.reg 4).val marked stored ends separate
      (by omega) heapFits
  have framed := loop.frame state.stack state.output
  rw [← ResetEntry.setup_configuration state header pointer base entry position (by omega) zero one decrement running] at framed
  have trace := setup.append framed
  let final := (configuration finalHeap limit 0 base finalLabel finalAddress (entry + 3 + 11)).frame state.stack state.output
  refine ⟨final, ?_, cleared, size, frame, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have peak : 9 + state.heap.size + (state.stack.length + state.output.length) = state.liveWords := by
      simp only [State.liveWords]
      omega
    have ticks : 3 + (11 * labels.length + 3) = 11 * labels.length + 6 := by omega
    simpa only [peak, Nat.max_self, ticks] using trace
  · simp [final, configuration, State.frame, show entry + 3 + 11 = entry + 14 by omega]
  · rfl
  · rfl
  · rfl
  · rfl
  · simp only [final, configuration, State.frame, State.liveWords, size, List.length_append, List.length_nil]
    omega

/-- After the rule has been copied, eleven fetched instructions restore the
three empty buffer cursors and clear the tautology header. -/
def headerCode (width n base : Nat) : Program width 8 :=
  #[.constant 0 (word width (base + 2 * n)),
    .constant 4 (word width (base + 3 * n + 4)), .store 0 4,
    .constant 0 (word width (base + 2 * n + 1)),
    .constant 4 (word width (base + 4 * n + 4)), .store 0 4,
    .constant 0 (word width (base + 2 * n + 2)),
    .constant 4 (word width (base + 5 * n + 4)), .store 0 4,
    .constant 0 (word width (base + 2 * n + 3)), .store 0 2]

@[simp] theorem headerCode_size (width n base : Nat) :
    (headerCode width n base).size = 11 := rfl

def HeaderAt (destination : Program width 8) (entry n base : Nat) : Prop :=
  ∀ phase : Fin 11, destination[entry + phase.val]? =
    some ((headerCode width n base)[phase.val])

end Controller.Horn.ResetReuse
