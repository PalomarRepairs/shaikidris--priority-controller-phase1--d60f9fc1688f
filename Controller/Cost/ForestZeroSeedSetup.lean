module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Horn.WorklistSeedRun
public import Controller.Cost.ForestZeroBackendFrame

@[expose] public section

/-! Source-relative physical seed initialization reads the query record-end
header and leaves the restored caller source header intact. -/
namespace Controller.Cost.ForestZeroSeedSetup
open Controller.Cost Controller.Horn.WorklistSeed Controller.Horn.WorklistBucketReady
variable {width n : Nat}

def code (width base recordHeader recordStart scan : Nat) : Program width 8 :=
  #[.constant 1 (word width recordStart), .constant 6 (word width (2 ^ width - 1)),
    .constant 3 (word width (Controller.Horn.WorklistFIFO.headSlot (n := n) base)),
    .constant 0 (word width recordHeader), .load 0 0, .store 3 0] ++
    setupCode (n := n) width base scan

theorem setup_execution (program : Program width 8)
    (base recordHeader recordStart recordEnd entry scan : Nat) (state : State width 8)
    (present : ∀ phase : Fin 10, program[entry + phase.val]? =
      (code (n := n) width base recordHeader recordStart scan)[phase.val]?)
    (position : state.pc = word width entry) (running : state.halted = false)
    (zero : state.reg 2 = word width 0)
    (sourceBound : recordHeader < state.heap.size) (sourceValue : state.heap[recordHeader]'sourceBound = word width recordEnd)
    (headBound : Controller.Horn.WorklistFIFO.headSlot (n := n) base < state.heap.size)
    (tailBound : tailSlot (n := n) base < state.heap.size)
    (room : state.heap.size < 2 ^ width) (capacity : entry + 10 < 2 ^ width) :
    ∃ final, Execution program state final 10 state.liveWords ∧
      final.reg 1 = word width recordStart ∧ final.reg 2 = state.reg 2 ∧
      final.reg 5 = state.reg 5 ∧ final.reg 6 = word width (2 ^ width - 1) ∧
      final.heap = (state.heap.set (Controller.Horn.WorklistFIFO.headSlot (n := n) base)
        (word width recordEnd) headBound).set (tailSlot (n := n) base)
        (word width (Controller.Horn.WorklistMark.queueStart (n := n) base)) (by simpa using tailBound) ∧
      final.heap.size = state.heap.size ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width scan ∧ final.halted = false := by
  let first := state.advance.put 1 (word width recordStart)
  let second := first.advance.put 6 (word width (2 ^ width - 1))
  let third := second.advance.put 3 (word width (Controller.Horn.WorklistFIFO.headSlot (n := n) base))
  let sourceAddress := third.advance.put 0 (word width recordHeader)
  let fourth := sourceAddress.advance.put 0 (word width recordEnd)
  let fifth : State width 8 := { fourth.advance with heap :=
    (state.heap.set (Controller.Horn.WorklistFIFO.headSlot (n := n) base) (word width recordEnd) headBound) }
  let sixth := fifth.advance.put 3 (word width (tailSlot (n := n) base))
  let seventh := sixth.advance.put 0 (word width (Controller.Horn.WorklistMark.queueStart (n := n) base))
  let eighth : State width 8 := { seventh.advance with heap :=
    (fifth.heap.set (tailSlot (n := n) base) (word width (Controller.Horn.WorklistMark.queueStart (n := n) base)) (by simpa [fifth] using tailBound)) }
  let final : State width 8 := { eighth.advance with pc := word width scan }
  have sourceFits : recordHeader < 2 ^ width := by omega
  have wordVal (value : Nat) (fits : value < 2 ^ width) : (word width value).val = value := Nat.mod_eq_of_lt fits
  have fetched (current : State width 8) (offset : Nat) (instruction : Instruction width 8)
      (pc : current.pc = word width (entry + offset)) (bound : entry + offset < 2 ^ width)
      (instructionAt : program[entry + offset]? = some instruction) :
      programStep program current = step instruction current := by
    unfold programStep
    rw [pc, wordVal (entry + offset) bound, instructionAt]
    rfl
  have nextPC (current : State width 8) (offset : Nat)
      (pc : current.pc = word width (entry + offset)) (bound : entry + offset < 2 ^ width) :
      current.advance.pc = word width (entry + offset + 1) := by
    simp only [State.advance, pc, wordVal (entry + offset) bound]
  have pc1 : first.pc = word width (entry + 1) := by simpa [first, State.put] using nextPC state 0 position (by omega)
  have pc2 : second.pc = word width (entry + 2) := by
    simpa [second, State.put, Nat.add_assoc] using nextPC first 1 pc1 (by omega)
  have pc3 : third.pc = word width (entry + 3) := by
    simpa [third, State.put, Nat.add_assoc] using nextPC second 2 pc2 (by omega)
  have pcSource : sourceAddress.pc = word width (entry + 4) := by
    simpa [sourceAddress, State.put, Nat.add_assoc] using nextPC third 3 pc3 (by omega)
  have pc5 : fourth.pc = word width (entry + 5) := by
    simpa [fourth, State.put, Nat.add_assoc] using nextPC sourceAddress 4 pcSource (by omega)
  have pc6 : fifth.pc = word width (entry + 6) := by
    simpa [fifth, State.put, Nat.add_assoc] using nextPC fourth 5 pc5 (by omega)
  have pc7 : sixth.pc = word width (entry + 7) := by
    simpa [sixth, State.put, Nat.add_assoc] using nextPC fifth 6 pc6 (by omega)
  have pc8 : seventh.pc = word width (entry + 8) := by
    simpa [seventh, State.put, Nat.add_assoc] using nextPC sixth 7 pc7 (by omega)
  have pc9 : eighth.pc = word width (entry + 9) := by
    simpa [eighth, State.put, Nat.add_assoc] using nextPC seventh 8 pc8 (by omega)
  have step1 : programStep program state = some first := by
    rw [fetched state 0 (.constant 1 (word width recordStart)) position (by omega)
      (by simpa [code, setupCode] using present ⟨0, by decide⟩)]
    simp [step, first, State.put, State.advance, running, zero, word, sourceBound, sourceValue, headBound, tailBound, Nat.mod_eq_of_lt sourceFits]
  have step2 : programStep program first = some second := by
    rw [fetched first 1 (.constant 6 (word width (2 ^ width - 1))) pc1 (by omega)
      (by simpa [code, setupCode] using present ⟨1, by decide⟩)]
    simp [step, first, second, State.put, State.advance, running, zero, word, sourceBound, sourceValue, headBound, tailBound, Nat.mod_eq_of_lt sourceFits]
  have step3 : programStep program second = some third := by
    rw [fetched second 2 (.constant 3 (word width (Controller.Horn.WorklistFIFO.headSlot (n := n) base))) pc2 (by omega)
      (by simpa [code, setupCode] using present ⟨2, by decide⟩)]
    simp [step, first, second, third, State.put, State.advance, running, zero, word, sourceBound, sourceValue, headBound, tailBound, Nat.mod_eq_of_lt sourceFits]
  have step4 : programStep program third = some sourceAddress := by
    rw [fetched third 3 (.constant 0 (word width recordHeader)) pc3 (by omega)
      (by simpa [code, setupCode] using present ⟨3, by decide⟩)]
    simp [step, first, second, third, sourceAddress, State.put, State.advance, running]
  have step5 : programStep program sourceAddress = some fourth := by
    rw [fetched sourceAddress 4 (.load 0 0) pcSource (by omega)
      (by simpa [code, setupCode] using present ⟨4, by decide⟩)]
    simp [step, first, second, third, sourceAddress, fourth, State.put, State.advance, running, zero, word, sourceBound, sourceValue, headBound, tailBound, Nat.mod_eq_of_lt sourceFits]
  have step6 : programStep program fourth = some fifth := by
    rw [fetched fourth 5 (.store 3 0) pc5 (by omega)
      (by simpa [code, setupCode] using present ⟨5, by decide⟩)]
    have addressFits : Controller.Horn.WorklistFIFO.headSlot (n := n) base < 2 ^ width := by omega
    simp [step, first, second, third, sourceAddress, fourth, fifth, State.put, State.advance, running, zero, word, sourceBound, sourceValue, headBound, tailBound, Nat.mod_eq_of_lt addressFits]
  have step7 : programStep program fifth = some sixth := by
    rw [fetched fifth 6 (.constant 3 (word width (tailSlot (n := n) base))) pc6 (by omega)
      (by simpa [code, setupCode] using present ⟨6, by decide⟩)]
    simp [step, first, second, third, sourceAddress, fourth, fifth, sixth, State.put, State.advance, running, zero, word, sourceBound, sourceValue, headBound, tailBound, Nat.mod_eq_of_lt sourceFits]
  have step8 : programStep program sixth = some seventh := by
    rw [fetched sixth 7 (.constant 0 (word width (Controller.Horn.WorklistMark.queueStart (n := n) base))) pc7 (by omega)
      (by simpa [code, setupCode] using present ⟨7, by decide⟩)]
    simp [step, first, second, third, sourceAddress, fourth, fifth, sixth, seventh, State.put, State.advance, running, zero, word, sourceBound, sourceValue, headBound, tailBound, Nat.mod_eq_of_lt sourceFits]
  have step9 : programStep program seventh = some eighth := by
    rw [fetched seventh 8 (.store 3 0) pc8 (by omega)
      (by simpa [code, setupCode] using present ⟨8, by decide⟩)]
    have addressFits : tailSlot (n := n) base < 2 ^ width := by omega
    simp [step, first, second, third, sourceAddress, fourth, fifth, sixth, seventh, eighth, State.put, State.advance, running, zero, word, sourceBound, sourceValue, headBound, tailBound, Nat.mod_eq_of_lt addressFits]
  have step10 : programStep program eighth = some final := by
    rw [fetched eighth 9 (.branchZero 2 (word width scan)) pc9 (by omega)
      (by simpa [code, setupCode] using present ⟨9, by decide⟩)]
    simp [step, first, second, third, sourceAddress, fourth, fifth, sixth, seventh, eighth, final, State.put, State.advance, running, zero, word, sourceBound, sourceValue, headBound, tailBound, Nat.mod_eq_of_lt sourceFits]
  refine ⟨final, ?_, ?_, ?_, ?_, ?_, rfl, ?_, rfl, rfl, rfl, running⟩
  · simpa [first, second, third, sourceAddress, fourth, fifth, sixth, seventh, eighth, final,
      State.put, State.advance, State.liveWords] using
      Execution.cons step1 (Execution.cons step2 (Execution.cons step3 (Execution.cons step4 (Execution.cons step5 (Execution.cons step6 (Execution.cons step7 (Execution.cons step8 (Execution.cons step9 (Execution.cons step10 (Execution.refl final))))))))))
  all_goals simp [first, second, third, sourceAddress, fourth, fifth, sixth, seventh, eighth, final, State.put, State.advance]



/-- Both actual setup stores lie in scratch, retaining every caller cell below
its allocation base. -/
theorem heap_frame (prefixSize base : Nat) (heap : Array (Word width))
    (recordEnd : Nat) (headBound : Controller.Horn.WorklistFIFO.headSlot (n := n) base < heap.size)
    (tailBound : tailSlot (n := n) base < heap.size)
    (prefixBound : prefixSize ≤ heap.size) (prefixBase : prefixSize ≤ base) :
    Controller.Cost.ForestZeroBackendFrame.PrefixFrame prefixSize heap
      ((heap.set (Controller.Horn.WorklistFIFO.headSlot (n := n) base)
        (word width recordEnd) headBound).set (tailSlot (n := n) base)
        (word width (Controller.Horn.WorklistMark.queueStart (n := n) base)) (by simpa using tailBound)) := by
  have first := Controller.Cost.ForestZeroBackendFrame.store (prefixSize := prefixSize) heap
    (Controller.Horn.WorklistFIFO.headSlot (n := n) base) (word width recordEnd) headBound
    (by unfold Controller.Horn.WorklistFIFO.headSlot; omega) prefixBound
  have second := Controller.Cost.ForestZeroBackendFrame.store (prefixSize := prefixSize)
    (heap.set (Controller.Horn.WorklistFIFO.headSlot (n := n) base) (word width recordEnd) headBound)
    (tailSlot (n := n) base) (word width (Controller.Horn.WorklistMark.queueStart (n := n) base)) (by simpa using tailBound)
    (by unfold tailSlot; omega) (by simpa using prefixBound)
  exact Controller.Cost.ForestZeroBackendFrame.trans first second

end Controller.Cost.ForestZeroSeedSetup
