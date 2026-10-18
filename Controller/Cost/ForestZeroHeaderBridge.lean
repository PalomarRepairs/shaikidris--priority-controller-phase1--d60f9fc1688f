module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestZeroIndexFrame

@[expose] public section

/-! Fetched restoration of the caller's saved source header after indexing. -/
namespace Controller.Cost.ForestZeroHeaderBridge
open Controller.Cost Controller.Cost.ForestZeroBackendFrame

def restoreCode (width : Nat) : Program width 8 :=
  #[.pop 4, .constant 3 (word width 0), .store 3 4]

def RestoreAt (program : Program width 8) (entry : Nat) : Prop :=
  ∀ phase : Fin 3, program[entry + phase.val]? = some (restoreCode width)[phase.val]

def popped (state : State width 8) (saved : Word width) (rest : List (Word width)) : State width 8 :=
  { state.advance.put 4 saved with stack := rest }

def addressed (state : State width 8) (saved : Word width) (rest : List (Word width)) : State width 8 :=
  (popped state saved rest).advance.put 3 (word width 0)

def restored (state : State width 8) (saved : Word width) (rest : List (Word width))
    (bound : 0 < state.heap.size) : State width 8 :=
  { (addressed state saved rest).advance with heap := state.heap.set 0 saved bound }

theorem restore_execution (program : Program width 8) (entry : Nat)
    (state : State width 8) (saved : Word width) (rest : List (Word width))
    (present : RestoreAt program entry) (position : state.pc = word width entry)
    (running : state.halted = false) (stack : state.stack = saved :: rest)
    (bound : 0 < state.heap.size) (capacity : entry + 3 < 2 ^ width) :
    Execution program state (restored state saved rest bound) 3 state.liveWords := by
  have pc0 : state.pc.val = entry := by rw [position]; exact Nat.mod_eq_of_lt (by omega)
  have pc1 : (popped state saved rest).pc.val = entry + 1 := by
    simp only [popped, State.advance, State.put, pc0]
    exact Nat.mod_eq_of_lt (by omega)
  have pc2 : (addressed state saved rest).pc.val = entry + 2 := by
    simp only [addressed, State.advance, State.put, pc1]
    exact Nat.mod_eq_of_lt (by omega)
  have f0 : program[entry]? = some (.pop 4) := by simpa [restoreCode] using present ⟨0, by decide⟩
  have f1 : program[entry + 1]? = some (.constant 3 (word width 0)) := by simpa [restoreCode] using present ⟨1, by decide⟩
  have f2 : program[entry + 2]? = some (.store 3 4) := by simpa [restoreCode] using present ⟨2, by decide⟩
  have first : programStep program state = some (popped state saved rest) := by
    simp only [programStep, pc0, f0, Option.bind_some]
    simp [step, running, stack, popped]
  have second : programStep program (popped state saved rest) = some (addressed state saved rest) := by
    simp only [programStep, pc1, f1, Option.bind_some]
    simp [step, popped, State.advance, State.put, running, addressed]
  have third : programStep program (addressed state saved rest) = some (restored state saved rest bound) := by
    simp only [programStep, pc2, f2, Option.bind_some]
    simp [step, addressed, popped,
      State.put, State.advance, running, word, bound, restored]
  have trace := Execution.cons first (Execution.cons second (Execution.cons third
    (Execution.refl (restored state saved rest bound))))
  convert trace using 1 <;>
    simp [State.liveWords, restored, addressed, popped, State.advance, State.put, stack] <;> omega

@[simp] theorem restored_header (state : State width 8) (saved : Word width)
    (rest : List (Word width)) (bound : 0 < state.heap.size) :
    (restored state saved rest bound).heap[0]? = some saved := by
  simp [restored]

@[simp] theorem restored_stack (state : State width 8) (saved : Word width)
    (rest : List (Word width)) (bound : 0 < state.heap.size) :
    (restored state saved rest bound).stack = rest := rfl


/-- Restoring the actual saved word closes the temporary header borrow and
recovers the complete original caller prefix, including cell zero. -/
theorem restore_prefix (prefixSize : Nat) (original : Array (Word width))
    (borrowed saved : Word width) (originalBound : 0 < original.size)
    (state : State width 8) (rest : List (Word width)) (bound : 0 < state.heap.size)
    (savedCell : original[0]'originalBound = saved)
    (frame : PrefixFrame prefixSize (original.set 0 borrowed originalBound) state.heap) :
    PrefixFrame prefixSize original (restored state saved rest bound).heap := by
  refine ⟨by simpa using frame.1, by simpa [restored] using frame.2.1, ?_⟩
  intro index below
  by_cases zero : index = 0
  · subst index
    simp [restored, Array.getElem?_eq_getElem originalBound, savedCell]
  · have finalCell := Array.getElem?_set_ne (v := saved) bound (Ne.symm zero)
    have originalCell := Array.getElem?_set_ne (v := borrowed) originalBound (Ne.symm zero)
    exact finalCell.trans ((frame.2.2 index below).trans originalCell)


def saveCode (width recordHeader : Nat) : Program width 8 :=
  #[.constant 3 (word width 0), .load 4 3, .push 4,
    .constant 3 (word width recordHeader), .load 4 3,
    .constant 3 (word width 0), .store 3 4]

def SaveAt (program : Program width 8) (entry recordHeader : Nat) : Prop :=
  ∀ phase : Fin 7, program[entry + phase.val]? = some (saveCode width recordHeader)[phase.val]

/-- The saved header is fetched from the caller's actual cell zero. The
replacement is fetched from the query's actual record-end header. -/
theorem save_execution (program : Program width 8) (entry recordHeader recordEnd : Nat)
    (state : State width 8) (present : SaveAt program entry recordHeader)
    (position : state.pc = word width entry) (running : state.halted = false)
    (bound : 0 < state.heap.size)
    (header : Controller.Horn.SourceScan.CursorStored recordEnd recordHeader state.heap)
    (capacity : entry + 7 < 2 ^ width) (room : state.heap.size < 2 ^ width) :
    ∃ final, Execution program state final 7 (state.liveWords + 1) ∧
      final.heap = state.heap.set 0 (word width recordEnd) bound ∧
      final.stack = state.heap[0]'bound :: state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry + 7) ∧ final.halted = false ∧
      (∀ register : Fin 8, register ≠ 3 → register ≠ 4 → final.reg register = state.reg register) := by
  have headerFits : recordHeader < 2 ^ width := by have := header.bound; omega
  have addressValue : (word width recordHeader).val = recordHeader := Nat.mod_eq_of_lt headerFits
  have zeroValue : (word width 0).val = 0 := by simp [word]
  let q1 := state.advance.put 3 (word width 0)
  let q2 := q1.advance.put 4 (state.heap[0]'bound)
  let q3 : State width 8 := { q2.advance with stack := state.heap[0]'bound :: state.stack }
  let q4 := q3.advance.put 3 (word width recordHeader)
  let q5 := q4.advance.put 4 (word width recordEnd)
  let q6 := q5.advance.put 3 (word width 0)
  let q7 : State width 8 := { q6.advance with heap := state.heap.set 0 (word width recordEnd) bound }
  have pc0 : state.pc.val = entry := by rw [position]; exact Nat.mod_eq_of_lt (by omega)
  have pc1 : q1.pc.val = entry + 1 := by
    simp only [q1, State.advance, State.put, pc0]
    exact Nat.mod_eq_of_lt (by omega)
  have pc2 : q2.pc.val = entry + 2 := by
    simp only [q2, State.advance, State.put, pc1]
    exact Nat.mod_eq_of_lt (by omega)
  have pc3 : q3.pc.val = entry + 3 := by
    simp only [q3, State.advance, State.put, pc2]
    exact Nat.mod_eq_of_lt (by omega)
  have pc4 : q4.pc.val = entry + 4 := by
    simp only [q4, State.advance, State.put, pc3]
    exact Nat.mod_eq_of_lt (by omega)
  have pc5 : q5.pc.val = entry + 5 := by
    simp only [q5, State.advance, State.put, pc4]
    exact Nat.mod_eq_of_lt (by omega)
  have pc6 : q6.pc.val = entry + 6 := by
    simp only [q6, State.advance, State.put, pc5]
    exact Nat.mod_eq_of_lt (by omega)
  have f0 : program[entry + 0]? = some (.constant 3 (word width 0)) := by simpa [saveCode] using present ⟨0, by decide⟩
  have f1 : program[entry + 1]? = some (.load 4 3) := by simpa [saveCode] using present ⟨1, by decide⟩
  have f2 : program[entry + 2]? = some (.push 4) := by simpa [saveCode] using present ⟨2, by decide⟩
  have f3 : program[entry + 3]? = some (.constant 3 (word width recordHeader)) := by simpa [saveCode] using present ⟨3, by decide⟩
  have f4 : program[entry + 4]? = some (.load 4 3) := by simpa [saveCode] using present ⟨4, by decide⟩
  have f5 : program[entry + 5]? = some (.constant 3 (word width 0)) := by simpa [saveCode] using present ⟨5, by decide⟩
  have f6 : program[entry + 6]? = some (.store 3 4) := by simpa [saveCode] using present ⟨6, by decide⟩
  simp only [Nat.add_zero] at f0
  have h1 : programStep program state = some q1 := by
    simp only [programStep, pc0, f0, Option.bind_some]
    simp [step, q1, State.advance, State.put, running,
      zeroValue, addressValue, bound, header.bound, header.value]
  have h2 : programStep program q1 = some q2 := by
    simp only [programStep, pc1, f1, Option.bind_some]
    simp [step, q2, q1, State.advance, State.put, running,
      zeroValue, addressValue, bound, header.bound, header.value]
  have h3 : programStep program q2 = some q3 := by
    simp only [programStep, pc2, f2, Option.bind_some]
    simp [step, q3, q2, q1, State.advance, State.put, running,
      zeroValue, addressValue, bound, header.bound, header.value]
  have h4 : programStep program q3 = some q4 := by
    simp only [programStep, pc3, f3, Option.bind_some]
    simp [step, q4, q3, q2, q1, State.advance, State.put, running,
      zeroValue, addressValue, bound, header.bound, header.value]
  have h5 : programStep program q4 = some q5 := by
    simp only [programStep, pc4, f4, Option.bind_some]
    simp [step, q5, q4, q3, q2, q1, State.advance, State.put, running,
      zeroValue, addressValue, bound, header.bound, header.value]
  have h6 : programStep program q5 = some q6 := by
    simp only [programStep, pc5, f5, Option.bind_some]
    simp [step, q6, q5, q4, q3, q2, q1, State.advance, State.put, running,
      zeroValue, addressValue, bound, header.bound, header.value]
  have h7 : programStep program q6 = some q7 := by
    simp only [programStep, pc6, f6, Option.bind_some]
    simp [step, q7, q6, q5, q4, q3, q2, q1, State.advance, State.put, running,
      zeroValue, addressValue, bound, header.bound, header.value]
  have trace := Execution.cons h1 (Execution.cons h2 (Execution.cons h3
    (Execution.cons h4 (Execution.cons h5 (Execution.cons h6 (Execution.cons h7 (Execution.refl q7)))))))
  refine ⟨q7, ?_, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · convert trace using 1 <;>
      simp [State.liveWords, q7, q6, q5, q4, q3, q2, q1, State.advance, State.put] <;> omega
  · change word width (q6.pc.val + 1) = word width (entry + 7)
    rw [pc6]
  · simpa [q7, q6, q5, q4, q3, q2, q1, State.advance, State.put] using running
  · intro register not3 not4
    simp [q7, q6, q5, q4, q3, q2, q1, State.advance, State.put, not3, not4]

open Controller.Horn Controller.Horn.WorklistStorage Controller.Horn.IndexScanRefinement Controller.Horn.IndexScanLoop

theorem source_header_index (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base processed : Nat) (value : Word width) (heap : Array (Word width))
    (index : IndexScan.PhysicalIndex clauses recordStart recordEnd base processed heap)
    (positiveBase : 0 < base) (bound : 0 < heap.size) :
    IndexScan.PhysicalIndex clauses recordStart recordEnd base processed
      (heap.set 0 value bound) := by
  have ending : recordStart ≤ recordEnd := by
    rw [index.originalEnd]
    exact Controller.Horn.NormalizeLoop.recordOffset_above clauses recordStart clauses.length
  have frame (position : Nat) (above : recordStart ≤ position) :
      (heap.set 0 value bound)[position]? = heap[position]? := by
    have different : position ≠ 0 := by have := index.separation; omega
    simp [Array.getElem?_set, Ne.symm different]
  refine ⟨index.prefixBound, by simpa using index.endpoint, ?_, ?_, ?_,
    index.originalEnd, index.separation, index.positiveEnd⟩
  · intro label
    have different : headAddress base label ≠ 0 := by
      unfold Controller.Horn.WorklistStorage.headAddress; omega
    simpa [Array.getElem?_set, Ne.symm different] using index.headValues label
  · intro item
    apply node_frame _ _ _ heap _ (index.nodes item) (by simp)
    intro position above inside
    exact frame position (by omega)
  · intro row
    apply IndexScan.record_frame _ _ heap _ (index.records row) (by simp)
    intro position above inside
    exact frame position (by
      have := Controller.Horn.NormalizeLoop.recordOffset_above clauses recordStart row.val
      omega)

end Controller.Cost.ForestZeroHeaderBridge
