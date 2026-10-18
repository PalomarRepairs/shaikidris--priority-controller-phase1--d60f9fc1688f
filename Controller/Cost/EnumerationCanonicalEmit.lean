module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.EnumerationCanonicalCoordinates

@[expose] public section

/-! Canonical physical-model output from the single completed prefix region.
The fetched header reads target membership once; the fixed coordinate sequence
then emits every enable, request and asserted interface-wire bit. -/
namespace Controller.Cost.EnumerationCanonicalEmit
open Controller.Decoder Controller.Native Controller.Native.Parameters Controller.Physical
open Controller.Cost.GateProgram Controller.Cost.RawTransferLoops
open Controller.Cost.EnumerationCanonicalCoordinates

abbrev Coordinates (parameters : Parameters) : Nat :=
  parameters.channels + parameters.buses * parameters.channels + 1

def header (width address : Nat) : List (Instruction width 8) :=
  [.constant 0 (word width address), .load 2 0, .constant 7 (word width 0)]

@[simp] theorem header_length : (header width address).length = 3 := rfl

def code (parameters : Parameters) (width entry base : Nat) : List (Instruction width 8) :=
  header width (base + parameters.bridge.target.val) ++
    EnumerationEmissionOperands.code width (entry + 3) (operands parameters base)

def words (parameters : Parameters) (width : Nat) (K : Finset (Channel parameters.channels)) : List (Word width) :=
  parameters.primaryRoles.map (fun role => boolWord width
    (primaryAssignment (realizeBridge parameters.bridge parameters.positiveBuses K) true role))

@[simp] theorem words_length (parameters : Parameters) (width : Nat) (K : Finset (Channel parameters.channels)) :
    (words parameters width K).length = Coordinates parameters := by
  simp only [words, List.length_map, primaryRoles_length]

theorem code_length_bound (parameters : Parameters) (width entry base : Nat) :
    (code parameters width entry base).length ≤ 3 + 6 * Coordinates parameters := by
  have bound := EnumerationEmissionOperands.code_length_bound width (entry + 3) (operands parameters base)
  simpa only [code, List.length_append, header_length, operands_length] using Nat.add_le_add_left bound 3

private theorem header_execution (program : Program width 8) (state : State width 8)
    (entry address : Nat) (value : Bool)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 3 < 2 ^ width) (heapFits : state.heap.size < 2 ^ width)
    (valid : address < state.heap.size) (cell : state.heap[address]? = some (boolWord width value))
    (present : SharedRootRead.BlockAt program entry (header width address)) :
    ∃ final, Execution program state final 3 state.liveWords ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry + 3) ∧ final.halted = false ∧
      final.reg 2 = boolWord width value ∧ final.reg 7 = word width 0 ∧
      (∀ register : Fin 8, register ≠ 0 → register ≠ 2 → register ≠ 7 → final.reg register = state.reg register) := by
  obtain ⟨addressed, t0, pc0, held0, heap0, stack0, output0, running0, frame0⟩ :=
    SharedEvaluationReclaim.constant_execution program entry address 0 state position running (by omega)
      (by simpa [header] using present 0 (by simp))
  have actualAddress : (addressed.reg 0).val = address := by rw [held0]; exact Nat.mod_eq_of_lt (by omega)
  obtain ⟨loaded, t1, pc1, held1, heap1, stack1, output1, running1, frame1⟩ :=
    EnumerationSteps.load_execution (program := program) addressed (entry + 1) 2 0 pc0 running0 (by omega)
      (by rw [actualAddress, heap0]; exact valid) (by simpa [header] using present 1 (by simp))
  have flag : loaded.reg 2 = boolWord width value := by
    rw [held1]
    have actualCell : addressed.heap[(addressed.reg 0).val]? = some (boolWord width value) := by
      simpa only [actualAddress, heap0] using cell
    exact (Array.getElem?_eq_some_iff.mp actualCell).2
  obtain ⟨final, t2, pc2, held2, heap2, stack2, output2, running2, frame2⟩ :=
    SharedEvaluationReclaim.constant_execution program (entry + 1 + 1) 0 7 loaded pc1 running1 (by omega)
      (by simpa [header, Nat.add_assoc] using present 2 (by simp))
  have live0 : addressed.liveWords = state.liveWords := by simp only [State.liveWords, heap0, stack0, output0]
  have live1 : loaded.liveWords = state.liveWords := by simp only [State.liveWords, heap1, stack1, output1, heap0, stack0, output0]
  refine ⟨final, ?_, heap2.trans (heap1.trans heap0), stack2.trans (stack1.trans stack0),
    output2.trans (output1.trans output0), ?_, running2, (frame2 2 (by decide)).trans flag, held2, ?_⟩
  · simpa only [live0, live1, Nat.max_self, Nat.reduceAdd] using t0.append (t1.append t2)
  · simpa only [Nat.add_assoc, Nat.reduceAdd] using pc2
  · intro register notZero notTwo notSeven
    rw [frame2 register notSeven, frame1 register notTwo, frame0 register notZero]

theorem execution (parameters : Parameters) (program : Program width 8) (state : State width 8)
    (entry base : Nat) (K : Finset (Channel parameters.channels))
    (stored : Stored parameters state.heap base K)
    (position : state.pc = word width entry) (running : state.halted = false)
    (widthPositive : 0 < width) (room : entry + (code parameters width entry base).length < 2 ^ width)
    (heapFits : state.heap.size < 2 ^ width) (maskRoom : base + parameters.channels ≤ state.heap.size)
    (present : SharedRootRead.BlockAt program entry (code parameters width entry base)) :
    ∃ final ticks, Execution program state final ticks (state.liveWords + Coordinates parameters) ∧
      ticks ≤ 3 + 4 * Coordinates parameters ∧ final.heap = state.heap ∧ final.stack = state.stack ∧
      final.output = (words parameters width K).reverse ++ state.output ∧
      final.pc = word width (entry + (code parameters width entry base).length) ∧ final.halted = false ∧
      EnumerationStreamEmit.workingWords final = EnumerationStreamEmit.workingWords state ∧
      (∀ register : Fin 8, register ≠ 0 → register ≠ 1 → register ≠ 2 → register ≠ 7 →
        final.reg register = state.reg register) := by
  have headBlock : SharedRootRead.BlockAt program entry (header width (base + parameters.bridge.target.val)) := by
    intro offset bound
    have whole := present offset (by simp only [code, List.length_append]; omega)
    simp only [code] at whole
    rw [List.getElem?_append_left bound] at whole
    exact whole
  have tailBlock : SharedRootRead.BlockAt program (entry + 3)
      (EnumerationEmissionOperands.code width (entry + 3) (operands parameters base)) := by
    intro offset bound
    have whole := present (3 + offset) (by simp only [code, List.length_append, header_length]; omega)
    simp only [code] at whole
    rw [List.getElem?_append_right (by simp only [header_length]; omega)] at whole
    simpa only [header_length, Nat.add_sub_cancel_left, Nat.add_assoc] using whole
  obtain ⟨prepared, first, heap, stack, output, pc, live, flag, zero, frame⟩ :=
    header_execution program state entry (base + parameters.bridge.target.val)
      (decide (parameters.bridge.target ∈ K)) position running
      (by simp only [code, List.length_append, header_length] at room; omega) heapFits
      (by have := parameters.bridge.target.isLt; omega) (stored parameters.bridge.target) headBlock
  obtain ⟨final, tail, finalHeap, finalStack, finalOutput, finalPC, finalRunning, finalFrame⟩ :=
    EnumerationEmissionOperands.execution program prepared (entry + 3) (operands parameters base)
      (decide (parameters.bridge.target ∈ K)) pc live flag zero widthPositive
      (by simpa only [code, List.length_append, header_length, Nat.add_assoc] using room)
      (by simpa only [heap] using heapFits)
      (by rw [heap]; exact operands_valid parameters state.heap base maskRoom) tailBlock
  have sameLive : prepared.liveWords = state.liveWords := by simp only [State.liveWords, heap, stack, output]
  have finalHeap' := finalHeap.trans heap
  have finalStack' := finalStack.trans stack
  refine ⟨final, 3 + EnumerationEmissionOperands.ticks (operands parameters base), ?_, ?_,
    finalHeap', finalStack', ?_, ?_, finalRunning,
    EnumerationStreamEmit.emission_working_words state final finalHeap' finalStack', ?_⟩
  · simpa only [sameLive, operands_length, Nat.max_eq_right (Nat.le_add_right _ _)] using first.append tail
  · have bound := EnumerationEmissionOperands.ticks_bound (operands parameters base)
    simpa only [operands_length] using Nat.add_le_add_left bound 3
  · rw [finalOutput, heap, output, operands_value parameters state.heap base K stored]; rfl
  · simpa only [code, List.length_append, header_length, Nat.add_assoc] using finalPC
  · intro register notZero notOne notTwo notSeven
    rw [finalFrame register notZero notOne, frame register notZero notTwo notSeven]

end Controller.Cost.EnumerationCanonicalEmit
