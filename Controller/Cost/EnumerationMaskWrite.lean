module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.EnumerationSteps
public import Controller.Cost.EnumerationMasks

@[expose] public section

/-! Fixed four-instruction updates of one runtime prefix-mask cell. The depth
in register three is read at execution time; the instruction array is fixed. -/
namespace Controller.Cost.EnumerationMaskWrite
open Controller.Cost.GateProgram Controller.Cost.RawTransferLoops

def Stored (heap : Array (Word width)) (base : Nat) (words : List (Word width)) : Prop :=
  ∀ index (inside : index < words.length), heap[base + index]? = some words[index]

theorem stored_update (heap : Array (Word width)) (base : Nat) (words : List (Word width))
    (stored : Stored heap base words) (index : Nat) (inside : index < words.length)
    (value : Word width) (valid : base + index < heap.size) :
    Stored (heap.set (base + index) value valid) base (words.set index value) := by
  intro offset below
  have offsetBound : offset < words.length := by simpa using below
  by_cases same : index = offset
  · subst offset
    rw [Array.getElem?_set_self, List.getElem_set_self (by simpa using inside)]
  · have distinct : base + index ≠ base + offset := by omega
    rw [Array.getElem?_set_ne valid distinct, List.getElem_set_ne same]
    exact stored offset offsetBound

def code (width base : Nat) (value : Bool) : List (Instruction width 8) :=
  [.constant 0 (word width base), .add 0 0 3, .constant 1 (boolWord width value), .store 0 1]

@[simp] theorem code_length : (code width base value).length = 4 := rfl

theorem execution (program : Program width 8) (state : State width 8)
    (entry base index : Nat) (value : Bool)
    (position : state.pc = word width entry) (running : state.halted = false)
    (held : state.reg 3 = word width index) (valid : base + index < state.heap.size)
    (heapFits : state.heap.size < 2 ^ width) (room : entry + 4 < 2 ^ width)
    (present : SharedRootRead.BlockAt program entry (code width base value)) :
    ∃ final, Execution program state final 4 state.liveWords ∧
      final.heap = state.heap.set (base + index) (boolWord width value) valid ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry + 4) ∧ final.halted = false ∧
      (∀ register : Fin 8, register ≠ 0 → register ≠ 1 → final.reg register = state.reg register) := by
  obtain ⟨loaded, t0, pc0, reg0, heap0, stack0, output0, running0, frame0⟩ :=
    SharedEvaluationReclaim.constant_execution program entry base 0 state position running (by omega)
      (by simpa [code] using present 0 (by simp))
  obtain ⟨added, t1, pc1, reg1, heap1, stack1, output1, running1, frame1⟩ :=
    EnumerationSteps.add_execution (program := program) loaded (entry + 1) 0 0 3 pc0 running0 (by omega)
      (by simpa [code] using present 1 (by simp))
  have address : added.reg 0 = word width (base + index) := by
    rw [reg1, reg0, frame0 3 (by decide), held]
    simp only [word, Nat.mod_eq_of_lt (by omega : base < 2 ^ width), Nat.mod_eq_of_lt (by omega : index < 2 ^ width)]
  obtain ⟨valued, t2, pc2, reg2, heap2, stack2, output2, running2, frame2⟩ :=
    SharedEvaluationReclaim.constant_execution program (entry + 1 + 1) (if value then 1 else 0) 1 added pc1 running1 (by omega)
      (by simpa [code, boolWord, Nat.add_assoc] using present 2 (by simp))
  have actualValue : valued.reg 1 = boolWord width value := reg2
  have addressValue : (valued.reg 0).val = base + index := by
    rw [frame2 0 (by decide), address]
    exact Nat.mod_eq_of_lt (by omega)
  obtain ⟨final, t3, pc3, heap3, stack3, output3, running3, frame3⟩ :=
    EnumerationSteps.store_execution (program := program) valued (entry + 1 + 1 + 1) 0 1 pc2 running2 (by omega)
      (by rw [addressValue, heap2, heap1, heap0]; exact valid)
      (by simpa [code, Nat.add_assoc] using present 3 (by simp))
  have live0 : loaded.liveWords = state.liveWords := by simp only [State.liveWords, heap0, stack0, output0]
  have live1 : added.liveWords = state.liveWords := by simp only [State.liveWords, heap1, stack1, output1, heap0, stack0, output0]
  have live2 : valued.liveWords = state.liveWords := by simp only [State.liveWords, heap2, stack2, output2, heap1, stack1, output1, heap0, stack0, output0]
  refine ⟨final, ?_, ?_, stack3.trans (stack2.trans (stack1.trans stack0)),
    output3.trans (output2.trans (output1.trans output0)), ?_, running3, ?_⟩
  · simpa only [live0, live1, live2, Nat.max_self, Nat.reduceAdd] using t0.append (t1.append (t2.append t3))
  · simpa only [addressValue, actualValue, heap2, heap1, heap0] using heap3
  · simpa only [Nat.add_assoc, Nat.reduceAdd] using pc3
  · intro register notZero notOne
    rw [frame3, frame2 register notOne, frame1 register notZero, frame0 register notZero]

end Controller.Cost.EnumerationMaskWrite
