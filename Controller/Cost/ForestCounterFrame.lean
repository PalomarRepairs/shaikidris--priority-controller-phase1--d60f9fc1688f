module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestCounter
public import Controller.Cost.Frames

@[expose] public section

/-!
# Guard-counter cells with retained traversal frames

Successful counter-cell executions retain arbitrary trailing stack and output
words. The five executed instructions are unchanged; the frame contributes its
actual length to peak storage. This module does not assert invalid-step
invariance or a whole-forest traversal bound.
-/
namespace Controller.Cost.ForestCounter

open Controller.Cost.GateProgram

@[simp] theorem framed_counterState_heap (heap : Array (Word width)) (cursor : Nat)
    (address counter increment : Word width) (stack output : List (Word width)) :
    ((counterState heap cursor address counter increment).frame stack output).heap = heap := rfl

@[simp] theorem framed_counterState_stack (heap : Array (Word width)) (cursor : Nat)
    (address counter increment : Word width) (stack output : List (Word width)) :
    ((counterState heap cursor address counter increment).frame stack output).stack = stack := rfl

@[simp] theorem framed_counterState_output (heap : Array (Word width)) (cursor : Nat)
    (address counter increment : Word width) (stack output : List (Word width)) :
    ((counterState heap cursor address counter increment).frame stack output).output = output := rfl

@[simp] theorem framed_counterState_liveWords (heap : Array (Word width)) (cursor : Nat)
    (address counter increment : Word width) (stack output : List (Word width)) :
    ((counterState heap cursor address counter increment).frame stack output).liveWords =
      5 + heap.size + stack.length + output.length := by
  simp only [State.frame_liveWords, counterState_liveWords]
  omega

/-- The actual indexed change cell retains all live traversal frames. -/
theorem change_execution_framed (program : Program width 4) (heap : Array (Word width))
    (base address delta : Nat) (oldAddress oldCounter oldIncrement storedCounter : Word width)
    (stack output : List (Word width))
    (programFits : base + 5 < 2 ^ width) (addressFits : address < 2 ^ width)
    (valid : address < heap.size) (stored : heap[address] = storedCounter)
    (block : BlockAt program base (changeCode width address delta)) :
    Execution program ((counterState heap base oldAddress oldCounter oldIncrement).frame stack output)
      ((counterState (heap.set address (word width (storedCounter.val + (word width delta).val)))
        (base + 5) (word width address)
        (word width (storedCounter.val + (word width delta).val)) (word width delta)).frame stack output)
      5 (5 + heap.size + stack.length + output.length) := by
  have trace := change_execution program heap base address delta oldAddress oldCounter oldIncrement
    storedCounter programFits addressFits valid stored block
  simpa only [Nat.add_assoc] using trace.frame stack output

/-- A positive path-entry increment does not reinitialize or discard the DFS stack. -/
theorem entry_execution_framed (program : Program width 4) (heap : Array (Word width))
    (base address count : Nat) (oldAddress oldCounter oldIncrement : Word width)
    (stack output : List (Word width))
    (programFits : base + 5 < 2 ^ width) (addressFits : address < 2 ^ width)
    (valid : address < heap.size) (stored : heap[address] = word width count)
    (countFits : count + 1 < 2 ^ width)
    (block : BlockAt program base (changeCode width address 1)) :
    Execution program ((counterState heap base oldAddress oldCounter oldIncrement).frame stack output)
      ((counterState (heap.set address (word width (count + 1))) (base + 5)
        (word width address) (word width (count + 1)) (word width 1)).frame stack output)
      5 (5 + heap.size + stack.length + output.length) := by
  have trace := entry_execution program heap base address count oldAddress oldCounter oldIncrement
    programFits addressFits valid stored countFits block
  simpa only [Nat.add_assoc] using trace.frame stack output

/-- A positive path-exit decrement retains every live traversal/output word. -/
theorem exit_execution_framed (program : Program width 4) (heap : Array (Word width))
    (base address count : Nat) (oldAddress oldCounter oldIncrement : Word width)
    (stack output : List (Word width))
    (programFits : base + 5 < 2 ^ width) (addressFits : address < 2 ^ width)
    (valid : address < heap.size) (stored : heap[address] = word width count)
    (positive : 0 < count) (countFits : count < 2 ^ width)
    (block : BlockAt program base (changeCode width address (2 ^ width - 1))) :
    Execution program ((counterState heap base oldAddress oldCounter oldIncrement).frame stack output)
      ((counterState (heap.set address (word width (count - 1))) (base + 5)
        (word width address) (word width (count - 1)) (word width (2 ^ width - 1))).frame stack output)
      5 (5 + heap.size + stack.length + output.length) := by
  have trace := exit_execution program heap base address count oldAddress oldCounter oldIncrement
    programFits addressFits valid stored positive countFits block
  simpa only [Nat.add_assoc] using trace.frame stack output

end Controller.Cost.ForestCounter
