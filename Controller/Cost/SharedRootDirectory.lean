module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedRootLoopCode

@[expose] public section

namespace Controller.Cost.SharedRootDirectory
open Controller.Cost.GateProgram Controller.Cost.ForestZeroAdmissibleCaller

/-- Each remaining root is stored at its corresponding cursor address. -/
def Stored (heap : Array (Word width)) (base : Nat) (roots : List (Fin nodes)) : Prop :=
  ∀ index root, roots[index]? = some root → heap[base + index]? = some (word width root.val)

theorem tail (heap : Array (Word width)) (base : Nat) (root : Fin nodes)
    (roots : List (Fin nodes)) (stored : Stored heap base (root :: roots)) :
    Stored heap (base + 1) roots := by
  intro index next member
  have found := stored (index + 1) next (by simpa using member)
  simpa only [Nat.add_assoc, Nat.add_comm 1 index] using found

theorem head (heap : Array (Word width)) (base : Nat) (root : Fin nodes)
    (roots : List (Fin nodes)) (stored : Stored heap base (root :: roots)) :
    heap[base]? = some (word width root.val) := by
  simpa using stored 0 root (by simp)

theorem root_update (heap : Array (Word width)) (base slot : Nat)
    (roots : List (Fin nodes)) (value : Word width) (valid : slot < heap.size)
    (stored : Stored heap base roots) (beforeSlot : base + roots.length ≤ slot) :
    Stored (heap.set slot value valid) base roots := by
  intro index root member
  have below : index < roots.length := by
    by_contra outside
    have missing : roots[index]? = none := List.getElem?_eq_none (by omega)
    rw [missing] at member
    contradiction
  rw [Array.getElem?_set_ne valid (by omega)]
  exact stored index root member

theorem ready_stored (sourceHeap : Array (Word width)) (state : State width 8)
    (tableBase inverseBase entry base : Nat) (rest : List (Word width))
    (roots : List (Fin nodes))
    (ready : QueryReady (ambient := ambient) sourceHeap tableBase inverseBase entry rest state)
    (stored : Stored sourceHeap base roots) (beforeTable : base + roots.length ≤ tableBase) :
    Stored state.heap base roots := by
  intro index root member
  have below : index < roots.length := by
    by_contra outside
    have missing : roots[index]? = none := List.getElem?_eq_none (by omega)
    rw [missing] at member
    contradiction
  exact (ready.sourceFrame.2.2 (base + index) (by omega)).trans (stored index root member)

/-- Repeated selections replace one root cell without accumulating source changes. -/
theorem selected_snapshot (heap : Array (Word width)) (slot : Nat)
    (oldRoot root : Fin nodes) (valid : slot < heap.size) :
    (heap.set slot (word width oldRoot.val) valid).set slot (word width root.val)
      (by simpa using valid) = heap.set slot (word width root.val) valid := by
  exact Array.set_set _ valid


theorem failed_query_tail (sourceHeap : Array (Word width)) (final : State width 8)
    (tableBase inverseBase entry base slot : Nat) (root : Fin nodes)
    (roots : List (Fin nodes)) (rest : List (Word width)) (valid : slot < sourceHeap.size)
    (stored : Stored sourceHeap base (root :: roots))
    (beforeSlot : base + (root :: roots).length ≤ slot) (slotBefore : slot < tableBase)
    (ready : QueryReady (ambient := ambient)
      (sourceHeap.set slot (word width root.val) valid) tableBase inverseBase entry
      (word width (base + 1) :: word width roots.length :: rest) final) :
    Stored final.heap (base + 1) roots := by
  have updated := root_update sourceHeap base slot (root :: roots) (word width root.val) valid stored beforeSlot
  exact ready_stored _ final tableBase inverseBase entry (base + 1) _ roots ready
    (tail _ base root roots updated) (by simp only [List.length_cons] at beforeSlot; omega)

theorem source_valid (heap : Array (Word width)) (base : Nat) (root : Fin nodes)
    (roots : List (Fin nodes)) (stored : Stored heap base (root :: roots)) : base < heap.size := by
  have found := head heap base root roots stored
  by_contra outside
  have missing : heap[base]? = none := Array.getElem?_eq_none (by omega)
  rw [missing] at found
  contradiction

end Controller.Cost.SharedRootDirectory
