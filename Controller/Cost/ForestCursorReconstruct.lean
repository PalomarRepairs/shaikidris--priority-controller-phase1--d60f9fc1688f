module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestCursorWholeProgram
public import Controller.Cost.ForestMarkerResetLoop
public import Mathlib.Tactic.FinCases

@[expose] public section

/-!
# One parent-pointer reconstruction loop

Zero is the terminal descriptor ID. Every positive ID stores an earlier parent
and its child position. A fixed instruction block reads these two cells, pushes
the position and continues with the parent. The caller retains the declared
root ID separately. Heap and output are read-only during this phase.
-/
namespace Controller.Cost.ForestCursorReconstruct
open Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestCounter Controller.Cost.ForestCursorProgram
open Controller.Cost.GateProgram Controller.Cost.ForestMarkerMachine

/-- The fetched code is independent of the selected route depth. Encoded −1
is added only to positive, represented IDs. -/
def reconstructCode (width base descriptorBase : ℕ) : ForestCounter.Code width :=
  [.branchZero 0 (word width (base + 14)),
   .constant 1 (word width (2 ^ width - 1)), .add 0 0 1,
   .add 0 0 0, .constant 1 (word width descriptorBase), .add 0 0 1,
   .load 1 0, .constant 2 (word width 1), .add 0 0 2,
   .load 2 0, .push 2, .copy 0 1,
   .constant 3 (word width 0), .branchZero 3 (word width base)]

@[simp] theorem reconstructCode_length (width base descriptorBase : ℕ) :
    (reconstructCode width base descriptorBase).length = 14 := rfl

/-- Every descriptor route has at most as many links as its numeric ID. The
bound follows from strict parent decrease, without a graph uniqueness premise. -/
theorem route_length_bound (routes : RouteDescriptors width heap) (pointer : ℕ)
    (bounded : pointer ≤ routes.count) : (routes.route pointer).length ≤ pointer := by
  have claim : ∀ pointer : ℕ, pointer ≤ routes.count → (routes.route pointer).length ≤ pointer := by
    intro pointer
    induction pointer using Nat.strong_induction_on with
    | h pointer ih =>
        intro bounded
        by_cases zero : pointer = 0
        · subst pointer; simp only [routes.sentinel, List.length_nil, le_refl]
        · have valid : 0 < pointer ∧ pointer ≤ routes.count := ⟨Nat.pos_of_ne_zero zero, bounded⟩
          have earlier := routes.parentEarlier pointer valid
          have parentBound : (heap[routes.base + 2 * (pointer - 1)]'(routes.parentValid pointer valid)).val ≤ routes.count :=
            Nat.le_trans (Nat.le_of_lt earlier) bounded
          have tail := ih _ earlier parentBound
          rw [routes.cellRoute pointer valid, List.length_cons]
          omega
  exact claim pointer bounded

/-- Address and no-wrap obligations are obtained from the actual represented
cells, rather than an unrestricted address oracle. -/
theorem descriptor_addresses (routes : RouteDescriptors width heap) (pointer : ℕ)
    (valid : 0 < pointer ∧ pointer ≤ routes.count) (heapFits : heap.size ≤ 2 ^ width) :
    routes.base + 2 * (pointer - 1) < heap.size ∧
    routes.base + 2 * (pointer - 1) + 1 < heap.size ∧
    routes.base + 2 * (pointer - 1) + 1 < 2 ^ width := by
  exact ⟨routes.parentValid pointer valid, routes.positionValid pointer valid,
    Nat.lt_of_lt_of_le (routes.positionValid pointer valid) heapFits⟩

private theorem predecessor_word (width pointer : ℕ) (positive : 0 < pointer)
    (fits : pointer < 2 ^ width) :
    word width ((word width pointer).val + (word width (2 ^ width - 1)).val) = word width (pointer - 1) := by
  have modulusPositive := Nat.two_pow_pos width
  have minusFits : 2 ^ width - 1 < 2 ^ width := by omega
  rw [show (word width pointer).val = pointer from Nat.mod_eq_of_lt fits,
    show (word width (2 ^ width - 1)).val = 2 ^ width - 1 from Nat.mod_eq_of_lt minusFits]
  apply Fin.ext
  change (pointer + (2 ^ width - 1)) % (2 ^ width) = (pointer - 1) % (2 ^ width)
  have arithmetic : pointer + (2 ^ width - 1) = (pointer - 1) + 2 ^ width := by omega
  rw [arithmetic, Nat.add_mod_right]

/-- The zero-ID test is one actual fetched instruction and reaches the shared
exit address without inspecting descriptor cells. -/
theorem sentinel_execution (program : Program width 4) (heap : Array (Word width))
    (base descriptorBase : ℕ) (loaded temporary : Word width)
    (fits : base + 14 < 2 ^ width)
    (block : BlockAt program base (reconstructCode width base descriptorBase)) :
    Execution program (counterState heap base (word width 0) loaded temporary)
      (counterState heap (base + 14) (word width 0) loaded temporary)
      1 (5 + heap.size) := by
  have fetched : program[base]? = some (.branchZero 0 (word width (base + 14))) := by
    simpa [reconstructCode] using block 0 (by simp)
  have transition := branch_transition program heap base (base + 14) 0
    (word width 0) loaded temporary (by omega) fetched
  have zero : ((counterState heap base (word width 0) loaded temporary).reg (0 : Fin 4)).val = 0 := by
    simp [counterState, word]
  rw [zero, ite_eq_left rfl] at transition
  have trace := Execution.cons transition (Execution.refl
    (counterState heap (base + 14) (word width 0) loaded temporary))
  simpa only [counterState_liveWords, max_self] using trace

private theorem advance_state (heap : Array (Word width)) (cursor : ℕ)
    (address loaded temporary : Word width) (fits : cursor < 2 ^ width) :
    (counterState heap cursor address loaded temporary).advance =
      counterState heap (cursor + 1) address loaded temporary := by
  unfold State.advance counterState
  rw [show (word width cursor).val = cursor from Nat.mod_eq_of_lt fits]

private theorem put_address (heap : Array (Word width)) (cursor : ℕ)
    (address loaded temporary value : Word width) :
    (counterState heap cursor address loaded temporary).put 0 value =
      counterState heap cursor value loaded temporary := by
  unfold State.put counterState
  congr 1
  funext register
  fin_cases register <;> rfl

private theorem put_temporary (heap : Array (Word width)) (cursor : ℕ)
    (address loaded temporary value : Word width) :
    (counterState heap cursor address loaded temporary).put 2 value =
      counterState heap cursor address loaded value := by
  unfold State.put counterState
  congr 1
  funext register
  fin_cases register <;> rfl

private theorem put_zero (heap : Array (Word width)) (cursor : ℕ)
    (address loaded temporary : Word width) :
    (counterState heap cursor address loaded temporary).put 3 (word width 0) =
      counterState heap cursor address loaded temporary := by
  unfold State.put counterState
  congr 1
  funext register
  fin_cases register <;> rfl

private theorem double_transition (program : Program width 4) (heap : Array (Word width))
    (cursor : ℕ) (address loaded temporary : Word width) (fits : cursor < 2 ^ width)
    (fetched : program[cursor]? = some (.add 0 0 0)) :
    programStep program (counterState heap cursor address loaded temporary) =
      some (counterState heap (cursor + 1) (word width (address.val + address.val)) loaded temporary) := by
  unfold programStep
  rw [show (counterState heap cursor address loaded temporary).pc.val = cursor from Nat.mod_eq_of_lt fits, fetched]
  change step (.add (0 : Fin 4) 0 0) (counterState heap cursor address loaded temporary) = _
  simp only [step, counterState, Bool.false_eq_true, ite_false]
  change some ((counterState heap cursor address loaded temporary).advance.put 0
    (word width (address.val + address.val))) = _
  rw [advance_state _ _ _ _ _ fits, put_address]
  rfl

private theorem offset_transition (program : Program width 4) (heap : Array (Word width))
    (cursor : ℕ) (address loaded temporary : Word width) (fits : cursor < 2 ^ width)
    (fetched : program[cursor]? = some (.add 0 0 2)) :
    programStep program (counterState heap cursor address loaded temporary) =
      some (counterState heap (cursor + 1) (word width (address.val + temporary.val)) loaded temporary) := by
  unfold programStep
  rw [show (counterState heap cursor address loaded temporary).pc.val = cursor from Nat.mod_eq_of_lt fits, fetched]
  change step (.add (0 : Fin 4) 0 2) (counterState heap cursor address loaded temporary) = _
  simp only [step, counterState, Bool.false_eq_true, ite_false]
  change some ((counterState heap cursor address loaded temporary).advance.put 0
    (word width (address.val + temporary.val))) = _
  rw [advance_state _ _ _ _ _ fits, put_address]
  rfl

private theorem temporary_read_transition (program : Program width 4) (heap : Array (Word width))
    (cursor address : ℕ) (loaded temporary : Word width) (cursorFits : cursor < 2 ^ width)
    (addressFits : address < 2 ^ width) (valid : address < heap.size)
    (fetched : program[cursor]? = some (.load 2 0)) :
    programStep program (counterState heap cursor (word width address) loaded temporary) =
      some (counterState heap (cursor + 1) (word width address) loaded heap[address]) := by
  unfold programStep
  rw [show (counterState heap cursor (word width address) loaded temporary).pc.val = cursor from Nat.mod_eq_of_lt cursorFits, fetched]
  change step (.load (2 : Fin 4) 0) (counterState heap cursor (word width address) loaded temporary) = _
  simp only [step, counterState, Bool.false_eq_true, ite_false]
  change (if h : (word width address).val < heap.size then
    some ((counterState heap cursor (word width address) loaded temporary).advance.put 2
      heap[(word width address).val]) else none) = _
  have encoded : (word width address).val = address := Nat.mod_eq_of_lt addressFits
  rw [dite_eq_left (by simpa only [encoded] using valid)]
  simp only [encoded]
  rw [advance_state _ _ _ _ _ cursorFits, put_temporary]
  rfl

private theorem push_temporary_transition (program : Program width 4) (heap : Array (Word width))
    (cursor : ℕ) (address loaded temporary : Word width) (fits : cursor < 2 ^ width)
    (fetched : program[cursor]? = some (.push 2)) :
    programStep program (counterState heap cursor address loaded temporary) =
      some ((counterState heap (cursor + 1) address loaded temporary).frame [temporary] []) := by
  unfold programStep
  rw [show (counterState heap cursor address loaded temporary).pc.val = cursor from Nat.mod_eq_of_lt fits, fetched]
  change step (.push (2 : Fin 4)) (counterState heap cursor address loaded temporary) = _
  simp [step, counterState, State.advance, State.frame,
    show (word width cursor).val = cursor from Nat.mod_eq_of_lt fits]

private theorem copy_parent_transition (program : Program width 4) (heap : Array (Word width))
    (cursor : ℕ) (address loaded temporary : Word width) (fits : cursor < 2 ^ width)
    (fetched : program[cursor]? = some (.copy 0 1)) :
    programStep program (counterState heap cursor address loaded temporary) =
      some (counterState heap (cursor + 1) loaded loaded temporary) := by
  unfold programStep
  rw [show (counterState heap cursor address loaded temporary).pc.val = cursor from Nat.mod_eq_of_lt fits, fetched]
  change step (.copy (0 : Fin 4) 1) (counterState heap cursor address loaded temporary) = _
  simp only [step, counterState, Bool.false_eq_true, ite_false]
  change some ((counterState heap cursor address loaded temporary).advance.put 0 loaded) = _
  rw [advance_state _ _ _ _ _ fits, put_address]
  rfl

private theorem zero_scratch_transition (program : Program width 4) (heap : Array (Word width))
    (cursor : ℕ) (address loaded temporary : Word width) (fits : cursor < 2 ^ width)
    (fetched : program[cursor]? = some (.constant 3 (word width 0))) :
    programStep program (counterState heap cursor address loaded temporary) =
      some (counterState heap (cursor + 1) address loaded temporary) := by
  unfold programStep
  rw [show (counterState heap cursor address loaded temporary).pc.val = cursor from Nat.mod_eq_of_lt fits, fetched]
  change step (.constant (3 : Fin 4) (word width 0)) (counterState heap cursor address loaded temporary) = _
  simp only [step, counterState, Bool.false_eq_true, ite_false]
  change some ((counterState heap cursor address loaded temporary).advance.put 3 (word width 0)) = _
  rw [advance_state _ _ _ _ _ fits, put_zero]
  rfl

/-- One positive descriptor executes the fixed fetched body, pushes exactly
its stored position, and returns to the same sentinel test with its parent ID. -/
theorem parent_execution (program : Program width 4) (heap : Array (Word width))
    (routes : RouteDescriptors width heap) (base pointer : ℕ) (loaded temporary : Word width)
    (valid : 0 < pointer ∧ pointer ≤ routes.count) (pointerFits : pointer < 2 ^ width)
    (heapFits : heap.size ≤ 2 ^ width) (programFits : base + 14 < 2 ^ width)
    (block : BlockAt program base (reconstructCode width base routes.base)) :
    Execution program (counterState heap base (word width pointer) loaded temporary)
      ((counterState heap base
        (heap[routes.base + 2 * (pointer - 1)]'(routes.parentValid pointer valid))
        (heap[routes.base + 2 * (pointer - 1)]'(routes.parentValid pointer valid))
        (heap[routes.base + 2 * (pointer - 1) + 1]'(routes.positionValid pointer valid))).frame
        [heap[routes.base + 2 * (pointer - 1) + 1]'(routes.positionValid pointer valid)] [])
      14 (6 + heap.size) := by
  let address := routes.base + 2 * (pointer - 1)
  let parent := heap[address]'(routes.parentValid pointer valid)
  let position := heap[address + 1]'(routes.positionValid pointer valid)
  have addressValid : address < heap.size := routes.parentValid pointer valid
  have positionValid : address + 1 < heap.size := routes.positionValid pointer valid
  have addressFits : address < 2 ^ width := Nat.lt_of_lt_of_le addressValid heapFits
  have positionFits : address + 1 < 2 ^ width := Nat.lt_of_lt_of_le positionValid heapFits
  have predecessorFits : pointer - 1 < 2 ^ width := by omega
  have doubleFits : 2 * (pointer - 1) < 2 ^ width := by dsimp [address] at addressFits; omega
  have descriptorFits : routes.base < 2 ^ width := by dsimp [address] at addressFits; omega
  have oneFits : 1 < 2 ^ width := by omega
  have fetched0 : program[base]? = some (.branchZero 0 (word width (base + 14))) := by
    simpa [reconstructCode] using block 0 (by simp)
  have fetched1 : program[base + 1]? = some (.constant 1 (word width (2 ^ width - 1))) := by
    simpa [reconstructCode] using block 1 (by simp)
  have fetched2 : program[base + 2]? = some (.add 0 0 1) := by
    simpa [reconstructCode] using block 2 (by simp)
  have fetched3 : program[base + 3]? = some (.add 0 0 0) := by
    simpa [reconstructCode] using block 3 (by simp)
  have fetched4 : program[base + 4]? = some (.constant 1 (word width routes.base)) := by
    simpa [reconstructCode] using block 4 (by simp)
  have fetched5 : program[base + 5]? = some (.add 0 0 1) := by
    simpa [reconstructCode] using block 5 (by simp)
  have fetched6 : program[base + 6]? = some (.load 1 0) := by
    simpa [reconstructCode] using block 6 (by simp)
  have fetched7 : program[base + 7]? = some (.constant 2 (word width 1)) := by
    simpa [reconstructCode] using block 7 (by simp)
  have fetched8 : program[base + 8]? = some (.add 0 0 2) := by
    simpa [reconstructCode] using block 8 (by simp)
  have fetched9 : program[base + 9]? = some (.load 2 0) := by
    simpa [reconstructCode] using block 9 (by simp)
  have fetched10 : program[base + 10]? = some (.push 2) := by
    simpa [reconstructCode] using block 10 (by simp)
  have fetched11 : program[base + 11]? = some (.copy 0 1) := by
    simpa [reconstructCode] using block 11 (by simp)
  have fetched12 : program[base + 12]? = some (.constant 3 (word width 0)) := by
    simpa [reconstructCode] using block 12 (by simp)
  have fetched13 : program[base + 13]? = some (.branchZero 3 (word width base)) := by
    simpa [reconstructCode] using block 13 (by simp)

  have t0 := branch_transition program heap base (base + 14) 0 (word width pointer) loaded temporary
    (by omega) fetched0
  have positive : ((counterState heap base (word width pointer) loaded temporary).reg (0 : Fin 4)).val ≠ 0 := by
    change (word width pointer).val ≠ 0
    rw [show (word width pointer).val = pointer from Nat.mod_eq_of_lt pointerFits]
    omega
  rw [ite_eq_right positive] at t0
  have t1 := constant_loaded_transition program heap (base + 1) (word width pointer) loaded temporary
    (word width (2 ^ width - 1)) (by omega) fetched1
  have t2 := add_address_transition program heap (base + 2) (word width pointer)
    (word width (2 ^ width - 1)) temporary (by omega) fetched2
  rw [predecessor_word width pointer valid.1 pointerFits] at t2
  have t3 := double_transition program heap (base + 3) (word width (pointer - 1))
    (word width (2 ^ width - 1)) temporary (by omega) fetched3
  have doubled : word width ((word width (pointer - 1)).val + (word width (pointer - 1)).val) =
      word width (2 * (pointer - 1)) := by
    rw [show (word width (pointer - 1)).val = pointer - 1 from Nat.mod_eq_of_lt predecessorFits]
    congr 1
    omega
  rw [doubled] at t3
  have t4 := constant_loaded_transition program heap (base + 4) (word width (2 * (pointer - 1)))
    (word width (2 ^ width - 1)) temporary (word width routes.base) (by omega) fetched4
  have t5 := add_address_transition program heap (base + 5) (word width (2 * (pointer - 1)))
    (word width routes.base) temporary (by omega) fetched5
  have addressed : word width ((word width (2 * (pointer - 1))).val + (word width routes.base).val) =
      word width address := by
    rw [show (word width (2 * (pointer - 1))).val = 2 * (pointer - 1) from Nat.mod_eq_of_lt doubleFits,
      show (word width routes.base).val = routes.base from Nat.mod_eq_of_lt descriptorFits]
    congr 1
    dsimp [address]
    omega
  rw [addressed] at t5
  have t6 := read_transition program heap (base + 6) address (word width routes.base) temporary parent
    (by omega) addressFits addressValid rfl fetched6
  have t7 := increment_transition program heap (base + 7) 1 (word width address) parent temporary
    (by omega) fetched7
  have t8 := offset_transition program heap (base + 8) (word width address) parent (word width 1)
    (by omega) fetched8
  have nextAddress : word width ((word width address).val + (word width 1).val) = word width (address + 1) := by
    rw [show (word width address).val = address from Nat.mod_eq_of_lt addressFits,
      show (word width 1).val = 1 from Nat.mod_eq_of_lt oneFits]
  rw [nextAddress] at t8
  have t9 := temporary_read_transition program heap (base + 9) (address + 1) parent (word width 1)
    (by omega) positionFits positionValid fetched9
  have t10 := push_temporary_transition program heap (base + 10) (word width (address + 1)) parent position
    (by omega) fetched10
  have t11 := copy_parent_transition program heap (base + 11) (word width (address + 1)) parent position
    (by omega) fetched11
  have t12 := zero_scratch_transition program heap (base + 12) parent parent position (by omega) fetched12
  have t13 := branch_transition program heap (base + 13) base 3 parent parent position (by omega) fetched13
  have zero : ((counterState heap (base + 13) parent parent position).reg (3 : Fin 4)).val = 0 := by
    simp [counterState, word]
  rw [zero, ite_eq_left rfl] at t13
  simp only [Nat.add_assoc] at t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12
  have firstSteps := Execution.cons t0 (Execution.cons t1 (Execution.cons t2 (Execution.cons t3
    (Execution.cons t4 (Execution.cons t5 (Execution.cons t6 (Execution.cons t7 (Execution.cons t8
    (Execution.cons t9 (Execution.cons t10 (Execution.refl
      ((counterState heap (base + 11) (word width (address + 1)) parent position).frame [position] []))))))))))))
  have suffix := (Execution.cons t11 (Execution.cons t12 (Execution.cons t13
    (Execution.refl (counterState heap base parent parent position))))).frame [position] []
  have trace := firstSteps.append suffix
  convert trace using 1 <;> simp only [counterState_liveWords, State.frame_liveWords,
    List.length_cons, List.length_nil, Nat.add_zero] <;> omega

/-- Exactly one reconstruction is performed. The same fetched block is reused
for every parent link; the resulting stack is the forward positional route,
followed by the caller's frame. Heap and output retain their original values. -/
theorem route_execution (program : Program width 4) (heap : Array (Word width))
    (routes : RouteDescriptors width heap) (base pointer : ℕ)
    (countFits : routes.count < 2 ^ width) (heapFits : heap.size ≤ 2 ^ width)
    (programFits : base + 14 < 2 ^ width)
    (block : BlockAt program base (reconstructCode width base routes.base))
    (bounded : pointer ≤ routes.count) (loaded temporary : Word width)
    (stack output : List (Word width)) :
    ∃ finalLoaded finalTemporary : Word width,
      Execution program ((counterState heap base (word width pointer) loaded temporary).frame stack output)
        ((counterState heap (base + 14) (word width 0) finalLoaded finalTemporary).frame
          ((routes.route pointer).reverse.map (word width) ++ stack) output)
        (14 * (routes.route pointer).length + 1)
        (5 + heap.size + ((routes.route pointer).length + stack.length + output.length)) := by
  have claim : ∀ pointer : ℕ, pointer ≤ routes.count →
      ∀ loaded temporary : Word width, ∀ stack output : List (Word width),
      ∃ finalLoaded finalTemporary : Word width,
        Execution program ((counterState heap base (word width pointer) loaded temporary).frame stack output)
          ((counterState heap (base + 14) (word width 0) finalLoaded finalTemporary).frame
            ((routes.route pointer).reverse.map (word width) ++ stack) output)
          (14 * (routes.route pointer).length + 1)
          (5 + heap.size + ((routes.route pointer).length + stack.length + output.length)) := by
    intro pointer
    induction pointer using Nat.strong_induction_on with
    | h pointer ih =>
        intro bounded loaded temporary stack output
        by_cases zero : pointer = 0
        · subst pointer
          refine ⟨loaded, temporary, ?_⟩
          have trace := (sentinel_execution program heap base routes.base loaded temporary programFits block).frame stack output
          simpa only [routes.sentinel, List.reverse_nil, List.map_nil, List.nil_append,
            List.length_nil, Nat.mul_zero, Nat.zero_add] using trace
        · have valid : 0 < pointer ∧ pointer ≤ routes.count := ⟨Nat.pos_of_ne_zero zero, bounded⟩
          let address := routes.base + 2 * (pointer - 1)
          let parent := heap[address]'(routes.parentValid pointer valid)
          let position := heap[address + 1]'(routes.positionValid pointer valid)
          have earlier : parent.val < pointer := routes.parentEarlier pointer valid
          have parentBound : parent.val ≤ routes.count := (Nat.le_of_lt earlier).trans bounded
          have pointerFits : pointer < 2 ^ width := Nat.lt_of_le_of_lt bounded countFits
          have first := (parent_execution program heap routes base pointer loaded temporary valid
            pointerFits heapFits programFits block).frame stack output
          change Execution program ((counterState heap base (word width pointer) loaded temporary).frame stack output)
            ((counterState heap base parent parent position).frame (position :: stack) output)
            14 (6 + heap.size + (stack.length + output.length)) at first
          obtain ⟨finalLoaded, finalTemporary, later⟩ := ih parent.val earlier parentBound parent position (position :: stack) output
          have parentWord : word width parent.val = parent := by
            apply Fin.ext
            exact Nat.mod_eq_of_lt parent.isLt
          rw [parentWord] at later
          have whole := first.append later
          have routeEq : routes.route pointer = position.val :: routes.route parent.val := routes.cellRoute pointer valid
          have positionWord : word width position.val = position := by
            apply Fin.ext
            exact Nat.mod_eq_of_lt position.isLt
          refine ⟨finalLoaded, finalTemporary, ?_⟩
          rw [routeEq, List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
            positionWord, List.append_assoc]
          convert whole using 1 <;>
            simp only [List.length_cons, List.length_nil, List.length_map, List.length_reverse,
              List.singleton_append] <;> omega
  exact claim pointer bounded loaded temporary stack output

/-- Resource bounds use the actual number of parent links, and hence the
selected descriptor ID, without charging a second witness reconstruction. -/
theorem reconstruction_bounds (routes : RouteDescriptors width heap) (pointer : ℕ)
    (bounded : pointer ≤ routes.count) :
    14 * (routes.route pointer).length + 1 ≤ 14 * pointer + 1 ∧
      (routes.route pointer).length ≤ routes.count := by
  have links := route_length_bound routes pointer bounded
  constructor
  · omega
  · exact links.trans bounded

end Controller.Cost.ForestCursorReconstruct
