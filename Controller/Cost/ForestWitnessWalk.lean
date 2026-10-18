module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestWitnessPath
public import Controller.Cost.ForestCursorWholeProgram

public import Mathlib.Tactic.FinCases

@[expose] public section

/-! Source and descriptor retention at the boundary between the complete
all-root traversal and one witness walk. The marker region is the existing
counter region whose zero restoration follows from the source traversal.
The stored source prefix and parent records precede that region. -/
namespace Controller.Cost.ForestWitnessWalk
open Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.GateProgram Controller.Cost.ForestCounter
open Controller.Cost.ForestCursorProgram Controller.Cost.ForestCursorTraversal
open Controller.Cost.ForestCursorRoot Controller.Cost.ForestCursorExecution
open Controller.Cost.ForestCursorAllRoots Controller.Cost.ForestCursorAllRootsExecution
open Controller.Cost.ForestCursorWholeProgram Controller.Cost.ForestCursorDescriptors
variable {width n : ℕ}

/-- Three real instructions reload the declared channel count from its
stored header and establish the emitter's marker-base register. -/
def emitInit (width markerBase countAddress : ℕ) : ForestCounter.Code width :=
  [.constant 3 (word width markerBase), .constant 0 (word width countAddress), .load 0 0]

@[simp] theorem emitInit_length : (emitInit width markerBase countAddress).length = 3 := rfl

/-- One fixed source walk, one header reload, and the fixed complement loop. -/
def code (width base : ℕ) (layout : ForestWitnessPath.Layout) (countAddress : ℕ) :
    ForestCounter.Code width :=
  ForestWitnessPath.code width base layout ++ emitInit width layout.markerBase countAddress ++
    ForestWitnessEmit.code width (base + 57)

@[simp] theorem code_length : (code width base layout countAddress).length = 67 := by
  simp [code]

private theorem fetchedInit (program : Program width 4) (s : State width 4)
    (base offset markerBase countAddress : ℕ) (pc : s.pc = word width (base + offset))
    (fits : base + offset < 2 ^ width) (inside : offset < 3)
    (block : BlockAt program base (emitInit width markerBase countAddress)) :
    programStep program s = ((emitInit width markerBase countAddress)[offset]?).bind
      (fun instruction => step instruction s) := by
  unfold programStep
  rw [pc, show (word width (base + offset)).val = base + offset from Nat.mod_eq_of_lt fits,
    block offset (by simpa only [emitInit_length] using inside)]
  rfl

private theorem advance_pc (s : State width 4) (pcValue : s.pc = word width pc)
    (fits : pc < 2 ^ width) : s.advance.pc = word width (pc + 1) := by
  simp only [State.advance, pcValue]
  rw [show (word width pc).val = pc from Nat.mod_eq_of_lt fits]

/-- Count and marker-base registers are physically established before output;
no source-list length or heap-size query acts as a machine operation. -/
theorem emitInit_execution (program : Program width 4) (s : State width 4)
    (base markerBase countAddress declaredCount : ℕ)
    (storedCount : countAddress < s.heap.size)
    (countWord : s.heap[countAddress]'storedCount = word width declaredCount)
    (addressFits : countAddress < 2 ^ width)
    (pc : s.pc = word width base) (running : s.halted = false)
    (fits : base + 3 < 2 ^ width)
    (block : BlockAt program base (emitInit width markerBase countAddress)) :
    ∃ ready, Execution program s ready 3 s.liveWords ∧
      ready.reg 0 = word width declaredCount ∧ ready.reg 1 = s.reg 1 ∧
      ready.reg 2 = s.reg 2 ∧ ready.reg 3 = word width markerBase ∧
      ready.heap = s.heap ∧ ready.stack = s.stack ∧ ready.output = s.output ∧
      ready.pc = word width (base + 3) ∧ ready.halted = false := by
  let one := s.advance.put 3 (word width markerBase)
  let two := one.advance.put 0 (word width countAddress)
  let ready := two.advance.put 0 (word width declaredCount)
  have addressValue : (word width countAddress).val = countAddress := Nat.mod_eq_of_lt addressFits
  have p1 : one.pc = word width (base + 1) := by
    simpa [one, State.put] using advance_pc s pc (by omega)
  have p2 : two.pc = word width (base + 2) := by
    simpa [two, State.put, Nat.add_assoc] using advance_pc one p1 (by omega)
  have p3 : ready.pc = word width (base + 3) := by
    simpa [ready, State.put, Nat.add_assoc] using advance_pc two p2 (by omega)
  have step0 : programStep program s = some one := by
    rw [fetchedInit program s base 0 markerBase countAddress (by simpa using pc) (by omega) (by decide) block]
    change step (.constant 3 (word width markerBase)) s = some one
    simp [step, one, running]
  have step1 : programStep program one = some two := by
    rw [fetchedInit program one base 1 markerBase countAddress p1 (by omega) (by decide) block]
    change step (.constant 0 (word width countAddress)) one = some two
    simp [step, one, two, State.advance, State.put, running]
  have step2 : programStep program two = some ready := by
    rw [fetchedInit program two base 2 markerBase countAddress p2 (by omega) (by decide) block]
    change step (.load 0 0) two = some ready
    simp [step, one, two, ready, State.advance, State.put, running, addressValue, storedCount, countWord]
  have l1 : one.liveWords = s.liveWords := rfl
  have l2 : two.liveWords = s.liveWords := rfl
  have l3 : ready.liveWords = s.liveWords := rfl
  refine ⟨ready, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, p3, ?_⟩
  · have trace := Execution.cons step0 (Execution.cons step1 (Execution.cons step2 (Execution.refl ready)))
    simpa only [l1, l2, l3, Nat.max_self] using trace
  all_goals simp [ready, two, one, State.advance, State.put, running]

private theorem fetchedPath (program : Program width 4) (s : State width 4)
    (base offset : ℕ) (layout : ForestWitnessPath.Layout)
    (pc : s.pc = word width (base + offset)) (fits : base + offset < 2 ^ width)
    (inside : offset < 54) (block : BlockAt program base (ForestWitnessPath.code width base layout)) :
    programStep program s = ((ForestWitnessPath.code width base layout)[offset]?).bind
      (fun instruction => step instruction s) := by
  unfold programStep
  rw [pc, show (word width (base + offset)).val = base + offset from Nat.mod_eq_of_lt fits,
    block offset (by simpa only [ForestWitnessPath.code_length] using inside)]
  rfl

/-- The node tag is fetched from the original stored header, using the
runtime current-node ID. The source and route stack remain unchanged. -/
theorem tag_read (program : Program width 4) (s : State width 4)
    (base : ℕ) (layout : ForestWitnessPath.Layout) (node tag : ℕ)
    (nodeHeld : s.reg 0 = word width node)
    (addressFits : layout.headerBase + 2 * node < 2 ^ width)
    (addressBound : layout.headerBase + 2 * node < s.heap.size)
    (storedTag : s.heap[layout.headerBase + 2 * node]'addressBound = word width tag)
    (pc : s.pc = word width base) (running : s.halted = false)
    (programFits : base + 54 < 2 ^ width)
    (block : BlockAt program base (ForestWitnessPath.code width base layout)) :
    ∃ ready, Execution program s ready 5 s.liveWords ∧
      ready.reg 0 = s.reg 0 ∧ ready.reg 1 = word width tag ∧
      ready.reg 2 = word width layout.headerBase ∧ ready.reg 3 = s.reg 3 ∧
      ready.heap = s.heap ∧ ready.stack = s.stack ∧ ready.output = s.output ∧
      ready.pc = word width (base + 5) ∧ ready.halted = false := by
  let one := s.advance.put 1 (word width node)
  let two := one.advance.put 1 (word width (node + node))
  let three := two.advance.put 2 (word width layout.headerBase)
  let four := three.advance.put 1 (word width (node + node + layout.headerBase))
  let ready := four.advance.put 1 (word width tag)
  have nodeValue : (word width node).val = node := Nat.mod_eq_of_lt (by omega)
  have doubleValue : (word width (node + node)).val = node + node := Nat.mod_eq_of_lt (by omega)
  have columnValue : (word width layout.headerBase).val = layout.headerBase := Nat.mod_eq_of_lt (by omega)
  have rowFits : node + node + layout.headerBase < 2 ^ width := by omega
  have rowValue : (word width (node + node + layout.headerBase)).val =
      node + node + layout.headerBase := Nat.mod_eq_of_lt rowFits
  have rowBound : node + node + layout.headerBase < s.heap.size := by omega
  have rowTag : s.heap[node + node + layout.headerBase]'rowBound = word width tag := by
    simpa only [two_mul, Nat.add_comm] using storedTag
  have p1 : one.pc = word width (base + 1) := by
    simpa [one, State.put] using advance_pc s (by simpa using pc) (by omega)
  have p2 : two.pc = word width (base + 2) := by
    simpa [two, State.put, Nat.add_assoc] using advance_pc one p1 (by omega)
  have p3 : three.pc = word width (base + 3) := by
    simpa [three, State.put, Nat.add_assoc] using advance_pc two p2 (by omega)
  have p4 : four.pc = word width (base + 4) := by
    simpa [four, State.put, Nat.add_assoc] using advance_pc three p3 (by omega)
  have p5 : ready.pc = word width (base + 5) := by
    simpa [ready, State.put, Nat.add_assoc] using advance_pc four p4 (by omega)
  have step0 : programStep program s = some one := by
    rw [fetchedPath program s base 0 layout (by simpa using pc) (by omega) (by decide) block]
    change step (.copy 1 0) s = some one
    simp [step, one, State.advance, State.put, running, nodeHeld,
      nodeValue, doubleValue, columnValue, rowValue, rowBound, rowTag]
  have step1 : programStep program one = some two := by
    rw [fetchedPath program one base 1 layout (p1) (by omega) (by decide) block]
    change step (.add 1 1 1) one = some two
    simp [step, one, two, State.advance, State.put, running, nodeHeld,
      nodeValue, doubleValue, columnValue, rowValue, rowBound, rowTag]
  have step2 : programStep program two = some three := by
    rw [fetchedPath program two base 2 layout (p2) (by omega) (by decide) block]
    change step (.constant 2 (word width layout.headerBase)) two = some three
    simp [step, one, two, three, State.advance, State.put, running, nodeHeld,
      nodeValue, doubleValue, columnValue, rowValue, rowBound, rowTag]
  have step3 : programStep program three = some four := by
    rw [fetchedPath program three base 3 layout (p3) (by omega) (by decide) block]
    change step (.add 1 1 2) three = some four
    simp [step, one, two, three, four, State.advance, State.put, running, nodeHeld,
      nodeValue, doubleValue, columnValue, rowValue, rowBound, rowTag]
  have step4 : programStep program four = some ready := by
    rw [fetchedPath program four base 4 layout (p4) (by omega) (by decide) block]
    change step (.load 1 1) four = some ready
    simp [step, one, two, three, four, ready, State.advance, State.put, running, nodeHeld,
      nodeValue, doubleValue, columnValue, rowValue, rowBound, rowTag]
  have l1 : one.liveWords = s.liveWords := rfl
  have l2 : two.liveWords = s.liveWords := rfl
  have l3 : three.liveWords = s.liveWords := rfl
  have l4 : four.liveWords = s.liveWords := rfl
  have l5 : ready.liveWords = s.liveWords := rfl
  refine ⟨ready, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, p5, ?_⟩
  · have trace := Execution.cons step0 (Execution.cons step1 (Execution.cons step2
      (Execution.cons step3 (Execution.cons step4 (Execution.refl ready)))))
    simpa only [l1, l2, l3, l4, l5, Nat.max_self] using trace
  all_goals simp [ready, four, three, two, one, State.advance, State.put, running]

/-- The input-tag branch performs four real dispatch instructions after
the stored tag read. Its modular decrement is checked at the declared width. -/
theorem dispatch_input (program : Program width 4) (s : State width 4)
    (base : ℕ) (layout : ForestWitnessPath.Layout)
    (tagHeld : s.reg 1 = word width 1) (pc : s.pc = word width (base + 5))
    (running : s.halted = false) (programFits : base + 54 < 2 ^ width)
    (block : BlockAt program base (ForestWitnessPath.code width base layout)) :
    ∃ ready, Execution program s ready 4 s.liveWords ∧
      ready.reg 0 = s.reg 0 ∧ ready.reg 3 = s.reg 3 ∧
      ready.heap = s.heap ∧ ready.stack = s.stack ∧ ready.output = s.output ∧
      ready.pc = word width (base + 46) ∧ ready.halted = false := by
  let one := s.advance
  let two := one.advance.put 2 (word width (2 ^ width - 1))
  let three := two.advance.put 1 (word width 0)
  let ready := { three.advance with pc := word width (base + 46) }
  have oneValue : (word width 1).val = 1 := Nat.mod_eq_of_lt (by omega)
  have minusValue : (word width (2 ^ width - 1)).val = 2 ^ width - 1 :=
    Nat.mod_eq_of_lt (by omega)
  have oneMod : 1 % 2 ^ width = 1 := Nat.mod_eq_of_lt (by omega)
  have minusMod : (2 ^ width - 1) % 2 ^ width = 2 ^ width - 1 := Nat.mod_eq_of_lt (by omega)
  have wrap : 1 + (2 ^ width - 1) = 2 ^ width := by omega
  have zeroWord : word width 0 = (0 : Word width) := by apply Fin.ext; simp [word]
  have p1 : one.pc = word width (base + 6) := by
    simpa [one, Nat.add_assoc] using advance_pc s pc (by omega)
  have p2 : two.pc = word width (base + 7) := by
    simpa [two, State.put, Nat.add_assoc] using advance_pc one p1 (by omega)
  have p3 : three.pc = word width (base + 8) := by
    simpa [three, State.put, Nat.add_assoc] using advance_pc two p2 (by omega)
  have step0 : programStep program s = some one := by
    rw [fetchedPath program s base 5 layout pc (by omega) (by decide) block]
    change step (.branchZero 1 (word width (base + 53))) s = some one
    simp [step, one, tagHeld, running, oneValue]
  have step1 : programStep program one = some two := by
    rw [fetchedPath program one base 6 layout p1 (by omega) (by decide) block]
    change step (.constant 2 (word width (2 ^ width - 1))) one = some two
    simp [step, one, two, State.advance, State.put, running]
  have step2 : programStep program two = some three := by
    rw [fetchedPath program two base 7 layout p2 (by omega) (by decide) block]
    change step (.add 1 1 2) two = some three
    simp [step, one, two, three, State.advance, State.put, running, tagHeld,
      oneValue, minusValue, oneMod, minusMod, wrap, word]
  have step3 : programStep program three = some ready := by
    rw [fetchedPath program three base 8 layout p3 (by omega) (by decide) block]
    change step (.branchZero 1 (word width (base + 46))) three = some ready
    simp [step, one, two, three, ready, State.advance, State.put, running, zeroWord]
  have l1 : one.liveWords = s.liveWords := rfl
  have l2 : two.liveWords = s.liveWords := rfl
  have l3 : three.liveWords = s.liveWords := rfl
  have l4 : ready.liveWords = s.liveWords := rfl
  refine ⟨ready, ?_, ?_, ?_, rfl, rfl, rfl, rfl, ?_⟩
  · have trace := Execution.cons step0 (Execution.cons step1
      (Execution.cons step2 (Execution.cons step3 (Execution.refl ready))))
    simpa only [l1, l2, l3, l4, Nat.max_self] using trace
  all_goals simp [ready, three, two, one, State.advance, State.put, running]

/-- Disjunction and guarded-child tags follow the same six comparison
instructions. Their concrete tag range comes from the guarded RoutePath. -/
theorem dispatch_child (program : Program width 4) (s : State width 4)
    (base : ℕ) (layout : ForestWitnessPath.Layout) (tag : ℕ)
    (tagRange : tag = 2 ∨ tag = 3) (tagHeld : s.reg 1 = word width tag)
    (pc : s.pc = word width (base + 5)) (running : s.halted = false)
    (programFits : base + 54 < 2 ^ width)
    (block : BlockAt program base (ForestWitnessPath.code width base layout)) :
    ∃ ready, Execution program s ready 6 s.liveWords ∧
      ready.reg 0 = s.reg 0 ∧ ready.reg 3 = s.reg 3 ∧
      ready.heap = s.heap ∧ ready.stack = s.stack ∧ ready.output = s.output ∧
      ready.pc = word width (base + if tag = 2 then 36 else 11) ∧ ready.halted = false := by
  let one := s.advance
  let two := one.advance.put 2 (word width (2 ^ width - 1))
  let three := two.advance.put 1 (word width (tag - 1))
  let four := three.advance
  let five := four.advance.put 1 (word width (tag - 2))
  let ready := if tag = 2 then { five.advance with pc := word width (base + 36) } else five.advance
  have tagFits : tag < 2 ^ width := by rcases tagRange with rfl | rfl <;> omega
  have tagValue : (word width tag).val = tag := Nat.mod_eq_of_lt tagFits
  have tagMod : tag % 2 ^ width = tag := Nat.mod_eq_of_lt tagFits
  have minusValue : (word width (2 ^ width - 1)).val = 2 ^ width - 1 := Nat.mod_eq_of_lt (by omega)
  have minusMod : (2 ^ width - 1) % 2 ^ width = 2 ^ width - 1 := Nat.mod_eq_of_lt (by omega)
  have firstValue : (word width (tag - 1)).val = tag - 1 := Nat.mod_eq_of_lt (by omega)
  have firstMod : (tag - 1) % 2 ^ width = tag - 1 := Nat.mod_eq_of_lt (by omega)
  have secondValue : (word width (tag - 2)).val = tag - 2 := Nat.mod_eq_of_lt (by omega)
  have secondMod : (tag - 2) % 2 ^ width = tag - 2 := Nat.mod_eq_of_lt (by omega)
  have firstArithmetic : (tag + (2 ^ width - 1)) % 2 ^ width = tag - 1 := by
    have rearrange : tag + (2 ^ width - 1) = (tag - 1) + 2 ^ width := by omega
    rw [rearrange, Nat.add_mod_right, firstMod]
  have secondArithmetic : ((tag - 1) + (2 ^ width - 1)) % 2 ^ width = tag - 2 := by
    have rearrange : (tag - 1) + (2 ^ width - 1) = (tag - 2) + 2 ^ width := by
      rcases tagRange with rfl | rfl <;> omega
    rw [rearrange, Nat.add_mod_right, secondMod]
  have positive : tag ≠ 0 := by rcases tagRange with rfl | rfl <;> decide
  have firstPositive : tag - 1 ≠ 0 := by rcases tagRange with rfl | rfl <;> decide
  have secondZero : tag - 2 = 0 ↔ tag = 2 := by rcases tagRange with rfl | rfl <;> decide
  have p1 : one.pc = word width (base + 6) := by
    simpa [one, Nat.add_assoc] using advance_pc s pc (by omega)
  have p2 : two.pc = word width (base + 7) := by
    simpa [two, State.put, Nat.add_assoc] using advance_pc one p1 (by omega)
  have p3 : three.pc = word width (base + 8) := by
    simpa [three, State.put, Nat.add_assoc] using advance_pc two p2 (by omega)
  have p4 : four.pc = word width (base + 9) := by
    simpa [four, Nat.add_assoc] using advance_pc three p3 (by omega)
  have p5 : five.pc = word width (base + 10) := by
    simpa [five, State.put, Nat.add_assoc] using advance_pc four p4 (by omega)
  have p6 : five.advance.pc = word width (base + 11) := by
    simpa [Nat.add_assoc] using advance_pc five p5 (by omega)
  have step0 : programStep program s = some one := by
    rw [fetchedPath program s base 5 layout pc (by omega) (by decide) block]
    change step (.branchZero 1 (word width (base + 53))) s = some one
    simp [step, one, State.advance, State.put, running, tagHeld, tagValue,
      minusValue, firstValue, secondValue, positive, firstPositive, secondZero,
      tagMod, minusMod, firstMod, secondMod, firstArithmetic, secondArithmetic, word]
  have step1 : programStep program one = some two := by
    rw [fetchedPath program one base 6 layout p1 (by omega) (by decide) block]
    change step (.constant 2 (word width (2 ^ width - 1))) one = some two
    simp [step, one, two, State.advance, State.put, running, tagHeld, tagValue,
      minusValue, firstValue, secondValue, positive, firstPositive, secondZero,
      tagMod, minusMod, firstMod, secondMod, firstArithmetic, secondArithmetic, word]
  have step2 : programStep program two = some three := by
    rw [fetchedPath program two base 7 layout p2 (by omega) (by decide) block]
    change step (.add 1 1 2) two = some three
    simp [step, one, two, three, State.advance, State.put, running, tagHeld, tagValue,
      minusValue, firstValue, secondValue, positive, firstPositive, secondZero,
      tagMod, minusMod, firstMod, secondMod, firstArithmetic, secondArithmetic, word]
  have step3 : programStep program three = some four := by
    rw [fetchedPath program three base 8 layout p3 (by omega) (by decide) block]
    change step (.branchZero 1 (word width (base + 46))) three = some four
    simp [step, one, two, three, four, State.advance, State.put, running, tagHeld, tagValue,
      minusValue, firstValue, secondValue, positive, firstPositive, secondZero,
      tagMod, minusMod, firstMod, secondMod, firstArithmetic, secondArithmetic, word]
  have step4 : programStep program four = some five := by
    rw [fetchedPath program four base 9 layout p4 (by omega) (by decide) block]
    change step (.add 1 1 2) four = some five
    simp [step, one, two, three, four, five, State.advance, State.put, running, tagHeld, tagValue,
      minusValue, firstValue, secondValue, positive, firstPositive, secondZero,
      tagMod, minusMod, firstMod, secondMod, firstArithmetic, secondArithmetic, word]
  have step5 : programStep program five = some ready := by
    rw [fetchedPath program five base 10 layout p5 (by omega) (by decide) block]
    change step (.branchZero 1 (word width (base + 36))) five = some ready
    simp [step, one, two, three, four, five, ready, State.advance, State.put, running, tagHeld, tagValue,
      minusValue, firstValue, secondValue, positive, firstPositive, secondZero,
      tagMod, minusMod, firstMod, secondMod, firstArithmetic, secondArithmetic, word]
  have l1 : one.liveWords = s.liveWords := rfl
  have l2 : two.liveWords = s.liveWords := rfl
  have l3 : three.liveWords = s.liveWords := rfl
  have l4 : four.liveWords = s.liveWords := rfl
  have l5 : five.liveWords = s.liveWords := rfl
  have l6 : ready.liveWords = s.liveWords := by
    unfold ready
    split <;> rfl
  have readyPC : ready.pc = word width (base + if tag = 2 then 36 else 11) := by
    unfold ready
    split
    · simp only [‹tag = 2›, ↓reduceIte]
    · simpa only [‹¬ tag = 2›, ↓reduceIte] using p6
  refine ⟨ready, ?_, ?_, ?_, ?_, ?_, ?_, readyPC, ?_⟩
  · have trace := Execution.cons step0 (Execution.cons step1 (Execution.cons step2
      (Execution.cons step3 (Execution.cons step4 (Execution.cons step5 (Execution.refl ready))))))
    simpa only [l1, l2, l3, l4, l5, l6, Nat.max_self] using trace
  all_goals by_cases isDisj : tag = 2 <;>
    simp [ready, five, four, three, two, one, State.advance, State.put, running, isDisj, p6]

/-- After the guard loop, three fetched instructions restore the saved node
and continue with the same selected-child block. The caller's positional stack
is exposed without constructing or copying a route. -/
theorem guard_finish (program : Program width 4) (s : State width 4)
    (base : ℕ) (layout : ForestWitnessPath.Layout) (node : ℕ)
    (suffix : List (Word width)) (saved : s.stack = word width node :: suffix)
    (pc : s.pc = word width (base + 33)) (running : s.halted = false)
    (programFits : base + 54 < 2 ^ width)
    (block : BlockAt program base (ForestWitnessPath.code width base layout)) :
    ∃ ready, Execution program s ready 3 s.liveWords ∧
      ready.reg 0 = word width node ∧ ready.reg 3 = s.reg 3 ∧
      ready.heap = s.heap ∧ ready.stack = suffix ∧ ready.output = s.output ∧
      ready.pc = word width (base + 36) ∧ ready.halted = false := by
  let one := { s.advance.put 0 (word width node) with stack := suffix }
  let two := one.advance.put 2 (word width 0)
  let ready := { two.advance with pc := word width (base + 36) }
  have zeroWord : word width 0 = (0 : Word width) := by apply Fin.ext; simp [word]
  have p1 : one.pc = word width (base + 34) := by
    simpa [one, State.put, Nat.add_assoc] using advance_pc s pc (by omega)
  have p2 : two.pc = word width (base + 35) := by
    simpa [two, State.put, Nat.add_assoc] using advance_pc one p1 (by omega)
  have step0 : programStep program s = some one := by
    rw [fetchedPath program s base 33 layout pc (by omega) (by decide) block]
    change step (.pop 0) s = some one
    simp [step, one, running, saved]
  have step1 : programStep program one = some two := by
    rw [fetchedPath program one base 34 layout p1 (by omega) (by decide) block]
    change step (.constant 2 (word width 0)) one = some two
    simp [step, one, two, State.advance, State.put, running]
  have step2 : programStep program two = some ready := by
    rw [fetchedPath program two base 35 layout p2 (by omega) (by decide) block]
    change step (.branchZero 2 (word width (base + 36))) two = some ready
    simp [step, one, two, ready, State.advance, State.put, running, zeroWord]
  have initialLive : s.liveWords = 6 + s.heap.size + suffix.length + s.output.length := by
    simp [State.liveWords, saved]; omega
  have l1 : one.liveWords = 5 + s.heap.size + suffix.length + s.output.length := by
    simp only [one, State.liveWords, State.advance, State.put]; omega
  have l2 : two.liveWords = one.liveWords := rfl
  have l3 : ready.liveWords = one.liveWords := rfl
  refine ⟨ready, ?_, ?_, ?_, rfl, rfl, rfl, rfl, ?_⟩
  · have trace := Execution.cons step0 (Execution.cons step1 (Execution.cons step2 (Execution.refl ready)))
    convert trace using 1 <;> simp only [initialLive, l2, l3, l1, Nat.max_self] <;> omega
  all_goals simp [ready, two, one, State.advance, State.put, running]

/-- The input exit fetches its original channel ID from the stored source
header. The reconstructed route stack is retained at this terminal. -/
theorem input_exit (program : Program width 4) (s : State width 4)
    (base : ℕ) (layout : ForestWitnessPath.Layout) (node : ℕ) (head : Channel n)
    (nodeHeld : s.reg 0 = word width node)
    (addressFits : layout.headerBase + 2 * node + 1 < 2 ^ width)
    (addressBound : layout.headerBase + 2 * node + 1 < s.heap.size)
    (storedHead : s.heap[layout.headerBase + 2 * node + 1]'addressBound = word width head.val)
    (pc : s.pc = word width (base + 46)) (running : s.halted = false)
    (programFits : base + 54 < 2 ^ width)
    (block : BlockAt program base (ForestWitnessPath.code width base layout)) :
    ∃ ready, Execution program s ready 7 s.liveWords ∧
      ready.reg 0 = word width head.val ∧ ready.reg 3 = s.reg 3 ∧
      ready.heap = s.heap ∧ ready.stack = s.stack ∧ ready.output = s.output ∧
      ready.pc = word width (base + 54) ∧ ready.halted = false := by
  let one := s.advance.put 1 (word width node)
  let two := one.advance.put 1 (word width (node + node))
  let three := two.advance.put 2 (word width (layout.headerBase + 1))
  let four := three.advance.put 1 (word width (node + node + (layout.headerBase + 1)))
  let five := four.advance.put 0 (word width head.val)
  let six := five.advance.put 2 (word width 0)
  let ready := { six.advance with pc := word width (base + 54) }
  have nodeValue : (word width node).val = node := Nat.mod_eq_of_lt (by omega)
  have doubleValue : (word width (node + node)).val = node + node := Nat.mod_eq_of_lt (by omega)
  have columnValue : (word width (layout.headerBase + 1)).val = layout.headerBase + 1 := Nat.mod_eq_of_lt (by omega)
  have rowFits : node + node + (layout.headerBase + 1) < 2 ^ width := by omega
  have rowValue : (word width (node + node + (layout.headerBase + 1))).val =
      node + node + (layout.headerBase + 1) := Nat.mod_eq_of_lt rowFits
  have rowBound : node + node + (layout.headerBase + 1) < s.heap.size := by omega
  have rowHead : s.heap[node + node + (layout.headerBase + 1)]'rowBound = word width head.val := by
    simpa only [two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using storedHead
  have zeroWord : word width 0 = (0 : Word width) := by apply Fin.ext; simp [word]
  have p1 : one.pc = word width (base + 47) := by
    simpa [one, State.put, Nat.add_assoc] using advance_pc s pc (by omega)
  have p2 : two.pc = word width (base + 48) := by
    simpa [two, State.put, Nat.add_assoc] using advance_pc one p1 (by omega)
  have p3 : three.pc = word width (base + 49) := by
    simpa [three, State.put, Nat.add_assoc] using advance_pc two p2 (by omega)
  have p4 : four.pc = word width (base + 50) := by
    simpa [four, State.put, Nat.add_assoc] using advance_pc three p3 (by omega)
  have p5 : five.pc = word width (base + 51) := by
    simpa [five, State.put, Nat.add_assoc] using advance_pc four p4 (by omega)
  have p6 : six.pc = word width (base + 52) := by
    simpa [six, State.put, Nat.add_assoc] using advance_pc five p5 (by omega)
  have step0 : programStep program s = some one := by
    rw [fetchedPath program s base 46 layout pc (by omega) (by decide) block]
    change step (.copy 1 0) s = some one
    simp [step, one, State.advance, State.put, running, nodeHeld,
      nodeValue, doubleValue, columnValue, rowValue, rowBound, rowHead, zeroWord]
  have step1 : programStep program one = some two := by
    rw [fetchedPath program one base 47 layout p1 (by omega) (by decide) block]
    change step (.add 1 1 1) one = some two
    simp [step, one, two, State.advance, State.put, running, nodeHeld,
      nodeValue, doubleValue, columnValue, rowValue, rowBound, rowHead, zeroWord]
  have step2 : programStep program two = some three := by
    rw [fetchedPath program two base 48 layout p2 (by omega) (by decide) block]
    change step (.constant 2 (word width (layout.headerBase + 1))) two = some three
    simp [step, one, two, three, State.advance, State.put, running, nodeHeld,
      nodeValue, doubleValue, columnValue, rowValue, rowBound, rowHead, zeroWord]
  have step3 : programStep program three = some four := by
    rw [fetchedPath program three base 49 layout p3 (by omega) (by decide) block]
    change step (.add 1 1 2) three = some four
    simp [step, one, two, three, four, State.advance, State.put, running, nodeHeld,
      nodeValue, doubleValue, columnValue, rowValue, rowBound, rowHead, zeroWord]
  have step4 : programStep program four = some five := by
    rw [fetchedPath program four base 50 layout p4 (by omega) (by decide) block]
    change step (.load 0 1) four = some five
    simp [step, one, two, three, four, five, State.advance, State.put, running, nodeHeld,
      nodeValue, doubleValue, columnValue, rowValue, rowBound, rowHead, zeroWord]
  have step5 : programStep program five = some six := by
    rw [fetchedPath program five base 51 layout p5 (by omega) (by decide) block]
    change step (.constant 2 (word width 0)) five = some six
    simp [step, one, two, three, four, five, six, State.advance, State.put, running, nodeHeld,
      nodeValue, doubleValue, columnValue, rowValue, rowBound, rowHead, zeroWord]
  have step6 : programStep program six = some ready := by
    rw [fetchedPath program six base 52 layout p6 (by omega) (by decide) block]
    change step (.branchZero 2 (word width (base + 54))) six = some ready
    simp [step, one, two, three, four, five, six, ready, State.advance, State.put, running, nodeHeld,
      nodeValue, doubleValue, columnValue, rowValue, rowBound, rowHead, zeroWord]
  have l1 : one.liveWords = s.liveWords := rfl
  have l2 : two.liveWords = s.liveWords := rfl
  have l3 : three.liveWords = s.liveWords := rfl
  have l4 : four.liveWords = s.liveWords := rfl
  have l5 : five.liveWords = s.liveWords := rfl
  have l6 : six.liveWords = s.liveWords := rfl
  have l7 : ready.liveWords = s.liveWords := rfl
  refine ⟨ready, ?_, ?_, ?_, rfl, rfl, rfl, rfl, ?_⟩
  · have trace := Execution.cons step0 (Execution.cons step1 (Execution.cons step2 (Execution.cons step3 (Execution.cons step4 (Execution.cons step5 (Execution.cons step6 (Execution.refl ready)))))))
    simpa only [l1, l2, l3, l4, l5, l6, l7, Nat.max_self] using trace
  all_goals simp [ready, six, five, four, three, two, one, State.advance, State.put, running]

/-- The complete terminal branch reads and dispatches the actual source
input node, then fetches its channel head. The gate equation excludes invalid
and live-AND tags structurally; no independent tag oracle is assumed. -/
theorem input_walk (program : Program width 4) (s : State width 4)
    (graph : DAG n) (records : GraphRecords width s.heap graph)
    (node : Fin graph.nodeCount) (head : Channel n)
    (gate : graph.node node = .input head) (base : ℕ)
    (layout : ForestWitnessPath.Layout) (header : layout.headerBase = records.recordBase)
    (nodeHeld : s.reg 0 = word width node.val)
    (pc : s.pc = word width base) (running : s.halted = false)
    (programFits : base + 54 < 2 ^ width) (heapFits : s.heap.size ≤ 2 ^ width)
    (block : BlockAt program base (ForestWitnessPath.code width base layout)) :
    ∃ final, Execution program s final 16 s.liveWords ∧
      final.reg 0 = word width head.val ∧ final.reg 3 = s.reg 3 ∧
      final.heap = s.heap ∧ final.stack = s.stack ∧ final.output = s.output ∧
      final.pc = word width (base + 54) ∧ final.halted = false := by
  have tagBound : layout.headerBase + 2 * node.val < s.heap.size := by
    simpa only [header] using records.tagValid node
  have tagCell : s.heap[layout.headerBase + 2 * node.val]'tagBound = word width 1 := by
    simpa only [header, gate] using records.tagWord node
  have headBound : layout.headerBase + 2 * node.val + 1 < s.heap.size := by
    simpa only [header] using records.headValid node
  have headCell : s.heap[layout.headerBase + 2 * node.val + 1]'headBound = word width head.val := by
    simpa only [header] using records.headWord node head gate
  obtain ⟨read, readTrace, readNode, readTag, readTemp, readSaved,
    readHeap, readStack, readOutput, readPC, readRunning⟩ :=
    tag_read program s base layout node.val 1 nodeHeld (by omega) tagBound tagCell
      pc running programFits block
  have readLive : read.liveWords = s.liveWords := by
    simp only [State.liveWords, readHeap, readStack, readOutput]
  obtain ⟨branch, branchTrace, branchNode, branchSaved, branchHeap,
    branchStack, branchOutput, branchPC, branchRunning⟩ :=
    dispatch_input program read base layout readTag readPC readRunning programFits block
  have branchLive : branch.liveWords = s.liveWords := by
    simp only [State.liveWords, branchHeap, branchStack, branchOutput, readHeap, readStack, readOutput]
  have branchHeld : branch.reg 0 = word width node.val :=
    branchNode.trans (readNode.trans nodeHeld)
  have branchHeadBound : layout.headerBase + 2 * node.val + 1 < branch.heap.size := by
    simpa only [branchHeap, readHeap] using headBound
  have branchHead : branch.heap[layout.headerBase + 2 * node.val + 1]'branchHeadBound = word width head.val := by
    simpa only [branchHeap, readHeap] using headCell
  obtain ⟨final, exitTrace, finalHead, finalSaved, finalHeap, finalStack,
    finalOutput, finalPC, finalRunning⟩ :=
    input_exit program branch base layout node.val head branchHeld (by omega)
      branchHeadBound branchHead branchPC branchRunning programFits block
  refine ⟨final, ?_, finalHead,
    finalSaved.trans (branchSaved.trans readSaved),
    finalHeap.trans (branchHeap.trans readHeap),
    finalStack.trans (branchStack.trans readStack),
    finalOutput.trans (branchOutput.trans readOutput), finalPC, finalRunning⟩
  have joined := (readTrace.append branchTrace).append exitTrace
  simpa only [readLive, branchLive, Nat.max_self] using joined

/-- The full disjunction step uses the reconstructed positional stack and
reads the selected occurrence from the original child stream. The source tag
is derived from the represented gate; the base word is an actual stored cell. -/
theorem disj_step (program : Program width 4) (s : State width 4)
    (graph : DAG n) (records : GraphRecords width s.heap graph)
    (node : Fin graph.nodeCount) (refs : List (Fin node.val))
    (gate : graph.node node = .disj refs) (position : Fin (graph.node node).children.length)
    (suffix : List (Word width)) (base : ℕ) (layout : ForestWitnessPath.Layout)
    (header : layout.headerBase = records.recordBase)
    (nodeHeld : s.reg 0 = word width node.val)
    (positions : s.stack = word width position.val :: suffix)
    (baseBound : layout.childrenBaseColumn + 2 * node.val < s.heap.size)
    (baseCell : s.heap[layout.childrenBaseColumn + 2 * node.val]'baseBound =
      word width (records.childBase node))
    (pc : s.pc = word width base) (running : s.halted = false)
    (programFits : base + 54 < 2 ^ width) (heapFits : s.heap.size ≤ 2 ^ width)
    (block : BlockAt program base (ForestWitnessPath.code width base layout)) :
    ∃ final, Execution program s final 21 s.liveWords ∧
      final.reg 0 = word width ((graph.node node).children.get position).val ∧
      final.heap = s.heap ∧ final.stack = suffix ∧ final.output = s.output ∧
      final.pc = word width base ∧ final.halted = false := by
  have tagBound : layout.headerBase + 2 * node.val < s.heap.size := by
    simpa only [header] using records.tagValid node
  have tagCell : s.heap[layout.headerBase + 2 * node.val]'tagBound = word width 2 := by
    simpa only [header, gate] using records.tagWord node
  obtain ⟨read, readTrace, readNode, readTag, readTemp, readSaved,
    readHeap, readStack, readOutput, readPC, readRunning⟩ :=
    tag_read program s base layout node.val 2 nodeHeld (by omega) tagBound tagCell
      pc running programFits block
  have readLive : read.liveWords = s.liveWords := by
    simp only [State.liveWords, readHeap, readStack, readOutput]
  obtain ⟨branch, branchTrace, branchNode, branchSaved, branchHeap,
    branchStack, branchOutput, branchPC, branchRunning⟩ :=
    dispatch_child program read base layout 2 (Or.inl rfl) readTag readPC readRunning programFits block
  have branchLive : branch.liveWords = s.liveWords := by
    simp only [State.liveWords, branchHeap, branchStack, branchOutput, readHeap, readStack, readOutput]
  have branchHeld : branch.reg 0 = word width node.val := branchNode.trans (readNode.trans nodeHeld)
  have branchPositions : branch.stack = word width position.val :: suffix :=
    branchStack.trans (readStack.trans positions)
  have branchBaseBound : layout.childrenBaseColumn + 2 * node.val < branch.heap.size := by
    simpa only [branchHeap, readHeap] using baseBound
  have branchBase : branch.heap[layout.childrenBaseColumn + 2 * node.val]'branchBaseBound =
      word width (records.childBase node) := by
    simpa only [branchHeap, readHeap] using baseCell
  have childBound : records.childBase node + position.val < s.heap.size := records.childValid node position
  have branchChildBound : records.childBase node + position.val < branch.heap.size := by
    simpa only [branchHeap, readHeap] using childBound
  have branchChild : branch.heap[records.childBase node + position.val]'branchChildBound =
      word width ((graph.node node).children.get position).val := by
    simpa only [branchHeap, readHeap] using records.childWord node position
  obtain ⟨final, childTrace, finalChild, finalPosition, finalHeap, finalStack,
    finalOutput, finalPC, finalRunning⟩ :=
    ForestWitnessPath.child_execution program branch base layout node.val position.val
      (records.childBase node) ((graph.node node).children.get position).val suffix
      branchHeld branchPositions (by omega) (by omega) branchBaseBound branchChildBound
      branchBase branchChild (by simpa using branchPC) branchRunning programFits block
  refine ⟨final, ?_, finalChild, finalHeap.trans (branchHeap.trans readHeap), finalStack,
    finalOutput.trans (branchOutput.trans readOutput), finalPC, finalRunning⟩
  have joined := (readTrace.append branchTrace).append childTrace
  simpa only [readLive, branchLive, Nat.max_self] using joined

private theorem physical_state_eq (s t : State width 4)
    (registers : s.reg = t.reg) (heap : s.heap = t.heap) (stack : s.stack = t.stack)
    (output : s.output = t.output) (pc : s.pc = t.pc) (halted : s.halted = t.halted) : s = t := by
  cases s
  cases t
  simp_all only [State.mk.injEq]

/-- Guard setup saves the runtime node and reads its actual stored arity
and guard-stream base. The extra stack word is charged until guard completion. -/
private theorem guard_setup_prefix (program : Program width 4) (s : State width 4)
    (base : ℕ) (layout : ForestWitnessPath.Layout) (node count cursor : ℕ)
    (nodeHeld : s.reg 0 = word width node)
    (arityFits : layout.arityBaseColumn + 2 * node + 1 < 2 ^ width)
    (streamFits : layout.childrenBaseColumn + 2 * node + 1 < 2 ^ width)
    (arityBound : layout.arityBaseColumn + 2 * node + 1 < s.heap.size)
    (streamBound : layout.childrenBaseColumn + 2 * node + 1 < s.heap.size)
    (arityCell : s.heap[layout.arityBaseColumn + 2 * node + 1]'arityBound = word width count)
    (streamCell : s.heap[layout.childrenBaseColumn + 2 * node + 1]'streamBound = word width cursor)
    (pc : s.pc = word width (base + 11)) (running : s.halted = false)
    (programFits : base + 54 < 2 ^ width)
    (block : BlockAt program base (ForestWitnessPath.code width base layout)) :
    Execution program (s) (UniformDAGScan.state s.heap (base + 15) (word width node) (word width (node + node)) (word width (layout.arityBaseColumn + 1)) (s.reg 3) (word width node :: s.stack) s.output) 4 (s.liveWords + 1) := by
  have nodeValue : (word width node).val = node := Nat.mod_eq_of_lt (by omega)
  have doubleValue : (word width (node + node)).val = node + node := Nat.mod_eq_of_lt (by omega)
  have arityColumn : (word width (layout.arityBaseColumn + 1)).val = layout.arityBaseColumn + 1 :=
    Nat.mod_eq_of_lt (by omega)
  have streamColumn : (word width (layout.childrenBaseColumn + 1)).val = layout.childrenBaseColumn + 1 :=
    Nat.mod_eq_of_lt (by omega)
  have arityAddress : (word width (node + node + (layout.arityBaseColumn + 1))).val =
      node + node + (layout.arityBaseColumn + 1) := Nat.mod_eq_of_lt (by omega)
  have streamAddress : (word width (node + node + (layout.childrenBaseColumn + 1))).val =
      node + node + (layout.childrenBaseColumn + 1) := Nat.mod_eq_of_lt (by omega)
  have arityValid : node + node + (layout.arityBaseColumn + 1) < s.heap.size := by omega
  have streamValid : node + node + (layout.childrenBaseColumn + 1) < s.heap.size := by omega
  have arityStored : s.heap[node + node + (layout.arityBaseColumn + 1)]'arityValid = word width count := by
    simpa only [two_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using arityCell
  have streamStored : s.heap[node + node + (layout.childrenBaseColumn + 1)]'streamValid = word width cursor := by
    simpa only [two_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using streamCell
  let one := UniformDAGScan.state s.heap (base + 12) (word width node) (s.reg 1) (s.reg 2) (s.reg 3) (word width node :: s.stack) s.output
  let two := UniformDAGScan.state s.heap (base + 13) (word width node) (word width node) (s.reg 2) (s.reg 3) (word width node :: s.stack) s.output
  let three := UniformDAGScan.state s.heap (base + 14) (word width node) (word width (node + node)) (s.reg 2) (s.reg 3) (word width node :: s.stack) s.output
  let four := UniformDAGScan.state s.heap (base + 15) (word width node) (word width (node + node)) (word width (layout.arityBaseColumn + 1)) (s.reg 3) (word width node :: s.stack) s.output
  have pc11 : (base + 11) % 2 ^ width = base + 11 := Nat.mod_eq_of_lt (by omega)
  have pc12 : (base + 12) % 2 ^ width = base + 12 := Nat.mod_eq_of_lt (by omega)
  have pc13 : (base + 13) % 2 ^ width = base + 13 := Nat.mod_eq_of_lt (by omega)
  have pc14 : (base + 14) % 2 ^ width = base + 14 := Nat.mod_eq_of_lt (by omega)
  have pcWord11 : (word width (base + 11)).val = base + 11 := Nat.mod_eq_of_lt (by omega)
  have pcWord12 : (word width (base + 12)).val = base + 12 := Nat.mod_eq_of_lt (by omega)
  have pcWord13 : (word width (base + 13)).val = base + 13 := Nat.mod_eq_of_lt (by omega)
  have pcWord14 : (word width (base + 14)).val = base + 14 := Nat.mod_eq_of_lt (by omega)
  have step0 : programStep program s = some one := by
    rw [fetchedPath program s base 11 layout pc (by omega) (by decide) block]
    change step (.push 0) s = some one
    simp [step, one, one, UniformDAGScan.state, State.advance, State.put,
      running, nodeHeld, pc, pc11, nodeValue, doubleValue, arityColumn,
      streamColumn, arityAddress, streamAddress, arityValid, streamValid,
      arityStored, streamStored, Nat.add_assoc]
    all_goals
      constructor
      · funext register
        fin_cases register <;> simp [nodeHeld]
      · simp only [pcWord11, pcWord12, pcWord13, pcWord14] <;>
          exact congrArg (word width) (by omega)
  have step1 : programStep program one = some two := by
    rw [fetchedPath program one base 12 layout (by rfl) (by omega) (by decide) block]
    change step (.copy 1 0) one = some two
    simp [step, two, one, UniformDAGScan.state, State.advance, State.put,
      running, nodeHeld, pc, pc12, nodeValue, doubleValue, arityColumn,
      streamColumn, arityAddress, streamAddress, arityValid, streamValid,
      arityStored, streamStored, Nat.add_assoc]
    all_goals
      constructor
      · funext register
        fin_cases register <;> simp [nodeHeld]
      · simp only [pcWord11, pcWord12, pcWord13, pcWord14] <;>
          exact congrArg (word width) (by omega)
  have step2 : programStep program two = some three := by
    rw [fetchedPath program two base 13 layout (by rfl) (by omega) (by decide) block]
    change step (.add 1 1 1) two = some three
    simp [step, three, two, UniformDAGScan.state, State.advance, State.put,
      running, nodeHeld, pc, pc13, nodeValue, doubleValue, arityColumn,
      streamColumn, arityAddress, streamAddress, arityValid, streamValid,
      arityStored, streamStored, Nat.add_assoc]
    all_goals
      constructor
      · funext register
        fin_cases register <;> simp [nodeHeld]
      · simp only [pcWord11, pcWord12, pcWord13, pcWord14] <;>
          exact congrArg (word width) (by omega)
  have step3 : programStep program three = some four := by
    rw [fetchedPath program three base 14 layout (by rfl) (by omega) (by decide) block]
    change step (.constant 2 (word width (layout.arityBaseColumn + 1))) three = some four
    simp [step, four, three, UniformDAGScan.state, State.advance, State.put,
      running, nodeHeld, pc, pc14, nodeValue, doubleValue, arityColumn,
      streamColumn, arityAddress, streamAddress, arityValid, streamValid,
      arityStored, streamStored, Nat.add_assoc]
    all_goals
      constructor
      · funext register
        fin_cases register <;> simp [nodeHeld]
      · simp only [pcWord11, pcWord12, pcWord13, pcWord14] <;>
          exact congrArg (word width) (by omega)
  have l1 : one.liveWords = s.liveWords + 1 := by
    simp [State.liveWords, UniformDAGScan.state, one]; omega
  have l2 : two.liveWords = s.liveWords + 1 := by
    simp [State.liveWords, UniformDAGScan.state, two]; omega
  have l3 : three.liveWords = s.liveWords + 1 := by
    simp [State.liveWords, UniformDAGScan.state, three]; omega
  have l4 : four.liveWords = s.liveWords + 1 := by
    simp [State.liveWords, UniformDAGScan.state, four]; omega
  have joined := Execution.cons step0 (Execution.cons step1 (Execution.cons step2 (Execution.cons step3 (Execution.refl four))))
  convert joined using 1 <;> simp only [l1, l2, l3, l4, Nat.max_self] <;> omega

private theorem guard_setup_middle (program : Program width 4) (s : State width 4)
    (base : ℕ) (layout : ForestWitnessPath.Layout) (node count cursor : ℕ)
    (nodeHeld : s.reg 0 = word width node)
    (arityFits : layout.arityBaseColumn + 2 * node + 1 < 2 ^ width)
    (streamFits : layout.childrenBaseColumn + 2 * node + 1 < 2 ^ width)
    (arityBound : layout.arityBaseColumn + 2 * node + 1 < s.heap.size)
    (streamBound : layout.childrenBaseColumn + 2 * node + 1 < s.heap.size)
    (arityCell : s.heap[layout.arityBaseColumn + 2 * node + 1]'arityBound = word width count)
    (streamCell : s.heap[layout.childrenBaseColumn + 2 * node + 1]'streamBound = word width cursor)
    (pc : s.pc = word width (base + 11)) (running : s.halted = false)
    (programFits : base + 54 < 2 ^ width)
    (block : BlockAt program base (ForestWitnessPath.code width base layout)) :
    Execution program (UniformDAGScan.state s.heap (base + 15) (word width node) (word width (node + node)) (word width (layout.arityBaseColumn + 1)) (s.reg 3) (word width node :: s.stack) s.output) (UniformDAGScan.state s.heap (base + 19) (word width node) (word width (node + node)) (word width (layout.arityBaseColumn + 1)) (word width count) (word width node :: s.stack) s.output) 4 (s.liveWords + 1) := by
  have nodeValue : (word width node).val = node := Nat.mod_eq_of_lt (by omega)
  have doubleValue : (word width (node + node)).val = node + node := Nat.mod_eq_of_lt (by omega)
  have arityColumn : (word width (layout.arityBaseColumn + 1)).val = layout.arityBaseColumn + 1 :=
    Nat.mod_eq_of_lt (by omega)
  have streamColumn : (word width (layout.childrenBaseColumn + 1)).val = layout.childrenBaseColumn + 1 :=
    Nat.mod_eq_of_lt (by omega)
  have arityAddress : (word width (node + node + (layout.arityBaseColumn + 1))).val =
      node + node + (layout.arityBaseColumn + 1) := Nat.mod_eq_of_lt (by omega)
  have streamAddress : (word width (node + node + (layout.childrenBaseColumn + 1))).val =
      node + node + (layout.childrenBaseColumn + 1) := Nat.mod_eq_of_lt (by omega)
  have arityValid : node + node + (layout.arityBaseColumn + 1) < s.heap.size := by omega
  have streamValid : node + node + (layout.childrenBaseColumn + 1) < s.heap.size := by omega
  have arityStored : s.heap[node + node + (layout.arityBaseColumn + 1)]'arityValid = word width count := by
    simpa only [two_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using arityCell
  have streamStored : s.heap[node + node + (layout.childrenBaseColumn + 1)]'streamValid = word width cursor := by
    simpa only [two_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using streamCell
  let four := UniformDAGScan.state s.heap (base + 15) (word width node) (word width (node + node)) (word width (layout.arityBaseColumn + 1)) (s.reg 3) (word width node :: s.stack) s.output
  let five := UniformDAGScan.state s.heap (base + 16) (word width node) (word width (node + node + (layout.arityBaseColumn + 1))) (word width (layout.arityBaseColumn + 1)) (s.reg 3) (word width node :: s.stack) s.output
  let six := UniformDAGScan.state s.heap (base + 17) (word width node) (word width (node + node + (layout.arityBaseColumn + 1))) (word width (layout.arityBaseColumn + 1)) (word width count) (word width node :: s.stack) s.output
  let seven := UniformDAGScan.state s.heap (base + 18) (word width node) (word width node) (word width (layout.arityBaseColumn + 1)) (word width count) (word width node :: s.stack) s.output
  let eight := UniformDAGScan.state s.heap (base + 19) (word width node) (word width (node + node)) (word width (layout.arityBaseColumn + 1)) (word width count) (word width node :: s.stack) s.output
  have pc15 : (base + 15) % 2 ^ width = base + 15 := Nat.mod_eq_of_lt (by omega)
  have pc16 : (base + 16) % 2 ^ width = base + 16 := Nat.mod_eq_of_lt (by omega)
  have pc17 : (base + 17) % 2 ^ width = base + 17 := Nat.mod_eq_of_lt (by omega)
  have pc18 : (base + 18) % 2 ^ width = base + 18 := Nat.mod_eq_of_lt (by omega)
  have pcWord15 : (word width (base + 15)).val = base + 15 := Nat.mod_eq_of_lt (by omega)
  have pcWord16 : (word width (base + 16)).val = base + 16 := Nat.mod_eq_of_lt (by omega)
  have pcWord17 : (word width (base + 17)).val = base + 17 := Nat.mod_eq_of_lt (by omega)
  have pcWord18 : (word width (base + 18)).val = base + 18 := Nat.mod_eq_of_lt (by omega)
  have step4 : programStep program four = some five := by
    rw [fetchedPath program four base 15 layout (by rfl) (by omega) (by decide) block]
    change step (.add 1 1 2) four = some five
    simp [step, five, four, UniformDAGScan.state, State.advance, State.put,
      running, nodeHeld, pc, pc15, nodeValue, doubleValue, arityColumn,
      streamColumn, arityAddress, streamAddress, arityValid, streamValid,
      arityStored, streamStored, Nat.add_assoc]
    all_goals
      constructor
      · funext register
        fin_cases register <;> simp [nodeHeld]
      · simp only [pcWord15, pcWord16,
            pcWord17, pcWord18] <;>
          exact congrArg (word width) (by omega)
  have arityNormalized : (word width (node + (node + (layout.arityBaseColumn + 1)))).val =
      node + (node + (layout.arityBaseColumn + 1)) := by simpa only [Nat.add_assoc] using arityAddress
  have arityNormalizedValid : node + (node + (layout.arityBaseColumn + 1)) < s.heap.size := by
    simpa only [Nat.add_assoc] using arityValid
  have arityNormalizedStored : s.heap[node + (node + (layout.arityBaseColumn + 1))]'(arityNormalizedValid) = word width count := by
    simpa only [Nat.add_assoc] using arityStored
  have step5 : programStep program five = some six := by
    rw [fetchedPath program five base 16 layout (by rfl) (by omega) (by decide) block]
    change step (.load 3 1) five = some six
    simp [step, six, five, UniformDAGScan.state, State.advance, State.put,
      running, nodeHeld, pc, pc16, nodeValue, doubleValue, arityColumn,
      streamColumn, arityAddress, streamAddress, arityValid, streamValid,
      arityStored, streamStored, arityNormalized, arityNormalizedValid, arityNormalizedStored, Nat.add_assoc]
    all_goals
      constructor
      · funext register
        fin_cases register <;> simp [nodeHeld]
      · simp only [pcWord15, pcWord16,
            pcWord17, pcWord18] <;>
          exact congrArg (word width) (by omega)
  have step6 : programStep program six = some seven := by
    rw [fetchedPath program six base 17 layout (by rfl) (by omega) (by decide) block]
    change step (.copy 1 0) six = some seven
    simp [step, seven, six, UniformDAGScan.state, State.advance, State.put,
      running, nodeHeld, pc, pc17, nodeValue, doubleValue, arityColumn,
      streamColumn, arityAddress, streamAddress, arityValid, streamValid,
      arityStored, streamStored, Nat.add_assoc]
    all_goals
      constructor
      · funext register
        fin_cases register <;> simp [nodeHeld]
      · simp only [pcWord15, pcWord16,
            pcWord17, pcWord18] <;>
          exact congrArg (word width) (by omega)
  have step7 : programStep program seven = some eight := by
    rw [fetchedPath program seven base 18 layout (by rfl) (by omega) (by decide) block]
    change step (.add 1 1 1) seven = some eight
    simp [step, eight, seven, UniformDAGScan.state, State.advance, State.put,
      running, nodeHeld, pc, pc18, nodeValue, doubleValue, arityColumn,
      streamColumn, arityAddress, streamAddress, arityValid, streamValid,
      arityStored, streamStored, Nat.add_assoc]
    all_goals
      constructor
      · funext register
        fin_cases register <;> simp [nodeHeld]
      · simp only [pcWord15, pcWord16,
            pcWord17, pcWord18] <;>
          exact congrArg (word width) (by omega)
  have l4 : four.liveWords = s.liveWords + 1 := by
    simp [State.liveWords, UniformDAGScan.state, four]; omega
  have l5 : five.liveWords = s.liveWords + 1 := by
    simp [State.liveWords, UniformDAGScan.state, five]; omega
  have l6 : six.liveWords = s.liveWords + 1 := by
    simp [State.liveWords, UniformDAGScan.state, six]; omega
  have l7 : seven.liveWords = s.liveWords + 1 := by
    simp [State.liveWords, UniformDAGScan.state, seven]; omega
  have l8 : eight.liveWords = s.liveWords + 1 := by
    simp [State.liveWords, UniformDAGScan.state, eight]; omega
  have joined := Execution.cons step4 (Execution.cons step5 (Execution.cons step6 (Execution.cons step7 (Execution.refl eight))))
  convert joined using 1 <;> simp only [l4, l5, l6, l7, l8, Nat.max_self] <;> omega

private theorem guard_setup_tail (program : Program width 4) (s : State width 4)
    (base : ℕ) (layout : ForestWitnessPath.Layout) (node count cursor : ℕ)
    (nodeHeld : s.reg 0 = word width node)
    (arityFits : layout.arityBaseColumn + 2 * node + 1 < 2 ^ width)
    (streamFits : layout.childrenBaseColumn + 2 * node + 1 < 2 ^ width)
    (arityBound : layout.arityBaseColumn + 2 * node + 1 < s.heap.size)
    (streamBound : layout.childrenBaseColumn + 2 * node + 1 < s.heap.size)
    (arityCell : s.heap[layout.arityBaseColumn + 2 * node + 1]'arityBound = word width count)
    (streamCell : s.heap[layout.childrenBaseColumn + 2 * node + 1]'streamBound = word width cursor)
    (pc : s.pc = word width (base + 11)) (running : s.halted = false)
    (programFits : base + 54 < 2 ^ width)
    (block : BlockAt program base (ForestWitnessPath.code width base layout)) :
    Execution program (UniformDAGScan.state s.heap (base + 19) (word width node) (word width (node + node)) (word width (layout.arityBaseColumn + 1)) (word width count) (word width node :: s.stack) s.output) (UniformDAGScan.state s.heap (base + 22) (word width cursor) (word width (node + node + (layout.childrenBaseColumn + 1))) (word width (layout.childrenBaseColumn + 1)) (word width count) (word width node :: s.stack) s.output) 3 (s.liveWords + 1) := by
  have nodeValue : (word width node).val = node := Nat.mod_eq_of_lt (by omega)
  have doubleValue : (word width (node + node)).val = node + node := Nat.mod_eq_of_lt (by omega)
  have arityColumn : (word width (layout.arityBaseColumn + 1)).val = layout.arityBaseColumn + 1 :=
    Nat.mod_eq_of_lt (by omega)
  have streamColumn : (word width (layout.childrenBaseColumn + 1)).val = layout.childrenBaseColumn + 1 :=
    Nat.mod_eq_of_lt (by omega)
  have arityAddress : (word width (node + node + (layout.arityBaseColumn + 1))).val =
      node + node + (layout.arityBaseColumn + 1) := Nat.mod_eq_of_lt (by omega)
  have streamAddress : (word width (node + node + (layout.childrenBaseColumn + 1))).val =
      node + node + (layout.childrenBaseColumn + 1) := Nat.mod_eq_of_lt (by omega)
  have arityValid : node + node + (layout.arityBaseColumn + 1) < s.heap.size := by omega
  have streamValid : node + node + (layout.childrenBaseColumn + 1) < s.heap.size := by omega
  have arityStored : s.heap[node + node + (layout.arityBaseColumn + 1)]'arityValid = word width count := by
    simpa only [two_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using arityCell
  have streamStored : s.heap[node + node + (layout.childrenBaseColumn + 1)]'streamValid = word width cursor := by
    simpa only [two_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using streamCell
  let eight := UniformDAGScan.state s.heap (base + 19) (word width node) (word width (node + node)) (word width (layout.arityBaseColumn + 1)) (word width count) (word width node :: s.stack) s.output
  let nine := UniformDAGScan.state s.heap (base + 20) (word width node) (word width (node + node)) (word width (layout.childrenBaseColumn + 1)) (word width count) (word width node :: s.stack) s.output
  let ten := UniformDAGScan.state s.heap (base + 21) (word width node) (word width (node + node + (layout.childrenBaseColumn + 1))) (word width (layout.childrenBaseColumn + 1)) (word width count) (word width node :: s.stack) s.output
  let ready := UniformDAGScan.state s.heap (base + 22) (word width cursor) (word width (node + node + (layout.childrenBaseColumn + 1))) (word width (layout.childrenBaseColumn + 1)) (word width count) (word width node :: s.stack) s.output
  have pc19 : (base + 19) % 2 ^ width = base + 19 := Nat.mod_eq_of_lt (by omega)
  have pc20 : (base + 20) % 2 ^ width = base + 20 := Nat.mod_eq_of_lt (by omega)
  have pc21 : (base + 21) % 2 ^ width = base + 21 := Nat.mod_eq_of_lt (by omega)
  have pcWord19 : (word width (base + 19)).val = base + 19 := Nat.mod_eq_of_lt (by omega)
  have pcWord20 : (word width (base + 20)).val = base + 20 := Nat.mod_eq_of_lt (by omega)
  have pcWord21 : (word width (base + 21)).val = base + 21 := Nat.mod_eq_of_lt (by omega)
  have step8 : programStep program eight = some nine := by
    rw [fetchedPath program eight base 19 layout (by rfl) (by omega) (by decide) block]
    change step (.constant 2 (word width (layout.childrenBaseColumn + 1))) eight = some nine
    simp [step, nine, eight, UniformDAGScan.state, State.advance, State.put,
      running, nodeHeld, pc, pc19, nodeValue, doubleValue, arityColumn,
      streamColumn, arityAddress, streamAddress, arityValid, streamValid,
      arityStored, streamStored, Nat.add_assoc]
    all_goals
      constructor
      · funext register
        fin_cases register <;> simp [nodeHeld]
      · simp only [pcWord19, pcWord20, pcWord21] <;>
          exact congrArg (word width) (by omega)
  have step9 : programStep program nine = some ten := by
    rw [fetchedPath program nine base 20 layout (by rfl) (by omega) (by decide) block]
    change step (.add 1 1 2) nine = some ten
    simp [step, ten, nine, UniformDAGScan.state, State.advance, State.put,
      running, nodeHeld, pc, pc20, nodeValue, doubleValue, arityColumn,
      streamColumn, arityAddress, streamAddress, arityValid, streamValid,
      arityStored, streamStored, Nat.add_assoc]
    all_goals
      constructor
      · funext register
        fin_cases register <;> simp [nodeHeld]
      · simp only [pcWord19, pcWord20, pcWord21] <;>
          exact congrArg (word width) (by omega)
  have streamNormalized : (word width (node + (node + (layout.childrenBaseColumn + 1)))).val =
      node + (node + (layout.childrenBaseColumn + 1)) := by simpa only [Nat.add_assoc] using streamAddress
  have streamNormalizedValid : node + (node + (layout.childrenBaseColumn + 1)) < s.heap.size := by
    simpa only [Nat.add_assoc] using streamValid
  have streamNormalizedStored : s.heap[node + (node + (layout.childrenBaseColumn + 1))]'(streamNormalizedValid) = word width cursor := by
    simpa only [Nat.add_assoc] using streamStored
  have step10 : programStep program ten = some ready := by
    rw [fetchedPath program ten base 21 layout (by rfl) (by omega) (by decide) block]
    change step (.load 0 1) ten = some ready
    simp [step, ready, ten, UniformDAGScan.state, State.advance, State.put,
      running, nodeHeld, pc, pc21, nodeValue, doubleValue, arityColumn,
      streamColumn, arityAddress, streamAddress, arityValid, streamValid,
      arityStored, streamStored, streamNormalized, streamNormalizedValid, streamNormalizedStored, Nat.add_assoc]
    all_goals
      constructor
      · funext register
        fin_cases register <;> simp [nodeHeld]
      · simp only [pcWord19, pcWord20, pcWord21] <;>
          exact congrArg (word width) (by omega)
  have l8 : eight.liveWords = s.liveWords + 1 := by
    simp [State.liveWords, UniformDAGScan.state, eight]; omega
  have l9 : nine.liveWords = s.liveWords + 1 := by
    simp [State.liveWords, UniformDAGScan.state, nine]; omega
  have l10 : ten.liveWords = s.liveWords + 1 := by
    simp [State.liveWords, UniformDAGScan.state, ten]; omega
  have l11 : ready.liveWords = s.liveWords + 1 := by
    simp [State.liveWords, UniformDAGScan.state, ready]; omega
  have joined := Execution.cons step8 (Execution.cons step9 (Execution.cons step10 (Execution.refl ready)))
  convert joined using 1 <;> simp only [l8, l9, l10, l11, Nat.max_self] <;> omega

theorem guard_setup (program : Program width 4) (s : State width 4)
    (base : ℕ) (layout : ForestWitnessPath.Layout) (node count cursor : ℕ)
    (nodeHeld : s.reg 0 = word width node)
    (arityFits : layout.arityBaseColumn + 2 * node + 1 < 2 ^ width)
    (streamFits : layout.childrenBaseColumn + 2 * node + 1 < 2 ^ width)
    (arityBound : layout.arityBaseColumn + 2 * node + 1 < s.heap.size)
    (streamBound : layout.childrenBaseColumn + 2 * node + 1 < s.heap.size)
    (arityCell : s.heap[layout.arityBaseColumn + 2 * node + 1]'arityBound = word width count)
    (streamCell : s.heap[layout.childrenBaseColumn + 2 * node + 1]'streamBound = word width cursor)
    (pc : s.pc = word width (base + 11)) (running : s.halted = false)
    (programFits : base + 54 < 2 ^ width)
    (block : BlockAt program base (ForestWitnessPath.code width base layout)) :
    Execution program s
      (UniformDAGScan.state s.heap (base + 22) (word width cursor)
        (word width (node + node + (layout.childrenBaseColumn + 1)))
        (word width (layout.childrenBaseColumn + 1)) (word width count)
        (word width node :: s.stack) s.output)
      11 (s.liveWords + 1) := by
  have first := guard_setup_prefix program s base layout node count cursor nodeHeld arityFits streamFits arityBound streamBound arityCell streamCell pc running programFits block
  have second := guard_setup_middle program s base layout node count cursor nodeHeld arityFits streamFits arityBound streamBound arityCell streamCell pc running programFits block
  have third := guard_setup_tail program s base layout node count cursor nodeHeld arityFits streamFits arityBound streamBound arityCell streamCell pc running programFits block
  have joined := (first.append second).append third
  simpa only [Nat.max_self] using joined

theorem guard_step (program : Program width 4) (s : State width 4)
    (graph : DAG n) (records : GraphRecords width s.heap graph)
    (node : Fin graph.nodeCount) (child : Fin node.val) (labels : List (Channel n))
    (gate : graph.node node = .guard child labels) (suffix : List (Word width))
    (base : ℕ) (layout : ForestWitnessPath.Layout)
    (header : layout.headerBase = records.recordBase)
    (nodeHeld : s.reg 0 = word width node.val)
    (positions : s.stack = word width 0 :: suffix)
    (arityBound : layout.arityBaseColumn + 2 * node.val + 1 < s.heap.size)
    (arityCell : s.heap[layout.arityBaseColumn + 2 * node.val + 1]'arityBound = word width labels.length)
    (streamBound : layout.childrenBaseColumn + 2 * node.val + 1 < s.heap.size)
    (streamCell : s.heap[layout.childrenBaseColumn + 2 * node.val + 1]'streamBound = word width (records.guardBase node))
    (baseBound : layout.childrenBaseColumn + 2 * node.val < s.heap.size)
    (baseCell : s.heap[layout.childrenBaseColumn + 2 * node.val]'baseBound = word width (records.childBase node))
    (baseBefore : layout.childrenBaseColumn + 2 * node.val < layout.markerBase)
    (childBefore : records.childBase node < layout.markerBase)
    (guardSource : ForestWitnessPath.GuardStream s.heap layout.markerBase (records.guardBase node) labels)
    (region : layout.markerBase + n ≤ s.heap.size)
    (cursorFits : records.guardBase node + labels.length < 2 ^ width)
    (countFits : labels.length < 2 ^ width)
    (pc : s.pc = word width base) (running : s.halted = false)
    (programFits : base + 54 < 2 ^ width) (heapFits : s.heap.size ≤ 2 ^ width)
    (block : BlockAt program base (ForestWitnessPath.code width base layout)) :
    ∃ final, Execution program s final (36 + 11 * labels.length) (s.liveWords + 1) ∧
      final.reg 0 = word width child.val ∧
      final.heap = ForestWitnessPath.markLabels s.heap layout.markerBase labels ∧
      final.stack = suffix ∧ final.output = s.output ∧
      final.pc = word width base ∧ final.halted = false := by
  have tagBound : layout.headerBase + 2 * node.val < s.heap.size := by
    simpa only [header] using records.tagValid node
  have tagCell : s.heap[layout.headerBase + 2 * node.val]'tagBound = word width 3 := by
    simpa only [header, gate] using records.tagWord node
  obtain ⟨read, readTrace, readNode, readTag, readTemp, readSaved,
    readHeap, readStack, readOutput, readPC, readRunning⟩ :=
    tag_read program s base layout node.val 3 nodeHeld (by omega) tagBound tagCell
      pc running programFits block
  have readLive : read.liveWords = s.liveWords := by
    simp only [State.liveWords, readHeap, readStack, readOutput]
  obtain ⟨branch, branchTrace, branchNode, branchSaved, branchHeap,
    branchStack, branchOutput, branchPC, branchRunning⟩ :=
    dispatch_child program read base layout 3 (Or.inr rfl) readTag readPC readRunning programFits block
  have branchLive : branch.liveWords = s.liveWords := by
    simp only [State.liveWords, branchHeap, branchStack, branchOutput, readHeap, readStack, readOutput]
  have branchHeld : branch.reg 0 = word width node.val := branchNode.trans (readNode.trans nodeHeld)
  have branchArityBound : layout.arityBaseColumn + 2 * node.val + 1 < branch.heap.size := by
    simpa only [branchHeap, readHeap] using arityBound
  have branchStreamBound : layout.childrenBaseColumn + 2 * node.val + 1 < branch.heap.size := by
    simpa only [branchHeap, readHeap] using streamBound
  have branchArity : branch.heap[layout.arityBaseColumn + 2 * node.val + 1]'branchArityBound = word width labels.length := by
    simpa only [branchHeap, readHeap] using arityCell
  have branchStream : branch.heap[layout.childrenBaseColumn + 2 * node.val + 1]'branchStreamBound = word width (records.guardBase node) := by
    simpa only [branchHeap, readHeap] using streamCell
  have setupTrace := guard_setup program branch base layout node.val labels.length (records.guardBase node)
    branchHeld (by omega) (by omega) branchArityBound branchStreamBound branchArity branchStream
    (by simpa using branchPC) branchRunning programFits block
  have branchPositions : branch.stack = word width 0 :: suffix :=
    branchStack.trans (readStack.trans positions)
  let prepared := UniformDAGScan.state s.heap (base + 22) (word width (records.guardBase node))
    (word width (node.val + node.val + (layout.childrenBaseColumn + 1)))
    (word width (layout.childrenBaseColumn + 1)) (word width labels.length)
    (word width node.val :: word width 0 :: suffix) s.output
  have setupPrepared : Execution program branch prepared 11 (s.liveWords + 1) := by
    simpa only [prepared, branchHeap, readHeap, branchPositions, branchOutput, readOutput, branchLive] using setupTrace
  obtain ⟨scratch, temporary, guardTrace⟩ := ForestWitnessPath.guard_execution program s.heap
    base layout (records.guardBase node) labels
    (word width (node.val + node.val + (layout.childrenBaseColumn + 1)))
    (word width (layout.childrenBaseColumn + 1))
    (word width node.val :: word width 0 :: suffix) s.output
    programFits cursorFits countFits region heapFits guardSource block
  let marked := ForestWitnessPath.markLabels s.heap layout.markerBase labels
  let loopFinal := UniformDAGScan.state marked (base + 33)
    (word width (records.guardBase node + labels.length)) scratch temporary (word width 0)
    (word width node.val :: word width 0 :: suffix) s.output
  have guardPeak : 5 + s.heap.size + (word width node.val :: word width 0 :: suffix).length + s.output.length =
      s.liveWords + 1 := by simp [State.liveWords, positions]; omega
  have guardPrepared : Execution program prepared loopFinal (11 * labels.length + 1) (s.liveWords + 1) := by
    simpa only [prepared, loopFinal, marked, guardPeak] using guardTrace
  obtain ⟨restored, restoreTrace, restoredNode, restoredSaved, restoredHeap,
    restoredStack, restoredOutput, restoredPC, restoredRunning⟩ :=
    guard_finish program loopFinal base layout node.val (word width 0 :: suffix)
      rfl rfl rfl programFits block
  have restorePeak : loopFinal.liveWords = s.liveWords + 1 := by
    simp [loopFinal, marked, UniformDAGScan.state, State.liveWords, positions] <;> omega
  let selectedPosition : Fin (graph.node node).children.length :=
    ⟨0, by simp [gate, Gate.children]⟩
  have childBound : records.childBase node < s.heap.size := by
    simpa only [selectedPosition, Nat.add_zero] using records.childValid node selectedPosition
  have originalChild : s.heap[records.childBase node]'childBound = word width child.val := by
    simpa [selectedPosition, gate, Gate.children] using records.childWord node selectedPosition
  have markedBaseBound : layout.childrenBaseColumn + 2 * node.val < marked.size := by
    simpa only [marked, ForestWitnessPath.markLabels_size] using baseBound
  have markedBase : marked[layout.childrenBaseColumn + 2 * node.val]'markedBaseBound = word width (records.childBase node) :=
    (ForestWitnessPath.markLabels_prefix s.heap layout.markerBase labels region _ baseBefore).trans baseCell
  have markedChildBound : records.childBase node + 0 < marked.size := by
    simpa only [marked, ForestWitnessPath.markLabels_size, Nat.add_zero] using childBound
  have markedChild : marked[records.childBase node + 0]'markedChildBound = word width child.val := by
    simpa only [Nat.add_zero] using
      (ForestWitnessPath.markLabels_prefix s.heap layout.markerBase labels region _ childBefore).trans originalChild
  have finalBaseBound : layout.childrenBaseColumn + 2 * node.val < restored.heap.size := by
    simpa only [restoredHeap, loopFinal, UniformDAGScan.state] using markedBaseBound
  have finalChildBound : records.childBase node + 0 < restored.heap.size := by
    simpa only [restoredHeap, loopFinal, UniformDAGScan.state] using markedChildBound
  have finalBase : restored.heap[layout.childrenBaseColumn + 2 * node.val]'finalBaseBound = word width (records.childBase node) := by
    simpa only [restoredHeap, loopFinal, UniformDAGScan.state] using markedBase
  have finalChild : restored.heap[records.childBase node + 0]'finalChildBound = word width child.val := by
    simpa only [restoredHeap, loopFinal, UniformDAGScan.state] using markedChild
  obtain ⟨final, childTrace, finalChildID, finalPosition, finalHeap, finalStack,
    finalOutput, finalPC, finalRunning⟩ :=
    ForestWitnessPath.child_execution program restored base layout node.val 0 (records.childBase node)
      child.val suffix restoredNode restoredStack (by omega) (by omega) finalBaseBound finalChildBound
      finalBase finalChild restoredPC restoredRunning programFits block
  have childPeak : restored.liveWords + 1 = s.liveWords + 1 := by
    simp only [State.liveWords, restoredHeap, loopFinal, UniformDAGScan.state, restoredStack,
      restoredOutput, marked, ForestWitnessPath.markLabels_size, List.length_cons]
    simp only [State.liveWords, positions, List.length_cons]
  refine ⟨final, ?_, finalChildID, finalHeap.trans restoredHeap, finalStack,
    finalOutput.trans restoredOutput, finalPC, finalRunning⟩
  have joined := ((((readTrace.append branchTrace).append setupPrepared).append guardPrepared).append restoreTrace).append childTrace
  convert joined using 1 <;>
    (try simp only [readLive, branchLive, restorePeak, childPeak, Nat.max_self,
      loopFinal, marked, UniformDAGScan.state, ForestWitnessPath.markLabels_size, readHeap, readStack, readOutput, branchHeap, branchStack, branchOutput, restoredHeap, restoredStack, restoredOutput, State.liveWords, positions, List.length_cons, List.length_append]) <;> omega

/-- Source records before the marker region retain all their actual cell
values after path marks. The rebased record is a proof witness; the runtime
walker still reads the same original source coordinates. -/
def markedRecords (heap : Array (Word width)) (graph : DAG n)
    (records : GraphRecords width heap graph) (markerBase : ℕ) (labels : List (Channel n))
    (region : markerBase + n ≤ heap.size)
    (tagBefore : ∀ node : Fin graph.nodeCount, records.recordBase + 2 * node.val < markerBase)
    (headBefore : ∀ node : Fin graph.nodeCount, records.recordBase + 2 * node.val + 1 < markerBase)
    (childBefore : ∀ node, ∀ position : Fin (graph.node node).children.length,
      records.childBase node + position.val < markerBase)
    (guardBefore : ∀ node, ∀ position : Fin (graph.node node).guardLabels.length,
      records.guardBase node + position.val < markerBase) :
    GraphRecords width (ForestWitnessPath.markLabels heap markerBase labels) graph where
  recordBase := records.recordBase
  childBase := records.childBase
  guardBase := records.guardBase
  tagValid := fun node => by rw [ForestWitnessPath.markLabels_size]; exact records.tagValid node
  tagWord := fun node =>
    (ForestWitnessPath.markLabels_prefix heap markerBase labels region _ (tagBefore node)).trans
      (records.tagWord node)
  headValid := fun node => by rw [ForestWitnessPath.markLabels_size]; exact records.headValid node
  headWord := fun node head gate =>
    (ForestWitnessPath.markLabels_prefix heap markerBase labels region _ (headBefore node)).trans
      (records.headWord node head gate)
  childValid := fun node position => by rw [ForestWitnessPath.markLabels_size]; exact records.childValid node position
  childWord := fun node position =>
    (ForestWitnessPath.markLabels_prefix heap markerBase labels region _ (childBefore node position)).trans
      (records.childWord node position)
  guardValid := fun node position => by rw [ForestWitnessPath.markLabels_size]; exact records.guardValid node position
  guardWord := fun node position =>
    (ForestWitnessPath.markLabels_prefix heap markerBase labels region _ (guardBefore node position)).trans
      (records.guardWord node position)

/-- Physical source cells used throughout one route walk. These fields state
contents and separation of the loaded cache; they do not perform graph-function
lookups or allocate a new source representation during the walk. -/
structure WalkSource (width : ℕ) (heap : Array (Word width)) (graph : DAG n)
    (layout : ForestWitnessPath.Layout) where
  records : GraphRecords width heap graph
  header : layout.headerBase = records.recordBase
  region : layout.markerBase + n ≤ heap.size
  tagBefore : ∀ node : Fin graph.nodeCount, records.recordBase + 2 * node.val < layout.markerBase
  headBefore : ∀ node : Fin graph.nodeCount, records.recordBase + 2 * node.val + 1 < layout.markerBase
  childBefore : ∀ node, ∀ position : Fin (graph.node node).children.length,
    records.childBase node + position.val < layout.markerBase
  guardBefore : ∀ node, ∀ position : Fin (graph.node node).guardLabels.length,
    records.guardBase node + position.val < layout.markerBase
  childColumnBefore : ∀ node : Fin graph.nodeCount,
    layout.childrenBaseColumn + 2 * node.val < layout.markerBase
  guardColumnBefore : ∀ node : Fin graph.nodeCount,
    layout.childrenBaseColumn + 2 * node.val + 1 < layout.markerBase
  arityColumnBefore : ∀ node : Fin graph.nodeCount,
    layout.arityBaseColumn + 2 * node.val + 1 < layout.markerBase
  childColumnWord : ∀ node : Fin graph.nodeCount,
    heap[layout.childrenBaseColumn + 2 * node.val]'(by
      have := childColumnBefore node; omega) = word width (records.childBase node)
  guardColumnWord : ∀ node : Fin graph.nodeCount,
    heap[layout.childrenBaseColumn + 2 * node.val + 1]'(by
      have := guardColumnBefore node; omega) = word width (records.guardBase node)
  arityColumnWord : ∀ node : Fin graph.nodeCount,
    heap[layout.arityBaseColumn + 2 * node.val + 1]'(by
      have := arityColumnBefore node; omega) = word width (graph.node node).guardLabels.length
  guardEndFits : ∀ node : Fin graph.nodeCount,
    records.guardBase node + (graph.node node).guardLabels.length < 2 ^ width

namespace WalkSource
variable {heap : Array (Word width)} {graph : DAG n} {layout : ForestWitnessPath.Layout}

/-- Marking changes only the reused channel region. Every subsequent source
fetch therefore uses exactly the same coordinates and stored word as before. -/
def marked (source : WalkSource width heap graph layout) (labels : List (Channel n)) :
    WalkSource width (ForestWitnessPath.markLabels heap layout.markerBase labels) graph layout where
  records := markedRecords heap graph source.records layout.markerBase labels source.region
    source.tagBefore source.headBefore source.childBefore source.guardBefore
  header := source.header
  region := by simpa only [ForestWitnessPath.markLabels_size] using source.region
  tagBefore := source.tagBefore
  headBefore := source.headBefore
  childBefore := source.childBefore
  guardBefore := source.guardBefore
  childColumnBefore := source.childColumnBefore
  guardColumnBefore := source.guardColumnBefore
  arityColumnBefore := source.arityColumnBefore
  childColumnWord := fun node =>
    (ForestWitnessPath.markLabels_prefix heap layout.markerBase labels source.region _
      (source.childColumnBefore node)).trans (source.childColumnWord node)
  guardColumnWord := fun node =>
    (ForestWitnessPath.markLabels_prefix heap layout.markerBase labels source.region _
      (source.guardColumnBefore node)).trans (source.guardColumnWord node)
  arityColumnWord := fun node =>
    (ForestWitnessPath.markLabels_prefix heap layout.markerBase labels source.region _
      (source.arityColumnBefore node)).trans (source.arityColumnWord node)
  guardEndFits := source.guardEndFits

/-- A guard's actual stream cells, including repeated labels, supply the
fixed-loop stream relation. No deduplicated semantic list replaces them. -/
theorem guard_stream (source : WalkSource width heap graph layout)
    (node : Fin graph.nodeCount) (child : Fin node.val) (labels : List (Channel n))
    (gate : graph.node node = .guard child labels) :
    ForestWitnessPath.GuardStream heap layout.markerBase (source.records.guardBase node) labels := by
  apply ForestWitnessPath.guardStream_of_cells heap layout.markerBase
    (source.records.guardBase node) labels (by have := source.region; omega)
  · intro slot valid
    have actualValid : slot < (graph.node node).guardLabels.length := by
      simpa only [gate, Gate.guardLabels] using valid
    have held := source.records.guardWord node ⟨slot, actualValid⟩
    simpa only [gate, Gate.guardLabels, List.get_eq_getElem] using held
  · intro slot valid
    have actualValid : slot < (graph.node node).guardLabels.length := by
      simpa only [gate, Gate.guardLabels] using valid
    exact source.guardBefore node ⟨slot, actualValid⟩

end WalkSource

/-- The resource witness follows precisely the same positional path. It is
used only in the proof: the fixed program consumes positions from the already
reconstructed stack and never constructs this witness at runtime. -/
inductive RouteWalkCost (graph : DAG n) :
    Fin graph.nodeCount → LeafRoute → Channel n → Finset (Channel n) → ℕ → Prop where
  | input (node : Fin graph.nodeCount) (head : Channel n)
      (gate : graph.node node = .input head) : RouteWalkCost graph node [] head ∅ 16
  | disj (node : Fin graph.nodeCount) (refs : List (Fin node.val))
      (position : Fin refs.length) (route : LeafRoute) (head : Channel n)
      (blocked : Finset (Channel n)) (ticks : ℕ)
      (gate : graph.node node = .disj refs)
      (tail : RouteWalkCost graph (graph.childIndex node (refs.get position)) route head blocked ticks) :
      RouteWalkCost graph node (position.val :: route) head blocked (21 + ticks)
  | guard (node : Fin graph.nodeCount) (child : Fin node.val)
      (labels : List (Channel n)) (route : LeafRoute) (head : Channel n)
      (blocked : Finset (Channel n)) (ticks : ℕ)
      (gate : graph.node node = .guard child labels)
      (tail : RouteWalkCost graph (graph.childIndex node child) route head blocked ticks) :
      RouteWalkCost graph node (0 :: route) head (labels.toFinset ∪ blocked)
        (36 + 11 * labels.length + ticks)

namespace RouteWalkCost
variable {graph : DAG n} {node : Fin graph.nodeCount} {route : LeafRoute}
  {head : Channel n} {blocked : Finset (Channel n)} {ticks : ℕ}

theorem routePath (cost : RouteWalkCost graph node route head blocked ticks) :
    RoutePath graph node route head blocked := by
  induction cost with
  | input node head gate => exact .input node head gate
  | disj node refs position route head blocked ticks gate tail ih =>
      exact .disj node refs position route head blocked gate ih
  | guard node child labels route head blocked ticks gate tail ih =>
      exact .guard node child labels route head blocked gate ih

end RouteWalkCost

variable {graph : DAG n} {node : Fin graph.nodeCount} {route : LeafRoute}
  {head : Channel n} {blocked : Finset (Channel n)} {ticks : ℕ}

/-- Every selected positional route has an exact fetched-instruction cost
witness. Guard labels remain counted with multiplicity. -/
theorem route_cost (path : RoutePath graph node route head blocked) :
    ∃ ticks, RouteWalkCost graph node route head blocked ticks := by
  induction path with
  | input node head gate => exact ⟨16, .input node head gate⟩
  | disj node refs position route head blocked gate tail ih =>
      obtain ⟨ticks, cost⟩ := ih
      exact ⟨21 + ticks, .disj node refs position route head blocked ticks gate cost⟩
  | guard node child labels route head blocked gate tail ih =>
      obtain ⟨ticks, cost⟩ := ih
      exact ⟨36 + 11 * labels.length + ticks,
        .guard node child labels route head blocked ticks gate cost⟩

/-- Channel marker contents at the physical reused-counter region. -/
def MarkerCells (source : WalkSource width heap graph layout)
    (blocked : Finset (Channel n)) : Prop :=
  ∀ coordinate : Channel n,
    heap[layout.markerBase + coordinate.val]'(by
      have := source.region; have := coordinate.isLt; omega) =
        boolWord width (decide (coordinate ∈ blocked))

/-- Complete fixed-code route execution. The source and stack premises describe
actual already loaded cells and the once-reconstructed positions. The final
marker region represents exactly the union of prior marks and the selected
route's guard set; one extra saved-node word is the only temporary stack cost. -/
theorem route_execution (cost : RouteWalkCost graph node route head blocked ticks)
    (program : Program width 4) (s : State width 4)
    (layout : ForestWitnessPath.Layout) (source : WalkSource width s.heap graph layout)
    (initial : Finset (Channel n)) (marked : MarkerCells source initial)
    (suffix : List (Word width)) (base : ℕ)
    (nodeHeld : s.reg 0 = word width node.val)
    (positions : s.stack = route.map (word width) ++ suffix)
    (pc : s.pc = word width base) (running : s.halted = false)
    (programFits : base + 54 < 2 ^ width) (heapFits : s.heap.size ≤ 2 ^ width)
    (block : BlockAt program base (ForestWitnessPath.code width base layout)) :
    ∃ final peak, Execution program s final ticks peak ∧ peak ≤ s.liveWords + 1 ∧
      final.reg 0 = word width head.val ∧ final.stack = suffix ∧ final.output = s.output ∧
      final.pc = word width (base + 54) ∧ final.halted = false ∧
      final.heap.size = s.heap.size ∧
      (∀ address, address < layout.markerBase → final.heap[address]? = s.heap[address]?) ∧
      ∃ finalSource : WalkSource width final.heap graph layout,
        MarkerCells finalSource (initial ∪ blocked) := by
  induction cost generalizing program s layout initial suffix base with
  | input node head gate =>
      obtain ⟨final, trace, held, saved, heap, stack, output, pcFinal, runningFinal⟩ :=
        input_walk program s graph source.records node head gate base layout source.header
          nodeHeld pc running programFits heapFits block
      have finalSource : WalkSource width final.heap graph layout := heap.symm ▸ source
      refine ⟨final, s.liveWords, trace, by omega, held, ?_, output,
        pcFinal, runningFinal, by simpa only [heap], ?_, finalSource, ?_⟩
      · simpa only [List.map_nil, List.nil_append] using stack.trans positions
      · intro address before; simp only [heap]
      · simpa only [MarkerCells, heap, Finset.union_empty] using marked
  | disj node refs position route head blocked ticks gate tail ih =>
      let actualPosition : Fin (graph.node node).children.length :=
        ⟨position.val, by simpa only [gate, Gate.children] using position.isLt⟩
      have baseBound : layout.childrenBaseColumn + 2 * node.val < s.heap.size := by
        have := source.childColumnBefore node; have := source.region; omega
      have stacked : s.stack = word width actualPosition.val :: (route.map (word width) ++ suffix) := by
        simpa only [List.map_cons, List.cons_append] using positions
      obtain ⟨next, stepTrace, held, heap, stack, output, pcNext, runningNext⟩ :=
        disj_step program s graph source.records node refs gate actualPosition
          (route.map (word width) ++ suffix) base layout source.header nodeHeld stacked
          baseBound (source.childColumnWord node) pc running programFits heapFits block
      have nextSource : WalkSource width next.heap graph layout := heap.symm ▸ source
      have nextMarked : MarkerCells nextSource initial := by
        simpa only [MarkerCells, heap] using marked
      have nextHeld : next.reg 0 = word width (graph.childIndex node (refs.get position)).val := by
        simpa [actualPosition, gate, Gate.children] using held
      obtain ⟨final, peak, trace, peakBound, headHeld, finalStack, finalOutput,
        finalPC, finalRunning, finalSize, finalReads, finalSource, finalMarks⟩ :=
        ih program next layout nextSource initial nextMarked suffix base nextHeld stack
          pcNext runningNext programFits (by simpa only [heap] using heapFits) block
      have live : next.liveWords ≤ s.liveWords := by
        simp only [State.liveWords, heap, stack, output, stacked, List.length_cons]; omega
      refine ⟨final, max s.liveWords peak, stepTrace.append trace, by omega,
        headHeld, finalStack, finalOutput.trans output, finalPC, finalRunning,
        finalSize.trans (congrArg Array.size heap), ?_, finalSource, finalMarks⟩
      intro address before
      simpa only [heap] using finalReads address before
  | guard node child labels route head blocked ticks gate tail ih =>
      have arityBound : layout.arityBaseColumn + 2 * node.val + 1 < s.heap.size := by
        have := source.arityColumnBefore node; have := source.region; omega
      have streamBound : layout.childrenBaseColumn + 2 * node.val + 1 < s.heap.size := by
        have := source.guardColumnBefore node; have := source.region; omega
      have baseBound : layout.childrenBaseColumn + 2 * node.val < s.heap.size := by
        have := source.childColumnBefore node; have := source.region; omega
      have arityCell : s.heap[layout.arityBaseColumn + 2 * node.val + 1]'arityBound = word width labels.length := by
        simpa only [gate, Gate.guardLabels] using source.arityColumnWord node
      have chosen : Fin (graph.node node).children.length := ⟨0, by simp [gate, Gate.children]⟩
      have childBefore : source.records.childBase node < layout.markerBase := by
        have before := source.childBefore node chosen
        omega
      have cursorFits : source.records.guardBase node + labels.length < 2 ^ width := by
        simpa only [gate, Gate.guardLabels] using source.guardEndFits node
      have stacked : s.stack = word width 0 :: (route.map (word width) ++ suffix) := by
        simpa only [List.map_cons, List.cons_append] using positions
      obtain ⟨next, stepTrace, held, heap, stack, output, pcNext, runningNext⟩ :=
        guard_step program s graph source.records node child labels gate
          (route.map (word width) ++ suffix) base layout source.header nodeHeld stacked
          arityBound arityCell streamBound (source.guardColumnWord node)
          baseBound (source.childColumnWord node) (source.childColumnBefore node) childBefore
          (source.guard_stream node child labels gate) source.region cursorFits (by omega)
          pc running programFits heapFits block
      have nextSource : WalkSource width next.heap graph layout :=
        heap.symm ▸ source.marked labels
      have nextMarked : MarkerCells nextSource (initial ∪ labels.toFinset) := by
        simpa only [MarkerCells, heap] using
          ForestWitnessPath.markLabels_cells s.heap layout.markerBase initial labels source.region marked
      obtain ⟨final, peak, trace, peakBound, headHeld, finalStack, finalOutput,
        finalPC, finalRunning, finalSize, finalReads, finalSource, finalMarks⟩ :=
        ih program next layout nextSource (initial ∪ labels.toFinset) nextMarked suffix base
          held stack pcNext runningNext programFits
          (by simpa only [heap, ForestWitnessPath.markLabels_size] using heapFits) block
      have live : next.liveWords ≤ s.liveWords := by
        simp only [State.liveWords, heap, ForestWitnessPath.markLabels_size,
          stack, output, stacked, List.length_cons]; omega
      refine ⟨final, max (s.liveWords + 1) peak, ?_, by omega,
        headHeld, finalStack, finalOutput.trans output, finalPC, finalRunning, ?_, ?_, finalSource, ?_⟩
      · simpa only [Nat.add_assoc] using stepTrace.append trace
      · simpa only [heap, ForestWitnessPath.markLabels_size] using finalSize
      · intro address before
        have initialValid : address < s.heap.size := by have := source.region; omega
        have markedValid : address < (ForestWitnessPath.markLabels s.heap layout.markerBase labels).size := by
          simpa only [ForestWitnessPath.markLabels_size] using initialValid
        have retained : (ForestWitnessPath.markLabels s.heap layout.markerBase labels)[address]? = s.heap[address]? := by
          rw [Array.getElem?_eq_getElem markedValid, Array.getElem?_eq_getElem initialValid]
          exact congrArg some (ForestWitnessPath.markLabels_prefix s.heap layout.markerBase labels source.region address before)
        exact (finalReads address before).trans (by simpa only [heap] using retained)
      · simpa only [Finset.union_assoc] using finalMarks

/-- The marker loop also retains metadata beyond the whole channel region.
In particular it retains the selected pointer and its declared-root ID. -/
theorem marked_suffix (heap : Array (Word width)) (markerBase : ℕ)
    (labels : List (Channel n)) (address : ℕ) (afterMarkers : markerBase + n ≤ address) :
    (ForestWitnessPath.markLabels heap markerBase labels)[address]? = heap[address]? := by
  induction labels generalizing heap with
  | nil => rfl
  | cons label rest ih =>
    have different : markerBase + label.val ≠ address := by have := label.isLt; omega
    have retained : (heap.setIfInBounds (markerBase + label.val) (word width 1))[address]? = heap[address]? := by
      by_cases valid : markerBase + label.val < heap.size
      · rw [Array.setIfInBounds_def, dite_eq_left valid]
        exact Array.getElem?_set_ne valid different
      · simp only [Array.setIfInBounds_def, dite_eq_right valid]
    exact (ih (heap.setIfInBounds (markerBase + label.val) (word width 1))).trans retained

/-- The provenance cell supplied by the actual shared setup is above every
channel marker, including when different declared roots have empty routes. -/
theorem marked_root_id (heap : Array (Word width)) (graph : DAG n)
    (current : Array (Word width)) (labels : List (Channel n)) :
    (ForestWitnessPath.markLabels current (setupOffset heap graph) labels)[provenanceCell heap graph]? =
      current[provenanceCell heap graph]? := by
  exact marked_suffix current (setupOffset heap graph) labels (provenanceCell heap graph)
    (by simp only [provenanceCell]; omega)

/-- One real header reload precedes the single assignment emission. The
channel count comes from its stored header; the marker region is read once.
Output order is ascending channel order, with the caller output retained. -/
theorem assignment_emit (program : Program width 4) (s : State width 4)
    (base markerBase countAddress : ℕ) (marked : Channel n → Bool)
    (countAddressFits : countAddress < 2 ^ width)
    (countAddressBound : countAddress < s.heap.size)
    (countCell : s.heap[countAddress]'countAddressBound = word width n)
    (pc : s.pc = word width base) (running : s.halted = false)
    (programFits : base + 13 < 2 ^ width) (countFits : n < 2 ^ width)
    (region : markerBase + n ≤ s.heap.size) (heapFits : s.heap.size ≤ 2 ^ width)
    (cells : ∀ coordinate : Channel n,
      s.heap[markerBase + coordinate.val]'(by have := coordinate.isLt; omega) =
        boolWord width (marked coordinate))
    (initBlock : BlockAt program base (emitInit width markerBase countAddress))
    (emitBlock : BlockAt program (base + 3) (ForestWitnessEmit.code width (base + 3))) :
    ∃ final, Execution program s final (10 * n + 4)
        (5 + s.heap.size + s.stack.length + (n + s.output.length)) ∧
      final.heap = s.heap ∧ final.stack = s.stack ∧
      final.output = List.ofFn (fun coordinate => boolWord width (!(marked coordinate))) ++ s.output ∧
      final.pc = word width (base + 13) ∧ final.halted = false := by
  obtain ⟨ready, initTrace, countHeld, scratchHeld, loadedHeld, markerHeld,
    readyHeap, readyStack, readyOutput, readyPC, readyRunning⟩ :=
    emitInit_execution program s base markerBase countAddress n
      countAddressBound countCell countAddressFits pc running (by omega) initBlock
  have registers : ready.reg =
      (ForestWitnessEmit.state s.heap (base + 3) (word width n)
        (ready.reg 1) (ready.reg 2) (word width markerBase) s.stack s.output).reg := by
    funext coordinate
    fin_cases coordinate <;>
      simp [ForestWitnessEmit.state, UniformDAGScan.state, countHeld, markerHeld]
  have canonical : ready = ForestWitnessEmit.state s.heap (base + 3) (word width n)
      (ready.reg 1) (ready.reg 2) (word width markerBase) s.stack s.output :=
    physical_state_eq _ _ registers readyHeap readyStack readyOutput readyPC readyRunning
  obtain ⟨finalScratch, finalLoaded, emitTrace⟩ := ForestWitnessEmit.execution program s.heap
    (base + 3) markerBase marked (ready.reg 1) (ready.reg 2) s.stack s.output
    (by omega) countFits region heapFits cells emitBlock
  rw [← canonical] at emitTrace
  let final := ForestWitnessEmit.state s.heap (base + 13) (word width 0)
    finalScratch finalLoaded (word width markerBase) s.stack
    (List.ofFn (fun coordinate => boolWord width (!(marked coordinate))) ++ s.output)
  refine ⟨final, ?_, rfl, rfl, rfl, rfl, rfl⟩
  have joined := initTrace.append emitTrace
  convert joined using 1 <;>
    (try simp only [final, State.liveWords, ForestWitnessEmit.state,
      UniformDAGScan.state, Nat.add_assoc]) <;> omega

private theorem set_other (heap : Array (Word width)) (cell address : ℕ)
    (value : Word width) (different : cell ≠ address) :
    (heap.setIfInBounds cell value)[address]? = heap[address]? := by
  by_cases valid : cell < heap.size
  · rw [Array.setIfInBounds_def, dite_eq_left valid]
    exact Array.getElem?_set_ne valid different
  · simp only [Array.setIfInBounds_def, dite_eq_right valid]

/-- One reconstructed selected route is walked once, then the original stored
channel count is reloaded and one assignment is emitted. The retained source
prefix supplies that reload; no runtime source-length query is introduced. -/
theorem walk_and_emit (cost : RouteWalkCost graph node route head blocked ticks)
    (feasible : head ∉ blocked) (program : Program width 4) (s : State width 4)
    (layout : ForestWitnessPath.Layout) (source : WalkSource width s.heap graph layout)
    (initialZero : MarkerCells source ∅) (suffix : List (Word width))
    (base countAddress : ℕ) (countBefore : countAddress < layout.markerBase)
    (countWord : s.heap[countAddress]'(by have := source.region; omega) = word width n)
    (nodeHeld : s.reg 0 = word width node.val)
    (positions : s.stack = route.map (word width) ++ suffix)
    (pc : s.pc = word width base) (running : s.halted = false)
    (programFits : base + 67 < 2 ^ width) (heapFits : s.heap.size ≤ 2 ^ width)
    (block : BlockAt program base (code width base layout countAddress)) :
    ∃ final peak, Execution program s final (ticks + 10 * n + 4) peak ∧
      peak ≤ s.liveWords + n + 1 ∧ final.heap.size = s.heap.size ∧
      final.stack = suffix ∧
      final.output = List.ofFn (fun coordinate : Channel n =>
        boolWord width (!(decide (coordinate ∈ blocked)))) ++ s.output ∧
      final.pc = word width (base + 67) ∧ final.halted = false ∧
      (Finset.univ \ blocked : Finset (Channel n)).Nonempty ∧
      graph.eval (assignmentOfSet (Finset.univ \ blocked)) node = true := by
  have pathBlock : BlockAt program base (ForestWitnessPath.code width base layout) := by
    apply BlockAt.prefix program base _ _
    simpa only [code, List.append_assoc] using block
  have afterPath : BlockAt program (base + 54)
      (emitInit width layout.markerBase countAddress ++ ForestWitnessEmit.code width (base + 57)) := by
    have stored := BlockAt.suffix program base (ForestWitnessPath.code width base layout)
      (emitInit width layout.markerBase countAddress ++ ForestWitnessEmit.code width (base + 57))
      (by simpa only [code, List.append_assoc] using block)
    simpa only [ForestWitnessPath.code_length] using stored
  have initBlock : BlockAt program (base + 54) (emitInit width layout.markerBase countAddress) :=
    BlockAt.prefix program (base + 54) _ _ afterPath
  have emitBlock : BlockAt program (base + 57) (ForestWitnessEmit.code width (base + 57)) := by
    simpa only [emitInit_length, Nat.add_assoc] using
      BlockAt.suffix program (base + 54) _ _ afterPath
  obtain ⟨walked, walkPeak, walkTrace, walkPeakBound, headHeld, walkStack, walkOutput,
    walkPC, walkRunning, walkSize, retained, walkSource, walkMarkers⟩ :=
    route_execution cost program s layout source ∅ initialZero suffix base nodeHeld positions
      pc running (by omega) heapFits pathBlock
  have countValid : countAddress < s.heap.size := by have := source.region; omega
  have walkCountValid : countAddress < walked.heap.size := by simpa only [walkSize] using countValid
  have walkCount : walked.heap[countAddress]'walkCountValid = word width n := by
    have read := retained countAddress countBefore
    rw [Array.getElem?_eq_getElem walkCountValid, Array.getElem?_eq_getElem countValid] at read
    exact (Option.some.inj read).trans countWord
  have markerPositive : 0 < layout.markerBase := by have := source.tagBefore node; omega
  have countFits : n < 2 ^ width := by have := source.region; omega
  have markerFits : layout.markerBase < 2 ^ width := by
    have positive := head.isLt; have := source.region; omega
  have markerCells : ∀ coordinate : Channel n,
      walked.heap[layout.markerBase + coordinate.val]'(by
        have := walkSource.region; have := coordinate.isLt; omega) =
        boolWord width (decide (coordinate ∈ blocked)) := by
    simpa only [MarkerCells, Finset.empty_union] using walkMarkers
  obtain ⟨final, emitTrace, finalHeap, finalStack,
    finalOutput, finalPC, finalRunning⟩ :=
    assignment_emit program walked (base + 54) layout.markerBase countAddress
      (fun coordinate : Channel n => decide (coordinate ∈ blocked))
      (by omega) walkCountValid walkCount walkPC walkRunning (by omega)
      countFits walkSource.region (by simpa only [walkSize] using heapFits) markerCells
      initBlock (by simpa only [Nat.add_assoc] using emitBlock)
  let emitPeak := 5 + walked.heap.size + walked.stack.length + (n + walked.output.length)
  have emitBound : emitPeak ≤ s.liveWords + n := by
    dsimp only [emitPeak]
    simp only [walkSize, walkStack, walkOutput, State.liveWords,
      positions, List.length_append, List.length_map]
    omega
  have member : head ∈ (Finset.univ \ blocked : Finset (Channel n)) := by
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]; exact feasible
  have guardsFalse : Disjoint blocked (Finset.univ \ blocked : Finset (Channel n)) := by
    apply Finset.disjoint_left.mpr
    intro coordinate blockedMember member
    exact (Finset.mem_sdiff.mp member).2 blockedMember
  refine ⟨final, max walkPeak emitPeak, ?_, by omega,
    (congrArg Array.size finalHeap).trans walkSize,
    finalStack.trans walkStack, ?_, ?_, finalRunning,
    ⟨head, member⟩, cost.routePath.livePath.eval_true _ member guardsFalse⟩
  · simpa only [Nat.add_assoc, emitPeak] using walkTrace.append emitTrace
  · simpa only [walkOutput] using finalOutput
  · simpa only [Nat.add_assoc] using finalPC

/-- Every coordinate before the counter region is outside both selector
stores in the actual shared setup layout. -/
theorem before_marker_separate (heap : Array (Word width)) (graph : DAG n)
    (address : ℕ) (beforeMarkers : address < setupOffset heap graph) :
    ForestCursorRootStore.RootCellLayout (setupLayout heap graph) address := by
  refine ⟨Or.inl beforeMarkers, ?_, ?_⟩ <;> simp only [setupLayout] <;> omega

/-- The conditional root-ID update also lies beyond the marker region. -/
theorem afterSetup_prefix (heap : Array (Word width)) (graph : DAG n)
    (state : RuntimeModel width n) (identifier address : ℕ)
    (beforeMarkers : address < setupOffset heap graph) :
    (afterSetup (setupLayout heap graph) (provenanceCell heap graph) identifier state).heap[address]? =
      state.heap[address]? := by
  change (ForestCursorRootStore.rootHeap width state.heap (setupLayout heap graph).found
    (provenanceCell heap graph) identifier)[address]? = _
  unfold ForestCursorRootStore.rootHeap
  split
  · apply set_other
    unfold provenanceCell
    omega
  · rfl

/-- Each source-root traversal preserves every physical source or descriptor
coordinate before the shared counter region. -/
theorem caller_prefix (heap : Array (Word width)) (graph : DAG n)
    (index : OccurrenceIndex graph) (b : ℕ) (target : Channel n)
    (state : RuntimeModel width n) (position : Fin graph.roots.length)
    (address : ℕ) (beforeMarkers : address < setupOffset heap graph) :
    (callerModel graph (setupLayout heap graph) (provenanceCell heap graph) index b target
      state position).heap[address]? = state.heap[address]? := by
  exact (ForestCursorRootStore.runModel_rootCell (setupLayout heap graph) index b target
    (afterSetup (setupLayout heap graph) (provenanceCell heap graph) position.val state)
    address (before_marker_separate heap graph address beforeMarkers)
    (cursorOps graph (graph.roots.get position) [])).trans
      (afterSetup_prefix heap graph state position.val address beforeMarkers)

/-- The entire declared-root sequence retains that physical prefix. -/
theorem roots_prefix (heap : Array (Word width)) (graph : DAG n)
    (indices : Fin graph.roots.length → OccurrenceIndex graph)
    (b : ℕ) (target : Channel n) (positions : List (Fin graph.roots.length))
    (state : RuntimeModel width n) (address : ℕ)
    (beforeMarkers : address < setupOffset heap graph) :
    (rootsModel graph (setupLayout heap graph) (provenanceCell heap graph) indices b target
      state positions).heap[address]? = state.heap[address]? := by
  induction positions generalizing state with
  | nil => rfl
  | cons position rest ih =>
      exact (ih _).trans (caller_prefix heap graph (indices position) b target state position address beforeMarkers)

/-- Parent records as well as the source packet survive the complete caller. -/
theorem whole_prefix (width : ℕ) (heap : Array (Word width)) (graph : DAG n)
    (b : ℕ) (target : Channel n) (address : ℕ)
    (beforeMarkers : address < setupOffset heap graph) :
    (wholeModel width heap graph b target).heap[address]? =
      (setupHeap width heap graph)[address]? :=
  roots_prefix heap graph (sourceIndices graph) b target (List.finRange graph.roots.length)
    (setupRuntime width heap graph) address beforeMarkers

theorem source_before_markers (heap : Array (Word width)) (graph : DAG n) :
    heap.size ≤ setupOffset heap graph := by unfold setupOffset; omega

/-- The dense descriptor allocation precedes the reused counter region. -/
theorem descriptor_before_markers (heap : Array (Word width)) (graph : DAG n)
    (pointer : ℕ) (positive : 0 < pointer) (bounded : pointer ≤ (buildRoots graph).count) :
    heap.size + 2 * (pointer - 1) + 1 < setupOffset heap graph := by
  unfold setupOffset
  omega

/-- The source-defined all-root model restores the same natural counters at
all boundaries; the setup counters are globally initialized only once. -/
theorem roots_counters (graph : DAG n) (layout : SelectorLayout n) (cell : ℕ)
    (indices : Fin graph.roots.length → OccurrenceIndex graph)
    (b : ℕ) (target : Channel n) (positions : List (Fin graph.roots.length))
    (state : RuntimeModel width n) :
    (rootsModel graph layout cell indices b target state positions).counters = state.counters := by
  induction positions generalizing state with
  | nil => rfl
  | cons position rest ih =>
      change (rootsModel graph layout cell indices b target
        (callerModel graph layout cell (indices position) b target state position) rest).counters = _
      rw [ih]
      exact root_model_counters graph (graph.roots.get position) layout (indices position) b target
        (afterSetup layout cell position.val state)

theorem whole_counters_zero (width : ℕ) (heap : Array (Word width)) (graph : DAG n)
    (b : ℕ) (target : Channel n) :
    (wholeModel width heap graph b target).counters = (fun _ : Channel n => 0) :=
  roots_counters graph (setupLayout heap graph) (provenanceCell heap graph) (sourceIndices graph)
    b target (List.finRange graph.roots.length) (setupRuntime width heap graph)

/-- Concrete stored-runtime preservation gives the full allocated marker
region; its capacity comes from the actual once-only setup allocation. -/
theorem whole_marker_region (width : ℕ) (heap : Array (Word width)) (graph : DAG n)
    (records : GraphRecords width (setupHeap width heap graph) graph)
    (routes : RouteDescriptors width (setupHeap width heap graph))
    (b : ℕ) (target : Channel n)
    (held : RuntimeStored graph records routes (setupLayout heap graph)
      (wholeModel width heap graph b target)) :
    setupOffset heap graph + n ≤ (wholeModel width heap graph b target).heap.size := by
  rw [held.persistent.size, setupHeap_size]
  unfold setupOffset
  omega

/-- Original source words are available at their real coordinates after
traversal, including tags, arities, incidence bases, and the declared-n header. -/
theorem whole_source_read (width : ℕ) (heap : Array (Word width)) (graph : DAG n)
    (records : GraphRecords width (setupHeap width heap graph) graph)
    (routes : RouteDescriptors width (setupHeap width heap graph))
    (b : ℕ) (target : Channel n)
    (held : RuntimeStored graph records routes (setupLayout heap graph)
      (wholeModel width heap graph b target)) (address : ℕ) (sourceBound : address < heap.size) :
    (wholeModel width heap graph b target).heap[address]'(by
      rw [held.persistent.size, setupHeap_size]; omega) = heap[address]'sourceBound := by
  have beforeMarkers : address < setupOffset heap graph := by
    have := source_before_markers heap graph
    omega
  have agreement := (whole_prefix width heap graph b target address beforeMarkers).trans
    (setup_prefix width heap graph address sourceBound)
  simpa only [Array.getElem?_eq_getElem sourceBound,
    Array.getElem?_eq_getElem (by rw [held.persistent.size, setupHeap_size]; omega :
      address < (wholeModel width heap graph b target).heap.size), Option.some.injEq] using agreement

/-- The physical stored-counter refinement returned by the complete caller
turns restoration into actual zero marker cells. No fresh allocation is used. -/
theorem whole_marker_zero (width : ℕ) (heap : Array (Word width)) (graph : DAG n)
    (records : GraphRecords width (setupHeap width heap graph) graph)
    (routes : RouteDescriptors width (setupHeap width heap graph))
    (b : ℕ) (target : Channel n)
    (held : RuntimeStored graph records routes (setupLayout heap graph)
      (wholeModel width heap graph b target)) (channel : Channel n) :
    (wholeModel width heap graph b target).heap[setupOffset heap graph + channel.val]'
      (held.counters.valid channel) = boolWord width false := by
  have actual := held.counters.held channel
  have zero : (wholeModel width heap graph b target).counters channel = 0 :=
    congrFun (whole_counters_zero width heap graph b target) channel
  have zeroWord : word width ((wholeModel width heap graph b target).counters channel) =
      boolWord width false := by simpa only [boolWord, Bool.false_eq_true, ↓reduceIte] using congrArg (word width) zero
  exact actual.trans zeroWord

open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestInputStored

/-- The original loaded row packet derives all graph-record cells. In
particular, only input nodes constrain header heads; other gates use their
original child streams, not header-head conventions. -/
def cacheRecords (heap : Array (Word width)) (graph : DAG n)
    (rows : List Row) (roots : List ℕ) (matched : RowsMatch graph rows) :
    GraphRecords width (cacheHeap width heap rows roots) graph where
  recordBase := heap.size
  childBase := fun node => heap.size + 6 * rows.length + (rowChildren (rows.take node.val)).length
  guardBase := fun node => heap.size + 6 * rows.length + (rowChildren rows).length +
    (rowGuards (rows.take node.val)).length
  tagValid := fun node => by
    simp only [cacheHeap_size]; have bound : node.val < rows.length := by
      rw [matched.length_eq]; exact node.isLt
    omega
  tagWord := fun node => by
    have bounded : node.val < rows.length := by rw [matched.length_eq]; exact node.isLt
    have valid : heap.size + 2 * node.val < (cacheHeap width heap rows roots).size := by
      simp only [cacheHeap_size]; omega
    change (cacheHeap width heap rows roots)[heap.size + 2 * node.val]'valid =
      word width (tagValue graph node)
    exact cache_tag_word heap graph rows roots matched node
  headValid := fun node => by
    simp only [cacheHeap_size]; have bound : node.val < rows.length := by
      rw [matched.length_eq]; exact node.isLt
    omega
  headWord := fun node head gate => by
    have bounded : node.val < rows.length := by rw [matched.length_eq]; exact node.isLt
    have loaded := cache_header_word heap rows roots (2 * node.val + 1)
      (by rw [rowHeaders_length]; omega)
    rw [header_head_value rows node.val bounded, (matched.node node).2.1 head gate] at loaded
    simpa only [Nat.add_assoc] using loaded
  childValid := fun node position => by
    have bounded : node.val < rows.length := by rw [matched.length_eq]; exact node.isLt
    have lengths := congrArg List.length (row_children_split rows node.val bounded)
    simp only [List.length_append, (matched.node node).2.2.1, List.length_map] at lengths
    simp only [cacheHeap_size]; have := position.isLt; omega
  childWord := fun node position => by
    simpa only [List.get_eq_getElem] using
      typed_child_cell heap graph rows roots matched node position.val position.isLt
  guardValid := fun node position => by
    have bounded : node.val < rows.length := by rw [matched.length_eq]; exact node.isLt
    have lengths := congrArg List.length (row_guards_split rows node.val bounded)
    simp only [List.length_append, (matched.node node).2.2.2, List.length_map] at lengths
    simp only [cacheHeap_size]; have := position.isLt; omega
  guardWord := fun node position => by
    simpa only [List.get_eq_getElem] using
      typed_guard_cell heap graph rows roots matched node position.val position.isLt

/-- Extending a physical heap with the once-only shared descriptor/counter
setup preserves graph records at their original coordinates. -/
def setupRecords (heap : Array (Word width)) (graph : DAG n)
    (records : GraphRecords width heap graph) : GraphRecords width (setupHeap width heap graph) graph where
  recordBase := records.recordBase
  childBase := records.childBase
  guardBase := records.guardBase
  tagValid := fun node => by rw [setupHeap_size]; have := records.tagValid node; omega
  tagWord := fun node => by
    have read := setup_prefix width heap graph _ (records.tagValid node)
    rw [Array.getElem?_eq_getElem (records.tagValid node),
      Array.getElem?_eq_getElem (by rw [setupHeap_size]; have := records.tagValid node; omega)] at read
    exact (Option.some.inj read).trans (records.tagWord node)
  headValid := fun node => by rw [setupHeap_size]; have := records.headValid node; omega
  headWord := fun node head gate => by
    have read := setup_prefix width heap graph _ (records.headValid node)
    rw [Array.getElem?_eq_getElem (records.headValid node),
      Array.getElem?_eq_getElem (by rw [setupHeap_size]; have := records.headValid node; omega)] at read
    exact (Option.some.inj read).trans (records.headWord node head gate)
  childValid := fun node position => by rw [setupHeap_size]; have := records.childValid node position; omega
  childWord := fun node position => by
    have read := setup_prefix width heap graph _ (records.childValid node position)
    rw [Array.getElem?_eq_getElem (records.childValid node position),
      Array.getElem?_eq_getElem (by rw [setupHeap_size]; have := records.childValid node position; omega)] at read
    exact (Option.some.inj read).trans (records.childWord node position)
  guardValid := fun node position => by rw [setupHeap_size]; have := records.guardValid node position; omega
  guardWord := fun node position => by
    have read := setup_prefix width heap graph _ (records.guardValid node position)
    rw [Array.getElem?_eq_getElem (records.guardValid node position),
      Array.getElem?_eq_getElem (by rw [setupHeap_size]; have := records.guardValid node position; omega)] at read
    exact (Option.some.inj read).trans (records.guardWord node position)

/-- The complete walk source is derived from the actual loaded cache and the
single shared setup. Cached guard counts and incidence bases retain duplicate
occurrences. The marker region is the already allocated counter region. -/
def loadedSource (heap : Array (Word width)) (graph : DAG n)
    (rows : List Row) (roots : List ℕ) (matched : RowsMatch graph rows)
    (fits : (setupHeap width (cacheHeap width heap rows roots) graph).size ≤ 2 ^ width) :
    WalkSource width (setupHeap width (cacheHeap width heap rows roots) graph) graph
      (ForestWitnessPath.packetLayout heap.size rows.length
        (setupOffset (cacheHeap width heap rows roots) graph)) := by
  let packet := cacheHeap width heap rows roots
  let represented := cacheRecords heap graph rows roots matched
  let records := setupRecords packet graph represented
  let layout := ForestWitnessPath.packetLayout heap.size rows.length (setupOffset packet graph)
  have packetBefore : packet.size ≤ layout.markerBase := by
    dsimp only [layout, ForestWitnessPath.packetLayout]; unfold setupOffset; omega
  have liftedCell (address : ℕ) (bound : address < packet.size) :
      (setupHeap width packet graph)[address]'(by rw [setupHeap_size]; omega) = packet[address]'bound := by
    have read := setup_prefix width packet graph address bound
    rw [Array.getElem?_eq_getElem bound,
      Array.getElem?_eq_getElem (by rw [setupHeap_size]; omega)] at read
    exact Option.some.inj read
  refine { records := records
           header := rfl
           region := ?_
           tagBefore := ?_
           headBefore := ?_
           childBefore := ?_
           guardBefore := ?_
           childColumnBefore := ?_
           guardColumnBefore := ?_
           arityColumnBefore := ?_
           childColumnWord := ?_
           guardColumnWord := ?_
           arityColumnWord := ?_
           guardEndFits := ?_ }
  · dsimp only [layout, ForestWitnessPath.packetLayout]; rw [setupHeap_size]; unfold setupOffset; omega
  · intro node; exact lt_of_lt_of_le (represented.tagValid node) packetBefore
  · intro node; exact lt_of_lt_of_le (represented.headValid node) packetBefore
  · intro node position; exact lt_of_lt_of_le (represented.childValid node position) packetBefore
  · intro node position; exact lt_of_lt_of_le (represented.guardValid node position) packetBefore
  · intro node
    have bounded : node.val < rows.length := by rw [matched.length_eq]; exact node.isLt
    dsimp only [layout, ForestWitnessPath.packetLayout]
    simp only [packet, cacheHeap_size] at packetBefore
    dsimp only [layout, ForestWitnessPath.packetLayout, packet] at packetBefore
    omega
  · intro node
    have bounded : node.val < rows.length := by rw [matched.length_eq]; exact node.isLt
    dsimp only [layout, ForestWitnessPath.packetLayout]
    simp only [packet, cacheHeap_size] at packetBefore
    dsimp only [layout, ForestWitnessPath.packetLayout, packet] at packetBefore
    omega
  · intro node
    have bounded : node.val < rows.length := by rw [matched.length_eq]; exact node.isLt
    dsimp only [layout, ForestWitnessPath.packetLayout]
    simp only [packet, cacheHeap_size] at packetBefore
    dsimp only [layout, ForestWitnessPath.packetLayout, packet] at packetBefore
    omega
  · intro node
    have valid : node.val < rows.length := by rw [matched.length_eq]; exact node.isLt
    obtain ⟨children, guards⟩ := cache_base_words heap rows roots node.val valid
    simpa only [layout, ForestWitnessPath.packetLayout, records, setupRecords, represented, cacheRecords, packet, Nat.add_assoc] using
      (liftedCell (heap.size + 2 * rows.length + 2 * node.val) (by simp only [packet, cacheHeap_size]; omega)).trans children
  · intro node
    have valid : node.val < rows.length := by rw [matched.length_eq]; exact node.isLt
    obtain ⟨children, guards⟩ := cache_base_words heap rows roots node.val valid
    simpa only [layout, ForestWitnessPath.packetLayout, records, setupRecords, represented, cacheRecords, packet, Nat.add_assoc] using
      (liftedCell (heap.size + 2 * rows.length + (2 * node.val + 1)) (by simp only [packet, cacheHeap_size]; omega)).trans guards
  · intro node
    have valid : node.val < rows.length := by rw [matched.length_eq]; exact node.isLt
    simpa only [layout, ForestWitnessPath.packetLayout, records, setupRecords, represented, cacheRecords, packet, Nat.add_assoc] using
      (liftedCell (heap.size + 4 * rows.length + (2 * node.val + 1)) (by simp only [packet, cacheHeap_size]; omega)).trans
        (cache_guard_arity_word heap graph rows roots matched node)
  · intro node
    have valid : node.val < rows.length := by rw [matched.length_eq]; exact node.isLt
    have lengths := congrArg List.length (row_guards_split rows node.val valid)
    simp only [List.length_append, (matched.node node).2.2.2, List.length_map] at lengths
    dsimp only [records, represented, setupRecords, cacheRecords]
    simp only [packet, cacheHeap_size, setupHeap_size] at fits
    omega

end Controller.Cost.ForestWitnessWalk
