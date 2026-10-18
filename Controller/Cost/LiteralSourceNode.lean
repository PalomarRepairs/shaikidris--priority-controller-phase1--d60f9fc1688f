module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.LiteralGuardUnion
public import Controller.Cost.UniformDAGTypedNode

@[expose] public section

/-! A fixed source-reading node program for positive literals, negative literals,
and constant-zero ancestry. Tags and operand identifiers are fetched from the
original DAG packet; only the chosen propagation lane changes dispatch. -/
namespace Controller.Cost.LiteralSourceNode
open Controller.Cost.GateProgram
abbrev Layout := UniformDAGNode.Layout

structure Mode where
  positive : Bool
  negative : Bool
  empty : Bool
  deriving DecidableEq, Repr

def destinations (base : Nat) (mode : Mode) (tag : Fin 5) : Nat :=
  match tag.val with
  | 0 => base + 14
  | 1 => if mode.positive then base + 22 else base + 18
  | 3 => if mode.negative then base + 65 else base + 31
  | _ => base + 31

def constantCode (width : Nat) (value : Bool) : Code width :=
  [.constant 2 (boolWord width value), .allocate 2]

def constantReturn (width base : Nat) (value : Bool) : Code width :=
  constantCode width value ++ UniformDAGNode.jumpCode width (base + 100)

def inputCode (width base : Nat) (layout : Layout) : Code width :=
  [.constant 1 (word width layout.channelBase)] ++
    (UniformDAGInputGate.code width layout.headBase ++ UniformDAGNode.jumpCode width (base + 100))

def arityCode (width base : Nat) (layout : Layout) : Code width :=
  [.constant 0 (word width layout.childArityBase), .add 0 0 3, .load 0 0,
   .branchZero 0 (word width (base + 14))]

def childrenCode (width base : Nat) (layout : Layout) : Code width :=
  arityCode width base layout ++
    (UniformDAGOrGate.code width (base + 35) layout.nodeBase layout.childArityBase
      layout.childSourceBase ++ UniformDAGNode.jumpCode width (base + 100))

def guardCode (width base : Nat) (layout : Layout) : Code width :=
  [.constant 1 (word width layout.nodeBase)] ++
    (LiteralGuardUnion.code width (base + 66) layout.headBase layout.channelBase
      layout.guardArityBase layout.guardSourceBase ++ UniformDAGNode.jumpCode width (base + 100))

def code (width base : Nat) (layout : Layout) (mode : Mode) : Code width :=
  UniformDAGDispatch.code width layout.tagBase (destinations base mode) ++
    (constantReturn width base mode.empty ++ (constantReturn width base false ++
      (inputCode width base layout ++ (childrenCode width base layout ++ guardCode width base layout))))

@[simp] theorem constantCode_length : (constantCode width value).length = 2 := rfl
@[simp] theorem constantReturn_length : (constantReturn width base value).length = 4 := rfl
@[simp] theorem inputCode_length : (inputCode width base layout).length = 9 := rfl
@[simp] theorem arityCode_length : (arityCode width base layout).length = 4 := rfl
@[simp] theorem childrenCode_length : (childrenCode width base layout).length = 34 := rfl
@[simp] theorem guardCode_length : (guardCode width base layout).length = 35 := rfl
@[simp] theorem code_length : (code width base layout mode).length = 100 := rfl

theorem blocks (program : Program width 4) (base : Nat) (layout : Layout) (mode : Mode)
    (block : BlockAt program base (code width base layout mode)) :
    BlockAt program base (UniformDAGDispatch.code width layout.tagBase (destinations base mode)) ∧
    BlockAt program (base + 14) (constantReturn width base mode.empty) ∧
    BlockAt program (base + 18) (constantReturn width base false) ∧
    BlockAt program (base + 22) (inputCode width base layout) ∧
    BlockAt program (base + 31) (childrenCode width base layout) ∧
    BlockAt program (base + 65) (guardCode width base layout) := by
  have b1 := BlockAt.suffix program base _ _ block
  have b2 := BlockAt.suffix program _ _ _ b1
  have b3 := BlockAt.suffix program _ _ _ b2
  have b4 := BlockAt.suffix program _ _ _ b3
  have b5 := BlockAt.suffix program _ _ _ b4
  refine ⟨BlockAt.prefix program base _ _ block, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [UniformDAGDispatch.code_length] using BlockAt.prefix program _ _ _ b1
  · simpa only [UniformDAGDispatch.code_length, constantReturn_length, Nat.add_assoc] using
      BlockAt.prefix program _ _ _ b2
  · simpa only [UniformDAGDispatch.code_length, constantReturn_length, Nat.add_assoc] using
      BlockAt.prefix program _ _ _ b3
  · simpa only [UniformDAGDispatch.code_length, constantReturn_length, inputCode_length,
      Nat.add_assoc] using BlockAt.prefix program _ _ _ b4
  · simpa only [UniformDAGDispatch.code_length, constantReturn_length, inputCode_length,
      childrenCode_length, Nat.add_assoc] using b5

theorem constant_execution (program : Program width 4) (s : State width 4)
    (base : ℕ) (value : Bool) (pc : s.pc = word width base) (running : s.halted = false)
    (fits : base + 2 < 2 ^ width) (room : s.heap.size < 2 ^ width)
    (block : BlockAt program base (constantCode width value)) :
    ∃ final, Execution program s final 2 (s.liveWords + 1) ∧
      final.reg 2 = boolWord width value ∧ final.reg 3 = s.reg 3 ∧
      final.heap = s.heap.push (boolWord width value) ∧
      final.stack = s.stack ∧ final.output = s.output ∧
      final.pc = word width (base + 2) ∧ final.halted = false := by
  let ready := s.advance.put 2 (boolWord width value)
  let final := { ready.advance with heap := s.heap.push (boolWord width value) }
  have pcVal : s.pc.val = base := by
    rw [pc]; exact Nat.mod_eq_of_lt (by omega)
  have readyPC : ready.pc = word width (base + 1) := by
    simp [ready, State.put, State.advance, pcVal]
  have readyVal : ready.pc.val = base + 1 := by
    rw [readyPC]; exact Nat.mod_eq_of_lt (by omega)
  have first : programStep program s = some ready := by
    unfold programStep
    rw [pcVal, show program[base]? = some (.constant 2 (boolWord width value)) from
      by simpa [constantCode] using block 0 (by simp [constantCode])]
    simp [step, ready, running]
  have last : programStep program ready = some final := by
    unfold programStep
    rw [readyVal, show program[base + 1]? = some (.allocate 2) from
      by simpa [constantCode] using block 1 (by simp [constantCode])]
    simp [step, ready, final, State.put, State.advance, running, room]
  refine ⟨final, ?_, ?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
  · have trace := Execution.cons first (Execution.cons last (Execution.refl final))
    have rlive : ready.liveWords = s.liveWords := rfl
    have flive : final.liveWords = s.liveWords + 1 := by
      simp [final, ready, State.put, State.advance, State.liveWords]; omega
    simpa only [rlive, flive, Nat.max_self,
      Nat.max_eq_right (by omega : s.liveWords ≤ s.liveWords + 1)] using trace
  · simp [final, ready, State.advance, State.put]
  · simp [final, ready, State.advance, State.put]
  · simp [final, State.advance, readyVal, Nat.add_assoc]
  · simp [final, ready, State.advance, State.put, running]


theorem constant_return (program : Program width 4) (s : State width 4)
    (entry base : Nat) (value : Bool)
    (pc : s.pc = word width entry) (running : s.halted = false)
    (fits : entry + 4 < 2 ^ width) (room : s.heap.size < 2 ^ width)
    (block : BlockAt program entry (constantReturn width base value)) :
    ∃ final, Execution program s final 4 (s.liveWords + 1) ∧
      final.heap = s.heap.push (boolWord width value) ∧
      final.stack = s.stack ∧ final.output = s.output ∧
      final.pc = word width (base + 100) ∧ final.halted = false := by
  obtain ⟨middle, trace, _, _, heap, stack, output, position, active⟩ :=
    constant_execution program s entry value pc running (by omega) room
      (BlockAt.prefix program entry _ _ block)
  have tail : BlockAt program (entry + 2) (UniformDAGNode.jumpCode width (base + 100)) := by
    simpa only [constantCode_length] using BlockAt.suffix program entry _ _ block
  obtain ⟨final, jump, fh, fs, fo, fp, fr⟩ :=
    UniformDAGNode.jump program middle (entry + 2) (base + 100) position active fits tail
  have live : middle.liveWords = s.liveWords + 1 := by
    simp [State.liveWords, heap, stack, output]; omega
  exact ⟨final, by simpa only [live, Nat.max_self] using trace.append jump,
    fh.trans heap, fs.trans stack, fo.trans output, fp, fr⟩

theorem input_return (program : Program width 4) (s : State width 4)
    (base offset identifier : Nat) (layout : Layout) (value : Bool)
    (offsetHeld : s.reg 3 = word width offset)
    (headBound : layout.headBase + offset < s.heap.size)
    (valueBound : layout.channelBase + identifier < s.heap.size)
    (source : s.heap[layout.headBase + offset] = word width identifier)
    (stored : s.heap[layout.channelBase + identifier] = boolWord width value)
    (pc : s.pc = word width (base + 22)) (running : s.halted = false)
    (fits : base + 100 < 2 ^ width) (room : s.heap.size < 2 ^ width)
    (block : BlockAt program (base + 22) (inputCode width base layout)) :
    ∃ final, Execution program s final 9 (s.liveWords + 1) ∧
      final.heap = s.heap.push (boolWord width value) ∧
      final.stack = s.stack ∧ final.output = s.output ∧
      final.pc = word width (base + 100) ∧ final.halted = false := by
  have first := BlockAt.prefix program (base + 22) _ _ block
  have rest := BlockAt.suffix program (base + 22) _ _ block
  have input : BlockAt program (base + 23) (UniformDAGInputGate.code width layout.headBase) := by
    simpa only [List.length_singleton, Nat.add_assoc] using BlockAt.prefix program _ _ _ rest
  have tail : BlockAt program (base + 29) (UniformDAGNode.jumpCode width (base + 100)) := by
    simpa only [List.length_singleton, UniformDAGInputGate.code_length, Nat.add_assoc] using
      BlockAt.suffix program _ _ _ rest
  obtain ⟨ready, setup, r1, r3, rh, rs, ro, rp, rr⟩ :=
    UniformDAGNode.initialize_value program s (base + 22) layout.channelBase pc running (by omega) first
  obtain ⟨middle, run, _, _, mh, ms, mo, mp, mr⟩ :=
    UniformDAGInputGate.execution program ready (base + 23) layout.headBase layout.channelBase offset
      identifier value (r3.trans offsetHeld) r1 (by omega) (by omega)
      (by simpa [rh] using headBound) (by simpa [rh] using valueBound)
      (by simpa [rh] using source) (by simpa [rh] using stored)
      (by simpa only [Nat.add_assoc] using rp) rr (by omega) (by simpa [rh] using room) input
  obtain ⟨final, jump, fh, fs, fo, fp, fr⟩ :=
    UniformDAGNode.jump program middle (base + 29) (base + 100)
      (by simpa only [Nat.add_assoc] using mp) mr (by omega) tail
  have rl : ready.liveWords = s.liveWords := by simp [State.liveWords, rh, rs, ro]
  have ml : middle.liveWords = s.liveWords + 1 := by
    simp [State.liveWords, mh, ms, mo, rh, rs, ro]; omega
  refine ⟨final, ?_, by simpa only [rh] using fh.trans mh,
    fs.trans (ms.trans rs), fo.trans (mo.trans ro), fp, fr⟩
  simpa only [rl, ml, Nat.max_eq_right (by omega : s.liveWords ≤ s.liveWords + 1),
    Nat.max_self] using (setup.append run).append jump

theorem arity_execution (program : Program width 4) (s : State width 4)
    (base offset count : Nat) (layout : Layout)
    (offsetHeld : s.reg 3 = word width offset)
    (bound : layout.childArityBase + offset < s.heap.size)
    (stored : s.heap[layout.childArityBase + offset] = word width count)
    (countFits : count < 2 ^ width)
    (pc : s.pc = word width (base + 31)) (running : s.halted = false)
    (fits : base + 100 < 2 ^ width) (room : s.heap.size < 2 ^ width)
    (block : BlockAt program (base + 31) (arityCode width base layout)) :
    ∃ final, Execution program s final 4 s.liveWords ∧
      final.heap = s.heap ∧ final.stack = s.stack ∧ final.output = s.output ∧
      final.reg 3 = s.reg 3 ∧
      final.pc = word width (if count = 0 then base + 14 else base + 35) ∧
      final.halted = false := by
  let a := s.advance.put 0 (word width layout.childArityBase)
  let b := a.advance.put 0 (word width (layout.childArityBase + offset))
  let c := b.advance.put 0 (word width count)
  let final := { c.advance with pc := word width (if count = 0 then base + 14 else base + 35) }
  have baseVal : (word width layout.childArityBase).val = layout.childArityBase := Nat.mod_eq_of_lt (by omega)
  have offVal : (word width offset).val = offset := Nat.mod_eq_of_lt (by omega)
  have addrVal : (word width (layout.childArityBase + offset)).val = layout.childArityBase + offset :=
    Nat.mod_eq_of_lt (by omega)
  have countVal : (word width count).val = count := Nat.mod_eq_of_lt countFits
  have pa : a.pc = word width (base + 32) := by
    simp [a, State.put, State.advance, pc, word,
      Nat.mod_eq_of_lt (by omega : base + 31 < 2 ^ width), Nat.add_assoc]
  have pb : b.pc = word width (base + 33) := by
    simp [b, State.put, State.advance, pa, Nat.mod_eq_of_lt (by omega : base + 32 < 2 ^ width), Nat.add_assoc, word]
  have pc' : c.pc = word width (base + 34) := by
    simp [c, State.put, State.advance, pb, Nat.mod_eq_of_lt (by omega : base + 33 < 2 ^ width), Nat.add_assoc, word]
  have t0 : programStep program s = some a := by
    unfold programStep
    rw [pc, show (word width (base + 31)).val = base + 31 from Nat.mod_eq_of_lt (by omega),
      show program[base + 31]? = some (.constant 0 (word width layout.childArityBase)) from
        (by simpa [arityCode] using block 0 (by simp))]
    simp [step, running, a]
  have t1 : programStep program a = some b := by
    unfold programStep
    rw [pa, show (word width (base + 32)).val = base + 32 from Nat.mod_eq_of_lt (by omega),
      show program[base + 32]? = some (.add 0 0 3) from (by simpa [arityCode, Nat.add_assoc] using block 1 (by simp))]
    simp [step, a, b, State.put, State.advance, running, offsetHeld, baseVal, offVal]
  have t2 : programStep program b = some c := by
    unfold programStep
    rw [pb, show (word width (base + 33)).val = base + 33 from Nat.mod_eq_of_lt (by omega),
      show program[base + 33]? = some (.load 0 0) from (by simpa [arityCode, Nat.add_assoc] using block 2 (by simp))]
    simp [step, a, b, c, State.put, State.advance, running, addrVal, bound, stored]
  have t3 : programStep program c = some final := by
    unfold programStep
    rw [pc', show (word width (base + 34)).val = base + 34 from Nat.mod_eq_of_lt (by omega),
      show program[base + 34]? = some (.branchZero 0 (word width (base + 14))) from
        (by simpa [arityCode, Nat.add_assoc] using block 3 (by simp))]
    by_cases zero : count = 0
    · simp [step, a, b, c, final, State.put, State.advance, running, zero, word]
    · have cv : c.pc.val = base + 34 := by rw [pc']; exact Nat.mod_eq_of_lt (by omega)
      have nonzero : word width count ≠ 0 := by
        intro equality
        have := congrArg Fin.val equality
        simp only [countVal, Fin.val_zero] at this
        exact zero this
      simp [step, final, show c.halted = false from running, show c.reg 0 = word width count from by simp [c, State.put],
        nonzero, zero, State.advance, cv, Nat.add_assoc]
  refine ⟨final, ?_, rfl, rfl, rfl, ?_, rfl, running⟩
  · simpa [final, c, b, a, State.liveWords, State.put, State.advance] using
      Execution.cons t0 (Execution.cons t1 (Execution.cons t2 (Execution.cons t3 (Execution.refl final))))
  · simp [final, c, b, a, State.put, State.advance]

theorem children_return (program : Program width 4) (s : State width 4)
    (base offset cursor : Nat) (layout : Layout) (values : List Bool) (empty : Bool)
    (offsetHeld : s.reg 3 = word width offset)
    (arityBound : layout.childArityBase + offset < s.heap.size)
    (sourceBound : layout.childSourceBase + offset < s.heap.size)
    (arityCell : s.heap[layout.childArityBase + offset] = word width values.length)
    (sourceCell : s.heap[layout.childSourceBase + offset] = word width cursor)
    (cursorFits : cursor + values.length < 2 ^ width)
    (cells : UniformDAGScanLoop.Stored s.heap layout.nodeBase cursor values)
    (pc : s.pc = word width (base + 31)) (running : s.halted = false)
    (fits : base + 100 < 2 ^ width) (room : s.heap.size < 2 ^ width)
    (block : BlockAt program (base + 31) (childrenCode width base layout))
    (zeroBlock : BlockAt program (base + 14) (constantReturn width base empty)) :
    ∃ final ticks peak, Execution program s final ticks peak ∧
      ticks ≤ 18 * values.length + 18 ∧ peak ≤ s.liveWords + 2 ∧
      final.heap = s.heap.push (boolWord width (if values = [] then empty else values.any (fun x => x))) ∧
      final.stack = s.stack ∧ final.output = s.output ∧
      final.pc = word width (base + 100) ∧ final.halted = false := by
  have first := BlockAt.prefix program (base + 31) _ _ block
  have rest := BlockAt.suffix program (base + 31) _ _ block
  obtain ⟨ready, test, rh, rs, ro, r3, rp, rr⟩ :=
    arity_execution program s base offset values.length layout offsetHeld arityBound arityCell
      (by omega) pc running fits room first
  have rl : ready.liveWords = s.liveWords := by simp [State.liveWords, rh, rs, ro]
  by_cases emptyValues : values = []
  · obtain ⟨final, trace, fh, fs, fo, fp, fr⟩ :=
      constant_return program ready (base + 14) base empty
        (by simpa [emptyValues] using rp) rr (by omega) (by simpa [rh] using room) zeroBlock
    refine ⟨final, 8, s.liveWords + 1, ?_, by simp [emptyValues], by omega,
      ?_, fs.trans rs, fo.trans ro, fp, fr⟩
    · simpa only [rl, Nat.max_eq_right (by omega : s.liveWords ≤ s.liveWords + 1)] using test.append trace
    · simpa [rh, emptyValues] using fh
  · have positive : values.length ≠ 0 := by simpa using emptyValues
    have kernel : BlockAt program (base + 35)
        (UniformDAGOrGate.code width (base + 35) layout.nodeBase layout.childArityBase layout.childSourceBase) := by
      simpa only [arityCode_length, Nat.add_assoc] using BlockAt.prefix program _ _ _ rest
    have tail : BlockAt program (base + 63) (UniformDAGNode.jumpCode width (base + 100)) := by
      simpa only [arityCode_length, UniformDAGOrGate.code_length, Nat.add_assoc] using
        BlockAt.suffix program _ _ _ rest
    obtain ⟨middle, ticks, peak, trace, time, space, mh, ms, mo, mp, mr⟩ :=
      UniformDAGOrGate.execution program ready (base + 35) layout.nodeBase layout.childArityBase
        layout.childSourceBase offset cursor values (r3.trans offsetHeld) (by omega) (by omega)
        (by simpa [rh] using arityBound) (by simpa [rh] using sourceBound)
        (by simpa [rh] using arityCell) (by simpa [rh] using sourceCell)
        cursorFits (by omega) (by simpa [rh] using cells)
        (by simpa [positive] using rp) rr (by omega) (by simpa [rh] using room) kernel
    obtain ⟨final, jump, fh, fs, fo, fp, fr⟩ :=
      UniformDAGNode.jump program middle (base + 63) (base + 100)
        (by simpa only [Nat.add_assoc] using mp) mr (by omega) tail
    have ml : middle.liveWords = s.liveWords + 1 := by
      simp [State.liveWords, mh, ms, mo, rh, rs, ro]; omega
    refine ⟨final, 4 + ticks + 2, max (max s.liveWords peak) middle.liveWords,
      (test.append trace).append jump, by omega, ?_, ?_, fs.trans (ms.trans rs), fo.trans (mo.trans ro), fp, fr⟩
    · rw [rl] at space; omega
    · simpa only [rh, emptyValues, ite_false, id] using fh.trans mh

theorem guard_return (program : Program width 4) (s : State width 4)
    (base offset childID cursor : Nat) (layout : Layout) (child : Bool) (guards : List Bool)
    (offsetHeld : s.reg 3 = word width offset)
    (headBound : layout.headBase + offset < s.heap.size)
    (childBound : layout.nodeBase + childID < s.heap.size)
    (headCell : s.heap[layout.headBase + offset] = word width childID)
    (childCell : s.heap[layout.nodeBase + childID] = boolWord width child)
    (arityBound : layout.guardArityBase + offset < s.heap.size)
    (sourceBound : layout.guardSourceBase + offset < s.heap.size)
    (arityCell : s.heap[layout.guardArityBase + offset] = word width guards.length)
    (sourceCell : s.heap[layout.guardSourceBase + offset] = word width cursor)
    (cursorFits : cursor + guards.length < 2 ^ width)
    (cells : UniformDAGScanLoop.Stored s.heap layout.channelBase cursor guards)
    (pc : s.pc = word width (base + 65)) (running : s.halted = false)
    (fits : base + 100 < 2 ^ width) (room : s.heap.size < 2 ^ width)
    (block : BlockAt program (base + 65) (guardCode width base layout)) :
    ∃ final ticks peak, Execution program s final ticks peak ∧
      ticks ≤ 18 * guards.length + 19 ∧ peak ≤ s.liveWords + 2 ∧
      final.heap = s.heap.push (boolWord width (child || guards.any (fun x => x))) ∧
      final.stack = s.stack ∧ final.output = s.output ∧
      final.pc = word width (base + 100) ∧ final.halted = false := by
  have first := BlockAt.prefix program (base + 65) _ _ block
  have rest := BlockAt.suffix program (base + 65) _ _ block
  have kernel : BlockAt program (base + 66)
      (LiteralGuardUnion.code width (base + 66) layout.headBase layout.channelBase
        layout.guardArityBase layout.guardSourceBase) := by
    simpa only [List.length_singleton, Nat.add_assoc] using BlockAt.prefix program _ _ _ rest
  have tail : BlockAt program (base + 98) (UniformDAGNode.jumpCode width (base + 100)) := by
    simpa only [List.length_singleton, LiteralGuardUnion.code_length, Nat.add_assoc] using
      BlockAt.suffix program _ _ _ rest
  obtain ⟨ready, setup, r1, r3, rh, rs, ro, rp, rr⟩ :=
    UniformDAGNode.initialize_value program s (base + 65) layout.nodeBase pc running (by omega) first
  obtain ⟨middle, ticks, peak, trace, time, space, mh, ms, mo, mp, mr⟩ :=
    LiteralGuardUnion.execution program ready (base + 66) layout.headBase layout.nodeBase layout.channelBase
      layout.guardArityBase layout.guardSourceBase offset childID cursor child guards
      (r3.trans offsetHeld) r1 (by omega) (by omega)
      (by simpa [rh] using headBound) (by simpa [rh] using childBound)
      (by simpa [rh] using headCell) (by simpa [rh] using childCell)
      (by omega) (by omega) (by simpa [rh] using arityBound) (by simpa [rh] using sourceBound)
      (by simpa [rh] using arityCell) (by simpa [rh] using sourceCell)
      cursorFits (by omega) (by simpa [rh] using cells)
      (by simpa only [Nat.add_assoc] using rp) rr (by omega) (by simpa [rh] using room) kernel
  obtain ⟨final, jump, fh, fs, fo, fp, fr⟩ :=
    UniformDAGNode.jump program middle (base + 98) (base + 100)
      (by simpa only [Nat.add_assoc] using mp) mr (by omega) tail
  have rl : ready.liveWords = s.liveWords := by simp [State.liveWords, rh, rs, ro]
  have ml : middle.liveWords = s.liveWords + 1 := by
    simp [State.liveWords, mh, ms, mo, rh, rs, ro]; omega
  refine ⟨final, 1 + ticks + 2, max (max s.liveWords peak) middle.liveWords,
    (setup.append trace).append jump, by omega, ?_, ?_, fs.trans (ms.trans rs), fo.trans (mo.trans ro), fp, fr⟩
  · rw [rl] at space; omega
  · simpa only [rh, id] using fh.trans mh

end Controller.Cost.LiteralSourceNode
