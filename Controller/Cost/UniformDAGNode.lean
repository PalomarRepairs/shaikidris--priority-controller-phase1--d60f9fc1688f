module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.UniformDAGDispatch
public import Controller.Cost.UniformDAGOrGate

@[expose] public section

/-! One fixed node program combines the cached-tag dispatcher with all five
runtime gate handlers. Every handler returns to the same next-node address.
The row offset and loop counters are held by the caller's stack. -/
namespace Controller.Cost.UniformDAGNode
open Controller.Cost.GateProgram

structure Layout where
  tagBase : ℕ
  headBase : ℕ
  channelBase : ℕ
  nodeBase : ℕ
  childArityBase : ℕ
  childSourceBase : ℕ
  guardArityBase : ℕ
  guardSourceBase : ℕ

def jumpCode (width target : ℕ) : Code width :=
  [.constant 0 (word width 0), .branchZero 0 (word width target)]
@[simp] theorem jumpCode_length : (jumpCode width target).length = 2 := rfl

def destinations (base : ℕ) (tag : Fin 5) : ℕ :=
  match tag.val with
  | 0 => base + 14 | 1 => base + 18 | 2 => base + 27
  | 3 => base + 57 | _ => base + 92

def zeroCode (width base : ℕ) : Code width :=
  UniformDAGZeroGate.code width ++ jumpCode width (base + 109)
def inputCode (width base : ℕ) (layout : Layout) : Code width :=
  [.constant 1 (word width layout.channelBase)] ++
    (UniformDAGInputGate.code width layout.headBase ++ jumpCode width (base + 109))
def orCode (width base : ℕ) (layout : Layout) : Code width :=
  UniformDAGOrGate.code width (base + 27) layout.nodeBase layout.childArityBase layout.childSourceBase ++
    jumpCode width (base + 109)
def guardCode (width base : ℕ) (layout : Layout) : Code width :=
  [.constant 1 (word width layout.nodeBase)] ++
    (UniformDAGGuardGate.code width (base + 58) layout.headBase layout.channelBase
      layout.guardArityBase layout.guardSourceBase ++ jumpCode width (base + 109))
def andCode (width base : ℕ) (layout : Layout) : Code width :=
  [.constant 1 (word width layout.nodeBase)] ++
    UniformDAGAndGate.code width (base + 93) layout.headBase layout.childSourceBase

def code (width base : ℕ) (layout : Layout) : Code width :=
  UniformDAGDispatch.code width layout.tagBase (destinations base) ++
    (zeroCode width base ++ (inputCode width base layout ++
      (orCode width base layout ++ (guardCode width base layout ++ andCode width base layout))))
@[simp] theorem zeroCode_length : (zeroCode width base).length = 4 := rfl
@[simp] theorem inputCode_length : (inputCode width base layout).length = 9 := rfl
@[simp] theorem orCode_length : (orCode width base layout).length = 30 := rfl
@[simp] theorem guardCode_length : (guardCode width base layout).length = 35 := rfl
@[simp] theorem andCode_length : (andCode width base layout).length = 17 := rfl
@[simp] theorem code_length : (code width base layout).length = 109 := rfl

private theorem fetched (program : Program width 4) (s : State width 4)
    (address : ℕ) (instruction : Instruction width 4)
    (pc : s.pc = word width address) (fits : address < 2 ^ width)
    (entry : program[address]? = some instruction) :
    programStep program s = step instruction s := by
  unfold programStep
  rw [pc, show (word width address).val = address from Nat.mod_eq_of_lt fits, entry]
  rfl

/-- One fetched initialization preserves all source cells and caller frames. -/
theorem initialize_value (program : Program width 4) (s : State width 4)
    (base valueBase : ℕ) (pc : s.pc = word width base) (running : s.halted = false)
    (fits : base + 1 < 2 ^ width)
    (block : BlockAt program base ([.constant 1 (word width valueBase)] : Code width)) :
    ∃ ready, Execution program s ready 1 s.liveWords ∧
      ready.reg 1 = word width valueBase ∧ ready.reg 3 = s.reg 3 ∧
      ready.heap = s.heap ∧ ready.stack = s.stack ∧ ready.output = s.output ∧
      ready.pc = word width (base + 1) ∧ ready.halted = false := by
  let ready := s.advance.put 1 (word width valueBase)
  have pv : s.pc.val = base := by rw [pc]; exact Nat.mod_eq_of_lt (by omega)
  have actual : programStep program s = some ready := by
    rw [fetched program s base (.constant 1 (word width valueBase)) pc (by omega)
      (block 0 (by simp))]
    simp [step, ready, running]
  refine ⟨ready, ?_, ?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
  · have live : ready.liveWords = s.liveWords := rfl
    simpa only [live, Nat.max_self] using Execution.cons actual (Execution.refl ready)
  all_goals simp [ready, State.advance, State.put, running, pv]

/-- A two-instruction return preserves the allocated value table and caller. -/
theorem jump (program : Program width 4) (s : State width 4)
    (base target : ℕ) (pc : s.pc = word width base) (running : s.halted = false)
    (fits : base + 2 < 2 ^ width) (block : BlockAt program base (jumpCode width target)) :
    ∃ final, Execution program s final 2 s.liveWords ∧
      final.heap = s.heap ∧ final.stack = s.stack ∧ final.output = s.output ∧
      final.pc = word width target ∧ final.halted = false := by
  let ready := s.advance.put 0 (word width 0)
  let final := { ready with pc := word width target }
  have pv : s.pc.val = base := by rw [pc]; exact Nat.mod_eq_of_lt (by omega)
  have readyPC : ready.pc = word width (base + 1) := by
    simp [ready, State.put, State.advance, pv]
  have first : programStep program s = some ready := by
    rw [fetched program s base (.constant 0 (word width 0)) pc (by omega)
      (by simpa [jumpCode] using block 0 (by simp [jumpCode]))]
    simp [step, ready, running]
  have last : programStep program ready = some final := by
    rw [fetched program ready (base + 1) (.branchZero 0 (word width target)) readyPC (by omega)
      (by simpa [jumpCode] using block 1 (by simp [jumpCode]))]
    simp [step, ready, final, State.advance, State.put, running, word]
  refine ⟨final, ?_, rfl, rfl, rfl, rfl, ?_⟩
  · have rl : ready.liveWords = s.liveWords := rfl
    have fl : final.liveWords = s.liveWords := rfl
    simpa only [rl, fl, Nat.max_self] using
      Execution.cons first (Execution.cons last (Execution.refl final))
  · simp [final, ready, State.advance, State.put, running]

/-- The zero handler joins actual tag fetch, false allocation and shared return. -/
theorem execution_zero (program : Program width 4) (s : State width 4)
    (base offset : ℕ) (layout : Layout)
    (offsetHeld : s.reg 3 = word width offset)
    (addressFits : layout.tagBase + offset < 2 ^ width)
    (addressBound : layout.tagBase + offset < s.heap.size)
    (source : s.heap[layout.tagBase + offset]'addressBound = word width 0)
    (pc : s.pc = word width base) (running : s.halted = false)
    (fits : base + 109 < 2 ^ width) (room : s.heap.size < 2 ^ width)
    (block : BlockAt program base (code width base layout)) :
    ∃ final, Execution program s final 8 (s.liveWords + 1) ∧
      final.heap = s.heap.push (boolWord width false) ∧
      final.stack = s.stack ∧ final.output = s.output ∧
      final.pc = word width (base + 109) ∧ final.halted = false := by
  let rest := zeroCode width base ++ (inputCode width base layout ++
    (orCode width base layout ++ (guardCode width base layout ++ andCode width base layout)))
  have dispatchBlock := BlockAt.prefix program base
    (UniformDAGDispatch.code width layout.tagBase (destinations base)) rest block
  have tailBlock : BlockAt program (base + 14) rest := by
    simpa only [UniformDAGDispatch.code_length] using BlockAt.suffix program base
      (UniformDAGDispatch.code width layout.tagBase (destinations base)) rest block
  have zeroBlock := BlockAt.prefix program (base + 14) (zeroCode width base)
    (inputCode width base layout ++ (orCode width base layout ++
      (guardCode width base layout ++ andCode width base layout))) tailBlock
  have kernel := BlockAt.prefix program (base + 14) (UniformDAGZeroGate.code width)
    (jumpCode width (base + 109)) zeroBlock
  have finish : BlockAt program (base + 16) (jumpCode width (base + 109)) := by
    simpa only [UniformDAGZeroGate.code_length, Nat.add_assoc] using
      BlockAt.suffix program (base + 14) (UniformDAGZeroGate.code width) _ zeroBlock
  obtain ⟨selected, dt, d0, d1, d3, dh, ds, dout, dp, dr⟩ :=
    UniformDAGDispatch.execution program s base layout.tagBase offset 0 (destinations base)
      offsetHeld addressFits addressBound source pc running (by omega) dispatchBlock
  obtain ⟨allocated, allocTrace, a2, a3, ah, ast, ao, ap, ar⟩ :=
    UniformDAGZeroGate.execution program selected (base + 14)
      (by simpa [destinations] using dp) dr (by omega) (by simpa [dh] using room) kernel
  obtain ⟨final, jt, fh, fs, fo, fp, fr⟩ := jump program allocated (base + 16) (base + 109)
    (by simpa [Nat.add_assoc] using ap) ar (by omega) finish
  have sl : selected.liveWords = s.liveWords := by simp [State.liveWords, dh, ds, dout]
  have al : allocated.liveWords = s.liveWords + 1 := by
    simp [State.liveWords, ah, dh, ast, ds, ao, dout]; omega
  refine ⟨final, ?_, ?_, fs.trans (ast.trans ds), fo.trans (ao.trans dout), fp, fr⟩
  · have joined := (dt.append allocTrace).append jt
    simpa [sl, al, Nat.max_eq_right (by omega : s.liveWords ≤ s.liveWords + 1)] using joined
  · simpa [fh, ah, dh]

/-- The input handler fetches its source channel, reads its stored value,
allocates the node result and returns to the common next-node address. -/
theorem execution_input (program : Program width 4) (s : State width 4)
    (base offset identifier : ℕ) (layout : Layout) (value : Bool)
    (offsetHeld : s.reg 3 = word width offset)
    (tagFits : layout.tagBase + offset < 2 ^ width)
    (headFits : layout.headBase + offset < 2 ^ width)
    (valueFits : layout.channelBase + identifier < 2 ^ width)
    (tagBound : layout.tagBase + offset < s.heap.size)
    (headBound : layout.headBase + offset < s.heap.size)
    (valueBound : layout.channelBase + identifier < s.heap.size)
    (tagCell : s.heap[layout.tagBase + offset]'tagBound = word width 1)
    (headCell : s.heap[layout.headBase + offset]'headBound = word width identifier)
    (valueCell : s.heap[layout.channelBase + identifier]'valueBound = boolWord width value)
    (pc : s.pc = word width base) (running : s.halted = false)
    (fits : base + 109 < 2 ^ width) (room : s.heap.size < 2 ^ width)
    (block : BlockAt program base (code width base layout)) :
    ∃ final, Execution program s final 16 (s.liveWords + 1) ∧
      final.heap = s.heap.push (boolWord width value) ∧
      final.stack = s.stack ∧ final.output = s.output ∧
      final.pc = word width (base + 109) ∧ final.halted = false := by
  let rest := zeroCode width base ++ (inputCode width base layout ++
    (orCode width base layout ++ (guardCode width base layout ++ andCode width base layout)))
  have dispatchBlock := BlockAt.prefix program base
    (UniformDAGDispatch.code width layout.tagBase (destinations base)) rest block
  have restBlock : BlockAt program (base + 14) rest := by
    simpa only [UniformDAGDispatch.code_length] using BlockAt.suffix program base
      (UniformDAGDispatch.code width layout.tagBase (destinations base)) rest block
  have afterZero : BlockAt program (base + 18)
      (inputCode width base layout ++ (orCode width base layout ++
        (guardCode width base layout ++ andCode width base layout))) := by
    simpa only [zeroCode_length, Nat.add_assoc] using BlockAt.suffix program (base + 14)
      (zeroCode width base) _ restBlock
  have inputBlock := BlockAt.prefix program (base + 18) (inputCode width base layout)
    (orCode width base layout ++ (guardCode width base layout ++ andCode width base layout)) afterZero
  have initBlock := BlockAt.prefix program (base + 18)
    ([.constant 1 (word width layout.channelBase)] : Code width)
    (UniformDAGInputGate.code width layout.headBase ++ jumpCode width (base + 109)) inputBlock
  have bodyBlock : BlockAt program (base + 19)
      (UniformDAGInputGate.code width layout.headBase ++ jumpCode width (base + 109)) := by
    simpa only [List.length_singleton, Nat.add_assoc] using BlockAt.suffix program (base + 18)
      ([.constant 1 (word width layout.channelBase)] : Code width) _ inputBlock
  have kernel := BlockAt.prefix program (base + 19) (UniformDAGInputGate.code width layout.headBase)
    (jumpCode width (base + 109)) bodyBlock
  have finish : BlockAt program (base + 25) (jumpCode width (base + 109)) := by
    simpa only [UniformDAGInputGate.code_length, Nat.add_assoc] using
      BlockAt.suffix program (base + 19) (UniformDAGInputGate.code width layout.headBase) _ bodyBlock
  obtain ⟨selected, dt, d0, d1, d3, dh, ds, dout, dp, dr⟩ :=
    UniformDAGDispatch.execution program s base layout.tagBase offset 1 (destinations base)
      offsetHeld tagFits tagBound tagCell pc running (by omega) dispatchBlock
  obtain ⟨ready, it, i1, i3, ih, ist, io, ip, ir⟩ := initialize_value program selected (base + 18)
    layout.channelBase (by simpa [destinations] using dp) dr (by omega) initBlock
  obtain ⟨allocated, allocTrace, a2, a3, ah, ast, ao, ap, ar⟩ :=
    UniformDAGInputGate.execution program ready (base + 19) layout.headBase layout.channelBase
      offset identifier value (i3.trans (d3.trans offsetHeld)) i1 headFits valueFits
      (by simpa [ih, dh] using headBound) (by simpa [ih, dh] using valueBound)
      (by simpa [ih, dh] using headCell) (by simpa [ih, dh] using valueCell)
      ip ir (by omega) (by simpa [ih, dh] using room) kernel
  obtain ⟨final, jt, fh, fs, fo, fp, fr⟩ := jump program allocated (base + 25) (base + 109)
    (by simpa [Nat.add_assoc] using ap) ar (by omega) finish
  have sl : selected.liveWords = s.liveWords := by simp [State.liveWords, dh, ds, dout]
  have il : ready.liveWords = s.liveWords := by simp [State.liveWords, ih, dh, ist, ds, io, dout]
  have al : allocated.liveWords = s.liveWords + 1 := by
    simp [State.liveWords, ah, ih, dh, ast, ist, ds, ao, io, dout]; omega
  refine ⟨final, ?_, ?_, fs.trans (ast.trans (ist.trans ds)), fo.trans (ao.trans (io.trans dout)), fp, fr⟩
  · have joined := ((dt.append it).append allocTrace).append jt
    simpa [sl, il, al, Nat.max_eq_right (by omega : s.liveWords ≤ s.liveWords + 1)] using joined
  · simpa [fh, ah, ih, dh]

private theorem handler_blocks (program : Program width 4) (base : ℕ) (layout : Layout)
    (block : BlockAt program base (code width base layout)) :
    BlockAt program base (UniformDAGDispatch.code width layout.tagBase (destinations base)) ∧
    BlockAt program (base + 27) (orCode width base layout) ∧
    BlockAt program (base + 57) (guardCode width base layout) ∧
    BlockAt program (base + 92) (andCode width base layout) := by
  let tail := zeroCode width base ++ (inputCode width base layout ++
    (orCode width base layout ++ (guardCode width base layout ++ andCode width base layout)))
  have dispatch := BlockAt.prefix program base
    (UniformDAGDispatch.code width layout.tagBase (destinations base)) tail block
  have rest : BlockAt program (base + 14) tail := by
    simpa only [UniformDAGDispatch.code_length] using BlockAt.suffix program base
      (UniformDAGDispatch.code width layout.tagBase (destinations base)) tail block
  have afterZero : BlockAt program (base + 18)
      (inputCode width base layout ++ (orCode width base layout ++
        (guardCode width base layout ++ andCode width base layout))) := by
    simpa only [zeroCode_length, Nat.add_assoc] using
      BlockAt.suffix program (base + 14) (zeroCode width base) _ rest
  have afterInput : BlockAt program (base + 27)
      (orCode width base layout ++ (guardCode width base layout ++ andCode width base layout)) := by
    simpa only [inputCode_length, Nat.add_assoc] using
      BlockAt.suffix program (base + 18) (inputCode width base layout) _ afterZero
  have orBlock := BlockAt.prefix program (base + 27) (orCode width base layout)
    (guardCode width base layout ++ andCode width base layout) afterInput
  have afterOr : BlockAt program (base + 57)
      (guardCode width base layout ++ andCode width base layout) := by
    simpa only [orCode_length, Nat.add_assoc] using
      BlockAt.suffix program (base + 27) (orCode width base layout) _ afterInput
  have guardBlock := BlockAt.prefix program (base + 57) (guardCode width base layout)
    (andCode width base layout) afterOr
  have andBlock : BlockAt program (base + 92) (andCode width base layout) := by
    simpa only [guardCode_length, Nat.add_assoc] using
      BlockAt.suffix program (base + 57) (guardCode width base layout) _ afterOr
  exact ⟨dispatch, orBlock, guardBlock, andBlock⟩

/-- The OR handler scans the actual stored child stream and returns its value. -/
theorem execution_or (program : Program width 4) (s : State width 4)
    (base offset cursor : ℕ) (layout : Layout) (values : List Bool)
    (offsetHeld : s.reg 3 = word width offset)
    (tagFits : layout.tagBase + offset < 2 ^ width)
    (tagBound : layout.tagBase + offset < s.heap.size)
    (tagCell : s.heap[layout.tagBase + offset]'tagBound = word width 2)
    (arityFits : layout.childArityBase + offset < 2 ^ width)
    (sourceFits : layout.childSourceBase + offset < 2 ^ width)
    (arityBound : layout.childArityBase + offset < s.heap.size)
    (sourceBound : layout.childSourceBase + offset < s.heap.size)
    (arityCell : s.heap[layout.childArityBase + offset]'arityBound = word width values.length)
    (sourceCell : s.heap[layout.childSourceBase + offset]'sourceBound = word width cursor)
    (cursorFits : cursor + values.length < 2 ^ width) (countFits : values.length < 2 ^ width)
    (cells : UniformDAGScanLoop.Stored s.heap layout.nodeBase cursor values)
    (pc : s.pc = word width base) (running : s.halted = false)
    (fits : base + 109 < 2 ^ width) (room : s.heap.size < 2 ^ width)
    (block : BlockAt program base (code width base layout)) :
    ∃ final ticks peak, Execution program s final ticks peak ∧
      ticks ≤ 18 * values.length + 23 ∧ peak ≤ s.liveWords + 2 ∧
      final.heap = s.heap.push (boolWord width (values.any (fun x => x))) ∧
      final.stack = s.stack ∧ final.output = s.output ∧
      final.pc = word width (base + 109) ∧ final.halted = false := by
  obtain ⟨dispatch, orBlock, guardBlock, andBlock⟩ := handler_blocks program base layout block
  have kernel := BlockAt.prefix program (base + 27)
    (UniformDAGOrGate.code width (base + 27) layout.nodeBase layout.childArityBase layout.childSourceBase)
    (jumpCode width (base + 109)) orBlock
  have finish : BlockAt program (base + 55) (jumpCode width (base + 109)) := by
    simpa only [UniformDAGOrGate.code_length, Nat.add_assoc] using BlockAt.suffix program (base + 27)
      (UniformDAGOrGate.code width (base + 27) layout.nodeBase layout.childArityBase layout.childSourceBase) _ orBlock
  obtain ⟨selected, dt, d0, d1, d3, dh, ds, dout, dp, dr⟩ :=
    UniformDAGDispatch.execution program s base layout.tagBase offset 2 (destinations base)
      offsetHeld tagFits tagBound tagCell pc running (by omega) dispatch
  obtain ⟨allocated, ticks, peak, ot, time, space, ah, ast, ao, ap, ar⟩ :=
    UniformDAGOrGate.execution program selected (base + 27) layout.nodeBase layout.childArityBase
      layout.childSourceBase offset cursor values (d3.trans offsetHeld) arityFits sourceFits
      (by simpa [dh] using arityBound) (by simpa [dh] using sourceBound)
      (by simpa [dh] using arityCell) (by simpa [dh] using sourceCell)
      cursorFits countFits (by simpa [dh] using cells)
      (by simpa [destinations] using dp) dr (by omega) (by simpa [dh] using room) kernel
  obtain ⟨final, jt, fh, fs, fo, fp, fr⟩ := jump program allocated (base + 55) (base + 109)
    (by simpa [Nat.add_assoc] using ap) ar (by omega) finish
  have sl : selected.liveWords = s.liveWords := by simp [State.liveWords, dh, ds, dout]
  have al : allocated.liveWords = s.liveWords + 1 := by
    simp [State.liveWords, ah, dh, ast, ds, ao, dout]; omega
  refine ⟨final, 9 + ticks + 2, max (max s.liveWords peak) allocated.liveWords, ?_, ?_, ?_,
    ?_, fs.trans (ast.trans ds), fo.trans (ao.trans dout), fp, fr⟩
  · simpa using (dt.append ot).append jt
  · omega
  · rw [sl] at space
    simp only [al, max_le_iff]
    exact ⟨⟨by omega, space⟩, by omega⟩
  · simpa [fh, ah, dh]

/-- The guarded handler reads its computed child, scans original channel
occurrences, allocates the result and returns to the shared continuation. -/
theorem execution_guard (program : Program width 4) (s : State width 4)
    (base offset childID cursor : ℕ) (layout : Layout) (child : Bool) (guards : List Bool)
    (offsetHeld : s.reg 3 = word width offset)
    (tagFits : layout.tagBase + offset < 2 ^ width)
    (tagBound : layout.tagBase + offset < s.heap.size)
    (tagCell : s.heap[layout.tagBase + offset]'tagBound = word width 3)
    (headFits : layout.headBase + offset < 2 ^ width)
    (childFits : layout.nodeBase + childID < 2 ^ width)
    (headBound : layout.headBase + offset < s.heap.size)
    (childBound : layout.nodeBase + childID < s.heap.size)
    (headCell : s.heap[layout.headBase + offset]'headBound = word width childID)
    (childCell : s.heap[layout.nodeBase + childID]'childBound = boolWord width child)
    (arityFits : layout.guardArityBase + offset < 2 ^ width)
    (sourceFits : layout.guardSourceBase + offset < 2 ^ width)
    (arityBound : layout.guardArityBase + offset < s.heap.size)
    (sourceBound : layout.guardSourceBase + offset < s.heap.size)
    (arityCell : s.heap[layout.guardArityBase + offset]'arityBound = word width guards.length)
    (sourceCell : s.heap[layout.guardSourceBase + offset]'sourceBound = word width cursor)
    (cursorFits : cursor + guards.length < 2 ^ width) (countFits : guards.length < 2 ^ width)
    (cells : UniformDAGScanLoop.Stored s.heap layout.channelBase cursor guards)
    (pc : s.pc = word width base) (running : s.halted = false)
    (fits : base + 109 < 2 ^ width) (room : s.heap.size < 2 ^ width)
    (block : BlockAt program base (code width base layout)) :
    ∃ final ticks peak, Execution program s final ticks peak ∧
      ticks ≤ 18 * guards.length + 30 ∧ peak ≤ s.liveWords + 2 ∧
      final.heap = s.heap.push (boolWord width (child && !(guards.any (fun x => x)))) ∧
      final.stack = s.stack ∧ final.output = s.output ∧
      final.pc = word width (base + 109) ∧ final.halted = false := by
  obtain ⟨dispatch, orBlock, guardBlock, andBlock⟩ := handler_blocks program base layout block
  have initBlock := BlockAt.prefix program (base + 57)
    ([.constant 1 (word width layout.nodeBase)] : Code width)
    (UniformDAGGuardGate.code width (base + 58) layout.headBase layout.channelBase
      layout.guardArityBase layout.guardSourceBase ++ jumpCode width (base + 109)) guardBlock
  have bodyBlock : BlockAt program (base + 58)
      (UniformDAGGuardGate.code width (base + 58) layout.headBase layout.channelBase
        layout.guardArityBase layout.guardSourceBase ++ jumpCode width (base + 109)) := by
    simpa only [List.length_singleton, Nat.add_assoc] using BlockAt.suffix program (base + 57)
      ([.constant 1 (word width layout.nodeBase)] : Code width) _ guardBlock
  have kernel := BlockAt.prefix program (base + 58)
    (UniformDAGGuardGate.code width (base + 58) layout.headBase layout.channelBase
      layout.guardArityBase layout.guardSourceBase) (jumpCode width (base + 109)) bodyBlock
  have finish : BlockAt program (base + 90) (jumpCode width (base + 109)) := by
    simpa only [UniformDAGGuardGate.code_length, Nat.add_assoc] using BlockAt.suffix program (base + 58)
      (UniformDAGGuardGate.code width (base + 58) layout.headBase layout.channelBase
        layout.guardArityBase layout.guardSourceBase) _ bodyBlock
  obtain ⟨selected, dt, d0, d1, d3, dh, ds, dout, dp, dr⟩ :=
    UniformDAGDispatch.execution program s base layout.tagBase offset 3 (destinations base)
      offsetHeld tagFits tagBound tagCell pc running (by omega) dispatch
  obtain ⟨ready, it, i1, i3, ih, ist, io, ip, ir⟩ := initialize_value program selected (base + 57)
    layout.nodeBase (by simpa [destinations] using dp) dr (by omega) initBlock
  obtain ⟨allocated, ticks, peak, gt, time, space, ah, ast, ao, ap, ar⟩ :=
    UniformDAGGuardGate.execution program ready (base + 58) layout.headBase layout.nodeBase
      layout.channelBase layout.guardArityBase layout.guardSourceBase offset childID cursor child guards
      (i3.trans (d3.trans offsetHeld)) i1 headFits childFits
      (by simpa [ih, dh] using headBound) (by simpa [ih, dh] using childBound)
      (by simpa [ih, dh] using headCell) (by simpa [ih, dh] using childCell)
      arityFits sourceFits (by simpa [ih, dh] using arityBound) (by simpa [ih, dh] using sourceBound)
      (by simpa [ih, dh] using arityCell) (by simpa [ih, dh] using sourceCell)
      cursorFits countFits (by simpa [ih, dh] using cells) ip ir (by omega)
      (by simpa [ih, dh] using room) kernel
  obtain ⟨final, jt, fh, fs, fo, fp, fr⟩ := jump program allocated (base + 90) (base + 109)
    (by simpa [Nat.add_assoc] using ap) ar (by omega) finish
  have sl : selected.liveWords = s.liveWords := by simp [State.liveWords, dh, ds, dout]
  have il : ready.liveWords = s.liveWords := by simp [State.liveWords, ih, dh, ist, ds, io, dout]
  have al : allocated.liveWords = s.liveWords + 1 := by
    simp [State.liveWords, ah, ih, dh, ast, ist, ds, ao, io, dout]; omega
  refine ⟨final, 11 + 1 + ticks + 2, max (max s.liveWords peak) allocated.liveWords, ?_, ?_, ?_,
    ?_, fs.trans (ast.trans (ist.trans ds)), fo.trans (ao.trans (io.trans dout)), fp, fr⟩
  · simpa [sl, Nat.max_self] using ((dt.append it).append gt).append jt
  · omega
  · rw [il] at space
    simp only [al, max_le_iff]
    exact ⟨⟨by omega, space⟩, by omega⟩
  · simpa [fh, ah, ih, dh]

/-- Both live-AND branches read their actual cached operands and allocate the
conjunction result before falling through to the common continuation. -/
theorem execution_and (program : Program width 4) (s : State width 4)
    (base offset cursor leftID rightID : ℕ) (layout : Layout) (left right : Bool)
    (offsetHeld : s.reg 3 = word width offset)
    (tagFits : layout.tagBase + offset < 2 ^ width)
    (tagBound : layout.tagBase + offset < s.heap.size)
    (tagCell : s.heap[layout.tagBase + offset]'tagBound = word width 4)
    (headFits : layout.headBase + offset < 2 ^ width)
    (sourceFits : layout.childSourceBase + offset < 2 ^ width)
    (cursorFits : cursor + 1 < 2 ^ width)
    (leftFits : layout.nodeBase + leftID < 2 ^ width)
    (rightFits : layout.nodeBase + rightID < 2 ^ width)
    (headBound : layout.headBase + offset < s.heap.size)
    (sourceBound : layout.childSourceBase + offset < s.heap.size)
    (cursorBound : cursor + 1 < s.heap.size)
    (leftBound : layout.nodeBase + leftID < s.heap.size)
    (rightBound : layout.nodeBase + rightID < s.heap.size)
    (headCell : s.heap[layout.headBase + offset]'headBound = word width leftID)
    (sourceCell : s.heap[layout.childSourceBase + offset]'sourceBound = word width cursor)
    (rightCell : s.heap[cursor + 1]'cursorBound = word width rightID)
    (leftValue : s.heap[layout.nodeBase + leftID]'leftBound = boolWord width left)
    (rightValue : s.heap[layout.nodeBase + rightID]'rightBound = boolWord width right)
    (pc : s.pc = word width base) (running : s.halted = false)
    (fits : base + 109 < 2 ^ width) (room : s.heap.size < 2 ^ width)
    (block : BlockAt program base (code width base layout)) :
    ∃ final, Execution program s final (if left then 30 else 29) (s.liveWords + 1) ∧
      final.heap = s.heap.push (boolWord width (left && right)) ∧
      final.stack = s.stack ∧ final.output = s.output ∧
      final.pc = word width (base + 109) ∧ final.halted = false := by
  obtain ⟨dispatch, orBlock, guardBlock, andBlock⟩ := handler_blocks program base layout block
  have initBlock := BlockAt.prefix program (base + 92)
    ([.constant 1 (word width layout.nodeBase)] : Code width)
    (UniformDAGAndGate.code width (base + 93) layout.headBase layout.childSourceBase) andBlock
  have kernel : BlockAt program (base + 93)
      (UniformDAGAndGate.code width (base + 93) layout.headBase layout.childSourceBase) := by
    simpa only [List.length_singleton, Nat.add_assoc] using BlockAt.suffix program (base + 92)
      ([.constant 1 (word width layout.nodeBase)] : Code width) _ andBlock
  obtain ⟨selected, dt, d0, d1, d3, dh, ds, dout, dp, dr⟩ :=
    UniformDAGDispatch.execution program s base layout.tagBase offset 4 (destinations base)
      offsetHeld tagFits tagBound tagCell pc running (by omega) dispatch
  obtain ⟨ready, it, i1, i3, ih, ist, io, ip, ir⟩ := initialize_value program selected (base + 92)
    layout.nodeBase (by simpa [destinations] using dp) dr (by omega) initBlock
  obtain ⟨final, atTrace, a2, a3, ah, ast, ao, ap, ar⟩ :=
    UniformDAGAndGate.execution program ready (base + 93) layout.headBase layout.childSourceBase
      layout.nodeBase offset cursor leftID rightID left right (i3.trans (d3.trans offsetHeld)) i1
      headFits sourceFits cursorFits leftFits rightFits
      (by simpa [ih, dh] using headBound) (by simpa [ih, dh] using sourceBound)
      (by simpa [ih, dh] using cursorBound) (by simpa [ih, dh] using leftBound)
      (by simpa [ih, dh] using rightBound) (by simpa [ih, dh] using headCell)
      (by simpa [ih, dh] using sourceCell) (by simpa [ih, dh] using rightCell)
      (by simpa [ih, dh] using leftValue) (by simpa [ih, dh] using rightValue)
      ip ir (by omega) (by simpa [ih, dh] using room) kernel
  have sl : selected.liveWords = s.liveWords := by simp [State.liveWords, dh, ds, dout]
  have il : ready.liveWords = s.liveWords := by simp [State.liveWords, ih, dh, ist, ds, io, dout]
  refine ⟨final, ?_, ?_, ast.trans (ist.trans ds), ao.trans (io.trans dout), ?_, ar⟩
  · have joined := (dt.append it).append atTrace
    cases left <;> simpa [sl, il, Nat.max_eq_right (by omega : s.liveWords ≤ s.liveWords + 1)] using joined
  · simpa [ah, ih, dh]
  · simpa [Nat.add_assoc] using ap

end Controller.Cost.UniformDAGNode
