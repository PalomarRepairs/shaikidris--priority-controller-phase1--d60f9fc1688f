module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.UniformDAGRead
public import Controller.Cost.ForestInputStored
public import Mathlib.Tactic.IntervalCases

@[expose] public section

/-! Runtime root output reads identifiers from the source table and values from
the shared value table. The instruction sequence is independent of root IDs. -/
namespace Controller.Cost.SharedRootLoop
open Controller.Cost.GateProgram

def readEmitCode (width : ℕ) : Code width :=
  UniformDAGRead.code width ++ [.emit 1]

def code (width base valueBase : ℕ) : Code width :=
  [.branchZero 2 (word width (base + 12)), .constant 1 (word width valueBase)] ++
  readEmitCode width ++
  [.constant 0 (word width 1), .add 3 3 0,
   .constant 0 (word width (2 ^ width - 1)), .add 2 2 0,
   .constant 0 (word width 0), .branchZero 0 (word width base)]

@[simp] theorem readEmitCode_length : (readEmitCode width).length = 4 := rfl
@[simp] theorem code_length : (code width base valueBase).length = 12 := rfl

/-- A root identifier is fetched from the heap and its shared value is emitted
in four steps, with exactly one additional live output word. -/
theorem read_emit_execution (program : Program width 4) (s : State width 4)
    (cursor valueBase index base : ℕ) (value : Bool)
    (cursorHeld : s.reg 3 = word width cursor)
    (baseHeld : s.reg 1 = word width valueBase)
    (cursorBound : cursor < s.heap.size) (cursorFits : cursor < 2 ^ width)
    (source : s.heap[cursor]'cursorBound = word width index)
    (valueBound : valueBase + index < s.heap.size)
    (valueFits : valueBase + index < 2 ^ width)
    (stored : s.heap[valueBase + index]'valueBound = boolWord width value)
    (pc : s.pc = word width base) (running : s.halted = false)
    (programFits : base + 4 < 2 ^ width)
    (block : BlockAt program base (readEmitCode width)) :
    ∃ final, Execution program s final 4 (s.liveWords + 1) ∧
      final.reg 2 = s.reg 2 ∧ final.reg 3 = s.reg 3 ∧
      final.heap = s.heap ∧ final.stack = s.stack ∧
      final.output = boolWord width value :: s.output ∧
      final.pc = word width (base + 4) ∧ final.halted = false := by
  have reads : BlockAt program base (UniformDAGRead.code width) := by
    intro offset inside
    have h := block offset (by simp only [readEmitCode_length];
                                  simp only [UniformDAGRead.code_length] at inside; omega)
    simp only [UniformDAGRead.code_length] at inside
    interval_cases offset <;> simpa [readEmitCode, UniformDAGRead.code] using h
  obtain ⟨ready, trace, r0, r1, r2, r3, heap, stack, output, readyPC, readyRunning⟩ :=
    UniformDAGRead.execution program s cursor valueBase index base value cursorHeld baseHeld
      cursorBound cursorFits source valueBound valueFits stored pc running (by omega) reads
  let final : State width 4 := { ready.advance with output := ready.reg 1 :: ready.output }
  have fetched : programStep program ready = some final := by
    unfold programStep
    rw [readyPC, show (word width (base + 3)).val = base + 3 from
      Nat.mod_eq_of_lt (by omega), block 3 (by simp)]
    simp [readEmitCode, UniformDAGRead.code, step, readyRunning, final]
  have readyLive : ready.liveWords = s.liveWords := by
    simp [State.liveWords, heap, stack, output]
  have finalLive : final.liveWords = s.liveWords + 1 := by
    simp [final, State.liveWords, State.advance, heap, stack, output]
    omega
  refine ⟨final, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have tail := Execution.cons fetched (Execution.refl final)
    have joined := trace.append tail
    simpa [readyLive, finalLive] using joined
  · simpa [final, State.advance] using r2
  · simpa [final, State.advance] using r3
  · exact heap
  · exact stack
  · simp [final, r1, output]
  · simp [final, State.advance, readyPC,
      show (word width (base + 3)).val = base + 3 from Nat.mod_eq_of_lt (by omega),
      Nat.add_assoc]
  · exact readyRunning

/-- A zero remaining count exits the fixed loop without reading the heap. -/
theorem zero_execution (program : Program width 4) (s : State width 4)
    (base valueBase : ℕ) (zero : s.reg 2 = word width 0)
    (pc : s.pc = word width base) (running : s.halted = false)
    (fits : base + 12 < 2 ^ width)
    (block : BlockAt program base (code width base valueBase)) :
    Execution program s { s with pc := word width (base + 12) } 1 s.liveWords := by
  have transition : programStep program s =
      some { s with pc := word width (base + 12) } := by
    unfold programStep
    rw [pc, show (word width base).val = base from Nat.mod_eq_of_lt (by omega),
      show base = base + 0 from (Nat.add_zero base).symm, block 0 (by simp)]
    simp [code, step, zero, running, word, State.advance]
  have trace := Execution.cons transition
    (Execution.refl ({ s with pc := word width (base + 12) } : State width 4))
  simpa [State.liveWords] using trace

private theorem fetched (program : Program width 4) (s : State width 4)
    (base : ℕ) (instruction : Instruction width 4)
    (pc : s.pc = word width base) (fits : base < 2 ^ width)
    (entry : program[base]? = some instruction) :
    programStep program s = step instruction s := by
  unfold programStep
  rw [pc, show (word width base).val = base from Nat.mod_eq_of_lt fits, entry]
  rfl

/-- A positive count enters the indirect read and installs the shared-table base. -/
theorem positive_entry_execution (program : Program width 4) (s : State width 4)
    (base valueBase remaining : ℕ)
    (count : s.reg 2 = word width (remaining + 1))
    (countFits : remaining + 1 < 2 ^ width)
    (pc : s.pc = word width base) (running : s.halted = false)
    (fits : base + 12 < 2 ^ width)
    (block : BlockAt program base (code width base valueBase)) :
    ∃ ready, Execution program s ready 2 s.liveWords ∧
      ready.reg 1 = word width valueBase ∧ ready.reg 2 = s.reg 2 ∧
      ready.reg 3 = s.reg 3 ∧ ready.heap = s.heap ∧ ready.stack = s.stack ∧
      ready.output = s.output ∧ ready.pc = word width (base + 2) ∧
      ready.halted = false := by
  let middle := s.advance
  let ready := middle.advance.put 1 (word width valueBase)
  have middlePC : middle.pc = word width (base + 1) := by
    simp [middle, State.advance, pc,
      show (word width base).val = base from Nat.mod_eq_of_lt (by omega)]
  have first : programStep program s = some middle := by
    rw [fetched program s base (.branchZero 2 (word width (base + 12))) pc (by omega)
      (by simpa [code] using block 0 (by simp))]
    simp [step, count, running, middle,
      show (word width (remaining + 1)).val = remaining + 1 from Nat.mod_eq_of_lt countFits]
  have second : programStep program middle = some ready := by
    rw [fetched program middle (base + 1) (.constant 1 (word width valueBase))
      middlePC (by omega) (by simpa [code] using block 1 (by simp))]
    simp [step, middle, ready, State.advance, running]
  have middleLive : middle.liveWords = s.liveWords := rfl
  have readyLive : ready.liveWords = s.liveWords := rfl
  refine ⟨ready, ?_, ?_, ?_, ?_, rfl, rfl, rfl, ?_, running⟩
  · have trace := Execution.cons first (Execution.cons second (Execution.refl ready))
    simpa [middleLive, readyLive] using trace
  · simp [ready, State.put]
  · simp [ready, middle, State.advance, State.put]
  · simp [ready, middle, State.advance, State.put]
  · simp [ready, State.put, State.advance, middlePC,
      show (word width (base + 1)).val = base + 1 from Nat.mod_eq_of_lt (by omega),
      Nat.add_assoc]

private theorem advance_pc (s : State width 4) (position : ℕ)
    (pc : s.pc = word width position) (fits : position < 2 ^ width) :
    s.advance.pc = word width (position + 1) := by
  simp [State.advance, pc,
    show (word width position).val = position from Nat.mod_eq_of_lt fits]

/-- The six-instruction tail advances the source cursor, decrements the count,
and jumps back without changing storage. -/
theorem tail_execution (program : Program width 4) (s : State width 4)
    (base valueBase cursor remaining : ℕ)
    (cursorHeld : s.reg 3 = word width cursor)
    (countHeld : s.reg 2 = word width (remaining + 1))
    (cursorFits : cursor + 1 < 2 ^ width) (countFits : remaining + 1 < 2 ^ width)
    (pc : s.pc = word width (base + 6)) (running : s.halted = false)
    (fits : base + 12 < 2 ^ width)
    (block : BlockAt program base (code width base valueBase)) :
    ∃ final, Execution program s final 6 s.liveWords ∧
      final.reg 2 = word width remaining ∧ final.reg 3 = word width (cursor + 1) ∧
      final.heap = s.heap ∧ final.stack = s.stack ∧ final.output = s.output ∧
      final.pc = word width base ∧ final.halted = false := by
  let a := s.advance.put 0 (word width 1)
  let b := a.advance.put 3 (word width (cursor + 1))
  let c := b.advance.put 0 (word width (2 ^ width - 1))
  let d := c.advance.put 2 (word width remaining)
  let e := d.advance.put 0 (word width 0)
  let final := { e.advance with pc := word width base }
  have ap : a.pc = word width (base + 7) := by
    simpa [a, State.put, Nat.add_assoc] using advance_pc s (base + 6) pc (by omega)
  have bp : b.pc = word width (base + 8) := by
    simpa [b, State.put, Nat.add_assoc] using advance_pc a (base + 7) ap (by omega)
  have cp : c.pc = word width (base + 9) := by
    simpa [c, State.put, Nat.add_assoc] using advance_pc b (base + 8) bp (by omega)
  have dp : d.pc = word width (base + 10) := by
    simpa [d, State.put, Nat.add_assoc] using advance_pc c (base + 9) cp (by omega)
  have ep : e.pc = word width (base + 11) := by
    simpa [e, State.put, Nat.add_assoc] using advance_pc d (base + 10) dp (by omega)
  have v1 : (word width 1).val = 1 := Nat.mod_eq_of_lt (by omega)
  have vc : (word width cursor).val = cursor := Nat.mod_eq_of_lt (by omega)
  have vn : (word width (remaining + 1)).val = remaining + 1 := Nat.mod_eq_of_lt countFits
  have vm : (word width (2 ^ width - 1)).val = 2 ^ width - 1 :=
    Nat.mod_eq_of_lt (by have := Nat.two_pow_pos width; omega)
  have decrement : word width (remaining + 1 + (2 ^ width - 1)) = word width remaining := by
    have sum : remaining + 1 + (2 ^ width - 1) = 2 ^ width + remaining := by
      have := Nat.two_pow_pos width; omega
    rw [sum]
    simp [word, Nat.add_mod_left]
  have t0 : programStep program s = some a := by
    rw [fetched program s (base + 6) (.constant 0 (word width 1)) pc (by omega)
      (by simpa [code, readEmitCode, UniformDAGRead.code] using block 6 (by simp))]
    simp [step, running, a]
  have t1 : programStep program a = some b := by
    rw [fetched program a (base + 7) (.add 3 3 0) ap (by omega)
      (by simpa [code, readEmitCode, UniformDAGRead.code] using block 7 (by simp))]
    simp [step, a, b, State.put, State.advance, cursorHeld, running, vc, v1]
  have t2 : programStep program b = some c := by
    rw [fetched program b (base + 8) (.constant 0 (word width (2 ^ width - 1))) bp (by omega)
      (by simpa [code, readEmitCode, UniformDAGRead.code] using block 8 (by simp))]
    simp [step, a, b, c, State.put, State.advance, running]
  have t3 : programStep program c = some d := by
    rw [fetched program c (base + 9) (.add 2 2 0) cp (by omega)
      (by simpa [code, readEmitCode, UniformDAGRead.code] using block 9 (by simp))]
    simp [step, a, b, c, d, State.put, State.advance, running, countHeld, vn, vm, decrement]
  have t4 : programStep program d = some e := by
    rw [fetched program d (base + 10) (.constant 0 (word width 0)) dp (by omega)
      (by simpa [code, readEmitCode, UniformDAGRead.code] using block 10 (by simp))]
    simp [step, a, b, c, d, e, State.put, State.advance, running]
  have t5 : programStep program e = some final := by
    rw [fetched program e (base + 11) (.branchZero 0 (word width base)) ep (by omega)
      (by simpa [code, readEmitCode, UniformDAGRead.code] using block 11 (by simp))]
    simp [step, e, d, c, b, a, State.put, State.advance, running, word, final]
  refine ⟨final, ?_, ?_, ?_, rfl, rfl, rfl, rfl, running⟩
  · have trace := Execution.cons t0 (Execution.cons t1 (Execution.cons t2
      (Execution.cons t3 (Execution.cons t4 (Execution.cons t5 (Execution.refl final))))))
    simpa [final, e, d, c, b, a, State.liveWords, State.put, State.advance] using trace
  · simp [final, e, d, State.put, State.advance]
  · simp [final, e, d, c, b, State.put, State.advance]

/-- One positive iteration outputs one represented root and returns to the
same loop address with the next cursor and the decreased remaining count. -/
theorem iteration_execution (program : Program width 4) (s : State width 4)
    (base valueBase cursor index remaining : ℕ) (value : Bool)
    (cursorHeld : s.reg 3 = word width cursor)
    (countHeld : s.reg 2 = word width (remaining + 1))
    (cursorFits : cursor + 1 < 2 ^ width) (countFits : remaining + 1 < 2 ^ width)
    (cursorBound : cursor < s.heap.size)
    (source : s.heap[cursor]'cursorBound = word width index)
    (valueBound : valueBase + index < s.heap.size)
    (valueFits : valueBase + index < 2 ^ width)
    (stored : s.heap[valueBase + index]'valueBound = boolWord width value)
    (pc : s.pc = word width base) (running : s.halted = false)
    (fits : base + 12 < 2 ^ width)
    (block : BlockAt program base (code width base valueBase)) :
    ∃ final, Execution program s final 12 (s.liveWords + 1) ∧
      final.reg 2 = word width remaining ∧ final.reg 3 = word width (cursor + 1) ∧
      final.heap = s.heap ∧ final.stack = s.stack ∧
      final.output = boolWord width value :: s.output ∧
      final.pc = word width base ∧ final.halted = false := by
  obtain ⟨ready, entryTrace, rb, rn, rc, rh, rs, ro, rp, rr⟩ :=
    positive_entry_execution program s base valueBase remaining countHeld countFits pc running fits block
  have reads : BlockAt program (base + 2) (readEmitCode width) := by
    intro offset inside
    have h := block (2 + offset) (by
      simp only [readEmitCode_length] at inside
      simp only [code_length]
      omega)
    simp only [readEmitCode_length] at inside
    interval_cases offset <;> simpa [code, readEmitCode, UniformDAGRead.code, Nat.add_assoc] using h
  obtain ⟨emitted, emitTrace, en, ec, eh, es, eo, ep, er⟩ :=
    read_emit_execution program ready cursor valueBase index (base + 2) value
      (rc.trans cursorHeld) rb (by simpa [rh] using cursorBound) (by omega)
      (by simpa [rh] using source) (by simpa [rh] using valueBound) valueFits
      (by simpa [rh] using stored) rp rr (by omega) reads
  obtain ⟨final, tailTrace, fn, fc, fh, fs, fo, fp, fr⟩ :=
    tail_execution program emitted base valueBase cursor remaining
      (ec.trans (rc.trans cursorHeld)) (en.trans (rn.trans countHeld)) cursorFits countFits
      (by simpa [Nat.add_assoc] using ep) er fits block
  have readyLive : ready.liveWords = s.liveWords := by simp [State.liveWords, rh, rs, ro]
  have emittedLive : emitted.liveWords = s.liveWords + 1 := by
    simp [State.liveWords, eh, es, eo, rh, rs, ro]
    omega
  refine ⟨final, ?_, fn, fc, fh.trans (eh.trans rh), fs.trans (es.trans rs), ?_, fp, fr⟩
  · have joined := (entryTrace.append emitTrace).append tailTrace
    simpa [readyLive, emittedLive] using joined
  · simp [fo, eo, ro]

/-- Every root-table cell and every associated shared-value cell is present in
the machine heap. Repetition of root identifiers is permitted. -/
def RepresentedRoots (heap : Array (Word width)) (cursor valueBase : ℕ) :
    List (ℕ × Bool) → Prop
  | [] => True
  | (index, value) :: rest =>
      ∃ (cursorBound : cursor < heap.size) (valueBound : valueBase + index < heap.size),
        heap[cursor]'cursorBound = word width index ∧
        heap[valueBase + index]'valueBound = boolWord width value ∧
        valueBase + index < 2 ^ width ∧ RepresentedRoots heap (cursor + 1) valueBase rest

/-- The fixed loop outputs all represented roots in twelve steps per root plus
one exit step. Its peak grows by exactly the number of emitted words. -/
theorem execution (program : Program width 4) (s : State width 4)
    (base valueBase cursor : ℕ) (roots : List (ℕ × Bool))
    (represented : RepresentedRoots s.heap cursor valueBase roots)
    (cursorHeld : s.reg 3 = word width cursor)
    (countHeld : s.reg 2 = word width roots.length)
    (cursorFits : cursor + roots.length < 2 ^ width)
    (countFits : roots.length < 2 ^ width)
    (pc : s.pc = word width base) (running : s.halted = false)
    (fits : base + 12 < 2 ^ width)
    (block : BlockAt program base (code width base valueBase)) :
    ∃ final, Execution program s final (12 * roots.length + 1) (s.liveWords + roots.length) ∧
      final.reg 2 = word width 0 ∧ final.reg 3 = word width (cursor + roots.length) ∧
      final.heap = s.heap ∧ final.stack = s.stack ∧
      final.output = (roots.map (fun root => boolWord width root.2)).reverse ++ s.output ∧
      final.pc = word width (base + 12) ∧ final.halted = false := by
  induction roots generalizing s cursor with
  | nil =>
      refine ⟨{ s with pc := word width (base + 12) }, ?_, countHeld, ?_, rfl, rfl, ?_, rfl, running⟩
      · simpa using zero_execution program s base valueBase countHeld pc running fits block
      · simpa using cursorHeld
      · simp
  | cons root roots ih =>
      rcases root with ⟨index, value⟩
      obtain ⟨cb, vb, source, stored, valueFits, rest⟩ := represented
      obtain ⟨next, trace, nn, nc, nh, ns, no, np, nr⟩ :=
        iteration_execution program s base valueBase cursor index roots.length value
          cursorHeld (by simpa using countHeld) (by simp only [List.length_cons] at cursorFits; omega)
          (by simpa using countFits) cb source vb valueFits stored pc running fits block
      obtain ⟨final, tail, fn, fc, fh, fs, fo, fp, fr⟩ :=
        ih next (cursor + 1) (by simpa [nh] using rest) nc nn
          (by simp only [List.length_cons] at cursorFits; omega)
          (by simp only [List.length_cons] at countFits; omega) np nr
      have nextLive : next.liveWords = s.liveWords + 1 := by
        simp [State.liveWords, nh, ns, no]
        omega
      refine ⟨final, ?_, fn, ?_, fh.trans nh, fs.trans ns, ?_, fp, fr⟩
      · have joined := trace.append tail
        simpa [nextLive, List.length_cons, Nat.mul_add, Nat.add_assoc,
          Nat.add_comm, Nat.add_left_comm] using joined
      · simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using fc
      · simp [fo, no, List.reverse_cons, List.append_assoc]

/-- A finite value table and a physically stored identifier stream establish
the root-loop relation, including repeated identifiers. -/
theorem represented_ids (heap : Array (Word width)) (values : Fin m → Bool)
    (ids : List (Fin m)) (cursor : ℕ)
    (fits : heap.size + m ≤ 2 ^ width)
    (sourceBounds : ∀ i, (valid : i < ids.length) → cursor + i < heap.size)
    (sourceCells : ∀ i, (valid : i < ids.length) →
      heap[cursor + i]'(sourceBounds i valid) = word width (ids[i]'valid).val) :
    RepresentedRoots (ForestInputStored.withValues heap values) cursor heap.size
      (ids.map (fun id => (id.val, values id))) := by
  induction ids generalizing cursor with
  | nil => trivial
  | cons id rest ih =>
      have cb : cursor < heap.size := by simpa using sourceBounds 0 (by simp)
      have cell : heap[cursor]'cb = word width id.val := by
        have first := sourceCells 0 (by simp)
        change heap[cursor + 0] = word width id.val at first
        simpa only [Nat.add_zero] using first
      have tail := ih (cursor + 1)
        (fun i valid => by have h := sourceBounds (i + 1) (by simpa using valid); omega)
        (fun i valid => by
          have validNext : i + 1 < (id :: rest).length := by simpa using valid
          have next := sourceCells (i + 1) validNext
          simpa only [List.getElem_cons_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using next)
      refine ⟨by simp; omega, by simp, ?_, ?_, ?_, tail⟩
      · exact (ForestInputStored.source_preserved heap values cursor cb).trans cell
      · exact ForestInputStored.value_cell heap values id
      · have := id.isLt; omega

def setupCode (width cursor count : ℕ) : Code width :=
  [.constant 3 (word width cursor), .constant 2 (word width count)]

@[simp] theorem setupCode_length : (setupCode width cursor count).length = 2 := rfl

/-- Two fetched constants initialize the runtime cursor and remaining count. -/
theorem setup_execution (program : Program width 4) (s : State width 4)
    (base cursor count : ℕ) (pc : s.pc = word width base) (running : s.halted = false)
    (fits : base + 2 < 2 ^ width)
    (block : BlockAt program base (setupCode width cursor count)) :
    ∃ ready, Execution program s ready 2 s.liveWords ∧
      ready.reg 2 = word width count ∧ ready.reg 3 = word width cursor ∧
      ready.heap = s.heap ∧ ready.stack = s.stack ∧ ready.output = s.output ∧
      ready.pc = word width (base + 2) ∧ ready.halted = false := by
  let middle := s.advance.put 3 (word width cursor)
  let ready := middle.advance.put 2 (word width count)
  have middlePC : middle.pc = word width (base + 1) := by
    simpa [middle, State.put] using advance_pc s base pc (by omega)
  have first : programStep program s = some middle := by
    rw [fetched program s base (.constant 3 (word width cursor)) pc (by omega)
      (by simpa [setupCode] using block 0 (by simp [setupCode]))]
    simp [step, middle, running]
  have second : programStep program middle = some ready := by
    rw [fetched program middle (base + 1) (.constant 2 (word width count)) middlePC (by omega)
      (by simpa [setupCode] using block 1 (by simp [setupCode]))]
    simp [step, middle, ready, State.advance, State.put, running]
  have middleLive : middle.liveWords = s.liveWords := rfl
  have readyLive : ready.liveWords = s.liveWords := rfl
  refine ⟨ready, ?_, ?_, ?_, rfl, rfl, rfl, ?_, running⟩
  · have trace := Execution.cons first (Execution.cons second (Execution.refl ready))
    simpa [middleLive, readyLive] using trace
  · simp [ready, State.put]
  · simp [ready, middle, State.put, State.advance]
  · simpa [ready, State.put, Nat.add_assoc] using
      advance_pc middle (base + 1) middlePC (by omega)

end Controller.Cost.SharedRootLoop
