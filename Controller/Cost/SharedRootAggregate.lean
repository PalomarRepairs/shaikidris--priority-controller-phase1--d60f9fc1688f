module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedRootLoop
public import Mathlib.Tactic.IntervalCases
public import Controller.Cost.SharedRootObserve

@[expose] public section

/-! Fixed counted control for root witness aggregation. -/
namespace Controller.Cost.SharedRootAggregate
open Controller.Cost.RawTransferLoops

def code (width base valueBase : Nat) : List (Instruction width 8) :=
  [.branchZero 5 (word width (base + 15)), .constant 1 (word width valueBase),
   .load 0 3, .add 0 0 1, .load 1 0,
   .pop 2, .branchZero 1 (word width (base + 8)), .copy 2 4, .allocate 2,
   .constant 0 (word width 1), .add 3 3 0,
   .constant 0 (word width (2 ^ width - 1)), .add 5 5 0,
   .constant 0 (word width 0), .branchZero 0 (word width base)]

@[simp] theorem code_length (width base valueBase : Nat) :
    (code width base valueBase).length = 15 := rfl

/-- A zero remaining count exits the fixed loop without reading the heap. -/
theorem zero_execution (program : Program width 8) (s : State width 8)
    (base valueBase : ℕ) (zero : s.reg 5 = word width 0)
    (pc : s.pc = word width base) (running : s.halted = false)
    (fits : base + 15 < 2 ^ width)
    (block : SharedRootRead.BlockAt program base (code width base valueBase)) :
    Execution program s { s with pc := word width (base + 15) } 1 s.liveWords := by
  have transition : programStep program s =
      some { s with pc := word width (base + 15) } := by
    unfold programStep
    rw [pc, show (word width base).val = base from Nat.mod_eq_of_lt (by omega),
      show base = base + 0 from (Nat.add_zero base).symm, block 0 (by simp)]
    simp [code, step, zero, running, word, State.advance]
  have trace := Execution.cons transition
    (Execution.refl ({ s with pc := word width (base + 15) } : State width 8))
  simpa [State.liveWords] using trace

private theorem fetched (program : Program width 8) (s : State width 8)
    (base : ℕ) (instruction : Instruction width 8)
    (pc : s.pc = word width base) (fits : base < 2 ^ width)
    (entry : program[base]? = some instruction) :
    programStep program s = step instruction s := by
  unfold programStep
  rw [pc, show (word width base).val = base from Nat.mod_eq_of_lt fits, entry]
  rfl

/-- A positive count enters the indirect read and installs the shared-table base. -/
theorem positive_entry_execution (program : Program width 8) (s : State width 8)
    (base valueBase remaining : ℕ)
    (count : s.reg 5 = word width (remaining + 1))
    (countFits : remaining + 1 < 2 ^ width)
    (pc : s.pc = word width base) (running : s.halted = false)
    (fits : base + 15 < 2 ^ width)
    (block : SharedRootRead.BlockAt program base (code width base valueBase)) :
    ∃ ready, Execution program s ready 2 s.liveWords ∧
      ready.reg 1 = word width valueBase ∧ ready.reg 5 = s.reg 5 ∧
      ready.reg 3 = s.reg 3 ∧ ready.heap = s.heap ∧ ready.stack = s.stack ∧
      ready.output = s.output ∧ ready.pc = word width (base + 2) ∧
      ready.halted = false ∧ ready.reg 4 = s.reg 4 := by
  let middle := s.advance
  let ready := middle.advance.put 1 (word width valueBase)
  have middlePC : middle.pc = word width (base + 1) := by
    simp [middle, State.advance, pc,
      show (word width base).val = base from Nat.mod_eq_of_lt (by omega)]
  have first : programStep program s = some middle := by
    rw [fetched program s base (.branchZero 5 (word width (base + 15))) pc (by omega)
      (by simpa [code] using block 0 (by simp))]
    simp [step, count, running, middle,
      show (word width (remaining + 1)).val = remaining + 1 from Nat.mod_eq_of_lt countFits]
  have second : programStep program middle = some ready := by
    rw [fetched program middle (base + 1) (.constant 1 (word width valueBase))
      middlePC (by omega) (by simpa [code] using block 1 (by simp))]
    simp [step, middle, ready, State.advance, running]
  have middleLive : middle.liveWords = s.liveWords := rfl
  have readyLive : ready.liveWords = s.liveWords := rfl
  refine ⟨ready, ?_, ?_, ?_, ?_, rfl, rfl, rfl, ?_, running, ?_⟩
  · have trace := Execution.cons first (Execution.cons second (Execution.refl ready))
    simpa [middleLive, readyLive] using trace
  · simp [ready, State.put]
  · simp [ready, middle, State.advance, State.put]
  · simp [ready, middle, State.advance, State.put]
  · simp [ready, State.put, State.advance, middlePC,
      show (word width (base + 1)).val = base + 1 from Nat.mod_eq_of_lt (by omega),
      Nat.add_assoc]
  · simp [ready, middle, State.advance, State.put]

private theorem advance_pc (s : State width 8) (position : ℕ)
    (pc : s.pc = word width position) (fits : position < 2 ^ width) :
    s.advance.pc = word width (position + 1) := by
  simp [State.advance, pc,
    show (word width position).val = position from Nat.mod_eq_of_lt fits]

/-- The six-instruction tail advances the source cursor, decrements the count,
and jumps back without changing storage. -/
theorem tail_execution (program : Program width 8) (s : State width 8)
    (base valueBase cursor remaining : ℕ)
    (cursorHeld : s.reg 3 = word width cursor)
    (countHeld : s.reg 5 = word width (remaining + 1))
    (cursorFits : cursor + 1 < 2 ^ width) (countFits : remaining + 1 < 2 ^ width)
    (pc : s.pc = word width (base + 9)) (running : s.halted = false)
    (fits : base + 15 < 2 ^ width)
    (block : SharedRootRead.BlockAt program base (code width base valueBase)) :
    ∃ final, Execution program s final 6 s.liveWords ∧
      final.reg 5 = word width remaining ∧ final.reg 3 = word width (cursor + 1) ∧
      final.heap = s.heap ∧ final.stack = s.stack ∧ final.output = s.output ∧
      final.pc = word width base ∧ final.halted = false ∧ final.reg 4 = s.reg 4 := by
  let a := s.advance.put 0 (word width 1)
  let b := a.advance.put 3 (word width (cursor + 1))
  let c := b.advance.put 0 (word width (2 ^ width - 1))
  let d := c.advance.put 5 (word width remaining)
  let e := d.advance.put 0 (word width 0)
  let final := { e.advance with pc := word width base }
  have ap : a.pc = word width (base + 10) := by
    simpa [a, State.put, Nat.add_assoc] using advance_pc s (base + 9) pc (by omega)
  have bp : b.pc = word width (base + 11) := by
    simpa [b, State.put, Nat.add_assoc] using advance_pc a (base + 10) ap (by omega)
  have cp : c.pc = word width (base + 12) := by
    simpa [c, State.put, Nat.add_assoc] using advance_pc b (base + 11) bp (by omega)
  have dp : d.pc = word width (base + 13) := by
    simpa [d, State.put, Nat.add_assoc] using advance_pc c (base + 12) cp (by omega)
  have ep : e.pc = word width (base + 14) := by
    simpa [e, State.put, Nat.add_assoc] using advance_pc d (base + 13) dp (by omega)
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
    rw [fetched program s (base + 9) (.constant 0 (word width 1)) pc (by omega)
      (by simpa [code] using block 9 (by simp))]
    simp [step, running, a]
  have t1 : programStep program a = some b := by
    rw [fetched program a (base + 10) (.add 3 3 0) ap (by omega)
      (by simpa [code] using block 10 (by simp))]
    simp [step, a, b, State.put, State.advance, cursorHeld, running, vc, v1]
  have t2 : programStep program b = some c := by
    rw [fetched program b (base + 11) (.constant 0 (word width (2 ^ width - 1))) bp (by omega)
      (by simpa [code] using block 11 (by simp))]
    simp [step, a, b, c, State.put, State.advance, running]
  have t3 : programStep program c = some d := by
    rw [fetched program c (base + 12) (.add 5 5 0) cp (by omega)
      (by simpa [code] using block 12 (by simp))]
    simp [step, a, b, c, d, State.put, State.advance, running, countHeld, vn, vm, decrement]
  have t4 : programStep program d = some e := by
    rw [fetched program d (base + 13) (.constant 0 (word width 0)) dp (by omega)
      (by simpa [code] using block 13 (by simp))]
    simp [step, a, b, c, d, e, State.put, State.advance, running]
  have t5 : programStep program e = some final := by
    rw [fetched program e (base + 14) (.branchZero 0 (word width base)) ep (by omega)
      (by simpa [code] using block 14 (by simp))]
    simp [step, e, d, c, b, a, State.put, State.advance, running, word, final]
  refine ⟨final, ?_, ?_, ?_, rfl, rfl, rfl, rfl, running, ?_⟩
  · have trace := Execution.cons t0 (Execution.cons t1 (Execution.cons t2
      (Execution.cons t3 (Execution.cons t4 (Execution.cons t5 (Execution.refl final))))))
    simpa [final, e, d, c, b, a, State.liveWords, State.put, State.advance] using trace
  · simp [final, e, d, State.put, State.advance]
  · simp [final, e, d, c, b, State.put, State.advance]
  · simp [final, e, d, c, b, a, State.put, State.advance]


theorem iteration_execution (resident : Program width 8) (state : State width 8)
    (base valueBase cursor index remaining : Nat) (observed : Bool)
    (old candidate : Word width) (suffix : List (Word width))
    (cursorHeld : state.reg 3 = word width cursor)
    (countHeld : state.reg 5 = word width (remaining + 1))
    (candidateHeld : state.reg 4 = candidate)
    (cursorFits : cursor + 1 < 2 ^ width) (countFits : remaining + 1 < 2 ^ width)
    (cursorBound : cursor < state.heap.size)
    (source : state.heap[cursor]'cursorBound = word width index)
    (valueBound : valueBase + index < state.heap.size)
    (valueFits : valueBase + index < 2 ^ width)
    (stored : state.heap[valueBase + index]'valueBound = boolWord width observed)
    (input : state.stack = old :: suffix)
    (pc : state.pc = word width base) (running : state.halted = false)
    (fits : base + 15 < 2 ^ width) (boolFits : 1 < 2 ^ width)
    (heapFits : state.heap.size < 2 ^ width)
    (block : SharedRootRead.BlockAt resident base (code width base valueBase)) :
    ∃ final ticks, Execution resident state final ticks state.liveWords ∧ ticks ≤ 15 ∧
      final.reg 5 = word width remaining ∧ final.reg 3 = word width (cursor + 1) ∧
      final.reg 4 = candidate ∧ final.heap = state.heap.push (if observed then candidate else old) ∧
      final.stack = suffix ∧ final.output = state.output ∧
      final.pc = word width base ∧ final.halted = false := by
  obtain ⟨ready, entryTrace, rb, rn, rc, rh, rs, ro, rp, rr, rCandidate⟩ :=
    positive_entry_execution resident state base valueBase remaining countHeld countFits pc running fits block
  have observeCode : CodeAt resident (base + 2) (SharedRootObserve.code width (base + 2)) := by
    intro phase
    rcases phase with ⟨index, bound⟩
    have inside : index < 7 := by simpa using bound
    have cell := block (2 + index) (by simp only [code_length]; omega)
    interval_cases index <;>
      simpa [code, SharedRootObserve.code, SharedRootRead.code, SharedRootWitness.code, Nat.add_assoc] using cell
  obtain ⟨observedState, ticks, observeTrace, time, oh, os, oo, op, orunning, oframe⟩ :=
    SharedRootObserve.execution resident ready cursor valueBase index (base + 2) observed old candidate suffix
      (rc.trans cursorHeld) rb (by simpa only [rh] using cursorBound) (by omega)
      (by simpa only [rh] using source) (by simpa only [rh] using valueBound) valueFits
      (by simpa only [rh] using stored) rp rr (by omega) boolFits
      (by simpa only [rh] using heapFits) (rs.trans input) (rCandidate.trans candidateHeld) observeCode
  obtain ⟨final, tailTrace, fn, fc, fh, fs, fo, fp, fr, fCandidate⟩ :=
    tail_execution resident observedState base valueBase cursor remaining
      ((oframe 3 (by decide) (by decide) (by decide)).trans (rc.trans cursorHeld))
      ((oframe 5 (by decide) (by decide) (by decide)).trans (rn.trans countHeld))
      cursorFits countFits (by simpa only [Nat.add_assoc, Nat.reduceAdd] using op) orunning fits block
  have readyLive : ready.liveWords = state.liveWords := by simp only [State.liveWords, rh, rs, ro]
  have observedLive : observedState.liveWords = state.liveWords := by
    simp only [State.liveWords, oh, os, oo, rh, ro, Array.size_push]
    simp only [State.liveWords, input, List.length_cons]
    omega
  have joined := entryTrace.append (observeTrace.append tailTrace)
  rw [readyLive, observedLive, Nat.max_self, Nat.max_self] at joined
  refine ⟨final, 2 + (ticks + 6), joined, by omega, fn, fc, ?_, fh.trans (oh.trans (by rw [rh])),
    fs.trans os, fo.trans (oo.trans ro), fp, fr⟩
  exact fCandidate.trans ((oframe 4 (by decide) (by decide) (by decide)).trans
    (rCandidate.trans candidateHeld))


theorem represented_push (heap : Array (Word width)) (word : Word width)
    (cursor valueBase : Nat) (roots : List (Nat × Bool))
    (represented : SharedRootLoop.RepresentedRoots heap cursor valueBase roots) :
    SharedRootLoop.RepresentedRoots (heap.push word) cursor valueBase roots := by
  induction roots generalizing cursor with
  | nil => trivial
  | cons root roots ih =>
    rcases root with ⟨index, value⟩
    obtain ⟨cb, vb, source, stored, fits, rest⟩ := represented
    refine ⟨by simp; omega, by simp; omega, ?_, ?_, fits, ih (cursor + 1) rest⟩
    · exact (Array.getElem_push_lt cb).trans source
    · exact (Array.getElem_push_lt vb).trans stored

def updated (candidate : Word width) (roots : List (Nat × Bool)) (witnesses : List (Word width)) :
    List (Word width) := List.zipWith (fun root old => if root.2 then candidate else old) roots witnesses

set_option maxHeartbeats 2000000 in
theorem execution (resident : Program width 8) (state : State width 8)
    (base valueBase cursor : Nat) (roots : List (Nat × Bool))
    (witnesses suffix : List (Word width)) (candidate : Word width)
    (represented : SharedRootLoop.RepresentedRoots state.heap cursor valueBase roots)
    (lengths : witnesses.length = roots.length) (input : state.stack = witnesses ++ suffix)
    (cursorHeld : state.reg 3 = word width cursor) (countHeld : state.reg 5 = word width roots.length)
    (candidateHeld : state.reg 4 = candidate)
    (cursorFits : cursor + roots.length < 2 ^ width) (countFits : roots.length < 2 ^ width)
    (heapFits : state.heap.size + roots.length < 2 ^ width)
    (pc : state.pc = word width base) (running : state.halted = false)
    (fits : base + 15 < 2 ^ width) (boolFits : 1 < 2 ^ width)
    (block : SharedRootRead.BlockAt resident base (code width base valueBase)) :
    ∃ final ticks, Execution resident state final ticks state.liveWords ∧ ticks ≤ 15 * roots.length + 1 ∧
      final.reg 5 = word width 0 ∧ final.reg 3 = word width (cursor + roots.length) ∧
      final.reg 4 = candidate ∧ final.heap = state.heap ++ (updated candidate roots witnesses).toArray ∧
      final.stack = suffix ∧ final.output = state.output ∧
      final.pc = word width (base + 15) ∧ final.halted = false := by
  induction roots generalizing state cursor witnesses with
  | nil =>
    have empty : witnesses = [] := List.eq_nil_of_length_eq_zero (by simpa using lengths)
    subst witnesses
    refine ⟨{ state with pc := word width (base + 15) }, 1, ?_, by simp,
      countHeld, ?_, candidateHeld, ?_, ?_, rfl, rfl, running⟩
    · exact zero_execution resident state base valueBase countHeld pc running fits block
    · simpa using cursorHeld
    · simp [updated]
    · simpa using input
  | cons root roots ih =>
    cases witnesses with
    | nil => simp at lengths
    | cons old witnesses =>
      rcases root with ⟨index, observed⟩
      obtain ⟨cb, vb, source, stored, valueFits, rest⟩ := represented
      obtain ⟨next, firstTicks, firstTrace, firstTime, nn, nc, nCandidate, nh, ns, no, np, nr⟩ :=
        iteration_execution resident state base valueBase cursor index roots.length observed old candidate
          (witnesses ++ suffix) cursorHeld (by simpa using countHeld) candidateHeld
          (by simp only [List.length_cons] at cursorFits; omega)
          (by simpa using countFits) cb source vb valueFits stored (by simpa using input)
          pc running fits boolFits (by omega) block
      have nextRepresented : SharedRootLoop.RepresentedRoots next.heap (cursor + 1) valueBase roots := by
        rw [nh]
        exact represented_push state.heap _ (cursor + 1) valueBase roots rest
      obtain ⟨final, lastTicks, lastTrace, lastTime, fn, fc, fCandidate, fh, fs, fo, fp, fr⟩ :=
        ih next (cursor + 1) witnesses nextRepresented (by simpa using lengths) ns nc nn nCandidate
          (by simp only [List.length_cons] at cursorFits; omega)
          (by simp only [List.length_cons] at countFits; omega)
          (by simp only [nh, Array.size_push]; simp only [List.length_cons] at heapFits; omega) np nr
      have nextLive : next.liveWords = state.liveWords := by
        simp only [State.liveWords, nh, ns, no, Array.size_push, input, List.length_append, List.length_cons]
        omega
      have joined := firstTrace.append lastTrace
      rw [nextLive, Nat.max_self] at joined
      refine ⟨final, firstTicks + lastTicks, joined, ?_, fn, ?_, fCandidate, ?_, fs, fo.trans no, fp, fr⟩
      · simp only [List.length_cons]; omega
      · simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using fc
      · rw [fh, nh]
        change state.heap.push (if observed then candidate else old) ++
          (updated candidate roots witnesses).toArray =
          state.heap ++ ((if observed then candidate else old) :: updated candidate roots witnesses).toArray
        rw [List.toArray_cons, Array.push_eq_append, Array.append_assoc]

end Controller.Cost.SharedRootAggregate
