module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.UniformDAGZeroGate
public import Mathlib.Tactic.IntervalCases

@[expose] public section

/-! A fixed dispatcher fetches the cached source tag and selects one of the
five gate handlers. Only layout addresses and handler addresses are constants;
the gate tag is read from the shared source packet. -/
namespace Controller.Cost.UniformDAGDispatch
open Controller.Cost.GateProgram

def code (width tagBase : ℕ) (dest : Fin 5 → ℕ) : Code width :=
  [.constant 0 (word width tagBase), .add 0 0 3, .load 0 0,
    .branchZero 0 (word width (dest 0)),
    .constant 2 (word width (2 ^ width - 1)),
    .add 0 0 2, .branchZero 0 (word width (dest 1)),
    .add 0 0 2, .branchZero 0 (word width (dest 2)),
    .add 0 0 2, .branchZero 0 (word width (dest 3)),
    .add 0 0 2, .branchZero 0 (word width (dest 4)), .halt]
@[simp] theorem code_length : (code width tagBase dest).length = 14 := rfl

private theorem fetched (program : Program width 4) (s : State width 4)
    (address : ℕ) (instruction : Instruction width 4)
    (pc : s.pc = word width address) (fits : address < 2 ^ width)
    (entry : program[address]? = some instruction) :
    programStep program s = step instruction s := by
  unfold programStep
  rw [pc, show (word width address).val = address from Nat.mod_eq_of_lt fits, entry]
  rfl

private theorem advance_pc (s : State width 4) (address : ℕ)
    (pc : s.pc = word width address) (fits : address < 2 ^ width) :
    s.advance.pc = word width (address + 1) := by
  simp only [State.advance, pc]
  rw [show (word width address).val = address from Nat.mod_eq_of_lt fits]

private theorem code_add (stage : ℕ) (bounded : stage < 4) :
    (code width tagBase dest)[5 + 2 * stage]? = some (.add 0 0 2) := by
  interval_cases stage <;> rfl

private theorem code_branch (stage : ℕ) (bounded : stage < 4) :
    (code width tagBase dest)[6 + 2 * stage]? =
      some (.branchZero 0 (word width (dest ⟨stage + 1, by omega⟩))) := by
  interval_cases stage <;> rfl

/-- Each comparison executes one decrement and one fetched conditional branch. -/
private theorem countdown (program : Program width 4) (base tagBase : ℕ)
    (dest : Fin 5 → ℕ) (fits : base + 14 < 2 ^ width)
    (block : BlockAt program base (code width tagBase dest))
    (remaining stage : ℕ) (bounded : stage + remaining < 4)
    (s : State width 4) (value : s.reg 0 = word width (remaining + 1))
    (pred : s.reg 2 = word width (2 ^ width - 1))
    (pc : s.pc = word width (base + 5 + 2 * stage)) (running : s.halted = false) :
    ∃ final, Execution program s final (2 * (remaining + 1)) s.liveWords ∧
      final.reg 0 = word width 0 ∧ final.reg 1 = s.reg 1 ∧
      final.reg 2 = s.reg 2 ∧ final.reg 3 = s.reg 3 ∧
      final.heap = s.heap ∧ final.stack = s.stack ∧ final.output = s.output ∧
      final.pc = word width (dest ⟨stage + remaining + 1, by omega⟩) ∧
      final.halted = false := by
  induction remaining generalizing stage s with
  | zero =>
    let ready := s.advance.put 0 (word width 0)
    let final := { ready with pc := word width (dest ⟨stage + 1, by omega⟩) }
    have pv : s.pc.val = base + 5 + 2 * stage := by
      rw [pc]; exact Nat.mod_eq_of_lt (by omega)
    have countVal : (word width 1).val = 1 := Nat.mod_eq_of_lt (by omega)
    have predVal : (word width (2 ^ width - 1)).val = 2 ^ width - 1 :=
      Nat.mod_eq_of_lt (by omega)
    have decrement : (1 + (2 ^ width - 1)) % 2 ^ width = 0 := by
      have eq : 1 + (2 ^ width - 1) = 2 ^ width := by omega
      rw [eq]; exact Nat.mod_self _
    have first : programStep program s = some ready := by
      rw [fetched program s _ (.add 0 0 2) pc (by omega)
        (by simpa only [Nat.add_assoc] using block (5 + 2 * stage) (by simp; omega) |>.trans (code_add stage (by omega)))]
      simp [step, ready, State.advance, State.put, value, pred, word, running,
        countVal, predVal, decrement]
    have readyPC : ready.pc = word width (base + 6 + 2 * stage) := by
      simp [ready, State.advance, State.put, pv]; congr 1 <;> omega
    have last : programStep program ready = some final := by
      rw [fetched program ready _ (.branchZero 0 (word width (dest ⟨stage + 1, by omega⟩))) readyPC (by omega)
        (by simpa only [Nat.add_assoc] using block (6 + 2 * stage) (by simp; omega) |>.trans (code_branch stage (by omega)))]
      simp [step, ready, final, State.put, State.advance, running, word]
    refine ⟨final, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
    · have rl : ready.liveWords = s.liveWords := rfl
      have fl : final.liveWords = s.liveWords := rfl
      simpa only [rl, fl, Nat.max_self] using
        Execution.cons first (Execution.cons last (Execution.refl final))
    all_goals simp [final, ready, State.put, State.advance, running]
  | succ remaining ih =>
    let ready := s.advance.put 0 (word width (remaining + 1))
    let next := ready.advance
    have pv : s.pc.val = base + 5 + 2 * stage := by
      rw [pc]; exact Nat.mod_eq_of_lt (by omega)
    have countVal : (word width (remaining + 1 + 1)).val = remaining + 1 + 1 :=
      Nat.mod_eq_of_lt (by omega)
    have predVal : (word width (2 ^ width - 1)).val = 2 ^ width - 1 :=
      Nat.mod_eq_of_lt (by omega)
    have decrement : ((remaining + 1 + 1) + (2 ^ width - 1)) % 2 ^ width = remaining + 1 := by
      have eq : (remaining + 1 + 1) + (2 ^ width - 1) = remaining + 1 + 2 ^ width := by omega
      rw [eq, Nat.add_mod_right]; exact Nat.mod_eq_of_lt (by omega)
    have remainingValue : (remaining + 1) % 2 ^ width = remaining + 1 := Nat.mod_eq_of_lt (by omega)
    have normalizedDecrement : (remaining + (2 + (2 ^ width - 1))) % 2 ^ width = remaining + 1 := by
      calc
        (remaining + (2 + (2 ^ width - 1))) % 2 ^ width =
            (remaining + 1 + 1 + (2 ^ width - 1)) % 2 ^ width := congrArg (fun x => x % 2 ^ width) (by omega)
        _ = remaining + 1 := decrement
    have first : programStep program s = some ready := by
      rw [fetched program s _ (.add 0 0 2) pc (by omega)
        (by simpa only [Nat.add_assoc] using block (5 + 2 * stage) (by simp; omega) |>.trans (code_add stage (by omega)))]
      simp [step, ready, State.advance, State.put, value, pred, word, running,
        countVal, predVal, normalizedDecrement, remainingValue, Nat.add_assoc]
    have readyPC : ready.pc = word width (base + 6 + 2 * stage) := by
      simp [ready, State.advance, State.put, pv]; congr 1 <;> omega
    have rv : ready.pc.val = base + 6 + 2 * stage := by
      rw [readyPC]; exact Nat.mod_eq_of_lt (by omega)
    have val : (word width (remaining + 1)).val = remaining + 1 := Nat.mod_eq_of_lt (by omega)
    have second : programStep program ready = some next := by
      rw [fetched program ready _ (.branchZero 0 (word width (dest ⟨stage + 1, by omega⟩))) readyPC (by omega)
        (by simpa only [Nat.add_assoc] using block (6 + 2 * stage) (by simp; omega) |>.trans (code_branch stage (by omega)))]
      simp [step, ready, next, State.put, State.advance, running, val]
    have nextPC : next.pc = word width (base + 5 + 2 * (stage + 1)) := by
      simp [next, State.advance, rv]; congr 1 <;> omega
    obtain ⟨final, trace, r0, r1, r2, r3, heap, stack, output, finalPC, finalRun⟩ :=
      ih (stage + 1) (by omega) next (by simp [next, ready, State.put, State.advance])
        (by simpa [next, ready, State.put, State.advance] using pred)
        nextPC (by simp [next, ready, State.put, State.advance, running])
    refine ⟨final, ?_, r0, ?_, ?_, ?_, heap, stack, output, ?_, finalRun⟩
    · have rl : ready.liveWords = s.liveWords := rfl
      have nl : next.liveWords = s.liveWords := rfl
      have prepTrace := Execution.cons first (Execution.cons second (Execution.refl next))
      have joined := prepTrace.append trace
      have converted : Execution program s final (2 + 2 * (remaining + 1)) s.liveWords := by
        simpa only [rl, nl, Nat.max_self, Nat.add_zero, Nat.zero_add, Nat.reduceAdd] using joined
      convert converted using 1 <;> omega
    · simpa [next, ready, State.put, State.advance] using r1
    · simpa [next, ready, State.put, State.advance] using r2
    · simpa [next, ready, State.put, State.advance] using r3
    · simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using finalPC

/-- The cached tag is read by three actual fetched instructions. -/
theorem read_tag (program : Program width 4) (s : State width 4)
    (base tagBase offset : ℕ) (tag : Fin 5) (dest : Fin 5 → ℕ)
    (offsetHeld : s.reg 3 = word width offset)
    (addressFits : tagBase + offset < 2 ^ width)
    (addressBound : tagBase + offset < s.heap.size)
    (source : s.heap[tagBase + offset]'addressBound = word width tag.val)
    (pc : s.pc = word width base) (running : s.halted = false)
    (fits : base + 14 < 2 ^ width)
    (block : BlockAt program base (code width tagBase dest)) :
    ∃ ready, Execution program s ready 3 s.liveWords ∧
      ready.reg 0 = word width tag.val ∧ ready.reg 1 = s.reg 1 ∧
      ready.reg 2 = s.reg 2 ∧ ready.reg 3 = s.reg 3 ∧
      ready.heap = s.heap ∧ ready.stack = s.stack ∧ ready.output = s.output ∧
      ready.pc = word width (base + 3) ∧ ready.halted = false := by
  let one := s.advance.put 0 (word width tagBase)
  let two := one.advance.put 0 (word width (tagBase + offset))
  let ready := two.advance.put 0 (word width tag.val)
  have pv : s.pc.val = base := by rw [pc]; exact Nat.mod_eq_of_lt (by omega)
  have p1 : one.pc = word width (base + 1) := by simp [one, State.advance, State.put, pv]
  have p1v : one.pc.val = base + 1 := by rw [p1]; exact Nat.mod_eq_of_lt (by omega)
  have p2 : two.pc = word width (base + 2) := by simp [two, State.advance, State.put, p1v, Nat.add_assoc]
  have p2v : two.pc.val = base + 2 := by rw [p2]; exact Nat.mod_eq_of_lt (by omega)
  have tv : (word width tagBase).val = tagBase := Nat.mod_eq_of_lt (by omega)
  have ov : (word width offset).val = offset := Nat.mod_eq_of_lt (by omega)
  have av : (word width (tagBase + offset)).val = tagBase + offset := Nat.mod_eq_of_lt addressFits
  have first : programStep program s = some one := by
    rw [fetched program s base (.constant 0 (word width tagBase)) pc (by omega)
      (by simpa [code] using block 0 (by simp [code]))]
    simp [step, one, running]
  have second : programStep program one = some two := by
    rw [fetched program one (base + 1) (.add 0 0 3) p1 (by omega)
      (by simpa [code] using block 1 (by simp [code]))]
    simp [step, one, two, State.advance, State.put, running, offsetHeld, tv, ov]
  have third : programStep program two = some ready := by
    rw [fetched program two (base + 2) (.load 0 0) p2 (by omega)
      (by simpa [code] using block 2 (by simp [code]))]
    simp [step, one, two, ready, State.advance, State.put, running, av, addressBound, source]
  have readyPC : ready.pc = word width (base + 3) := by
    simpa [ready, State.put, Nat.add_assoc] using advance_pc two (base + 2) p2 (by omega)
  refine ⟨ready, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, readyPC, ?_⟩
  · have ol : one.liveWords = s.liveWords := rfl
    have tl : two.liveWords = s.liveWords := rfl
    have rl : ready.liveWords = s.liveWords := rfl
    simpa only [ol, tl, rl, Nat.max_self] using
      Execution.cons first (Execution.cons second (Execution.cons third (Execution.refl ready)))
  all_goals simp [ready, two, one, State.advance, State.put, running, p2v, Nat.add_assoc]

/-- All five typed tags select their runtime handler without allocation. -/
theorem execution (program : Program width 4) (s : State width 4)
    (base tagBase offset : ℕ) (tag : Fin 5) (dest : Fin 5 → ℕ)
    (offsetHeld : s.reg 3 = word width offset)
    (addressFits : tagBase + offset < 2 ^ width)
    (addressBound : tagBase + offset < s.heap.size)
    (source : s.heap[tagBase + offset]'addressBound = word width tag.val)
    (pc : s.pc = word width base) (running : s.halted = false)
    (fits : base + 14 < 2 ^ width)
    (block : BlockAt program base (code width tagBase dest)) :
    ∃ final, Execution program s final (if tag.val = 0 then 4 else 5 + 2 * tag.val) s.liveWords ∧
      final.reg 0 = word width 0 ∧ final.reg 1 = s.reg 1 ∧ final.reg 3 = s.reg 3 ∧
      final.heap = s.heap ∧ final.stack = s.stack ∧ final.output = s.output ∧
      final.pc = word width (dest tag) ∧ final.halted = false := by
  obtain ⟨read, trace, r0, r1, r2, r3, heap, stack, output, readPC, readRun⟩ :=
    read_tag program s base tagBase offset tag dest offsetHeld addressFits addressBound source pc running fits block
  have readVal : read.pc.val = base + 3 := by rw [readPC]; exact Nat.mod_eq_of_lt (by omega)
  by_cases zero : tag.val = 0
  · have tagZero : tag = 0 := Fin.ext zero
    let final := { read with pc := word width (dest 0) }
    have last : programStep program read = some final := by
      rw [fetched program read (base + 3) (.branchZero 0 (word width (dest 0))) readPC (by omega)
        (by simpa [code] using block 3 (by simp [code]))]
      simp [step, final, State.advance, readRun, r0, zero, word]
    refine ⟨final, ?_, ?_, r1, r3, heap, stack, output, ?_, readRun⟩
    · have rl : read.liveWords = s.liveWords := by simp [State.liveWords, heap, stack, output]
      have fl : final.liveWords = s.liveWords := rl
      simpa only [zero, ite_eq_left, rl, fl, Nat.max_self] using trace.append (Execution.cons last (Execution.refl final))
    · simpa [final, zero] using r0
    · simp [final, tagZero]
  · let one := read.advance
    let ready := one.advance.put 2 (word width (2 ^ width - 1))
    have tagVal : (word width tag.val).val = tag.val := Nat.mod_eq_of_lt (by omega)
    have first : programStep program read = some one := by
      rw [fetched program read (base + 3) (.branchZero 0 (word width (dest 0))) readPC (by omega)
        (by simpa [code] using block 3 (by simp [code]))]
      simp [step, one, readRun, r0, tagVal, zero]
    have onePC : one.pc = word width (base + 4) := by simp [one, State.advance, readVal, Nat.add_assoc]
    have ov : one.pc.val = base + 4 := by rw [onePC]; exact Nat.mod_eq_of_lt (by omega)
    have second : programStep program one = some ready := by
      rw [fetched program one (base + 4) (.constant 2 (word width (2 ^ width - 1))) onePC (by omega)
        (by simpa [code] using block 4 (by simp [code]))]
      simp [step, one, ready, State.advance, readRun]
    have readyPC : ready.pc = word width (base + 5) := by simp [ready, State.put, State.advance, ov, Nat.add_assoc]
    obtain ⟨final, tail, f0, f1, f2, f3, fh, fs, fo, fp, fr⟩ :=
      countdown program base tagBase dest fits block (tag.val - 1) 0 (by omega) ready
        (by simpa [ready, one, State.advance, State.put, Nat.sub_add_cancel (by omega : 1 ≤ tag.val)] using r0)
        (by simp [ready, State.put]) (by simpa using readyPC)
        (by simp [ready, one, State.put, State.advance, readRun])
    refine ⟨final, ?_, f0, ?_, ?_, ?_, ?_, ?_, ?_, fr⟩
    · have rl : read.liveWords = s.liveWords := by simp [State.liveWords, heap, stack, output]
      have ol : one.liveWords = s.liveWords := rl
      have il : ready.liveWords = s.liveWords := rl
      have prep := Execution.cons first (Execution.cons second (Execution.refl ready))
      have joined := (trace.append prep).append tail
      have size : tag.val - 1 + 1 = tag.val := by omega
      simpa only [ite_eq_right zero, size, rl, ol, il, Nat.max_self, Nat.zero_add, Nat.reduceAdd, Nat.add_assoc] using joined
    · simpa [ready, one, State.put, State.advance] using f1.trans (by simpa [ready, one, State.put, State.advance] using r1)
    · simpa [ready, one, State.put, State.advance] using f3.trans (by simpa [ready, one, State.put, State.advance] using r3)
    · exact fh.trans heap
    · exact fs.trans stack
    · exact fo.trans output
    · have chosen : (⟨0 + (tag.val - 1) + 1, by omega⟩ : Fin 5) = tag := Fin.ext (by simp; omega)
      simpa only [chosen] using fp

end Controller.Cost.UniformDAGDispatch
