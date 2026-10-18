module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedCandidateRoute
public import Controller.Cost.SharedDetectorAssembly

@[expose] public section

/-! The declared root occurrences are read from the retained packet. One
healthy table and one candidate table are shared by every observation. The
scan branches on the first healthy-zero root whose candidate value is true. -/
namespace Controller.Extensions.SupportRootScan
open Controller.Cost Controller.Cost.RawTransferLoops Controller.Cost.SharedDetectorAssembly

private theorem subblock (program : Program width 8) (entry : Nat)
    (whole : List (Instruction width 8)) (present : SharedRootRead.BlockAt program entry whole)
    (offset : Nat) (part : List (Instruction width 8)) (bound : offset + part.length ≤ whole.length)
    (same : (whole.drop offset).take part.length = part) :
    SharedRootRead.BlockAt program (entry + offset) part := by
  intro i below
  have selected := congrArg (fun xs : List (Instruction width 8) => xs[i]?) same
  simp only [List.getElem?_take, List.getElem?_drop, ite_eq_left below] at selected
  have stored : program[(entry + offset) + i]? = whole[offset + i]? := by
    simpa only [Nat.add_assoc] using present (offset + i) (by omega)
  exact stored.trans selected

def nodeCode (width entry cursor healthyBase valueBase found : Nat) : List (Instruction width 8) :=
  [.constant 3 (word width cursor), .constant 1 (word width healthyBase),
    .load 0 3, .add 0 0 1, .load 1 0,
    .branchZero 1 (word width (entry + 8)), .constant 0 (word width 0), .branchZero 0 (word width (entry + 15)),
    .constant 1 (word width valueBase), .load 0 3, .add 0 0 1, .load 1 0,
    .branchZero 1 (word width (entry + 15)), .constant 0 (word width 0), .branchZero 0 (word width found)]

@[simp] theorem nodeCode_length : (nodeCode width entry cursor healthyBase valueBase found).length = 15 := rfl

theorem node_execution (program : Program width 8) (state : State width 8)
    (entry cursor index healthyBase valueBase found : Nat) (healthy value : Bool)
    (source : state.heap[cursor]? = some (word width index))
    (healthyStored : state.heap[healthyBase + index]? = some (boolWord width healthy))
    (valueStored : state.heap[valueBase + index]? = some (boolWord width value))
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 15 < 2 ^ width) (heapFits : state.heap.size < 2 ^ width)
    (present : SharedRootRead.BlockAt program entry (nodeCode width entry cursor healthyBase valueBase found)) :
    ∃ final ticks, Execution program state final ticks state.liveWords ∧ ticks ≤ 13 ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (if !healthy && value then found else entry + 15) ∧ final.halted = false := by
  have sourceBound := (Array.getElem?_eq_some_iff.mp source).1
  have sourceCell := (Array.getElem?_eq_some_iff.mp source).2
  have healthyBound := (Array.getElem?_eq_some_iff.mp healthyStored).1
  have healthyCell := (Array.getElem?_eq_some_iff.mp healthyStored).2
  have valueBound := (Array.getElem?_eq_some_iff.mp valueStored).1
  have valueCell := (Array.getElem?_eq_some_iff.mp valueStored).2
  have readAt := subblock program entry _ present 2 (SharedRootRead.code width) (by simp) rfl
  have healthyAt := subblock program entry _ present 5
    (SharedCandidateRoute.code width (entry + 5) (entry + 15) 1).toList (by simp) (by rfl)
  have valueAt := subblock program entry _ present 9 (SharedRootRead.code width) (by simp) rfl
  have routeAt := subblock program entry _ present 12
    (SharedCandidateRoute.code width (entry + 12) found 1).toList (by simp) (by rfl)
  obtain ⟨s1, t1, p1, v1, h1, st1, o1, r1, f1⟩ :=
    SharedEvaluationReclaim.constant_execution program entry cursor 3 state position running (by omega)
      (by simpa [nodeCode] using present 0 (by simp))
  obtain ⟨s2, t2, p2, v2, h2, st2, o2, r2, f2⟩ :=
    SharedEvaluationReclaim.constant_execution program (entry + 1) healthyBase 1 s1 p1 r1 (by omega)
      (by simpa [nodeCode] using present 1 (by simp))
  obtain ⟨read, t3, _, observed, _, cursorReg, h3, st3, o3, p3, r3, _⟩ :=
    SharedRootRead.execution program s2 cursor healthyBase index (entry + 2) healthy
      ((f2 3 (by decide)).trans v1) v2 (by simpa [h2, h1] using sourceBound) (by omega)
      (by simpa [h2, h1] using sourceCell) (by simpa [h2, h1] using healthyBound) (by omega)
      (by simpa [h2, h1] using healthyCell) (by simpa [Nat.add_assoc] using p2) r2 (by omega) readAt
  obtain ⟨tested, t4, h4, st4, o4, p4, r4, f4⟩ :=
    SharedCandidateRoute.execution program read (entry + 5) (entry + 15) 1 healthy
      (by simpa [Nat.add_assoc] using p3) r3 (by omega) (by omega) observed (block_code _ _ _ healthyAt)
  have readHeap : read.heap = state.heap := h3.trans (h2.trans h1)
  have testedHeap : tested.heap = state.heap := h4.trans readHeap
  have testedStack : tested.stack = state.stack := st4.trans (st3.trans (st2.trans st1))
  have testedOutput : tested.output = state.output := o4.trans (o3.trans (o2.trans o1))
  have l1 : s1.liveWords = state.liveWords := by simp only [State.liveWords, h1, st1, o1]
  have l2 : s2.liveWords = state.liveWords := by simp only [State.liveWords, h2, st2, o2, h1, st1, o1]
  have l3 : read.liveWords = state.liveWords := by simp only [State.liveWords, h3, st3, o3, h2, st2, o2, h1, st1, o1]
  have l4 : tested.liveWords = state.liveWords := by simp only [State.liveWords, testedHeap, testedStack, testedOutput]
  have joined := t1.append (t2.append (t3.append t4))
  simp only [l1, l2, l3, Nat.max_self] at joined
  cases healthy with
  | true =>
      exact ⟨tested, 8, by simpa using joined, by decide, testedHeap, testedStack, testedOutput,
        by simpa using p4, r4⟩
  | false =>
      obtain ⟨s5, t5, p5, v5, h5, st5, o5, r5, f5⟩ :=
        SharedEvaluationReclaim.constant_execution program (entry + 8) valueBase 1 tested
          (by simpa [Nat.add_assoc] using p4) r4 (by omega)
          (by simpa [nodeCode] using present 8 (by simp))
      have cursorHeld : s5.reg 3 = word width cursor := by
        rw [f5 3 (by decide), f4 3 (by decide), cursorReg, f2 3 (by decide), v1]
      obtain ⟨reread, t6, _, second, _, _, h6, st6, o6, p6, r6, _⟩ :=
        SharedRootRead.execution program s5 cursor valueBase index (entry + 9) value cursorHeld v5
          (by simpa [h5, testedHeap] using sourceBound) (by omega)
          (by simpa [h5, testedHeap] using sourceCell) (by simpa [h5, testedHeap] using valueBound) (by omega)
          (by simpa [h5, testedHeap] using valueCell) (by simpa [Nat.add_assoc] using p5) r5 (by omega) valueAt
      obtain ⟨final, t7, h7, st7, o7, p7, r7, _⟩ :=
        SharedCandidateRoute.execution program reread (entry + 12) found 1 value
          (by simpa [Nat.add_assoc] using p6) r6 (by omega) (by omega) second (block_code _ _ _ routeAt)
      have l5 : s5.liveWords = state.liveWords := by
        simp only [State.liveWords, h5, st5, o5, testedHeap, testedStack, testedOutput]
      have l6 : reread.liveWords = state.liveWords := by simp only [State.liveWords, h6, st6, o6, h5, st5, o5,
        testedHeap, testedStack, testedOutput]
      refine ⟨final, 10 + (if value then 3 else 1), ?_, by cases value <;> decide,
        h7.trans (h6.trans (h5.trans testedHeap)), st7.trans (st6.trans (st5.trans testedStack)),
        o7.trans (o6.trans (o5.trans testedOutput)), ?_, r7⟩
      · simpa only [l4, l5, l6, Nat.max_self, ← Nat.add_assoc, Nat.reduceAdd, Bool.false_eq_true, ite_false] using
          joined.append (t5.append (t6.append t7))
      · simpa [Nat.add_assoc] using p7

def code (width entry cursor healthyBase valueBase found count : Nat) : List (Instruction width 8) :=
  (List.range count).flatMap fun i => nodeCode width (entry + 15 * i) (cursor + i) healthyBase valueBase found

@[simp] theorem code_length : (code width entry cursor healthyBase valueBase found count).length = 15 * count := by
  simp [code, List.length_flatMap]; omega

theorem code_succ : code width entry cursor healthyBase valueBase found (count + 1) =
    nodeCode width entry cursor healthyBase valueBase found ++
      code width (entry + 15) (cursor + 1) healthyBase valueBase found count := by
  simp only [code, List.range_succ_eq_map, List.flatMap_cons, Nat.mul_zero, Nat.add_zero,
    List.flatMap_map]
  congr 1
  apply List.flatMap_congr
  intro i member
  congr 1 <;> omega

theorem execution (program : Program width 8) (state : State width 8)
    (entry cursor healthyBase valueBase found : Nat) (observations : List Nat)
    (healthy values : Nat → Bool)
    (source : ∀ i (below : i < observations.length), state.heap[cursor + i]? = some (word width observations[i]))
    (healthyStored : ∀ i ∈ observations, state.heap[healthyBase + i]? = some (boolWord width (healthy i)))
    (valueStored : ∀ i ∈ observations, state.heap[valueBase + i]? = some (boolWord width (values i)))
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 15 * observations.length < 2 ^ width) (heapFits : state.heap.size < 2 ^ width)
    (present : SharedRootRead.BlockAt program entry
      (code width entry cursor healthyBase valueBase found observations.length)) :
    ∃ final ticks, Execution program state final ticks state.liveWords ∧ ticks ≤ 13 * observations.length ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (if observations.any (fun i => !healthy i && values i) then found
        else entry + 15 * observations.length) ∧ final.halted = false := by
  induction observations generalizing entry cursor state with
  | nil => exact ⟨state, 0, Execution.refl _, by simp, rfl, rfl, rfl, by simpa using position, running⟩
  | cons head tail ih =>
      rw [List.length_cons, code_succ] at present
      have firstAt := block_left program entry _ _ present
      have tailAt := block_right program entry _ _ present
      simp only [nodeCode_length] at tailAt
      obtain ⟨middle, mt, first, time, heap, stack, output, pc, active⟩ :=
        node_execution program state entry cursor head healthyBase valueBase found (healthy head) (values head)
          (by have selected := source 0 (by simp)
              change state.heap[cursor + 0]? = some (word width head) at selected
              simpa using selected)
          (healthyStored head (by simp)) (valueStored head (by simp))
          position running (by simp only [List.length_cons] at room; omega) heapFits firstAt
      by_cases changed : (!healthy head && values head) = true
      · refine ⟨middle, mt, first, by simp only [List.length_cons]; omega, heap, stack, output, ?_, active⟩
        simpa [changed] using pc
      · have continuePC : middle.pc = word width (entry + 15) := by simpa [changed] using pc
        obtain ⟨final, ft, second, ftime, fh, fs, fo, fp, fr⟩ :=
          ih middle (entry + 15) (cursor + 1)
            (by intro i below
                have selected := source (i + 1) (by simp; omega)
                change state.heap[cursor + (i + 1)]? = some (word width tail[i]) at selected
                simpa only [heap, Nat.add_assoc, Nat.add_comm 1 i] using selected)
            (by intro i member; simpa [heap] using healthyStored i (by simp [member]))
            (by intro i member; simpa [heap] using valueStored i (by simp [member]))
            continuePC active (by simp only [List.length_cons] at room; omega) (by simpa [heap] using heapFits) tailAt
        have live : middle.liveWords = state.liveWords := by simp only [State.liveWords, heap, stack, output]
        refine ⟨final, mt + ft, by simpa only [live, Nat.max_self] using first.append second,
          by simp only [List.length_cons]; omega, fh.trans heap, fs.trans stack, fo.trans output, ?_, fr⟩
        simpa [changed, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using fp

end Controller.Extensions.SupportRootScan
