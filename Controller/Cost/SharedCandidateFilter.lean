module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedCandidateRead

@[expose] public section

/-! Fetched baseline and exclusion tests skip exactly the disallowed candidate heads. -/
namespace Controller.Cost.SharedCandidateFilter
open Controller.Cost.RawTransferLoops Controller.Cost.ForestInputStored

def code (width entry skip base : Nat) : Program width 8 :=
  SharedCandidateRead.code width base ++
    (SharedCandidateRoute.code width (entry + 3) skip 1 ++
      SharedCandidateRoute.code width (entry + 6) skip 2)

@[simp] theorem code_size (width entry skip base : Nat) : (code width entry skip base).size = 9 := by simp [code]

theorem execution (resident : Program width 8) (state : State width 8)
    (heap : Array (Word width)) (values : Fin n → Bool) (channel : Fin n) (excluded : Bool)
    (entry skip : Nat) (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 9 < 2 ^ width) (capacity : heap.size + n < 2 ^ width) (boolFits : 1 < 2 ^ width)
    (heapStored : state.heap = withValues heap values)
    (candidateHeld : state.reg 4 = word width channel.val) (excludedHeld : state.reg 2 = boolWord width excluded)
    (physical : CodeAt resident entry (code width entry skip heap.size)) :
    ∃ final ticks, Execution resident state final ticks state.liveWords ∧ ticks ≤ 7 ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (if values channel || excluded then skip else entry + 9) ∧ final.halted = false ∧
      (∀ register : Fin 8, register ≠ 0 → register ≠ 1 → final.reg register = state.reg register) := by
  have all := physical
  unfold code at all
  have readCode := RawSharedOrdered.takePrefix resident entry _ _ all
  have tail := RawSharedOrdered.takeSuffix resident entry _ _ all
  have firstRoute := RawSharedOrdered.takePrefix resident (entry + 3) _ _ (by simpa using tail)
  have secondRoute := RawSharedOrdered.takeSuffix resident (entry + 3) _ _ (by simpa using tail)
  obtain ⟨read, readTrace, baseline, rh, rs, ro, rp, rr, rf⟩ :=
    SharedCandidateRead.execution resident state heap values channel entry position running
      (by omega) capacity heapStored candidateHeld readCode
  have readLive : read.liveWords = state.liveWords := by simp only [State.liveWords, rh, rs, ro]
  cases selected : values channel with
  | true =>
    obtain ⟨final, routeTrace, fh, fs, fo, fp, fr, ff⟩ :=
      SharedCandidateRoute.execution resident read (entry + 3) skip 1 true rp rr (by omega) boolFits
        (by simpa only [selected] using baseline) firstRoute
    have joined := readTrace.append routeTrace
    rw [readLive, Nat.max_self] at joined
    refine ⟨final, 6, by simpa using joined, by decide, fh.trans rh, fs.trans rs, fo.trans ro, ?_, fr, ?_⟩
    · simpa [selected] using fp
    · intro register different0 different1
      exact (ff register different0).trans (rf register different0 different1)
  | false =>
    obtain ⟨tested, testTrace, th, ts, testedOutput, tp, tr, tf⟩ :=
      SharedCandidateRoute.execution resident read (entry + 3) skip 1 false rp rr (by omega) boolFits
        (by simpa only [selected] using baseline) firstRoute
    have testedLive : tested.liveWords = state.liveWords := by
      simp only [State.liveWords, th, ts, testedOutput, rh, rs, ro]
    obtain ⟨final, routeTrace, fh, fs, fo, fp, fr, ff⟩ :=
      SharedCandidateRoute.execution resident tested (entry + 6) skip 2 excluded
        (by simpa only [Bool.false_eq_true, ite_false, Nat.add_assoc, Nat.reduceAdd] using tp)
        tr (by omega) boolFits
        ((tf 2 (by decide)).trans ((rf 2 (by decide) (by decide)).trans excludedHeld))
        (by simpa only [SharedCandidateRoute.code_size, Nat.add_assoc, Nat.reduceAdd] using secondRoute)
    have joined := readTrace.append (testTrace.append routeTrace)
    rw [readLive, testedLive, Nat.max_self, Nat.max_self] at joined
    refine ⟨final, 3 + (1 + (if excluded then 3 else 1)), by simpa using joined, ?_,
      fh.trans (th.trans rh), fs.trans (ts.trans rs), fo.trans (testedOutput.trans ro), ?_, fr, ?_⟩
    · cases excluded <;> decide
    · simpa [selected, Nat.add_assoc] using fp
    · intro register different0 different1
      exact (ff register different0).trans ((tf register different0).trans (rf register different0 different1))

theorem allowed_iff (T F : Finset (Channel n)) (channel : Channel n) :
    (assignmentOfSet T channel || assignmentOfSet F channel) = false ↔ channel ∉ T ∧ channel ∉ F := by
  simp [assignmentOfSet]

end Controller.Cost.SharedCandidateFilter
