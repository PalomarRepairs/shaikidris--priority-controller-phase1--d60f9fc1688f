module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedEvaluationReclaim
public import Controller.Cost.SharedGraphEvaluation

@[expose] public section

/-! Fetched reclamation of a suffix while retaining the graph and channel table. -/
namespace Controller.Cost.SharedGraphReclaim
open Controller.Cost.RawTransferLoops

private theorem release_round (resident : Program width 8) (entry done count : Nat)
    (state : State width 8) (position : state.pc = word width entry)
    (room : entry + 4 < 2 ^ width) (running : state.halted = false)
    (heapPositive : 0 < state.heap.size) (countFits : count + 1 < 2 ^ width)
    (countReg : state.reg 0 = word width (count + 1))
    (maskReg : state.reg 7 = word width (2 ^ width - 1)) (zeroReg : state.reg 6 = word width 0)
    (atCode : CodeAt resident entry (countedReleaseCode width entry done)) :
    ∃ next peak, Execution resident state next 4 peak ∧ peak ≤ state.liveWords ∧
      next.pc = word width entry ∧ next.halted = false ∧ next.heap = state.heap.pop ∧
      next.stack = state.stack ∧ next.output = state.output ∧
      next.reg 0 = word width count ∧
      (∀ index : Fin 8, index ≠ 0 → next.reg index = state.reg index) := by
  let s1 := state.advance
  let s2 := { s1.advance with heap := state.heap.pop }
  let s3 := s2.advance.put 0 (word width count)
  let next := { s3.advance with pc := word width entry }
  have maskFits : 2 ^ width - 1 < 2 ^ width := by have := Nat.two_pow_pos width; omega
  have pc1 : s1.pc = word width (entry + 1) := advance_position state position (by omega)
  have pc2 : s2.pc = word width (entry + 2) := by
    exact advance_position s1 pc1 (by omega)
  have pc3 : s3.pc = word width (entry + 3) := by
    exact advance_position s2 pc2 (by omega)
  have code0 : resident[entry]? = some (.branchZero 0 (word width done)) := by
    simpa [countedReleaseCode] using atCode ⟨0, by simp⟩
  have code1 : resident[entry + 1]? = some .release := by
    simpa [countedReleaseCode] using atCode ⟨1, by simp⟩
  have code2 : resident[entry + 2]? = some (.add 0 0 7) := by
    simpa [countedReleaseCode] using atCode ⟨2, by simp⟩
  have code3 : resident[entry + 3]? = some (.branchZero 6 (word width entry)) := by
    simpa [countedReleaseCode] using atCode ⟨3, by simp⟩
  have countValue : (state.reg 0).val = count + 1 := by
    rw [countReg]; exact Nat.mod_eq_of_lt countFits
  have maskValue : (state.reg 7).val = 2 ^ width - 1 := by
    rw [maskReg]; exact Nat.mod_eq_of_lt maskFits
  have active : state.heap.isEmpty = false := Array.isEmpty_eq_false_iff.mpr (by
    intro empty; rw [empty] at heapPositive; simp at heapPositive)
  have t0 : programStep resident state = some s1 := by
    rw [fetched resident state entry _ position (by omega) code0]
    simp [step, running, countValue, s1]
  have t1 : programStep resident s1 = some s2 := by
    rw [fetched resident s1 (entry + 1) _ pc1 (by omega) code1]
    simp [step, s1, State.advance, running, active, s2]
  have t2 : programStep resident s2 = some s3 := by
    rw [fetched resident s2 (entry + 2) _ pc2 (by omega) code2]
    have v0 : (s2.reg 0).val = count + 1 := countValue
    have v7 : (s2.reg 7).val = 2 ^ width - 1 := maskValue
    simp only [step, show s2.halted = false from running, Bool.false_eq_true, ite_false, v0, v7]
    rw [decrement_word]
  have t3 : programStep resident s3 = some next := by
    rw [fetched resident s3 (entry + 3) _ pc3 (by omega) code3]
    simp [step, s3, s2, s1, State.advance, State.put, running, zeroReg, word, next]
  have l1 : s1.liveWords = state.liveWords := rfl
  have l2 : s2.liveWords ≤ state.liveWords := by
    simp only [s2, s1, State.liveWords, State.advance, Array.size_pop]; omega
  have l3 : s3.liveWords = s2.liveWords := rfl
  have ln : next.liveWords = s2.liveWords := rfl
  have trace := Execution.cons t0 (Execution.cons t1 (Execution.cons t2
    (Execution.cons t3 (Execution.refl next))))
  have peakEqual : max state.liveWords (max s1.liveWords
      (max s2.liveWords (max s3.liveWords next.liveWords))) = state.liveWords := by omega
  refine ⟨next, state.liveWords, ?_, le_rfl, rfl, running, rfl, rfl, rfl, ?_, ?_⟩
  · simpa only [Nat.zero_add, peakEqual] using trace
  · simp [next, s3, State.advance, State.put]
  · intro index different
    simp [next, s3, s2, s1, State.advance, State.put, different]


theorem execution (resident : Program width 8) (entry done : Nat)
    (retained : Array (Word width)) (values : List (Word width)) :
    ∀ state : State width 8, state.pc = word width entry → state.halted = false →
      entry + 4 < 2 ^ width → state.heap = retained ++ values.toArray →
      values.length < 2 ^ width → state.reg 0 = word width values.length →
      state.reg 7 = word width (2 ^ width - 1) → state.reg 6 = word width 0 →
      CodeAt resident entry (countedReleaseCode width entry done) →
    ∃ final peak, Execution resident state final (4 * values.length + 1) peak ∧
      peak ≤ state.liveWords ∧ final.heap = retained ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width done ∧ final.halted = false ∧ final.reg 0 = word width 0 ∧
      (∀ index : Fin 8, index ≠ 0 → final.reg index = state.reg index) := by
  induction values using List.reverseRecOn with
  | nil =>
    intro state position running room heap countFits countReg maskReg zeroReg atCode
    let final := { state.advance with pc := word width done }
    have transition : programStep resident state = some final :=
      release_zero_step resident entry done state position (by omega) running
        (by rw [countReg]; simp [word]) atCode
    have live : final.liveWords = state.liveWords := rfl
    refine ⟨final, state.liveWords, ?_, le_rfl, ?_, rfl, rfl, rfl, running, countReg, ?_⟩
    · simpa only [List.length_nil, Nat.mul_zero, Nat.zero_add, live, Nat.max_self] using
        Execution.cons transition (Execution.refl final)
    · simpa [final, State.advance] using heap
    · intro index different; rfl
  | append_singleton values value ih =>
    intro state position running room heap countFits countReg maskReg zeroReg atCode
    have length : (values ++ [value]).length = values.length + 1 := by simp
    obtain ⟨middle, firstPeak, first, firstBound, middlePC, middleRunning, middleHeap,
      middleStack, middleOutput, middleReg, middleFrame⟩ :=
      release_round resident entry done values.length state position room running
        (by simp [heap]) (by simpa only [length] using countFits)
        (by simpa only [length] using countReg) maskReg zeroReg atCode
    have middlePhysical : middle.heap = retained ++ values.toArray := by
      rw [middleHeap, heap]
      simp
    have middleLive : middle.liveWords ≤ state.liveWords :=
      (Execution.final_storage_le first).trans firstBound
    obtain ⟨final, lastPeak, last, lastBound, finalHeap, finalStack, finalOutput,
      finalPC, finalRunning, finalReg, finalFrame⟩ :=
      ih middle middlePC middleRunning room middlePhysical (by omega) middleReg
        ((middleFrame 7 (by decide)).trans maskReg)
        ((middleFrame 6 (by decide)).trans zeroReg) atCode
    refine ⟨final, max firstPeak lastPeak, ?_, Nat.max_le.mpr
      ⟨firstBound, lastBound.trans middleLive⟩, finalHeap, finalStack.trans middleStack,
      finalOutput.trans middleOutput, finalPC, finalRunning, finalReg, ?_⟩
    · have total : 4 + (4 * values.length + 1) = 4 * (values ++ [value]).length + 1 := by simp; omega
      simpa only [total] using first.append last
    · intro index different
      exact (finalFrame index different).trans (middleFrame index different)

set_option maxHeartbeats 2000000 in
theorem setup_execution (resident : Program width 8) (state : State width 8)
    (entry done : Nat) (retained : Array (Word width)) (values : List (Word width)) (position : state.pc = word width entry)
    (running : state.halted = false) (room : entry + 7 < 2 ^ width)
    (heapStored : state.heap = retained ++ values.toArray) (heapFits : values.length < 2 ^ width)
    (physical : CodeAt resident entry (SharedEvaluationReclaim.code width entry done values.length)) :
    ∃ final, Execution resident state final (4 * values.length + 4) state.liveWords ∧
      final.heap = retained ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width done ∧ final.halted = false ∧
      final.reg 0 = word width 0 ∧ final.reg 6 = word width 0 ∧
      final.reg 7 = word width (2 ^ width - 1) ∧
      (∀ index : Fin 8, index ≠ 0 → index ≠ 6 → index ≠ 7 → final.reg index = state.reg index) := by
  have all := physical
  unfold SharedEvaluationReclaim.code at all
  have setup := RawSharedOrdered.takePrefix resident entry _ _ all
  have tail := RawSharedOrdered.takeSuffix resident entry _ _ all
  have loop : CodeAt resident (entry + 3) (countedReleaseCode width (entry + 3) done) := by
    simpa only [List.size_toArray, List.length_cons, List.length_nil] using tail
  obtain ⟨counted, t₀, pc₀, value₀, heap₀, stack₀, out₀, run₀, frame₀⟩ :=
    SharedEvaluationReclaim.constant_execution resident entry values.length 0 state position running (by omega)
      (by simpa using setup ⟨0, by change 0 < 3; decide⟩)
  obtain ⟨zeroed, t₁, pc₁, value₁, heap₁, stack₁, out₁, run₁, frame₁⟩ :=
    SharedEvaluationReclaim.constant_execution resident (entry + 1) 0 6 counted pc₀ run₀ (by omega)
      (by simpa using setup ⟨1, by change 1 < 3; decide⟩)
  obtain ⟨ready, t₂, pc₂, value₂, heap₂, stack₂, out₂, run₂, frame₂⟩ :=
    SharedEvaluationReclaim.constant_execution resident (entry + 2) (2 ^ width - 1) 7 zeroed
      (by simpa only [Nat.add_assoc, Nat.reduceAdd] using pc₁) run₁ (by omega)
      (by simpa using setup ⟨2, by change 2 < 3; decide⟩)
  obtain ⟨final, peak, release, bound, empty, stack, output, pc, active, zero, frame⟩ :=
    execution resident (entry + 3) done retained values ready
      (by simpa only [Nat.add_assoc, Nat.reduceAdd] using pc₂) run₂ (by omega)
      (by rw [heap₂, heap₁, heap₀]; exact heapStored) heapFits
      (by rw [frame₂ 0 (by decide), frame₁ 0 (by decide)]; exact value₀)
      value₂ (by rw [frame₂ 6 (by decide)]; exact value₁) loop
  have countedLive : counted.liveWords = state.liveWords := by
    simp only [State.liveWords, heap₀, stack₀, out₀]
  have zeroedLive : zeroed.liveWords = state.liveWords := by
    simp only [State.liveWords, heap₁, stack₁, out₁, heap₀, stack₀, out₀]
  have readyLive : ready.liveWords = state.liveWords := by
    simp only [State.liveWords, heap₂, stack₂, out₂, heap₁, stack₁, out₁, heap₀, stack₀, out₀]
  have joined := t₀.append (t₁.append (t₂.append release))
  have ticksEq : 1 + (1 + (1 + (4 * values.length + 1))) = 4 * values.length + 4 := by omega
  have peakEq : max state.liveWords (max counted.liveWords (max zeroed.liveWords peak)) =
      state.liveWords := by simp only [countedLive, zeroedLive, readyLive] at bound ⊢; omega
  rw [ticksEq, peakEq] at joined
  refine ⟨final, joined, empty, stack.trans (stack₂.trans (stack₁.trans stack₀)),
    output.trans (out₂.trans (out₁.trans out₀)), pc, active, zero, ?_, ?_, ?_⟩
  · rw [frame 6 (by decide), frame₂ 6 (by decide)]; exact value₁
  · rw [frame 7 (by decide)]; exact value₂
  · intro index a b c
    rw [frame index a, frame₂ index c, frame₁ index b, frame₀ index a]


open Controller.Decoder Controller.Decoder.DAG Controller.Cost.GateProgram
open Controller.Cost.ForestIndexedOperands
open Controller.Cost.ForestInputStored Controller.Cost.ForestInputPrefixStored
open Controller.Cost.UniformDAGRun

theorem node_table_execution (resident : Program width 8) (state : State width 8)
    (graph : DAG n) (rows : List Row) (roots : List Nat) (values : Assignment n)
    (entry done : Nat) (position : state.pc = word width entry)
    (running : state.halted = false) (room : entry + 7 < 2 ^ width)
    (physicalHeap : state.heap = evaluationHeap (packetHeaderHeap width n rows roots)
      rows roots values (graph.evalTable values))
    (capacity : graph.nodeCount < 2 ^ width)
    (physicalCode : CodeAt resident entry
      (SharedEvaluationReclaim.code width entry done graph.nodeCount)) :
    ∃ final, Execution resident state final (4 * graph.nodeCount + 4) state.liveWords ∧
      final.heap = channelHeap (packetHeaderHeap width n rows roots) rows roots values ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width done ∧ final.halted = false ∧
      final.reg 0 = word width 0 ∧ final.reg 6 = word width 0 ∧
      final.reg 7 = word width (2 ^ width - 1) ∧
      (∀ index : Fin 8, index ≠ 0 → index ≠ 6 → index ≠ 7 → final.reg index = state.reg index) := by
  let words := List.ofFn (fun id => boolWord width (graph.evalTable values id))
  have length : words.length = graph.nodeCount := by simp [words]
  simpa only [length] using setup_execution resident state entry done
    (channelHeap (packetHeaderHeap width n rows roots) rows roots values) words
    position running room physicalHeap (by simpa only [length] using capacity)
    (by simpa only [length] using physicalCode)

end Controller.Cost.SharedGraphReclaim
