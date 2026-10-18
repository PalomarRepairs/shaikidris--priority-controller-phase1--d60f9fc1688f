module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Extensions.SupportSearch

@[expose] public section

/-! Initialized bounded-subset traversal with successful continuation or an
actual exhaustion halt. The caller supplies the fixed callback and its time
and scratch bounds; the mask and two-word sentinel are explicit runtime data. -/
namespace Controller.Extensions.SupportSearchRun
open Controller.Cost Controller.Extensions.SupportStream Controller.Extensions.SupportSearch

theorem ids_all (n : Nat) : ids 0 n (by omega) = List.finRange n := by
  have fn : (fun i : Fin n => (⟨0 + i.val, by omega⟩ : Fin n)) = id := by
    funext i; apply Fin.ext; simp
  simpa only [ids, fn] using List.ofFn_id n

theorem leaves_clamp (n r : Nat) : leaves n (min r n) = leaves n r := by
  by_cases lower : r ≤ n
  · rw [Nat.min_eq_left lower]
  · rw [Nat.min_eq_right (by omega), leaves_saturated n n le_rfl, leaves_saturated n r (by omega)]

def initial (n capacity entry : Nat) (source : Array (Word width))
    (rest output : List (Word width)) : State width 8 where
  reg i := if i = 3 then word width 0 else if i = 5 then word width (min capacity n) else word width 0
  heap := maskHeap source (∅ : Finset (Fin n))
  stack := word width n :: word width 0 :: rest
  output := output
  pc := word width entry
  halted := false

@[simp] theorem initial_live (n capacity entry : Nat) (source : Array (Word width))
    (rest output : List (Word width)) :
    (initial n capacity entry source rest output).liveWords =
      source.size + n + rest.length + output.length + 11 := by
  simp only [initial, State.liveWords, maskHeap_size, List.length_cons]; omega

def Outcome (source : Array (Word width)) (query : Finset (Fin n) → Option β)
    (found : Nat) (rest : List (Word width)) (final : State width 8) : Option β → Prop
  | none => final.heap = maskHeap source (∅ : Finset (Fin n)) ∧ final.stack = rest ∧ final.halted = true
  | some value => (∃ chosen, final.heap = maskHeap source chosen ∧ query chosen = some value) ∧
      (∃ saved, final.stack = saved ++ rest) ∧ final.pc = word width found ∧ final.halted = false

/-- A supplied callback is composed with the actual initialized core. Capacity
is clamped before word encoding, preserving the complete semantic search. -/
theorem from_mask (program : Program width 8) (source : Array (Word width))
    (query : Finset (Fin n) → Option β) (entry call found Q S capacity : Nat)
    (callback : Callback program source query entry call found Q S)
    (present : SharedRootRead.BlockAt program entry (SupportTraversal.code width entry n source.size call))
    (room : entry + 36 < 2 ^ width) (limitFits : n < 2 ^ width)
    (heapFits : source.size + n < 2 ^ width) (rest output : List (Word width)) :
    ∃ final ticks peak, Execution program (initial n capacity entry source rest output) final ticks peak ∧
      ticks ≤ (Q + 50) * leaves n capacity + 6 ∧
      peak ≤ source.size + 3 * n + S + rest.length + output.length + 11 ∧
      final.output = output ∧ Outcome source query found rest final
        (search (fun xs : List (Fin n) => query xs.toFinset) capacity (List.finRange n) []).result := by
  let state := initial n capacity entry source rest output
  obtain ⟨searched, ticks, peak, trace, time, space, out, active, result⟩ :=
    SupportSearch.execution program source query entry call found Q S callback present room limitFits heapFits
      n 0 (min capacity n) [] state (by omega) (by simp [Prefix]) rfl rfl rfl
      (by simp [state, initial]) (by simp [state, initial]) (by omega)
  have meaning : (search (fun xs : List (Fin n) => query xs.toFinset) (min capacity n)
      (ids 0 n (by omega)) []).result =
      (search (fun xs : List (Fin n) => query xs.toFinset) capacity (List.finRange n) []).result := by
    rw [ids_all]
    simpa only [List.length_finRange] using congrArg Run.result
      (search_clamp (fun xs : List (Fin n) => query xs.toFinset) capacity (List.finRange n) [])
  rw [fullCalls_eq, leaves_clamp] at time
  rw [meaning] at result
  have startLive := initial_live n capacity entry source rest output
  change state.liveWords = _ at startLive
  cases answer : (search (fun xs : List (Fin n) => query xs.toFinset) capacity (List.finRange n) []).result with
  | some value =>
      have good : Result source query entry found state searched (some value) := by
        simpa only [answer] using result
      obtain ⟨heap, ⟨saved, stack⟩, pc⟩ := good
      refine ⟨searched, ticks, peak, trace, by omega, by omega, out, heap, ?_, pc, active⟩
      exact ⟨saved ++ [word width n, word width 0], by
        simpa only [state, initial, List.append_assoc, List.cons_append, List.nil_append] using stack⟩
  | none =>
      have failed : Result source query entry found state searched none := by
        simpa only [answer] using result
      obtain ⟨heap, stack, pc⟩ := failed
      obtain ⟨_, _, returnAt, _, haltAt⟩ := SupportTraversal.blocks program entry n source.size call present
      obtain ⟨returned, rt, rh, rs, ro, rp, rr, rl⟩ :=
        SupportTraversal.exhausted_execution program searched (SupportTraversal.backtrack entry) n source.size
          (SupportTraversal.backtrack entry) (SupportTraversal.done entry) rest pc active stack limitFits
          (by unfold SupportTraversal.backtrack; omega) returnAt
      obtain ⟨final, ft, halted, fh, fs, fo⟩ :=
        EnumerationSteps.halt_execution program returned (SupportTraversal.done entry) rp rr
          (by unfold SupportTraversal.done; omega) haltAt
      have searchedLive : searched.liveWords = state.liveWords := by
        simp only [State.liveWords, heap, stack, out]
      refine ⟨final, ticks + 5 + 1, max peak (max searched.liveWords returned.liveWords),
        by simpa only [Nat.add_assoc] using trace.append (rt.append ft),
        by omega, by omega, fo.trans (ro.trans out), fh.trans (rh.trans heap), fs.trans rs, halted⟩

/-- The full callback family has B_k(n) leaves, with k kept as a parameter. -/
theorem support_bound (n k Q : Nat) :
    (Q + 50) * leaves n (k + 1) + 6 =
      (Q + 50) * Controller.Extensions.BoundedAnd.supportCount n k + 6 := by
  rw [leaves_eq_supportCount]

/-- Saturating the positional mask enumerates the selector functions. -/
theorem selector_bound (n k Q : Nat) (bound : n ≤ k) :
    (Q + 50) * leaves n n + 6 ≤ (Q + 50) * 2 ^ k + 6 := by
  rw [leaves_saturated n n le_rfl]
  exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) bound)) _

/-- The original healthy-zero support search is the exact consumer of the
fetched iterator, once its candidate evaluator supplies the callback contract. -/
theorem support_scan (program : Program width 8) (source : Array (Word width))
    (graph : Controller.Decoder.DAG n) (k b : Nat) (target : Controller.Channel n)
    (healthy : Fin graph.nodeCount → Bool) (entry call found Q S : Nat)
    (callback : Callback program source
      (Controller.Extensions.BoundedAnd.supportQuery graph b target healthy) entry call found Q S)
    (present : SharedRootRead.BlockAt program entry (SupportTraversal.code width entry n source.size call))
    (room : entry + 36 < 2 ^ width) (limitFits : n < 2 ^ width)
    (heapFits : source.size + n < 2 ^ width) (rest output : List (Word width)) :
    ∃ final ticks peak, Execution program (initial n (k + 1) entry source rest output) final ticks peak ∧
      ticks ≤ (Q + 50) * Controller.Extensions.BoundedAnd.supportCount n k + 6 ∧
      peak ≤ source.size + 3 * n + S + rest.length + output.length + 11 ∧
      final.output = output ∧ Outcome source
        (Controller.Extensions.BoundedAnd.supportQuery graph b target healthy) found rest final
        (SupportStream.scanSupports graph k b target healthy) := by
  obtain ⟨final, ticks, peak, trace, time, space, out, result⟩ :=
    from_mask program source (Controller.Extensions.BoundedAnd.supportQuery graph b target healthy)
      entry call found Q S (k + 1) callback present room limitFits heapFits rest output
  rw [support_bound] at time
  exact ⟨final, ticks, peak, trace, time, space, out, result⟩

/-- A two-instruction quiet callback instantiates the contract for exhaustive
traversal without successful queries. -/
theorem rejecting_callback (program : Program width 8) (source : Array (Word width))
    (entry call found : Nat) (room : call + 2 < 2 ^ width)
    (present : SharedRootRead.BlockAt program call
      (SupportBranch.jump width (SupportTraversal.backtrack entry))) :
    Callback program source (fun _ : Finset (Fin n) => (none : Option (Finset (Fin n))))
      entry call found 2 0 := by
  intro chosen state _ position running
  obtain ⟨final, trace, pc, heap, stack, output, active, _⟩ :=
    EnumerationSteps.jump_execution program state call (SupportTraversal.backtrack entry) position running room
      (by simpa [SupportBranch.jump] using present 0 (by simp [SupportBranch.jump]))
      (by simpa [SupportBranch.jump] using present 1 (by simp [SupportBranch.jump]))
  exact ⟨final, 2, state.liveWords, trace, le_rfl, by omega, heap, stack, output, active, pc⟩

def memberCode (width base backtrack index : Nat) : List (Instruction width 8) :=
  [.constant 3 (word width index)] ++ SupportTraversal.readCode width base backtrack

@[simp] theorem memberCode_length : (memberCode width base backtrack index).length = 5 := rfl

/-- A successful callback returns the actual retained mask when one chosen
channel is present. This demonstrates both exits of the callback contract. -/
theorem member_callback (program : Program width 8) (source : Array (Word width))
    (entry call : Nat) (index : Fin n) (room : call + 5 < 2 ^ width)
    (heapFits : source.size + n < 2 ^ width)
    (present : SharedRootRead.BlockAt program call
      (memberCode width source.size (SupportTraversal.backtrack entry) index.val)) :
    Callback program source (fun chosen => if index ∈ chosen then some chosen else none)
      entry call (call + 5) 5 0 := by
  intro chosen state stored position running
  obtain ⟨loaded, t1, p1, v1, h1, st1, o1, r1, _⟩ :=
    SharedEvaluationReclaim.constant_execution program call index.val 3 state position running (by omega)
      (by
        have first := present 0 (by simp)
        change program[call + 0]? = some (.constant 3 (word width index.val)) at first
        simpa only [Nat.add_zero] using first)
  have afterAt := Controller.Cost.SharedDetectorAssembly.block_right program call
    [.constant 3 (word width index.val)] _ present
  obtain ⟨final, t2, h2, st2, o2, p2, r2, _⟩ :=
    SupportTraversal.read_execution program loaded (call + 1) source.size
      (SupportTraversal.backtrack entry) index.val (decide (index ∈ chosen)) p1 r1 v1
      (by rw [h1, stored, maskHeap_size]; exact Nat.add_lt_add_left index.isLt _)
      (by simpa only [h1, stored, maskHeap_size] using heapFits)
      (by simpa only [h1, stored] using maskHeap_cell source chosen index) (by omega) afterAt
  have live : loaded.liveWords = state.liveWords := by simp only [State.liveWords, h1, st1, o1]
  refine ⟨final, 5, state.liveWords, ?_, le_rfl, by omega,
    h2.trans h1, st2.trans st1, o2.trans o1, r2, ?_⟩
  · simpa only [live, Nat.max_self, Nat.reduceAdd] using t1.append t2
  · by_cases member : index ∈ chosen <;> simpa [member, Nat.add_assoc] using p2

def ReturnedOutcome (source : Array (Word width)) (query : Finset (Fin n) → Option β)
    (entry found : Nat) (rest : List (Word width)) (final : State width 8) : Option β → Prop
  | none => final.heap = maskHeap source (∅ : Finset (Fin n)) ∧ final.stack = rest ∧
      final.pc = word width (SupportTraversal.done entry) ∧ final.halted = false
  | some value => Outcome source query found rest final (some value)

/-- Exhaustion returns to the core's caller boundary, so another output query
can reuse the same traversal and storage without restarting a halted machine. -/
theorem returning_from_state (program : Program width 8) (source : Array (Word width))
    (query : Finset (Fin n) → Option β) (entry call found Q S capacity : Nat)
    (ending : Instruction width 8) (callback : Callback program source query entry call found Q S)
    (present : SharedRootRead.BlockAt program entry (SupportTraversal.endingCode width entry n source.size call ending))
    (room : entry+36 < 2^width) (limitFits : n < 2^width)
    (heapFits : source.size+n < 2^width) (rest : List (Word width)) (state : State width 8)
    (position : state.pc = word width entry) (running : state.halted = false)
    (heapStored : state.heap = maskHeap source (∅ : Finset (Fin n)))
    (callerSaved : state.stack = word width n :: word width 0 :: rest)
    (cursorReg : state.reg 3 = word width 0)
    (capacityReg : state.reg 5 = word width (min capacity n)) :
    ∃ final ticks peak, Execution program state final ticks peak ∧
      ticks ≤ (Q+50)*leaves n capacity+5 ∧
      peak ≤ source.size+3*n+S+rest.length+state.output.length+11 ∧ final.output = state.output ∧
      ReturnedOutcome source query entry found rest final
        (search (fun chosen : List (Fin n) => query chosen.toFinset) capacity (List.finRange n) []).result := by
  obtain ⟨searched, ticks, peak, trace, time, space, out, active, result⟩ :=
    SupportSearch.execution program source query entry call found Q S callback present room limitFits heapFits
      n 0 (min capacity n) [] state (by omega) (by simp [Prefix]) position running
      (by simpa only [List.toFinset_nil] using heapStored) cursorReg capacityReg (by omega)
  have meaning : (search (fun chosen : List (Fin n) => query chosen.toFinset) (min capacity n)
      (ids 0 n (by omega)) []).result =
      (search (fun chosen : List (Fin n) => query chosen.toFinset) capacity (List.finRange n) []).result := by
    rw [ids_all]
    simpa only [List.length_finRange] using congrArg Run.result
      (search_clamp (fun chosen : List (Fin n) => query chosen.toFinset) capacity (List.finRange n) [])
  rw [fullCalls_eq, leaves_clamp] at time
  rw [meaning] at result
  have startLive : state.liveWords = source.size+n+rest.length+state.output.length+11 := by
    simp only [State.liveWords, heapStored, maskHeap_size, callerSaved, List.length_cons]; omega
  cases answer : (search (fun chosen : List (Fin n) => query chosen.toFinset) capacity (List.finRange n) []).result with
  | some value =>
    have good : Result source query entry found state searched (some value) := by simpa only [answer] using result
    obtain ⟨heap, ⟨saved, stack⟩, pc⟩ := good
    refine ⟨searched, ticks, peak, trace, by omega, by omega, out, heap, ?_, pc, active⟩
    exact ⟨saved++[word width n,word width 0], by
      simpa only [callerSaved, List.append_assoc, List.cons_append, List.nil_append] using stack⟩
  | none =>
    have failed : Result source query entry found state searched none := by simpa only [answer] using result
    obtain ⟨heap, stack, pc⟩ := failed
    obtain ⟨_, _, returnAt, _, _⟩ := SupportTraversal.ending_blocks program entry n source.size call ending present
    obtain ⟨final, last, fh, fs, fo, fp, fr, fl⟩ :=
      SupportTraversal.exhausted_execution program searched (SupportTraversal.backtrack entry) n source.size
        (SupportTraversal.backtrack entry) (SupportTraversal.done entry) rest pc active
        (stack.trans callerSaved) limitFits
        (by unfold SupportTraversal.backtrack; omega) returnAt
    have live : searched.liveWords = state.liveWords := by simp only [State.liveWords, heap, stack, out]
    refine ⟨final, ticks+5, max peak searched.liveWords, trace.append last, by omega, by omega,
      fo.trans out, fh.trans (heap.trans heapStored), fs, fp, fr⟩

theorem returning_from_mask (program : Program width 8) (source : Array (Word width))
    (query : Finset (Fin n) → Option β) (entry call found Q S capacity : Nat)
    (ending : Instruction width 8) (callback : Callback program source query entry call found Q S)
    (present : SharedRootRead.BlockAt program entry (SupportTraversal.endingCode width entry n source.size call ending))
    (room : entry+36 < 2^width) (limitFits : n < 2^width)
    (heapFits : source.size+n < 2^width) (rest output : List (Word width)) :
    ∃ final ticks peak, Execution program (initial n capacity entry source rest output) final ticks peak ∧
      ticks ≤ (Q+50)*leaves n capacity+5 ∧
      peak ≤ source.size+3*n+S+rest.length+output.length+11 ∧ final.output = output ∧
      ReturnedOutcome source query entry found rest final
        (search (fun chosen : List (Fin n) => query chosen.toFinset) capacity (List.finRange n) []).result := by
  exact returning_from_state program source query entry call found Q S capacity ending callback present
    room limitFits heapFits rest (initial n capacity entry source rest output) rfl rfl rfl rfl
    (by simp [initial]) (by simp [initial])

end Controller.Extensions.SupportSearchRun
