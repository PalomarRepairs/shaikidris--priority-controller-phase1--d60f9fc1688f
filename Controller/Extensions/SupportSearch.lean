module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Extensions.SupportTraversal
public import Controller.Extensions.SupportStream
public import Controller.Cost.SharedChannelStore

@[expose] public section

/-! The bounded-subset core refines the include-first semantic search. A failed
subtree restores its incoming mask and stack; its sibling reuses that storage.
The callback contract accounts for its own fetched execution and scratch. -/
namespace Controller.Extensions.SupportSearch
open Controller.Cost Controller.Cost.ForestInputStored
open Controller.Extensions.SupportStream

def maskHeap (source : Array (Word width)) (chosen : Finset (Fin n)) : Array (Word width) :=
  withValues source (fun i => decide (i ∈ chosen))

@[simp] theorem maskHeap_size (source : Array (Word width)) (chosen : Finset (Fin n)) :
    (maskHeap source chosen).size = source.size + n := by simp [maskHeap]

theorem maskHeap_cell (source : Array (Word width)) (chosen : Finset (Fin n)) (i : Fin n) :
    (maskHeap source chosen)[source.size + i.val]'(by simp) =
      boolWord width (decide (i ∈ chosen)) := value_cell _ _ _

theorem maskHeap_insert (source : Array (Word width)) (chosen : Finset (Fin n)) (i : Fin n) :
    (maskHeap source chosen).set (source.size + i.val) (boolWord width true)
      (by simp) = maskHeap source (insert i chosen) := by
  unfold maskHeap
  rw [SharedChannelStore.stored_update]
  congr 1
  funext j
  by_cases same : j = i <;> simp [same]

theorem maskHeap_clear (source : Array (Word width)) (chosen : Finset (Fin n)) (i : Fin n)
    (absent : i ∉ chosen) :
    (maskHeap source chosen).set (source.size + i.val) (boolWord width false)
      (by simp) = maskHeap source chosen := by
  unfold maskHeap
  rw [SharedChannelStore.stored_update]
  congr 1
  funext j
  by_cases same : j = i <;> simp [same, absent]

def ids (cursor count : Nat) (room : cursor + count ≤ n) : List (Fin n) :=
  List.ofFn fun i : Fin count => ⟨cursor + i.val, by have := i.isLt; omega⟩

@[simp] theorem ids_length (room : cursor + count ≤ n) : (ids cursor count room).length = count := by
  simp [ids]

@[simp] theorem ids_zero (room : cursor + 0 ≤ n) : ids cursor 0 room = [] := rfl

theorem ids_succ (room : cursor + (count + 1) ≤ n) :
    ids cursor (count + 1) room =
      ⟨cursor, by omega⟩ :: ids (cursor + 1) count (by omega) := by
  simp only [ids, List.ofFn_succ]
  congr 1
  apply congrArg List.ofFn
  funext i
  apply Fin.ext
  simp; omega

def Prefix (cursor : Nat) (chosen : List (Fin n)) : Prop := ∀ i ∈ chosen, i.val < cursor

theorem prefix_absent (chosen : List (Fin n)) (bounded : Prefix cursor chosen)
    (i : Fin n) (indexEq : i.val = cursor) : i ∉ chosen.toFinset := by
  intro member
  have less := bounded i (List.mem_toFinset.mp member)
  omega

theorem prefix_cons (chosen : List (Fin n)) (bounded : Prefix cursor chosen)
    (i : Fin n) (indexEq : i.val = cursor) : Prefix (cursor + 1) (i :: chosen) := by
  intro j member
  rcases List.mem_cons.mp member with same | old
  · subst j; omega
  · have := bounded j old; omega

/-- The callback executes on the actual mask and returns quietly to the
backtrack label, or transfers to the successful continuation. It may clobber
registers: parent cursor/capacity are recovered from the two-word frames. -/
def Callback (program : Program width 8) (source : Array (Word width))
    (query : Finset (Fin n) → Option β) (entry call found Q S : Nat) : Prop :=
  ∀ chosen (state : State width 8), state.heap = maskHeap source chosen →
    state.pc = word width call → state.halted = false →
    ∃ final ticks peak, Execution program state final ticks peak ∧ ticks ≤ Q ∧
      peak ≤ state.liveWords + S ∧ final.heap = state.heap ∧ final.stack = state.stack ∧
      final.output = state.output ∧ final.halted = false ∧
      final.pc = word width (if (query chosen).isSome then found else SupportTraversal.backtrack entry)

/-- Failed search restores the exact incoming allocation. Successful search
retains a concrete queried mask and a stack suffix for the caller. -/
def Result (source : Array (Word width)) (query : Finset (Fin n) → Option β)
    (entry found : Nat) (before after : State width 8) : Option β → Prop
  | none => after.heap = before.heap ∧ after.stack = before.stack ∧
      after.pc = word width (SupportTraversal.backtrack entry)
  | some value => (∃ chosen, after.heap = maskHeap source chosen ∧ query chosen = some value) ∧
      (∃ saved, after.stack = saved ++ before.stack) ∧ after.pc = word width found

theorem some_frame (source : Array (Word width)) (query : Finset (Fin n) → Option β)
    (entry found : Nat) (before middle final : State width 8) (value : β)
    (result : Result source query entry found middle final (some value))
    (saved : List (Word width)) (frame : middle.stack = saved ++ before.stack) :
    Result source query entry found before final (some value) := by
  obtain ⟨heap, ⟨extra, stack⟩, pc⟩ := result
  refine ⟨heap, ⟨extra ++ saved, ?_⟩, pc⟩
  rw [stack, frame, List.append_assoc]

theorem maskHeap_erase (source : Array (Word width)) (chosen : Finset (Fin n)) (i : Fin n) :
    (maskHeap source chosen).set (source.size + i.val) (boolWord width false)
      (by simp) = maskHeap source (chosen.erase i) := by
  unfold maskHeap
  rw [SharedChannelStore.stored_update]
  congr 1
  funext j
  by_cases same : j = i <;> simp [same]

theorem leaf_execution {ending : Instruction width 8} (program : Program width 8) (source : Array (Word width))
    (query : Finset (Fin n) → Option β) (entry call found Q S : Nat)
    (callback : Callback program source query entry call found Q S)
    (present : SharedRootRead.BlockAt program entry (SupportTraversal.endingCode width entry n source.size call ending))
    (room : entry + 36 < 2 ^ width) (limitFits : n < 2 ^ width)
    (state : State width 8) (cursor capacity : Nat) (chosen : Finset (Fin n))
    (position : state.pc = word width entry) (running : state.halted = false)
    (heapStored : state.heap = maskHeap source chosen)
    (cursorReg : state.reg 3 = word width cursor) (capacityReg : state.reg 5 = word width capacity)
    (cursorBound : cursor ≤ n) (capacityFits : capacity < 2 ^ width)
    (leaf : capacity = 0 ∨ cursor = n) :
    ∃ final ticks peak, Execution program state final ticks peak ∧ ticks + 44 ≤ Q + 50 ∧
      peak ≤ state.liveWords + S ∧ final.output = state.output ∧ final.halted = false ∧
      Result source query entry found state final (query chosen) := by
  obtain ⟨dispatchAt, _, _, _, _⟩ := SupportTraversal.ending_blocks program entry n source.size call ending present
  obtain ⟨dispatched, dt, dispatchTrace, time, dh, ds, dout, dp, dr, df⟩ :=
    SupportBranch.dispatch_execution program state entry n call cursor capacity position running cursorReg capacityReg
      (by omega) capacityFits limitFits (by omega) dispatchAt
  have atCall : dispatched.pc = word width call := by simpa only [ite_eq_left leaf] using dp
  obtain ⟨final, ct, cp, callbackTrace, ctime, cspace, ch, cs, co, cr, pc⟩ :=
    callback chosen dispatched (dh.trans heapStored) atCall dr
  have live : dispatched.liveWords = state.liveWords := by simp only [State.liveWords, dh, ds, dout]
  refine ⟨final, dt + ct, max state.liveWords cp, dispatchTrace.append callbackTrace,
    by omega, by omega, co.trans dout, cr, ?_⟩
  cases answer : query chosen with
  | none => exact ⟨ch.trans dh, cs.trans ds, by simpa [answer] using pc⟩
  | some value => exact ⟨⟨chosen, ch.trans (dh.trans heapStored), answer⟩,
      ⟨[], by simpa using cs.trans ds⟩, by simpa [answer] using pc⟩

set_option maxHeartbeats 1600000 in
/-- The complete fetched recursion refines the semantic search, including
early success and exact restoration after failure. Callback scratch is reused
between siblings; only two words per current recursion level remain live. -/
theorem execution {ending : Instruction width 8} (program : Program width 8) (source : Array (Word width))
    (query : Finset (Fin n) → Option β) (entry call found Q S : Nat)
    (callback : Callback program source query entry call found Q S)
    (present : SharedRootRead.BlockAt program entry (SupportTraversal.endingCode width entry n source.size call ending))
    (room : entry + 36 < 2 ^ width) (limitFits : n < 2 ^ width)
    (heapFits : source.size + n < 2 ^ width)
    (remaining cursor capacity : Nat) (chosen : List (Fin n)) (state : State width 8)
    (depth : cursor + remaining = n) (bounded : Prefix cursor chosen)
    (position : state.pc = word width entry) (running : state.halted = false)
    (heapStored : state.heap = maskHeap source chosen.toFinset)
    (cursorReg : state.reg 3 = word width cursor) (capacityReg : state.reg 5 = word width capacity)
    (capacityFits : capacity < 2 ^ width) :
    ∃ final ticks peak, Execution program state final ticks peak ∧
      ticks + 44 ≤ (Q + 50) * fullCalls remaining capacity ∧
      peak ≤ state.liveWords + 2 * remaining + S ∧ final.output = state.output ∧ final.halted = false ∧
      Result source query entry found state final
        (search (fun xs : List (Fin n) => query xs.toFinset) capacity
          (ids cursor remaining (by omega)) chosen).result := by
  induction remaining generalizing cursor capacity chosen state with
  | zero =>
      obtain ⟨final, ticks, peak, trace, time, space, output, active, result⟩ :=
        leaf_execution program source query entry call found Q S callback present room limitFits
          state cursor capacity chosen.toFinset position running heapStored cursorReg capacityReg
          (by omega) capacityFits (Or.inr (by omega))
      refine ⟨final, ticks, peak, trace, ?_, by omega, output, active, ?_⟩
      · cases capacity <;> simpa only [fullCalls, Nat.mul_one] using time
      · cases capacity <;> simpa only [ids_zero, search] using result
  | succ remaining ih =>
      cases capacity with
      | zero =>
          obtain ⟨final, ticks, peak, trace, time, space, output, active, result⟩ :=
            leaf_execution program source query entry call found Q S callback present room limitFits
              state cursor 0 chosen.toFinset position running heapStored cursorReg capacityReg
              (by omega) capacityFits (Or.inl rfl)
          exact ⟨final, ticks, peak, trace, by simpa only [fullCalls, Nat.mul_one] using time,
            by omega, output, active, by simpa only [search] using result⟩
      | succ capacity =>
          let head : Fin n := ⟨cursor, by omega⟩
          let tail := ids (cursor + 1) remaining (show cursor + 1 + remaining ≤ n by omega)
          let first := search (fun xs : List (Fin n) => query xs.toFinset) capacity tail (head :: chosen)
          let second := search (fun xs : List (Fin n) => query xs.toFinset) (capacity + 1) tail chosen
          have tree : (search (fun xs : List (Fin n) => query xs.toFinset) (capacity + 1)
              (ids cursor (remaining + 1) (by omega)) chosen).result =
              match first.result with | some value => some value | none => second.result := by
            simp only [ids_succ, search]
            split <;> simp_all [first, second, tail, head]
          have absent : head ∉ chosen.toFinset := prefix_absent chosen bounded head rfl
          obtain ⟨dispatchAt, includeAt, returnAt, excludeAt, _⟩ :=
            SupportTraversal.ending_blocks program entry n source.size call ending present
          obtain ⟨dispatched, dt, dtrace, dtime, dh, ds, dout, dp, dr, df⟩ :=
            SupportBranch.dispatch_execution program state entry n call cursor (capacity + 1)
              position running cursorReg capacityReg (by omega) capacityFits limitFits (by omega) dispatchAt
          have includePC : dispatched.pc = word width (entry + 4) := by
            simpa only [ite_eq_right (by omega : ¬(capacity + 1 = 0 ∨ cursor = n))] using dp
          have dl : dispatched.liveWords = state.liveWords := by simp only [State.liveWords, dh, ds, dout]
          obtain ⟨included, itrace, ihp, ist, iout, ip, ir, ic, ib, _, il⟩ :=
            SupportBranch.child_execution program dispatched (entry + 4) source.size entry cursor capacity true
              includePC dr ((df 3 (by decide)).trans cursorReg) ((df 5 (by decide)).trans capacityReg)
              (by omega) capacityFits (by rw [dh, heapStored, maskHeap_size]; omega)
              (by simpa only [dh, heapStored, maskHeap_size] using heapFits) (by simp; omega) includeAt
          have includedHeap : included.heap = maskHeap source (head :: chosen).toFinset := by
            calc
              included.heap = (maskHeap source chosen.toFinset).set (source.size + head.val)
                  (boolWord width true) (by simp) := by simpa only [dh, heapStored] using ihp
              _ = maskHeap source (head :: chosen).toFinset := by
                simpa only [List.toFinset_cons] using maskHeap_insert source chosen.toFinset head
          have includedStack : included.stack = word width cursor :: word width (capacity + 1) :: state.stack := by
            simpa only [ds, ite_eq_left rfl, ite_true] using ist
          have includedLive : included.liveWords = state.liveWords + 2 := by omega
          obtain ⟨left, lt, lp, ltrace, ltime, lspace, lout, lr, lresult⟩ :=
            ih (cursor := cursor + 1) (capacity := capacity) (chosen := head :: chosen) (state := included)
              (depth := by omega) (bounded := prefix_cons chosen bounded head rfl)
              (position := ip) (running := ir) (heapStored := includedHeap) (cursorReg := ic)
              (capacityReg := ib) (capacityFits := by omega)
          change Result source query entry found included left first.result at lresult
          cases firstAnswer : first.result with
          | some value =>
              have good : Result source query entry found included left (some value) := by
                simpa only [firstAnswer] using lresult
              have secondPositive : 0 < fullCalls remaining (capacity + 1) := by
                rw [fullCalls_eq]; exact leaves_positive _ _
              have budget : 50 ≤ (Q + 50) * fullCalls remaining (capacity + 1) := by nlinarith
              refine ⟨left, dt + 12 + lt, max state.liveWords (max (dispatched.liveWords + 2) lp),
                ?_, ?_, ?_, lout.trans (iout.trans dout), lr, ?_⟩
              · simpa only [SupportBranch.childCode_length, ite_eq_left rfl, ite_true, Nat.reduceAdd, Nat.add_assoc] using
                  dtrace.append (itrace.append ltrace)
              · simp only [fullCalls, Nat.mul_add]; omega
              · omega
              · rw [tree, firstAnswer]
                exact some_frame source query entry found state included left value good
                  [word width cursor, word width (capacity + 1)] includedStack
          | none =>
              have failed : Result source query entry found included left none := by
                simpa only [firstAnswer] using lresult
              obtain ⟨leftHeap, leftStack, leftPC⟩ := failed
              have leftLive : left.liveWords = state.liveWords + 2 := by
                have same : left.liveWords = included.liveWords := by
                  simp only [State.liveWords, leftHeap, leftStack, lout]
                exact same.trans includedLive
              obtain ⟨restored, rtrace, rh, rst, rout, rp, rr, rc, rb, _, rl⟩ :=
                SupportTraversal.return_execution program left (SupportTraversal.backtrack entry) n source.size
                  (SupportTraversal.backtrack entry) (SupportTraversal.done entry) cursor (capacity + 1)
                  state.stack true leftPC lr (leftStack.trans includedStack) (by omega) limitFits
                  (by rw [leftHeap, includedHeap, maskHeap_size]; omega)
                  (by simpa only [leftHeap, includedHeap, maskHeap_size] using heapFits)
                  (by simpa only [leftHeap, includedHeap, List.toFinset_cons, head,
                    Finset.mem_insert_self, decide_true] using
                    maskHeap_cell source (insert head chosen.toFinset) head)
                  (by unfold SupportTraversal.backtrack; omega) returnAt
              have restoredPC : restored.pc = word width (entry + 25) := by
                simpa only [ite_eq_left rfl, ite_true, SupportTraversal.backtrack, Nat.add_assoc, Nat.reduceAdd] using rp
              have restoredHeap : restored.heap = maskHeap source (insert head chosen.toFinset) := by
                simpa only [List.toFinset_cons] using rh.trans (leftHeap.trans includedHeap)
              have restoredLive : restored.liveWords = state.liveWords := by omega
              obtain ⟨excluded, etrace, ehp, est, eout, ep, er, ec, eb, _, el⟩ :=
                SupportBranch.child_execution program restored (entry + 25) source.size entry cursor (capacity + 1) false
                  restoredPC rr rc (by simpa only [Bool.false_eq_true, ite_false, Nat.add_zero] using rb)
                  (by omega) (by simpa only [Bool.false_eq_true, ite_false, Nat.add_zero] using capacityFits)
                  (by rw [restoredHeap, maskHeap_size]; omega)
                  (by simpa only [restoredHeap, maskHeap_size] using heapFits) (by simp; omega) excludeAt
              have excludedHeap : excluded.heap = maskHeap source chosen.toFinset := by
                calc
                  excluded.heap = (maskHeap source (insert head chosen.toFinset)).set (source.size + head.val)
                      (boolWord width false) (by simp) := by simpa only [restoredHeap] using ehp
                  _ = maskHeap source chosen.toFinset := by
                    simpa only [Finset.erase_insert absent] using maskHeap_erase source (insert head chosen.toFinset) head
              have excludedStack : excluded.stack = word width cursor :: word width (capacity + 1) :: state.stack := by
                simpa only [rst, Bool.false_eq_true, ite_false, Nat.add_zero] using est
              have excludedLive : excluded.liveWords = state.liveWords + 2 := by omega
              obtain ⟨right, rt, sp, strace, stime, sspace, sout, sr, sresult⟩ :=
                ih (cursor := cursor + 1) (capacity := capacity + 1) (chosen := chosen) (state := excluded)
                  (depth := by omega) (bounded := by intro i member; have := bounded i member; omega)
                  (position := ep) (running := er) (heapStored := excludedHeap) (cursorReg := ec)
                  (capacityReg := eb) (capacityFits := capacityFits)
              change Result source query entry found excluded right second.result at sresult
              have firstOutput : restored.output = state.output := rout.trans (lout.trans (iout.trans dout))
              cases secondAnswer : second.result with
              | some value =>
                  have good : Result source query entry found excluded right (some value) := by
                    simpa only [secondAnswer] using sresult
                  refine ⟨right, dt + 12 + lt + 9 + 10 + rt,
                    max state.liveWords (max (dispatched.liveWords + 2)
                      (max lp (max left.liveWords (max (restored.liveWords + 2) sp)))),
                    ?_,
                    ?_, ?_, sout.trans (eout.trans firstOutput), sr, ?_⟩
                  · simpa only [SupportBranch.childCode_length, ite_eq_left rfl, ite_true, Bool.false_eq_true,
                      ite_false, Nat.zero_add, ← Nat.add_assoc, Nat.reduceAdd] using
                      dtrace.append (itrace.append (ltrace.append (rtrace.append (etrace.append strace))))
                  · simp only [fullCalls, Nat.mul_add]; omega
                  · omega
                  · rw [tree, firstAnswer]
                    change Result source query entry found state right second.result
                    rw [secondAnswer]
                    exact some_frame source query entry found state excluded right value good
                      [word width cursor, word width (capacity + 1)] excludedStack
              | none =>
                  have failed : Result source query entry found excluded right none := by
                    simpa only [secondAnswer] using sresult
                  obtain ⟨rightHeap, rightStack, rightPC⟩ := failed
                  have rightLive : right.liveWords = state.liveWords + 2 := by
                    have same : right.liveWords = excluded.liveWords := by
                      simp only [State.liveWords, rightHeap, rightStack, sout]
                    exact same.trans excludedLive
                  obtain ⟨final, ftrace, fh, fst, fout, fp, fr, _, _, _, fl⟩ :=
                    SupportTraversal.return_execution program right (SupportTraversal.backtrack entry) n source.size
                      (SupportTraversal.backtrack entry) (SupportTraversal.done entry) cursor (capacity + 1)
                      state.stack false rightPC sr (rightStack.trans excludedStack) (by omega) limitFits
                      (by rw [rightHeap, excludedHeap, maskHeap_size]; omega)
                      (by simpa only [rightHeap, excludedHeap, maskHeap_size] using heapFits)
                      (by simpa only [rightHeap, excludedHeap, head, absent, decide_false] using
                        maskHeap_cell source chosen.toFinset head)
                      (by unfold SupportTraversal.backtrack; omega) returnAt
                  refine ⟨final, dt + 12 + lt + 9 + 10 + rt + 9,
                    max state.liveWords (max (dispatched.liveWords + 2)
                      (max lp (max left.liveWords (max (restored.liveWords + 2) (max sp right.liveWords))))),
                    ?_,
                    ?_, ?_, fout.trans (sout.trans (eout.trans firstOutput)), fr, ?_⟩
                  · simpa only [SupportBranch.childCode_length, ite_eq_left rfl, ite_true, Bool.false_eq_true,
                      ite_false, Nat.zero_add, ← Nat.add_assoc, Nat.reduceAdd] using
                      dtrace.append (itrace.append (ltrace.append (rtrace.append (etrace.append (strace.append ftrace)))))
                  · simp only [fullCalls, Nat.mul_add]; omega
                  · omega
                  · rw [tree, firstAnswer]
                    change Result source query entry found state final second.result
                    rw [secondAnswer]
                    exact ⟨fh.trans (rightHeap.trans (excludedHeap.trans heapStored.symm)), fst, fp⟩

end Controller.Extensions.SupportSearch
