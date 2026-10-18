module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.EnumerationRootQuery
public import Controller.Cost.SharedDetectorPrepared
public import Controller.Cost.ForestRootProjection

public import Mathlib.Tactic.FinCases

@[expose] public section

/-! The returning output scan used as the enumeration oracle. It is the shared detector's
output loop with three exits changed: an accepted candidate discards the remaining reference
tags and returns with register 4 = 1; a healthy-true output runs the quiet zero query and
either continues or joins that accept; exhaustion returns with register 4 = 0. No native lift,
no emission and no halt occur. -/
namespace Controller.Cost.EnumerationLoop
open Controller.Cost.GateProgram Controller.Cost.RawTransferLoops

theorem single (program : Program width 8) (state next : State width 8) (entry : Nat)
    (instruction : Instruction width 8) (position : state.pc = word width entry)
    (fits : entry < 2 ^ width) (present : program[entry]? = some instruction)
    (stepped : step instruction state = some next) :
    Execution program state next 1 (max state.liveWords next.liveWords) := by
  have transition : programStep program state = some next := by
    rw [fetched program state entry instruction position fits present]
    exact stepped
  simpa only [Nat.zero_add] using Execution.cons transition (Execution.refl next)

/-- Accept after a candidate: move the remaining-tag count to register 0, discard those tags,
set the decision and return. Placed at loop entry + 22. -/
def acceptCode (width entry ret : Nat) : List (Instruction width 8) :=
  [.copy 0 6, .constant 7 (word width (2 ^ width - 1)), .constant 6 (word width 0)] ++
    (ForestRootProjection.discardCode width (entry + 25) (entry + 29)).toList ++
    [.constant 4 (word width 1), .branchZero 0 (word width ret)]

@[simp] theorem acceptCode_length : (acceptCode width entry ret).length = 9 := by
  simp [acceptCode]

theorem accept_execution (program : Program width 8) (state : State width 8) (entry ret : Nat)
    (tags rest : List (Word width))
    (position : state.pc = word width (entry + 22)) (running : state.halted = false)
    (room : entry + 31 < 2 ^ width) (tagsFit : tags.length < 2 ^ width)
    (stack : state.stack = tags ++ rest) (count : state.reg 6 = word width tags.length)
    (present : SharedRootRead.BlockAt program (entry + 22) (acceptCode width entry ret)) :
    ∃ final ticks peak, Execution program state final ticks peak ∧ ticks = 4 * tags.length + 6 ∧
      peak ≤ state.liveWords ∧ final.heap = state.heap ∧ final.stack = rest ∧ final.output = state.output ∧
      final.pc = word width ret ∧ final.halted = false ∧ final.reg 4 = word width 1 := by
  have fetch : ∀ offset (valid : offset < 9), program[entry + 22 + offset]? = (acceptCode width entry ret)[offset]? :=
    fun offset valid => present offset (by simpa using valid)
  let s1 := state.advance.put 0 (state.reg 6)
  have step1 : step (.copy 0 6) state = some s1 := by simp [step, running, s1]
  have trace1 := single program state s1 (entry + 22) _ position (by omega)
    (by simpa [acceptCode] using fetch 0 (by decide)) step1
  have pc1 : s1.pc = word width (entry + 22 + 1) := by
    simpa [s1, State.put] using advance_position state position (by omega)
  obtain ⟨s2, t2, pc2, r2, h2, k2, o2, run2, f2⟩ :=
    SharedEvaluationReclaim.constant_execution program (entry + 22 + 1) (2 ^ width - 1) 7 s1 pc1 running (by omega)
      (by simpa [acceptCode, Nat.add_assoc] using fetch 1 (by decide))
  obtain ⟨s3, t3, pc3, r3, h3, k3, o3, run3, f3⟩ :=
    SharedEvaluationReclaim.constant_execution program (entry + 22 + 1 + 1) 0 6 s2 pc2 run2 (by omega)
      (by simpa [acceptCode, Nat.add_assoc] using fetch 2 (by decide))
  have discardAt : RawTransferLoops.CodeAt program (entry + 25) (ForestRootProjection.discardCode width (entry + 25) (entry + 29)) := by
    intro phase
    have found := fetch (3 + phase.val) (by have := phase.isLt; simp at this; omega)
    fin_cases phase <;> simpa [acceptCode, ForestRootProjection.discardCode, Nat.add_assoc] using found
  have s3Stack : s3.stack = tags ++ rest := by rw [k3, k2]; simp [s1, State.put, State.advance, stack]
  obtain ⟨s4, peak4, t4, space4, h4, k4, o4, pc4, run4, zero4, frame4⟩ :=
    ForestRootProjection.discard_execution program (entry + 25) (entry + 29) tags rest s3
      (by simpa [Nat.add_assoc] using pc3) run3 (by omega) s3Stack tagsFit
      (by rw [f3 0 (by decide), f2 0 (by decide)]; simpa [s1, State.put] using count)
      (by rw [f3 7 (by decide)]; exact r2) r3 discardAt
  obtain ⟨s5, t5, pc5, r5, h5, k5, o5, run5, f5⟩ :=
    SharedEvaluationReclaim.constant_execution program (entry + 29) 1 4 s4 pc4 run4 (by omega)
      (by simpa [acceptCode, ForestRootProjection.discardCode, Nat.add_assoc] using fetch 7 (by decide))
  let final : State width 8 := { s5.advance with pc := word width ret }
  have zero5 : (s5.reg 0).val = 0 := by rw [f5 0 (by decide), zero4]; simp [word]
  have step6 : step (.branchZero 0 (word width ret)) s5 = some final := by
    simp [step, run5, final, zero5]
  have trace6 := single program s5 final (entry + 29 + 1) _ pc5 (by omega)
    (by simpa [acceptCode, ForestRootProjection.discardCode, Nat.add_assoc] using fetch 8 (by decide)) step6
  have l1 : s1.liveWords = state.liveWords := rfl
  have l2 : s2.liveWords = state.liveWords := by simp only [State.liveWords, h2, k2, o2]; rfl
  have l3 : s3.liveWords = state.liveWords := by simp only [State.liveWords, h3, k3, o3] at l2 ⊢; exact l2
  have l4 : s4.liveWords ≤ peak4 := t4.final_storage_le
  have l5 : s5.liveWords = s4.liveWords := by simp only [State.liveWords, h5, k5, o5]
  have lf : final.liveWords = s5.liveWords := rfl
  have joined := trace1.append (t2.append (t3.append (t4.append (t5.append trace6))))
  refine ⟨final, _, _, joined, by omega, ?_, ?_, ?_, ?_, rfl, run5, ?_⟩
  · simp only [max_le_iff, l1, l2, l3, l5, lf]; omega
  · change s5.heap = state.heap; rw [h5, h4, h3, h2]; rfl
  · change s5.stack = rest; rw [k5, k4]
  · change s5.output = state.output; rw [o5, o4, o3, o2]; rfl
  · change s5.reg 4 = word width 1; exact r5

/-- After the quiet query: a failed query continues at the loop entry; a successful one drops
the two cursor words, loads the remaining-tag count and joins the accept. -/
def dispatchCode (width entry : Nat) : List (Instruction width 8) :=
  [.branchZero 4 (word width entry), .pop 0, .pop 6, .constant 0 (word width 0),
    .branchZero 0 (word width (entry + 22))]

@[simp] theorem dispatchCode_length : (dispatchCode width entry).length = 5 := rfl

theorem dispatch_failed (program : Program width 8) (state : State width 8) (at_ entry : Nat)
    (position : state.pc = word width at_) (running : state.halted = false) (room : at_ + 5 < 2 ^ width)
    (decision : state.reg 4 = word width 0)
    (present : SharedRootRead.BlockAt program at_ (dispatchCode width entry)) :
    ∃ final, Execution program state final 1 state.liveWords ∧ final.heap = state.heap ∧
      final.stack = state.stack ∧ final.output = state.output ∧ final.reg = state.reg ∧
      final.pc = word width entry ∧ final.halted = false := by
  let final : State width 8 := { state.advance with pc := word width entry }
  have stepped : step (.branchZero 4 (word width entry)) state = some final := by
    simp [step, running, final, decision, word]
  have trace := single program state final at_ _ position (by omega)
    (by simpa [dispatchCode] using present 0 (by simp)) stepped
  have live : final.liveWords = state.liveWords := rfl
  exact ⟨final, by simpa only [live, Nat.max_self] using trace, rfl, rfl, rfl, rfl, rfl, running⟩

theorem dispatch_accepted (program : Program width 8) (state : State width 8) (at_ entry : Nat)
    (first second : Word width) (rest : List (Word width))
    (position : state.pc = word width at_) (running : state.halted = false) (room : at_ + 5 < 2 ^ width)
    (decision : state.reg 4 = word width 1) (oneFits : 1 < 2 ^ width)
    (stack : state.stack = first :: second :: rest)
    (present : SharedRootRead.BlockAt program at_ (dispatchCode width entry)) :
    ∃ final peak, Execution program state final 5 peak ∧ peak ≤ state.liveWords ∧ final.heap = state.heap ∧
      final.stack = rest ∧ final.output = state.output ∧ final.reg 6 = second ∧
      final.pc = word width (entry + 22) ∧ final.halted = false := by
  have fetch : ∀ offset (valid : offset < 5), program[at_ + offset]? = (dispatchCode width entry)[offset]? :=
    fun offset valid => present offset (by simpa using valid)
  let s1 := state.advance
  have one : (state.reg 4).val ≠ 0 := by rw [decision]; simp [word, Nat.mod_eq_of_lt oneFits]
  have step1 : step (.branchZero 4 (word width entry)) state = some s1 := by simp [step, running, s1, one]
  have trace1 := single program state s1 at_ _ position (by omega) (by simpa [dispatchCode] using fetch 0 (by decide)) step1
  have pc1 : s1.pc = word width (at_ + 1) := advance_position state position (by omega)
  let s2 : State width 8 := { s1.advance.put 0 first with stack := second :: rest }
  have step2 : step (.pop 0) s1 = some s2 := by simp [step, running, s1, s2, stack, State.advance, State.put]
  have trace2 := single program s1 s2 (at_ + 1) _ pc1 (by omega) (by simpa [dispatchCode] using fetch 1 (by decide)) step2
  have pc2 : s2.pc = word width (at_ + 2) := by
    simpa [s2, State.put, Nat.add_assoc] using advance_position s1 pc1 (by omega)
  let s3 : State width 8 := { s2.advance.put 6 second with stack := rest }
  have step3 : step (.pop 6) s2 = some s3 := by simp [step, running, s1, s2, s3, State.advance, State.put]
  have trace3 := single program s2 s3 (at_ + 2) _ pc2 (by omega) (by simpa [dispatchCode] using fetch 2 (by decide)) step3
  have pc3 : s3.pc = word width (at_ + 2 + 1) := by
    simpa [s3, State.put] using advance_position s2 pc2 (by omega)
  obtain ⟨s4, t4, pc4, r4, h4, k4, o4, run4, f4⟩ :=
    SharedEvaluationReclaim.constant_execution program (at_ + 2 + 1) 0 0 s3 pc3 running (by omega)
      (by simpa [dispatchCode, Nat.add_assoc] using fetch 3 (by decide))
  let final : State width 8 := { s4.advance with pc := word width (entry + 22) }
  have zero4 : (s4.reg 0).val = 0 := by rw [r4]; simp [word]
  have step5 : step (.branchZero 0 (word width (entry + 22))) s4 = some final := by simp [step, run4, final, zero4]
  have trace5 := single program s4 final (at_ + 2 + 1 + 1) _ pc4 (by omega)
    (by simpa [dispatchCode, Nat.add_assoc] using fetch 4 (by decide)) step5
  have l1 : s1.liveWords = state.liveWords := rfl
  have l2 : s2.liveWords + 1 = state.liveWords := by simp [s2, s1, State.liveWords, State.advance, State.put, stack]; omega
  have l3 : s3.liveWords + 1 = s2.liveWords := by simp [s3, s2, s1, State.liveWords, State.advance, State.put]; omega
  have l4 : s4.liveWords = s3.liveWords := by simp only [State.liveWords, h4, k4, o4]
  have lf : final.liveWords = s4.liveWords := rfl
  have joined := trace1.append (trace2.append (trace3.append (t4.append trace5)))
  refine ⟨final, _, joined, ?_, ?_, ?_, ?_, ?_, rfl, run4⟩
  · simp only [max_le_iff, l1, lf, l4]; omega
  · change s4.heap = state.heap; rw [h4]; rfl
  · change s4.stack = rest; rw [k4]
  · change s4.output = state.output; rw [o4]; rfl
  · change s4.reg 6 = second; rw [f4 6 (by decide)]; simp [s3, State.put]

/-- Exhaustion returns the negative decision. -/
def exhaustedCode (width ret : Nat) : List (Instruction width 8) :=
  [.constant 4 (word width 0), .constant 0 (word width 0), .branchZero 0 (word width ret)]

@[simp] theorem exhaustedCode_length : (exhaustedCode width ret).length = 3 := rfl

theorem exhausted_execution (program : Program width 8) (state : State width 8) (at_ ret : Nat)
    (position : state.pc = word width at_) (running : state.halted = false) (room : at_ + 3 < 2 ^ width)
    (present : SharedRootRead.BlockAt program at_ (exhaustedCode width ret)) :
    ∃ final, Execution program state final 3 state.liveWords ∧ final.heap = state.heap ∧
      final.stack = state.stack ∧ final.output = state.output ∧ final.reg 4 = word width 0 ∧
      final.pc = word width ret ∧ final.halted = false := by
  have fetch : ∀ offset (valid : offset < 3), program[at_ + offset]? = (exhaustedCode width ret)[offset]? :=
    fun offset valid => present offset (by simpa using valid)
  obtain ⟨s1, t1, pc1, r1, h1, k1, o1, run1, f1⟩ :=
    SharedEvaluationReclaim.constant_execution program at_ 0 4 state position running (by omega)
      (by simpa [exhaustedCode] using fetch 0 (by decide))
  obtain ⟨s2, t2, pc2, r2, h2, k2, o2, run2, f2⟩ :=
    SharedEvaluationReclaim.constant_execution program (at_ + 1) 0 0 s1 pc1 run1 (by omega)
      (by simpa [exhaustedCode] using fetch 1 (by decide))
  let final : State width 8 := { s2.advance with pc := word width ret }
  have zero2 : (s2.reg 0).val = 0 := by rw [r2]; simp [word]
  have step3 : step (.branchZero 0 (word width ret)) s2 = some final := by simp [step, run2, final, zero2]
  have trace3 := single program s2 final (at_ + 1 + 1) _ pc2 (by omega)
    (by simpa [exhaustedCode, Nat.add_assoc] using fetch 2 (by decide)) step3
  have l1 : s1.liveWords = state.liveWords := by simp only [State.liveWords, h1, k1, o1]
  have l2 : s2.liveWords = state.liveWords := by simp only [State.liveWords, h2, k2, o2] at l1 ⊢; exact l1
  have lf : final.liveWords = s2.liveWords := rfl
  have joined := t1.append (t2.append trace3)
  rw [l1, l2, lf, l2, Nat.max_self, Nat.max_self] at joined
  refine ⟨final, by simpa only [Nat.max_self] using joined, ?_, ?_, ?_, ?_, rfl, run2⟩
  · change s2.heap = state.heap; rw [h2, h1]
  · change s2.stack = state.stack; rw [k2, k1]
  · change s2.output = state.output; rw [o2, o1]
  · change s2.reg 4 = word width 0; rw [f2 4 (by decide), r1]

section Layout
open Controller.Cost.ForestZeroDictionary Controller.Native Controller.Native.SourceController Controller.Decoder

def returnPoint (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels)) (heapSize coordinateBase slot entry : Nat)
    (root : Fin graph.nodeCount) (width : Nat) : Nat :=
  EnumerationRootQuery.returnEntry width parameters graph T F heapSize coordinateBase slot (entry + 49) root

/-- One resident copy of the returning output scan; `ret` is the caller's return address. -/
def code (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels)) (heap : Array (Word width))
    (layout : Layout (parameters.channels + graph.nodeCount) heap.size)
    (coordinateBase slot offset entry ret : Nat) (root : Fin graph.nodeCount) : List (Instruction width 8) :=
  (SharedRootTaggedCursor.code width parameters.channels entry
    (returnPoint parameters graph T F heap.size coordinateBase slot entry root width + 5)
    (entry + 37) (entry + 31)).toList ++
  (acceptCode width entry ret ++
  ((SharedRootResumeEntry.skipCode width layout.tableBase layout.inverseBase entry).toList ++
  ((SharedRootHealthyEntry.code width layout.tableBase layout.inverseBase offset slot).toList ++
  (EnumerationRootQuery.code parameters graph T F heap layout coordinateBase slot (entry + 49) root ++
  (dispatchCode width entry ++ exhaustedCode width ret)))))

theorem returnEntry_point (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels)) (heapSize coordinateBase slot entry width : Nat)
    (root currentRoot : Fin graph.nodeCount) :
    EnumerationRootQuery.returnEntry width parameters graph T F heapSize coordinateBase slot (entry + 49) root =
      returnPoint parameters graph T F heapSize coordinateBase slot entry currentRoot width := by
  unfold returnPoint EnumerationRootQuery.returnEntry
  rw [SharedQuerySourceCode.root_entry_irrel graph parameters.buses parameters.bridge.target T F
    coordinateBase slot (entry + 49) heapSize root currentRoot]

theorem query_end (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels)) (heap : Array (Word width))
    (layout : Layout (parameters.channels + graph.nodeCount) heap.size)
    (coordinateBase slot entry : Nat) (root : Fin graph.nodeCount) :
    entry + 49 + (EnumerationRootQuery.code parameters graph T F heap layout coordinateBase slot (entry + 49) root).length =
      returnPoint parameters graph T F heap.size coordinateBase slot entry root width :=
  EnumerationRootQuery.returnEntry_eq parameters graph T F heap layout coordinateBase slot (entry + 49) root

theorem code_length (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels)) (heap : Array (Word width))
    (layout : Layout (parameters.channels + graph.nodeCount) heap.size)
    (coordinateBase slot offset entry ret : Nat) (root : Fin graph.nodeCount) :
    entry + (code parameters graph T F heap layout coordinateBase slot offset entry ret root).length =
      returnPoint parameters graph T F heap.size coordinateBase slot entry root width + 8 := by
  have query := query_end parameters graph T F heap layout coordinateBase slot entry root
  simp only [code, List.length_append, Array.length_toList, SharedRootTaggedCursor.code_size, acceptCode_length,
    SharedRootResumeEntry.skipCode_size, SharedRootHealthyEntry.code_size, dispatchCode_length, exhaustedCode_length]
  omega

theorem code_length_bound (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels)) (heap : Array (Word width))
    (layout : Layout (parameters.channels + graph.nodeCount) heap.size)
    (coordinateBase slot offset entry ret : Nat) (root : Fin graph.nodeCount) :
    (code parameters graph T F heap layout coordinateBase slot offset entry ret root).length ≤
      410 * (graph.countedSize + 1) + 502 := by
  have bound := EnumerationRootQuery.code_length_bound parameters graph T F heap layout coordinateBase slot (entry + 49) root
  simp only [code, List.length_append, Array.length_toList, SharedRootTaggedCursor.code_size, acceptCode_length,
    SharedRootResumeEntry.skipCode_size, SharedRootHealthyEntry.code_size, dispatchCode_length, exhaustedCode_length]
  omega

theorem shared (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels)) (before after : Array (Word width))
    (leftLayout : Layout (parameters.channels + graph.nodeCount) before.size)
    (rightLayout : Layout (parameters.channels + graph.nodeCount) after.size)
    (coordinateBase slot offset entry ret : Nat) (left right : Fin graph.nodeCount)
    (sameSize : before.size = after.size) (sameTable : leftLayout.tableBase = rightLayout.tableBase)
    (sameInverse : leftLayout.inverseBase = rightLayout.inverseBase) :
    code parameters graph T F before leftLayout coordinateBase slot offset entry ret left =
      code parameters graph T F after rightLayout coordinateBase slot offset entry ret right := by
  have sameQuery := EnumerationRootQuery.shared parameters graph T F before after leftLayout rightLayout
    coordinateBase slot (entry + 49) left right sameSize
  have samePoint : returnPoint parameters graph T F before.size coordinateBase slot entry left width =
      returnPoint parameters graph T F after.size coordinateBase slot entry right width := by
    unfold returnPoint EnumerationRootQuery.returnEntry
    rw [sameSize, SharedQuerySourceCode.root_entry_irrel graph parameters.buses parameters.bridge.target T F
      coordinateBase slot (entry + 49) after.size left right]
  unfold code
  rw [sameQuery, samePoint, sameTable, sameInverse]

private theorem head_at (program : Program width 8) (entry : Nat) (left right : List (Instruction width 8))
    (present : SharedRootRead.BlockAt program entry (left ++ right)) : SharedRootRead.BlockAt program entry left := by
  intro offset below
  have found := present offset (by simp only [List.length_append]; omega)
  rwa [List.getElem?_append_left below] at found

private theorem tail_at (program : Program width 8) (entry : Nat) (left right : List (Instruction width 8))
    (present : SharedRootRead.BlockAt program entry (left ++ right)) :
    SharedRootRead.BlockAt program (entry + left.length) right := by
  intro offset below
  have found := present (left.length + offset) (by simp only [List.length_append]; omega)
  rw [List.getElem?_append_right (by omega)] at found
  simpa only [Nat.add_sub_cancel_left, Nat.add_assoc] using found

private theorem array_at (program : Program width 8) (entry : Nat) (instructions : Program width 8)
    (present : SharedRootRead.BlockAt program entry instructions.toList) : CodeAt program entry instructions := by
  intro phase
  simpa only [Array.getElem?_toList] using present phase.val (by simpa only [Array.length_toList] using phase.isLt)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem blocks_at (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels)) (heap : Array (Word width))
    (layout : Layout (parameters.channels + graph.nodeCount) heap.size)
    (coordinateBase slot offset entry ret : Nat) (root : Fin graph.nodeCount)
    (program : Program width 8)
    (present : SharedRootRead.BlockAt program entry
      (code parameters graph T F heap layout coordinateBase slot offset entry ret root)) :
    CodeAt program entry (SharedRootTaggedCursor.code width parameters.channels entry
      (returnPoint parameters graph T F heap.size coordinateBase slot entry root width + 5) (entry + 37) (entry + 31)) ∧
    SharedRootRead.BlockAt program (entry + 22) (acceptCode width entry ret) ∧
    CodeAt program (entry + 31) (SharedRootResumeEntry.skipCode width layout.tableBase layout.inverseBase entry) ∧
    CodeAt program (entry + 37) (SharedRootHealthyEntry.code width layout.tableBase layout.inverseBase offset slot) ∧
    SharedRootRead.BlockAt program (entry + 49)
      (EnumerationRootQuery.code parameters graph T F heap layout coordinateBase slot (entry + 49) root) ∧
    SharedRootRead.BlockAt program (returnPoint parameters graph T F heap.size coordinateBase slot entry root width)
      (dispatchCode width entry) ∧
    SharedRootRead.BlockAt program (returnPoint parameters graph T F heap.size coordinateBase slot entry root width + 5)
      (exhaustedCode width ret) := by
  unfold code at present
  have cursorBlock := head_at program entry _ _ present
  have first := tail_at program entry _ _ present
  simp only [Array.length_toList, SharedRootTaggedCursor.code_size] at first
  have acceptBlock := head_at program (entry + 22) _ _ first
  have second := tail_at program (entry + 22) _ _ first
  simp only [acceptCode_length, Nat.add_assoc, Nat.reduceAdd] at second
  have skipBlock := head_at program _ _ _ second
  have third := tail_at program _ _ _ second
  simp only [Array.length_toList, SharedRootResumeEntry.skipCode_size, Nat.add_assoc, Nat.reduceAdd] at third
  have healthyBlock := head_at program _ _ _ third
  have fourth := tail_at program _ _ _ third
  simp only [Array.length_toList, SharedRootHealthyEntry.code_size, Nat.add_assoc, Nat.reduceAdd] at fourth
  have queryBlock := head_at program _ _ _ fourth
  have fifth := tail_at program _ _ _ fourth
  have queryEnd := query_end parameters graph T F heap layout coordinateBase slot entry root
  rw [queryEnd] at fifth
  have dispatchBlock := head_at program _ _ _ fifth
  have last := tail_at program _ _ _ fifth
  simp only [dispatchCode_length] at last
  exact ⟨array_at _ _ _ cursorBlock, acceptBlock, array_at _ _ _ skipBlock, array_at _ _ _ healthyBlock,
    by simpa only [Nat.add_assoc] using queryBlock, dispatchBlock, last⟩

end Layout

end Controller.Cost.EnumerationLoop
