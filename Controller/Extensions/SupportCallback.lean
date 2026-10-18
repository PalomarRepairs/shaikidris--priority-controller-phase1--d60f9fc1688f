module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Extensions.SupportCandidate
public import Controller.Extensions.SupportSearchRun

@[expose] public section

/-! The healthy-zero support callback evaluates the forced-target candidate,
reclaims its value table, and restores the traversal mask on both outcomes.
The retained packet contains the healthy reference table. -/
namespace Controller.Extensions.SupportCallback
open Controller.Decoder Controller.Decoder.DAG Controller.Cost Controller.Cost.GateProgram
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestInputStored
open Controller.Cost.ForestInputPrefixStored Controller.Cost.UniformDAGSource
open Controller.Cost.SharedDetectorAssembly

def prepareCode (width b address : Nat) : List (Instruction width 8) :=
  if b = 1 then SupportTarget.saveCode width address else []

def returnCode (width b address destination : Nat) : List (Instruction width 8) :=
  (if b = 1 then SupportTarget.restoreCode width address else []) ++
    [.constant 0 (word width 0), .branchZero 0 (word width destination)]

@[simp] theorem prepareCode_length : (prepareCode width b address).length = if b = 1 then 5 else 0 := by
  by_cases one : b = 1 <;> simp [prepareCode, one]

@[simp] theorem returnCode_length : (returnCode width b address destination).length = if b = 1 then 5 else 2 := by
  by_cases one : b = 1 <;> simp [returnCode, one]

theorem prepare_execution (program : Program width 8) (state : State width 8)
    (source : Array (Word width)) (chosen : Finset (Channel n)) (target : Channel n) (b entry : Nat)
    (heapStored : state.heap = withValues source (assignmentOfSet chosen))
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 5 < 2 ^ width) (capacity : source.size + n < 2 ^ width)
    (present : SharedRootRead.BlockAt program entry (prepareCode width b (source.size + target.val))) :
    ∃ final ticks peak, Execution program state final ticks peak ∧ ticks ≤ 5 ∧ peak ≤ state.liveWords + 1 ∧
      final.heap = withValues source (assignmentOfSet (BoundedAnd.candidate b target chosen)) ∧
      final.stack = (if b = 1 then [boolWord width (assignmentOfSet chosen target)] else []) ++ state.stack ∧
      final.output = state.output ∧
      final.pc = word width (entry + (prepareCode width b (source.size + target.val)).length) ∧
      final.halted = false := by
  by_cases one : b = 1
  · have stored : state.heap[source.size + target.val]? =
        some (boolWord width (assignmentOfSet chosen target)) := by
      rw [heapStored, Array.getElem?_eq_getElem (by simp)]
      exact congrArg some (value_cell source (assignmentOfSet chosen) target)
    obtain ⟨final, trace, heap, stack, output, pc, active, _⟩ :=
      SupportTarget.save_execution program state entry (source.size + target.val) _ stored position running room
        (by simp only [heapStored, withValues_size]; omega) (by simpa [prepareCode, one] using present)
    have update := SharedChannelStore.stored_update source (assignmentOfSet chosen) target true
    have assignments : (fun i => if i = target then true else assignmentOfSet chosen i) =
        assignmentOfSet (insert target chosen) := by
      funext i; simp [assignmentOfSet, eq_comm]
    refine ⟨final, 5, state.liveWords + 1, trace, le_rfl, le_rfl, ?_, ?_, output, ?_, active⟩
    · exact heap.trans (by simpa only [heapStored, assignments, BoundedAnd.candidate, ite_eq_left one] using update)
    · simpa only [ite_eq_left one, List.singleton_append] using stack
    · simpa only [prepareCode_length, ite_eq_left one] using pc
  · exact ⟨state, 0, state.liveWords, Execution.refl _, by omega, by omega,
      by simpa [BoundedAnd.candidate, one] using heapStored,
      by simp [one], rfl, by simpa [one] using position, running⟩

theorem return_execution (program : Program width 8) (state : State width 8)
    (source : Array (Word width)) (chosen : Finset (Channel n)) (target : Channel n) (b entry destination : Nat)
    (rest output : List (Word width))
    (heapStored : state.heap = withValues source (assignmentOfSet (BoundedAnd.candidate b target chosen)))
    (saved : state.stack = (if b = 1 then [boolWord width (assignmentOfSet chosen target)] else []) ++ rest)
    (outputStored : state.output = output)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 5 < 2 ^ width) (capacity : source.size + n < 2 ^ width)
    (present : SharedRootRead.BlockAt program entry (returnCode width b (source.size + target.val) destination)) :
    ∃ final ticks, Execution program state final ticks state.liveWords ∧ ticks ≤ 5 ∧
      final.heap = withValues source (assignmentOfSet chosen) ∧ final.stack = rest ∧ final.output = output ∧
      final.pc = word width destination ∧ final.halted = false := by
  by_cases one : b = 1
  · have firstAt := block_left program entry _ _ present
    have lastAt := block_right program entry _ _ present
    simp only [ite_eq_left one, SupportTarget.restoreCode_length] at firstAt lastAt
    have assignments : (fun i => if i = target then true else assignmentOfSet chosen i) =
        assignmentOfSet (insert target chosen) := by
      funext i; simp [assignmentOfSet, eq_comm]
    have update := SharedChannelStore.stored_update source (assignmentOfSet chosen) target true
    have heap : state.heap = (withValues source (assignmentOfSet chosen)).set (source.size + target.val)
        (boolWord width true) (by simp) := by
      rw [heapStored, update, assignments]
      simp only [BoundedAnd.candidate, ite_eq_left one]
    obtain ⟨restored, first, rh, rs, ro, rp, rr, _⟩ :=
      SupportTarget.restore_execution program state entry (source.size + target.val)
        (withValues source (assignmentOfSet chosen)) (boolWord width (assignmentOfSet chosen target)) rest
        (by simp) (value_cell source (assignmentOfSet chosen) target) heap
        (by simpa [one] using saved) position running (by omega) (by simp; omega) firstAt
    obtain ⟨final, last, pc, fh, fs, fo, active, _⟩ :=
      EnumerationSteps.jump_execution program restored (entry + 3) destination rp rr (by omega)
        (by simpa using lastAt 0 (by simp)) (by simpa using lastAt 1 (by simp))
    have live : restored.liveWords ≤ state.liveWords := Execution.final_storage_le first
    exact ⟨final, 5, by simpa only [Nat.max_eq_left live] using first.append last, le_rfl,
      fh.trans rh, fs.trans rs, fo.trans (ro.trans outputStored), pc, active⟩
  · have physical : SharedRootRead.BlockAt program entry
        [.constant 0 (word width 0), .branchZero 0 (word width destination)] := by
      simpa [returnCode, one] using present
    obtain ⟨final, trace, pc, heap, stack, out, active, _⟩ :=
      EnumerationSteps.jump_execution program state entry destination position running (by omega)
        (by simpa using physical 0 (by simp)) (by simpa using physical 1 (by simp))
    exact ⟨final, 2, trace, by decide, by simpa [BoundedAnd.candidate, one] using heap.trans heapStored,
      by simpa [one] using stack.trans saved, out.trans outputStored, pc, active⟩

def code (width n b : Nat) (packet : Array (Word width)) (rows : List Row) (roots : List Nat)
    (target entry found rejected : Nat) : List (Instruction width 8) :=
  let address := (cacheHeap width packet rows roots).size + target
  let start := entry + (prepareCode width b address).length
  let last := start + 144 + 15 * roots.length
  let yes := last + (returnCode width b address rejected).length
  prepareCode width b address ++
    (SupportCandidate.code width n packet rows roots start 5 yes last ++
      (returnCode width b address rejected ++ returnCode width b address found))

theorem code_length (roots : List Nat) :
    (code width n b packet rows roots target entry found rejected).length =
      148 + 15 * roots.length + (if b = 1 then 11 else 0) := by
  by_cases one : b = 1 <;> simp [code, one] <;> omega

set_option maxHeartbeats 2000000 in
theorem execution (program : Program width 8) (state : State width 8)
    (graph : DAG n) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (heads : HeadsMatch graph rows matched)
    (rootMatches : RootsMatch graph roots) (healthy : Fin graph.nodeCount → Bool)
    (chosen : Finset (Channel n)) (target : Channel n) (b entry found rejected : Nat)
    (heapStored : state.heap = channelHeap (SupportCandidate.header width n rows roots healthy)
      rows roots (assignmentOfSet chosen))
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 159 + 15 * roots.length < 2 ^ width)
    (capacity : (cacheHeap width (SupportCandidate.header width n rows roots healthy) rows roots).size +
      n + graph.nodeCount < 2 ^ width)
    (present : SharedRootRead.BlockAt program entry
      (code width n b (SupportCandidate.header width n rows roots healthy) rows roots target.val entry found rejected)) :
    ∃ final ticks peak, Execution program state final ticks peak ∧
      ticks ≤ 43 * graph.countedSize + 13 * roots.length + 4 * graph.nodeCount + 22 ∧
      peak ≤ state.liveWords + graph.nodeCount + 5 ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (if (BoundedAnd.supportQuery graph b target healthy chosen).isSome
        then found else rejected) ∧ final.halted = false := by
  let packet := SupportCandidate.header width n rows roots healthy
  let source := cacheHeap width packet rows roots
  have sourceCapacity : source.size + n + graph.nodeCount < 2 ^ width := capacity
  let address := source.size + target.val
  let start := entry + (prepareCode width b address).length
  let last := start + 144 + 15 * roots.length
  let yes := last + (returnCode width b address rejected).length
  have prepareLength : (prepareCode width b address).length ≤ 5 := by
    rw [prepareCode_length]; split <;> omega
  have returnLength : (returnCode width b address rejected).length ≤ 5 := by
    rw [returnCode_length]; split <;> omega
  change SharedRootRead.BlockAt program entry
    (prepareCode width b address ++ (SupportCandidate.code width n packet rows roots start 5 yes last ++
      (returnCode width b address rejected ++ returnCode width b address found))) at present
  have prepareAt := block_left program entry _ _ present
  have afterPrepare := block_right program entry _ _ present
  have roundAt := block_left program start _ _ afterPrepare
  have afterRound := block_right program start _ _ afterPrepare
  simp only [SupportCandidate.code_length, ← Nat.add_assoc] at afterRound
  have noAt := block_left program last _ _ afterRound
  have yesAt := block_right program last _ _ afterRound
  obtain ⟨prepared, pt, pp, prepare, ptime, pspace, ph, ps, po, pc, pr⟩ :=
    prepare_execution program state source chosen target b entry heapStored position running (by omega)
      (by omega) prepareAt
  have candidateHeap : prepared.heap = channelHeap packet rows roots
      (assignmentOfSet (BoundedAnd.candidate b target chosen)) := ph
  have countCell : prepared.heap[1]? = some (word width graph.nodeCount) := by
    rw [candidateHeap, SupportCandidate.channel_retained_cell packet rows roots _ 1 (by simp [packet]; omega)]
    exact SupportCandidate.header_count graph rows roots healthy matched
  obtain ⟨evaluated, et, ep, round, etime, espace, eh, es, eo, epos, er⟩ :=
    SupportCandidate.execution program prepared packet graph rows roots matched heads rootMatches
      (assignmentOfSet (BoundedAnd.candidate b target chosen)) healthy start 5 yes last candidateHeap countCell
      (by intro root _; exact SupportCandidate.header_value roots healthy root) pc pr
      (by dsimp [start]; omega) capacity roundAt
  let changed := graph.roots.any (fun root => !healthy root &&
    graph.evalTable (assignmentOfSet (BoundedAnd.candidate b target chosen)) root)
  let offset := if changed then yes else last
  let destination := if changed then found else rejected
  have physical : SharedRootRead.BlockAt program offset (returnCode width b address destination) := by
    cases h : changed
    · simpa [offset, destination, h] using noAt
    · simpa [offset, destination, yes, h] using yesAt
  have atOffset : evaluated.pc = word width offset := epos
  have offsetFits : offset + 5 < 2 ^ width := by
    dsimp [offset, yes, last, start]
    split <;> omega
  obtain ⟨final, ft, finish, ftime, fh, fs, fo, fp, fr⟩ :=
    return_execution program evaluated source chosen target b offset destination state.stack state.output
      (eh.trans ph) (es.trans ps) (eo.trans po) atOffset er offsetFits (by omega) physical
  have preparedLive : prepared.liveWords ≤ state.liveWords + 1 :=
    (Execution.final_storage_le prepare).trans pspace
  have evaluatedLive : evaluated.liveWords = prepared.liveWords := by simp only [State.liveWords, eh, es, eo]
  refine ⟨final, pt + et + ft, max (max pp ep) evaluated.liveWords,
    (prepare.append round).append finish, by omega, by omega,
    fh.trans heapStored.symm, fs, fo, ?_, fr⟩
  simpa only [destination, changed, SupportCandidate.supportQuery_isSome] using fp

theorem contract (program : Program width 8) (graph : DAG n) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (heads : HeadsMatch graph rows matched)
    (rootMatches : RootsMatch graph roots) (healthy : Fin graph.nodeCount → Bool)
    (target : Channel n) (b entry call found : Nat)
    (room : call + 159 + 15 * roots.length < 2 ^ width)
    (capacity : (cacheHeap width (SupportCandidate.header width n rows roots healthy) rows roots).size +
      n + graph.nodeCount < 2 ^ width)
    (present : SharedRootRead.BlockAt program call
      (code width n b (SupportCandidate.header width n rows roots healthy) rows roots target.val call found
        (SupportTraversal.backtrack entry))) :
    SupportSearch.Callback program (cacheHeap width (SupportCandidate.header width n rows roots healthy) rows roots)
      (BoundedAnd.supportQuery graph b target healthy) entry call found (100 * (graph.countedSize + 1))
      (graph.nodeCount + 5) := by
  intro chosen state heap pc running
  obtain ⟨final, ticks, peak, trace, time, space, fh, fs, fo, fp, fr⟩ :=
    execution program state graph rows roots matched heads rootMatches healthy chosen target b call found
      (SupportTraversal.backtrack entry) heap pc running room capacity present
  have rootCount : roots.length = graph.roots.length := by rw [rootMatches]; simp
  have size := graph.countedSize_eq
  exact ⟨final, ticks, peak, trace, by omega, by omega, fh, fs, fo, fr, fp⟩

theorem search (program : Program width 8) (graph : DAG n) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (heads : HeadsMatch graph rows matched)
    (rootMatches : RootsMatch graph roots) (healthy : Fin graph.nodeCount → Bool)
    (target : Channel n) (k b entry call found : Nat)
    (room : call + 159 + 15 * roots.length < 2 ^ width)
    (coreRoom : entry + 36 < 2 ^ width)
    (capacity : (cacheHeap width (SupportCandidate.header width n rows roots healthy) rows roots).size +
      n + graph.nodeCount < 2 ^ width)
    (callbackAt : SharedRootRead.BlockAt program call
      (code width n b (SupportCandidate.header width n rows roots healthy) rows roots target.val call found
        (SupportTraversal.backtrack entry)))
    (coreAt : SharedRootRead.BlockAt program entry
      (SupportTraversal.code width entry n
        (cacheHeap width (SupportCandidate.header width n rows roots healthy) rows roots).size call))
    (rest output : List (Word width)) :
    ∃ final ticks peak, Execution program
      (SupportSearchRun.initial n (k+1) entry
        (cacheHeap width (SupportCandidate.header width n rows roots healthy) rows roots) rest output)
      final ticks peak ∧
      ticks ≤ (100 * (graph.countedSize + 1) + 50) * BoundedAnd.supportCount n k + 6 ∧
      peak ≤ 8 * graph.countedSize + rest.length + output.length + 21 ∧
      final.output = output ∧ SupportSearchRun.Outcome
        (cacheHeap width (SupportCandidate.header width n rows roots healthy) rows roots)
        (BoundedAnd.supportQuery graph b target healthy) found rest final
        (SupportStream.scanSupports graph k b target healthy) := by
  have callback := contract program graph rows roots matched heads rootMatches healthy target b entry call found
    room capacity callbackAt
  obtain ⟨final, ticks, peak, trace, time, space, out, result⟩ :=
    SupportSearchRun.support_scan program _ graph k b target healthy entry call found
      (100 * (graph.countedSize + 1)) (graph.nodeCount + 5) callback coreAt coreRoom
      (by omega) (by omega) rest output
  obtain ⟨children, guards⟩ := matched_incidence_lengths graph rows matched
  have rootCount : roots.length = graph.roots.length := by rw [rootMatches]; simp
  have size := graph.countedSize_eq
  simp only [cacheHeap_size, SupportCandidate.header_size, matched.length_eq, children, guards, rootCount] at space
  exact ⟨final, ticks, peak, trace, time, by omega, out, result⟩

theorem search_code_words (graph : DAG n) (roots : List Nat) (rootMatches : RootsMatch graph roots) :
    144 + 4 * (code width n b packet rows roots target entry found rejected).length ≤
      60 * graph.countedSize + 780 := by
  have rootCount : roots.length = graph.roots.length := by rw [rootMatches]; simp
  have size := graph.countedSize_eq
  rw [code_length]
  split <;> omega

theorem returning_search (program : Program width 8) (graph : DAG n) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (heads : HeadsMatch graph rows matched)
    (rootMatches : RootsMatch graph roots) (healthy : Fin graph.nodeCount → Bool)
    (target : Channel n) (k b entry call found : Nat) (ending : Instruction width 8)
    (room : call+159+15*roots.length < 2^width) (coreRoom : entry+36 < 2^width)
    (capacity : (cacheHeap width (SupportCandidate.header width n rows roots healthy) rows roots).size+
      n+graph.nodeCount < 2^width)
    (callbackAt : SharedRootRead.BlockAt program call
      (code width n b (SupportCandidate.header width n rows roots healthy) rows roots target.val call found
        (SupportTraversal.backtrack entry)))
    (coreAt : SharedRootRead.BlockAt program entry (SupportTraversal.endingCode width entry n
      (cacheHeap width (SupportCandidate.header width n rows roots healthy) rows roots).size call ending))
    (rest output : List (Word width)) :
    ∃ final ticks peak, Execution program
      (SupportSearchRun.initial n (k+1) entry (cacheHeap width (SupportCandidate.header width n rows roots healthy) rows roots)
        rest output) final ticks peak ∧
      ticks ≤ (100*(graph.countedSize+1)+50)*BoundedAnd.supportCount n k+5 ∧
      peak ≤ 8*graph.countedSize+rest.length+output.length+21 ∧ final.output = output ∧
      SupportSearchRun.ReturnedOutcome (cacheHeap width (SupportCandidate.header width n rows roots healthy) rows roots)
        (BoundedAnd.supportQuery graph b target healthy) entry found rest final (SupportStream.scanSupports graph k b target healthy) := by
  have callback := contract program graph rows roots matched heads rootMatches healthy target b entry call found room capacity callbackAt
  obtain ⟨final, ticks, peak, trace, time, space, out, result⟩ :=
    SupportSearchRun.returning_from_mask program _ (BoundedAnd.supportQuery graph b target healthy) entry call found
      (100*(graph.countedSize+1)) (graph.nodeCount+5) (k+1) ending callback coreAt coreRoom (by omega) (by omega) rest output
  rw [SupportStream.leaves_eq_supportCount] at time
  obtain ⟨children, guards⟩ := matched_incidence_lengths graph rows matched
  have rootCount : roots.length = graph.roots.length := by rw [rootMatches]; simp
  have size := graph.countedSize_eq
  simp only [cacheHeap_size, SupportCandidate.header_size, matched.length_eq, children, guards, rootCount] at space
  exact ⟨final, ticks, peak, trace, time, by omega, out, result⟩

end Controller.Extensions.SupportCallback
