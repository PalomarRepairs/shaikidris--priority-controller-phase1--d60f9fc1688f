module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestZeroReclaim
public import Controller.Cost.ForestZeroChannelEmit

@[expose] public section

/-! The source-correct seeded FIFO decision, emitted answer and physical query
suffix release execute consecutively in one program. The captured entry reads
the retained boundary from the caller stack and computes the allocation count
from the actual heap cursor. -/
set_option autoImplicit false
namespace Controller.Cost.ForestZeroAnswerReclaim
open Controller.Cost Controller.Cost.ForestZeroBackendFrame
open Controller.Horn Controller.Horn.WorklistMark Controller.Horn.WorklistFIFO
open Controller.Horn.WorklistOutcome Controller.Horn.WorklistPropagation
open Controller.Horn.WorklistPropagationStep Controller.Horn.WorklistStorage
open Controller.Horn.WorklistFIFORun Controller.Horn.WorklistSeed
variable {width n : Nat}

theorem initialized_execution (keep : Nat) (formula : Controller.CNF.Formula (Fin n)) (dual : Controller.Horn.DualHorn formula)
    (recordHeader recordStart recordEnd base entry scan seedDone conflict : Nat)
    (state : State width 8) (program : Program width 8)
    (physical : Controller.Horn.IndexScan.PhysicalIndex (formula.clauses.toList) recordStart recordEnd base
      (Controller.Horn.IndexScan.occurrences (formula.clauses.toList) recordStart).length state.heap)
    (header : Controller.Horn.SourceScan.CursorStored recordEnd recordHeader state.heap)
    (fifo : Stored ([] : List (Fin n)) base state.heap)
    (separated : base + 5 * n + 4 ≤ recordStart)
    (setupAt : ∀ phase : Fin 10, program[entry + phase.val]? =
      (Controller.Cost.ForestZeroSeedSetup.code (n := n) width base recordHeader recordStart scan)[phase.val]?)
    (scanAt : Controller.Horn.WorklistSeed.At (n := n) program base scan seedDone conflict)
    (position : state.pc = word width entry) (running : state.halted = false)
    (zero : state.reg 2 = word width 0) (one : state.reg 5 = word width 1)
    (room : state.heap.size < 2 ^ width) (setupCapacity : entry + 10 < 2 ^ width)
    (scanCapacity : scan + 47 < 2 ^ width)
    (prefixBound : keep ≤ state.heap.size) (prefixBelow : keep ≤ base)
    (fetch : Nat)
    (headAt : ∀ phase : Fin 4, program[seedDone + phase.val]? =
      (Controller.Horn.WorklistAccept.headSetupCode (n := n) width base fetch)[phase.val]?)
    (headCapacity : seedDone + 4 < 2 ^ width)
    (fifoDone bucket advance ready skip : Nat)
    (fetchAt : WorklistFIFO.FetchAt (n := n) program base fetch fifoDone bucket)
    (advanceAt : WorklistFIFO.AdvanceAt (n := n) program base advance fetch)
    (loopAt : WorklistBucketLoop.At program bucket advance ready)
    (readyAt : WorklistBucketReady.At (n := n) program base ready skip conflict bucket)
    (fetchCapacity : fetch + 14 < 2 ^ width) (advanceCapacity : advance + 5 < 2 ^ width)
    (bucketCapacity : bucket + 12 < 2 ^ width) (readyCapacity : ready + 26 < 2 ^ width)
    (cleanupEntry : Nat) (successAt : ForestZeroAnswer.At program fifoDone 1 cleanupEntry)
    (conflictAt : ForestZeroAnswer.At program conflict 0 cleanupEntry)
    (successCapacity : fifoDone + 4 < 2 ^ width)
    (conflictCapacity : conflict + 4 < 2 ^ width) (returnCapacity : cleanupEntry < 2 ^ width)
    (count returnPc : Nat) (rest : List (Word width))
    (savedCount : state.stack = word width count :: rest)
    (allocated : state.heap.size = keep + count) (countFits : count < 2 ^ width)
    (cleanupSetup : ∀ phase : Fin 3, program[cleanupEntry + phase.val]? =
      (ForestZeroReclaim.setupCode width)[phase.val]?)
    (cleanupLoop : ForestZeroReclaim.At program (cleanupEntry + 3) returnPc)
    (cleanupCapacity : cleanupEntry + 7 < 2 ^ width) :
    ∃ answer : Bool, ∃ finalQueue final ticks,
      ticks ≤ 36 * formula.clauses.toList.length +
        32 * (IndexScan.occurrences formula.clauses.toList recordStart).length + 26 * n + 32 + 4 * count ∧
      Execution program state final ticks (state.liveWords + 1) ∧
      final.heap.size = keep ∧ final.stack = rest ∧
      final.output = word width (if answer then 1 else 0) :: state.output ∧
      final.pc = word width returnPc ∧ final.halted = false ∧
      PrefixFrame keep state.heap final.heap ∧
      (answer = true ↔ ∃ assignment : Fin n → Bool, Controller.CNF.Satisfies assignment formula) ∧
      (answer = true → Controller.CNF.Satisfies (offAssignment finalQueue) formula) := by
  obtain ⟨answer, queue, middle, firstTicks, firstBound, first, middleSize,
    middleStack, middleOutput, middlePC, middleRunning, firstFrame, answerIff, model⟩ :=
    ForestZeroAnswer.initialized_answer_execution keep formula dual recordHeader recordStart recordEnd base
      entry scan seedDone conflict state program physical header fifo separated setupAt scanAt position running zero one room
      setupCapacity scanCapacity prefixBound prefixBelow fetch headAt headCapacity fifoDone bucket advance ready skip
      fetchAt advanceAt loopAt readyAt fetchCapacity advanceCapacity bucketCapacity readyCapacity
      cleanupEntry successAt conflictAt successCapacity conflictCapacity returnCapacity
  obtain ⟨final, last, finalSize, finalStack, finalOutput, finalPC, finalRunning, lastFrame⟩ :=
    ForestZeroReclaim.stacked_execution program cleanupEntry returnPc keep count middle rest
      cleanupSetup cleanupLoop middlePC middleRunning cleanupCapacity countFits
      (middleStack.trans savedCount) (middleSize.trans allocated)
  have middleLive : middle.liveWords = state.liveWords + 1 := by
    unfold State.liveWords
    rw [middleSize, middleStack, middleOutput]
    simp only [List.length_cons]
    omega
  refine ⟨answer, queue, final, firstTicks + (4 * count + 4), by omega,
    ?_, finalSize, finalStack, finalOutput.trans middleOutput, finalPC, finalRunning,
    ForestZeroBackendFrame.trans firstFrame lastFrame, answerIff, model⟩
  simpa only [middleLive, Nat.max_self] using first.append last

/-- The actual heap cursor supplies the release count before seeded decision,
answer emission and reclamation. The caller saves only the retained boundary. -/
theorem captured_initialized_execution (keep : Nat) (formula : Controller.CNF.Formula (Fin n)) (dual : Controller.Horn.DualHorn formula)
    (recordHeader recordStart recordEnd base entry scan seedDone conflict : Nat)
    (state : State width 8) (program : Program width 8)
    (physical : Controller.Horn.IndexScan.PhysicalIndex (formula.clauses.toList) recordStart recordEnd base
      (Controller.Horn.IndexScan.occurrences (formula.clauses.toList) recordStart).length state.heap)
    (header : Controller.Horn.SourceScan.CursorStored recordEnd recordHeader state.heap)
    (fifo : Stored ([] : List (Fin n)) base state.heap)
    (separated : base + 5 * n + 4 ≤ recordStart)
    (setupAt : ∀ phase : Fin 10, program[entry + 6 + phase.val]? =
      (Controller.Cost.ForestZeroSeedSetup.code (n := n) width base recordHeader recordStart scan)[phase.val]?)
    (scanAt : Controller.Horn.WorklistSeed.At (n := n) program base scan seedDone conflict)
    (position : state.pc = word width entry) (running : state.halted = false)
    (zero : state.reg 2 = word width 0) (one : state.reg 5 = word width 1)
    (room : state.heap.size < 2 ^ width) (setupCapacity : entry + 16 < 2 ^ width)
    (scanCapacity : scan + 47 < 2 ^ width)
    (prefixBound : keep ≤ state.heap.size) (prefixBelow : keep ≤ base)
    (fetch : Nat)
    (headAt : ∀ phase : Fin 4, program[seedDone + phase.val]? =
      (Controller.Horn.WorklistAccept.headSetupCode (n := n) width base fetch)[phase.val]?)
    (headCapacity : seedDone + 4 < 2 ^ width)
    (fifoDone bucket advance ready skip : Nat)
    (fetchAt : WorklistFIFO.FetchAt (n := n) program base fetch fifoDone bucket)
    (advanceAt : WorklistFIFO.AdvanceAt (n := n) program base advance fetch)
    (loopAt : WorklistBucketLoop.At program bucket advance ready)
    (readyAt : WorklistBucketReady.At (n := n) program base ready skip conflict bucket)
    (fetchCapacity : fetch + 14 < 2 ^ width) (advanceCapacity : advance + 5 < 2 ^ width)
    (bucketCapacity : bucket + 12 < 2 ^ width) (readyCapacity : ready + 26 < 2 ^ width)
    (cleanupEntry : Nat) (successAt : ForestZeroAnswer.At program fifoDone 1 cleanupEntry)
    (conflictAt : ForestZeroAnswer.At program conflict 0 cleanupEntry)
    (successCapacity : fifoDone + 4 < 2 ^ width)
    (conflictCapacity : conflict + 4 < 2 ^ width) (returnCapacity : cleanupEntry < 2 ^ width)
    (returnPc : Nat) (rest : List (Word width))
    (savedKeep : state.stack = word width keep :: rest)
    (actualCursor : state.reg 7 = word width state.heap.size)
    (captureAt : ∀ phase : Fin 6, program[entry + phase.val]? =
      (ForestZeroReclaim.captureCode width)[phase.val]?)
    (cleanupSetup : ∀ phase : Fin 3, program[cleanupEntry + phase.val]? =
      (ForestZeroReclaim.setupCode width)[phase.val]?)
    (cleanupLoop : ForestZeroReclaim.At program (cleanupEntry + 3) returnPc)
    (cleanupCapacity : cleanupEntry + 7 < 2 ^ width) :
    ∃ answer : Bool, ∃ finalQueue final ticks,
      ticks ≤ 36 * formula.clauses.toList.length +
        32 * (IndexScan.occurrences formula.clauses.toList recordStart).length + 26 * n + 38 + 4 * (state.heap.size - keep) ∧
      Execution program state final ticks (state.liveWords + 1) ∧
      final.heap.size = keep ∧ final.stack = rest ∧
      final.output = word width (if answer then 1 else 0) :: state.output ∧
      final.pc = word width returnPc ∧ final.halted = false ∧
      PrefixFrame keep state.heap final.heap ∧
      (answer = true ↔ ∃ assignment : Fin n → Bool, Controller.CNF.Satisfies assignment formula) ∧
      (answer = true → Controller.CNF.Satisfies (offAssignment finalQueue) formula) := by
  obtain ⟨middle, capture, sameHeap, savedCount, sameOutput, middlePC, middleRunning, preserved⟩ :=
    ForestZeroReclaim.capture_execution program entry keep state rest captureAt position running
      (by omega) room prefixBound savedKeep actualCursor one
  have countFits : state.heap.size - keep < 2 ^ width := by omega
  have allocated : middle.heap.size = keep + (state.heap.size - keep) := by
    rw [sameHeap]
    omega
  obtain ⟨answer, queue, final, ticks, bound, run, finalSize, finalStack, finalOutput,
    finalPC, finalRunning, frame, answerIff, model⟩ :=
    initialized_execution keep formula dual recordHeader recordStart recordEnd base (entry + 6)
      scan seedDone conflict middle program
      (by simpa only [sameHeap] using physical)
      (by simpa only [sameHeap] using header)
      (by simpa only [sameHeap] using fifo)
      separated setupAt scanAt middlePC middleRunning
      ((preserved 2 (by decide) (by decide)).trans zero)
      ((preserved 5 (by decide) (by decide)).trans one)
      (by simpa only [sameHeap] using room) (by omega) scanCapacity
      (by simpa only [sameHeap] using prefixBound) prefixBelow fetch headAt headCapacity
      fifoDone bucket advance ready skip fetchAt advanceAt loopAt readyAt fetchCapacity
      advanceCapacity bucketCapacity readyCapacity cleanupEntry successAt conflictAt
      successCapacity conflictCapacity returnCapacity (state.heap.size - keep) returnPc
      rest savedCount allocated countFits cleanupSetup cleanupLoop cleanupCapacity
  have live : middle.liveWords = state.liveWords := by
    unfold State.liveWords
    rw [sameHeap, savedCount, sameOutput, savedKeep]
    simp only [List.length_cons]
  refine ⟨answer, queue, final, 6 + ticks, by omega, ?_, finalSize, finalStack,
    ?_, finalPC, finalRunning, ?_, answerIff, model⟩
  · simpa only [live, Nat.max_eq_right (Nat.le_add_right state.liveWords 1)] using capture.append run
  · simpa only [sameOutput] using finalOutput
  · simpa only [sameHeap] using frame

/-- The actual terminal model and original-row forcing invariant identify the
greatest assignment without an additional solver run. -/
theorem terminal_greatest (formula : Controller.CNF.Formula (Fin n))
    (dual : Controller.Horn.DualHorn formula) (queue : List (Fin n))
    (model : Controller.CNF.Satisfies (offAssignment queue) formula)
    (forced : QueueForced formula.clauses.toList queue) :
    offAssignment queue = Controller.Horn.greatestCandidate formula := by
  apply Controller.Horn.terminal_state_eq_greatest
    (Controller.Horn.Worklist.satisfies_rulesClosed dual model)
  intro assignment satisfied label trueValue
  by_cases queued : label ∈ queue
  · have falseValue := forced assignment
      ((Controller.Horn.WorklistOutcome.original_models_iff formula dual assignment).mpr satisfied)
      label queued
    exact False.elim (Bool.false_ne_true (falseValue.symm.trans trueValue))
  · simp [offAssignment, queued]

/-- The emitted ascending coordinate words are exactly those of the greatest
source-formula model, including coordinates absent from all clauses. -/
theorem terminal_output_greatest (formula : Controller.CNF.Formula (Fin n))
    (dual : Controller.Horn.DualHorn formula) (queue : List (Fin n))
    (model : Controller.CNF.Satisfies (offAssignment queue) formula)
    (forced : QueueForced formula.clauses.toList queue) :
    (List.finRange n).map (fun label => word width (if offAssignment queue label then 1 else 0)) =
      (List.finRange n).map
        (fun label => word width (if Controller.Horn.greatestCandidate formula label then 1 else 0)) := by
  rw [terminal_greatest formula dual queue model forced]

/-- The terminal model is emitted from actual FIFO off cells before their
allocation is released. Output words survive physical reclamation. -/
theorem model_emission_reclaim (program : Program width 8)
    (entry base keep count returnPc : Nat) (queue : List (Fin n))
    (state : State width 8) (rest : List (Word width))
    (fifo : Stored queue base state.heap)
    (present : Controller.Horn.WorklistAccept.EmitCodeAt program entry base
      (Controller.Horn.WorklistAccept.outputLabels n))
    (position : state.pc = word width entry) (running : state.halted = false)
    (one : state.reg 5 = word width 1) (room : state.heap.size < 2 ^ width)
    (emitCapacity : entry + 4 * n < 2 ^ width) (oneFits : 1 < 2 ^ width)
    (setupAt : ∀ phase : Fin 3, program[entry + 4 * n + phase.val]? =
      (ForestZeroReclaim.setupCode width)[phase.val]?)
    (loopAt : ForestZeroReclaim.At program (entry + 4 * n + 3) returnPc)
    (cleanupCapacity : entry + 4 * n + 7 < 2 ^ width)
    (countFits : count < 2 ^ width)
    (saved : state.stack = word width count :: rest)
    (allocated : state.heap.size = keep + count) :
    ∃ final, Execution program state final (4 * n + (4 * count + 4))
        (state.liveWords + n) ∧
      final.heap.size = keep ∧ final.stack = rest ∧
      final.output = (List.finRange n).map
        (fun label => word width (if offAssignment queue label then 1 else 0)) ++ state.output ∧
      final.pc = word width returnPc ∧ final.halted = false ∧
      PrefixFrame keep state.heap final.heap := by
  obtain ⟨middle, first, heap, stack, output, _, pc, live⟩ :=
    Controller.Horn.WorklistAccept.emit_code_execution program entry base
      (Controller.Horn.WorklistAccept.outputLabels n) queue state fifo present position running one room
      (by simpa only [Controller.Horn.WorklistAccept.output_labels_length] using emitCapacity) oneFits
  obtain ⟨final, last, size, finalStack, finalOutput, finalPC, finalRunning, frame⟩ :=
    ForestZeroReclaim.stacked_execution program (entry + 4 * n) returnPc keep count middle rest
      setupAt loopAt (by simpa only [Controller.Horn.WorklistAccept.output_labels_length] using pc)
      live cleanupCapacity countFits (stack.trans saved) (congrArg Array.size heap |>.trans allocated)
  have middleLive : middle.liveWords = state.liveWords + n := by
    unfold State.liveWords
    rw [heap, stack, output]
    simp only [List.length_append, List.length_reverse, List.length_map,
      Controller.Horn.WorklistAccept.output_labels_length]
    omega
  refine ⟨final, ?_, size, finalStack, ?_, finalPC, finalRunning, ?_⟩
  · simpa only [Controller.Horn.WorklistAccept.output_labels_length, middleLive, Nat.max_self]
      using first.append last
  · rw [finalOutput, output]
    simp only [Controller.Horn.WorklistAccept.outputLabels, List.map_reverse, List.reverse_reverse]
  · simpa only [heap] using frame

/-- The actual original-source decision and answer trace retains physical
terminal FIFO storage and its greatest-model identity for emission before cleanup. -/
theorem initialized_model_answer_execution (prefixSize : Nat) (formula : Controller.CNF.Formula (Fin n)) (dual : Controller.Horn.DualHorn formula)
    (recordHeader recordStart recordEnd base entry scan seedDone conflict : Nat)
    (state : State width 8) (program : Program width 8)
    (physical : Controller.Horn.IndexScan.PhysicalIndex (formula.clauses.toList) recordStart recordEnd base
      (Controller.Horn.IndexScan.occurrences (formula.clauses.toList) recordStart).length state.heap)
    (header : Controller.Horn.SourceScan.CursorStored recordEnd recordHeader state.heap)
    (fifo : Stored ([] : List (Fin n)) base state.heap)
    (separated : base + 5 * n + 4 ≤ recordStart)
    (setupAt : ∀ phase : Fin 10, program[entry + phase.val]? =
      (Controller.Cost.ForestZeroSeedSetup.code (n := n) width base recordHeader recordStart scan)[phase.val]?)
    (scanAt : Controller.Horn.WorklistSeed.At (n := n) program base scan seedDone conflict)
    (position : state.pc = word width entry) (running : state.halted = false)
    (zero : state.reg 2 = word width 0) (one : state.reg 5 = word width 1)
    (room : state.heap.size < 2 ^ width) (setupCapacity : entry + 10 < 2 ^ width)
    (scanCapacity : scan + 47 < 2 ^ width)
    (prefixBound : prefixSize ≤ state.heap.size) (prefixBelow : prefixSize ≤ base)
    (fetch : Nat)
    (headAt : ∀ phase : Fin 4, program[seedDone + phase.val]? =
      (Controller.Horn.WorklistAccept.headSetupCode (n := n) width base fetch)[phase.val]?)
    (headCapacity : seedDone + 4 < 2 ^ width)
    (fifoDone bucket advance ready skip : Nat)
    (fetchAt : WorklistFIFO.FetchAt (n := n) program base fetch fifoDone bucket)
    (advanceAt : WorklistFIFO.AdvanceAt (n := n) program base advance fetch)
    (loopAt : WorklistBucketLoop.At program bucket advance ready)
    (readyAt : WorklistBucketReady.At (n := n) program base ready skip conflict bucket)
    (fetchCapacity : fetch + 14 < 2 ^ width) (advanceCapacity : advance + 5 < 2 ^ width)
    (bucketCapacity : bucket + 12 < 2 ^ width) (readyCapacity : ready + 26 < 2 ^ width)
    (returnPc : Nat) (successAt : ForestZeroAnswer.At program fifoDone 1 returnPc)
    (conflictAt : ForestZeroAnswer.At program conflict 0 returnPc)
    (successCapacity : fifoDone + 4 < 2 ^ width)
    (conflictCapacity : conflict + 4 < 2 ^ width) (returnCapacity : returnPc < 2 ^ width) :
    ∃ answer : Bool, ∃ finalQueue final ticks,
      ticks ≤ 36 * formula.clauses.toList.length +
        32 * (IndexScan.occurrences formula.clauses.toList recordStart).length + 26 * n + 28 ∧
      Execution program state final ticks (state.liveWords + 1) ∧
      final.heap.size = state.heap.size ∧ final.stack = state.stack ∧
      final.output = word width (if answer then 1 else 0) :: state.output ∧
      final.pc = word width returnPc ∧ final.halted = false ∧
      PrefixFrame prefixSize state.heap final.heap ∧
      (answer = true ↔ ∃ assignment : Fin n → Bool, Controller.CNF.Satisfies assignment formula) ∧
      (answer = true → Controller.CNF.Satisfies (offAssignment finalQueue) formula ∧
        Stored finalQueue base final.heap ∧
        offAssignment finalQueue = Controller.Horn.greatestCandidate formula) := by
  obtain ⟨queue, middle, firstTicks, firstBound, first, middleSize, middleStack, middleOutput, firstFrame, result⟩ :=
    Controller.Cost.ForestZeroOutcome.initialized_original_execution prefixSize formula dual recordHeader recordStart recordEnd base
      entry scan seedDone conflict state program physical header fifo separated setupAt scanAt position running zero one room
      setupCapacity scanCapacity prefixBound prefixBelow fetch headAt headCapacity fifoDone bucket advance ready skip
      fetchAt advanceAt loopAt readyAt fetchCapacity advanceCapacity bucketCapacity readyCapacity
  have middleLive : middle.liveWords = state.liveWords := by
    unfold State.liveWords
    rw [middleSize, middleStack, middleOutput]
  rcases result with ⟨pc, live, noModels⟩ | ⟨fired, finished, model, forced⟩
  · obtain ⟨final, last, heap, stack, output, finalPC, finalRunning, lastFrame⟩ :=
      ForestZeroAnswer.execution prefixSize program conflict 0 returnPc middle conflictAt pc live conflictCapacity returnCapacity firstFrame.2.1
    refine ⟨false, queue, final, firstTicks + 4, by omega, ?_, ?_, stack.trans middleStack,
      ?_, finalPC, finalRunning, Controller.Cost.ForestZeroBackendFrame.trans firstFrame lastFrame, ?_, ?_⟩
    · simpa only [middleLive, show max state.liveWords (state.liveWords + 1) = state.liveWords + 1 by omega] using first.append last
    · rw [heap]; exact middleSize
    · simpa only [Bool.false_eq_true, ↓reduceIte, middleOutput] using output
    · constructor
      · intro impossible; cases impossible
      · intro modelExists; exact False.elim (noModels modelExists)
    · intro impossible; cases impossible
  · obtain ⟨final, last, heap, stack, output, finalPC, finalRunning, lastFrame⟩ :=
      ForestZeroAnswer.execution prefixSize program fifoDone 1 returnPc middle successAt finished.position finished.running
        successCapacity returnCapacity firstFrame.2.1
    refine ⟨true, queue, final, firstTicks + 4, by omega, ?_, ?_, stack.trans middleStack,
      ?_, finalPC, finalRunning, Controller.Cost.ForestZeroBackendFrame.trans firstFrame lastFrame, ?_, ?_⟩
    · simpa only [middleLive, show max state.liveWords (state.liveWords + 1) = state.liveWords + 1 by omega] using first.append last
    · rw [heap]; exact middleSize
    · simpa only [↓reduceIte, middleOutput] using output
    · exact ⟨fun _ => ⟨offAssignment queue, model⟩, fun _ => rfl⟩
    · intro _
      refine ⟨model, ?_, terminal_greatest formula dual queue model forced⟩
      simpa only [heap] using finished.fifo

/-- The successful terminal emits its SAT tag, then all physical model values,
then releases query storage. The output remains available after reclamation. -/
theorem tagged_model_emission_reclaim (program : Program width 8)
    (entry base keep count returnPc : Nat) (queue : List (Fin n))
    (state : State width 8) (rest : List (Word width))
    (fifo : Stored queue base state.heap)
    (tag0 : program[entry]? = some (.constant 0 (word width 1)))
    (tag1 : program[entry + 1]? = some (.emit 0))
    (present : Controller.Horn.WorklistAccept.EmitCodeAt program (entry + 2) base
      (Controller.Horn.WorklistAccept.outputLabels n))
    (position : state.pc = word width entry) (running : state.halted = false)
    (one : state.reg 5 = word width 1) (room : state.heap.size < 2 ^ width)
    (emitCapacity : entry + 2 + 4 * n < 2 ^ width) (oneFits : 1 < 2 ^ width)
    (setupAt : ∀ phase : Fin 3, program[entry + 2 + 4 * n + phase.val]? =
      (ForestZeroReclaim.setupCode width)[phase.val]?)
    (loopAt : ForestZeroReclaim.At program (entry + 2 + 4 * n + 3) returnPc)
    (cleanupCapacity : entry + 2 + 4 * n + 7 < 2 ^ width)
    (countFits : count < 2 ^ width)
    (saved : state.stack = word width count :: rest)
    (allocated : state.heap.size = keep + count) :
    ∃ final, Execution program state final (4 * n + 4 * count + 6)
        (state.liveWords + n + 1) ∧
      final.heap.size = keep ∧ final.stack = rest ∧
      final.output = (List.finRange n).map
        (fun label => word width (if offAssignment queue label then 1 else 0)) ++
        (word width 1 :: state.output) ∧
      final.pc = word width returnPc ∧ final.halted = false ∧
      PrefixFrame keep state.heap final.heap := by
  obtain ⟨tagged, first, heap, stack, output, heldOne, pc, live⟩ :=
    Controller.Horn.WorklistAccept.tag_execution program entry 1 state tag0 tag1
      position running (by omega)
  obtain ⟨final, last, size, finalStack, finalOutput, finalPC, finalRunning, frame⟩ :=
    model_emission_reclaim program (entry + 2) base keep count returnPc queue tagged rest
      (by simpa only [heap] using fifo) present pc live (heldOne.trans one)
      (by simpa only [heap] using room) emitCapacity oneFits setupAt loopAt cleanupCapacity
      countFits (stack.trans saved) (congrArg Array.size heap |>.trans allocated)
  have taggedLive : tagged.liveWords = state.liveWords + 1 := by
    unfold State.liveWords
    rw [heap, stack, output]
    simp only [List.length_cons]
    omega
  refine ⟨final, ?_, size, finalStack, ?_, finalPC, finalRunning, ?_⟩
  · have trace := first.append last
    convert trace using 1 <;> (try simp only [taggedLive]) <;> omega
  · rw [finalOutput, output]
  · simpa only [heap] using frame

theorem initialized_model_reclaim_execution (keep : Nat) (formula : Controller.CNF.Formula (Fin n)) (dual : Controller.Horn.DualHorn formula)
    (recordHeader recordStart recordEnd base entry scan seedDone conflict : Nat)
    (state : State width 8) (program : Program width 8)
    (physical : Controller.Horn.IndexScan.PhysicalIndex (formula.clauses.toList) recordStart recordEnd base
      (Controller.Horn.IndexScan.occurrences (formula.clauses.toList) recordStart).length state.heap)
    (header : Controller.Horn.SourceScan.CursorStored recordEnd recordHeader state.heap)
    (fifo : Stored ([] : List (Fin n)) base state.heap)
    (separated : base + 5 * n + 4 ≤ recordStart)
    (setupAt : ∀ phase : Fin 10, program[entry + phase.val]? =
      (Controller.Cost.ForestZeroSeedSetup.code (n := n) width base recordHeader recordStart scan)[phase.val]?)
    (scanAt : Controller.Horn.WorklistSeed.At (n := n) program base scan seedDone conflict)
    (position : state.pc = word width entry) (running : state.halted = false)
    (zero : state.reg 2 = word width 0) (one : state.reg 5 = word width 1)
    (room : state.heap.size < 2 ^ width) (setupCapacity : entry + 10 < 2 ^ width)
    (scanCapacity : scan + 47 < 2 ^ width)
    (prefixBound : keep ≤ state.heap.size) (prefixBelow : keep ≤ base)
    (fetch : Nat)
    (headAt : ∀ phase : Fin 4, program[seedDone + phase.val]? =
      (Controller.Horn.WorklistAccept.headSetupCode (n := n) width base fetch)[phase.val]?)
    (headCapacity : seedDone + 4 < 2 ^ width)
    (fifoDone bucket advance ready skip : Nat)
    (fetchAt : WorklistFIFO.FetchAt (n := n) program base fetch fifoDone bucket)
    (advanceAt : WorklistFIFO.AdvanceAt (n := n) program base advance fetch)
    (loopAt : WorklistBucketLoop.At program bucket advance ready)
    (readyAt : WorklistBucketReady.At (n := n) program base ready skip conflict bucket)
    (fetchCapacity : fetch + 14 < 2 ^ width) (advanceCapacity : advance + 5 < 2 ^ width)
    (bucketCapacity : bucket + 12 < 2 ^ width) (readyCapacity : ready + 26 < 2 ^ width)
    (cleanupEntry returnPc count : Nat) (rest : List (Word width))
    (saved : state.stack = word width count :: rest)
    (allocated : state.heap.size = keep + count) (countFits : count < 2 ^ width)
    (tag0 : program[fifoDone]? = some (.constant 0 (word width 1)))
    (tag1 : program[fifoDone + 1]? = some (.emit 0))
    (emitAt : Controller.Horn.WorklistAccept.EmitCodeAt program (fifoDone + 2) base
      (Controller.Horn.WorklistAccept.outputLabels n))
    (successSetup : ∀ phase : Fin 3, program[fifoDone + 2 + 4 * n + phase.val]? =
      (ForestZeroReclaim.setupCode width)[phase.val]?)
    (successLoop : ForestZeroReclaim.At program (fifoDone + 2 + 4 * n + 3) returnPc)
    (successCapacity : fifoDone + 2 + 4 * n + 7 < 2 ^ width)
    (conflictAt : ForestZeroAnswer.At program conflict 0 cleanupEntry)
    (conflictCapacity : conflict + 4 < 2 ^ width) (cleanupFits : cleanupEntry < 2 ^ width)
    (cleanupSetup : ∀ phase : Fin 3, program[cleanupEntry + phase.val]? =
      (ForestZeroReclaim.setupCode width)[phase.val]?)
    (cleanupLoop : ForestZeroReclaim.At program (cleanupEntry + 3) returnPc)
    (cleanupCapacity : cleanupEntry + 7 < 2 ^ width) (oneFits : 1 < 2 ^ width) :
    ∃ answer : Bool, ∃ queue final ticks peak,
      ticks ≤ 36 * formula.clauses.toList.length +
        32 * (IndexScan.occurrences formula.clauses.toList recordStart).length +
        30 * n + 32 + 4 * count ∧
      Execution program state final ticks peak ∧ peak ≤ state.liveWords + n + 1 ∧
      final.heap.size = keep ∧ final.stack = rest ∧
      final.output = (if answer then
        (List.finRange n).map (fun label => word width (if offAssignment queue label then 1 else 0)) ++
          [word width 1] else [word width 0]) ++ state.output ∧
      final.pc = word width returnPc ∧ final.halted = false ∧
      PrefixFrame keep state.heap final.heap ∧
      (answer = true ↔ ∃ assignment : Fin n → Bool, Controller.CNF.Satisfies assignment formula) ∧
      (answer = true → offAssignment queue = Controller.Horn.greatestCandidate formula) := by
  obtain ⟨queue, middle, firstTicks, firstBound, first, middleSize, middleStack, middleOutput, firstFrame, result⟩ :=
    ForestZeroOutcome.initialized_original_execution keep formula dual recordHeader recordStart recordEnd base
      entry scan seedDone conflict state program physical header fifo separated setupAt scanAt position running zero one room
      setupCapacity scanCapacity prefixBound prefixBelow fetch headAt headCapacity fifoDone bucket advance ready skip
      fetchAt advanceAt loopAt readyAt fetchCapacity advanceCapacity bucketCapacity readyCapacity
  have middleLive : middle.liveWords = state.liveWords := by
    unfold State.liveWords
    rw [middleSize, middleStack, middleOutput]
  rcases result with ⟨pc, live, noModels⟩ | ⟨fired, finished, model, forced⟩
  · obtain ⟨tagged, tag, heap, stack, output, tagPC, tagRunning, tagFrame⟩ :=
      ForestZeroAnswer.execution keep program conflict 0 cleanupEntry middle conflictAt pc live
        conflictCapacity cleanupFits firstFrame.2.1
    obtain ⟨final, last, size, finalStack, finalOutput, finalPC, finalRunning, frame⟩ :=
      ForestZeroReclaim.stacked_execution program cleanupEntry returnPc keep count tagged rest
        cleanupSetup cleanupLoop tagPC tagRunning cleanupCapacity countFits
        (stack.trans (middleStack.trans saved))
        ((congrArg Array.size heap).trans (middleSize.trans allocated))
    have taggedLive : tagged.liveWords = state.liveWords + 1 := by
      unfold State.liveWords
      rw [heap, stack, output, middleSize, middleStack, middleOutput]
      simp only [List.length_cons]
      omega
    refine ⟨false, queue, final, firstTicks + 4 + (4 * count + 4), state.liveWords + 1, by omega,
      ?_, by omega, size, finalStack, ?_, finalPC, finalRunning,
      ForestZeroBackendFrame.trans firstFrame (ForestZeroBackendFrame.trans tagFrame frame), ?_, ?_⟩
    · have trace := (first.append tag).append last
      simpa only [middleLive, taggedLive,
        show max state.liveWords (state.liveWords + 1) = state.liveWords + 1 by omega,
        Nat.max_self] using trace
    · rw [finalOutput, output, middleOutput]
      rfl
    · constructor
      · intro impossible; cases impossible
      · intro existsModel; exact False.elim (noModels existsModel)
    · intro impossible; cases impossible
  · obtain ⟨final, last, size, finalStack, output, finalPC, finalRunning, frame⟩ :=
      tagged_model_emission_reclaim program fifoDone base keep count returnPc queue middle rest
        finished.fifo tag0 tag1 emitAt finished.position finished.running finished.one finished.room
        (by omega) oneFits successSetup successLoop successCapacity countFits
        (middleStack.trans saved) (middleSize.trans allocated)
    refine ⟨true, queue, final, firstTicks + (4 * n + 4 * count + 6), state.liveWords + n + 1, by omega,
      ?_, le_rfl, size, finalStack, ?_, finalPC, finalRunning,
      ForestZeroBackendFrame.trans firstFrame frame, ?_, ?_⟩
    · have trace := first.append last
      simpa only [middleLive, show max state.liveWords (state.liveWords + n + 1) =
        state.liveWords + n + 1 by omega] using trace
    · rw [output, middleOutput]
      simp only [↓reduceIte,
        List.append_assoc, List.singleton_append]
    · exact ⟨fun _ => ⟨offAssignment queue, model⟩, fun _ => rfl⟩
    · exact fun _ => terminal_greatest formula dual queue model forced

theorem captured_model_reclaim_execution (keep : Nat) (formula : Controller.CNF.Formula (Fin n)) (dual : Controller.Horn.DualHorn formula)
    (recordHeader recordStart recordEnd base entry scan seedDone conflict : Nat)
    (state : State width 8) (program : Program width 8)
    (physical : Controller.Horn.IndexScan.PhysicalIndex (formula.clauses.toList) recordStart recordEnd base
      (Controller.Horn.IndexScan.occurrences (formula.clauses.toList) recordStart).length state.heap)
    (header : Controller.Horn.SourceScan.CursorStored recordEnd recordHeader state.heap)
    (fifo : Stored ([] : List (Fin n)) base state.heap)
    (separated : base + 5 * n + 4 ≤ recordStart)
    (setupAt : ∀ phase : Fin 10, program[entry + 6 + phase.val]? =
      (Controller.Cost.ForestZeroSeedSetup.code (n := n) width base recordHeader recordStart scan)[phase.val]?)
    (scanAt : Controller.Horn.WorklistSeed.At (n := n) program base scan seedDone conflict)
    (position : state.pc = word width entry) (running : state.halted = false)
    (zero : state.reg 2 = word width 0) (one : state.reg 5 = word width 1)
    (room : state.heap.size < 2 ^ width) (setupCapacity : entry + 16 < 2 ^ width)
    (scanCapacity : scan + 47 < 2 ^ width)
    (prefixBound : keep ≤ state.heap.size) (prefixBelow : keep ≤ base)
    (fetch : Nat)
    (headAt : ∀ phase : Fin 4, program[seedDone + phase.val]? =
      (Controller.Horn.WorklistAccept.headSetupCode (n := n) width base fetch)[phase.val]?)
    (headCapacity : seedDone + 4 < 2 ^ width)
    (fifoDone bucket advance ready skip : Nat)
    (fetchAt : WorklistFIFO.FetchAt (n := n) program base fetch fifoDone bucket)
    (advanceAt : WorklistFIFO.AdvanceAt (n := n) program base advance fetch)
    (loopAt : WorklistBucketLoop.At program bucket advance ready)
    (readyAt : WorklistBucketReady.At (n := n) program base ready skip conflict bucket)
    (fetchCapacity : fetch + 14 < 2 ^ width) (advanceCapacity : advance + 5 < 2 ^ width)
    (bucketCapacity : bucket + 12 < 2 ^ width) (readyCapacity : ready + 26 < 2 ^ width)
    (cleanupEntry returnPc : Nat) (rest : List (Word width))
    (savedKeep : state.stack = word width keep :: rest)
    (actualCursor : state.reg 7 = word width state.heap.size)
    (captureAt : ∀ phase : Fin 6, program[entry + phase.val]? =
      (ForestZeroReclaim.captureCode width)[phase.val]?)
    (tag0 : program[fifoDone]? = some (.constant 0 (word width 1)))
    (tag1 : program[fifoDone + 1]? = some (.emit 0))
    (emitAt : Controller.Horn.WorklistAccept.EmitCodeAt program (fifoDone + 2) base
      (Controller.Horn.WorklistAccept.outputLabels n))
    (successSetup : ∀ phase : Fin 3, program[fifoDone + 2 + 4 * n + phase.val]? =
      (ForestZeroReclaim.setupCode width)[phase.val]?)
    (successLoop : ForestZeroReclaim.At program (fifoDone + 2 + 4 * n + 3) returnPc)
    (successCapacity : fifoDone + 2 + 4 * n + 7 < 2 ^ width)
    (conflictAt : ForestZeroAnswer.At program conflict 0 cleanupEntry)
    (conflictCapacity : conflict + 4 < 2 ^ width) (cleanupFits : cleanupEntry < 2 ^ width)
    (cleanupSetup : ∀ phase : Fin 3, program[cleanupEntry + phase.val]? =
      (ForestZeroReclaim.setupCode width)[phase.val]?)
    (cleanupLoop : ForestZeroReclaim.At program (cleanupEntry + 3) returnPc)
    (cleanupCapacity : cleanupEntry + 7 < 2 ^ width) (oneFits : 1 < 2 ^ width) :
    ∃ answer : Bool, ∃ queue final ticks peak,
      ticks ≤ 36 * formula.clauses.toList.length +
        32 * (IndexScan.occurrences formula.clauses.toList recordStart).length +
        30 * n + 38 + 4 * (state.heap.size - keep) ∧
      Execution program state final ticks peak ∧ peak ≤ state.liveWords + n + 1 ∧
      final.heap.size = keep ∧ final.stack = rest ∧
      final.output = (if answer then
        (List.finRange n).map (fun label => word width (if offAssignment queue label then 1 else 0)) ++
          [word width 1] else [word width 0]) ++ state.output ∧
      final.pc = word width returnPc ∧ final.halted = false ∧
      PrefixFrame keep state.heap final.heap ∧
      (answer = true ↔ ∃ assignment : Fin n → Bool, Controller.CNF.Satisfies assignment formula) ∧
      (answer = true → offAssignment queue = Controller.Horn.greatestCandidate formula) := by
  obtain ⟨middle, capture, sameHeap, savedCount, sameOutput, middlePC, middleRunning, preserved⟩ :=
    ForestZeroReclaim.capture_execution program entry keep state rest captureAt position running
      (by omega) room prefixBound savedKeep actualCursor one
  have countFits : state.heap.size - keep < 2 ^ width := by omega
  have allocated : middle.heap.size = keep + (state.heap.size - keep) := by
    rw [sameHeap]
    omega
  obtain ⟨answer, queue, final, ticks, peak, bound, run, peakBound, finalSize, finalStack,
    finalOutput, finalPC, finalRunning, frame, answerIff, greatest⟩ :=
    initialized_model_reclaim_execution keep formula dual recordHeader recordStart recordEnd base (entry + 6)
      scan seedDone conflict middle program
      (by simpa only [sameHeap] using physical)
      (by simpa only [sameHeap] using header)
      (by simpa only [sameHeap] using fifo)
      separated setupAt scanAt middlePC middleRunning
      ((preserved 2 (by decide) (by decide)).trans zero)
      ((preserved 5 (by decide) (by decide)).trans one)
      (by simpa only [sameHeap] using room) (by omega) scanCapacity
      (by simpa only [sameHeap] using prefixBound) prefixBelow fetch headAt headCapacity
      fifoDone bucket advance ready skip fetchAt advanceAt loopAt readyAt fetchCapacity
      advanceCapacity bucketCapacity readyCapacity cleanupEntry returnPc (state.heap.size - keep) rest
      savedCount allocated countFits tag0 tag1 emitAt successSetup successLoop successCapacity
      conflictAt conflictCapacity cleanupFits cleanupSetup cleanupLoop cleanupCapacity oneFits
  have live : middle.liveWords = state.liveWords := by
    unfold State.liveWords
    rw [sameHeap, savedCount, sameOutput, savedKeep]
    simp only [List.length_cons]
  refine ⟨answer, queue, final, 6 + ticks, max state.liveWords peak, by omega,
    capture.append run, ?_, finalSize, finalStack, ?_, finalPC, finalRunning, ?_, answerIff, greatest⟩
  · rw [live] at peakBound
    omega
  · simpa only [sameOutput] using finalOutput
  · simpa only [sameHeap] using frame

/-- Original-channel model words survive the physical release of the query
suffix. Both phases execute in the same fetched caller program. -/
theorem channel_emission_reclaim {channels : Nat} (program : Program width 8)
    (entry cleanupEntry returnPc table offBase keep count : Nat)
    (slots : Fin channels → Nat) (bits : Fin channels → Bool)
    (state : State width 8) (rest : List (Word width))
    (stored : ForestZeroChannelEmit.Stored state.heap table offBase slots bits)
    (position : state.pc = word width entry) (running : state.halted = false)
    (zero : state.reg 2 = word width 0) (remaining : state.reg 3 = word width channels)
    (tableWord : state.reg 4 = word width table) (one : state.reg 5 = word width 1)
    (decrement : state.reg 6 = word width (2 ^ width - 1))
    (offWord : state.reg 7 = word width offBase)
    (channelsFit : channels + 1 < 2 ^ width) (heapFits : state.heap.size ≤ 2 ^ width)
    (emitCapacity : entry + 14 < 2 ^ width)
    (emitAt : ForestZeroChannelEmit.CodeAt program entry cleanupEntry)
    (setupAt : ∀ phase : Fin 3, program[cleanupEntry + phase.val]? =
      (ForestZeroReclaim.setupCode width)[phase.val]?)
    (loopAt : ForestZeroReclaim.At program (cleanupEntry + 3) returnPc)
    (cleanupCapacity : cleanupEntry + 7 < 2 ^ width)
    (countFits : count < 2 ^ width)
    (saved : state.stack = word width count :: rest)
    (allocated : state.heap.size = keep + count) :
    ∃ final ticks peak, Execution program state final ticks peak ∧
      ticks ≤ 13 * channels + 4 * count + 5 ∧
      peak ≤ state.liveWords + channels ∧
      final.heap.size = keep ∧ final.stack = rest ∧
      final.output = (List.finRange channels).map
        (fun channel => ForestZeroChannelEmit.bitWord width (bits channel)) ++ state.output ∧
      final.pc = word width returnPc ∧ final.halted = false ∧
      PrefixFrame keep state.heap final.heap := by
  obtain ⟨middle, ticks, peak, emitted, timeBound, peakBound, heap, stack,
      output, registers, remainingZero, pc, live⟩ :=
    ForestZeroChannelEmit.execution program state entry cleanupEntry table offBase slots bits
      stored position running zero remaining tableWord one decrement offWord channelsFit
      heapFits emitCapacity emitAt
  obtain ⟨final, released, size, finalStack, finalOutput, finalPC, finalRunning, frame⟩ :=
    ForestZeroReclaim.stacked_execution program cleanupEntry returnPc keep count middle rest
      setupAt loopAt pc live cleanupCapacity countFits (stack.trans saved)
      ((congrArg Array.size heap).trans allocated)
  have middleLive : middle.liveWords = state.liveWords + channels := by
    unfold State.liveWords
    rw [heap, stack, output]
    simp only [List.length_append, List.length_map, List.length_finRange]
    omega
  refine ⟨final, ticks + (4 * count + 4), max peak middle.liveWords,
    emitted.append released, ?_, ?_, size, finalStack, ?_, finalPC, finalRunning, ?_⟩
  · omega
  · rw [middleLive]
    exact max_le peakBound (Nat.le_refl _)
  · rw [finalOutput, output]
  · simpa only [heap] using frame

/-- The retained physical dictionary and terminal FIFO determine the emitted
original-channel model before reclamation. No separate model-cell premise is
needed at this interface. -/
theorem dictionary_emission_reclaim {channels ambient : Nat}
    (program : Program width 8) (state : State width 8)
    (entry cleanupEntry returnPc base keep count : Nat)
    (dictionary : ForestZeroCompile.Dictionary ambient)
    (layout : ForestZeroDictionary.Layout ambient state.heap.size)
    (represented : ForestZeroDictionary.Represented state.heap layout dictionary)
    (within : channels ≤ ambient)
    (queue : List (Fin dictionary.coordinates.size))
    (fifo : Stored queue base state.heap)
    (localFit : dictionary.coordinates.size + 1 < 2 ^ width)
    (position : state.pc = word width entry) (running : state.halted = false)
    (zero : state.reg 2 = word width 0) (remaining : state.reg 3 = word width channels)
    (tableWord : state.reg 4 = word width layout.tableBase) (one : state.reg 5 = word width 1)
    (decrement : state.reg 6 = word width (2 ^ width - 1))
    (offWord : state.reg 7 = word width (base + 1))
    (channelsFit : channels + 1 < 2 ^ width) (heapFits : state.heap.size ≤ 2 ^ width)
    (emitCapacity : entry + 14 < 2 ^ width)
    (emitAt : ForestZeroChannelEmit.CodeAt program entry cleanupEntry)
    (setupAt : ∀ phase : Fin 3, program[cleanupEntry + phase.val]? =
      (ForestZeroReclaim.setupCode width)[phase.val]?)
    (loopAt : ForestZeroReclaim.At program (cleanupEntry + 3) returnPc)
    (cleanupCapacity : cleanupEntry + 7 < 2 ^ width)
    (countFits : count < 2 ^ width) (rest : List (Word width))
    (saved : state.stack = word width count :: rest)
    (allocated : state.heap.size = keep + count) :
    ∃ final ticks peak, Execution program state final ticks peak ∧
      ticks ≤ 13 * channels + 4 * count + 5 ∧ peak ≤ state.liveWords + channels ∧
      final.heap.size = keep ∧ final.stack = rest ∧
      final.output = (List.finRange channels).map (fun channel => ForestZeroChannelEmit.bitWord width
        (ForestZeroModelLift.lift dictionary true (ForestZeroChannelEmit.localValues queue)
          ⟨channel.val, lt_of_lt_of_le channel.isLt within⟩)) ++ state.output ∧
      final.pc = word width returnPc ∧ final.halted = false ∧
      PrefixFrame keep state.heap final.heap := by
  exact channel_emission_reclaim program entry cleanupEntry returnPc layout.tableBase (base + 1)
    keep count _ _ state rest
    (ForestZeroChannelEmit.stored_from_dictionary state.heap dictionary layout represented
      within base queue fifo localFit)
    position running zero remaining tableWord one decrement offWord channelsFit heapFits
    emitCapacity emitAt setupAt loopAt cleanupCapacity countFits saved allocated

end Controller.Cost.ForestZeroAnswerReclaim
