module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestZeroOutcome

public import Mathlib.Tactic.FinCases

@[expose] public section

/-! Fixed fetched answer blocks emit one Boolean decision word and return to
caller code while retaining the physical query source and model flags. -/
set_option autoImplicit false
namespace Controller.Cost.ForestZeroAnswer
open Controller.Cost Controller.Cost.ForestZeroBackendFrame
variable {width : Nat}

def code (width value returnPc : Nat) : Program width 8 :=
  #[.constant 0 (word width value), .emit 0,
    .constant 0 (word width 0), .branchZero 0 (word width returnPc)]

def At (program : Program width 8) (entry value returnPc : Nat) : Prop :=
  ∀ phase : Fin 4, program[entry + phase.val]? = (code width value returnPc)[phase.val]?

private theorem fetched (program : Program width 8) (state : State width 8)
    (entry : Nat) (instruction : Instruction width 8)
    (position : state.pc = word width entry) (fits : entry < 2 ^ width)
    (present : program[entry]? = some instruction) :
    programStep program state = step instruction state := by
  unfold programStep
  rw [position, show (word width entry).val = entry from Nat.mod_eq_of_lt fits, present]
  rfl

private theorem advance_pc (state : State width 8) (entry : Nat)
    (position : state.pc = word width entry) (fits : entry < 2 ^ width) :
    state.advance.pc = word width (entry + 1) := by
  simp only [State.advance, position, show (word width entry).val = entry from Nat.mod_eq_of_lt fits]

theorem execution (prefixSize : Nat) (program : Program width 8)
    (entry value returnPc : Nat) (state : State width 8)
    (present : At program entry value returnPc)
    (position : state.pc = word width entry) (running : state.halted = false)
    (capacity : entry + 4 < 2 ^ width) (returnCapacity : returnPc < 2 ^ width)
    (prefixBound : prefixSize ≤ state.heap.size) :
    ∃ final, Execution program state final 4 (state.liveWords + 1) ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧
      final.output = word width value :: state.output ∧
      final.pc = word width returnPc ∧ final.halted = false ∧
      PrefixFrame prefixSize state.heap final.heap := by
  obtain ⟨middle, first, heap, stack, output, _, pc, live⟩ :=
    Controller.Horn.WorklistAccept.tag_execution program entry value state
      (by simpa [At, code] using present ⟨0, by decide⟩)
      (by simpa [At, code] using present ⟨1, by decide⟩)
      position running (by omega)
  let cleared := middle.advance.put 0 (word width 0)
  let final : State width 8 := { cleared.advance with pc := word width returnPc }
  have step2 : programStep program middle = some cleared := by
    rw [fetched program middle (entry + 2) (.constant 0 (word width 0)) pc (by omega)
      (by simpa [At, code] using present ⟨2, by decide⟩)]
    simp [step, cleared, live]
  have pc3 : cleared.pc = word width (entry + 3) := by
    simpa [cleared, State.put, Nat.add_assoc, State.put] using advance_pc middle (entry + 2) pc (by omega)
  have step3 : programStep program cleared = some final := by
    rw [fetched program cleared (entry + 3) (.branchZero 0 (word width returnPc)) pc3 (by omega)
      (by simpa [At, code] using present ⟨3, by decide⟩)]
    simp [step, cleared, final, State.advance, State.put, live, word]
  have middleLive : middle.liveWords = state.liveWords + 1 := by
    unfold State.liveWords
    rw [heap, stack, output]
    simp
    omega
  have clearLive : cleared.liveWords = middle.liveWords := rfl
  have finalLive : final.liveWords = middle.liveWords := rfl
  have last : Execution program middle final 2 middle.liveWords := by
    simpa only [clearLive, finalLive, Nat.max_self, Nat.zero_add, Nat.reduceAdd] using
      Execution.cons step2 (Execution.cons step3 (Execution.refl final))
  refine ⟨final, ?_, heap, stack, output, rfl, live, ?_⟩
  · simpa only [middleLive, Nat.max_self, Nat.reduceAdd] using first.append last
  · simpa only [final, cleared, State.advance, State.put, heap] using
      (Controller.Cost.ForestZeroBackendFrame.refl state.heap prefixBound)

open Controller.Horn Controller.Horn.WorklistMark Controller.Horn.WorklistFIFO
open Controller.Horn.WorklistOutcome Controller.Horn.WorklistPropagation
open Controller.Horn.WorklistPropagationStep Controller.Horn.WorklistStorage
open Controller.Horn.WorklistFIFORun Controller.Horn.WorklistSeed
variable {n : Nat}

theorem initialized_answer_execution (prefixSize : Nat) (formula : Controller.CNF.Formula (Fin n)) (dual : Controller.Horn.DualHorn formula)
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
    (returnPc : Nat) (successAt : At program fifoDone 1 returnPc)
    (conflictAt : At program conflict 0 returnPc)
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
      (answer = true → Controller.CNF.Satisfies (offAssignment finalQueue) formula) := by
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
      execution prefixSize program conflict 0 returnPc middle conflictAt pc live conflictCapacity returnCapacity firstFrame.2.1
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
      execution prefixSize program fifoDone 1 returnPc middle successAt finished.position finished.running
        successCapacity returnCapacity firstFrame.2.1
    refine ⟨true, queue, final, firstTicks + 4, by omega, ?_, ?_, stack.trans middleStack,
      ?_, finalPC, finalRunning, Controller.Cost.ForestZeroBackendFrame.trans firstFrame lastFrame, ?_, ?_⟩
    · simpa only [middleLive, show max state.liveWords (state.liveWords + 1) = state.liveWords + 1 by omega] using first.append last
    · rw [heap]; exact middleSize
    · simpa only [↓reduceIte, middleOutput] using output
    · exact ⟨fun _ => ⟨offAssignment queue, model⟩, fun _ => rfl⟩
    · exact fun _ => model


/-- Preserve the fetched answer tag beneath the four physical reset words. -/
def saveTagCode (width : Nat) : Program width 8 :=
  #[.pop 6, .pop 4, .pop 3, .pop 7, .push 0, .push 7, .push 3, .push 4, .push 6]

theorem save_tag_execution (program : Program width 8) (state : State width 8)
    (entry : Nat) (count inverse localCount queryBase : Word width)
    (rest : List (Word width))
    (saved : state.stack = count :: inverse :: localCount :: queryBase :: rest)
    (position : state.pc = word width entry) (running : state.halted = false)
    (capacity : entry + 9 < 2 ^ width)
    (present : ∀ phase : Fin 9, program[entry + phase.val]? = (saveTagCode width)[phase.val]?) :
    ∃ final, Execution program state final 9 (state.liveWords + 1) ∧
      final.heap = state.heap ∧ final.output = state.output ∧
      final.stack = count :: inverse :: localCount :: queryBase :: state.reg 0 :: rest ∧
      final.reg 0 = state.reg 0 ∧ final.reg 5 = state.reg 5 ∧
      final.pc = word width (entry + 9) ∧ final.halted = false := by
  let s1 : State width 8 := { state.advance.put 6 count with stack := inverse :: localCount :: queryBase :: rest }
  let s2 : State width 8 := { s1.advance.put 4 inverse with stack := localCount :: queryBase :: rest }
  let s3 : State width 8 := { s2.advance.put 3 localCount with stack := queryBase :: rest }
  let s4 : State width 8 := { s3.advance.put 7 queryBase with stack := rest }
  let s5 : State width 8 := { s4.advance with stack := s4.reg 0 :: s4.stack }
  let s6 : State width 8 := { s5.advance with stack := s5.reg 7 :: s5.stack }
  let s7 : State width 8 := { s6.advance with stack := s6.reg 3 :: s6.stack }
  let s8 : State width 8 := { s7.advance with stack := s7.reg 4 :: s7.stack }
  let s9 : State width 8 := { s8.advance with stack := s8.reg 6 :: s8.stack }
  have t0 : programStep program state = some s1 := by
    rw [fetched program state (entry + 0) (.pop 6) position (by omega)
      (by simpa [saveTagCode] using present ⟨0, by decide⟩)]
    simp [step, s1, State.put, State.advance, saved, running]
  have pc1 : s1.pc = word width (entry + 1) := by
    simpa [s1, Nat.add_assoc, State.put] using advance_pc state (entry + 0) position (by omega)
  have run1 : s1.halted = false := by simp [s1, State.put, State.advance, running]
  have t1 : programStep program s1 = some s2 := by
    rw [fetched program s1 (entry + 1) (.pop 4) pc1 (by omega)
      (by simpa [saveTagCode] using present ⟨1, by decide⟩)]
    simp [step, s1, s2, State.put, State.advance, saved, running]
  have pc2 : s2.pc = word width (entry + 2) := by
    simpa [s2, Nat.add_assoc, State.put] using advance_pc s1 (entry + 1) pc1 (by omega)
  have run2 : s2.halted = false := by simp [s1, s2, State.put, State.advance, running]
  have t2 : programStep program s2 = some s3 := by
    rw [fetched program s2 (entry + 2) (.pop 3) pc2 (by omega)
      (by simpa [saveTagCode] using present ⟨2, by decide⟩)]
    simp [step, s1, s2, s3, State.put, State.advance, saved, running]
  have pc3 : s3.pc = word width (entry + 3) := by
    simpa [s3, Nat.add_assoc, State.put] using advance_pc s2 (entry + 2) pc2 (by omega)
  have run3 : s3.halted = false := by simp [s1, s2, s3, State.put, State.advance, running]
  have t3 : programStep program s3 = some s4 := by
    rw [fetched program s3 (entry + 3) (.pop 7) pc3 (by omega)
      (by simpa [saveTagCode] using present ⟨3, by decide⟩)]
    simp [step, s1, s2, s3, s4, State.put, State.advance, saved, running]
  have pc4 : s4.pc = word width (entry + 4) := by
    simpa [s4, Nat.add_assoc, State.put] using advance_pc s3 (entry + 3) pc3 (by omega)
  have run4 : s4.halted = false := by simp [s1, s2, s3, s4, State.put, State.advance, running]
  have t4 : programStep program s4 = some s5 := by
    rw [fetched program s4 (entry + 4) (.push 0) pc4 (by omega)
      (by simpa [saveTagCode] using present ⟨4, by decide⟩)]
    simp [step, s1, s2, s3, s4, s5, State.put, State.advance, saved, running]
  have pc5 : s5.pc = word width (entry + 5) := by
    simpa [s5, Nat.add_assoc, State.put] using advance_pc s4 (entry + 4) pc4 (by omega)
  have run5 : s5.halted = false := by simp [s1, s2, s3, s4, s5, State.put, State.advance, running]
  have t5 : programStep program s5 = some s6 := by
    rw [fetched program s5 (entry + 5) (.push 7) pc5 (by omega)
      (by simpa [saveTagCode] using present ⟨5, by decide⟩)]
    simp [step, s1, s2, s3, s4, s5, s6, State.put, State.advance, saved, running]
  have pc6 : s6.pc = word width (entry + 6) := by
    simpa [s6, Nat.add_assoc, State.put] using advance_pc s5 (entry + 5) pc5 (by omega)
  have run6 : s6.halted = false := by simp [s1, s2, s3, s4, s5, s6, State.put, State.advance, running]
  have t6 : programStep program s6 = some s7 := by
    rw [fetched program s6 (entry + 6) (.push 3) pc6 (by omega)
      (by simpa [saveTagCode] using present ⟨6, by decide⟩)]
    simp [step, s1, s2, s3, s4, s5, s6, s7, State.put, State.advance, saved, running]
  have pc7 : s7.pc = word width (entry + 7) := by
    simpa [s7, Nat.add_assoc, State.put] using advance_pc s6 (entry + 6) pc6 (by omega)
  have run7 : s7.halted = false := by simp [s1, s2, s3, s4, s5, s6, s7, State.put, State.advance, running]
  have t7 : programStep program s7 = some s8 := by
    rw [fetched program s7 (entry + 7) (.push 4) pc7 (by omega)
      (by simpa [saveTagCode] using present ⟨7, by decide⟩)]
    simp [step, s1, s2, s3, s4, s5, s6, s7, s8, State.put, State.advance, saved, running]
  have pc8 : s8.pc = word width (entry + 8) := by
    simpa [s8, Nat.add_assoc, State.put] using advance_pc s7 (entry + 7) pc7 (by omega)
  have run8 : s8.halted = false := by simp [s1, s2, s3, s4, s5, s6, s7, s8, State.put, State.advance, running]
  have t8 : programStep program s8 = some s9 := by
    rw [fetched program s8 (entry + 8) (.push 6) pc8 (by omega)
      (by simpa [saveTagCode] using present ⟨8, by decide⟩)]
    simp [step, s1, s2, s3, s4, s5, s6, s7, s8, s9, State.put, State.advance, saved, running]
  have pc9 : s9.pc = word width (entry + 9) := by
    simpa [s9, Nat.add_assoc, State.put] using advance_pc s8 (entry + 8) pc8 (by omega)
  have run9 : s9.halted = false := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, State.put, State.advance, running]
  refine ⟨s9, ?_, ?_, ?_, ?_, ?_, ?_, pc9, run9⟩
  · have trace := Execution.cons t0 (Execution.cons t1 (Execution.cons t2 (Execution.cons t3 (Execution.cons t4 (Execution.cons t5 (Execution.cons t6 (Execution.cons t7 (Execution.cons t8 (Execution.refl s9)))))))))
    convert trace using 1 <;> simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, State.liveWords, State.put, State.advance, saved, Nat.max_assoc] <;> omega
  all_goals simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, State.put, State.advance]


/-- The decision tag is stored on the stack before projection and reclamation. -/
def savedCode (width value returnPc : Nat) : Program width 8 :=
  #[.constant 0 (word width value), .emit 0] ++ saveTagCode width ++
    #[.constant 0 (word width 0), .branchZero 0 (word width returnPc)]

def SavedAt (program : Program width 8) (entry value returnPc : Nat) : Prop :=
  ∀ phase : Fin 13, program[entry + phase.val]? = (savedCode width value returnPc)[phase.val]?

theorem saved_execution (program : Program width 8) (state : State width 8)
    (entry value returnPc : Nat) (count inverse localCount queryBase : Word width)
    (rest : List (Word width))
    (saved : state.stack = count :: inverse :: localCount :: queryBase :: rest)
    (position : state.pc = word width entry) (running : state.halted = false)
    (capacity : entry + 13 < 2 ^ width) (present : SavedAt program entry value returnPc) :
    ∃ final, Execution program state final 13 (state.liveWords + 2) ∧
      final.heap = state.heap ∧
      final.output = word width value :: state.output ∧
      final.stack = count :: inverse :: localCount :: queryBase :: word width value :: rest ∧
      final.reg 5 = state.reg 5 ∧
      final.pc = word width returnPc ∧ final.halted = false := by
  let first := state.advance.put 0 (word width value)
  let tagged : State width 8 := { first.advance with output := word width value :: state.output }
  have pc1 : first.pc = word width (entry + 1) := by
    simpa [first, State.put] using advance_pc state entry position (by omega)
  have pc2 : tagged.pc = word width (entry + 2) := by
    simpa [tagged, Nat.add_assoc] using advance_pc first (entry + 1) pc1 (by omega)
  have t0 : programStep program state = some first := by
    rw [fetched program state entry (.constant 0 (word width value)) position (by omega)
      (by simpa [SavedAt, savedCode, saveTagCode] using present ⟨0, by decide⟩)]
    simp [step, first, running]
  have t1 : programStep program first = some tagged := by
    rw [fetched program first (entry + 1) (.emit 0) pc1 (by omega)
      (by simpa [SavedAt, savedCode, saveTagCode] using present ⟨1, by decide⟩)]
    simp [step, first, tagged, State.put, State.advance, running]
  have taggedLive : tagged.liveWords = state.liveWords + 1 := by
    simp [tagged, first, State.liveWords, State.put, State.advance]
    omega
  have firstTrace : Execution program state tagged 2 (state.liveWords + 1) := by
    convert Execution.cons t0 (Execution.cons t1 (Execution.refl tagged)) using 1 <;>
      simp [first, tagged, State.liveWords, State.put, State.advance] <;> omega
  have saveAt : ∀ phase : Fin 9,
      program[entry + 2 + phase.val]? = (saveTagCode width)[phase.val]? := by
    intro phase
    have original := present ⟨2 + phase.val, by omega⟩
    fin_cases phase <;> simpa [savedCode, saveTagCode, Nat.add_assoc] using original
  obtain ⟨middle, save, heap, output, stack, reg0, reg5, pc, live⟩ :=
    save_tag_execution program tagged (entry + 2) count inverse localCount queryBase rest
      (by simpa [tagged, first, State.advance, State.put] using saved)
      pc2 (by simp [tagged, first, State.advance, State.put, running]) (by omega) saveAt
  let cleared := middle.advance.put 0 (word width 0)
  let final : State width 8 := { cleared.advance with pc := word width returnPc }
  have clearPc : cleared.pc = word width (entry + 12) := by
    simpa [cleared, State.put, Nat.add_assoc] using advance_pc middle (entry + 2 + 9) pc (by omega)
  have t11 : programStep program middle = some cleared := by
    rw [fetched program middle (entry + 11) (.constant 0 (word width 0))
      (by simpa [Nat.add_assoc] using pc) (by omega)
      (by simpa [SavedAt, savedCode, saveTagCode] using present ⟨11, by decide⟩)]
    simp [step, cleared, live]
  have t12 : programStep program cleared = some final := by
    rw [fetched program cleared (entry + 12) (.branchZero 0 (word width returnPc))
      clearPc (by omega)
      (by simpa [SavedAt, savedCode, saveTagCode] using present ⟨12, by decide⟩)]
    simp [step, cleared, final, State.advance, State.put, live, word]
  have middleLive : middle.liveWords = state.liveWords + 2 := by
    simp only [State.liveWords, heap, output, stack]
    simp [tagged, first, State.advance, State.put, State.liveWords, saved]
    omega
  have suffix : Execution program middle final 2 middle.liveWords := by
    simpa only [cleared, final, State.liveWords, State.advance, State.put, Nat.max_self,
      Nat.zero_add, Nat.reduceAdd] using Execution.cons t11 (Execution.cons t12 (Execution.refl final))
  refine ⟨final, ?_, ?_, ?_, ?_, ?_, rfl, ?_⟩
  · simpa only [taggedLive, middleLive, Nat.reduceAdd,
      show max (state.liveWords + 1) (state.liveWords + 2) = state.liveWords + 2 by omega,
      Nat.max_self] using (firstTrace.append save).append suffix
  · simpa [final, cleared, State.advance, State.put, tagged, first] using heap
  · simpa [final, cleared, State.advance, State.put, tagged] using output
  · simpa [final, cleared, State.advance, State.put, reg0, tagged, first] using stack
  · simpa [final, cleared, State.advance, State.put, tagged, first] using reg5
  · simp [final, cleared, State.advance, State.put, live]

end Controller.Cost.ForestZeroAnswer
