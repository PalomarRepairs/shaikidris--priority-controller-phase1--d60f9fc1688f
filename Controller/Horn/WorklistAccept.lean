module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.Horn
public import Controller.Horn.WorklistSeedRun
public import Controller.Horn.WorklistOutcome

@[expose] public section

/-! The complete physical worklist program retains original normalized rows
and linked occurrences from cold input through its emitted observable result. -/
namespace Controller.Horn.WorklistAccept
open Controller.Cost Controller.Horn.WorklistMark Controller.Horn.WorklistFIFO
open Controller.Horn.WorklistPropagation Controller.Horn.WorklistOutcome
open Controller.Horn.WorklistPropagationStep Controller.Horn.WorklistStorage
variable {width n : Nat}

/-- Reuse the seed comparison header as the actual FIFO head cursor. -/
def headSetupCode (width base fetch : Nat) : Program width 8 :=
  #[.constant 3 (word width (headSlot (n := n) base)),
    .constant 0 (word width (queueStart (n := n) base)), .store 3 0,
    .branchZero 2 (word width fetch)]

@[simp] theorem head_setup_size (width base fetch : Nat) :
    (headSetupCode (n := n) width base fetch).size = 4 := rfl

private theorem word_val (value : Nat) (fits : value < 2 ^ width) :
    (word width value).val = value := Nat.mod_eq_of_lt fits

private theorem fetched (program : Program width 8) (state : State width 8)
    (entry : Nat) (instruction : Instruction width 8)
    (position : state.pc = word width entry) (fits : entry < 2 ^ width)
    (present : program[entry]? = some instruction) :
    programStep program state = step instruction state := by
  unfold programStep
  rw [position, word_val entry fits, present]
  rfl

private theorem advance_pc (state : State width 8) (entry : Nat)
    (position : state.pc = word width entry) (fits : entry < 2 ^ width) :
    state.advance.pc = word width (entry + 1) := by
  simp only [State.advance, position, word_val entry fits]

/-- Four fetched instructions initialize the FIFO head without allocating or
changing original records, then enter the FIFO fetch loop. -/
theorem head_setup_execution (program : Program width 8) (base entry scan : Nat)
    (state : State width 8)
    (present : ∀ phase : Fin 4, program[entry + phase.val]? =
      (headSetupCode (n := n) width base scan)[phase.val]?)
    (position : state.pc = word width entry) (running : state.halted = false)
    (zero : state.reg 2 = word width 0)
    (capacity : entry + 4 < 2 ^ width)
    (headBound : headSlot (n := n) base < state.heap.size)
    (room : state.heap.size < 2 ^ width) :
    ∃ final, Execution program state final 4 state.liveWords ∧
      final.heap = state.heap.set (headSlot (n := n) base)
        (word width (queueStart (n := n) base)) headBound ∧
      final.pc = word width scan ∧ final.halted = false ∧
      final.reg 1 = state.reg 1 ∧ final.reg 2 = state.reg 2 ∧
      final.reg 5 = state.reg 5 ∧ final.reg 6 = state.reg 6 ∧
      final.heap.size = state.heap.size ∧ final.stack = state.stack ∧ final.output = state.output := by
  let first := state.advance.put 3 (word width (headSlot (n := n) base))
  let second := first.advance.put 0 (word width (queueStart (n := n) base))
  let third : State width 8 := { second.advance with
    heap := state.heap.set (headSlot (n := n) base) (word width (queueStart (n := n) base)) headBound }
  let final : State width 8 := { third.advance with pc := word width scan }
  have pc1 : first.pc = word width (entry + 1) := advance_pc state entry position (by omega)
  have pc2 : second.pc = word width (entry + 2) := by
    simpa [second, State.put, Nat.add_assoc] using advance_pc first (entry + 1) pc1 (by omega)
  have pc3 : third.pc = word width (entry + 3) := by
    simpa [third, Nat.add_assoc] using advance_pc second (entry + 2) pc2 (by omega)
  have step1 : programStep program state = some first := by
    rw [fetched program state entry (.constant 3 (word width (headSlot (n := n) base))) position
      (by omega) (by simpa [headSetupCode] using present ⟨0, by decide⟩)]
    simp [step, running, first]
  have step2 : programStep program first = some second := by
    rw [fetched program first (entry + 1) (.constant 0 (word width (queueStart (n := n) base))) pc1
      (by omega) (by simpa [headSetupCode] using present ⟨1, by decide⟩)]
    simp [step, first, second, State.put, State.advance, running]
  have step3 : programStep program second = some third := by
    rw [fetched program second (entry + 2) (.store 3 0) pc2 (by omega)
      (by simpa [headSetupCode] using present ⟨2, by decide⟩)]
    have addressFits : headSlot (n := n) base < 2 ^ width := by omega
    simp [step, first, second, third, State.put, State.advance, running,
      word_val (headSlot (n := n) base) addressFits, headBound]
  have step4 : programStep program third = some final := by
    rw [fetched program third (entry + 3) (.branchZero 2 (word width scan)) pc3 (by omega)
      (by simpa [headSetupCode] using present ⟨3, by decide⟩)]
    simp [step, first, second, third, final, State.put, State.advance, running, zero, word]
  refine ⟨final, ?_, rfl, rfl, running, ?_, ?_, ?_, ?_, ?_, rfl, rfl⟩
  · simpa [first, second, third, final, State.put, State.advance, State.liveWords] using
      Execution.cons step1 (Execution.cons step2 (Execution.cons step3
        (Execution.cons step4 (Execution.refl final))))
  all_goals simp [first, second, third, final, State.put, State.advance]


/-- The completed original-row scan enters the physical FIFO after the fetched
head-header store; its semantic facts retain the original rows and pending queue. -/
theorem seed_to_fifo (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base entry fetch : Nat) (program : Program width 8)
    (queue : List (Fin n)) (fired : Fin clauses.length → Bool) (state : State width 8)
    (seed : Controller.Horn.WorklistSeedRun.ScanInvariant clauses recordStart recordEnd base entry
      clauses.length queue fired state)
    (separated : base + 5 * n + 4 ≤ recordStart)
    (present : ∀ phase : Fin 4, program[entry + phase.val]? =
      (headSetupCode (n := n) width base fetch)[phase.val]?)
    (capacity : entry + 4 < 2 ^ width) :
    ∃ final, Execution program state final 4 state.liveWords ∧
      Controller.Horn.WorklistFIFORun.Ready clauses recordStart recordEnd base fetch queue 0 fired final ∧
      ProcessedComplete clauses recordStart queue 0 none [] fired ∧
      FiredMeaning clauses queue fired ∧ Controller.Horn.WorklistSeed.QueueForced clauses queue ∧
      final.heap.size = state.heap.size ∧ final.stack = state.stack ∧ final.output = state.output := by
  have headBound : headSlot (n := n) base < state.heap.size := by
    have := seed.fifo.fits
    unfold headSlot
    omega
  obtain ⟨final, trace, heap, pc, running, row, zero, one, decrement, size, stack, output⟩ :=
    head_setup_execution program base entry fetch state present seed.position seed.running seed.zero
      capacity headBound seed.room
  have originalRows : ∀ index : Fin clauses.length,
      Controller.Horn.WorklistStorage.MutableStored (Controller.Horn.Worklist.compileClause clauses[index.val])
        (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val)
        (remaining (Controller.Horn.Worklist.compileClause clauses[index.val]) (queue.take 0)) (fired index) state.heap := by
    intro index
    simpa [remaining] using seed.rows index
  obtain ⟨spine, fifo, rows⟩ := head_store_frame clauses recordStart recordEnd base queue
    (fun index => remaining (Controller.Horn.Worklist.compileClause clauses[index.val]) (queue.take 0))
    fired state.heap (word width (queueStart (n := n) base)) seed.spine seed.fifo originalRows separated
  have firedZero : FiredZero clauses recordStart queue 0 none [] fired := by
    intro index marked
    simpa [remaining, processedForRow] using seed.firedEmpty index marked
  have headValue : final.heap[headSlot (n := n) base]? = some (word width (queueStart (n := n) base + 0)) := by
    rw [heap]
    simp
  have tailValue : final.heap[Controller.Horn.WorklistBucketReady.tailSlot (n := n) base]? =
      some (word width (queueStart (n := n) base + queue.length)) := by
    rw [heap]
    exact (Array.getElem?_set_ne headBound (by unfold headSlot Controller.Horn.WorklistBucketReady.tailSlot; omega)).trans seed.tail
  refine ⟨final, trace, ?_, ?_, seed.firedHead, seed.forced, size, stack, output⟩
  · refine ⟨?_, ?_, Nat.zero_le _, ?_, firedZero, headValue, tailValue,
      zero.trans seed.zero, one.trans seed.one, decrement.trans seed.decrement,
      pc, running, ?_⟩
    · simpa only [heap] using spine
    · simpa only [heap] using fifo
    · intro index; simpa only [heap] using rows index
    · simpa only [size] using seed.room
  · intro index enabled countZero
    apply seed.complete index index.isLt enabled
    simpa [processedForRow, remaining] using countZero

/-- Read and complement the actual off flag before emitting the assignment bit. -/
def emitCell (width address : Nat) : Program width 8 :=
  #[.constant 0 (word width address), .load 1 0, .xor 1 1 5, .emit 1]

def EmitAt (program : Program width 8) (entry address : Nat) : Prop :=
  ∀ phase : Fin 4, program[entry + phase.val]? = (emitCell width address)[phase.val]?

/-- Four fetched instructions emit a Boolean complement of a stored off flag,
charging the additional output word to the peak. -/
theorem emit_cell_execution (program : Program width 8) (entry address : Nat)
    (state : State width 8) (marked : Bool)
    (present : EmitAt program entry address)
    (position : state.pc = word width entry) (running : state.halted = false)
    (one : state.reg 5 = word width 1)
    (bound : address < state.heap.size)
    (value : state.heap[address]'bound = word width (if marked then 1 else 0))
    (room : state.heap.size < 2 ^ width) (capacity : entry + 4 < 2 ^ width)
    (oneFits : 1 < 2 ^ width) :
    ∃ final, Execution program state final 4 (state.liveWords + 1) ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧
      final.output = word width (if marked then 0 else 1) :: state.output ∧
      final.reg 5 = state.reg 5 ∧ final.pc = word width (entry + 4) ∧ final.halted = false := by
  let first := state.advance.put 0 (word width address)
  let second := first.advance.put 1 (word width (if marked then 1 else 0))
  let third := second.advance.put 1 (word width (if marked then 0 else 1))
  let final : State width 8 := { third.advance with
    output := word width (if marked then 0 else 1) :: state.output }
  have pc1 : first.pc = word width (entry + 1) := advance_pc state entry position (by omega)
  have pc2 : second.pc = word width (entry + 2) := by
    simpa [second, State.put, Nat.add_assoc] using advance_pc first (entry + 1) pc1 (by omega)
  have pc3 : third.pc = word width (entry + 3) := by
    simpa [third, State.put, Nat.add_assoc] using advance_pc second (entry + 2) pc2 (by omega)
  have step1 : programStep program state = some first := by
    rw [fetched program state entry (.constant 0 (word width address)) position (by omega)
      (by simpa [emitCell] using present ⟨0, by decide⟩)]
    simp [step, first, running]
  have step2 : programStep program first = some second := by
    rw [fetched program first (entry + 1) (.load 1 0) pc1 (by omega)
      (by simpa [emitCell] using present ⟨1, by decide⟩)]
    simp [step, first, second, State.put, State.advance, running, value, bound,
      word_val (width := width) address (by omega)]
  have step3 : programStep program second = some third := by
    rw [fetched program second (entry + 2) (.xor 1 1 5) pc2 (by omega)
      (by simpa [emitCell] using present ⟨2, by decide⟩)]
    cases marked <;> simp [step, first, second, third, State.put, State.advance,
      running, one, word_val 1 oneFits, word, Nat.mod_eq_of_lt oneFits]
  have step4 : programStep program third = some final := by
    rw [fetched program third (entry + 3) (.emit 1) pc3 (by omega)
      (by simpa [emitCell] using present ⟨3, by decide⟩)]
    simp [step, first, second, third, final, State.put, State.advance, running]
  have live1 : first.liveWords = state.liveWords := rfl
  have live2 : second.liveWords = state.liveWords := rfl
  have live3 : third.liveWords = state.liveWords := rfl
  have live4 : final.liveWords = state.liveWords + 1 := by
    simp [final, third, second, first, State.liveWords, State.put, State.advance]
    omega
  refine ⟨final, ?_, rfl, rfl, rfl, ?_, ?_, running⟩
  · have trace := Execution.cons step1 (Execution.cons step2
      (Execution.cons step3 (Execution.cons step4 (Execution.refl final))))
    simpa only [live1, live2, live3, live4, Nat.zero_add, Nat.add_zero,
      show max state.liveWords (state.liveWords + 1) = state.liveWords + 1 by omega] using trace
  · simp [final, third, second, first, State.put, State.advance]
  · simpa [final, Nat.add_assoc] using advance_pc third (entry + 3) pc3 (by omega)

/-- The stored marked flag is the complement of the greatest assignment bit. -/
theorem emit_off_execution (program : Program width 8) (entry base : Nat)
    (queue : List (Fin n)) (label : Fin n) (state : State width 8)
    (fifo : Stored queue base state.heap)
    (present : EmitAt program entry (offAddress base label))
    (position : state.pc = word width entry) (running : state.halted = false)
    (one : state.reg 5 = word width 1) (room : state.heap.size < 2 ^ width)
    (capacity : entry + 4 < 2 ^ width) (oneFits : 1 < 2 ^ width) :
    ∃ final, Execution program state final 4 (state.liveWords + 1) ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧
      final.output = word width (if offAssignment queue label then 1 else 0) :: state.output ∧
      final.reg 5 = state.reg 5 ∧ final.pc = word width (entry + 4) ∧ final.halted = false := by
  have bound : offAddress base label < state.heap.size := by
    have := fifo.fits
    have := label.isLt
    unfold offAddress
    omega
  have value : state.heap[offAddress base label]'bound =
      word width (if decide (label ∈ queue) then 1 else 0) := by
    simpa only [decide_eq_true_eq] using fifo.flags label
  obtain ⟨final, trace, heap, stack, output, heldOne, pc, finalRunning⟩ :=
    emit_cell_execution program entry (offAddress base label) state (decide (label ∈ queue))
      present position running one bound value room capacity oneFits
  refine ⟨final, trace, heap, stack, ?_, heldOne, pc, finalRunning⟩
  by_cases member : label ∈ queue <;> simpa [offAssignment, member] using output


def emitCode (width base : Nat) (labels : List (Fin n)) : Program width 8 :=
  labels.foldr (fun label rest => emitCell width (offAddress base label) ++ rest) #[]

@[simp] theorem emit_code_size (width base : Nat) (labels : List (Fin n)) :
    (emitCode width base labels).size = 4 * labels.length := by
  induction labels with
  | nil => rfl
  | cons label rest ih =>
    change (emitCell width (offAddress base label) ++ emitCode width base rest).size = 4 * (label :: rest).length
    rw [Array.size_append, ih]
    simp [emitCell]
    omega

def EmitCodeAt (program : Program width 8) (entry base : Nat) (labels : List (Fin n)) : Prop :=
  ∀ phase : Nat, phase < 4 * labels.length →
    program[entry + phase]? = (emitCode width base labels)[phase]?

/-- The fetched output pass visits every supplied declared label once; heap and
pending marks remain the actual terminal FIFO's stored values. -/
theorem emit_code_execution (program : Program width 8) (entry base : Nat)
    (labels : List (Fin n)) (queue : List (Fin n)) (state : State width 8)
    (fifo : Stored queue base state.heap) (present : EmitCodeAt program entry base labels)
    (position : state.pc = word width entry) (running : state.halted = false)
    (one : state.reg 5 = word width 1) (room : state.heap.size < 2 ^ width)
    (capacity : entry + 4 * labels.length < 2 ^ width) (oneFits : 1 < 2 ^ width) :
    ∃ final, Execution program state final (4 * labels.length) (state.liveWords + labels.length) ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧
      final.output = (labels.map (fun label => word width (if offAssignment queue label then 1 else 0))).reverse ++ state.output ∧
      final.reg 5 = state.reg 5 ∧ final.pc = word width (entry + 4 * labels.length) ∧ final.halted = false := by
  induction labels generalizing state entry with
  | nil =>
    refine ⟨state, ?_, rfl, rfl, by simp, rfl, ?_, running⟩
    · simpa using Execution.refl (p := program) state
    · simpa using position
  | cons label rest ih =>
    have firstAt : EmitAt program entry (offAddress base label) := by
      intro phase
      have available := present phase.val (by have := phase.isLt; simp only [List.length_cons]; omega)
      change program[entry + phase.val]? = (emitCell width (offAddress base label))[phase.val]?
      change program[entry + phase.val]? =
        (emitCell width (offAddress base label) ++ emitCode width base rest)[phase.val]? at available
      rw [Array.getElem?_append_left (by simpa [emitCell] using phase.isLt)] at available
      exact available
    obtain ⟨middle, first, heap, stack, output, heldOne, pc, middleRunning⟩ :=
      emit_off_execution program entry base queue label state fifo firstAt position running one room
        (by simp only [List.length_cons] at capacity; omega) oneFits
    have restAt : EmitCodeAt program (entry + 4) base rest := by
      intro phase inside
      have available := present (4 + phase) (by simp only [List.length_cons]; omega)
      change program[entry + (4 + phase)]? =
        (emitCell width (offAddress base label) ++ emitCode width base rest)[4 + phase]? at available
      rw [Array.getElem?_append_right (by simp [emitCell])] at available
      simpa only [show (emitCell width (offAddress base label)).size = 4 from rfl,
        Nat.add_sub_cancel_left, Nat.add_assoc] using available
    obtain ⟨final, last, finalHeap, finalStack, finalOutput, finalOne, finalPC, finalRunning⟩ :=
      ih (entry + 4) middle (by simpa only [heap] using fifo) restAt pc middleRunning
        (heldOne.trans one) (by simpa only [heap] using room)
        (by simp only [List.length_cons] at capacity; omega)
    have middleLive : middle.liveWords = state.liveWords + 1 := by
      simp only [State.liveWords, heap, stack, output, List.length_cons]
      omega
    refine ⟨final, ?_, finalHeap.trans heap, finalStack.trans stack, ?_, finalOne.trans heldOne, ?_, finalRunning⟩
    · have trace := first.append last
      simpa only [middleLive, List.length_cons, Nat.mul_add, Nat.mul_one,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
        show max (1 + state.liveWords) (rest.length + (1 + state.liveWords)) =
          rest.length + (1 + state.liveWords) by omega,
        show max (state.liveWords + 1) (state.liveWords + 1 + rest.length) =
          state.liveWords + 1 + rest.length by omega] using trace
    · rw [finalOutput, output]
      simp [List.reverse_cons, List.append_assoc]
    · simpa [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using finalPC


/-- The emitted result reaches an actual fetched halt instruction. -/
theorem halt_execution (program : Program width 8) (entry : Nat) (state : State width 8)
    (present : program[entry]? = some .halt) (position : state.pc = word width entry)
    (running : state.halted = false) (fits : entry < 2 ^ width) :
    ∃ final, Execution program state final 1 state.liveWords ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.halted = true := by
  let final : State width 8 := { state.advance with halted := true }
  have transition : programStep program state = some final := by
    rw [fetched program state entry .halt position fits present]
    simp [step, running, final]
  refine ⟨final, ?_, rfl, rfl, rfl, rfl⟩
  simpa [final, State.advance, State.liveWords] using
    Execution.cons transition (Execution.refl final)

/-- Declared labels are emitted in reverse traversal order because each fetched
emit prepends; the observable list therefore has ascending variable order. -/
def outputLabels (n : Nat) : List (Fin n) := (List.finRange n).reverse

@[simp] theorem output_labels_length (n : Nat) : (outputLabels n).length = n := by
  simp [outputLabels]

/-- All fetched phase addresses are relative to the actual cold program end. -/
def seedEnd (width : Nat) (clauses : List (Controller.CNF.Clause (Fin n))) : Nat :=
  Controller.Horn.IndexScanCold.entry width clauses + 88

def conflictEntry (width : Nat) (clauses : List (Controller.CNF.Clause (Fin n))) : Nat :=
  seedEnd width clauses + 64 + 4 * n

def tagCode (width value : Nat) : Program width 8 :=
  #[.constant 0 (word width value), .emit 0]

def haltCode (width : Nat) : Program width 8 := #[.halt]

def conflictCode (width : Nat) : Program width 8 :=
  #[.constant 0 (word width 0), .emit 0, .halt]

@[simp] theorem tag_code_size (width value : Nat) : (tagCode width value).size = 2 := rfl
@[simp] theorem halt_code_size (width : Nat) : (haltCode width).size = 1 := rfl
@[simp] theorem conflict_code_size (width : Nat) : (conflictCode width).size = 3 := rfl

private theorem chunk_projection (before chunk after : Program width 8) (phase : Nat)
    (inside : phase < chunk.size) :
    (before ++ chunk ++ after)[before.size + phase]? = chunk[phase]? := by
  rw [Array.getElem?_append_left (by simp only [Array.size_append]; omega)]
  rw [Array.getElem?_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left]

/-- The cold prefix remains opaque while projecting the small runtime sections. -/
@[irreducible] def coldPrefix (width : Nat)
    (clauses : List (Controller.CNF.Clause (Fin n))) : Program width 8 :=
  Controller.Horn.WorklistSeedRun.program width clauses (conflictEntry width clauses)

@[simp] theorem cold_prefix_size (width : Nat)
    (clauses : List (Controller.CNF.Clause (Fin n))) :
    (coldPrefix width clauses).size = seedEnd width clauses := by
  unfold coldPrefix
  simp [seedEnd]

@[irreducible] def sectionPrefix0 (width : Nat)
    (clauses : List (Controller.CNF.Clause (Fin n))) : Program width 8 :=
  (coldPrefix width clauses)

@[irreducible] def sectionPrefix1 (width : Nat)
    (clauses : List (Controller.CNF.Clause (Fin n))) : Program width 8 :=
  (coldPrefix width clauses) ++
      (headSetupCode (n := n) width (Controller.Horn.SourceSerialize.base clauses) (seedEnd width clauses + 4))

@[irreducible] def sectionPrefix2 (width : Nat)
    (clauses : List (Controller.CNF.Clause (Fin n))) : Program width 8 :=
  (coldPrefix width clauses) ++
      (headSetupCode (n := n) width (Controller.Horn.SourceSerialize.base clauses) (seedEnd width clauses + 4)) ++
      (Controller.Horn.WorklistFIFO.fetchCode (n := n) width (Controller.Horn.SourceSerialize.base clauses) (seedEnd width clauses + 4) (seedEnd width clauses + 61) (seedEnd width clauses + 18))

@[irreducible] def sectionPrefix3 (width : Nat)
    (clauses : List (Controller.CNF.Clause (Fin n))) : Program width 8 :=
  (coldPrefix width clauses) ++
      (headSetupCode (n := n) width (Controller.Horn.SourceSerialize.base clauses) (seedEnd width clauses + 4)) ++
      (Controller.Horn.WorklistFIFO.fetchCode (n := n) width (Controller.Horn.SourceSerialize.base clauses) (seedEnd width clauses + 4) (seedEnd width clauses + 61) (seedEnd width clauses + 18)) ++
      (Controller.Horn.WorklistBucketLoop.code width (seedEnd width clauses + 18) (seedEnd width clauses + 56) (seedEnd width clauses + 30))

@[irreducible] def sectionPrefix4 (width : Nat)
    (clauses : List (Controller.CNF.Clause (Fin n))) : Program width 8 :=
  (coldPrefix width clauses) ++
      (headSetupCode (n := n) width (Controller.Horn.SourceSerialize.base clauses) (seedEnd width clauses + 4)) ++
      (Controller.Horn.WorklistFIFO.fetchCode (n := n) width (Controller.Horn.SourceSerialize.base clauses) (seedEnd width clauses + 4) (seedEnd width clauses + 61) (seedEnd width clauses + 18)) ++
      (Controller.Horn.WorklistBucketLoop.code width (seedEnd width clauses + 18) (seedEnd width clauses + 56) (seedEnd width clauses + 30)) ++
      (Controller.Horn.WorklistBucketReady.code (n := n) width (Controller.Horn.SourceSerialize.base clauses) (seedEnd width clauses + 30) (seedEnd width clauses + 56) (conflictEntry width clauses) (seedEnd width clauses + 18))

@[irreducible] def sectionPrefix5 (width : Nat)
    (clauses : List (Controller.CNF.Clause (Fin n))) : Program width 8 :=
  (coldPrefix width clauses) ++
      (headSetupCode (n := n) width (Controller.Horn.SourceSerialize.base clauses) (seedEnd width clauses + 4)) ++
      (Controller.Horn.WorklistFIFO.fetchCode (n := n) width (Controller.Horn.SourceSerialize.base clauses) (seedEnd width clauses + 4) (seedEnd width clauses + 61) (seedEnd width clauses + 18)) ++
      (Controller.Horn.WorklistBucketLoop.code width (seedEnd width clauses + 18) (seedEnd width clauses + 56) (seedEnd width clauses + 30)) ++
      (Controller.Horn.WorklistBucketReady.code (n := n) width (Controller.Horn.SourceSerialize.base clauses) (seedEnd width clauses + 30) (seedEnd width clauses + 56) (conflictEntry width clauses) (seedEnd width clauses + 18)) ++
      (Controller.Horn.WorklistFIFO.advanceCode (n := n) width (Controller.Horn.SourceSerialize.base clauses) (seedEnd width clauses + 4))

@[irreducible] def sectionPrefix6 (width : Nat)
    (clauses : List (Controller.CNF.Clause (Fin n))) : Program width 8 :=
  (coldPrefix width clauses) ++
      (headSetupCode (n := n) width (Controller.Horn.SourceSerialize.base clauses) (seedEnd width clauses + 4)) ++
      (Controller.Horn.WorklistFIFO.fetchCode (n := n) width (Controller.Horn.SourceSerialize.base clauses) (seedEnd width clauses + 4) (seedEnd width clauses + 61) (seedEnd width clauses + 18)) ++
      (Controller.Horn.WorklistBucketLoop.code width (seedEnd width clauses + 18) (seedEnd width clauses + 56) (seedEnd width clauses + 30)) ++
      (Controller.Horn.WorklistBucketReady.code (n := n) width (Controller.Horn.SourceSerialize.base clauses) (seedEnd width clauses + 30) (seedEnd width clauses + 56) (conflictEntry width clauses) (seedEnd width clauses + 18)) ++
      (Controller.Horn.WorklistFIFO.advanceCode (n := n) width (Controller.Horn.SourceSerialize.base clauses) (seedEnd width clauses + 4)) ++
      (tagCode width 1) ++
      (emitCode width (Controller.Horn.SourceSerialize.base clauses) (outputLabels n))

@[irreducible] def sectionPrefix7 (width : Nat)
    (clauses : List (Controller.CNF.Clause (Fin n))) : Program width 8 :=
  (coldPrefix width clauses) ++
      (headSetupCode (n := n) width (Controller.Horn.SourceSerialize.base clauses) (seedEnd width clauses + 4)) ++
      (Controller.Horn.WorklistFIFO.fetchCode (n := n) width (Controller.Horn.SourceSerialize.base clauses) (seedEnd width clauses + 4) (seedEnd width clauses + 61) (seedEnd width clauses + 18)) ++
      (Controller.Horn.WorklistBucketLoop.code width (seedEnd width clauses + 18) (seedEnd width clauses + 56) (seedEnd width clauses + 30)) ++
      (Controller.Horn.WorklistBucketReady.code (n := n) width (Controller.Horn.SourceSerialize.base clauses) (seedEnd width clauses + 30) (seedEnd width clauses + 56) (conflictEntry width clauses) (seedEnd width clauses + 18)) ++
      (Controller.Horn.WorklistFIFO.advanceCode (n := n) width (Controller.Horn.SourceSerialize.base clauses) (seedEnd width clauses + 4)) ++
      (tagCode width 1) ++
      (emitCode width (Controller.Horn.SourceSerialize.base clauses) (outputLabels n)) ++
      (haltCode width)

@[irreducible] def sectionPrefix8 (width : Nat)
    (clauses : List (Controller.CNF.Clause (Fin n))) : Program width 8 :=
  (coldPrefix width clauses) ++
      (headSetupCode (n := n) width (Controller.Horn.SourceSerialize.base clauses) (seedEnd width clauses + 4)) ++
      (Controller.Horn.WorklistFIFO.fetchCode (n := n) width (Controller.Horn.SourceSerialize.base clauses) (seedEnd width clauses + 4) (seedEnd width clauses + 61) (seedEnd width clauses + 18)) ++
      (Controller.Horn.WorklistBucketLoop.code width (seedEnd width clauses + 18) (seedEnd width clauses + 56) (seedEnd width clauses + 30)) ++
      (Controller.Horn.WorklistBucketReady.code (n := n) width (Controller.Horn.SourceSerialize.base clauses) (seedEnd width clauses + 30) (seedEnd width clauses + 56) (conflictEntry width clauses) (seedEnd width clauses + 18)) ++
      (Controller.Horn.WorklistFIFO.advanceCode (n := n) width (Controller.Horn.SourceSerialize.base clauses) (seedEnd width clauses + 4)) ++
      (tagCode width 1)

@[simp] theorem sectionPrefix0_size (width : Nat)
    (clauses : List (Controller.CNF.Clause (Fin n))) :
    (sectionPrefix0 width clauses).size = seedEnd width clauses := by
  simp [sectionPrefix0, sectionPrefix0, sectionPrefix1, sectionPrefix2, sectionPrefix3, sectionPrefix4, sectionPrefix5, sectionPrefix6, sectionPrefix7, sectionPrefix8, seedEnd, conflictEntry] <;> omega

@[simp] theorem sectionPrefix1_size (width : Nat)
    (clauses : List (Controller.CNF.Clause (Fin n))) :
    (sectionPrefix1 width clauses).size = seedEnd width clauses + 4 := by
  simp [sectionPrefix1, sectionPrefix0, sectionPrefix1, sectionPrefix2, sectionPrefix3, sectionPrefix4, sectionPrefix5, sectionPrefix6, sectionPrefix7, sectionPrefix8, seedEnd, conflictEntry] <;> omega

@[simp] theorem sectionPrefix2_size (width : Nat)
    (clauses : List (Controller.CNF.Clause (Fin n))) :
    (sectionPrefix2 width clauses).size = seedEnd width clauses + 18 := by
  simp [sectionPrefix2, sectionPrefix0, sectionPrefix1, sectionPrefix2, sectionPrefix3, sectionPrefix4, sectionPrefix5, sectionPrefix6, sectionPrefix7, sectionPrefix8, seedEnd, conflictEntry] <;> omega

@[simp] theorem sectionPrefix3_size (width : Nat)
    (clauses : List (Controller.CNF.Clause (Fin n))) :
    (sectionPrefix3 width clauses).size = seedEnd width clauses + 30 := by
  simp [sectionPrefix3, sectionPrefix0, sectionPrefix1, sectionPrefix2, sectionPrefix3, sectionPrefix4, sectionPrefix5, sectionPrefix6, sectionPrefix7, sectionPrefix8, seedEnd, conflictEntry] <;> omega

@[simp] theorem sectionPrefix4_size (width : Nat)
    (clauses : List (Controller.CNF.Clause (Fin n))) :
    (sectionPrefix4 width clauses).size = seedEnd width clauses + 56 := by
  simp [sectionPrefix4, sectionPrefix0, sectionPrefix1, sectionPrefix2, sectionPrefix3, sectionPrefix4, sectionPrefix5, sectionPrefix6, sectionPrefix7, sectionPrefix8, seedEnd, conflictEntry] <;> omega

@[simp] theorem sectionPrefix5_size (width : Nat)
    (clauses : List (Controller.CNF.Clause (Fin n))) :
    (sectionPrefix5 width clauses).size = seedEnd width clauses + 61 := by
  simp [sectionPrefix5, sectionPrefix0, sectionPrefix1, sectionPrefix2, sectionPrefix3, sectionPrefix4, sectionPrefix5, sectionPrefix6, sectionPrefix7, sectionPrefix8, seedEnd, conflictEntry] <;> omega

@[simp] theorem sectionPrefix6_size (width : Nat)
    (clauses : List (Controller.CNF.Clause (Fin n))) :
    (sectionPrefix6 width clauses).size = seedEnd width clauses + 63 + 4 * n := by
  simp [sectionPrefix6, sectionPrefix0, sectionPrefix1, sectionPrefix2, sectionPrefix3, sectionPrefix4, sectionPrefix5, sectionPrefix6, sectionPrefix7, sectionPrefix8, seedEnd, conflictEntry] <;> omega

@[simp] theorem sectionPrefix7_size (width : Nat)
    (clauses : List (Controller.CNF.Clause (Fin n))) :
    (sectionPrefix7 width clauses).size = conflictEntry width clauses := by
  simp [sectionPrefix7, sectionPrefix0, sectionPrefix1, sectionPrefix2, sectionPrefix3, sectionPrefix4, sectionPrefix5, sectionPrefix6, sectionPrefix7, sectionPrefix8, seedEnd, conflictEntry] <;> omega

@[simp] theorem sectionPrefix8_size (width : Nat)
    (clauses : List (Controller.CNF.Clause (Fin n))) :
    (sectionPrefix8 width clauses).size = seedEnd width clauses + 63 := by
  simp [sectionPrefix8, sectionPrefix0, sectionPrefix1, sectionPrefix2, sectionPrefix3, sectionPrefix4, sectionPrefix5, sectionPrefix6, sectionPrefix7, sectionPrefix8, seedEnd, conflictEntry] <;> omega

/-- Normalization, seed scan, FIFO, original buckets and output share one fixed
instruction array. Its forward branches refer to this same array. -/
@[irreducible] def program (width : Nat) (clauses : List (Controller.CNF.Clause (Fin n))) : Program width 8 :=
  let base := Controller.Horn.SourceSerialize.base clauses
  let entry := seedEnd width clauses
  let conflict := conflictEntry width clauses
  coldPrefix width clauses ++
    headSetupCode (n := n) width base (entry + 4) ++
    Controller.Horn.WorklistFIFO.fetchCode (n := n) width base (entry + 4) (entry + 61) (entry + 18) ++
    Controller.Horn.WorklistBucketLoop.code width (entry + 18) (entry + 56) (entry + 30) ++
    Controller.Horn.WorklistBucketReady.code (n := n) width base (entry + 30) (entry + 56) conflict (entry + 18) ++
    Controller.Horn.WorklistFIFO.advanceCode (n := n) width base (entry + 4) ++
    tagCode width 1 ++
    emitCode width base (outputLabels n) ++ haltCode width ++
    conflictCode width

@[simp] theorem program_size (width : Nat) (clauses : List (Controller.CNF.Clause (Fin n))) :
    (program width clauses).size = seedEnd width clauses + 67 + 4 * n := by
  simp [program, Controller.Horn.WorklistSeedRun.program_size, seedEnd,
    Controller.Horn.WorklistFIFO.fetch_size, Controller.Horn.WorklistBucketLoop.code,
    Controller.Horn.WorklistBucketReady.code, Controller.Horn.WorklistFIFO.advance_size]
  omega

theorem head_at (width : Nat) (clauses : List (Controller.CNF.Clause (Fin n))) :
    ∀ phase : Fin 4, (program width clauses)[seedEnd width clauses + phase.val]? = (headSetupCode (n := n) width (Controller.Horn.SourceSerialize.base clauses) (seedEnd width clauses + 4))[phase.val]? := by
  intro phase
  let before : Program width 8 := sectionPrefix0 width clauses
  let chunk : Program width 8 := headSetupCode (n := n) width (Controller.Horn.SourceSerialize.base clauses) (seedEnd width clauses + 4)
  let after : Program width 8 := (Controller.Horn.WorklistFIFO.fetchCode (n := n) width (Controller.Horn.SourceSerialize.base clauses) (seedEnd width clauses + 4) (seedEnd width clauses + 61) (seedEnd width clauses + 18)) ++
      (Controller.Horn.WorklistBucketLoop.code width (seedEnd width clauses + 18) (seedEnd width clauses + 56) (seedEnd width clauses + 30)) ++
      (Controller.Horn.WorklistBucketReady.code (n := n) width (Controller.Horn.SourceSerialize.base clauses) (seedEnd width clauses + 30) (seedEnd width clauses + 56) (conflictEntry width clauses) (seedEnd width clauses + 18)) ++
      (Controller.Horn.WorklistFIFO.advanceCode (n := n) width (Controller.Horn.SourceSerialize.base clauses) (seedEnd width clauses + 4)) ++
      (tagCode width 1) ++
      (emitCode width (Controller.Horn.SourceSerialize.base clauses) (outputLabels n)) ++
      (haltCode width) ++
      (conflictCode width)
  have beforeSize : before.size = seedEnd width clauses := by
    simpa only [before] using sectionPrefix0_size width clauses
  have placed : program width clauses = before ++ chunk ++ after := by
    simp only [program, before, sectionPrefix0, sectionPrefix1, sectionPrefix2, sectionPrefix3, sectionPrefix4, sectionPrefix5, sectionPrefix6, sectionPrefix7, sectionPrefix8, chunk, after, Array.append_assoc, Array.append_empty]
  have insideChunk : phase.val < chunk.size := by
    simpa [chunk] using phase.isLt
  rw [placed]
  have projected := chunk_projection before chunk after phase.val insideChunk
  simpa only [beforeSize, chunk] using projected

theorem fetch_at (width : Nat) (clauses : List (Controller.CNF.Clause (Fin n))) :
    Controller.Horn.WorklistFIFO.FetchAt (n := n) (program width clauses) (Controller.Horn.SourceSerialize.base clauses) (seedEnd width clauses + 4) (seedEnd width clauses + 61) (seedEnd width clauses + 18) := by
  intro phase
  let before : Program width 8 := sectionPrefix1 width clauses
  let chunk : Program width 8 := Controller.Horn.WorklistFIFO.fetchCode (n := n) width (Controller.Horn.SourceSerialize.base clauses) (seedEnd width clauses + 4) (seedEnd width clauses + 61) (seedEnd width clauses + 18)
  let after : Program width 8 := (Controller.Horn.WorklistBucketLoop.code width (seedEnd width clauses + 18) (seedEnd width clauses + 56) (seedEnd width clauses + 30)) ++
      (Controller.Horn.WorklistBucketReady.code (n := n) width (Controller.Horn.SourceSerialize.base clauses) (seedEnd width clauses + 30) (seedEnd width clauses + 56) (conflictEntry width clauses) (seedEnd width clauses + 18)) ++
      (Controller.Horn.WorklistFIFO.advanceCode (n := n) width (Controller.Horn.SourceSerialize.base clauses) (seedEnd width clauses + 4)) ++
      (tagCode width 1) ++
      (emitCode width (Controller.Horn.SourceSerialize.base clauses) (outputLabels n)) ++
      (haltCode width) ++
      (conflictCode width)
  have beforeSize : before.size = seedEnd width clauses + 4 := by
    simpa only [before] using sectionPrefix1_size width clauses
  have placed : program width clauses = before ++ chunk ++ after := by
    simp only [program, before, sectionPrefix0, sectionPrefix1, sectionPrefix2, sectionPrefix3, sectionPrefix4, sectionPrefix5, sectionPrefix6, sectionPrefix7, sectionPrefix8, chunk, after, Array.append_assoc, Array.append_empty]
  have insideChunk : phase.val < chunk.size := by
    simpa [chunk] using phase.isLt
  rw [placed]
  have projected := chunk_projection before chunk after phase.val insideChunk
  simpa only [beforeSize, chunk] using projected

theorem bucket_at (width : Nat) (clauses : List (Controller.CNF.Clause (Fin n))) :
    Controller.Horn.WorklistBucketLoop.At (program width clauses) (seedEnd width clauses + 18) (seedEnd width clauses + 56) (seedEnd width clauses + 30) := by
  intro phase
  let before : Program width 8 := sectionPrefix2 width clauses
  let chunk : Program width 8 := Controller.Horn.WorklistBucketLoop.code width (seedEnd width clauses + 18) (seedEnd width clauses + 56) (seedEnd width clauses + 30)
  let after : Program width 8 := (Controller.Horn.WorklistBucketReady.code (n := n) width (Controller.Horn.SourceSerialize.base clauses) (seedEnd width clauses + 30) (seedEnd width clauses + 56) (conflictEntry width clauses) (seedEnd width clauses + 18)) ++
      (Controller.Horn.WorklistFIFO.advanceCode (n := n) width (Controller.Horn.SourceSerialize.base clauses) (seedEnd width clauses + 4)) ++
      (tagCode width 1) ++
      (emitCode width (Controller.Horn.SourceSerialize.base clauses) (outputLabels n)) ++
      (haltCode width) ++
      (conflictCode width)
  have beforeSize : before.size = seedEnd width clauses + 18 := by
    simpa only [before] using sectionPrefix2_size width clauses
  have placed : program width clauses = before ++ chunk ++ after := by
    simp only [program, before, sectionPrefix0, sectionPrefix1, sectionPrefix2, sectionPrefix3, sectionPrefix4, sectionPrefix5, sectionPrefix6, sectionPrefix7, sectionPrefix8, chunk, after, Array.append_assoc, Array.append_empty]
  have insideChunk : phase.val < chunk.size := by
    simpa [chunk] using phase.isLt
  rw [placed]
  have projected := chunk_projection before chunk after phase.val insideChunk
  simpa only [beforeSize, chunk] using projected

theorem ready_at (width : Nat) (clauses : List (Controller.CNF.Clause (Fin n))) :
    Controller.Horn.WorklistBucketReady.At (n := n) (program width clauses) (Controller.Horn.SourceSerialize.base clauses) (seedEnd width clauses + 30) (seedEnd width clauses + 56) (conflictEntry width clauses) (seedEnd width clauses + 18) := by
  intro phase
  let before : Program width 8 := sectionPrefix3 width clauses
  let chunk : Program width 8 := Controller.Horn.WorklistBucketReady.code (n := n) width (Controller.Horn.SourceSerialize.base clauses) (seedEnd width clauses + 30) (seedEnd width clauses + 56) (conflictEntry width clauses) (seedEnd width clauses + 18)
  let after : Program width 8 := (Controller.Horn.WorklistFIFO.advanceCode (n := n) width (Controller.Horn.SourceSerialize.base clauses) (seedEnd width clauses + 4)) ++
      (tagCode width 1) ++
      (emitCode width (Controller.Horn.SourceSerialize.base clauses) (outputLabels n)) ++
      (haltCode width) ++
      (conflictCode width)
  have beforeSize : before.size = seedEnd width clauses + 30 := by
    simpa only [before] using sectionPrefix3_size width clauses
  have placed : program width clauses = before ++ chunk ++ after := by
    simp only [program, before, sectionPrefix0, sectionPrefix1, sectionPrefix2, sectionPrefix3, sectionPrefix4, sectionPrefix5, sectionPrefix6, sectionPrefix7, sectionPrefix8, chunk, after, Array.append_assoc, Array.append_empty]
  have insideChunk : phase.val < chunk.size := by
    simpa [chunk] using phase.isLt
  rw [placed]
  have projected := chunk_projection before chunk after phase.val insideChunk
  simpa only [beforeSize, chunk] using projected

theorem advance_at (width : Nat) (clauses : List (Controller.CNF.Clause (Fin n))) :
    Controller.Horn.WorklistFIFO.AdvanceAt (n := n) (program width clauses) (Controller.Horn.SourceSerialize.base clauses) (seedEnd width clauses + 56) (seedEnd width clauses + 4) := by
  intro phase
  let before : Program width 8 := sectionPrefix4 width clauses
  let chunk : Program width 8 := Controller.Horn.WorklistFIFO.advanceCode (n := n) width (Controller.Horn.SourceSerialize.base clauses) (seedEnd width clauses + 4)
  let after : Program width 8 := (tagCode width 1) ++
      (emitCode width (Controller.Horn.SourceSerialize.base clauses) (outputLabels n)) ++
      (haltCode width) ++
      (conflictCode width)
  have beforeSize : before.size = seedEnd width clauses + 56 := by
    simpa only [before] using sectionPrefix4_size width clauses
  have placed : program width clauses = before ++ chunk ++ after := by
    simp only [program, before, sectionPrefix0, sectionPrefix1, sectionPrefix2, sectionPrefix3, sectionPrefix4, sectionPrefix5, sectionPrefix6, sectionPrefix7, sectionPrefix8, chunk, after, Array.append_assoc, Array.append_empty]
  have insideChunk : phase.val < chunk.size := by
    simpa [chunk] using phase.isLt
  rw [placed]
  have projected := chunk_projection before chunk after phase.val insideChunk
  simpa only [beforeSize, chunk] using projected

@[irreducible] def runtimeTail (width : Nat)
    (clauses : List (Controller.CNF.Clause (Fin n))) : Program width 8 :=
  headSetupCode (n := n) width (Controller.Horn.SourceSerialize.base clauses) ((seedEnd width clauses) + 4) ++
    Controller.Horn.WorklistFIFO.fetchCode (n := n) width (Controller.Horn.SourceSerialize.base clauses) ((seedEnd width clauses) + 4) ((seedEnd width clauses) + 61) ((seedEnd width clauses) + 18) ++
    Controller.Horn.WorklistBucketLoop.code width ((seedEnd width clauses) + 18) ((seedEnd width clauses) + 56) ((seedEnd width clauses) + 30) ++
    Controller.Horn.WorklistBucketReady.code (n := n) width (Controller.Horn.SourceSerialize.base clauses) ((seedEnd width clauses) + 30) ((seedEnd width clauses) + 56) (conflictEntry width clauses) ((seedEnd width clauses) + 18) ++
    Controller.Horn.WorklistFIFO.advanceCode (n := n) width (Controller.Horn.SourceSerialize.base clauses) ((seedEnd width clauses) + 4) ++
    tagCode width 1 ++ emitCode width (Controller.Horn.SourceSerialize.base clauses) (outputLabels n) ++ haltCode width ++
    conflictCode width

private theorem cold_prefix_eq (width : Nat)
    (clauses : List (Controller.CNF.Clause (Fin n))) :
    coldPrefix width clauses = Controller.Horn.WorklistSeedRun.program width clauses
      (conflictEntry width clauses) := by
  unfold coldPrefix
  rfl

private theorem program_append_eq (width : Nat)
    (clauses : List (Controller.CNF.Clause (Fin n))) :
    program width clauses = coldPrefix width clauses ++ runtimeTail width clauses := by
  simp only [program, runtimeTail, Array.append_assoc]

private theorem seed_execution_append (clauses : List (Controller.CNF.Clause (Fin n)))
    (state final : State width 8) (ticks peak : Nat)
    (trace : Execution (Controller.Horn.WorklistSeedRun.program width clauses
      (conflictEntry width clauses)) state final ticks peak) :
    Execution (program width clauses) state final ticks peak := by
  have opaqueTrace : Execution (coldPrefix width clauses) state final ticks peak := by
    rw [cold_prefix_eq]
    exact trace
  have lifted : Execution (coldPrefix width clauses ++ runtimeTail width clauses)
      state final ticks peak :=
    Controller.Horn.IndexScanCold.append_execution (coldPrefix width clauses)
      (runtimeTail width clauses) opaqueTrace
  rw [program_append_eq]
  exact lifted

/-- Original cold input reaches either a proved conflict or the semantic FIFO
terminal state in the same fixed program, with all original incidences charged. -/
theorem cold_fifo_execution (clauses : List (Controller.CNF.Clause (Fin n)))
    (state : State width 8) (suffix : List (Word width))
    (emptyHeap : state.heap = #[])
    (input : state.stack = (Controller.Horn.SourceSerialize.heap (width := width) clauses).toList ++ suffix)
    (position : state.pc = word width 0) (running : state.halted = false)
    (dual : ∀ index : Fin clauses.length, Controller.Horn.DualHornClause clauses[index.val])
    (codeFits : (program width clauses).size < 2 ^ width)
    (heapFits : Controller.Horn.IndexScanCold.recordStart width clauses + 3 * clauses.length +
      3 * (clauses.map List.length).sum < 2 ^ width) :
    ∃ (recordEnd : Nat) (queue : List (Fin n)) (fired : Fin clauses.length → Bool)
      (final : State width 8) (ticks peak : Nat),
      Execution (program width clauses) state final ticks peak ∧
      final.stack = suffix ∧ final.output = state.output ∧ queue.length ≤ n ∧
      ticks ≤ 51 * n + 115 * (clauses.map List.length).sum + 131 * clauses.length + 89 ∧
      peak ≤ state.liveWords + 5 * n + 4 + 3 * clauses.length + 3 * (clauses.map List.length).sum ∧
      ((final.pc = word width (conflictEntry width clauses) ∧ final.halted = false ∧
        ¬ ∃ assignment : Fin n → Bool, ∀ row : Fin clauses.length,
          (Controller.Horn.Worklist.compileClause clauses[row.val]).Holds assignment) ∨
        (Controller.Horn.WorklistFIFORun.Done clauses (Controller.Horn.IndexScanCold.recordStart width clauses)
          recordEnd (Controller.Horn.SourceSerialize.base clauses) (seedEnd width clauses + 61) queue fired final ∧
          EnabledComplete clauses queue fired ∧ FiredMeaning clauses queue fired ∧
          Controller.Horn.WorklistSeed.QueueForced clauses queue)) := by
  obtain ⟨recordEnd, seedQueue, seedFired, seeded, seedTicks, seedPeak,
      seedTrace, seedStack, seedOutput, seedBound, seedCost, seedStorage, _, seedResult⟩ :=
    Controller.Horn.WorklistSeedRun.cold_seed_execution clauses (conflictEntry width clauses) state suffix
      emptyHeap input position running dual
      (by rw [Controller.Horn.WorklistSeedRun.program_size,
        Controller.Horn.IndexScanCold.program_size]
          have size := program_size width clauses
          unfold seedEnd at size
          omega) heapFits
  have appendedSeed : Execution (program width clauses) state seeded seedTicks seedPeak :=
    seed_execution_append clauses state seeded seedTicks seedPeak seedTrace
  rcases seedResult with conflict | seed
  · exact ⟨recordEnd, seedQueue, seedFired, seeded, seedTicks, seedPeak, appendedSeed,
      seedStack, seedOutput, seedBound, by omega, seedStorage, Or.inl conflict⟩
  · have separated : Controller.Horn.SourceSerialize.base clauses + 5 * n + 4 ≤
        Controller.Horn.IndexScanCold.recordStart width clauses := by
      simp [Controller.Horn.IndexScanCold.recordStart, Controller.Horn.NormalizeCold.words]
    have positioned : Controller.Horn.WorklistSeedRun.ScanInvariant clauses
        (Controller.Horn.IndexScanCold.recordStart width clauses) recordEnd
        (Controller.Horn.SourceSerialize.base clauses) (seedEnd width clauses) clauses.length seedQueue seedFired seeded := by
      simpa only [Controller.Horn.WorklistSeedRun.program_size, Controller.Horn.IndexScanCold.program_size, seedEnd] using seed
    obtain ⟨readyState, setupTrace, initial, complete, meaning, forced, setupSize, setupStack, setupOutput⟩ :=
      seed_to_fifo clauses (Controller.Horn.IndexScanCold.recordStart width clauses) recordEnd
        (Controller.Horn.SourceSerialize.base clauses) (seedEnd width clauses) (seedEnd width clauses + 4)
        (program width clauses) seedQueue seedFired seeded positioned separated (head_at width clauses)
        (by have size := program_size width clauses; omega)
    obtain ⟨finalQueue, finalFired, final, fifoTicks, growth, unique, fifoCost, fifoTrace,
        fifoSize, fifoStack, fifoOutput, finalRunning, result⟩ :=
      semantic_runtime clauses (Controller.Horn.IndexScanCold.recordStart width clauses) recordEnd
        (Controller.Horn.SourceSerialize.base clauses) (seedEnd width clauses + 4) (seedEnd width clauses + 61)
        (seedEnd width clauses + 18) (seedEnd width clauses + 56) (seedEnd width clauses + 30)
        (seedEnd width clauses + 56) (conflictEntry width clauses) (program width clauses)
        separated (fetch_at width clauses) (advance_at width clauses) (bucket_at width clauses) (ready_at width clauses)
        (by have size := program_size width clauses; omega) (by have size := program_size width clauses; omega)
        (by have size := program_size width clauses; omega) (by have size := program_size width clauses; omega)
        n 0 seedQueue seedFired readyState (by omega) initial complete meaning forced
    have readyLive : readyState.liveWords = seeded.liveWords := by
      unfold State.liveWords; rw [setupSize, setupStack, setupOutput]
    have seededStorage := seedTrace.final_storage_le
    have incidenceCost := Controller.Horn.WorklistFIFORun.incidence_bound
      (Controller.Horn.IndexScan.occurrences clauses (Controller.Horn.IndexScanCold.recordStart width clauses)) (seedQueue.take 0)
    have finalBound := Controller.Horn.WorklistMark.enqueue_bound finalQueue unique
    have all := (appendedSeed.append setupTrace).append fifoTrace
    refine ⟨recordEnd, finalQueue, finalFired, final, seedTicks + 4 + fifoTicks,
      max seedPeak seeded.liveWords, ?_, fifoStack.trans (setupStack.trans seedStack),
      fifoOutput.trans (setupOutput.trans seedOutput), finalBound, ?_, ?_, ?_⟩
    · simpa only [readyLive, Nat.max_assoc, Nat.max_self] using all
    · have positiveCount := Controller.Horn.IndexScanCold.occurrences_length_le clauses
        (Controller.Horn.IndexScanCold.recordStart width clauses)
      simp only [List.take_zero, List.length_nil, Nat.sub_zero] at fifoCost incidenceCost
      omega
    · omega
    · rcases result with conflict | finished
      · exact Or.inl ⟨conflict.1, finalRunning, conflict.2⟩
      · exact Or.inr finished


theorem success_tag_zero (width : Nat) (clauses : List (Controller.CNF.Clause (Fin n))) :
    (program width clauses)[seedEnd width clauses + 61]? = some (.constant 0 (word width 1)) := by
  let before : Program width 8 := sectionPrefix5 width clauses
  let chunk : Program width 8 := tagCode width 1
  let after : Program width 8 := (emitCode width (Controller.Horn.SourceSerialize.base clauses) (outputLabels n)) ++
      (haltCode width) ++
      (conflictCode width)
  have beforeSize : before.size = seedEnd width clauses + 61 := by
    simpa only [before] using sectionPrefix5_size width clauses
  have placed : program width clauses = before ++ chunk ++ after := by
    simp only [program, before, sectionPrefix0, sectionPrefix1, sectionPrefix2, sectionPrefix3, sectionPrefix4, sectionPrefix5, sectionPrefix6, sectionPrefix7, sectionPrefix8, chunk, after, Array.append_assoc, Array.append_empty]
  have projected := chunk_projection before chunk after 0 (by simp [chunk])
  rw [placed, ← beforeSize]
  simpa [chunk, tagCode, haltCode, conflictCode] using projected

theorem success_tag_one (width : Nat) (clauses : List (Controller.CNF.Clause (Fin n))) :
    (program width clauses)[seedEnd width clauses + 61 + 1]? = some (.emit 0) := by
  let before : Program width 8 := sectionPrefix5 width clauses
  let chunk : Program width 8 := tagCode width 1
  let after : Program width 8 := (emitCode width (Controller.Horn.SourceSerialize.base clauses) (outputLabels n)) ++
      (haltCode width) ++
      (conflictCode width)
  have beforeSize : before.size = seedEnd width clauses + 61 := by
    simpa only [before] using sectionPrefix5_size width clauses
  have placed : program width clauses = before ++ chunk ++ after := by
    simp only [program, before, sectionPrefix0, sectionPrefix1, sectionPrefix2, sectionPrefix3, sectionPrefix4, sectionPrefix5, sectionPrefix6, sectionPrefix7, sectionPrefix8, chunk, after, Array.append_assoc, Array.append_empty]
  have projected := chunk_projection before chunk after 1 (by simp [chunk])
  rw [placed, ← beforeSize]
  simpa [chunk, tagCode, haltCode, conflictCode] using projected

theorem success_halt_at (width : Nat) (clauses : List (Controller.CNF.Clause (Fin n))) :
    (program width clauses)[seedEnd width clauses + 63 + 4 * n]? = some (.halt) := by
  let before : Program width 8 := sectionPrefix6 width clauses
  let chunk : Program width 8 := haltCode width
  let after : Program width 8 := (conflictCode width)
  have beforeSize : before.size = seedEnd width clauses + 63 + 4 * n := by
    simpa only [before] using sectionPrefix6_size width clauses
  have placed : program width clauses = before ++ chunk ++ after := by
    simp only [program, before, sectionPrefix0, sectionPrefix1, sectionPrefix2, sectionPrefix3, sectionPrefix4, sectionPrefix5, sectionPrefix6, sectionPrefix7, sectionPrefix8, chunk, after, Array.append_assoc, Array.append_empty]
  have projected := chunk_projection before chunk after 0 (by simp [chunk])
  rw [placed, ← beforeSize]
  simpa [chunk, tagCode, haltCode, conflictCode] using projected

theorem conflict_tag_zero (width : Nat) (clauses : List (Controller.CNF.Clause (Fin n))) :
    (program width clauses)[conflictEntry width clauses]? = some (.constant 0 (word width 0)) := by
  let before : Program width 8 := sectionPrefix7 width clauses
  let chunk : Program width 8 := conflictCode width
  let after : Program width 8 := #[]
  have beforeSize : before.size = conflictEntry width clauses := by
    simpa only [before] using sectionPrefix7_size width clauses
  have placed : program width clauses = before ++ chunk ++ after := by
    simp only [program, before, sectionPrefix0, sectionPrefix1, sectionPrefix2, sectionPrefix3, sectionPrefix4, sectionPrefix5, sectionPrefix6, sectionPrefix7, sectionPrefix8, chunk, after, Array.append_assoc, Array.append_empty]
  have projected := chunk_projection before chunk after 0 (by simp [chunk])
  rw [placed, ← beforeSize]
  simpa [chunk, tagCode, haltCode, conflictCode] using projected

theorem conflict_tag_one (width : Nat) (clauses : List (Controller.CNF.Clause (Fin n))) :
    (program width clauses)[conflictEntry width clauses + 1]? = some (.emit 0) := by
  let before : Program width 8 := sectionPrefix7 width clauses
  let chunk : Program width 8 := conflictCode width
  let after : Program width 8 := #[]
  have beforeSize : before.size = conflictEntry width clauses := by
    simpa only [before] using sectionPrefix7_size width clauses
  have placed : program width clauses = before ++ chunk ++ after := by
    simp only [program, before, sectionPrefix0, sectionPrefix1, sectionPrefix2, sectionPrefix3, sectionPrefix4, sectionPrefix5, sectionPrefix6, sectionPrefix7, sectionPrefix8, chunk, after, Array.append_assoc, Array.append_empty]
  have projected := chunk_projection before chunk after 1 (by simp [chunk])
  rw [placed, ← beforeSize]
  simpa [chunk, tagCode, haltCode, conflictCode] using projected

theorem conflict_halt_at (width : Nat) (clauses : List (Controller.CNF.Clause (Fin n))) :
    (program width clauses)[conflictEntry width clauses + 2]? = some (.halt) := by
  let before : Program width 8 := sectionPrefix7 width clauses
  let chunk : Program width 8 := conflictCode width
  let after : Program width 8 := #[]
  have beforeSize : before.size = conflictEntry width clauses := by
    simpa only [before] using sectionPrefix7_size width clauses
  have placed : program width clauses = before ++ chunk ++ after := by
    simp only [program, before, sectionPrefix0, sectionPrefix1, sectionPrefix2, sectionPrefix3, sectionPrefix4, sectionPrefix5, sectionPrefix6, sectionPrefix7, sectionPrefix8, chunk, after, Array.append_assoc, Array.append_empty]
  have projected := chunk_projection before chunk after 2 (by simp [chunk])
  rw [placed, ← beforeSize]
  simpa [chunk, tagCode, haltCode, conflictCode] using projected

theorem output_at (width : Nat) (clauses : List (Controller.CNF.Clause (Fin n))) :
    EmitCodeAt (program width clauses) (seedEnd width clauses + 63)
      (Controller.Horn.SourceSerialize.base clauses) (outputLabels n) := by
  intro phase inside
  let before : Program width 8 := sectionPrefix8 width clauses
  let chunk : Program width 8 := emitCode width (Controller.Horn.SourceSerialize.base clauses) (outputLabels n)
  let after : Program width 8 := (haltCode width) ++
      (conflictCode width)
  have beforeSize : before.size = seedEnd width clauses + 63 := by
    simpa only [before] using sectionPrefix8_size width clauses
  have placed : program width clauses = before ++ chunk ++ after := by
    simp only [program, before, sectionPrefix0, sectionPrefix1, sectionPrefix2, sectionPrefix3, sectionPrefix4, sectionPrefix5, sectionPrefix6, sectionPrefix7, sectionPrefix8, chunk, after, Array.append_assoc, Array.append_empty]
  have insideChunk : phase < chunk.size := by
    simpa [chunk] using inside
  rw [placed]
  have projected := chunk_projection before chunk after phase insideChunk
  simpa only [beforeSize, chunk] using projected

/-- Two fetched instructions emit the result tag, without changing the
assignment flags or the register used to complement them. -/
theorem tag_execution (program : Program width 8) (entry value : Nat) (state : State width 8)
    (present0 : program[entry]? = some (.constant 0 (word width value)))
    (present1 : program[entry + 1]? = some (.emit 0))
    (position : state.pc = word width entry) (running : state.halted = false)
    (capacity : entry + 2 < 2 ^ width) :
    ∃ final, Execution program state final 2 (state.liveWords + 1) ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧
      final.output = word width value :: state.output ∧ final.reg 5 = state.reg 5 ∧
      final.pc = word width (entry + 2) ∧ final.halted = false := by
  let first := state.advance.put 0 (word width value)
  let final : State width 8 := { first.advance with output := word width value :: state.output }
  have pc : first.pc = word width (entry + 1) := advance_pc state entry position (by omega)
  have step0 : programStep program state = some first := by
    rw [fetched program state entry (.constant 0 (word width value)) position (by omega) present0]
    simp [step, first, running]
  have step1 : programStep program first = some final := by
    rw [fetched program first (entry + 1) (.emit 0) pc (by omega) present1]
    simp [step, first, final, State.put, State.advance, running]
  have live0 : first.liveWords = state.liveWords := rfl
  have live1 : final.liveWords = state.liveWords + 1 := by
    simp [final, first, State.liveWords, State.put, State.advance]
    omega
  refine ⟨final, ?_, rfl, rfl, rfl, ?_, ?_, running⟩
  · simpa only [live0, live1, Nat.zero_add, Nat.add_zero,
      show max state.liveWords (state.liveWords + 1) = state.liveWords + 1 by omega] using
      Execution.cons step0 (Execution.cons step1 (Execution.refl final))
  · simp [final, first, State.put, State.advance]
  · simpa [final, Nat.add_assoc] using advance_pc first (entry + 1) pc (by omega)

/-- The emitted words encode the precise D04 result, with a result tag retained
even for zero variables. -/
def resultWords (width : Nat) (result : Option (Vector Bool n)) : List (Word width) :=
  match result with
  | none => [word width 0]
  | some values => (List.finRange n).map (fun label => word width (if values[label.val] then 1 else 0)) ++ [word width 1]

/-- The contract size counts every declared variable, original row and literal,
including empty clauses and unused variables. -/
def hsize (formula : Controller.CNF.Formula (Fin n)) : Nat :=
  1 + n + formula.clauses.size + (formula.clauses.toList.map List.length).sum

/-- Full actual-machine acceptance data, with the exact D04 observable encoded
by fetched instructions and all instruction/output storage charged. -/
structure Accepted (formula : Controller.CNF.Formula (Fin n))
    (initial final : State width 8) (suffix : List (Word width)) (ticks peak : Nat) : Prop where
  trace : Execution (program width formula.clauses.toList) initial final ticks peak
  caller : final.stack = suffix
  halted : final.halted = true
  observable : final.output = resultWords width (Controller.Horn.Worklist.solveFormula formula) ++ initial.output
  timeBound : ticks ≤ 131 * hsize formula
  peakBound : peak ≤ initial.liveWords + 6 * n + 5 + 3 * formula.clauses.size +
    3 * (formula.clauses.toList.map List.length).sum
  totalStorage : programWords (program width formula.clauses.toList) + peak ≤ initial.liveWords + 1421 * hsize formula

/-- The semantic FIFO terminal executes its tagged greatest assignment output
and halts. The output loads the actual terminal off cells. -/
theorem finish_success (formula : Controller.CNF.Formula (Fin n))
    (dual : Controller.Horn.DualHorn formula) (recordEnd : Nat)
    (queue : List (Fin n)) (fired : Fin formula.clauses.toList.length → Bool) (state : State width 8)
    (done : Controller.Horn.WorklistFIFORun.Done formula.clauses.toList
      (Controller.Horn.IndexScanCold.recordStart width formula.clauses.toList) recordEnd
      (Controller.Horn.SourceSerialize.base formula.clauses.toList)
      (seedEnd width formula.clauses.toList + 61) queue fired state)
    (complete : EnabledComplete formula.clauses.toList queue fired)
    (meaning : FiredMeaning formula.clauses.toList queue fired)
    (forced : Controller.Horn.WorklistSeed.QueueForced formula.clauses.toList queue)
    (codeFits : (program width formula.clauses.toList).size < 2 ^ width) :
    ∃ final, Execution (program width formula.clauses.toList) state final (4 * n + 3) (state.liveWords + n + 1) ∧
      final.stack = state.stack ∧ final.halted = true ∧
      final.output = resultWords width (Controller.Horn.Worklist.solveFormula formula) ++ state.output := by
  obtain ⟨_, values, returned, assignment⟩ := d04_observable formula dual queue fired complete meaning forced
  have oneFits : 1 < 2 ^ width := by have size := program_size width formula.clauses.toList; omega
  obtain ⟨tagged, tagTrace, tagHeap, tagStack, tagOutput, tagOne, tagPC, tagRunning⟩ :=
    tag_execution (program width formula.clauses.toList) (seedEnd width formula.clauses.toList + 61) 1 state
      (success_tag_zero width formula.clauses.toList) (success_tag_one width formula.clauses.toList)
      done.position done.running (by have size := program_size width formula.clauses.toList; omega)
  obtain ⟨emitted, emitTrace, emitHeap, emitStack, emitOutput, emitOne, emitPC, emitRunning⟩ :=
    emit_code_execution (program width formula.clauses.toList) (seedEnd width formula.clauses.toList + 63)
      (Controller.Horn.SourceSerialize.base formula.clauses.toList) (outputLabels n) queue tagged
      (by simpa only [tagHeap] using done.fifo) (output_at width formula.clauses.toList)
      (by simpa [Nat.add_assoc] using tagPC) tagRunning (tagOne.trans done.one)
      (by simpa only [tagHeap] using done.room)
      (by have size := program_size width formula.clauses.toList; simp only [output_labels_length]; omega) oneFits
  obtain ⟨final, haltTrace, _, haltStack, haltOutput, halted⟩ :=
    halt_execution (program width formula.clauses.toList)
      (seedEnd width formula.clauses.toList + 63 + 4 * n) emitted
      (success_halt_at width formula.clauses.toList)
      (by simpa only [output_labels_length] using emitPC) emitRunning
      (by have size := program_size width formula.clauses.toList; omega)
  have tagLive : tagged.liveWords = state.liveWords + 1 := by
    simp only [State.liveWords, tagHeap, tagStack, tagOutput, List.length_cons]; omega
  have emitLive : emitted.liveWords = state.liveWords + 1 + n := by
    have relative : emitted.liveWords = tagged.liveWords + n := by
      unfold State.liveWords
      rw [emitHeap, emitStack, emitOutput]
      simp only [List.length_append, List.length_reverse, List.length_map, output_labels_length]
      omega
    rw [relative, tagLive]
  refine ⟨final, ?_, haltStack.trans (emitStack.trans tagStack), halted, ?_⟩
  · have trace := (tagTrace.append emitTrace).append haltTrace
    simpa only [output_labels_length, tagLive, emitLive, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      show max (state.liveWords + 1) (state.liveWords + 1 + n) = state.liveWords + 1 + n by omega,
      Nat.max_self, Nat.reduceAdd,
      show 1 + (2 + 4 * n) = 3 + 4 * n by omega,
      show max (1 + state.liveWords) (n + (1 + state.liveWords)) = n + (1 + state.liveWords) by omega] using trace
  · rw [haltOutput, emitOutput, tagOutput, returned]
    simp only [resultWords, outputLabels, List.map_reverse, List.reverse_reverse,
      List.append_assoc, List.singleton_append]
    congr 1
    apply List.map_congr_left
    intro label member
    rw [congrFun assignment label]


/-- A conflict derived from original rows emits the exact D04 contradiction
result and reaches a fetched halt. -/
theorem finish_conflict (formula : Controller.CNF.Formula (Fin n))
    (dual : Controller.Horn.DualHorn formula) (state : State width 8)
    (position : state.pc = word width (conflictEntry width formula.clauses.toList))
    (running : state.halted = false)
    (noModels : ¬ ∃ assignment : Fin n → Bool, ∀ row : Fin formula.clauses.toList.length,
      (Controller.Horn.Worklist.compileClause formula.clauses.toList[row.val]).Holds assignment)
    (codeFits : (program width formula.clauses.toList).size < 2 ^ width) :
    ∃ final, Execution (program width formula.clauses.toList) state final 3 (state.liveWords + 1) ∧
      final.stack = state.stack ∧ final.halted = true ∧
      final.output = resultWords width (Controller.Horn.Worklist.solveFormula formula) ++ state.output := by
  have contradiction : Controller.CNF.Unsatisfiable formula := by
    rintro ⟨assignment, models⟩
    apply noModels
    exact ⟨assignment, (original_models_iff formula dual assignment).mpr models⟩
  have returned := (Controller.Horn.Worklist.solveFormula_none_iff formula dual).mpr contradiction
  obtain ⟨tagged, first, heap, stack, output, one, pc, taggedRunning⟩ :=
    tag_execution (program width formula.clauses.toList) (conflictEntry width formula.clauses.toList) 0 state
      (conflict_tag_zero width formula.clauses.toList) (conflict_tag_one width formula.clauses.toList)
      position running (by have size := program_size width formula.clauses.toList; unfold conflictEntry; omega)
  obtain ⟨final, last, _, finalStack, finalOutput, halted⟩ :=
    halt_execution (program width formula.clauses.toList) (conflictEntry width formula.clauses.toList + 2)
      tagged (conflict_halt_at width formula.clauses.toList) pc taggedRunning
      (by have size := program_size width formula.clauses.toList; unfold conflictEntry; omega)
  have live : tagged.liveWords = state.liveWords + 1 := by
    simp only [State.liveWords, heap, stack, output, List.length_cons]; omega
  refine ⟨final, ?_, finalStack.trans stack, halted, ?_⟩
  · simpa only [live, Nat.max_self] using first.append last
  · simp only [returned, resultWords, finalOutput, output, List.singleton_append]

/-- Full R02 execution from the actual serialized original formula: one cold
normalization and physical index, one zero-body scan, one FIFO traversal per
marked variable, one visit per original occurrence, tagged output, and halt. -/
theorem cold_worklist_acceptance (formula : Controller.CNF.Formula (Fin n))
    (dual : Controller.Horn.DualHorn formula) (state : State width 8) (suffix : List (Word width))
    (emptyHeap : state.heap = #[])
    (input : state.stack = (Controller.Horn.SourceSerialize.heap (width := width) formula.clauses.toList).toList ++ suffix)
    (position : state.pc = word width 0) (running : state.halted = false)
    (codeFits : (program width formula.clauses.toList).size < 2 ^ width)
    (heapFits : Controller.Horn.IndexScanCold.recordStart width formula.clauses.toList +
      3 * formula.clauses.size + 3 * (formula.clauses.toList.map List.length).sum < 2 ^ width) :
    ∃ final ticks peak, Accepted formula state final suffix ticks peak := by
  have sourceDual : ∀ index : Fin formula.clauses.toList.length,
      Controller.Horn.DualHornClause formula.clauses.toList[index.val] := by
    intro index
    apply dual
    simpa using List.getElem_mem index.isLt
  obtain ⟨recordEnd, queue, fired, terminal, firstTicks, firstPeak, first,
      caller, originalOutput, queueBound, firstCost, firstStorage, outcome⟩ :=
    cold_fifo_execution formula.clauses.toList state suffix emptyHeap input position running sourceDual codeFits
      (by simpa using heapFits)
  have terminalStorage := first.final_storage_le
  have exactSize : programWords (program width formula.clauses.toList) =
      1416 + 16 * n + 24 * formula.clauses.size + 24 * (formula.clauses.toList.map List.length).sum := by
    unfold programWords
    rw [program_size]
    simp only [seedEnd, Controller.Horn.IndexScanCold.entry, Controller.Horn.NormalizeCold.program_size,
      Array.length_toList]
    omega
  rcases outcome with conflict | ⟨done, complete, meaning, forced⟩
  · obtain ⟨final, last, finalCaller, halted, observable⟩ :=
      finish_conflict formula dual terminal conflict.1 conflict.2.1 conflict.2.2 codeFits
    refine ⟨final, firstTicks + 3, max firstPeak (terminal.liveWords + 1), ?_⟩
    refine ⟨first.append last, finalCaller.trans caller, halted, ?_, ?_, ?_, ?_⟩
    · simpa only [originalOutput] using observable
    · unfold hsize
      simp only [Array.length_toList] at firstCost
      omega
    · simp only [Array.length_toList] at firstStorage
      omega
    · unfold hsize
      simp only [Array.length_toList] at firstStorage
      rw [exactSize]
      omega
  · obtain ⟨final, last, finalCaller, halted, observable⟩ :=
      finish_success formula dual recordEnd queue fired terminal done complete meaning forced codeFits
    refine ⟨final, firstTicks + (4 * n + 3), max firstPeak (terminal.liveWords + n + 1), ?_⟩
    refine ⟨first.append last, finalCaller.trans caller, halted, ?_, ?_, ?_, ?_⟩
    · simpa only [originalOutput] using observable
    · unfold hsize
      simp only [Array.length_toList] at firstCost
      omega
    · simp only [Array.length_toList] at firstStorage
      omega
    · unfold hsize
      simp only [Array.length_toList] at firstStorage
      rw [exactSize]
      omega


/-- The machine endpoint uses exactly the public R02 input-size convention. -/
theorem hsize_eq_inputSize (formula : Controller.CNF.Formula (Fin n)) :
    hsize formula = Controller.Cost.Horn.inputSize formula := rfl

/-- A single input-size word bound covers actual code, packed rows, scratch,
queue and original linked occurrence addresses. -/
theorem cold_worklist_acceptance_of_word_bound (formula : Controller.CNF.Formula (Fin n))
    (dual : Controller.Horn.DualHorn formula) (state : State width 8) (suffix : List (Word width))
    (emptyHeap : state.heap = #[])
    (input : state.stack = (Controller.Horn.SourceSerialize.heap (width := width) formula.clauses.toList).toList ++ suffix)
    (position : state.pc = word width 0) (running : state.halted = false)
    (wordBound : 400 * Controller.Cost.Horn.inputSize formula < 2 ^ width) :
    ∃ final ticks peak, Accepted formula state final suffix ticks peak := by
  apply cold_worklist_acceptance formula dual state suffix emptyHeap input position running
  · rw [program_size]
    simp only [seedEnd, Controller.Horn.IndexScanCold.entry, Controller.Horn.NormalizeCold.program_size,
      Array.length_toList]
    unfold Controller.Cost.Horn.inputSize at wordBound
    omega
  · simp only [Controller.Horn.IndexScanCold.recordStart, Controller.Horn.NormalizeCold.words_eq,
      Array.length_toList]
    unfold Controller.Cost.Horn.inputSize at wordBound
    omega

end Controller.Horn.WorklistAccept

namespace Controller.Cost.Horn
open Controller.Cost

/-- The public resource result refines the exact D04 executable by a fetched
cold program, with declared variables and empty clauses counted in inputSize. -/
theorem solveFormula_indexed_word_linear (formula : Controller.CNF.Formula (Fin n))
    (dual : Controller.Horn.DualHorn formula) (state : State width 8) (suffix : List (Word width))
    (emptyHeap : state.heap = #[])
    (input : state.stack = (Controller.Horn.SourceSerialize.heap (width := width) formula.clauses.toList).toList ++ suffix)
    (position : state.pc = word width 0) (running : state.halted = false)
    (wordBound : 400 * inputSize formula < 2 ^ width) :
    ∃ final ticks peak,
      Execution (Controller.Horn.WorklistAccept.program width formula.clauses.toList) state final ticks peak ∧
      final.halted = true ∧ final.stack = suffix ∧
      final.output = Controller.Horn.WorklistAccept.resultWords width
        (Controller.Horn.Worklist.solveFormula formula) ++ state.output ∧
      ticks ≤ 131 * inputSize formula ∧
      programWords (Controller.Horn.WorklistAccept.program width formula.clauses.toList) + peak ≤
        state.liveWords + 1421 * inputSize formula := by
  obtain ⟨final, ticks, peak, accepted⟩ :=
    Controller.Horn.WorklistAccept.cold_worklist_acceptance_of_word_bound formula dual state suffix
      emptyHeap input position running wordBound
  exact ⟨final, ticks, peak, accepted.trace, accepted.halted, accepted.caller, accepted.observable,
    by simpa only [Controller.Horn.WorklistAccept.hsize_eq_inputSize] using accepted.timeBound,
    by simpa only [Controller.Horn.WorklistAccept.hsize_eq_inputSize] using accepted.totalStorage⟩

end Controller.Cost.Horn

