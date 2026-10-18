module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.DAGProgram

@[expose] public section

/-! Actual observation loads, emissions and halt. Output words remain charged
throughout these traces; heap values are read, not supplied as computed answers. -/
namespace Controller.Cost.OutputProgram

open Controller.Cost.GateProgram

abbrev Code (width : Nat) := List (Instruction width 4)

def emitCell (width address : Nat) : Code width :=
  [.constant 0 (word width address), .load 1 0, .emit 1]

def emitCode (width : Nat) (addresses : List Nat) : Code width :=
  addresses.flatMap (emitCell width)

@[simp] theorem emitCode_length (width : Nat) (addresses : List Nat) :
    (emitCode width addresses).length = 3 * addresses.length := by
  induction addresses with
  | nil => simp [emitCode]
  | cons address rest ih => simp [emitCode, emitCell, ih, Nat.mul_succ]; omega

def heapValue (heap : Array (Word width)) (address : Nat) : Word width :=
  (heap[address]?).getD (word width 0)

theorem heapValue_eq (heap : Array (Word width)) (address : Nat)
    (valid : address < heap.size) : heapValue heap address = heap[address] := by
  simp [heapValue, Array.getElem?_eq_getElem valid]

private theorem fetch (program : Program width 4) (s : State width 4)
    (cursor : Nat) (instruction : Instruction width 4)
    (pc : s.pc = word width cursor) (fits : cursor < 2 ^ width)
    (fetched : program[cursor]? = some instruction) :
    programStep program s = step instruction s := by
  unfold programStep
  rw [pc, show (word width cursor).val = cursor from Nat.mod_eq_of_lt fits, fetched]
  rfl

private theorem advance_pc (s : State width 4) (cursor : Nat)
    (pc : s.pc = word width cursor) (fits : cursor < 2 ^ width) :
    s.advance.pc = word width (cursor + 1) := by
  simp only [State.advance, pc]
  rw [show (word width cursor).val = cursor from Nat.mod_eq_of_lt fits]

/-- Three fetched instructions read one real heap word and prepend it to output. -/
theorem emitCell_execution (program : Program width 4) (s : State width 4)
    (base address : Nat) (pc : s.pc = word width base) (running : s.halted = false)
    (fits : base + 3 < 2 ^ width) (heapFits : s.heap.size < 2 ^ width)
    (valid : address < s.heap.size) (block : BlockAt program base (emitCell width address)) :
    ∃ final, Execution program s final 3 (s.liveWords + 1) ∧
      final.heap = s.heap ∧ final.stack = s.stack ∧
      final.output = heapValue s.heap address :: s.output ∧
      final.pc = word width (base + 3) ∧ final.halted = false := by
  let first := s.advance.put 0 (word width address)
  let second := first.advance.put 1 (heapValue s.heap address)
  let final := { second.advance with output := heapValue s.heap address :: s.output }
  have firstPC : first.pc = word width (base + 1) := by
    exact advance_pc s base pc (by omega)
  have secondPC : second.pc = word width (base + 2) := by
    change first.advance.pc = word width (base + 2)
    simpa only [Nat.add_assoc, Nat.reduceAdd] using advance_pc first (base + 1) firstPC (by omega)
  have addressHeld : first.reg 0 = word width address := by simp [first, State.put]
  have addressFits : address < 2 ^ width := by omega
  have firstStep : programStep program s = some first := by
    rw [fetch program s base (.constant 0 (word width address)) pc (by omega)
      (by simpa [emitCell] using block 0 (by simp [emitCell]))]
    simp [step, running, first]
  have secondStep : programStep program first = some second := by
    rw [fetch program first (base + 1) (.load 1 0) firstPC (by omega)
      (by simpa [emitCell] using block 1 (by simp [emitCell]))]
    have firstRunning : first.halted = false := running
    have firstHeap : first.heap = s.heap := rfl
    simp only [step, firstRunning, Bool.false_eq_true, ite_false, addressHeld,
      show (word width address).val = address from Nat.mod_eq_of_lt addressFits, firstHeap]
    rw [dite_eq_left valid, ← heapValue_eq s.heap address valid]
  have finalStep : programStep program second = some final := by
    rw [fetch program second (base + 2) (.emit 1) secondPC (by omega)
      (by simpa [emitCell] using block 2 (by simp [emitCell]))]
    have secondRunning : second.halted = false := running
    simp [step, running, final, second, first, State.put, State.advance]
  have firstLive : first.liveWords = s.liveWords := rfl
  have secondLive : second.liveWords = s.liveWords := rfl
  have finalLive : final.liveWords = s.liveWords + 1 := by
    simp [final, second, first, State.put, State.advance, State.liveWords]; omega
  refine ⟨final, ?_, rfl, rfl, rfl, ?_, running⟩
  · have trace := Execution.cons firstStep (Execution.cons secondStep
      (Execution.cons finalStep (Execution.refl final)))
    simpa only [firstLive, secondLive, finalLive, Nat.zero_add, Nat.add_zero,
      show max s.liveWords (s.liveWords + 1) = s.liveWords + 1 by omega] using trace
  · simpa only [Nat.add_assoc] using advance_pc second (base + 2) secondPC (by omega)

/-- Stored order is emitted in order; the machine output list is reversed. -/
theorem emitCode_execution (program : Program width 4) (s : State width 4)
    (base : Nat) (addresses : List Nat) (pc : s.pc = word width base)
    (running : s.halted = false) (fits : base + 3 * addresses.length < 2 ^ width)
    (heapFits : s.heap.size < 2 ^ width)
    (valid : ∀ address ∈ addresses, address < s.heap.size)
    (block : BlockAt program base (emitCode width addresses)) :
    ∃ final, Execution program s final (3 * addresses.length) (s.liveWords + addresses.length) ∧
      final.heap = s.heap ∧ final.stack = s.stack ∧
      final.output = (addresses.map (heapValue s.heap)).reverse ++ s.output ∧
      final.pc = word width (base + 3 * addresses.length) ∧ final.halted = false := by
  induction addresses generalizing s base with
  | nil =>
    refine ⟨s, ?_, rfl, rfl, ?_, ?_, running⟩
    · simpa using Execution.refl (p := program) s
    · simp
    · simpa using pc
  | cons address rest ih =>
    have code : emitCode width (address :: rest) = emitCell width address ++ emitCode width rest := by
      simp [emitCode]
    have headBlock := BlockAt.prefix program base (emitCell width address) (emitCode width rest)
      (by simpa only [code] using block)
    obtain ⟨middle, headTrace, middleHeap, middleStack, middleOutput, middlePC, middleRunning⟩ :=
      emitCell_execution program s base address pc running (by simp only [List.length_cons] at fits; omega)
        heapFits (valid address (by simp)) headBlock
    have restBlock : BlockAt program (base + 3) (emitCode width rest) := by
      simpa [emitCell] using BlockAt.suffix program base (emitCell width address)
        (emitCode width rest) (by simpa only [code] using block)
    obtain ⟨final, restTrace, finalHeap, finalStack, finalOutput, finalPC, finalRunning⟩ :=
      ih middle (base + 3) middlePC middleRunning
        (by simp only [List.length_cons] at fits; omega) (by simpa only [middleHeap] using heapFits)
        (by intro a member; rw [middleHeap]; exact valid a (by simp [member])) restBlock
    have middleLive : middle.liveWords = s.liveWords + 1 := by
      simp only [State.liveWords, middleHeap, middleStack, middleOutput, List.length_cons]; omega
    refine ⟨final, ?_, finalHeap.trans middleHeap, finalStack.trans middleStack, ?_, ?_, finalRunning⟩
    · have joined := headTrace.append restTrace
      have peak : max (s.liveWords + 1) (middle.liveWords + rest.length) =
          s.liveWords + (address :: rest).length := by rw [middleLive]; simp only [List.length_cons]; omega
      rw [peak] at joined
      simpa only [List.length_cons, Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using joined
    · rw [finalOutput, middleHeap, middleOutput]
      simp [List.reverse_cons, List.append_assoc]
    · simpa only [List.length_cons, Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using finalPC

/-- The terminal instruction is a real fetched transition and charges one step. -/
theorem halt_execution (program : Program width 4) (s : State width 4)
    (base : Nat) (pc : s.pc = word width base) (running : s.halted = false)
    (fits : base < 2 ^ width) (fetched : program[base]? = some .halt) :
    Execution program s { s.advance with halted := true } 1 s.liveWords := by
  have transition : programStep program s = some { s.advance with halted := true } := by
    rw [fetch program s base .halt pc fits fetched]
    simp [step, running]
  have trace := Execution.cons transition (Execution.refl { s.advance with halted := true })
  simpa [State.liveWords, State.advance] using trace

open Controller.Decoder Controller.Cost.DAGProgram

def observationAddresses (graph : DAG n) : List Nat :=
  graph.roots.map (fun root => n + root.val)

def completeCode (graph : DAG n) (width : Nat) : Code width :=
  prefixCode graph width 0 graph.nodeCount (Nat.le_refl _) ++
    emitCode width (observationAddresses graph)

def completeProgram (graph : DAG n) (width : Nat) : Program width 4 :=
  (completeCode graph width).toArray.push .halt

theorem completeProgram_block (graph : DAG n) (width : Nat) :
    BlockAt (completeProgram graph width) 0 (completeCode graph width) := by
  intro offset bound
  have notEnd : offset ≠ (completeCode graph width).length := by omega
  simp only [completeProgram, Nat.zero_add, Array.getElem?_push, List.size_toArray,
    notEnd, ite_false, List.getElem?_toArray]

theorem completeProgram_halt (graph : DAG n) (width : Nat) :
    (completeProgram graph width)[(completeCode graph width).length]? = some .halt := by
  simp [completeProgram, Array.getElem?_push]

theorem completeProgram_size_le (graph : DAG n) (width : Nat) :
    (completeProgram graph width).size ≤ 12 * graph.countedSize +
      3 * graph.roots.length + 1 := by
  have coreBound := fullCode_length_le graph width 0
  simp only [completeProgram, Array.size_push, List.size_toArray, completeCode,
    List.length_append, emitCode_length, observationAddresses, List.length_map]
  omega

/-- A complete actual program evaluates, emits every stored root incidence,
and halts. Inputs and code addresses must be representable. -/
theorem complete_execution (graph : DAG n) (guarded : graph.Guarded)
    (assignment : Assignment n) (initialHeap : Array (Word width))
    (initialAddress initialLoaded : Word width) (initialAccumulator : Bool)
    (inputs : ChannelsStored assignment initialHeap) (initialSize : initialHeap.size = n)
    (programFits : (completeCode graph width).length < 2 ^ width)
    (heapFits : n + graph.nodeCount < 2 ^ width) :
    ∃ final ticks,
      Execution (completeProgram graph width)
        (cellState initialHeap 0 initialAddress initialLoaded initialAccumulator)
        final ticks (5 + n + graph.nodeCount + graph.roots.length) ∧
      final.halted = true ∧ final.heap.size = n + graph.nodeCount ∧
      ChannelsStored assignment final.heap ∧
      final.output = ((graph.outputValues assignment).map (boolWord width)).reverse ∧
      ticks ≤ 12 * graph.countedSize + 3 * graph.roots.length + 1 := by
  let core := prefixCode graph width 0 graph.nodeCount (Nat.le_refl _)
  let program := completeProgram graph width
  have allBlock := completeProgram_block graph width
  have coreBlock : BlockAt program 0 core :=
    BlockAt.prefix program 0 core (emitCode width (observationAddresses graph)) allBlock
  have coreFits : 0 + core.length < 2 ^ width := by
    simp only [completeCode, List.length_append] at programFits
    dsimp [core]; omega
  obtain ⟨heap, address, loaded, accumulator, coreTicks, channels, heapSize,
      table, coreTrace, tickBound⟩ :=
    full_execution graph guarded program 0 assignment initialHeap initialAddress initialLoaded
      initialAccumulator inputs initialSize coreFits heapFits coreBlock
  let middle := cellState heap core.length address loaded accumulator
  have coreTrace' : Execution program
      (cellState initialHeap 0 initialAddress initialLoaded initialAccumulator)
      middle coreTicks (5 + n + graph.nodeCount) := by
    simpa only [Nat.zero_add] using coreTrace
  have middleHeap : middle.heap = heap := rfl
  have emissionBlock : BlockAt program core.length (emitCode width (observationAddresses graph)) := by
    simpa only [Nat.zero_add] using BlockAt.suffix program 0 core
      (emitCode width (observationAddresses graph)) allBlock
  have emissionFits : core.length + 3 * (observationAddresses graph).length < 2 ^ width := by
    simpa only [completeCode, List.length_append, emitCode_length] using programFits
  have valid : ∀ a ∈ observationAddresses graph, a < middle.heap.size := by
    intro a member
    obtain ⟨root, _, rfl⟩ := List.mem_map.mp member
    have rootBound : root.val < graph.nodeCount := root.isLt
    change n + root.val < heap.size
    rw [heapSize]; omega
  obtain ⟨emitted, emissionTrace, emittedHeap, emittedStack, emittedOutput, emittedPC, emittedRunning⟩ :=
    emitCode_execution program middle core.length (observationAddresses graph) rfl rfl
      emissionFits (by rw [middleHeap, heapSize]; exact heapFits) valid emissionBlock
  have finalPC : emitted.pc = word width (completeCode graph width).length := by
    simpa only [completeCode, List.length_append, emitCode_length] using emittedPC
  have terminal := halt_execution program emitted (completeCode graph width).length
    finalPC emittedRunning programFits (completeProgram_halt graph width)
  let final := { emitted.advance with halted := true }
  have outputLength : emitted.output.length = graph.roots.length := by
    rw [emittedOutput]
    simp [middle, cellState, observationAddresses]
  have emittedLive : emitted.liveWords = 5 + n + graph.nodeCount + graph.roots.length := by
    simp only [State.liveWords, emittedHeap, emittedStack, middle, cellState, heapSize,
      List.length_nil, outputLength]
    omega
  refine ⟨final, coreTicks + 3 * (observationAddresses graph).length + 1, ?_, rfl,
    ?_, ?_, ?_, ?_⟩
  · have joined := coreTrace'.append (emissionTrace.append terminal)
    have middleLive : middle.liveWords = 5 + n + graph.nodeCount := by
      simp only [middle, cellState_liveWords, heapSize]; omega
    have count : (observationAddresses graph).length = graph.roots.length := by
      simp [observationAddresses]
    have peak : max (5 + n + graph.nodeCount)
        (max (middle.liveWords + (observationAddresses graph).length) emitted.liveWords) =
        5 + n + graph.nodeCount + graph.roots.length := by rw [middleLive, count, emittedLive]; omega
    rw [peak] at joined
    simpa only [Nat.zero_add, Nat.add_assoc] using joined
  · change emitted.heap.size = n + graph.nodeCount
    rw [emittedHeap]; exact heapSize
  · change ChannelsStored assignment emitted.heap
    rw [emittedHeap]; exact channels
  · change emitted.output = _
    rw [emittedOutput]
    simp only [middle, cellState, List.append_nil]
    congr 1
    change (graph.roots.map (fun root => n + root.val)).map (heapValue heap) = _
    rw [List.map_map]
    simp only [DAG.outputValues, List.map_map]
    apply List.map_congr_left
    intro root _
    obtain ⟨validRoot, held⟩ := table root
    change heapValue heap (n + root.val) = boolWord width (graph.eval assignment root)
    rw [heapValue_eq heap (n + root.val) validRoot, held]
  · have count : (observationAddresses graph).length = graph.roots.length := by
      simp [observationAddresses]
    rw [count]; omega

/-- The initial heap encodes only supplied input coordinates, never a decoder answer. -/
def inputHeap (width : Nat) (assignment : Assignment n) : Array (Word width) :=
  (List.ofFn (fun label : Channel n => boolWord width (assignment label))).toArray

@[simp] theorem inputHeap_size (width : Nat) (assignment : Assignment n) :
    (inputHeap width assignment).size = n := by simp [inputHeap]

theorem inputHeap_stored (width : Nat) (assignment : Assignment n) :
    ChannelsStored assignment (inputHeap width assignment) := by
  refine ⟨?_, ?_⟩
  · intro label; simpa using label.isLt
  · intro label; simp [inputHeap, List.getElem_ofFn]

theorem completeProgram_representable (graph : DAG n) (assignment : Assignment n)
    (registersFit : 4 ≤ 2 ^ width)
    (programFits : (completeCode graph width).length < 2 ^ width)
    (heapFits : n + graph.nodeCount < 2 ^ width) :
    Representable (completeProgram graph width)
      (cellState (inputHeap width assignment) 0 (word width 0) (word width 0) false) := by
  refine ⟨registersFit, ?_, ?_⟩
  · simp only [completeProgram, Array.size_push, List.size_toArray]; omega
  · change (inputHeap width assignment).size ≤ 2 ^ width
    rw [inputHeap_size]; omega

/-- Starting from the direct input encoding discharges the table premise. -/
theorem complete_execution_encoded (graph : DAG n) (guarded : graph.Guarded)
    (assignment : Assignment n)
    (programFits : (completeCode graph width).length < 2 ^ width)
    (heapFits : n + graph.nodeCount < 2 ^ width) :
    ∃ final ticks,
      Execution (completeProgram graph width)
        (cellState (inputHeap width assignment) 0 (word width 0) (word width 0) false)
        final ticks (5 + n + graph.nodeCount + graph.roots.length) ∧
      final.halted = true ∧ final.heap.size = n + graph.nodeCount ∧
      ChannelsStored assignment final.heap ∧
      final.output = ((graph.outputValues assignment).map (boolWord width)).reverse ∧
      ticks ≤ 12 * graph.countedSize + 3 * graph.roots.length + 1 :=
  complete_execution graph guarded assignment (inputHeap width assignment)
    (word width 0) (word width 0) false (inputHeap_stored width assignment)
    (inputHeap_size width assignment) programFits heapFits

/-- Resident storage charges generated instructions, the complete table and
all emitted observations, including repeated roots. -/
theorem completeProgram_peak_resident_le (graph : DAG n) (width : Nat) :
    programWords (completeProgram graph width) +
      (5 + n + graph.nodeCount + graph.roots.length) ≤ 61 * graph.countedSize + 9 := by
  have codeBound := completeProgram_size_le graph width
  have tableBound : n + graph.nodeCount + graph.roots.length ≤ graph.countedSize := by
    rw [DAG.countedSize_eq]; omega
  unfold programWords
  omega

theorem completeProgram_peak_bits_le (graph : DAG n) (width : Nat) :
    width * (programWords (completeProgram graph width) +
      (5 + n + graph.nodeCount + graph.roots.length)) ≤ width * (61 * graph.countedSize + 9) :=
  Nat.mul_le_mul_left width (completeProgram_peak_resident_le graph width)

end Controller.Cost.OutputProgram
