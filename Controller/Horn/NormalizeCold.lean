module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Horn.SourceSerialize
public import Controller.Horn.NormalizeInitialize
public import Controller.Horn.NormalizeEmbed
public import Controller.Horn.TrackedInput

@[expose] public section

/-! Original clause words are loaded from the caller stack into an empty heap.
Four fetched constants establish the common register convention. The stored
loader, initializer and shared normalizer then execute in one program. Source
and caller storage are charged; no normalized rule list is supplied. -/
namespace Controller.Horn.NormalizeCold
open Controller.Cost Controller.Horn.SourceDirectory
open Controller.Horn.Worklist.IndexedNormalize
variable {width n : Nat}

def bootstrap (width : Nat) : Program width 8 :=
  #[.constant 2 (word width 0), .constant 5 (word width 1),
    .constant 6 (word width (2 ^ width - 1)), .constant 7 (word width 0)]

@[simp] theorem bootstrap_size (width : Nat) : (bootstrap width).size = 4 := rfl

def words (clauses : List (Controller.CNF.Clause (Fin n))) : Nat :=
  (Controller.Horn.SourceSerialize.heap (width := width) clauses).size

def loadedPrefix (width : Nat) (clauses : List (Controller.CNF.Clause (Fin n))) : Program width 8 :=
  bootstrap width ++ (Controller.Horn.TrackedInput.code (width := width) (words (width := width) clauses)).toArray

def initializedPrefix (width : Nat) (clauses : List (Controller.CNF.Clause (Fin n))) : Program width 8 :=
  let prefixCode := loadedPrefix width clauses
  prefixCode ++ Controller.Horn.NormalizeInitialize.code width prefixCode.size n
    (Controller.Horn.SourceSerialize.base clauses) 0

def program (width : Nat) (clauses : List (Controller.CNF.Clause (Fin n))) : Program width 8 :=
  let prefixCode := initializedPrefix width clauses
  prefixCode ++ Controller.Horn.NormalizeCNF.code width prefixCode.size n
    (Controller.Horn.SourceSerialize.base clauses) 0 1 2 3 4

@[simp] theorem words_eq (clauses : List (Controller.CNF.Clause (Fin n))) :
    words (width := width) clauses = 5 + 2 * clauses.length + 2 * (clauses.map List.length).sum := by
  simp [words, Controller.Horn.SourceSerialize.base, Controller.Horn.SourceSerialize.source]

@[simp] theorem loadedPrefix_size (clauses : List (Controller.CNF.Clause (Fin n))) :
    (loadedPrefix width clauses).size = 4 + 3 * words (width := width) clauses := by
  simp [loadedPrefix]

@[simp] theorem initializedPrefix_size (clauses : List (Controller.CNF.Clause (Fin n))) :
    (initializedPrefix width clauses).size = 23 + 3 * words (width := width) clauses := by
  simp [initializedPrefix]; omega

@[simp] theorem program_size (clauses : List (Controller.CNF.Clause (Fin n))) :
    (program width clauses).size = 199 + 6 * clauses.length + 6 * (clauses.map List.length).sum := by
  simp [program, words_eq]; omega

@[simp] theorem program_words (clauses : List (Controller.CNF.Clause (Fin n))) :
    programWords (program width clauses) = 796 + 24 * clauses.length + 24 * (clauses.map List.length).sum := by
  simp [programWords]; omega

private theorem prefix_fetch (first rest : Program width 8) (position : Nat)
    (inside : position < first.size) : (first ++ rest)[position]? = first[position]? :=
  Array.getElem?_append_left inside

/-- Exact physical initializer placement survives the later normalizer suffix. -/
theorem initializer_at (clauses : List (Controller.CNF.Clause (Fin n))) :
    Controller.Horn.NormalizeInitialize.At (program width clauses)
      (loadedPrefix width clauses).size n (Controller.Horn.SourceSerialize.base clauses) 0 := by
  have stored := Controller.Horn.NormalizeInitialize.stored_at (loadedPrefix width clauses) n
    (Controller.Horn.SourceSerialize.base clauses) 0
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold program
    rw [prefix_fetch _ _ _ (by simp [initializedPrefix])]
    exact stored.counter
  · intro phase
    unfold program
    rw [prefix_fetch _ _ _ (by simp [initializedPrefix]; have := phase.isLt; omega)]
    exact stored.allocate phase
  · intro phase
    unfold program
    rw [prefix_fetch _ _ _ (by simp [initializedPrefix]; have := phase.isLt; omega)]
    exact stored.endpoint phase
  · intro phase
    unfold program
    rw [prefix_fetch _ _ _ (by simp [initializedPrefix]; have := phase.isLt; omega)]
    exact stored.headers phase

/-- No source-dependent duplication of the shared normalizer code. -/
theorem kernel_at (clauses : List (Controller.CNF.Clause (Fin n))) :
    Controller.Horn.NormalizeCode.KernelAt (program width clauses)
      (initializedPrefix width clauses).size n (Controller.Horn.SourceSerialize.base clauses) 0 1 2 3 4 :=
  Controller.Horn.NormalizeCode.prefix_kernel (initializedPrefix width clauses) n
    (Controller.Horn.SourceSerialize.base clauses) 0 1 2 3 4

/-- Each loader instruction is fetched at its actual stored address. -/
theorem loader_at (clauses : List (Controller.CNF.Clause (Fin n))) :
    Controller.Horn.TrackedInput.BlockAt (program width clauses) 4
      (Controller.Horn.TrackedInput.code (width := width) (words (width := width) clauses)) := by
  intro offset inside
  have lengthBound : offset < 3 * words (width := width) clauses := by
    simpa only [Controller.Horn.TrackedInput.code_length] using inside
  unfold program
  rw [prefix_fetch _ _ _ (by simp only [initializedPrefix, Array.size_append, Controller.Horn.NormalizeInitialize.code_size, loadedPrefix_size]; omega)]
  unfold initializedPrefix
  rw [prefix_fetch _ _ _ (by simp only [loadedPrefix_size]; omega)]
  unfold loadedPrefix
  rw [Array.getElem?_append_right (by simp)]
  simp only [bootstrap_size, Nat.add_sub_cancel_left, List.getElem?_toArray]

/-- Four actual bootstrap fetches, with arbitrary caller stack and output. -/
theorem bootstrap_at (clauses : List (Controller.CNF.Clause (Fin n))) :
    ∀ phase : Fin 4, (program width clauses)[phase.val]? = (bootstrap width)[phase.val]? := by
  intro phase
  unfold program
  rw [prefix_fetch _ _ _ (by simp [initializedPrefix, loadedPrefix]; have := phase.isLt; omega)]
  unfold initializedPrefix
  rw [prefix_fetch _ _ _ (by simp [loadedPrefix]; have := phase.isLt; omega)]
  unfold loadedPrefix
  exact prefix_fetch _ _ _ (by simpa using phase.isLt)

def booted (state : State width 8) : State width 8 :=
  (((state.advance.put 2 (word width 0)).advance.put 5 (word width 1)).advance.put 6
    (word width (2 ^ width - 1))).advance.put 7 (word width 0)

private theorem word_value (value : Nat) (fits : value < 2 ^ width) :
    (word width value).val = value := Nat.mod_eq_of_lt fits

/-- The bootstrap uses four charged instructions, without changing live storage. -/
theorem bootstrap_execution (clauses : List (Controller.CNF.Clause (Fin n)))
    (state : State width 8) (position : state.pc = word width 0)
    (running : state.halted = false) (capacity : 4 < 2 ^ width) :
    Execution (program width clauses) state (booted state) 4 state.liveWords := by
  let s1 := state.advance.put 2 (word width 0)
  let s2 := s1.advance.put 5 (word width 1)
  let s3 := s2.advance.put 6 (word width (2 ^ width - 1))
  have p1 : s1.pc = word width 1 := by simp [s1, State.advance, State.put, position, word_value (width := width) 0 (by omega)]
  have p2 : s2.pc = word width 2 := by simp [s2, State.advance, State.put, p1, word_value (width := width) 1 (by omega)]
  have p3 : s3.pc = word width 3 := by simp [s3, State.advance, State.put, p2, word_value (width := width) 2 (by omega)]
  have t0 : programStep (program width clauses) state = some s1 := by
    unfold programStep
    rw [position, word_value (width := width) 0 (by omega)]
    have fetch := bootstrap_at (width := width) clauses ⟨0, by decide⟩
    rw [show (program width clauses)[0]? = some (.constant 2 (word width 0)) from by simpa [bootstrap] using fetch]
    simp [step, s1, running]
  have t1 : programStep (program width clauses) s1 = some s2 := by
    unfold programStep
    rw [p1, word_value (width := width) 1 (by omega)]
    have fetch := bootstrap_at (width := width) clauses ⟨1, by decide⟩
    rw [show (program width clauses)[1]? = some (.constant 5 (word width 1)) from by simpa [bootstrap] using fetch]
    simp [step, s2, s1, State.advance, State.put, running]
  have t2 : programStep (program width clauses) s2 = some s3 := by
    unfold programStep
    rw [p2, word_value (width := width) 2 (by omega)]
    have fetch := bootstrap_at (width := width) clauses ⟨2, by decide⟩
    rw [show (program width clauses)[2]? = some (.constant 6 (word width (2 ^ width - 1))) from by simpa [bootstrap] using fetch]
    simp [step, s3, s2, s1, State.advance, State.put, running]
  have t3 : programStep (program width clauses) s3 = some (booted state) := by
    unfold programStep
    rw [p3, word_value (width := width) 3 (by omega)]
    have fetch := bootstrap_at (width := width) clauses ⟨3, by decide⟩
    rw [show (program width clauses)[3]? = some (.constant 7 (word width 0)) from by simpa [bootstrap] using fetch]
    simp [step, booted, s3, s2, s1, State.advance, State.put, running]
  have trace := Execution.cons t0 (Execution.cons t1 (Execution.cons t2
    (Execution.cons t3 (Execution.refl (booted state)))))
  simpa [booted, s1, s2, s3, State.liveWords, State.advance, State.put] using trace

/-- Original input only: physical source words, arbitrary trailing caller frame,
and an empty initial heap. Program and heap capacity are separate obligations. -/
theorem execution (clauses : List (Controller.CNF.Clause (Fin n)))
    (state : State width 8) (suffix : List (Word width))
    (emptyHeap : state.heap = #[])
    (input : state.stack = (Controller.Horn.SourceSerialize.heap (width := width) clauses).toList ++ suffix)
    (position : state.pc = word width 0) (running : state.halted = false)
    (dual : ∀ index : Fin clauses.length, Controller.Horn.DualHornClause clauses[index.val])
    (codeFits : (program width clauses).size < 2 ^ width)
    (heapFits : words (width := width) clauses + 5 * n + 4 + 3 * clauses.length +
      (clauses.map List.length).sum < 2 ^ width) :
    ∃ final : State width 8, ∃ marks : Marks n, ∃ ticks peak : Nat,
      Execution (program width clauses) state final ticks peak ∧
      Controller.Horn.NormalizeLoop.Invariant clauses (Controller.Horn.SourceSerialize.layout clauses)
        (words (width := width) clauses + 5 * n + 4) clauses.length marks final ∧
      final.pc = word width (program width clauses).size ∧
      final.stack = suffix ∧ final.output = state.output ∧
      ticks ≤ 25 * n + 67 * (clauses.map List.length).sum + 77 * clauses.length + 60 ∧
      peak ≤ state.liveWords + 5 * n + 4 + 3 * clauses.length + (clauses.map List.length).sum := by
  have codeSize := program_size (width := width) clauses
  have E := words_eq (width := width) clauses
  have bootTrace := bootstrap_execution clauses state position running (by omega)
  have bootPC : (booted state).pc = word width 4 := by
    simp [booted, State.advance, State.put, position, word_value (width := width) 0 (by omega), word_value (width := width) 1 (by omega),
      word_value (width := width) 2 (by omega), word_value (width := width) 3 (by omega)]
  have bootRunning : (booted state).halted = false := by simpa [booted, State.advance, State.put] using running
  have bootHeap : (booted state).heap = #[] := by simpa [booted, State.advance, State.put] using emptyHeap
  have bootStack : (booted state).stack = state.stack := rfl
  have bootOutput : (booted state).output = state.output := rfl
  have bootLive : (booted state).liveWords = state.liveWords := rfl
  obtain ⟨loaded, loadTrace, loadedHeap, loadedStack, loadedOutput, loadedPC, loadedRunning,
    loadedPointer, loadedFrame⟩ := Controller.Horn.TrackedInput.code_execution (program width clauses)
      (booted state) (Controller.Horn.SourceSerialize.heap (width := width) clauses).toList suffix 4
      bootPC bootRunning (by simpa [bootStack] using input)
      (by simpa [words] using (show 4 + 3 * words (width := width) clauses < 2 ^ width by omega))
      (by simp only [bootHeap, Array.size_empty, Array.length_toList, Nat.zero_add]; change words (width := width) clauses < 2 ^ width; omega)
      (by simp [booted, State.advance, State.put, emptyHeap])
      (by simp [booted, State.advance, State.put]) (loader_at clauses)
  have loadedOriginal : loaded.heap = Controller.Horn.SourceSerialize.heap (width := width) clauses := by
    simpa [bootHeap] using loadedHeap
  have loadedSize : loaded.heap.size = words (width := width) clauses := by rw [loadedOriginal]; rfl
  have loadedLive : loaded.liveWords = state.liveWords := by
    simp only [State.liveWords, loadedSize, loadedStack, loadedOutput, bootOutput,
      input, emptyHeap, Array.size_empty, List.length_append, Array.length_toList, words]; omega
  have representable : Controller.Horn.SourceSerialize.Representable width clauses := by
    constructor
    · omega
    · simpa [words] using (show words (width := width) clauses < 2 ^ width by omega)
  have originalInput := Controller.Horn.SourceSerialize.input clauses loaded loadedOriginal
    (by rw [loadedFrame 2 (by decide) (by decide)]; simp [booted, State.advance, State.put])
    (by rw [loadedFrame 5 (by decide) (by decide)]; simp [booted, State.advance, State.put])
    (by rw [loadedFrame 6 (by decide) (by decide)]; simp [booted, State.advance, State.put])
    loadedRunning representable
  obtain ⟨initialized, initTrace, invariant, initPC, initStack, initOutput⟩ :=
    Controller.Horn.NormalizeInitialize.execution (program width clauses) (loadedPrefix width clauses).size
      clauses (Controller.Horn.SourceSerialize.layout clauses) (initializer_at clauses) loaded originalInput
      (by simpa [Controller.Horn.SourceSerialize.layout, words] using loadedSize.symm)
      loadedPointer (by simpa [words, Controller.Horn.SourceSerialize.base, Controller.Horn.SourceSerialize.source] using loadedPC) (by simp at codeFits ⊢; omega)
      (by rw [loadedSize]; omega)
  have initSize : initialized.heap.size = words (width := width) clauses + 5 * n + 4 := by
    simpa [Controller.Horn.NormalizeLoop.recordOffset, loadedSize] using invariant.records.endpoint
  have initLive : initialized.liveWords = state.liveWords + 5 * n + 4 := by
    simp only [State.liveWords, initSize, initStack, initOutput, loadedStack,
      loadedOutput, bootOutput, input, emptyHeap, Array.size_empty, List.length_append,
      Array.length_toList, words]; omega
  have transformedKernel := Controller.Horn.NormalizeEmbed.neutralized_kernel (program width clauses)
    (initializedPrefix width clauses).size n (Controller.Horn.SourceSerialize.base clauses) 0 1 2 3 4
    (kernel_at clauses)
  have components := Controller.Horn.NormalizeCode.kernel_components
    (Controller.Horn.NormalizeEmbed.neutralize (program width clauses)) (initializedPrefix width clauses).size
    clauses (Controller.Horn.SourceSerialize.layout clauses) transformedKernel
  obtain ⟨final, marks, loopTicks, loopPeak, loopTrace, complete, finalPC, cost, storage⟩ :=
    Controller.Horn.NormalizeLoop.normalize_all_execution
      (Controller.Horn.NormalizeEmbed.neutralize (program width clauses)) (initializedPrefix width clauses).size
      clauses (Controller.Horn.SourceSerialize.layout clauses) components
      (loaded.heap.size + 5 * n + 4) (Marks.initial n) initialized invariant dual
      (by simpa [initializedPrefix, Nat.add_assoc] using initPC)
      (by simpa [program] using codeFits) (by rw [initSize]; omega)
      (Controller.Horn.NormalizeEmbed.neutralized_neutral (program width clauses))
  have caller := Controller.Horn.SourceDirectory.caller_execution
    (Controller.Horn.NormalizeEmbed.neutralized_neutral (program width clauses)) loopTrace
  have originalLoop := Controller.Horn.NormalizeEmbed.lift_execution loopTrace complete.input.running
  have full := (bootTrace.append loadTrace).append (initTrace.append originalLoop)
  refine ⟨final, marks, 4 + 3 * words (width := width) clauses + (5 * (5 * n + 4) + 15 + loopTicks),
    max state.liveWords (max state.liveWords (max (state.liveWords + 5 * n + 4) loopPeak)),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Array.length_toList, words, bootLive, loadedLive, ← Nat.max_assoc, Nat.max_self] using full
  · simpa only [loadedSize] using complete
  · simpa only [program, Array.size_append, Controller.Horn.NormalizeCNF.code_size] using finalPC
  · exact caller.1.trans (initStack.trans loadedStack)
  · exact caller.2.trans (initOutput.trans (loadedOutput.trans bootOutput))
  · omega
  · simp only [Controller.Horn.NormalizeEmbed.neutralize_words] at storage
    rw [initLive] at storage
    omega

end Controller.Horn.NormalizeCold
