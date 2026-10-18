module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestZeroAnswer

@[expose] public section

/-! Fixed-program first-success control uses the physical register-four tag.
Per-query execution contracts retain the shared source and sparse dictionary
invariant. Failed queries advance without channel emission; model emission is
charged only on the terminating successful query. -/
namespace Controller.Cost.ForestZeroRootLoop
open Controller.Cost
variable {width : Nat}

def dispatchCode (width next : Nat) : Program width 8 :=
  #[.branchZero 4 (word width next), .halt]

def dispatchState (state : State width 8) (entry next : Nat) (answer : Bool) : State width 8 :=
  { state with pc := word width (if answer then entry + 2 else next), halted := answer }

private theorem fetched (program : Program width 8) (state : State width 8)
    (entry : Nat) (instruction : Instruction width 8)
    (position : state.pc = word width entry) (fits : entry < 2 ^ width)
    (present : program[entry]? = some instruction) :
    programStep program state = step instruction state := by
  unfold programStep
  rw [position, show (word width entry).val = entry from Nat.mod_eq_of_lt fits, present]
  rfl

/-- Dispatch branches on the fetched decision register, with no output read. -/
theorem dispatch_execution (program : Program width 8) (state : State width 8)
    (entry next : Nat) (answer : Bool)
    (position : state.pc = word width entry) (running : state.halted = false)
    (decision : state.reg 4 = word width (if answer then 1 else 0))
    (fits : entry + 2 < 2 ^ width)
    (present : ∀ phase : Fin 2,
      program[entry + phase.val]? = (dispatchCode width next)[phase.val]?) :
    Execution program state (dispatchState state entry next answer)
      (if answer then 2 else 1) state.liveWords := by
  cases answer with
  | false =>
    have transition : programStep program state = some (dispatchState state entry next false) := by
      rw [fetched program state entry (.branchZero 4 (word width next)) position (by omega)
        (by simpa [dispatchCode] using present ⟨0, by decide⟩)]
      simp [step, running, decision, word, State.advance, dispatchState]
    simpa [dispatchState, State.liveWords, Nat.max_self] using
      Execution.cons transition (Execution.refl (dispatchState state entry next false))
  | true =>
    let middle : State width 8 := { state with pc := word width (entry + 1) }
    have transition : programStep program state = some middle := by
      rw [fetched program state entry (.branchZero 4 (word width next)) position (by omega)
        (by simpa [dispatchCode] using present ⟨0, by decide⟩)]
      have one : (word width 1).val = 1 := Nat.mod_eq_of_lt (by omega)
      have pc : state.pc.val = entry := by rw [position]; exact Nat.mod_eq_of_lt (by omega)
      simp [step, running, decision, one, pc, State.advance, middle]
    have finish : programStep program middle = some (dispatchState state entry next true) := by
      rw [fetched program middle (entry + 1) .halt rfl (by omega)
        (by simpa [dispatchCode] using present ⟨1, by decide⟩)]
      have pc : (word width (entry + 1)).val = entry + 1 := Nat.mod_eq_of_lt (by omega)
      simp [step, middle, running, State.advance, dispatchState, pc, Nat.add_assoc]
    simpa [middle, dispatchState, State.liveWords, Nat.max_self] using
      Execution.cons transition (Execution.cons finish (Execution.refl (dispatchState state entry next true)))

def exhaustedCode (width : Nat) : Program width 8 := #[.constant 4 (word width 0), .halt]

def exhaustedState (state : State width 8) (entry : Nat) : State width 8 :=
  { state.put 4 (word width 0) with pc := word width (entry + 2), halted := true }

theorem exhausted_execution (program : Program width 8) (state : State width 8)
    (entry : Nat) (position : state.pc = word width entry) (running : state.halted = false)
    (fits : entry + 2 < 2 ^ width)
    (present : ∀ phase : Fin 2,
      program[entry + phase.val]? = (exhaustedCode width)[phase.val]?) :
    Execution program state (exhaustedState state entry) 2 state.liveWords := by
  let middle := state.advance.put 4 (word width 0)
  have pc : middle.pc = word width (entry + 1) := by
    simp [middle, State.advance, State.put, position,
      show (word width entry).val = entry from Nat.mod_eq_of_lt (by omega)]
  have first : programStep program state = some middle := by
    rw [fetched program state entry (.constant 4 (word width 0)) position (by omega)
      (by simpa [exhaustedCode] using present ⟨0, by decide⟩)]
    simp [step, running, middle]
  have last : programStep program middle = some (exhaustedState state entry) := by
    rw [fetched program middle (entry + 1) .halt pc (by omega)
      (by simpa [exhaustedCode] using present ⟨1, by decide⟩)]
    have initialPC : state.pc.val = entry := by rw [position]; exact Nat.mod_eq_of_lt (by omega)
    have nextPC : (word width (entry + 1)).val = entry + 1 := Nat.mod_eq_of_lt (by omega)
    simp [step, middle, running, exhaustedState, State.advance, State.put, initialPC, nextPC, Nat.add_assoc]
  simpa [middle, exhaustedState, State.liveWords, State.advance, State.put, Nat.max_self] using
    Execution.cons first (Execution.cons last (Execution.refl (exhaustedState state entry)))

/-- The remaining stream is a physical continuation of the fixed source list. -/
def TailOf {A : Type} (all remaining : List A) : Prop := ∃ before, all = before ++ remaining

theorem tailOf_tail {A : Type} {all : List A} {item : A} {rest : List A}
    (suffix : TailOf all (item :: rest)) : TailOf all rest := by
  obtain ⟨before, same⟩ := suffix
  refine ⟨before ++ [item], ?_⟩
  simpa [List.append_assoc] using same

/-- A query contract concerns actual executions in the same fixed program.
The source constructor, solver, reset and tag recovery must discharge it. -/
def QueryContract {A : Type} (program : Program width 8) (all : List A)
    (ready : List A → State width 8 → Prop) (feasible : A → Prop)
    (witness : A → List (Word width) → Prop) (resume : List A → Nat)
    (dispatch : A → Nat) (work : A → Nat) (scratch emitTicks emitWords : Nat) : Prop :=
  ∀ item rest state, TailOf all (item :: rest) → ready (item :: rest) state →
    ∃ answer : Bool, ∃ final ticks peak,
      Execution program state final ticks peak ∧
      final.pc = word width (dispatch item) ∧ final.halted = false ∧
      final.reg 4 = word width (if answer then 1 else 0) ∧
      ticks ≤ work item + (if answer then emitTicks else 0) ∧
      peak ≤ state.liveWords + scratch + (if answer then emitWords else 0) ∧
      final.liveWords ≤ state.liveWords + 1 + (if answer then emitWords else 0) ∧
      (answer = true ↔ feasible item) ∧
      (answer = true → witness item final.output) ∧
      (answer = false → ready rest (dispatchState final (dispatch item) (resume rest) false)) ∧
      dispatch item + 2 < 2 ^ width ∧
      (∀ phase : Fin 2, program[dispatch item + phase.val]? =
        (dispatchCode width (resume rest))[phase.val]?)


/-- The fixed-program scan stops at its first successful query. Both resource
bounds charge channel emission once, regardless of the number of failures. -/
theorem first_success_execution {A : Type} (program : Program width 8) (all : List A)
    (ready : List A → State width 8 → Prop) (feasible : A → Prop)
    (witness : A → List (Word width) → Prop) (resume : List A → Nat)
    (dispatch : A → Nat) (work : A → Nat) (scratch emitTicks emitWords : Nat)
    (query : QueryContract program all ready feasible witness resume dispatch work scratch emitTicks emitWords)
    (emptyReady : ∀ state, ready [] state → state.pc = word width (resume []) ∧ state.halted = false)
    (emptyFits : resume [] + 2 < 2 ^ width)
    (emptyAt : ∀ phase : Fin 2,
      program[resume [] + phase.val]? = (exhaustedCode width)[phase.val]?)
    (remaining : List A) (suffix : TailOf all remaining)
    (state : State width 8) (initial : ready remaining state) :
    ∃ result : Bool, ∃ final ticks peak,
      Execution program state final ticks peak ∧ final.halted = true ∧
      final.reg 4 = word width (if result then 1 else 0) ∧
      ticks ≤ (remaining.map work).sum + remaining.length + emitTicks + 2 ∧
      peak ≤ state.liveWords + scratch + remaining.length + emitWords + 1 ∧
      (result = true ↔ ∃ item ∈ remaining, feasible item) ∧
      (result = true → ∃ item ∈ remaining, feasible item ∧ witness item final.output) := by
  induction remaining generalizing state with
  | nil =>
    obtain ⟨position, running⟩ := emptyReady state initial
    have trace := exhausted_execution program state (resume []) position running emptyFits emptyAt
    refine ⟨false, exhaustedState state (resume []), 2, state.liveWords, trace, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · simp [exhaustedState, State.put]
    · simp
    · simp only [List.length_nil, Nat.add_zero]; omega
    · simp
    · simp
  | cons item rest ih =>
    obtain ⟨answer, afterQuery, queryTicks, queryPeak, queryTrace, position, running,
        decision, queryTime, querySpace, queryLive, meaning, model, nextReady, fits, present⟩ :=
      query item rest state suffix initial
    cases answer with
    | false =>
      have branch := dispatch_execution program afterQuery (dispatch item) (resume rest) false
        position running decision fits present
      obtain ⟨result, final, tailTicks, tailPeak, tailTrace, halted, finalDecision,
          tailTime, tailSpace, tailMeaning, tailModel⟩ :=
        ih (tailOf_tail suffix) (dispatchState afterQuery (dispatch item) (resume rest) false) (nextReady rfl)
      have notFeasible : ¬ feasible item := by
        intro possible
        have impossible := meaning.mpr possible
        cases impossible
      have nextLive : (dispatchState afterQuery (dispatch item) (resume rest) false).liveWords =
          afterQuery.liveWords := rfl
      have firstTime : queryTicks ≤ work item := by simpa using queryTime
      have firstSpace : queryPeak ≤ state.liveWords + scratch := by simpa using querySpace
      have firstLive : afterQuery.liveWords ≤ state.liveWords + 1 := by simpa using queryLive
      have joined := (queryTrace.append branch).append tailTrace
      refine ⟨result, final, queryTicks + 1 + tailTicks,
        max (max queryPeak afterQuery.liveWords) tailPeak, joined, halted, finalDecision, ?_, ?_, ?_, ?_⟩
      · simp only [List.map_cons, List.sum_cons, List.length_cons]
        omega
      · rw [nextLive] at tailSpace
        apply Nat.max_le.mpr
        constructor
        · apply Nat.max_le.mpr
          constructor <;> simp only [List.length_cons] <;> omega
        · simp only [List.length_cons]; omega
      · constructor
        · intro success
          obtain ⟨found, member, possible⟩ := tailMeaning.mp success
          exact ⟨found, List.mem_cons_of_mem item member, possible⟩
        · rintro ⟨found, member, possible⟩
          rcases List.mem_cons.mp member with same | member
          · subst found
            exact (notFeasible possible).elim
          · exact tailMeaning.mpr ⟨found, member, possible⟩
      · intro success
        obtain ⟨found, member, possible, actual⟩ := tailModel success
        exact ⟨found, List.mem_cons_of_mem item member, possible, actual⟩
    | true =>
      have branch := dispatch_execution program afterQuery (dispatch item) (resume rest) true
        position running decision fits present
      have possible := meaning.mp rfl
      have actual := model rfl
      refine ⟨true, dispatchState afterQuery (dispatch item) (resume rest) true,
        queryTicks + 2, max queryPeak afterQuery.liveWords, queryTrace.append branch,
        rfl, decision, ?_, ?_, ?_, ?_⟩
      · simp only [List.map_cons, List.sum_cons, List.length_cons]
        simp only [Bool.true_eq, ite_true] at queryTime
        omega
      · simp only [Bool.true_eq, ite_true] at querySpace queryLive
        apply Nat.max_le.mpr
        constructor <;> simp only [List.length_cons] <;> omega
      · exact ⟨fun _ => ⟨item, List.mem_cons_self, possible⟩, fun _ => rfl⟩
      · exact fun _ => ⟨item, List.mem_cons_self, possible, actual⟩

/-- Per-query linear charges add without introducing a product of the number
of queries and the total source size. The caller must discharge `bound` from
its executed constructor and prove the aggregate source-incidence bounds. -/
theorem linear_work_sum {A : Type} (items : List A)
    (work rows literals : A → Nat) (a b c : Nat)
    (bound : ∀ item ∈ items, work item ≤ a * rows item + b * literals item + c) :
    (items.map work).sum ≤
      a * (items.map rows).sum + b * (items.map literals).sum + c * items.length := by
  revert bound
  induction items with
  | nil => intro _; simp
  | cons item rest ih =>
    intro bound
    have head := bound item (by simp)
    have tail := ih (by
      intro next inside
      exact bound next (by simp only [List.mem_cons]; exact Or.inr inside))
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    calc
      work item + (rest.map work).sum ≤
          (a * rows item + b * literals item + c) +
          (a * (rest.map rows).sum + b * (rest.map literals).sum + c * rest.length) :=
        Nat.add_le_add head tail
      _ = a * (rows item + (rest.map rows).sum) +
          b * (literals item + (rest.map literals).sum) + c * (rest.length + 1) := by
        simp only [Nat.mul_add, Nat.mul_one]
        omega

end Controller.Cost.ForestZeroRootLoop
